$(
###############################################################################
  COMPLEX TOPOLOGICAL VECTOR SPACES (DEPRECATED)
###############################################################################

  The intent is for this deprecated section to be deleted once its theorems
  have extensible structure versions (or are not useful).  You can make a list
  of "terminal" theorems (i.e., theorems not referenced by anything else) and
  for each theorem see if there exists an extensible structure version (or
  decide it is not useful), and if so, delete it.  Then, repeat this
  recursively.  One way to search for terminal theorems is to log the output
  ("MM> OPEN LOG xxx.txt") of "MM> SHOW USAGE <label-match>" in the Metamath
  program and search for "(None)".

$)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Additional material on group theory (deprecated)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  This section contains an earlier development of groups that was defined
  before extensible structures were introduced.

  The intent is for this deprecated section to be deleted once the
  corresponding definitions and theorems for complex topological vector spaces,
  which are using them, are revised accordingly.

$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definitions and basic properties for groups
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c GrpOp $.
  $c GId $.
  $c inv $.
  $c /g $.

  $( Extend class notation with the class of all group operations. $)
  cgr $a class GrpOp $.

  $( Extend class notation with a function mapping a group operation to the
     group's identity element. $)
  cgi $a class GId $.

  $( Extend class notation with a function mapping a group operation to the
     inverse function for the group. $)
  cgn $a class inv $.

  $( Extend class notation with a function mapping a group operation to the
     division (or subtraction) operation for the group. $)
  cgs $a class /g $.

  ${
    $d g t u x y z $.
    $( Define the class of all group operations.  The base set for a group can
       be determined from its group operation.  Based on the definition in
       Exercise 28 of [Herstein] p. 54.  (Contributed by NM, 10-Oct-2006.)
       (New usage is discouraged.) $)
    df-grpo $a |- GrpOp = { g | E. t ( g : ( t X. t ) --> t
       /\ A. x e. t A. y e. t A. z e. t ( ( x g y ) g z ) = ( x g ( y g z ) )
   /\ E. u e. t A. x e. t ( ( u g x ) = x /\ E. y e. t ( y g x ) = u ) ) } $.

    $( Define a function that maps a group operation to the group's identity
       element.  (Contributed by FL, 5-Feb-2010.)  (Revised by Mario Carneiro,
       15-Dec-2013.)  (New usage is discouraged.) $)
    df-gid $a |- GId = ( g e. _V |-> ( iota_ u e. ran g A. x e. ran g
                        ( ( u g x ) = x /\ ( x g u ) = x ) ) ) $.

    $( Define a function that maps a group operation to the group's inverse
       function.  (Contributed by NM, 26-Oct-2006.)
       (New usage is discouraged.) $)
    df-ginv $a |- inv = ( g e. GrpOp |-> ( x e. ran g |->
                    ( iota_ z e. ran g ( z g x ) = ( GId ` g ) ) ) ) $.

    $( Define a function that maps a group operation to the group's division
       (or subtraction) operation.  (Contributed by NM, 15-Feb-2008.)
       (New usage is discouraged.) $)
    df-gdiv $a |- /g = ( g e. GrpOp |-> ( x e. ran g , y e. ran g |->
                         ( x g ( ( inv ` g ) ` y ) ) ) ) $.
  $}

  ${
    $d g t u x y z G $.  $d g t u x y z X $.
    isgrp.1 $e |- X = ran G $.
    $( The predicate "is a group operation."  Note that ` X ` is the base set
       of the group.  (Contributed by NM, 10-Oct-2006.)
       (New usage is discouraged.) $)
    isgrpo $p |- ( G e. A -> ( G e. GrpOp <-> ( G : ( X X. X ) --> X /\
       A. x e. X A. y e. X A. z e. X ( ( x G y ) G z ) = ( x G ( y G z ) )
   /\ E. u e. X A. x e. X ( ( u G x ) = x /\ E. y e. X ( y G x ) = u ) ) ) ) $=
      ( vt vg wcel cv wceq cxp wf co wral wrex wa oveq cgr crn w3a oveq1d eqtrd
      wex feq1 oveq2d eqeq12d ralbidv 2ralbidv eqeq1d rexbidv anbi12d 3anbi123d
      rexralbidv exbidv df-grpo elab2g simpl ralimi oveq2 id eqcom bitrdi rspcv
      wfo rspceeqv syld syl5 reximdv impcom ralrimiva anim2i foov sylibr eqcomd
      ex forn syl 3adant2 pm4.71ri exbii wb rnexg eqeq2i xpeq1 xpeq2 feq2d feq3
      cvv bitrd raleq raleqbi1dv rexeq anbi2d rexeqbi1dv sylbir ceqsexgv ) FEKZ
      FUAKZILZFUBZMZXBXBNZXBFOZALZBLZFPZCLZFPZXGXHXJFPZFPZMZCXBQZBXBQZAXBQZDLZX
      GFPZXGMZXHXGFPZXRMZBXBRZSZAXBQZDXBRZUCZSZIUFZGGNZGFOZXNCGQZBGQZAGQZXTYBBG
      RZSZAGQZDGRZUCZWTXAYGIUFZYIXEXBJLZOZXGXHUUAPZXJUUAPZXGXHXJUUAPZUUAPZMZCXB
      QZBXBQAXBQZXRXGUUAPZXGMZXHXGUUAPZXRMZBXBRZSZAXBQDXBRZUCZIUFYTJFUAEUUAFMZU
      UQYGIUURUUBXFUUIXQUUPYFXEXBUUAFUGUURUUHXOABXBXBUURUUGXNCXBUURUUDXKUUFXMUU
      RUUDUUCXJFPXKUUCXJUUAFTUURUUCXIXJFXGXHUUAFTUDUEUURUUFXGUUEFPXMXGUUEUUAFTU
      URUUEXLXGFXHXJUUAFTUHUEUIUJUKUURUUOYDDAXBXBUURUUKXTUUNYCUURUUJXSXGXRXGUUA
      FTULUURUUMYBBXBUURUULYAXRXHXGUUAFTULUMUNUPUOUQABCDIJURUSYGYHIYGXDXFYFXDXQ
      XFYFSZXEXBFVGZXDUUSXFXJXRXHFPZMBXBRZDXBRZCXBQZSUUTYFUVDXFYFUVCCXBXJXBKZYF
      UVCUVEYEUVBDXBYEXTAXBQZUVEUVBYDXTAXBXTYCUTVAUVEUVFXJXRXJFPZMZUVBXTUVHAXJX
      BXGXJMZXTUVGXJMUVHUVIXSUVGXGXJXGXJXRFVBUVIVCUIUVGXJVDVEVFUVEUVHUVBBXJXBUV
      AUVGXJXHXJXRFVBVHVRVIVJVKVLVMVNDBCXBXBXBFVOVPUUTXCXBXEXBFVSVQVTWAWBWCVEWT
      XCWKKYIYSWDFEWEYGYSIXCWKXDXBGMZYGYSWDGXCXBHWFUVJXFYKXQYNYFYRUVJXFYJXBFOYK
      UVJXEYJXBFUVJXEGXBNYJXBGXBWGXBGGWHUEWIXBGYJFWJWLXPYMAXBGXOYLBXBGXNCXBGWMW
      NWNYEYQDXBGYDYPAXBGUVJYCYOXTYBBXBGWOWPWNWQUOWRWSVTWL $.
  $}

  ${
    $d u x y z G $.  $d u x y z U $.  $d u x y z X $.  $d y N $.
    isgrpoi.1 $e |- X e. _V $.
    isgrpoi.2 $e |- G : ( X X. X ) --> X $.
    isgrpoi.3 $e |- ( ( x e. X /\ y e. X /\ z e. X ) ->
                   ( ( x G y ) G z ) = ( x G ( y G z ) ) ) $.
    isgrpoi.4 $e |- U e. X $.
    isgrpoi.5 $e |- ( x e. X -> ( U G x ) = x ) $.
    isgrpoi.6 $e |- ( x e. X -> N e. X ) $.
    isgrpoi.7 $e |- ( x e. X -> ( N G x ) = U ) $.
    $( Properties that determine a group operation.  Read ` N ` as
       ` N ( x ) ` .  (Contributed by NM, 4-Nov-2006.)
       (New usage is discouraged.) $)
    isgrpoi $p |- G e. GrpOp $=
      ( vu wcel co wceq wral wrex cgr cxp wf cv rgen3 eqeq1d rspcev syl2anc jca
      wa oveq1 rgen eqeq2 rexbidv anbi12d ralbidv mp2an cvv w3a wb xpex fex crn
      wfo eqcomd rspceov mp3an1 mpdan foov mpbir2an forn eqcomi isgrpo mpbir3an
      ax-mp ) EUAPZGGUBZGEUCZAUDZBUDZEQCUDZEQVSVTWAEQZEQRZCGSBGSAGSZOUDZVSEQZVS
      RZVTVSEQZWERZBGTZUJZAGSZOGTZIWCABCGGGJUEDGPZDVSEQZVSRZWHDRZBGTZUJZAGSZWMK
      WSAGVSGPZWPWRLXAFGPFVSEQZDRZWRMNWQXCBFGVTFRWHXBDVTFVSEUKUFUGUHUIULWLWTODG
      WEDRZWKWSAGXDWGWPWJWRXDWFWOVSWEDVSEUKUFXDWIWQBGWEDWHUMUNUOUPUGUQEURPZVPVR
      WDWMUSUTVRVQURPXEIGGHHVAVQGUREVBUQABCOUREGEVCZGVQGEVDZXFGRXGVRVSWBRCGTBGT
      ZAGSIXHAGXAVSWORZXHXAWOVSLVEWNXAXIXHKBCGGDVSVSEVFVGVHULBCAGGGEVIVJVQGEVKV
      OVLVMVOVN $.
  $}

  ${
    $d w x y z A $.  $d x y z B $.  $d z C $.  $d u w x y z G $.
    $d u w x y z X $.  $d y U $.
    grpfo.1 $e |- X = ran G $.
    $( A group operation maps onto the group's underlying set.  (Contributed by
       NM, 30-Oct-2006.)  (New usage is discouraged.) $)
    grpofo $p |- ( G e. GrpOp -> G : ( X X. X ) -onto-> X ) $=
      ( vx vy vz vu cgr wcel cxp wf crn wceq wa wfo cv co wral wrex w3a isgrpo
      ibi simp1d eqcomi jctir dffo2 sylibr ) AHIZBBJZBAKZALZBMZNUIBAOUHUJULUHUJ
      DPZEPZAQFPZAQUMUNUOAQAQMFBREBRDBRZGPZUMAQUMMUNUMAQUQMEBSNDBRGBSZUHUJUPURT
      DEFGHABCUAUBUCBUKCUDUEUIBAUFUG $.

    $( Closure law for a group operation.  (Contributed by NM, 10-Oct-2006.)
       (New usage is discouraged.) $)
    grpocl $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) -> ( A G B ) e. X ) $=
      ( cgr wcel cxp wf co wfo grpofo fof syl fovcdm syl3an1 ) CFGZDDHZDCIZADGB
      DGABCJDGQRDCKSCDELRDCMNABDDDCOP $.

    $( A group has a left identity element, and every member has a left
       inverse.  (Contributed by NM, 2-Nov-2006.)
       (New usage is discouraged.) $)
    grpolidinv $p |- ( G e. GrpOp ->
         E. u e. X A. x e. X ( ( u G x ) = x /\ E. y e. X ( y G x ) = u ) ) $=
      ( vz cgr wcel cxp wf cv co wceq wral wrex wa w3a isgrpo ibi simp3d ) DHIZ
      EEJEDKZALZBLZDMGLZDMUDUEUFDMDMNGEOBEOAEOZCLZUDDMUDNUEUDDMUHNBEPQAEOCEPZUB
      UCUGUIRABGCHDEFSTUA $.

    $( The base set of a group is not empty.  (Contributed by Szymon
       Jaroszewicz, 3-Apr-2007.)  (New usage is discouraged.) $)
    grpon0 $p |- ( G e. GrpOp -> X =/= (/) ) $=
      ( vu vx vy cgr wcel cv co wceq wrex wa wral c0 wne grpolidinv rexn0 syl )
      AGHDIZEIZAJUAKFIUAAJTKFBLMEBNZDBLBOPEFDABCQUBDBRS $.

    $( A group operation is associative.  (Contributed by NM, 10-Oct-2006.)
       (New usage is discouraged.) $)
    grpoass $p |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
              ( ( A G B ) G C ) = ( A G ( B G C ) ) ) $=
      ( vx vy vz vu cgr wcel cv co wceq wral w3a oveq1 eqeq12d oveq2 wf wrex wa
      cxp isgrpo ibi simp2d oveq1d oveq2d rspc3v mpan9 ) DKLZGMZHMZDNZIMZDNZUMU
      NUPDNZDNZOZIEPHEPGEPZAELBELCELQABDNZCDNZABCDNZDNZOZULEEUDEDUAZVAJMZUMDNUM
      OUNUMDNVHOHEUBUCGEPJEUBZULVGVAVIQGHIJKDEFUEUFUGUTVFAUNDNZUPDNZAURDNZOVBUP
      DNZABUPDNZDNZOGHIABCEEEUMAOZUQVKUSVLVPUOVJUPDUMAUNDRUHUMAURDRSUNBOZVKVMVL
      VOVQVJVBUPDUNBADTUHVQURVNADUNBUPDRUISUPCOZVMVCVOVEUPCVBDTVRVNVDADUPCBDTUI
      SUJUK $.

    $( Lemma for ~ grpoidinv .  (Contributed by NM, 10-Oct-2006.)
       (New usage is discouraged.) $)
    grpoidinvlem1 $p |- ( ( ( G e. GrpOp /\ ( Y e. X /\ A e. X ) ) /\
                  ( ( Y G A ) = U /\ ( A G A ) = A ) ) -> ( U G A ) = U ) $=
      ( cgr wcel wa co wceq w3a id 3anidm23 grpoass sylan2 oveq1 ad2antrl oveq2
      adantr ad2antll simprl eqtrd 3eqtr3d ) CGHZEDHZADHZIZIZEACJZBKZAACJZAKZIZ
      IZUJACJZEULCJZBACJZBUIUPUQKZUNUHUEUFUGUGLZUSUFUGUTUTMNEAACDFOPTUKUPURKUIU
      MUJBACQRUOUQUJBUMUQUJKUIUKULAECSUAUIUKUMUBUCUD $.

    $( Lemma for ~ grpoidinv .  (Contributed by NM, 10-Oct-2006.)
       (New usage is discouraged.) $)
    grpoidinvlem2 $p |- ( ( ( G e. GrpOp /\ ( Y e. X /\ A e. X ) )
     /\ ( ( U G Y ) = Y /\ ( Y G A ) = U ) )
            -> ( ( A G Y ) G ( A G Y ) ) = ( A G Y ) ) $=
      ( cgr wcel wa co wceq w3a simprr simprl grpocl 3com23 3jca grpoass syldan
      3expb adantr oveq1 adantl simpl eqtr2d id 3anidm13 sylan2 sylan9eqr eqtrd
      eqcomd oveq2d ) CGHZEDHZADHZIZIZBECJZEKZEACJZBKZIZIZAECJZVDCJZAEVDCJZCJZV
      DUQVEVGKZVBUMUPUOUNVDDHZLVHUQUOUNVIUMUNUOMUMUNUONUMUNUOVIUMUOUNVIAECDFOPT
      QAEVDCDFRSUAVCVFEACVCEVFVBUQEUTECJZVFVBVJUREVAVJURKUSUTBECUBUCUSVAUDUEUPU
      MUNUOUNLZVJVFKUNUOVKVKUFUGEAECDFRUHUIUKULUJ $.

    ${
      $d w x y z U $.  $d w y ph $.  $d y ps $.
      grpidinvlem3.2 $e |- ( ph <-> A. x e. X ( U G x ) = x ) $.
      grpidinvlem3.3 $e |- ( ps <-> A. x e. X E. z e. X ( z G x ) = U ) $.
      $( Lemma for ~ grpoidinv .  (Contributed by NM, 11-Oct-2006.)
         (New usage is discouraged.) $)
      grpoidinvlem3 $p |- ( ( ( ( G e. GrpOp /\ U e. X ) /\ ( ph /\ ps ) ) /\
                  A e. X ) -> E. y e. X ( ( y G A ) = U /\ ( A G y ) = U ) ) $=
        ( vw wcel wa cv co wceq wrex wral cgr oveq1 eqeq1d cbvrexvw bitri oveq2
        ralbii rexbidv rspccva sylanb adantll grpocl adantllr ad2antrl ad2antrr
        3expa biimpi eqeq12d rspcva syl2anc adantr pm3.22 an31s adantlll anim1i
        id adantlr grpoidinvlem2 3expb ad2ant2rl sylan2b anass an32s syldan imp
        wi grpoidinvlem1 sylan exp43 rexlimdv syl5 mpand exp32 com34 imp32 impl
        ex mpd eqtr3d ancld reximdva ) HUANZGINZOZABOZOZFINZOZDPZFHQZGRZDISZXAF
        WSHQZGRZOZDISWOWQXBWNBWQXBABWSCPZHQZGRZDISZCITZWQXBBEPZXFHQZGRZEISZCITZ
        XJLXNXICIXMXHEDIXKWSRXLXGGXKWSXFHUBUCUDUGUEXIXBCFIXFFRZXHXADIXPXGWTGXFF
        WSHUFUCUHUIUJUKUKWRXAXEDIWRWSINZOZXAXDXRXAXDXRXAOZGXCHQZXCGXRXTXCRZXAXR
        XCINZGXFHQZXFRZCITZYAWNWQXQYBWOWLWQXQYBWMWLWQXQYBFWSHIJULZUPUMUMWPYEWQX
        QAYEWNBAYEKUQUNUOYDYACXCIXFXCRZYCXTXFXCXFXCGHUFYGVFURUSUTVAXSXCXCHQXCRZ
        XTGRZXSWLXQWQOZOZGWSHQZWSRZXAOYHXRYKXAWNWQXQYKWOWLWQXQYKWMXQWQWLYKYJWLV
        BVCUMUMVAXRYMXAWOWQXQYMWNWOXQYMWQAXQYMBAYEXQYMKYDYMCWSIXFWSRZYCYLXFWSXF
        WSGHUFYNVFURUIUJVGVGVDVEFGHIWSJVHUTXRYHYIVPZXAWPWQXQYOWNABWQXQOZYOVPWNA
        YPBYOWNAYPBYOVPWNAYPOOZYBBYOWLYPYBWMAWLWQXQYBYFVIZVJYBBOMPZXCHQZGRZMISZ
        YQYOBYBYSXFHQZGRZMISZCITZUUBBXOUUFLXNUUECIXMUUDEMIXKYSRXLUUCGXKYSXFHUBU
        CUDUGUEUUEUUBCXCIYGUUDUUAMIYGUUCYTGXFXCYSHUFUCUHUSVKYQUUAYOMIYQYSINZUUA
        YHYIYQUUGOWLUUGYBOOZUUAYHOYIYQUUGUUHWLYPUUGUUHVPZWMAWLYPYBUUIYRWLYBOUUG
        UUHWLUUGYBUUHWLUUGOYBOUUHWLUUGYBVLUQVMWGVNVJVOXCGHIYSJVQVRVSVTWAWBWCWDW
        EWFVAWHWIWGWJWKWH $.
    $}

    $( Lemma for ~ grpoidinv .  (Contributed by NM, 14-Oct-2006.)
       (New usage is discouraged.) $)
    grpoidinvlem4 $p |- ( ( ( G e. GrpOp /\ A e. X ) /\ E. y e. X
             ( ( y G A ) = U /\ ( A G y ) = U ) ) -> ( A G U ) = ( U G A ) ) $=
      ( cgr wcel wa cv wceq simpll simplr simpr grpoass syl13anc oveq2 sylan9eq
      co oveq1 sylan9req anasss r19.29an ) DGHZBEHZIZAJZBDSZCKZBUGDSZCKZIBCDSZC
      BDSZKZAEUFUGEHZIZUIUKUNUPUIIUKULUJBDSZUMUPUIUQBUHDSZULUPUDUEUOUEUQURKUDUE
      UOLUDUEUOMZUFUONUSBUGBDEFOPUHCBDQRUJCBDTUAUBUC $.

    $( A group has a left and right identity element, and every member has a
       left and right inverse.  (Contributed by NM, 14-Oct-2006.)
       (New usage is discouraged.) $)
    grpoidinv $p |- ( G e. GrpOp -> E. u e. X A. x e. X ( ( ( u G x ) = x /\
         ( x G u ) = x ) /\ E. y e. X ( ( y G x ) = u /\ ( x G y ) = u ) ) ) $=
      ( vz vw wcel cv co wceq wrex wa wral simpl ralimi id adantll adantl oveq2
      cgr eqeq12d rspccva sylan anim1i adantrr adantr ad2antlr simpr jca32 biid
      grpoidinvlem3 sylancom grpoidinvlem4 eqtrd ralrimiva grpolidinv reximddv
      syl2anc jca31 ) DUBIZCJZGJZDKZVDLZHJVDDKVCLHEMZNZGEOZVCAJZDKZVJLZVJVCDKZV
      JLZNBJZVJDKVCLVJVODKVCLNBEMZNZAEOCEVBVCEIZVINZNZVQAEVTVJEIZNZVLVNVPVSWAVL
      VBVIWAVLVRVIVFGEOZWAVLVHVFGEVFVGPQZVFVLGVJEVDVJLZVEVKVDVJVDVJVCDUAWERUCUD
      UESSZWBVMVKVJWBVBWANVPVMVKLVTVBWAVBVSPUFVTWAVBVRNZWCVGGEOZNNVPWBWGWCWHVTW
      GWAVBVRWGVIWGRUGUHVSWCVBWAVIWCVRWDTUIVSWHVBWAVIWHVRVHVGGEVFVGUJQTUIUKWCWH
      GBHVJVCDEFWCULWHULUMUNZBVJVCDEFUOUTWFUPWIVAUQGHCDEFURUS $.

    $( The left identity element of a group is unique.  Lemma 2.2.1(a) of
       [Herstein] p. 55.  (Contributed by NM, 14-Oct-2006.)
       (New usage is discouraged.) $)
    grpoideu $p |- ( G e. GrpOp -> E! u e. X A. x e. X ( u G x ) = x ) $=
      ( vw vz vy wcel cv co wceq wral weq wa wrex oveq2 id eqeq12d eqeq1d sylib
      cgr wi wreu grpoidinv simpll ralimi cbvralvw ad2antlr simpr oveq1 anbi12d
      adantl rexbidv rspcva adantll sylan2 grpoidinvlem4 syldan adantllr adantr
      an32s ad2ant2rl ad2ant2lr 3eqtr3d ex mpand ralrimiva jca reximdva ralbidv
      mpd reu8 sylibr ) CUBIZBJZAJZCKZVQLZADMZFJZVQCKZVQLZADMZBFNZUCZFDMZOZBDPZ
      VTBDUDVOVPGJZCKZWJLZWJVPCKWJLZOZHJZWJCKZVPLZWJWOCKZVPLZOZHDPZOZGDMZBDPWIG
      HBCDEUEVOXCWHBDVOVPDIZOZXCWHXEXCOZVTWGXCVTXEXCWLGDMVTXBWLGDWLWMXAUFUGWLVS
      GADGANZWKVRWJVQWJVQVPCQXGRSUHUAZUMXFWFFDXFWADIZOZVTWDWEXCVTXEXIXHUIXJVTWD
      OZWEXJXKOWAVPCKZVPWACKZVPWAXJXLXMLZXKVOXCXIXNXDVOXIXCXNVOXIOZXCWOWACKZVPL
      ZWAWOCKZVPLZOZHDPZXNXCXOXAGDMZYAXBXAGDWNXAUJUGXIYBYAVOXAYAGWADGFNZWTXTHDY
      CWQXQWSXSYCWPXPVPWJWAWOCQTYCWRXRVPWJWAWOCUKTULUNUOUPUQHWAVPCDEURUSVBUTVAX
      EXIXKXLVPLZXCXEWDYDXIVTXDWDYDVOWCYDAVPDABNZWBXLVQVPVQVPWACQYERSUOUPVCUTXI
      VTXMWALZXFWDVSYFAWADAFNZVRXMVQWAVQWAVPCQYGRSUOVDVEVFVGVHVIVFVJVLVTWDBFDWE
      VSWCADWEVRWBVQVPWAVQCUKTVKVMVN $.
  $}

  $( A group's range in terms of its domain.  (Contributed by NM, 6-Apr-2008.)
     (New usage is discouraged.) $)
  grporndm $p |- ( G e. GrpOp -> ran G = dom dom G ) $=
    ( cgr wcel crn cxp wfo cdm wceq eqid grpofo fof fdmd dmeqd dmxpid eqtr2di
    syl ) ABCADZQEZQAFZQAGZGZHAQQIJSUARGQSTRSRQARQAKLMQNOP $.

  $( The empty set is not a group.  (Contributed by NM, 25-Apr-2007.)
     (New usage is discouraged.) $)
  0ngrp $p |- -. (/) e. GrpOp $=
    ( c0 cgr wcel wne neirr crn rn0 eqcomi grpon0 mto ) ABCAADAEAAAFAGHIJ $.

  ${
    $d g u x G $.  $d g u x X $.
    gidval.1 $e |- X = ran G $.
    $( The value of the identity element of a group.  (Contributed by Mario
       Carneiro, 15-Dec-2013.)  (New usage is discouraged.) $)
    gidval $p |- ( G e. V -> ( GId ` G ) =
             ( iota_ u e. X A. x e. X ( ( u G x ) = x /\ ( x G u ) = x ) ) ) $=
      ( vg wcel cvv cgi cfv cv co wceq wa wral crio crn oveq eqeq1d riotaeqbidv
      elex rneq eqtr4di anbi12d raleqbidv df-gid riotaex fvmpt syl ) CDHCIHCJKB
      LZALZCMZULNZULUKCMZULNZOZAEPZBEQZNCDUBGCUKULGLZMZULNZULUKUTMZULNZOZAUTRZP
      ZBVFQUSIJUTCNZVGURBVFEVHVFCREUTCUCFUDZVHVEUQAVFEVIVHVBUNVDUPVHVAUMULUKULU
      TCSTVHVCUOULULUKUTCSTUEUFUAABGUGURBEUHUIUJ $.
  $}

  ${
    $d x y A $.  $d u x y G $.  $d u x y U $.  $d u x y X $.
    grpoidval.1 $e |- X = ran G $.
    grpoidval.2 $e |- U = ( GId ` G ) $.
    $( Lemma for ~ grpoidcl and others.  (Contributed by NM, 5-Feb-2010.)
       (Proof shortened by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoidval $p |- ( G e. GrpOp -> U =
                     ( iota_ u e. X A. x e. X ( u G x ) = x ) ) $=
      ( vy cgr wcel cgi cv co wceq wral crio wa wrex simpl ralimi cfv gidval wi
      wreu w3a rgenw a1i grpoidinv reximi syl grpoideu 3jca reupick2 riotabidva
      wb sylan eqtr4d eqtrid ) DIJZCDKUAZBLZALZDMVBNZAEOZBEPZGUSUTVCVBVADMVBNZQ
      ZAEOZBEPVEABDIEFUBUSVDVHBEUSVHVDUCZBEOZVHBERZVDBEUDZUEVAEJVDVHUOUSVJVKVLV
      JUSVIBEVGVCAEVCVFSTUFUGUSVGHLZVBDMVANVBVMDMVANQHERZQZAEOZBERVKAHBDEFUHVPV
      HBEVOVGAEVGVNSTUIUJABDEFUKULVDVHBEUMUPUNUQUR $.

    $( The identity element of a group belongs to the group.  (Contributed by
       NM, 24-Oct-2006.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoidcl $p |- ( G e. GrpOp -> U e. X ) $=
      ( vu vx cgr wcel cv co wceq wral crio grpoidval wreu grpoideu riotacl syl
      eqeltrd ) BHIZAFJGJZBKUBLGCMZFCNZCGFABCDEOUAUCFCPUDCIGFBCDQUCFCRST $.

    $( A group's properties using the explicit identity element.  (Contributed
       by NM, 5-Feb-2010.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoidinv2 $p |- ( ( G e. GrpOp /\ A e. X ) -> ( ( ( U G A ) = A /\
         ( A G U ) = A ) /\ E. y e. X ( ( y G A ) = U /\ ( A G y ) = U ) ) ) $=
      ( vx vu wcel cv co wceq wa wrex wral oveq1 eqeq1d oveq2 anbi12d crab crio
      cgr grpoidval grpoideu riotacl2 syl eqeltrd wi w3a wb simpll ralimi rgenw
      wreu grpoidinv 3jca reupick2 sylan rabbidva eleqtrd eqeq2 rexbidv ralbidv
      a1i elrab sylib simprd id eqeq12d rspccva ) DUCJZCHKZDLZVMMZVMCDLZVMMZNZA
      KZVMDLZCMZVMVSDLZCMZNZAEOZNZHEPZBEJCBDLZBMZBCDLZBMZNZVSBDLZCMZBVSDLZCMZNZ
      AEOZNZVLCEJZWGVLCIKZVMDLZVMMZVMXADLZVMMZNZVTXAMZWBXAMZNZAEOZNZHEPZIEUAZJW
      TWGNVLCXCHEPZIEUAZXMVLCXNIEUBZXOHICDEFGUDVLXNIEUOZXPXOJHIDEFUEZXNIEUFUGUH
      VLXNXLIEVLXLXNUIZIEPZXLIEOZXQUJXAEJXNXLUKVLXTYAXQXTVLXSIEXKXCHEXCXEXJULUM
      UNVEHAIDEFUPXRUQXNXLIEURUSUTVAXLWGICEXACMZXKWFHEYBXFVRXJWEYBXCVOXEVQYBXBV
      NVMXACVMDQRYBXDVPVMXACVMDSRTYBXIWDAEYBXGWAXHWCXACVTVBXACWBVBTVCTVDVFVGVHW
      FWSHBEVMBMZVRWLWEWRYCVOWIVQWKYCVNWHVMBVMBCDSYCVIZVJYCVPWJVMBVMBCDQYDVJTYC
      WDWQAEYCWAWNWCWPYCVTWMCVMBVSDSRYCWBWOCVMBVSDQRTVCTVKUS $.

    $( The identity element of a group is a left identity.  (Contributed by NM,
       24-Oct-2006.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpolid $p |- ( ( G e. GrpOp /\ A e. X ) -> ( U G A ) = A ) $=
      ( vy cgr wcel wa co wceq cv wrex grpoidinv2 simplld ) CHIADIJBACKALABCKAL
      GMZACKBLAQCKBLJGDNGABCDEFOP $.

    $( The identity element of a group is a right identity.  (Contributed by
       NM, 24-Oct-2006.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grporid $p |- ( ( G e. GrpOp /\ A e. X ) -> ( A G U ) = A ) $=
      ( vx cgr wcel wa co wceq cv wrex grpoidinv2 simplr syl ) CHIADIJBACKALZAB
      CKALZJGMZACKBLATCKBLJGDNZJSGABCDEFORSUAPQ $.
  $}

  ${
    $d y A $.  $d y B $.  $d y C $.  $d y G $.  $d y X $.
    grprcan.1 $e |- X = ran G $.
    $( Right cancellation law for groups.  (Contributed by NM, 26-Oct-2006.)
       (New usage is discouraged.) $)
    grporcan $p |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                  ( ( A G C ) = ( B G C ) <-> A = B ) ) $=
      ( vy wcel co wceq wrex adantl oveq1 grpoass adantrr 3eqtr3d oveq2 grporid
      wa ad2antrl cgr wb cv cgi cfv wi eqid grpoidinv2 simpr ad2ant2rl ad2antll
      reximi 3anassrs adantlrl 3exp2 adantllr adantrrl ad2antrr ad2ant2r adantr
      syl imp42 exp45 rexlimdv mpd impbid1 exp43 3imp2 ) DUAHZAEHZBEHZCEHZACDIZ
      BCDIZJZABJZUBZVIVJVKVLVQVIVJSZVKVLSZSZVOVPVTCGUCZDIZDUDUEZJZGEKZVOVPUFZVI
      VLWEVJVKVIVLSWCCDICJCWCDICJSZWACDIWCJZWDSZGEKZSWEGCWCDEFWCUGZUHWJWEWGWIWD
      GEWHWDUIULLVAUJVTWDWFGEVTWAEHZWDVOVPVTWLWDVOSSZSZAWCDIZBWCDIZABWNAWBDIZBW
      BDIZWOWPVTWLVOWQWRJWDVTWLVOSSVMWADIZVNWADIZWQWRVOWSWTJVTWLVMVNWADMUKVTWLW
      SWQJZVOVRVLWLXAVKVIVJVLWLXAACWADEFNUMUNOVTWLWTWRJZVOVIVSWLXBVJVIVKVLWLXBV
      IVKVLWLXBBCWADEFNUOVBUPOPUQWMWQWOJZVTWDXCWLVOWBWCADQTLWMWRWPJZVTWDXDWLVOW
      BWCBDQTLPVRWOAJVSWMAWCDEFWKRURVTWPBJZWMVIVKXEVJVLBWCDEFWKRUSUTPVCVDVEABCD
      MVFVGVH $.
  $}

  ${
    $d y z A $.  $d y z G $.  $d y z U $.  $d y z X $.
    grpoinveu.1 $e |- X = ran G $.
    grpoinveu.2 $e |- U = ( GId ` G ) $.
    $( The left inverse element of a group is unique.  Lemma 2.2.1(b) of
       [Herstein] p. 55.  (Contributed by NM, 27-Oct-2006.)
       (New usage is discouraged.) $)
    grpoinveu $p |- ( ( G e. GrpOp /\ A e. X ) -> E! y e. X ( y G A ) = U ) $=
      ( vz cgr wcel wa cv co wceq wi wral wrex wreu grpoidinv2 simpl reximi syl
      adantl w3a eqtr3 grporcan imbitrid 3exp2 com24 imp41 an32s expd ralrimdva
      ancld reximdva mpd oveq1 eqeq1d reu8 sylibr ) DIJZBEJZKZALZBDMZCNZHLZBDMZ
      CNZVDVGNZOZHEPZKZAEQZVFAERVCVFAEQZVNVCCBDMBNBCDMBNKZVFBVDDMCNZKZAEQZKVOAB
      CDEFGSVSVOVPVRVFAEVFVQTUAUCUBVCVFVMAEVCVDEJZKZVFVLWAVFVKHEWAVGEJZKVFVIVJV
      CWBVTVFVIKZVJOZVAVBWBVTWDVAVTWBVBWDVAVTWBVBWDWCVEVHNVAVTWBVBUDKVJVEVHCUEV
      DVGBDEFUFUGUHUIUJUKULUMUNUOUPVFVIAHEVJVEVHCVDVGBDUQURUSUT $.

    $( Two ways of saying that an element of a group is the identity element.
       (Contributed by Paul Chapman, 25-Feb-2008.)
       (New usage is discouraged.) $)
    grpoid $p |- ( ( G e. GrpOp /\ A e. X ) ->
                  ( A = U <-> ( A G A ) = A ) ) $=
      ( cgr wcel wa co wceq wb grpoidcl grporcan 3exp2 mpid pm2.43d imp grpolid
      wi eqeq2d bitr3d ) CGHZADHZIZAACJZBACJZKZABKZUFAKUCUDUHUILZUCUDUJUCUDBDHZ
      UDUJTBCDEFMUCUDUKUDUJABACDENOPQRUEUGAUFABCDEFSUAUB $.
  $}

  ${
    grprn.1 $e |- G e. GrpOp $.
    grprn.2 $e |- dom G = ( X X. X ) $.
    $( The range of a group operation.  Useful for satisfying group base set
       hypotheses of the form ` X = ran G ` .  (Contributed by NM, 5-Nov-2006.)
       (New usage is discouraged.) $)
    grporn $p |- X = ran G $=
      ( cxp wfn crn wceq wfun cdm cgr wcel wfo eqid grpofo fofun df-fn mpbir2an
      mp2b fofn wa fndmu xpid11 sylib mp2an ) ABBEZFZAAGZUHEZFZBUHHZUGAIZAJUFHA
      KLZUIUHAMZULCAUHUHNOZUIUHAPSDAUFQRUMUNUJCUOUIUHATSUGUJUAUFUIHUKUFUIAUBBUH
      UCUDUE $.
  $}

  ${
    $d x y A $.  $d g x y G $.  $d g x y X $.  $d g x U $.
    grpinvfval.1 $e |- X = ran G $.
    grpinvfval.2 $e |- U = ( GId ` G ) $.
    grpinvfval.3 $e |- N = ( inv ` G ) $.
    $( The inverse function of a group.  (Contributed by NM, 26-Oct-2006.)
       (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoinvfval $p |- ( G e. GrpOp -> N = ( x e. X |->
                     ( iota_ y e. X ( y G x ) = U ) ) ) $=
      ( vg cgr wcel cgn cfv cv co wceq crio cvv cgi cmpt crn rnexg eqeltrid syl
      mptexg rneq eqtr4di oveq fveq2 eqeq12d riotaeqbidv mpteq12dv fvmptg mpdan
      df-ginv eqtrid ) DKLZEDMNZAFBOZAOZDPZCQZBFRZUAZIURVESLZUSVEQURFSLVFURFDUB
      ZSGDKUCUDAFVDSUFUEJDAJOZUBZUTVAVHPZVHTNZQZBVIRZUAVEKSMVHDQZAVIVMFVDVNVIVG
      FVHDUGGUHZVNVLVCBVIFVOVNVJVBVKCUTVAVHDUIVNVKDTNCVHDTUJHUHUKULUMABJUPUNUOU
      Q $.

    $( The inverse of a group element.  (Contributed by NM, 26-Oct-2006.)
       (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoinvval $p |- ( ( G e. GrpOp /\ A e. X ) ->
                    ( N ` A ) = ( iota_ y e. X ( y G A ) = U ) ) $=
      ( vx cgr wcel cfv cv co wceq crio cmpt grpoinvfval fveq1d oveq2 riotabidv
      eqeq1d eqid riotaex fvmpt sylan9eq ) DKLZBFLBEMBJFANZJNZDOZCPZAFQZRZMUIBD
      OZCPZAFQZUHBEUNJACDEFGHISTJBUMUQFUNUJBPZULUPAFURUKUOCUJBUIDUAUCUBUNUDUPAF
      UEUFUG $.
  $}

  ${
    $d y A $.  $d y G $.  $d y X $.
    grpinvcl.1 $e |- X = ran G $.
    grpinvcl.2 $e |- N = ( inv ` G ) $.
    $( A group element's inverse is a group element.  (Contributed by NM,
       27-Oct-2006.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoinvcl $p |- ( ( G e. GrpOp /\ A e. X ) -> ( N ` A ) e. X ) $=
      ( vy cgr wcel wa cfv cv co cgi wceq crio eqid grpoinvval wreu grpoinveu
      riotacl syl eqeltrd ) BHIADIJZACKGLABMBNKZOZGDPZDGAUEBCDEUEQZFRUDUFGDSUGD
      IGAUEBDEUHTUFGDUAUBUC $.
  $}

  ${
    $d y A $.  $d y G $.  $d y N $.  $d y U $.  $d y X $.
    grpinv.1 $e |- X = ran G $.
    grpinv.2 $e |- U = ( GId ` G ) $.
    grpinv.3 $e |- N = ( inv ` G ) $.
    $( The properties of a group element's inverse.  (Contributed by NM,
       27-Oct-2006.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoinv $p |- ( ( G e. GrpOp /\ A e. X ) ->
                 ( ( ( N ` A ) G A ) = U /\ ( A G ( N ` A ) ) = U ) ) $=
      ( vy cgr wcel wa cfv co wceq cv crab crio simprd eqeq1d wreu riotacl2 syl
      grpoinvval grpoinveu eqeltrd wi wral wrex w3a simpl rgenw grpoidinv2 3jca
      wb a1i reupick2 sylan rabbidva eleqtrd oveq1 oveq2 anbi12d elrab sylib )
      CJKAEKLZADMZEKZVGACNZBOZAVGCNZBOZLZVFVGIPZACNZBOZAVNCNZBOZLZIEQZKVHVMLVFV
      GVPIEQZVTVFVGVPIERZWAIABCDEFGHUDVFVPIEUAZWBWAKIABCEFGUEZVPIEUBUCUFVFVPVSI
      EVFVSVPUGZIEUHZVSIEUIZWCUJVNEKVPVSUOVFWFWGWCWFVFWEIEVPVRUKULUPVFBACNAOABC
      NAOLWGIABCEFGUMSWDUNVPVSIEUQURUSUTVSVMIVGEVNVGOZVPVJVRVLWHVOVIBVNVGACVATW
      HVQVKBVNVGACVBTVCVDVES $.

    $( The left inverse of a group element.  (Contributed by NM, 27-Oct-2006.)
       (New usage is discouraged.) $)
    grpolinv $p |- ( ( G e. GrpOp /\ A e. X ) -> ( ( N ` A ) G A ) = U ) $=
      ( cgr wcel wa cfv co wceq grpoinv simpld ) CIJAEJKADLZACMBNAQCMBNABCDEFGH
      OP $.

    $( The right inverse of a group element.  (Contributed by NM, 27-Oct-2006.)
       (New usage is discouraged.) $)
    grporinv $p |- ( ( G e. GrpOp /\ A e. X ) -> ( A G ( N ` A ) ) = U ) $=
      ( cgr wcel wa cfv co wceq grpoinv simprd ) CIJAEJKADLZACMBNAQCMBNABCDEFGH
      OP $.

    $( The inverse of a group element expressed in terms of the identity
       element.  (Contributed by NM, 27-Oct-2006.)
       (New usage is discouraged.) $)
    grpoinvid1 $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
                    ( ( N ` A ) = B <-> ( A G B ) = U ) ) $=
      ( wcel w3a wceq co wa oveq2 adantl 3adant3 adantr eqtr3d syldan grpoinvcl
      cgr cfv grporinv grpolinv oveq1d adantrr simprl simprr 3jca grpoass 3impb
      grpolid 3adant2 grporid 3eqtr3rd impbida ) DUBJZAFJZBFJZKZAEUCZBLZABDMZCL
      ZVAVCNAVBDMZVDCVCVFVDLVAVBBADOPVAVFCLZVCURUSVGUTACDEFGHIUDQRSVAVENVBVDDMZ
      VBCDMZBVBVEVHVILVAVDCVBDOPVAVHBLVEVACBDMZVHBVAVBADMZBDMZVJVHURUSVLVJLUTUR
      USNVKCBDACDEFGHIUEUFQURUSUTVLVHLZURUSUTNZVBFJZUSUTKVMURVNNVOUSUTURUSVOUTA
      DEFGIUAZUGURUSUTUHURUSUTUIUJVBABDFGUKTULSURUTVJBLUSBCDFGHUMUNSRVAVIVBLZVE
      URUSVQUTURUSVOVQVPVBCDFGHUOTQRUPUQ $.

    $( The inverse of a group element expressed in terms of the identity
       element.  (Contributed by NM, 27-Oct-2006.)
       (New usage is discouraged.) $)
    grpoinvid2 $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
                    ( ( N ` A ) = B <-> ( B G A ) = U ) ) $=
      ( cgr wcel w3a wceq co wa oveq1 adantl 3adant3 adantr syldan cfv grpolinv
      eqtr3d grpoinvcl grpolid eqcomd simprr simprl adantrr 3jca 3impb grporinv
      grpoass oveq2d grporid 3adant2 3eqtrd 3eqtr2d impbida ) DJKZAFKZBFKZLZAEU
      AZBMZBADNZCMZVCVEOVDADNZVFCVEVHVFMVCVDBADPQVCVHCMZVEUTVAVIVBACDEFGHIUBRSU
      CVCVGOVDCVDDNZVFVDDNZBVCVDVJMVGVCVJVDUTVAVJVDMZVBUTVAVDFKZVLADEFGIUDZVDCD
      FGHUETRUFSVGVKVJMVCVFCVDDPQVCVKBMVGVCVKBAVDDNZDNZBCDNZBUTVAVBVKVPMZUTVAVB
      OZVBVAVMLVRUTVSOVBVAVMUTVAVBUGUTVAVBUHUTVAVMVBVNUIUJBAVDDFGUMTUKUTVAVPVQM
      VBUTVAOVOCBDACDEFGHIULUNRUTVBVQBMVABCDFGHUOUPUQSURUS $.
  $}

  ${
    grplcan.1 $e |- X = ran G $.
    $( Left cancellation law for groups.  (Contributed by NM, 27-Oct-2006.)
       (New usage is discouraged.) $)
    grpolcan $p |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                  ( ( C G A ) = ( C G B ) <-> A = B ) ) $=
      ( wcel w3a wa co wceq cfv oveq2 eqid adantlr oveq1d adantrl simprr adantr
      3eqtr3d cgr cgn adantl cgi grpolinv grpoinvcl simprl 3jca grpoass anassrs
      wi syldan grpolid adantrr exp53 3imp2 impbid1 ) DUAGZAEGZBEGZCEGZHICADJZC
      BDJZKZABKZURUSUTVAVDVEUKURUSUTVAVDVEURUSIZUTVAIZIZVDICDUBLZLZVBDJZVJVCDJZ
      ABVDVKVLKVHVBVCVJDMUCVHVKAKZVDVFVAVMUTVFVAIZVJCDJZADJZDUDLZADJZVKAVNVOVQA
      DURVAVOVQKZUSCVQDVIEFVQNZVINZUEZOPURUSVAVPVKKZURUSVAIZVJEGZVAUSHWCURWDIWE
      VAUSURVAWEUSCDVIEFWAUFZQURUSVARURUSVAUGUHVJCADEFUIULUJVFVRAKVAAVQDEFVTUMS
      TQSVHVLBKZVDURVGWGUSURVGIZVOBDJZVQBDJZVLBWHVOVQBDURVAVSUTWBQPURVGWEVAUTHW
      IVLKWHWEVAUTURVAWEUTWFQURUTVARURUTVAUGUHVJCBDEFUIULURUTWJBKVABVQDEFVTUMUN
      TOSTUOUPABCDMUQ $.
  $}

  ${
    $d x y G $.  $d x y N $.  $d x y X $.
    grpasscan1.1 $e |- X = ran G $.
    grpasscan1.2 $e |- N = ( inv ` G ) $.
    $( Double inverse law for groups.  Lemma 2.2.1(c) of [Herstein] p. 55.
       (Contributed by NM, 27-Oct-2006.)  (New usage is discouraged.) $)
    grpo2inv $p |- ( ( G e. GrpOp /\ A e. X ) -> ( N ` ( N ` A ) ) = A ) $=
      ( cgr wcel wa cfv wceq cgi grpoinvcl eqid grporinv syldan grpolinv eqtr4d
      co w3a wb simpr 3jca grpolcan mpbid ) BGHZADHZIZACJZUICJZBSZUIABSZKZUJAKZ
      UHUKBLJZULUFUGUIDHZUKUOKABCDEFMZUIUOBCDEUONZFOPAUOBCDEURFQRUFUGUJDHZUGUPT
      UMUNUAUHUSUGUPUFUGUPUSUQUIBCDEFMPUFUGUBUQUCUJAUIBDEUDPUE $.

    $( Mapping of the inverse function of a group.  (Contributed by NM,
       29-Mar-2008.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoinvf $p |- ( G e. GrpOp -> N : X -1-1-onto-> X ) $=
      ( vx vy cgr wcel wfn crn wceq cv cfv wral eqid grpoinvcl grpo2inv fveq2
      wa wi wf1o co cgi crio cmpt riotaex fnmpti grpoinvfval fneq1d mpbiri wrex
      cab fnrnfv syl eqcomd rspceeqv syl2anc ex simpr adantr eqeltrd rexlimdva2
      impbid eqabdv eqtr4d wb eqeqan12d anandis imbitrid ralrimivva syl3anbrc
      dff1o6 ) AHIZBCJZBKZCLFMZBNZGMZBNZLZVQVSLZUAZGCOFCOCCBUBVNVOFCVSVQAUCAUDN
      ZLZGCUEZUFZCJFCWFWGWEGCUGWGPUHVNCBWGFGWDABCDWDPEUIUJUKZVNVPVSVRLZFCULZGUM
      ZCVNVOVPWKLWHFGCBUNUOVNWJGCVNVSCIZWJVNWLWJVNWLTZVTCIVSVTBNZLWJVSABCDEQWMW
      NVSVSABCDERZUPFVTCVRWNVSVQVTBSUQURUSVNWIWLFCVNVQCIZTZWITVSVRCWQWIUTWQVRCI
      WIVQABCDEQVAVBVCVDVEVFVNWCFGCCWAVRBNZWNLZVNWPWLTTWBVRVTBSVNWPWLWSWBVGWQWM
      WRVQWNVSVQABCDERWOVHVIVJVKFGCCBVMVL $.

    $( The inverse of the group operation reverses the arguments.  Lemma
       2.2.1(d) of [Herstein] p. 55.  (Contributed by NM, 27-Oct-2006.)
       (New usage is discouraged.) $)
    grpoinvop $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
                   ( N ` ( A G B ) ) = ( ( N ` B ) G ( N ` A ) ) ) $=
      ( cgr wcel co cfv wceq grpoinvcl 3adant2 3adant3 syl3anc grpoass syl13anc
      grpocl grporinv w3a simp1 simp2 eqid oveq1d grpolid syldan 3eqtr3d oveq2d
      cgi simp3 3eqtrd wb grpoinvid1 mpbird ) CHIZAEIZBEIZUAZABCJZDKBDKZADKZCJZ
      LZUTVCCJZCUJKZLZUSVEABVCCJZCJZAVBCJZVFUSUPUQURVCEIZVEVILUPUQURUBZUPUQURUC
      UPUQURUKZUSUPVAEIZVBEIZVKVLUPURVNUQBCDEFGMNZUPUQVOURACDEFGMZOZVAVBCEFSPZA
      BVCCEFQRUSVHVBACUSBVACJZVBCJZVFVBCJZVHVBUSVTVFVBCUPURVTVFLUQBVFCDEFVFUDZG
      TNUEUSUPURVNVOWAVHLVLVMVPVRBVAVBCEFQRUPUQWBVBLZURUPUQVOWDVQVBVFCEFWCUFUGO
      UHUIUPUQVJVFLURAVFCDEFWCGTOULUSUPUTEIVKVDVGUMVLABCEFSVSUTVCVFCDEFWCGUNPUO
      $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d g x y G $.  $d g x y N $.  $d g x y X $.
    grpdiv.1 $e |- X = ran G $.
    grpdiv.2 $e |- N = ( inv ` G ) $.
    grpdiv.3 $e |- D = ( /g ` G ) $.
    $( Group division (or subtraction) operation.  (Contributed by NM,
       15-Feb-2008.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpodivfval $p |- ( G e. GrpOp -> D = ( x e. X , y e. X |->
                       ( x G ( N ` y ) ) ) ) $=
      ( vg cgr wcel cgs cfv cv co cmpo cvv wceq cgn rnexg eqeltrid mpoexga rneq
      crn syl2anc eqtr4di eqidd fveq2 fveq1d oveq123d mpoeq123dv df-gdiv fvmptg
      id mpdan eqtrid ) DKLZCDMNZABFFAOZBOZENZDPZQZIURVDRLZUSVDSURFRLZVFVEURFDU
      EZRGDKUAUBZVHABFFVCRRUCUFJDABJOZUEZVJUTVAVITNZNZVIPZQVDKRMVIDSZABVJVJVMFF
      VCVNVJVGFVIDUDGUGZVOVNUTUTVLVBVIDVNUOVNUTUHVNVAVKEVNVKDTNEVIDTUIHUGUJUKUL
      ABJUMUNUPUQ $.

    $( Group division (or subtraction) operation value.  (Contributed by NM,
       15-Feb-2008.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpodivval $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
                   ( A D B ) = ( A G ( N ` B ) ) ) $=
      ( vx vy cgr wcel co cfv wceq wa cv cmpo grpodivfval oveqd oveq1 eqid ovex
      fveq2 oveq2d ovmpo sylan9eq 3impb ) DLMZAFMZBFMZABCNZABEOZDNZPUJUKULQUMAB
      JKFFJRZKRZEOZDNZSZNUOUJCUTABJKCDEFGHITUAJKABFFUSUOUTAURDNUPAURDUBUQBPURUN
      ADUQBEUEUFUTUCAUNDUDUGUHUI $.

    $( Group division by an inverse.  (Contributed by NM, 15-Feb-2008.)
       (New usage is discouraged.) $)
    grpodivinv $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
                   ( A D ( N ` B ) ) = ( A G B ) ) $=
      ( cgr wcel w3a cfv co wceq grpoinvcl 3adant2 grpodivval syld3an3 grpo2inv
      oveq2d eqtrd ) DJKZAFKZBFKZLZABEMZCNZAUGEMZDNZABDNUCUDUEUGFKZUHUJOUCUEUKU
      DBDEFGHPQAUGCDEFGHIRSUFUIBADUCUEUIBOUDBDEFGHTQUAUB $.

    $( Inverse of a group division.  (Contributed by NM, 24-Feb-2008.)
       (New usage is discouraged.) $)
    grpoinvdiv $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
                   ( N ` ( A D B ) ) = ( B D A ) ) $=
      ( cgr wcel w3a co cfv grpodivval fveq2d wceq grpoinvcl 3adant2 grpoinvop
      syld3an3 grpo2inv oveq1d 3com23 eqtr4d 3eqtrd ) DJKZAFKZBFKZLZABCMZENABEN
      ZDMZENZULENZAENZDMZBACMZUJUKUMEABCDEFGHIOPUGUHUIULFKZUNUQQUGUIUSUHBDEFGHR
      SAULDEFGHTUAUJUQBUPDMZURUJUOBUPDUGUIUOBQUHBDEFGHUBSUCUGUIUHURUTQBACDEFGHI
      OUDUEUF $.
  $}

  ${
    $d x y G $.  $d x y X $.
    grpdivf.1 $e |- X = ran G $.
    grpdivf.3 $e |- D = ( /g ` G ) $.
    $( Mapping for group division.  (Contributed by NM, 10-Apr-2008.)  (Revised
       by Mario Carneiro, 15-Dec-2013.)  (New usage is discouraged.) $)
    grpodivf $p |- ( G e. GrpOp -> D : ( X X. X ) --> X ) $=
      ( vx vy cgr wcel cxp wf cv cgn cfv co cmpo wral eqid grpoinvcl 3adant2
      grpocl syld3an3 3expib ralrimivv fmpo sylib grpodivfval feq1d mpbird ) BH
      IZCCJZCAKUKCFGCCFLZGLZBMNZNZBOZPZKZUJUPCIZGCQFCQURUJUSFGCCUJULCIZUMCIZUSU
      JUTVAUOCIZUSUJVAVBUTUMBUNCDUNRZSTULUOBCDUAUBUCUDFGCCUPCUQUQRUEUFUJUKCAUQF
      GABUNCDVCEUGUHUI $.

    $( Closure of group division (or subtraction) operation.  (Contributed by
       NM, 15-Feb-2008.)  (New usage is discouraged.) $)
    grpodivcl $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) -> ( A D B ) e. X ) $=
      ( cgr wcel cxp wf co grpodivf fovcdm syl3an1 ) DHIEEJECKAEIBEIABCLEICDEFG
      MABEEECNO $.

    $( Double group division.  (Contributed by NM, 24-Feb-2008.)
       (New usage is discouraged.) $)
    grpodivdiv $p |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
         ( A D ( B D C ) ) = ( A G ( C D B ) ) ) $=
      ( cgr wcel w3a wa co cgn cfv wceq simpl simpr1 grpodivcl 3adant3r1 oveq2d
      eqid grpodivval syl3anc grpoinvdiv eqtrd ) EIJZAFJZBFJZCFJZKZLZABCDMZDMZA
      UMENOZOZEMZACBDMZEMULUGUHUMFJZUNUQPUGUKQUGUHUIUJRUGUIUJUSUHBCDEFGHSTAUMDE
      UOFGUOUBZHUCUDULUPURAEUGUIUJUPURPUHBCDEUOFGUTHUETUAUF $.

    $( Associative-type law for multiplication and division.  (Contributed by
       NM, 15-Feb-2008.)  (New usage is discouraged.) $)
    grpomuldivass $p |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
         ( ( A G B ) D C ) = ( A G ( B D C ) ) ) $=
      ( cgr wcel w3a wa co cgn cfv wceq simpr1 simpr2 eqid grpodivval grpoinvcl
      3ad2antr3 grpoass syldan grpocl 3adant3r3 simpr3 syl3anc 3adant3r1 oveq2d
      3jca simpl 3eqtr4d ) EIJZAFJZBFJZCFJZKZLZABEMZCENOZOZEMZABVBEMZEMZUTCDMZA
      BCDMZEMUNURUOUPVBFJZKVCVEPUSUOUPVHUNUOUPUQQUNUOUPUQRUNUOUQVHUPCEVAFGVASZU
      AUBUKABVBEFGUCUDUSUNUTFJZUQVFVCPUNURULUNUOUPVJUQABEFGUEUFUNUOUPUQUGUTCDEV
      AFGVIHTUHUSVGVDAEUNUPUQVGVDPUOBCDEVAFGVIHTUIUJUM $.

    ${
      grpdivid.3 $e |- U = ( GId ` G ) $.
      $( Division of a group member by itself.  (Contributed by NM,
         15-Feb-2008.)  (New usage is discouraged.) $)
      grpodivid $p |- ( ( G e. GrpOp /\ A e. X ) -> ( A D A ) = U ) $=
        ( cgr wcel wa co cgn cfv wceq eqid grpodivval 3anidm23 grporinv eqtrd )
        DIJZAEJZKAABLZAADMNZNDLZCUAUBUCUEOAABDUDEFUDPZGQRACDUDEFHUFST $.
    $}

    $( Cancellation law for group division.  ( ~ npcan analog.)  (Contributed
       by NM, 15-Feb-2008.)  (New usage is discouraged.) $)
    grponpcan $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
        ( ( A D B ) G B ) = A ) $=
      ( cgr wcel w3a co cgn cfv eqid grpodivval oveq1d wceq simp1 3adant2 eqtrd
      simp2 grpoinvcl simp3 grpoass syl13anc wa grpolinv oveq2d grporid 3adant3
      cgi ) DHIZAEIZBEIZJZABCKZBDKABDLMZMZDKZBDKZAUOUPUSBDABCDUQEFUQNZGOPUOUTAU
      RBDKZDKZAUOULUMUREIZUNUTVCQULUMUNRULUMUNUAULUNVDUMBDUQEFVAUBSULUMUNUCAURB
      DEFUDUEUOVCADUKMZDKZAULUNVCVFQUMULUNUFVBVEADBVEDUQEFVENZVAUGUHSULUMVFAQUN
      AVEDEFVGUIUJTTT $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Abelian groups
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c AbelOp $.

  $( Extend class notation with the class of all Abelian group operations. $)
  cablo $a class AbelOp $.

  ${
    $d g x y $.
    $( Define the class of all Abelian group operations.  (Contributed by NM,
       2-Nov-2006.)  (New usage is discouraged.) $)
    df-ablo $a |- AbelOp
     = { g e. GrpOp | A. x e. ran g A. y e. ran g ( x g y ) = ( y g x ) } $.
  $}

  ${
    $d g x y G $.  $d g x y X $.
    isabl.1 $e |- X = ran G $.
    $( The predicate "is an Abelian (commutative) group operation."
       (Contributed by NM, 2-Nov-2006.)  (New usage is discouraged.) $)
    isablo $p |- ( G e. AbelOp <-> ( G e. GrpOp /\
             A. x e. X A. y e. X ( x G y ) = ( y G x ) ) ) $=
      ( vg cv co wceq crn wral cgr cablo rneq eqtr4di raleq raleqbi1dv syl oveq
      wb eqeq12d 2ralbidv bitrd df-ablo elrab2 ) AGZBGZFGZHZUGUFUHHZIZBUHJZKZAU
      LKZUFUGCHZUGUFCHZIZBDKADKZFCLMUHCIZUNUKBDKZADKZURUSULDIUNVATUSULCJDUHCNEO
      UMUTAULDUKBULDPQRUSUKUQABDDUSUIUOUJUPUFUGUHCSUGUFUHCSUAUBUCABFUDUE $.
  $}

  ${
    $d x y G $.
    $( An Abelian group operation is a group operation.  (Contributed by NM,
       2-Nov-2006.)  (New usage is discouraged.) $)
    ablogrpo $p |- ( G e. AbelOp -> G e. GrpOp ) $=
      ( vx vy cablo wcel cgr cv co wceq crn wral eqid isablo simplbi ) ADEAFEBG
      ZCGZAHPOAHICAJZKBQKBCAQQLMN $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y G $.  $d x y X $.
    ablcom.1 $e |- X = ran G $.
    $( An Abelian group operation is commutative.  (Contributed by NM,
       2-Nov-2006.)  (New usage is discouraged.) $)
    ablocom $p |- ( ( G e. AbelOp /\ A e. X /\ B e. X ) ->
                 ( A G B ) = ( B G A ) ) $=
      ( vx vy cablo wcel co wceq cv wral cgr isablo simprbi oveq1 oveq2 eqeq12d
      wa rspc2v syl5com 3impib ) CHIZADIZBDIZABCJZBACJZKZUDFLZGLZCJZUKUJCJZKZGD
      MFDMZUEUFTUIUDCNIUOFGCDEOPUNUIAUKCJZUKACJZKFGABDDUJAKULUPUMUQUJAUKCQUJAUK
      CRSUKBKUPUGUQUHUKBACRUKBACQSUAUBUC $.

    $( Commutative/associative law for Abelian groups.  (Contributed by NM,
       26-Apr-2007.)  (New usage is discouraged.) $)
    ablo32 $p |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                 ( ( A G B ) G C ) = ( ( A G C ) G B ) ) $=
      ( cablo wcel w3a wa co wceq ablocom 3adant3r1 oveq2d cgr ablogrpo grpoass
      sylan 3ancomb sylan2b 3eqtr4d ) DGHZAEHZBEHZCEHZIZJZABCDKZDKZACBDKZDKZABD
      KCDKZACDKBDKZUHUIUKADUCUEUFUIUKLUDBCDEFMNOUCDPHZUGUMUJLDQZABCDEFRSUCUOUGU
      NULLZUPUGUOUDUFUEIUQUDUEUFTACBDEFRUASUB $.

    $( Commutative/associative law for Abelian groups.  (Contributed by NM,
       26-Apr-2007.)  (New usage is discouraged.) $)
    ablo4 $p |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X ) /\ ( C e. X /\
   D e. X ) ) -> ( ( A G B ) G ( C G D ) ) = ( ( A G C ) G ( B G D ) ) ) $=
      ( wcel wa wceq w3a simprlr simprrl 3jca syldan grpocl 3expb grpoass sylan
      co cablo simprll ablo32 oveq1d ablogrpo adantrr simprrr adantrlr adantrrr
      cgr 3eqtr3d 3impb ) EUAHZAFHZBFHZIZCFHZDFHZIZABETZCDETETZACETZBDETETZJUMU
      PUSIZIZUTCETZDETZVBBETZDETZVAVCVEVFVHDEUMVDUNUOUQKVFVHJVEUNUOUQUMUNUOUSUB
      UMUNUOUSLUMUPUQURMNABCEFGUCOUDUMEUJHZVDVGVAJZEUEZVJVDUTFHZUQURKVKVJVDIZVM
      UQURVJUPVMUSVJUNUOVMABEFGPQUFVJUPUQURMVJUPUQURUGZNUTCDEFGROSUMVJVDVIVCJZV
      LVJVDVBFHZUOURKVPVNVQUOURVJUPUQVQURVJUNUQVQUOVJUNUQVQACEFGPQUHUIVJUNUOUSL
      VONVBBDEFGROSUKUL $.
  $}

  ${
    $d x y G $.  $d x y X $.
    isabli.1 $e |- G e. GrpOp $.
    isabli.2 $e |- dom G = ( X X. X ) $.
    isabli.3 $e |- ( ( x e. X /\ y e. X ) -> ( x G y ) = ( y G x ) ) $.
    $( Properties that determine an Abelian group operation.  (Contributed by
       NM, 5-Nov-2006.)  (New usage is discouraged.) $)
    isabloi $p |- G e. AbelOp $=
      ( cablo wcel cgr cv co wceq wral rgen2 grporn isablo mpbir2an ) CHICJIAKZ
      BKZCLTSCLMZBDNADNEUAABDDGOABCDCDEFPQR $.
  $}

  ${
    abldiv.1 $e |- X = ran G $.
    abldiv.3 $e |- D = ( /g ` G ) $.
    $( Law for group multiplication and division.  (Contributed by NM,
       15-Feb-2008.)  (New usage is discouraged.) $)
    ablomuldiv $p |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
     ( ( A G B ) D C ) = ( ( A D C ) G B ) ) $=
      ( cablo wcel w3a wa co wceq ablocom 3adant3r3 oveq1d 3ancoma cgr ablogrpo
      grpomuldivass sylan sylan2b simpr2 grpodivcl syl3an1 3adant3r2 jca syldan
      3expb 3eqtrd ) EIJZAFJZBFJZCFJZKZLZABEMZCDMBAEMZCDMZBACDMZEMZVABEMZUQURUS
      CDULUMUNURUSNUOABEFGOPQUPULUNUMUOKZUTVBNZUMUNUORULESJZVDVEETZBACDEFGHUAUB
      UCULUPUNVAFJZLVBVCNZUQUNVHULUMUNUOUDULUMUOVHUNULVFUMUOVHVGACDEFGHUEUFUGUH
      ULUNVHVIBVAEFGOUJUIUK $.

    $( Law for double group division.  (Contributed by NM, 29-Feb-2008.)
       (New usage is discouraged.) $)
    ablodivdiv $p |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
    ( A D ( B D C ) ) = ( ( A D B ) G C ) ) $=
      ( cablo wcel w3a wa co cgr wceq ablogrpo grpodivdiv 3ancomb grpomuldivass
      sylan ablomuldiv eqtr3d sylan2b eqtrd ) EIJZAFJZBFJZCFJZKZLABCDMDMZACBDME
      MZABDMCEMZUEENJZUIUJUKOEPZABCDEFGHQTUIUEUFUHUGKZUKULOUFUGUHRUEUOLACEMBDMZ
      UKULUEUMUOUPUKOUNACBDEFGHSTACBDEFGHUAUBUCUD $.

    $( Law for double group division.  (Contributed by NM, 29-Feb-2008.)
       (New usage is discouraged.) $)
    ablodivdiv4 $p |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
    ( ( A D B ) D C ) = ( A D ( B G C ) ) ) $=
      ( cablo wcel w3a wa co cgn cfv cgr wceq ablogrpo simpl grpodivcl syl3anc
      3adant3r3 simpr3 eqid grpodivval sylan simpr1 simpr2 simp3 grpoinvcl 3jca
      syl2an ablodivdiv syldan grpodivinv syl3an1 3adant3r1 oveq2d 3eqtr2d ) EI
      JZAFJZBFJZCFJZKZLZABDMZCDMZVFCENOZOZEMZABVIDMZDMZABCEMZDMUTEPJZVDVGVJQZER
      ZVNVDLVNVFFJZVCVOVNVDSVNVAVBVQVCABDEFGHTUBVNVAVBVCUCVFCDEVHFGVHUDZHUEUAUF
      UTVDVAVBVIFJZKVLVJQVEVAVBVSUTVAVBVCUGUTVAVBVCUHUTVNVCVSVDVPVAVBVCUICEVHFG
      VRUJULUKABVIDEFGHUMUNVEVKVMADUTVBVCVKVMQZVAUTVNVBVCVTVPBCDEVHFGVRHUOUPUQU
      RUS $.

    $( Swap the second and third terms in a double division.  (Contributed by
       NM, 29-Feb-2008.)  (New usage is discouraged.) $)
    ablodiv32 $p |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
   ( ( A D B ) D C ) = ( ( A D C ) D B ) ) $=
      ( cablo wcel w3a wa co wceq ablocom 3adant3r1 ablodivdiv4 3ancomb sylan2b
      oveq2d 3eqtr4d ) EIJZAFJZBFJZCFJZKZLZABCEMZDMACBEMZDMZABDMCDMACDMBDMZUGUH
      UIADUBUDUEUHUINUCBCEFGOPTABCDEFGHQUFUBUCUEUDKUKUJNUCUDUERACBDEFGHQSUA $.

    $( Cancellation law for group division.  ( ~ nncan analog.)  (Contributed
       by NM, 7-Mar-2008.)  (New usage is discouraged.) $)
    ablonncan $p |- ( ( G e. AbelOp /\ A e. X /\ B e. X ) ->
             ( A D ( A D B ) ) = B ) $=
      ( cablo wcel w3a co cgi cfv wceq wa id 3anidm12 ablodivdiv sylan2 sylan
      3impb cgr ablogrpo eqid grpodivid 3adant3 oveq1d grpolid 3adant2 3eqtrd )
      DHIZAEIZBEIZJZAABCKCKZAACKZBDKZDLMZBDKZBUKULUMUOUQNZULUMOUKULULUMJZUTULUM
      VAVAPQAABCDEFGRSUAUNUPURBDUKULUPURNZUMUKDUBIZULVBDUCZACURDEFGURUDZUETUFUG
      UKUMUSBNZULUKVCUMVFVDBURDEFVEUHTUIUJ $.

    $( Cancellation law for group division.  ( ~ nnncan1 analog.)  (Contributed
       by NM, 7-Mar-2008.)  (New usage is discouraged.) $)
    ablonnncan1 $p |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
         ( ( A D B ) D ( A D C ) ) = ( C D B ) ) $=
      ( cablo wcel w3a wa wceq simpr1 simpr2 cgr ablogrpo grpodivcl 3adant3r2
      co syl3an1 3jca ablodiv32 syldan ablonncan oveq1d eqtrd ) EIJZAFJZBFJZCFJ
      ZKZLZABDTACDTZDTZAUNDTZBDTZCBDTUHULUIUJUNFJZKUOUQMUMUIUJURUHUIUJUKNUHUIUJ
      UKOUHUIUKURUJUHEPJUIUKUREQACDEFGHRUASUBABUNDEFGHUCUDUMUPCBDUHUIUKUPCMUJAC
      DEFGHUESUFUG $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Complex vector spaces
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definition and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c CVecOLD $.

  $( Extend class notation with the class of all complex vector spaces. $)
  cvc $a class CVecOLD $.

  ${
    $d g s x y z $.
    $( Define the class of all complex vector spaces.  (Contributed by NM,
       3-Nov-2006.)  (New usage is discouraged.) $)
    df-vc $a |- CVecOLD = { <. g , s >. | ( g e. AbelOp /\
     s : ( CC X. ran g ) --> ran g /\ A. x e. ran g ( ( 1 s x ) = x /\
       A. y e. CC ( A. z e. ran g ( y s ( x g z ) ) = ( ( y s x ) g ( y s z ) )
         /\ A. z e. CC ( ( ( y + z ) s x ) = ( ( y s x ) g ( z s x ) ) /\
           ( ( y x. z ) s x ) = ( y s ( z s x ) ) ) ) ) ) } $.

    $( The class of all complex vector spaces is a relation.  (Contributed by
       NM, 17-Mar-2007.)  (New usage is discouraged.) $)
    vcrel $p |- Rel CVecOLD $=
      ( vg vs vx vy vz cv cablo wcel cc crn cxp wf c1 co wceq wral caddc wa w3a
      cmul cvc df-vc relopabiv ) AFZGHIUDJZKUEBFZLMCFZUFNUGODFZUGEFZUDNUFNUHUGU
      FNZUHUIUFNUDNOEUEPUHUIQNUGUFNUJUIUGUFNZUDNOUHUITNUGUFNUHUKUFNOREIPRDIPRCU
      EPSABUACDEABUBUC $.
  $}

  ${
    $d g s x y z G $.  $d g s x y z S $.  $d g s W $.  $d g s x y z X $.
    $d x y z A $.  $d x y z B $.  $d x y z C $.
    vciOLD.1 $e |- G = ( 1st ` W ) $.
    vciOLD.2 $e |- S = ( 2nd ` W ) $.
    vciOLD.3 $e |- X = ran G $.
    $( Obsolete version of ~ cvsi .  The properties of a complex vector space,
       which is an Abelian group (i.e. the vectors, with the operation of
       vector addition) accompanied by a scalar multiplication operation on the
       field of complex numbers.  The variable ` W ` was chosen because ` _V `
       is already used for the universal class.  (Contributed by NM,
       3-Nov-2006.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    vciOLD $p |- ( W e. CVecOLD ->
              ( G e. AbelOp /\
         S : ( CC X. X ) --> X /\ A. x e. X ( ( 1 S x ) = x /\
       A. y e. CC ( A. z e. X ( y S ( x G z ) ) = ( ( y S x ) G ( y S z ) )
         /\ A. z e. CC ( ( ( y + z ) S x ) = ( ( y S x ) G ( z S x ) ) /\
           ( ( y x. z ) S x ) = ( y S ( z S x ) ) ) ) ) ) ) $=
      ( vg vs cc cv co wceq wral wa oveq ralbidv cablo wcel cxp wf c1 caddc w3a
      cmul crn copab cvc c1st cfv wb eqeq2i eleq1 rneq eqtr4di xpeq2 feq2d feq3
      bitrd syl oveq2d eqeq12d raleqbidv eqeq2d anbi1d anbi12d anbi2d 3anbi123d
      sylbir c2nd feq1 eqeq1d oveq12d eqtrd 3anbi23d elopabi df-vc eleq2s ) EUA
      UBZMGUCZGDUDZUEANZDOZWEPZBNZWECNZEOZDOZWHWEDOZWHWIDOZEOZPZCGQZWHWIUFOZWED
      OZWLWIWEDOZEOZPZWHWIUHOZWEDOZWHWSDOZPZRZCMQZRZBMQZRZAGQZUGZFKNZUAUBZMXMUI
      ZUCZXOLNZUDZUEWEXQOZWEPZWHWEWIXMOZXQOZWHWEXQOZWHWIXQOZXMOZPZCXOQZWQWEXQOZ
      YCWIWEXQOZXMOZPZXBWEXQOZWHYIXQOZPZRZCMQZRZBMQZRZAXOQZUGZKLUJUKUUAWBWCGXQU
      DZXTWHWJXQOZYCYDEOZPZCGQZYHYCYIEOZPZYNRZCMQZRZBMQZRZAGQZUGZXLKLFXMFULUMZP
      XMEPZUUAUUOUNEUUPXMHUOUUQXNWBXRUUBYTUUNXMEUAUPUUQXOGPZXRUUBUNUUQXOEUIGXME
      UQJURZUURXRWCXOXQUDUUBUURXPWCXOXQXOGMUSUTXOGWCXQVAVBVCUUQYSUUMAXOGUUSUUQY
      RUULXTUUQYQUUKBMUUQYGUUFYPUUJUUQYFUUECXOGUUSUUQYBUUCYEUUDUUQYAWJWHXQWEWIX
      MESVDYCYDXMESVEVFUUQYOUUICMUUQYKUUHYNUUQYJUUGYHYCYIXMESVGVHTVITVJVFVKVLXQ
      FVMUMZPXQDPZUUOXLUNDUUTXQIUOUVAUUBWDUUNXKWBWCGXQDVNUVAUUMXJAGUVAXTWGUULXI
      UVAXSWFWEUEWEXQDSVOUVAUUKXHBMUVAUUFWPUUJXGUVAUUEWOCGUVAUUCWKUUDWNWHWJXQDS
      UVAYCWLYDWMEWHWEXQDSZWHWIXQDSVPVETUVAUUIXFCMUVAUUHXAYNXEUVAYHWRUUGWTWQWEX
      QDSUVAYCWLYIWSEUVBWIWEXQDSZVPVEUVAYLXCYMXDXBWEXQDSUVAYMWHWSXQOXDUVAYIWSWH
      XQUVCVDWHWSXQDSVQVEVITVITVITVRVLVSABCKLVTWA $.

    $( Functionality of th scalar product of a complex vector space.
       (Contributed by NM, 3-Nov-2006.)  (New usage is discouraged.) $)
    vcsm $p |- ( W e. CVecOLD -> S : ( CC X. X ) --> X ) $=
      ( vx vy vz cvc wcel cablo cc cxp cv co wceq wral wa wf cmul vciOLD simp2d
      c1 caddc ) CKLBMLNDODAUAUEHPZAQUGRIPZUGJPZBQAQUHUGAQZUHUIAQBQRJDSUHUIUFQU
      GAQUJUIUGAQZBQRUHUIUBQUGAQUHUKAQRTJNSTINSTHDSHIJABCDEFGUCUD $.

    $( Closure of the scalar product of a complex vector space.  (Contributed
       by NM, 3-Nov-2006.)  (New usage is discouraged.) $)
    vccl $p |- ( ( W e. CVecOLD /\ A e. CC /\ B e. X ) -> ( A S B ) e. X ) $=
      ( cvc wcel cc cxp wf co vcsm fovcdm syl3an1 ) EJKLFMFCNALKBFKABCOFKCDEFGH
      IPABFLFCQR $.

    $( Identity element for the scalar product of a complex vector space.
       (Contributed by NM, 3-Nov-2006.)  Obsolete theorem, use ~ clmvs1
       together with ~ cvsclm instead.  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    vcidOLD $p |- ( ( W e. CVecOLD /\ A e. X ) -> ( 1 S A ) = A ) $=
      ( vx vy vz cvc wcel c1 cv co wceq wral cc wa cablo cxp wf cmul w3a vciOLD
      caddc simpl ralimi 3ad2ant3 syl oveq2 id eqeq12d rspccva sylan ) DLMZNIOZ
      BPZURQZIERZAEMNABPZAQZUQCUAMZSEUBEBUCZUTJOZURKOZCPBPVFURBPZVFVGBPCPQKERVF
      VGUGPURBPVHVGURBPZCPQVFVGUDPURBPVFVIBPQTKSRTJSRZTZIERZUEVAIJKBCDEFGHUFVLV
      DVAVEVKUTIEUTVJUHUIUJUKUTVCIAEURAQZUSVBURAURANBULVMUMUNUOUP $.

    $( Distributive law for the scalar product of a complex vector space.
       (Contributed by NM, 3-Nov-2006.)  (New usage is discouraged.) $)
    vcdi $p |- ( ( W e. CVecOLD /\ ( A e. CC /\ B e. X /\ C e. X ) ) ->
       ( A S ( B G C ) ) = ( ( A S B ) G ( A S C ) ) ) $=
      ( vy vx vz cc wcel w3a co wceq wral oveq1 cvc wi cv cablo cxp wf c1 caddc
      cmul vciOLD simpl ralimi adantl 3ad2ant3 syl oveq2d oveq2 eqeq12d oveq12d
      wa oveq1d rspc3v syl5 3com12 impcom ) ANOZBGOZCGOZPFUAOZABCEQZDQZABDQZACD
      QZEQZRZVGVFVHVIVOUBVIKUCZLUCZMUCZEQZDQZVPVQDQZVPVRDQZEQZRZMGSZKNSZLGSZVGV
      FVHPVOVIEUDOZNGUEGDUFZUGVQDQVQRZWEVPVRUHQVQDQWAVRVQDQZEQRVPVRUIQVQDQVPWKD
      QRUTMNSZUTZKNSZUTZLGSZPWGLKMDEFGHIJUJWPWHWGWIWOWFLGWNWFWJWMWEKNWEWLUKULUM
      ULUNUOWDVOVPBVREQZDQZVPBDQZWBEQZRAWQDQZVLAVRDQZEQZRLKMBACGNGVQBRZVTWRWCWT
      XDVSWQVPDVQBVRETUPXDWAWSWBEVQBVPDUQVAURVPARZWRXAWTXCVPAWQDTXEWSVLWBXBEVPA
      BDTVPAVRDTUSURVRCRZXAVKXCVNXFWQVJADVRCBEUQUPXFXBVMVLEVRCADUQUPURVBVCVDVE
      $.

    $( Distributive law for the scalar product of a complex vector space.
       (Contributed by NM, 3-Nov-2006.)  (New usage is discouraged.) $)
    vcdir $p |- ( ( W e. CVecOLD /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
      ( ( A + B ) S C ) = ( ( A S C ) G ( B S C ) ) ) $=
      ( vy vz vx cc wcel caddc co wceq wral oveq2 w3a cvc wi cv cablo cxp wf c1
      cmul vciOLD simpl ralimi adantl 3ad2ant3 syl oveq12d eqeq12d oveq1 oveq1d
      wa oveq2d rspc3v syl5 3coml impcom ) ANOZBNOZCGOZUAFUBOZABPQZCDQZACDQZBCD
      QZEQZRZVHVFVGVIVOUCVIKUDZLUDZPQZMUDZDQZVPVSDQZVQVSDQZEQZRZLNSZKNSZMGSZVHV
      FVGUAVOVIEUEOZNGUFGDUGZUHVSDQVSRZVPVSVQEQDQWAVPVQDQEQRLGSZWDVPVQUIQVSDQVP
      WBDQRZUTZLNSZUTZKNSZUTZMGSZUAWGMKLDEFGHIJUJWRWHWGWIWQWFMGWPWFWJWOWEKNWNWE
      WKWMWDLNWDWLUKULUMULUMULUNUOWDVOVRCDQZVPCDQZVQCDQZEQZRAVQPQZCDQZVLXAEQZRM
      KLCABGNNVSCRZVTWSWCXBVSCVRDTXFWAWTWBXAEVSCVPDTVSCVQDTUPUQVPARZWSXDXBXEXGV
      RXCCDVPAVQPURUSXGWTVLXAEVPACDURUSUQVQBRZXDVKXEVNXHXCVJCDVQBAPTUSXHXAVMVLE
      VQBCDURVAUQVBVCVDVE $.

    $( Associative law for the scalar product of a complex vector space.
       (Contributed by NM, 3-Nov-2006.)  (New usage is discouraged.) $)
    vcass $p |- ( ( W e. CVecOLD /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
      ( ( A x. B ) S C ) = ( A S ( B S C ) ) ) $=
      ( vy vz vx cc wcel w3a cmul co wceq wral cvc wi cv cablo cxp wf c1 vciOLD
      caddc simpr ralimi adantl 3ad2ant3 syl oveq2 oveq2d eqeq12d oveq1d rspc3v
      wa oveq1 syl5 3coml impcom ) ANOZBNOZCGOZPFUAOZABQRZCDRZABCDRZDRZSZVGVEVF
      VHVMUBVHKUCZLUCZQRZMUCZDRZVNVOVQDRZDRZSZLNTZKNTZMGTZVGVEVFPVMVHEUDOZNGUEG
      DUFZUGVQDRVQSZVNVQVOERDRVNVQDRZVNVODRERSLGTZVNVOUIRVQDRWHVSERSZWAUTZLNTZU
      TZKNTZUTZMGTZPWDMKLDEFGHIJUHWPWEWDWFWOWCMGWNWCWGWMWBKNWLWBWIWKWALNWJWAUJU
      KULUKULUKUMUNWAVMVPCDRZVNVOCDRZDRZSAVOQRZCDRZAWRDRZSMKLCABGNNVQCSZVRWQVTW
      SVQCVPDUOXCVSWRVNDVQCVODUOUPUQVNASZWQXAWSXBXDVPWTCDVNAVOQVAURVNAWRDVAUQVO
      BSZXAVJXBVLXEWTVICDVOBAQUOURXEWRVKADVOBCDVAUPUQUSVBVCVD $.

    $( A vector plus itself is two times the vector.  (Contributed by NM,
       1-Feb-2007.)  Obsolete theorem, use ~ clmvs2 together with ~ cvsclm
       instead.  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    vc2OLD $p |- ( ( W e. CVecOLD /\ A e. X ) -> ( A G A ) = ( 2 S A ) ) $=
      ( cvc wcel wa c1 co c2 vcidOLD oveq12d caddc df-2 oveq1i ax-1cn cc mpanr1
      wceq vcdir mp3anr1 eqtr2id eqtr3d ) DIJZAEJZKZLABMZUKCMZAACMNABMZUJUKAUKA
      CABCDEFGHOZUNPUJUMLLQMZABMZULNUOABRSUHLUAJZUIUPULUCZTUHUQUQUIURTLLABCDEFG
      HUDUEUBUFUG $.
  $}

  ${
    $d x y z G $.  $d x y z W $.
    vcabl.1 $e |- G = ( 1st ` W ) $.
    $( Vector addition is an Abelian group operation.  (Contributed by NM,
       3-Nov-2006.)  (New usage is discouraged.) $)
    vcablo $p |- ( W e. CVecOLD -> G e. AbelOp ) $=
      ( vx vy vz cvc wcel cablo cc crn cxp c2nd cfv cv co wceq wral wa eqid wf
      c1 caddc cmul vciOLD simp1d ) BGHAIHJAKZLUGBMNZUAUBDOZUHPUIQEOZUIFOZAPUHP
      UJUIUHPZUJUKUHPAPQFUGRUJUKUCPUIUHPULUKUIUHPZAPQUJUKUDPUIUHPUJUMUHPQSFJRSE
      JRSDUGRDEFUHABUGCUHTUGTUEUF $.

    $( Vector addition is a group operation.  (Contributed by NM, 4-Nov-2006.)
       (New usage is discouraged.) $)
    vcgrp $p |- ( W e. CVecOLD -> G e. GrpOp ) $=
      ( cvc wcel cablo cgr vcablo ablogrpo syl ) BDEAFEAGEABCHAIJ $.
  $}

  ${
    vclcan.1 $e |- G = ( 1st ` W ) $.
    vclcan.2 $e |- X = ran G $.
    $( Left cancellation law for vector addition.  (Contributed by NM,
       4-Nov-2006.)  (New usage is discouraged.) $)
    vclcan $p |- ( ( W e. CVecOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                  ( ( C G A ) = ( C G B ) <-> A = B ) ) $=
      ( cvc wcel cgr w3a co wceq wb vcgrp grpolcan sylan ) EIJDKJAFJBFJCFJLCADM
      CBDMNABNODEGPABCDFHQR $.
  $}

  ${
    vczcl.1 $e |- G = ( 1st ` W ) $.
    vczcl.2 $e |- X = ran G $.
    vczcl.3 $e |- Z = ( GId ` G ) $.
    $( The zero vector is a vector.  (Contributed by NM, 4-Nov-2006.)
       (New usage is discouraged.) $)
    vczcl $p |- ( W e. CVecOLD -> Z e. X ) $=
      ( cvc wcel cgr vcgrp grpoidcl syl ) BHIAJIDCIABEKDACFGLM $.

    $( The zero vector is a right identity element.  (Contributed by NM,
       4-Nov-2006.)  (New usage is discouraged.) $)
    vc0rid $p |- ( ( W e. CVecOLD /\ A e. X ) -> ( A G Z ) = A ) $=
      ( cvc wcel cgr co wceq vcgrp grporid sylan ) CIJBKJADJAEBLAMBCFNAEBDGHOP
      $.
  $}

  ${
    vc0.1 $e |- G = ( 1st ` W ) $.
    vc0.2 $e |- S = ( 2nd ` W ) $.
    vc0.3 $e |- X = ran G $.
    vc0.4 $e |- Z = ( GId ` G ) $.
    $( Zero times a vector is the zero vector.  Equation 1a of [Kreyszig]
       p. 51.  (Contributed by NM, 4-Nov-2006.)  (New usage is discouraged.) $)
    vc0 $p |- ( ( W e. CVecOLD /\ A e. X ) -> ( 0 S A ) = Z ) $=
      ( cvc wcel wa cc0 co wceq c1 vc0rid cc 0cn oveq1i mp3anr1 vcidOLD 3eqtr3a
      caddc 1p0e1 ax-1cn vcdir mpanr1 oveq1d 3eqtr2rd w3a wb vccl mp3an2 adantr
      vczcl simpr 3jca vclcan syldan mpbid ) DKLZAELZMZANABOZCOZAFCOZPZVFFPZVEV
      HAQABOZVFCOZVGACDEFGIJRVEQNUEOZABOZVKVLAVMQABUFUAVCNSLZVDVNVLPZTVCQSLVOVD
      VPUGQNABCDEGHIUHUBUIABCDEGHIUCZUDVEVKAVFCVQUJUKVCVDVFELZFELZVDULVIVJUMVEV
      RVSVDVCVOVDVRTNABCDEGHIUNUOVCVSVDCDEFGIJUQUPVCVDURUSVFFACDEGIUTVAVB $.

    $( Anything times the zero vector is the zero vector.  Equation 1b of
       [Kreyszig] p. 51.  (Contributed by NM, 24-Nov-2006.)
       (New usage is discouraged.) $)
    vcz $p |- ( ( W e. CVecOLD /\ A e. CC ) -> ( A S Z ) = Z ) $=
      ( cvc wcel cc wa cc0 cmul co wceq vczcl anim2i ancoms vcass mp3anr2 mul01
      0cn syldan oveq1d vc0 mpdan sylan9eqr oveq2d adantr 3eqtr3rd ) DKLZAMLZNA
      OPQZFBQZAOFBQZBQZFAFBQZUNUOUOFELZNZUQUSRZUOUNVBUNVAUOCDEFGIJSZTUAUNUOOMLV
      AVCUEAOFBCDEGHIUBUCUFUOUNUQURFUOUPOFBAUDUGUNVAURFRVDFBCDEFGHIJUHUIZUJUNUS
      UTRUOUNURFABVEUKULUM $.
  $}

  ${
    vcm.1 $e |- G = ( 1st ` W ) $.
    vcm.2 $e |- S = ( 2nd ` W ) $.
    vcm.3 $e |- X = ran G $.
    vcm.4 $e |- M = ( inv ` G ) $.
    $( Minus 1 times a vector is the underlying group's inverse element.
       Equation 2 of [Kreyszig] p. 51.  (Contributed by NM, 25-Nov-2006.)
       (New usage is discouraged.) $)
    vcm $p |- ( ( W e. CVecOLD /\ A e. X ) -> ( -u 1 S A ) = ( M ` A ) ) $=
      ( wcel c1 co cfv wceq cc neg1cn syl2anc cc0 eqtr3d cvc cneg cgi cgr vcgrp
      wa adantr vccl mp3an2 eqid grporid simpr grpoinvcl sylan grpoass syl13anc
      vcidOLD oveq2d caddc ax-1cn 1pneg1e0 addcomli oveq1i vcdir mp3anr1 mpanr1
      vc0 3eqtr3a oveq1d grporinv grpolid ) EUAKZAFKZUFZLUBZABMZCUCNZCMZVPADNZV
      NCUDKZVPFKZVRVPOVLVTVMCEGUEZUGZVLVOPKZVMWAQVOABCEFGHIUHUIZVPVQCFIVQUJZUKR
      VNVQVSCMZVRVSVNVPAVSCMZCMZWGVRVNVPACMZVSCMZWIWGVNVTWAVMVSFKZWKWIOWCWEVLVM
      ULVLVTVMWLWBACDFIJUMUNZVPAVSCFIUOUPVNWJVQVSCVNVPLABMZCMZWJVQVNWNAVPCABCEF
      GHIUQURVNVOLUSMZABMZSABMWOVQWPSABLVOSUTQVAVBVCVLLPKZVMWQWOOZUTVLWDWRVMWSQ
      VOLABCEFGHIVDVEVFABCEFVQGHIWFVGVHTVITVNWHVQVPCVLVTVMWHVQOWBAVQCDFIWFJVJUN
      URTVNVTWLWGVSOWCWMVSVQCFIWFVKRTT $.
  $}

  ${
    $d g s x y z G $.  $d g s x y z S $.  $d g s x z X $.
    isvclem.1 $e |- X = ran G $.
    $( Lemma for ~ isvcOLD .  (Contributed by NM, 31-May-2008.)
       (New usage is discouraged.) $)
    isvclem $p |- ( ( G e. _V /\ S e. _V ) -> ( <. G , S >. e. CVecOLD
     <-> ( G e. AbelOp /\ S : ( CC X. X ) --> X /\ A. x e. X ( ( 1 S x ) = x /\
       A. y e. CC ( A. z e. X ( y S ( x G z ) ) = ( ( y S x ) G ( y S z ) )
         /\ A. z e. CC ( ( ( y + z ) S x ) = ( ( y S x ) G ( z S x ) ) /\
           ( ( y x. z ) S x ) = ( y S ( z S x ) ) ) ) ) ) ) ) $=
      ( vg vs wcel cv cc wf co wceq wral wa cvv oveq ralbidv cop cvc crn cxp c1
      cablo caddc cmul w3a copab df-vc eleq2i eleq1 wb rneq eqtr4di xpeq2 feq2d
      bitrd syl oveq2d eqeq12d raleqbidv eqeq2d anbi1d anbi12d anbi2d 3anbi123d
      feq3 feq1 eqeq1d oveq12d eqtrd 3anbi23d opelopabg bitrid ) EDUAZUBJVQHKZU
      FJZLVRUCZUDZVTIKZMZUEAKZWBNZWDOZBKZWDCKZVRNZWBNZWGWDWBNZWGWHWBNZVRNZOZCVT
      PZWGWHUGNZWDWBNZWKWHWDWBNZVRNZOZWGWHUHNZWDWBNZWGWRWBNZOZQZCLPZQZBLPZQZAVT
      PZUIZHIUJZJERJDRJQEUFJZLFUDZFDMZUEWDDNZWDOZWGWDWHENZDNZWGWDDNZWGWHDNZENZO
      ZCFPZWPWDDNZXTWHWDDNZENZOZXAWDDNZWGYFDNZOZQZCLPZQZBLPZQZAFPZUIZUBXLVQABCH
      IUKULXKXMXNFWBMZWFWGXRWBNZWKWLENZOZCFPZWQWKWRENZOZXDQZCLPZQZBLPZQZAFPZUIY
      RHIEDRRVREOZVSXMWCYSXJUUKVREUFUMUULVTFOZWCYSUNUULVTEUCFVREUOGUPZUUMWCXNVT
      WBMYSUUMWAXNVTWBVTFLUQURVTFXNWBVIUSUTUULXIUUJAVTFUUNUULXHUUIWFUULXGUUHBLU
      ULWOUUCXFUUGUULWNUUBCVTFUUNUULWJYTWMUUAUULWIXRWGWBWDWHVRESVAWKWLVRESVBVCU
      ULXEUUFCLUULWTUUEXDUULWSUUDWQWKWRVRESVDVETVFTVGVCVHWBDOZYSXOUUKYQXMXNFWBD
      VJUUOUUJYPAFUUOWFXQUUIYOUUOWEXPWDUEWDWBDSVKUUOUUHYNBLUUOUUCYDUUGYMUUOUUBY
      CCFUUOYTXSUUAYBWGXRWBDSUUOWKXTWLYAEWGWDWBDSZWGWHWBDSVLVBTUUOUUFYLCLUUOUUE
      YHXDYKUUOWQYEUUDYGWPWDWBDSUUOWKXTWRYFEUUPWHWDWBDSZVLVBUUOXBYIXCYJXAWDWBDS
      UUOXCWGWRDNYJWGWRWBDSUUOWRYFWGDUUQVAVMVBVFTVFTVFTVNVOVP $.
  $}

  $( The components of a complex vector space are sets.  (Contributed by NM,
     31-May-2008.)  (New usage is discouraged.) $)
  vcex $p |- ( <. G , S >. e. CVecOLD -> ( G e. _V /\ S e. _V ) ) $=
    ( cop cvc wcel wbr cvv wa df-br vcrel brrelex12i sylbir ) BACDEBADFBGEAGEHB
    ADIBADJKL $.

  ${
    $d x y z G $.  $d x y z S $.  $d x z X $.
    isvcOLD.1 $e |- X = ran G $.
    $( The predicate "is a complex vector space."  (Contributed by NM,
       31-May-2008.)  Obsolete version of ~ iscvsp .
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    isvcOLD $p |- ( <. G , S >. e. CVecOLD <-> ( G e. AbelOp /\
         S : ( CC X. X ) --> X /\ A. x e. X ( ( 1 S x ) = x /\
       A. y e. CC ( A. z e. X ( y S ( x G z ) ) = ( ( y S x ) G ( y S z ) )
         /\ A. z e. CC ( ( ( y + z ) S x ) = ( ( y S x ) G ( z S x ) ) /\
           ( ( y x. z ) S x ) = ( y S ( z S x ) ) ) ) ) ) ) $=
      ( cop cvc wcel cvv wa cablo cc cxp cv co wceq wral cgr wf caddc cmul vcex
      c1 w3a elex adantr cnex ablogrpo crn rnexg eqeltrid syl xpexg sylancr fex
      sylan2 ancoms jca 3adant3 isvclem pm5.21nii ) EDHIJEKJZDKJZLZEMJZNFOZFDUA
      ZUEAPZDQVJRBPZVJCPZEQDQVKVJDQZVKVLDQEQRCFSVKVLUBQVJDQVMVLVJDQZEQRVKVLUCQV
      JDQVKVNDQRLCNSLBNSLAFSZUFDEUDVGVIVFVOVGVILVDVEVGVDVIEMUGUHVIVGVEVGVIVHKJZ
      VEVGNKJFKJZVPUIVGETJZVQEUJVRFEUKKGETULUMUNNFKKUOUPVHFKDUQURUSUTVAABCDEFGV
      BVC $.
  $}

  ${
    $d x y z G $.  $d x y z S $.  $d x y z X $.
    isvciOLD.1 $e |- G e. AbelOp $.
    isvciOLD.2 $e |- dom G = ( X X. X ) $.
    isvciOLD.3 $e |- S : ( CC X. X ) --> X $.
    isvciOLD.4 $e |- ( x e. X -> ( 1 S x ) = x ) $.
    isvciOLD.5 $e |- ( ( y e. CC /\ x e. X /\ z e. X ) ->
                  ( y S ( x G z ) ) = ( ( y S x ) G ( y S z ) ) ) $.
    isvciOLD.6 $e |- ( ( y e. CC /\ z e. CC /\ x e. X ) ->
                  ( ( y + z ) S x ) = ( ( y S x ) G ( z S x ) ) ) $.
    isvciOLD.7 $e |- ( ( y e. CC /\ z e. CC /\ x e. X ) ->
                  ( ( y x. z ) S x ) = ( y S ( z S x ) ) ) $.
    isvciOLD.8 $e |- W = <. G , S >. $.
    $( Properties that determine a complex vector space.  (Contributed by NM,
       5-Nov-2006.)  Obsolete version of ~ iscvsi .
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    isvciOLD $p |- W e. CVecOLD $=
      ( wcel cc co wceq wral cop cvc cablo cxp wf c1 cv caddc cmul 3com12 3expa
      wa ralrimiva w3a jca 3comr rgen cgr ablogrpo ax-mp grporn isvcOLD eqeltri
      mpbir3an ) FEDUAZUBOVEUBPEUCPZQGUDGDUEUFAUGZDRVGSZBUGZVGCUGZERDRVIVGDRZVI
      VJDRERSZCGTZVIVJUHRVGDRVKVJVGDRZERSZVIVJUIRVGDRVIVNDRSZULZCQTZULZBQTZULZA
      GTHJWAAGVGGPZVHVTKWBVSBQWBVIQPZULZVMVRWDVLCGWBWCVJGPZVLWCWBWEVLLUJUKUMWDV
      QCQWBWCVJQPZVQWCWFWBVQWCWFWBUNVOVPMNUOUPUKUMUOUMUOUQABCDEGEGVFEURPHEUSUTI
      VAVBVDVC $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Examples of complex vector spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z $.
    $( Obsolete version of ~ cnaddabl .  Complex number addition is an Abelian
       group operation.  (Contributed by NM, 5-Nov-2006.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    cnaddabloOLD $p |- + e. AbelOp $=
      ( vx vy vz caddc cc cc0 cv cneg cnex ax-addf addass 0cn addlid negcl wcel
      co wceq addcom mpdan negid eqtr3d isgrpoi cxp fdmi isabloi ) ABDEABCFDAGZ
      HZEIJUFBGZCGKLUFMUFNZUFEOZUFUGDPZUGUFDPZFUJUGEOUKULQUIUFUGRSUFTUAUBEEUCED
      JUDUFUHRUE $.

    $( Obsolete version of ~ cnaddid .  The group identity element of complex
       number addition is zero.  (Contributed by Steve Rodriguez, 3-Dec-2006.)
       (Revised by Mario Carneiro, 21-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    cnidOLD $p |- 0 = ( GId ` + ) $=
      ( vy vx caddc cgi cfv cv co wceq cc wral crio cc0 wcel cablo cnaddabloOLD
      cgr ablogrpo ax-mp cxp ax-addf fdmi grporn eqid grpoidval addlid rgen 0cn
      wreu wb grpoideu oveq1 eqeq1d ralbidv riota2 mp2an mpbi eqtr2i ) CDEZAFZB
      FZCGZUTHZBIJZAIKZLCPMZURVDHCNMVEOCQRZBAURCICIVFIISICTUAUBZURUCUDRLUTCGZUT
      HZBIJZVDLHZVIBIUTUEUFLIMVCAIUHZVJVKUIUGVEVLVFBACIVGUJRVCVJAILUSLHZVBVIBIV
      MVAVHUTUSLUTCUKULUMUNUOUPUQ $.

    $( Obsolete version of ~ cncvs .  The set of complex numbers is a complex
       vector space.  The vector operation is ` + ` , and the scalar product is
       ` x. ` .  (Contributed by NM, 5-Nov-2006.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    cncvcOLD $p |- <. + , x. >. e. CVecOLD $=
      ( vx vy vz cmul caddc cop cc cnaddabloOLD cxp ax-addf fdmi ax-mulf mullid
      cv adddi adddir mulass eqid isvciOLD ) ABCDEEDFZGHGGIGEJKLANZMBNZUACNZOUB
      UCUAPUBUCUAQTRS $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Normed complex vector spaces
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definition and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c NrmCVec $.

  $c +v $.
  $c BaseSet $.
  $c .sOLD $.
  $c 0vec $.
  $c -v $.
  $c normCV $.

  $c IndMet $.

  $( Extend class notation with the class of all normed complex vector
     spaces. $)
  cnv $a class NrmCVec $.

  $( Extend class notation with vector addition in a normed complex vector
     space.  In the literature, the subscript "v" is omitted, but we need it to
     avoid ambiguity with complex number addition ` + ` ~ caddc . $)
  cpv $a class +v $.

  $( Extend class notation with the base set of a normed complex vector space.
     (Note that ` BaseSet ` is capitalized because, once it is fixed for a
     particular vector space ` U ` , it is not a function, unlike e.g.,
     ` normCV ` .  This is our typical convention.)
     (New usage is discouraged.) $)
  cba $a class BaseSet $.

  $( Extend class notation with scalar multiplication in a normed complex
     vector space.  In the literature scalar multiplication is usually
     indicated by juxtaposition, but we need an explicit symbol to prevent
     ambiguity. $)
  cns $a class .sOLD $.

  $( Extend class notation with zero vector in a normed complex vector
     space. $)
  cn0v $a class 0vec $.

  $( Extend class notation with vector subtraction in a normed complex vector
     space. $)
  cnsb $a class -v $.

  $( Extend class notation with the norm function in a normed complex vector
     space.  In the literature, the norm of ` A ` is usually written "|| ` A `
     ||", but we use function notation to take advantage of our existing
     theorems about functions. $)
  cnmcv $a class normCV $.

  $( Extend class notation with the class of the induced metrics on normed
     complex vector spaces. $)
  cims $a class IndMet $.

  ${
    $d g s n u w x y $.  $d y N $.
    $( Define the class of all normed complex vector spaces.  (Contributed by
       NM, 11-Nov-2006.)  (New usage is discouraged.) $)
    df-nv $a |- NrmCVec = { <. <. g , s >. , n >. |
      ( <. g , s >. e. CVecOLD /\ n : ran g --> RR /\ A. x e. ran g
        ( ( ( n ` x ) = 0 -> x = ( GId ` g ) ) /\
          A. y e. CC ( n ` ( y s x ) ) = ( ( abs ` y ) x. ( n ` x ) ) /\
          A. y e. ran g ( n ` ( x g y ) ) <_ ( ( n ` x ) + ( n ` y ) ) ) ) } $.

    $( Structure of the class of all normed complex vectors spaces.
       (Contributed by NM, 28-Nov-2006.)  (Revised by Mario Carneiro,
       1-May-2015.)  (New usage is discouraged.) $)
    nvss $p |- NrmCVec C_ ( CVecOLD X. _V ) $=
      ( vw vg vs vn vx vy cv cop wceq cvc wcel cfv co wral w3a wa wex copab cvv
      cnv crn cr wf cc0 cgi wi cabs cmul cc caddc cle wbr cxp biimpar 3ad2antr1
      eleq1 exlimivv jctir ssopab2i coprab df-nv dfoprab2 eqtri df-xp 3sstr4i
      vex ) AGZBGZCGZHZIZVJJKZVHUAZUBDGZUCZEGZVNLZUDIVPVHUELIUFFGZVPVIMVNLVRUGL
      VQUHMIFUINVPVRVHMVNLVQVRVNLUJMUKULFVMNOEVMNZOZPZCQBQZADRZVGJKZVNSKZPZADRT
      JSUMWBWFADWBWDWEWAWDBCVKVOVLWDVSVKWDVLVGVJJUPUNUOUQDVFURUSTVTBCDUTWCEFBDC
      VAVTBCDAVBVCADJSVDVE $.

    $( A normed complex vector space is a vector space.  (Contributed by NM,
       5-Jun-2008.)  (Revised by Mario Carneiro, 1-May-2015.)
       (New usage is discouraged.) $)
    nvvcop $p |- ( <. W , N >. e. NrmCVec -> W e. CVecOLD ) $=
      ( cop cnv wcel cvc cvv cxp nvss sseli opelxp1 syl ) BACZDEMFGHZEBFEDNMIJB
      AFGKL $.

    $( Define vector addition on a normed complex vector space.  (Contributed
       by NM, 23-Apr-2007.)  (New usage is discouraged.) $)
    df-va $a |- +v = ( 1st o. 1st ) $.

    $( Define the base set of a normed complex vector space.  (Contributed by
       NM, 23-Apr-2007.)  (New usage is discouraged.) $)
    df-ba $a |- BaseSet = ( x e. _V |-> ran ( +v ` x ) ) $.

    $( Define scalar multiplication on a normed complex vector space.
       (Contributed by NM, 24-Apr-2007.)  (New usage is discouraged.) $)
    df-sm $a |- .sOLD = ( 2nd o. 1st ) $.

    $( Define the zero vector in a normed complex vector space.  (Contributed
       by NM, 24-Apr-2007.)  (New usage is discouraged.) $)
    df-0v $a |- 0vec = ( GId o. +v ) $.

    $( Define vector subtraction on a normed complex vector space.
       (Contributed by NM, 15-Feb-2008.)  (New usage is discouraged.) $)
    df-vs $a |- -v = ( /g o. +v ) $.

    $( Define the norm function in a normed complex vector space.  (Contributed
       by NM, 25-Apr-2007.)  (New usage is discouraged.) $)
    df-nmcv $a |- normCV = 2nd $.

    $( Define the induced metric on a normed complex vector space.
       (Contributed by NM, 11-Sep-2007.)  (New usage is discouraged.) $)
    df-ims $a |- IndMet = ( u e. NrmCVec |->
                            ( ( normCV ` u ) o. ( -v ` u ) ) ) $.
  $}

  $( The class of all normed complex vectors spaces is a relation.
     (Contributed by NM, 14-Nov-2006.)  (New usage is discouraged.) $)
  nvrel $p |- Rel NrmCVec $=
    ( cnv cvc cvv cxp wss wrel nvss relxp relss mp2 ) ABCDZEKFAFGBCHAKIJ $.

  ${
    vafval.2 $e |- G = ( +v ` U ) $.
    $( Value of the function for the vector addition (group) operation on a
       normed complex vector space.  (Contributed by NM, 23-Apr-2007.)
       (New usage is discouraged.) $)
    vafval $p |- G = ( 1st ` ( 1st ` U ) ) $=
      ( cpv cfv c1st cvv wcel wceq df-va fveq1i wf wfo fo1st fof ax-mp fvco3 c0
      ccom fvprc mpan eqtrid wn fveq2d 1st0 eqtr2di eqtrd pm2.61i eqtri ) BADEZ
      AFEZFEZCAGHZUJULIUMUJAFFSZEZULADUNJKGGFLZUMUOULIGGFMUPNGGFOPGGAFFQUAUBUMU
      CZUJRULADTUQULRFERUQUKRFAFTUDUEUFUGUHUI $.
  $}

  ${
    $d u U $.
    bafval.1 $e |- X = ( BaseSet ` U ) $.
    bafval.2 $e |- G = ( +v ` U ) $.
    $( Value of the function for the base set of a normed complex vector space.
       (Contributed by NM, 23-Apr-2007.)  (Revised by Mario Carneiro,
       16-Nov-2013.)  (New usage is discouraged.) $)
    bafval $p |- X = ran G $=
      ( vu cba cfv cpv crn cvv wcel wceq cv fveq2 rneqd df-ba fvex c0 fvprc rn0
      rnex fvmpt wn eqcomi 3eqtr4a pm2.61i rneqi 3eqtr4i ) AGHZAIHZJZCBJAKLZUJU
      LMFAFNZIHZJULKGUNAMUOUKUNAIOPFQUKAIRUBUCUMUDZSSJZUJULUQSUAUEAGTUPUKSAITPU
      FUGDBUKEUHUI $.
  $}

  ${
    smfval.4 $e |- S = ( .sOLD ` U ) $.
    $( Value of the function for the scalar multiplication operation on a
       normed complex vector space.  (Contributed by NM, 24-Apr-2007.)
       (New usage is discouraged.) $)
    smfval $p |- S = ( 2nd ` ( 1st ` U ) ) $=
      ( cns cfv c1st c2nd cvv wcel wceq ccom df-sm fveq1i wf wfo fo1st ax-mp c0
      fof fvprc fvco3 mpan eqtrid wn fveq2d 2nd0 eqtr2di eqtrd pm2.61i eqtri )
      ABDEZBFEZGEZCBHIZUKUMJUNUKBGFKZEZUMBDUOLMHHFNZUNUPUMJHHFOUQPHHFSQHHBGFUAU
      BUCUNUDZUKRUMBDTURUMRGERURULRGBFTUEUFUGUHUIUJ $.
  $}

  ${
    0vfval.2 $e |- G = ( +v ` U ) $.
    0vfval.5 $e |- Z = ( 0vec ` U ) $.
    $( Value of the function for the zero vector on a normed complex vector
       space.  (Contributed by NM, 24-Apr-2007.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.) $)
    0vfval $p |- ( U e. V -> Z = ( GId ` G ) ) $=
      ( wcel cvv cgi cfv wceq elex cpv ccom wfn c1st crn wss wfo cn0v fo1st ssv
      fofn ax-mp fnco mp3an df-va fneq1i mpbir fvco2 df-0v fveq1i eqtri 3eqtr4g
      mpan fveq2i syl ) ACGAHGZDBIJZKACLURAIMNZJZAMJZIJZDUSMHOZURVAVCKVDPPNZHOZ
      PHOZVGPQZHRVFHHPSVGUAHHPUCUDZVIVHUBHHPPUEUFHMVEUGUHUIHIMAUJUODATJVAFATUTU
      KULUMBVBIEUPUNUQ $.
  $}

  ${
    nmfval.6 $e |- N = ( normCV ` U ) $.
    $( Value of the norm function in a normed complex vector space.
       (Contributed by NM, 25-Apr-2007.)  (New usage is discouraged.) $)
    nmcvfval $p |- N = ( 2nd ` U ) $=
      ( cnmcv cfv c2nd df-nmcv fveq1i eqtri ) BADEAFECADFGHI $.
  $}

  ${
    nvop2.1 $e |- W = ( 1st ` U ) $.
    nvop2.6 $e |- N = ( normCV ` U ) $.
    $( A normed complex vector space is an ordered pair of a vector space and a
       norm operation.  (Contributed by NM, 28-Nov-2006.)
       (New usage is discouraged.) $)
    nvop2 $p |- ( U e. NrmCVec -> U = <. W , N >. ) $=
      ( cnv wcel c1st cfv c2nd cop wrel wceq nvrel 1st2nd mpan nmcvfval opeq12i
      eqtr4di ) AFGZAAHIZAJIZKZCBKFLTAUCMNAFOPCUABUBDABEQRS $.
  $}

  ${
    nvvop.1 $e |- W = ( 1st ` U ) $.
    nvvop.2 $e |- G = ( +v ` U ) $.
    nvvop.4 $e |- S = ( .sOLD ` U ) $.
    $( The vector space component of a normed complex vector space is an
       ordered pair of the underlying group and a scalar product.  (Contributed
       by NM, 28-Nov-2006.)  (New usage is discouraged.) $)
    nvvop $p |- ( U e. NrmCVec -> W = <. G , S >. ) $=
      ( cnv wcel c1st cfv c2nd cop cvc wrel wceq vcrel cvv fveq2i eqtr4i eleq1d
      cnmcv cxp nvss eqid nvop2 ibi sselid opelxp1 1st2nd sylancr vafval smfval
      syl opeq12i eqtr4di ) BHIZDDJKZDLKZMZCAMUQNODNIZDUTPQUQDBUBKZMZNRUCZIVAUQ
      HVDVCUDUQVCHIUQBVCHBVBDEVBUEUFUAUGUHDVBNRUIUNDNUJUKCURAUSCBJKZJKURBCFULDV
      EJESTAVELKUSABGUMDVELESTUOUP $.
  $}

  ${
    $d g n s x y G $.  $d g n s x y N $.  $d g n s x y S $.  $d g n s x y X $.
    $d g n s Z $.
    isnvlem.1 $e |- X = ran G $.
    isnvlem.2 $e |- Z = ( GId ` G ) $.
    $( Lemma for ~ isnv .  (Contributed by NM, 11-Nov-2006.)
       (New usage is discouraged.) $)
    isnvlem $p |- ( ( G e. _V /\ S e. _V /\ N e. _V ) ->
                 ( <. <. G , S >. , N >. e. NrmCVec <-> ( <. G , S >. e.
        CVecOLD
        /\ N : X --> RR /\ A. x e. X ( ( ( N ` x ) = 0 -> x = Z )
           /\ A. y e. CC ( N ` ( y S x ) ) = ( ( abs ` y ) x. ( N ` x ) ) /\
           A. y e. X ( N ` ( x G y ) ) <_ ( ( N ` x ) + ( N ` y ) ) ) ) ) ) $=
      ( wcel cv cvc cr cfv wceq co cc wral w3a cvv vg vs vn cop cnv crn cc0 cgi
      wf wi cabs cmul caddc cle wbr coprab df-nv eleq2i opeq1 eleq1d rneq feq2d
      fveq2 eqeq2d imbi2d oveq fveq2d breq1d raleqbidv 3anbi13d 3anbi123d opeq2
      eqtr4di fveqeq2d ralbidv 3anbi2d feq1 fveq1 eqeq1d imbi1d eqeq12d oveq12d
      oveq2d breq12d 3anbi23d eloprabg bitrid ) DCUDZEUDZUEJWIUAKZUBKZUDZLJZWJU
      FZMUCKZUIZAKZWONZUGOZWQWJUHNZOZUJZBKZWQWKPZWONXCUKNZWRULPZOZBQRZWQXCWJPZW
      ONZWRXCWONZUMPZUNUOZBWNRZSZAWNRZSZUAUBUCUPZJDTJCTJETJSWHLJZFMEUIZWQENZUGO
      ZWQGOZUJZXCWQCPZENZXEYAULPZOZBQRZWQXCDPZENZYAXCENZUMPZUNUOZBFRZSZAFRZSZUE
      XRWIABUAUCUBUQURXQDWKUDZLJZFMWOUIZWSYCUJZXHYJWONZXLUNUOZBFRZSZAFRZSXSUUAU
      UBYEWONZXFOZBQRZUUESZAFRZSYRUAUBUCDCETTTWJDOZWMYTWPUUAXPUUGUUMWLYSLWJDWKU
      SUTUUMWNFMWOUUMWNDUFFWJDVAHVMZVBUUMXOUUFAWNFUUNUUMXBUUBXNUUEXHUUMXAYCWSUU
      MWTGWQUUMWTDUHNGWJDUHVCIVMVDVEUUMXMUUDBWNFUUNUUMXJUUCXLUNUUMXIYJWOWQXCWJD
      VFVGVHVIVJVIVKWKCOZYTXSUUGUULUUAUUOYSWHLWKCDVLUTUUOUUFUUKAFUUOXHUUJUUBUUE
      UUOXGUUIBQUUOXDYEXFWOXCWQWKCVFVNVOVPVOVJWOEOZUUAXTUULYQXSFMWOEVQUUPUUKYPA
      FUUPUUBYDUUJYIUUEYOUUPWSYBYCUUPWRYAUGWQWOEVRZVSVTUUPUUIYHBQUUPUUHYFXFYGYE
      WOEVRUUPWRYAXEULUUQWCWAVOUUPUUDYNBFUUPUUCYKXLYMUNYJWOEVRUUPWRYAXKYLUMUUQX
      CWOEVRWBWDVOVKVOWEWFWG $.
  $}

  $( The components of a normed complex vector space are sets.  (Contributed by
     NM, 5-Jun-2008.)  (Revised by Mario Carneiro, 1-May-2015.)
     (New usage is discouraged.) $)
  nvex $p |- ( <. <. G , S >. , N >. e. NrmCVec
          -> ( G e. _V /\ S e. _V /\ N e. _V ) ) $=
    ( cop cnv wcel cvv wa w3a cvc nvvcop vcex syl cxp nvss sseli opelxp2 df-3an
    sylanbrc ) BADZCDZEFZBGFZAGFZHZCGFZUCUDUFIUBTJFUECTKABLMUBUAJGNZFUFEUGUAOPT
    CJGQMUCUDUFRS $.

  ${
    $d x y G $.  $d x y N $.  $d x y S $.  $d x y X $.
    isnv.1 $e |- X = ran G $.
    isnv.2 $e |- Z = ( GId ` G ) $.
    $( The predicate "is a normed complex vector space."  (Contributed by NM,
       5-Jun-2008.)  (New usage is discouraged.) $)
    isnv $p |- ( <. <. G , S >. , N >. e. NrmCVec <-> ( <. G , S >. e. CVecOLD
        /\ N : X --> RR /\ A. x e. X ( ( ( N ` x ) = 0 -> x = Z )
           /\ A. y e. CC ( N ` ( y S x ) ) = ( ( abs ` y ) x. ( N ` x ) ) /\
           A. y e. X ( N ` ( x G y ) ) <_ ( ( N ` x ) + ( N ` y ) ) ) ) ) $=
      ( cop wcel cvv w3a cr cv cfv wceq co wral wa cnv cvc wf cc0 wi cabs caddc
      cmul cc cle wbr nvex vcex adantr crn simpld rnexg syl eqeltrid fex sylan2
      ancoms df-3an sylanbrc 3adant3 isnvlem pm5.21nii ) DCJZEJUAKDLKZCLKZELKZM
      ZVHUBKZFNEUCZAOZEPZUDQVOGQUEBOZVOCREPVQUFPVPUHRQBUISVOVQDREPVPVQEPUGRUJUK
      BFSMAFSZMCDEULVMVNVLVRVMVNTVIVJTZVKVLVMVSVNCDUMZUNVNVMVKVMVNFLKVKVMFDUOZL
      HVMVIWALKVMVIVJVTUPDLUQURUSFNLEUTVAVBVIVJVKVCVDVEABCDEFGHIVFVG $.
  $}

  ${
    $d x y G $.  $d x y N $.  $d x y S $.  $d x y X $.
    isnvi.5 $e |- X = ran G $.
    isnvi.6 $e |- Z = ( GId ` G ) $.
    isnvi.7 $e |- <. G , S >. e. CVecOLD $.
    isnvi.8 $e |- N : X --> RR $.
    isnvi.9 $e |- ( ( x e. X /\ ( N ` x ) = 0 ) -> x = Z ) $.
    isnvi.10 $e |- ( ( y e. CC /\ x e. X ) ->
                    ( N ` ( y S x ) ) = ( ( abs ` y ) x. ( N ` x ) ) ) $.
    isnvi.11 $e |- ( ( x e. X /\ y e. X ) ->
                    ( N ` ( x G y ) ) <_ ( ( N ` x ) + ( N ` y ) ) ) $.
    isnvi.12 $e |- U = <. <. G , S >. , N >. $.
    $( Properties that determine a normed complex vector space.  (Contributed
       by NM, 15-Apr-2007.)  (New usage is discouraged.) $)
    isnvi $p |- U e. NrmCVec $=
      ( wcel cfv wceq co cop cnv cvc cr wf cv cc0 wi cabs cmul cc caddc cle wbr
      wral w3a ex ancoms ralrimiva 3jca rgen isnv mpbir3an eqeltri ) DECUAZFUAZ
      UBPVFUBQVEUCQGUDFUEAUFZFRZUGSZVGHSZUHZBUFZVGCTFRVLUIRVHUJTSZBUKUOZVGVLETF
      RVHVLFRULTUMUNZBGUOZUPZAGUOKLVQAGVGGQZVKVNVPVRVIVJMUQVRVMBUKVLUKQVRVMNURU
      SVRVOBGOUSUTVAABCEFGHIJVBVCVD $.
  $}

  ${
    $d x y G $.  $d x y N $.  $d x U $.  $d x y S $.  $d x y X $.
    nvi.1 $e |- X = ( BaseSet ` U ) $.
    nvi.2 $e |- G = ( +v ` U ) $.
    nvi.4 $e |- S = ( .sOLD ` U ) $.
    nvi.5 $e |- Z = ( 0vec ` U ) $.
    nvi.6 $e |- N = ( normCV ` U ) $.
    $( The properties of a normed complex vector space, which is a vector space
       accompanied by a norm.  (Contributed by NM, 11-Nov-2006.)  (Revised by
       Mario Carneiro, 21-Dec-2013.)  (New usage is discouraged.) $)
    nvi $p |- ( U e. NrmCVec -> ( <. G , S >. e. CVecOLD /\ N : X --> RR /\
       A. x e. X ( ( ( N ` x ) = 0 -> x = Z )
           /\ A. y e. CC ( N ` ( y S x ) ) = ( ( abs ` y ) x. ( N ` x ) ) /\
              A. y e. X ( N ` ( x G y ) ) <_ ( ( N ` x ) + ( N ` y ) ) ) ) ) $=
      ( cnv wcel cfv wceq co wral w3a cop cvc cr wf cv cc0 wi cabs cc caddc cle
      cmul wbr c1st eqid nvop2 nvvop opeq1d eqtrd id eqeltrrd bafval isnv sylib
      cgi 0vfval eqeq2d imbi2d 3anbi1d ralbidv 3anbi3d mpbird ) DNOZECUAZUBOZGU
      CFUDZAUEZFPZUFQZVQHQZUGZBUEZVQCRFPWBUHPVRULRQBUISZVQWBERFPVRWBFPUJRUKUMBG
      SZTZAGSZTVOVPVSVQEVEPZQZUGZWCWDTZAGSZTZVMVNFUAZNOWLVMDWMNVMDDUNPZFUAWMDFW
      NWNUOZMUPVMWNVNFCDEWNWOJKUQURUSVMUTVAABCEFGWGDEGIJVBWGUOVCVDVMWFWKVOVPVMW
      EWJAGVMWAWIWCWDVMVTWHVSVMHWGVQDENHJLVFVGVHVIVJVKVL $.
  $}

  ${
    $d x y U $.  $d x y W $.
    nvvc.1 $e |- W = ( 1st ` U ) $.
    $( The vector space component of a normed complex vector space.
       (Contributed by NM, 28-Nov-2006.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.) $)
    nvvc $p |- ( U e. NrmCVec -> W e. CVecOLD ) $=
      ( vx vy cnv wcel cpv cfv cns cop cvc eqid nvvop cba cr cv wceq co wral wf
      cnmcv cc0 cn0v wi cabs cmul cc caddc cle wbr w3a nvi simp1d eqeltrd ) AFG
      ZBAHIZAJIZKZLURAUQBCUQMZURMZNUPUSLGAOIZPAUBIZUADQZVCIZUCRVDAUDIZRUEEQZVDU
      RSVCIVGUFIVEUGSREUHTVDVGUQSVCIVEVGVCIUISUJUKEVBTULDVBTDEURAUQVCVBVFVBMUTV
      AVFMVCMUMUNUO $.
  $}

  ${
    nvabl.1 $e |- G = ( +v ` U ) $.
    $( The vector addition operation of a normed complex vector space is an
       Abelian group.  (Contributed by NM, 15-Feb-2008.)
       (New usage is discouraged.) $)
    nvablo $p |- ( U e. NrmCVec -> G e. AbelOp ) $=
      ( cnv wcel c1st cfv cvc cablo eqid nvvc vafval vcablo syl ) ADEAFGZHEBIEA
      OOJKBOABCLMN $.

    $( The vector addition operation of a normed complex vector space is a
       group.  (Contributed by NM, 15-Feb-2008.)
       (New usage is discouraged.) $)
    nvgrp $p |- ( U e. NrmCVec -> G e. GrpOp ) $=
      ( cnv wcel cablo cgr nvablo ablogrpo syl ) ADEBFEBGEABCHBIJ $.
  $}

  ${
    nvgf.1 $e |- X = ( BaseSet ` U ) $.
    nvgf.2 $e |- G = ( +v ` U ) $.
    $( Mapping for the vector addition operation.  (Contributed by NM,
       28-Jan-2008.)  (New usage is discouraged.) $)
    nvgf $p |- ( U e. NrmCVec -> G : ( X X. X ) --> X ) $=
      ( cnv wcel cgr cxp wfo wf nvgrp bafval grpofo fof 3syl ) AFGBHGCCIZCBJQCB
      KABELBCABCDEMNQCBOP $.
  $}

  ${
    nvsf.1 $e |- X = ( BaseSet ` U ) $.
    nvsf.4 $e |- S = ( .sOLD ` U ) $.
    $( Mapping for the scalar multiplication operation.  (Contributed by NM,
       28-Jan-2008.)  (New usage is discouraged.) $)
    nvsf $p |- ( U e. NrmCVec -> S : ( CC X. X ) --> X ) $=
      ( cnv wcel c1st cfv cvc cc cxp wf eqid nvvc cpv vafval smfval bafval vcsm
      syl ) BFGBHIZJGKCLCAMBUBUBNOABPIZUBCBUCUCNZQABERBUCCDUDSTUA $.
  $}

  ${
    nvgcl.1 $e |- X = ( BaseSet ` U ) $.
    nvgcl.2 $e |- G = ( +v ` U ) $.
    $( Closure law for the vector addition (group) operation of a normed
       complex vector space.  (Contributed by NM, 23-Apr-2007.)
       (New usage is discouraged.) $)
    nvgcl $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                    ( A G B ) e. X ) $=
      ( cnv wcel cgr co nvgrp bafval grpocl syl3an1 ) CHIDJIAEIBEIABDKEICDGLABD
      ECDEFGMNO $.

    $( The vector addition (group) operation is commutative.  (Contributed by
       NM, 4-Dec-2007.)  (New usage is discouraged.) $)
    nvcom $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                ( A G B ) = ( B G A ) ) $=
      ( cnv wcel cablo co wceq nvablo bafval ablocom syl3an1 ) CHIDJIAEIBEIABDK
      BADKLCDGMABDECDEFGNOP $.

    $( The vector addition (group) operation is associative.  (Contributed by
       NM, 4-Dec-2007.)  (New usage is discouraged.) $)
    nvass $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
              ( ( A G B ) G C ) = ( A G ( B G C ) ) ) $=
      ( cnv wcel cgr w3a co wceq nvgrp bafval grpoass sylan ) DIJEKJAFJBFJCFJLA
      BEMCEMABCEMEMNDEHOABCEFDEFGHPQR $.

    $( Commutative/associative law for vector addition.  (Contributed by NM,
       27-Dec-2007.)  (New usage is discouraged.) $)
    nvadd32 $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                 ( ( A G B ) G C ) = ( ( A G C ) G B ) ) $=
      ( cnv wcel cablo w3a co wceq nvablo bafval ablo32 sylan ) DIJEKJAFJBFJCFJ
      LABEMCEMACEMBEMNDEHOABCEFDEFGHPQR $.

    $( Right cancellation law for vector addition.  (Contributed by NM,
       4-Dec-2007.)  (New usage is discouraged.) $)
    nvrcan $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                  ( ( A G C ) = ( B G C ) <-> A = B ) ) $=
      ( cnv wcel cgr w3a co wceq wb nvgrp bafval grporcan sylan ) DIJEKJAFJBFJC
      FJLACEMBCEMNABNODEHPABCEFDEFGHQRS $.

    $( Rearrangement of 4 terms in a vector sum.  (Contributed by NM,
       8-Feb-2008.)  (New usage is discouraged.) $)
    nvadd4 $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X ) /\ ( C e. X /\
       D e. X ) ) -> ( ( A G B ) G ( C G D ) ) = ( ( A G C ) G ( B G D ) ) ) $=
      ( cnv wcel cablo wa co wceq nvablo bafval ablo4 syl3an1 ) EJKFLKAGKBGKMCG
      KDGKMABFNCDFNFNACFNBDFNFNOEFIPABCDFGEFGHIQRS $.
  $}

  ${
    nvscl.1 $e |- X = ( BaseSet ` U ) $.
    nvscl.4 $e |- S = ( .sOLD ` U ) $.
    $( Closure law for the scalar product operation of a normed complex vector
       space.  (Contributed by NM, 1-Feb-2007.)  (New usage is discouraged.) $)
    nvscl $p |- ( ( U e. NrmCVec /\ A e. CC /\ B e. X ) ->
                       ( A S B ) e. X ) $=
      ( cnv wcel c1st cfv cvc cc co eqid nvvc cpv vafval smfval bafval syl3an1
      vccl ) DHIDJKZLIAMIBEIABCNEIDUCUCOPABCDQKZUCEDUDUDOZRCDGSDUDEFUETUBUA $.

    $( Identity element for the scalar product of a normed complex vector
       space.  (Contributed by NM, 4-Dec-2007.)  (New usage is discouraged.) $)
    nvsid $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( 1 S A ) = A ) $=
      ( cnv wcel c1st cfv cvc c1 co wceq eqid nvvc cpv vafval smfval bafval
      vcidOLD sylan ) CGHCIJZKHADHLABMANCUCUCOPABCQJZUCDCUDUDOZRBCFSCUDDEUETUAU
      B $.

    $( Associative law for the scalar product of a normed complex vector space.
       (Contributed by NM, 17-Nov-2007.)  (New usage is discouraged.) $)
    nvsass $p |- ( ( U e. NrmCVec /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
      ( ( A x. B ) S C ) = ( A S ( B S C ) ) ) $=
      ( cnv wcel c1st cfv cvc cc w3a cmul co wceq eqid nvvc vafval smfval vcass
      cpv bafval sylan ) EIJEKLZMJANJBNJCFJOABPQCDQABCDQDQREUGUGSTABCDEUDLZUGFE
      UHUHSZUADEHUBEUHFGUIUEUCUF $.

    $( Commutative law for the scalar product of a normed complex vector space.
       (Contributed by NM, 14-Feb-2008.)  (New usage is discouraged.) $)
    nvscom $p |- ( ( U e. NrmCVec /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
      ( A S ( B S C ) ) = ( B S ( A S C ) ) ) $=
      ( cnv wcel cc w3a wa cmul co wceq mulcom oveq1d 3adant3 nvsass 3ancoma
      adantl sylan2b 3eqtr3d ) EIJZAKJZBKJZCFJZLZMABNOZCDOZBANOZCDOZABCDODOBACD
      ODOZUIUKUMPZUEUFUGUOUHUFUGMUJULCDABQRSUBABCDEFGHTUIUEUGUFUHLUMUNPUFUGUHUA
      BACDEFGHTUCUD $.
  $}

  ${
    nvdi.1 $e |- X = ( BaseSet ` U ) $.
    nvdi.2 $e |- G = ( +v ` U ) $.
    nvdi.4 $e |- S = ( .sOLD ` U ) $.
    $( Distributive law for the scalar product of a complex vector space.
       (Contributed by NM, 4-Dec-2007.)  (New usage is discouraged.) $)
    nvdi $p |- ( ( U e. NrmCVec /\ ( A e. CC /\ B e. X /\ C e. X ) ) ->
       ( A S ( B G C ) ) = ( ( A S B ) G ( A S C ) ) ) $=
      ( cnv wcel c1st cfv cvc cc w3a co wceq eqid nvvc vafval smfval vcdi sylan
      bafval ) EKLEMNZOLAPLBGLCGLQABCFRDRABDRACDRFRSEUGUGTUAABCDFUGGEFIUBDEJUCE
      FGHIUFUDUE $.

    $( Distributive law for the scalar product of a complex vector space.
       (Contributed by NM, 4-Dec-2007.)  (New usage is discouraged.) $)
    nvdir $p |- ( ( U e. NrmCVec /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
      ( ( A + B ) S C ) = ( ( A S C ) G ( B S C ) ) ) $=
      ( cnv wcel c1st cfv cvc cc w3a caddc co wceq eqid nvvc vafval vcdir sylan
      smfval bafval ) EKLEMNZOLAPLBPLCGLQABRSCDSACDSBCDSFSTEUHUHUAUBABCDFUHGEFI
      UCDEJUFEFGHIUGUDUE $.

    $( A vector plus itself is two times the vector.  (Contributed by NM,
       9-Feb-2008.)  (New usage is discouraged.) $)
    nv2 $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( A G A ) = ( 2 S A ) ) $=
      ( cnv wcel c1st cfv cvc co c2 wceq eqid nvvc vafval smfval bafval vc2OLD
      sylan ) CIJCKLZMJAEJAADNOABNPCUDUDQRABDUDECDGSBCHTCDEFGUAUBUC $.
  $}

  ${
    $d g x y $.
    vsfval.2 $e |- G = ( +v ` U ) $.
    vsfval.3 $e |- M = ( -v ` U ) $.
    $( Value of the function for the vector subtraction operation on a normed
       complex vector space.  (Contributed by NM, 15-Feb-2008.)  (Revised by
       Mario Carneiro, 27-Dec-2014.)  (New usage is discouraged.) $)
    vsfval $p |- M = ( /g ` G ) $=
      ( vg vx vy cnsb cfv cpv cgs cvv wcel wceq wf c1st c0 cgr cv df-vs wfo fof
      ccom fveq1i fo1st ax-mp fco mp2an df-va feq1i mpbir fvco3 mpan eqtrid cdm
      wn 0ngrp crn cgn co cmpo vex rnex mpoex df-gdiv dmmpti eleq2i mtbir ndmfv
      mp1i fvprc fveq2d 3eqtr4rd pm2.61i fveq2i 3eqtr4i ) AIJZAKJZLJZCBLJAMNZVR
      VTOWAVRALKUDZJZVTAIWBUAUEMMKPZWAWCVTOWDMMQQUDZPZMMQPZWGWFMMQUBWGUFMMQUCUG
      ZWHMMMQQUHUIMMKWEUJUKULMMALKUMUNUOWAUQZRLJZRVTVRRLUPZNZUQWJROWIWLRSNURWKS
      RFSGHFTZUSZWNGTHTWMUTJJWMVAZVBLGHWNWNWOWMFVCVDZWPVEGHFVFVGVHVIRLVJVKWIVSR
      LAKVLVMAIVLVNVOEBVSLDVPVQ $.
  $}

  ${
    nvzcl.1 $e |- X = ( BaseSet ` U ) $.
    nvzcl.6 $e |- Z = ( 0vec ` U ) $.
    $( Closure law for the zero vector of a normed complex vector space.
       (Contributed by NM, 27-Nov-2007.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.) $)
    nvzcl $p |- ( U e. NrmCVec -> Z e. X ) $=
      ( cnv wcel cpv cfv cgi eqid 0vfval cgr nvgrp bafval grpoidcl syl eqeltrd
      ) AFGZCAHIZJIZBATFCTKZELSTMGUABGATUBNUATBATBDUBOUAKPQR $.
  $}

  ${
    nv0id.1 $e |- X = ( BaseSet ` U ) $.
    nv0id.2 $e |- G = ( +v ` U ) $.
    nv0id.6 $e |- Z = ( 0vec ` U ) $.
    $( The zero vector is a right identity element.  (Contributed by NM,
       28-Nov-2007.)  (Revised by Mario Carneiro, 21-Dec-2013.)
       (New usage is discouraged.) $)
    nv0rid $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( A G Z ) = A ) $=
      ( cnv wcel wa co cgi cfv wceq 0vfval oveq2d adantr cgr nvgrp eqid grporid
      bafval sylan eqtrd ) BIJZADJZKAECLZACMNZCLZAUFUHUJOUGUFEUIACBCIEGHPQRUFCS
      JUGUJAOBCGTAUICDBCDFGUCUIUAUBUDUE $.

    $( The zero vector is a left identity element.  (Contributed by NM,
       28-Nov-2007.)  (Revised by Mario Carneiro, 21-Dec-2013.)
       (New usage is discouraged.) $)
    nv0lid $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( Z G A ) = A ) $=
      ( cnv wcel wa co cgi cfv wceq 0vfval oveq1d adantr cgr nvgrp eqid grpolid
      bafval sylan eqtrd ) BIJZADJZKEACLZCMNZACLZAUFUHUJOUGUFEUIACBCIEGHPQRUFCS
      JUGUJAOBCGTAUICDBCDFGUCUIUAUBUDUE $.
  $}

  ${
    nv0.1 $e |- X = ( BaseSet ` U ) $.
    nv0.4 $e |- S = ( .sOLD ` U ) $.
    nv0.6 $e |- Z = ( 0vec ` U ) $.
    $( Zero times a vector is the zero vector.  (Contributed by NM,
       27-Nov-2007.)  (Revised by Mario Carneiro, 21-Dec-2013.)
       (New usage is discouraged.) $)
    nv0 $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( 0 S A ) = Z ) $=
      ( cnv wcel wa cc0 co cpv cfv cgi c1st cvc wceq eqid nvvc vafval vc0 sylan
      smfval bafval 0vfval adantr eqtr4d ) CIJZADJZKLABMZCNOZPOZEUJCQOZRJUKULUN
      SCUOUOTUAABUMUODUNCUMUMTZUBBCGUECUMDFUPUFUNTUCUDUJEUNSUKCUMIEUPHUGUHUI $.
  $}

  ${
    nvsz.4 $e |- S = ( .sOLD ` U ) $.
    nvsz.6 $e |- Z = ( 0vec ` U ) $.
    $( Anything times the zero vector is the zero vector.  (Contributed by NM,
       28-Nov-2007.)  (Revised by Mario Carneiro, 21-Dec-2013.)
       (New usage is discouraged.) $)
    nvsz $p |- ( ( U e. NrmCVec /\ A e. CC ) -> ( A S Z ) = Z ) $=
      ( cnv wcel cc wa cpv cfv cgi co c1st cvc wceq eqid nvvc cba vafval smfval
      bafval vcz sylan 0vfval adantr oveq2d 3eqtr4d ) CGHZAIHZJZACKLZMLZBNZUNAD
      BNDUJCOLZPHUKUOUNQCUPUPRSABUMUPCTLZUNCUMUMRZUABCEUBCUMUQUQRURUCUNRUDUEULD
      UNABUJDUNQUKCUMGDURFUFUGZUHUSUI $.
  $}

  ${
    nvinv.1 $e |- X = ( BaseSet ` U ) $.
    nvinv.2 $e |- G = ( +v ` U ) $.
    nvinv.4 $e |- S = ( .sOLD ` U ) $.
    nvinv.5 $e |- M = ( inv ` G ) $.
    $( Minus 1 times a vector is the underlying group's inverse element.
       Equation 2 of [Kreyszig] p. 51.  (Contributed by NM, 15-Feb-2008.)
       (New usage is discouraged.) $)
    nvinv $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( -u 1 S A ) = ( M ` A ) ) $=
      ( cnv wcel c1st cfv cvc c1 cneg co wceq eqid nvvc vafval smfval vcm sylan
      bafval ) CKLCMNZOLAFLPQABRAENSCUGUGTUAABDEUGFCDHUBBCIUCCDFGHUFJUDUE $.
  $}

  ${
    $d x G $.  $d x N $.  $d x U $.
    nvinvfval.2 $e |- G = ( +v ` U ) $.
    nvinvfval.4 $e |- S = ( .sOLD ` U ) $.
    nvinvfval.3 $e |- N = ( S o. `' ( 2nd |` ( { -u 1 } X. _V ) ) ) $.
    $( Function for the negative of a vector on a normed complex vector space,
       in terms of the underlying addition group inverse.  (We currently do not
       have a separate notation for the negative of a vector.)  (Contributed by
       NM, 27-Mar-2008.)  (New usage is discouraged.) $)
    nvinvfval $p |- ( U e. NrmCVec -> N = ( inv ` G ) ) $=
      ( vx cnv wcel cba cfv cgn cc wf eqid neg1cn sylancl ffnd wfn c1 cneg nvsf
      cxp curry1f wf1o nvgrp bafval grpoinvf f1ofn 3syl cv wa co wceq curry1val
      cgr adantr nvinv eqtrd eqfnfvd ) BIJZHBKLZDCMLZVBVCVCDVBNVCUDZVCAOUAUBZNJ
      ZVCVCDOABVCVCPZFUCZQNVCVFVCADGUERSVBCUQJVCVCVDUFVDVCTBCEUGCVDVCBCVCVHEUHV
      DPZUIVCVCVDUJUKVBHULZVCJZUMZVKDLZVFVKAUNZVKVDLVMAVETZVGVNVOUOVBVPVLVBVEVC
      AVISURQNVCVFVKADGUPRVKABCVDVCVHEFVJUSUTVA $.
  $}

  ${
    nvm.1 $e |- X = ( BaseSet ` U ) $.
    nvm.2 $e |- G = ( +v ` U ) $.
    nvm.3 $e |- M = ( -v ` U ) $.
    nvm.6 $e |- N = ( /g ` G ) $.
    $( Vector subtraction in terms of group division operation.  (Contributed
       by NM, 15-Feb-2008.)  (New usage is discouraged.) $)
    nvm $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
          ( A M B ) = ( A N B ) ) $=
      ( co wceq cnv wcel w3a cgs cfv vsfval eqtr4i oveqi a1i ) ABELABFLMCNOAGOB
      GOPEFABEDQRFCDEIJSKTUAUB $.
  $}

  ${
    $d x y G $.  $d x y U $.  $d x y X $.
    nvmval.1 $e |- X = ( BaseSet ` U ) $.
    nvmval.2 $e |- G = ( +v ` U ) $.
    nvmval.4 $e |- S = ( .sOLD ` U ) $.
    nvmval.3 $e |- M = ( -v ` U ) $.
    $( Value of vector subtraction on a normed complex vector space.
       (Contributed by NM, 11-Sep-2007.)  (New usage is discouraged.) $)
    nvmval $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                ( A M B ) = ( A G ( -u 1 S B ) ) ) $=
      ( cnv wcel w3a cgs cfv co cgn wceq eqid cneg cgr nvgrp grpodivval syl3an1
      c1 bafval nvm nvinv 3adant2 oveq2d 3eqtr4d ) DLMZAGMZBGMZNZABEOPZQZABERPZ
      PZEQZABFQAUFUABCQZEQUMEUBMUNUOURVASDEIUCABUQEUSGDEGHIUGUSTZUQTZUDUEABDEFU
      QGHIKVDUHUPVBUTAEUMUOVBUTSUNBCDEUSGHIJVCUIUJUKUL $.

    $( Value of vector subtraction on a normed complex vector space.
       (Contributed by Mario Carneiro, 19-Nov-2013.)
       (New usage is discouraged.) $)
    nvmval2 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                ( A M B ) = ( ( -u 1 S B ) G A ) ) $=
      ( cnv wcel w3a co c1 cneg nvmval wceq cc neg1cn nvscl 3adant2 nvcom eqtrd
      mp3an2 syld3an3 ) DLMZAGMZBGMZNABFOAPQZBCOZEOZULAEOZABCDEFGHIJKRUHUIUJULG
      MZUMUNSUHUJUOUIUHUKTMUJUOUAUKBCDGHJUBUFUCAULDEGHIUDUGUE $.

    $( Value of the function for the vector subtraction operation on a normed
       complex vector space.  (Contributed by NM, 11-Sep-2007.)  (Revised by
       Mario Carneiro, 23-Dec-2013.)  (New usage is discouraged.) $)
    nvmfval $p |- ( U e. NrmCVec -> M = ( x e. X , y e. X |->
                    ( x G ( -u 1 S y ) ) ) ) $=
      ( cnv wcel cv cgn cfv co cmpo c1 wceq cgr nvgrp bafval vsfval grpodivfval
      cneg eqid syl w3a nvinv 3adant2 oveq2d mpoeq3dva eqtr4d ) DLMZFABGGANZBNZ
      EOPZPZEQZRZABGGUPSUFUQCQZEQZRUOEUAMFVATDEIUBABFEURGDEGHIUCURUGZDEFIKUDUEU
      HUOABGGVCUTUOUPGMZUQGMZUIVBUSUPEUOVFVBUSTVEUQCDEURGHIJVDUJUKULUMUN $.
  $}

  ${
    $d x y U $.  $d x y X $.
    nvmf.1 $e |- X = ( BaseSet ` U ) $.
    nvmf.3 $e |- M = ( -v ` U ) $.
    $( Mapping for the vector subtraction operation.  (Contributed by NM,
       11-Sep-2007.)  (Revised by Mario Carneiro, 23-Dec-2013.)
       (New usage is discouraged.) $)
    nvmf $p |- ( U e. NrmCVec -> M : ( X X. X ) --> X ) $=
      ( vx vy cnv wcel cxp wf cv c1 cneg cns cfv co wral wa eqid cpv cmpo simpl
      simprl cc neg1cn nvscl mp3an2 adantrl nvgcl syl3anc ralrimivva fmpo sylib
      nvmfval feq1d mpbird ) AHIZCCJZCBKUSCFGCCFLZMNZGLZAOPZQZAUAPZQZUBZKZURVFC
      IZGCRFCRVHURVIFGCCURUTCIZVBCIZSZSURVJVDCIZVIURVLUCURVJVKUDURVKVMVJURVAUEI
      VKVMUFVAVBVCACDVCTZUGUHUIUTVDAVECDVETZUJUKULFGCCVFCVGVGTUMUNURUSCBVGFGVCA
      VEBCDVOVNEUOUPUQ $.

    $( Closure law for the vector subtraction operation of a normed complex
       vector space.  (Contributed by NM, 11-Sep-2007.)
       (New usage is discouraged.) $)
    nvmcl $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A M B ) e. X ) $=
      ( cnv wcel cxp wf co nvmf fovcdm syl3an1 ) CHIEEJEDKAEIBEIABDLEICDEFGMABE
      EEDNO $.

    $( Cancellation law for vector subtraction.  ( ~ nnncan1 analog.)
       (Contributed by NM, 7-Mar-2008.)  (New usage is discouraged.) $)
    nvnnncan1 $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
         ( ( A M B ) M ( A M C ) ) = ( C M B ) ) $=
      ( cnv wcel cpv cfv cablo w3a co wceq eqid nvablo bafval vsfval sylan
      ablonnncan1 ) DIJDKLZMJAFJBFJCFJNABEOACEOEOCBEOPDUCUCQZRABCEUCFDUCFGUDSDU
      CEUDHTUBUA $.
  $}

  ${
    nvmdi.1 $e |- X = ( BaseSet ` U ) $.
    nvmdi.3 $e |- M = ( -v ` U ) $.
    nvmdi.4 $e |- S = ( .sOLD ` U ) $.
    $( Distributive law for scalar product over subtraction.  (Contributed by
       NM, 14-Feb-2008.)  (New usage is discouraged.) $)
    nvmdi $p |- ( ( U e. NrmCVec /\ ( A e. CC /\ B e. X /\ C e. X ) ) ->
       ( A S ( B M C ) ) = ( ( A S B ) M ( A S C ) ) ) $=
      ( cnv wcel cc w3a co wceq neg1cn nvscl oveq2d nvmval wa c1 cpv cfv simpr1
      cneg simpr2 mp3an2 3ad2antr3 3jca eqid nvdi syldan mp3anr2 3adantr2 eqtrd
      nvscom 3adant3r1 simpl 3adant3r3 3adant3r2 syl3anc 3eqtr4d ) EKLZAMLZBGLZ
      CGLZNZUAZABUBUFZCDOZEUCUDZOZDOZABDOZVJACDOZDOZVLOZABCFOZDOVOVPFOZVIVNVOAV
      KDOZVLOZVRVDVHVEVFVKGLZNVNWBPVIVEVFWCVDVEVFVGUEVDVEVFVGUGVDVEVGWCVFVDVJML
      ZVGWCQVJCDEGHJRUHUIUJABVKDEVLGHVLUKZJULUMVIWAVQVOVLVDVEVGWAVQPZVFVDVEWDVG
      WFQAVJCDEGHJUQUNUOSUPVIVSVMADVDVFVGVSVMPVEBCDEVLFGHWEJITURSVIVDVOGLZVPGLZ
      VTVRPVDVHUSVDVEVFWGVGABDEGHJRUTVDVEVGWHVFACDEGHJRVAVOVPDEVLFGHWEJITVBVC
      $.
  $}

  ${
    nvnegneg.1 $e |- X = ( BaseSet ` U ) $.
    nvnegneg.4 $e |- S = ( .sOLD ` U ) $.
    $( Double negative of a vector.  (Contributed by NM, 4-Dec-2007.)
       (New usage is discouraged.) $)
    nvnegneg $p |- ( ( U e. NrmCVec /\ A e. X ) ->
                  ( -u 1 S ( -u 1 S A ) ) = A ) $=
      ( cnv wcel wa c1 cneg co cpv cfv cgn wceq cc neg1cn eqid nvinv mp3an2 cgr
      nvscl syldan fveq2d nvgrp bafval grpo2inv sylan 3eqtrd ) CGHZADHZIZJKZUNA
      BLZBLZUOCMNZONZNZAURNZURNZAUKULUODHZUPUSPUKUNQHULVBRUNABCDEFUCUAUOBCUQURD
      EUQSZFURSZTUDUMUOUTURABCUQURDEVCFVDTUEUKUQUBHULVAAPCUQVCUFAUQURDCUQDEVCUG
      VDUHUIUJ $.
  $}

  ${
    nvmul0or.1 $e |- X = ( BaseSet ` U ) $.
    nvmul0or.4 $e |- S = ( .sOLD ` U ) $.
    nvmul0or.6 $e |- Z = ( 0vec ` U ) $.
    $( If a scalar product is zero, one of its factors must be zero.
       (Contributed by NM, 6-Dec-2007.)  (New usage is discouraged.) $)
    nvmul0or $p |- ( ( U e. NrmCVec /\ A e. CC /\ B e. X ) ->
                    ( ( A S B ) = Z <-> ( A = 0 \/ B = Z ) ) ) $=
      ( wcel cc co wceq cc0 wa c1 oveq2 3ad2antl2 3adant2 3eqtr3d cnv w3a wo wn
      wne df-ne cdiv ad2antlr recid2 oveq1d simpl1 reccl simpl2 simpl3 syl13anc
      cmul nvsass adantr adantlr nvsz sylan2 anassrs 3adantl3 ex biimtrrid orrd
      nvsid wi nv0 oveq1 eqeq1d syl5ibrcom 3adant3 jaod impbid ) DUAJZAKJZBEJZU
      BZABCLZFMZANMZBFMZUCZVSWAWDVSWAOZWBWCWBUDANUEZWEWCANUFWEWFWCWEWFOPAUGLZVT
      CLZWGFCLZBFWAWHWIMVSWFVTFWGCQUHVSWFWHBMWAVSWFOZWGAUPLZBCLZPBCLZWHBVQVPWFW
      LWMMVRVQWFOZWKPBCAUIUJRWJVPWGKJZVQVRWLWHMVPVQVRWFUKVQVPWFWOVRAULZRVPVQVRW
      FUMVPVQVRWFUNWGABCDEGHUQUOVSWMBMZWFVPVRWQVQBCDEGHVGSURTUSVSWFWIFMZWAVPVQW
      FWRVRVPVQWFWRWNVPWOWRWPWGCDFHIUTVAVBVCUSTVDVEVFVDVSWBWAWCVPVRWBWAVHVQVPVR
      OWAWBNBCLZFMBCDEFGHIVIWBVTWSFANBCVJVKVLSVPVQWCWAVHVRVPVQOWAWCAFCLZFMACDFH
      IUTWCVTWTFBFACQVKVLVMVNVO $.
  $}

  ${
    nvrinv.1 $e |- X = ( BaseSet ` U ) $.
    nvrinv.2 $e |- G = ( +v ` U ) $.
    nvrinv.4 $e |- S = ( .sOLD ` U ) $.
    nvrinv.6 $e |- Z = ( 0vec ` U ) $.
    $( A vector minus itself.  (Contributed by NM, 4-Dec-2007.)  (Revised by
       Mario Carneiro, 21-Dec-2013.)  (New usage is discouraged.) $)
    nvrinv $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( A G ( -u 1 S A ) ) = Z ) $=
      ( cnv wcel wa cgn cfv co cgi c1 wceq eqid cgr nvgrp bafval grporinv sylan
      cneg nvinv oveq2d 0vfval adantr 3eqtr4d ) CKLZAELZMZAADNOZOZDPZDQOZARUFAB
      PZDPFULDUALUMUQURSCDHUBAURDUOECDEGHUCURTUOTZUDUEUNUSUPADABCDUOEGHIUTUGUHU
      LFURSUMCDKFHJUIUJUK $.

    $( Minus a vector plus itself.  (Contributed by NM, 4-Dec-2007.)  (Revised
       by Mario Carneiro, 21-Dec-2013.)  (New usage is discouraged.) $)
    nvlinv $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( ( -u 1 S A ) G A ) = Z ) $=
      ( cnv wcel wa cgn cfv co cgi c1 wceq eqid cgr nvgrp bafval grpolinv sylan
      cneg nvinv oveq1d 0vfval adantr 3eqtr4d ) CKLZAELZMZADNOZOZADPZDQOZRUFABP
      ZADPFULDUALUMUQURSCDHUBAURDUOECDEGHUCURTUOTZUDUEUNUSUPADABCDUOEGHIUTUGUHU
      LFURSUMCDKFHJUIUJUK $.
  $}

  ${
    nvpncan2.1 $e |- X = ( BaseSet ` U ) $.
    nvpncan2.2 $e |- G = ( +v ` U ) $.
    nvpncan2.3 $e |- M = ( -v ` U ) $.
    $( Cancellation law for vector subtraction.  (Contributed by NM,
       27-Dec-2007.)  (New usage is discouraged.) $)
    nvpncan2 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                 ( ( A G B ) M A ) = B ) $=
      ( cnv wcel w3a co c1 cneg cfv wceq eqid 3adant3 eqtrd simp1 nvgcl syl3anc
      cns simp2 nvmval simp3 neg1cn nvscl mp3an2 nvadd32 syl13anc nvrinv oveq1d
      cc cn0v nv0lid 3adant2 ) CJKZAFKZBFKZLZABDMZAEMZVCNOZACUDPZMZDMZBVBUSVCFK
      UTVDVHQUSUTVAUAZABCDFGHUBUSUTVAUEZVCAVFCDEFGHVFRZIUFUCVBVHAVGDMZBDMZBVBUS
      UTVAVGFKZVHVMQVIVJUSUTVAUGUSUTVNVAUSVEUOKUTVNUHVEAVFCFGVKUIUJSABVGCDFGHUK
      ULVBVMCUPPZBDMZBVBVLVOBDUSUTVLVOQVAAVFCDFVOGHVKVORZUMSUNUSVAVPBQUTBCDFVOG
      HVQUQURTTT $.

    $( Cancellation law for vector subtraction.  (Contributed by NM,
       24-Jan-2008.)  (New usage is discouraged.) $)
    nvpncan $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                 ( ( A G B ) M B ) = A ) $=
      ( cnv wcel co wceq w3a nvcom oveq1d nvpncan2 eqtr3d 3com23 ) CJKZBFKZAFKZ
      ABDLZBELZAMTUAUBNZBADLZBELUDAUEUFUCBEBACDFGHOPBACDEFGHIQRS $.

    $( Commutative/associative law for vector addition and subtraction.
       (Contributed by NM, 24-Jan-2008.)  (New usage is discouraged.) $)
    nvaddsub $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
      ( ( A G B ) M C ) = ( ( A M C ) G B ) ) $=
      ( cnv wcel cablo w3a co wceq nvablo bafval vsfval ablomuldiv sylan ) DKLE
      MLAGLBGLCGLNABEOCFOACFOBEOPDEIQABCFEGDEGHIRDEFIJSTUA $.

    $( Cancellation law for a normed complex vector space.  (Contributed by NM,
       24-Jan-2008.)  (New usage is discouraged.) $)
    nvnpcan $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
         ( ( A M B ) G B ) = A ) $=
      ( cnv wcel w3a co wceq wa simprl simprr 3jca nvaddsub syldan 3impb eqtr3d
      nvpncan ) CJKZAFKZBFKZLABDMBEMZABEMBDMZAUDUEUFUGUHNZUDUEUFOZUEUFUFLUIUDUJ
      OUEUFUFUDUEUFPUDUEUFQZUKRABBCDEFGHISTUAABCDEFGHIUCUB $.

    $( Rearrangement of 4 terms in a mixed vector addition and subtraction.
       (Contributed by NM, 8-Feb-2008.)  (New usage is discouraged.) $)
    nvaddsub4 $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X ) /\ ( C e. X /\
       D e. X ) ) -> ( ( A G B ) M ( C G D ) ) = ( ( A M C ) G ( B M D ) ) ) $=
      ( wcel wa co wceq neg1cn 3adant2 nvscl mp3an2 nvmval cnv w3a cneg cns cfv
      c1 cc eqid nvdi mp3anr1 oveq2d anim12dan syld3an3 eqtrd simp1 nvgcl 3expb
      3adant3 syl3anc 3adant3r 3adant2r 3adant3l 3adant2l oveq12d 3eqtr4d
      nvadd4 ) EUALZAHLZBHLZMZCHLZDHLZMZUBZABFNZUFUCZCDFNZEUDUEZNZFNZAVPCVRNZFN
      ZBVPDVRNZFNZFNZVOVQGNZACGNZBDGNZFNVNVTVOWAWCFNZFNZWEVNVSWIVOFVGVMVSWIOZVJ
      VGVPUGLZVKVLWKPVPCDVREFHIJVRUHZUIUJQUKVGVJVMWAHLZWCHLZMZWJWEOVGVMWPVJVGVK
      WNVLWOVGWLVKWNPVPCVREHIWMRSVGWLVLWOPVPDVREHIWMRSULQABWAWCEFHIJVFUMUNVNVGV
      OHLZVQHLZWFVTOVGVJVMUOVGVJWQVMVGVHVIWQABEFHIJUPUQURVGVMWRVJVGVKVLWRCDEFHI
      JUPUQQVOVQVREFGHIJWMKTUSVNWGWBWHWDFVGVHVMWGWBOZVIVGVHVKWSVLACVREFGHIJWMKT
      UTVAVGVIVMWHWDOZVHVGVIVLWTVKBDVREFGHIJWMKTVBVCVDVE $.
  $}

  ${
    nvmeq0.1 $e |- X = ( BaseSet ` U ) $.
    nvmeq0.3 $e |- M = ( -v ` U ) $.
    nvmeq0.5 $e |- Z = ( 0vec ` U ) $.
    $( The difference between two vectors is zero iff they are equal.
       (Contributed by NM, 24-Jan-2008.)  (New usage is discouraged.) $)
    nvmeq0 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
            ( ( A M B ) = Z <-> A = B ) ) $=
      ( cnv wcel w3a co cpv cfv wceq wb wa nvmcl 3expb nvzcl adantr simprr 3jca
      eqid nvrcan syldan 3impb nvnpcan nv0lid 3adant2 eqeq12d bitr3d ) CJKZAEKZ
      BEKZLZABDMZBCNOZMZFBUSMZPZURFPZABPUNUOUPVBVCQZUNUOUPRZUREKZFEKZUPLVDUNVER
      VFVGUPUNUOUPVFABCDEGHSTUNVGVECEFGIUAUBUNUOUPUCUDURFBCUSEGUSUEZUFUGUHUQUTA
      VABABCUSDEGVHHUIUNUPVABPUOBCUSEFGVHIUJUKULUM $.

    $( A vector minus itself is the zero vector.  (Contributed by NM,
       28-Jan-2008.)  (New usage is discouraged.) $)
    nvmid $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( A M A ) = Z ) $=
      ( cnv wcel wa co wceq eqid wb nvmeq0 3anidm23 mpbiri ) BIJZADJZKAACLEMZAA
      MZANSTUAUBOAABCDEFGHPQR $.
  $}

  ${
    $d x y N $.  $d x y U $.  $d x y X $.
    nvf.1 $e |- X = ( BaseSet ` U ) $.
    nvf.6 $e |- N = ( normCV ` U ) $.
    $( Mapping for the norm function.  (Contributed by NM, 11-Nov-2006.)
       (New usage is discouraged.) $)
    nvf $p |- ( U e. NrmCVec -> N : X --> RR ) $=
      ( vx vy cnv wcel cpv cfv cns cop cvc cr cv wceq co wral eqid wf cn0v cabs
      cc0 wi cmul cc caddc cle wbr w3a nvi simp2d ) AHIAJKZALKZMNICOBUAFPZBKZUD
      QUPAUBKZQUEGPZUPUORBKUSUCKUQUFRQGUGSUPUSUNRBKUQUSBKUHRUIUJGCSUKFCSFGUOAUN
      BCURDUNTUOTURTEULUM $.

    $( The norm of a normed complex vector space is a real number.
       (Contributed by NM, 24-Nov-2006.)  (New usage is discouraged.) $)
    nvcl $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( N ` A ) e. RR ) $=
      ( cnv wcel cr nvf ffvelcdmda ) BGHDIACBCDEFJK $.

    ${
      nvcli.9 $e |- U e. NrmCVec $.
      nvcli.7 $e |- A e. X $.
      $( The norm of a normed complex vector space is a real number.
         (Contributed by NM, 20-Apr-2007.)  (New usage is discouraged.) $)
      nvcli $p |- ( N ` A ) e. RR $=
        ( cnv wcel cfv cr nvcl mp2an ) BIJADJACKLJGHABCDEFMN $.
    $}
  $}

  ${
    $d y A $.  $d x y B $.  $d x y N $.  $d x y S $.  $d x y U $.  $d x y X $.
    nvs.1 $e |- X = ( BaseSet ` U ) $.
    nvs.4 $e |- S = ( .sOLD ` U ) $.
    nvs.6 $e |- N = ( normCV ` U ) $.
    $( Proportionality property of the norm of a scalar product in a normed
       complex vector space.  (Contributed by NM, 11-Nov-2006.)
       (New usage is discouraged.) $)
    nvs $p |- ( ( U e. NrmCVec /\ A e. CC /\ B e. X ) ->
               ( N ` ( A S B ) ) = ( ( abs ` A ) x. ( N ` B ) ) ) $=
      ( vy vx wcel cc co cfv cabs cmul wceq cv wral cnv wa cc0 wi cpv caddc cle
      cn0v wbr w3a cop cvc cr wf nvi simp3d simp2 ralimi syl oveq2 fveq2d fveq2
      eqid oveq2d eqeq12d fvoveq1 oveq1d rspc2v syl5 3impia 3com13 ) BFLZAMLZDU
      ALZABCNEOZAPOZBEOZQNZRZVLVMVNVSVNJSZKSZCNZEOZVTPOZWAEOZQNZRZJMTZKFTZVLVMU
      BVSVNWEUCRWADUHOZRUDZWHWAVTDUEOZNEOWEVTEOUFNUGUIJFTZUJZKFTZWIVNWLCUKULLFU
      MEUNWOKJCDWLEFWJGWLVCHWJVCIUOUPWNWHKFWKWHWMUQURUSWGVSVTBCNZEOZWDVQQNZRKJB
      AFMWABRZWCWQWFWRWSWBWPEWABVTCUTVAWSWEVQWDQWABEVBVDVEVTARZWQVOWRVRVTABECVF
      WTWDVPVQQVTAPVBVGVEVHVIVJVK $.

    $( The norm of a scalar product with a nonnegative real.  (Contributed by
       NM, 1-Jan-2008.)  (New usage is discouraged.) $)
    nvsge0 $p |- ( ( U e. NrmCVec /\ ( A e. RR /\ 0 <_ A ) /\ B e. X ) ->
               ( N ` ( A S B ) ) = ( A x. ( N ` B ) ) ) $=
      ( cnv wcel cr cc0 cle wbr wa co cfv cmul wceq w3a cabs cc recn adantr nvs
      syl3an2 absid 3ad2ant2 oveq1d eqtrd ) DJKZALKZMANOZPZBFKZUAZABCQERZAUBRZB
      ERZSQZAUTSQUOULAUCKZUPURVATUMVBUNAUDUEABCDEFGHIUFUGUQUSAUTSUOULUSATUPAUHU
      IUJUK $.

    $( The norm of the negative of a vector.  (Contributed by NM, 28-Nov-2006.)
       (New usage is discouraged.) $)
    nvm1 $p |- ( ( U e. NrmCVec /\ A e. X ) ->
               ( N ` ( -u 1 S A ) ) = ( N ` A ) ) $=
      ( cnv wcel wa c1 cneg co cfv cabs cmul cc wceq neg1cn mp3an2 absnegi abs1
      nvs ax-1cn eqtri oveq1i nvcl recnd mullidd eqtrid eqtrd ) CIJZAEJZKZLMZAB
      NDOZUPPOZADOZQNZUSUMUPRJUNUQUTSTUPABCDEFGHUDUAUOUTLUSQNUSURLUSQURLPOLLUEU
      BUCUFUGUOUSUOUSACDEFHUHUIUJUKUL $.
  $}

  ${
    nvdif.1 $e |- X = ( BaseSet ` U ) $.
    nvdif.2 $e |- G = ( +v ` U ) $.
    nvdif.4 $e |- S = ( .sOLD ` U ) $.
    nvdif.6 $e |- N = ( normCV ` U ) $.
    $( The norm of the difference between two vectors.  (Contributed by NM,
       1-Dec-2006.)  (New usage is discouraged.) $)
    nvdif $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
               ( N ` ( A G ( -u 1 S B ) ) ) = ( N ` ( B G ( -u 1 S A ) ) ) ) $=
      ( wcel co cfv wceq neg1cn nvscl mp3an2 3adant3 syl3anc cnv w3a c1 cneg cc
      simp1 a1i simp3 nvdi syl13anc nvnegneg oveq2d 3adant2 simp2 3eqtrd fveq2d
      nvcom nvgcl nvm1 syl2anc eqtr3d ) DUALZAGLZBGLZUBZUCUDZBVFACMZEMZCMZFNZAV
      FBCMZEMZFNVHFNZVEVIVLFVEVIVKVFVGCMZEMZVKAEMZVLVEVBVFUELZVDVGGLZVIVOOVBVCV
      DUFZVQVEPUGVBVCVDUHZVBVCVRVDVBVQVCVRPVFACDGHJQRSZVFBVGCDEGHIJUIUJVEVNAVKE
      VBVCVNAOVDACDGHJUKSULVEVBVKGLZVCVPVLOVSVBVDWBVCVBVQVDWBPVFBCDGHJQRUMVBVCV
      DUNVKADEGHIUQTUOUPVEVBVHGLZVJVMOVSVEVBVDVRWCVSVTWABVGDEGHIURTVHCDFGHJKUSU
      TVA $.

    $( The norm of a vector plus the imaginary scalar product of another.
       (Contributed by NM, 2-Feb-2007.)  (New usage is discouraged.) $)
    nvpi $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
               ( N ` ( A G ( _i S B ) ) ) = ( N ` ( B G ( -u _i S A ) ) ) ) $=
      ( wcel c1 ci co cfv cmul cneg ax-icn wceq cnv w3a cr simp1 mp3an2 3adant2
      nvscl nvgcl syld3an3 nvcl syl2anc recnd mullidd cabs absnegi eqtri oveq1i
      absi negicn nvs simp2 nvdi mp3anr1 syl12anc mulneg1i ixi negeqi negneg1e1
      cc nvsass mpanr1 nvsid 3eqtr3a oveq2d nvcom syld3an2 3eqtrd fveq2d eqtr3d
      wa 3adant3 eqtr3id ) DUALZAGLZBGLZUBZMANBCOZEOZFPZQOZWIBNRZACOZEOZFPZWFWI
      WFWIWFWCWHGLZWIUCLWCWDWEUDZWCWDWEWGGLZWOWCWEWQWDWCNVILZWEWQSNBCDGHJUGUEUF
      ZAWGDEGHIUHUIZWHDFGHKUJUKULUMWFWJWKUNPZWIQOZWNXAMWIQXANUNPMNSUOURUPUQWFWK
      WHCOZFPZXBWNWFWCWOXDXBTZWPWTWCWKVILZWOXEUSWKWHCDFGHJKUTUEUKWFXCWMFWFXCWLW
      KWGCOZEOZWLBEOZWMWFWCWDWQXCXHTZWPWCWDWEVAWSWCXFWDWQXJUSWKAWGCDEGHIJVBVCVD
      WFXGBWLEWCWEXGBTWDWCWEVTWKNQOZBCOZMBCOXGBXKMBCXKNNQOZRZMNNSSVEXNMRZRMXMXO
      VFVGVHUPUPUQWCWRWEXLXGTZSWCXFWRWEXPUSWKNBCDGHJVJVCVKBCDGHJVLVMUFVNWCWLGLZ
      WDWEXIWMTWCWDXQWEWCXFWDXQUSWKACDGHJUGUEWAWLBDEGHIVOVPVQVRVSWBVS $.
  $}

  ${
    nvz0.5 $e |- Z = ( 0vec ` U ) $.
    nvz0.6 $e |- N = ( normCV ` U ) $.
    $( The norm of a zero vector is zero.  (Contributed by NM, 24-Nov-2006.)
       (New usage is discouraged.) $)
    nvz0 $p |- ( U e. NrmCVec -> ( N ` Z ) = 0 ) $=
      ( cnv wcel cc0 cns cfv co cmul cba wceq eqid nvzcl cr cle wa mpdan pm3.2i
      wbr 0re 0le0 nvsge0 mp3an2 nv0 fveq2d cc nvcl recnd mul02d 3eqtr3d ) AFGZ
      HCAIJZKZBJZHCBJZLKZURHUNCAMJZGZUQUSNZAUTCUTOZDPZUNHQGZHHRUBZSVAVBVEVFUCUD
      UAHCUOABUTVCUOOZEUEUFTUNUPCBUNVAUPCNVDCUOAUTCVCVGDUGTUHUNURUNVAURUIGVDUNV
      ASURCABUTVCEUJUKTULUM $.
  $}

  ${
    $d x A $.  $d x y N $.  $d x y U $.  $d x y X $.  $d x Z $.
    nvz.1 $e |- X = ( BaseSet ` U ) $.
    nvz.5 $e |- Z = ( 0vec ` U ) $.
    nvz.6 $e |- N = ( normCV ` U ) $.
    $( The norm of a vector is zero iff the vector is zero.  First part of
       Problem 2 of [Kreyszig] p. 64.  (Contributed by NM, 24-Nov-2006.)
       (New usage is discouraged.) $)
    nvz $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( ( N ` A ) = 0 <-> A = Z ) ) $=
      ( vx vy cnv wcel cfv cc0 wceq wi cv co wral eqid wa cns cabs cc cpv caddc
      cmul cle wbr w3a cop cvc cr nvi simp3d simp1 ralimi fveqeq2 eqeq1 imbi12d
      wf rspccv 3syl imp fveq2 nvz0 sylan9eqr ex adantr impbid ) BKLZADLZUAACMZ
      NOZAEOZVKVLVNVOPZVKIQZCMZNOZVQEOZPZJQZVQBUBMZRCMWBUCMVRUGROJUDSZVQWBBUEMZ
      RCMVRWBCMUFRUHUIJDSZUJZIDSZWAIDSVLVPPVKWEWCUKULLDUMCVAWHIJWCBWECDEFWETWCT
      GHUNUOWGWAIDWAWDWFUPUQWAVPIADVQAOVSVNVTVOVQANCURVQAEUSUTVBVCVDVKVOVNPVLVK
      VOVNVOVKVMECMNAECVEBCEGHVFVGVHVIVJ $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y G $.  $d x y N $.  $d x y U $.  $d x y X $.
    nvtri.1 $e |- X = ( BaseSet ` U ) $.
    nvtri.2 $e |- G = ( +v ` U ) $.
    nvtri.6 $e |- N = ( normCV ` U ) $.
    $( Triangle inequality for the norm of a normed complex vector space.
       (Contributed by NM, 11-Nov-2006.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.) $)
    nvtri $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
          ( N ` ( A G B ) ) <_ ( ( N ` A ) + ( N ` B ) ) ) $=
      ( vx vy wcel co cfv caddc cle wbr cv wral wceq cnv wa cn0v c1st c2nd cabs
      cc0 wi cmul cc w3a cop cvc cr wf cns eqid smfval eqcomi nvi simp3d ralimi
      simp3 fvoveq1 fveq2 oveq1d breq12d oveq2 fveq2d oveq2d rspc2v syl5 3impia
      syl 3comr ) AFLZBFLZCUALZABDMZENZAENZBENZOMZPQZVPVQVRWDVRJRZKRZDMENZWEENZ
      WFENZOMZPQZKFSZJFSZVPVQUBWDVRWHUGTWECUCNZTUHZWFWECUDNUENZMENWFUFNWHUIMTKU
      JSZWLUKZJFSZWMVRDWPULUMLFUNEUOWSJKWPCDEFWNGHCUPNZWPWTCWTUQURUSWNUQIUTVAWR
      WLJFWOWQWLVCVBVNWKWDAWFDMZENZWAWIOMZPQJKABFFWEATZWGXBWJXCPWEAWFEDVDXDWHWA
      WIOWEAEVEVFVGWFBTZXBVTXCWCPXEXAVSEWFBADVHVIXEWIWBWAOWFBEVEVJVGVKVLVMVO $.
  $}

  ${
    nvmtri.1 $e |- X = ( BaseSet ` U ) $.
    nvmtri.3 $e |- M = ( -v ` U ) $.
    nvmtri.6 $e |- N = ( normCV ` U ) $.
    $( Triangle inequality for the norm of a vector difference.  (Contributed
       by NM, 27-Dec-2007.)  (New usage is discouraged.) $)
    nvmtri $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
          ( N ` ( A M B ) ) <_ ( ( N ` A ) + ( N ` B ) ) ) $=
      ( wcel c1 cfv co caddc cle neg1cn eqid mp3an2 3adant2 cmul cnv w3a cns cc
      cneg cpv wbr nvscl syld3an3 nvmval fveq2d wceq wa cabs nvs ax-1cn absnegi
      nvtri abs1 eqtri oveq1i nvcl recnd mullidd eqtrid eqtr2d oveq2d 3brtr4d )
      CUAJZAFJZBFJZUBZAKUEZBCUCLZMZCUFLZMZELZAELZVOELZNMZABDMZELVSBELZNMOVIVJVK
      VOFJZVRWAOUGVIVKWDVJVIVMUDJZVKWDPVMBVNCFGVNQZUHRSAVOCVPEFGVPQZIURUIVLWBVQ
      EABVNCVPDFGWGWFHUJUKVLWCVTVSNVIVKWCVTULVJVIVKUMZVTVMUNLZWCTMZWCVIWEVKVTWJ
      ULPVMBVNCEFGWFIUORWHWJKWCTMWCWIKWCTWIKUNLKKUPUQUSUTVAWHWCWHWCBCEFGIVBVCVD
      VEVFSVGVH $.
  $}

  ${
    nvabs.1 $e |- X = ( BaseSet ` U ) $.
    nvabs.2 $e |- G = ( +v ` U ) $.
    nvabs.4 $e |- S = ( .sOLD ` U ) $.
    nvabs.6 $e |- N = ( normCV ` U ) $.
    $( Norm difference property of a normed complex vector space.  Problem 3 of
       [Kreyszig] p. 64.  (Contributed by NM, 4-Dec-2006.)
       (New usage is discouraged.) $)
    nvabs $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
       ( abs ` ( ( N ` A ) - ( N ` B ) ) ) <_ ( N ` ( A G ( -u 1 S B ) ) ) ) $=
      ( wcel cfv co cle wbr cr nvcl 3adant2 wceq cnv w3a cmin cabs nvdif negeqd
      c1 cneg 3adant3 simp1 neg1cn nvscl mp3an2 nvgcl syld3an3 syl2anc renegcld
      cc 3com23 caddc nvcom cn0v wa simprr adantrr simprl 3jca nvass 3impb eqid
      syldan nvlinv oveq2d nv0rid 3eqtrd eqtrd fveq2d eqbrtrrd subnegd breqtrrd
      nvtri recnd lesubd eqbrtrd simp2 simp3 syl13anc syld3an2 lesubaddd mpbird
      resubcld absled mpbir2and ) DUALZAGLZBGLZUBZAFMZBFMZUCNZUDMAUGUHZBCNZENZF
      MZOPXDUHZWTOPWTXDOPZWQXEBXAACNZENZFMZUHZWTOWQXDXIABCDEFGHIJKUEUFWQWSWRXJW
      NWPWSQLWOBDFGHKRSZWNWOWRQLWPADFGHKRUIZWQXIWQWNXHGLZXIQLWNWOWPUJZWNWPWOXMW
      NWPWOXGGLZXMWNWOXOWPWNXAURLZWOXOUKXAACDGHJULUMZSBXGDEGHIUNUOUSZXHDFGHKRUP
      ZUQWQWSWRXIUTNZWRXJUCNOWQAXHENZFMZWSXTOWQYABFWQYAXHAENZBWNWOWPXMYAYCTXRAX
      HDEGHIVAUOWQYCBXGAENZENZBDVBMZENZBWNWOWPYCYETZWNWOWPVCZWPXOWOUBYHWNYIVCWP
      XOWOWNWOWPVDWNWOXOWPXQVEWNWOWPVFVGBXGADEGHIVHVKVIWQYDYFBEWNWOYDYFTWPACDEG
      YFHIJYFVJZVLUIVMWNWPYGBTWOBDEGYFHIYJVNSVOVPVQWNWOWPXMYBXTOPXRAXHDEFGHIKWA
      UOVRWQWRXIWQWRXLWBWQXIXSWBVSVTWCWDWQXFWRXDWSUTNZOPWQXCBENZFMZWRYKOWQYLAFW
      QYLAXBBENZENZAYFENZAWQWNWOXBGLZWPYLYOTXNWNWOWPWEWNWPYQWOWNXPWPYQUKXABCDGH
      JULUMSZWNWOWPWFAXBBDEGHIVHWGWQYNYFAEWNWPYNYFTWOBCDEGYFHIJYJVLSVMWNWOYPATW
      PADEGYFHIYJVNUIVOVQWNXCGLZWOWPYMYKOPWNWOWPYQYSYRAXBDEGHIUNUOZXCBDEFGHIKWA
      WHVRWQWRWSXDXLXKWQWNYSXDQLXNYTXCDFGHKRUPZWIWJWQWTXDWQWRWSXLXKWKUUAWLWM $.
  $}

  ${
    nvge0.1 $e |- X = ( BaseSet ` U ) $.
    nvge0.6 $e |- N = ( normCV ` U ) $.
    $( The norm of a normed complex vector space is nonnegative.  Second part
       of Problem 2 of [Kreyszig] p. 64.  (Contributed by NM, 28-Nov-2006.)
       (Proof shortened by AV, 10-Jul-2022.)  (New usage is discouraged.) $)
    nvge0 $p |- ( ( U e. NrmCVec /\ A e. X ) -> 0 <_ ( N ` A ) ) $=
      ( cnv wcel wa c2 cfv cc0 c1 co caddc cle wceq eqid cc neg1cn crp 2rp nvcl
      a1i cneg cns cmul cpv cn0v nvz0 adantr 1pneg1e0 oveq1i nv0 eqtr2id ax-1cn
      nvdir mp3anr1 mpanr1 nvsid oveq1d 3eqtrd fveq2d eqtr3d nvscl mp3an2 nvtri
      wbr mpd3an3 eqbrtrd nvm1 oveq2d recnd 2timesd eqtr4d breqtrd prodge0rd )
      BGHZADHZIZJACKZJUAHVTUBUDABCDEFUCZVTLWAMUEZABUFKZNZCKZONZJWAUGNZPVTLAWEBU
      HKZNZCKZWGPVTBUIKZCKZLWKVRWMLQVSBCWLWLRZFUJUKVTWLWJCVTWLMWCONZAWDNZMAWDNZ
      WEWINZWJVTWPLAWDNWLWOLAWDULUMAWDBDWLEWDRZWNUNUOVRWCSHZVSWPWRQZTVRMSHWTVSX
      AUPMWCAWDBWIDEWIRZWSUQURUSVTWQAWEWIAWDBDEWSUTVAVBVCVDVRVSWEDHZWKWGPVHVRWT
      VSXCTWCAWDBDEWSVEVFAWEBWICDEXBFVGVIVJVTWGWAWAONWHVTWFWAWAOAWDBCDEWSFVKVLV
      TWAVTWAWBVMVNVOVPVQ $.
  $}

  ${
    nvgt0.1 $e |- X = ( BaseSet ` U ) $.
    nvgt0.5 $e |- Z = ( 0vec ` U ) $.
    nvgt0.6 $e |- N = ( normCV ` U ) $.
    $( A nonzero norm is positive.  (Contributed by NM, 20-Nov-2007.)
       (New usage is discouraged.) $)
    nvgt0 $p |- ( ( U e. NrmCVec /\ A e. X ) ->
                   ( A =/= Z <-> 0 < ( N ` A ) ) ) $=
      ( cnv wcel wa cfv cc0 wne clt wbr nvz necon3bid cr cle nvcl nvge0 syl2anc
      wb ne0gt0 bitr3d ) BIJADJKZACLZMNZAENMUHOPZUGUHMAEABCDEFGHQRUGUHSJMUHTPUI
      UJUDABCDFHUAABCDFHUBUHUEUCUF $.
  $}

  ${
    nv1.1 $e |- X = ( BaseSet ` U ) $.
    nv1.4 $e |- S = ( .sOLD ` U ) $.
    nv1.5 $e |- Z = ( 0vec ` U ) $.
    nv1.6 $e |- N = ( normCV ` U ) $.
    $( From any nonzero vector, construct a vector whose norm is one.
       (Contributed by NM, 6-Dec-2007.)  (New usage is discouraged.) $)
    nv1 $p |- ( ( U e. NrmCVec /\ A e. X /\ A =/= Z ) ->
               ( N ` ( ( 1 / ( N ` A ) ) S A ) ) = 1 ) $=
      ( wcel wne c1 cfv co cr cc0 cle wbr 3adant3 cnv cdiv cmul wceq simp1 nvcl
      w3a wa nvz necon3bid biimp3ar rereccld clt nvgt0 biimp3a 1re 0le1 mpanl12
      divge0 syl2anc simp2 nvsge0 syl121anc cc recnd recid2d eqtrd ) CUAKZAEKZA
      FLZUGZMADNZUBOZABODNZVMVLUCOZMVKVHVMPKQVMRSZVIVNVOUDVHVIVJUEVKVLVHVIVLPKZ
      VJACDEGJUFZTZVHVIVLQLVJVHVIUHZVLQAFACDEFGIJUIUJUKZULVKVQQVLUMSZVPVSVHVIVJ
      WBACDEFGIJUNUOMPKQMRSVQWBUHVPUPUQMVLUSURUTVHVIVJVAVMABCDEGHJVBVCVKVLVHVIV
      LVDKVJVTVLVRVETWAVFVG $.
  $}

  ${
    nvop.2 $e |- G = ( +v ` U ) $.
    nvop.4 $e |- S = ( .sOLD ` U ) $.
    nvop.6 $e |- N = ( normCV ` U ) $.
    $( A complex inner product space in terms of ordered pair components.
       (Contributed by NM, 11-Sep-2007.)  (New usage is discouraged.) $)
    nvop $p |- ( U e. NrmCVec -> U = <. <. G , S >. , N >. ) $=
      ( cnv wcel c1st cfv c2nd cop wrel wceq nvrel 1st2nd mpan nmcvfval opeq2i
      eqid nvvop opeq1d eqtr3id eqtrd ) BHIZBBJKZBLKZMZCAMZDMZHNUFBUIOPBHQRUFUI
      UGDMUKDUHUGBDGSTUFUGUJDABCUGUGUAEFUBUCUDUE $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Examples of normed complex vector spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y $.
    cnnv.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The set of complex numbers is a normed complex vector space.  The vector
       operation is ` + ` , the scalar product is ` x. ` , and the norm
       function is ` abs ` .  (Contributed by Steve Rodriguez, 3-Dec-2006.)
       (New usage is discouraged.) $)
    cnnv $p |- U e. NrmCVec $=
      ( vx vy cmul caddc cabs cc cc0 cablo wcel cgr cnaddabloOLD ablogrpo ax-mp
      cxp ax-addf fdmi cv wceq grporn cnidOLD cncvcOLD absf abs00 biimpa absmul
      cfv abstri isnvi ) CDEAFGHIFHFJKFLKMFNOHHPHFQRUAUBUCUDCSZHKUKGUHITUKITUKU
      EUFDSZUKUGUKULUIBUJ $.
  $}

  ${
    cnnvg.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The vector addition (group) operation of the normed complex vector space
       of complex numbers.  (Contributed by NM, 12-Jan-2008.)
       (New usage is discouraged.) $)
    cnnvg $p |- + = ( +v ` U ) $=
      ( cpv cfv c1st caddc cmul cop eqid vafval cabs fveq2i opex cc cr cvv wcel
      wf absf op1st cnex fex mp2an eqtri addex mulex 3eqtrri ) ACDZAEDZEDFGHZED
      FAUHUHIJUIUJEUIUJKHZEDUJAUKEBLUJKFGMNOKRNPQKPQSUANOPKUBUCTUDLFGUEUFTUG $.
  $}

  ${
    cnnvba.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The base set of the normed complex vector space of complex numbers.
       (Contributed by NM, 7-Nov-2007.)  (New usage is discouraged.) $)
    cnnvba $p |- CC = ( BaseSet ` U ) $=
      ( caddc crn cpv cfv cc cnnvg rneqi cablo wcel cnaddabloOLD ablogrpo ax-mp
      cba cgr cxp ax-addf fdmi eqid grporn bafval 3eqtr4i ) CDAEFZDGAOFZCUDABHI
      CGCJKCPKLCMNGGQGCRSUAAUDUEUETUDTUBUC $.
  $}

  ${
    cnnvs.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The scalar product operation of the normed complex vector space of
       complex numbers.  (Contributed by NM, 12-Jan-2008.)
       (New usage is discouraged.) $)
    cnnvs $p |- x. = ( .sOLD ` U ) $=
      ( cns cfv c1st c2nd caddc cmul cop eqid smfval cabs fveq2i opex cc cr cvv
      wf wcel absf cnex fex mp2an op1st eqtri addex mulex op2nd 3eqtrri ) ACDZA
      EDZFDGHIZFDHUJAUJJKUKULFUKULLIZEDULAUMEBMULLGHNOPLROQSLQSTUAOPQLUBUCUDUEM
      GHUFUGUHUI $.
  $}

  ${
    cnnvnm.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The norm operation of the normed complex vector space of complex
       numbers.  (Contributed by NM, 12-Jan-2008.)
       (New usage is discouraged.) $)
    cnnvnm $p |- abs = ( normCV ` U ) $=
      ( cnmcv cfv c2nd caddc cmul cop cabs eqid nmcvfval fveq2i opex cc cr wcel
      wf cvv absf cnex fex mp2an op2nd 3eqtrri ) ACDZAEDFGHZIHZEDIAUEUEJKAUGEBL
      UFIFGMNOIQNRPIRPSTNORIUAUBUCUD $.
  $}

  ${
    $d x y U $.
    cnnvm.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The vector subtraction operation of the normed complex vector space of
       complex numbers.  (Contributed by NM, 12-Jan-2008.)  (Revised by Mario
       Carneiro, 23-Dec-2013.)  (New usage is discouraged.) $)
    cnnvm $p |- - = ( -v ` U ) $=
      ( vx vy cc cv cmin co cmpo c1 cneg cmul caddc cnsb cfv wcel wa wceq mulm1
      ax-mp adantl oveq2d negsub eqtr2d mpoeq3ia cxp wfn subf ffn fnov mpbi cnv
      wf cnnv cnnvba cnnvg cnnvs eqid nvmfval 3eqtr4i ) CDEECFZDFZGHZIZCDEEVAJK
      VBLHZMHZIZGANOZCDEEVCVFVAEPZVBEPZQZVFVAVBKZMHVCVKVEVLVAMVJVEVLRVIVBSUAUBV
      AVBUCUDUEGEEUFZUGZGVDRVMEGUMVNUHVMEGUITCDEEGUJUKAULPVHVGRABUNCDLAMVHEABUO
      ABUPABUQVHURUSTUT $.
  $}

  ${
    elimnv.1 $e |- X = ( BaseSet ` U ) $.
    elimnv.5 $e |- Z = ( 0vec ` U ) $.
    elimnv.9 $e |- U e. NrmCVec $.
    $( Hypothesis elimination lemma for normed complex vector spaces to assist
       weak deduction theorem.  (Contributed by NM, 16-May-2007.)
       (New usage is discouraged.) $)
    elimnv $p |- if ( A e. X , A , Z ) e. X $=
      ( cnv wcel nvzcl ax-mp elimel ) ADCBHIDCIGBCDEFJKL $.
  $}

  $( Hypothesis elimination lemma for normed complex vector spaces to assist
     weak deduction theorem.  (Contributed by NM, 16-May-2007.)
     (New usage is discouraged.) $)
  elimnvu $p |- if ( U e. NrmCVec , U , <. <. + , x. >. , abs >. )
                 e. NrmCVec $=
    ( caddc cmul cop cabs cnv eqid cnnv elimel ) ABCDEDZFJJGHI $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Induced metric of a normed complex vector space
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d u U $.
    imsval.3 $e |- M = ( -v ` U ) $.
    imsval.6 $e |- N = ( normCV ` U ) $.
    imsval.8 $e |- D = ( IndMet ` U ) $.
    $( Value of the induced metric of a normed complex vector space.
       (Contributed by NM, 11-Sep-2007.)  (Revised by Mario Carneiro,
       16-Nov-2013.)  (New usage is discouraged.) $)
    imsval $p |- ( U e. NrmCVec -> D = ( N o. M ) ) $=
      ( vu cnv wcel cims cfv cnmcv cnsb ccom cv wceq fveq2 coeq12d fvex coeq12i
      df-ims coex fvmpt 3eqtr4g ) BIJBKLBMLZBNLZOZADCOHBHPZMLZUINLZOUHIKUIBQUJU
      FUKUGUIBMRUIBNRSHUBUFUGBMTBNTUCUDGDUFCUGFEUAUE $.
  $}

  ${
    imsdval.1 $e |- X = ( BaseSet ` U ) $.
    imsdval.3 $e |- M = ( -v ` U ) $.
    imsdval.6 $e |- N = ( normCV ` U ) $.
    imsdval.8 $e |- D = ( IndMet ` U ) $.
    $( Value of the induced metric (distance function) of a normed complex
       vector space.  Equation 1 of [Kreyszig] p. 59.  (Contributed by NM,
       11-Sep-2007.)  (Revised by Mario Carneiro, 27-Dec-2014.)
       (New usage is discouraged.) $)
    imsdval $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                  ( A D B ) = ( N ` ( A M B ) ) ) $=
      ( cnv wcel w3a cop cfv co ccom wceq df-ov imsval 3ad2ant1 fveq1d cxp nvmf
      wf wa opelxpi fvco3 syl2an 3impb eqtrd fveq2i 3eqtr4g ) DLMZAGMZBGMZNZABO
      ZCPZUSEPZFPZABCQABEQZFPURUTUSFERZPZVBURUSCVDUOUPCVDSUQCDEFIJKUAUBUCUOUPUQ
      VEVBSZUOGGUDZGEUFUSVGMVFUPUQUGDEGHIUEABGGUHVGGUSFEUIUJUKULABCTVCVAFABETUM
      UN $.
  $}

  ${
    imsdval2.1 $e |- X = ( BaseSet ` U ) $.
    imsdval2.2 $e |- G = ( +v ` U ) $.
    imsdval2.4 $e |- S = ( .sOLD ` U ) $.
    imsdval2.6 $e |- N = ( normCV ` U ) $.
    imsdval2.8 $e |- D = ( IndMet ` U ) $.
    $( TODO $)
    $( Value of the distance function of the induced metric of a normed complex
       vector space.  Equation 1 of [Kreyszig] p. 59.  (Contributed by NM,
       28-Nov-2006.)  (New usage is discouraged.) $)
    imsdval2 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                  ( A D B ) = ( N ` ( A G ( -u 1 S B ) ) ) ) $=
      ( cnv wcel w3a co cnsb cfv c1 cneg eqid imsdval nvmval fveq2d eqtrd ) ENO
      AHOBHOPZABCQABERSZQZGSATUABDQFQZGSABCEUHGHIUHUBZLMUCUGUIUJGABDEFUHHIJKUKU
      DUEUF $.
  $}

  ${
    nvnd.1 $e |- X = ( BaseSet ` U ) $.
    nvnd.5 $e |- Z = ( 0vec ` U ) $.
    nvnd.6 $e |- N = ( normCV ` U ) $.
    nvnd.8 $e |- D = ( IndMet ` U ) $.
    $( The norm of a normed complex vector space expressed in terms of the
       distance function of its induced metric.  Problem 1 of [Kreyszig] p. 63.
       (Contributed by NM, 4-Dec-2006.)  (New usage is discouraged.) $)
    nvnd $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( N ` A ) = ( A D Z ) ) $=
      ( cnv wcel wa co cnsb cfv wceq adantr eqid mpd3an3 nvzcl imsdval cneg cns
      c1 cpv nvmval cc neg1cn nvsz mpan2 oveq2d nv0rid 3eqtrd fveq2d eqtr2d ) C
      KLZAELZMZAFBNZAFCOPZNZDPZADPUQURFELZUTVCQUQVDURCEFGHUARZAFBCVADEGVASZIJUB
      TUSVBADUSVBAUEUCZFCUDPZNZCUFPZNZAFVJNZAUQURVDVBVKQVEAFVHCVJVAEGVJSZVHSZVF
      UGTUQVKVLQURUQVIFAVJUQVGUHLVIFQUIVGVHCFVNHUJUKULRACVJEFGVMHUMUNUOUP $.
  $}

  ${
    imsdfn.1 $e |- X = ( BaseSet ` U ) $.
    imsdfn.8 $e |- D = ( IndMet ` U ) $.
    $( Mapping for the induced metric distance function of a normed complex
       vector space.  (Contributed by NM, 29-Nov-2006.)
       (New usage is discouraged.) $)
    imsdf $p |- ( U e. NrmCVec -> D : ( X X. X ) --> RR ) $=
      ( cnv wcel cxp cr wf cnmcv cfv cnsb ccom eqid nvf nvmf fco syl2anc imsval
      feq1d mpbird ) BFGZCCHZIAJUDIBKLZBMLZNZJZUCCIUEJUDCUFJUHBUECDUEOZPBUFCDUF
      OZQUDCIUEUFRSUCUDIAUGABUFUEUJUIETUAUB $.
  $}

  ${
    $d x y z D $.  $d x y z X $.
    imsmetlem.1 $e |- X = ( BaseSet ` U ) $.
    imsmetlem.2 $e |- G = ( +v ` U ) $.
    imsmetlem.7 $e |- M = ( inv ` G ) $.
    imsmetlem.4 $e |- S = ( .sOLD ` U ) $.
    imsmetlem.5 $e |- Z = ( 0vec ` U ) $.
    imsmetlem.6 $e |- N = ( normCV ` U ) $.
    imsmetlem.8 $e |- D = ( IndMet ` U ) $.
    imsmetlem.9 $e |- U e. NrmCVec $.
    $( Lemma for ~ imsmet .  (Contributed by NM, 29-Nov-2006.)
       (New usage is discouraged.) $)
    imsmetlem $p |- D e. ( Met ` X ) $=
      ( wcel co wceq mp3an1 vx vy vz cba fvexi cnv cxp cr wf imsdf ax-mp cv cc0
      wa c1 cfv imsdval2 eqeq1d wb cc neg1cn nvscl mp3an12 nvgcl sylan2 sylancr
      cneg nvz nvzcl w3a nvrcan mpan mp3an2 sylancom simpl adantl simpr syl3anc
      nvass nvlinv oveq2d nv0rid adantr 3eqtrd nv0lid eqeq12d bitr3d 3bitrd cle
      caddc syl2anc 3adant3 3adant2 nvtri 3adant1 3ad2ant3 oveq1d eqtr3d fveq2d
      wbr simp1 eqtr4d nvdif eqtrd oveq12d 3brtr4d 3coml ismeti ) UAUBUCAGGCUDI
      UECUFQZGGUGUHAUIPACGIOUJUKUAULZGQZUBULZGQZUNZXJXLARZUMSXJUOVGZXLBRZDRZFUP
      ZUMSZXRHSZXJXLSZXNXOXSUMXIXKXMXOXSSZPXJXLABCDFGIJLNOUQTZURXNXIXRGQZXTYAUS
      PXMXKXQGQZYEXIXPUTQZXMYFPVAXPXLBCGILVBVCZXIXKYFYEPXJXQCDGIJVDTVEZXRCFGHIM
      NVHVFXNXRXLDRZHXLDRZSZYAYBXKXMYEYLYAUSZYIYEHGQZXMYMXIYNPCGHIMVIUKXIYEYNXM
      VJYMPXRHXLCDGIJVKVLVMVNXNYJXJYKXLXNYJXJXQXLDRZDRZXJHDRZXJXNXKYFXMYJYPSZXK
      XMVOXMYFXKYHVPXKXMVQXIXKYFXMVJYRPXJXQXLCDGIJVSVLVRXNYOHXJDXMYOHSZXKXIXMYS
      PXLBCDGHIJLMVTVLVPWAXKYQXJSZXMXIXKYTPXJCDGHIJMWBVLZWCWDXMYKXLSZXKXIXMUUBP
      XLCDGHIJMWEVLVPWFWGWHUCULZGQZXKXMXOUUCXJARZUUCXLARZWJRZWIWTUUDXKXMVJZXJXP
      UUCBRZDRZUUCXQDRZDRZFUPZUUJFUPZUUKFUPZWJRZXOUUGWIUUHUUJGQZUUKGQZUUMUUPWIW
      TZUUDXKUUQXMUUDXKUNZXKUUIGQZUUQUUDXKVQZUUDUVAXKXIYGUUDUVAPVAXPUUCBCGILVBV
      CWCZXIXKUVAUUQPXJUUICDGIJVDTWKWLZUUDXMUURXKXMUUDYFUURYHXIUUDYFUURPUUCXQCD
      GIJVDTVEWMXIUUQUURUUSPUUJUUKCDFGIJNWNTWKUUHXOXSUUMXKXMYCUUDYDWOUUHUULXRFU
      UHUUJUUCDRZXQDRZUULXRUUHUUQUUDYFUVFUULSZUVDUUDXKXMXAXMUUDYFXKYHWPXIUUQUUD
      YFVJUVGPUUJUUCXQCDGIJVSVLVRUUHUVEXJXQDUUDXKUVEXJSXMUUTUVEXJUUIUUCDRZDRZYQ
      XJUUTXKUVAUUDUVEUVISZUVBUVCUUDXKVOXIXKUVAUUDVJUVJPXJUUIUUCCDGIJVSVLVRUUTU
      VHHXJDUUDUVHHSZXKXIUUDUVKPUUCBCDGHIJLMVTVLWCWAXKYTUUDUUAVPWDWLWQWRWSXBUUH
      UUEUUNUUFUUOWJUUDXKUUEUUNSXMUUTUUEUUCXPXJBRDRFUPZUUNXIUUDXKUUEUVLSPUUCXJA
      BCDFGIJLNOUQTXIUUDXKUVLUUNSPUUCXJBCDFGIJLNXCTXDWLUUDXMUUFUUOSZXKXIUUDXMUV
      MPUUCXLABCDFGIJLNOUQTWMXEXFXGXH $.
  $}

  ${
    imsmet.1 $e |- X = ( BaseSet ` U ) $.
    imsmet.8 $e |- D = ( IndMet ` U ) $.
    $( The induced metric of a normed complex vector space is a metric space.
       Part of Definition 2.2-1 of [Kreyszig] p. 58.  (Contributed by NM,
       4-Dec-2006.)  (Revised by Mario Carneiro, 10-Sep-2015.)
       (New usage is discouraged.) $)
    imsmet $p |- ( U e. NrmCVec -> D e. ( Met ` X ) ) $=
      ( cnv wcel cims cfv cmet caddc cmul cop cabs cif wceq fveq2 eqtrid eqid
      cba fveq2d eleq12d cns cpv cnmcv cn0v elimnvu imsmetlem dedth eqeltrid
      cgn ) BFGZABHIZCJIZEULUMUNGULBKLMNMZOZHIZUPTIZJIZGBUOBUPPZUMUQUNUSBUPHQUT
      CURJUTCBTIURDBUPTQRUAUBUQUPUCIZUPUPUDIZVBUKIZUPUEIZURUPUFIZURSVBSVCSVASVE
      SVDSUQSBUGUHUIUJ $.

    $( The induced metric of a normed complex vector space is an extended
       metric space.  (Contributed by Mario Carneiro, 10-Sep-2015.)
       (New usage is discouraged.) $)
    imsxmet $p |- ( U e. NrmCVec -> D e. ( *Met ` X ) ) $=
      ( cnv wcel cmet cfv cxmet imsmet metxmet syl ) BFGACHIGACJIGABCDEKACLM $.
  $}

  ${
    cnims.6 $e |- U = <. <. + , x. >. , abs >. $.
    cnims.7 $e |- D = ( abs o. - ) $.
    $( The metric induced on the complex numbers. ~ cnmet proves that it is a
       metric.  (Contributed by Steve Rodriguez, 5-Dec-2006.)  (Revised by NM,
       15-Jan-2008.)  (New usage is discouraged.) $)
    cnims $p |- D = ( IndMet ` U ) $=
      ( cabs cmin ccom cims cfv wcel wceq cnnv cnnvm cnnvnm imsval ax-mp eqtr4i
      cnv eqid ) AEFGZBHIZDBRJUATKBCLUABFEBCMBCNUASOPQ $.
  $}

  ${
    $d r s w x y z C $.  $d r s w x y z G $.  $d r s w x y z J $.
    $d r s w x y z U $.
    vacn.c $e |- C = ( IndMet ` U ) $.
    vacn.j $e |- J = ( MetOpen ` C ) $.
    vacn.g $e |- G = ( +v ` U ) $.
    $( Vector addition is jointly continuous in both arguments.  (Contributed
       by Jeff Hankins, 16-Jun-2009.)  (Revised by Mario Carneiro,
       10-Sep-2015.)  (New usage is discouraged.) $)
    vacn $p |- ( U e. NrmCVec -> G e. ( ( J tX J ) Cn J ) ) $=
      ( vz vw wcel co cfv cv clt wbr wa wral crp cr syl3anc vx vs vy vr cnv ctx
      ccn cba wf wi wrex eqid nvgf c2 cdiv rphalfcl adantl caddc simplll imsmet
      cxp cmet syl simplrl adantr simprl simplrr simprr rpre ad2antlr lt2halves
      metcl cle cnsb cnmcv nvmcl nvtri nvgcl imsdval nvaddsub4 syl122anc fveq2d
      wceq eqtrd oveq12d 3brtr4d readdcld lelttr mpand ralrimivva breq2 anbi12d
      syld imbi1d 2ralbidv syl2anc ralrimiva cxmet wb imsxmet txmetcn mpbir2and
      rspcev ) BUEJZCDDUFKDUGKJZBUHLZXFVAXFCUIZUAMZHMZAKZUBMZNOZUCMZIMZAKZXKNOZ
      PZXHXMCKZXIXNCKZAKZUDMZNOZUJZIXFQHXFQZUBRUKZUDRQZUCXFQUAXFQZBCXFXFULZGUMX
      DYFUAUCXFXFXDXHXFJZXMXFJZPZPZYEUDRYLYARJZPZYAUNUOKZRJZXJYONOZXOYONOZPZYBU
      JZIXFQHXFQZYEYMYPYLYAUPUQYNYTHIXFXFYNXIXFJZXNXFJZPZPZYSXJXOURKZYANOZYBUUE
      XJSJZXOSJZYASJZYSUUGUJUUEAXFVBLJZYIUUBUUHUUEXDUUKXDYKYMUUDUSZABXFYHEUTVCZ
      YNYIUUDXDYIYJYMVDVEZYNUUBUUCVFZXHXIAXFVLTZUUEUUKYJUUCUUIUUMYNYJUUDXDYIYJY
      MVGVEZYNUUBUUCVHZXMXNAXFVLTZYMUUJYLUUDYAVIVJZXJXOYAVKTUUEXTUUFVMOZUUGYBUU
      EXHXIBVNLZKZXMXNUVBKZCKZBVOLZLZUVCUVFLZUVDUVFLZURKZXTUUFVMUUEXDUVCXFJZUVD
      XFJZUVGUVJVMOUULUUEXDYIUUBUVKUULUUNUUOXHXIBUVBXFYHUVBULZVPTUUEXDYJUUCUVLU
      ULUUQUURXMXNBUVBXFYHUVMVPTUVCUVDBCUVFXFYHGUVFULZVQTUUEXTXRXSUVBKZUVFLZUVG
      UUEXDXRXFJZXSXFJZXTUVPWCUULUUEXDYIYJUVQUULUUNUUQXHXMBCXFYHGVRTZUUEXDUUBUU
      CUVRUULUUOUURXIXNBCXFYHGVRTZXRXSABUVBUVFXFYHUVMUVNEVSTUUEUVOUVEUVFUUEXDYI
      YJUUBUUCUVOUVEWCUULUUNUUQUUOUURXHXMXIXNBCUVBXFYHGUVMVTWAWBWDUUEXJUVHXOUVI
      URUUEXDYIUUBXJUVHWCUULUUNUUOXHXIABUVBUVFXFYHUVMUVNEVSTUUEXDYJUUCXOUVIWCUU
      LUUQUURXMXNABUVBUVFXFYHUVMUVNEVSTWEWFUUEXTSJZUUFSJUUJUVAUUGPYBUJUUEUUKUVQ
      UVRUWAUUMUVSUVTXRXSAXFVLTUUEXJXOUUPUUSWGUUTXTUUFYAWHTWIWMWJYDUUAUBYORXKYO
      WCZYCYTHIXFXFUWBXQYSYBUWBXLYQXPYRXKYOXJNWKXKYOXONWKWLWNWOXCWPWQWJXDAXFWRL
      JZUWCUWCXEXGYGPWSABXFYHEWTZUWDUWDUAUCUDUBIHAAACDDDXFXFXFFFFXATXB $.
  $}

  ${
    $d d e x y C $.  $d d e x y J $.  $d d e x y K $.  $d d e x y N $.
    $d d e x y U $.
    nmcvcn.1 $e |- N = ( normCV ` U ) $.
    nmcvcn.2 $e |- C = ( IndMet ` U ) $.
    nmcvcn.j $e |- J = ( MetOpen ` C ) $.
    nmcvcn.k $e |- K = ( topGen ` ran (,) ) $.
    $( The norm of a normed complex vector space is a continuous function.
       (Contributed by NM, 16-May-2007.)  (Proof shortened by Mario Carneiro,
       10-Jan-2014.)  (New usage is discouraged.) $)
    nmcvcn $p |- ( U e. NrmCVec -> N e. ( J Cn K ) ) $=
      ( vx vy vd ve wcel co cfv cr crp eqid wa cnv ccn cba wf clt wbr cabs cmin
      cv ccom cxp cres wi wral wrex nvf simprr cle w3a nvcl anim12d remet metcl
      ex cmet mp3an1 syl6 3impib imsmet syl3an1 c1 cneg cns cpv nvabs remetdval
      wceq syl imsdval2 3brtr4d jca31 3expa rpre lelttr expdimp an32s ralrimdva
      syl2an impr breq2 rspceaimv syl2anc ralrimivva wb imsxmet rexmet cioo crn
      cxmet ctg cmopn tgioo eqtri metcn sylancl mpbir2and ) BUANZECDUBONZBUCPZQ
      EUDZJUIZKUIZAOZLUIZUEUFZXKEPZXLEPZUGUHUJQQUKULZOZMUIZUEUFZUMKXIUNLRUOZMRU
      NJXIUNZBEXIXISZFUPXGYBJMXIRXGXKXINZXTRNZTTYFXMXTUEUFZYAUMZKXIUNZYBXGYEYFU
      QXGYEYFYIXGYETZYFYHKXIYJXLXINZTZYFYHYLXSQNZXMQNZTZXSXMURUFZTZXTQNZYHYFXGY
      EYKYQXGYEYKUSZYMYNYPXGYEYKYMXGYEYKTXPQNZXQQNZTZYMXGYEYTYKUUAXGYEYTXKBEXIY
      DFUTVDXGYKUUAXLBEXIYDFUTVDVAZXRQVEPNYTUUAYMXRXRSZVBXPXQXRQVCVFVGVHXGAXIVE
      PNYEYKYNABXIYDGVIXKXLAXIVCVJYSXPXQUHOUGPZXKVKVLXLBVMPZOBVNPZOEPXSXMURXKXL
      UUFBUUGEXIYDUUGSZUUFSZFVOYSUUBXSUUEVQXGYEYKUUBUUCVHXPXQXRUUDVPVRXKXLAUUFB
      UUGEXIYDUUHUUIFGVSVTWAWBXTWCYOYRYPYHYOYRTYPYGYAYMYNYRYPYGTYAUMXSXMXTWDWBW
      EWFWHVDWGWIXOYGYALKXTRXIXNXTXMUEWJWKWLWMXGAXIWSPNXRQWSPNXHXJYCTWNABXIYDGW
      OXRUUDWPJMLKAXRECDXIQHDWQWRWTPXRXAPZIXRUUJUUDUUJSXBXCXDXEXF $.
  $}

  ${
    nmcnc.1 $e |- N = ( normCV ` U ) $.
    nmcnc.2 $e |- C = ( IndMet ` U ) $.
    nmcnc.j $e |- J = ( MetOpen ` C ) $.
    nmcnc.k $e |- K = ( TopOpen ` CCfld ) $.
    $( The norm of a normed complex vector space is a continuous function to
       ` CC ` .  (For ` RR ` , see ~ nmcvcn .)  (Contributed by NM,
       12-Aug-2007.)  (New usage is discouraged.) $)
    nmcnc $p |- ( U e. NrmCVec -> N e. ( J Cn K ) ) $=
      ( cnv wcel cr crest co ccn ctop wss cnfldtop cnrest2r ax-mp tgioo2 eqcomi
      cioo crn ctg cfv nmcvcn sselid ) BJKCDLMNZONZCDONZEDPKUJUKQDIRLCDSTABCUIE
      FGHUCUDUEUFUIDIUAUBUGUH $.
  $}

  ${
    $d r s w x y z C $.  $d r s w x y z J $.  $d s w z T $.  $d r x y U $.
    $d r s w x y z K $.  $d r s w x y z S $.  $d r s w x y z X $.
    smcn.c $e |- C = ( IndMet ` U ) $.
    smcn.j $e |- J = ( MetOpen ` C ) $.
    smcn.s $e |- S = ( .sOLD ` U ) $.
    smcn.k $e |- K = ( TopOpen ` CCfld ) $.
    ${
      smcn.x $e |- X = ( BaseSet ` U ) $.
      smcn.n $e |- N = ( normCV ` U ) $.
      smcn.u $e |- U e. NrmCVec $.
      smcn.t $e |- T = ( 1 / ( 1 + ( ( ( ( N ` y ) +
                         ( abs ` x ) ) + 1 ) / r ) ) ) $.
      $( Lemma for ~ smcn .  (Contributed by Mario Carneiro, 5-May-2014.)
         (Revised by Mario Carneiro, 10-Sep-2015.)
         (New usage is discouraged.) $)
      smcnlem $p |- S e. ( ( K tX J ) Cn J ) $=
        ( co vz vs vw ctx ccn wcel cc cxp wf cv cabs cmin ccom clt wbr wral crp
        wa wi wrex cnv nvsf ax-mp c1 cfv caddc cdiv cr simpr nvcl sylancr abscl
        1rp adantr readdcld cc0 cle nvge0 absge0 addge0d ge0p1rpd rpdivcl sylan
        rpaddcl rpreccld eqeltrid cmet imsmet a1i simplll simpllr nvscl syl3anc
        simprll simprlr metcl rpre ad2antlr mettri syl13anc abscld peano2re syl
        cmul rpred remulcld cnsb subcld eqid nvmcl abssubd wceq cnmetdval eqtrd
        syl2anc simprrl eqbrtrrd ltled eqbrtrd lemul1ad mulcomd breqtrd absge0d
        rpcnd recnd pncan3d fveq2d abstrid 1red letrd cneg neg1cn oveq2d oveq1d
        imsdval nvs 3eqtr2d lelttrd breq2 cxmet ltaddrp mpbid eqbrtrid leadd2dd
        1re recgt1d simprrr lemul12ad le2addd cpv imsdval2 mulcl mulm1d negsubd
        nvdir nvsass 3eqtr3d oveq12d 1cnd addassd adddird 3brtr4d oveq2i rpne0d
        nvmdi divrecd eqtr4id simplr ltp1d addcomd ltdiv23d expr anbi12d imbi1d
        ralrimivva 2ralbidv rspcev ralrimiva rgen2 wb imsxmet cnfldtopn txmetcn
        cnxmet mp3an mpbir2an ) DHGUDTGUETUFZUGJUHJDUIZAUJZUAUJZUKULUMZTZUBUJZU
        NUOZBUJZUCUJZCTZUWMUNUOZURZUWIUWODTZUWJUWPDTZCTZKUJZUNUOZUSZUCJUPUAUGUP
        ZUBUQUTZKUQUPZBJUPAUGUPZFVAUFZUWHRDFJPNVBVCUXHABUGJUWIUGUFZUWOJUFZURZUX
        GKUQUXMUXCUQUFZURZEUQUFZUWLEUNUOZUWQEUNUOZURZUXDUSZUCJUPUAUGUPZUXGUXOEV
        DVDUWOIVEZUWIUKVEZVFTZVDVFTZUXCVGTZVFTZVGTZUQSUXOUYGUXOVDUQUFUYFUQUFZUY
        GUQUFZVMUXMUYEUQUFUXNUYIUXMUYDUXMUYBUYCUXMUXJUXLUYBVHUFZRUXKUXLVIZUWOFI
        JPQVJZVKZUXKUYCVHUFZUXLUWIVLVNZVOUXMUYBUYCUYNUYPUXMUXJUXLVPUYBVQUOZRUYL
        UWOFIJPQVRZVKUXKVPUYCVQUOUXLUWIVSVNVTWAUYEUXCWBWCZVDUYFWDVKZWEWFZUXOUXT
        UAUCUGJUXOUWJUGUFZUWPJUFZURZUXSUXDUXOVUDUXSURZURZUXBUWTUWJUWODTZCTZVUGU
        XACTZVFTZUXCVUFCJWGVEUFZUWTJUFZUXAJUFZUXBVHUFVUKVUFUXJVUKRCFJPLWHVCWIZV
        UFUXJUXKUXLVULUXJVUFRWIZUXKUXLUXNVUEWJZUXKUXLUXNVUEWKZUWIUWODFJPNWLWMZV
        UFUXJVUBVUCVUMVUOUXOVUBVUCUXSWNZUXOVUBVUCUXSWOZUWJUWPDFJPNWLWMZUWTUXACJ
        WPWMVUFVUHVUIVUFVUKVULVUGJUFZVUHVHUFVUNVURVUFUXJVUBUXLVVBVUOVUSVUQUWJUW
        ODFJPNWLWMZUWTVUGCJWPWMVUFVUKVVBVUMVUIVHUFVUNVVCVVAVUGUXACJWPWMVOZUXNUX
        CVHUFUXMVUEUXCWQWRZVUFVUKVULVUMVVBUXBVUJVQUOVUNVURVVAVVCUWTUXAVUGCJWSWT
        VUFVUJUYEEXDTZUXCVVDVUFUYEEVUFUYDVHUFUYEVHUFVUFUYBUYCVUFUXJUXLUYKRVUQUY
        MVKZVUFUWIVUPXAZVOUYDXBXCZVUFEUXOUXPVUEVUAVNZXEZXFVVEVUFUWIUWJULTZUKVEZ
        UYBXDTZUWJUKVEZUWOUWPFXGVEZTZIVEZXDTZVFTUYBEXDTZUYCVDVFTZEXDTZVFTZVUJVV
        FVQVUFVVNVVSVVTVWBVUFVVMUYBVUFVVLVUFUWIUWJVUPVUSXHZXAZVVGXFVUFVVOVVRVUF
        UWJVUSXAZVUFUXJVVQJUFZVVRVHUFRVUFUXJUXLVUCVWGVUOVUQVUTUWOUWPFVVPJPVVPXI
        ZXJWMZVVQFIJPQVJVKZXFVUFUYBEVVGVVKXFVUFVWAEVUFUYOVWAVHUFVVHUYCXBXCZVVKX
        FVUFVVNEUYBXDTVVTVQVUFVVMEUYBVWEVVKVVGVUFUXJUXLUYQRVUQUYRVKVUFVVMUWJUWI
        ULTZUKVEZEVQVUFUWIUWJVUPVUSXKZVUFVWMEVUFVWLVUFUWJUWIVUSVUPXHZXAZVVKVUFU
        WLVWMEUNVUFUWLVVMVWMVUFUXKVUBUWLVVMXLVUPVUSUWIUWJUWKUWKXIXMXOVWNXNUXOVU
        DUXQUXRXPXQXRZXSXTVUFEUYBVUFEVVJYDZVUFUYBVVGYEZYAYBVUFVVOVWAVVREVWFVWKV
        WJVVKVUFUWJVUSYCVUFUXJVWGVPVVRVQUORVWIVVQFIJPQVRVKVUFVVOUYCVWMVFTZVWAVW
        FVUFUYCVWMVVHVWPVOVWKVUFUWIVWLVFTZUKVEVVOVWTVQVUFVXAUWJUKVUFUWIUWJVUPVU
        SYFYGVUFUWIVWLVUPVWOYHXQVUFVWMVDUYCVWPVUFYIZVVHVUFVWMEVDVWPVVKVXBVWQVUF
        EVDVVKVXBVUFEUYHVDUNSVUFVDUYGUNUOZUYHVDUNUOVUFVDVHUFUYIVXCUUEUXOUYIVUEU
        YSVNZVDUYFUUAVKVUFUYGUXOUYJVUEUYTVNZUUFUUBUUCXRYJUUDYJVUFVVREVWJVVKVUFU
        WQVVREUNVUFUXJUXLVUCUWQVVRXLVUOVUQVUTUWOUWPCFVVPIJPVWHQLYOWMUXOVUDUXQUX
        RUUGXQXRUUHUUIVUFVUHVVNVUIVVSVFVUFVUHUWTVDYKZVUGDTZFUUJVEZTZIVEZVVLUWOD
        TZIVEZVVNVUFUXJVULVVBVUHVXJXLVUOVURVVCUWTVUGCDFVXHIJPVXHXIZNQLUUKWMVUFV
        XKVXIIVUFUWIVXFUWJXDTZVFTZUWODTZUWTVXNUWODTZVXHTZVXKVXIVUFUXJUXKVXNUGUF
        ZUXLVXPVXRXLVUOVUPVUFVXFUGUFZVUBVXSYLVUSVXFUWJUULVKVUQUWIVXNUWODFVXHJPV
        XMNUUOWTVUFVXOVVLUWODVUFVXOUWIUWJYKZVFTVVLVUFVXNVYAUWIVFVUFUWJVUSUUMYMV
        UFUWIUWJVUPVUSUUNXNYNVUFVXQVXGUWTVXHVUFUXJVXTVUBUXLVXQVXGXLVUOVXTVUFYLW
        IVUSVUQVXFUWJUWODFJPNUUPWTYMUUQYGVUFUXJVVLUGUFUXLVXLVVNXLVUOVWDVUQVVLUW
        ODFIJPNQYPWMYQVUFVUIVUGUXAVVPTZIVEZUWJVVQDTZIVEZVVSVUFUXJVVBVUMVUIVYCXL
        VUOVVCVVAVUGUXACFVVPIJPVWHQLYOWMVUFVYDVYBIVUFUXJVUBUXLVUCVYDVYBXLVUOVUS
        VUQVUTUWJUWOUWPDFVVPJPVWHNUVEWTYGVUFUXJVUBVWGVYEVVSXLVUOVUSVWIUWJVVQDFI
        JPNQYPWMYQUURVUFVVFUYBVWAVFTZEXDTVWCVUFUYEVYFEXDVUFUYBUYCVDVWSVUFUYCVVH
        YEVUFUUSZUUTYNVUFUYBVWAEVWSVUFVWAVWKYEVWRUVAXNUVBVUFVVFUYEUYGVGTZUXCUNV
        UFVVFUYEUYHXDTVYHEUYHUYEXDSUVCVUFUYEUYGVUFUYEVVIYEVUFUYGVXEYDVUFUYGVXEU
        VDUVFUVGVUFUYEUXCUYGVVIUXMUXNVUEUVHVXEVUFUYFUYFVDVFTUYGUNVUFUYFVUFUYFVX
        DXEUVIVUFUYFVDVUFUYFVXDYDVYGUVJYBUVKXSYRYRUVLUVOUXFUYAUBEUQUWMEXLZUXEUX
        TUAUCUGJVYIUWSUXSUXDVYIUWNUXQUWRUXRUWMEUWLUNYSUWMEUWQUNYSUVMUVNUVPUVQXO
        UVRUVSUWKUGYTVEUFCJYTVEUFZVYJUWGUWHUXIURUVTUWDUXJVYJRCFJPLUWAVCZVYKABKU
        BUCUAUWKCCDHGGUGJJHOUWBMMUWCUWEUWF $.
    $}

    $( Scalar multiplication is jointly continuous in both arguments.
       (Contributed by NM, 16-Jun-2009.)  (Revised by Mario Carneiro,
       5-May-2014.)  (New usage is discouraged.) $)
    smcn $p |- ( U e. NrmCVec -> S e. ( ( K tX J ) Cn J ) ) $=
      ( wcel ctx co ccn caddc cns cfv cims cmopn eqtrid eqid vx vy cnv cmul cop
      vr cabs cif wceq fveq2 fveq2d oveq2d oveq12d eleq12d c1 cv cnmcv cdiv cba
      elimnvu smcnlem dedth ) CUCJZBEDKLZDMLZJVCCNUDUEUGUEZUHZOPZEVGQPZRPZKLZVJ
      MLZJCVFCVGUIZBVHVEVLVMBCOPVHHCVGOUJSVMVDVKDVJMVMDVJEKVMDARPVJGVMAVIRVMACQ
      PVIFCVGQUJSUKSZULVNUMUNUAUBVIVHUOUOUBUPVGUQPZPUAUPUGPNLUONLUFUPURLNLURLZV
      GVJEVOVGUSPZUFVITVJTVHTIVQTVOTCUTVPTVAVB $.
  $}

  ${
    $d x y J $.  $d x y M $.  $d x y U $.
    vmcn.c $e |- C = ( IndMet ` U ) $.
    vmcn.j $e |- J = ( MetOpen ` C ) $.
    vmcn.m $e |- M = ( -v ` U ) $.
    $( Vector subtraction is jointly continuous in both arguments.
       (Contributed by Mario Carneiro, 6-May-2014.)
       (New usage is discouraged.) $)
    vmcn $p |- ( U e. NrmCVec -> M e. ( ( J tX J ) Cn J ) ) $=
      ( vx vy cnv wcel cba cfv cv co eqid ctopon cc a1i cnmpt22f c1 cns cpv ctx
      cneg cmpo ccn nvmfval cxmet imsxmet mopntopon syl ccnfld ctopn cnfldtopon
      cnmpt1st neg1cn cnmpt2c cnmpt2nd smcn vacn eqeltrd ) BJKZDHIBLMZVDHNZUAUE
      ZINZBUBMZOZBUCMZOUFCCUDOCUGOHIVHBVJDVDVDPZVJPZVHPZGUHVCHIVEVIVJCCCCCVDVDV
      CAVDUIMKCVDQMKABVDVKEUJACVDFUKULZVNVCHICCVDVDVNVNUPVCHIVFVGVHCCUMUNMZCCVD
      VDVNVNVCHIVFCCVOVDVDRVNVNVORQMKVCVOVOPZUOSVFRKVCUQSURVCHICCVDVDVNVNUSAVHB
      CVOEFVMVPUTTABVJCEFVLVATVB $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Inner product
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c .iOLD $.

  $( Extend class notation with the class inner product functions. $)
  cdip $a class .iOLD $.

  ${
    $d k u x y $.
    $( Define a function that maps a normed complex vector space to its inner
       product operation in case its norm satisfies the parallelogram identity
       (otherwise the operation is still defined, but not meaningful).  Based
       on Exercise 4(a) of [ReedSimon] p. 63 and Theorem 6.44 of [Ponnusamy]
       p. 361.  Vector addition is ` ( 1st `` w ) ` , the scalar product is
       ` ( 2nd `` w ) ` , and the norm is ` n ` .  (Contributed by NM,
       10-Apr-2007.)  (New usage is discouraged.) $)
    df-dip $a |- .iOLD = ( u e. NrmCVec |->
      ( x e. ( BaseSet ` u ) , y e. ( BaseSet ` u ) |->
    ( sum_ k e. ( 1 ... 4 ) ( ( _i ^ k ) x. ( ( ( normCV ` u ) ` ( x ( +v ` u )
        ( ( _i ^ k ) ( .sOLD ` u ) y ) ) ) ^ 2 ) ) / 4 ) ) ) $.

$(
    df-dip $a |- .iOLD = { <. x , y >. | ( x e. NrmCVec /\ E. g E. s E. n
            ( x = <. <. g , s >. , n >. /\ y = { <. <. a , b >. , c >. |
            ( ( a e. dom n /\ b e. dom n ) /\ c = ( sum_ k e. ( 1 ... 4 )
             ( ( _i ^ k ) x. ( ( n ` ( a g ( ( _i ^ k ) s b ) ) ) ^ 2 ) )
              / 4 ) ) } ) ) } $.

    df-dip $a |- .iOLD = { <. x , y >. | ( x e. NrmCVec /\ E. g E. s E. n
            ( x = <. <. g , s >. , n >. /\ y = { <. <. a , b >. , c >. |
            ( ( a e. dom n /\ b e. dom n ) /\ c =
                ( ( ( ( ( n ` ( a g b ) ) ^ 2 ) +
                ( ( n ` ( a g ( -u 1 s b ) ) ) ^ 2 ) ) +
                ( _i x. ( ( ( n ` ( a g ( _i s b ) ) ) ^ 2 ) +
                ( ( n ` ( a g ( -u _i s b ) ) ) ^ 2 ) ) ) ) / 4 ) ) } ) ) } $.
$)
  $}

  ${
    $d k u x y G $.  $d k u x y N $.  $d k u x y S $.  $d k u x y U $.
    $d k x y A $.  $d k x y B $.  $d k u x y X $.
    dipfval.1 $e |- X = ( BaseSet ` U ) $.
    dipfval.2 $e |- G = ( +v ` U ) $.
    dipfval.4 $e |- S = ( .sOLD ` U ) $.
    dipfval.6 $e |- N = ( normCV ` U ) $.
    dipfval.7 $e |- P = ( .iOLD ` U ) $.
    $( The inner product function on a normed complex vector space.  The
       definition is meaningful for vector spaces that are also inner product
       spaces, i.e. satisfy the parallelogram law.  (Contributed by NM,
       10-Apr-2007.)  (Revised by Mario Carneiro, 16-Nov-2013.)
       (New usage is discouraged.) $)
    dipfval $p |- ( U e. NrmCVec -> P = ( x e. X , y e. X |->
      ( sum_ k e. ( 1 ... 4 ) ( ( _i ^ k ) x.
        ( ( N ` ( x G ( ( _i ^ k ) S y ) ) ) ^ 2 ) ) / 4 ) ) ) $=
      ( cfv c4 co cv cexp cba vu cnv wcel cdip c1 cfz ci cmul csu cdiv cmpo cns
      c2 cnmcv wceq fveq2 eqtr4di eqidd oveqd oveq123d fveq12d oveq1d sumeq2sdv
      cpv oveq2d mpoeq123dv df-dip fvexi mpoex fvmpt eqtrid ) EUBUCCEUDOABIIUEP
      UFQZUGFRSQZARZVMBRZDQZGQZHOZUMSQZUHQZFUIZPUJQZUKZNUAEABUARZTOZWEVLVMVNVMV
      OWDULOZQZWDVDOZQZWDUNOZOZUMSQZUHQZFUIZPUJQZUKWCUBUDWDEUOZABWEWEWOIIWBWPWE
      ETOIWDETUPJUQZWQWPWNWAPUJWPVLWMVTFWPWLVSVMUHWPWKVRUMSWPWIVQWJHWPWJEUNOHWD
      EUNUPMUQWPVNVNWGVPWHGWPWHEVDOGWDEVDUPKUQWPVNURWPWFDVMVOWPWFEULODWDEULUPLU
      QUSUTVAVBVEVCVBVFABUAFVGABIIWBIETJVHZWRVIVJVK $.

    $( Value of the inner product.  The definition is meaningful for normed
       complex vector spaces that are also inner product spaces, i.e. satisfy
       the parallelogram law, although for convenience we define it for any
       normed complex vector space.  The vector (group) addition operation is
       ` G ` , the scalar product is ` S ` , the norm is ` N ` , and the set of
       vectors is ` X ` .  Equation 6.45 of [Ponnusamy] p. 361.  (Contributed
       by NM, 31-Jan-2007.)  (Revised by Mario Carneiro, 16-Nov-2013.)
       (New usage is discouraged.) $)
    ipval $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A P B ) =
                ( sum_ k e. ( 1 ... 4 ) ( ( _i ^ k ) x. ( ( N ` ( A G
                    ( ( _i ^ k ) S B ) ) ) ^ 2 ) ) / 4 ) ) $=
      ( co c4 cexp c2 cmul cdiv vx vy cnv wcel c1 cfz ci cv cfv wceq wa dipfval
      csu cmpo oveqd fvoveq1 oveq1d oveq2d sumeq2sdv oveq2 fveq2d eqid sylan9eq
      ovex ovmpo 3impb ) EUCUDZAIUDZBIUDZABCOZUEPUFOZUGFUHQOZAVLBDOZGOZHUIZRQOZ
      SOZFUMZPTOZUJVGVHVIUKVJABUAUBIIVKVLUAUHZVLUBUHZDOZGOHUIZRQOZSOZFUMZPTOZUN
      ZOVSVGCWHABUAUBCDEFGHIJKLMNULUOUAUBABIIWGVSWHVKVLAWBGOZHUIZRQOZSOZFUMZPTO
      VTAUJZWFWMPTWNVKWEWLFWNWDWKVLSWNWCWJRQVTAWBHGUPUQURUSUQWABUJZWMVRPTWOVKWL
      VQFWOWKVPVLSWOWJVORQWOWIVNHWOWBVMAGWABVLDUTURVAUQURUSUQWHVBVRPTVDVEVCVF
      $.

    $( Lemma for ~ ipval3 .  (Contributed by NM, 1-Feb-2007.)
       (New usage is discouraged.) $)
    ipval2lem2 $p |- ( ( ( U e. NrmCVec /\ A e. X /\ B e. X ) /\ C e. CC ) ->
               ( ( N ` ( A G ( C S B ) ) ) ^ 2 ) e. RR ) $=
      ( cnv wcel w3a cc wa co cfv cr simpl1 simpl2 nvscl 3expa 3adantl2 syl3anc
      3com23 nvgcl nvcl syl2anc resqcld ) FOPZAIPZBIPZQCRPZSZACBETZGTZHUAZURUNU
      TIPZVAUBPUNUOUPUQUCZURUNUOUSIPZVBVCUNUOUPUQUDUNUPUQVDUOUNUPUQVDUNUQUPVDCB
      EFIJLUEUIUFUGAUSFGIJKUJUHUTFHIJMUKULUM $.

    $( Lemma for ~ ipval3 .  (Contributed by NM, 1-Feb-2007.)
       (New usage is discouraged.) $)
    ipval2lem3 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
               ( ( N ` ( A G B ) ) ^ 2 ) e. RR ) $=
      ( wcel c1 co cfv c2 cexp cr cnv w3a wa nvsid oveq2d fveq2d oveq1d 3adant2
      wceq cc ax-1cn ipval2lem2 mpan2 eqeltrrd ) EUANZAHNZBHNZUBZAOBDPZFPZGQZRS
      PZABFPZGQZRSPZTUOUQVBVEUIUPUOUQUCZVAVDRSVFUTVCGVFUSBAFBDEHIKUDUEUFUGUHURO
      UJNVBTNUKABOCDEFGHIJKLMULUMUN $.

    $( Lemma for ~ ipval3 .  (Contributed by NM, 1-Feb-2007.)
       (New usage is discouraged.) $)
    ipval2lem4 $p |- ( ( ( U e. NrmCVec /\ A e. X /\ B e. X ) /\ C e. CC ) ->
               ( ( N ` ( A G ( C S B ) ) ) ^ 2 ) e. CC ) $=
      ( cnv wcel w3a cc wa co cfv c2 cexp ipval2lem2 recnd ) FOPAIPBIPQCRPSACBE
      TGTHUAUBUCTABCDEFGHIJKLMNUDUE $.

    $( Expansion of the inner product value ~ ipval .  (Contributed by NM,
       31-Jan-2007.)  (Revised by Mario Carneiro, 5-May-2014.)
       (New usage is discouraged.) $)
    ipval2 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A P B )
               = ( ( ( ( ( N ` ( A G B ) ) ^ 2 ) -
               ( ( N ` ( A G ( -u 1 S B ) ) ) ^ 2 ) ) +
               ( _i x. ( ( ( N ` ( A G ( _i S B ) ) ) ^ 2 ) -
               ( ( N ` ( A G ( -u _i S B ) ) ) ^ 2 ) ) ) ) / 4 ) ) $=
      ( wcel co c1 ci cexp c2 cmul vk cnv w3a c4 cfz cv cfv csu cdiv cneg caddc
      cmin ipval cc ax-icn ipval2lem4 mpan2 mulcl sylancr neg1cn subcld negsubd
      negicn mulm1d oveq2d mulneg1 oveq12d mp3an1 syl2anc oveq1d sub32d 3eqtr4d
      eqtrd wceq subdi wa nvsid fveq2d 3adant2 ipval2lem3 recnd mullidd cn nnuz
      c3 df-4 oveq2 i4 eqtrdi cn0 nnnn0 expcl adantl sylan2 mulcld df-3 i3 df-2
      i2 cz 1z exp1 ax-mp fsum1 1nn jctil eqidd fsump1i simprd subadd23d eqtr4d
      addcomd ) EUBNZAHNZBHNZUCZABCOPUDUEOQUAUFZROZAXRBDOZFOZGUGZSROZTOZUAUHZUD
      UIOABFOZGUGZSROZAPUJZBDOZFOZGUGZSROZULOZQAQBDOZFOZGUGZSROZAQUJZBDOZFOZGUG
      ZSROZULOZTOZUKOZUDUIOABCDEUAFGHIJKLMUMXPYDUUEUDUIXPQYQTOZYHYLTOZUKOZYRUUB
      TOZUKOZPAPBDOZFOZGUGZSROZTOZUKOZUUDYLULOZYGUKOZYDUUEXPUUJUUQUUOYGUKXPUUFY
      LULOZQUUBTOZUJZUKOUUSUUTULOZUUJUUQXPUUSUUTXPUUFYLXPQUNNZYQUNNZUUFUNNZUOXP
      UVCUVDUOABQCDEFGHIJKLMUPUQZQYQURUSZXPYHUNNYLUNNUTABYHCDEFGHIJKLMUPUQZVAXP
      UVCUUBUNNZUUTUNNUOXPYRUNNUVIVCABYRCDEFGHIJKLMUPUQZQUUBURUSZVBXPUUHUUSUUIU
      VAUKXPUUHUUFYLUJZUKOUUSXPUUGUVLUUFUKXPYLUVHVDVEXPUUFYLUVGUVHVBVMXPUVCUVIU
      UIUVAVNUOUVJQUUBVFUSVGXPUUQUUFUUTULOZYLULOUVBXPUUDUVMYLULXPUVDUVIUUDUVMVN
      ZUVFUVJUVCUVDUVIUVNUOQYQUUBVOVHVIVJXPUUFUUTYLUVGUVKUVHVKVMVLXPUUOPYGTOYGX
      PUUNYGPTXMXOUUNYGVNXNXMXOVPZUUMYFSRUVOUULYEGUVOUUKBAFBDEHIKVQVEVRVJVSVEXP
      YGXPYGABCDEFGHIJKLMVTWAZWBVMVGXPUDWCNYDUUPVNXPYCUUOUUJUUPUAWEPUDWCWDWFXQU
      DVNZXRPYBUUNTUVQXRQUDROPXQUDQRWGWHWIZUVQYAUUMSRUVQXTUULGUVQXSUUKAFUVQXRPB
      DUVRVJVEVRVJVGXPXQWCNZVPXRYBUVSXRUNNZXPUVSUVCXQWJNUVTUOXQWKQXQWLUSZWMUVSX
      PUVTYBUNNUWAABXRCDEFGHIJKLMUPWNWOZXPYCUUIUUHUUJUASPWEWCWDWPXQWEVNZXRYRYBU
      UBTUWCXRQWEROYRXQWEQRWGWQWIZUWCYAUUASRUWCXTYTGUWCXSYSAFUWCXRYRBDUWDVJVEVR
      VJVGUWBXPYCUUGUUFUUHUAPPSWCWDWRXQSVNZXRYHYBYLTUWEXRQSROYHXQSQRWGWSWIZUWEY
      AYKSRUWEXTYJGUWEXSYIAFUWEXRYHBDUWFVJVEVRVJVGUWBXPPPUEOYCUAUHUUFVNZPWCNXPP
      WTNUVEUWGXAUVGYCUUFUAPXQPVNZXRQYBYQTUWHXRQPROZQXQPQRWGUVCUWIQVNUOQXBXCWIZ
      UWHYAYPSRUWHXTYOGUWHXSYNAFUWHXRQBDUWJVJVEVRVJVGXDUSXEXFXPUUHXGXHXPUUJXGXH
      XPUUPXGXHXIXPUUEUUDYMUKOUURXPYMUUDXPYGYLUVPUVHVAXPUVCUUCUNNUUDUNNUOXPYQUU
      BUVFUVJVAQUUCURUSZXLXPUUDYLYGUWKUVHUVPXJXKVLVJVM $.

    $( Four times the inner product value ~ ipval3 , useful for simplifying
       certain proofs.  (Contributed by NM, 10-Apr-2007.)
       (New usage is discouraged.) $)
    4ipval2 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
        ( 4 x. ( A P B ) ) = ( ( ( ( N ` ( A G B ) ) ^ 2 ) -
               ( ( N ` ( A G ( -u 1 S B ) ) ) ^ 2 ) ) +
               ( _i x. ( ( ( N ` ( A G ( _i S B ) ) ) ^ 2 ) -
               ( ( N ` ( A G ( -u _i S B ) ) ) ^ 2 ) ) ) ) ) $=
      ( wcel c4 co cmul cfv ci cc cnv w3a c2 cexp cneg cmin caddc ipval2 oveq2d
      c1 cdiv wceq cr simp1 nvgcl nvcl syl2anc recnd sqcld neg1cn nvscl 3adant2
      mp3an2 syld3an3 subcld ax-icn negicn mulcl sylancr addcld cc0 wne divcan2
      4cn 4ne0 mp3an23 syl eqtrd ) EUANZAHNZBHNZUBZOABCPZQPOABFPZGRZUCUDPZAUJUE
      ZBDPZFPZGRZUCUDPZUFPZSASBDPZFPZGRZUCUDPZASUEZBDPZFPZGRZUCUDPZUFPZQPZUGPZO
      UKPZQPZXDWBWCXEOQABCDEFGHIJKLMUHUIWBXDTNZXFXDULZWBWLXCWBWFWKWBWEWBWEWBVSW
      DHNWEUMNVSVTWAUNZABEFHIJUOWDEGHILUPUQURUSWBWJWBWJWBVSWIHNZWJUMNXIVSVTWAWH
      HNZXJVSWAXKVTVSWGTNWAXKUTWGBDEHIKVAVCVBAWHEFHIJUOVDWIEGHILUPUQURUSVEWBSTN
      ZXBTNXCTNVFWBWPXAWBWOWBWOWBVSWNHNZWOUMNXIVSVTWAWMHNZXMVSWAXNVTVSXLWAXNVFS
      BDEHIKVAVCVBAWMEFHIJUOVDWNEGHILUPUQURUSWBWTWBWTWBVSWSHNZWTUMNXIVSVTWAWRHN
      ZXOVSWAXPVTVSWQTNWAXPVGWQBDEHIKVAVCVBAWREFHIJUOVDWSEGHILUPUQURUSVESXBVHVI
      VJXGOTNOVKVLXHVNVOXDOVMVPVQVR $.

    ${
      ipval3.3 $e |- M = ( -v ` U ) $.
      $( Expansion of the inner product value ~ ipval .  (Contributed by NM,
         17-Nov-2007.)  (New usage is discouraged.) $)
      ipval3 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A P B )
               = ( ( ( ( ( N ` ( A G B ) ) ^ 2 ) -
               ( ( N ` ( A M B ) ) ^ 2 ) ) +
               ( _i x. ( ( ( N ` ( A G ( _i S B ) ) ) ^ 2 ) -
               ( ( N ` ( A M ( _i S B ) ) ) ^ 2 ) ) ) ) / 4 ) ) $=
        ( wcel co c2 cexp ci cnv w3a cfv c1 cneg cmin cmul caddc c4 cdiv ipval2
        nvmval fveq2d oveq1d oveq2d wceq cc ax-icn nvscl mp3an2 syld3an3 neg1cn
        3adant2 wa nvsass mp3anr1 mpanr1 mulm1i oveq1i eqtr3di oveq12d eqtr4d
        eqtrd ) EUAPZAIPZBIPZUBZABCQABFQHUCRSQZAUDUEZBDQFQZHUCZRSQZUFQZTATBDQZF
        QHUCRSQZATUEZBDQZFQZHUCZRSQZUFQZUGQZUHQZUIUJQVRABGQZHUCZRSQZUFQZTWEAWDG
        QZHUCZRSQZUFQZUGQZUHQZUIUJQABCDEFHIJKLMNUKVQXCWMUIUJVQWQWCXBWLUHVQWPWBV
        RUFVQWOWARSVQWNVTHABDEFGIJKLOULUMUNUOVQXAWKTUGVQWTWJWEUFVQWSWIRSVQWRWHH
        VQWRAVSWDDQZFQZWHVNVOVPWDIPZWRXEUPVNVPXFVOVNTUQPZVPXFURTBDEIJLUSUTVCAWD
        DEFGIJKLOULVAVQXDWGAFVNVPXDWGUPVOVNVPVDVSTUGQZBDQZXDWGVNXGVPXIXDUPZURVN
        VSUQPXGVPXJVBVSTBDEIJLVEVFVGXHWFBDTURVHVIVJVCUOVMUMUNUOUOVKUNVL $.
    $}
  $}

  ${
    ipid.1 $e |- X = ( BaseSet ` U ) $.
    ipid.6 $e |- N = ( normCV ` U ) $.
    ipid.7 $e |- P = ( .iOLD ` U ) $.
    $( The inner product of a vector with itself is the square of the vector's
       norm.  Equation I4 of [Ponnusamy] p. 362.  (Contributed by NM,
       1-Feb-2007.)  (New usage is discouraged.) $)
    ipidsq $p |- ( ( U e. NrmCVec /\ A e. X ) ->
                ( A P A ) = ( ( N ` A ) ^ 2 ) ) $=
      ( wcel co cfv c2 cexp c1 ci cmul caddc wceq cc0 cc cnv wa cpv cneg cns c4
      cmin cdiv eqid ipval2 3anidm23 nv2 fveq2d cr cle wbr pm3.2i nvsge0 mp3an2
      2re 0le2 eqtrd oveq1d nvcl recnd cn0 2cn mulexp mp3an13 syl oveq1i eqtrdi
      2nn0 sq2 cn0v nvrinv adantr sq0id oveq12d 4cn sqcld mulcl sylancr subid1d
      nvz0 csqrt 1re neg1rr absreim mp2an ax-icn ax-1cn mulneg2i mulridi negeqi
      eqtri oveq2i fveq2i sqneg ax-mp 3eqtr3i 3eqtr2i negicn addcli nvs 3eqtr4a
      cabs nvdir mp3anr1 mpanr1 nvsid 3eqtr3d oveq2d w3a ipval2lem4 mpan2 it0e0
      subidd addridd eqtr2d wne 4ne0 divcan3 mp3an23 3eqtr2d ) CUAIZAEIZUBZAABJ
      ZAACUCKZJZDKZLMJZANUDZACUEKZJYJJZDKZLMJZUGJZOAOAYOJZYJJZDKZLMJZAOUDZAYOJZ
      YJJZDKZLMJZUGJZPJZQJZUFUHJZUFADKZLMJZPJZUFUHJZUUNYFYGYIUULRAABYOCYJDEFYJU
      IZYOUIZGHUJUKYHUUOUUKUFUHYHUUKUUOSQJUUOYHYSUUOUUJSQYHYSUUOSUGJUUOYHYMUUOY
      RSUGYHYMLUUMPJZLMJZUUOYHYLUUSLMYHYLLAYOJZDKZUUSYHYKUVADAYOCYJEFUUQUURULUM
      YFLUNIZSLUOUPZUBYGUVBUUSRUVCUVDUTVAUQLAYOCDEFUURGURUSVBVCYHUUTLLMJZUUNPJZ
      UUOYHUUMTIZUUTUVFRZYHUUMACDEFGVDVEZLTIUVGLVFIUVHVGVMLUUMLVHVIVJUVEUFUUNPV
      NVKVLVBYHYQYHYQCVOKZDKZSYHYPUVJDAYOCYJEUVJFUUQUURUVJUIZVPUMYFUVKSRYGCDUVJ
      UVLGWEVQVBVRVSYHUUOYHUFTIZUUNTIZUUOTIVTYHUUMUVIWAZUFUUNWBWCZWDVBYHUUJOSPJ
      SYHUUISOPYHUUIUUCUUCUGJSYHUUHUUCUUCUGYHUUGUUBLMYHNUUDQJZAYOJZDKZNOQJZAYOJ
      ZDKZUUGUUBYHUVQXGKZUUMPJZUVTXGKZUUMPJZUVSUWBUWCUWEUUMPUWCNLMJZUWGQJZWFKZN
      ONPJZQJZXGKZUWENOYNPJZQJZXGKZUWGYNLMJZQJZWFKZUWCUWINUNIZYNUNIUWOUWRRWGWHN
      YNWIWJUWNUVQXGUWMUUDNQUWMUWJUDUUDONWKWLWMUWJOOWKWNZWOWPWQWRUWQUWHWFUWPUWG
      UWGQNTIZUWPUWGRWLNWSWTWQWRXAUWSUWSUWLUWIRWGWGNNWIWJUWKUVTXGUWJONQUWTWQWRX
      BVKYFUVQTIYGUVSUWDRNUUDWLXCXDUVQAYOCDEFUURGXEUSYFUVTTIYGUWBUWFRNOWLWKXDUV
      TAYOCDEFUURGXEUSXFYHUVRUUFDYHUVRNAYOJZUUEYJJZUUFYFUUDTIZYGUVRUXCRZXCYFUXA
      UXDYGUXEWLNUUDAYOCYJEFUUQUURXHXIXJYHUXBAUUEYJAYOCEFUURXKZVCVBUMYHUWAUUADY
      HUWAUXBYTYJJZUUAYFOTIZYGUWAUXGRZWKYFUXAUXHYGUXIWLNOAYOCYJEFUUQUURXHXIXJYH
      UXBAYTYJUXFVCVBUMXLVCXMYHUUCYFYGUUCTIZYFYGYGXNUXHUXJWKAAOBYOCYJDEFUUQUURG
      HXOXPUKXRVBXMXQVLVSYHUUOUVPXSXTVCYHUVNUUPUUNRZUVOUVNUVMUFSYAUXKVTYBUUNUFY
      CYDVJYE $.

    $( Norm expressed in terms of inner product.  (Contributed by NM,
       11-Sep-2007.)  (New usage is discouraged.) $)
    ipnm $p |- ( ( U e. NrmCVec /\ A e. X ) ->
                ( N ` A ) = ( sqrt ` ( A P A ) ) ) $=
      ( cnv wcel wa co csqrt cfv c2 cexp ipidsq fveq2d nvcl nvge0 sqrtsqd
      eqtr2d ) CIJAEJKZAABLZMNADNZOPLZMNUEUCUDUFMABCDEFGHQRUCUEACDEFGSACDEFGTUA
      UB $.
  $}

  ${
    $d k A $.  $d k B $.  $d k x y U $.  $d k x y X $.
    ipcl.1 $e |- X = ( BaseSet ` U ) $.
    ipcl.7 $e |- P = ( .iOLD ` U ) $.
    $( An inner product is a complex number.  (Contributed by NM, 1-Feb-2007.)
       (Revised by Mario Carneiro, 5-May-2014.)  (New usage is discouraged.) $)
    dipcl $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                ( A P B ) e. CC ) $=
      ( vk cnv wcel w3a co c1 c4 cfz ci cexp cfv cc eqid cns cpv cnmcv cmul csu
      cv c2 cdiv ipval fzfid cn0 ax-icn elfznn nnnn0d sylancr adantl ipval2lem4
      wa expcl sylan2 mulcld fsumcl cc0 wne 4cn 4ne0 divcl mp3an23 syl eqeltrd
      ) DIJAEJBEJKZABCLMNOLZPHUFZQLZAVNBDUARZLDUBRZLDUCRZRUGQLZUDLZHUEZNUHLZSAB
      CVODHVPVQEFVPTZVOTZVQTZGUIVKVTSJZWASJZVKVLVSHVKMNUJVKVMVLJZURVNVRWGVNSJZV
      KWGPSJVMUKJWHULWGVMVMNUMUNPVMUSUOZUPWGVKWHVRSJWIABVNCVODVPVQEFWBWCWDGUQUT
      VAVBWENSJNVCVDWFVEVFVTNVGVHVIVJ $.

    $( Mapping for the inner product operation.  (Contributed by NM,
       28-Jan-2008.)  (Revised by Mario Carneiro, 16-Nov-2013.)
       (New usage is discouraged.) $)
    ipf $p |- ( U e. NrmCVec -> P : ( X X. X ) --> CC ) $=
      ( vx vy vk cnv wcel cxp cc wf c4 co cv cexp cfv wral eqid c1 cfz ci cnmcv
      cns cpv cmul csu cdiv cmpo w3a ipval dipcl eqeltrrd 3expib ralrimivv fmpo
      c2 sylib dipfval feq1d mpbird ) BIJZCCKZLAMVDLFGCCUANUBOUCHPQOZFPZVEGPZBU
      ERZOBUFRZOBUDRZRURQOUGOHUHNUIOZUJZMZVCVKLJZGCSFCSVMVCVNFGCCVCVFCJZVGCJZVN
      VCVOVPUKVFVGAOVKLVFVGAVHBHVIVJCDVITZVHTZVJTZEULVFVGABCDEUMUNUOUPFGCCVKLVL
      VLTUQUSVCVDLAVLFGAVHBHVIVJCDVQVRVSEUTVAVB $.

    $( The complex conjugate of an inner product reverses its arguments.
       Equation I1 of [Ponnusamy] p. 362.  (Contributed by NM, 1-Feb-2007.)
       (New usage is discouraged.) $)
    dipcj $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
               ( * ` ( A P B ) ) = ( B P A ) ) $=
      ( wcel co cfv c2 cexp cmin ci c4 cdiv wceq cc mpan2 cr cnv w3a ccj cpv c1
      cnmcv cneg cns cmul caddc eqid ipval2 fveq2d 3com23 ipval2lem3 ipval2lem4
      recnd neg1cn subcld ax-icn negicn mulcl sylancr addcld cc0 wne 4ne0 cjdiv
      4cn mp3an23 syl 4re cjre ax-mp oveq2i ipval2lem2 resubcld syl2anc submul2
      cjreim mp3an2 nvcom oveq1d oveq12d negsubdi2d eqcomd oveq2d 3eqtrd eqtrid
      nvdif nvpi eqtrd eqtr4d ) DUAHZAEHZBEHZUBZABCIZUCJABDUDJZIZDUFJZJZKLIZAUE
      UGZBDUHJZIWSIXAJZKLIZMIZNANBXEIWSIXAJZKLIZANUGZBXEIWSIXAJZKLIZMIZUIIZUJIZ
      OPIZUCJZBACIZWQWRXQUCABCXEDWSXAEFWSUKZXEUKZXAUKZGULUMWQXSBAWSIZXAJZKLIZBX
      DAXEIWSIXAJZKLIZMIZNBNAXEIWSIXAJZKLIZBXKAXEIWSIXAJZKLIZMIZUIIZUJIZOPIZXRW
      NWPWOXSYPQBACXEDWSXAEFXTYAYBGULUNWQXRXPUCJZOUCJZPIZYPWQXPRHZXRYSQZWQXHXOW
      QXCXGWQXCABCXEDWSXAEFXTYAYBGUOZUQWQXDRHZXGRHURABXDCXEDWSXAEFXTYAYBGUPSUSZ
      WQNRHZXNRHZXORHUTWQXJXMWQUUEXJRHUTABNCXEDWSXAEFXTYAYBGUPSZWQXKRHZXMRHVAAB
      XKCXEDWSXAEFXTYAYBGUPSZUSZNXNVBVCVDYTORHOVEVFUUAVIVGXPOVHVJVKWQYSYQOPIYPY
      ROYQPOTHYROQVLOVMVNVOWQYQYOOPWQYQXHXOMIZXHNXNUGZUIIZUJIZYOWQXHTHXNTHYQUUK
      QWQXCXGUUBWQUUCXGTHURABXDCXEDWSXAEFXTYAYBGVPSVQWQXJXMWQUUEXJTHUTABNCXEDWS
      XAEFXTYAYBGVPSWQUUHXMTHVAABXKCXEDWSXAEFXTYAYBGVPSVQXHXNVTVRWQXHRHZUUFUUKU
      UNQZUUDUUJUUOUUEUUFUUPUTXHNXNVSWAVRWQXHYHUUMYNUJWQXCYEXGYGMWQXBYDKLWQWTYC
      XAABDWSEFXTWBUMWCWQXFYFKLABXEDWSXAEFXTYAYBWJWCWDWQUULYMNUIWQUULXMXJMIYMWQ
      XJXMUUGUUIWEWQXMYJXJYLMWQXLYIKLWQYIXLWNWPWOYIXLQBAXEDWSXAEFXTYAYBWKUNWFWC
      WQXIYKKLABXEDWSXAEFXTYAYBWKWCWDWLWGWDWHWCWIWLWMWM $.

    $( An inner product times its conjugate.  (Contributed by NM, 23-Nov-2007.)
       (New usage is discouraged.) $)
    ipipcj $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                ( ( A P B ) x. ( B P A ) ) = ( ( abs ` ( A P B ) ) ^ 2 ) ) $=
      ( cnv wcel w3a co cabs cfv c2 cexp ccj cmul dipcl absvalsqd dipcj oveq2d
      eqtr2d ) DHIAEIBEIJZABCKZLMNOKUDUDPMZQKUDBACKZQKUCUDABCDEFGRSUCUEUFUDQABC
      DEFGTUAUB $.

    $( Orthogonality (meaning inner product is 0) is commutative.  (Contributed
       by NM, 17-Apr-2008.)  (New usage is discouraged.) $)
    diporthcom $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X )
              -> ( ( A P B ) = 0 <-> ( B P A ) = 0 ) ) $=
      ( cnv wcel co cc0 wceq ccj cfv fveq2 cj0 eqtrdi dipcj eqeq1d imbitrid w3a
      3com23 impbid ) DHIZAEIZBEIZUAZABCJZKLZBACJZKLZUIUHMNZKLUGUKUIULKMNZKUHKM
      OPQUGULUJKABCDEFGRSTUKUJMNZKLUGUIUKUNUMKUJKMOPQUGUNUHKUDUFUEUNUHLBACDEFGR
      UBSTUC $.
  $}

  ${
    dip0r.1 $e |- X = ( BaseSet ` U ) $.
    dip0r.5 $e |- Z = ( 0vec ` U ) $.
    dip0r.7 $e |- P = ( .iOLD ` U ) $.
    $( Inner product with a zero second argument.  (Contributed by NM,
       5-Feb-2007.)  (New usage is discouraged.) $)
    dip0r $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( A P Z ) = 0 ) $=
      ( wcel co cfv c2 cexp cmin ci caddc c4 cc0 wceq oveq2d cnv cpv cnmcv cneg
      wa c1 cns cmul cdiv nvzcl adantr eqid ipval2 mpd3an3 cc neg1cn nvsz mpan2
      fveq2d oveq1d ipval2lem3 recnd subidd negicn ax-icn eqtr4d w3a ipval2lem4
      cr eqtrd oveq12d it0e0 oveq2i 00id eqtri eqtrdi 4cn 4ne0 div0i ) CUAIZADI
      ZUEZAEBJZAECUBKZJZCUCKZKZLMJZAUFUDZECUGKZJZWDJZWFKZLMJZNJZOAOEWJJZWDJZWFK
      ZLMJZAOUDZEWJJZWDJZWFKZLMJZNJZUHJZPJZQUIJZRVTWAEDIZWCXHSVTXIWACDEFGUJUKZA
      EBWJCWDWFDFWDULZWJULZWFULZHUMUNWBXHRQUIJRWBXGRQUIWBXGRORUHJZPJZRWBWORXFXN
      PWBWOWHWHNJRWBWNWHWHNWBWMWGLMWBWLWEWFWBWKEAWDVTWKESZWAVTWIUOIXPUPWIWJCEXL
      GUQURUKTUSUTTWBWHWBWHVTWAXIWHVIIXJAEBWJCWDWFDFXKXLXMHVAUNVBVCVJWBXEROUHWB
      XEWSWSNJRWBXDWSWSNWBXCWRLMWBXBWQWFWBXAWPAWDVTXAWPSWAVTXAEWPVTWTUOIXAESVDW
      TWJCEXLGUQURVTOUOIZWPESVEOWJCEXLGUQURVFUKTUSUTTWBWSVTWAXIWSUOIZXJVTWAXIVG
      XQXRVEAEOBWJCWDWFDFXKXLXMHVHURUNVCVJTVKXORRPJRXNRRPVLVMVNVOVPUTQVQVRVSVPV
      J $.

    $( Inner product with a zero first argument.  Part of proof of Theorem 6.44
       of [Ponnusamy] p. 361.  (Contributed by NM, 5-Feb-2007.)
       (New usage is discouraged.) $)
    dip0l $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( Z P A ) = 0 ) $=
      ( cnv wcel wa co ccj cfv cc0 wceq nvzcl adantr dipcj mpd3an3 dip0r fveq2d
      cj0 eqtrdi eqtr3d ) CIJZADJZKZAEBLZMNZEABLZOUFUGEDJZUJUKPUFULUGCDEFGQRAEB
      CDFHSTUHUJOMNOUHUIOMABCDEFGHUAUBUCUDUE $.

    $( The inner product of a vector with itself is zero iff the vector is
       zero.  Part of Definition 3.1-1 of [Kreyszig] p. 129.  (Contributed by
       NM, 24-Jan-2008.)  (New usage is discouraged.) $)
    ipz $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( ( A P A ) = 0 <-> A = Z ) ) $=
      ( cnv wcel wa co cc0 wceq cnmcv cfv c2 cexp eqid ipidsq eqeq1d cc wb nvcl
      recnd sqeq0 syl nvz 3bitrd ) CIJADJKZAABLZMNACOPZPZQRLZMNZUMMNZAENUJUKUNM
      ABCULDFULSZHTUAUJUMUBJUOUPUCUJUMACULDFUQUDUEUMUFUGACULDEFGUQUHUI $.
  $}

  ${
    $d k x y z J $.  $d k x y z K $.  $d k x y z U $.
    dipcn.p $e |- P = ( .iOLD ` U ) $.
    dipcn.c $e |- C = ( IndMet ` U ) $.
    dipcn.j $e |- J = ( MetOpen ` C ) $.
    dipcn.k $e |- K = ( TopOpen ` CCfld ) $.
    $( Inner product is jointly continuous in both arguments.  (Contributed by
       NM, 21-Aug-2007.)  (Revised by Mario Carneiro, 10-Sep-2015.)
       (New usage is discouraged.) $)
    dipcn $p |- ( U e. NrmCVec -> P e. ( ( J tX J ) Cn K ) ) $=
      ( vx vy vk vz wcel cfv c4 co ccn cc a1i cnv cba c1 cfz ci cv cexp cns cpv
      cnmcv c2 cmul csu cdiv cmpo ctx eqid dipfval ctopon imsxmet mopntopon syl
      cxmet fzfid wa adantr cnfldtopon cn0 ax-icn cn elfznn adantl nnnn0d expcl
      sylancr cnmpt2c cnmpt1st cnmpt2nd smcn cnmpt22f vacn nmcnc cnmpt21f oveq1
      cmpt sqcn cnmpt21 mulcn fsum2cn cc0 wne 4cn 4ne0 divccn mp2an eqeltrd ) C
      UANZBJKCUBOZWRUCPUDQZUELUFZUGQZJUFZXAKUFZCUHOZQZCUIOZQZCUJOZOZUKUGQZULQZL
      UMZPUNQZUODDUPQZERQJKBXDCLXFXHWRWRUQZXFUQZXDUQZXHUQZFURWQJKMXLMUFZPUNQZXM
      DDEEWRWRSWQAWRVCONDWRUSONZACWRXOGUTADWRHVAVBZYBWQJKWSXKLDEDWRWRIYBWQUCPVD
      YBWQWTWSNZVEZJKXAXJULDDEEEWRWRWQYAYCYBVFZYEYDJKXADDEWRWRSYEYEESUSONZYDEIV
      GZTZYDUESNWTVHNXASNVIYDWTYCWTVJNWQWTPVKVLVMUEWTVNVOVPZYDJKMXIXSUKUGQZXJDD
      EEWRWRSYEYEYDJKXGXHDDDEWRWRYEYEYDJKXBXEXFDDDDDWRWRYEYEYDJKDDWRWRYEYEVQYDJ
      KXAXCXDDDEDDWRWRYEYEYIYDJKDDWRWRYEYEVRWQXDEDUPQDRQNYCAXDCDEGHXQIVSVFVTWQX
      FXNDRQNYCACXFDGHXPWAVFVTWQXHDERQNYCACDEXHXRGHIWBVFWCYHMSYJWEEERQZNYDMEIWF
      TXSXIUKUGWDWGULEEUPQERQNYDEIWHTVTWIYFWQYGTMSXTWEYKNZWQPSNPWJWKYLWLWMMPEIW
      NWOTXSXLPUNWDWGWP $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Subspaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c SubSp $.

  $( Extend class notation with the class of all subspaces of normed complex
     vector spaces. $)
  css $a class SubSp $.

  ${
    $d u w $.
    $( Define the class of all subspaces of normed complex vector spaces.
       (Contributed by NM, 26-Jan-2008.)  (New usage is discouraged.) $)
    df-ssp $a |- SubSp = ( u e. NrmCVec |->
     { w e. NrmCVec | ( ( +v ` w ) C_ ( +v ` u ) /\ ( .sOLD ` w ) C_ ( .sOLD `
        u )
         /\ ( normCV ` w ) C_ ( normCV ` u ) ) } ) $.
  $}

  ${
    $d u w G $.  $d u w N $.  $d u w S $.  $d u w U $.
    sspval.g $e |- G = ( +v ` U ) $.
    sspval.s $e |- S = ( .sOLD ` U ) $.
    sspval.n $e |- N = ( normCV ` U ) $.
    sspval.h $e |- H = ( SubSp ` U ) $.
    $( The set of all subspaces of a normed complex vector space.  (Contributed
       by NM, 26-Jan-2008.)  (Revised by Mario Carneiro, 16-Nov-2013.)
       (New usage is discouraged.) $)
    sspval $p |- ( U e. NrmCVec -> H = { w e. NrmCVec | (
         ( +v ` w ) C_ G /\ ( .sOLD ` w ) C_ S /\ ( normCV ` w ) C_ N ) } ) $=
      ( vu cnv wcel cfv cpv wss cns cnmcv fveq2 eqtr4di css cv crab wceq sseq2d
      w3a 3anbi123d rabbidv df-ssp cpw cxp fvexi pwex xpex wi rabss cop wa fvex
      elpw opelxpi syl2anbr biimpri syl2an 3impa eqid nvop eleq1d mprgbir ssexi
      imbitrrid fvmpt eqtrid ) CLMECUANAUBZONZDPZVNQNZBPZVNRNZFPZUFZALUCZJKCVOK
      UBZONZPZVQWCQNZPZVSWCRNZPZUFZALUCWBLUAWCCUDZWJWAALWKWEVPWGVRWIVTWKWDDVOWK
      WDCONDWCCOSGTUEWKWFBVQWKWFCQNBWCCQSHTUEWKWHFVSWKWHCRNFWCCRSITUEUGUHAKUIWB
      DUJZBUJZUKZFUJZUKZWNWOWLWMDDCOGULUMBBCQHULUMUNFFCRIULUMUNWBWPPWAVNWPMZUOA
      LWAALWPUPWAWQVNLMZVOVQUQZVSUQZWPMZVPVRVTXAVPVRURWSWNMZVSWOMZXAVTVPVOWLMVQ
      WMMXBVRVODVNOUSUTVQBVNQUSUTVOVQWLWMVAVBXCVTVSFVNRUSUTVCWSVSWNWOVAVDVEWRVN
      WTWPVQVNVOVSVOVFVQVFVSVFVGVHVKVIVJVLVM $.
  $}

  ${
    $d w F $.  $d w G $.  $d w M $.  $d w N $.  $d w R $.  $d w S $.  $d w U $.
    $d w W $.
    isssp.g $e |- G = ( +v ` U ) $.
    isssp.f $e |- F = ( +v ` W ) $.
    isssp.s $e |- S = ( .sOLD ` U ) $.
    isssp.r $e |- R = ( .sOLD ` W ) $.
    isssp.n $e |- N = ( normCV ` U ) $.
    isssp.m $e |- M = ( normCV ` W ) $.
    isssp.h $e |- H = ( SubSp ` U ) $.
    $( The predicate "is a subspace."  (Contributed by NM, 26-Jan-2008.)
       (New usage is discouraged.) $)
    isssp $p |- ( U e. NrmCVec -> ( W e. H <-> ( W e. NrmCVec /\ (
               F C_ G /\ R C_ S /\ M C_ N ) ) ) ) $=
      ( vw cnv cfv wss wcel cv cpv cns cnmcv crab wa sspval eleq2d wceq eqtr4di
      w3a fveq2 sseq1d 3anbi123d elrab bitrdi ) CRUAZIFUAIQUBZUCSZETZUSUDSZBTZU
      SUESZHTZULZQRUFZUAIRUADETZABTZGHTZULZUGURFVGIQBCEFHJLNPUHUIVFVKQIRUSIUJZV
      AVHVCVIVEVJVLUTDEVLUTIUCSDUSIUCUMKUKUNVLVBABVLVBIUDSAUSIUDUMMUKUNVLVDGHVL
      VDIUESGUSIUEUMOUKUNUOUPUQ $.
  $}

  ${
    sspid.h $e |- H = ( SubSp ` U ) $.
    $( A normed complex vector space is a subspace of itself.  (Contributed by
       NM, 8-Apr-2008.)  (New usage is discouraged.) $)
    sspid $p |- ( U e. NrmCVec -> U e. H ) $=
      ( cnv wcel cpv cfv wss cns cnmcv w3a ssid 3pm3.2i jctr eqid isssp mpbird
      wa ) ADEZABESAFGZTHZAIGZUBHZAJGZUDHZKZRSUFUAUCUETLUBLUDLMNUBUBATTBUDUDATO
      ZUGUBOZUHUDOZUICPQ $.
  $}

  ${
    sspnv.h $e |- H = ( SubSp ` U ) $.
    $( A subspace is a normed complex vector space.  (Contributed by NM,
       27-Jan-2008.)  (New usage is discouraged.) $)
    sspnv $p |- ( ( U e. NrmCVec /\ W e. H ) -> W e. NrmCVec ) $=
      ( cnv wcel cpv cfv wss cns cnmcv w3a eqid isssp simprbda ) AEFCBFCEFCGHZA
      GHZICJHZAJHZICKHZAKHZILRSAPQBTUACQMPMSMRMUAMTMDNO $.
  $}

  ${
    sspba.x $e |- X = ( BaseSet ` U ) $.
    sspba.y $e |- Y = ( BaseSet ` W ) $.
    sspba.h $e |- H = ( SubSp ` U ) $.
    $( The base set of a subspace is included in the parent base set.
       (Contributed by NM, 27-Jan-2008.)  (New usage is discouraged.) $)
    sspba $p |- ( ( U e. NrmCVec /\ W e. H ) -> Y C_ X ) $=
      ( cnv wcel wa cpv cfv crn wss cns cnmcv w3a eqid bafval isssp simp1d rnss
      simplbda syl 3sstr4g ) AIJZCBJZKZCLMZNZALMZNZEDUIUJULOZUKUMOUIUNCPMZAPMZO
      ZCQMZAQMZOZUGUHCIJUNUQUTRUOUPAUJULBURUSCULSZUJSZUPSUOSUSSURSHUAUDUBUJULUC
      UECUJEGVBTAULDFVATUF $.
  $}

  ${
    $d x y F $.  $d x y G $.  $d x y H $.  $d x y U $.  $d x y W $.
    $d x y Y $.
    sspg.y $e |- Y = ( BaseSet ` W ) $.
    sspg.g $e |- G = ( +v ` U ) $.
    sspg.f $e |- F = ( +v ` W ) $.
    sspg.h $e |- H = ( SubSp ` U ) $.
    $( Vector addition on a subspace is a restriction of vector addition on the
       parent space.  (Contributed by NM, 28-Jan-2008.)
       (New usage is discouraged.) $)
    sspg $p |- ( ( U e. NrmCVec /\ W e. H ) -> F = ( G |` ( Y X. Y ) ) ) $=
      ( vx vy wcel wa wceq wfn wss cfv eqid syl cnv cxp cres cv co wral w3a cba
      wfun nvgf ffund funresd adantr wf sspnv ffnd fnresdm cnmcv isssp simplbda
      simp1d ssres eqsstrrd 3jca oprssov sylan eqcomd ralrimivva jctil wb sspba
      cns xpss12 syl2anc fnssres eqfnov mpbird ) AUAMZEDMZNZBCFFUBZUCZOZWAWAOZK
      UDZLUDZBUEZWEWFWBUEZOZLFUFKFUFZNZVTWJWDVTWIKLFFVTWEFMWFFMNZNWHWGVTWBUIZBW
      APZBWBQZUGWLWHWGOVTWMWNWOVRWMVSVRWACVRAUHRZWPUBZWPCACWPWPSZHUJZUKULUMVTWA
      FBVTEUAMZWAFBUNADEJUOEBFGIUJTUPZVTBBWAUCZWBVTWNXBBOXAWABUQTVTBCQZXBWBQVTX
      CEVLRZAVLRZQZEURRZAURRZQZVRVSWTXCXFXIUGXDXEABCDXGXHEHIXESXDSXHSXGSJUSUTVA
      BCWAVBTVCVDWEWFFFWBBVEVFVGVHWASVIVTWNWBWAPZWCWKVJXAVTCWQPZWAWQQZXJVRXKVSV
      RWQWPCWSUPUMVTFWPQZXMXLADEWPFWRGJVKZXNFWPFWPVMVNWQWACVOVNKLFFFFBWBVPVNVQ
      $.

    $( Vector addition on a subspace in terms of vector addition on the parent
       space.  (Contributed by NM, 28-Jan-2008.)
       (New usage is discouraged.) $)
    sspgval $p |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. Y /\ B e. Y ) ) ->
                    ( A F B ) = ( A G B ) ) $=
      ( cnv wcel wa co cxp cres sspg oveqd ovres sylan9eq ) CMNGFNOZAHNBHNOABDP
      ABEHHQRZPABEPUCDUDABCDEFGHIJKLSTABHHEUAUB $.
  $}

  ${
    $d x y R $.  $d x y S $.  $d x y H $.  $d x y U $.  $d x y W $.
    $d x y Y $.
    ssps.y $e |- Y = ( BaseSet ` W ) $.
    ssps.s $e |- S = ( .sOLD ` U ) $.
    ssps.r $e |- R = ( .sOLD ` W ) $.
    ssps.h $e |- H = ( SubSp ` U ) $.
    $( Scalar multiplication on a subspace is a restriction of scalar
       multiplication on the parent space.  (Contributed by NM, 28-Jan-2008.)
       (New usage is discouraged.) $)
    ssps $p |- ( ( U e. NrmCVec /\ W e. H ) -> R = ( S |` ( CC X. Y ) ) ) $=
      ( vx vy wcel wa cc wceq wfn wss cfv eqid cnv cxp cres cv co wral wfun w3a
      cba nvsf ffund funresd adantr sspnv syl ffnd fnresdm cnmcv isssp simplbda
      cpv simp2d ssres eqsstrrd 3jca oprssov sylan eqcomd ralrimivva jctil ssid
      wf wb sspba xpss12 sylancr fnssres syl2anc eqfnov mpbird ) CUAMZEDMZNZABO
      FUBZUCZPZWDWDPZKUDZLUDZAUEZWHWIWEUEZPZLFUFKOUFZNZWCWMWGWCWLKLOFWCWHOMWIFM
      NZNWKWJWCWEUGZAWDQZAWERZUHWOWKWJPWCWPWQWRWAWPWBWAWDBWAOCUISZUBZWSBBCWSWST
      ZHUJZUKULUMWCWDFAWCEUAMZWDFAVLCDEJUNAEFGIUJUOUPZWCAAWDUCZWEWCWQXEAPXDWDAU
      QUOWCABRZXEWERWCEVASZCVASZRZXFEURSZCURSZRZWAWBXCXIXFXLUHABCXGXHDXJXKEXHTX
      GTHIXKTXJTJUSUTVBABWDVCUOVDVEWHWIOFWEAVFVGVHVIWDTVJWCWQWEWDQZWFWNVMXDWCBW
      TQZWDWTRZXMWAXNWBWAWTWSBXBUPUMWCOORFWSRXOOVKCDEWSFXAGJVNOOFWSVOVPWTWDBVQV
      RKLOFOFAWEVSVRVT $.

    $( Scalar multiplication on a subspace in terms of scalar multiplication on
       the parent space.  (Contributed by NM, 28-Jan-2008.)
       (New usage is discouraged.) $)
    sspsval $p |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. CC /\ B e. Y ) ) ->
                    ( A R B ) = ( A S B ) ) $=
      ( cnv wcel wa cc co cxp cres ssps oveqd ovres sylan9eq ) EMNGFNOZAPNBHNOA
      BCQABDPHRSZQABDQUDCUEABCDEFGHIJKLTUAABPHDUBUC $.
  $}

  $( TODO - sspvallem doesn't save space yet, but might if another
     operation is added. $)
  $(
  @{
    @d x y F @.  @d x y G @.  @d x y H @.  @d x y U @.  @d x y W @.
    @d x y Y @.
    sspvallem.y @e |- Y = ( BaseSet ` W ) @.
    sspvallem.h @e |- H = ( SubSp ` U ) @.
    @{
      sspvallem.1 @e |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. Y /\ B e. Y )
         ) -> R = S ) @.
      sspvallem.2 @e |- ( ( W e. NrmCVec /\ A e. Y /\ B e. Y ) -> P = R ) @.
      sspvallem.3 @e |- ( ( U e. NrmCVec /\ A e. ( BaseSet ` U ) /\
          B e. ( BaseSet ` U ) ) -> Q = S ) @.
      @( Lemma for ~ sspmval and others. @)
      sspvallem @p |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. Y /\ B e. Y ) )
          -> P = Q ) @=
       ( cnv wcel wa wceq 3expb sspnv sylanOLD cba cfv eqid sspba sseld anim12d
        imp adantlr syldan 3eqtr4d ) GPQZIHQZRZAJQZBJQZRZREFCDMIPQZURCESZUOUSUP
        UQUTNTGHILUAUBUOURAGUCUDZQZBVAQZRZDFSZUOURVDUOUPVBUQVCUOJVAAGHIVAJVAUEK
        LUFZUGUOJVABVFUGUHUIUMVDVEUNUMVBVCVEOTUJUKUL @.
        @( [ ?] @) @( [1-Feb-2008] @)
    @}

    @{
      sspmlem.1  @e |- ( ( ( U e. NrmCVec /\ W e. H ) /\ (
       x e. Y /\ y e. Y ) ) -> ( x F y ) = ( x G y ) ) @.
      sspmlem.2 @e |- ( W e. NrmCVec -> F : ( Y X. Y ) --> R ) @.
      sspmlem.3 @e |- ( U e. NrmCVec -> G : ( ( BaseSet ` U ) X.
               ( BaseSet ` U ) ) --> S ) @.
      @( Lemma for ~ sspm and others. @)
      sspmlem @p |- ( ( U e. NrmCVec /\ W e. H ) ->
            F = ( G |` ( Y X. Y ) ) ) @=
        ( cnv wcel wa cxp cres wceq cv co wral ovres adantl eqtr4d ex
        ralrimivv eqid jctil wfn wb eqfnov wf sspnv ffn 3syl cba cfv wss
   fnssres syl adantr sspba xpss12 anidms sylancOLD mpbird ) EPQZIHQZRZFGJJSZTZ
        UAZVMVMUAZAUBZBUBZFUCZVQVRVNUCZUAZBJUDAJUDZRZVLWBVPVLWAABJJVLVQJQVRJQRZ
        WAVLWDRVSVQVRGUCZVTMWDVTWEUAVLVQVRJJGUEUFUGUHUIVMUJUKFVMULZVNVMULZVOWCU
        MVLABJJJJFVNUNVLIPQVMCFUOWFEHILUPNVMCFUQURGEUSUTZWHSZULZVMWIVAZWGVLWIVM
        GVBVJWJVKVJWIDGUOWJOWIDGUQVCVDVLJWHVAZWKEHIWHJWHUJKLVEWLWKJWHJWHVFVGVCV
        HVHVI @.
        @( [ ?] @) @( [1-Feb-2008] @)
    @}
  @}
  $)

  ${
    $d x y F $.  $d x y G $.  $d x y H $.  $d x y U $.  $d x y W $.
    $d x y Y $.
    sspmlem.y $e |- Y = ( BaseSet ` W ) $.
    sspmlem.h $e |- H = ( SubSp ` U ) $.
    sspmlem.1 $e |- ( ( ( U e. NrmCVec /\ W e. H ) /\ (
             x e. Y /\ y e. Y ) ) -> ( x F y ) = ( x G y ) ) $.
    sspmlem.2 $e |- ( W e. NrmCVec -> F : ( Y X. Y ) --> R ) $.
    sspmlem.3 $e |- ( U e. NrmCVec -> G : ( ( BaseSet ` U ) X.
             ( BaseSet ` U ) ) --> S ) $.
    $( Lemma for ~ sspm and others.  (Contributed by NM, 1-Feb-2008.)
       (New usage is discouraged.) $)
    sspmlem $p |- ( ( U e. NrmCVec /\ W e. H ) -> F = ( G |` ( Y X. Y ) ) ) $=
      ( wcel wa wceq co wfn cnv cxp cres cv wral ovres adantl eqtr4d ralrimivva
      eqid jctil wb sspnv ffn 3syl cba cfv wss ffnd adantr sspba xpss12 syl2anc
      wf fnssres eqfnov mpbird ) EUAPZIHPZQZFGJJUBZUCZRZVKVKRZAUDZBUDZFSZVOVPVL
      SZRZBJUEAJUEZQZVJVTVNVJVSABJJVJVOJPVPJPQZQVQVOVPGSZVRMWBVRWCRVJVOVPJJGUFU
      GUHUIVKUJUKVJFVKTZVLVKTZVMWAULVJIUAPVKCFVDWDEHILUMNVKCFUNUOVJGEUPUQZWFUBZ
      TZVKWGURZWEVHWHVIVHWGDGOUSUTVJJWFURZWJWIEHIWFJWFUJKLVAZWKJWFJWFVBVCWGVKGV
      EVCABJJJJFVLVFVCVG $.
  $}

  ${
    $d x y L $.  $d x y M $.  $d x y H $.  $d x y U $.  $d x y W $.
    $d x y Y $.
    sspm.y $e |- Y = ( BaseSet ` W ) $.
    sspm.m $e |- M = ( -v ` U ) $.
    sspm.l $e |- L = ( -v ` W ) $.
    sspm.h $e |- H = ( SubSp ` U ) $.
    $( Vector addition on a subspace in terms of vector addition on the parent
       space.  (Contributed by NM, 28-Jan-2008.)
       (New usage is discouraged.) $)
    sspmval $p |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. Y /\ B e. Y ) ) ->
                    ( A L B ) = ( A M B ) ) $=
      ( cnv wcel wa cns cfv co wceq eqid c1 cpv wi sspnv cc neg1cn nvscl mp3an2
      cneg ex syl anim2d imp sspgval syldan sspsval mpanr1 adantrl oveq2d eqtrd
      nvmval 3expb sylan cba sspba sseld anim12d adantlr 3eqtr4d ) CMNZGDNZOZAH
      NZBHNZOZOZAUAUIZBGPQZRZGUBQZRZAVQBCPQZRZCUBQZRZABERZABFRZVPWAAVSWDRZWEVLV
      OVMVSHNZOZWAWHSVLVOWJVLVNWIVMVLGMNZVNWIUCCDGLUDZWKVNWIWKVQUENZVNWIUFVQBVR
      GHIVRTZUGUHUJUKULUMAVSCVTWDDGHIWDTZVTTZLUNUOVPVSWCAWDVLVNVSWCSZVMVLWMVNWQ
      UFVQBVRWBCDGHIWBTZWNLUPUQURUSUTVLWKVOWFWASZWLWKVMVNWSABVRGVTEHIWPWNKVAVBV
      CVLVOACVDQZNZBWTNZOZWGWESZVLVOXCVLVMXAVNXBVLHWTACDGWTHWTTZILVEZVFVLHWTBXF
      VFVGUMVJXCXDVKVJXAXBXDABWBCWDFWTXEWOWRJVAVBVHUOVI $.

    $( Vector subtraction on a subspace is a restriction of vector subtraction
       on the parent space.  (Contributed by NM, 28-Jan-2008.)
       (New usage is discouraged.) $)
    sspm $p |- ( ( U e. NrmCVec /\ W e. H ) -> L = ( M |` ( Y X. Y ) ) ) $=
      ( vx vy cba cfv cv sspmval nvmf eqid sspmlem ) KLFAMNZACDBEFGJKOLOABCDEFG
      HIJPECFGIQADTTRHQS $.
  $}

  ${
    sspz.z $e |- Z = ( 0vec ` U ) $.
    sspz.q $e |- Q = ( 0vec ` W ) $.
    sspz.h $e |- H = ( SubSp ` U ) $.
    $( The zero vector of a subspace is the same as the parent's.  (Contributed
       by NM, 28-Jan-2008.)  (New usage is discouraged.) $)
    sspz $p |- ( ( U e. NrmCVec /\ W e. H ) -> Q = Z ) $=
      ( cnv wcel wa cnsb cfv co cba wceq sspnv eqid syl nvmid nvzcl jca sspmval
      mpdan syl2anc2 sspba sseldd syldan 3eqtr3d ) BIJZDCJZKZAADLMZNZAABLMZNZAE
      ULADOMZJZURKZUNUPPULDIJZUSBCDHQZUTURURDUQAUQRZGUAZVCUBSAABCUMUODUQVBUORZU
      MRZHUCUDULUTURUNAPVAVCADUMUQAVBVEGTUEUJUKABOMZJUPEPULUQVFABCDVFUQVFRZVBHU
      FULUTURVAVCSUGABUOVFEVGVDFTUHUI $.
  $}

  ${
    $d x H $.  $d x M $.  $d x N $.  $d x U $.  $d x W $.  $d x Y $.
    sspn.y $e |- Y = ( BaseSet ` W ) $.
    sspn.n $e |- N = ( normCV ` U ) $.
    sspn.m $e |- M = ( normCV ` W ) $.
    sspn.h $e |- H = ( SubSp ` U ) $.
    $( The norm on a subspace is a restriction of the norm on the parent space.
       (Contributed by NM, 28-Jan-2008.)  (New usage is discouraged.) $)
    sspn $p |- ( ( U e. NrmCVec /\ W e. H ) -> M = ( N |` Y ) ) $=
      ( vx cnv wcel wa cr syl cfv wfn wss eqid cres wf sspnv nvf ffnd cba sspba
      adantr fnssres syl2anc cv wfun cdm ffund funresd ad2antrr fnresdm cpv cns
      wceq w3a isssp simplbda simp3d ssres eqsstrrd fdmd eleq2d biimpar funssfv
      sylan syl3anc eqcomd eqfnfvd ) ALMZEBMZNZKFCDFUAZVQFOCVQELMZFOCUBABEJUCZE
      CFGIUDZPUEZVQDAUFQZRZFWCSVRFRVOWDVPVOWCODADWCWCTZHUDZUEUHABEWCFWEGJUGWCFD
      UIUJVQKUKZFMZNZWGVRQZWGCQZWIVRULZCVRSZWGCUMZMZWJWKUTVOWLVPWHVOFDVOWCODWFU
      NUOUPVQWMWHVQCCFUAZVRVQCFRWPCUTWBFCUQPVQCDSZWPVRSVQEURQZAURQZSZEUSQZAUSQZ
      SZWQVOVPVSWTXCWQVAXAXBAWRWSBCDEWSTWRTXBTXATHIJVBVCVDCDFVEPVFUHVQVSWHWOVTV
      SWOWHVSWNFWGVSFOCWAVGVHVIVKWGVRCVJVLVMVN $.

    $( The norm on a subspace in terms of the norm on the parent space.
       (Contributed by NM, 28-Jan-2008.)  (New usage is discouraged.) $)
    sspnval $p |- ( ( U e. NrmCVec /\ W e. H /\ A e. Y ) ->
                    ( M ` A ) = ( N ` A ) ) $=
      ( cnv wcel cfv wceq wa cres sspn fveq1d fvres sylan9eq 3impa ) BLMZFCMZAG
      MZADNZAENZOUCUDPZUEUFAEGQZNUGUHADUIBCDEFGHIJKRSAGETUAUB $.
  $}

  ${
    sspims.y $e |- Y = ( BaseSet ` W ) $.
    sspims.d $e |- D = ( IndMet ` U ) $.
    sspims.c $e |- C = ( IndMet ` W ) $.
    sspims.h $e |- H = ( SubSp ` U ) $.
    $d x y C $.  $d x y D $.  $d x y H $.  $d x y U $.  $d x y W $.
    $d x y Y $.
    $( The induced metric on a subspace in terms of the induced metric on the
       parent space.  (Contributed by NM, 1-Feb-2008.)
       (New usage is discouraged.) $)
    sspimsval $p |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. Y /\ B e. Y ) ) ->
                    ( A C B ) = ( A D B ) ) $=
      ( cnv wcel wa cfv co wceq eqid 3expb cnsb cnmcv sspnv nvmcl sylan sspnval
      3expa syldan sspmval fveq2d eqtrd imsdval cba sspba sseld anim12d adantlr
      imp 3eqtr4d ) EMNZGFNZOZAHNZBHNZOZOZABGUAPZQZGUBPZPZABEUAPZQZEUBPZPZABCQZ
      ABDQZVFVJVHVMPZVNVBVEVHHNZVJVQRZVBGMNZVEVREFGLUCZVTVCVDVRABGVGHIVGSZUDTUE
      UTVAVRVSVHEFVIVMGHIVMSZVISZLUFUGUHVFVHVLVMABEFVGVKGHIVKSZWBLUIUJUKVBVTVEV
      OVJRZWAVTVCVDWFABCGVGVIHIWBWDKULTUEVBVEAEUMPZNZBWGNZOZVPVNRZVBVEWJVBVCWHV
      DWIVBHWGAEFGWGHWGSZILUNZUOVBHWGBWMUOUPURUTWJWKVAUTWHWIWKABDEVKVMWGWLWEWCJ
      ULTUQUHUS $.

    $( The induced metric on a subspace is a restriction of the induced metric
       on the parent space.  (Contributed by NM, 1-Feb-2008.)
       (New usage is discouraged.) $)
    sspims $p |- ( ( U e. NrmCVec /\ W e. H ) -> C = ( D |` ( Y X. Y ) ) ) $=
      ( vx vy cr cv sspimsval imsdf cba cfv eqid sspmlem ) KLMMCABDEFGJKNLNABCD
      EFGHIJOAEFGIPBCCQRZUASHPT $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Operators on complex vector spaces
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definitions and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c LnOp $.
  $c normOpOLD $.
  $c BLnOp $.
  $c 0op $.

  $( Extend class notation with the class of linear operators on normed complex
     vector spaces. $)
  clno $a class LnOp $.

  $( Extend class notation with the class of operator norms on normed complex
     vector spaces. $)
  cnmoo $a class normOpOLD $.

  $( Extend class notation with the class of bounded linear operators on normed
     complex vector spaces. $)
  cblo $a class BLnOp $.

  $( Extend class notation with the class of zero operators on normed complex
     vector spaces. $)
  c0o $a class 0op $.

  ${
    $d t u w x y z $.
    $( Define the class of linear operators between two normed complex vector
       spaces.  In the literature, an operator may be a partial function, i.e.,
       the domain of an operator is not necessarily the entire vector space.
       However, since the domain of a linear operator is a vector subspace, we
       define it with a complete function for convenience and will use subset
       relations to specify the partial function case.  (Contributed by NM,
       6-Nov-2007.)  (New usage is discouraged.) $)
    df-lno $a |- LnOp = ( u e. NrmCVec , w e. NrmCVec |->
    { t e. ( ( BaseSet ` w ) ^m ( BaseSet ` u ) ) |
       A. x e. CC A. y e. ( BaseSet ` u ) A. z e. ( BaseSet ` u )
      ( t ` ( ( x ( .sOLD ` u ) y ) ( +v ` u ) z ) ) =
         ( ( x ( .sOLD ` w ) ( t ` y ) ) ( +v ` w ) ( t ` z ) ) } ) $.

    $( Define the norm of an operator between two normed complex vector spaces.
       This definition produces an operator norm function for each pair of
       vector spaces ` <. u , w >. ` .  Based on definition of linear operator
       norm in [AkhiezerGlazman] p. 39, although we define it for all operators
       for convenience.  It isn't necessarily meaningful for nonlinear
       operators, since it doesn't take into account operator values at vectors
       with norm greater than 1.  See Equation 2 of [Kreyszig] p. 92 for a
       definition that does (although it ignores the value at the zero vector).
       However, operator norms are rarely if ever used for nonlinear operators.
       (Contributed by NM, 6-Nov-2007.)  (New usage is discouraged.) $)
    df-nmoo $a |- normOpOLD = ( u e. NrmCVec , w e. NrmCVec |->
                ( t e. ( ( BaseSet ` w ) ^m ( BaseSet ` u ) ) |->
        sup ( { x | E. z e. ( BaseSet ` u ) ( ( ( normCV ` u ) ` z ) <_ 1 /\
            x = ( ( normCV ` w ) ` ( t ` z ) ) ) } , RR* , < ) ) ) $.

    $( Define the class of bounded linear operators between two normed complex
       vector spaces.  (Contributed by NM, 6-Nov-2007.)
       (New usage is discouraged.) $)
    df-blo $a |- BLnOp = ( u e. NrmCVec , w e. NrmCVec |->
      { t e. ( u LnOp w ) | ( ( u normOpOLD w ) ` t ) < +oo } ) $.

    $( Define the zero operator between two normed complex vector spaces.
       (Contributed by NM, 28-Nov-2007.)  (New usage is discouraged.) $)
    df-0o $a |- 0op = ( u e. NrmCVec , w e. NrmCVec |->
                        ( ( BaseSet ` u ) X. { ( 0vec ` w ) } ) ) $.
  $}

  $c adj $.
  $( Adjoint of an operator. $)
  caj $a class adj $.

  $c HmOp $.
  $( Set of Hermitional (self-adjoint) operators. $)
  chmo $a class HmOp $.

  ${
    $d s t u w x y $.
    $( Define the adjoint of an operator (if it exists).  The domain of
       ` U adj W ` is the set of all operators from ` U ` to ` W ` that have an
       adjoint.  Definition 3.9-1 of [Kreyszig] p. 196, although we don't
       require that ` U ` and ` W ` be Hilbert spaces nor that the operators be
       linear.  Although we define it for any normed vector space for
       convenience, the definition is meaningful only for inner product spaces.
       (Contributed by NM, 25-Jan-2008.)  (New usage is discouraged.) $)
    df-aj $a |- adj = ( u e. NrmCVec , w e. NrmCVec |->
        { <. t , s >. | ( t : ( BaseSet ` u ) --> ( BaseSet ` w ) /\
                          s : ( BaseSet ` w ) --> ( BaseSet ` u ) /\
        A. x e. ( BaseSet ` u ) A. y e. ( BaseSet ` w )
          ( ( t ` x ) ( .iOLD ` w ) y ) = ( x ( .iOLD ` u ) ( s ` y ) ) ) } )
        $.

    $( Define the set of Hermitian (self-adjoint) operators on a normed complex
       vector space (normally a Hilbert space).  Although we define it for any
       normed vector space for convenience, the definition is meaningful only
       for inner product spaces.  (Contributed by NM, 26-Jan-2008.)
       (New usage is discouraged.) $)
    df-hmo $a |- HmOp = ( u e. NrmCVec |->
                { t e. dom ( u adj u ) | ( ( u adj u ) ` t ) = t } ) $.

$(
    @( Alternate definition of the set of Hermitian (self-adjoint) operators on
       a normed complex vector space (normally a Hilbert space). @)
    dfhm2 @p |- HmOp = { <. u , o >. | ( u e. NrmCVec /\ o = { t | ( t :
  ( BaseSet ` u ) --> ( BaseSet ` u ) /\ A. x e. ( BaseSet ` u ) A. y e.
  ( BaseSet ` u ) ( x ( .iOLD ` u ) ( t ` y ) ) = ( ( t ` x ) ( .iOLD ` u ) y )
       ) } ) } @=
      (  ) ? @.
      @( [ ?] @) @( [8-Feb-2008] @)
$)
  $}

  ${
    $d t u w x y z U $.  $d t u w x y z W $.  $d t u w y z X $.  $d t u w Y $.
    $d t u w G $.  $d t u w R $.  $d t u w H $.  $d t u w S $.
    $d t u w x y z T $.
    lnoval.1 $e |- X = ( BaseSet ` U ) $.
    lnoval.2 $e |- Y = ( BaseSet ` W ) $.
    lnoval.3 $e |- G = ( +v ` U ) $.
    lnoval.4 $e |- H = ( +v ` W ) $.
    lnoval.5 $e |- R = ( .sOLD ` U ) $.
    lnoval.6 $e |- S = ( .sOLD ` W ) $.
    lnoval.7 $e |- L = ( U LnOp W ) $.
    $( The set of linear operators between two normed complex vector spaces.
       (Contributed by NM, 6-Nov-2007.)  (Revised by Mario Carneiro,
       16-Nov-2013.)  (New usage is discouraged.) $)
    lnoval $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> L =
      { t e. ( Y ^m X ) | A. x e. CC A. y e. X A. z e. X
        ( t ` ( ( x R y ) G z ) ) = ( ( x S ( t ` y ) ) H ( t ` z ) ) } ) $=
      ( vu vw cnv wcel wa clno co cv cfv wceq wral cc cmap crab cns cpv eqtr4di
      cba fveq2 oveq2d oveqd eqidd oveq123d fveqeq2d raleqbidv rabeqbidv oveq1d
      ralbidv eqeq2d 2ralbidv df-lno ovex rabex ovmpo eqtrid ) GUCUDKUCUDUEJGKU
      FUGAUHZBUHZEUGZCUHZHUGZDUHZUIZVPVQWAUIZFUGZVSWAUIZIUGZUJZCLUKBLUKZAULUKZD
      MLUMUGZUNZTUAUBGKUCUCVPVQUAUHZUOUIZUGZVSWLUPUIZUGZWAUIVPWCUBUHZUOUIZUGZWE
      WQUPUIZUGZUJZCWLURUIZUKZBXCUKZAULUKZDWQURUIZXCUMUGZUNWKUFWBXAUJZCLUKZBLUK
      ZAULUKZDXGLUMUGZUNWLGUJZXFXLDXHXMXNXCLXGUMXNXCGURUILWLGURUSNUQZUTXNXEXKAU
      LXNXDXJBXCLXOXNXBXICXCLXOXNWPVTXAWAXNWNVRVSVSWOHXNWOGUPUIHWLGUPUSPUQXNWME
      VPVQXNWMGUOUIEWLGUOUSRUQVAXNVSVBVCVDVEVEVHVFWQKUJZXLWIDXMWJXPXGMLUMXPXGKU
      RUIMWQKURUSOUQVGXPXKWHAULXPXIWGBCLLXPXAWFWBXPWSWDWEWEWTIXPWTKUPUIIWQKUPUS
      QUQXPWRFVPWCXPWRKUOUIFWQKUOUSSUQVAXPWEVBVCVIVJVHVFABCUBUADVKWIDWJMLUMVLVM
      VNVO $.

    $( The predicate "is a linear operator."  (Contributed by NM, 4-Dec-2007.)
       (Revised by Mario Carneiro, 16-Nov-2013.)
       (New usage is discouraged.) $)
    islno $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> ( T e. L <->
      ( T : X --> Y /\ A. x e. CC A. y e. X A. z e. X
      ( T ` ( ( x R y ) G z ) ) = ( ( x S ( T ` y ) ) H ( T ` z ) ) ) ) ) $=
      ( vw cnv wcel wa cv co cfv wceq wral cc cmap crab wf lnoval eleq2d oveq2d
      fveq1 oveq12d eqeq12d 2ralbidv ralbidv elrab cba fvexi elmap anbi1i bitri
      bitrdi ) GUBUCKUBUCUDZFJUCFAUEZBUEZDUFCUEZHUFZUAUEZUGZVJVKVNUGZEUFZVLVNUG
      ZIUFZUHZCLUIBLUIZAUJUIZUAMLUKUFZULZUCZLMFUMZVMFUGZVJVKFUGZEUFZVLFUGZIUFZU
      HZCLUIBLUIZAUJUIZUDZVIJWDFABCUADEGHIJKLMNOPQRSTUNUOWEFWCUCZWNUDWOWBWNUAFW
      CVNFUHZWAWMAUJWQVTWLBCLLWQVOWGVSWKVMVNFUQWQVQWIVRWJIWQVPWHVJEVKVNFUQUPVLV
      NFUQURUSUTVAVBWPWFWNMLFMKVCOVDLGVCNVDVEVFVGVH $.

    $d t u w A $.  $d t w B $.  $d t C $.
    $( Basic linearity property of a linear operator.  (Contributed by NM,
       4-Dec-2007.)  (Revised by Mario Carneiro, 16-Nov-2013.)
       (New usage is discouraged.) $)
    lnolin $p |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) /\
       ( A e. CC /\ B e. X /\ C e. X ) ) ->
      ( T ` ( ( A R B ) G C ) ) = ( ( A S ( T ` B ) ) H ( T ` C ) ) ) $=
      ( vu vw vt cnv wcel w3a cv co cfv wceq wral cc wf wa islno biimp3a simprd
      oveq1 fvoveq1d oveq1d eqeq12d oveq2 fveq2 oveq2d fveq2d rspc3v mpan9 ) GU
      DUEZKUDUEZFJUEZUFZUAUGZUBUGZDUHZUCUGZHUHFUIZVLVMFUIZEUHZVOFUIZIUHZUJZUCLU
      KUBLUKUAULUKZAULUEBLUECLUEUFABDUHZCHUHZFUIZABFUIZEUHZCFUIZIUHZUJZVKLMFUMZ
      WBVHVIVJWKWBUNUAUBUCDEFGHIJKLMNOPQRSTUOUPUQWAWJAVMDUHZVOHUHFUIZAVQEUHZVSI
      UHZUJWCVOHUHZFUIZWGVSIUHZUJUAUBUCABCULLLVLAUJZVPWMVTWOWSVNWLVOFHVLAVMDURU
      SWSVRWNVSIVLAVQEURUTVAVMBUJZWMWQWOWRWTWLWCVOFHVMBADVBUSWTWNWGVSIWTVQWFAEV
      MBFVCVDUTVAVOCUJZWQWEWRWIXAWPWDFVOCWCHVBVEXAVSWHWGIVOCFVCVDVAVFVG $.
  $}

  ${
    $d x y z T $.  $d x y z U $.  $d x y z W $.  $d x y z X $.
    lnof.1 $e |- X = ( BaseSet ` U ) $.
    lnof.2 $e |- Y = ( BaseSet ` W ) $.
    lnof.7 $e |- L = ( U LnOp W ) $.
    $( A linear operator is a mapping.  (Contributed by NM, 4-Dec-2007.)
       (Revised by Mario Carneiro, 18-Nov-2013.)
       (New usage is discouraged.) $)
    lnof $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) -> T : X --> Y ) $=
      ( vx vy vz cnv wcel cv cns cfv co wral eqid wf wa cpv wceq islno simprbda
      cc 3impa ) BMNZDMNZACNZEFAUAZUIUJUBUKULJOZKOZBPQZRLOZBUCQZRAQUMUNAQDPQZRU
      PAQDUCQZRUDLESKESJUGSJKLUOURABUQUSCDEFGHUQTUSTUOTURTIUEUFUH $.
  $}

  ${
    lno0.1 $e |- X = ( BaseSet ` U ) $.
    lno0.2 $e |- Y = ( BaseSet ` W ) $.
    lno0.5 $e |- Q = ( 0vec ` U ) $.
    lno0.z $e |- Z = ( 0vec ` W ) $.
    lno0.7 $e |- L = ( U LnOp W ) $.
    $( The value of a linear operator at zero is zero.  (Contributed by NM,
       4-Dec-2007.)  (Revised by Mario Carneiro, 18-Nov-2013.)
       (New usage is discouraged.) $)
    lno0 $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L )
         -> ( T ` Q ) = Z ) $=
      ( cnv wcel w3a cfv co wceq eqid c1 cneg cns cpv neg1cn a1i nvzcl 3ad2ant1
      cc 3jca lnolin mpdan nvlinv fveq2d simp2 lnof ffvelcdmd syl2anc 3eqtr3d )
      CNOZENOZBDOZPZUAUBZACUCQZRACUDQZRZBQZVDABQZEUCQZRVIEUDQZRZVIHVCVDUIOZAFOZ
      VNPVHVLSVCVMVNVNVMVCUEUFUTVAVNVBCFAIKUGZUHZVPUJVDAAVEVJBCVFVKDEFGIJVFTZVK
      TZVETZVJTZMUKULUTVAVHVISVBUTVGABUTVNVGASVOAVECVFFAIVQVSKUMULUNUHVCVAVIGOV
      LHSUTVAVBUOVCFGABBCDEFGIJMUPVPUQVIVJEVKGHJVRVTLUMURUS $.
  $}

  ${
    $d x y z S $.  $d x y z T $.  $d x y z U $.  $d x y z X $.
    lnocoi.l $e |- L = ( U LnOp W ) $.
    lnocoi.m $e |- M = ( W LnOp X ) $.
    lnocoi.n $e |- N = ( U LnOp X ) $.
    lnocoi.u $e |- U e. NrmCVec $.
    lnocoi.w $e |- W e. NrmCVec $.
    lnocoi.x $e |- X e. NrmCVec $.
    lnocoi.s $e |- S e. L $.
    lnocoi.t $e |- T e. M $.
    $( The composition of two linear operators is linear.  (Contributed by NM,
       12-Jan-2008.)  (Revised by Mario Carneiro, 19-Nov-2013.)
       (New usage is discouraged.) $)
    lnocoi $p |- ( T o. S ) e. N $=
      ( wcel cfv co eqid vx vy vz ccom cba wf cv cns cpv wceq wral cc cnv mp3an
      lnof fco mp2an w3a nvscl mp3an1 nvgcl stoic3 sylancr id ffvelcdmi 3pm3.2i
      fvco3 lnolin mpan syl3an fveq2d simp2 oveq2d simp3 oveq12d 3eqtr4rd rgen3
      eqtr4d wa wb islno mpbir2an ) BAUDZFQZCUERZHUERZWCUFZUAUGZUBUGZCUHRZSZUCU
      GZCUIRZSZWCRZWHWIWCRZHUHRZSZWLWCRZHUIRZSZUJZUCWEUKUBWEUKUAULUKZGUERZWFBUF
      ZWEXDAUFZWGGUMQZHUMQZBEQZXEMNPBGEHXDWFXDTZWFTZJUOUNCUMQZXGADQZXFLMOACDGWE
      XDWETZXJIUOUNZWEXDWFBAUPUQXBUAUBUCULWEWEWHULQZWIWEQZWLWEQZURZWOWNARZBRZXA
      XSXFWNWEQZWOYAUJXOXPXQWKWEQZXRYBXLXPXQYCLWHWIWJCWEXNWJTZUSUTXLYCXRYBLWKWL
      CWMWEXNWMTZVAUTVBWEXDWNBAVGVCXSWHWIARZGUHRZSWLARZGUIRZSZBRZWHYFBRZWQSZYHB
      RZWTSZYAXAXPXPXQYFXDQZXRYHXDQZYKYOUJZXPVDWEXDWIAXOVEWEXDWLAXOVEXGXHXIURXP
      YPYQURYRXGXHXIMNPVFWHYFYHYGWQBGYIWTEHXDWFXJXKYITZWTTZYGTZWQTZJVHVIVJXSXTY
      JBXLXGXMURXSXTYJUJXLXGXMLMOVFWHWIWLWJYGACWMYIDGWEXDXNXJYEYSYDUUAIVHVIVKXS
      WRYMWSYNWTXSWPYLWHWQXSXFXQWPYLUJXOXPXQXRVLWEXDWIBAVGVCVMXSXFXRWSYNUJXOXPX
      QXRVNWEXDWLBAVGVCVOVPVRVQXLXHWDWGXCVSVTLNUAUBUCWJWQWCCWMWTFHWEWFXNXKYEYTY
      DUUBKWAUQWB $.
  $}

  ${
    lnoadd.1 $e |- X = ( BaseSet ` U ) $.
    lnoadd.5 $e |- G = ( +v ` U ) $.
    lnoadd.6 $e |- H = ( +v ` W ) $.
    lnoadd.7 $e |- L = ( U LnOp W ) $.
    $( Addition property of a linear operator.  (Contributed by NM,
       7-Dec-2007.)  (Revised by Mario Carneiro, 19-Nov-2013.)
       (New usage is discouraged.) $)
    lnoadd $p |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) /\
  ( A e. X /\ B e. X ) ) -> ( T ` ( A G B ) ) = ( ( T ` A ) H ( T ` B ) ) ) $=
      ( cnv wcel c1 cfv co wceq eqid w3a wa cns ax-1cn cba lnolin mp3anr1 simp1
      cc simpl nvsid syl2an fvoveq1d simpl2 wf ffvelcdm syl2anc oveq1d 3eqtr3d
      lnof ) DNOZHNOZCGOZUAZAIOZBIOZUBZUBZPADUCQZRZBERCQZPACQZHUCQZRZBCQZFRZABE
      RCQVLVOFRVDPUIOVEVFVKVPSUDPABVIVMCDEFGHIHUEQZJVQTZKLVITZVMTZMUFUGVHVJABCE
      VDVAVEVJASVGVAVBVCUHVEVFUJZAVIDIJVSUKULUMVHVNVLVOFVHVBVLVQOZVNVLSVAVBVCVG
      UNVDIVQCUOVEWBVGCDGHIVQJVRMUTWAIVQACUPULVLVMHVQVRVTUKUQURUS $.
  $}

  ${
    lnosub.1 $e |- X = ( BaseSet ` U ) $.
    lnosub.5 $e |- M = ( -v ` U ) $.
    lnosub.6 $e |- N = ( -v ` W ) $.
    lnosub.7 $e |- L = ( U LnOp W ) $.
    $( Subtraction property of a linear operator.  (Contributed by NM,
       7-Dec-2007.)  (Revised by Mario Carneiro, 19-Nov-2013.)
       (New usage is discouraged.) $)
    lnosub $p |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) /\
  ( A e. X /\ B e. X ) ) -> ( T ` ( A M B ) ) = ( ( T ` A ) N ( T ` B ) ) ) $=
      ( cnv wcel wa cfv co wceq eqid w3a cneg cns cpv neg1cn cba lnolin mp3anr1
      c1 cc ancom2s nvmval2 3expb 3ad2antl1 fveq2d simpl2 simpl ffvelcdm syl2an
      wf lnof simpr syl3anc 3eqtr4d ) DNOZHNOZCEOZUAZAIOZBIOZPZPZUIUBZBDUCQZRAD
      UDQZRZCQZVMBCQZHUCQZRACQZHUDQZRZABFRZCQVTVRGRZVHVJVIVQWBSZVHVMUJOVJVIWEUE
      VMBAVNVSCDVOWAEHIHUFQZJWFTZVOTZWATZVNTZVSTZMUGUHUKVLWCVPCVEVFVKWCVPSZVGVE
      VIVJWLABVNDVOFIJWHWJKULUMUNUOVLVFVTWFOZVRWFOZWDWBSVEVFVGVKUPVHIWFCUTZVIWM
      VKCDEHIWFJWGMVAZVIVJUQIWFACURUSVHWOVJWNVKWPVIVJVBIWFBCURUSVTVRVSHWAGWFWGW
      IWKLULVCVD $.
  $}

  ${
    lnomul.1 $e |- X = ( BaseSet ` U ) $.
    lnomul.5 $e |- R = ( .sOLD ` U ) $.
    lnomul.6 $e |- S = ( .sOLD ` W ) $.
    lnomul.7 $e |- L = ( U LnOp W ) $.
    $( Scalar multiplication property of a linear operator.  (Contributed by
       NM, 5-Dec-2007.)  (Revised by Mario Carneiro, 19-Nov-2013.)
       (New usage is discouraged.) $)
    lnomul $p |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) /\
       ( A e. CC /\ B e. X ) ) -> ( T ` ( A R B ) ) = ( A S ( T ` B ) ) ) $=
      ( cnv wcel wa co cfv wceq eqid w3a cc cn0v cpv simpl simprl simprr simpl1
      nvzcl syl lnolin syl13anc nvscl syl3anc nv0rid syl2anc fveq2d lno0 oveq2d
      cba adantr simpl2 wf lnof ffvelcdmd eqtrd 3eqtr3d ) FNOZHNOZEGOZUAZAUBOZB
      IOZPZPZABCQZFUCRZFUDRZQZERZABERZDQZVQERZHUDRZQZVPERWBVOVKVLVMVQIOZVTWESVK
      VNUEVKVLVMUFZVKVLVMUGZVOVHWFVHVIVJVNUHZFIVQJVQTZUIUJABVQCDEFVRWDGHIHUTRZJ
      WKTZVRTZWDTZKLMUKULVOVSVPEVOVHVPIOZVSVPSWIVOVHVLVMWOWIWGWHABCFIJKUMUNVPFV
      RIVQJWMWJUOUPUQVOWEWBHUCRZWDQZWBVKWEWQSVNVKWCWPWBWDVQEFGHIWKWPJWLWJWPTZMU
      RUSVAVOVIWBWKOZWQWBSVHVIVJVNVBZVOVIVLWAWKOWSWTWGVOIWKBEVKIWKEVCVNEFGHIWKJ
      WLMVDVAWHVEAWADHWKWLLUMUNWBHWDWKWPWLWNWRUOUPVFVG $.
  $}

  ${
    nvo00.1 $e |- X = ( BaseSet ` U ) $.
    $( Two ways to express a zero operator.  (Contributed by NM, 27-Nov-2007.)
       (New usage is discouraged.) $)
    nvo00 $p |- ( ( U e. NrmCVec /\ T : X --> Y ) ->
                  ( T = ( X X. { Z } ) <-> ran T = { Z } ) ) $=
      ( wf wfn c0 wne csn cxp wceq crn wb cnv wcel ffn cn0v cfv eqid nvzcl ne0d
      fconst5 syl2anr ) CDAGACHCIJACEKZLMANUFMOBPQZCDARUGCBSTZBCUHFUHUAUBUCCEAU
      DUE $.
  $}

  ${
    $d t u w x z U $.  $d t u w x z W $.  $d t u w z X $.  $d t u w x Y $.
    $d t u w L $.  $d t u w M $.  $d t x z T $.
    nmoofval.1 $e |- X = ( BaseSet ` U ) $.
    nmoofval.2 $e |- Y = ( BaseSet ` W ) $.
    nmoofval.3 $e |- L = ( normCV ` U ) $.
    nmoofval.4 $e |- M = ( normCV ` W ) $.
    nmoofval.6 $e |- N = ( U normOpOLD W ) $.
    $( The operator norm function.  (Contributed by NM, 6-Nov-2007.)  (Revised
       by Mario Carneiro, 16-Nov-2013.)  (New usage is discouraged.) $)
    nmoofval $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> N =
       ( t e. ( Y ^m X ) |-> sup ( { x | E. z e. X
         ( ( L ` z ) <_ 1 /\ x = ( M ` ( t ` z ) ) ) } , RR* , < ) ) ) $=
      ( cmap cv cfv cba cnmcv vu vw cnv wcel wa cnmoo cle wbr wceq wrex cab cxr
      co c1 clt csup fveq2 eqtr4di oveq2d fveq1d breq1d anbi1d rexeqbidv abbidv
      supeq1d mpteq12dv oveq1d eqeq2d anbi2d rexbidv df-nmoo mptex ovmpo eqtrid
      cmpt ovex ) DUCUDHUCUDUEGDHUFUMCJIPUMZBQZERZUNUGUHZAQZVRCQRZFRZUIZUEZBIUJ
      ZAUKZULUOUPZVOZOUAUBDHUCUCCUBQZSRZUAQZSRZPUMZVRWLTRZRZUNUGUHZWAWBWJTRZRZU
      IZUEZBWMUJZAUKZULUOUPZVOWIUFCWKIPUMZVTWTUEZBIUJZAUKZULUOUPZVOWLDUIZCWNXDX
      EXIXJWMIWKPXJWMDSRIWLDSUQKURZUSXJULXCXHUOXJXBXGAXJXAXFBWMIXKXJWQVTWTXJWPV
      SUNUGXJVRWOEXJWODTREWLDTUQMURUTVAVBVCVDVEVFWJHUIZCXEXIVQWHXLWKJIPXLWKHSRJ
      WJHSUQLURVGXLULXHWGUOXLXGWFAXLXFWEBIXLWTWDVTXLWSWCWAXLWBWRFXLWRHTRFWJHTUQ
      NURUTVHVIVJVDVEVFABUBUACVKCVQWHJIPVPVLVMVN $.

    $( The operator norm function.  (Contributed by NM, 27-Nov-2007.)  (Revised
       by Mario Carneiro, 16-Nov-2013.)  (New usage is discouraged.) $)
    nmooval $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) ->
      ( N ` T ) = sup ( { x | E. z e. X
        ( ( L ` z ) <_ 1 /\ x = ( M ` ( T ` z ) ) ) } , RR* , < ) ) $=
      ( vt cfv wceq cxr clt cnv wcel wf cv c1 cle wbr wa wrex cab csup cmap cba
      co fvexi elmap nmoofval fveq1d fveq1 fveq2d eqeq2d anbi2d rexbidv supeq1d
      cmpt abbidv eqid xrltso supex fvmpt sylan9eq sylan2br 3impa ) DUAUBZHUAUB
      ZIJCUCZCGQZBUDZEQUEUFUGZAUDZVRCQZFQZRZUHZBIUIZAUJZSTUKZRZVPVNVOUHZCJIULUN
      ZUBZWHJICJHUMLUOIDUMKUOUPWIWKVQCPWJVSVTVRPUDZQZFQZRZUHZBIUIZAUJZSTUKZVEZQ
      WGWICGWTABPDEFGHIJKLMNOUQURPCWSWGWJWTWLCRZSWRWFTXAWQWEAXAWPWDBIXAWOWCVSXA
      WNWBVTXAWMWAFVRWLCUSUTVAVBVCVFVDWTVGSWFTVHVIVJVKVLVM $.
  $}

  ${
    $d x z T $.  $d x z W $.  $d x z X $.  $d x z Y $.
    nmosetre.2 $e |- Y = ( BaseSet ` W ) $.
    nmosetre.4 $e |- N = ( normCV ` W ) $.
    $( The set in the supremum of the operator norm definition ~ df-nmoo is a
       set of reals.  (Contributed by NM, 13-Nov-2007.)
       (New usage is discouraged.) $)
    nmosetre $p |- ( ( W e. NrmCVec /\ T : X --> Y ) -> {
     x | E. z e. X ( ( M ` z ) <_ 1 /\ x = ( N ` ( T ` z ) ) ) } C_ RR ) $=
      ( cnv wcel wf wa cv cfv c1 cle wbr cr wceq wrex nvcl sylan2 anassrs eleq1
      ffvelcdm imbitrrid impcom adantrl rexlimdva2 abssdv ) FKLZGHCMZNZBOZDPQRS
      ZAOZUPCPZEPZUAZNZBGUBATUOVBURTLZBGUOUPGLZNZVAVCUQVAVEVCVEVCVAUTTLZUMUNVDV
      FUNVDNUMUSHLVFGHUPCUGUSFEHIJUCUDUEURUTTUFUHUIUJUKUL $.
  $}

  ${
    $d x y M $.  $d x y N $.  $d x y T $.  $d x y X $.  $d x y Z $.
    nmosetn0.1 $e |- X = ( BaseSet ` U ) $.
    nmosetn0.5 $e |- Z = ( 0vec ` U ) $.
    nmosetn0.4 $e |- M = ( normCV ` U ) $.
    $( The set in the supremum of the operator norm definition ~ df-nmoo is
       nonempty.  (Contributed by NM, 8-Dec-2007.)
       (New usage is discouraged.) $)
    nmosetn0 $p |- ( U e. NrmCVec -> ( N ` ( T ` Z ) ) e. { x | E. y e. X (
       ( M ` y ) <_ 1 /\ x = ( N ` ( T ` y ) ) ) } ) $=
      ( wcel cv cfv c1 cle wbr wceq wa wrex cnv cab cc0 nvz0 0le1 eqbrtrdi eqid
      nvzcl jctir fveq2 breq1d 2fveq3 eqeq2d anbi12d rspcev syl2anc fvex anbi2d
      eqeq1 rexbidv elab sylibr ) DUALZBMZENZOPQZHCNZFNZVDCNFNZRZSZBGTZVHVFAMZV
      IRZSZBGTZAUBLVCHGLHENZOPQZVHVHRZSZVLDGHIJUHVCVRVSVCVQUCOPDEHJKUDUEUFVHUGU
      IVKVTBHGVDHRZVFVRVJVSWAVEVQOPVDHEUJUKWAVIVHVHVDHFCULUMUNUOUPVPVLAVHVGFUQV
      MVHRZVOVKBGWBVNVJVFVMVHVIUSURUTVAVB $.
  $}

  ${
    $d x z T $.  $d x z U $.  $d x z W $.  $d x z X $.  $d x z Y $.
    nmoxr.1 $e |- X = ( BaseSet ` U ) $.
    nmoxr.2 $e |- Y = ( BaseSet ` W ) $.
    nmoxr.3 $e |- N = ( U normOpOLD W ) $.
    $( The norm of an operator is an extended real.  (Contributed by NM,
       27-Nov-2007.)  (New usage is discouraged.) $)
    nmoxr $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) ->
              ( N ` T ) e. RR* ) $=
      ( vz vx cnv wcel wf cfv cv cnmcv wa cxr eqid w3a c1 cle wbr wceq wrex cab
      clt csup nmooval wss nmosetre ressxr sstrdi supxrcl syl 3adant1 eqeltrd
      cr ) BLMZDLMZEFANZUAACOJPZBQOZOUBUCUDKPVCAODQOZOUERJEUFKUGZSUHUIZSKJABVDV
      ECDEFGHVDTVETZIUJVAVBVGSMZUTVAVBRZVFSUKVIVJVFUSSKJAVDVEDEFHVHULUMUNVFUOUP
      UQUR $.

    $( The norm of an operator is nonnegative.  (Contributed by NM,
       8-Dec-2007.)  (New usage is discouraged.) $)
    nmooge0 $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) ->
                  0 <_ ( N ` T ) ) $=
      ( vz vx cnv wcel cc0 cfv cnmcv cxr eqid cle wbr wf w3a cn0v 0xr a1i simp2
      cr nvzcl ffvelcdm sylan2 ancoms 3adant2 nvcl syl2anc rexrd nmoxr nvge0 cv
      wceq wrex cab clt csup wss nmosetre ressxr sstrdi nmosetn0 supxrub syl2an
      c1 wa 3impa 3comr nmooval breqtrrd xrletrd ) BLMZDLMZEFAUAZUBZNBUCOZAOZDP
      OZOZACOZNQMWAUDUEWAWEWAVSWCFMZWEUGMVRVSVTUFZVRVTWGVSVTVRWGVRVTWBEMWGBEWBG
      WBRZUHEFWBAUIUJUKULZWCDWDFHWDRZUMUNUOABCDEFGHIUPWAVSWGNWESTWHWJWCDWDFHWKU
      QUNWAWEJURZBPOZOVKSTKURWLAOWDOUSVLJEUTKVAZQVBVCZWFSVSVTVRWEWOSTZVSVTVRWPV
      SVTVLZWNQVDWEWNMWPVRWQWNUGQKJAWMWDDEFHWKVEVFVGKJABWMWDEWBGWIWMRZVHWNWEVIV
      JVMVNKJABWMWDCDEFGHWRWKIVOVPVQ $.

    $( The norm of an operator is either real or plus infinity.  (Contributed
       by NM, 8-Dec-2007.)  (New usage is discouraged.) $)
    nmorepnf $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) ->
                   ( ( N ` T ) e. RR <-> ( N ` T ) =/= +oo ) ) $=
      ( vz vx cnv wcel cv cnmcv cfv cr cpnf wne eqid wf w3a c1 cle wceq wa wrex
      wbr cab cxr clt csup wb wss c0 nmosetre cn0v nmosetn0 ne0d supxrre2 3impb
      syl2anr nmooval eleq1d neeq1d 3bitr4d ) BLMZDLMZEFAUAZUBZJNZBOPZPUCUDUHKN
      VKAPDOPZPUEUFJEUGKUIZUJUKULZQMZVORSZACPZQMVRRSVGVHVIVPVQUMZVHVIUFVNQUNVNU
      OSVSVGKJAVLVMDEFHVMTZUPVGVNBUQPZAPVMPKJABVLVMEWAGWATVLTZURUSVNUTVBVAVJVRV
      OQKJABVLVMCDEFGHWBVTIVCZVDVJVRVORWCVEVF $.

    $( The norm of any operator is real iff it is less than plus infinity.
       (Contributed by NM, 8-Dec-2007.)  (New usage is discouraged.) $)
    nmoreltpnf $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) ->
                   ( ( N ` T ) e. RR <-> ( N ` T ) < +oo ) ) $=
      ( cnv wcel wf w3a cfv cr cpnf wne clt wbr nmorepnf cxr wceq wn wb nltpnft
      nmoxr syl necon2abid bitr4d ) BJKDJKEFALMZACNZOKUKPQUKPRSZABCDEFGHITUJULU
      KPUJUKUAKUKPUBULUCUDABCDEFGHIUFUKUEUGUHUI $.

    $( The norm of an operator is greater than minus infinity.  (Contributed by
       NM, 8-Dec-2007.)  (New usage is discouraged.) $)
    nmogtmnf $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) ->
                  -oo < ( N ` T ) ) $=
      ( cnv wcel wf w3a cfv cr cpnf wceq wn wb wo cmnf clt wbr wne df-ne bitrdi
      nmorepnf xor3 nbior sylbir mnfltxr 3syl ) BJKDJKEFALMZACNZOKZUNPQZRZSZUOU
      PTZUAUNUBUCUMUOUNPUDUQABCDEFGHIUGUNPUEUFURUOUPSRUSUOUPUHUOUPUIUJUNUKUL $.
  $}

  ${
    $d x y A $.  $d x y L $.  $d x y M $.  $d x y T $.  $d x y U $.
    $d x y W $.  $d x y X $.  $d x y Y $.
    nmoolb.1 $e |- X = ( BaseSet ` U ) $.
    nmoolb.2 $e |- Y = ( BaseSet ` W ) $.
    nmoolb.l $e |- L = ( normCV ` U ) $.
    nmoolb.m $e |- M = ( normCV ` W ) $.
    nmoolb.3 $e |- N = ( U normOpOLD W ) $.
    $( A lower bound for an operator norm.  (Contributed by NM, 8-Dec-2007.)
       (New usage is discouraged.) $)
    nmoolb $p |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) /\
         ( A e. X /\ ( L ` A ) <_ 1 ) ) -> ( M ` ( T ` A ) ) <_ ( N ` T ) ) $=
      ( vy vx cfv cle wa wceq cnv wcel wf w3a c1 wbr cv wrex cab cxr clt wss cr
      nmosetre ressxr sstrdi 3adant1 fveq2 breq1d 2fveq3 eqeq2d anbi12d biantru
      csup eqid bitr4di rspcev fvex eqeq1 anbi2d rexbidv sylibr supxrub nmooval
      elab syl2an adantr breqtrrd ) CUAUBZGUAUBZHIBUCZUDZAHUBADQZUERUFZSZSABQZE
      QZOUGZDQZUERUFZPUGZWHBQEQZTZSZOHUHZPUIZUJUKVDZBFQZRWBWPUJULZWGWPUBZWGWQRU
      FWEVTWAWSVSVTWASWPUMUJPOBDEGHIKMUNUOUPUQWEWJWGWLTZSZOHUHZWTXBWDOAHWHATZXB
      WDWGWGTZSWDXDWJWDXAXEXDWIWCUERWHADURUSXDWLWGWGWHAEBUTVAVBXEWDWGVEVCVFVGWO
      XCPWGWFEVHWKWGTZWNXBOHXFWMXAWJWKWGWLVIVJVKVOVLWPWGVMVPWBWRWQTWEPOBCDEFGHI
      JKLMNVNVQVR $.
  $}

  ${
    $d x z A $.  $d f k r x y z L $.  $d x y U $.  $d x y W $.  $d k r x y Y $.
    $d f k r x y z M $.  $d f k r x y z T $.  $d f k r x y z X $.
    $d k r y N $.
    nmoubi.1 $e |- X = ( BaseSet ` U ) $.
    nmoubi.y $e |- Y = ( BaseSet ` W ) $.
    nmoubi.l $e |- L = ( normCV ` U ) $.
    nmoubi.m $e |- M = ( normCV ` W ) $.
    nmoubi.3 $e |- N = ( U normOpOLD W ) $.
    nmoubi.u $e |- U e. NrmCVec $.
    nmoubi.w $e |- W e. NrmCVec $.
    $( An upper bound for an operator norm.  (Contributed by NM, 11-Dec-2007.)
       (New usage is discouraged.) $)
    nmoubi $p |- ( ( T : X --> Y /\ A e. RR* ) -> ( ( N ` T ) <_ A <->
      A. x e. X ( ( L ` x ) <_ 1 -> ( M ` ( T ` x ) ) <_ A ) ) ) $=
      ( vz cle wi vy wf cxr wcel wa cfv wbr cv c1 wceq wrex cab wral clt wb cnv
      csup nmooval mp3an12 breq1d adantr wss cr nmosetre ressxr supxrleub sylan
      mpan sstrdi bitrd eqeq1 anbi2d rexbidv ralab ralcom4 ancomst impexp bitri
      wal albii fvex breq1 imbi2d ceqsalv ralbii r19.23v 3bitr3i bitr4i bitrdi
      ) IJCUBZBUCUDZUEZCGUFZBSUGZRUHZBSUGZRAUHZEUFUISUGZUAUHZWQCUFZFUFZUJZUEZAI
      UKZUAULZUMZWRXABSUGZTZAIUMZWLWNXEUCUNUQZBSUGZXFWJWNXKUOWKWJWMXJBSDUPUDHUP
      UDZWJWMXJUJPQUAACDEFGHIJKLMNOURUSUTVAWJXEUCVBWKXKXFUOWJXEVCUCXLWJXEVCVBQU
      AACEFHIJLNVDVHVEVIRXEBVFVGVJXFWRWOXAUJZUEZAIUKZWPTZRVSZXIXDXOWPRUAWSWOUJZ
      XCXNAIXRXBXMWRWSWOXAVKVLVMVNXNWPTZRVSZAIUMXSAIUMZRVSXIXQXSARIVOXTXHAIXTXM
      WRWPTZTZRVSXHXSYCRXSXMWRUEWPTYCWRXMWPVPXMWRWPVQVRVTYBXHRXAWTFWAXMWPXGWRWO
      XABSWBWCWDVRWEYAXPRXNWPAIWFVTWGWHWI $.

    $( An upper bound for an operator norm.  (Contributed by NM, 12-Dec-2007.)
       (New usage is discouraged.) $)
    nmoub3i $p |- ( ( T : X --> Y /\ A e. RR /\ A. x e. X
  ( M ` ( T ` x ) ) <_ ( A x. ( L ` x ) ) ) -> ( N ` T ) <_ ( abs ` A ) ) $=
      ( wcel cle wbr wf cr cv cfv cmul co wral cabs wa c1 cnv nvcl mpan remulcl
      wi sylan2 adantr recn abscld syl2an ad2antrr cc0 simpl nvge0 adantl leabs
      jca lemul1a syl31anc 1red absge0d 3jca lemul2a sylan wceq mulridd breqtrd
      w3a recnd adantlll ffvelcdm sylancr adantlr adantll ad2antlr letr syl3anc
      letrd mpan2d ex com23 ralimdva imp cxr rexrd nmoubi biimpar syldan 3impa
      wb ) IJCUAZBUBRZAUCZCUDZFUDZBXCEUDZUEUFZSTZAIUGZCGUDBUHUDZSTZXAXBUIZXIXFU
      JSTZXEXJSTZUOZAIUGZXKXLXIXPXLXHXOAIXLXCIRZUIZXMXHXNXRXMXHXNUOXRXMUIXHXGXJ
      STZXNXBXQXMXSXAXBXQUIZXMUIZXGXJXFUEUFZXJXTXGUBRZXMXQXBXFUBRZYCDUKRZXQYDPX
      CDEIKMULUMZBXFUNUPZUQXTYBUBRZXMXBXJUBRZYDYHXQXBBBURZUSZYFXJXFUNUTUQXBYIXQ
      XMYKVAXTXGYBSTZXMXTXBYIYDVBXFSTZUIZBXJSTZYLXBXQVCXBYIXQYKUQZXQYNXBXQYDYMY
      FYEXQYMPXCDEIKMVDUMVGVEXBYOXQBVFUQBXJXFVHVIUQYAYBXJUJUEUFZXJSXTYDUJUBRZYI
      VBXJSTZUIZVRXMYBYQSTXTYDYRYTXQYDXBYFVEXTVJXTYIYSYPXBYSXQXBBYJVKUQVGVLXFUJ
      XJVMVNXBYQXJVOXQXMXBXJXBXJYKVSVPVAVQWHVTXRXHXSUIXNUOZXMXRXEUBRZYCYIUUAXAX
      QUUBXBXAXQUIHUKRXDJRUUBQIJXCCWAXDHFJLNULWBWCXBXQYCXAYGWDXBYIXAXQYKWEXEXGX
      JWFWGUQWIWJWKWLWMXLXKXPXBXAXJWNRXKXPWTXBXJYKWOAXJCDEFGHIJKLMNOPQWPUPWQWRW
      S $.

    $( An upper bound for an operator norm.  (Contributed by NM, 11-Dec-2007.)
       (New usage is discouraged.) $)
    nmoub2i $p |- ( ( T : X --> Y /\ ( A e. RR /\ 0 <_ A ) /\ A. x e. X
  ( M ` ( T ` x ) ) <_ ( A x. ( L ` x ) ) ) -> ( N ` T ) <_ A ) $=
      ( cle wbr cfv wf cr wcel cc0 wa cv cmul co wral w3a cabs nmoub3i 3adant2r
      wceq absid 3ad2ant2 breqtrd ) IJCUAZBUBUCZUDBRSZUEZAUFZCTFTBVBETUGUHRSAIU
      IZUJCGTZBUKTZBRURUSVCVDVERSUTABCDEFGHIJKLMNOPQULUMVAURVEBUNVCBUOUPUQ $.

    $( Two ways to express that an operator is bounded.  (Contributed by NM,
       11-Jan-2008.)  (New usage is discouraged.) $)
    nmobndi $p |- ( T : X --> Y -> ( ( N ` T ) e. RR <->
     E. r e. RR A. y e. X ( ( L ` y ) <_ 1 -> ( M ` ( T ` y ) ) <_ r ) ) ) $=
      ( cr wcel cle wf cfv cv wbr wrex c1 wral leid breq2 rspcev mpdan cxr cmnf
      wi wa clt cnv nmoxr mp3an12 adantr simprl nmogtmnf simprr xrre rexlimdvaa
      syl22anc impbid2 wb rexr nmoubi sylan2 rexbidva bitrd ) HIBUAZBFUBZRSZVOJ
      UCZTUDZJRUEZAUCZDUBUFTUDVTBUBEUBVQTUDUNAHUGZJRUEVNVPVSVPVOVOTUDZVSVOUHVRW
      BJVORVQVOVOTUIUJUKVNVRVPJRVNVQRSZVRUOZUOVOULSZWCUMVOUPUDZVRVPVNWEWDCUQSZG
      UQSZVNWEPQBCFGHIKLOURUSUTVNWCVRVAVNWFWDWGWHVNWFPQBCFGHIKLOVBUSUTVNWCVRVCV
      OVQVDVFVEVGVNVRWAJRWCVNVQULSVRWAVHVQVIAVQBCDEFGHIKLMNOPQVJVKVLVM $.

    $( Two ways two express that an operator is unbounded.  (Contributed by NM,
       11-Jan-2008.)  (New usage is discouraged.) $)
    nmounbi $p |- ( T : X --> Y -> ( ( N ` T ) = +oo <->
      A. r e. RR E. y e. X ( ( L ` y ) <_ 1 /\ r < ( M ` ( T ` y ) ) ) ) ) $=
      ( cfv cr wcel wf cv c1 cle wbr clt wa wrex wral cpnf wi wne wn nmobndi wb
      cnv nmorepnf mp3an12 ffvelcdm nvcl sylancr lenlt sylan an32s imbi2d imnan
      bitrdi ralbidva ralnex rexbidva rexnal 3bitr3d necon4abid ) HIBUAZAUBZDRU
      CUDUEZJUBZVOBRZERZUFUEZUGZAHUHZJSUIZBFRZUJVNWDSTZVPVSVQUDUEZUKZAHUIZJSUHZ
      WDUJULZWCUMZABCDEFGHIJKLMNOPQUNCUPTGUPTZVNWEWJUOPQBCFGHIKLOUQURVNWIWBUMZJ
      SUHWKVNWHWMJSVNVQSTZUGZWHWAUMZAHUIWMWOWGWPAHWOVOHTZUGZWGVPVTUMZUKWPWRWFWS
      VPVNWQWNWFWSUOZVNWQUGZVSSTZWNWTXAWLVRITXBQHIVOBUSVRGEILNUTVAVSVQVBVCVDVEV
      PVTVFVGVHWAAHVIVGVJWBJSVKVGVLVM $.

    $( An unbounded operator determines an unbounded sequence.  (Contributed by
       NM, 11-Jan-2008.)  (Revised by Mario Carneiro, 7-Apr-2013.)
       (New usage is discouraged.) $)
    nmounbseqi $p |- ( ( T : X --> Y /\ ( N ` T ) = +oo ) ->
         E. f ( f : NN --> X /\ A. k e. NN ( ( L ` ( f ` k ) ) <_ 1 /\
          k < ( M ` ( T ` ( f ` k ) ) ) ) ) ) $=
      ( vy cfv cn wf cpnf wceq wa cv c1 cle wbr clt wrex cr wral nmounbi biimpa
      wex wcel nnre imim1i ralimi2 cba fvexi nnenom fveq2 breq1d 2fveq3 anbi12d
      breq2d axcc4 3syl ) IJAUAZAGSUBUCZUDRUEZESZUFUGUHZDUEZVLASFSZUIUHZUDZRIUJ
      ZDUKULZVSDTULTICUEZUAVOWASZESZUFUGUHZVOWBASFSZUIUHZUDZDTULUDCUOVJVKVTRABE
      FGHIJDKLMNOPQUMUNVSVSDUKTVOTUPVOUKUPVSVOUQURUSVRWGRICDTIBUTKVAVBVLWBUCZVN
      WDVQWFWHVMWCUFUGVLWBEVCVDWHVPWEVOUIVLWBFAVEVGVFVHVI $.

    $( Alternate shorter proof of ~ nmounbseqi based on Axioms ~ ax-reg and
       ~ ax-ac2 instead of ~ ax-cc .  (Contributed by NM, 11-Jan-2008.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    nmounbseqiALT $p |- ( ( T : X --> Y /\ ( N ` T ) = +oo ) ->
         E. f ( f : NN --> X /\ A. k e. NN ( ( L ` ( f ` k ) ) <_ 1 /\
          k < ( M ` ( T ` ( f ` k ) ) ) ) ) ) $=
      ( vy cfv cn wf cpnf wceq wa cv c1 cle wbr clt wrex cr wral nmounbi biimpa
      wex wcel nnre imim1i ralimi2 nnex fveq2 breq1d fveq2d breq2d anbi12d ac6s
      3syl ) IJAUAZAGSUBUCZUDRUEZESZUFUGUHZDUEZVJASZFSZUIUHZUDZRIUJZDUKULZVRDTU
      LTICUEZUAVMVTSZESZUFUGUHZVMWAASZFSZUIUHZUDZDTULUDCUOVHVIVSRABEFGHIJDKLMNO
      PQUMUNVRVRDUKTVMTUPVMUKUPVRVMUQURUSVQWGDRTICUTVJWAUCZVLWCVPWFWHVKWBUFUGVJ
      WAEVAVBWHVOWEVMUIWHVNWDFVJWAAVAVCVDVEVFVG $.

    $( A bounded sequence determines a bounded operator.  (Contributed by NM,
       18-Jan-2008.)  (Revised by Mario Carneiro, 7-Apr-2013.)
       (New usage is discouraged.) $)
    nmobndseqi $p |- ( ( T : X --> Y /\
         A. f ( ( f : NN --> X /\ A. k e. NN ( L ` ( f ` k ) ) <_ 1 ) ->
        E. k e. NN ( M ` ( T ` ( f ` k ) ) ) <_ k ) ) -> ( N ` T ) e. RR ) $=
      ( cn cfv wi vy wf cv c1 cle wbr wral wa wrex cr wcel impexp r19.35 imbi2i
      wal bitr4i albii wn wex cba fvexi nnenom wceq fveq2 breq1d 2fveq3 imbi12d
      notbid axcc4 con3i dfrex2 alinexa bitri dfral2 rexbii rexnal 3imtr4i nnre
      anim1i reximi2 syl sylbi nmobndi imbitrrid imp ) IJAUBZRICUCZUBZDUCZWGSZE
      SZUDUEUFZDRUGZUHWJASFSZWIUEUFZDRUIZTZCUOZAGSUJUKZWRWSWFUAUCZESZUDUEUFZWTA
      SFSZWIUEUFZTZUAIUGZDUJUIZWRWHWLWOTZDRUIZTZCUOZXGWQXJCWQWHWMWPTZTXJWHWMWPU
      LXIXLWHWLWODRUMUNUPUQXKXFDRUIZXGWHXHURZDRUGZUHCUSZURZXEURZUAIUIZDRUGZURZX
      KXMXTXPXRXNUAICDRIBUTKVAVBWTWJVCZXEXHYBXBWLXDWOYBXAWKUDUEWTWJEVDVEYBXCWNW
      IUEWTWJFAVFVEVGVHVIVJXKWHXOURZTZCUOXQXJYDCXIYCWHXHDRVKUNUQWHXOCVLVMXMXSUR
      ZDRUIYAXFYEDRXEUAIVNVOXSDRVPVMVQXFXFDRUJWIRUKWIUJUKXFWIVRVSVTWAWBUAABEFGH
      IJDKLMNOPQWCWDWE $.

    $( Alternate shorter proof of ~ nmobndseqi based on Axioms ~ ax-reg and
       ~ ax-ac2 instead of ~ ax-cc .  (Contributed by NM, 18-Jan-2008.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    nmobndseqiALT $p |- ( ( T : X --> Y /\
         A. f ( ( f : NN --> X /\ A. k e. NN ( L ` ( f ` k ) ) <_ 1 ) ->
        E. k e. NN ( M ` ( T ` ( f ` k ) ) ) <_ k ) ) -> ( N ` T ) e. RR ) $=
      ( cn cfv cle vy wf cv c1 wbr wral wa wrex wi cr wcel impexp r19.35 imbi2i
      wal bitr4i albii nnex wceq breq1d fveq2d imbi12d ac6n nnre anim1i reximi2
      fveq2 syl sylbi nmobndi imbitrrid imp ) IJAUBZRICUCZUBZDUCZVNSZESZUDTUEZD
      RUFZUGVQASZFSZVPTUEZDRUHZUIZCUOZAGSUJUKZWFWGVMUAUCZESZUDTUEZWHASZFSZVPTUE
      ZUIZUAIUFZDUJUHZWFVOVSWCUIZDRUHZUIZCUOZWPWEWSCWEVOVTWDUIZUIWSVOVTWDULWRXA
      VOVSWCDRUMUNUPUQWTWODRUHWPWNWQDUARICURWHVQUSZWJVSWMWCXBWIVRUDTWHVQEVGUTXB
      WLWBVPTXBWKWAFWHVQAVGVAUTVBVCWOWODRUJVPRUKVPUJUKWOVPVDVEVFVHVIUAABEFGHIJD
      KLMNOPQVJVKVL $.
  $}

  ${
    $d t u w L $.  $d t u w N $.  $d t T $.  $d t u w U $.  $d t u w W $.
    bloval.3 $e |- N = ( U normOpOLD W ) $.
    bloval.4 $e |- L = ( U LnOp W ) $.
    bloval.5 $e |- B = ( U BLnOp W ) $.
    $( The class of bounded linear operators between two normed complex vector
       spaces.  (Contributed by NM, 6-Nov-2007.)  (Revised by Mario Carneiro,
       16-Nov-2013.)  (New usage is discouraged.) $)
    bloval $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) ->
                   B = { t e. L | ( N ` t ) < +oo } ) $=
      ( vu vw cnv co cv cfv cpnf clt wbr cnmoo clno wcel cblo crab oveq1 fveq1d
      wa wceq breq1d rabeqbidv oveq2 eqtr4di df-blo ovexi rabex ovmpo eqtrid )
      CLUAFLUAUFBCFUBMANZEOZPQRZADUCZIJKCFLLUQJNZKNZSMZOZPQRZAVAVBTMZUCUTUBUQCV
      BSMZOZPQRZACVBTMZUCVACUGZVEVIAVFVJVACVBTUDVKVDVHPQVKUQVCVGVACVBSUDUEUHUIV
      BFUGZVIUSAVJDVLVJCFTMDVBFCTUJHUKVLVHURPQVLUQVGEVLVGCFSMEVBFCSUJGUKUEUHUIK
      JAULUSADDCFTHUMUNUOUP $.

    $( The predicate "is a bounded linear operator."  (Contributed by NM,
       6-Nov-2007.)  (New usage is discouraged.) $)
    isblo $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> ( T e. B <->
      ( T e. L /\ ( N ` T ) < +oo ) ) ) $=
      ( vt cnv wcel wa cv cfv cpnf clt wbr crab bloval eleq2d wceq fveq2 breq1d
      elrab bitrdi ) CKLFKLMZBALBJNZEOZPQRZJDSZLBDLBEOZPQRZMUGAUKBJACDEFGHITUAU
      JUMJBDUHBUBUIULPQUHBEUCUDUEUF $.

    $( The predicate "is a bounded linear operator."  (Contributed by NM,
       8-Dec-2007.)  (New usage is discouraged.) $)
    isblo2 $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> ( T e. B <->
      ( T e. L /\ ( N ` T ) e. RR ) ) ) $=
      ( cnv wcel wa cfv cpnf clt wbr cr isblo cba eqid lnof nmoreltpnf syld3an3
      wb wf 3expa pm5.32da bitr4d ) CJKZFJKZLZBAKBDKZBEMZNOPZLULUMQKZLABCDEFGHI
      RUKULUOUNUIUJULUOUNUDZUIUJULCSMZFSMZBUEUPBCDFUQURUQTZURTZHUABCEFUQURUSUTG
      UBUCUFUGUH $.
  $}

  ${
    bloln.4 $e |- L = ( U LnOp W ) $.
    bloln.5 $e |- B = ( U BLnOp W ) $.
    $( A bounded operator is a linear operator.  (Contributed by NM,
       8-Dec-2007.)  (New usage is discouraged.) $)
    bloln $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. B ) -> T e. L ) $=
      ( cnv wcel wa cnmoo co cfv cpnf clt wbr eqid isblo simprbda 3impa ) CHIZE
      HIZBAIZBDIZUAUBJUCUDBCEKLZMNOPABCDUEEUEQFGRST $.
  $}

  ${
    blof.1 $e |- X = ( BaseSet ` U ) $.
    blof.2 $e |- Y = ( BaseSet ` W ) $.
    blof.5 $e |- B = ( U BLnOp W ) $.
    $( A bounded operator is an operator.  (Contributed by NM, 8-Dec-2007.)
       (New usage is discouraged.) $)
    blof $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. B ) -> T : X --> Y ) $=
      ( cnv wcel clno co wf eqid bloln lnof syld3an3 ) CJKDJKBAKBCDLMZKEFBNABCS
      DSOZIPBCSDEFGHTQR $.
  $}

  ${
    nmblore.1 $e |- X = ( BaseSet ` U ) $.
    nmblore.2 $e |- Y = ( BaseSet ` W ) $.
    nmblore.3 $e |- N = ( U normOpOLD W ) $.
    nmblore.5 $e |- B = ( U BLnOp W ) $.
    $( The norm of a bounded operator is a real number.  (Contributed by NM,
       8-Dec-2007.)  (New usage is discouraged.) $)
    nmblore $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. B ) ->
                ( N ` T ) e. RR ) $=
      ( cnv wcel w3a cfv cr clt wbr syld3an3 wa cmnf cpnf wf blof nmogtmnf clno
      co eqid isblo simplbda 3impa cxr wb nmoxr xrrebnd syl mpbir2and ) CLMZELM
      ZBAMZNZBDOZPMZUAVBQRZVBUBQRZURUSUTFGBUCZVDABCEFGHIKUDZBCDEFGHIJUESURUSUTV
      EURUSTUTBCEUFUGZMVEABCVHDEJVHUHKUIUJUKVAVBULMZVCVDVETUMURUSUTVFVIVGBCDEFG
      HIJUNSVBUOUPUQ $.
  $}

  ${
    $d u w U $.  $d u w W $.  $d u w X $.  $d u w Z $.
    0oval.1 $e |- X = ( BaseSet ` U ) $.
    0oval.6 $e |- Z = ( 0vec ` W ) $.
    0oval.0 $e |- O = ( U 0op W ) $.
    $( The zero operator between two normed complex vector spaces.
       (Contributed by NM, 28-Nov-2007.)  (Revised by Mario Carneiro,
       16-Nov-2013.)  (New usage is discouraged.) $)
    0ofval $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> O = ( X X. { Z } ) ) $=
      ( vu vw cnv wcel c0o csn cxp cv cba cfv cn0v wceq wa fveq2 eqtr4di xpeq1d
      co sneqd xpeq2d df-0o fvexi snex xpex ovmpo eqtrid ) AKLCKLUABACMUEDENZOZ
      HIJACKKIPZQRZJPZSRZNZOUOMDUTOUPATZUQDUTVAUQAQRDUPAQUBFUCUDURCTZUTUNDVBUSE
      VBUSCSREURCSUBGUCUFUGJIUHDUNDAQFUIEUJUKULUM $.

    $( Value of the zero operator.  (Contributed by NM, 28-Nov-2007.)
       (New usage is discouraged.) $)
    0oval $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ A e. X ) ->
            ( O ` A ) = Z ) $=
      ( cnv wcel w3a cfv csn cxp wceq wa 0ofval fveq1d 3adant3 cn0v fvexi eqtrd
      fvconst2 3ad2ant3 ) BJKZDJKZAEKZLACMZAEFNOZMZFUFUGUIUKPUHUFUGQACUJBCDEFGH
      IRSTUHUFUKFPUGEFAFDUAHUBUDUEUC $.
  $}

  ${
    0oo.1 $e |- X = ( BaseSet ` U ) $.
    0oo.2 $e |- Y = ( BaseSet ` W ) $.
    0oo.0 $e |- Z = ( U 0op W ) $.
    $( The zero operator is an operator.  (Contributed by NM, 28-Nov-2007.)
       (New usage is discouraged.) $)
    0oo $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> Z : X --> Y ) $=
      ( cnv wcel wa wf cn0v cfv csn cxp wss fvex fconst eqid nvzcl snssd adantl
      fss sylancr 0ofval feq1d mpbird ) AIJZBIJZKZCDELCDCBMNZOZPZLZUJUOUIUJCUMU
      NLUMDQUOCULBMRSUJULDBDULGULTZUAUBCUMDUNUDUEUCUKCDEUNAEBCULFUPHUFUGUH $.
  $}

  ${
    $d x y z U $.  $d x y z W $.  $d x y z Z $.
    0lno.0 $e |- Z = ( U 0op W ) $.
    0lno.7 $e |- L = ( U LnOp W ) $.
    $( The zero operator is linear.  (Contributed by NM, 28-Nov-2007.)
       (Revised by Mario Carneiro, 19-Nov-2013.)
       (New usage is discouraged.) $)
    0lno $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> Z e. L ) $=
      ( vx vy vz wcel wa cfv cv co wceq wral cc eqid syl3anc 0oval cnv cba cn0v
      cns cpv 0oo simplll simpllr simplr simprl nvscl simprr nvgcl oveq12d nvsz
      wf oveq2d oveq1d nvzcl nv0rid syl2anc2 3eqtrd eqtr4d ralrimivva ralrimiva
      syl2anc islno mpbir2and ) AUAJZCUAJZKZDBJAUBLZCUBLZDUPGMZHMZAUDLZNZIMZAUE
      LZNZDLZVNVODLZCUDLZNZVRDLZCUELZNZOZIVLPHVLPZGQPACVLVMDVLRZVMRZEUFVKWIGQVK
      VNQJZKZWHHIVLVLWMVOVLJZVRVLJZKZKZWACUCLZWGWQVIVJVTVLJZWAWROVIVJWLWPUGZVIV
      JWLWPUHZWQVIVQVLJZWOWSWTWQVIWLWNXBWTVKWLWPUIZWMWNWOUJZVNVOVPAVLWJVPRZUKSW
      MWNWOULZVQVRAVSVLWJVSRZUMSVTADCVLWRWJWRRZETSWQWGVNWRWCNZWRWFNWRWRWFNZWRWQ
      WDXIWEWRWFWQWBWRVNWCWQVIVJWNWBWROWTXAXDVOADCVLWRWJXHETSUQWQVIVJWOWEWROWTX
      AXFVRADCVLWRWJXHETSUNWQXIWRWRWFWQVJWLXIWROXAXCVNWCCWRWCRZXHUOVFURWQVJWRVM
      JXJWROXACVMWRWKXHUSWRCWFVMWRWKWFRZXHUTVAVBVCVDVEGHIVPWCDAVSWFBCVLVMWJWKXG
      XLXEXKFVGVH $.
  $}

  ${
    $d x z U $.  $d x z W $.  $d x z Z $.
    nmoo0.3 $e |- N = ( U normOpOLD W ) $.
    nmoo0.0 $e |- Z = ( U 0op W ) $.
    $( The operator norm of the zero operator.  (Contributed by NM,
       27-Nov-2007.)  (New usage is discouraged.) $)
    nmoo0 $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) ->
         ( N ` Z ) = 0 ) $=
      ( vz vx cnv wcel wa cfv cc0 cxr clt c1 cle wceq wrex eqid csn csup cv wbr
      cnmcv cba cab wf 0oo nmooval mpd3an3 df-sn cn0v nvzcl nvz0 eqbrtrdi fveq2
      wb 0le1 breq1d rspcev syl2anc biantrurd adantr 0oval 3expa ad2antlr eqtrd
      fveq2d eqeq2d anbi2d rexbidva r19.41v bitr2di bitrd abbidv eqtr2id xrltso
      supeq1d wor 0xr supsn mp2an eqtrdi ) AIJZCIJZKZDBLZMUAZNOUBZMWGWHGUCZAUEL
      ZLZPQUDZHUCZWKDLZCUELZLZRZKZGAUFLZSZHUGZNOUBZWJWEWFXACUFLZDUHWHXDRACXAXED
      XATZXETZFUIHGDAWLWQBCXAXEXFXGWLTZWQTZEUJUKWGNXCWIOWGWIWOMRZHUGXCHMULWGXJX
      BHWGXJWNGXASZXJKZXBWEXJXLURWFWEXKXJWEAUMLZXAJXMWLLZPQUDZXKAXAXMXFXMTZUNWE
      XNMPQAWLXMXPXHUOUSUPWNXOGXMXAWKXMRWMXNPQWKXMWLUQUTVAVBVCVDWGXBWNXJKZGXASX
      LWGWTXQGXAWGWKXAJZKZWSXJWNXSWRMWOXSWRCUMLZWQLZMXSWPXTWQWEWFXRWPXTRWKADCXA
      XTXFXTTZFVEVFVIWFYAMRWEXRCWQXTYBXIUOVGVHVJVKVLWNXJGXAVMVNVOVPVQVSVHNOVTMN
      JWJMRVRWANMOWBWCWD $.
  $}

  ${
    0blo.0 $e |- Z = ( U 0op W ) $.
    0blo.7 $e |- B = ( U BLnOp W ) $.
    $( The zero operator is a bounded linear operator.  (Contributed by NM,
       8-Dec-2007.)  (New usage is discouraged.) $)
    0blo $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> Z e. B ) $=
      ( cnv wcel wa clno co cnmoo cfv cr eqid 0lno cc0 nmoo0 0re eqeltrdi
      isblo2 mpbir2and ) BGHCGHIZDAHDBCJKZHDBCLKZMZNHBUDCDEUDOZPUCUFQNBUECDUEOZ
      ERSTADBUDUECUHUGFUAUB $.
  $}

  ${
    $d y z K $.  $d y z M $.  $d x N $.  $d z R $.  $d y z S $.  $d x y z T $.
    $d y z U $.  $d y z W $.  $d x y z X $.  $d y z Y $.  $d x Z $.
    nmlno0.3 $e |- N = ( U normOpOLD W ) $.
    nmlno0.0 $e |- Z = ( U 0op W ) $.
    nmlno0.7 $e |- L = ( U LnOp W ) $.
    ${
      nmlno0lem.u $e |- U e. NrmCVec $.
      nmlno0lem.w $e |- W e. NrmCVec $.
      nmlno0lem.l $e |- T e. L $.
      nmlno0lem.1 $e |- X = ( BaseSet ` U ) $.
      nmlno0lem.2 $e |- Y = ( BaseSet ` W ) $.
      nmlno0lem.r $e |- R = ( .sOLD ` U ) $.
      nmlno0lem.s $e |- S = ( .sOLD ` W ) $.
      nmlno0lem.p $e |- P = ( 0vec ` U ) $.
      nmlno0lem.q $e |- Q = ( 0vec ` W ) $.
      nmlno0lem.k $e |- K = ( normCV ` U ) $.
      nmlno0lem.m $e |- M = ( normCV ` W ) $.
      $( Lemma for ~ nmlno0i .  (Contributed by NM, 28-Nov-2007.)
         (New usage is discouraged.) $)
      nmlno0lem $p |- ( ( N ` T ) = 0 <-> T = Z ) $=
        ( vx vz vy cfv cc0 wceq cv wral wcel wa wne wn c1 cdiv co clt wbr wi cc
        cnv cr nvcl mpan recnd adantr wb nvz fveq2 lno0 eqtrdi biimtrdi necon3d
        mp3an recne0d simpr wo reccld wf lnof ffvelcdmi nvmul0or mp3an1 syl2anc
        imp necon3abid neanior bitr4di mpbir2and nvscl nvgt0 sylancr adantl cle
        mpbid ex wrex cab cxr wss nmosetre mp2an ressxr sstri simpl necon3i nv1
        csup sylan2 1re eqeltrdi w3a 3pm3.2i lnomul eqcomd fveq2d breq1d 2fveq3
        eqle eqeq2d anbi12d rspcev syl12anc eqeq1 anbi2d rexbidv sylibr adantll
        fvex elab wfn ffn ax-mp supxrub nmooval eqeq1i biimpi breqtrd 0re lenlt
        ad2antrr sylancl pm2.65d nne sylib 0oval mp3an12 eqtr4d ralrimiva nmoo0
        0oo eqfnfv impbii ) EJULZUMUNZENUNZUVBUIUOZEULZUVDNULZUNZUILUPZUVCUVBUV
        GUILUVBUVDLUQZURZUVEBUVFUVJUVEBUSZUTUVEBUNZUVJUVKUMVAUVDGULZVBVCZUVEDVC
        ZIULZVDVEZUVIUVKUVQVFUVBUVIUVKUVQUVIUVKURZUVOBUSZUVQUVRUVSUVNUMUSZUVKUV
        RUVMUVIUVMVGUQUVKUVIUVMFVHUQZUVIUVMVIUQRUVDFGLUAUGVJVKVLVMZUVIUVKUVMUMU
        SUVIUVMUMUVEBUVIUVMUMUNZUVDAUNZUVLUWAUVIUWCUWDVNRUVDFGLAUAUEUGVOVKUWDUV
        EAEULZBUVDAEVPUWAKVHUQZEHUQZUWEBUNRSTAEFHKLMBUAUBUEUFQVQWAVRZVSVTWLZWBU
        VIUVKWCUVRUVSUVNUMUNUVLWDZUTUVTUVKURUVRUWJUVOBUVRUVNVGUQZUVEMUQZUVOBUNU
        WJVNZUVRUVMUWBUWIWEZUVIUWLUVKLMUVDEUWAUWFUWGLMEWFZRSTEFHKLMUAUBQWGWAZWH
        VMZUWFUWKUWLUWMSUVNUVEDKMBUBUDUFWIWJWKWMUVNUMUVEBWNWOWPUVRUWFUVOMUQZUVS
        UVQVNSUVRUWKUWLUWRUWNUWQUWFUWKUWLUWRSUVNUVEDKMUBUDWQWJWKZUVOKIMBUBUFUHW
        RWSXBXCWTUVJUVKUVQUTZUVJUVKURZUVPUMXAVEZUWTUXAUVPUJUOZGULZVAXAVEZUKUOZU
        XCEULIULZUNZURZUJLXDZUKXEZXFVDXOZUMXAUVIUVKUVPUXLXAVEZUVBUVRUXKXFXGUVPU
        XKUQZUXMUXKVIXFUWFUWOUXKVIXGSUWPUKUJEGIKLMUBUHXHXIXJXKUVRUXEUVPUXGUNZUR
        ZUJLXDZUXNUVRUVNUVDCVCZLUQZUXRGULZVAXAVEZUVPUXREULZIULZUNZUXQUVRUWKUVIU
        XSUWNUVIUVKXLZUWAUWKUVIUXSRUVNUVDCFLUAUCWQWJWKUVRUXTVIUQUXTVAUNZUYAUVRU
        XTVAVIUVKUVIUVDAUSZUYFUVDAUVEBUWHXMUWAUVIUYGUYFRUVDCFGLAUAUCUEUGXNWJXPZ
        XQXRUYHUXTVAYFWKUVRUVOUYBIUVRUYBUVOUVRUWKUVIUYBUVOUNZUWNUYEUWAUWFUWGXSU
        WKUVIURUYIUWAUWFUWGRSTXTUVNUVDCDEFHKLUAUCUDQYAVKWKYBYCUXPUYAUYDURUJUXRL
        UXCUXRUNZUXEUYAUXOUYDUYJUXDUXTVAXAUXCUXRGVPYDUYJUXGUYCUVPUXCUXRIEYEYGYH
        YIYJUXJUXQUKUVPUVOIYPUXFUVPUNZUXIUXPUJLUYKUXHUXOUXEUXFUVPUXGYKYLYMYQYNU
        XKUVPUUAWSYOUVBUXLUMUNZUVIUVKUVBUYLUVAUXLUMUWAUWFUWOUVAUXLUNRSUWPUKUJEF
        GIJKLMUAUBUGUHOUUBWAUUCUUDUUHUUEUVIUVKUXBUWTVNZUVBUVRUVPVIUQZUMVIUQUYMU
        VRUWFUWRUYNSUWSUVOKIMUBUHVJWSUUFUVPUMUUGUUIYOXBXCUUJUVEBUUKUULUVIUVFBUN
        ZUVBUWAUWFUVIUYORSUVDFNKLBUAUFPUUMUUNWTUUOUUPELYRZNLYRZUVCUVHVNUWOUYPUW
        PLMEYSYTLMNWFZUYQUWAUWFUYRRSFKLMNUAUBPUURXILMNYSYTUILENUUSXIYNUVCUVANJU
        LZUMENJVPUWAUWFUYSUMUNRSFJKNOPUUQXIVRUUT $.
    $}

    ${
      nmlno0i.u $e |- U e. NrmCVec $.
      nmlno0i.w $e |- W e. NrmCVec $.
      $( The norm of a linear operator is zero iff the operator is zero.
         (Contributed by NM, 6-Dec-2007.)  (New usage is discouraged.) $)
      nmlno0i $p |- ( T e. L -> ( ( N ` T ) = 0 <-> T = Z ) ) $=
        ( wcel cfv cc0 wceq wb cn0v cns cnmcv eqid cif fveqeq2 bibi12d cba 0lno
        eqeq1 cnv mp2an elimel nmlno0lem dedth ) ACLZADMNOZAFOZPULAFUAZDMNOZUOF
        OZPAFAUOOUMUPUNUQAUONDUBAUOFUFUCBQMZEQMZBRMZERMZUOBBSMZCESMZDEBUDMZEUDM
        ZFGHIJKAFCBUGLEUGLFCLJKBCEFHIUEUHUIVDTVETUTTVATURTUSTVBTVCTUJUK $.
    $}

    $( The norm of a linear operator is zero iff the operator is zero.
       (Contributed by NM, 24-Nov-2007.)  (New usage is discouraged.) $)
    nmlno0 $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) ->
       ( ( N ` T ) = 0 <-> T = Z ) ) $=
      ( wcel cfv cc0 wceq wb wi clno co cnmoo c0o oveq1 cnv caddc cmul cop cabs
      cif eqtrid eleq2d fveq1d eqeq1d eqeq2d bibi12d imbi12d oveq2 eqid elimnvu
      nmlno0i dedth2h 3impia ) BUAJZEUAJZACJZADKZLMZAFMZNZUTVAVBVFOAUTBUBUCUDUE
      UDZUFZEPQZJZAVHERQZKZLMZAVHESQZMZNZOAVHVAEVGUFZPQZJZAVHVQRQZKZLMZAVHVQSQZ
      MZNZOBEVGVGBVHMZVBVJVFVPWFCVIAWFCBEPQVIIBVHEPTUGUHWFVDVMVEVOWFVCVLLWFADVK
      WFDBERQVKGBVHERTUGUIUJWFFVNAWFFBESQVNHBVHESTUGUKULUMEVQMZVJVSVPWEWGVIVRAE
      VQVHPUNUHWGVMWBVOWDWGVLWALWGAVKVTEVQVHRUNUIUJWGVNWCAEVQVHSUNUKULUMAVHVRVT
      VQWCVTUOWCUOVRUOBUPEUPUQURUS $.
  $}

  ${
    $d x A $.  $d x K $.  $d x L $.  $d x M $.  $d x T $.  $d x U $.  $d x W $.
    $d x X $.
    nmlnoubi.1 $e |- X = ( BaseSet ` U ) $.
    nmlnoubi.z $e |- Z = ( 0vec ` U ) $.
    nmlnoubi.k $e |- K = ( normCV ` U ) $.
    nmlnoubi.m $e |- M = ( normCV ` W ) $.
    nmlnoubi.3 $e |- N = ( U normOpOLD W ) $.
    nmlnoubi.7 $e |- L = ( U LnOp W ) $.
    nmlnoubi.u $e |- U e. NrmCVec $.
    nmlnoubi.w $e |- W e. NrmCVec $.
    $( An upper bound for the operator norm of a linear operator, using only
       the properties of nonzero arguments.  (Contributed by NM, 1-Jan-2008.)
       (New usage is discouraged.) $)
    nmlnoubi $p |- ( ( T e. L /\ ( A e. RR /\ 0 <_ A ) /\ A. x e. X ( x =/= Z
     -> ( M ` ( T ` x ) ) <_ ( A x. ( K ` x ) ) ) ) -> ( N ` T ) <_ A ) $=
      ( cc0 wcel cr cle wbr wa cv wne cfv cmul co wral wceq 2fveq3 fveq2 oveq2d
      wi breq12d id imp adantll 0le0 cn0v cnv cba eqid lno0 mp3an12 fveq2d nvz0
      ax-mp eqtrdi adantr oveq2i recn mul01d eqtrid ad2antrl mpbiri pm2.61ne ex
      ralimdv 3impia wf lnof nmoub2i syl3an1 syld3an3 ) CFUAZBUBUAZTBUCUDZUEZAU
      FZKUGZWLCUHGUHZBWLEUHZUIUJZUCUDZUPZAJUKZWQAJUKZCHUHBUCUDZWHWKWSWTWHWKUEZW
      RWQAJXBWRWQXBWRUEWQKCUHZGUHZBKEUHZUIUJZUCUDZWLKWLKULZWNXDWPXFUCWLKGCUMXHW
      OXEBUIWLKEUNUOUQWRWMWQXBWRWMWQWRURUSUTXBXGWRXBXGTTUCUDVAXBXDTXFTUCWHXDTUL
      WKWHXDIVBUHZGUHZTWHXCXIGDVCUAZIVCUAZWHXCXIULRSKCDFIJIVDUHZXILXMVEZMXIVEZQ
      VFVGVHXLXJTULSIGXIXOOVIVJVKVLWIXFTULWHWJWIXFBTUIUJTXETBUIXKXETULRDEKMNVIV
      JVMWIBBVNVOVPVQUQVRVLVSVTWAWBWHJXMCWCZWKWTXAXKXLWHXPRSCDFIJXMLXNQWDVGABCD
      EGHIJXMLXNNOPRSWEWFWG $.
  $}

  ${
    nmlnogt0.3 $e |- N = ( U normOpOLD W ) $.
    nmlnogt0.0 $e |- Z = ( U 0op W ) $.
    nmlnogt0.7 $e |- L = ( U LnOp W ) $.
    $( The norm of a nonzero linear operator is positive.  (Contributed by NM,
       10-Dec-2007.)  (New usage is discouraged.) $)
    nmlnogt0 $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) ->
                   ( T =/= Z <-> 0 < ( N ` T ) ) ) $=
      ( cnv wcel w3a cfv cc0 wne clt wbr cba wb eqid nmlno0 necon3bid cxr nmoxr
      wf lnof cle nmooge0 wa wo 0xr xrlttri2 mpan2 adantr wn xrlenlt mpan biorf
      biimpa syl bitr4d syl2anc syld3an3 bitr3d ) BJKZEJKZACKZLZADMZNOZAFONVIPQ
      ZVHVINAFABCDEFGHIUAUBVEVFVGBRMZERMZAUEZVJVKSZABCEVLVMVLTZVMTZIUFVEVFVNLVI
      UCKZNVIUGQZVOABDEVLVMVPVQGUDABDEVLVMVPVQGUHVRVSUIZVJVINPQZVKUJZVKVRVJWBSZ
      VSVRNUCKZWCUKVINULUMUNVTWAUOZVKWBSVRVSWEWDVRVSWESUKNVIUPUQUSWAVKURUTVAVBV
      CVD $.
  $}

  ${
    $d x L $.  $d x T $.  $d x U $.  $d x W $.  $d x X $.
    lnon0.1 $e |- X = ( BaseSet ` U ) $.
    lnon0.6 $e |- Z = ( 0vec ` U ) $.
    lnon0.0 $e |- O = ( U 0op W ) $.
    lnon0.7 $e |- L = ( U LnOp W ) $.
    $( The domain of a nonzero linear operator contains a nonzero vector.
       (Contributed by NM, 15-Dec-2007.)  (New usage is discouraged.) $)
    lnon0 $p |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) /\ T =/= O )
                   -> E. x e. X x =/= Z ) $=
      ( cnv wcel wne wn wceq wral bitr3i cfv w3a cv wrex ralnex nne ralbii cn0v
      csn cxp wfn wa fveq2 cba eqid lno0 sylan9eqr ralimdv lnof jctild fconstfv
      ex ffnd wf fvex fconst2 imbitrdi 0ofval 3adant3 sylibrd biimtrid necon1ad
      eqeq2d imp ) CMNZFMNZBDNZUAZBEOAUBZHOZAGUCZVQVTBEVTPZVRHQZAGRZVQBEQZWAVSP
      ZAGRWCVSAGUDWEWBAGVRHUEUFSVQWCBGFUGTZUHZUIZQZWDVQWCBGUJZVRBTZWFQZAGRZUKZW
      IVQWCWMWJVQWBWLAGVQWBWLWBVQWKHBTWFVRHBULHBCDFGFUMTZWFIWOUNZJWFUNZLUOUPVAU
      QVQGWOBBCDFGWOIWPLURVBUSWNGWGBVCWIAGWFBUTGWFBFUGVDVESVFVQEWHBVNVOEWHQVPCE
      FGWFIWQKVGVHVLVIVJVKVM $.
  $}

  ${
    nmblolbi.1 $e |- X = ( BaseSet ` U ) $.
    nmblolbi.4 $e |- L = ( normCV ` U ) $.
    nmblolbi.5 $e |- M = ( normCV ` W ) $.
    nmblolbi.6 $e |- N = ( U normOpOLD W ) $.
    nmblolbi.7 $e |- B = ( U BLnOp W ) $.
    nmblolbi.u $e |- U e. NrmCVec $.
    nmblolbi.w $e |- W e. NrmCVec $.
    ${
      nmblolbii.b $e |- T e. B $.
      $( A lower bound for the norm of a bounded linear operator.  (Contributed
         by NM, 7-Dec-2007.)  (New usage is discouraged.) $)
      nmblolbii $p |- ( A e. X ->
                ( M ` ( T ` A ) ) <_ ( ( N ` T ) x. ( L ` A ) ) ) $=
        ( wcel cfv cc0 cmul co cle wbr cn0v wceq fveq2 fveq2d oveq2d breq12d wa
        wne cdiv c1 cns cr cba cnv nvcl mpan adantr eqid nvz necon3bid rereccld
        wb biimpar clt nvgt0 biimpa recgt0d 0re ltle sylancr mpd blof ffvelcdmi
        wi wf mp3an nvsge0 mp3an1 syl21anc cc recnd simpl clno w3a bloln lnomul
        3pm3.2i syl2anc divrec2d 3eqtr4rd ancoms syldan nv1 eqle nmoolb eqbrtrd
        nvscl nmblore a1i ledivmul2 syl112anc mpbid 0le0 lno0 fveq2i nvz0 ax-mp
        eqtri oveq2i recni mul01i 3brtr4i pm2.61ne ) AIRZACSZFSZCGSZAESZUAUBZUC
        UDZDUESZCSZFSZYAYEESZUAUBZUCUDZAYEAYEUFZXTYGYCYIUCYKXSYFFAYECUGUHYKYBYH
        YAUAAYEEUGUIUJXRAYEULZUKZXTYBUMUBZYAUCUDZYDYMYNUNYBUMUBZADUOSZUBZCSZFSZ
        YAUCYMYPXSHUOSZUBZFSZYPXTUAUBZYTYNYMYPUPRZTYPUCUDZXSHUQSZRZUUCUUDUFZYMY
        BXRYBUPRZYLDURRZXRUUJOADEIJKUSUTVAZXRYBTULYLXRYBTAYEUUKXRYBTUFYKVFOADEI
        YEJYEVBZKVCUTVDVGZVEZYMTYPVHUDZUUFYMYBUULXRYLTYBVHUDZUUKXRYLUUQVFOADEIY
        EJUUMKVIUTVJZVKYMTUPRUUEUUPUUFVRVLUUOTYPVMVNVOXRUUHYLIUUGACUUKHURRZCBRZ
        IUUGCVSZOPQBCDHIUUGJUUGVBZNVPVTZVQZVAUUSUUEUUFUKUUHUUIPYPXSUUAHFUUGUVBU
        UAVBZLWAWBWCYMYSUUBFYMYPWDRZXRYSUUBUFZYMYPUUOWEZXRYLWFUUKUUSCDHWGUBZRZW
        HUVFXRUKUVGUUKUUSUVJOPUUKUUSUUTUVJOPQBCDUVIHUVIVBZNWIVTZWKYPAYQUUACDUVI
        HIJYQVBZUVEUVKWJUTWLUHYMXTYBYMXTXRXTUPRZYLXRUUSUUHUVNPUVDXSHFUUGUVBLUSV
        NVAZWEYMYBUULWEUUNWMWNYMYRIRZYRESZUNUCUDZYTYAUCUDZXRYLUVFUVPUVHUVFXRUVP
        UUKUVFXRUVPOYPAYQDIJUVMXAWBWOWPZYMUVQUPRZUVQUNUFZUVRYMUUKUVPUWAOUVTYRDE
        IJKUSVNUUKXRYLUWBOAYQDEIYEJUVMUUMKWQWBUVQUNWRWLUUKUUSUVAWHUVPUVRUKUVSUU
        KUUSUVAOPUVCWKYRCDEFGHIUUGJUVBKLMWSUTWLWTYMUVNYAUPRZUUJUUQYOYDVFUVOUWCY
        MUUKUUSUUTUWCOPQBCDGHIUUGJUVBMNXBVTZXCUULUURXTYAYBXDXEXFYJXRTTYGYIUCXGY
        GHUESZFSZTYFUWEFUUKUUSUVJYFUWEUFOPUVLYECDUVIHIUUGUWEJUVBUUMUWEVBZUVKXHV
        TXIUUSUWFTUFPHFUWEUWGLXJXKXLYIYATUAUBTYHTYAUAUUKYHTUFODEYEUUMKXJXKXMYAY
        AUWDXNXOXLXPXCXQ $.
    $}

    $( A lower bound for the norm of a bounded linear operator.  (Contributed
       by NM, 10-Dec-2007.)  (New usage is discouraged.) $)
    nmblolbi $p |- ( ( T e. B /\ A e. X ) ->
              ( M ` ( T ` A ) ) <_ ( ( N ` T ) x. ( L ` A ) ) ) $=
      ( wcel cfv cmul co cle wbr c0o cif wceq fveq1 fveq2d fveq2 oveq1d breq12d
      wi imbi2d cnv eqid 0blo mp2an elimel nmblolbii dedth imp ) CBQZAIQZACRZFR
      ZCGRZAERZSTZUAUBZVAVBVHUKVBAVACDHUCTZUDZRZFRZVJGRZVFSTZUAUBZUKCVICVJUEZVH
      VOVBVPVDVLVGVNUAVPVCVKFACVJUFUGVPVEVMVFSCVJGUHUIUJULABVJDEFGHIJKLMNOPCVIB
      DUMQHUMQVIBQOPBDHVIVIUNNUOUPUQURUSUT $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x L $.  $d x y M $.  $d x y N $.  $d x y T $.
    $d x y U $.  $d x y W $.  $d x y X $.
    isblo3i.1 $e |- X = ( BaseSet ` U ) $.
    isblo3i.m $e |- M = ( normCV ` U ) $.
    isblo3i.n $e |- N = ( normCV ` W ) $.
    isblo3i.4 $e |- L = ( U LnOp W ) $.
    isblo3i.5 $e |- B = ( U BLnOp W ) $.
    isblo3i.u $e |- U e. NrmCVec $.
    isblo3i.w $e |- W e. NrmCVec $.
    $( The predicate "is a bounded linear operator."  Definition 2.7-1 of
       [Kreyszig] p. 91.  (Contributed by NM, 11-Dec-2007.)
       (New usage is discouraged.) $)
    isblo3i $p |- ( T e. B <-> ( T e. L /\
          E. x e. RR A. y e. X ( N ` ( T ` y ) ) <_ ( x x. ( M ` y ) ) ) ) $=
      ( wcel cfv cr cv cmul co cle wbr wral wrex wa cnv bloln mp3an12 cnmoo cba
      eqid nmblore nmblolbi ralrimiva wceq oveq1 breq2d ralbidv syl2anc jca w3a
      rspcev cpnf clt simp1 wf lnof cabs cxr nmoxr 3ad2ant1 recn rexrd 3ad2ant2
      abscld pnfxr a1i nmoub3i ltpnf syl xrlelttrd syl3an1 isblo mp2an sylanbrc
      wb rexlimdv3a imp impbii ) DCRZDFRZBUAZDSHSZAUAZWOGSZUBUCZUDUEZBJUFZATUGZ
      UHWMWNXBEUIRZIUIRZWMWNPQCDEFINOUJUKWMDEIULUCZSZTRZWPXFWRUBUCZUDUEZBJUFZXB
      XCXDWMXGPQCDEXEIJIUMSZKXKUNZXEUNZOUOUKWMXIBJWOCDEGHXEIJKLMXMOPQUPUQXAXJAX
      FTWQXFURZWTXIBJXNWSXHWPUDWQXFWRUBUSUTVAVEVBVCWNXBWMWNXAWMATWNWQTRZXAVDWNX
      FVFVGUEZWMWNXOXAVHWNJXKDVIZXOXAXPXCXDWNXQPQDEFIJXKKXLNVJUKXQXOXAVDZXFWQVK
      SZVFXQXOXFVLRZXAXCXDXQXTPQDEXEIJXKKXLXMVMUKVNXOXQXSVLRXAXOXSXOWQWQVOVRZVP
      VQVFVLRXRVSVTBWQDEGHXEIJXKKXLLMXMPQWAXOXQXSVFVGUEZXAXOXSTRYBYAXSWBWCVQWDW
      EXCXDWMWNXPUHWIPQCDEFXEIXMNOWFWGWHWJWKWL $.

    $( Properties that determine a bounded linear operator.  (Contributed by
       NM, 13-Jan-2008.)  (New usage is discouraged.) $)
    blo3i $p |- ( ( T e. L /\ A e. RR /\ A. y e. X ( N ` ( T ` y ) ) <_
               ( A x. ( M ` y ) ) ) -> T e. B ) $=
      ( vx wcel cr cv cfv cmul co cle wbr wral wa wrex wceq oveq1 breq2d rspcev
      ralbidv isblo3i biimpri sylan2 3impb ) DFSZBTSZAUAZDUBHUBZBVAGUBZUCUDZUEU
      FZAJUGZDCSZUTVFUHUSVBRUAZVCUCUDZUEUFZAJUGZRTUIZVGVKVFRBTVHBUJZVJVEAJVMVIV
      DVBUEVHBVCUCUKULUNUMVGUSVLUHRACDEFGHIJKLMNOPQUOUPUQUR $.
  $}

  ${
    blometi.1 $e |- X = ( BaseSet ` U ) $.
    blometi.2 $e |- Y = ( BaseSet ` W ) $.
    blometi.8 $e |- C = ( IndMet ` U ) $.
    blometi.d $e |- D = ( IndMet ` W ) $.
    blometi.6 $e |- N = ( U normOpOLD W ) $.
    blometi.7 $e |- B = ( U BLnOp W ) $.
    blometi.u $e |- U e. NrmCVec $.
    blometi.w $e |- W e. NrmCVec $.
    $( Upper bound for the distance between the values of a bounded linear
       operator.  (Contributed by NM, 11-Dec-2007.)
       (New usage is discouraged.) $)
    blometi $p |- ( ( T e. B /\ P e. X /\ Q e. X ) ->
         ( ( T ` P ) D ( T ` Q ) ) <_ ( ( N ` T ) x. ( P C Q ) ) ) $=
      ( cfv wcel w3a cnsb co cnmcv cmul cle wbr wa cnv eqid nvmcl mp3an1 sylan2
      nmblolbi 3impb wceq wf mp3an12 ffvelcdmda 3adant3 3adant2 imsdval syl2anc
      bloln lnosub mp3anl1 mpanl1 syl3an1 fveq2d eqtr4d 3adant1 oveq2d 3brtr4d
      blof clno ) FAUAZDJUAZEJUAZUBZDEGUCTZUDZFTZIUETZTZFHTZWBGUETZTZUFUDZDFTZE
      FTZCUDZWFDEBUDZUFUDUGVQVRVSWEWIUGUHZVRVSUIZVQWBJUAZWNGUJUAZVRVSWPRDEGWAJL
      WAUKZULUMWBAFGWGWDHIJLWGUKZWDUKZPQRSUOUNUPVTWLWJWKIUCTZUDZWDTZWEVTWJKUAZW
      KKUAZWLXCUQZVQVRXDVSVQJKDFWQIUJUAZVQJKFURRSAFGIJKLMQVOUSZUTVAVQVSXEVRVQJK
      EFXHUTVBXGXDXEXFSWJWKCIXAWDKMXAUKZWTOVCUMVDVTWCXBWDVQFGIVPUDZUAZVRVSWCXBU
      QZWQXGVQXKRSAFGXJIXJUKZQVEUSXKVRVSXLXGXKWOXLSWQXGXKWOXLRDEFGXJWAXAIJLWRXI
      XMVFVGVHUPVIVJVKVTWMWHWFUFVRVSWMWHUQZVQWQVRVSXNRDEBGWAWGJLWRWSNVCUMVLVMVN
      $.
  $}

  ${
    $d w x y z B $.  $d w x y z C $.  $d w x y z D $.  $d x L $.  $d x y z P $.
    $d w x y z J $.  $d w x y z K $.  $d w x y z T $.  $d w x y z U $.
    $d w x y z W $.  $d x y z X $.
    blocni.8 $e |- C = ( IndMet ` U ) $.
    blocni.d $e |- D = ( IndMet ` W ) $.
    blocni.j $e |- J = ( MetOpen ` C ) $.
    blocni.k $e |- K = ( MetOpen ` D ) $.
    blocni.4 $e |- L = ( U LnOp W ) $.
    blocni.5 $e |- B = ( U BLnOp W ) $.
    blocni.u $e |- U e. NrmCVec $.
    blocni.w $e |- W e. NrmCVec $.
    blocni.l $e |- T e. L $.
    ${
      blocnilem.1 $e |- X = ( BaseSet ` U ) $.
      $( TODO - this needs to be broken up or shortened $)
      $( Lemma for ~ blocni and ~ lnocni .  If a linear operator is continuous
         at any point, it is bounded.  (Contributed by NM, 17-Dec-2007.)
         (Revised by Mario Carneiro, 10-Jan-2014.)
         (New usage is discouraged.) $)
      blocnilem $p |- ( ( P e. X /\ T e. ( ( J CnP K ) ` P ) ) -> T e. B ) $=
        ( vz vx vy wcel ccnp co cfv wa cv cnmcv cmul cle wbr wral cr wrex c1 wi
        crp cxmet cba cnv imsxmet eqid 1rp metcnpi3 mpanr2 mpanl12 cdiv rpreccl
        ax-mp rpred ad2antlr cnsb wb wceq imsdval mp3an1 breq1d mp3an ffvelcdmi
        wf lnof syl2an 3pm3.2i lnosub mpan fveq2d eqtr4d imbi12d ancoms adantlr
        w3a ralbidva cn0v 2fveq3 fveq2 oveq2d breq12d wne cns cpv a1i simpll cc
        simpr nvcl adantr cc0 clt nvgt0 biimpa elrpd rpdivcl rpcnd simprl nvscl
        syl3anc nvpncan2 rprege0d nvsge0 rpcn ad2antrl recnd nvz biimpar adantl
        necon3bid divcan1d 3eqtrd rpre fvoveq1 syl syl2anc eqtrd rpcnne0 breq2d
        imp nvz0 leidd eqbrtrd nvgcl mpid sylancr 1red lemuldiv2d lnomul recdiv
        rspcv rpne0 divrec2d eqtr2d 3bitr4d sylibd an32s lno0 fveq2i eqtri 0le0
        anassrs eqbrtri oveq2i mul01 eqtrid breqtrrid ad3antlr ralrimdva sylbid
        pm2.61ne ex oveq1 ralbidv rspcev rexlimdva2 syl5 isblo3i mpbiran sylibr
        ) DKUEZEDGHUFUGUHUEZUIUBUJZEUHZJUKUHZUHZUCUJZUWBFUKUHZUHZULUGZUMUNZUBKU
        OZUCUPUQZEAUEZUVTUWAUWLUWAUWFDBUGZUDUJZUMUNZUWFEUHZDEUHZCUGZURUMUNZUSZU
        CKUOZUDUTUQZUVTUWLBKVAUHUEZCJVBUHZVAUHUEZUWAUXCFVCUEZUXDRBFKUALVDVLJVCU
        EZUXFSCJUXEUXEVEZMVDVLUXDUXFUIUWAURUTUEUXCVFUDUCURBCDEGHKUXENOVGVHVIUVT
        UXBUWLUDUTUVTUWOUTUEZUIZUXBUIURUWOVJUGZUPUEZUWEUXLUWHULUGZUMUNZUBKUOZUW
        LUXJUXMUVTUXBUXJUXLUWOVKZVMVNUXKUXBUXPUXKUXBUWFDFVOUHZUGZUWGUHZUWOUMUNZ
        UXSEUHZUWDUHZURUMUNZUSZUCKUOZUXPUXKUXAUYEUCKUVTUWFKUEZUXAUYEVPZUXJUYGUV
        TUYHUYGUVTUIZUWPUYAUWTUYDUYIUWNUXTUWOUMUXGUYGUVTUWNUXTVQRUWFDBFUXRUWGKU
        AUXRVEZUWGVEZLVRVSVTUYIUWSUYCURUMUYIUWSUWQUWRJVOUHZUGZUWDUHZUYCUYGUWQUX
        EUEZUWRUXEUEZUWSUYNVQZUVTKUXEUWFEUXGUXHEIUEZKUXEEWCRSTEFIJKUXEUAUXIPWDW
        AZWBKUXEDEUYSWBUXHUYOUYPUYQSUWQUWRCJUYLUWDUXEUXIUYLVEZUWDVEZMVRVSWEUYIU
        YBUYMUWDUXGUXHUYRWNZUYIUYBUYMVQUXGUXHUYRRSTWFZUWFDEFIUXRUYLJKUAUYJUYTPW
        GWHWIWJVTWKWLWMWOUXKUYFUXOUBKUXKUWBKUEZUIZUYFUXOVUEUYFUIUXOFWPUHZEUHZUW
        DUHZUXLVUFUWGUHZULUGZUMUNZUWBVUFUWBVUFVQZUWEVUHUXNVUJUMUWBVUFUWDEWQVULU
        WHVUIUXLULUWBVUFUWGWRWSWTVUEUWBVUFXAZUYFUXOVUEVUMUIUYFUXOUXKVUDVUMUYFUX
        OUSUXKVUDVUMUIZUIZUYFDUWOUWHVJUGZUWBFXBUHZUGZFXCUHZUGZDUXRUGZEUHZUWDUHZ
        URUMUNZUXOVUOUYFVVAUWGUHZUWOUMUNZVVDVUOVVEUWOUWOUMVUOVVEVURUWGUHZVUPUWH
        ULUGZUWOVUOVVAVURUWGVUOUXGUVTVURKUEZVVAVURVQUXGVUORXDZUVTUXJVUNXEZVUOUX
        GVUPXFUEZVUDVVIVVJVUOVUPUXKUXJUWHUTUEZVUPUTUEVUNUVTUXJXGZVUNUWHVUDUWHUP
        UEZVUMUXGVUDVVORUWBFUWGKUAUYKXHWHZXIVUDVUMXJUWHXKUNZUXGVUDVUMVVQVPRUWBF
        UWGKVUFUAVUFVEZUYKXLWHXMXNZUWOUWHXOWEZXPZUXKVUDVUMXQZVUPUWBVUQFKUAVUQVE
        ZXRXSZDVURFVUSUXRKUAVUSVEZUYJXTXSZWIVUOUXGVUPUPUEXJVUPUMUNUIZVUDVVGVVHV
        QVVJVUOVUPVVTYAZVWBVUPUWBVUQFUWGKUAVWCUYKYBXSVUOUWOUWHUXJUWOXFUEZUVTVUN
        UWOYCVNZVUOUWHVUDVVOUXKVUMVVPYDYEZVUNUWHXJXAZUXKVUDVWLVUMVUDUWHXJUWBVUF
        UXGVUDUWHXJVQVULVPRUWBFUWGKVUFUAVVRUYKYFWHYIYGYHYJYKUXJUWOUWOUMUNUVTVUN
        UXJUWOUWOYLUUAVNUUBVUOVUTKUEZUYFVVFVVDUSZUSVUOUXGUVTVVIVWMVVJVVKVWDDVUR
        FVUSKUAVWEUUCXSUYEVWNUCVUTKUWFVUTVQZUYAVVFUYDVVDVWOUXTVVEUWOUMUWFVUTDUW
        GUXRYMVTVWOUYCVVCURUMVWOUYBVVBUWDUWFVUTDEUXRYMWIVTWKUUJYNUUDVUOVUPUWEUL
        UGZURUMUNUWEURVUPVJUGZUMUNVVDUXOVUOUWEURVUPVUDUWEUPUEZUXKVUMVUDUXHUWCUX
        EUEZVWRSKUXEUWBEUYSWBZUWCJUWDUXEUXIVUAXHUUEYDVUOUUFVVTUUGVUOVVCVWPURUMV
        UOVVCVUPUWCJXBUHZUGZUWDUHZVWPVUOVVBVXBUWDVUOVVBVUREUHZVXBVUOVVAVUREVWFW
        IVUOVVLVUDVXDVXBVQZVWAVWBVUBVVLVUDUIVXEVUCVUPUWBVUQVXAEFIJKUAVWCVXAVEZP
        UUHWHYOYPWIVUOUXHVWGVWSVXCVWPVQUXHVUOSXDVWHVUDVWSUXKVUMVWTYDVUPUWCVXAJU
        WDUXEUXIVXFVUAYBXSYPVTVUOUXNVWQUWEUMVUOVWQUWHUWOVJUGZUXNUXKUXJVVMVWQVXG
        VQZVUNVVNVVSUXJVWIUWOXJXAZUIUWHXFUEVWLUIVXHVVMUWOYQUWHYQUWOUWHUUIWEWEVU
        OUWHUWOVWKVWJUXJVXIUVTVUNUWOUUKVNUULUUMYRUUNUUOUVAYSUUPUXJVUKUVTVUDUYFU
        XJVUHXJVUJUMVUHXJXJUMVUHJWPUHZUWDUHZXJVUGVXJUWDUXGUXHUYRVUGVXJVQRSTVUFE
        FIJKUXEVXJUAUXIVVRVXJVEZPUUQWAUURUXHVXKXJVQSJUWDVXJVXLVUAYTVLUUSUUTUVBU
        XJUXLXFUEZVUJXJVQUXJUXLUXQXPVXMVUJUXLXJULUGXJVUIXJUXLULUXGVUIXJVQRFUWGV
        UFVVRUYKYTVLUVCUXLUVDUVEYNUVFUVGUVJUVKUVHUVIYSUWKUXPUCUXLUPUWFUXLVQZUWJ
        UXOUBKVXNUWIUXNUWEUMUWFUXLUWHULUVLYRUVMUVNYOUVOUVPYSUWMUYRUWLTUCUBAEFIU
        WGUWDJKUAUYKVUAPQRSUVQUVRUVS $.
    $}

    $( A linear operator is continuous iff it is bounded.  Theorem 2.7-9(a) of
       [Kreyszig] p. 97.  (Contributed by NM, 18-Dec-2007.)  (Revised by Mario
       Carneiro, 10-Jan-2014.)  (New usage is discouraged.) $)
    blocni $p |- ( T e. ( J Cn K ) <-> T e. B ) $=
      ( wcel cfv vx vw vz vy ccn co cn0v cba ccnp eqid nvzcl ax-mp cxmet ctopon
      cnv imsmet metxmet mopntopon toponunii cncnpi mpan2 blocnilem sylancr c0o
      cmet eleq1 wne wa wf cv clt wbr wi wral crp wrex cnmoo cdiv simprr cr cc0
      nmblore mp3an12 nmlnogt0 mp3an biimpi anim12i elrp sylibr adantr rpdivcld
      wb simprl metcl mp3an1 sylan simplrr rpred ad2antrr ltmuldiv2 syl3anc cle
      cmul id ad2ant2r blometi 3expa ffvelcdmi syl2an remulcl adantllr adantlrr
      anassrs lelttr mpand sylbird ralrimiva breq2 rspceaimv syl2anc ralrimivva
      lnof jctil metcn csn cxp wceq 0ofval cnconst2 eqeltri a1i pm2.61ne impbii
      mp2an ) DFGUEUFZSZDASZYPEUGTZEUHTZSZDYRFGUIUFTSZYQEUOSZYTPEYSYRYSUJZYRUJU
      KULZYPYTUUAUUDYRDFGYSYSFBYSUMTSZFYSUNTSZBYSVETSZUUEUUBUUGPBEYSUUCJUPULZBY
      SUQULZBFYSLURULZUSUTVAABCYRDEFGHIYSJKLMNOPQRUUCVBVCYQYPEIVDUFZYOSZDUUKDUU
      KYOVFYQDUUKVGZVHZYSIUHTZDVIZUAVJZUBVJZBUFZUCVJZVKVLZUUQDTZUURDTZCUFZUDVJZ
      VKVLZVMUBYSVNUCVOVPZUDVOVNUAYSVNZVHZYPUUNUVHUUPUUNUVGUAUDYSVOUUNUUQYSSZUV
      EVOSZVHZVHZUVEDEIVQUFZTZVRUFZVOSUUSUVPVKVLZUVFVMZUBYSVNUVGUVMUVEUVOUUNUVJ
      UVKVSUUNUVOVOSZUVLUUNUVOVTSZWAUVOVKVLZVHZUVSYQUVTUUMUWAUUBIUOSZYQUVTPQADE
      UVNIYSUUOUUCUUOUJZUVNUJZOWBWCZUUMUWAUUBUWCDHSZUUMUWAWLPQRDEHUVNIUUKUWEUUK
      UJZNWDWEWFWGZUVOWHWIWJWKUVMUVRUBYSUVMUURYSSZVHZUVQUVOUUSXCUFZUVEVKVLZUVFU
      WKUUSVTSZUVEVTSZUWBUWMUVQWLUVMUVJUWJUWNUUNUVJUVKWMZUUGUVJUWJUWNUUHUUQUURB
      YSWNWOZWPUWKUVEUUNUVJUVKUWJWQWRZUUNUWBUVLUWJUWIWSUUSUVEUVOWTXAUWKUVDUWLXB
      VLZUWMUVFUVMYQUVJVHZUWJUWSYQUVJUWTUUMUVKUWTXDXEYQUVJUWJUWSABCUUQUURDEUVNI
      YSUUOUUCUWDJKUWEOPQXFXGWPUWKUVDVTSZUWLVTSZUWOUWSUWMVHUVFVMUVMUVJUWJUXAUWP
      UVJUVBUUOSZUVCUUOSZUXAUWJYSUUOUUQDUUBUWCUWGUUPPQRDEHIYSUUOUUCUWDNYBWEZXHY
      SUUOUURDUXEXHCUUOVETSZUXCUXDUXAUWCUXFQCIUUOUWDKUPULZUVBUVCCUUOWNWOXIWPUUN
      UVJUWJUXBUVKYQUVJUWJUXBUUMYQUVJUWJUXBYQUVTUWNUXBUVJUWJVHUWFUWQUVOUUSXJXIX
      MXKXLUWRUVDUWLUVEXNXAXOXPXQUVAUVQUVFUCUBUVPVOYSUUTUVPUUSVKXRXSXTYAUXEYCUU
      ECUUOUMTSZYPUVIWLUUIUXFUXHUXGCUUOUQULZUAUDUCUBBCDFGYSUUOLMYDYNWIUULYQUUKY
      SIUGTZYEYFZYOUUBUWCUUKUXKYGPQEUUKIYSUXJUUCUXJUJZUWHYHYNUUFGUUOUNTSZUXJUUO
      SZUXKYOSUUJUXHUXMUXICGUUOMURULUWCUXNQIUUOUXJUWDUXLUKULUXJFGYSUUOYIWEYJYKY
      LYM $.

    ${
      lnocni.1 $e |- X = ( BaseSet ` U ) $.
      $( If a linear operator is continuous at any point, it is continuous
         everywhere.  Theorem 2.7-9(b) of [Kreyszig] p. 97.  (Contributed by
         NM, 18-Dec-2007.)  (New usage is discouraged.) $)
      lnocni $p |- ( ( P e. X /\ T e. ( ( J CnP K ) ` P ) ) ->
                T e. ( J Cn K ) ) $=
        ( wcel ccnp co cfv wa ccn blocnilem blocni sylibr ) DKUBEDGHUCUDUEUBUFE
        AUBEGHUGUDUBABCDEFGHIJKLMNOPQRSTUAUHABCEFGHIJLMNOPQRSTUIUJ $.
    $}
  $}

  ${
    blocn.8 $e |- C = ( IndMet ` U ) $.
    blocn.d $e |- D = ( IndMet ` W ) $.
    blocn.j $e |- J = ( MetOpen ` C ) $.
    blocn.k $e |- K = ( MetOpen ` D ) $.
    blocn.5 $e |- B = ( U BLnOp W ) $.
    blocn.u $e |- U e. NrmCVec $.
    blocn.w $e |- W e. NrmCVec $.
    ${
      blocn.4 $e |- L = ( U LnOp W ) $.
      $( A linear operator is continuous iff it is bounded.  Theorem 2.7-9(a)
         of [Kreyszig] p. 97.  (Contributed by NM, 25-Dec-2007.)
         (New usage is discouraged.) $)
      blocn $p |- ( T e. L -> ( T e. ( J Cn K ) <-> T e. B ) ) $=
        ( wcel co wb ccn c0o cif wceq eleq1 bibi12d cnv eqid 0lno elimel blocni
        mp2an dedth ) DHRZDFGUASZRZDARZTUNDEIUBSZUCZUORZUSARZTDURDUSUDUPUTUQVAD
        USUOUEDUSAUEUFABCUSEFGHIJKLMQNOPDURHEUGRIUGRURHROPEHIURURUHQUIULUJUKUM
        $.
    $}

    $( A bounded linear operator is continuous.  (Contributed by NM,
       25-Dec-2007.)  (New usage is discouraged.) $)
    blocn2 $p |- ( T e. B -> T e. ( J Cn K ) ) $=
      ( clno co wcel ccn cnv eqid bloln mp3an12 blocn biimprd mpcom ) DEHPQZRZD
      ARZDFGSQRZETRHTRUIUHNOADEUGHUGUAZMUBUCUHUJUIABCDEFGUGHIJKLMNOUKUDUEUF $.
  $}

  ${
    $d u w P $.  $d s t u w x y U $.  $d s t u w x y W $.  $d s t u w x X $.
    $d u w Q $.  $d s t u w y Y $.
    ajfval.1 $e |- X = ( BaseSet ` U ) $.
    ajfval.2 $e |- Y = ( BaseSet ` W ) $.
    ajfval.3 $e |- P = ( .iOLD ` U ) $.
    ajfval.4 $e |- Q = ( .iOLD ` W ) $.
    ajfval.5 $e |- A = ( U adj W ) $.
    $( The adjoint function.  (Contributed by NM, 25-Jan-2008.)  (Revised by
       Mario Carneiro, 16-Nov-2013.)  (New usage is discouraged.) $)
    ajfval $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> A =
     { <. t , s >. | ( t : X --> Y /\ s : Y --> X /\ A. x e. X A. y e. Y
    ( ( t ` x ) Q y ) = ( x P ( s ` y ) ) ) } ) $=
      ( co cv cfv cba vu vw cnv wcel wa caj wf wceq wral w3a copab cdip eqtr4di
      fveq2 feq2d feq3d oveqd eqeq2d ralbidv raleqbidv 3anbi123d opabbidv df-aj
      eqeq1d cmap cxp ovex xpex fvexi anbi12i biimpri 3adant3 ssopab2i sseqtrri
      elmap df-xp ssexi ovmpo eqtrid ) GUCUDHUCUDUEDGHUFQIJCRZUGZJIKRZUGZARZVTS
      ZBRZFQZWDWFWBSZEQZUHZBJUIZAIUIZUJZCKUKZPUAUBGHUCUCUARZTSZUBRZTSZVTUGZWRWP
      WBUGZWEWFWQULSZQZWDWHWOULSZQZUHZBWRUIZAWPUIZUJZCKUKWNUFIWRVTUGZWRIWBUGZXB
      WIUHZBWRUIZAIUIZUJZCKUKWOGUHZXHXNCKXOWSXIWTXJXGXMXOWPIWRVTXOWPGTSIWOGTUNL
      UMZUOXOWPIWBWRXPUPXOXFXLAWPIXPXOXEXKBWRXOXDWIXBXOXCEWDWHXOXCGULSEWOGULUNN
      UMUQURUSUTVAVBWQHUHZXNWMCKXQXIWAXJWCXMWLXQWRJVTIXQWRHTSJWQHTUNMUMZUPXQWRJ
      IWBXRUOXQXLWKAIXQXKWJBWRJXRXQXBWGWIXQXAFWEWFXQXAHULSFWQHULUNOUMUQVDUTUSVA
      VBABUBUACKVCWNJIVEQZIJVEQZVFZXSXTJIVEVGIJVEVGVHWNVTXSUDZWBXTUDZUEZCKUKYAW
      MYDCKWAWCYDWLYDWAWCUEYBWAYCWCJIVTJHTMVIZIGTLVIZVOIJWBYFYEVOVJVKVLVMCKXSXT
      VPVNVQVRVS $.
  $}

  ${
    $d t u A $.  $d t T $.  $d t u U $.
    hmoval.8 $e |- H = ( HmOp ` U ) $.
    hmoval.9 $e |- A = ( U adj U ) $.
    $( The set of Hermitian (self-adjoint) operators on a normed complex vector
       space.  (Contributed by NM, 26-Jan-2008.)  (Revised by Mario Carneiro,
       16-Nov-2013.)  (New usage is discouraged.) $)
    hmoval $p |- ( U e. NrmCVec -> H = { t e. dom A | ( A ` t ) = t } ) $=
      ( vu cnv wcel chmo cfv cv wceq cdm crab caj co oveq12 anidms eqtr4di ovex
      dmeqd fveq1d eqeq1d rabeqbidv df-hmo cvv eqeltri dmex rabex fvmpt eqtrid
      ) CHIDCJKALZBKZUMMZABNZOZEGCUMGLZURPQZKZUMMZAUSNZOUQHJURCMZVAUOAVBUPVCUSB
      VCUSCCPQZBVCUSVDMURCURCPRSFTZUBVCUTUNUMVCUMUSBVEUCUDUEGAUFUOAUPBBVDUGFCCP
      UAUHUIUJUKUL $.

    $( The predicate "is a hermitian operator."  (Contributed by NM,
       26-Jan-2008.)  (New usage is discouraged.) $)
    ishmo $p |- ( U e. NrmCVec ->
      ( T e. H <-> ( T e. dom A /\ ( A ` T ) = T ) ) ) $=
      ( vt cnv wcel cv cfv wceq cdm crab wa hmoval eleq2d fveq2 id eqeq12d
      elrab bitrdi ) CHIZBDIBGJZAKZUDLZGAMZNZIBUGIBAKZBLZOUCDUHBGACDEFPQUFUJGBU
      GUDBLZUEUIUDBUDBARUKSTUAUB $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Inner product (pre-Hilbert) spaces
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definition and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c CPreHilOLD $.

  $( Extend class notation with the class of all complex inner product spaces
     (also called pre-Hilbert spaces). $)
  ccphlo $a class CPreHilOLD $.

  ${
    $d g n s x y $.
    $( Define the class of all complex inner product spaces.  An inner product
       space is a normed vector space whose norm satisfies the parallelogram
       law (a property that induces an inner product).  Based on Exercise 4(b)
       of [ReedSimon] p. 63.  The vector operation is ` g ` , the scalar
       product is ` s ` , and the norm is ` n ` .  An inner product space is
       also called a pre-Hilbert space.  (Contributed by NM, 2-Apr-2007.)
       (New usage is discouraged.) $)
    df-ph $a |- CPreHilOLD = ( NrmCVec i^i { <. <. g , s >. , n >. |
          A. x e. ran g A. y e. ran g
       ( ( ( n ` ( x g y ) ) ^ 2 ) + ( ( n ` ( x g ( -u 1 s y ) ) ) ^ 2 ) ) =
        ( 2 x. ( ( ( n ` x ) ^ 2 ) + ( ( n ` y ) ^ 2 ) ) ) } ) $.

    $( Every complex inner product space is a normed complex vector space.
       (Contributed by NM, 2-Apr-2007.)  (New usage is discouraged.) $)
    phnv $p |- ( U e. CPreHilOLD -> U e. NrmCVec ) $=
      ( vx vy vg vn vs ccphlo cnv cv co cfv c2 cexp c1 cneg caddc cmul wceq crn
      wral coprab cin df-ph inss1 eqsstri sseli ) GHAGHBIZCIZDIZJEIZKLMJUGNOUHF
      IJUIJUJKLMJPJLUGUJKLMJUHUJKLMJPJQJRCUISZTBUKTDFEUAZUBHBCDEFUCHULUDUEUF $.

    $( The class of all complex inner product spaces is a relation.
       (Contributed by NM, 2-Apr-2007.)  (New usage is discouraged.) $)
    phrel $p |- Rel CPreHilOLD $=
      ( vx ccphlo cnv wss wrel cv phnv ssriv nvrel relss mp2 ) BCDCEBEABCAFGHIB
      CJK $.
  $}

  ${
    phnvi.1 $e |- U e. CPreHilOLD $.
    $( Every complex inner product space is a normed complex vector space.
       (Contributed by NM, 20-Nov-2007.)  (New usage is discouraged.) $)
    phnvi $p |- U e. NrmCVec $=
      ( ccphlo wcel cnv phnv ax-mp ) ACDAEDBAFG $.
  $}

  ${
    $d g n s x y G $.  $d g n s x y N $.  $d g n s x y S $.  $d g n s x y X $.
    isphg.1 $e |- X = ran G $.
    $( The predicate "is a complex inner product space."  An inner product
       space is a normed vector space whose norm satisfies the parallelogram
       law.  The vector (group) addition operation is ` G ` , the scalar
       product is ` S ` , and the norm is ` N ` .  An inner product space is
       also called a pre-Hilbert space.  (Contributed by NM, 2-Apr-2007.)
       (New usage is discouraged.) $)
    isphg $p |- ( ( G e. A /\ S e. B /\ N e. C ) ->
  ( <. <. G , S >. , N >. e. CPreHilOLD <-> ( <. <. G , S >. , N >. e. NrmCVec
        /\
          A. x e. X A. y e. X
      ( ( ( N ` ( x G y ) ) ^ 2 ) + ( ( N ` ( x G ( -u 1 S y ) ) ) ^ 2 ) ) =
        ( 2 x. ( ( ( N ` x ) ^ 2 ) + ( ( N ` y ) ^ 2 ) ) ) ) ) ) $=
      ( wcel cv co cfv c2 cexp caddc wceq wral oveq1d vg vn cop ccphlo cnv cneg
      vs c1 cmul crn coprab wa w3a df-ph elin2 rneq eqtr4di oveq fveq2d oveq12d
      eqeq1d raleqbidv oveq2d 2ralbidv fveq1 eqeq12d eloprabg anbi2d bitrid ) G
      FUCHUCZUDKVJUEKZVJALZBLZUALZMZUBLZNZOPMZVLUHUFZVMUGLZMZVNMZVPNZOPMZQMZOVL
      VPNZOPMZVMVPNZOPMZQMZUIMZRZBVNUJZSZAWMSZUAUGUBUKZKZULGCKFDKHEKUMZVKVLVMGM
      ZHNZOPMZVLVSVMFMZGMZHNZOPMZQMZOVLHNZOPMZVMHNZOPMZQMZUIMZRZBISAISZULVJUEWP
      UDABUAUBUGUNUOWRWQXNVKWOWSVPNZOPMZVLWAGMZVPNZOPMZQMZWKRZBISZAISXPXCVPNZOP
      MZQMZWKRZBISAISXNUAUGUBGFHCDEVNGRZWNYBAWMIYGWMGUJIVNGUPJUQZYGWLYABWMIYHYG
      WEXTWKYGVRXPWDXSQYGVQXOOPYGVOWSVPVLVMVNGURUSTYGWCXROPYGWBXQVPVLWAVNGURUST
      UTVAVBVBVTFRZYAYFABIIYIXTYEWKYIXSYDXPQYIXRYCOPYIXQXCVPYIWAXBVLGVSVMVTFURV
      CUSTVCVAVDVPHRZYFXMABIIYJYEXFWKXLYJXPXAYDXEQYJXOWTOPWSVPHVETYJYCXDOPXCVPH
      VETUTYJWJXKOUIYJWGXHWIXJQYJWFXGOPVLVPHVETYJWHXIOPVMVPHVETUTVCVFVDVGVHVI
      $.
  $}

  ${
    phop.2 $e |- G = ( +v ` U ) $.
    phop.4 $e |- S = ( .sOLD ` U ) $.
    phop.6 $e |- N = ( normCV ` U ) $.
    $( A complex inner product space in terms of ordered pair components.
       (Contributed by NM, 2-Apr-2007.)  (New usage is discouraged.) $)
    phop $p |- ( U e. CPreHilOLD -> U = <. <. G , S >. , N >. ) $=
      ( ccphlo wcel c1st cfv c2nd cop wrel wceq phrel 1st2nd mpan nmcvfval cvc
      opeq2i cnv phnv eqid nvvc vcrel vafval smfval opeq12i eqtr4di 3syl opeq1d
      eqtr3id eqtrd ) BHIZBBJKZBLKZMZCAMZDMZHNUOBUROPBHQRUOURUPDMUTDUQUPBDGSUAU
      OUPUSDUOBUBIUPTIZUPUSOBUCBUPUPUDUEVAUPUPJKZUPLKZMZUSTNVAUPVDOUFUPTQRCVBAV
      CBCEUGABFUHUIUJUKULUMUN $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Examples of pre-Hilbert spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y $.
    cncph.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The set of complex numbers is an inner product (pre-Hilbert) space.
       (Contributed by Steve Rodriguez, 28-Apr-2007.)  (Revised by Mario
       Carneiro, 7-Nov-2013.)  (New usage is discouraged.) $)
    cncph $p |- U e. CPreHilOLD $=
      ( vx vy caddc cmul cop cabs ccphlo wcel cv co c2 cexp wceq cc eqtrd recnd
      cfv cvv cnv c1 cneg wral eqid cnnv cmin mulm1 adantl oveq2d negsub fveq2d
      wa oveq1d ccj cre sqabsadd sqabssub oveq12d abscl sqcld addcl syl2an cjcl
      2cn mulcl sylan2 recl syl sylancr ppncand 2times eqcomd rgen2 addex mulex
      wb cr wf absf fex mp2an cablo cgr cnaddabloOLD ablogrpo ax-mp cxp ax-addf
      cnex fdmi grporn isphg mp3an mpbir2an eqeltri ) AEFGHGZIBWQIJZWQUAJZCKZDK
      ZELHSMNLZWTUBUCXAFLZELZHSZMNLZELZMWTHSZMNLZXAHSZMNLZELZFLZOZDPUDCPUDZWQWQ
      UEUFXNCDPPWTPJZXAPJZUMZXGXBWTXAUGLZHSZMNLZELZXMXRXFYAXBEXRXEXTMNXRXDXSHXR
      XDWTXAUCZELXSXRXCYCWTEXQXCYCOXPXAUHUIUJWTXAUKQULUNUJXRYBXLXLELZXMXRYBXLMW
      TXAUOSZFLZUPSZFLZELZXLYHUGLZELYDXRXBYIYAYJEWTXAUQWTXAURUSXRXLYHXLXPXIPJXK
      PJXLPJZXQXPXHXPXHWTUTRVAXQXJXQXJXAUTRVAXIXKVBVCZXRMPJYGPJZYHPJVEXRYFPJZYM
      XQXPYEPJYNXAVDWTYEVFVGYNYGYFVHRVIMYGVFVJYLVKQXRYKYDXMOYLYKXMYDXLVLVMVIQQV
      NETJFTJHTJZWRWSXOUMVQVOVPPVRHVSPTJYOVTWJPVRTHWAWBCDTTTFEHPEPEWCJEWDJWEEWF
      WGPPWHPEWIWKWLWMWNWOWP $.
  $}

  ${
    elimph.1 $e |- X = ( BaseSet ` U ) $.
    elimph.5 $e |- Z = ( 0vec ` U ) $.
    elimph.6 $e |- U e. CPreHilOLD $.
    $( TODO - use elimnvOLD ? $)
    $( Hypothesis elimination lemma for complex inner product spaces to assist
       weak deduction theorem.  (Contributed by NM, 27-Apr-2007.)
       (New usage is discouraged.) $)
    elimph $p |- if ( A e. X , A , Z ) e. X $=
      ( phnvi elimnv ) ABCDEFBGHI $.
  $}

  $( TODO - use elimnvu ? $)
  $( Hypothesis elimination lemma for complex inner product spaces to assist
     weak deduction theorem.  (Contributed by NM, 6-May-2007.)
     (New usage is discouraged.) $)
  elimphu $p |- if ( U e. CPreHilOLD , U , <. <. + , x. >. , abs >. )
                 e. CPreHilOLD $=
    ( caddc cmul cop cabs ccphlo eqid cncph elimel ) ABCDEDZFJJGHI $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Properties of pre-Hilbert spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y A $.  $d y B $.  $d x y G $.  $d x y M $.  $d x y N $.  $d x y U $.
    $d x y X $.
    isph.1 $e |- X = ( BaseSet ` U ) $.
    isph.2 $e |- G = ( +v ` U ) $.
    isph.3 $e |- M = ( -v ` U ) $.
    isph.6 $e |- N = ( normCV ` U ) $.
    $( The predicate "is an inner product space."  (Contributed by NM,
       1-Feb-2008.)  (New usage is discouraged.) $)
    isph $p |- ( U e. CPreHilOLD <-> ( U e. NrmCVec /\ A. x e. X A. y e. X
      ( ( ( N ` ( x G y ) ) ^ 2 ) + ( ( N ` ( x M y ) ) ^ 2 ) ) = (
      2 x. ( ( ( N ` x ) ^ 2 ) + ( ( N ` y ) ^ 2 ) ) ) ) ) $=
      ( wcel co cfv c2 cexp caddc wceq wa cvv ccphlo cnv cmul wral phnv cns cop
      cv wb eqid nvop eleq1 cneg cpv fvexi fvex cnmcv bafval isphg mp3an nvmval
      c1 3expa fveq2d oveq1d oveq2d eqeq1d ralbidva pm5.32i anbi1d bitrid bitrd
      bitr2id syl bianabs biadanii ) CUALZCUBLZAUHZBUHZDMFNOPMZVSVTEMZFNZOPMZQM
      ZOVSFNOPMVTFNOPMQMUCMZRZBGUDZAGUDZCUEVRVQWIVRCDCUFNZUGFUGZRZVQVRWISZUIWJC
      DFIWJUJZKUKWLVQWKUALZWMCWKUAULWOWKUBLZWAVSVBUMVTWJMDMZFNZOPMZQMZWFRZBGUDZ
      AGUDZSZWLWMDTLWJTLFTLWOXDUIDCUNIUOCUFUPFCUQKUOABTTTWJDFGCDGHIURUSUTWMVRXC
      SWLXDVRWIXCVRWHXBAGVRVSGLZSZWGXABGXFVTGLZSZWEWTWFXHWDWSWAQXHWCWROPXHWBWQF
      VRXEXGWBWQRVSVTWJCDEGHIWNJVAVCVDVEVFVGVHVHVIWLVRWPXCCWKUBULVJVMVKVLVNVOVP
      $.

    $( The parallelogram law for an inner product space.  (Contributed by NM,
       2-Apr-2007.)  (New usage is discouraged.) $)
    phpar2 $p |- ( ( U e. CPreHilOLD /\ A e. X /\ B e. X ) ->
      ( ( ( N ` ( A G B ) ) ^ 2 ) + ( ( N ` ( A M B ) ) ^ 2 ) ) =
        ( 2 x. ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) ) $=
      ( vx co cfv c2 cexp caddc cmul wceq oveq1d vy ccphlo wcel w3a cv wral cnv
      isph simprbi 3ad2ant1 wi fvoveq1 oveq12d fveq2 oveq2d oveq2 fveq2d rspc2v
      eqeq12d 3adant1 mpd ) CUBUCZAGUCZBGUCZUDLUEZUAUEZDMFNZOPMZVEVFEMFNZOPMZQM
      ZOVEFNZOPMZVFFNZOPMZQMZRMZSZUAGUFLGUFZABDMZFNZOPMZABEMZFNZOPMZQMZOAFNZOPM
      ZBFNZOPMZQMZRMZSZVBVCVSVDVBCUGUCVSLUACDEFGHIJKUHUIUJVCVDVSWMUKVBVRWMAVFDM
      ZFNZOPMZAVFEMZFNZOPMZQMZOWHVOQMZRMZSLUAABGGVEASZVKWTVQXBXCVHWPVJWSQXCVGWO
      OPVEAVFFDULTXCVIWROPVEAVFFEULTUMXCVPXAORXCVMWHVOQXCVLWGOPVEAFUNTTUOUSVFBS
      ZWTWFXBWLXDWPWBWSWEQXDWOWAOPXDWNVTFVFBADUPUQTXDWRWDOPXDWQWCFVFBAEUPUQTUMX
      DXAWKORXDVOWJWHQXDVNWIOPVFBFUNTUOUOUSURUTVA $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y G $.  $d x y N $.  $d x y S $.  $d x y X $.
    phpar.1 $e |- X = ( BaseSet ` U ) $.
    phpar.2 $e |- G = ( +v ` U ) $.
    phpar.4 $e |- S = ( .sOLD ` U ) $.
    phpar.6 $e |- N = ( normCV ` U ) $.
    $( The parallelogram law for an inner product space.  (Contributed by NM,
       2-Apr-2007.)  (New usage is discouraged.) $)
    phpar $p |- ( ( U e. CPreHilOLD /\ A e. X /\ B e. X ) ->
      ( ( ( N ` ( A G B ) ) ^ 2 ) + ( ( N ` ( A G ( -u 1 S B ) ) ) ^ 2 ) ) =
        ( 2 x. ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) ) $=
      ( wcel co cfv c2 cexp caddc cmul cvv oveq1d vx vy ccphlo w3a cv cneg wceq
      c1 wral cop cpv fvexi cns cnmcv 3pm3.2i phop eleq1d bafval isphg simplbda
      ibi sylancr 3ad2ant1 wi fvoveq1 oveq12d fveq2 oveq2d eqeq12d oveq2 fveq2d
      cnv rspc2v 3adant1 mpd ) DUCLZAGLZBGLZUDUAUEZUBUEZEMFNZOPMZVSUHUFZVTCMZEM
      FNZOPMZQMZOVSFNZOPMZVTFNZOPMZQMZRMZUGZUBGUIUAGUIZABEMZFNZOPMZAWCBCMZEMZFN
      ZOPMZQMZOAFNZOPMZBFNZOPMZQMZRMZUGZVPVQWOVRVPESLZCSLZFSLZUDZECUJFUJZUCLZWO
      XKXLXMEDUKIULCDUMJULFDUNKULUOVPXPVPDXOUCCDEFIJKUPUQVAXNXPXOVLLWOUAUBSSSCE
      FGDEGHIURUSUTVBVCVQVRWOXJVDVPWNXJAVTEMZFNZOPMZAWDEMZFNZOPMZQMZOXEWKQMZRMZ
      UGUAUBABGGVSAUGZWGYCWMYEYFWBXSWFYBQYFWAXROPVSAVTFEVETYFWEYAOPVSAWDFEVETVF
      YFWLYDORYFWIXEWKQYFWHXDOPVSAFVGTTVHVIVTBUGZYCXCYEXIYGXSWRYBXBQYGXRWQOPYGX
      QWPFVTBAEVJVKTYGYAXAOPYGXTWTFYGWDWSAEVTBWCCVJVHVKTVFYGYDXHORYGWKXGXEQYGWJ
      XFOPVTBFVGTVHVHVIVMVNVO $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y G $.  $d x y N $.  $d x y S $.  $d x y X $.
    ip1i.1 $e |- X = ( BaseSet ` U ) $.
    ip1i.2 $e |- G = ( +v ` U ) $.
    ip1i.4 $e |- S = ( .sOLD ` U ) $.
    ip1i.7 $e |- P = ( .iOLD ` U ) $.
    ip1i.9 $e |- U e. CPreHilOLD $.
    ${
      ip1i.a $e |- A e. X $.
      ip1i.b $e |- B e. X $.
      ip1i.c $e |- C e. X $.
      ${
        ip1i.6 $e |- N = ( normCV ` U ) $.
        ip0i.j $e |- J e. CC $.
        $( A slight variant of Equation 6.46 of [Ponnusamy] p. 362, where ` J `
           is either 1 or -1 to represent +-1.  (Contributed by NM,
           23-Apr-2007.)  (New usage is discouraged.) $)
        ip0i $p |- ( ( ( ( N ` ( ( A G B ) G ( J S C ) ) ) ^ 2 ) -
             ( ( N ` ( ( A G B ) G ( -u J S C ) ) ) ^ 2 ) ) +
             ( ( ( N ` ( ( A G ( -u 1 S B ) ) G ( J S C ) ) ) ^ 2 ) -
           ( ( N ` ( ( A G ( -u 1 S B ) ) G ( -u J S C ) ) ) ^ 2 ) ) ) =
                ( 2 x. ( ( ( N ` ( A G ( J S C ) ) ) ^ 2 ) -
                ( ( N ` ( A G ( -u J S C ) ) ) ^ 2 ) ) ) $=
          ( c2 co cfv cexp cneg cmin cmul caddc c1 2cn phnvi cnv cc nvscl mp3an
          wcel nvgcl nvcli recni sqcli negcli subdii wceq mulcli pnpcan2 eqtr4i
          cablo w3a c1st cvc eqid nvvc vafval vcablo mp2b 3pm3.2i bafval ablo32
          fveq2i oveq1i neg1cn oveq12i ccphlo adddii 3eqtri addsub4i 3eqtr2ri
          mp2an phpar ) UAAHCEUBZGUBZIUCZUAUDUBZAHUEZCEUBZGUBZIUCZUAUDUBZUFUBUG
          UBZUAWMUGUBZUABIUCZUAUDUBZUGUBZUHUBZUAWRUGUBZXCUHUBZUFUBZABGUBZWJGUBZ
          IUCZUAUDUBZAUIUEZBEUBZGUBZWJGUBZIUCZUAUDUBZUHUBZXHWOGUBZIUCZUAUDUBZXN
          WOGUBZIUCZUAUDUBZUHUBZUFUBXKYAUFUBXQYDUFUBUHUBWSWTXEUFUBZXGUAWMWRUJWL
          WLWKFIJKSFOUKZFULUPZAJUPZWJJUPZWKJUPZYGPYHHUMUPCJUPZYJYGTRHCEFJKMUNUO
          ZAWJFGJKLUQUOZURUSUTZWQWQWPFIJKSYGYHYIWOJUPZWPJUPZYGPYHWNUMUPYLYPYGHT
          VARWNCEFJKMUNUOZAWOFGJKLUQUOZURUSUTZVBWTUMUPXEUMUPXCUMUPXGYFVCUAWMUJY
          OVDUAWRUJYTVDUAXBUJXAXABFIJKSYGQURUSUTZVDWTXEXCVEUOVFXRXDYEXFUFXRWKBG
          UBZIUCZUAUDUBZWKXMGUBZIUCZUAUDUBZUHUBZUAWMXBUHUBUGUBZXDXKUUDXQUUGUHXJ
          UUCUAUDXIUUBIGVGUPZYIBJUPZYJVHXIUUBVCYHFVIUCZVJUPUUJYGFUULUULVKVLGUUL
          FGLVMVNVOZYIUUKYJPQYMVPABWJGJFGJKLVQZVRWHVSVTXPUUFUAUDXOUUEIUUJYIXMJU
          PZYJVHXOUUEVCUUMYIUUOYJPYHXLUMUPUUKUUOYGWAQXLBEFJKMUNUOZYMVPAXMWJGJUU
          NVRWHVSVTWBFWCUPZYKUUKUUHUUIVCOYNQWKBEFGIJKLMSWIUOUAWMXBUJYOUUAWDWEYE
          WPBGUBZIUCZUAUDUBZWPXMGUBZIUCZUAUDUBZUHUBZUAWRXBUHUBUGUBZXFYAUUTYDUVC
          UHXTUUSUAUDXSUURIUUJYIUUKYPVHXSUURVCUUMYIUUKYPPQYRVPABWOGJUUNVRWHVSVT
          YCUVBUAUDYBUVAIUUJYIUUOYPVHYBUVAVCUUMYIUUOYPPUUPYRVPAXMWOGJUUNVRWHVSV
          TWBUUQYQUUKUVDUVEVCOYSQWPBEFGIJKLMSWIUOUAWRXBUJYTUUAWDWEWBXKXQYAYDXJX
          JXIFIJKSYGYHXHJUPZYJXIJUPYGYHYIUUKUVFYGPQABFGJKLUQUOZYMXHWJFGJKLUQUOU
          RUSUTXPXPXOFIJKSYGYHXNJUPZYJXOJUPYGYHYIUUOUVHYGPUUPAXMFGJKLUQUOZYMXNW
          JFGJKLUQUOURUSUTXTXTXSFIJKSYGYHUVFYPXSJUPYGUVGYRXHWOFGJKLUQUOURUSUTYC
          YCYBFIJKSYGYHUVHYPYBJUPYGUVIYRXNWOFGJKLUQUOURUSUTWFWG $.

        $( Lemma for ~ ip1i .  (Contributed by NM, 21-Apr-2007.)
           (New usage is discouraged.) $)
        ip1ilem $p |- ( ( ( A G B ) P C ) +
                         ( ( A G ( -u 1 S B ) ) P C ) ) = ( 2 x. ( A P C ) ) $=
          ( c4 co c1 cneg caddc cmul cdiv c2 cfv cexp cmin ci wcel wceq 4ipval2
          cnv phnvi mp3an oveq2i 2cn 4cn dipcl mul12i nvgcl nvcli resqcli recni
          cc ax-1cn negcli nvscl subcli ax-icn mulcli adddii nvsid mp2an fveq2i
          ip0i oveq1i oveq12i 3eqtr3i eqtr4i eqtr2i 3eqtri 3eqtr3ri addcli 4ne0
          add4i divcan3i ) UAABGUBZCDUBZAUCUDZBEUBZGUBZCDUBZUEUBZUFUBZUAUGUBUAU
          HACDUBZUFUBZUFUBZUAUGUBWQWTWRXAUAUGUHUAWSUFUBZUFUBUHACGUBZIUIZUHUJUBZ
          AWMCEUBZGUBZIUIZUHUJUBZUKUBZULAULCEUBZGUBZIUIZUHUJUBZAULUDZCEUBZGUBZI
          UIZUHUJUBZUKUBZUFUBZUEUBZUFUBZXAWRXBYBUHUFFUPUMZAJUMZCJUMZXBYBUNFOUQZ
          PRACDEFGIJKLMSNUOURUSUHUAWSUTVAYDYEYFWSVHUMYGPRACDFJKNVBURZVCYCWKCGUB
          ZIUIZUHUJUBZWKXFGUBZIUIZUHUJUBZUKUBZWOCGUBZIUIZUHUJUBZWOXFGUBZIUIZUHU
          JUBZUKUBZUEUBZULWKXKGUBZIUIZUHUJUBZWKXPGUBZIUIZUHUJUBZUKUBZUFUBZULWOX
          KGUBZIUIZUHUJUBZWOXPGUBZIUIZUHUJUBZUKUBZUFUBZUEUBZUEUBZYOUUKUEUBZUUBU
          USUEUBZUEUBZWRYCUHXJUFUBZUHYAUFUBZUEUBUVAUHXJYAUTXEXIXEXDXCFIJKSYGYDY
          EYFXCJUMYGPRACFGJKLVDURVEVFVGXIXHXGFIJKSYGYDYEXFJUMZXGJUMYGPYDWMVHUMZ
          YFUVGYGUCVIVJZRWMCEFJKMVKURZAXFFGJKLVDURVEVFVGVLULXTVMXNXSXNXMXLFIJKS
          YGYDYEXKJUMZXLJUMYGPYDULVHUMYFUVKYGVMRULCEFJKMVKURZAXKFGJKLVDURVEVFVG
          XSXRXQFIJKSYGYDYEXPJUMZXQJUMYGPYDXOVHUMYFUVMYGULVMVJRXOCEFJKMVKURZAXP
          FGJKLVDURVEVFVGVLZVNVOUUCUVEUUTUVFUEWKUCCEUBZGUBZIUIZUHUJUBZYNUKUBZWO
          UVPGUBZIUIZUHUJUBZUUAUKUBZUEUBUHAUVPGUBZIUIZUHUJUBZXIUKUBZUFUBUUCUVEA
          BCDEFGUCIJKLMNOPQRSVIVSUVTYOUWDUUBUEUVSYKYNUKUVRYJUHUJUVQYIIUVPCWKGYD
          YFUVPCUNYGRCEFJKMVPVQZUSVRVTVTUWCYRUUAUKUWBYQUHUJUWAYPIUVPCWOGUWIUSVR
          VTVTWAUWHXJUHUFUWGXEXIUKUWFXDUHUJUWEXCIUVPCAGUWIUSVRVTVTUSWBULUUJUURU
          EUBZUFUBULUHXTUFUBZUFUBUUTUVFUWJUWKULUFABCDEFGULIJKLMNOPQRSVMVSUSULUU
          JUURVMUUFUUIUUFUUEUUDFIJKSYGYDWKJUMZUVKUUDJUMYGYDYEBJUMZUWLYGPQABFGJK
          LVDURZUVLWKXKFGJKLVDURVEVFVGUUIUUHUUGFIJKSYGYDUWLUVMUUGJUMYGUWNUVNWKX
          PFGJKLVDURVEVFVGVLZUUNUUQUUNUUMUULFIJKSYGYDWOJUMZUVKUULJUMYGYDYEWNJUM
          ZUWPYGPYDUVHUWMUWQYGUVIQWMBEFJKMVKURAWNFGJKLVDURZUVLWOXKFGJKLVDURVEVF
          VGUUQUUPUUOFIJKSYGYDUWPUVMUUOJUMYGUWRUVNWOXPFGJKLVDURVEVFVGVLZVOULUHX
          TVMUTUVOVCWBWAWCYOUUBUUKUUSYKYNYKYJYIFIJKSYGYDUWLYFYIJUMYGUWNRWKCFGJK
          LVDURVEVFVGYNYMYLFIJKSYGYDUWLUVGYLJUMYGUWNUVJWKXFFGJKLVDURVEVFVGVLYRU
          UAYRYQYPFIJKSYGYDUWPYFYPJUMYGUWRRWOCFGJKLVDURVEVFVGUUAYTYSFIJKSYGYDUW
          PUVGYSJUMYGUWRUVJWOXFFGJKLVDURVEVFVGVLULUUJVMUWOVNULUURVMUWSVNWIWRUAW
          LUFUBZUAWPUFUBZUEUBUVDUAWLWPVAYDUWLYFWLVHUMYGUWNRWKCDFJKNVBURZYDUWPYF
          WPVHUMYGUWRRWOCDFJKNVBURZVOUWTUVBUXAUVCUEYDUWLYFUWTUVBUNYGUWNRWKCDEFG
          IJKLMSNUOURYDUWPYFUXAUVCUNYGUWRRWOCDEFGIJKLMSNUOURWAWDWEWFVTWQUAWLWPU
          XBUXCWGVAWHWJWTUAUHWSUTYHVNVAWHWJWB $.
      $}

      $( Equation 6.47 of [Ponnusamy] p. 362.  (Contributed by NM,
         27-Apr-2007.)  (New usage is discouraged.) $)
      ip1i $p |- ( ( ( A G B ) P C ) +
                       ( ( A G ( -u 1 S B ) ) P C ) ) = ( 2 x. ( A P C ) ) $=
        ( c1 cnmcv cfv eqid ax-1cn ip1ilem ) ABCDEFGQFRSZHIJKLMNOPUCTUAUB $.
    $}

    ${
      ip2i.8 $e |- A e. X $.
      ip2i.9 $e |- B e. X $.
      $( Equation 6.48 of [Ponnusamy] p. 362.  (Contributed by NM,
         26-Apr-2007.)  (New usage is discouraged.) $)
      ip2i $p |- ( ( 2 S A ) P B ) = ( 2 x. ( A P B ) ) $=
        ( co c1 caddc cc0 wcel wceq c2 cneg cmul cnv cc phnvi nvgcl mp3an dipcl
        addridi cn0v cfv eqid nvrinv mp2an oveq1i dip0l eqtri oveq2i w3a ax-1cn
        df-2 3pm3.2i nvdir nvsid oveq12i 3eqtr4ri ip1i ) UAADOZBCOZAAFOZBCOZAPU
        BADOFOZBCOZQOZUAABCOUCOVLRQOVLVOVJVLEUDSZVKGSZBGSZVLUESELUFZVPAGSZVTVQV
        SMMAAEFGHIUGUHNVKBCEGHKUIUHUJVNRVLQVNEUKULZBCOZRVMWABCVPVTVMWATVSMADEFG
        WAHIJWAUMZUNUOUPVPVRWBRTVSNBCEGWAHWCKUQUOURUSVIVKBCVIPPQOZADOZVKUAWDADV
        BUPWEPADOZWFFOZVKVPPUESZWHVTUTWEWGTVSWHWHVTVAVAMVCPPADEFGHIJVDUOWFAWFAF
        VPVTWFATVSMADEGHJVEUOZWIVFURURUPVGAABCDEFGHIJKLMMNVHUR $.
    $}

    ${
      ipdiri.8 $e |- A e. X $.
      ipdiri.9 $e |- B e. X $.
      ipdiri.10 $e |- C e. X $.
      $( Lemma for ~ ipdiri .  (Contributed by NM, 26-Apr-2007.)
         (New usage is discouraged.) $)
      ipdirilem $p |- ( ( A G B ) P C ) = ( ( A P C ) + ( B P C ) ) $=
        ( co wcel wceq mp2an c2 c1 cdiv cmul cneg caddc 2thalfe1 oveq1i cnv w3a
        cc phnvi 2cn halfcn nvgcl mp3an 3pm3.2i nvsass nvsid 3eqtr3i nvscl ip2i
        eqtr3i neg1cn ip1i cn0v cfv cablo wa c1st eqid nvvc ax-mp vafval vcablo
        cvc pm3.2i bafval ablo4 smfval vc2OLD nvrinv oveq12i nv0rid 3eqtri nvdi
        oveq2i eqtr4i ax-1cn 2ne0 divcan1i mulcomi neg1mulneg1e1 nv0lid 3eqtr2i
        eqtri ) ABGQZCDQZUAUBUAUCQZWQEQZCDQUDQZWTWSAUBUEZBEQZGQZEQZGQZCDQZWTXBX
        EEQZGQZCDQZUFQACDQZBCDQZUFQUAWTEQZCDQWRXAXMWQCDUAWSUDQZWQEQZUBWQEQZXMWQ
        XNUBWQEUGUHFUIRZUAUKRZWSUKRZWQHRZUJXOXMSFMULZXRXSXTUMUNXQAHRZBHRZXTYANO
        ABFGHIJUOUPZUQUAWSWQEFHIKURTXQXTXPWQSYAYDWQEFHIKUSTUTUHWTCDEFGHIJKLMXQX
        SXTWTHRYAUNYDWSWQEFHIKVAUPZPVBVCWTXECDEFGHIJKLMYEXQXSXDHRZXEHRYAUNXQYBX
        CHRZYFYANXQXBUKRZYCYGYAVDOXBBEFHIKVAUPZAXCFGHIJUOUPZWSXDEFHIKVAUPPVEXGX
        KXJXLUFXFACDWSWQXDGQZEQZWSUAUDQZAEQZXFAYLWSUAAEQZEQZYNYKYOWSEYKAAGQZBXC
        GQZGQZYOFVFVGZGQZYOGVHRZYBYCVIZYBYGVIYKYSSFVJVGZVPRZUUBXQUUEYAFUUDUUDVK
        VLVMZGUUDFGJVNZVOVMZYBYCNOVQZYBYGNYIVQABAXCGHFGHIJVRZVSUPYQYOYRYTGUUEYB
        YQYOSUUFNAEGUUDHUUGEFKVTZUUJWATXQYCYRYTSYAOBEFGHYTIJKYTVKZWBTWCXQYOHRZU
        UAYOSYAXQXRYBUUMYAUMNUAAEFHIKVAUPYOFGHYTIJUULWDTWEWGXQXSXRYBUJYNYPSYAXS
        XRYBUNUMNUQWSUAAEFHIKURTWHXQXSXTYFUJYLXFSYAXSXTYFUNYDYJUQWSWQXDEFGHIJKW
        FTYNUBAEQZAYMUBAEUBUAWIUMWJWKZUHXQYBUUNASYANAEFHIKUSTWPUTUHXIBCDXIWSWQX
        BAEQZBGQZGQZEQZUBBEQZBXIWTWSUUQEQZGQZUUSXHUVAWTGXBWSUDQZXDEQZWSXBUDQZXD
        EQZXHUVAUVCUVEXDEXBWSVDUNWLUHXQYHXSYFUJUVDXHSYAYHXSYFVDUNYJUQXBWSXDEFHI
        KURTUVFWSXBXDEQZEQZUVAXQXSYHYFUJUVFUVHSYAXSYHYFUNVDYJUQWSXBXDEFHIKURTUV
        GUUQWSEUVGUUPXBXCEQZGQZUUQXQYHYBYGUJUVGUVJSYAYHYBYGVDNYIUQXBAXCEFGHIJKW
        FTUVIBUUPGXBXBUDQZBEQZUUTUVIBUVKUBBEWMUHXQYHYHYCUJUVLUVISYAYHYHYCVDVDOU
        QXBXBBEFHIKURTXQYCUUTBSYAOBEFHIKUSTZUTWGWPWGWPUTWGXQXSXTUUQHRZUJUUSUVBS
        YAXSXTUVNUNYDXQUUPHRZYCUVNYAXQYHYBUVOYAVDNXBAEFHIKVAUPZOUUPBFGHIJUOUPUQ
        WSWQUUQEFGHIJKWFTWHUUSWSUABEQZEQZYMBEQZUUTUURUVQWSEUURAUUPGQZBBGQZGQZUW
        AUVQUUBUUCUVOYCVIUURUWBSUUHUUIUVOYCUVPOVQABUUPBGHUUJVSUPUWBYTUWAGQZUWAU
        VTYTUWAGXQYBUVTYTSYANAEFGHYTIJKUULWBTUHXQUWAHRZUWCUWASYAXQYCYCUWDYAOOBB
        FGHIJUOUPUWAFGHYTIJUULWNTWPUUEYCUWAUVQSUUFOBEGUUDHUUGUUKUUJWATWEWGXQXSX
        RYCUJUVSUVRSYAXSXRYCUNUMOUQWSUABEFHIKURTYMUBBEUUOUHWOUVMWEUHWCWO $.
    $}

    $( Distributive law for inner product.  Equation I3 of [Ponnusamy] p. 362.
       (Contributed by NM, 27-Apr-2007.)  (New usage is discouraged.) $)
    ipdiri $p |- ( ( A e. X /\ B e. X /\ C e. X ) ->
                 ( ( A G B ) P C ) = ( ( A P C ) + ( B P C ) ) ) $=
      ( wcel co caddc wceq cif oveq1 oveq2 cn0v cfv oveq1d eqeq12d oveq12d eqid
      oveq2d elimph ipdirilem dedth3h ) AHNZBHNZCHNZABGOZCDOZACDOZBCDOZPOZQUKAF
      UAUBZRZBGOZCDOZUTCDOZUQPOZQUTULBUSRZGOZCDOZVCVECDOZPOZQVFUMCUSRZDOZUTVJDO
      ZVEVJDOZPOZQABCUSUSUSAUTQZUOVBURVDVOUNVACDAUTBGSUCVOUPVCUQPAUTCDSUCUDBVEQ
      ZVBVGVDVIVPVAVFCDBVEUTGTUCVPUQVHVCPBVECDSUGUDCVJQZVGVKVIVNCVJVFDTVQVCVLVH
      VMPCVJUTDTCVJVEDTUEUDUTVEVJDEFGHIJKLMAFHUSIUSUFZMUHBFHUSIVRMUHCFHUSIVRMUH
      UIUJ $.

    ${
      $d j k A $.  $d j k B $.  $d j k C $.  $d j N $.  $d j k P $.
      $d j k S $.  $d j k X $.
      ipasslem1.b $e |- B e. X $.
      $( Lemma for ~ ipassi .  Show the inner product associative law for
         nonnegative integers.  (Contributed by NM, 27-Apr-2007.)
         (New usage is discouraged.) $)
      ipasslem1 $p |- ( ( N e. NN0 /\ A e. X ) ->
                      ( ( N S A ) P B ) = ( N x. ( A P B ) ) ) $=
        ( wcel co cmul wceq cc0 oveq1 vj vk cn0 cv wi c1 caddc wa cc ax-1cn cnv
        nn0cn w3a phnvi nvdir mpan mp3an2 sylan nvsid adantl oveq2d eqtrd dipcl
        oveq1d mp3an13 nvscl mp3an1 ipdiri mp3an3 sylancom eqtr4d adddir syl2an
        mullidd sylan9eq adantr exp31 a2d cn0v cfv eqid dip0l mp2an nv0 3eqtr4a
        mul02d eqeq12d imbi2d nn0indALT imp ) GUCOAHOZGADPZBCPZGABCPZQPZRZWKUAU
        DZADPZBCPZWQWNQPZRZUEWKSADPZBCPZSWNQPZRZUEWKUBUDZADPZBCPZXFWNQPZRZUEWKX
        FUFUGPZADPZBCPZXKWNQPZRZUEWKWPUEUAUBGXFUCOZWKXJXOXPWKXJXOXPWKUHZXJUHXMX
        IUFWNQPZUGPZXNXQXJXMXHXRUGPZXSXQXMXGAFPZBCPZXTXQXLYABCXQXLXGUFADPZFPZYA
        XPXFUIOZWKXLYDRZXFULZYEUFUIOZWKYFUJEUKOZYEYHWKUMYFEMUNZXFUFADEFHIJKUOUP
        UQURXQYCAXGFWKYCARZXPYIWKYKYJADEHIKUSUPUTVAVBVDXQXTXHWNUGPZYBXQXRWNXHUG
        WKXRWNRXPWKWNYIWKBHOZWNUIOZYJNABCEHILVCVEZVNUTVAXPWKXGHOZYBYLRZXPYEWKYP
        YGYIYEWKYPYJXFADEHIKVFVGURYPWKYMYQNXGABCDEFHIJKLMVHVIVJVKVKXHXIXRUGTVOX
        QXNXSRZXJXPYEYNYRWKYGYOYEYHYNYRUJXFUFWNVLUQVMVPVKVQVRWKEVSVTZBCPZSXCXDY
        IYMYTSRYJNBCEHYSIYSWAZLWBWCWKXBYSBCYIWKXBYSRYJADEHYSIKUUAWDUPVDWKWNYOWF
        WEWQSRZXAXEWKUUBWSXCWTXDUUBWRXBBCWQSADTVDWQSWNQTWGWHWQXFRZXAXJWKUUCWSXH
        WTXIUUCWRXGBCWQXFADTVDWQXFWNQTWGWHWQXKRZXAXOWKUUDWSXMWTXNUUDWRXLBCWQXKA
        DTVDWQXKWNQTWGWHWQGRZXAWPWKUUEWSWMWTWOUUEWRWLBCWQGADTVDWQGWNQTWGWHWIWJ
        $.

      $( Lemma for ~ ipassi .  Show the inner product associative law for
         nonpositive integers.  (Contributed by NM, 27-Apr-2007.)
         (New usage is discouraged.) $)
      ipasslem2 $p |- ( ( N e. NN0 /\ A e. X ) ->
              ( ( -u N S A ) P B ) = ( -u N x. ( A P B ) ) ) $=
        ( wcel co cmul cc cc0 wceq cn0 wa cneg nn0cn negcld phnvi dipcl mp3an13
        cnv mulcl syl2an nvscl mp3an1 sylan syl cmin caddc ax-1cn mulneg2 mpan2
        c1 mulrid negeqd eqtr2d adantr oveq1d neg1cn nvsass mpan mp3an2 mp3an12
        w3a ipasslem1 sylan2 oveq2d negsubd mulneg1 adantl adddid ipdiri mp3an3
        eqtrd mpdan cn0v eqid nvrinv dip0l mp2an eqtrdi eqtr3d mul01d sylan9eqr
        cfv 3eqtr2d subeq0d eqcomd ) GUAOZAHOZUBZGUCZABCPZQPZWTADPZBCPZWSXBXDWQ
        WTROZXAROZXBROWRWQGGUDZUEZEUIOZWRBHOZXFEMUFZNABCEHILUGUHZWTXAUJUKZWSXCH
        OZXDROZWQXEWRXNXHXIXEWRXNXKWTADEHIKULUMUNXIXNXJXOXKNXCBCEHILUGUHUOWSXBX
        DUPPXBGVAUCZADPZBCPZQPZUPPXBXSUCZUQPZSWSXDXSXBUPWSXDGXQDPZBCPZXSWSXCYBB
        CWQGROZWRXCYBTXGYDWRUBZXCGXPQPZADPZYBYEWTYFADYDWTYFTWRYDYFGVAQPZUCZWTYD
        VAROYFYITURGVAUSUTYDYHGGVBVCVDVEVFYDXPROZWRYGYBTZVGXIYDYJWRVLYKXKGXPADE
        HIKVHVIVJWBUNVFWRWQXQHOZYCXSTXIYJWRYLXKVGXPADEHIKULVKZXQBCDEFGHIJKLMNVM
        VNWBVOWSXBXSXMWQYDXRROZXSROWRXGWRYLYNYMXIYLXJYNXKNXQBCEHILUGUHUOZGXRUJU
        KVPWSXBWTXRQPZUQPZYASWSYPXTXBUQWQYDYNYPXTTWRXGYOGXRVQUKVOWSWTXAXRUQPZQP
        ZYQSWSWTXAXRWQXEWRXHVEWRXFWQXLVRWRYNWQYOVRVSWRWQYSWTSQPSWRYRSWTQWRAXQFP
        ZBCPZYRSWRYLUUAYRTZYMWRYLXJUUBNAXQBCDEFHIJKLMVTWAWCWRUUAEWDWMZBCPZSWRYT
        UUCBCXIWRYTUUCTXKADEFHUUCIJKUUCWEZWFVIVFXIXJUUDSTXKNBCEHUUCIUUELWGWHWIW
        JVOWQWTXHWKWLWJWJWNWOWP $.

      $( Lemma for ~ ipassi .  Show the inner product associative law for all
         integers.  (Contributed by NM, 27-Apr-2007.)
         (New usage is discouraged.) $)
      ipasslem3 $p |- ( ( N e. ZZ /\ A e. X ) ->
              ( ( N S A ) P B ) = ( N x. ( A P B ) ) ) $=
        ( wcel cn0 co cmul wceq oveq1d cz cr cn wa elznn0nn ipasslem1 ipasslem2
        cneg wo nnnn0 sylan adantll recn negnegd ad2antrr 3eqtr3d jaoian sylanb
        ) GUAOGPOZGUBOZGUHZUCOZUDZUIAHOZGADQZBCQZGABCQZRQZSZGUEUSVDVIVCABCDEFGH
        IJKLMNUFVCVDUDVAUHZADQZBCQZVJVGRQZVFVHVBVDVLVMSZUTVBVAPOVDVNVAUJABCDEFV
        AHIJKLMNUGUKULUTVLVFSVBVDUTVKVEBCUTVJGADUTGGUMUNZTTUOUTVMVHSVBVDUTVJGVG
        RVOTUOUPUQUR $.

      $( Lemma for ~ ipassi .  Show the inner product associative law for
         positive integer reciprocals.  (Contributed by NM, 27-Apr-2007.)
         (New usage is discouraged.) $)
      ipasslem4 $p |- ( ( N e. NN /\ A e. X ) ->
                  ( ( ( 1 / N ) S A ) P B ) = ( ( 1 / N ) x. ( A P B ) ) ) $=
        ( wcel c1 co cmul cc adantr cn wa cdiv nnrecre recnd phnvi nvscl mp3an1
        cnv sylan dipcl mp3an13 syl mulcl syl2an nncn cc0 recidd oveq1d mullidd
        wne nnne0 sylan9eq wceq nvsid simpr w3a nvsass syl3anc eqtr3d cn0 nnnn0
        mpan ipasslem1 syl2anc 3eqtrd adantl mulassd mulcanad ) GUAOZAHOZUBZPGU
        CQZADQZBCQZWCABCQZRQZGWBWDHOZWESOZVTWCSOZWAWHVTWCGUDUEZEUIOZWJWAWHEMUFZ
        WCADEHIKUGUHUJZWLWHBHOZWIWMNWDBCEHILUKULUMVTWJWFSOZWGSOWAWKWLWAWOWPWMNA
        BCEHILUKULZWCWFUNUOVTGSOZWAGUPZTZVTGUQVAWAGVBZTWBGWCRQZWFRQZGWERQZGWGRQ
        WBXCWFGWDDQZBCQZXDVTWAXCPWFRQWFVTXBPWFRVTGWSXAURZUSWAWFWQUTVCWBAXEBCWBX
        BADQZAXEVTWAXHPADQZAVTXBPADXGUSWLWAXIAVDWMADEHIKVEVMVCWBWRWJWAXHXEVDZWT
        VTWJWAWKTZVTWAVFWLWRWJWAVGXJWMGWCADEHIKVHVMVIVJUSWBGVKOZWHXFXDVDVTXLWAG
        VLTWNWDBCDEFGHIJKLMNVNVOVPWBGWCWFWTXKWAWPVTWQVQVRVJVS $.

      $( Lemma for ~ ipassi .  Show the inner product associative law for
         rational numbers.  (Contributed by NM, 27-Apr-2007.)
         (New usage is discouraged.) $)
      ipasslem5 $p |- ( ( C e. QQ /\ A e. X ) ->
                  ( ( C S A ) P B ) = ( C x. ( A P B ) ) ) $=
        ( vj vk wcel co cmul wceq cq cv cdiv cn wrex cz wi elq wa w3a c1 cc zcn
        nnrecre recnd cnv phnvi dipcl mp3an13 mulass syl3an adantr nncn cc0 wne
        adantl nnne0 divrecd 3adant3 oveq1d nvsass eqtrd nvscl mp3an1 ipasslem3
        mpan sylan sylan2 3impb ipasslem4 3adant1 oveq2d 3eqtr4rd oveq1 eqeq12d
        id 3eqtrd syl5ibrcom 3expia com23 rexlimivv sylbi imp ) CUAQZAHQZCAERZB
        DRZCABDRZSRZTZWNCOUBZPUBZUCRZTZPUDUEOUFUEWOWTUGZOPCUHXDXEOPUFUDXAUFQZXB
        UDQZUIZWOXDWTXFXGWOXDWTUGXFXGWOUJZWTXDXCAERZBDRZXCWRSRZTXIXAUKXBUCRZSRZ
        WRSRZXAXMWRSRZSRZXLXKXFXAULQZXGXMULQZWOWRULQZXOXQTXAUMZXGXMXBUNUOZFUPQZ
        WOBHQXTFMUQZNABDFHILURUSXAXMWRUTVAXIXCXNWRSXFXGXCXNTWOXHXAXBXFXRXGYAVBX
        GXBULQXFXBVCVFXGXBVDVEXFXBVGVFVHVIZVJXIXKXAXMAERZERZBDRZXAYFBDRZSRZXQXI
        XJYGBDXIXJXNAERZYGXIXCXNAEYEVJXFXRXGXSWOWOYKYGTZYAYBWOWFYCXRXSWOUJYLYDX
        AXMAEFHIKVKVPVAVLVJXFXGWOYHYJTZXGWOUIXFYFHQZYMXGXSWOYNYBYCXSWOYNYDXMAEF
        HIKVMVNVQYFBDEFGXAHIJKLMNVOVRVSXIYIXPXASXGWOYIXPTXFABDEFGXBHIJKLMNVTWAW
        BWGWCXDWQXKWSXLXDWPXJBDCXCAEWDVJCXCWRSWDWEWHWIWJWKWLWM $.
    $}

    ${
      $d w B $.  $d x F $.  $d w K $.  $d w P $.  $d w S $.  $d w U $.
      $d w X $.  $d w x A $.
      ipasslem7.a $e |- A e. X $.
      ipasslem7.b $e |- B e. X $.
      ipasslem7.f $e |- F = ( w e. RR |->
                              ( ( ( w S A ) P B ) - ( w x. ( A P B ) ) ) ) $.
      ${
        ipasslem7.j $e |- J = ( topGen ` ran (,) ) $.
        ipasslem7.k $e |- K = ( TopOpen ` CCfld ) $.
        $( Lemma for ~ ipassi .  Show that
           ` ( ( w S A ) P B ) - ( w x. ( A P B ) ) ` is continuous on ` RR ` .
           (Contributed by NM, 23-Aug-2007.)  (Revised by Mario Carneiro,
           6-May-2014.)  (New usage is discouraged.) $)
        ipasslem7 $p |- F e. ( J Cn K ) $=
          ( cr cv co cmul cmin cmpt ccn wcel wtru cioo crn ctg cfv crest tgioo2
          cc eqtri ctopon cnfldtopon a1i wss ax-resscn cims cmopn cnmptid cxmet
          cnv phnvi eqid imsxmet ax-mp mopntopon mp1i cnmptc ctx cnmpt12f dipcn
          smcn dipcl mp3an mulcn subcn cnmpt1res mptru eqeltri ) GAUBAUCZBEUDZC
          DUDZWGBCDUDZUEUDZUFUDZUGZIJUHUDZSWMWNUIUJAWLJIJUQUBIUKULUMUNJUBUOUDTJ
          UAUPURJUQUSUNUIUJJUAUTVAZUBUQVBUJVCVAUJAWIWKUFJJJJUQWOUJAWHCDJFVDUNZV
          EUNZWQJUQWOUJAWGBEJJWQWQUQWOUJAJUQWOVFZUJABJWQUQKWOWPKVGUNUIZWQKUSUNU
          IUJFVHUIZWSFPVIZWPFKLWPVJZVKVLWPWQKWQVJZVMVNZBKUIZUJQVAVOWTEJWQVPUDWQ
          UHUDUIUJXAWPEFWQJXBXCNUAVSVNVQUJACJWQUQKWOXDCKUIZUJRVAVOWTDWQWQVPUDJU
          HUDUIUJXAWPDFWQJOXBXCUAVRVNVQUJAWGWJUEJJJJUQWOWRUJAWJJJUQUQWOWOWJUQUI
          ZUJWTXEXFXGXAQRBCDFKLOVTWAVAVOUEJJVPUDJUHUDZUIUJJUAWBVAVQUFXHUIUJJUAW
          CVAVQWDWEWF $.
      $}

      $( Lemma for ~ ipassi .  By ~ ipasslem5 , ` F ` is 0 for all ` QQ ` ;
         since it is continuous and ` QQ ` is dense in ` RR ` by ~ qdensere2 ,
         we conclude ` F ` is 0 for all ` RR ` .  (Contributed by NM,
         24-Aug-2007.)  (Revised by Mario Carneiro, 6-May-2014.)
         (New usage is discouraged.) $)
      ipasslem8 $p |- F : RR --> { 0 } $=
        ( wcel cq co vx cc0 cc ccnv csn cima wss cioo crn ctg cfv ccl cr wf 0cn
        wceq cv wral cmul cmin qre oveq1 oveq1d oveq12d ovex fvmpt syl wa phnvi
        qcn cnv nvscl mp3an1 sylan dipcl mp3an13 ipasslem5 subeq0bd mpan2 eqtrd
        rgen wfun cdm wb funmpt2 qssre dmmpti sseqtrri funconstss mpbi qdensere
        mp2an ccnfld ctopn ct1 ccn w3a cha eqid cnfldhaus haust1 ax-mp uniretop
        ipasslem7 cnfldtopon toponunii dnsconst mpanl12 mp3an ) UBUCRZSGUDUBUEZ
        UFUGZSUHUIUJUKZULUKUKUMUPZUMXKGUNZUOUAUQZGUKZUBUPZUASURZXLXRUASXPSRZXQX
        PBETZCDTZXPBCDTZUSTZUTTZUBXTXPUMRXQYEUPXPVAAXPAUQZBETZCDTZYFYCUSTZUTTZY
        EUMGYFXPUPZYHYBYIYDUTYKYGYACDYFXPBEVBVCYFXPYCUSVBVDQYBYDUTVEVFVGXTBIRZY
        EUBUPOXTYLVHZYBYDYMYAIRZYBUCRZXTXPUCRZYLYNXPVJFVKRZYPYLYNFNVIZXPBEFIJLV
        LVMVNYQYNCIRYOYRPYACDFIJMVOVPVGBCXPDEFHIJKLMNPVQVRVSVTWAGWBSGWCZUGXSXLW
        DAUMYJGQWESUMYSWFAUMYJGYHYIUTVEQWGWHUASUBGWIWLWJWKWMWNUKZWORZGXMYTWPTRX
        JXLXNWQXOYTWRRUUAYTYTWSZWTYTXAXBABCDEFGHXMYTIJKLMNOPQXMWSUUBXDSUBGXMYTU
        MUCXCUCYTYTUUBXEXFXGXHXI $.
    $}

    ${
      $d w A $.  $d w B $.  $d w C $.  $d w P $.  $d w S $.  $d w U $.
      $d w X $.
      ipasslem9.a $e |- A e. X $.
      ipasslem9.b $e |- B e. X $.
      $( Lemma for ~ ipassi .  Conclude from ~ ipasslem8 the inner product
         associative law for real numbers.  (Contributed by NM, 24-Aug-2007.)
         (New usage is discouraged.) $)
      ipasslem9 $p |- ( C e. RR ->
                  ( ( C S A ) P B ) = ( C x. ( A P B ) ) ) $=
        ( vw cr wcel co cc0 cmul cmin wceq cv cmpt cfv oveq1d oveq12d eqid ovex
        oveq1 fvmpt csn wf ipasslem8 fvconst mpan eqtr3d cc wb recn phnvi nvscl
        cnv mp3an13 dipcl syl mp3an mulcl mpan2 subeq0ad mpbid ) CQRZCAESZBDSZC
        ABDSZUASZUBSZTUCZVOVQUCZVMCPQPUDZAESZBDSZWAVPUASZUBSZUEZUFZVRTPCWEVRQWF
        WACUCZWCVOWDVQUBWHWBVNBDWACAEUKUGWACVPUAUKUHWFUIZVOVQUBUJULQTUMWFUNVMWG
        TUCPABDEFWFGHIJKLMNOWIUOQTCWFUPUQURVMCUSRZVSVTUTCVAWJVOVQWJVNHRZVOUSRZF
        VDRZWJAHRZWKFMVBZNCAEFHIKVCVEWMWKBHRZWLWOOVNBDFHILVFVEVGWJVPUSRZVQUSRWM
        WNWPWQWONOABDFHILVFVHCVPVIVJVKVGVL $.
    $}

    ${
      ipasslem10.a $e |- A e. X $.
      ipasslem10.b $e |- B e. X $.
      ipasslem10.6 $e |- N = ( normCV ` U ) $.
      $( Lemma for ~ ipassi .  Show the inner product associative law for the
         imaginary number ` _i ` .  (Contributed by NM, 24-Aug-2007.)
         (New usage is discouraged.) $)
      ipasslem10 $p |- ( ( _i S A ) P B ) = ( _i x. ( A P B ) ) $=
        ( ci co cmul wcel ccj cfv cneg c4 wceq c2 cexp c1 cmin caddc cnv ax-icn
        phnvi cc nvscl mp3an 4ipval2 4cn negicn dipcl mul12i nvgcl nvcli neg1cn
        recni sqcli subcli mulcli addcomi adddii w3a nvsass mp2an oveq1i eqtr3i
        3pm3.2i ixi oveq2i fveq2i negeqi negneg1e1 3eqtri nvsid 3eqtr3i oveq12i
        mulneg1i mulm1i negsubdi2i eqtr2i mulassi eqtr4i mulcomli mullidi eqtri
        4ne0 mulcani mpbi dipcj cjmuli cr neg1rr cjrebi cji ax-1cn mul2negi ) B
        QADRZCRZUAUBZQUCZBACRZSRZUAUBZXFBCRZQABCRZSRZXGXKUAUDXGSRZUDXKSRZUEXGXK
        UEXPBXFFRZGUBZUFUGRZBUHUCZXFDRZFRZGUBZUFUGRZUIRZQBQXFDRZFRZGUBZUFUGRZBX
        IXFDRZFRZGUBZUFUGRZUIRZSRZUJRZXQEUKTZBHTZXFHTZXPYQUEEMUMZOYRQUNTZAHTZYT
        UUAULNQADEHIKUOUPZBXFCDEFGHIJKPLUQUPXQXIUDXJSRZSRZYQUDXIXJURUSYRYSUUCXJ
        UNTUUAONBACEHILUTUPZVAYQXIBAFRZGUBZUFUGRZBYAADRZFRZGUBZUFUGRZUIRZQXTBXI
        ADRZFRZGUBZUFUGRZUIRZSRZUJRZSRZUUFYQYPYFUJRZUVCYFYPXTYEXSXSXREGHIPUUAYR
        YSYTXRHTUUAOUUDBXFEFHIJVBUPVCVEVFZYDYDYCEGHIPUUAYRYSYBHTZYCHTUUAOYRYAUN
        TZYTUVFUUAVDUUDYAXFDEHIKUOUPBYBEFHIJVBUPVCVEVFVGQYOULYJYNYIYIYHEGHIPUUA
        YRYSYGHTZYHHTUUAOYRUUBYTUVHUUAULUUDQXFDEHIKUOUPBYGEFHIJVBUPVCVEVFYMYMYL
        EGHIPUUAYRYSYKHTZYLHTUUAOYRXIUNTZYTUVIUUAUSUUDXIXFDEHIKUOUPBYKEFHIJVBUP
        VCVEVFVGVHVIUVCXIUUOSRZXIUVASRZUJRUVDXIUUOUVAUSUUJUUNUUIUUIUUHEGHIPUUAY
        RYSUUCUUHHTUUAONBAEFHIJVBUPVCVEVFZUUMUUMUULEGHIPUUAYRYSUUKHTZUULHTUUAOY
        RUVGUUCUVNUUAVDNYAADEHIKUOUPBUUKEFHIJVBUPVCVEVFZVGZQUUTULXTUUSUVEUURUUR
        UUQEGHIPUUAYRYSUUPHTZUUQHTUUAOYRUVJUUCUVQUUAUSNXIADEHIKUOUPBUUPEFHIJVBU
        PVCVEVFVGZVHVJYPUVKYFUVLUJYPQUUNUUJUIRZSRZQYASRZUUOSRZUVKYOUVSQSYJUUNYN
        UUJUIYIUUMUFUGYHUULGYGUUKBFQQSRZADRZYGUUKYRUUBUUBUUCVKUWDYGUEUUAUUBUUBU
        UCULULNVPQQADEHIKVLVMUWCYAADVQVNVOVRVSVNYMUUIUFUGYLUUHGYKABFXIQSRZADRZU
        HADRZYKAUWEUHADUWEUWCUCYAUCUHQQULULWFUWCYAVQVTWAWBZVNYRUVJUUBUUCVKUWFYK
        UEUUAUVJUUBUUCUSULNVPXIQADEHIKVLVMYRUUCUWGAUEUUANADEHIKWCVMWDVRVSVNWEVR
        UVTQYAUUOSRZSRUWBUVSUWIQSUWIUUOUCUVSUUOUVPWGUUJUUNUVMUVOWHWIVRQYAUUOULV
        DUVPWJWKUWAXIUUOSYAQXIVDULQULWGZWLVNWBYFUWEUUTSRZUVLYFUHUUTSRZUWKYFUUTU
        WLYEUUSXTUIYDUURUFUGYCUUQGYBUUPBFYAQSRZADRZYBUUPYRUVGUUBUUCVKUWNYBUEUUA
        UVGUUBUUCVDULNVPYAQADEHIKVLVMUWMXIADUWJVNVOVRVSVNVRUUTUVRWMWKUWEUHUUTSU
        WHVNWKXIQUUTUSULUVRWJWNWEWKWKUUEUVBXISYRYSUUCUUEUVBUEUUAONBACDEFGHIJKPL
        UQUPVRWKWKWKXGXKUDYRYSYTXGUNTUUAOUUDBXFCEHILUTUPXIXJUSUUGVHURWOWPWQVSYR
        YSYTXHXMUEUUAOUUDBXFCEHILWRUPXLXIUAUBZXJUAUBZSRXOXIXJUSUUGWSUWOQUWPXNSU
        WMUAUBYAUAUBZQUAUBZSRZUWOQYAQVDULWSUWMXIUAUWJVSUWSYAXISRUHQSRQUWQYAUWRX
        ISYAWTTUWQYAUEXAYAVDXBWQXCWEUHQXDULXEQULWMWBWDYRYSUUCUWPXNUEUUAONBACEHI
        LWRUPWEWNWD $.
    $}

    ${
      $d x B $.  $d x y C $.  $d x y P $.
      ipasslem11.a $e |- A e. X $.
      ipasslem11.b $e |- B e. X $.
      $( TODO - proof got longer with axcnreOLD -> cnre because
         of mulcl - is it possible to rewrite it to shorten it? $)
      $( Lemma for ~ ipassi .  Show the inner product associative law for all
         complex numbers.  (Contributed by NM, 25-Aug-2007.)
         (New usage is discouraged.) $)
      ipasslem11 $p |- ( C e. CC ->
                  ( ( C S A ) P B ) = ( C x. ( A P B ) ) ) $=
        ( wcel ci cmul co wceq vx vy cc cv caddc cr wrex cnre wa ax-icn sylancr
        recn mulcom adantl oveq2d eqeq2d cnv phnvi nvscl mp3an13 sylancl ipdiri
        syl mulcl mp3an3 syl2an ipasslem9 mp3an w3a nvsass mp3an23 oveq1d dipcl
        mpan mulass cnmcv cfv ipasslem10 oveq2i eqtr4di 3eqtr4d oveqan12d eqtrd
        eqid nvdir adddir oveq1 eqeq12d syl5ibrcom sylbid rexlimivv ) CUCPCUAUD
        ZQUBUDZRSZUESZTZUBUFUGUAUFUGCAESZBDSZCABDSZRSZTZUAUBCUHWPXAUAUBUFUFWLUF
        PZWMUFPZUIZWPCWLWMQRSZUESZTZXAXDWOXFCXDWNXEWLUEXCWNXETZXBXCQUCPZWMUCPZX
        HUJWMULZQWMUMUKUNUOUPXDXAXGXFAESZBDSZXFWSRSZTXDWLAESZXEAESZGSZBDSZWLWSR
        SZXEWSRSZUESZXMXNXDXRXOBDSZXPBDSZUESZYAXBXOHPZXPHPZXRYDTZXCXBWLUCPZYEWL
        ULZFUQPZYHAHPZYEFMURZNWLAEFHIKUSUTVCXCXEUCPZYFXCXJXIYMXKUJWMQVDVAZYJYMY
        KYFYLNXEAEFHIKUSUTVCYEYFBHPZYGOXOXPBDEFGHIJKLMVBVEVFXBXCYBXSYCXTUEABWLD
        EFGHIJKLMNOVGXCWMQAESZESZBDSWMYPBDSZRSZYCXTYPBWMDEFGHIJKLMYJXIYKYPHPYLU
        JNQAEFHIKUSVHOVGXCXPYQBDXCXJXPYQTZXKXJXIYKYTUJNYJXJXIYKVIYTYLWMQAEFHIKV
        JVNVKVCVLXCXTWMQWSRSZRSZYSXCXJXTUUBTZXKXJXIWSUCPZUUCUJYJYKYOUUDYLNOABDF
        HILVMVHZWMQWSVOVKVCYRUUAWMRABDEFGFVPVQZHIJKLMNOUUFWDVRVSVTWAWBWCXDXLXQB
        DXBYHYMXLXQTZXCYIYNYHYMYKUUGNYJYHYMYKVIUUGYLWLXEAEFGHIJKWEVNVEVFVLXBYHY
        MXNYATZXCYIYNYHYMUUDUUHUUEWLXEWSWFVEVFWAXGWRXMWTXNXGWQXLBDCXFAEWGVLCXFW
        SRWGWHWIWJWKVC $.
    $}

    $( Associative law for inner product.  Equation I2 of [Ponnusamy] p. 363.
       (Contributed by NM, 25-Aug-2007.)  (New usage is discouraged.) $)
    ipassi $p |- ( ( A e. CC /\ B e. X /\ C e. X ) ->
                  ( ( A S B ) P C ) = ( A x. ( B P C ) ) ) $=
      ( wcel co cmul wceq wi cif oveq2 cc cn0v cfv oveq1d oveq2d eqeq12d imbi2d
      wa oveq1 eqid elimph ipasslem11 dedth2h com12 3impib ) AUANZBHNZCHNZABEOZ
      CDOZABCDOZPOZQZUQURUHUPVCUQURUPVCRUPAUQBFUBUCZSZEOZCDOZAVECDOZPOZQZRUPVFU
      RCVDSZDOZAVEVKDOZPOZQZRBCVDVDBVEQZVCVJUPVPUTVGVBVIVPUSVFCDBVEAETUDVPVAVHA
      PBVECDUIUEUFUGCVKQZVJVOUPVQVGVLVIVNCVKVFDTVQVHVMAPCVKVEDTUEUFUGVEVKADEFGH
      IJKLMBFHVDIVDUJZMUKCFHVDIVRMUKULUMUNUO $.
  $}

  ${
    dipdir.1 $e |- X = ( BaseSet ` U ) $.
    dipdir.2 $e |- G = ( +v ` U ) $.
    dipdir.7 $e |- P = ( .iOLD ` U ) $.
    $( Distributive law for inner product.  Equation I3 of [Ponnusamy] p. 362.
       (Contributed by NM, 25-Aug-2007.)  (New usage is discouraged.) $)
    dipdir $p |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                 ( ( A G B ) P C ) = ( ( A P C ) + ( B P C ) ) ) $=
      ( wcel co caddc wceq cba cfv cpv cdip oveqd eqid ccphlo w3a cmul cop cabs
      wi cif fveq2 eqtrid eleq2d 3anbi123d oveq1d eqtrd oveq12d eqeq12d imbi12d
      cns elimphu ipdiri dedth imp ) EUAKZAGKZBGKZCGKZUBZABFLZCDLZACDLZBCDLZMLZ
      NZVBVFVLUFAVBEMUCUDUEUDZUGZOPZKZBVOKZCVOKZUBZABVNQPZLZCVNRPZLZACWBLZBCWBL
      ZMLZNZUFEVMEVNNZVFVSVLWGWHVCVPVDVQVEVRWHGVOAWHGEOPVOHEVNOUHUIZUJWHGVOBWIU
      JWHGVOCWIUJUKWHVHWCVKWFWHVHWACDLWCWHVGWACDWHFVTABWHFEQPVTIEVNQUHUISULWHDW
      BWACWHDERPWBJEVNRUHUIZSUMWHVIWDVJWEMWHDWBACWJSWHDWBBCWJSUNUOUPABCWBVNUQPZ
      VNVTVOVOTVTTWKTWBTEURUSUTVA $.

    $( Distributive law for inner product.  (Contributed by NM, 20-Nov-2007.)
       (New usage is discouraged.) $)
    dipdi $p |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                 ( A P ( B G C ) ) = ( ( A P B ) + ( A P C ) ) ) $=
      ( wcel w3a co caddc wceq id wa ccj cfv dipcj ccphlo 3com13 cnv phnv simpl
      3com12 dipdir sylan2 fveq2d nvgcl 3com23 3adant3r3 syl3anc sylan cc dipcl
      simpr3 3adant3r1 3adant3r2 cjaddd oveq12d eqtrd 3eqtr3d ) AGKZBGKZCGKZLEU
      AKZVFVEVDLZABCFMZDMZABDMZACDMZNMZOVFVEVDVHVHPUBVGVHQZVIADMZRSZBADMZCADMZN
      MZRSZVJVMVNVOVSRVHVGVEVFVDLZVOVSOVEVFVDWAWAPUFBCADEFGHIJUGUHUIVGEUCKZVHVP
      VJOZEUDZWBVHQZWBVIGKZVDWCWBVHUEWBVFVEWFVDWBVEVFWFBCEFGHIUJUKULWBVFVEVDUQV
      IADEGHJTUMUNVGWBVHVTVMOWDWEVTVQRSZVRRSZNMVMWEVQVRWBVEVDVQUOKVFBADEGHJUPUR
      WBVFVDVRUOKVECADEGHJUPUSUTWEWGVKWHVLNWBVEVDWGVKOVFBADEGHJTURWBVFVDWHVLOVE
      CADEGHJTUSVAVBUNVCUH $.
  $}

  ${
    ip2dii.1 $e |- X = ( BaseSet ` U ) $.
    ip2dii.2 $e |- G = ( +v ` U ) $.
    ip2dii.7 $e |- P = ( .iOLD ` U ) $.
    ip2dii.u $e |- U e. CPreHilOLD $.
    ip2dii.a $e |- A e. X $.
    ip2dii.b $e |- B e. X $.
    ip2dii.c $e |- C e. X $.
    ip2dii.d $e |- D e. X $.
    $( Inner product of two sums.  (Contributed by NM, 17-Apr-2008.)
       (New usage is discouraged.) $)
    ip2dii $p |- ( ( A G B ) P ( C G D ) )
                = ( ( ( A P C ) + ( B P D ) ) + ( ( A P D ) + ( B P C ) ) ) $=
      ( co caddc wcel mp3an ccphlo wceq 3pm3.2i dipdi mp2an oveq12i phnvi nvgcl
      w3a cnv dipdir cc dipcl add42i 3eqtr4i ) ACDGQZEQZBUPEQZRQZACEQZADEQZRQZB
      CEQZBDEQZRQZRQABGQUPEQZUTVDRQVAVCRQRQUQVBURVERFUASZAHSZCHSZDHSZUIUQVBUBLV
      HVIVJMOPUCACDEFGHIJKUDUEVGBHSZVIVJUIURVEUBLVKVIVJNOPUCBCDEFGHIJKUDUEUFVGV
      HVKUPHSZUIVFUSUBLVHVKVLMNFUJSZVIVJVLFLUGZOPCDFGHIJUHTUCABUPEFGHIJKUKUEUTV
      DVAVCVMVHVIUTULSVNMOACEFHIKUMTVMVKVJVDULSVNNPBDEFHIKUMTVMVHVJVAULSVNMPADE
      FHIKUMTVMVKVIVCULSVNNOBCEFHIKUMTUNUO $.
  $}

  ${
    ipass.1 $e |- X = ( BaseSet ` U ) $.
    ipass.4 $e |- S = ( .sOLD ` U ) $.
    ipass.7 $e |- P = ( .iOLD ` U ) $.
    $( Associative law for inner product.  Equation I2 of [Ponnusamy] p. 363.
       (Contributed by NM, 25-Aug-2007.)  (New usage is discouraged.) $)
    dipass $p |- ( ( U e. CPreHilOLD /\ ( A e. CC /\ B e. X /\ C e. X ) ) ->
                 ( ( A S B ) P C ) = ( A x. ( B P C ) ) ) $=
      ( wcel co cmul wceq cba cfv cns cdip fveq2 eqid ccphlo cc w3a wi cop cabs
      caddc cif eqtrid eleq2d oveqd oveq1d eqtrd oveq2d eqeq12d imbi12d elimphu
      3anbi23d cpv ipassi dedth imp ) FUAKZAUBKZBGKZCGKZUCZABELZCDLZABCDLZMLZNZ
      VCVGVLUDVDBVCFUGMUEUFUEZUHZOPZKZCVOKZUCZABVNQPZLZCVNRPZLZABCWALZMLZNZUDFV
      MFVNNZVGVRVLWEWFVEVPVFVQVDWFGVOBWFGFOPVOHFVNOSUIZUJWFGVOCWGUJURWFVIWBVKWD
      WFVIVTCDLWBWFVHVTCDWFEVSABWFEFQPVSIFVNQSUIUKULWFDWAVTCWFDFRPWAJFVNRSUIZUK
      UMWFVJWCAMWFDWABCWHUKUNUOUPABCWAVSVNVNUSPZVOVOTWITVSTWATFUQUTVAVB $.

    $( "Associative" law for second argument of inner product (compare
       ~ dipass ).  (Contributed by NM, 22-Nov-2007.)
       (New usage is discouraged.) $)
    dipassr $p |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. CC /\ C e. X ) ) ->
                 ( A P ( B S C ) ) = ( ( * ` B ) x. ( A P C ) ) ) $=
      ( wcel cc w3a wa co ccj cfv cmul wceq dipcj ccphlo 3anrot dipass cnv phnv
      sylan2b fveq2d simpl nvscl 3adant3r1 simpr1 syl3anc sylan dipcl 3adant3r2
      simpr2 3com23 cjmuld oveq2d eqtrd 3eqtr3d ) FUAKZAGKZBLKZCGKZMZNZBCEOZADO
      ZPQZBCADOZROZPQZAVHDOZBPQZACDOZROZVGVIVLPVFVBVDVEVCMVIVLSVCVDVEUBBCADEFGH
      IJUCUFUGVBFUDKZVFVJVNSZFUEZVRVFNZVRVHGKZVCVSVRVFUHVRVDVEWBVCBCEFGHIUIUJVR
      VCVDVEUKVHADFGHJTULUMVBVRVFVMVQSVTWAVMVOVKPQZROVQWABVKVRVCVDVEUPVRVCVEVKL
      KZVDVRVEVCWDCADFGHJUNUQUOURWAWCVPVORVRVCVEWCVPSZVDVRVEVCWECADFGHJTUQUOUSU
      TUMVA $.

    $( "Associative" law for inner product.  Conjugate version of ~ dipassr .
       (Contributed by NM, 23-Nov-2007.)  (New usage is discouraged.) $)
    dipassr2 $p |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. CC /\ C e. X ) ) ->
                 ( A P ( ( * ` B ) S C ) ) = ( B x. ( A P C ) ) ) $=
      ( ccphlo wcel cc w3a wa ccj cfv co cmul wceq cjcl dipassr syl3anr2 adantl
      cjcj 3ad2ant2 oveq1d eqtrd ) FKLZAGLZBMLZCGLZNZOZABPQZCERDRZUOPQZACDRZSRZ
      BURSRUKUJUIUOMLULUPUSTBUAAUOCDEFGHIJUBUCUNUQBURSUMUQBTZUIUKUJUTULBUEUFUDU
      GUH $.
  $}

  ${
    ipsubdir.1 $e |- X = ( BaseSet ` U ) $.
    ipsubdir.3 $e |- M = ( -v ` U ) $.
    ipsubdir.7 $e |- P = ( .iOLD ` U ) $.
    $( Distributive law for inner product subtraction.  (Contributed by NM,
       20-Nov-2007.)  (New usage is discouraged.) $)
    dipsubdir $p |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                 ( ( A M B ) P C ) = ( ( A P C ) - ( B P C ) ) ) $=
      ( wcel w3a wa cneg cfv co caddc wceq cc sylan ccphlo cns cpv cmin idd cnv
      c1 phnv neg1cn nvscl mp3an2 ex 3anim123d imp dipdir syldan nvmval syl3an1
      eqid 3adant3r3 oveq1d cmul dipass mp3anr1 dipcl 3expb mulm1d eqtrd oveq2d
      3adantr1 3adant3r2 3adant3r1 negsubd eqtr2d 3eqtr4d ) EUAKZAGKZBGKZCGKZLZ
      MZAUGNZBEUBOZPZEUCOZPZCDPZACDPZWDCDPZQPZABFPZCDPWHBCDPZUDPZVPVTVQWDGKZVSL
      ZWGWJRVPVTWOVPVQVQVRWNVSVSVPVQUEVPVRWNVPEUFKZVRWNEUHZWPWBSKZVRWNUIWBBWCEG
      HWCUSZUJUKTULVPVSUEUMUNAWDCDEWEGHWEUSZJUOUPWAWKWFCDVPVQVRWKWFRZVSVPWPVQVR
      XAWQABWCEWEFGHWTWSIUQURUTVAWAWJWHWLNZQPZWMWAWIXBWHQVPVRVSWIXBRVQVPVRVSMZM
      ZWIWBWLVBPZXBVPWRVRVSWIXFRUIWBBCDWCEGHWSJVCVDXEWLVPWPXDWLSKZWQWPVRVSXGBCD
      EGHJVEZVFTVGVHVJVIVPWPVTXCWMRWQWPVTMWHWLWPVQVSWHSKVRACDEGHJVEVKWPVRVSXGVQ
      XHVLVMTVNVO $.

    $( Distributive law for inner product subtraction.  (Contributed by NM,
       20-Nov-2007.)  (New usage is discouraged.) $)
    dipsubdi $p |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                 ( A P ( B M C ) ) = ( ( A P B ) - ( A P C ) ) ) $=
      ( wcel w3a co cmin wceq id wa ccj cfv dipcj ccphlo 3com13 3com12 cnv phnv
      dipsubdir sylan2 fveq2d simpl nvmcl 3com23 3adant3r3 simpr3 syl3anc sylan
      cc dipcl 3adant3r1 3adant3r2 cjsub syl2anc oveq12d eqtrd 3eqtr3d ) AGKZBG
      KZCGKZLEUAKZVGVFVELZABCFMZDMZABDMZACDMZNMZOVGVFVEVIVIPUBVHVIQZVJADMZRSZBA
      DMZCADMZNMZRSZVKVNVOVPVTRVIVHVFVGVELZVPVTOVFVGVEWBWBPUCBCADEFGHIJUFUGUHVH
      EUDKZVIVQVKOZEUEZWCVIQZWCVJGKZVEWDWCVIUIWCVGVFWGVEWCVFVGWGBCEFGHIUJUKULWC
      VGVFVEUMVJADEGHJTUNUOVHWCVIWAVNOWEWFWAVRRSZVSRSZNMZVNWFVRUPKZVSUPKZWAWJOW
      CVFVEWKVGBADEGHJUQURWCVGVEWLVFCADEGHJUQUSVRVSUTVAWFWHVLWIVMNWCVFVEWHVLOVG
      BADEGHJTURWCVGVEWIVMOVFCADEGHJTUSVBVCUOVDUG $.
  $}

  ${
    pyth.1 $e |- X = ( BaseSet ` U ) $.
    pyth.2 $e |- G = ( +v ` U ) $.
    pyth.6 $e |- N = ( normCV ` U ) $.
    pyth.7 $e |- P = ( .iOLD ` U ) $.
    pythi.u $e |- U e. CPreHilOLD $.
    pythi.a $e |- A e. X $.
    pythi.b $e |- B e. X $.
    $( The Pythagorean theorem for an arbitrary complex inner product
       (pre-Hilbert) space ` U ` .  The square of the norm of the sum of two
       orthogonal vectors (i.e. whose inner product is 0) is the sum of the
       squares of their norms.  Problem 2 in [Kreyszig] p. 135.  (Contributed
       by NM, 17-Apr-2008.)  (New usage is discouraged.) $)
    pythi $p |- ( ( A P B ) = 0 -> ( ( N ` ( A G B ) ) ^ 2 )
        = ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) $=
      ( co cc0 wceq caddc wcel mp3an cfv c2 cexp ip2dii id cnv phnvi diporthcom
      wb biimpi oveq12d 00id eqtrdi oveq2d cc dipcl addcli addridi eqtrid nvgcl
      ipidsq mp2an oveq12i 3eqtr3g ) ABCOZPQZABEOZVGCOZAACOZBBCOZROZVGFUAUBUCOZ
      AFUAUBUCOZBFUAUBUCOZROVFVHVKVEBACOZROZROZVKABABCDEGHIKLMNMNUDVFVQVKPROVKV
      FVPPVKRVFVPPPROPVFVEPVOPRVFUEVFVOPQZDUFSZAGSZBGSZVFVRUIDLUGZMNABCDGHKUHTU
      JUKULUMUNVKVIVJVSVTVTVIUOSWBMMAACDGHKUPTVSWAWAVJUOSWBNNBBCDGHKUPTUQURUMUS
      VSVGGSZVHVLQWBVSVTWAWCWBMNABDEGHIUTTVGCDFGHJKVAVBVIVMVJVNRVSVTVIVMQWBMACD
      FGHJKVAVBVSWAVJVNQWBNBCDFGHJKVAVBVCVD $.
  $}

  ${
    siii.1 $e |- X = ( BaseSet ` U ) $.
    siii.6 $e |- N = ( normCV ` U ) $.
    siii.7 $e |- P = ( .iOLD ` U ) $.
    siii.9 $e |- U e. CPreHilOLD $.
    siii.a $e |- A e. X $.
    siii.b $e |- B e. X $.
    ${
      sii1.3 $e |- M = ( -v ` U ) $.
      sii1.4 $e |- S = ( .sOLD ` U ) $.
      sii1.c $e |- C e. CC $.
      sii1.r $e |- ( C x. ( A P B ) ) e. RR $.
      sii1.z $e |- 0 <_ ( C x. ( A P B ) ) $.
      $( Lemma for ~ sii .  (Contributed by NM, 23-Nov-2007.)
         (New usage is discouraged.) $)
      siilem1 $p |- ( ( B P A ) = ( C x. ( ( N ` B ) ^ 2 ) ) ->
                ( sqrt ` ( ( A P B ) x. ( C x. ( ( N ` B ) ^ 2 ) ) ) ) <_
                       ( ( N ` A ) x. ( N ` B ) ) ) $=
        ( co cfv c2 cexp cmul wceq csqrt cle wbr cc0 cmin ccj phnvi cnv wcel cc
        cjcli nvscl mp3an nvmcl nvcli sqge0i ccphlo w3a 3pm3.2i dipsubdi ipidsq
        mp2an dipass oveq2i eqtri recni sqcli dipcl mulcli sub4 mp4an dipsubdir
        oveq12i oveq1i subdii 3eqtr4i 3eqtr3i oveq2 mul01i eqtrdi sylbir oveq2d
        dipassr2 breqtri subeq0i resqcli subcli subid1i breqtrid subge0i pm3.2i
        sylib cr wa lemul1a mpan syl breqtrrdi mulge0i remulcli sqrtlei mulcomi
        sqmuli wb mulassi fveq2i nvge0 sqrtsqi ax-mp 3brtr3g ) BADUAZCBHUBZUCUD
        UAZUEUAZUFZCABDUAZUEUAZXSUEUAZUGUBZAHUBZXRUEUAZUCUDUAZUGUBZYBXTUEUAZUGU
        BYGUHYAYDYHUHUIZYEYIUHUIZYAYDYFUCUDUAZXSUEUAZYHUHYAYCYMUHUIZYDYNUHUIZYA
        UJYMYCUKUAZUHUIYOYAUJYQCULUBZXQXTUKUAZUEUAZUKUAZYQUHUJAYRBEUAZGUAZHUBZU
        CUDUAZUUAUHUUDUUCFHIJKFMUMZFUNUOZAIUOZUUBIUOZUUCIUOZUUFNUUGYRUPUOZBIUOZ
        UUIUUFCRUQZOYRBEFIJQURUSZAUUBFGIJPUTUSZVAVBUUCUUCDUAZUUCADUAZUUCUUBDUAZ
        UKUAZUUEUUAFVCUOZUUJUUHUUIVDUUPUUSUFMUUJUUHUUIUUONUUNVEUUCAUUBDFGIJPLVF
        VHUUGUUJUUPUUEUFUUFUUOUUCDFHIJKLVGVHYMYRXQUEUAZUKUAZYCUUBUUBDUAZUKUAZUK
        UAZYQUVAYRXTUEUAZUKUAZUKUAZUUSUUAUVEUVBYCUVFUKUAZUKUAZUVHUVDUVIUVBUKUVC
        UVFYCUKUVCYRBUUBDUAZUEUAZUVFUUTUUKUULUUIVDUVCUVLUFMUUKUULUUIUUMOUUNVEYR
        BUUBDEFIJQLVIVHUVKXTYRUEUVKCBBDUAZUEUAZXTUUTUULCUPUOZUULVDUVKUVNUFMUULU
        VOUULOROVEBCBDEFIJQLWIVHUVMXSCUEUUGUULUVMXSUFUUFOBDFHIJKLVGVHVJVKVJVKVJ
        VJYMUPUOUVAUPUOYCUPUOUVFUPUOUVJUVHUFYFYFAFHIJKUUFNVAZVLZVMYRXQUUMUUGUUL
        UUHXQUPUOUUFONBADFIJLVNUSZVOYCSVLZYRXTUUMCXSRXRXRBFHIJKUUFOVAZVLZVMVOZV
        OYMUVAYCUVFVPVQVKUUQUVBUURUVDUKUUQAADUAZUUBADUAZUKUAZUVBUUTUUHUUIUUHVDU
        UQUWEUFMUUHUUIUUHNUUNNVEAUUBADFGIJPLVRVHUWCYMUWDUVAUKUUGUUHUWCYMUFUUFNA
        DFHIJKLVGVHUUTUUKUULUUHVDUWDUVAUFMUUKUULUUHUUMONVEYRBADEFIJQLVIVHVSVKUU
        RAUUBDUAZUVCUKUAZUVDUUTUUHUUIUUIVDUURUWGUFMUUHUUIUUINUUNUUNVEAUUBUUBDFG
        IJPLVRVHUWFYCUVCUKUUTUUHUVOUULVDUWFYCUFMUUHUVOUULNROVEACBDEFIJQLWIVHVTV
        KVSYTUVGYQUKYRXQXTUUMUVRUWBWAVJWBWCWJYAUUAYQUJUKUAYQYAYTUJYQUKYAYSUJUFZ
        YTUJUFXQXTUVRUWBWKUWHYTYRUJUEUAUJYSUJYRUEWDYRUUMWEWFWGWHYQYMYCYMYFUVPWL
        ZVLUVSWMWNWFWOYMYCUWISWPWRYCWSUOZYMWSUOZXSWSUOZUJXSUHUIZWTZVDYOYPUWJUWK
        UWNSUWIUWLUWMXRUVTWLZXRUVTVBZWQVEYCYMXSXAXBXCYFXRUVQUWAXIXDUJYDUHUIZUJY
        HUHUIYKYLXJUJYCUHUIUWMUWQTUWPYCXSSUWOXEVHYGYFXRUVPUVTXFZVBYDYHYCXSSUWOX
        FYGUWRWLXGVHWRYDYJUGYDYBCUEUAZXSUEUAYJYCUWSXSUECYBRUUGUUHUULYBUPUOUUFNO
        ABDFIJLVNUSZXHVTYBCXSUWTRXSUWOVLXKVKXLUJYGUHUIZYIYGUFUJYFUHUIZUJXRUHUIZ
        UXAUUGUUHUXBUUFNAFHIJKXMVHUUGUULUXCUUFOBFHIJKXMVHYFXRUVPUVTXEVHYGUWRXNX
        OXP $.
    $}

    ${
      siii2.3 $e |- M = ( -v ` U ) $.
      siii2.4 $e |- S = ( .sOLD ` U ) $.
      $( Lemma for ~ sii .  (Contributed by NM, 24-Nov-2007.)
         (New usage is discouraged.) $)
      siilem2 $p |- ( ( C e. CC /\ ( C x. ( A P B ) ) e. RR /\
                           0 <_ ( C x. ( A P B ) ) ) ->
                ( ( B P A ) = ( C x. ( ( N ` B ) ^ 2 ) ) ->
                  ( sqrt ` ( ( A P B ) x. ( C x. ( ( N ` B ) ^ 2 ) ) ) ) <_
                         ( ( N ` A ) x. ( N ` B ) ) ) ) $=
        ( co cmul cc0 cc wcel cr cle wbr w3a c2 cexp wceq csqrt wi oveq1 eqeq2d
        cfv cif oveq2d fveq2d breq1d imbi12d eleq1 eleq1d 3anbi123d phnvi dipcl
        breq2d 0cn cnv mp3an mul02i 0re eqeltri breqtrri 3pm3.2i elimhyp simp1i
        0le0 simp2i simp3i siilem1 dedth ) CUAUBZCABDRZSRZUCUBZTWCUDUEZUFZBADRZ
        CBHUNZUGUHRZSRZUIZWBWJSRZUJUNZAHUNWHSRZUDUEZUKWGWFCTUOZWISRZUIZWBWQSRZU
        JUNZWNUDUEZUKCTCWPUIZWKWRWOXAXBWJWQWGCWPWISULZUMXBWMWTWNUDXBWLWSUJXBWJW
        QWBSXCUPUQURUSABWPDEFGHIJKLMNOPQWPUAUBZWPWBSRZUCUBZTXEUDUEZWFXDXFXGUFTU
        AUBZTWBSRZUCUBZTXIUDUEZUFCTXBWAXDWDXFWEXGCWPUAUTXBWCXEUCCWPWBSULZVAXBWC
        XETUDXLVEVBTWPUIZXHXDXJXFXKXGTWPUAUTXMXIXEUCTWPWBSULZVAXMXIXETUDXNVEVBX
        HXJXKVFXITUCWBFVGUBAIUBBIUBWBUAUBFMVCNOABDFIJLVDVHVIZVJVKTTXIUDVPXOVLVM
        VNZVOXDXFXGXPVQXDXFXGXPVRVSVT $.
    $}

    $( Inference from ~ sii .  (Contributed by NM, 20-Nov-2007.)
       (New usage is discouraged.) $)
    siii $p |- ( abs ` ( A P B ) ) <_ ( ( N ` A ) x. ( N ` B ) ) $=
      ( co cfv cmul cle wbr wceq cc0 wcel cabs cn0v oveq2 cnv phnvi dip0r mp2an
      eqid eqtrdi abs00bd nvge0 nvcli mulge0i eqbrtrdi wne c2 cexp csqrt ccj cc
      cdiv dipcl mp3an absval ax-mp recni sqeq0i wb nvz bitri necon3bii resqcli
      divcan1zi sylbir dipcj eqtr4di oveq2d fveq2d eqtr4id eqcomd cr wi divclzi
      wa div23 mp3an12 mpan ipipcj mulcomli oveq1i eqtr3di abscli redivclzi clt
      eqeltrd sqgt0i sqge0i divge0 mpanl12 sylancr breqtrrd cns siilem2 syl3anc
      cnsb mpd eqbrtrd pm2.61ine ) ABCMZUANZAENZBENZOMZPQBDUBNZBXNRZXJSXMPXOXIX
      OXIAXNCMZSBXNACUCDUDTZAFTZXPSRDJUEZKACDFXNGXNUHZIUFUGUIUJSXKPQZSXLPQZSXMP
      QXQXRYAXSKADEFGHUKUGXQBFTZYBXSLBDEFGHUKUGXKXLADEFGHXSKULBDEFGHXSLULZUMUGU
      NBXNUOZXJXIBACMZXLUPUQMZVAMZYGOMZOMZURNZXMPYEXJXIXIUSNZOMZURNZYKXIUTTZXJY
      NRXQXRYCYOXSKLABCDFGIVBVCZXIVDVEYEYJYMURYEYIYLXIOYEYIYFYLYEYGSUOZYIYFRYGS
      BXNYGSRXLSRZXOXLXLYDVFVGXQYCYRXOVHXSLBDEFXNGXTHVIUGZVJVKZYFYGXQYCXRYFUTTZ
      XSLKBACDFGIVBVCZYGXLYDVLZVFZVMVNZXQXRYCYLYFRXSKLABCDFGIVOVCVPVQVRVSYEYFYI
      RZYKXMPQZYEYIYFUUEVTYEYHUTTZYHXIOMZWATSUUIPQUUFUUGWBYEYQUUHYTYFYGUUBUUDWC
      VNYEUUIXJUPUQMZYGVAMZWAYEYFXIOMZYGVAMZUUIUUKYEYQUUMUUIRZYTYGUTTZYQUUNUUDU
      UAYOUUOYQWDUUNUUBYPYFXIYGWEWFWGVNUULUUJYGVAXIYFUUJYPUUBXQXRYCXIYFOMUUJRXS
      KLABCDFGIWHVCWIWJWKZYEYQUUKWATYTUUJYGXJXIYPWLZVLZUUCWMVNWOYESUUKUUIPYEYGW
      ATZSYGWNQZSUUKPQZUUCYEXLSUOUUTXLSBXNYSVKXLYDWPVNUUJWATSUUJPQUUSUUTWDUVAUU
      RXJUUQWQUUJYGWRWSWTUUPXAABYHCDXBNZDDXENZEFGHIJKLUVCUHUVBUHXCXDXFXGXH $.
  $}

  ${
    sii.1 $e |- X = ( BaseSet ` U ) $.
    sii.6 $e |- N = ( normCV ` U ) $.
    sii.7 $e |- P = ( .iOLD ` U ) $.
    sii.9 $e |- U e. CPreHilOLD $.
    $( Obsolete version of ~ ipcau as of 22-Sep-2024.  Schwarz inequality.
       Part of Lemma 3-2.1(a) of [Kreyszig] p. 137.  This is also called the
       Cauchy-Schwarz inequality by some authors and
       Bunjakovaskij-Cauchy-Schwarz inequality by others.  See also Theorems
       ~ bcseqi , ~ bcsiALT , ~ bcsiHIL , ~ csbren .  (Contributed by NM,
       12-Jan-2008.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    sii $p |- ( ( A e. X /\ B e. X ) ->
               ( abs ` ( A P B ) ) <_ ( ( N ` A ) x. ( N ` B ) ) ) $=
      ( wcel co cabs cfv cmul cle wbr cif wceq fveq2 cn0v fvoveq1 breq12d oveq2
      oveq1d fveq2d oveq2d eqid elimph siii dedth2h ) AFKZBFKZABCLMNZAENZBENZOL
      ZPQULADUANZRZBCLZMNZUSENZUPOLZPQUSUMBURRZCLZMNZVBVDENZOLZPQABURURAUSSZUNV
      AUQVCPAUSBMCUBVIUOVBUPOAUSETUEUCBVDSZVAVFVCVHPVJUTVEMBVDUSCUDUFVJUPVGVBOB
      VDETUGUCUSVDCDEFGHIJADFURGURUHZJUIBDFURGVKJUIUJUK $.
  $}

  ${
    $d w x y z A $.  $d w y z C $.  $d w y z F $.  $d w x y z U $.
    $d w x y z X $.  $d x P $.  $d z B $.
    ipblnfi.1 $e |- X = ( BaseSet ` U ) $.
    ipblnfi.7 $e |- P = ( .iOLD ` U ) $.
    ipblnfi.9 $e |- U e. CPreHilOLD $.
    ipblnfi.c $e |- C = <. <. + , x. >. , abs >. $.
    ipblnfi.l $e |- B = ( U BLnOp C ) $.
    ipblnfi.f $e |- F = ( x e. X |-> ( x P A ) ) $.
    $( A function ` F ` generated by varying the first argument of an inner
       product (with its second argument a fixed vector ` A ` ) is a bounded
       linear functional, i.e. a bounded linear operator from the vector space
       to ` CC ` .  (Contributed by NM, 12-Jan-2008.)  (Revised by Mario
       Carneiro, 19-Nov-2013.)  (New usage is discouraged.) $)
    ipblnfi $p |- ( A e. X -> F e. B ) $=
      ( vz wcel co cfv cc wceq vy vw clno cnmcv cr cv cabs cmul cle wbr wral wf
      cns cpv caddc cnv phnvi dipcl mp3an1 ancoms fmptd wa eqid nvscl ad2ant2lr
      simprr simpll ccphlo w3a dipdir syl3anc simplr simprl ipassi oveq1d eqtrd
      mpan adantll nvgcl sylan anasss oveq1 ovex fvmpt ad2antrl oveq2d ad2antll
      syl oveq12d 3eqtr4d ralrimivva ralrimiva wb cnnv cnnvba cnnvg cnnvs islno
      mp2an sylanbrc sii adantl fveq2d recnd mulcom syl2an 3brtr4d cnnvnm blo3i
      nvcl ) BHPZGFDUCQZPZBFUDRZRZUEPZOUFZGRZUGRZXOXQXNRZUHQZUIUJZOHUKGCPXKHSGU
      LZUAUFZXQFUMRZQZUBUFZFUNRZQZGRZYDXRUHQZYGGRZUOQZTZUBHUKOHUKZUASUKZXMXKAHA
      UFZBEQZSGYQHPZXKYRSPZFUPPZYSXKYTFKUQZYQBEFHIJURUSUTNVAXKYOUASXKYDSPZVBZYN
      OUBHHUUDXQHPZYGHPZVBZVBZYIBEQZYDXQBEQZUHQZYGBEQZUOQZYJYMUUHUUIYFBEQZUULUO
      QZUUMUUHYFHPZUUFXKUUIUUOTZUUCUUEUUPXKUUFUUAUUCUUEUUPUUBYDXQYEFHIYEVCZVDUS
      ZVEUUDUUEUUFVFXKUUCUUGVGZFVHPUUPUUFXKVIUUQKYFYGBEFYHHIYHVCZJVJVQVKUUHUUNU
      UKUULUOUUHUUCUUEXKUUNUUKTXKUUCUUGVLUUDUUEUUFVMUUTYDXQBEYEFYHHIUVAUURJKVNV
      KVOVPUUHYIHPZYJUUITUUDUUEUUFUVBUUDUUEVBUUPUUFUVBUUCUUEUUPXKUUSVRUUAUUPUUF
      UVBUUBYFYGFYHHIUVAVSUSVTWAAYIYRUUIHGYQYIBEWBNYIBEWCWDWHUUHYKUUKYLUULUOUUH
      XRUUJYDUHUUEXRUUJTZUUDUUFAXQYRUUJHGYQXQBEWBNXQBEWCWDZWEWFUUFYLUULTUUDUUEA
      YGYRUULHGYQYGBEWBNYGBEWCWDWGWIWJWKWLUUADUPPXMYCYPVBWMUUBDLWNZUAOUBYEUHGFY
      HUOXLDHSIDLWOUVADLWPUURDLWQXLVCZWRWSWTUUAXKXPUUBBFXNHIXNVCZXJVQZXKYBOHXKU
      UEVBZUUJUGRZXTXOUHQZXSYAUIUUEXKUVJUVKUIUJXQBEFXNHIUVGJKXAUTUVIXRUUJUGUUEU
      VCXKUVDXBXCXKXOSPXTSPYAUVKTUUEXKXOUVHXDUUEXTUUAUUEXTUEPUUBXQFXNHIUVGXJVQX
      DXOXTXEXFXGWLOXOCGFXLXNUGDHIUVGDLXHUVFMUUBUVEXIVK $.
  $}

  ${
    $d x A $.  $d x B $.  $d s t x P $.  $d s t Q $.  $d x y S $.
    $d s t x y T $.  $d x U $.  $d s t x y X $.  $d s t x y Y $.
    ip2eqi.1 $e |- X = ( BaseSet ` U ) $.
    ip2eqi.7 $e |- P = ( .iOLD ` U ) $.
    ip2eqi.u $e |- U e. CPreHilOLD $.
    $( Two vectors are equal iff their inner products with all other vectors
       are equal.  (Contributed by NM, 24-Jan-2008.)
       (New usage is discouraged.) $)
    ip2eqi $p |- ( ( A e. X /\ B e. X ) -> ( A. x e. X ( x P A
                                               ) = ( x P B ) <-> A = B ) ) $=
      ( wcel co wceq cfv eqid mp3an1 oveq1 syl cc0 mpan wb wa cv wral cnv phnvi
      cnsb wi nvmcl eqeq12d rspcv cmin cn0v simpl simpr ccphlo dipsubdi syl3anc
      w3a eqeq1d bitr3d cc dipcl syl2anc sylancom subeq0ad nvmeq0 3bitr3d oveq2
      ipz sylibd ralrimivw impbid1 ) BFJZCFJZUAZAUBZBDKZVPCDKZLZAFUCZBCLZVOVTBC
      EUFMZKZBDKZWCCDKZLZWAVOWCFJZVTWFUGEUDJZVMVNWGEIUEZBCEWBFGWBNZUHOZVSWFAWCF
      VPWCLVQWDVRWEVPWCBDPVPWCCDPUIUJQVOWDWEUKKZRLZWCEULMZLZWFWAVOWCWCDKZRLZWMW
      OVOWPWLRVOWGVMVNWPWLLZWKVMVNUMZVMVNUNEUOJWGVMVNURWRIWCBCDEWBFGWJHUPSUQUSV
      OWGWQWOTZWKWHWGWTWIWCDEFWNGWNNZHVISQUTVOWDWEVOWGVMWDVAJZWKWSWHWGVMXBWIWCB
      DEFGHVBOVCVMVNWGWEVAJZWKWHWGVNXCWIWCCDEFGHVBOVDVEWHVMVNWOWATWIBCEWBFWNGWJ
      XAVFOVGVJWAVSAFBCVPDVHVKVL $.

    $( A condition implying that two operators are equal.  (Contributed by NM,
       25-Jan-2008.)  (New usage is discouraged.) $)
    phoeqi $p |- ( ( S : Y --> X /\ T : Y --> X ) -> ( A. x e. X A. y e.
      Y ( x P ( S ` y ) ) = ( x P ( T ` y ) ) <-> S = T ) ) $=
      ( cv cfv co wceq wral wf wa wcel wb ralcom ffvelcdm anandirs ralbidva wfn
      ip2eqi syl2an ffn eqfnfv bitr4d bitrid ) ALZBLZDMZCNULUMEMZCNOZBHPAGPUPAG
      PZBHPZHGDQZHGEQZRZDEOZUPABGHUAVAURUNUOOZBHPZVBVAUQVCBHUSUTUMHSZUQVCTZUSVE
      RUNGSUOGSVFUTVERHGUMDUBHGUMEUBAUNUOCFGIJKUFUGUCUDUSDHUEEHUEVBVDTUTHGDUHHG
      EUHBHDEUIUGUJUK $.

    $( Every operator has at most one adjoint.  (Contributed by NM,
       25-Jan-2008.)  (New usage is discouraged.) $)
    ajmoi $p |- E* s ( s : Y --> X /\
           A. x e. X A. y e. Y ( ( T ` x ) Q y ) = ( x P ( s ` y ) ) ) $=
      ( vt cv wf cfv co wceq wral wa wmo wi r19.26-2 eqtr2 sylbir phoeqi biimpa
      wal 2ralimi sylan2 an4s gen2 feq1 fveq1 oveq2d 2ralbidv anbi12d mo4 mpbir
      eqeq2d ) HGINZOZANZEPBNZDQZVCVDVAPZCQZRZBHSAGSZTZIUAVJHGMNZOZVEVCVDVKPZCQ
      ZRZBHSAGSZTZTVAVKRZUBZMUHIUHVSIMVBVLVIVPVRVIVPTZVBVLTZVGVNRZBHSAGSZVRVTVH
      VOTZBHSAGSWCVHVOABGHUCWDWBABGHVEVGVNUDUIUEWAWCVRABCVAVKFGHJKLUFUGUJUKULVJ
      VQIMVRVBVLVIVPHGVAVKUMVRVHVOABGHVRVGVNVEVRVFVMVCCVDVAVKUNUOUTUPUQURUS $.
  $}

  ${
    $d s t x y U $.  $d s t x y W $.
    ajfuni.5 $e |- A = ( U adj W ) $.
    ajfuni.u $e |- U e. CPreHilOLD $.
    ajfuni.w $e |- W e. NrmCVec $.
    $( The adjoint function is a function.  (Contributed by NM, 25-Jan-2008.)
       (New usage is discouraged.) $)
    ajfuni $p |- Fun A $=
      ( vt vs vx vy wfun cba cfv cv wf cdip co wceq wral eqid w3a copab funopab
      wmo wa ajmoi 3simpc moimi ax-mp mpgbir cnv wcel phnvi ajfval mp2an funeqi
      mpbir ) AKBLMZCLMZGNZOZUSURHNZOZINZUTMJNZCPMZQVDVEVBMBPMZQRJUSSIURSZUAZGH
      UBZKZVKVIHUDZGVIGHUCVCVHUEZHUDVLIJVGVFUTBURUSHURTZVGTZEUFVIVMHVAVCVHUGUHU
      IUJAVJBUKULCUKULAVJRBEUMFIJGAVGVFBCURUSHVNUSTVOVFTDUNUOUPUQ $.
  $}

  ${
    ajfun.5 $e |- A = ( U adj W ) $.
    $( The adjoint function is a function.  This is not immediately apparent
       from ~ df-aj but results from the uniqueness shown by ~ ajmoi .
       (Contributed by NM, 26-Jan-2008.)  (New usage is discouraged.) $)
    ajfun $p |- ( ( U e. CPreHilOLD /\ W e. NrmCVec ) -> Fun A ) $=
      ( ccphlo wcel cnv wfun caddc cmul cop cabs cif caj co oveq1 eqtrid funeqd
      wceq oveq2 eqid elimphu elimnvu ajfuni dedth2h ) BEFZCGFZAHUFBIJKLKZMZCNO
      ZHUIUGCUHMZNOZHBCUHUHBUISZAUJUMABCNOUJDBUICNPQRCUKSUJULCUKUINTRULUIUKULUA
      BUBCUCUDUE $.
  $}

  ${
    $d t P $.  $d t Q $.  $d s t x y T $.  $d s t x y U $.  $d s t x y W $.
    $d s t x y X $.  $d s t y Y $.
    ajval.1 $e |- X = ( BaseSet ` U ) $.
    ajval.2 $e |- Y = ( BaseSet ` W ) $.
    ajval.3 $e |- P = ( .iOLD ` U ) $.
    ajval.4 $e |- Q = ( .iOLD ` W ) $.
    ajval.5 $e |- A = ( U adj W ) $.
    $( Value of the adjoint function.  (Contributed by NM, 25-Jan-2008.)
       (New usage is discouraged.) $)
    ajval $p |- ( ( U e. CPreHilOLD /\ W e. NrmCVec /\ T : X --> Y ) ->
       ( A ` T ) = ( iota s ( s : Y --> X /\
          A. x e. X A. y e. Y ( ( T ` x ) Q y ) = ( x P ( s ` y ) ) ) ) ) $=
      ( vt wcel cfv wceq ccphlo cnv wf w3a cv co wral copab wa cio ajfval sylan
      phnv fveq1d 3adant3 cvv cba fvexi fex mpan2 eqid feq1 fveq1 oveq1d eqeq1d
      2ralbidv 3anbi13d fvopab5 syl 3anass baib iotabidv eqtrd 3ad2ant3 ) GUARZ
      HUBRZIJFUCZUDFCSZFIJQUEZUCZJIKUEZUCZAUEZVSSZBUEZEUFZWCWEWASDUFZTZBJUGAIUG
      ZUDZQKUHZSZWBWCFSZWEEUFZWGTZBJUGAIUGZUIZKUJZVOVPVRWLTVQVOVPUIFCWKVOGUBRVP
      CWKTGUMABQCDEGHIJKLMNOPUKULUNUOVQVOWLWRTVPVQWLVQWBWPUDZKUJZWRVQFUPRZWLWTT
      VQIUPRXAIGUQLURIJUPFUSUTWJWSQKFWKUPWKVAVSFTZVTVQWIWPWBIJVSFVBXBWHWOABIJXB
      WFWNWGXBWDWMWEEWCVSFVCVDVEVFVGVHVIVQWSWQKWSVQWQVQWBWPVJVKVLVMVNVM $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Complex Banach spaces
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definition and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c CBan $.

  $( Extend class notation with the class of all complex Banach spaces. $)
  ccbn $a class CBan $.

  $( Define the class of all complex Banach spaces.  (Contributed by NM,
     5-Dec-2006.)  Use ~ df-bn instead.  (New usage is discouraged.) $)
  df-cbn $a |- CBan = { u e. NrmCVec |
    ( IndMet ` u ) e. ( CMet ` ( BaseSet ` u ) ) } $.

  ${
    $d u D $.  $d u U $.  $d u X $.
    iscbn.x $e |- X = ( BaseSet ` U ) $.
    iscbn.8 $e |- D = ( IndMet ` U ) $.
    $( A complex Banach space is a normed complex vector space with a complete
       induced metric.  (Contributed by NM, 5-Dec-2006.)  Use ~ isbn instead.
       (New usage is discouraged.) $)
    iscbn $p |- ( U e. CBan <-> ( U e. NrmCVec /\ D e. ( CMet ` X ) ) ) $=
      ( vu cv cims cfv cba ccmet wcel cnv ccbn wceq fveq2 eqtr4di fveq2d df-cbn
      eleq12d elrab2 ) FGZHIZUBJIZKIZLACKIZLFBMNUBBOZUCAUEUFUGUCBHIAUBBHPEQUGUD
      CKUGUDBJICUBBJPDQRTFSUA $.

    $( The induced metric on complex Banach space is complete.  (Contributed by
       NM, 8-Sep-2007.)  Use ~ bncmet (or preferably ~ bncms ) instead.
       (New usage is discouraged.) $)
    cbncms $p |- ( U e. CBan -> D e. ( CMet ` X ) ) $=
      ( ccbn wcel cnv ccmet cfv iscbn simprbi ) BFGBHGACIJGABCDEKL $.
  $}

  $( Every complex Banach space is a normed complex vector space.  (Contributed
     by NM, 17-Mar-2007.)  Use ~ bnnvc instead.  (New usage is discouraged.) $)
  bnnv $p |- ( U e. CBan -> U e. NrmCVec ) $=
    ( ccbn wcel cnv cims cfv cba ccmet eqid iscbn simplbi ) ABCADCAEFZAGFZHFCLA
    MMILIJK $.

  $( The class of all complex Banach spaces is a relation.  (Contributed by NM,
     17-Mar-2007.)  (New usage is discouraged.) $)
  bnrel $p |- Rel CBan $=
    ( vx ccbn cnv wss wrel cv bnnv ssriv nvrel relss mp2 ) BCDCEBEABCAFGHIBCJK
    $.

  ${
    bnsscmcl.x $e |- X = ( BaseSet ` U ) $.
    bnsscmcl.d $e |- D = ( IndMet ` U ) $.
    bnsscmcl.j $e |- J = ( MetOpen ` D ) $.
    bnsscmcl.h $e |- H = ( SubSp ` U ) $.
    bnsscmcl.y $e |- Y = ( BaseSet ` W ) $.
    $( A subspace of a Banach space is a Banach space iff it is closed in the
       norm-induced metric of the parent space.  (Contributed by NM,
       1-Feb-2008.)  (New usage is discouraged.) $)
    bnsscmcl $p |- ( ( U e. CBan /\ W e. H ) -> ( W e. CBan <->
                Y e. ( Clsd ` J ) ) ) $=
      ( ccbn wcel cfv ccmet cnv wb sylan syl cims cxp cres ccld bnnv sspnv eqid
      wa iscbn baib wceq sspims eleq1d cbncms adantr cmetss 3bitrd ) BMNZECNZUH
      ZEMNZEUAOZGPOZNZAGGUBUCZVCNZGDUDONZUTEQNZVAVDRURBQNZUSVHBUEZBCEKUFSVAVHVD
      VBEGLVBUGZUIUJTUTVBVEVCURVIUSVBVEUKVJVBABCEGLIVKKULSUMUTAFPONZVFVGRURVLUS
      ABFHIUNUOADFGJUPTUQ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Examples of complex Banach spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    cnbn.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The set of complex numbers is a complex Banach space.  (Contributed by
       Steve Rodriguez, 4-Jan-2007.)  (New usage is discouraged.) $)
    cnbn $p |- U e. CBan $=
      ( ccbn wcel cnv caddc cmul cop cabs cims cfv cc ccmet cnnv cmin ccom eqid
      cnims eqcomi cncmet cnnvba fveq2i iscbn mpbir2an ) ACDAEDFGHIHZJKZLMKDABN
      UFIOPZUFUGUEUEQUGQRSTUFALABUAAJKUFAUEJBUBSUCUD $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Uniform Boundedness Theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d c k n r x y z A $.  $d c k n r t x z D $.  $d k n t x y J $.
    $d d k t x z K $.  $d c d k m n r t u x y z N $.  $d t z P $.
    $d c k n r t x y ph $.  $d d t x z R $.  $d c d k m n r t u x y z T $.
    $d c d n r t x y z U $.  $d c d n r t x y W $.  $d c d k m n r t x y z X $.
    ubth.1 $e |- X = ( BaseSet ` U ) $.
    ubth.2 $e |- N = ( normCV ` W ) $.
    ${
      ubthlem.3 $e |- D = ( IndMet ` U ) $.
      ubthlem.4 $e |- J = ( MetOpen ` D ) $.
      ubthlem.5 $e |- U e. CBan $.
      ubthlem.6 $e |- W e. NrmCVec $.
      ubthlem.7 $e |- ( ph -> T C_ ( U BLnOp W ) ) $.
      ${
        ubthlem.8 $e |- ( ph -> A. x e. X E. c e. RR A. t e. T
                                ( N ` ( t ` x ) ) <_ c ) $.
        ubthlem.9 $e |- A = ( k e. NN |-> { z e. X |
                              A. t e. T ( N ` ( t ` z ) ) <_ k } ) $.
        $( Lemma for ~ ubth .  The function ` A ` exhibits a countable
           collection of sets that are closed, being the inverse image under
           ` t ` of the closed ball of radius ` k ` , and by assumption they
           cover ` X ` .  Thus, by the Baire Category theorem ~ bcth2 , for
           some ` n ` the set ` A `` n ` has an interior, meaning that there is
           a closed ball ` { z e. X | ( y D z ) <_ r } ` in the set.
           (Contributed by Mario Carneiro, 11-Jan-2014.)
           (New usage is discouraged.) $)
        ubthlem1 $p |- ( ph -> E. n e. NN E. y e. X E. r e. RR+
                        { z e. X | ( y D z ) <_ r } C_ ( A ` n ) ) $=
          ( cv cfv cnt c0 wne cn wrex co cle wbr crab wss crp ccld wf cuni wceq
          wral wcel wa rzal ralrimivw rabid2 sylibr eqcomd eleq1d iinrab adantl
          crn ciin ccnv cba cima cims cmopn cblo sselda ccn eqid ccbn cnv ax-mp
          id bnnv blocn2 ctopon wb cxmet ccmet cmet cbncms cmetmet metxmet mp2b
          mopntopon imsxmet iscncl mp2an sylib syl adantlr ffvelcdmda biantrurd
          simpld fveq2 breq1d elrab bitr4di pm5.32da 2fveq3 a1i wfn ffn cr cn0v
          cxr nvzcl mp3an12 clt wi simpr syl2an adantr sylancr ralimdva elssuni
          cvv sseld sylan rexlimdva mpd wex sstr2 ex elpreima 3syl eqrdv imaeq2
          3bitr4d simprd nnre ad2antlr nvnd mpan xmetsym eqtr4d rabbiia rspcdva
          rexrd blcld eqeltrd ralrimiva syl2anr eqeltrrd ctop mopntop toponunii
          iincld topcld pm2.61ne fmptd cpw frnd cldss2 sstrdi sspwuni arch ltle
          impr an32s nvcl simpllr simplrl letr syl3anc mpan2d expr fvexi fvmpt2
          rabex mpan2 eleq2d ralbidv bitrdi bicomd sylan9bbr ffnd sylbird syl6d
          fnfvelrn dfss3 eqssd ne0i bcth2 mpanl12 ffvelcdm sselid elpwid ntrss3
          syl2anc cbl ntropn mopni2 mp3an1 sseqtrrdi c2 ntrss2 syl5com ad2antrr
          cdiv w3a jctil rphalfcl rpxrd rpxr rphalflt 3jca breq2 rabbidv sseq1d
          blsscls2 rspcev 3syld syldan jcad eximdv n0 df-rex 3imtr4g reximdva )
          AKUGZFUHZLUIUHUHZUJUKZKULUMZCUGZDUGZGUNZPUGZUOUPZDOUQZUYRURZPUSUMZCOU
          MZKULUMAULLUTUHZFVAZFVOZVBZOVCZVUAAJULVUCEUGZUHMUHZJUGZUOUPZEHVDZDOUQ
          ZVUKFAVURULVEZVFZVVAVUKVEOVUKVEZHUJHUJVCZVVAOVUKVVEOVVAVVEVUTDOVDOVVA
          VCVVEVUTDOVUSEHVGVHVUTDOVIVJVKVLVVCHUJUKZVFEHVUSDOUQZVPZVVAVUKVVFVVHV
          VAVCVVCVUSEDHOVMVNVVFVVFVVGVUKVEZEHVDVVHVUKVEVVCVVFWIVVCVVIEHVVCVUPHV
          EZVFZVVGVUPVQZVUBMUHZVURUOUPZCNVRUHZUQZVSZVUKVVKBVVGVVQVVKBUGZOVEZVVR
          VUPUHZMUHZVURUOUPZVFZVVSVVTVVPVEZVFZVVRVVGVEZVVRVVQVEZVVKVVSVWBVWDVVK
          VVSVFZVWBVVTVVOVEZVWBVFVWDVWHVWIVWBVVKOVVOVVRVUPAVVJOVVOVUPVAZVVBAVVJ
          VFZVWJVVLVVRVSZVUKVEZBNVTUHZWAUHZUTUHZVDZVWKVUPINWBUNZVEZVWJVWQVFZAHV
          WRVUPUDWCVWSVUPLVWOWDUNVEZVWTVWRGVWNVUPILVWONTVWNWEZUAVWOWEZVWRWEIWFV
          EZIWGVEZUBIWJWHZUCWKLOWLUHVEZVWOVVOWLUHVEZVXAVWTWMGOWNUHVEZVXGGOWOUHV
          EZGOWPUHVEVXIVXDVXJUBGIORTWQWHZGOWRGOWSWTZGLOUAXAWHZVWNVVOWNUHVEZVXHN
          WGVEZVXNUCVWNNVVOVVOWEZVXBXBWHZVWNVWOVVOVXCXAWHBVUPLVWOOVVOXCXDXEXFZX
          JZXGZXHXIVVNVWBCVVTVVOVUBVVTVCVVMVWAVURUOVUBVVTMXKXLXMXNXOVWFVWCWMVVK
          VUSVWBDVVROVUCVVRVCZVUQVWAVURUOVUCVVRMVUPXPXLZXMXQVVKVWJVUPOXRVWGVWEW
          MVXTOVVOVUPXSOVVRVVPVUPUUAUUBUUEUUCVVKVWMVVQVUKVEBVWPVVPVVRVVPVCVWLVV
          QVUKVVRVVPVVLUUDVLAVVJVWQVVBVWKVWJVWQVXRUUFXGVVKVURYBVEZVVPVWPVEZVVKV
          URVVBVURXTVEZAVVJVURUUGZUUHUUOVXNNYAUHZVVOVEZVYCVYDVXQVXOVYHUCNVVOVYG
          VXPVYGWEZYCWHZCVWNVYGVURVVPVWOVVOVXCVVNVYGVUBVWNUNZVURUOUPCVVOVUBVVOV
          EZVVMVYKVURUOVYLVVMVUBVYGVWNUNZVYKVXOVYLVVMVYMVCUCVUBVWNNMVVOVYGVXPVY
          ISVXBUUIUUJVXNVYHVYLVYKVYMVCVXQVYJVYGVUBVWNVVOUUKYDUULXLUUMUUPYDXFUUN
          UUQUUREHVVGLUVDUUSUUTVVDVVCLUVAVEZVVDVXIVYNVXLGLOUAUVBWHZLOOLVXMUVCZU
          VEWHXQUVFUFUVGZAVUNOAVUMOUVHZURVUNOURAVUMVUKVYRAULVUKFVYQUVILOVYPUVJZ
          UVKVUMOUVLXEAVVRVUNVEZBOVDZOVUNURAVWAQUGZUOUPZEHVDZQXTUMZBOVDWUAUEAWU
          EVYTBOAVVSVFZWUDVYTQXTWUFWUBXTVEZVFZWUBVURYEUPZJULUMZWUDVYTYFZWUGWUJW
          UFWUBJUVMVNWUHWUIWUKJULWUHVVBVFWUIWUDVWBEHVDZVYTWUHVVBWUIWUDWULYFWUHV
          VBWUIVFZVFZWUCVWBEHWUNVVJVFZWUCWUBVURUOUPZVWBWUNWUPVVJWUHVVBWUIWUPWUH
          WUGVYEWUIWUPYFVVBWUFWUGYGVYFWUBVURUVNYHUVOYIWUOVWAXTVEZWUGVYEWUCWUPVF
          VWBYFWUHVVJWUQWUMWUFVVJWUQWUGWUFVVJVFVXOVWIWUQUCAVVJVVSVWIVWKOVVOVVRV
          UPVXSXHUVPVVTNMVVOVXPSUVQYJXGXGWUFWUGWUMVVJUVRWUOVVBVYEWUHVVBWUIVVJUV
          SVYFXFVWAWUBVURUVTUWAUWBYKUWCWUFVVBWULVYTYFWUGWUFVVBVFWULVVRVURFUHZVE
          ZVYTVVBWUSVVSWULVFZWUFWULVVBWUSVVRVVAVEWUTVVBWURVVAVVRVVBVVAYMVEWURVV
          AVCVUTDOOIVRRUWDUWFJULVVAYMFUFUWEUWGUWHVUTWULDVVROVYAVUSVWBEHVYBUWIXM
          UWJWUFWULWUTWUFVVSWULAVVSYGXIUWKUWLWUFFULXRZVVBWUSVYTYFAWVAVVSAULVUKF
          VYQUWMYIWVAVVBVFZWURVUNVVRWVBWURVUMVEWURVUNURULVURFUWPWURVUMYLXFYNYOU
          WNXGUWOYPYQYPYKYQBOVUNUWQVJUWRVXJOUJUKZVULVUOVFVUAVXKVXEIYAUHZOVEWVCV
          XFIOWVDRWVDWEYCOWVDUWSWTGKLFOUAUWTUXAUXFAUYTVUJKULAUYQULVEZVFZVUBUYSV
          EZCYRVUBOVEZVUIVFZCYRUYTVUJWVFWVGWVICWVFWVGWVHVUIWVFUYSOVUBWVFVYNUYRO
          URZUYSOURZVYOAVULWVEWVJVYQVULWVEVFZUYROWVLVUKVYRUYRVYSULVUKUYQFUXBUXC
          UXDYOZUYRLOVYPUXEYJYNWVFWVGVUIWVFWVGVFVUBVVRGUXGUHUNZUYSURZBUSUMZVUIW
          VFUYSLVEZWVGWVPWVFVYNWVJWVQVYOWVMUYRLOVYPUXHYJZVXIWVQWVGWVPVXLBUYSGVU
          BLOUAUXIUXJYOWVFWVGWVHWVPVUIYFWVFUYSOVUBWVFWVQWVKWVRWVQUYSLVBOUYSLYLV
          YPUXKXFWCWVFWVHVFZWVOVUIBUSWVSVVRUSVEZVFZWVOWVNUYRURZVUDVVRUXLUXPUNZU
          OUPZDOUQZUYRURZVUIWVFWVOWWBYFWVHWVTWVFUYSUYRURZWVOWWBWVFVYNWVJWWGVYOW
          VMUYRLOVYPUXMYJWVNUYSUYRYSUXNUXOWWAWWEWVNURZWWBWWFYFWVSVXIWVHVFWWCYBV
          EZVVRYBVEZWWCVVRYEUPZUXQWWHWVTWVSWVHVXIWVFWVHYGVXLUXRWVTWWIWWJWWKWVTW
          WCVVRUXSZUXTVVRUYAVVRUYBUYCDGVUBWWCWWEVVRLOUAWWEWEUYGYHWWEWVNUYRYSXFW
          WAWWCUSVEZWWFVUIYFWVTWWMWVSWWLVNWWMWWFVUIVUHWWFPWWCUSVUEWWCVCZVUGWWEU
          YRWWNVUFWWDDOVUEWWCVUDUOUYDUYEUYFUYHYTXFUYIYPUYJYQYTUYKUYLCUYSUYMVUIC
          OUYNUYOUYPYQ $.

        ubthlem.10 $e |- ( ph -> K e. NN ) $.
        ubthlem.11 $e |- ( ph -> P e. X ) $.
        ubthlem.12 $e |- ( ph -> R e. RR+ ) $.
        ubthlem.13 $e |- ( ph -> { z e. X | ( P D z ) <_ R } C_ ( A ` K ) ) $.
        $( Lemma for ~ ubth .  Given that there is a closed ball
           ` B ( P , R ) ` in ` A `` K ` , for any ` x e. B ( 0 , 1 ) ` , we
           have ` P + R x. x e. B ( P , R ) ` and ` P e. B ( P , R ) ` , so
           both of these have ` norm ( t ( z ) ) <_ K ` and so ` norm ( t ( x `
           ` ) ) <_ ( norm ( t ( P ) ) + norm ( t ( P + R x. x ) ) ) / R <_ ( `
           ` K + K ) / R ` , which is our desired uniform bound.  (Contributed
           by Mario Carneiro, 11-Jan-2014.)  (New usage is discouraged.) $)
        ubthlem2 $p |- ( ph -> E. d e. RR A. t e. T
                         ( ( U normOpOLD W ) ` t ) <_ d ) $=
          ( caddc co cdiv cr wcel cv cnmoo cfv cle wbr wral wrex nnrpd rpaddcld
          rpdivcld rpred wa cnmcv c1 wi cns cpv wceq oveq2 breq1d eleq1 imbi12d
          crab wss rabss sylib ad2antrr cnv ccbn bnnv ax-mp a1i crp rpcnd simpr
          cc eqid nvscl syl3anc nvgcl rspcdva cmul cnsb cxmet ccmet cmet cbncms
          cmetmet metxmet mp2b xmetsym imsdval nvpncan2 fveq2d 3eqtrd cc0 eqtrd
          rprege0d nvsge0 mulridd eqcomd breq12d nvcl mpan adantl lemul2d wb cn
          1red ralbidv cba 2fveq3 elrab sylancr adantr ccld mopntopon ffvelcdmd
          syl ctopon syl32anc syld ralrimiva syl2anc bitr4d breq2 rabbidv fvexi
          rabex fvmpt eleq2d bitrdi 3imtr3d com12 ad2antlr xmet0 rpge0d eqbrtrd
          rsp sylanbrc sseldd eleqtrd simprd r19.21bi ccnv cima cims cmopn cblo
          wf sselda ccn blocn2 iscncl mp2an simpld nnred le2add syl22anc mpan2d
          imsxmet clno mp3an12 lnosub lnomul 3eqtr3d ffvelcdmda nvmtri eqbrtrrd
          bloln remulcld readdcld letr mpand lemuldiv2d sylibd cxr rpxrd nmoubi
          adantld mpbird brralrspcev ) AMMULUMZHUNUMZUOUPDUQZJOURUMZUSZUWTUTVAZ
          DIVBUXCRUQUTVADIVBRUOVCAUWTAUWSHAMMAMUHVDZUXEVEZUJVFZVGAUXDDIAUXAIUPZ
          VHZUXDBUQZJVIUSZUSZVJUTVAZUXJUXAUSZNUSZUWTUTVAZVKZBPVBZUXIUXQBPUXIUXJ
          PUPZVHZUXMGHUXJJVLUSZUMZJVMUSZUMZPUPZUYDUXAUSZNUSZMUTVAZDIVBZVHZUXPUX
          TGUYDFUMZHUTVAZUYDMEUSZUPZUXMUYJUXTGCUQZFUMZHUTVAZUYOUYMUPZVKZUYLUYNV
          KCPUYDUYOUYDVNZUYQUYLUYRUYNUYTUYPUYKHUTUYOUYDGFVOVPUYOUYDUYMVQVRAUYSC
          PVBZUXHUXSAUYQCPVSZUYMVTVUAUKUYQCPUYMWAWBWCUXTJWDUPZGPUPZUYBPUPZUYEVU
          CUXTJWEUPZVUCUCJWFWGZWHZAVUDUXHUXSUIWCZUXTVUCHWLUPZUXSVUEVUHUXTHAHWIU
          PUXHUXSUJWCZWJZUXIUXSWKZHUXJUYAJPSUYAWMZWNWOZGUYBJUYCPSUYCWMZWPWOZWQU
          XTUYLHUXLWRUMZHVJWRUMZUTVAUXMUXTUYKVURHVUSUTUXTUYKUYBUXKUSZVURUXTUYKU
          YDGFUMZUYDGJWSUSZUMZUXKUSZVUTUXTFPWTUSUPZVUDUYEUYKVVAVNVVEUXTFPXAUSUP
          ZFPXBUSUPVVEVUFVVFUCFJPSUAXCWGFPXDFPXEXFZWHVUIVUQGUYDFPXGWOUXTVUCUYEV
          UDVVAVVDVNVUHVUQVUIUYDGFJVVBUXKPSVVBWMZUXKWMZUAXHWOUXTVVCUYBUXKUXTVUC
          VUDVUEVVCUYBVNVUHVUIVUOGUYBJUYCVVBPSVUPVVHXIWOZXJXKUXTVUCHUOUPXLHUTVA
          VHZUXSVUTVURVNVUHUXTHVUKXNZVUMHUXJUYAJUXKPSVUNVVIXOWOXMUXTVUSHUXTHVUL
          XPXQXRUXTUXLVJHUXSUXLUOUPZUXIVUCUXSVVMVUGUXJJUXKPSVVIXSXTYAUXTYEVUKYB
          UUAAUYNUYJYCUXHUXSAUYNUYDUYOUXAUSNUSZMUTVAZDIVBZCPVSZUPUYJAUYMVVQUYDA
          MYDUPUYMVVQVNUHKMVVNKUQZUTVAZDIVBZCPVSVVQYDEVVRMVNZVVTVVPCPVWAVVSVVOD
          IVVRMVVNUTUUBYFUUCUGVVPCPPJYGSUUDUUEUUFYOZUUGVVPUYICUYDPUYTVVOUYHDIUY
          TVVNUYGMUTUYOUYDNUXAYHVPYFYIUUHWCUUIUXTUYIUXPUYEUXTUYIUYHUXPUXHUYIUYH
          VKAUXSUYIUXHUYHUYHDIUUOUUJUUKUXTUYHHUXOWRUMZUWSUTVAZUXPUXTUYHUYGGUXAU
          SZNUSZULUMZUWSUTVAZVWDUXTUYHVWFMUTVAZVWHUXIVWIUXSAVWIDIAVUDVWIDIVBZAG
          VVQUPVUDVWJVHAGUYMVVQAVUBUYMGUKAVUDGGFUMZHUTVAZGVUBUPUIAVWKXLHUTAVVEV
          UDVWKXLVNVVGUIGFPUULYJAHUJUUMUUNUYQVWLCGPUYOGVNZUYPVWKHUTUYOGGFVOVPYI
          UUPUUQVWBUURVVPVWJCGPVWMVVOVWIDIVWMVVNVWFMUTUYOGNUXAYHVPYFYIWBUUSUUTY
          KUXTUYGUOUPZVWFUOUPZMUOUPZVWPUYHVWIVHVWHVKUXTOWDUPZUYFOYGUSZUPZVWNUDU
          XTPVWRUYDUXAUXIPVWRUXAUVFZUXSUXIVWTUXAUVAUXJUVBLYLUSUPBOUVCUSZUVDUSZY
          LUSVBZUXIUXAJOUVEUMZUPZVWTVXCVHZAIVXDUXAUEUVGZVXEUXALVXBUVHUMUPZVXFVX
          DFVXAUXAJLVXBOUAVXAWMZUBVXBWMZVXDWMZVUGUDUVILPYPUSUPZVXBVWRYPUSUPZVXH
          VXFYCVVEVXLVVGFLPUBYMWGVWQVXAVWRWTUSUPVXMUDVXAOVWRVWRWMZVXIUVQVXAVXBV
          WRVXJYMXFBUXALVXBPVWRUVJUVKWBYOUVLZYKZVUQYNZUYFONVWRVXNTXSYJZUXTVWQVW
          EVWRUPZVWOUDUXTPVWRGUXAVXPVUIYNZVWEONVWRVXNTXSYJZAVWPUXHUXSAMUHUVMWCZ
          VYBUYGVWFMMUVNUVOUVPUXTVWCVWGUTVAZVWHVWDUXTUYFVWEOWSUSZUMZNUSZVWCVWGU
          TUXTVYFHUXNOVLUSZUMZNUSZVWCUXTVYEVYHNUXTVVCUXAUSZUYBUXAUSZVYEVYHUXTVV
          CUYBUXAVVJXJUXTVUCVWQUXAJOUVRUMZUPZUYEVUDVYJVYEVNVUHVWQUXTUDWHZUXIVYM
          UXSUXIVXEVYMVXGVUCVWQVXEVYMVUGUDVXDUXAJVYLOVYLWMZVXKUWFUVSYOYKZVUQVUI
          UYDGUXAJVYLVVBVYDOPSVVHVYDWMZVYOUVTYQUXTVUCVWQVYMVUJUXSVYKVYHVNVUHVYN
          VYPVULVUMHUXJUYAVYGUXAJVYLOPSVUNVYGWMZVYOUWAYQUWBXJUXTVWQVVKUXNVWRUPZ
          VYIVWCVNVYNVVLUXIPVWRUXJUXAVXOUWCZHUXNVYGONVWRVXNVYRTXOWOXMUXTVWQVWSV
          XSVYFVWGUTVAVYNVXQVXTUYFVWEOVYDNVWRVXNVYQTUWDWOUWEUXTVWCUOUPVWGUOUPUW
          SUOUPZVYCVWHVHVWDVKUXTHUXOUXTHVUKVGUXTVWQVYSUXOUOUPUDVYTUXNONVWRVXNTX
          SYJZUWGUXTUYGVWFVXRVYAUWHAWUAUXHUXSAUWSUXFVGWCZVWCVWGUWSUWIWOUWJYRUXT
          UXOUWSHWUBWUCVUKUWKUWLYRUWPYRYSUXIVWTUWTUWMUPZUXDUXRYCVXOAWUDUXHAUWTU
          XGUWNYKBUWTUXAJUXKNUXBOPVWRSVXNVVITUXBWMVUGUDUWOYTUWQYSRDUXCUWTUTUOIU
          WRYT $.
      $}

      $d d ph $.
      $( Lemma for ~ ubth .  Prove the reverse implication, using ~ nmblolbi .
         (Contributed by Mario Carneiro, 11-Jan-2014.)
         (New usage is discouraged.) $)
      ubthlem3 $p |- ( ph ->
                ( A. x e. X E. c e. RR A. t e. T ( N ` ( t ` x ) ) <_ c <->
                  E. d e. RR A. t e. T ( ( U normOpOLD W ) ` t ) <_ d ) ) $=
        ( cle vz vu vy vr vn vm vk cv cfv wbr wral cr wrex cnmoo co wceq fveq2d
        fveq1 breq1d cbvralvw ralbidv bitrid cbvrexvw 2fveq3 rexralbidv wa crab
        breq2 cn cmpt wss crp cblo adantr bilani cbvrabv rabbidv eqtrid cbvmptv
        ubthlem1 wcel ad3antrrr ad2antrr simplrl simplrr simprl simprr ubthlem2
        expr rexlimdva rexlimdvva mpd biimtrrid cnmcv cmul simpr cnv ccbn ax-mp
        ex bnnv eqid nvcl remulcl syl2an cba wf sselda adantlr ad2ant2r mp3an12
        mpan blof syl simplr ffvelcdmd cxr cmnf clt nmoxr simpllr nmogtmnf xrre
        syl22anc ad2antlr syl2anc nmblolbi cc0 nvge0 jca lemul1a syl31anc letrd
        ralimdva brralrspcev syl6an ralrimdva impbid ) ABUHZCUHZUIZHUIZKUHZTUJZ
        CEUKKULUMZBJUKZYTFIUNUOZUIZLUHZTUJZCEUKZLULUMZUUFUAUHZUBUHZUIZHUIZUUITU
        JZUBEUKZLULUMZUAJUKZAUULUUSUUEUABJUUSUUMYTUIZHUIZUUCTUJZCEUKZKULUMUUMYS
        UPZUUEUURUVDLKULUURUVBUUITUJZCEUKUUIUUCUPZUVDUUQUVFUBCEUUNYTUPZUUPUVBUU
        ITUVHUUOUVAHUUMUUNYTURUQUSUTUVGUVFUVCCEUUIUUCUVBTVHVAVBVCUVEUVCUUDKCULE
        UVEUVBUUBUUCTUUMYSHYTVDUSVEVBUTZAUUTUULAUUTVFZUCUHZUUMDUOUDUHZTUJUAJVGU
        EUHZUFVIUUIUUNUIZHUIZUFUHZTUJZUBEUKZLJVGZVJZUIVKZUDVLUMZUCJUMUEVIUMUULU
        VJBUCUACUVTDEFUGUEGHIJUDKMNOPQRAEFIVMUOZVKZUUTSVNUUTUUFAUVIVOZUFUGVIUVS
        UVBUGUHZTUJZCEUKZUAJVGZUVPUWFUPZUVSUVBUVPTUJZCEUKZUAJVGUWIUVRUWLLUAJUVR
        UUIYTUIZHUIZUVPTUJZCEUKUUIUUMUPZUWLUVQUWOUBCEUVHUVOUWNUVPTUVHUVNUWMHUUI
        UUNYTURUQUSUTUWPUWOUWKCEUWPUWNUVBUVPTUUIUUMHYTVDUSVAVBVPUWJUWLUWHUAJUWJ
        UWKUWGCEUVPUWFUVBTVHVAVQVRVSZVTUVJUWBUULUEUCVIJUVJUVMVIWAZUVKJWAZVFZVFZ
        UWAUULUDVLUXAUVLVLWAZUWAUULUXAUXBUWAVFZVFBUACUVTDUVKUVLEFUGGUVMHIJKLMNO
        PQRAUWDUUTUWTUXCSWBUVJUUFUWTUXCUWEWCUWQUVJUWRUWSUXCWDUVJUWRUWSUXCWEUXAU
        XBUWAWFUXAUXBUWAWGWHWIWJWKWLWTWMAUUKUUFLULAUUIULWAZVFZUUKUUEBJUXEYSJWAZ
        VFZUUIYSFWNUIZUIZWOUOZULWAZUUKUUBUXJTUJZCEUKUUEUXEUXDUXIULWAZUXKUXFAUXD
        WPFWQWAZUXFUXMFWRWAUXNQFXAWSZYSFUXHJMUXHXBZXCXLZUUIUXIXDXEZUXGUUJUXLCEU
        XGYTEWAZUUJUXLUXGUXSUUJVFZVFZUUBUUHUXIWOUOZUXJUYAUUAIXFUIZWAZUUBULWAZUY
        AJUYCYSYTUYAYTUWCWAZJUYCYTXGZUXEUXSUYFUXFUUJAUXSUYFUXDAEUWCYTSXHXIXJZUX
        NIWQWAZUYFUYGUXORUWCYTFIJUYCMUYCXBZUWCXBZXMXKXNZUXEUXFUXTXOZXPUYIUYDUYE
        RUUAIHUYCUYJNXCXLXNUYAUUHULWAZUXMUYBULWAUYAUUHXQWAZUXDXRUUHXSUJZUUJUYNU
        YAUYGUYOUYLUXNUYIUYGUYOUXORYTFUUGIJUYCMUYJUUGXBZXTXKXNAUXDUXFUXTYAZUYAU
        YGUYPUYLUXNUYIUYGUYPUXORYTFUUGIJUYCMUYJUYQYBXKXNUXGUXSUUJWGZUUHUUIYCYDZ
        UXFUXMUXEUXTUXQYEUUHUXIXDYFUXGUXKUXTUXRVNUYAUYFUXFUUBUYBTUJUYHUYMYSUWCY
        TFUXHHUUGIJMUXPNUYQUYKUXORYGYFUYAUYNUXDUXMYHUXITUJZVFZUUJUYBUXJTUJUYTUY
        RUXFVUBUXEUXTUXFUXMVUAUXQUXNUXFVUAUXOYSFUXHJMUXPYIXLYJYEUYSUUHUUIUXIYKY
        LYMWIYNKCUUBUXJTULEYOYPYQWJYR $.
    $}

    ubth.3 $e |- M = ( U normOpOLD W ) $.
    $( Uniform Boundedness Theorem, also called the Banach-Steinhaus Theorem.
       Let ` T ` be a collection of bounded linear operators on a Banach space.
       If, for every vector ` x ` , the norms of the operators' values are
       bounded, then the operators' norms are also bounded.  Theorem 4.7-3 of
       [Kreyszig] p. 249.  See also
       ~ http://en.wikipedia.org/wiki/Uniform_boundedness_principle .
       (Contributed by NM, 7-Nov-2007.)  (Proof shortened by Mario Carneiro,
       11-Jan-2014.)  (New usage is discouraged.) $)
    ubth $p |- ( ( U e. CBan /\ W e. NrmCVec /\ T C_ ( U BLnOp W ) ) ->
                 ( A. x e. X E. c e. RR A. t e. T ( N ` ( t ` x ) ) <_ c <->
                   E. d e. RR A. t e. T ( M ` t ) <_ d ) ) $=
      ( cblo co cfv cle wbr wral cr ccbn wcel cnv wss cv wrex wb caddc cmul cop
      wi cabs cif cba cnmoo cnmcv wceq oveq1 sseq2d fveq2 eqtrid raleqdv fveq1d
      breq1d rexralbidv bibi12d imbi12d oveq2 ralbidv cims cmopn elimel elimnvu
      eqid cnbn id ubthlem3 dedth2h 3impia ) DUAUBZGUCUBZCDGNOZUDZAUEBUEZPZFPZI
      UEZQRZBCSITUFZAHSZWDEPZJUEZQRZBCSJTUFZUGZVTWAWCWOUKCVTDUHUIUJULUJZUMZGNOZ
      UDZWIAWQUNPZSZWDWQGUOOZPZWLQRZBCSJTUFZUGZUKCWQWAGWPUMZNOZUDZWEXGUPPZPZWGQ
      RZBCSITUFZAWTSZWDWQXGUOOZPZWLQRZBCSJTUFZUGZUKDGWPWPDWQUQZWCWSWOXFXTWBWRCD
      WQGNURUSXTWJXAWNXEXTWIAHWTXTHDUNPWTKDWQUNUTVAVBXTWMXDJBTCXTWKXCWLQXTWDEXB
      XTEDGUOOXBMDWQGUOURVAVCVDVEVFVGGXGUQZWSXIXFXSYAWRXHCGXGWQNVHUSYAXAXNXEXRY
      AWIXMAWTYAWHXLIBTCYAWFXKWGQYAWEFXJYAFGUPPXJLGXGUPUTVAVCVDVEVIYAXDXQJBTCYA
      XCXPWLQYAWDXBXOGXGWQUOVHVCVDVEVFVGXIABWQVJPZCWQYBVKPZXJXGWTIJWTVNXJVNYBVN
      YCVNDWPUAWPWPVNVOVLGVMXIVPVQVRVS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Minimizing Vector Theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d j n x y F $.  $d k n w x y J $.  $d y K $.  $d y L $.  $d f j w x y M $.
    $d f j w x y N $.  $d f j k n w x y ph $.  $d w x R $.  $d f k n w x y S $.
    $d f j k n w x y A $.  $d f j k n w x y D $.  $d w x y U $.  $d w x y W $.
    $d n T $.  $d j k n w x X $.  $d f j k n w x y Y $.
    minveco.x $e |- X = ( BaseSet ` U ) $.
    minveco.m $e |- M = ( -v ` U ) $.
    minveco.n $e |- N = ( normCV ` U ) $.
    minveco.y $e |- Y = ( BaseSet ` W ) $.
    minveco.u $e |- ( ph -> U e. CPreHilOLD ) $.
    minveco.w $e |- ( ph -> W e. ( ( SubSp ` U ) i^i CBan ) ) $.
    minveco.a $e |- ( ph -> A e. X ) $.
    ${
      minveco.d $e |- D = ( IndMet ` U ) $.
      minveco.j $e |- J = ( MetOpen ` D ) $.
      minveco.r $e |- R = ran ( y e. Y |-> ( N ` ( A M y ) ) ) $.
      $( Lemma for ~ minveco .  The set of all distances from points of ` Y `
         to ` A ` are a nonempty set of nonnegative reals.  (Contributed by
         Mario Carneiro, 8-May-2014.)  (New usage is discouraged.) $)
      minvecolem1 $p |- ( ph ->
                         ( R C_ RR /\ R =/= (/) /\ A. w e. R 0 <_ w ) ) $=
        ( cr wss c0 wne cc0 cv cle wbr wral co cfv cmpt crn wcel wa ccphlo phnv
        cnv syl adantr css ccbn cin elin sylib simpld eqid sspba syl2anc sselda
        nvmcl syl3anc nvcl fmpttd frnd eqsstrid cdm cn0v simprd bnnv nvzcl 3syl
        fvex dmmpti eleqtrrdi ne0d wceq dm0rn0 eqeq1i necon3bii nvge0 ralrimiva
        bitr4i cvv wb rgenw breq2 ralrnmptw ax-mp sylibr raleqi 3jca ) AFUDUEFU
        FUGZUHCUIZUJUKZCFULZAFBMDBUIZIUMZJUNZUOZUPZUDUCAMUDXMABMXLUDAXJMUQZURZG
        VAUQZXKLUQZXLUDUQAXQXOAGUSUQXQRGUTVBZVCZXPXQDLUQZXJLUQXRXTAYAXOTVCAMLXJ
        AXQKGVDUNZUQZMLUEXSAYCKVEUQZAKYBVEVFUQYCYDURSKYBVEVGVHZVIGYBKLMNQYBVJVK
        VLVMDXJGILNOVNVOZXKGJLNPVPVLVQVRVSAXMVTZUFUGXFAYGKWAUNZAYHMYGAYDKVAUQYH
        MUQAYCYDYEWBKWCKMYHQYHVJWDWEBMXLXMXKJWFZXMVJZWGWHWIYGUFFUFYGUFWJXNUFWJF
        UFWJXMWKFXNUFUCWLWPWMVHAXHCXNULZXIAUHXLUJUKZBMULZYKAYLBMXPXQXRYLXTYFXKG
        JLNPWNVLWOXLWQUQZBMULYKYMWRYNBMYIWSXHYLBCMXLXMWQYJXGXLUHUJWTXAXBXCXHCFX
        NUCXDXCXE $.

      minveco.s $e |- S = inf ( R , RR , < ) $.
      ${
        minvecolem2.1 $e |- ( ph -> B e. RR ) $.
        minvecolem2.2 $e |- ( ph -> 0 <_ B ) $.
        minvecolem2.3 $e |- ( ph -> K e. Y ) $.
        minvecolem2.4 $e |- ( ph -> L e. Y ) $.
        minvecolem2.5 $e |- ( ph -> ( ( A D K ) ^ 2 ) <_ ( ( S ^ 2 ) + B ) ) $.
        minvecolem2.6 $e |- ( ph -> ( ( A D L ) ^ 2 ) <_ ( ( S ^ 2 ) + B ) ) $.
        $( Lemma for ~ minveco .  Any two points ` K ` and ` L ` in ` Y ` are
           close to each other if they are close to the infimum of distance to
           ` A ` .  (Contributed by Mario Carneiro, 9-May-2014.)  (Revised by
           AV, 4-Oct-2020.)  (New usage is discouraged.) $)
        minvecolem2 $p |- ( ph -> ( ( K D L ) ^ 2 ) <_ ( 4 x. B ) ) $=
          ( vx vw co c2 cexp c4 cmul cle wbr caddc c1 cdiv cpv cfv cns wcel 4re
          cr clt cinf wss c0 wne cv wral wrex cc0 minvecolem1 simp1d simp2d 0re
          simp3d breq1 ralbidv sylancr infrecl syl3anc eqeltrid resqcld remulcl
          wceq rspcev cmet cnv ccphlo phnv syl imsmet css ccbn cin inss1 sselid
          eqid sspba syl2anc sseldd metcl readdcld ax-1cn halfcl syl22anc nvgcl
          cc mp1i eqeltrrd nvmcl wb mpbird fveq2d wa pm3.2i lemul2 mp3an3 mpbid
          a1i recnd 2re 2cn oveq1i eqtrdi eqtr3d oveq12d oveq1d imsdval 3eqtr4d
          syl13anc sspgval sspnv sspsval nvcl infregelb syl31anc breqtrrdi cmpt
          nvscl oveq2 rspceeqv sylancl fvex elrnmpti eleqtrrdi infrelb eqbrtrid
          crn sylibr le2sq2 4pos leadd1dd le2addd 2timesd breqtrrd phpar2 sqmul
          2pos sq2 cabs nvs 0le2 absid mp2an nvmdi 2thalfe1 nvsid eqtrid nvsass
          nv2 nvaddsub4 syl122anc 3eqtr2d metsym nvnnncan1 oveq2d 2t2e4 mulassd
          eqtr3id 3brtr4d letrd 4cn adddid breqtrd leadd2d ) AJKEUPZUQURUPZUSDU
          TUPZVAVBUSGUQURUPZUTUPZUWQVCUPZUWTUWRVCUPZVAVBAUXAUSUWSDVCUPZUTUPZUXB
          VAAUXAUSCVDUQVEUPZJKHVFVGZUPZHVHVGZUPZLUPZMVGZUQURUPZUTUPZUWQVCUPZUXD
          AUWTUWQAUSVKVIZUWSVKVIZUWTVKVIVJAGAGFVKVLVMZVKUGAFVKVNZFVOVPZUNVQZUOV
          QZVAVBZUOFVRZUNVKVSZUXQVKVIAUXRUXSVTUYAVAVBZUOFVRZABUOCEFHILMNOPQRSTU
          AUBUCUDUEUFWAZWBZAUXRUXSUYFUYGWCZAVTVKVIZUYFUYDWDAUXRUXSUYFUYGWEZUYCU
          YFUNVTVKUXTVTWNUYBUYEUOFUXTVTUYAVAWFWGWOWHZUNUOFWIWJWKZWLZUSUWSWMWHZA
          UWPAEOWPVGVIZJOVIZKOVIZUWPVKVIAHWQVIZUYPAHWRVIZUYSUAHWSWTZEHOQUDXAWTZ
          APOJAUYSNHXBVGZVIZPOVNVUAAVUCXCXDVUCNVUCXCXEUBXFZHVUCNOPQTVUCXGZXHXIZ
          UJXJZAPOKVUGUKXJZJKEOXKWJWLZXLAUXMUWQAUXOUXLVKVIZUXMVKVIVJAUXKAUYSUXJ
          OVIZUXKVKVIZVUAAUYSCOVIZUXIOVIZVULVUAUCAPOUXIVUGAUXEUXGNVHVGZUPZUXIPA
          UYSVUDUXEXQVIZUXGPVIZVUQUXIWNVUAVUEVDXQVIVURAXMVDXNXRZAJKNVFVGZUPZUXG
          PAUYSVUDJPVIZKPVIZVVBUXGWNVUAVUEUJUKJKHVVAUXFVUCNPTUXFXGZVVAXGZVUFUUA
          XOANWQVIZVVCVVDVVBPVIAUYSVUDVVGVUAVUEHVUCNVUFUUBXIZUJUKJKNVVAPTVVFXPW
          JXSZUXEUXGVUPUXHHVUCNPTUXHXGZVUPXGZVUFUUCXOAVVGVURVUSVUQPVIVVHVUTVVIU
          XEUXGVUPNPTVVKUUIWJXSZXJZCUXIHLOQRXTWJZUXJHMOQSUUDXIZWLZUSUXLWMWHZVUJ
          XLAUXOUXCVKVIZUXDVKVIVJAUWSDUYNUHXLZUSUXCWMWHAUWTUXMUWQUYOVVQVUJAUWSU
          XLVAVBZUWTUXMVAVBZAGVKVIVTGVAVBVUMGUXKVAVBVVTUYMAVTUXQGVAAVTUXQVAVBZU
          YFUYKAUXRUXSUYDUYJVWBUYFYAUYHUYIUYLUYJAWDYIUNUOUOFVTUUEUUFYBUGUUGVVOA
          GUXQUXKVAUGAUXRUYDUXKFVIUXQUXKVAVBUYHUYLAUXKBPCBVQZLUPZMVGZUUHZUURZFA
          UXKVWEWNBPVSZUXKVWGVIAUXIPVIUXKUXKWNVWHVVLUXKXGBUXIPVWEUXKUXKVWCUXIWN
          VWDUXJMVWCUXICLUUJYCUUKUULBPVWEUXKVWFVWFXGVWDMUUMUUNUUSUFUUOUNUOUXKFU
          UPWJUUQGUXKUUTXOAUXPVUKVVTVWAYAZUYNVVPUXPVUKUXOVTUSVLVBZYDVWIUXOVWJVJ
          UVAYEUWSUXLUSYFYGXIYHUVBAUQCJEUPZUQURUPZCKEUPZUQURUPZVCUPZUTUPZUQUQUX
          CUTUPZUTUPZUXNUXDVAAVWOVWQVAVBZVWPVWRVAVBZAVWOUXCUXCVCUPVWQVAAVWLVWNU
          XCUXCAVWKAUYPVUNUYQVWKVKVIVUBUCVUHCJEOXKWJWLZAVWMAUYPVUNUYRVWMVKVIVUB
          UCVUICKEOXKWJWLZVVSVVSULUMUVCAUXCAUXCVVSYJZUVDUVEAVWOVKVIZVWQVKVIZVWS
          VWTYAZAVWLVWNVXAVXBXLAUQVKVIZVVRVXEYKVVSUQUXCWMWHVXDVXEVXGVTUQVLVBZYD
          VXFVXGVXHYKUVHYEVWOVWQUQYFYGXIYHACJLUPZCKLUPZUXFUPZMVGZUQURUPZVXIVXJL
          UPZMVGZUQURUPZVCUPZUQVXIMVGZUQURUPZVXJMVGZUQURUPZVCUPZUTUPZUXNVWPAUYT
          VXIOVIZVXJOVIZVXQVYCWNUAAUYSVUNUYQVYDVUAUCVUHCJHLOQRXTWJAUYSVUNUYRVYE
          VUAUCVUICKHLOQRXTWJVXIVXJHUXFLMOQVVERSUVFWJAUXMVXMUWQVXPVCAUQUXKUTUPZ
          UQURUPZUXMVXMAVYGUQUQURUPZUXLUTUPZUXMAUQXQVIZUXKXQVIVYGVYIWNYLAUXKVVO
          YJUQUXKUVGWHVYHUSUXLUTUVIYMYNAVYFVXLUQURAUQUXJUXHUPZMVGZVYFVXLAVYLUQU
          VJVGZUXKUTUPZVYFAUYSVYJVULVYLVYNWNVUAVYJAYLYIZVVNUQUXJUXHHMOQVVJSUVKW
          JVYMUQUXKUTVXGVTUQVAVBVYMUQWNYKUVLUQUVMUVNYMYNAVYKVXKMAVYKUQCUXHUPZUQ
          UXIUXHUPZLUPZCCUXFUPZUXGLUPZVXKAUYSVYJVUNVUOVYKVYRWNVUAVYOUCVVMUQCUXI
          UXHHLOQRVVJUVOYTAVYSVYPUXGVYQLAUYSVUNVYSVYPWNVUAUCCUXHHUXFOQVVEVVJUVT
          XIAUQUXEUTUPZUXGUXHUPZUXGVYQAWUBVDUXGUXHUPZUXGWUAVDUXGUXHUVPYMAUYSUXG
          OVIZWUCUXGWNVUAAUYSUYQUYRWUDVUAVUHVUIJKHUXFOQVVEXPWJZUXGUXHHOQVVJUVQX
          IUVRAUYSVYJVURWUDWUBVYQWNVUAVYOVUTWUEUQUXEUXGUXHHOQVVJUVSYTYOYPAUYSVU
          NVUNUYQUYRVYTVXKWNVUAUCUCVUHVUICCJKHUXFLOQVVERUWAUWBUWCYCYOYQYOAUWPVX
          OUQURAKJEUPZKJLUPZMVGZUWPVXOAUYSUYRUYQWUFWUHWNVUAVUIVUHKJEHLMOQRSUDYR
          WJAUYPUYQUYRUWPWUFWNVUBVUHVUIJKEOUWDWJAVXNWUGMAUYSVUNUYQUYRVXNWUGWNVU
          AUCVUHVUICJKHLOQRUWEYTYCYSYQYPAVWOVYBUQUTAVWLVXSVWNVYAVCAVWKVXRUQURAU
          YSVUNUYQVWKVXRWNVUAUCVUHCJEHLMOQRSUDYRWJYQAVWMVXTUQURAUYSVUNUYRVWMVXT
          WNVUAUCVUICKEHLMOQRSUDYRWJYQYPUWFYSAUXDUQUQUTUPZUXCUTUPVWRWUIUSUXCUTU
          WGYMAUQUQUXCVYOVYOVXCUWHUWIUWJUWKAUSUWSDUSXQVIAUWLYIAUWSUYNYJADUHYJUW
          MUWNAUWQUWRUWTVUJAUXODVKVIUWRVKVIVJUHUSDWMWHUYOUWOYB $.
      $}

      ${
        minveco.f $e |- ( ph -> F : NN --> Y ) $.
        minveco.1 $e |- ( ( ph /\ n e. NN ) ->
            ( ( A D ( F ` n ) ) ^ 2 ) <_ ( ( S ^ 2 ) + ( 1 / n ) ) ) $.
        $( Lemma for ~ minveco .  The sequence formed by taking elements
           successively closer to the infimum is Cauchy.  (Contributed by Mario
           Carneiro, 8-May-2014.)  (Revised by AV, 4-Oct-2020.)
           (New usage is discouraged.) $)
        minvecolem3 $p |- ( ph -> F e. ( Cau ` D ) ) $=
          ( vj vx vw ccau cfv wcel cv co clt wbr cuz wral cn wrex wa c4 c2 cexp
          crp cdiv cfl c1 caddc cr cc0 cle cn0 4re 4pos elrpii cz simpr rpexpcl
          sylancl rpdivcl sylancr rprege0 flge0nn0 nn0p1nn 4syl cmul ccphlo cnv
          cmet phnv imsmet 3syl ad2antrr wss css syl ccbn cin inss1 sselid eqid
          2z sspba syl2anc adantr ffvelcdmd sseldd eluznn sylan syl3anc resqcld
          wf metcl nnrpd rpreccld rpmulcl rpred rpge0d ffvelcdmda syldan oveq2d
          wceq fveq2 oveq1d oveq2 breq12d ralrimiva rspcdva wne rspcev readdcld
          w3a wb cc rpcnne0 mpbird eqidd cinf c0 minvecolem1 breq1 ralbidv mpan
          3anim3i infrecl eqeltrid nnrecred adantlr eluzle adantl rpregt0d nnre
          0re nngt0 lerec mpbid leadd2dd letrd minvecolem2 ax-mp recdiv eqbrtrd
          flltp1 ltrec1d pm3.2i ltmuldiv2 mp3an3 metge0 ad2antlr lt2sq syl21anc
          jca lelttrd breq1d raleqbidv nnuz cxmet imsxmet 1zzd fssd iscauf ) AI
          DULUMUNUIUOZIUMZHUOZIUMZDUPZUJUOZUQURZHUWEUSUMZUTZUIVAVBZUJVGUTAUWNUJ
          VGAUWJVGUNZVCZVDUWJVEVFUPZVHUPZVIUMZVJVKUPZVAUNZUWTIUMZUWHDUPZUWJUQUR
          ZHUWTUSUMZUTZUWNUWPUWRVGUNZUWRVLUNZVMUWRVNURVCUWSVOUNUXAUWPVDVGUNZUWQ
          VGUNZUXGVDVPVQVRZUWPUWOVEVSUNUXJAUWOVTXEUWJVEWAWBZVDUWQWCWDZUWRWEUWRW
          FUWSWGWHZUWPUXDHUXEUWPUWGUXEUNZVCZUXDUXCVEVFUPZUWQUQURZUXPUXQVDVJUWTV
          HUPZWIUPZUWQUXPUXCUXPDNWLUMUNZUXBNUNZUWHNUNZUXCVLUNZAUYAUWOUXOAGWJUNZ
          GWKUNZUYATGWMZDGNPUCWNWOWPZUXPONUXBAONWQZUWOUXOAUYFMGWRUMZUNUYIAUYEUY
          FTUYGWSAUYJWTXAZUYJMUYJWTXBUAXCGUYJMNOPSUYJXDXFXGZWPZUXPVAOUWTIAVAOIX
          OZUWOUXOUGWPZUWPUXAUXOUXNXHZXIZXJZUXPONUWHUYMUXPVAOUWGIUYOUWPUXAUXOUW
          GVAUNZUXNUWGUWTXKXLZXIXJZUXBUWHDNXPXMZXNUXPUXTUXPUXIUXSVGUNZUXTVGUNUX
          KUXPUWTUXPUWTUYPXQZXRVDUXSXSWDXTUXPUWQUWPUXJUXOUXLXHZXTZUXPBCUXSDEFGJ
          UXBUWHKLMNOPQRSAUYEUWOUXOTWPAMUYKUNUWOUXOUAWPACNUNZUWOUXOUBWPZUCUDUEU
          FUXPUXSUWPVUCUXOUWPUWTUWPUWTUXNXQXRXHZXTZUXPUXSVUIYAUYQUWPUXOUYSUWHOU
          NUYTUWPVAOUWGIAUYNUWOUGXHYBYCZUXPCUWHDUPZVEVFUPZFVEVFUPZVJUWGVHUPZVKU
          PZVNURZCUXBDUPZVEVFUPZVUNUXSVKUPZVNURHVAUWTUWGUWTYEZVUMVUSVUPVUTVNVVA
          VULVURVEVFVVAUWHUXBCDUWGUWTIYFYDYGVVAVUOUXSVUNVKUWGUWTVJVHYHYDYIAVUQH
          VAUTUWOUXOAVUQHVAUHYJWPUYPYKUXPVUMVUPVUTUXPVULUXPUYAVUGUYCVULVLUNUYHV
          UHUXPONUWHUYMVUKXJCUWHDNXPXMXNUXPVUNVUOAVUNVLUNUWOUXOAFAFEVLUQUUAZVLU
          FAEVLWQZEUUBYLZVMUKUOZVNURZUKEUTZYOVVCVVDUWJVVEVNURZUKEUTZUJVLVBZYOVV
          BVLUNABUKCDEGJKLMNOPQRSTUAUBUCUDUEUUCVVGVVJVVCVVDVMVLUNVVGVVJUUPVVIVV
          GUJVMVLUWJVMYEVVHVVFUKEUWJVMVVEVNUUDUUEYMUUFUUGUJUKEUUHWOUUIXNWPZUXPU
          WGUYTUUJZYNUXPVUNUXSVVKVUJYNUWPUXOUYSVUQUYTAUYSVUQUWOUHUUKYCUXPVUOUXS
          VUNVVLVUJVVKUXPUWTUWGVNURZVUOUXSVNURZUXOVVMUWPUWTUWGUULUUMUXPUWTVLUNV
          MUWTUQURVCUWGVLUNZVMUWGUQURZVCZVVMVVNYPUXPUWTVUDUUNUXPUYSVVQUYTUYSVVO
          VVPUWGUUOUWGUUQUVOWSUWTUWGUURXGUUSUUTUVAUVBUXPUXTUWQUQURZUXSUWQVDVHUP
          ZUQURZUXPVVSUWTUXPUXJUXIVVSVGUNVUEUXKUWQVDWCWBVUDUXPVJVVSVHUPZUWRUWTU
          QUXPUWQYQUNUWQVMYLVCZVDYQUNVDVMYLVCZVWAUWRYEUXPUXJVWBVUEUWQYRWSUXIVWC
          UXKVDYRUVCUWQVDUVDWBUXPUXHUWRUWTUQURUXPUWRUWPUXGUXOUXMXHXTUWRUVFWSUVE
          UVGUXPUXSVLUNZUWQVLUNZVVRVVTYPZVUJVUFVWDVWEVDVLUNZVMVDUQURZVCVWFVWGVW
          HVPVQUVHUXSUWQVDUVIUVJXGYSUVPUXPUYDVMUXCVNURZUWJVLUNVMUWJVNURVCZUXDUX
          RYPVUBUXPUYAUYBUYCVWIUYHUYRVUAUXBUWHDNUVKXMUWOVWJAUXOUWJWEUVLUXCUWJUV
          MUVNYSYJUWMUXFUIUWTVAUWEUWTYEZUWKUXDHUWLUXEUWEUWTUSYFVWKUWIUXCUWJUQVW
          KUWFUXBUWHDUWEUWTIYFYGUVQUVRYMXGYJAUJUWHUWFDUIHIVJNVAUVSAUYEUYFDNUVTU
          MUNTUYGDGNPUCUWAWOAUWBAUYSVCUWHYTAUWEVAUNVCUWFYTAVAONIUGUYLUWCUWDYS
          $.

        $( Lemma for ~ minveco . ` F ` is convergent in the subspace topology
           on ` Y ` .  (Contributed by Mario Carneiro, 7-May-2014.)
           (New usage is discouraged.) $)
        minvecolem4a $p |- ( ph -> F
                      ( ~~>t ` ( MetOpen ` ( D |` ( Y X. Y ) ) ) )
                      ( ( ~~>t ` ( MetOpen ` ( D |` ( Y X. Y ) ) ) ) ` F ) ) $=
          ( cxp cres cmopn cfv clm cdm wcel wbr cba ccmet ccau cims wceq ccphlo
          cnv css phnv syl ccbn wa elin sylib simpld eqid sspims syl2anc simprd
          cin cbncms eqeltrrd minvecolem3 cxmet cn wf wb cmet imsmet 3syl causs
          metxmet mpbid cmetcau cha wfun xmetres methaus lmfun funfvbrb ) AIDOO
          UIUJZUKULZUMULZUNUOZIIWSULWSUPZAWQMUQULZURULZUOIWQUSULUOZWTAMUTULZWQX
          CAGVCUOZMGVDULZUOZXEWQVAAGVBUOZXFTGVEZVFAXHMVGUOZAMXGVGVPUOXHXKVHUAMX
          GVGVIVJZVKXEDGXGMOSUCXEVLZXGVLVMVNAXKXEXCUOAXHXKXLVOXEMXBXBVLXMVQVFVR
          AIDUSULUOZXDABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHVSADNVTULUOZWAOIWBXNX
          DWCADNWDULUOZXOAXIXFXPTXJDGNPUCWEWFDNWHVFZUGDINOWGVNWIWQIWRXBWRVLZWJV
          NAWRWKUOZWSWLWTXAWCAXOWQNOVPZVTULUOXSXQDONWMWQWRXTXRWNWFWRWOIWSWPWFWI
          $.

        $( Lemma for ~ minveco .  The convergent point of the Cauchy sequence
           ` F ` is a member of the base space.  (Contributed by Mario
           Carneiro, 16-Jun-2014.)  (New usage is discouraged.) $)
        minvecolem4b $p |- ( ph -> ( ( ~~>t ` J ) ` F ) e. X ) $=
          ( clm cfv cnv wcel css wss ccphlo phnv syl ccbn cin elin sylib simpld
          eqid sspba syl2anc cxp cres cmopn wfun wbr wceq cxmet imsxmet methaus
          wa cha lmfun minvecolem4a crest co c1 cvv nnuz cba fvexi ctop mopntop
          cn a1i ctopon xmetres2 mopntopon lmcl 1zzd metrest fveq2d breqd bitrd
          lmss mpbird funbrfv sylc eqeltrd sseldd ) AONIJUIUJZUJZAGUKULZMGUMUJZ
          ULZONUNZAGUOULXGTGUPUQZAXIMURULZAMXHURUSULXIXLVOUAMXHURUTVAVBGXHMNOPS
          XHVCVDVEZAXFIDOOVFVGZVHUJZUIUJZUJZOAXEVIZIXQXEVJZXFXQVKAJVPULZXRADNVL
          UJULZXTAXGYAXKDGNPUCVMUQZDJNUDVNUQJVQUQAXSIXQXPVJZABCDEFGHIJKLMNOPQRS
          TUAUBUCUDUEUFUGUHVRZAXSIXQJOVSVTZUIUJZVJYCAXQIJYEWAWBOWHYEVCWCOWBULAO
          MWDSWEWIAYAJWFULYBDJNUDWGUQAXOOWJUJULZYCXQOULAXNOVLUJULZYGAYAXJYHYBXM
          DONWKVEXNXOOXOVCZWLUQYDXQIXOOWMVEZAWNUGWSAYFXPIXQAYEXOUIAYAXJYEXOVKYB
          XMDXNJXONOXNVCUDYIWOVEWPWQWRWTIXQXEXAXBYJXCXD $.

        $( Lemma for ~ minveco .  The infimum of the distances to ` A ` is a
           real number.  (Contributed by Mario Carneiro, 16-Jun-2014.)
           (Revised by AV, 4-Oct-2020.)  (New usage is discouraged.) $)
        minvecolem4c $p |- ( ph -> S e. RR ) $=
          ( vx vw cr clt cinf wss c0 wne cle wbr wral wrex wcel cc0 minvecolem1
          cv simp1d simp2d 0re simp3d wceq breq1 ralbidv rspcev sylancr infrecl
          syl3anc eqeltrid ) AFEUKULUMZUKUFAEUKUNZEUOUPZUIVDZUJVDZUQURZUJEUSZUI
          UKUTZVQUKVAAVRVSVBWAUQURZUJEUSZABUJCDEGJKLMNOPQRSTUAUBUCUDUEVCZVEAVRV
          SWFWGVFAVBUKVAWFWDVGAVRVSWFWGVHWCWFUIVBUKVTVBVIWBWEUJEVTVBWAUQVJVKVLV
          MUIUJEVNVOVP $.

        minveco.t $e |- T = ( 1 /
      ( ( ( ( ( A D ( ( ~~>t ` J ) ` F ) ) + S ) / 2 ) ^ 2 ) - ( S ^ 2 ) ) ) $.
        $( Lemma for ~ minveco .  The convergent point of the Cauchy sequence
           ` F ` attains the minimum distance, and so is closer to ` A ` than
           any other point in ` Y ` .  (Contributed by Mario Carneiro,
           7-May-2014.)  (Revised by AV, 4-Oct-2020.)
           (New usage is discouraged.) $)
        minvecolem4 $p |- ( ph -> E. x e. Y A. y e. Y
                          ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) ) $=
          ( vw clm cfv wcel co cle wbr wral wrex cxp cres cmopn wfun wceq cxmet
          cha ccphlo cnv phnv imsxmet 3syl methaus lmfun minvecolem4a crest cvv
          cv c1 cn eqid nnuz cba fvexi a1i ctop syl mopntop ctopon wss css ccbn
          cin elin sylib simpld sspba syl2anc xmetres2 mopntopon lmcl 1zzd lmss
          metrest fveq2d breqd mpbird funbrfv sylc eqeltrd minvecolem4b imsdval
          wa bitrd syl3anc adantr cr cmet metcl clt caddc c2 cdiv cexp readdcld
          cc0 crp resqcld recnd 2timesd breq1d wb 3bitr2d ralbidv rspcev metge0
          cmul 0re ad2antrr letrd imsmet minvecolem4c sselda nvcl wn ltnled cfl
          nvmcl cuz cn0 cmin rehalfcld resubcld ltadd1d 2re 2pos ltmuldiv2 cinf
          pm3.2i c0 wne minvecolem1 simp3d simp1d simp2d breq1 sylancr syl31anc
          infregelb breqtrrdi addge0d divge0 lt2sqd posdifd 3bitrd biimpa elrpd
          syl21anc rpreccld eqeltrid rprege0d flge0nn0 nnzd rexrd simpll eluznn
          nn0p1nn breqtrrd sylan fssd ffvelcdmda nnrecred rpred reflcl peano2re
          nnred fllep1 eluzle adantl eqbrtrrid 1red nngt0d syl122anc leaddsub2d
          lediv23 mpbid le2sqd lmle leadd2d lemuldiv2 mp3an3 biimpar ex sylbird
          syldan pm2.18d cmpt crn simpr fvex elrnmpt1 sylancl eleqtrrdi infrelb
          eqbrtrid eqbrtrrd ralrimiva oveq2 ) AKLUMUNZUNZQUODUYJMUPZNUNZDCVRZMU
          PZNUNZUQURZCQUSZDBVRZMUPZNUNZUYOUQURZCQUSZBQUTAUYJKEQQVAVBZVCUNZUMUNZ
          UNZQAUYIVDZKVUFUYIURZUYJVUFVEAEPVFUNUOZLVGUOVUGAIVHUOZIVIUOZVUIUBIVJZ
          EIPRUEVKZVLZELPUFVMLVNVLAVUHKVUFVUEURZACDEFGIJKLMNOPQRSTUAUBUCUDUEUFU
          GUHUIUJVOZAVUHKVUFLQVPUPZUMUNZURVUOAVUFKLVUQVSVQQVTVUQWAWBQVQUOAQOWCU
          AWDWEAVUKVUILWFUOAVUJVUKUBVULWGZVUMELPUFWHVLAVUDQWIUNUOZVUOVUFQUOAVUC
          QVFUNUOZVUTAVUIQPWJZVVAVUNAVUKOIWKUNZUOZVVBVUSAVVDOWLUOZAOVVCWLWMUOVV
          DVVEXMUCOVVCWLWNWOWPIVVCOPQRUAVVCWAWQWRZEQPWSWRVUCVUDQVUDWAZWTWGVUPVU
          FKVUDQXAWRZAXBUIXCAVURVUEKVUFAVUQVUDUMAVUIVVBVUQVUDVEVUNVVFEVUCLVUDPQ
          VUCWAUFVVGXDWRXEXFXNXGZKVUFUYIXHXIZVVHXJAUYPCQAUYMQUOZXMZDUYJEUPZUYLU
          YOUQAVVMUYLVEZVVKAVUKDPUOZUYJPUOZVVNVUSUDACDEFGIJKLMNOPQRSTUAUBUCUDUE
          UFUGUHUIUJXKZDUYJEIMNPRSTUEXLXOXPVVLVVMGUYOAVVMXQUOZVVKAEPXRUNUOZVVOV
          VPVVRAVUJVUKVVSUBVULEIPRUEUUAVLZUDVVQDUYJEPXSXOZXPAGXQUOZVVKACDEFGIJK
          LMNOPQRSTUAUBUCUDUEUFUGUHUIUJUUBZXPVVLVUKUYNPUOZUYOXQUOAVUKVVKVUSXPZV
          VLVUKVVOUYMPUOVWDVWEAVVOVVKUDXPAQPUYMVVFUUCDUYMIMPRSUUHXOUYNINPRTUUDW
          RAVVMGUQURZVVKAVWFAVWFUUEGVVMXTURZVWFAGVVMVWCVWAUUFAVWGVWFAVWGVVMVVMG
          YAUPZYBYCUPZUQURZVWFAVWGXMZEUYJDVWIJKLHUUGUNZVSYAUPZPVWMUUIUNZVWNWAUF
          AVUIVWGVUNXPVWKVWMVWKHXQUOZYFHUQURXMVWLUUJUOVWMVTUOZVWKHVWKHVSVWIYBYD
          UPZGYBYDUPZUUKUPZYCUPZYGUKVWKVWSVWKVWSAVWSXQUOZVWGAVWQVWRAVWIAVWHAVVM
          GVWAVWCYEZUULZYHZAGVWCYHZUUMZXPAVWGYFVWSXTURZAVWGGVWIXTURZVWRVWQXTURV
          XGAVWGGGYAUPZVWHXTURYBGYQUPZVWHXTURZVXHAGVVMGVWCVWAVWCUUNAVXJVXIVWHXT
          AGAGVWCYIYJYKAVWBVWHXQUOZYBXQUOZYFYBXTURZXMZVXKVXHYLVWCVXBVXOAVXMVXNU
          UOUUPUUSZWEZGVWHYBUUQXOYMAGVWIVWCVXCAYFFXQXTUURZGUQAYFVXRUQURZYFULVRZ
          UQURZULFUSZAFXQWJZFUUTUVAZVYBACULDEFILMNOPQRSTUAUBUCUDUEUFUGUVBZUVCZA
          VYCVYDUYRVXTUQURZULFUSZBXQUTZYFXQUOZVXSVYBYLAVYCVYDVYBVYEUVDZAVYCVYDV
          YBVYEUVEAVYJVYBVYIYRVYFVYHVYBBYFXQUYRYFVEVYGVYAULFUYRYFVXTUQUVFYNYOUV
          GZVYJAYRWEBULULFYFUVIUVHXGUHUVJZAVXLYFVWHUQURVXOYFVWIUQURZVXBAVVMGVWA
          VWCAVVSVVOVVPYFVVMUQURVVTUDVVQDUYJEPYPXOVYMUVKVXQVWHYBUVLUVRZUVMAVWRV
          WQVXEVXDUVNUVOUVPZUVQUVSUVTZUWAHUWBVWLUWGVLZUWCAKUYJUYIURVWGAKVUFUYJU
          YIVVIVVJUWHXPAVVOVWGUDXPVWKVWIAVWIXQUOZVWGVXCXPUWDVWKJVRZVWNUOZXMZDVY
          TKUNZEUPZVWIUQURWUDYBYDUPZVWQUQURWUBWUEVWRVSVYTYCUPZYAUPZVWQWUBWUDWUB
          AVYTVTUOZWUDXQUOZAVWGWUAUWEZVWKVWPWUAWUHVYRVYTVWMUWFUWIZAWUHXMZVVSVVO
          WUCPUOZWUIAVVSWUHVVTXPZAVVOWUHUDXPZAVTPVYTKAVTQPKUIVVFUWJUWKZDWUCEPXS
          XOWRZYHWUBVWRWUFWUBGAVWBVWGWUAVWCYSYHZWUBVYTWUKUWLZYEAVWQXQUOVWGWUAVX
          DYSZWUBAWUHWUEWUGUQURWUJWUKUJWRWUBWUGVWQUQURWUFVWSUQURZWUBVWTVYTUQURZ
          WVAWUBVWTHVYTUQUKWUBHVWMVYTWUBHVWKHYGUOWUAVYQXPUWMZWUBVWOVWLXQUOVWMXQ
          UOWVCHUWNVWLUWOVLWUBVYTWUKUWPZWUBVWOHVWMUQURWVCHUWQWGWUAVWMVYTUQURVWK
          VWMVYTUWRUWSYTUWTWUBVSXQUOVXAVXGVYTXQUOYFVYTXTURWVBWVAYLWUBUXAAVXAVWG
          WUAVXFYSVWKVXGWUAVYPXPWVDWUBVYTWUKUXBVSVWSVYTUXEUXCUXFWUBVWRWUFVWQWUR
          WUSWUTUXDXGYTWUBWUDVWIWUQAVYSVWGWUAVXCYSWUBAWUHYFWUDUQURZWUJWUKWULVVS
          VVOWUMWVEWUNWUOWUPDWUCEPYPXOWRAVYNVWGWUAVYOYSUXGXGUXHAVWFVWJAVWFVVMVV
          MYAUPZVWHUQURYBVVMYQUPZVWHUQURZVWJAVVMGVVMVWAVWCVWAUXIAWVGWVFVWHUQAVV
          MAVVMVWAYIYJYKAVVRVXLWVHVWJYLZVWAVXBVVRVXLVXOWVIVXPVVMVWHYBUXJUXKWRYM
          UXLUXOUXMUXNUXPXPVVLGVXRUYOUQUHVVLVYCVYIUYOFUOVXRUYOUQURAVYCVVKVYKXPA
          VYIVVKVYLXPVVLUYOCQUYOUXQZUXRZFVVLVVKUYOVQUOUYOWVKUOAVVKUXSUYNNUXTCQU
          YOWVJVQWVJWAUYAUYBUGUYCBULUYOFUYDXOUYEYTUYFUYGVUBUYQBUYJQUYRUYJVEZVUA
          UYPCQWVLUYTUYLUYOUQWVLUYSUYKNUYRUYJDMUYHXEYKYNYOWR $.
      $}

      $( Lemma for ~ minveco .  Discharge the assumption about the sequence
         ` F ` by applying countable choice ~ ax-cc .  (Contributed by Mario
         Carneiro, 9-May-2014.)  (Revised by AV, 4-Oct-2020.)
         (New usage is discouraged.) $)
      minvecolem5 $p |- ( ph -> E. x e. Y A. y e. Y
                        ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) ) $=
        ( vf vn vw vk cn cv wf cfv co c2 cexp c1 cdiv caddc cle wbr wral wa wex
        wrex wcel csqrt wn clt cc0 nnrecgt0 adantl nnrecre cinf wss minvecolem1
        cr c0 wne w3a adantr simp1d simp2d 0re simp3d wceq breq1 ralbidv rspcev
        sylancr infrecl syl3anc eqeltrid resqcld ltaddposd mpbid readdcld elrpd
        sqge0d addgegt0d resqrtth syl2anc breqtrrd rpsqrtcld rpred wb infregelb
        rpge0d 0red syl31anc mpbird breqtrrdi sqrtge0d lt2sqd ltnled breq2i crn
        bitrid cmpt raleqi fvex rgenw breq2 ralrnmptw ax-mp bitri bitrdi rexnal
        cvv eqid mtbid sylibr cnv syl ad2antrr ccbn breq1d oveq1d oveq2 oveq2d
        ccphlo phnv css cin inss1 sselid sspba sselda nvmcl letrid nvge0 le2sqd
        nvcl ord bitrd notbid imsdval 3imtr4d reximdva mpd ralrimiva cba nnenom
        fvexi axcc4 clm cmin simprl simprr fveq2 breq12d rspccva sylan exlimddv
        minvecolem4 ) AUJNUFUKZULZDUGUKZUVPUMZEUNZUOUPUNZGUOUPUNZUQUVRURUNZUSUN
        ZUTVAZUGUJVBZVCZDBUKZJUNKUMDCUKZJUNZKUMZUTVACNVBBNVEUFADUWIEUNZUOUPUNZU
        WDUTVAZCNVEZUGUJVBUWGUFVDAUWOUGUJAUVRUJVFZVCZUWDVGUMZUWKUTVAZVHZCNVEZUW
        OUWQUWSCNVBZVHUXAUWQUWRGUTVAZUXBUWQGUWRVIVAZUXCVHUWQUXDUWBUWRUOUPUNZVIV
        AUWQUWBUWDUXEVIUWQVJUWCVIVAZUWBUWDVIVAUWPUXFAUVRVKVLZUWQUWCUWBUWPUWCVQV
        FAUVRVMVLZUWQGUWQGFVQVIVNZVQUEUWQFVQVOZFVRVSZUWHUHUKZUTVAZUHFVBZBVQVEZU
        XIVQVFUWQUXJUXKVJUXLUTVAZUHFVBZAUXJUXKUXQVTUWPACUHDEFHIJKLMNOPQRSTUAUBU
        CUDVPWAZWBZUWQUXJUXKUXQUXRWCZUWQVJVQVFZUXQUXOWDUWQUXJUXKUXQUXRWEZUXNUXQ
        BVJVQUWHVJWFUXMUXPUHFUWHVJUXLUTWGWHWIWJZBUHFWKWLWMZWNZWOWPUWQUWDVQVFZVJ
        UWDUTVAUXEUWDWFZUWQUWBUWCUYEUXHWQZUWQUWDUWQUWDUYHUWQUWBUWCUYEUXHUWQGUYD
        WSUXGWTWRZXHZUWDXAXBZXCUWQGUWRUYDUWQUWRUWQUWDUYIXDXEZUWQVJUXIGUTUWQVJUX
        IUTVAZUXQUYBUWQUXJUXKUXOUYAUYMUXQXFUXSUXTUYCUWQXIBUHUHFVJXGXJXKUEXLUWQU
        WDUYHUYJXMZXNXKUWQGUWRUYDUYLXOWPUWQUXCUWRUXLUTVAZUHFVBZUXBUXCUWRUXIUTVA
        ZUWQUYPGUXIUWRUTUEXPUWQUXJUXKUXOUWRVQVFZUYQUYPXFUXSUXTUYCUYLBUHUHFUWRXG
        XJXRUYPUYOUHCNUWKXSZXQZVBZUXBUYOUHFUYTUDXTUWKYIVFZCNVBVUAUXBXFVUBCNUWJK
        YAYBUYOUWSCUHNUWKUYSYIUYSYJUXLUWKUWRUTYCYDYEYFYGYKUWSCNYHYLUWQUWTUWNCNU
        WQUWINVFZVCZUWDUWKUOUPUNZUTVAZVHVUEUWDUTVAZUWTUWNVUDVUFVUGVUDUWDVUEUWQU
        YFVUCUYHWAVUDUWKVUDHYMVFZUWJMVFZUWKVQVFAVUHUWPVUCAHUUAVFZVUHSHUUBYNZYOZ
        VUDVUHDMVFZUWIMVFZVUIVULAVUMUWPVUCUAYOZUWQNMUWIANMVOZUWPAVUHLHUUCUMZVFV
        UPVUKAVUQYPUUDZVUQLVUQYPUUETUUFHVUQLMNORVUQYJUUGXBWAUUHZDUWIHJMOPUUIWLZ
        UWJHKMOQUUMXBZWNUUJUUNVUDUWSVUFVUDUWSUXEVUEUTVAVUFVUDUWRUWKUWQUYRVUCUYL
        WAVVAUWQVJUWRUTVAVUCUYNWAVUDVUHVUIVJUWKUTVAVULVUTUWJHKMOQUUKXBUULVUDUXE
        UWDVUEUTUWQUYGVUCUYKWAYQUUOUUPVUDUWMVUEUWDUTVUDUWLUWKUOUPVUDVUHVUMVUNUW
        LUWKWFVULVUOVUSDUWIEHJKMOPQUBUUQWLYRYQUURUUSUUTUVAUWNUWECNUFUGUJNLUVBRU
        VDUVCUWIUVSWFZUWMUWAUWDUTVVBUWLUVTUOUPUWIUVSDEYSYRYQUVEYNAUWGVCZBCDEFGU
        QDUVPIUVFUMUMEUNGUSUNUOURUNUOUPUNUWBUVGUNURUNZHUIUVPIJKLMNOPQRAVUJUWGSW
        AALVURVFUWGTWAAVUMUWGUAWAUBUCUDUEAUVQUWFUVHVVCUWFUIUKZUJVFDVVEUVPUMZEUN
        ZUOUPUNZUWBUQVVEURUNZUSUNZUTVAZAUVQUWFUVIUWEVVKUGVVEUJUVRVVEWFZUWAVVHUW
        DVVJUTVVLUVTVVGUOUPVVLUVSVVFDEUVRVVEUVPUVJYTYRVVLUWCVVIUWBUSUVRVVEUQURY
        SYTUVKUVLUVMVVDYJUVOUVN $.

      $( Lemma for ~ minveco .  Any minimal point is less than ` S ` away from
         ` A ` .  (Contributed by Mario Carneiro, 9-May-2014.)  (Revised by AV,
         4-Oct-2020.)  (New usage is discouraged.) $)
      minvecolem6 $p |- ( ( ph /\ x e. Y ) ->
        ( ( ( A D x ) ^ 2 ) <_ ( ( S ^ 2 ) + 0 ) <->
          A. y e. Y ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) ) ) $=
        ( vw cv wcel wa co cexp cc0 caddc cle wbr cfv wral cnv wceq ccphlo phnv
        c2 syl adantr css wss ccbn cin inss1 sselid eqid syl2anc sselda imsdval
        sspba syl3anc oveq1d cr clt cinf wne wrex w3a minvecolem1 simp1d simp2d
        0red simp3d breq1 ralbidv rspcev infrecl eqeltrid resqcld recnd addridd
        c0 breq12d nvmcl nvcl nvge0 wb infregelb mpbird breqtrrdi le2sqd breq2i
        syl31anc bitrid 3bitr2d cmpt crn raleqi cvv rgenw breq2 ralrnmptw ax-mp
        fvex bitri bitrdi ) ABUGZNUHZUIZDYBEUJZVBUKUJZGVBUKUJZULUMUJZUNUOZDYBJU
        JZKUPZUFUGZUNUOZUFFUQZYKDCUGJUJZKUPZUNUOZCNUQZYDYIYKVBUKUJZYGUNUOYKGUNU
        OZYNYDYFYSYHYGUNYDYEYKVBUKYDHURUHZDMUHZYBMUHZYEYKUSAUUAYCAHUTUHUUASHVAV
        CZVDZAUUBYCUAVDZANMYBAUUALHVEUPZUHNMVFUUDAUUGVGVHUUGLUUGVGVITVJHUUGLMNO
        RUUGVKVOVLVMZDYBEHJKMOPQUBVNVPVQYDYGYDYGYDGYDGFVRVSVTZVRUEYDFVRVFZFWQWA
        ZYBYLUNUOZUFFUQZBVRWBZUUIVRUHYDUUJUUKULYLUNUOZUFFUQZAUUJUUKUUPWCYCACUFD
        EFHIJKLMNOPQRSTUAUBUCUDWDVDZWEZYDUUJUUKUUPUUQWFZYDULVRUHZUUPUUNYDWGZYDU
        UJUUKUUPUUQWHZUUMUUPBULVRYBULUSUULUUOUFFYBULYLUNWIWJWKVLZBUFFWLVPWMZWNW
        OWPWRYDYKGYDUUAYJMUHZYKVRUHZUUEYDUUAUUBUUCUVEUUEUUFUUHDYBHJMOPWSVPZYJHK
        MOQWTVLZUVDYDUUAUVEULYKUNUOUUEUVGYJHKMOQXAVLYDULUUIGUNYDULUUIUNUOZUUPUV
        BYDUUJUUKUUNUUTUVIUUPXBUURUUSUVCUVABUFUFFULXCXHXDUEXEXFYTYKUUIUNUOZYDYN
        GUUIYKUNUEXGYDUUJUUKUUNUVFUVJYNXBUURUUSUVCUVHBUFUFFYKXCXHXIXJYNYMUFCNYP
        XKZXLZUQZYRYMUFFUVLUDXMYPXNUHZCNUQUVMYRXBUVNCNYOKXSXOYMYQCUFNYPUVKXNUVK
        VKYLYPYKUNXPXQXRXTYA $.

      $( Lemma for ~ minveco .  Since any two minimal points are distance zero
         away from each other, the minimal point is unique.  (Contributed by
         Mario Carneiro, 9-May-2014.)  (New usage is discouraged.) $)
      minvecolem7 $p |- ( ph -> E! x e. Y A. y e. Y
                        ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) ) $=
        ( vw cv co cfv cle wbr wral wrex wa wceq wreu minvecolem5 wcel cexp cc0
        wi c2 caddc c4 cmul ccphlo ad2antrr css ccbn cin cr 0re simplrl simplrr
        a1i simprl simprr minvecolem2 ex wb minvecolem6 adantrr adantrl anbi12d
        0le0 4cn mul01i breq2i cmet cnv phnv syl adantr imsmet wss inss1 sselid
        eqid sspba syl2anc sseldd metcl syl3anc sqge0d biantrud resqcld sylancl
        letri3 recnd sqeq0 meteq0 bitrd 3bitr2d bitrid 3imtr3d ralrimivva oveq2
        cc fveq2d breq1d ralbidv reu4 sylanbrc ) ADBUGZJUHZKUIZDCUGJUHKUIZUJUKZ
        CNULZBNUMYIDUFUGZJUHZKUIZYGUJUKZCNULZUNZYDYJUOZVAZUFNULBNULYIBNUPABCDEF
        GHIJKLMNOPQRSTUAUBUCUDUEUQAYQBUFNNAYDNURZYJNURZUNZUNZDYDEUHVBUSUHGVBUSU
        HUTVCUHZUJUKZDYJEUHVBUSUHUUBUJUKZUNZYDYJEUHZVBUSUHZVDUTVEUHZUJUKZYOYPUU
        AUUEUUIUUAUUEUNZCDUTEFGHIYDYJJKLMNOPQRAHVFURZYTUUESVGALHVHUIZVIVJZURYTU
        UETVGADMURYTUUEUAVGUBUCUDUEUTVKURZUUJVLVOUTUTUJUKUUJWEVOAYRYSUUEVMAYRYS
        UUEVNUUAUUCUUDVPUUAUUCUUDVQVRVSUUAUUCYIUUDYNAYRUUCYIVTYSABCDEFGHIJKLMNO
        PQRSTUAUBUCUDUEWAWBAYSUUDYNVTYRAUFCDEFGHIJKLMNOPQRSTUAUBUCUDUEWAWCWDUUI
        UUGUTUJUKZUUAYPUUHUTUUGUJVDWFWGWHUUAUUOUUOUTUUGUJUKZUNZUUGUTUOZYPUUAUUP
        UUOUUAUUFUUAEMWIUIURZYDMURZYJMURZUUFVKURUUAHWJURZUUSAUVBYTAUUKUVBSHWKWL
        ZWMEHMOUBWNWLZUUANMYDANMWOZYTAUVBLUULURUVEUVCAUUMUULLUULVIWPTWQHUULLMNO
        RUULWRWSWTWMZAYRYSVPXAZUUANMYJUVFAYRYSVQXAZYDYJEMXBXCZXDXEUUAUUGVKURUUN
        UURUUQVTUUAUUFUVIXFVLUUGUTXHXGUUAUURUUFUTUOZYPUUAUUFXRURUURUVJVTUUAUUFU
        VIXIUUFXJWLUUAUUSUUTUVAUVJYPVTUVDUVGUVHYDYJEMXKXCXLXMXNXOXPYIYNBUFNYPYH
        YMCNYPYFYLYGUJYPYEYKKYDYJDJXQXSXTYAYBYC $.
    $}

    $( Minimizing vector theorem, or the Hilbert projection theorem.  There is
       exactly one vector in a complete subspace ` W ` that minimizes the
       distance to an arbitrary vector ` A ` in a parent inner product space.
       Theorem 3.3-1 of [Kreyszig] p. 144, specialized to subspaces instead of
       convex subsets.  (Contributed by NM, 11-Apr-2008.)  (Proof shortened by
       Mario Carneiro, 9-May-2014.)  (New usage is discouraged.) $)
    minveco $p |- ( ph -> E! x e. Y A. y e. Y
                   ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) ) $=
      ( vj cfv eqid cims cv co cmpt crn cr cinf cmopn wceq oveq2 fveq2d cbvmptv
      clt rneqi minvecolem7 ) ABCDEUASZRJDRUBZFUCZGSZUDZUEZVAUFUMUGZEUPUHSZFGHI
      JKLMNOPQUPTVCTUTCJDCUBZFUCZGSZUDRCJUSVFUQVDUIURVEGUQVDDFUJUKULUNVBTUO $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Complex Hilbert spaces
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definition and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c CHilOLD $.

  $( Extend class notation with the class of all complex Hilbert spaces. $)
  chlo $a class CHilOLD $.

  $( Define the class of all complex Hilbert spaces.  A Hilbert space is a
     Banach space which is also an inner product space.  (Contributed by Steve
     Rodriguez, 28-Apr-2007.)  (New usage is discouraged.) $)
  df-hlo $a |- CHilOLD = ( CBan i^i CPreHilOLD ) $.

  $( The predicate "is a complex Hilbert space."  A Hilbert space is a Banach
     space which is also an inner product space, i.e. whose norm satisfies the
     parallelogram law.  (Contributed by Steve Rodriguez, 28-Apr-2007.)
     (New usage is discouraged.) $)
  ishlo $p |- ( U e. CHilOLD <-> ( U e. CBan /\ U e. CPreHilOLD ) ) $=
    ( ccbn ccphlo chlo df-hlo elin2 ) ABCDEF $.

  $( Every complex Hilbert space is a complex Banach space.  (Contributed by
     Steve Rodriguez, 28-Apr-2007.)  (New usage is discouraged.) $)
  hlobn $p |- ( U e. CHilOLD -> U e. CBan ) $=
    ( chlo wcel ccbn ccphlo ishlo simplbi ) ABCADCAECAFG $.

  $( Every complex Hilbert space is an inner product space (also called a
     pre-Hilbert space).  (Contributed by NM, 28-Apr-2007.)
     (New usage is discouraged.) $)
  hlph $p |- ( U e. CHilOLD -> U e. CPreHilOLD ) $=
    ( chlo wcel ccbn ccphlo ishlo simprbi ) ABCADCAECAFG $.

  $( The class of all complex Hilbert spaces is a relation.  (Contributed by
     NM, 17-Mar-2007.)  (New usage is discouraged.) $)
  hlrel $p |- Rel CHilOLD $=
    ( vx chlo ccbn wss wrel cv hlobn ssriv bnrel relss mp2 ) BCDCEBEABCAFGHIBCJ
    K $.

  $( Every complex Hilbert space is a normed complex vector space.
     (Contributed by NM, 17-Mar-2007.)  (New usage is discouraged.) $)
  hlnv $p |- ( U e. CHilOLD -> U e. NrmCVec ) $=
    ( chlo wcel ccbn cnv hlobn bnnv syl ) ABCADCAECAFAGH $.

  ${
    hlnvi.1 $e |- U e. CHilOLD $.
    $( Every complex Hilbert space is a normed complex vector space.
       (Contributed by NM, 6-Jun-2008.)  (New usage is discouraged.) $)
    hlnvi $p |- U e. NrmCVec $=
      ( chlo wcel cnv hlnv ax-mp ) ACDAEDBAFG $.
  $}

  ${
    hlvc.1 $e |- W = ( 1st ` U ) $.
    $( Every complex Hilbert space is a complex vector space.  (Contributed by
       NM, 7-Sep-2007.)  (New usage is discouraged.) $)
    hlvc $p |- ( U e. CHilOLD -> W e. CVecOLD ) $=
      ( chlo wcel cnv cvc hlnv nvvc syl ) ADEAFEBGEAHABCIJ $.
  $}

  ${
    hlcmet.x $e |- X = ( BaseSet ` U ) $.
    hlcmet.8 $e |- D = ( IndMet ` U ) $.
    $( The induced metric on a complex Hilbert space is complete.  (Contributed
       by NM, 8-Sep-2007.)  (New usage is discouraged.) $)
    hlcmet $p |- ( U e. CHilOLD -> D e. ( CMet ` X ) ) $=
      ( chlo wcel ccbn ccmet cfv hlobn cbncms syl ) BFGBHGACIJGBKABCDELM $.

    $( The induced metric on a complex Hilbert space.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hlmet $p |- ( U e. CHilOLD -> D e. ( Met ` X ) ) $=
      ( chlo wcel ccmet cfv cmet hlcmet cmetmet syl ) BFGACHIGACJIGABCDEKACLM
      $.
  $}

  ${
    hlpar2.1 $e |- X = ( BaseSet ` U ) $.
    hlpar2.2 $e |- G = ( +v ` U ) $.
    hlpar2.3 $e |- M = ( -v ` U ) $.
    hlpar2.6 $e |- N = ( normCV ` U ) $.
    $( The parallelogram law satisfied by Hilbert space vectors.  (Contributed
       by Steve Rodriguez, 28-Apr-2007.)  (New usage is discouraged.) $)
    hlpar2 $p |- ( ( U e. CHilOLD /\ A e. X /\ B e. X ) ->
      ( ( ( N ` ( A G B ) ) ^ 2 ) + ( ( N ` ( A M B ) ) ^ 2 ) ) =
        ( 2 x. ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) ) $=
      ( chlo wcel ccphlo co cfv c2 cexp caddc cmul wceq hlph phpar2 syl3an1 ) C
      LMCNMAGMBGMABDOFPQROABEOFPQROSOQAFPQROBFPQROSOTOUACUBABCDEFGHIJKUCUD $.
  $}

  ${
    hlpar.1 $e |- X = ( BaseSet ` U ) $.
    hlpar.2 $e |- G = ( +v ` U ) $.
    hlpar.4 $e |- S = ( .sOLD ` U ) $.
    hlpar.6 $e |- N = ( normCV ` U ) $.
    $( The parallelogram law satisfied by Hilbert space vectors.  (Contributed
       by Steve Rodriguez, 28-Apr-2007.)  (New usage is discouraged.) $)
    hlpar $p |- ( ( U e. CHilOLD /\ A e. X /\ B e. X ) ->
      ( ( ( N ` ( A G B ) ) ^ 2 ) + ( ( N ` ( A G ( -u 1 S B ) ) ) ^ 2 ) ) =
        ( 2 x. ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) ) $=
      ( chlo wcel ccphlo co cfv c2 cexp c1 caddc cneg cmul wceq phpar syl3an1
      hlph ) DLMDNMAGMBGMABEOFPQROASUABCOEOFPQROTOQAFPQROBFPQROTOUBOUCDUFABCDEF
      GHIJKUDUE $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Standard axioms for a complex Hilbert space
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    hlex.1 $e |- X = ( BaseSet ` U ) $.
    $( The base set of a Hilbert space is a set.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hlex $p |- X e. _V $=
      ( cba fvexi ) BADCE $.
  $}

  ${
    hladdf.1 $e |- X = ( BaseSet ` U ) $.
    hladdf.2 $e |- G = ( +v ` U ) $.
    $( Mapping for Hilbert space vector addition.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hladdf $p |- ( U e. CHilOLD -> G : ( X X. X ) --> X ) $=
      ( chlo wcel cnv cxp wf hlnv nvgf syl ) AFGAHGCCICBJAKABCDELM $.

    $( Hilbert space vector addition is commutative.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hlcom $p |- ( ( U e. CHilOLD /\ A e. X /\ B e. X ) ->
                ( A G B ) = ( B G A ) ) $=
      ( chlo wcel cnv co wceq hlnv nvcom syl3an1 ) CHICJIAEIBEIABDKBADKLCMABCDE
      FGNO $.

    $( Hilbert space vector addition is associative.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hlass $p |- ( ( U e. CHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                   ( ( A G B ) G C ) = ( A G ( B G C ) ) ) $=
      ( chlo wcel cnv w3a co wceq hlnv nvass sylan ) DIJDKJAFJBFJCFJLABEMCEMABC
      EMEMNDOABCDEFGHPQ $.
  $}

  ${
    hl0cl.1 $e |- X = ( BaseSet ` U ) $.
    hl0cl.5 $e |- Z = ( 0vec ` U ) $.
    $( The Hilbert space zero vector.  (Contributed by NM, 7-Sep-2007.)
       (New usage is discouraged.) $)
    hl0cl $p |- ( U e. CHilOLD -> Z e. X ) $=
      ( chlo wcel cnv hlnv nvzcl syl ) AFGAHGCBGAIABCDEJK $.
  $}

  ${
    hladdid.1 $e |- X = ( BaseSet ` U ) $.
    hladdid.2 $e |- G = ( +v ` U ) $.
    hladdid.5 $e |- Z = ( 0vec ` U ) $.
    $( Hilbert space addition with the zero vector.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hladdid $p |- ( ( U e. CHilOLD /\ A e. X ) -> ( A G Z ) = A ) $=
      ( chlo wcel cnv co wceq hlnv nv0rid sylan ) BIJBKJADJAECLAMBNABCDEFGHOP
      $.
  $}

  ${
    hlmulf.1 $e |- X = ( BaseSet ` U ) $.
    hlmulf.4 $e |- S = ( .sOLD ` U ) $.
    $( Mapping for Hilbert space scalar multiplication.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hlmulf $p |- ( U e. CHilOLD -> S : ( CC X. X ) --> X ) $=
      ( chlo wcel cnv cc cxp wf hlnv nvsf syl ) BFGBHGICJCAKBLABCDEMN $.

    $( Hilbert space scalar multiplication by one.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hlmulid $p |- ( ( U e. CHilOLD /\ A e. X ) -> ( 1 S A ) = A ) $=
      ( chlo wcel cnv c1 co wceq hlnv nvsid sylan ) CGHCIHADHJABKALCMABCDEFNO
      $.

    $( Hilbert space scalar multiplication associative law.  (Contributed by
       NM, 7-Sep-2007.)  (New usage is discouraged.) $)
    hlmulass $p |- ( ( U e. CHilOLD /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
                   ( ( A x. B ) S C ) = ( A S ( B S C ) ) ) $=
      ( chlo wcel cnv cc w3a cmul co wceq hlnv nvsass sylan ) EIJEKJALJBLJCFJMA
      BNOCDOABCDODOPEQABCDEFGHRS $.
  $}

  ${
    hldi.1 $e |- X = ( BaseSet ` U ) $.
    hldi.2 $e |- G = ( +v ` U ) $.
    hldi.4 $e |- S = ( .sOLD ` U ) $.
    $( Hilbert space scalar multiplication distributive law.  (Contributed by
       NM, 7-Sep-2007.)  (New usage is discouraged.) $)
    hldi $p |- ( ( U e. CHilOLD /\ ( A e. CC /\ B e. X /\ C e. X ) ) ->
                  ( A S ( B G C ) ) = ( ( A S B ) G ( A S C ) ) ) $=
      ( chlo wcel cnv cc w3a co wceq hlnv nvdi sylan ) EKLEMLANLBGLCGLOABCFPDPA
      BDPACDPFPQERABCDEFGHIJST $.

    $( Hilbert space scalar multiplication distributive law.  (Contributed by
       NM, 7-Sep-2007.)  (New usage is discouraged.) $)
    hldir $p |- ( ( U e. CHilOLD /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
                  ( ( A + B ) S C ) = ( ( A S C ) G ( B S C ) ) ) $=
      ( chlo wcel cnv cc w3a caddc co wceq hlnv nvdir sylan ) EKLEMLANLBNLCGLOA
      BPQCDQACDQBCDQFQRESABCDEFGHIJTUA $.
  $}

  ${
    hlmul0.1 $e |- X = ( BaseSet ` U ) $.
    hlmul0.4 $e |- S = ( .sOLD ` U ) $.
    hlmul0.5 $e |- Z = ( 0vec ` U ) $.
    $( Hilbert space scalar multiplication by zero.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hlmul0 $p |- ( ( U e. CHilOLD /\ A e. X ) -> ( 0 S A ) = Z ) $=
      ( chlo wcel cnv cc0 co wceq hlnv nv0 sylan ) CIJCKJADJLABMENCOABCDEFGHPQ
      $.
  $}

  ${
    hlipf.1 $e |- X = ( BaseSet ` U ) $.
    hlipf.7 $e |- P = ( .iOLD ` U ) $.
    $( Mapping for Hilbert space inner product.  (Contributed by NM,
       19-Nov-2007.)  (New usage is discouraged.) $)
    hlipf $p |- ( U e. CHilOLD -> P : ( X X. X ) --> CC ) $=
      ( chlo wcel cnv cxp cc wf hlnv ipf syl ) BFGBHGCCIJAKBLABCDEMN $.

    $( Conjugate law for Hilbert space inner product.  (Contributed by NM,
       8-Sep-2007.)  (New usage is discouraged.) $)
    hlipcj $p |- ( ( U e. CHilOLD /\ A e. X /\ B e. X ) ->
                  ( A P B ) = ( * ` ( B P A ) ) ) $=
      ( chlo wcel w3a co ccj cfv wceq cnv hlnv dipcj syl3an1 3com23 eqcomd ) DH
      IZAEIZBEIZJBACKLMZABCKZUAUCUBUDUENZUADOIUCUBUFDPBACDEFGQRST $.
  $}

  ${
    hlipdir.1 $e |- X = ( BaseSet ` U ) $.
    hlipdir.2 $e |- G = ( +v ` U ) $.
    hlipdir.7 $e |- P = ( .iOLD ` U ) $.
    $( Distributive law for Hilbert space inner product.  (Contributed by NM,
       8-Sep-2007.)  (New usage is discouraged.) $)
    hlipdir $p |- ( ( U e. CHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                  ( ( A G B ) P C ) = ( ( A P C ) + ( B P C ) ) ) $=
      ( chlo wcel ccphlo w3a co caddc wceq hlph dipdir sylan ) EKLEMLAGLBGLCGLN
      ABFOCDOACDOBCDOPOQERABCDEFGHIJST $.
  $}

  ${
    hlipass.1 $e |- X = ( BaseSet ` U ) $.
    hlipass.4 $e |- S = ( .sOLD ` U ) $.
    hlipass.7 $e |- P = ( .iOLD ` U ) $.
    $( Associative law for Hilbert space inner product.  (Contributed by NM,
       8-Sep-2007.)  (New usage is discouraged.) $)
    hlipass $p |- ( ( U e. CHilOLD /\ ( A e. CC /\ B e. X /\ C e. X ) ) ->
                  ( ( A S B ) P C ) = ( A x. ( B P C ) ) ) $=
      ( chlo wcel ccphlo cc w3a co cmul wceq hlph dipass sylan ) FKLFMLANLBGLCG
      LOABEPCDPABCDPQPRFSABCDEFGHIJTUA $.
  $}

  ${
    hlipgt0.1 $e |- X = ( BaseSet ` U ) $.
    hlipgt0.5 $e |- Z = ( 0vec ` U ) $.
    hlipgt0.7 $e |- P = ( .iOLD ` U ) $.
    $( The inner product of a Hilbert space vector by itself is positive.
       (Contributed by NM, 8-Sep-2007.)  (New usage is discouraged.) $)
    hlipgt0 $p |- ( ( U e. CHilOLD /\ A e. X /\ A =/= Z ) -> 0 < ( A P A ) ) $=
      ( chlo wcel cnv wne cc0 co clt wbr hlnv cfv 3adant3 wceq cnmcv c2 cexp cr
      w3a eqid nvcl wa nvz biimpd necon3d 3impia sqgt0d ipidsq breqtrrd syl3an1
      ) CIJCKJZADJZAELZMAABNZOPCQUQURUSUEZMACUARZRZUBUCNZUTOVAVCUQURVCUDJUSACVB
      DFVBUFZUGSUQURUSVCMLUQURUHZVCMAEVFVCMTAETACVBDEFGVEUIUJUKULUMUQURUTVDTUSA
      BCVBDFVEHUNSUOUP $.
  $}

  ${
    hlcompl.1 $e |- D = ( IndMet ` U ) $.
    hlcompl.2 $e |- J = ( MetOpen ` D ) $.
    $( Completeness of a Hilbert space.  (Contributed by NM, 8-Sep-2007.)
       (Revised by Mario Carneiro, 9-May-2014.)  (New usage is discouraged.) $)
    hlcompl $p |- ( ( U e. CHilOLD /\ F e. ( Cau ` D ) ) ->
                    F e. dom ( ~~>t ` J ) ) $=
      ( chlo wcel cba cfv ccmet ccau clm cdm eqid hlcmet cmetcau sylan ) BGHABI
      JZKJHCALJHCDMJNHABSSOEPACDSFQR $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Examples of complex Hilbert spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    cnhl.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The set of complex numbers is a complex Hilbert space.  (Contributed by
       Steve Rodriguez, 28-Apr-2007.)  (New usage is discouraged.) $)
    cnchl $p |- U e. CHilOLD $=
      ( chlo wcel ccbn ccphlo cnbn cncph ishlo mpbir2an ) ACDAEDAFDABGABHAIJ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Hellinger-Toeplitz Theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d w y F $.  $d w x y z K $.  $d w x y z N $.  $d w z P $.  $d w x y z W $.
    $d w x y z ph $.  $d u v w x y z T $.  $d u v w x y z U $.  $d w x y z X $.
    htth.1 $e |- X = ( BaseSet ` U ) $.
    htth.2 $e |- P = ( .iOLD ` U ) $.
    htth.3 $e |- L = ( U LnOp U ) $.
    htth.4 $e |- B = ( U BLnOp U ) $.
    ${
      htthlem.5 $e |- N = ( normCV ` U ) $.
      htthlem.6 $e |- U e. CHilOLD $.
      htthlem.7 $e |- W = <. <. + , x. >. , abs >. $.
      htthlem.8 $e |- ( ph -> T e. L ) $.
      htthlem.9 $e |- ( ph -> A. x e. X A. y e. X
                        ( x P ( T ` y ) ) = ( ( T ` x ) P y ) ) $.
      htthlem.10 $e |- F = ( z e. X |-> ( w e. X |-> ( w P ( T ` z ) ) ) ) $.
      htthlem.11 $e |- K = ( F " { z e. X | ( N ` z ) <_ 1 } ) $.
      $( Lemma for ~ htth .  The collection ` K ` , which consists of functions
         ` F ( z ) ( w ) = <. w | T ( z ) >. = <. T ( w ) | z >. ` for each
         ` z ` in the unit ball, is a collection of bounded linear functions by
         ~ ipblnfi , so by the Uniform Boundedness theorem ~ ubth , there is a
         uniform bound ` y ` on ` || F ( x ) || ` for all ` x ` in the unit
         ball.  Then ` | T ( x ) | ^ 2 = <. T ( x ) | T ( x ) >. = F ( x ) ( `
         ` T ( x ) ) <_ y | T ( x ) | ` , so ` | T ( x ) | <_ y ` and ` T ` is
         bounded.  (Contributed by NM, 11-Jan-2008.)  (Revised by Mario
         Carneiro, 23-Aug-2014.)  (New usage is discouraged.) $)
      htthlem $p |- ( ph -> T e. B ) $=
        ( wcel cnmoo co cfv cpnf clt wbr cr cv c1 cle wi wral wrex wa cnv hlnvi
        cabs lnof mp3an12 ffvelcdmda nvcl sylancr wceq crab wfun cima cblo cmpt
        wf syl chlo ccphlo hlph ax-mp eqid ipblnfi fmptd ffund eleqtrdi fvelima
        adantr id syl2an ex weq fveq2 breq1d elrab cba oveq2d mpteq2dv mptfvmpt
        fveq1d oveq1 ovex fvmpt sylan9eqr ad2ant2lr rsp2 impl eqtrd fveq2d cmul
        adantrr simpl dipcl mp3an1 abscld mpan ad2antrl remulcld sii 1red nvge0
        cc0 jca simprr lemul2a syl31anc recnd mulridd breqtrd eqbrtrd syl5ibcom
        cc letrd syld syl2anc wb mpbid ad2ant2r mpd expr sylan2b fveq1 ralrimiv
        rexlimdva brralrspcev ralrimiva wss crn imassrn eqsstri frnd ccbn hlobn
        sstrid cnnv cnnvnm ubth bilanri cdm dmmptd eleq2d funfvima sylan syldan
        biimpar eleqtrrdi rspcv cnnvba nmblore simplr cexp adantl ipidsq resqcl
        c2 sqge0 absidd sqvald 3eqtrd nmblolbi eqbrtrrd lemul1ad lemul1 biimprd
        w3a 3expia expdimp syl21anc mpid 0red nmooge0 breq1 wo 0re leloe mpjaod
        blof com23 ralrimdva reximdva nmobndi mpbird ltpnf isblo mp2an sylanbrc
        ) AHLUGZHIIUHUIZUJZUKULUMZHFUGZUCAUXIUNUGZUXJAUXLBUOZMUJZUPUQUMZUXMHUJZ
        MUJZCUOZUQUMZURZBOUSZCUNUTZAEUOZINUHUIZUJZUXRUQUMZEKUSZCUNUTZUYBAUXMUYC
        UJZVDUJZDUOZUQUMEKUSDUNUTZBOUSZUYHAUYLBOAUXMOUGZVAZUXQUNUGZUYJUXQUQUMZE
        KUSUYLUYOIVBUGZUXPOUGZUYPIUAVCZAOOUXMHAUXGOOHVPZUCUYRUYRUXGVUAUYTUYTHIL
        IOOPPRVEVFVQZVGZUXPIMOPTVHVIZUYOUYQEKUYOUYCKUGZUXRJUJZUYCVJZCUYKMUJZUPU
        QUMZDOVKZUTZUYQUYOVUEVUKUYOJVLZUYCJVUJVMZUGVUKVUEAVULUYNAOINVNUIZJADOEO
        UYCUYKHUJZGUIZVOZVUNJAUYKOUGVAVUOOUGVUQVUNUGAOOUYKHVUBVGEVUOVUNNGIVUQOP
        QIVRUGZIVSUGUAIVTWAZUBVUNWBZVUQWBWCVQZUEWDZWEZWHVUEUYCKVUMVUEWIUFWFCUYC
        VUJJWGWJWKUYOVUGUYQCVUJUYOUXRVUJUGZVAUXMVUFUJZVDUJZUXQUQUMZVUGUYQVVDUYO
        UXROUGZUXRMUJZUPUQUMZVAZVVGVUIVVJDUXRODCWLZVUHVVIUPUQUYKUXRMWMWNWOUYOVV
        KVAZVVFUXPUXRGUIZVDUJZUXQUQVVMVVEVVNVDVVMVVEUXMUXRHUJZGUIZVVNUYNVVHVVEV
        VQVJAVVJVVHUYNVVEUXMEOUYCVVPGUIZVOZUJVVQVVHUXMVUFVVSEDVVRWPJVUQOOIUXRVV
        LEOVUPVVRVVLVUOVVPUYCGUYKUXRHWMWQWRUEPWSWTEUXMVVRVVQOVVSUYCUXMVVPGXAVVS
        WBUXMVVPGXBXCXDXEUYOVVHVVQVVNVJZVVJAUYNVVHVVTAVVTCOUSBOUSUYNVVHVAVVTURU
        DVVTBCOOXFVQXGXKXHXIVVMVVOUXQVVIXJUIZUXQVVMVVNUYOUYSVVHVVNYLUGZVVKVUCVV
        HVVJXLZUYRUYSVVHVWBUYTUXPUXRGIOPQXMXNWJXOVVMUXQVVIUYOUYPVVKVUDWHZVVHVVI
        UNUGZUYOVVJUYRVVHVWEUYTUXRIMOPTVHXPXQZXRVWDUYOUYSVVHVVOVWAUQUMVVKVUCVWC
        UXPUXRGIMOPTQVUSXSWJVVMVWAUXQUPXJUIZUXQUQVVMVWEUPUNUGUYPYBUXQUQUMZVAZVV
        JVWAVWGUQUMVWFVVMXTUYOVWIVVKUYOUYPVWHVUDUYOUYRUYSVWHUYTVUCUXPIMOPTYAZVI
        YCWHUYOVVHVVJYDVVIUPUXQYEYFVVMUXQVVMUXQVWDYGYHYIYMYJUUAVUGVVFUYJUXQUQVU
        GVVEUYIVDUXMVUFUYCUUBXIWNYKUUDYNUUCDEUYJUXQUQUNKUUEYOUUFAKVUNUUGZUYMUYH
        YPZAKJUUHZVUNKVUMVWMUFJVUJUUIUUJAOVUNJVVBUUKUUNIUULUGZNVBUGZVWKVWLVURVW
        NUAIUUMWANUBUUOZBEKIUYDVDNODCPNUBUUPZUYDWBZUUQVFVQYQAUYGUYACUNAUXRUNUGZ
        VAZUYGUXTBOVWTUYNVAUXOUYGUXSVWTUYNUXOUYGUXSURVWTUYNUXOVAZVAZUYGUXMJUJZU
        YDUJZUXRUQUMZUXSVXBVXCKUGUYGVXEURVXBVXCVUMKVXBUXMVUJUGZVXCVUMUGZVXFVXAV
        WTVUIUXODUXMODBWLZVUHUXNUPUQUYKUXMMWMWNWOUURAUYNVXFVXGURZVWSUXOAUYNUXMJ
        UUSZUGZVXIAVXKUYNAVXJOUXMADJOVUQVUNUEVVAUUTUVAUVEAVULVXKVXIVVCVUJUXMJUV
        BUVCUVDYRYSUFUVFUYFVXEEVXCKUYCVXCVJUYEVXDUXRUQUYCVXCUYDWMWNUVGVQVWTUYNV
        XEUXSURUXOVWTUYNVXEUXSVWTUYNVXEVAZVAZYBUXQULUMZUXSYBUXQVJZVXMVXNUXQUXQX
        JUIZUXRUXQXJUIZUQUMZUXSVXMVXPVXDUXQXJUIZVXQVXMUXQUXQAUYNUYPVWSVXEVUDYRZ
        VXTXRVXMVXDUXQAUYNVXDUNUGZVWSVXEUYOVXCVUNUGZVYAAOVUNUXMJVVBVGZUYRVWOVYB
        VYAUYTVWPVUNVXCIUYDNOYLPNUBUVHZVWRVUTUVIVFVQYRZVXTXRVXMUXRUXQAVWSVXLUVJ
        ZVXTXRVXMUXPVXCUJZVDUJZVXPVXSUQVXMVYHUXQUVOUVKUIZVDUJZVYIVXPVXMVYGVYIVD
        VXMVYGUXPUXPGUIZVYIAUYNVYGVYKVJVWSVXEUYOVYGUXPEOUYCUXPGUIZVOZUJZVYKUYOU
        XPVXCVYMUYNVXCVYMVJAEDVYLWPJVUQOOIUXMVXHEOVUPVYLVXHVUOUXPUYCGUYKUXMHWMW
        QWRUEPWSUVLWTUYOUYSVYNVYKVJVUCEUXPVYLVYKOVYMUYCUXPUXPGXAVYMWBUXPUXPGXBX
        CVQXHYRVXMUYRUYSVYKVYIVJUYTAUYNUYSVWSVXEVUCYRZUXPGIMOPTQUVMVIXHXIVXMUYP
        VYJVYIVJVXTUYPVYIUXQUVNUXQUVPUVQVQVXMUXQVXMUXQVXTYGUVRUVSVXMVYBUYSVYHVX
        SUQUMAUYNVYBVWSVXEVYCYRVYOUXPVUNVXCIMVDUYDNOPTVWQVWRVUTUYTVWPUVTYOUWAVX
        MVXDUXRUXQVYEVYFVXTVXMUYRUYSVWHUYTVYOVWJVIZVWTUYNVXEYDZUWBYMVXMUYPVWSUY
        PVXNVXRUXSURZURVXTVYFVXTUYPVWSVAUYPVXNVYRUYPVWSUYPVXNVAZVYRUYPVWSVYSUWE
        UXSVXRUXQUXRUXQUWCUWDUWFUWGUWHUWIVXMYBUXRUQUMVXOUXSVXMYBVXDUXRVXMUWJVYE
        VYFVXMOYLVXCVPZYBVXDUQUMZAUYNVYTVWSVXEUYOVYBVYTVYCUYRVWOVYBVYTUYTVWPVUN
        VXCINOYLPVYDVUTUWQVFVQYRUYRVWOVYTWUAUYTVWPVXCIUYDNOYLPVYDVWRUWKVFVQVYQY
        MYBUXQUXRUQUWLYKVXMVWHVXNVXOUWMZVYPVXMYBUNUGUYPVWHWUBYPUWNVXTYBUXQUWOVI
        YQUWPYTXKYNYTUWRUWSUWTYSAVUAUXLUYBYPVUBBHIMMUXHIOOCPPTTUXHWBZUYTUYTUXAV
        QUXBUXIUXCVQUYRUYRUXKUXGUXJVAYPUYTUYTFHILUXHIWUCRSUXDUXEUXF $.
    $}

    $( Hellinger-Toeplitz Theorem: any self-adjoint linear operator defined on
       all of Hilbert space is bounded.  Theorem 10.1-1 of [Kreyszig] p. 525.
       Discovered by E. Hellinger and O. Toeplitz in 1910, "it aroused both
       admiration and puzzlement since the theorem establishes a relation
       between properties of two different kinds, namely, the properties of
       being defined everywhere and being bounded."  (Contributed by NM,
       11-Jan-2008.)  (Revised by Mario Carneiro, 23-Aug-2014.)
       (New usage is discouraged.) $)
    htth $p |- ( ( U e. CHilOLD /\ T e. L /\
        A. x e. X A. y e. X ( x P ( T ` y ) ) = ( ( T ` x ) P y ) ) ->
      T e. B ) $=
      ( vw cv cfv co wceq wral fveq2 eqid vu vv vz chlo wcel wa caddc cmul cabs
      wi cop cif clno cdip cba cblo oveq12 anidms eqtrid eleq2d oveqd raleqbidv
      eqeq12d anbi12d imbi12d cmpt cnmcv c1 cle wbr crab cima cnchl simpl oveq1
      elimel oveq1d oveq2d oveq2 bilani cbvmptv mpteq2dv breq1d cbvrabv imaeq2i
      cbvral2vw htthlem dedth 3impib ) FUDUEZEGUEZANZBNZEOZDPZWLEOZWMDPZQZBHRZA
      HRZECUEZWJWKWTUFZXAUJEWJFUGUHUKUIUKZULZXDUMPZUEZWLWNXDUNOZPZWPWMXGPZQZBXD
      UOOZRZAXKRZUFZEXDXDUPPZUEZUJFXCFXDQZXBXNXAXPXQWKXFWTXMXQGXEEXQGFFUMPZXEKX
      QXRXEQFXDFXDUMUQURUSUTXQWSXLAHXKXQHFUOOXKIFXDUOSUSZXQWRXJBHXKXSXQWOXHWQXI
      XQDXGWLWNXQDFUNOXGJFXDUNSUSZVAXQDXGWPWMXTVAVCVBVBVDXQCXOEXQCFFUPPZXOLXQYA
      XOQFXDFXDUPUQURUSUTVEXNUAUBUCMXOXGEXDAXKBXKWMWPXGPZVFZVFZYDWLXDVGOZOZVHVI
      VJZAXKVKZVLXEYEXCXKXKTXGTXETXOTYETFXCUDXCXCTZVMVPYIXFXMVNXMUANZUBNZEOZXGP
      ZYJEOZYKXGPZQZUBXKRUAXKRXFXJYPYJWNXGPZYNWMXGPZQABUAUBXKXKWLYJQZXHYQXIYRWL
      YJWNXGVOYSWPYNWMXGWLYJESVQVCWMYKQZYQYMYRYOYTWNYLYJXGWMYKESVRWMYKYNXGVSVCW
      FVTAUCXKYCMXKMNZUCNZEOZXGPZVFZWLUUBQZYCMXKUUAWPXGPZVFUUEBMXKYBUUGWMUUAWPX
      GVOWAUUFMXKUUGUUDUUFWPUUCUUAXGWLUUBESVRWBUSWAYHUUBYEOZVHVIVJZUCXKVKYDYGUU
      IAUCXKUUFYFUUHVHVIWLUUBYESWCWDWEWGWHWI $.
  $}
