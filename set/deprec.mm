

$(
###############################################################################
       ADDITIONAL MATERIAL ON GROUPS, RINGS, AND FIELDS (DEPRECATED)
###############################################################################

  This part contains an earlier development of groups, rings, and fields
  that was defined before extensible structures were introduced.

  Theorem ~ grpo2grp shows the relationship between the older group definition
  and the extensible structure definition.

$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                 Additional material on group theory
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
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
  $c ^g $.

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

  $( Extend class notation with a function mapping a group operation to the
     power operation for the group. $)
  cgx $a class ^g $.

  ${
    $d f g t u x y z $.
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

    $( Define a function that maps a group operation to the group's power
       operation.  (Contributed by Paul Chapman, 17-Apr-2009.)
       (New usage is discouraged.) $)
    df-gx $a |- ^g = ( g e. GrpOp |-> ( x e. ran g , y e. ZZ |->
      if ( y = 0 , ( GId ` g ) ,
        if ( 0 < y , ( seq 1 ( g , ( NN X. { x } ) ) ` y ) ,
          ( ( inv ` g ) ` ( seq 1 ( g , ( NN X. { x } ) ) ` -u y ) ) ) ) ) ) $.
  $}

  ${
    $d g n t u x y z G $.  $d g n t u x y z X $.
    isgrp.1 $e |- X = ran G $.
    $( The predicate "is a group operation."  Note that ` X ` is the base set
       of the group.  (Contributed by NM, 10-Oct-2006.)
       (New usage is discouraged.) $)
    isgrpo $p |- ( G e. A -> ( G e. GrpOp <-> ( G : ( X X. X ) --> X /\
       A. x e. X A. y e. X A. z e. X ( ( x G y ) G z ) = ( x G ( y G z ) )
   /\ E. u e. X A. x e. X ( ( u G x ) = x /\ E. y e. X ( y G x ) = u ) ) ) ) $=
      ( vt vg wcel cv wceq cxp wf co wral wrex wa oveq cgr crn w3a oveq1d eqtrd
      wex feq1 oveq2d eqeq12d ralbidv 2ralbidv eqeq1d rexbidv anbi12d 3anbi123d
      rexralbidv exbidv df-grpo elab2g simpl ralimi oveq2 id eqcom syl6bb rspcv
      wfo eqeq2d rspcev syld syl5 reximdv impcom ralrimiva anim2i sylibr eqcomd
      ex foov forn syl 3adant2 pm4.71ri exbii wb rnexg eqeq2i xpeq1 xpeq2 feq2d
      cvv feq3 bitrd raleq raleqbi1dv rexeq anbi2d rexeqbi1dv sylbir ceqsexgv )
      FEKZFUAKZILZFUBZMZXCXCNZXCFOZALZBLZFPZCLZFPZXHXIXKFPZFPZMZCXCQZBXCQZAXCQZ
      DLZXHFPZXHMZXIXHFPZXSMZBXCRZSZAXCQZDXCRZUCZSZIUFZGGNZGFOZXOCGQZBGQZAGQZYA
      YCBGRZSZAGQZDGRZUCZXAXBYHIUFZYJXFXCJLZOZXHXIUUBPZXKUUBPZXHXIXKUUBPZUUBPZM
      ZCXCQZBXCQAXCQZXSXHUUBPZXHMZXIXHUUBPZXSMZBXCRZSZAXCQDXCRZUCZIUFUUAJFUAEUU
      BFMZUURYHIUUSUUCXGUUJXRUUQYGXFXCUUBFUGUUSUUIXPABXCXCUUSUUHXOCXCUUSUUEXLUU
      GXNUUSUUEUUDXKFPXLUUDXKUUBFTUUSUUDXJXKFXHXIUUBFTUDUEUUSUUGXHUUFFPXNXHUUFU
      UBFTUUSUUFXMXHFXIXKUUBFTUHUEUIUJUKUUSUUPYEDAXCXCUUSUULYAUUOYDUUSUUKXTXHXS
      XHUUBFTULUUSUUNYCBXCUUSUUMYBXSXIXHUUBFTULUMUNUPUOUQABCDIJURUSYHYIIYHXEXGY
      GXEXRXGYGSZXFXCFVGZXEUUTXGXKXSXIFPZMZBXCRZDXCRZCXCQZSUVAYGUVFXGYGUVECXCXK
      XCKZYGUVEUVGYFUVDDXCYFYAAXCQZUVGUVDYEYAAXCYAYDUTVAUVGUVHXKXSXKFPZMZUVDYAU
      VJAXKXCXHXKMZYAUVIXKMUVJUVKXTUVIXHXKXHXKXSFVBUVKVCUIUVIXKVDVEVFUVGUVJUVDU
      VCUVJBXKXCXIXKMUVBUVIXKXIXKXSFVBVHVIVRVJVKVLVMVNVODBCXCXCXCFVSVPUVAXDXCXF
      XCFVTVQWAWBWCWDVEXAXDWKKYJYTWEFEWFYHYTIXDWKXEXCGMZYHYTWEGXDXCHWGUVLXGYLXR
      YOYGYSUVLXGYKXCFOYLUVLXFYKXCFUVLXFGXCNYKXCGXCWHXCGGWIUEWJXCGYKFWLWMXQYNAX
      CGXPYMBXCGXOCXCGWNWOWOYFYRDXCGYEYQAXCGUVLYDYPYAYCBXCGWPWQWOWRUOWSWTWAWM
      $.

    $( The predicate "is a group operation."  (Contributed by NM,
       23-Oct-2012.)  (New usage is discouraged.) $)
    isgrpo2 $p |- ( G e. A -> ( G e. GrpOp <-> ( G : ( X X. X ) --> X /\
       A. x e. X A. y e. X A. z e. X
         ( ( x G y ) e. X /\ ( ( x G y ) G z ) = ( x G ( y G z ) ) )
   /\ E. u e. X A. x e. X ( ( u G x ) = x /\ E. n e. X ( n G x ) = u ) ) ) ) $=
      ( wcel cv co wceq wral wrex wa w3a 3anass syl6bb ralbidva cgr cxp crn wfn
      wf isgrpo ffn ad2antrr simplr simpr fnovrn syl3anc syl6eleqr biantrurd wb
      ralbidv weq oveq1 eqeq1d cbvrexv anbi2i ralbii rexbii a1i anbi12d pm5.32i
      bitr4i ) GEJZGUAJZHHUBZHGUEZAKZBKZGLZCKZGLVLVMVOGLGLMZCHNZBHNZAHNZDKZVLGL
      VLMZVMVLGLZVTMZBHOZPZAHNZDHOZPZPZVKVNHJZVPPZCHNZBHNZAHNZWAFKZVLGLZVTMZFHO
      ZPZAHNZDHOZQZVHVIVKVSWGQWIABCDEGHIUFVKVSWGRSWIVKWNXAPZPXBVKWHXCVKVSWNWGXA
      VKVRWMAHVKVLHJZPZVQWLBHXEVMHJZPZVPWKCHXGWJVPXGVNGUCZHXGGVJUDZXDXFVNXHJVKX
      IXDXFVJHGUGUHVKXDXFUIXEXFUJHHVLVMGUKULIUMUNUPTTWGXAUOVKWFWTDHWEWSAHWDWRWA
      WCWQBFHBFUQWBWPVTVMWOVLGURUSUTVAVBVCVDVEVFVKWNXARVGS $.
  $}

  ${
    $d u x y z G $.  $d u x y z U $.  $d u x y z X $.  $d y N $.
    isgrpi.1 $e |- X e. _V $.
    isgrpi.2 $e |- G : ( X X. X ) --> X $.
    isgrpi.3 $e |- ( ( x e. X /\ y e. X /\ z e. X ) ->
                   ( ( x G y ) G z ) = ( x G ( y G z ) ) ) $.
    isgrpi.4 $e |- U e. X $.
    isgrpi.5 $e |- ( x e. X -> ( U G x ) = x ) $.
    isgrpi.6 $e |- ( x e. X -> N e. X ) $.
    isgrpi.7 $e |- ( x e. X -> ( N G x ) = U ) $.
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
      ( cgr wcel cxp wf co wfo grpofo fof syl fovrn syl3an1 ) CFGZDDHZDCIZADGBD
      GABCJDGQRDCKSCDELRDCMNABDDDCOP $.

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
        ( vw wcel wa cv co wceq wrex wral cgr oveq1 eqeq1d cbvrexv ralbii bitri
        rexbidv rspccva sylanb adantll grpocl adantllr biimpi ad2antrl ad2antrr
        oveq2 3expa eqeq12d rspcva syl2anc adantr pm3.22 an31s adantlr adantlll
        id anim1i grpoidinvlem2 wi 3expb ad2ant2rl anass an32s ex grpoidinvlem1
        sylan2b syldan imp sylan exp43 rexlimdv syl5 mpand exp32 com34 impl mpd
        imp32 eqtr3d ancld reximdva ) HUANZGINZOZABOZOZFINZOZDPZFHQZGRZDISZXAFW
        SHQZGRZOZDISWOWQXBWNBWQXBABWSCPZHQZGRZDISZCITZWQXBBEPZXFHQZGRZEISZCITZX
        JLXNXICIXMXHEDIXKWSRXLXGGXKWSXFHUBUCUDUEUFXIXBCFIXFFRZXHXADIXPXGWTGXFFW
        SHUPUCUGUHUIUJUJWRXAXEDIWRWSINZOZXAXDXRXAXDXRXAOZGXCHQZXCGXRXTXCRZXAXRX
        CINZGXFHQZXFRZCITZYAWNWQXQYBWOWLWQXQYBWMWLWQXQYBFWSHIJUKZUQULULWPYEWQXQ
        AYEWNBAYEKUMUNUOYDYACXCIXFXCRZYCXTXFXCXFXCGHUPYGVFURUSUTVAXSXCXCHQXCRZX
        TGRZXSWLXQWQOZOZGWSHQZWSRZXAOYHXRYKXAWNWQXQYKWOWLWQXQYKWMXQWQWLYKYJWLVB
        VCULULVAXRYMXAWOWQXQYMWNWOXQYMWQAXQYMBAYEXQYMKYDYMCWSIXFWSRZYCYLXFWSXFW
        SGHUPYNVFURUHUIVDVDVEVGFGHIWSJVHUTXRYHYIVIZXAWPWQXQYOWNABWQXQOZYOVIWNAY
        PBYOWNAYPBYOVIWNAYPOOZYBBYOWLYPYBWMAWLWQXQYBYFVJZVKYBBOMPZXCHQZGRZMISZY
        QYOBYBYSXFHQZGRZMISZCITZUUBBXOUUFLXNUUECIXMUUDEMIXKYSRXLUUCGXKYSXFHUBUC
        UDUEUFUUEUUBCXCIYGUUDUUAMIYGUUCYTGXFXCYSHUPUCUGUSVPYQUUAYOMIYQYSINZUUAY
        HYIYQUUGOWLUUGYBOOZUUAYHOYIYQUUGUUHWLYPUUGUUHVIZWMAWLYPYBUUIYRWLYBOUUGU
        UHWLUUGYBUUHWLUUGOYBOUUHWLUUGYBVLUMVMVNVQVKVRXCGHIYSJVOVSVTWAWBWCWDWEWH
        WFVAWGWIVNWJWKWG $.
    $}

    $( Lemma for ~ grpoidinv .  (Contributed by NM, 14-Oct-2006.)
       (New usage is discouraged.) $)
    grpoidinvlem4 $p |- ( ( ( G e. GrpOp /\ A e. X ) /\ E. y e. X
             ( ( y G A ) = U /\ ( A G y ) = U ) ) -> ( A G U ) = ( U G A ) ) $=
      ( cgr wcel wa cv co wceq wrex simpll simplr simpr syl13anc oveq2 sylan9eq
      grpoass oveq1 sylan9req anasss exp31 rexlimdv imp ) DGHZBEHZIZAJZBDKZCLZB
      UJDKZCLZIZAEMBCDKZCBDKZLZUIUOURAEUIUJEHZUOURUIUSIZULUNURUTULIUNUPUMBDKZUQ
      UTULVABUKDKZUPUTUGUHUSUHVAVBLUGUHUSNUGUHUSOZUIUSPVCBUJBDEFTQUKCBDRSUMCBDU
      AUBUCUDUEUF $.

    $( A group has a left and right identity element, and every member has a
       left and right inverse.  (Contributed by NM, 14-Oct-2006.)
       (New usage is discouraged.) $)
    grpoidinv $p |- ( G e. GrpOp -> E. u e. X A. x e. X ( ( ( u G x ) = x /\
         ( x G u ) = x ) /\ E. y e. X ( ( y G x ) = u /\ ( x G y ) = u ) ) ) $=
      ( vz vw wcel cv co wceq wrex wa wral simpl ralimi id adantll adantl oveq2
      cgr grpolidinv eqeq12d rspccva sylan anim1i adantrr adantr ad2antlr simpr
      jca32 biid grpoidinvlem3 sylancom grpoidinvlem4 syl2anc eqtrd jca31 exp32
      ralrimiva reximdvai mpd ) DUBIZCJZGJZDKZVFLZHJVFDKVELHEMZNZGEOZCEMVEAJZDK
      ZVLLZVLVEDKZVLLZNBJZVLDKVELVLVQDKVELNBEMZNZAEOZCEMGHCDEFUCVDVKVTCEVDVEEIZ
      VKVTVDWAVKNZNZVSAEWCVLEIZNZVNVPVRWBWDVNVDVKWDVNWAVKVHGEOZWDVNVJVHGEVHVIPQ
      ZVHVNGVLEVFVLLZVGVMVFVLVFVLVEDUAWHRUDUEUFSSZWEVOVMVLWEVDWDNVRVOVMLWCVDWDV
      DWBPUGWCWDVDWANZWFVIGEOZNNVRWEWJWFWKWCWJWDVDWAWJVKWJRUHUIWBWFVDWDVKWFWAWG
      TUJWBWKVDWDVKWKWAVJVIGEVHVIUKQTUJULWFWKGBHVLVEDEFWFUMWKUMUNUOZBVLVEDEFUPU
      QWIURWLUSVAUTVBVC $.

    $( The left identity element of a group is unique.  Lemma 2.2.1(a) of
       [Herstein] p. 55.  (Contributed by NM, 14-Oct-2006.)
       (New usage is discouraged.) $)
    grpoideu $p |- ( G e. GrpOp -> E! u e. X A. x e. X ( u G x ) = x ) $=
      ( vw vz vy wcel cv co wceq wral weq wa wrex oveq2 id eqeq12d eqeq1d sylib
      cgr wi wreu grpoidinv simpll ralimi cbvralv adantl ad2antlr simpr anbi12d
      oveq1 rexbidv rspcva sylan2 grpoidinvlem4 syldan an32s adantllr ad2ant2rl
      adantll adantr ad2ant2lr 3eqtr3d mpand ralrimiva jca reximdva mpd ralbidv
      ex reu8 sylibr ) CUBIZBJZAJZCKZVQLZADMZFJZVQCKZVQLZADMZBFNZUCZFDMZOZBDPZV
      TBDUDVOVPGJZCKZWJLZWJVPCKWJLZOZHJZWJCKZVPLZWJWOCKZVPLZOZHDPZOZGDMZBDPWIGH
      BCDEUEVOXCWHBDVOVPDIZOZXCWHXEXCOZVTWGXCVTXEXCWLGDMVTXBWLGDWLWMXAUFUGWLVSG
      ADGANZWKVRWJVQWJVQVPCQXGRSUHUAZUIXFWFFDXFWADIZOZVTWDWEXCVTXEXIXHUJXJVTWDO
      ZWEXJXKOWAVPCKZVPWACKZVPWAXJXLXMLZXKVOXCXIXNXDVOXIXCXNVOXIOZXCWOWACKZVPLZ
      WAWOCKZVPLZOZHDPZXNXCXOXAGDMZYAXBXAGDWNXAUKUGXIYBYAVOXAYAGWADGFNZWTXTHDYC
      WQXQWSXSYCWPXPVPWJWAWOCQTYCWRXRVPWJWAWOCUMTULUNUOVBUPHWAVPCDEUQURUSUTVCXE
      XIXKXLVPLZXCXEWDYDXIVTXDWDYDVOWCYDAVPDABNZWBXLVQVPVQVPWACQYERSUOVBVAUTXIV
      TXMWALZXFWDVSYFAWADAFNZVRXMVQWAVQWAVPCQYGRSUOVDVEVLVFVGVHVLVIVJVTWDBFDWEV
      SWCADWEVRWBVQVPWAVQCUMTVKVMVN $.
  $}

  $( A group's range in terms of its domain.  (Contributed by NM, 6-Apr-2008.)
     (New usage is discouraged.) $)
  grporndm $p |- ( G e. GrpOp -> ran G = dom dom G ) $=
    ( cgr wcel crn cxp wfo cdm wceq eqid grpofo wf fof fdm dmeqd dmxpid syl6req
    syl ) ABCADZREZRAFZRAGZGZHARRIJTUBSGRTUASTSRAKUASHSRALSRAMQNROPQ $.

  $( The empty set is not a group.  (Contributed by NM, 25-Apr-2007.)
     (New usage is discouraged.) $)
  0ngrp $p |- -. (/) e. GrpOp $=
    ( c0 cgr wcel wne neirr crn rn0 eqcomi grpon0 mto ) ABCAADAEAAAFAGHIJ $.

  ${
    grprn.1 $e |- G e. GrpOp $.
    grprn.2 $e |- dom G = ( X X. X ) $.
    $( The range of a group operation.  Useful for satisfying group base set
       hypotheses of the form ` X = ran G ` .  (Contributed by NM,
       5-Nov-2006.)  (New usage is discouraged.) $)
    grporn $p |- X = ran G $=
      ( cxp wfn crn wceq wfun cdm cgr wcel wfo eqid grpofo fofun df-fn mpbir2an
      mp2b fofn wa fndmu xpid11 sylib mp2an ) ABBEZFZAAGZUHEZFZBUHHZUGAIZAJUFHA
      KLZUIUHAMZULCAUHUHNOZUIUHAPSDAUFQRUMUNUJCUOUIUHATSUGUJUAUFUIHUKUFUIAUBBUH
      UCUDUE $.
  $}

  ${
    $d g u x G $.  $d g u x X $.
    gidval.1 $e |- X = ran G $.
    $( The value of the identity element of a group.  (Contributed by Mario
       Carneiro, 15-Dec-2013.)  (New usage is discouraged.) $)
    gidval $p |- ( G e. V -> ( GId ` G ) =
             ( iota_ u e. X A. x e. X ( ( u G x ) = x /\ ( x G u ) = x ) ) ) $=
      ( vg wcel cvv cgi cfv cv co wceq wa wral crio crn oveq eqeq1d riotaeqbidv
      elex rneq syl6eqr anbi12d raleqbidv df-gid riotaex fvmpt syl ) CDHCIHCJKB
      LZALZCMZULNZULUKCMZULNZOZAEPZBEQZNCDUBGCUKULGLZMZULNZULUKUTMZULNZOZAUTRZP
      ZBVFQUSIJUTCNZVGURBVFEVHVFCREUTCUCFUDZVHVEUQAVFEVIVHVBUNVDUPVHVAUMULUKULU
      TCSTVHVCUOULULUKUTCSTUEUFUAABGUGURBEUHUIUJ $.
  $}

  ${
    $d g u x $.
    $( ` GId ` is a function.  (Contributed by FL, 5-Feb-2010.)  (Revised by
       Mario Carneiro, 15-Dec-2013.)  (New usage is discouraged.) $)
    fngid $p |- GId Fn _V $=
      ( vg vu vx cvv cv co wceq wa crn wral crio cgi riotaex df-gid fnmpti ) AD
      BEZCEZAEZFQGQPRFQGHCRIZJZBSKLTBSMCBANO $.
  $}

  ${
    $d u x y z A $.
    grpsn.1 $e |- A e. _V $.
    $( TODO - this is useless since we have ablosn - delete this
       if ever get an example of a non-Abelian group to go here. $)
    $( The group operation for the singleton group.  (Contributed by NM,
       4-Nov-2006.)  (New usage is discouraged.) $)
    grposn $p |- { <. <. A , A >. , A >. } e. GrpOp $=
      ( vx vy vz cop csn wf cv wcel wceq co elsn wa oveq2 oveq1 syl6eq sylan9eq
      eqtr4d sylbi snex cxp wf1o opex f1osn f1of ax-mp xpsn feq2i mpbir w3a cfv
      df-ov fvsn eqtri oveq1d sylan9eqr 3impa oveq2d 3impb syl3anb snid isgrpoi
      id a1i ) CDEAAAFZAFGZAAGZAUAVHVHUBZVHVGHVFGZVHVGHZVJVHVGUCVKVFAAAUDZBUEVJ
      VHVGUFUGVIVJVHVGAABBUHUIUJCIZVHJZVMAKZDIZVHJVPAKZEIZVHJVRAKZVMVPVGLZVRVGL
      ZVMVPVRVGLZVGLZKCAMZDAMEAMVOVQVSUKWAAWCVOVQVSWAAKVSVOVQNZWAVTAVGLZAVRAVTV
      GOWEWFAAVGLZAWEVTAAVGVOVQVTAVPVGLZAVMAVPVGPVQWHWGAVPAAVGOWGVFVGULAAAVGUMV
      FAVLBUNUOZQRUPWIQUQURVOVQVSWCAKVOVQVSNZWCAWBVGLZAVMAWBVGPWJWKWGAWJWBAAVGV
      QVSWBAVRVGLZAVPAVRVGPVSWLWGAVRAAVGOWIQRUSWIQRUTSVAABVBZVNVOAVMVGLZVMKWDVO
      WNAVMVOWNWGAVMAAVGOWIQZVOVDSTAVHJVNWMVEVNVOWNAKWDWOTVC $.
  $}

  ${
    $d x y A $.  $d g u x y G $.  $d u x y U $.  $d g u x y X $.
    grpoidval.1 $e |- X = ran G $.
    grpoidval.2 $e |- U = ( GId ` G ) $.
    $( Lemma for ~ grpoidcl and others.  (Contributed by NM, 5-Feb-2010.)
       (Proof shortened by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoidval $p |- ( G e. GrpOp -> U =
                     ( iota_ u e. X A. x e. X ( u G x ) = x ) ) $=
      ( vy cgr wcel cgi cv co wceq wral crio wa wrex simpl ralimi cfv gidval wi
      wreu w3a rgenw a1i grpoidinv reximi syl grpoideu 3jca reupick2 riotabidva
      wb sylan eqtr4d syl5eq ) DIJZCDKUAZBLZALZDMVBNZAEOZBEPZGUSUTVCVBVADMVBNZQ
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
      ( vy cgr wcel wa co wceq cv wrex grpoidinv2 simpld ) CHIADIJZBACKALZABCKA
      LZQRSJGMZACKBLATCKBLJGDNGABCDEFOPP $.

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
    grpinveu.1 $e |- X = ran G $.
    grpinveu.2 $e |- U = ( GId ` G ) $.
    $( The left inverse element of a group is unique.  Lemma 2.2.1(b) of
       [Herstein] p. 55.  (Contributed by NM, 27-Oct-2006.)
       (New usage is discouraged.) $)
    grpoinveu $p |- ( ( G e. GrpOp /\ A e. X ) -> E! y e. X ( y G A ) = U ) $=
      ( vz cgr wcel wa cv co wceq wi wral wrex wreu grpoidinv2 simpl reximi syl
      adantl eqtr3 grporcan syl5ib 3exp2 com24 imp41 an32s exp3a ancld reximdva
      w3a ralrimdva mpd oveq1 eqeq1d reu8 sylibr ) DIJZBEJZKZALZBDMZCNZHLZBDMZC
      NZVDVGNZOZHEPZKZAEQZVFAERVCVFAEQZVNVCCBDMBNBCDMBNKZVFBVDDMCNZKZAEQZKVOABC
      DEFGSVSVOVPVRVFAEVFVQTUAUCUBVCVFVMAEVCVDEJZKZVFVLWAVFVKHEWAVGEJZKVFVIVJVC
      WBVTVFVIKZVJOZVAVBWBVTWDVAVTWBVBWDVAVTWBVBWDWCVEVHNVAVTWBVBUNKVJVEVHCUDVD
      VGBDEFUEUFUGUHUIUJUKUOULUMUPVFVIAHEVJVEVHCVDVGBDUQURUSUT $.

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
    $d n x y A $.  $d y B $.  $d y C $.  $d f g n x y G $.  $d f g n x y X $.
    $d f g n x U $.
    grpinvfval.1 $e |- X = ran G $.
    grpinvfval.2 $e |- U = ( GId ` G ) $.
    grpinvfval.3 $e |- N = ( inv ` G ) $.
    $( The inverse function of a group.  (Contributed by NM, 26-Oct-2006.)
       (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoinvfval $p |- ( G e. GrpOp -> N = ( x e. X |->
                     ( iota_ y e. X ( y G x ) = U ) ) ) $=
      ( vg cgr wcel cgn cfv cv co wceq crio cvv cgi cmpt crn rnexg syl5eqel syl
      mptexg rneq syl6eqr oveq fveq2 eqeq12d riotaeqbidv mpteq12dv fvmptg mpdan
      df-ginv syl5eq ) DKLZEDMNZAFBOZAOZDPZCQZBFRZUAZIURVESLZUSVEQURFSLVFURFDUB
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

    $( The right inverse of a group element.  (Contributed by NM,
       27-Oct-2006.)  (New usage is discouraged.) $)
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
    grpinvid.1 $e |- U = ( GId ` G ) $.
    grpinvid.2 $e |- N = ( inv ` G ) $.
    $( The inverse of the identity element of a group.  (Contributed by NM,
       4-Dec-2006.)  (New usage is discouraged.) $)
    grpoinvid $p |- ( G e. GrpOp -> ( N ` U ) = U ) $=
      ( cgr wcel cfv wceq co eqid grpoidcl grpolid mpdan wb grpoinvid1 mpd3an23
      crn mpbird ) BFGZACHAIZAABJAIZTABRZGZUBABUCUCKZDLZAABUCUEDMNTUDUDUAUBOUFU
      FAAABCUCUEDEPQS $.
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
    $d a b c .+ $.  $d a b c K $.
    grp2grp.a $e |- ( Base ` K ) = ran .+ $.
    grp2grp.p $e |- ( +g ` K ) = .+ $.
    grp2grp.g $e |- .+ e. GrpOp $.
    $( Convert a group operation to a group structure.  (Contributed by NM,
       25-Oct-2012.)  (Revised by Mario Carneiro, 6-Jan-2015.)
       (New usage is discouraged.) $)
    grpo2grp $p |- K e. Grp $=
      ( va vb vc crn cv cgn cfv cgi cbs eqcomi wcel co eqid wceq mpan cgr ax-mp
      cplusg grpocl mp3an1 grpoass grpoidcl grpolid grpoinvcl grpolinv isgrpi
      w3a ) FGHAIZABFJZAKLZLZAMLZBNLUMCOBUCLADOAUAPZUNUMPZGJZUMPZUNUTAQZUMPEUNU
      TAUMUMRZUDUEURUSVAHJZUMPULVBVDAQUNUTVDAQAQSEUNUTVDAUMVCUFTURUQUMPEUQAUMVC
      UQRZUGUBURUSUQUNAQUNSEUNUQAUMVCVEUHTURUSUPUMPEUNAUOUMVCUORZUITURUSUPUNAQU
      QSEUNUQAUOUMVCVEVFUJTUK $.
  $}

  $( (Commented out since it's not in use and not worth repairing, seeing as
     GrpOp is being deprecated. -MC 6-Jan-2015)
  @{
    @d a b c e m x y A @.  @d a b c e m x y G @.  @d a b c e m x y P @.
    @d a e m K @.
    grp2grpo.a @e |- A = ( Base ` K ) @.
    grp2grpo.p @e |- .+ = ( +g ` K ) @.
    grp2grpo.g @e |- G = ( x e. A , y e. A |-> ( x .+ y ) ) @.
    @( Convert a group structure to a group operation and vice-versa. @)
    grp2grpo @p |- ( K e. Grp <-> G e. GrpOp ) @=
      ( va vb vc ve vm wcel co wral wceq wa wrex cgrp cgr crn cxp wf wb cv ovex
      wfn fnmpt2i a1i isgrp2 simplbi simpl ralimi rr19.3v sylib syl oveq1 oveq2
      ovmpt2 eleq1d ralbidva ralbiia sylibr ffnov sylanbrc wfo grplidinv eqeq1d
      ancoms rexbidva adantl anbi12d rexbiia r19.12 eqcom eqeq2d rspcev syl5bi
      adantrd reximdv ralimia 3syl foov forn eqcomd xpeq12 anidms feq23 mpancom
      ex mpbid fndmu sylancr xpid11 biimpi adantr cbvral2v ad2antlr oveq1d rsp2
      ffn sylanbr sylan simplrl rspc2v impcom anassrs adantlrl syl2anc adantll
      imp eqtrd oveq2d eqeq12d 2ralbidva sylbi biimpa jca biimpri sylbir impbii
      biimpar rr19.28v ralbii r19.26-2 bitri 3bitr4i anbi12i eleq2 anbi1d rexeq
      raleqbi1dv anbi2d cvv cbs eqeltri isgrpo2 ibi rexeqbi1dv syl5bbr ibar w3a
      bitrd syl5bb cmpt2 cfv fvex mpt2ex eqid ax-mp 3anass bitr2i syl6bb biimpd
      syl5rbb 3impib ) FUAOZEUBOZUUSUUTUUSEUCZUVAUDZUVAEUEZUUSUUTUFUUSCCUDZCEUE
      ZUVCUUSEUVDUIZJUGZKUGZEPZCOZKCQZJCQZUVEUVFUUSABCCAUGZBUGZDPZEIUVMUVNDUHUJ
      ZUKUUSUVGUVHDPZCOZKCQZJCQZUVLUUSUVRUVQLUGZDPZUVGUVHUWADPZDPZRZSZLCQZKCQZJ
      CQZUVTUUSUWIMUGZUVGDPZUVGRZNUGZUVGDPZUWJRZNCTZSZJCQZMCTZCDMNFJKLGHULZUMUW
      HUVSJCUWHUVRLCQZKCQUVSUWGUXAKCUWFUVRLCUVRUWEUNUOUOUVRKLCUPUQUOURUVKUVSJCU
      VGCOZUVJUVRKCUXBUVHCOZSZUVIUVQCABUVGUVHCCUVOUVQEUVGUVNDPZUVMUVGUVNDUSZUVN
      UVHUVGDUTIUVGUVHDUHVAZVBZVCVDZVEJKCCCEVFVGZUUSCUVARZUVEUVCUFZUUSUVACUUSUV
      DCEVHZUVACRUUSUVEUVGUWJUVHEPZRZKCTZMCTZJCQZUXMUXJUUSUWJUVGEPZUVGRZUWMUVGE
      PZUWJRZNCTZSZJCQZMCTZUYDMCTZJCQUXRUUSUWSUYFJNMCDFGHVIUYEUWRMCUWJCOZUYDUWQ
      JCUYHUXBSZUXTUWLUYCUWPUYIUXSUWKUVGABUWJUVGCCUVOUWKEUWJUVNDPUVMUWJUVNDUSUV
      NUVGUWJDUTIUWJUVGDUHVAVJUXBUYCUWPUFUYHUXBUYBUWONCUXBUWMCOZSUYAUWNUWJUYJUX
      BUYAUWNRABUWMUVGCCUVOUWNEUWMUVNDPUVMUWMUVNDUSUVNUVGUWMDUTIUWMUVGDUHVAVKVJ
      VLVMVNVCVOZVEUYDMJCCVPUYGUXQJCUXBUYDUXPMCUXBUXTUXPUYCUXTUVGUXSRZUXBUXPUXS
      UVGVQUXBUYLUXPUXOUYLKUVGCUVHUVGRUXNUXSUVGUVHUVGUWJEUTVRVSWLVTWAWBWCWDMKJC
      CCEWEVGUVDCEWFURWGUVDUVBRZUXKUXLUXKUYMCUVACUVAWHWIUVDCUVBUVAEWJWKURWMUVCU
      USUVCUVIUVAOZUVIUWAEPZUVGUVHUWAEPZEPZRZSZLUVAQZKUVAQZJUVAQZUXTUYBNUVATZSZ
      JUVAQZMUVATZSZSZUUTUUSUWIUWSSZUVCVUHUWTUVCVUIVUGVUHUVCUXKVUIVUGUFUVCUYMUX
      KUVCUVFEUVBUIUYMUVPUVBUVAEXCUVDUVBEWNWOCUVAWPUQVUIUVJUYRSZLCQZKCQZJCQZUYF
      SUXKVUGVUMUWIUYFUWSUVLUYRLCQZKCQJCQZSZUVTUWELCQZKCQJCQZSZVUMUWIVUPVUSVUPU
      VTVURUVLUVTVUOUVLUVTUXIWQWRUVLVUOVURUVLUVMUVNEPZCOZBCQACQZVUOVURUFZUVJVVA
      UVMUVHEPZCOJKABCCUVGUVMRUVIVVDCUVGUVMUVHEUSVBUVHUVNRVVDVUTCUVHUVNUVMEUTVB
      WSZVVBVUNVUQJKCCVVBUXDSZUYRUWELCVVFUWACOZSZUYOUWBUYQUWDVVHUYOUVQUWAEPZUWB
      VVHUVIUVQUWAEUXDUVIUVQRVVBVVGUXGWTXAVVFUVRVVGVVIUWBRVVBUVLUXDUVRVVEUVLUXD
      SUVJUVRUVLUXDUVJUVJJKCCXBXMUXDUVJUVRUFUVLUXHVMWMXDABUVQUWACCUVOUWBEUVQUVN
      DPUVMUVQUVNDUSUVNUWAUVQDUTIUVQUWADUHVAXEXNVVHUYQUVGUYPDPZUWDVVHUXBUYPCOZU
      YQVVJRVVBUXBUXCVVGXFVVBUXCVVGVVKUXBVVBUXCVVGVVKUXCVVGSVVBVVKVVAVVKUVHUVNE
      PZCOABUVHUWACCUVMUVHRVUTVVLCUVMUVHUVNEUSVBUVNUWARVVLUYPCUVNUWAUVHEUTVBXGX
      HXIXJABUVGUYPCCUVOVVJEUXEUXFUVNUYPUVGDUTIUVGUYPDUHVAXKVVHUYPUWCUVGDUXDVVG
      UYPUWCRZVVBUXCVVGVVMUXBABUVHUWACCUVOUWCEUVHUVNDPUVMUVHUVNDUSUVNUWAUVHDUTI
      UVHUWADUHVAXLXLXOXNXPVCXQXRZXSXTVUSUVLVUOUVTUVLVURUVLUVTUXIYAWRUVTVUOVURU
      VTUVLVVCUXIVVNYBYDXTYCVUMUVJVUNSKCQZJCQVUPVULVVOJCUVJUYRKLCYEYFUVJVUNJKCC
      YGYHUWIUVRVUQSKCQZJCQVUSUWHVVPJCUVRUWEKLCYEYFUVRVUQJKCCYGYHYIUYKYJUXKVUMV
      UBUYFVUFVULVUAJCUVAVUKUYTKCUVAVUJUYSLCUVAUXKUVJUYNUYRCUVAUVIYKYLYNYNYNUYE
      VUEMCUVAUYDVUDJCUVAUXKUYCVUCUXTUYBNCUVAYMYOYNUUAVNUUBURZUVCVUGUUCUUEUUFUU
      TUVCVUBVUFUUDZVUHEYPOUUTVVRUFEABCCUVOUUGYPIABCCUVOCFYQUUHYPGFYQUUIYRZVVSU
      UJYRJKLMYPNEUVAUVAUUKZYSUULUVCVUBVUFUUMUUNUUOURYTUUTVVRUUSUUTVVRJKLMUBNEU
      VAVVTYSYTUVCVUBVUFUUSUVCVUGUUSUUSVUIUVCVUGUWTVVQUUQUUPUURURYC @.
      @( [29-Oct-2012] @)
  @}
  $)

  ${
    $d u v w x y z G $.  $d u v w x y z X $.  $d u v w x y z ph $.
    isgrp2d.1 $e |- ( ph -> X e. V ) $.
    isgrp2d.2 $e |- ( ph -> X =/= (/) ) $.
    isgrp2d.3 $e |- ( ph -> G : ( X X. X ) --> X ) $.
    isgrp2d.4 $e |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) ) ->
                      ( ( x G y ) G z ) = ( x G ( y G z ) ) ) $.
    isgrp2d.5 $e |- ( ( ph /\ ( x e. X /\ y e. X ) ) ->
                      E. z e. X ( z G x ) = y ) $.
    isgrp2d.6 $e |- ( ( ph /\ ( x e. X /\ y e. X ) ) ->
                     E. z e. X ( x G z ) = y ) $.
    $( An alternate way to show a group operation.  Exercise 1 of [Herstein]
       p. 57.  (Contributed by Mario Carneiro, 12-May-2014.)
       (New usage is discouraged.) $)
    isgrp2d $p |- ( ph -> G e. GrpOp ) $=
      ( vu wcel co wceq wral wrex wa vw vv cgr crn cxp wf cv c0 adantr anass1rs
      wfo wne eqcom rexbii sylib ralrimiva r19.2z syl2anc foov sylanbrc xpeq12d
      forn syl feq23d mpbird ralrimivvva raleqdv raleqbidv wex simpr ralrimivva
      n0 jca weq oveq2 eqeq1d rexbidv eqeq2 oveq1 cbvrexv syl6bb rspc2v ralbidv
      sylc rspccva sylan ad2ant2r ad3antrrr simplr simpllr simprr oveq1d oveq2d
      wi eqeq12d rspc3v syl3anc simprl eqtr3d anassrs syl5ibcom adantrl adantlr
      rexlimdva rspcv adantllr adantrr expr ralrimdva reximdva exlimddv rexeqdv
      mpd id anbi2d rexeqbidv cvv w3a wb xpexg fex eqid isgrpo mpbir3and ) AEUC
      OZEUDZYFUEZYFEUFZBUGZCUGZEPZDUGZEPZYIYJYLEPZEPZQZDYFRZCYFRZBYFRZNUGZYIEPZ
      YIQZYJYIEPZYTQZCYFSZTZBYFRZNYFSZAYHGGUEZGEUFZJAYGYFUUIGEAYFGYFGAUUIGEUKZY
      FGQAUUJYJYIYLEPZQZDGSZBGSZCGRUUKJAUUOCGAYJGOZTZGUHULZUUNBGRUUOAUURUUPIUIU
      UQUUNBGUUQYIGOZTUULYJQZDGSZUUNAUUSUUPUVAMUJUUTUUMDGUULYJUMUNUOUPUUNBGUQUR
      UPBDCGGGEUSUTUUIGEVBVCZUVBVAUVBVDVEAYSYPDGRZCGRZBGRZAYPBCDGGGKVFZAYRUVDBY
      FGUVBAYQUVCCYFGUVBAYPDYFGUVBVGVHVHVEAUUHUUBUUDCGSZTZBGRZNGSZAUAUGZGOZUVJU
      AAUURUVLUAVIIUAGVLUOAUVLTZYTUVKEPZUVKQZNGSZUVJUVMUVLUVLTYLYIEPZYJQZDGSZCG
      RZBGRZUVPUVMUVLUVLAUVLVJZUWBVMAUWAUVLAUVSBCGGLVKUIUVSUVPYLUVKEPZYJQZDGSZB
      CUVKUVKGGBUAVNZUVRUWDDGUWFUVQUWCYJYIUVKYLEVOVPVQCUAVNZUWEUWCUVKQZDGSUVPUW
      GUWDUWHDGYJUVKUWCVRVQUWHUVODNGDNVNUWCUVNUVKYLYTUVKEVSVPVTWAWBWDUVMUVOUVIN
      GUVMYTGOZTZUVOUVHBGUWJUUSUVOUVHUWJUUSUVOTTZUUBUVGUWKUVKUBUGZEPZYIQZUBGSZU
      UBUVMUUSUWOUWIUVOUVMUVKYLEPZYJQZDGSZCGRZUUSUWOAUVACGRZBGRUVLUWSAUVABCGGMV
      KUWTUWSBUVKGUWFUVAUWRCGUWFUUTUWQDGUWFUULUWPYJYIUVKYLEVSVPVQWCWEWFUWRUWOCY
      IGCBVNZUWRUWPYIQZDGSUWOUXAUWQUXBDGYJYIUWPVRVQUXBUWNDUBGDUBVNZUWPUWMYIYLUW
      LUVKEVOZVPVTWAWEWFWGUWJUVOUWOUUBWNUUSUWJUVOTZUWNUUBUBGUXEUWLGOZTYTUWMEPZU
      WMQZUWNUUBUWJUVOUXFUXHUWJUVOUXFTZTZUVNUWLEPZUXGUWMUXJUVEUXKUXGQZAUVEUVLUW
      IUXIUVFWHUXJUWIUVLUXFUVEUXLWNUVMUWIUXIWIAUVLUWIUXIWJUWJUVOUXFWKYPUXLYTYJE
      PZYLEPZYTYNEPZQUVNYLEPZYTUWPEPZQBCDYTUVKUWLGGGBNVNZYMUXNYOUXOUXRYKUXMYLEY
      IYTYJEVSWLYIYTYNEVSWOUWGUXNUXPUXOUXQUWGUXMUVNYLEYJUVKYTEVOWLUWGYNUWPYTEYJ
      UVKYLEVSWMWOUXCUXPUXKUXQUXGYLUWLUVNEVOUXCUWPUWMYTEUXDWMWOWPWQXMUXJUVNUVKU
      WLEUWJUVOUXFWRWLWSWTUWNUXGUUAUWMYIUWMYIYTEVOUWNXNWOXAXDXBXMUWJUUSUVGUVOAU
      WIUUSUVGUVLAUWITUUSTZUVQYTQZDGSZUVGUXSUWIUVTUYAAUWIUUSWIAUUSUVTUWIAUUSTUV
      SCGAUUSUUPUVSLWTUPXCUVSUYACYTGCNVNUVRUXTDGYJYTUVQVRVQXEWDUXTUUDDCGDCVNUVQ
      UUCYTYLYJYIEVSVPVTUOXFXGVMXHXIXJXMXKAUUGUVINYFGUVBAUUFUVHBYFGUVBAUUEUVGUU
      BAUUDCYFGUVBXLXOVHXPVEAEXQOZYEYHYSUUHXRXSAUUJUUIXQOZUYBJAGFOZUYDUYCHHGGFF
      XTURUUIGXQEYAURBCDNXQEYFYFYBYCVCYD $.
  $}

  ${
    $d x y z G $.  $d x y z X $.
    isgrp2i.1 $e |- X e. _V $.
    isgrp2i.2 $e |- X =/= (/) $.
    isgrp2i.3 $e |- G : ( X X. X ) --> X $.
    isgrp2i.4 $e |- ( ( x e. X /\ y e. X /\ z e. X ) ->
                    ( ( x G y ) G z ) = ( x G ( y G z ) ) ) $.
    isgrp2i.5 $e |- ( ( x e. X /\ y e. X ) -> E. z e. X ( z G x ) = y ) $.
    isgrp2i.6 $e |- ( ( x e. X /\ y e. X ) -> E. z e. X ( x G z ) = y ) $.
    $( An alternate way to show a group operation.  Exercise 1 of [Herstein]
       p. 57.  (Contributed by NM, 5-Dec-2006.)  (Revised by Mario Carneiro,
       12-May-2014.)  (New usage is discouraged.) $)
    isgrp2i $p |- G e. GrpOp $=
      ( wcel wtru cvv a1i cv co wceq adantl wrex cgr c0 wne cxp wf isgrp2d trud
      w3a wa ) DUALMABCDNEENLMFOEUBUCMGOEEUDEDUEMHOAPZELZBPZELZCPZELUHUJULDQUND
      QUJULUNDQDQRMISUKUMUIZUNUJDQULRCETMJSUOUJUNDQULRCETMKSUFUG $.
  $}

  ${
    $d x y z G $.  $d x y N $.  $d x y z X $.
    grpasscan1.1 $e |- X = ran G $.
    grpasscan1.2 $e |- N = ( inv ` G ) $.
    $( An associative cancellation law for groups.  (Contributed by Paul
       Chapman, 25-Feb-2008.)  (New usage is discouraged.) $)
    grpoasscan1 $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
                          ( A G ( ( N ` A ) G B ) ) = B ) $=
      ( cgr wcel w3a cfv co cgi wceq eqid grporinv 3adant3 oveq1d wa wi grpoass
      grpoinvcl 3exp2 imp mpd 3impia grpolid 3adant2 3eqtr3d ) CHIZAEIZBEIZJZAA
      DKZCLZBCLZCMKZBCLZAUNBCLCLZBUMUOUQBCUJUKUOUQNULAUQCDEFUQOZGPQRUJUKULUPUSN
      ZUJUKSUNEIZULVATZACDEFGUBUJUKVBVCTUJUKVBULVAAUNBCEFUAUCUDUEUFUJULURBNUKBU
      QCEFUTUGUHUI $.

    $( An associative cancellation law for groups.  (Contributed by Paul
       Chapman, 17-Apr-2009.)  (New usage is discouraged.) $)
    grpoasscan2 $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
                       ( ( A G ( N ` B ) ) G B ) = A ) $=
      ( cgr wcel w3a cfv cgi wceq simp1 simp2 grpoinvcl 3adant2 simp3 grpoass
      co syl13anc eqid grpolinv oveq2d grporid 3adant3 3eqtrd ) CHIZAEIZBEIZJZA
      BDKZCTBCTZAULBCTZCTZACLKZCTZAUKUHUIULEIZUJUMUOMUHUIUJNUHUIUJOUHUJURUIBCDE
      FGPQUHUIUJRAULBCEFSUAUKUNUPACUHUJUNUPMUIBUPCDEFUPUBZGUCQUDUHUIUQAMUJAUPCE
      FUSUEUFUG $.

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
      cab fnrnfv syl eqcomd eqeq2d rspcev syl2anc ex simpr adantr eqeltrd exp31
      rexlimdv impbid abbi2dv eqtr4d eqeqan12d anandis syl5ib ralrimivva dff1o6
      wb syl3anbrc ) AHIZBCJZBKZCLFMZBNZGMZBNZLZVSWALZUAZGCOFCOCCBUBVPVQFCWAVSA
      UCAUDNZLZGCUEZUFZCJFCWHWIWGGCUGWIPUHVPCBWIFGWFABCDWFPEUIUJUKZVPVRWAVTLZFC
      ULZGUMZCVPVQVRWMLWJFGCBUNUOVPWLGCVPWACIZWLVPWNWLVPWNTZWBCIWAWBBNZLZWLWAAB
      CDEQWOWPWAWAABCDERZUPWKWQFWBCVSWBLVTWPWAVSWBBSUQURUSUTVPWKWNFCVPVSCIZWKWN
      VPWSTZWKTWAVTCWTWKVAWTVTCIWKVSABCDEQVBVCVDVEVFVGVHVPWEFGCCWCVTBNZWPLZVPWS
      WNTTWDVTWBBSVPWSWNXBWDVNWTWOXAVSWPWAVSABCDERWRVIVJVKVLFGCCBVMVO $.

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
    $d x y z A $.  $d x y z B $.  $d f g x y z G $.  $d f g x y z N $.
    $d f g x y z X $.
    grpdiv.1 $e |- X = ran G $.
    grpdiv.2 $e |- N = ( inv ` G ) $.
    grpdiv.3 $e |- D = ( /g ` G ) $.
    $( Group division (or subtraction) operation.  (Contributed by NM,
       15-Feb-2008.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpodivfval $p |- ( G e. GrpOp -> D = ( x e. X , y e. X |->
                       ( x G ( N ` y ) ) ) ) $=
      ( vg cgr wcel cgs cfv cv co cmpt2 cvv wceq cgn crn rnexg syl5eqel syl2anc
      mpt2exga rneq syl6eqr id eqidd fveq1d oveq123d mpt2eq123dv df-gdiv fvmptg
      fveq2 mpdan syl5eq ) DKLZCDMNZABFFAOZBOZENZDPZQZIURVDRLZUSVDSURFRLZVFVEUR
      FDUAZRGDKUBUCZVHABFFVCRRUEUDJDABJOZUAZVJUTVAVITNZNZVIPZQVDKRMVIDSZABVJVJV
      MFFVCVNVJVGFVIDUFGUGZVOVNUTUTVLVBVIDVNUHVNUTUIVNVAVKEVNVKDTNEVIDTUOHUGUJU
      KULABJUMUNUPUQ $.

    $( Group division (or subtraction) operation value.  (Contributed by NM,
       15-Feb-2008.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpodivval $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
                   ( A D B ) = ( A G ( N ` B ) ) ) $=
      ( vx vy cgr wcel co cfv wceq wa cv cmpt2 grpodivfval oveqd oveq1 sylan9eq
      fveq2 oveq2d eqid ovex ovmpt2 3impb ) DLMZAFMZBFMZABCNZABEOZDNZPUJUKULQUM
      ABJKFFJRZKRZEOZDNZSZNUOUJCUTABJKCDEFGHITUAJKABFFUSUOUTAURDNUPAURDUBUQBPUR
      UNADUQBEUDUEUTUFAUNDUGUHUCUI $.

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
    $d x y z G $.  $d x y z X $.
    grpdivf.1 $e |- X = ran G $.
    grpdivf.3 $e |- D = ( /g ` G ) $.
    $( Mapping for group division.  (Contributed by NM, 10-Apr-2008.)  (Revised
       by Mario Carneiro, 15-Dec-2013.)  (New usage is discouraged.) $)
    grpodivf $p |- ( G e. GrpOp -> D : ( X X. X ) --> X ) $=
      ( vx vy cgr wcel cxp wf cv cgn cfv co cmpt2 wral eqid grpoinvcl 3adant2
      grpocl syld3an3 3expib ralrimivv fmpt2 sylib grpodivfval feq1d mpbird ) B
      HIZCCJZCAKUKCFGCCFLZGLZBMNZNZBOZPZKZUJUPCIZGCQFCQURUJUSFGCCUJULCIZUMCIZUS
      UJUTVAUOCIZUSUJVAVBUTUMBUNCDUNRZSTULUOBCDUAUBUCUDFGCCUPCUQUQRUEUFUJUKCAUQ
      FGABUNCDVCEUGUHUI $.

    $( Closure of group division (or subtraction) operation.  (Contributed by
       NM, 15-Feb-2008.)  (New usage is discouraged.) $)
    grpodivcl $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) -> ( A D B ) e. X ) $=
      ( cgr wcel cxp wf co grpodivf fovrn syl3an1 ) DHIEEJECKAEIBEIABCLEICDEFGM
      ABEEECNO $.

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

    $( Cancellation law for group division.  ( ~ pncan analog.)  (Contributed
       by NM, 15-Feb-2008.)  (New usage is discouraged.) $)
    grpopncan $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
        ( ( A G B ) D B ) = A ) $=
      ( cgr wcel w3a co cgi cfv wceq simp1 simp2 simp3 grpomuldivass syl13anc
      wa eqid grpodivid oveq2d 3adant2 grporid 3adant3 3eqtrd ) DHIZAEIZBEIZJZA
      BDKBCKZABBCKZDKZADLMZDKZAUKUHUIUJUJULUNNUHUIUJOUHUIUJPUHUIUJQZUQABBCDEFGR
      SUHUJUNUPNUIUHUJTUMUOADBCUODEFGUOUAZUBUCUDUHUIUPANUJAUODEFURUEUFUG $.

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

    $( Cancellation law for mixed addition and group division.  ( ~ pnpcan2
       analog.)  (Contributed by NM, 15-Feb-2008.)
       (New usage is discouraged.) $)
    grpopnpcan2 $p |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
         ( ( A G C ) D ( B G C ) ) = ( A D B ) ) $=
      ( wcel w3a co cfv wceq grpocl 3adant3r1 grpodivval syl3anc oveq2d 3adant2
      eqid cgr wa cgn simpl 3adant3r2 grpoinvop cgi grporinv oveq1d simp1 simp3
      grpoinvcl 3adant3 grpoass syl13anc grpolid syldan simpr1 simpr3 3ad2antr3
      3eqtr3d 3ad2antr2 3adant3r3 3eqtr4d 3eqtrd ) EUAIZAFIZBFIZCFIZJZUBZACEKZB
      CEKZDKZVLVMEUCLZLZEKZVLCVOLZBVOLZEKZEKZABDKZVKVFVLFIZVMFIZVNVQMVFVJUDZVFV
      GVIWCVHACEFGNUEVFVHVIWDVGBCEFGNOVLVMDEVOFGVOTZHPQVKVPVTVLEVFVHVIVPVTMVGBC
      EVOFGWFUFORVKACVTEKZEKZAVSEKZWAWBVKWGVSAEVFVHVIWGVSMVGVFVHVIJZCVREKZVSEKZ
      EUGLZVSEKZWGVSWJWKWMVSEVFVIWKWMMVHCWMEVOFGWMTZWFUHSUIWJVFVIVRFIZVSFIZWLWG
      MVFVHVIUJVFVHVIUKVFVIWPVHCEVOFGWFULZSVFVHWQVIBEVOFGWFULZUMCVRVSEFGUNUOVFV
      HWNVSMZVIVFVHWQWTWSVSWMEFGWOUPUQUMVAORVKVFVGVIVTFIZWAWHMWEVFVGVHVIURVFVGV
      HVIUSVKVFWPWQXAWEVFVGVIWPVHWRUTVFVGVHWQVIWSVBVRVSEFGNQACVTEFGUNUOVFVGVHWB
      WIMVIABDEVOFGWFHPVCVDVE $.

    $( Cancellation law for group division.  ( ~ nnncan2 analog.)  (Contributed
       by NM, 15-Feb-2008.)  (New usage is discouraged.) $)
    grponnncan2 $p |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
         ( ( A D C ) D ( B D C ) ) = ( A D B ) ) $=
      ( cgr wcel w3a wa co cgn cfv wceq eqid grpodivval 3adant3r2 idd 3adant3r1
      oveq12d grpoinvcl ex 3anim123d imp grpopnpcan2 syldan eqtrd ) EIJZAFJZBFJ
      ZCFJZKZLZACDMZBCDMZDMACENOZOZEMZBUSEMZDMZABDMZUOUPUTUQVADUJUKUMUPUTPULACD
      EURFGURQZHRSUJULUMUQVAPUKBCDEURFGVDHRUAUBUJUNUKULUSFJZKZVBVCPUJUNVFUJUKUK
      ULULUMVEUJUKTUJULTUJUMVECEURFGVDUCUDUEUFABUSDEFGHUGUHUI $.

    $( Cancellation law for group division.  ( ~ npncan analog.)  (Contributed
       by NM, 24-Feb-2008.)  (New usage is discouraged.) $)
    grponpncan $p |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
             ( ( A D B ) G ( B D C ) ) = ( A D C ) ) $=
      ( cgr wcel w3a wa co wceq grpodivcl 3adant3r3 simpr2 simpr3 grpomuldivass
      3jca syldan grponpcan 3expb oveq1d 3adantr3 eqtr3d ) EIJZAFJZBFJZCFJZKZLZ
      ABDMZBEMZCDMZUMBCDMEMZACDMZUGUKUMFJZUIUJKUOUPNULURUIUJUGUHUIURUJABDEFGHOP
      UGUHUIUJQUGUHUIUJRTUMBCDEFGHSUAUGUHUIUOUQNUJUGUHUILLUNACDUGUHUIUNANABDEFG
      HUBUCUDUEUF $.

    $( Relationship between group division and group multiplication.
       (Contributed by Mario Carneiro, 11-Jul-2014.)
       (New usage is discouraged.) $)
    grpodiveq $p |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                   ( ( A D B ) = C <-> ( C G B ) = A ) ) $=
      ( co wceq cgr wcel w3a wa eqcom wb simpl simpr3 grpodivcl 3adant3r3
      simpr2 grporcan syl13anc grponpcan eqeq2d bitr3d syl5bb ) ABDIZCJCUHJZEKL
      ZAFLZBFLZCFLZMZNZCBEIZAJZUHCOUOUPUHBEIZJZUIUQUOUJUMUHFLZULUSUIPUJUNQUJUKU
      LUMRUJUKULUTUMABDEFGHSTUJUKULUMUACUHBEFGUBUCUOURAUPUJUKULURAJUMABDEFGHUDT
      UEUFUG $.
  $}

  ${
    $d G f g x y z $.  $d N f g z $.  $d U f g x y z $.  $d X f g x y z $.
    $d A x y z $.  $d G x y z $.  $d K x y z $.  $d N x y z $.
    gxfval.1 $e |- X = ran G $.
    gxfval.2 $e |- U = ( GId ` G ) $.
    gxfval.3 $e |- N = ( inv ` G ) $.
    gxfval.4 $e |- P = ( ^g ` G ) $.
    $( The value of the group power operator function.  (Contributed by Paul
       Chapman, 17-Apr-2009.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    gxfval $p |- ( G e. GrpOp -> P = ( x e. X , y e. ZZ |->
        if ( y = 0 , U , if ( 0 < y , ( seq 1 ( G , ( NN X. { x } ) ) ` y ) ,
          ( N ` ( seq 1 ( G , ( NN X. { x } ) ) ` -u y ) ) ) ) ) ) $=
      ( vg cgr wcel cfv cz cv wceq cif cvv cgx cc0 clt wbr cn csn cxp cseq cneg
      c1 cmpt2 crn rnexg syl5eqel zex mpt2exga sylancl cgi cgn rneq eqidd fveq2
      syl6eqr seqeq2 fveq1d fveq12d ifeq12d mpt2eq123dv df-gx fvmptg syl5eq
      mpdan ) EMNZCEUAOZABGPBQZUBRZDUBVOUCUDZVOEUEAQUFUGZUJUHZOZVOUIZVSOZFOZSZS
      ZUKZKVMWFTNZVNWFRVMGTNPTNWGVMGEULZTHEMUMUNUOABGPWETTUPUQLEABLQZULZPVPWIUR
      OZVQVOWIVRUJUHZOZWAWLOZWIUSOZOZSZSZUKWFMTUAWIERZABWJPWRGPWEWSWJWHGWIEUTHV
      CWSPVAWSVPWKDWQWDWSWKEURODWIEURVBIVCWSVQWMVTWPWCWSVOWLVSWIEVRUJVDZVEWSWNW
      BWOFWSWOEUSOFWIEUSVBJVCWSWAWLVSWTVEVFVGVGVHABLVIVJVLVK $.

    $( The result of the group power operator.  (Contributed by Paul Chapman,
       17-Apr-2009.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    gxval $p |- ( ( G e. GrpOp /\ A e. X /\ K e. ZZ ) -> ( A P K ) =
      if ( K = 0 , U , if ( 0 < K , ( seq 1 ( G , ( NN X. { A } ) ) ` K ) ,
           ( N ` ( seq 1 ( G , ( NN X. { A } ) ) ` -u K ) ) ) ) ) $=
      ( vx vy wcel cz cc0 wceq clt cfv cif cgr co wbr cn csn c1 cseq cneg wa cv
      cmpt2 gxfval oveqd sneq xpeq2d seqeq3d fveq1d fveq2d ifeq12d ifeq2d eqeq1
      cxp breq2 fveq2 negeq ifbieq12d ifbieq2d eqid cgi cvv fvex eqeltri ovmpt2
      ifex sylan9eq 3impb ) DUANZAGNZEONZAEBUBZEPQZCPERUCZEDUDAUEZVBZUFUGZSZEUH
      ZWESZFSZTZTZQVQVRVSUIVTAELMGOMUJZPQZCPWLRUCZWLDUDLUJZUEZVBZUFUGZSZWLUHZWR
      SZFSZTZTZUKZUBWKVQBXEAELMBCDFGHIJKULUMLMAEGOXDWKXEWMCWNWLWESZWTWESZFSZTZT
      WOAQZWMXCXICXJWNWSXFXBXHXJWLWRWEXJWQWDDUFXJWPWCUDWOAUNUOUPZUQXJXAXGFXJWTW
      RWEXKUQURUSUTWLEQZWMWAXIWJCWLEPVAXLWNWBXFXHWFWIWLEPRVCWLEWEVDXLXGWHFXLWTW
      GWEWLEVEURURVFVGXEVHWACWJCDVISVJIDVIVKVLWBWFWIEWEVKWHFVKVNVNVMVOVP $.
  $}

  ${
    gxpval.1 $e |- X = ran G $.
    gxpval.2 $e |- P = ( ^g ` G ) $.
    $( The result of the group power operator when the exponent is positive.
       (Contributed by Paul Chapman, 17-Apr-2009.)  (Revised by Mario Carneiro,
       15-Dec-2013.)  (New usage is discouraged.) $)
    gxpval $p |- ( ( G e. GrpOp /\ A e. X /\ K e. NN ) ->
                   ( A P K ) = ( seq 1 ( G , ( NN X. { A } ) ) ` K ) ) $=
      ( cgr wcel cn w3a co cc0 wceq cgi cfv cif eqid 3ad2ant3 syl clt cseq cneg
      wbr csn cxp c1 cgn cz nnz gxval syl3an3 nnne0 neneqd iffalse nngt0 iftrue
      wn 3eqtrd ) CHIZAEIZDJIZKZADBLZDMNZCOPZMDUAUDZDCJAUEUFUGUBZPZDUCVHPCUHPZP
      ZQZQZVLVIVBUTVADUIIVDVMNDUJABVFCDVJEFVFRVJRGUKULVCVEURZVMVLNVBUTVNVAVBDMD
      UMUNSVEVFVLUOTVCVGVLVINVBUTVGVADUPSVGVIVKUQTUS $.
  $}

  ${
    gxnval.1 $e |- X = ran G $.
    gxnval.2 $e |- P = ( ^g ` G ) $.
    gxnval.3 $e |- N = ( inv ` G ) $.
    $( The result of the group power operator when the exponent is negative.
       (Contributed by Paul Chapman, 17-Apr-2009.)  (Revised by Mario Carneiro,
       15-Dec-2013.)  (New usage is discouraged.) $)
    gxnval $p |- ( ( G e. GrpOp /\ A e. X /\ ( K e. ZZ /\ K < 0 ) ) ->
        ( A P K ) = ( N ` ( seq 1 ( G , ( NN X. { A } ) ) ` -u K ) ) ) $=
      ( wcel cc0 clt wbr wceq cfv cif wn 0re iffalse syl cgr cz w3a cgi csn cxp
      wa co cn c1 cseq cneg eqid gxval 3adant3r ltnri breq1 mtbiri simp3r nsyl3
      cr wi zre ltnsym sylancl imp 3ad2ant3 3eqtrd ) CUAJZAFJZDUBJZDKLMZUGZUCZA
      DBUHZDKNZCUDOZKDLMZDCUIAUEUFUJUKZOZDULVSOEOZPZPZWBWAVIVJVKVOWCNVLABVQCDEF
      GVQUMIHUNUOVNVPQWCWBNVPVLVNVPVLKKLMKRUPDKKLUQURVIVJVKVLUSUTVPVQWBSTVNVRQZ
      WBWANVMVIWDVJVKVLWDVKDVAJKVAJVLWDVBDVCRDKVDVEVFVGVRVTWASTVH $.
  $}

  ${
    gx0.1 $e |- X = ran G $.
    gx0.2 $e |- U = ( GId ` G ) $.
    gx0.3 $e |- P = ( ^g ` G ) $.
    $( The result of the group power operator when the exponent is zero.
       (Contributed by Paul Chapman, 17-Apr-2009.)  (Revised by Mario Carneiro,
       15-Dec-2013.)  (New usage is discouraged.) $)
    gx0 $p |- ( ( G e. GrpOp /\ A e. X ) -> ( A P 0 ) = U ) $=
      ( cgr wcel wa cc0 co wceq clt wbr cn cfv cif eqid csn cxp c1 cseq cneg cz
      cgn 0z gxval mp3an3 iftrue ax-mp syl6eq ) DIJZAEJZKALBMZLLNZCLLOPLDQAUAUB
      UCUDZRLUEURRDUGRZRSZSZCUNUOLUFJUPVANUHABCDLUSEFGUSTHUIUJUQVACNLTUQCUTUKUL
      UM $.
  $}

  ${
    $d A g $.  $d G g $.
    gx1.1 $e |- X = ran G $.
    gx1.2 $e |- P = ( ^g ` G ) $.
    $( The result of the group power operator when the exponent is one.
       (Contributed by Paul Chapman, 17-Apr-2009.)  (Revised by Mario Carneiro,
       15-Dec-2013.)  (New usage is discouraged.) $)
    gx1 $p |- ( ( G e. GrpOp /\ A e. X ) -> ( A P 1 ) = A ) $=
      ( cgr wcel wa c1 co cn csn cxp cfv cseq wceq 1nn gxpval mp3an3 cz 1z seq1
      ax-mp syl6eq fvconst2g mpan2 adantl eqtrd ) CGHZADHZIZAJBKZJLAMNZOZAULUMJ
      CUNJPOZUOUJUKJLHZUMUPQRABCJDEFSTJUAHUPUOQUBCUNJUCUDUEUKUOAQZUJUKUQURRLAJD
      UFUGUHUI $.
  $}

  ${
    gxnn0neg.1 $e |- X = ran G $.
    gxnn0neg.2 $e |- N = ( inv ` G ) $.
    gxnn0neg.3 $e |- P = ( ^g ` G ) $.
    $( A negative group power is the inverse of the positive power (lemma with
       nonnegative exponent - use ~ gxneg instead).  (Contributed by Paul
       Chapman, 17-Apr-2009.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    gxnn0neg $p |- ( ( G e. GrpOp /\ A e. X /\ K e. NN0 ) ->
                     ( A P -u K ) = ( N ` ( A P K ) ) ) $=
      ( wcel cneg co cfv wceq cn cc0 wa clt fveq2d eqtr4d cgr cn0 elnn0 w3a csn
      wo cxp c1 cseq cz wbr nnnegz nngt0 nnre lt0neg2d mpbid jca gxnval syl3an3
      gxpval nncn negnegd 3ad2ant3 3expia cgi negeq neg0 syl6eq oveq2d eqid gx0
      sylan9eqr oveq2 grpoinvid adantr eqtrd ex jaod syl5bi 3impia ) CUAJZAFJZD
      UBJZADKZBLZADBLZEMZNZWCDOJZDPNZUFWAWBQZWHDUCWKWIWHWJWAWBWIWHWAWBWIUDZWEWD
      KZCOAUEUGUHUIZMZEMZWGWIWAWBWDUJJZWDPRUKZQWEWPNWIWQWRDULWIPDRUKWRDUMWIDDUN
      UOUPUQABCWDEFGIHURUSWLWFWOEWLWFDWNMZWOABCDFGIUTWIWAWOWSNWBWIWMDWNWIDDVAVB
      SVCTSTVDWKWJWHWKWJQWECVEMZWGWJWKWEAPBLZWTWJWDPABWJWDPKPDPVFVGVHVIABWTCFGW
      TVJZIVKZVLWJWKWGXAEMZWTWJWFXAEDPABVMSWKXDWTEMZWTWKXAWTEXCSWAXEWTNWBWTCEXB
      HVNVOVPVLTVQVRVSVT $.
  $}

  ${
    $d A g k m $.  $d G g k m $.  $d K g m $.  $d P k m $.  $d X k m $.
    gxnn0suc.1 $e |- X = ran G $.
    gxnn0suc.2 $e |- P = ( ^g ` G ) $.
    $( Induction on group power (lemma with nonnegative exponent - use ~ gxsuc
       instead).  (Contributed by Paul Chapman, 17-Apr-2009.)  (Revised by
       Mario Carneiro, 15-Dec-2013.)  (New usage is discouraged.) $)
    gxnn0suc $p |- ( ( G e. GrpOp /\ A e. X /\ K e. NN0 ) ->
                     ( A P ( K + 1 ) ) = ( ( A P K ) G A ) ) $=
      ( wcel c1 caddc co wceq cn cc0 wa cfv oveq2d oveq1d eqtrd adantr wo elnn0
      cgr cn0 w3a csn cxp cseq peano2nn gxpval syl3an3 fvconst2g sylan2 3adant1
      cuz seqp1 nnuz eleq2s 3ad2ant3 3eqtr4d 3expia cgi grpolid simpr gx0 0p1e1
      eqid syl6eq gx1 3eqtr4rd ex jaod syl5bi 3impia ) CUCHZAEHZDUDHZADIJKZBKZA
      DBKZACKZLZVQDMHZDNLZUAVOVPOZWBDUBWEWCWBWDVOVPWCWBVOVPWCUEZVSVRCMAUFUGZIUH
      ZPZWAWCVOVPVRMHZVSWILDUIZABCVREFGUJUKWFDWHPZVRWGPZCKZWLACKWIWAWFWMAWLCVPW
      CWMALZVOWCVPWJWOWKMAVREULUMUNQWCVOWIWNLZVPWPDIUOPMCWGIDUPUQURUSWFVTWLACAB
      CDEFGUJRUTSVAWEWDWBWEWDOZCVBPZACKZAWAVSWEWSALWDAWRCEFWRVGZVCTWQVTWRACWQVT
      ANBKZWRWQDNABWEWDVDZQWEXAWRLWDABWRCEFWTGVETSRWQVSAIBKZAWQVRIABWQVRNIJKIWQ
      DNIJXBRVFVHQWEXCALWDABCEFGVITSVJVKVLVMVN $.

    $( Closure of the group power operator.  (Contributed by Paul Chapman,
       17-Apr-2009.)  (New usage is discouraged.) $)
    gxcl $p |- ( ( G e. GrpOp /\ A e. X /\ K e. ZZ ) -> ( A P K ) e. X ) $=
      ( vm vk wcel co cv cc0 wa wceq oveq2 eleq1d cfv wi 3expia cgr cz c1 caddc
      cneg cgi eqid gx0 grpoidcl adantr eqeltrd cn0 w3a grpocl 3adant3 gxnn0suc
      3com23 sylibrd cn cgn nnnn0 gxnn0neg syl3an3 grpoinvcl 3ad2antl1 ex zindd
      3impia ) CUAJZAEJZDUBJADBKZEJZAHLZBKZEJAMBKZEJAILZBKZEJZAVPUEZBKZEJZAVPUC
      UDKZBKZEJZVLVIVJNZHIDVMMOVNVOEVMMABPQVMVPOVNVQEVMVPABPQVMWBOVNWCEVMWBABPQ
      VMVSOVNVTEVMVSABPQVMDOVNVKEVMDABPQWEVOCUFRZEABWFCEFWFUGZGUHVIWFEJVJWFCEFW
      GUIUJUKVIVJVPULJZVRWDSVIVJWHUMZVRVQACKZEJZWDVIVJVRWKSWHVIVJVRWKVIVRVJWKVQ
      ACEFUNUQTUOWIWCWJEABCVPEFGUPQURTVIVJVPUSJZVRWASVIVJWLUMZVRWAWMVRNVTVQCUTR
      ZRZEWMVTWOOZVRWLVIVJWHWPVPVAABCVPWNEFWNUGZGVBVCUJVIVJVRWOEJWLVQCWNEFWQVDV
      EUKVFTVGVH $.
  $}

  ${
    gxneg.1 $e |- X = ran G $.
    gxneg.2 $e |- N = ( inv ` G ) $.
    gxneg.3 $e |- P = ( ^g ` G ) $.
    $( A negative group power is the inverse of the positive power.
       (Contributed by Paul Chapman, 17-Apr-2009.)
       (New usage is discouraged.) $)
    gxneg $p |- ( ( G e. GrpOp /\ A e. X /\ K e. ZZ ) ->
                     ( A P -u K ) = ( N ` ( A P K ) ) ) $=
      ( wcel cz w3a cn0 cneg co cfv wceq wi wa gxnn0neg cgr 3expia exp3a 3impia
      3adant3l simp1 znegcl syl3an3 3adant3r grpo2inv syl2anc simp3l zcn negneg
      gxcl cc oveq2d 3syl eqtr3d fveq2d wo cr elznn0 simprbi 3ad2ant3 mpjaod )
      CUAJZAFJZDKJZLDMJZADNZBOZADBOZEPZQZVKMJZVGVHVIVJVORVGVHSZVIVJVOVGVHVIVJSV
      OVGVHVJVOVIABCDEFGHITUEUBUCUDVGVHVIVPVORVQVIVPVOVGVHVIVPSZVOVGVHVRLZVLEPZ
      EPZVLVNVSVGVLFJZWAVLQVGVHVRUFVGVHVIWBVPVIVGVHVKKJWBDUGABCVKFGIUOUHUIVLCEF
      GHUJUKVSVTVMEVSAVKNZBOZVTVMVGVHVPWDVTQVIABCVKEFGHITUEVSVIDUPJZWDVMQVGVHVI
      VPULDUMWEWCDABDUNUQURUSUTUSUBUCUDVIVGVJVPVAZVHVIDVBJWFDVCVDVEVF $.

    $( The inverse of a negative group power is the positive power.
       (Contributed by Paul Chapman, 17-Apr-2009.)
       (New usage is discouraged.) $)
    gxneg2 $p |- ( ( G e. GrpOp /\ A e. X /\ K e. ZZ ) ->
                   ( N ` ( A P -u K ) ) = ( A P K ) ) $=
      ( cgr wcel cz w3a cneg co cfv gxneg fveq2d wceq simp1 gxcl grpo2inv eqtrd
      syl2anc ) CJKZAFKZDLKZMZADNBOZEPADBOZEPZEPZUJUHUIUKEABCDEFGHIQRUHUEUJFKUL
      UJSUEUFUGTABCDFGIUAUJCEFGHUBUDUC $.

    $( The result of the group power operator when the exponent is minus one.
       (Contributed by Paul Chapman, 17-Apr-2009.)
       (New usage is discouraged.) $)
    gxm1 $p |- ( ( G e. GrpOp /\ A e. X ) -> ( A P -u 1 ) = ( N ` A ) ) $=
      ( cgr wcel wa c1 cneg co cfv cz wceq 1z gxneg mp3an3 gx1 fveq2d eqtrd ) C
      IJZAEJZKZALMBNZALBNZDOZADOUDUELPJUGUIQRABCLDEFGHSTUFUHADABCEFHUAUBUC $.
  $}

  ${
    $d A k m $.  $d G k m $.  $d K m $.  $d P k m $.  $d X k m $.
    gxcom.1 $e |- X = ran G $.
    gxcom.2 $e |- P = ( ^g ` G ) $.
    $( The group power operator commutes with the group operation.
       (Contributed by Paul Chapman, 17-Apr-2009.)
       (New usage is discouraged.) $)
    gxcom $p |- ( ( G e. GrpOp /\ A e. X /\ K e. ZZ ) ->
                  ( ( A P K ) G A ) = ( A G ( A P K ) ) ) $=
      ( wcel cz co wceq cc0 wa oveq2 oveq1d oveq2d eqeq12d cfv adantr syl3anc
      vm vk cgr cv cneg c1 caddc cgi eqid grpolid gx0 grporid eqtrd 3eqtr4d cn0
      wi nn0z simp1 simp2 gxcl grpoass syl13anc syl3an3 gxnn0suc eqeq1d biimpar
      w3a ex 3expia cn nnz cgn simpl1 simpl2 znegcl grpoinvcl syl2anc grpoinvop
      gxneg fveq2 adantl 3eqtr2rd 3eqtr2d grpoasscan1 grpocl grpoasscan2 eqtr3d
      syl5 zindd 3impia ) CUCHZAEHZDIHADBJZACJZAWMCJZKZAUAUDZBJZACJZAWRCJZKALBJ
      ZACJZAXACJZKAUBUDZBJZACJZAXECJZKZAXDUEZBJZACJZAXJCJZKZAXDUFUGJZBJZACJZAXO
      CJZKZWPWKWLMZUAUBDWQLKZWSXBWTXCXTWRXAACWQLABNZOXTWRXAACYAPQWQXDKZWSXFWTXG
      YBWRXEACWQXDABNZOYBWRXEACYCPQWQXNKZWSXPWTXQYDWRXOACWQXNABNZOYDWRXOACYEPQW
      QXIKZWSXKWTXLYFWRXJACWQXIABNZOYFWRXJACYGPQWQDKZWSWNWTWOYHWRWMACWQDABNZOYH
      WRWMACYIPQXSCUHRZACJAXBXCAYJCEFYJUIZUJXSXAYJACABYJCEFYKGUKZOXSXCAYJCJAXSX
      AYJACYLPAYJCEFYKULUMUNWKWLXDUOHZXHXRUPWKWLYMVGZXHXRYNXHMZXGACJZAXFCJZXPXQ
      YNYPYQKZXHYMWKWLXDIHZYRXDUQWKWLYSVGZWKWLXEEHZWLYRWKWLYSURWKWLYSUSZABCXDEF
      GUTZUUBAXEACEFVAVBVCSYOXOXGACYNXOXGKXHYNXOXFXGABCXDEFGVDZVEVFOYNXQYQKXHYN
      XOXFACUUDPSUNVHVIXDVJHYSXSXHXMUPZXDVKWKWLYSUUEYTXHXMYTXHMZXLACVLRZRZCJZAC
      JZXKXLUUFUUIXJACUUFUUIAXJUUHCJZCJZXJUUFWKWLXJEHZUUHEHZUUIUULKWKWLYSXHVMZW
      KWLYSXHVNZYTUUMXHYSWKWLXIIHUUMXDVOABCXIEFGUTVCSZUUFWKWLUUNUUOUUPACUUGEFUU
      GUIZVPVQAXJUUHCEFVAVBUUFUULAUUHXJCJZCJZXJUUFUUKUUSACUUFUUKXEUUGRZUUHCJZXG
      UUGRZUUSUUFXJUVAUUHCYTXJUVAKXHABCXDUUGEFUURGVSSZOUUFWKWLUUAUVCUVBKUUOUUPY
      TUUAXHUUCSZAXECUUGEFUURVRTUUFUUSUUHUVACJZXFUUGRZUVCUUFXJUVAUUHCUVDPUUFWKU
      UAWLUVGUVFKUUOUVEUUPXEACUUGEFUURVRTXHUVGUVCKYTXFXGUUGVTWAWBWCPUUFWKWLUUMU
      UTXJKUUOUUPUUQAXJCUUGEFUURWDTUMUMOUUFWKXLEHZWLUUJXLKUUOUUFWKWLUUMUVHUUOUU
      PUUQAXJCEFWETUUPXLACUUGEFUURWFTWGVHVIWHWIWJ $.
  $}

  ${
    $d A k m $.  $d G k m $.  $d K k m $.  $d N k m $.  $d P k m $.
    $d X k m $.
    gxinv.1 $e |- X = ran G $.
    gxinv.2 $e |- N = ( inv ` G ) $.
    gxinv.3 $e |- P = ( ^g ` G ) $.
    $( The group power operator commutes with the group inverse function.
       (Contributed by Paul Chapman, 17-Apr-2009.)
       (New usage is discouraged.) $)
    gxinv $p |- ( ( G e. GrpOp /\ A e. X /\ K e. ZZ ) ->
                  ( ( N ` A ) P K ) = ( N ` ( A P K ) ) ) $=
      ( wcel cfv co wceq cc0 wa oveq2 fveq2d eqeq12d adantr syld3an2 vm vk cneg
      cgr cz cv c1 caddc cgi grpoinvid gx0 grpoinvcl syldan 3eqtr4rd cn0 wi w3a
      eqid 3adant3 gxnn0suc nn0z gxcom syl3an3 eqtrd simp1 gxcl simp2 grpoinvop
      adantl syl3anc 3eqtr4d ex 3expia nnz gxneg simpr eqtr4d syl5 zindd 3impia
      cn ) CUDJZAFJZDUEJAEKZDBLZADBLZEKZMZWDUAUFZBLZAWIBLZEKZMWDNBLZANBLZEKZMWD
      UBUFZBLZAWPBLZEKZMZWDWPUCZBLZAXABLZEKZMZWDWPUGUHLZBLZAXFBLZEKZMZWHWBWCOZU
      AUBDWINMZWJWMWLWOWINWDBPXLWKWNEWINABPQRWIWPMZWJWQWLWSWIWPWDBPXMWKWREWIWPA
      BPQRWIXFMZWJXGWLXIWIXFWDBPXNWKXHEWIXFABPQRWIXAMZWJXBWLXDWIXAWDBPXOWKXCEWI
      XAABPQRWIDMZWJWEWLWGWIDWDBPXPWKWFEWIDABPQRXKCUIKZEKZXQWOWMWBXRXQMWCXQCEXQ
      URZHUJSXKWNXQEABXQCFGXSIUKQWBWCWDFJZWMXQMACEFGHULZWDBXQCFGXSIUKUMUNWBWCWP
      UOJZWTXJUPWBWCYBUQZWTXJYCWTOWDWQCLZWDWSCLZXGXIWTYDYEMYCWQWSWDCPVIYCXGYDMW
      TYCXGWQWDCLZYDWBXTWCYBXGYFMWBWCXTYBYAUSZWDBCWPFGIUTTWBXTWCYBYFYDMZYGYBWBX
      TWPUEJZYHWPVAZWDBCWPFGIVBVCTVDSYCXIYEMWTYCXIWRACLZEKZYEYCXHYKEABCWPFGIUTQ
      YCWBWRFJZWCYLYEMWBWCYBVEYBWBWCYIYMYJABCWPFGIVFVCWBWCYBVGWRACEFGHVHVJVDSVK
      VLVMWPWAJYIXKWTXEUPZWPVNWBWCYIYNWBWCYIUQZWTXEYOWTOZXBWQEKZXDYOXBYQMZWTWBX
      TWCYIYRWBWCXTYIYAUSWDBCWPEFGHIVOTSYPXCWQEYPXCWSWQYOXCWSMWTABCWPEFGHIVOSYO
      WTVPVQQVQVLVMVRVSVT $.

    $( The group power operator commutes with the group inverse function.
       (Contributed by Paul Chapman, 17-Apr-2009.)
       (New usage is discouraged.) $)
    gxinv2 $p |- ( ( G e. GrpOp /\ A e. X /\ K e. ZZ ) ->
                   ( N ` ( ( N ` A ) P K ) ) = ( A P K ) ) $=
      ( cgr wcel cz w3a cfv co wceq grpoinvcl 3adant3 gxinv syld3an2 grpo2inv
      oveq1d eqtr3d ) CJKZAFKZDLKZMZAENZENZDBOZUHDBOENZADBOUDUHFKZUEUFUJUKPUDUE
      ULUFACEFGHQRUHBCDEFGHISTUGUIADBUDUEUIAPUFACEFGHUARUBUC $.
  $}

  ${
    gxsuc.1 $e |- X = ran G $.
    gxsuc.2 $e |- P = ( ^g ` G ) $.
    $( Induction on group power.  (Contributed by Paul Chapman, 17-Apr-2009.)
       (New usage is discouraged.) $)
    gxsuc $p |- ( ( G e. GrpOp /\ A e. X /\ K e. ZZ ) ->
                  ( A P ( K + 1 ) ) = ( ( A P K ) G A ) ) $=
      ( wcel cn0 c1 caddc co wceq cneg wa cfv syld3an3 syl2anc oveq2d cc cgr cz
      w3a cn wi gxnn0suc 3expia 3adant3 cgn simp3l gxcom simp1 peano2z syl gxcl
      eqid grpo2inv cmin nnm1nn0 adantl wb zcn ax-1cn negdi negcld negsub eqtrd
      sylancl eleq1d adantr mpbird syl3an3 oveq1d npcan gxneg 3eqtr3d grpoinvcl
      eqtr3d fveq2d simp2 grpoinvop syl3anc grpoasscan1 3eqtr2rd exp3a elznn0nn
      3impia wo cr simpr orim2i sylbi 3ad2ant3 mpjaod ) CUAHZAEHZDUBHZUCDIHZADJ
      KLZBLZADBLZACLZMZDNZUDHZWOWPWRXCUEWQWOWPWRXCABCDEFGUFUGUHWOWPWQXEXCUEWOWP
      OWQXEXCWOWPWQXEOZXCWOWPXFUCZXBAXACLZAACUIPZPZWTCLZCLZWTWOWPXFWQXBXHMWOWPW
      QXEUJZABCDEFGUKQXGXKXAACXGXJWTXIPZXIPZCLZXKXAXGXOWTXJCXGWOWTEHZXOWTMWOWPX
      FULZWOWPXFWSUBHZXQXGWQXSXMDUMZUNABCWSEFGUOQZWTCXIEFXIUPZUQRSXGXNACLZXIPZX
      AXIPZXIPZXPXAXGYCYEXIXGAWSNZBLZACLZAXDBLZYCYEXGAYGJKLZBLZYIYJXFWOWPYGIHZY
      LYIMXFYMXDJURLZIHZXEYOWQXDUSUTWQYMYOVAXEWQYGYNIWQYGXDJNKLZYNWQDTHJTHZYGYP
      MDVBZVCDJVDVHWQXDTHZYQYPYNMWQDYRVEZVCXDJVFVHVGZVIVJVKABCYGEFGUFVLXGWQYLYJ
      MXMWQYKXDABWQYKYNJKLZXDWQYGYNJKUUAVMWQYSYQUUBXDMYTVCXDJVNVHVGSUNVRXGYHXNA
      CWOWPXFWQYHXNMZXMWQWOWPXSUUCXTABCWSXIEFYBGVOVLQVMWOWPXFWQYJYEMXMABCDXIEFY
      BGVOQVPVSXGWOXNEHZWPYDXPMXRXGWOXQUUDXRYAWTCXIEFYBVQRWOWPXFVTXNACXIEFYBWAW
      BXGWOXAEHZYFXAMXRWOWPXFWQUUEXMABCDEFGUOQXACXIEFYBUQRVPVRSWOWPXFXQXLWTMYAA
      WTCXIEFYBWCQWDUGWEWGWQWOWRXEWHZWPWQWRDWIHZXEOZWHUUFDWFUUHXEWRUUGXEWJWKWLW
      MWN $.
  $}

  ${
    $d G k m $.  $d K k m $.  $d P k m $.  $d U k m $.
    gxid.1 $e |- U = ( GId ` G ) $.
    gxid.2 $e |- P = ( ^g ` G ) $.
    $( The identity element of a group to any power remains unchanged.
       (Contributed by Paul Chapman, 17-Apr-2009.)
       (New usage is discouraged.) $)
    gxid $p |- ( ( G e. GrpOp /\ K e. ZZ ) -> ( U P K ) = U ) $=
      ( vm vk wcel cz co wceq cv cc0 oveq2 eqeq1d eqid wi syl3anc cfv cgr caddc
      cneg c1 crn grpoidcl gx0 mpdan cn0 nn0z wa simpl simpr gxsuc gxcl grporid
      adantr syldan eqtr2d biimpd ex syl5 cn nnz w3a cgn gxneg syl3an2 3anidm12
      3adant3 fveq2 grpoinvid sylan9eqr 3adant2 eqtrd 3exp zindd imp ) CUAIZDJI
      BDAKZBLZBGMZAKZBLBNAKZBLZBHMZAKZBLZBWFUCZAKZBLZBWFUDUBKZAKZBLZWAVSGHDWBNL
      WCWDBWBNBAOPWBWFLWCWGBWBWFBAOPWBWLLWCWMBWBWLBAOPWBWILWCWJBWBWIBAOPWBDLWCV
      TBWBDBAOPVSBCUEZIZWEBCWOWOQZEUFZBABCWOWQEFUGUHWFUIIWFJIZVSWHWNRZWFUJVSWSW
      TVSWSUKZWHWNXAWGWMBXAWMWGBCKZWGXAVSWPWSWMXBLVSWSULZVSWPWSWRUQZVSWSUMZBACW
      FWOWQFUNSVSWSWGWOIZXBWGLXAVSWPWSXFXCXDXEBACWFWOWQFUOSWGBCWOWQEUPURUSPUTVA
      VBWFVCIWSVSWHWKRWFVDVSWSWHWKVSWSWHVEWJWGCVFTZTZBVSWSWJXHLZWHVSWSXIVSVSWPW
      SXIWRBACWFXGWOWQXGQZFVGVHVIVJVSWHXHBLWSWHVSXHBXGTBWGBXGVKBCXGEXJVLVMVNVOV
      PVBVQVR $.
  $}

  ${
    $d A k m $.  $d G k m $.  $d J k m $.  $d K m $.  $d P k m $.  $d X k m $.
    gxnn0add.1 $e |- X = ran G $.
    gxnn0add.2 $e |- P = ( ^g ` G ) $.
    $( The group power of a sum is the group product of the powers (lemma with
       nonnegative exponent - use ~ gxadd instead).  (Contributed by Paul
       Chapman, 17-Apr-2009.)  (New usage is discouraged.) $)
    gxnn0add $p |- ( ( G e. GrpOp /\ A e. X /\ ( J e. ZZ /\ K e. NN0 ) ) ->
                     ( A P ( J + K ) ) = ( ( A P J ) G ( A P K ) ) ) $=
      ( wcel wa caddc co wceq wi cc0 c1 oveq2 oveq2d eqeq12d imbi2d cgr cn0 w3a
      vm vk cz cv cgi cfv addid1d 3ad2ant3 gxcl eqid grporid ex 3ad2ant1 eqtr4d
      zcn mpd 3adant3 nn0z gxsuc 3adant3l adantr simpl1 3adant3r simpl2 grpoass
      gx0 syl13anc zaddcl syl3an3 oveq1 sylan9eq cc ax-1cn addass mp3an3 syl2an
      3eqtr2rd 3expia exp3a 3impia com12 a2d syl nn0ind imp3a ) CUAIZAFIZDUFIZE
      UBIZJADEKLZBLZADBLZAEBLZCLZMZWIWJJZWKWLWRWIWJWKWLWRNWLWIWJWKUCZWRWTADUDUG
      ZKLZBLZWOAXABLZCLZMZNWTADOKLZBLZWOAOBLZCLZMZNWTADUEUGZKLZBLZWOAXLBLZCLZMZ
      NZWTADXLPKLZKLZBLZWOAXSBLZCLZMZNZWTWRNUDUEEXAOMZXFXKWTYFXCXHXEXJYFXBXGABX
      AODKQRYFXDXIWOCXAOABQRSTXAXLMZXFXQWTYGXCXNXEXPYGXBXMABXAXLDKQRYGXDXOWOCXA
      XLABQRSTXAXSMZXFYDWTYHXCYAXEYCYHXBXTABXAXSDKQRYHXDYBWOCXAXSABQRSTXAEMZXFW
      RWTYIXCWNXEWQYIXBWMABXAEDKQRYIXDWPWOCXAEABQRSTWTXHWOCUHUIZCLZXJWTXHWOYKWK
      WIXHWOMWJWKXGDABWKDDURZUJRUKWTWOFIZYKWOMZABCDFGHULZWIWJYMYNNWKWIYMYNWOYJC
      FGYJUMZUNUOUPUSUQWIWJXJYKMWKWSXIYJWOCABYJCFGYPHVIRUTUQXLUBIXLUFIZXRYENXLV
      AYQWTXQYDWTYQXQYDNZWIWJWKYQYRNWSWKYQYRWIWJWKYQJZYRWIWJYSUCZXQYDYTXQJZYCXP
      ACLZAXMPKLZBLZYAUUAYCWOXOACLZCLZUUBYTYCUUFMZXQWIWJYQUUGWKWIWJYQUCYBUUEWOC
      ABCXLFGHVBRVCVDUUAWIYMXOFIZWJUUBUUFMWIWJYSXQVEYTYMXQWIWJWKYMYQYOVFVDYTUUH
      XQWIWJYQUUHWKABCXLFGHULVCVDWIWJYSXQVGWOXOACFGVHVJUQYTXQUUDXNACLZUUBYSWIWJ
      XMUFIUUDUUIMDXLVKABCXMFGHVBVLXNXPACVMVNUUAUUCXTABYTUUCXTMZXQYSWIUUJWJWKDV
      OIZXLVOIZUUJYQYLXLURUUKUULPVOIUUJVPDXLPVQVRVSUKVDRVTUOWAWBWCWDWEWFWGWDWAW
      HWC $.

    $( The group power of a sum is the group product of the powers.
       (Contributed by Paul Chapman, 17-Apr-2009.)
       (New usage is discouraged.) $)
    gxadd $p |- ( ( G e. GrpOp /\ A e. X /\ ( J e. ZZ /\ K e. ZZ ) ) ->
                  ( A P ( J + K ) ) = ( ( A P J ) G ( A P K ) ) ) $=
      ( wcel cz wa caddc co wceq wi 3expia 3impia syl3an3 cc eqtr3d cgr w3a cn0
      cneg gxnn0add exp3a adantr cgn cfv zaddcl adantrr gxcl simprl grpoasscan2
      simp1 eqid syl3anc gxneg oveq2d simprr jca zcn cmin addcl negsub sylancom
      pncan eqtrd syl2an 3ad2ant3 oveq1d expdimp wo cr elznn0 simprbi adantl ex
      mpjaod imp3a ) CUAIZAFIZDJIZEJIZKADELMZBMZADBMZAEBMZCMZNZWAWBKZWCWDWJWAWB
      WCWDWJOWAWBWCUBZWDWJWLWDKEUCIZWJEUDZUCIZWLWMWJOZWDWAWBWCWPWKWCWMWJWAWBWCW
      MKWJABCDEFGHUEPUFQUGWLWDWOWJWAWBWCWDWOKZWJOWKWCWQWJWAWBWCWQKZWJWAWBWRUBZW
      FWHCUHUIZUIZCMZWHCMZWFWIWSWAWFFIZWHFIZXCWFNWAWBWRUOWRWAWBWEJIZXDWCWDXFWOD
      EUJUKZABCWEFGHULRWRWAWBWDXEWCWDWOUMZABCEFGHULRWFWHCWTFGWTUPZUNUQWSXBWGWHC
      WSWFAWNBMZCMZXBWGWSXJXAWFCWRWAWBWDXJXANXHABCEWTFGXIHURRUSWSAWEWNLMZBMZXKW
      GWRWAWBXFWOKXMXKNWRXFWOXGWCWDWOUTVAABCWEWNFGHUERWRWAXMWGNWBWRXLDABWCDSIZE
      SIZXLDNWQDVBWDXOWOEVBUGXNXOKXLWEEVCMZDXNXOWESIXLXPNDEVDWEEVEVFDEVGVHVIUSV
      JTTVKTPUFQVLWDWMWOVMZWLWDEVNIXQEVOVPVQVSVRPVTQ $.
  $}

  ${
    gxsub.1 $e |- X = ran G $.
    gxsub.2 $e |- N = ( inv ` G ) $.
    gxsub.3 $e |- P = ( ^g ` G ) $.
    $( The group power of a difference is the group quotient of the powers.
       (Contributed by Paul Chapman, 17-Apr-2009.)
       (New usage is discouraged.) $)
    gxsub $p |- ( ( G e. GrpOp /\ A e. X /\ ( J e. ZZ /\ K e. ZZ ) ) ->
        ( A P ( J - K ) ) = ( ( A P J ) G ( N ` ( A P K ) ) ) ) $=
      ( cgr wcel cz wa w3a co wceq cc zcn oveq2d cneg caddc znegcl anim2i gxadd
      cmin cfv syl3an3 negsub syl2an 3ad2ant3 gxneg 3adant3l 3eqtr3d ) CKLZAGLZ
      DMLZEMLZNZOZADEUAZUBPZBPZADBPZAVABPZCPZADEUFPZBPVDAEBPFUGZCPUSUOUPUQVAMLZ
      NVCVFQURVIUQEUCUDABCDVAGHJUEUHUTVBVGABUSUOVBVGQZUPUQDRLERLVJURDSESDEUIUJU
      KTUTVEVHVDCUOUPURVEVHQUQABCEFGHIJULUMTUN $.
  $}

  ${
    $d A k m $.  $d G k m $.  $d J k m $.  $d K m $.  $d P k m $.  $d X k m $.
    gxnn0mul.1 $e |- X = ran G $.
    gxnn0mul.2 $e |- P = ( ^g ` G ) $.
    $( The group power of a product is the composition of the powers (lemma
       with nonnegative exponent - use ~ gxmul instead).  (Contributed by Paul
       Chapman, 17-Apr-2009.)  (New usage is discouraged.) $)
    gxnn0mul $p |- ( ( G e. GrpOp /\ A e. X /\ ( J e. ZZ /\ K e. NN0 ) ) ->
                     ( A P ( J x. K ) ) = ( ( A P J ) P K ) ) $=
      ( wcel wa cmul co wceq wi cc0 c1 caddc oveq2 oveq2d eqeq12d vm vk cgr cn0
      cz w3a cv imbi2d cgi cfv eqid gx0 3adant3 zcn 3ad2ant3 simp1 gxcl syl2anc
      mul01d 3eqtr4d oveq1 adantl nn0cn ax-1cn adddi mp3an3 mulid1 adantr eqtrd
      cc syl2an nn0z zmulcl sylan2 simpl jca gxadd syl3an3 3adant3r nn0zd gxsuc
      simp3r syl3anc ex 3expia exp3a 3impia com12 a2d nn0ind imp3a ) CUCIZAFIZD
      UEIZEUDIZJADEKLZBLZADBLZEBLZMZWLWMJZWNWOWTWLWMWNWOWTNWOWLWMWNUFZWTXBADUAU
      GZKLZBLZWRXCBLZMZNXBADOKLZBLZWROBLZMZNXBADUBUGZKLZBLZWRXLBLZMZNXBADXLPQLZ
      KLZBLZWRXQBLZMZNXBWTNUAUBEXCOMZXGXKXBYBXEXIXFXJYBXDXHABXCODKRSXCOWRBRTUHX
      CXLMZXGXPXBYCXEXNXFXOYCXDXMABXCXLDKRSXCXLWRBRTUHXCXQMZXGYAXBYDXEXSXFXTYDX
      DXRABXCXQDKRSXCXQWRBRTUHXCEMZXGWTXBYEXEWQXFWSYEXDWPABXCEDKRSXCEWRBRTUHXBA
      OBLZCUIUJZXIXJWLWMYFYGMWNABYGCFGYGUKZHULUMWNWLXIYFMWMWNXHOABWNDDUNZUSSUOX
      BWLWRFIZXJYGMWLWMWNUPABCDFGHUQZWRBYGCFGYHHULURUTXLUDIZXBXPYAXBYLXPYANZWLW
      MWNYLYMNXAWNYLYMWLWMWNYLJZYMWLWMYNUFZXPYAYOXPJXNWRCLZXOWRCLZXSXTXPYPYQMYO
      XNXOWRCVAVBYOXSYPMXPYOXSAXMDQLZBLZYPYNWLXSYSMWMYNXRYRABWNDVJIZXLVJIZXRYRM
      YLYIXLVCYTUUAJXRXMDPKLZQLZYRYTUUAPVJIXRUUCMVDDXLPVEVFYTUUCYRMUUAYTUUBDXMQ
      DVGSVHVIVKSUOYNWLWMXMUEIZWNJYSYPMYNUUDWNYLWNXLUEIZUUDXLVLDXLVMVNWNYLVOVPA
      BCXMDFGHVQVRVIVHYOXTYQMZXPYOWLYJUUEUUFWLWMYNUPWLWMWNYJYLYKVSYOXLWLWMWNYLW
      BVTWRBCXLFGHWAWCVHUTWDWEWFWGWHWIWJWHWEWKWG $.

    $( The group power of a product is the composition of the powers.
       (Contributed by Paul Chapman, 17-Apr-2009.)
       (New usage is discouraged.) $)
    gxmul $p |- ( ( G e. GrpOp /\ A e. X /\ ( J e. ZZ /\ K e. ZZ ) ) ->
                  ( A P ( J x. K ) ) = ( ( A P J ) P K ) ) $=
      ( wcel cz wa cmul co wceq wi w3a 3expia 3impia cfv syl3anc cgr cneg exp3a
      cn0 gxnn0mul adantr cgn znegcl simpr anim12i syl3an3 zcn mul2neg 3ad2ant3
      cc syl2an oveq2d eqid gxneg 3adant3r oveq1d 3eqtr3d simp1 simp3rl znegcld
      gxcl gxinv eqtrd fveq2d grpo2inv syl2anc 3eqtrd expdimp wo elznn0 simprbi
      cr adantl mpjaod ex imp3a ) CUAIZAFIZDJIZEJIZKADELMZBMZADBMZEBMZNZWBWCKZW
      DWEWJWBWCWDWEWJOWBWCWDPZWEWJWLWEKEUDIZWJEUBZUDIZWLWMWJOZWEWBWCWDWPWKWDWMW
      JWBWCWDWMKWJABCDEFGHUEQUCRUFWLWEWOWJWBWCWDWEWOKZWJOWKWDWQWJWBWCWDWQKZWJWB
      WCWRPZWGWHWNBMZCUGSZSZWIXASZXASZWIWSWGWHXASZWNBMZXBWSADUBZWNLMZBMZAXGBMZW
      NBMZWGXFWRWBWCXGJIZWOKXIXKNWDXLWQWODUHWEWOUIUJABCXGWNFGHUEUKWSXHWFABWRWBX
      HWFNZWCWDDUOIEUOIZXMWQDULWEXNWOEULUFDEUMUPUNUQWSXJXEWNBWBWCWDXJXENWQABCDX
      AFGXAURZHUSUTVAVBWSWBWHFIZWNJIXFXBNWBWCWRVCZWBWCWDXPWQABCDFGHVFUTZWSEWEWO
      WDWBWCVDZVEWHBCWNXAFGXOHVGTVHWSWTXCXAWSWBXPWEWTXCNXQXRXSWHBCEXAFGXOHUSTVI
      WSWBWIFIZXDWINXQWSWBXPWEXTXQXRXSWHBCEFGHVFTWICXAFGXOVJVKVLQUCRVMWEWMWOVNZ
      WLWEEVQIYAEVOVPVRVSVTQWAR $.
  $}

  ${
    gxmodid.1 $e |- X = ran G $.
    gxmodid.2 $e |- U = ( GId ` G ) $.
    gxmodid.3 $e |- P = ( ^g ` G ) $.
    $( Casting out powers of the identity element leaves the group power
       unchanged.  (Contributed by Paul Chapman, 17-Apr-2009.)
       (New usage is discouraged.) $)
    gxmodid $p |- ( ( G e. GrpOp /\ ( K e. ZZ /\ M e. NN ) /\
      ( A e. X /\ ( A P M ) = U ) ) -> ( A P ( K mod M ) ) = ( A P K ) ) $=
      ( wcel cz wa co wceq cmul cr 3ad2ant2 oveq2d zcnd cgr cn w3a cmo cdiv cfl
      cfv cneg cmin caddc crp zre nnrp modval syl2an simpl nnz adantl cc0 nnne0
      wne nnre redivcl syl3an 3anidm23 flcld zmulcld negsubd simp3l znegcld jca
      simp1 gxadd syl3anc 3eqtr2d mulneg2d gxmul syl112anc 3ad2ant3 gxid 3eqtrd
      oveq1 syl2anc eqtr3d simp2l gxcl grporid ) DUAKZELKZFUBKZMZAGKZAFBNZCOZMZ
      UCZAEFUDNZBNZAEBNZAFEFUENZUFUGZPNZUHZBNZDNZWSCDNZWSWPWRAEXBUINZBNAEXCUJNZ
      BNZXEWPWQXGABWKWHWQXGOZWOWIEQKZFUKKXJWJEULZFUMEFUNUORSWPXHXGABWKWHXHXGOWO
      WKEXBWKEWIWJUPZTWKXBWKFXAWJFLKZWIFUQURZWKWTWIWJWTQKZWIXKWJFQKWJFUSVAXPXLF
      VBFUTEFVCVDVEVFZVGZTVHRSWPWHWLWIXCLKZMZXIXEOWHWKWOVLZWHWKWLWNVIZWKWHXTWOW
      KWIXSXMWKXBXRVJVKRABDEXCGHJVMVNVOWPXDCWSDWPAFXAUHZPNZBNZXDCWPYDXCABWKWHYD
      XCOWOWKFXAWKFXOTWKXAXQTVPRSWPYEWMYCBNZCYCBNZCWPWHWLXNYCLKZYEYFOYAYBWKWHXN
      WOXORWKWHYHWOWKXAXQVJRZABDFYCGHJVQVRWOWHYFYGOZWKWNYJWLWMCYCBWBURVSWPWHYHY
      GCOYAYIBCDYCIJVTWCWAWDSWPWHWSGKZXFWSOYAWPWHWLWIYKYAYBWHWIWJWOWEABDEGHJWFV
      NWSCDGHIWGWCWA $.
  $}

  ${
    resgrprn.1 $e |- H = ( G |` ( Y X. Y ) ) $.
    $( The underlying set of a group operation which is a restriction of a
       mapping.  (Contributed by Paul Chapman, 25-Mar-2008.)
       (New usage is discouraged.) $)
    resgrprn $p |- ( ( dom G = ( X X. X ) /\ H e. GrpOp /\ Y C_ X ) ->
                        Y = ran H ) $=
      ( cdm cxp wceq cgr wcel wss w3a crn cres dmeqi xpss12 anidms sseq2 sylib
      wa biimpar sylan2 ssdmres syl5eq 3adant2 wfo eqid grpofo fof fdm 3ad2ant2
      wf 3syl eqtr3d xpid11 ) AFZCCGZHZBIJZDCKZLZDDGZBMZVCGZHDVCHVABFZVBVDURUTV
      EVBHUSURUTTZVEAVBNZFZVBBVGEOVFVBUPKZVHVBHUTURVBUQKZVIUTVJDCDCPQURVIVJUPUQ
      VBRUAUBVBAUCSUDUEUSURVEVDHZUTUSVDVCBUFVDVCBULVKBVCVCUGUHVDVCBUIVDVCBUJUMU
      KUNDVCUOS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
            Definition and basic properties of Abelian groups
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
      ( vg cv co wceq crn wral cgr cablo rneq syl6eqr raleq raleqbi1dv syl oveq
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
      ( cablo wcel cgr cv co wceq wral rgen2a grporn isablo mpbir2an ) CHICJIAK
      ZBKZCLTSCLMZBDNADNEUAABDGOABCDCDEFPQR $.
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

    $( Cancellation law for group division.  ( ~ nnncan analog.)  (Contributed
       by NM, 29-Feb-2008.)  (New usage is discouraged.) $)
    ablonnncan $p |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
      ( ( A D ( B D C ) ) D C ) = ( A D B ) ) $=
      ( cablo wcel w3a wa wceq simpr1 cgr ablogrpo grpodivcl syl3an1 3adant3r1
      co simpr3 3jca ablodivdiv4 syldan grponpcan oveq2d eqtrd ) EIJZAFJZBFJZCF
      JZKZLZABCDTZDTCDTZAUNCETZDTZABDTUHULUIUNFJZUKKUOUQMUMUIURUKUHUIUJUKNUHUJU
      KURUIUHEOJZUJUKUREPZBCDEFGHQRSUHUIUJUKUAUBAUNCDEFGHUCUDUMUPBADUHUJUKUPBMZ
      UIUHUSUJUKVAUTBCDEFGHUERSUFUG $.

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

  ${
    $d A k m $.  $d B k m $.  $d G k m $.  $d K m $.  $d P k m $.  $d X k m $.
    gxdi.1 $e |- X = ran G $.
    gxdi.2 $e |- P = ( ^g ` G ) $.
    $( Distribution of group power over group operation for abelian groups.
       (Contributed by Paul Chapman, 17-Apr-2009.)
       (New usage is discouraged.) $)
    gxdi $p |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X ) /\ K e. ZZ ) ->
                 ( ( A G B ) P K ) = ( ( A P K ) G ( B P K ) ) ) $=
      ( wcel wceq cc0 oveq2 oveq12d eqeq12d cfv 3ad2ant1 syl2anc eqtr4d syl3anc
      co vm vk cablo wa cz wi cv cneg caddc w3a cgi cgr ablogrpo grpocl syl3an1
      eqid gx0 grpoidcl syl grpolid simp2 simp3 cn0 gxsuc oveq1 3ad2ant3 simp11
      c1 nn0z gxcl ablo4 syl122anc 3eqtrd 3exp syl5 cn nnz cgn gxneg ablocom wb
      eqeq1 mpbird fveq2d grpoinvop zindd 3expb 3impia ) DUCIZAFIZBFIZUDEUEIZAB
      DTZECTZAECTZBECTZDTZJZWIWJWKWLWRUFWMUAUGZCTZAWSCTZBWSCTZDTZJWMKCTZAKCTZBK
      CTZDTZJWMUBUGZCTZAXHCTZBXHCTZDTZJZWMXHUHZCTZAXNCTZBXNCTZDTZJZWMXHVHUITZCT
      ZAXTCTZBXTCTZDTZJZWRWIWJWKUJZUAUBEWSKJZWTXDXCXGWSKWMCLYGXAXEXBXFDWSKACLWS
      KBCLMNWSXHJZWTXIXCXLWSXHWMCLYHXAXJXBXKDWSXHACLWSXHBCLMNWSXTJZWTYAXCYDWSXT
      WMCLYIXAYBXBYCDWSXTACLWSXTBCLMNWSXNJZWTXOXCXRWSXNWMCLYJXAXPXBXQDWSXNACLWS
      XNBCLMNWSEJZWTWNXCWQWSEWMCLYKXAWOXBWPDWSEACLWSEBCLMNYFXDDUKOZYLDTZXGYFXDY
      LYMYFDULIZWMFIZXDYLJWIWJYNWKDUMZPZWIYNWJWKYOYPABDFGUNUOZWMCYLDFGYLUPZHUQQ
      YFYNYLFIZYMYLJYQYFYNYTYQYLDFGYSURUSYLYLDFGYSUTQRYFXEYLXFYLDYFYNWJXEYLJYQW
      IWJWKVAZACYLDFGYSHUQQYFYNWKXFYLJYQWIWJWKVBZBCYLDFGYSHUQQMRXHVCIXHUEIZYFXM
      YEUFXHVIYFUUCXMYEYFUUCXMUJZYAXJADTZXKBDTZDTZYDUUDYAXIWMDTZXLWMDTZUUGUUDYN
      YOUUCYAUUHJYFUUCYNXMYQPZYFUUCYOXMYRPZYFUUCXMVAZWMCDXHFGHVDSXMYFUUHUUIJUUC
      XIXLWMDVEVFUUDWIXJFIZXKFIZWJWKUUIUUGJWIWJWKUUCXMVGZUUDYNWJUUCUUMUUJYFUUCW
      JXMUUAPZUULACDXHFGHVJSZUUDYNWKUUCUUNUUJYFUUCWKXMUUBPZUULBCDXHFGHVJSZUUPUU
      RXJXKABDFGVKVLVMUUDYBUUEYCUUFDUUDYNWJUUCYBUUEJUUJUUPUULACDXHFGHVDSUUDYNWK
      UUCYCUUFJUUJUURUULBCDXHFGHVDSMRVNVOXHVPIUUCYFXMXSUFXHVQYFUUCXMXSUUDXOXJDV
      ROZOZXKUUTOZDTZXRUUDXOXIUUTOZXKXJDTZUUTOZUVCUUDYNYOUUCXOUVDJUUJUUKUULWMCD
      XHUUTFGUUTUPZHVSSUUDXIUVEUUTUUDXIUVEJZXLUVEJZUUDWIUUMUUNUVIUUOUUQUUSXJXKD
      FGVTSXMYFUVHUVIWAUUCXIXLUVEWBVFWCWDUUDYNUUNUUMUVFUVCJUUJUUSUUQXKXJDUUTFGU
      VGWESVMUUDXPUVAXQUVBDUUDYNWJUUCXPUVAJUUJUUPUULACDXHUUTFGUVGHVSSUUDYNWKUUC
      XQUVBJUUJUURUULBCDXHUUTFGUVGHVSSMRVNVOWFWGWH $.
  $}

  ${
    $d ph u x y z $.  $d G u n x y z $.  $d X u n x y z $.  $d U u n x y z $.
    $d N n $.
    isgrpda.1 $e |- ( ph -> X e. _V ) $.
    isgrpda.2 $e |- ( ph -> G : ( X X. X ) --> X ) $.
    isgrpda.3 $e |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) )
                            -> ( ( x G y ) G z ) = ( x G ( y G z ) ) ) $.
    isgrpda.4 $e |- ( ph -> U e. X ) $.
    isgrpda.5 $e |- ( ( ph /\ x e. X ) -> ( U G x ) = x ) $.

    ${
      isgrpda.6 $e |- ( ( ph /\ x e. X ) -> E. n e. X ( n G x ) = U ) $.
      $( Properties that determine a group operation.  (Contributed by Jeff
         Madsen, 1-Dec-2009.)  (New usage is discouraged.) $)
      isgrpda $p |- ( ph -> G e. GrpOp ) $=
        ( vu co wceq wral wrex cvv cgr wcel crn cxp wf cv w3a ralrimivvva oveq1
        wa eqeq1d cbvrexv sylibr ralrimiva eqeq2 rexbidv anbi12d ralbidv rspcev
        jca syl2anc wfo adantr simpr rspceov syl3anc foov sylanbrc forn xpeq12d
        eqcomd feq23d raleqdv raleqbidv anbi2d rexeqbidv 3anbi123d mpbir3and wb
        syl rexeqdv xpexg fex eqid isgrpo mpbird ) AGUAUBZGUCZWHUDZWHGUEZBUFZCU
        FZGPDUFZGPWKWLWMGPZGPQZDWHRZCWHRZBWHRZOUFZWKGPZWKQZWLWKGPZWSQZCWHSZUJZB
        WHRZOWHSZUGZAXHHHUDZHGUEZWODHRZCHRZBHRZXAXCCHSZUJZBHRZOHSZJAWOBCDHHHKUH
        AEHUBZEWKGPZWKQZXBEQZCHSZUJZBHRZXQLAYCBHAWKHUBZUJZXTYBMYFFUFZWKGPZEQZFH
        SYBNYAYICFHWLYGQXBYHEWLYGWKGUIUKULUMUTUNXPYDOEHWSEQZXOYCBHYJXAXTXNYBYJW
        TXSWKWSEWKGUIUKYJXCYACHWSEXBUOUPUQURUSVAAWJXJWRXMXGXQAWIWHXIHGAWHHWHHAX
        IHGVBZWHHQAXJWKWNQDHSCHSZBHRYKJAYLBHYFXRYEWKXSQYLAXRYELVCAYEVDYFXSWKMVK
        CDHHEWKWKGVEVFUNCDBHHHGVGVHXIHGVIVTZYMVJYMVLAWQXLBWHHYMAWPXKCWHHYMAWODW
        HHYMVMVNVNAXFXPOWHHYMAXEXOBWHHYMAXDXNXAAXCCWHHYMWAVOVNVPVQVRAGTUBZWGXHV
        SAXJXITUBZYNJAHTUBZYPYOIIHHTTWBVAXIHTGWCVABCDOTGWHWHWDWEVTWF $.
    $}

    ${
      isgrpod.6 $e |- ( ( ph /\ x e. X ) -> N e. X ) $.
      isgrpod.7 $e |- ( ( ph /\ x e. X ) -> ( N G x ) = U ) $.
      $( Properties that determine a group operation.  (Renamed from ~ isgrpd
         to ~ isgrpod to prevent naming conflict. -NM 5-Jun-2013) (Contributed
         by Jeff Madsen, 1-Dec-2009.)  (New usage is discouraged.) $)
      isgrpod $p |- ( ph -> G e. GrpOp ) $=
        ( vn cv wcel co wceq wa wrex oveq1 eqeq1d rspcev syl2anc isgrpda ) ABCD
        EPFHIJKLMABQZHRUAGHRGUHFSZETZPQZUHFSZETZPHUBNOUMUJPGHUKGTULUIEUKGUHFUCU
        DUEUFUG $.
    $}

    ${
      isablda.6 $e |- ( ( ph /\ x e. X ) -> E. n e. X ( n G x ) = U ) $.
      isablda.7 $e |- ( ( ph /\ ( x e. X /\ y e. X ) )
                              -> ( x G y ) = ( y G x ) ) $.
      $( Properties that determine an Abelian group operation.  (Contributed by
         Jeff Madsen, 11-Jun-2010.)  (New usage is discouraged.) $)
      isabloda $p |- ( ph -> G e. AbelOp ) $=
        ( wcel cv co wceq cdm cgr crn wral cablo isgrpda wa grporndm syl cxp wf
        fdm dmeqd dmxpid syl6eq eqtrd eleq2d anbi12d ex sylbid ralrimivv isablo
        eqid sylanbrc ) AGUAPZBQZCQZGRVFVEGRSZCGUBZUCBVHUCGUDPABCDEFGHIJKLMNUEZ
        AVGBCVHVHAVEVHPZVFVHPZUFVEHPZVFHPZUFZVGAVJVLVKVMAVHHVEAVHGTZTZHAVDVHVPS
        VIGUGUHAVPHHUIZTHAVOVQAVQHGUJVOVQSJVQHGUKUHULHUMUNUOZUPAVHHVFVRUPUQAVNV
        GOURUSUTBCGVHVHVBVAVC $.
    $}

    ${
      isabld.6 $e |- ( ( ph /\ x e. X ) -> N e. X ) $.
      isabld.7 $e |- ( ( ph /\ x e. X ) -> ( N G x ) = U ) $.
      isabld.8 $e |- ( ( ph /\ ( x e. X /\ y e. X ) )
                                            -> ( x G y ) = ( y G x ) ) $.
      $( Properties that determine an Abelian group operation.  (Changed label
         from ~ isabld to ~ isablod -NM 6-Aug-2013.)  (Contributed by Jeff
         Madsen, 5-Dec-2009.)  (New usage is discouraged.) $)
      isablod $p |- ( ph -> G e. AbelOp ) $=
        ( vn cv wcel wceq wa co wrex oveq1 eqeq1d rspcev syl2anc isabloda ) ABC
        DEQFHIJKLMABRZHSUAGHSGUIFUBZETZQRZUIFUBZETZQHUCNOUNUKQGHULGTUMUJEULGUIF
        UDUEUFUGPUH $.
    $}
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Subgroups
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c SubGrpOp $.

  $( Extend class notation to include the class of subgroups. $)
  csubgo $a class SubGrpOp $.

  $( Define the set of subgroups of ` g ` .  (Contributed by Paul Chapman,
     3-Mar-2008.)  (New usage is discouraged.) $)
  df-subgo $a |- SubGrpOp = ( g e. GrpOp |-> ( GrpOp i^i ~P g ) ) $.

  ${
    $d G g h $.  $d H h $.
    $( The predicate "is a subgroup of ` G ` ."  (Contributed by Paul Chapman,
       3-Mar-2008.)  (Revised by Mario Carneiro, 12-Jul-2014.)
       (New usage is discouraged.) $)
    issubgo $p |- ( H e. ( SubGrpOp ` G ) <->
                   ( G e. GrpOp /\ H e. GrpOp /\ H C_ G ) ) $=
      ( vg cgr wcel csubgo cfv wa wss w3a cpw cin cvv inss2 pwexg ssexg sylancr
      wceq cv pm5.32i pweq ineq2d df-subgo fvmptg mpdan eleq2d elin elpwg bitri
      syl6bb cdm dmmptss elfvdm sseldi pm4.71ri 3anass 3bitr4i ) ADEZBAFGZEZHUR
      BDEZBAIZHZHUTURVAVBJURUTVCURUTBDAKZLZEZVCURUSVEBURVEMEZUSVERURVEVDIVDMEVG
      DVDNADOVEVDMPQCADCSZKZLZVEDMFVHARVIVDDVHAUAUBCUCZUDUEUFVFVABVDEZHVCBDVDUG
      VAVLVBBADUHTUIUJTUTURUTFUKDACDVJFVKULBAFUMUNUOURVAVBUPUQ $.
  $}

  ${
    subgores.1 $e |- W = ran H $.
    $( A subgroup operation is the restriction of its parent group operation to
       its underlying set.  (Contributed by Paul Chapman, 3-Mar-2008.)
       (New usage is discouraged.) $)
    subgores $p |- ( H e. ( SubGrpOp ` G ) -> H = ( G |` ( W X. W ) ) ) $=
      ( csubgo cfv wcel cxp cres wfun wss cdm wceq cgr crn issubgo simp1bi 3syl
      wfo grpofo fofun simp3bi wf simp2bi fof fdm eqimss2 fun2ssres syl3anc wfn
      eqid fofn fnresdm 4syl eqtr2d ) BAEFGZACCHZIZBUQIZBUPAJZBAKZUQBLZKZURUSMU
      PANGZAOZVEHZVEASUTUPVDBNGZVAABPZQAVEVEUKTVFVEAUARUPVDVGVAVHUBUPUQCBUCZVBU
      QMVCUPVGUQCBSZVIUPVDVGVAVHUDZBCDTZUQCBUERUQCBUFUQVBUGRUQABUHUIUPVGVJBUQUJ
      USBMVKVLUQCBULUQBUMUNUO $.

    $( The result of a subgroup operation is the same as the result of its
       parent operation.  (Contributed by Paul Chapman, 3-Mar-2008.)  (Revised
       by Mario Carneiro, 8-Jul-2014.)  (New usage is discouraged.) $)
    subgoov $p |- ( ( H e. ( SubGrpOp ` G ) /\ ( A e. W /\ B e. W ) ) ->
                   ( A H B ) = ( A G B ) ) $=
      ( csubgo cfv wcel wa co cxp cres subgores oveqd ovres sylan9eq ) DCGHIZAE
      IBEIJABDKABCEELMZKABCKRDSABCDEFNOABEECPQ $.
  $}

  ${
    subgornss.1 $e |- X = ran G $.
    subgornss.2 $e |- W = ran H $.
    $( The underlying set of a subgroup is a subset of its parent group's
       underlying set.  (Contributed by Paul Chapman, 3-Mar-2008.)
       (New usage is discouraged.) $)
    subgornss $p |- ( H e. ( SubGrpOp ` G ) -> W C_ X ) $=
      ( csubgo cfv wcel crn cxp cima cres subgores rneqd df-ima syl6eqr imassrn
      syl6eqss 3sstr4g ) BAGHIZBJZAJZCDUAUBACCKZLZUCUAUBAUDMZJUEUABUFABCFNOAUDP
      QAUDRSFET $.
  $}

  ${
    subgoid.1 $e |- U = ( GId ` G ) $.
    subgoid.2 $e |- T = ( GId ` H ) $.
    $( The identity element of a subgroup is the same as its parent's.
       (Contributed by Paul Chapman, 3-Mar-2008.)
       (New usage is discouraged.) $)
    subgoid $p |- ( H e. ( SubGrpOp ` G ) -> T = U ) $=
      ( csubgo cfv wcel wceq co crn id cgr wss issubgo simp2bi grpoidcl syl2anc
      eqid syl subgoov grpolid eqtr3d wb simp1bi subgornss sseldd grpoid mpbird
      syl12anc ) DCGHIZABJZAACKZAJZULAADKZUNAULULADLZIZURUPUNJULMULDNIZURULCNIZ
      USDCOZCDPZQZADUQUQTZFRUAZVEAACDUQVDUBUKULUSURUPAJVCVEAADUQVDFUCSUDULUTACL
      ZIUMUOUEULUTUSVAVBUFULUQVFACDUQVFVFTZVDUGVEUHABCVFVGEUISUJ $.
  $}

  ${
    subgoinv.1 $e |- W = ran H $.
    subgoinv.2 $e |- M = ( inv ` G ) $.
    subgoinv.3 $e |- N = ( inv ` H ) $.
    $( The inverse of a subgroup element is the same as its inverse in the
       parent group.  (Contributed by Mario Carneiro, 8-Jul-2014.)
       (New usage is discouraged.) $)
    subgoinv $p |- ( ( H e. ( SubGrpOp ` G ) /\ A e. W ) ->
                    ( N ` A ) = ( M ` A ) ) $=
      ( csubgo cfv wcel wceq co cgi cgr wss eqid sylan adantr wa grporinv simpl
      issubgo simp2bi grpoinvcl subgoov syl12anc subgoid 3eqtr3d crn wb simp1bi
      simpr subgornss sselda sseldd grpoinvid1 syl3anc mpbird eqcomd ) CBJKLZAF
      LZUAZADKZAEKZVDVEVFMZAVFBNZBOKZMZVDAVFCNZCOKZVHVIVBCPLZVCVKVLMVBBPLZVMCBQ
      ZBCUDZUEZAVLCEFGVLRZIUBSVDVBVCVFFLZVKVHMVBVCUCVBVCUNVBVMVCVSVQACEFGIUFSZA
      VFBCFGUGUHVBVLVIMVCVLVIBCVIRZVRUITUJVDVNABUKZLVFWBLVGVJULVBVNVCVBVNVMVOVP
      UMTVBFWBABCFWBWBRZGUOZUPVDFWBVFVBFWBQVCWDTVTUQAVFVIBDWBWCWAHURUSUTVA $.
  $}

  ${
    $d A x y $.  $d B y $.  $d G x y $.  $d H x y $.  $d Y x y $.
    issubgoilem.1 $e |- ( ( x e. Y /\ y e. Y ) -> ( x H y ) = ( x G y ) ) $.
    $( Lemma for ~ issubgoi .  (Contributed by Paul Chapman, 25-Feb-2008.)
       (New usage is discouraged.) $)
    issubgoilem $p |- ( ( A e. Y /\ B e. Y ) -> ( A H B ) = ( A G B ) ) $=
      ( cv co wceq oveq1 eqeq12d oveq2 vtocl2ga ) AIZBIZFJZPQEJZKCQFJZCQEJZKCDF
      JZCDEJZKABCDGGPCKRTSUAPCQFLPCQELMQDKTUBUAUCQDCFNQDCENMHO $.
  $}

  ${
    $d G a b $.  $d H a b x y $.  $d H b x y z $.  $d N a b y $.
    $d U a b x y $.  $d U b x y z $.  $d Y a b x y $.  $d Y b x y z $.
    issubgoi.1 $e |- G e. GrpOp $.
    issubgoi.2 $e |- X = ran G $.
    issubgoi.3 $e |- U = ( GId ` G ) $.
    issubgoi.4 $e |- N = ( inv ` G ) $.
    issubgoi.5 $e |- Y C_ X $.
    issubgoi.6 $e |- H = ( G |` ( Y X. Y ) ) $.
    issubgoi.7 $e |- ( ( x e. Y /\ y e. Y ) -> ( x G y ) e. Y ) $.
    issubgoi.8 $e |- U e. Y $.
    issubgoi.9 $e |- ( x e. Y -> ( N ` x ) e. Y ) $.
    $( Properties that determine a subgroup.  (Contributed by Paul Chapman,
       25-Feb-2008.)  (New usage is discouraged.) $)
    issubgoi $p |- H e. ( SubGrpOp ` G ) $=
      ( wcel co wceq vz va vb csubgo cfv cgr wss cv crn cvv rnexg ax-mp eqeltri
      ssexi cxp wf wfn wral cres wfo grpofo fof xpss12 mp2an fssres feq1i mpbir
      mp2b ffn oveqi ovres syl5eq issubgoilem eqeltrd rgen2a ffnov mpbir2an w3a
      oveq1d 3adant3 sylan 3impa oveq2d 3adant1 fovcl sylan2 3impb grpoass mpan
      sseli syl3an 3eqtr4d grpolid sylancr eqtrd mpancom grpolinv isgrpoi resss
      wa eqsstri issubgo mpbir3an ) EDUDUERDUFRZEUFREDUGIABUACEAUHZFUEZHHGGDUIZ
      UJJXDXGUJRIDUFUKULUMMUNHHUOZHEUPEXHUQZXEBUHZESZHRZBHURAHURXHGEUPZXIXMXHGD
      XHUSZUPZGGUOZGDUPZXHXPUGZXOXDXPGDUTXQIDGJVAXPGDVBVHHGUGZXSXRMMHGHGVCVDXPG
      XHDVEVDXHGEXNNVFVGXHGEVIULXLABHXEHRZXJHRZWTZXKXEXJDSZHUBUCXEXJDEHUBUHZHRU
      CUHZHRWTYDYEESYDYEXNSYDYEDSEXNYDYENVJYDYEHHDVKVLZVMZOVNZVOABHHHEVPVQZXTYA
      UAUHZHRZVRZXKYJDSZYCYJDSZXKYJESZXEXJYJESZESZXTYAYMYNTYKYBXKYCYJDYGVSVTXTY
      AYKYOYMTZYBXLYKYRYHUBUCXKYJDEHYFVMWAWBYLXEYPDSZXEXJYJDSZDSZYQYNYAYKYSUUAT
      XTYAYKWTZYPYTXEDUBUCXJYJDEHYFVMWCWDXTYAYKYQYSTZUUBXTYPHRUUCXJYJHHHEYIWEUB
      UCXEYPDEHYFVMWFWGXTXEGRZYAXJGRZYKYJGRZYNUUATZHGXEMWJZHGXJMWJHGYJMWJXDUUDU
      UEUUFVRUUGIXEXJYJDGJWHWIWKWLWLPXTCXEESZCXEDSZXECHRXTUUIUUJTPUBUCCXEDEHYFV
      MWIXTXDUUDUUJXETIUUHXECDGJKWMWNWOQXTXFXEESZXFXEDSZCXFHRXTUUKUULTQUBUCXFXE
      DEHYFVMWPXTXDUUDUULCTIUUHXECDFGJKLWQWNWOWREXNDNDXHWSXADEXBXC $.
  $}

  ${
    $d G x y $.  $d H x y $.
    $( A subgroup of an Abelian group is Abelian.  (Contributed by Paul
       Chapman, 25-Apr-2008.)  (New usage is discouraged.) $)
    subgoablo $p |- ( ( G e. AbelOp /\ H e. ( SubGrpOp ` G ) )
           -> H e. AbelOp ) $=
      ( vx vy cablo wcel csubgo cfv wa cv co wceq crn wral sseld isablo subgoov
      eqid cgr adantll simpr subgornss anim12d simprbi rsp2 syl sylan9r ancom2s
      wi imp 3eqtr4d ralrimivva wss issubgo simp2bi biimpri sylan syl2anc ) AEF
      ZBAGHFZIZUTCJZDJZBKZVCVBBKZLZDBMZNCVGNZBEFZUSUTUAVAVFCDVGVGVAVBVGFZVCVGFZ
      IZIVBVCAKZVCVBAKZVDVEVAVLVMVNLZUTVLVBAMZFZVCVPFZIZUSVOUTVJVQVKVRUTVGVPVBA
      BVGVPVPRZVGRZUBZOUTVGVPVCWBOUCUSVODVPNCVPNZVSVOUIUSASFZWCCDAVPVTPUDVOCDVP
      VPUEUFUGUJUTVLVDVMLUSVBVCABVGWAQTUTVLVEVNLZUSUTVKVJWEVCVBABVGWAQUHTUKULUT
      BSFZVHVIUTWDWFBAUMABUNUOVIWFVHICDBVGWAPUPUQUR $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
             Operation properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Ass $.

  $( Extend class notation with a device to add associativity to internal
     operations. $)
  cass $a class Ass $.

  ${
    $d g x y z $.
    $( A device to add associativity to various sorts of internal operations.
       The definition is meaningful when ` g ` is a magma at least.
       (Contributed by FL, 1-Nov-2009.)  (New usage is discouraged.) $)
    df-ass $a |- Ass = { g | A. x e. dom dom g A. y e. dom dom g
    A. z e. dom dom g ( ( x g y ) g z ) = ( x g ( y g z ) ) } $.
  $}

  $c ExId $.

  $( Extend class notation with the class of all the internal operations with
     an identity element. $)
  cexid $a class ExId $.

  ${
    $d g x y $.
    $( A device to add an identity element to various sorts of internal
       operations.  (Contributed by FL, 2-Nov-2009.)
       (New usage is discouraged.) $)
    df-exid $a |- ExId = { g | E. x e. dom dom g A. y e. dom dom g
    ( ( x g y ) = y /\ ( y g x ) = y ) } $.
  $}

  ${
    $d G g x y z $.  $d X g x y z $.
    isass.1 $e |- X = dom dom G $.
    $( The predicate "is an associative operation".  (Contributed by FL,
       1-Nov-2009.)  (New usage is discouraged.) $)
    isass $p |- ( G e. A -> ( G e. Ass <-> A. x e. X A. y e. X A. z e. X
      ( ( x G y ) G z ) = ( x G ( y G z ) ) ) ) $=
      ( vg cv co wceq cdm wral wcel w3a wi wal eleq2d oveq eqtrd cass 3anbi123d
      dmeq oveq1d oveq2d eqeq12d imbi12d albidv 2albidv r3al 3bitr4g eqcomi a1i
      dmeqd raleqdv raleqbidv 2ralbidv 3bitrd df-ass elab2g ) AIZBIZHIZJZCIZVCJ
      ZVAVBVEVCJZVCJZKZCVCLZLZMBVKMAVKMZVAVBEJZVEEJZVAVBVEEJZEJZKZCFMZBFMAFMZHE
      UADVCEKZVLVQCELZLZMZBWBMZAWBMZWCBFMZAFMVSVTVAVKNZVBVKNZVEVKNZOZVIPZCQZBQA
      QVAWBNZVBWBNZVEWBNZOZVQPZCQZBQAQVLWEVTWLWRABVTWKWQCVTWJWPVIVQVTWGWMWHWNWI
      WOVTVKWBVAVTVJWAVCEUCUNZRVTVKWBVBWSRVTVKWBVEWSRUBVTVFVNVHVPVTVFVMVEVCJVNV
      TVDVMVEVCVAVBVCESUDVMVEVCESTVTVHVAVOVCJVPVTVGVOVAVCVBVEVCESUEVAVOVCESTUFU
      GUHUIVIABCVKVKVKUJVQABCWBWBWBUJUKVTWDWFAWBFWBFKVTFWBGULUMZVTWCBWBFWTUOUPV
      TWCVRABFFVTVQCWBFWTUOUQURABCHUSUT $.
  $}

  ${
    $d G g x y $.  $d X g x y $.
    isexid.1 $e |- X = dom dom G $.
    $( The predicate ` G ` has a left and right identity element.  (Contributed
       by FL, 2-Nov-2009.)  (Revised by Mario Carneiro, 22-Dec-2013.)
       (New usage is discouraged.) $)
    isexid $p |- ( G e. A -> ( G e. ExId <-> E. x e. X A. y e. X
      ( ( x G y ) = y /\ ( y G x ) = y ) ) ) $=
      ( vg cv co wceq wa cdm wral wrex cexid dmeq dmeqd syl6eqr oveq eqeq1d
      anbi12d raleqbidv rexeqbidv df-exid elab2g ) AHZBHZGHZIZUGJZUGUFUHIZUGJZK
      ZBUHLZLZMZAUONUFUGDIZUGJZUGUFDIZUGJZKZBEMZAENGDOCUHDJZUPVBAUOEVCUODLZLEVC
      UNVDUHDPQFRZVCUMVABUOEVEVCUJURULUTVCUIUQUGUFUGUHDSTVCUKUSUGUGUFUHDSTUAUBU
      CABGUDUE $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Group-like structures
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Magma $.

  $( Extend class notation with the class of all magmas. $)
  cmagm $a class Magma $.

  ${
    $d g t $.
    $( A magma is a binary internal operation.  (Contributed by FL,
       2-Nov-2009.)  (New usage is discouraged.) $)
    df-mgm $a |- Magma = { g | E. t g : ( t X. t ) --> t } $.
  $}

  ${
    $d G g t $.  $d X t $.
    ismgm.1 $e |- X = dom dom G $.
    $( The predicate "is a magma".  (Contributed by FL, 2-Nov-2009.)
       (New usage is discouraged.) $)
    ismgm $p |- ( G e. A -> ( G e. Magma <-> G : ( X X. X ) --> X ) ) $=
      ( vt vg wcel cmagm cv cdm wceq cxp wf wa wex c0 wi dmeq wb cvv exbidv f00
      feq1 df-mgm elab2g dm0 dmeqi eqtri syl6req syl adantr sylbi xpeq12 anidms
      feq23 mpancom eqeq1 imbi12d mpbiri wn fdm wne df-ne sylbir eqeq1d biimpcd
      dmxp eqcoms 3syl com12 pm2.61i pm4.71ri exbii syl6bb dmexg eqcomi xpeq12i
      feq23i ceqsexgv bitrd ) BAGZBHGZEIZBJZJZKZWCWCLZWCBMZNZEOZCCLZCBMZWAWBWHE
      OZWJWGWCFIZMZEOWMFBHAWNBKWOWHEWGWCWNBUCUAEFUDUEWHWIEWHWFWCPKZWHWFQZWPWQPP
      LZPBMZPWEKZQWSBPKZWRPKZNWTWRBUBXAWTXBXAWDPJZKZWTBPRXDWEXCJZPWDXCRXEXCPXCP
      UFUGUFUHUIUJUKULWPWHWSWFWTWGWRKZWPWHWSSWPXFWCPWCPUMUNWGWCWRPBUOUPWCPWEUQU
      RUSWHWPUTZWFWHWDWGKWEWGJZKXGWFQZWGWCBVAWDWGRXIXHWEXGXHWEKWFXGXHWCWEXGWCPV
      BXHWCKWCPVCWCWCVGVDVEVFVHVIVJVKVLVMVNWAWDTGWETGWJWLSBAVOWDTVOWHWLEWETWFWH
      WEWELZWEBMZWLWGXJKZWFWHXKSWFXLWCWEWCWEUMUNWGWCXJWEBUOUPXJWEWKCBWECWECCWED
      VPZXMVQXMVRVNVSVIVT $.
  $}

  ${
    clmgm.1 $e |- X = dom dom G $.
    $( Closure of a magma.  (Contributed by FL, 14-Sep-2010.)
       (New usage is discouraged.) $)
    clmgm $p |- ( ( G e. Magma /\ A e. X /\ B e. X ) -> ( A G B ) e. X ) $=
      ( cmagm wcel co wi cxp wf ismgm fovrn 3exp syl6bi pm2.43i 3imp ) CFGZADGZ
      BDGZABCHDGZRSTUAIIZRRDDJDCKZUBFCDELUCSTUAABDDDCMNOPQ $.
  $}

  ${
    $d G u x y $.  $d X u x y $.
    opidon.1 $e |- X = dom dom G $.
    $( An operation with a left and right identity element is onto.
       (Contributed by FL, 2-Nov-2009.)  (Revised by Mario Carneiro,
       22-Dec-2013.)  (New usage is discouraged.) $)
    opidon $p |- ( G e. ( Magma i^i ExId ) ->
      G : ( X X. X ) -onto-> X ) $=
      ( vy vu vx cmagm cexid cin wcel cxp wf cv co wceq wrex wral wfo sseli syl
      inss1 ismgm ibi wa inss2 isexid biimpd sylc simpl ralimi oveq2 id eqeq12d
      rspcv eqeq1d syl5bb rspcev ex syld syl5 reximdv impcom ralrimiva sylanbrc
      eqcom foov ) AGHIZJZBBKZBALZDMZEMZFMZANZOZFBPZEBPZDBQZVIBARVHAGJZVJVGGAGH
      UASVSVJGABCUBUCTVHVNVMOZVMVLANVMOZUDZFBQZEBPZVRVHAHJZWEWDVGHAGHUESZWFWEWE
      WDEFHABCUFUGUHWDVQDBVKBJZWDVQWGWCVPEBWCVTFBQZWGVPWBVTFBVTWAUIUJWGWHVLVKAN
      ZVKOZVPVTWJFVKBVMVKOZVNWIVMVKVMVKVLAUKZWKULUMUNWGWJVPVOWJFVKBVOVNVKOWKWJV
      KVNVEWKVNWIVKWLUOUPUQURUSUTVAVBVCTEFDBBBAVFVD $.
  $}

  $( Range of an operation with a left and right identity element.
     (Contributed by FL, 2-Nov-2009.)  (New usage is discouraged.) $)
  rngopid $p |- ( G e. ( Magma i^i ExId ) -> ran G = dom dom G ) $=
    ( cmagm cexid cin wcel cdm cxp wfo crn wceq eqid opidon forn syl ) ABCDEAFF
    ZOGZOAHAIOJAOOKLPOAMN $.

  ${
    opidon2.1 $e |- X = ran G $.
    $( An operation with a left and right identity element is onto.
       (Contributed by FL, 2-Nov-2009.)  (New usage is discouraged.) $)
    opidon2 $p |- ( G e. ( Magma i^i ExId ) ->
      G : ( X X. X ) -onto-> X ) $=
      ( cmagm cexid cin wcel cdm cxp wfo eqid opidon wceq crn syl5req wb xpeq12
      forn anidms syl foeq2 foeq3 bitrd biimpd mpcom ) ADEFGAHHZUFIZUFAJZBBIZBA
      JZAUFUFKLUFBMZUHUJUHBANUFCUGUFAROUKUHUJUKUHUIUFAJZUJUKUGUIMZUHULPUKUMUFBU
      FBQSUGUIUFAUATUFBUIAUBUCUDUET $.

  $}

  ${
    $d G u x $.  $d X u x $.
    isexid2.1 $e |- X = ran G $.
    $( If ` G e. ( Magma i^i ExId ) ` , then it has a left and right identity
       element that belongs to the range of the operation.  (Contributed by FL,
       12-Dec-2009.)  (Revised by Mario Carneiro, 22-Dec-2013.)
       (New usage is discouraged.) $)
    isexid2 $p |- ( G e. ( Magma i^i ExId ) -> E. u e. X A. x e. X
      ( ( u G x ) = x /\ ( x G u ) = x ) ) $=
      ( crn wceq cmagm cexid cin wcel cv co wa wral wrex cdm raleq rexeqbi1dv
      wi rngopid elin isexid ibi adantl sylbi eqeq2 imbi12d syl5ibr mpcom com12
      eqid a1d sylibrd ax-mp ) DCFZGZCHIJKZBLZALZCMUTGUTUSCMUTGNZADOZBDPZTEUQUR
      VAAUPOZBUPPZVCURUQVEUPCQQZGZURUQVETZCUAURVHVGDVFGZVAAVFOZBVFPZTZURCHKZCIK
      ZNVLCHIUBVNVLVMVNVKVIVNVKBAICVFVFULUCUDUMUEUFVGUQVIVEVKUPVFDUGVDVJBUPVFVA
      AUPVFRSUHUIUJUKVBVDBDUPVAADUPRSUNUO $.
  $}

  ${
    $d G u x y $.  $d X u x y $.
    exidu1.1 $e |- X = ran G $.
    $( Unicity of the left and right identity element of a magma when it
       exists.  (Contributed by FL, 12-Dec-2009.)  (Revised by Mario Carneiro,
       22-Dec-2013.)  (New usage is discouraged.) $)
    exidu1 $p |- ( G e. ( Magma i^i ExId ) ->
      E! u e. X A. x e. X ( ( u G x ) = x /\ ( x G u ) = x ) ) $=
      ( vy wcel cv co wceq wa wral weq ralimi oveq2 id eqeq12d rspcv syl5 oveq1
      cmagm cexid cin wrex wreu isexid2 simpl simpr im2anan9r eqtr2 eqcomd syl6
      wi rgen2a a1i eqeq1d anbi12d ralbidv reu4 sylanbrc ) CUAUBUCGZBHZAHZCIZVC
      JZVCVBCIZVCJZKZADLZBDUDVIFHZVCCIZVCJZVCVJCIZVCJZKZADLZKZBFMZUMZFDLBDLZVIB
      DUEABCDEUFVTVAVSBFDVBDGZVJDGZKVQVBVJCIZVJJZWCVBJZKZVRWBVIWDWAVPWEVIVEADLW
      BWDVHVEADVEVGUGNVEWDAVJDAFMZVDWCVCVJVCVJVBCOWGPQRSVPVNADLWAWEVOVNADVLVNUH
      NVNWEAVBDABMZVMWCVCVBVCVBVJCTWHPQRSUIWFVJVBWCVJVBUJUKULUNUOVIVPBFDVRVHVOA
      DVRVEVLVGVNVRVDVKVCVBVJVCCTUPVRVFVMVCVBVJVCCOUPUQURUSUT $.
  $}

  ${
    $d G u x $.  $d X u x $.
    idrval.1 $e |- X = ran G $.
    idrval.2 $e |- U = ( GId ` G ) $.
    $( The value of the identity element.  (Contributed by FL, 12-Dec-2009.)
       (Revised by Mario Carneiro, 22-Dec-2013.)
       (New usage is discouraged.) $)
    idrval $p |- ( G e. A -> U = ( iota_ u e. X
                   A. x e. X ( ( u G x ) = x /\ ( x G u ) = x ) ) ) $=
      ( wcel cgi cfv cv co wceq wa wral crio gidval syl5eq ) ECIDEJKBLZALZEMUAN
      UATEMUANOAFPBFQHABECFGRS $.
  $}

  ${
    $d G u x $.  $d X u x $.
    iorlid.1 $e |- X = ran G $.
    iorlid.2 $e |- U = ( GId ` G ) $.
    $( A magma right and left identity belongs to the underlying set of the
       operation.  (Contributed by FL, 12-Dec-2009.)  (Revised by Mario
       Carneiro, 22-Dec-2013.)  (New usage is discouraged.) $)
    iorlid $p |- ( G e. ( Magma i^i ExId ) -> U e. X ) $=
      ( vu vx cmagm cexid cin wcel cv co wceq wa wral crio idrval wreu exidu1
      riotacl syl eqeltrd ) BHIJZKZAFLZGLZBMUGNUGUFBMUGNOGCPZFCQZCGFUDABCDERUEU
      HFCSUICKGFBCDTUHFCUAUBUC $.
  $}

  ${
    $d A x $.  $d G u x y $.  $d U u x y $.  $d X u x y $.
    cmpidelt.1 $e |- X = ran G $.
    cmpidelt.2 $e |- U = ( GId ` G ) $.
    $( A magma right and left identity element keeps the other elements
       unchanged.  (Contributed by FL, 12-Dec-2009.)  (Revised by Mario
       Carneiro, 22-Dec-2013.)  (New usage is discouraged.) $)
    cmpidelt $p |- ( ( G e. ( Magma i^i ExId ) /\ A e. X ) ->
      ( ( U G A ) = A /\ ( A G U ) = A ) ) $=
      ( vx vu cmagm wcel cv co wceq wa wral oveq1 eqeq1d oveq2 anbi12d eqeq12d
      cexid cin crio idrval eqcomd wreu wb iorlid exidu1 ralbidv riota2 syl2anc
      mpbird id rspccva sylan ) CIUAUBZJZBGKZCLZUSMZUSBCLZUSMZNZGDOZADJBACLZAMZ
      ABCLZAMZNZURVEHKZUSCLZUSMZUSVKCLZUSMZNZGDOZHDUCZBMZURBVRGHUQBCDEFUDUEURBD
      JVQHDUFVEVSUGBCDEFUHGHCDEUIVQVEHDBVKBMZVPVDGDVTVMVAVOVCVTVLUTUSVKBUSCPQVT
      VNVBUSVKBUSCRQSUJUKULUMVDVJGADUSAMZVAVGVCVIWAUTVFUSAUSABCRWAUNZTWAVBVHUSA
      USABCPWBTSUOUP $.
  $}

  $c SemiGrp $.

  $( Extend class notation with the class of all semi-groups. $)
  csem $a class SemiGrp $.

  $( A semi-group is an associative magma.  (Contributed by FL, 2-Nov-2009.)
     (New usage is discouraged.) $)
  df-sgr $a |- SemiGrp = ( Magma i^i Ass ) $.

  $( A semi-group is a magma.  (Contributed by FL, 2-Nov-2009.)
     (New usage is discouraged.) $)
  smgrpismgm $p |- ( G e. SemiGrp -> G e. Magma ) $=
    ( cmagm wcel cass cin csem elin simplbi df-sgr eleq2s ) ABCZABDEZFALCKADCAB
    DGHIJ $.

  $( A semi-group is associative.  (Contributed by FL, 2-Nov-2009.)
     (New usage is discouraged.) $)
  smgrpisass $p |- ( G e. SemiGrp -> G e. Ass ) $=
    ( cass wcel cmagm cin csem elin simprbi df-sgr eleq2s ) ABCZADBEZFALCADCKAD
    BGHIJ $.

  ${
    $d G x y z $.  $d X x y z $.
    issmgrp.1 $e |- X = dom dom G $.
    $( The predicate "is a semi-group".  (Contributed by FL, 2-Nov-2009.)
       (New usage is discouraged.) $)
    issmgrp $p |- ( G e. A -> ( G e. SemiGrp
       <-> ( G : ( X X. X ) --> X /\ A. x e. X A. y e. X A. z e. X
         ( ( x G y ) G z ) = ( x G ( y G z ) ) ) ) ) $=
      ( csem wcel cmagm cass cin cxp wf cv co wceq wral wa syl5bb df-sgr eleq2i
      elin ismgm isass anbi12d ) EHIEJKLZIZEDIZFFMFENZAOZBOZEPCOZEPUKULUMEPEPQC
      FRBFRAFRZSZHUGEUAUBUHEJIZEKIZSUIUOEJKUCUIUPUJUQUNDEFGUDABCDEFGUEUFTT $.
  $}

  ${
    $d G x y z $.  $d X x y z $.
    smgrpmgm.1 $e |- X = dom dom G $.
    $( A semi-group is a magma.  (Contributed by FL, 2-Nov-2009.)
       (New usage is discouraged.) $)
    smgrpmgm $p |- ( G e. SemiGrp -> G : ( X X. X ) --> X ) $=
      ( vx vy vz csem wcel cxp wf cv co wceq wral issmgrp simpl syl6bi pm2.43i
      wa ) AGHZBBIBAJZTTUADKZEKZALFKZALUBUCUDALALMFBNEBNDBNZSUADEFGABCOUAUEPQR
      $.
  $}

  ${
    $d G x y z $.  $d X x y z $.
    smgrpass.1 $e |- X = dom dom G $.
    $( A semi-group is associative.  (Contributed by FL, 2-Nov-2009.)
       (New usage is discouraged.) $)
    smgrpass $p |- ( G e. SemiGrp ->
      A. x e. X A. y e. X A. z e. X ( ( x G y ) G z ) = ( x G ( y G z ) ) ) $=
      ( csem wcel cv co wceq wral cxp wf wa issmgrp simpr syl6bi pm2.43i ) DGHZ
      AIZBIZDJCIZDJUAUBUCDJDJKCELBELAELZTTEEMEDNZUDOUDABCGDEFPUEUDQRS $.
  $}

  $c MndOp $.

  $( Extend class notation with the class of all monoids. $)
  cmndo $a class MndOp $.

  $( A monoid is a semi-group with an identity element.  (Contributed by FL,
     2-Nov-2009.)  (New usage is discouraged.) $)
  df-mndo $a |- MndOp = ( SemiGrp i^i ExId ) $.

  $( A monoid is a semi-group.  (Contributed by FL, 2-Nov-2009.)
     (New usage is discouraged.) $)
  mndoissmgrp $p |- ( G e. MndOp -> G e. SemiGrp ) $=
    ( csem wcel cexid cin cmndo elin simplbi df-mndo eleq2s ) ABCZABDEZFALCKADC
    ABDGHIJ $.

  $( A monoid has an identity element.  (Contributed by FL, 2-Nov-2009.)
     (New usage is discouraged.) $)
  mndoisexid $p |- ( G e. MndOp -> G e. ExId ) $=
    ( cexid wcel csem cin cmndo elin simprbi df-mndo eleq2s ) ABCZADBEZFALCADCK
    ADBGHIJ $.

  $( A monoid is a magma.  (Contributed by FL, 2-Nov-2009.)
     (New usage is discouraged.) $)
  mndoismgm $p |- ( G e. MndOp -> G e. Magma ) $=
    ( cmndo wcel csem cmagm mndoissmgrp smgrpismgm syl ) ABCADCAECAFAGH $.

  $( A monoid is a magma with an identity element.  (Contributed by FL,
     18-Feb-2010.)  (New usage is discouraged.) $)
  mndomgmid $p |- ( G e. MndOp -> G e. ( Magma i^i ExId ) ) $=
    ( cmndo wcel cmagm cexid cin mndoismgm mndoisexid elin sylanbrc ) ABCADCAEC
    ADEFCAGAHADEIJ $.

  ${
    $d G x y $.  $d X x y $.
    ismndo.1 $e |- X = dom dom G $.
    $( The predicate "is a monoid".  (Contributed by FL, 2-Nov-2009.)  (Revised
       by Mario Carneiro, 22-Dec-2013.)  (New usage is discouraged.) $)
    ismndo $p |- ( G e. A -> ( G e. MndOp
     <-> ( G e. SemiGrp /\ E. x e. X A. y e. X
      ( ( x G y ) = y /\ ( y G x ) = y ) ) ) ) $=
      ( cmndo wcel csem cexid cin cv co wceq wa wral wrex df-mndo eleq2i syl5bb
      elin isexid anbi2d ) DGHDIJKZHZDCHZDIHZALZBLZDMUINUIUHDMUINOBEPAEQZOZGUDD
      RSUEUGDJHZOUFUKDIJUAUFULUJUGABCDEFUBUCTT $.
  $}

  ${
    $d G x y z $.  $d X x y z $.
    ismndo1.1 $e |- X = dom dom G $.
    $( The predicate "is a monoid".  (Contributed by FL, 2-Nov-2009.)  (Revised
       by Mario Carneiro, 22-Dec-2013.)  (New usage is discouraged.) $)
    ismndo1 $p |- ( G e. A -> ( G e. MndOp <->
      ( G : ( X X. X ) --> X /\
        A. x e. X A. y e. X A. z e. X
          ( ( x G y ) G z ) = ( x G ( y G z ) ) /\
        E. x e. X A. y e. X
         ( ( x G y ) = y /\ ( y G x ) = y ) ) ) ) $=
      ( wcel cmndo csem cv co wceq wa wral wrex cxp wf w3a ad2antrl ismndo 3jca
      smgrpmgm smgrpass simprr 3simpa issmgrp syl5ibr imp simpr3 impbida bitrd
      jca ) EDHZEIHEJHZAKZBKZELZUQMUQUPELUQMNBFOAFPZNZFFQFERZURCKZELUPUQVBELELM
      CFOBFOAFOZUSSZABDEFGUAUNUTVDUNUTNVAVCUSUOVAUNUSEFGUCTUOVCUNUSABCEFGUDTUNU
      OUSUEUBUNVDNUOUSUNVDUOVDUOUNVAVCNVAVCUSUFABCDEFGUGUHUIUNVAVCUSUJUMUKUL $.
  $}

  ${
    $d G x y z $.  $d X x y z $.
    ismndo2.1 $e |- X = ran G $.
    $( The predicate "is a monoid".  (Contributed by FL, 2-Nov-2009.)  (Revised
       by Mario Carneiro, 22-Dec-2013.)  (New usage is discouraged.) $)
    ismndo2 $p |- ( G e. A -> ( G e. MndOp <->
      ( G : ( X X. X ) --> X /\
        A. x e. X A. y e. X A. z e. X
          ( ( x G y ) G z ) = ( x G ( y G z ) ) /\
        E. x e. X A. y e. X
         ( ( x G y ) = y /\ ( y G x ) = y ) ) ) ) $=
      ( wcel cdm wceq cxp wf cv co wral wrex w3a wi a1i wb cmndo wa cmagm cexid
      crn cin mndomgmid rngopid syl syl5eq dmxpid syl6req 3ad2ant1 eqid ismndo1
      fdm dmeqd xpid11 biimpri feq23 mpancom raleq raleqbi1dv rexeqbi1dv bibi2d
      3anbi123d syl5ibrcom pm5.21ndd ) EDHZFEIZIZJZEUAHZFFKZFELZAMZBMZENZCMZENV
      PVQVSENENJZCFOZBFOZAFOZVRVQJVQVPENVQJUBZBFOZAFPZQZVMVLRVIVMFEUEZVKGVMEUCU
      DUFHWHVKJEUGEUHUIUJSWGVLRVIVOWCVLWFVOVKVNIFVOVJVNVNFEUPUQFUKULUMSVIVMWGTV
      LVMVKVKKZVKELZVTCVKOZBVKOZAVKOZWDBVKOZAVKPZQZTABCDEVKVKUNUOVLWGWPVMVLVOWJ
      WCWMWFWOVNWIJZVLVOWJTWQVLFVKURUSVNFWIVKEUTVAWBWLAFVKWAWKBFVKVTCFVKVBVCVCW
      EWNAFVKWDBFVKVBVDVFVEVGVH $.
  $}

  ${
    $d G w x y z $.
    $( A group is a monoid.  (Contributed by FL, 2-Nov-2009.)  (Revised by
       Mario Carneiro, 22-Dec-2013.)  (New usage is discouraged.) $)
    grpomndo $p |- ( G e. GrpOp -> G e. MndOp ) $=
      ( vx vy vz vw cgr wcel cmndo crn cxp wf cv co wceq wral wrex wa w3a eqid
      wi isgrpo biimpd grpoidinv simpl ralimi reximi biimprcd 3exp impcom com3l
      ismndo2 syl mpcom exp3acom3r a1i com13 3imp syli pm2.43i ) AFGZAHGZUTUTAI
      ZVBJVBAKZBLZCLZAMZDLZAMVDVEVGAMAMNDVBOCVBOBVBOZELZVDAMVDNVEVDAMZVINCVBPQB
      VBOEVBPZRZVAUTUTVLBCDEFAVBVBSZUAUBVCVHVKUTVATZVKVHVCVNVHVCVNTTVKUTVHVCVAV
      FVENVJVENQZVIVEAMVDNVEVIAMVDNQEVBPZQZCVBOZBVBPZUTVHVCQZVATZCEBAVBVMUCVSVO
      CVBOZBVBPZUTWATVRWBBVBVQVOCVBVOVPUDUEUFVTWCUTVAVCVHWCVNTVCVHWCVNUTVAVCVHW
      CRBCDFAVBVMUKUGUHUIUJULUMUNUOUPUQURUS $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                     Examples of Abelian groups
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d u x y z A $.
    ablsn.1 $e |- A e. _V $.
    $( The Abelian group operation for the singleton group.  (Contributed by
       NM, 5-Nov-2006.)  (New usage is discouraged.) $)
    ablosn $p |- { <. <. A , A >. , A >. } e. AbelOp $=
      ( vx vy cop csn grposn cdm cxp dmsnop xpsn eqtr4i cv wcel wceq co elsn wa
      oveq12 oveq2 oveq1 sylan9eq eqtr4d syl2anb isabloi ) CDAAEZAEFZAFZABGUGHU
      FFUHUHIUFABJAABBKLCMZUHNUIAOZDMZAOZUIUKUGPZUKUIUGPZOUKUHNCAQDAQUJULRUMAAU
      GPZUNUIAUKAUGSUJULUNUKAUGPUOUIAUKUGTUKAAUGUAUBUCUDUE $.

    $( The identity element of the trivial group.  (Contributed by FL,
       21-Jun-2010.)  (Proof shortened by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    gidsn $p |- ( GId ` { <. <. A , A >. , A >. } ) = A $=
      ( cop csn cgr wcel cgi wceq grposn opex rnsnop eqcomi eqid grpoidcl elsni
      cfv crn mp2b ) AACZACDZEFTGPZADZFUAAHABIUATUBTQUBSAAAJKLUAMNUAAOR $.

    $( The inverse function of the trivial group.  (Contributed by FL,
       21-Jun-2010.)  (Proof shortened by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    ginvsn $p |- ( inv ` { <. <. A , A >. , A >. } ) = ( _I |` { A } ) $=
      ( cid cfv cop csn cres cgn cvv wcel wceq fvi ax-mp opeq2i sneqi wf1o f1of
      wfn wf mp2b f1ovi ffn fnressn mp2an cgr grposn crn rnsnop eqcomi grpoinvf
      opex eqid fsn mpbi 3eqtr4ri ) AACDZEZFZAAEZFZCAFZGZUSAEFZHDZUQUSUPAAAIJZU
      PAKBAILMNOCIRZVEVBURKIICPIICSVFUAIICQIICUBTBIACUCUDVAVAVDSZVDUTKVCUEJVAVA
      VDPVGABUFVCVDVAVCUGVAUSAAAUKUHUIVDULUJVAVAVDQTAAVDBBUMUNUO $.
  $}

  ${
    $d x y z A $.
    $( Complex number addition is an Abelian group operation.  (Contributed by
       NM, 5-Nov-2006.)  (New usage is discouraged.) $)
    cnaddablo $p |- + e. AbelOp $=
      ( vx vy vz caddc cc cc0 cv cneg cnex ax-addf addass 0cn addid2 negcl wcel
      co wceq addcom mpdan negid eqtr3d isgrpoi cxp fdmi isabloi ) ABDEABCFDAGZ
      HZEIJUFBGZCGKLUFMUFNZUFEOZUFUGDPZUGUFDPZFUJUGEOUKULQUIUFUGRSUFTUAUBEEUCED
      JUDUFUHRUE $.

    $( The group identity element of complex number addition is zero.
       (Contributed by Steve Rodriguez, 3-Dec-2006.)  (Revised by Mario
       Carneiro, 21-Dec-2013.)  (New usage is discouraged.) $)
    cnid $p |- 0 = ( GId ` + ) $=
      ( vy vx caddc cgi cfv cv co wceq cc wral crio cc0 cgr wcel cablo ablogrpo
      cnaddablo ax-mp cxp ax-addf fdmi grporn eqid grpoidval addid2 rgen wb 0cn
      wreu grpoideu oveq1 eqeq1d ralbidv riota2 mp2an mpbi eqtr2i ) CDEZAFZBFZC
      GZUTHZBIJZAIKZLCMNZURVDHCONVEQCPRZBAURCICIVFIISICTUAUBZURUCUDRLUTCGZUTHZB
      IJZVDLHZVIBIUTUEUFLINVCAIUIZVJVKUGUHVEVLVFBACIVGUJRVCVJAILUSLHZVBVIBIVMVA
      VHUTUSLUTCUKULUMUNUOUPUQ $.

    $( Value of the group inverse of complex number addition.  (Contributed by
       Steve Rodriguez, 3-Dec-2006.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.) $)
    addinv $p |- ( A e. CC -> ( ( inv ` + ) ` A ) = -u A ) $=
      ( vy cc wcel caddc cgn cfv cv co cc0 wceq crio cneg cgr cablo mpan eqeq1d
      0cn wreu mpbid cnaddablo ablogrpo ax-mp cxp ax-addf fdmi grporn cnid eqid
      grpoinvval cmin df-neg oveq1i npcan syl5eq wb negcl negeu mpan2 wa addcom
      reubidva oveq1 riota2 syl2anc eqtrd ) ACDZAEFGZGZBHZAEIZJKZBCLZAMZENDZVGV
      IVMKEODVOUAEUBUCZBAJEVHCECVPCCUDCEUEUFUGUHVHUIUJPVGVNAEIZJKZVMVNKZVGVQJAU
      KIZAEIZJVNVTAEAULUMJCDZVGWAJKRJAUNPUOVGVNCDVLBCSZVRVSUPAUQVGAVJEIZJKZBCSZ
      WCVGWBWFRBAJURUSVGWEVLBCVGVJCDUTWDVKJAVJVAQVBTVLVRBCVNVJVNKVKVQJVJVNAEVCQ
      VDVETVF $.

    $( The real numbers under addition comprise a subgroup of the complex
       numbers under addition.  (Contributed by Paul Chapman, 25-Apr-2008.)
       (New usage is discouraged.) $)
    readdsubgo $p |- ( + |` ( RR X. RR ) ) e. ( SubGrpOp ` + ) $=
      ( vx vy cc0 caddc cr cxp cres cgn cfv cablo wcel cnaddablo ablogrpo ax-mp
      cc cgr ax-addf fdmi eqid cv grporn cnid ax-resscn readdcl 0re cneg addinv
      wceq recn syl renegcl eqeltrd issubgoi ) ABCDDEEFGZDHIZOEDJKDPKLDMNZDOUPO
      OFODQRUAUBUOSUCUNSATZBTUDUEUQEKZUQUOIZUQUFZEURUQOKUSUTUHUQUIUQUGUJUQUKULU
      M $.

    $( The integers under addition comprise a subgroup of the complex numbers
       under addition.  (Contributed by Paul Chapman, 25-Apr-2008.)
       (New usage is discouraged.) $)
    zaddsubgo $p |- ( + |` ( ZZ X. ZZ ) ) e. ( SubGrpOp ` + ) $=
      ( vx vy cc0 caddc cz cxp cres cgn cfv cablo wcel cnaddablo ablogrpo ax-mp
      cc cgr ax-addf fdmi eqid cv grporn cnid zsscn zaddcl cneg wceq zcn addinv
      0z syl znegcl eqeltrd issubgoi ) ABCDDEEFGZDHIZOEDJKDPKLDMNZDOUPOOFODQRUA
      UBUOSUCUNSATZBTUDUIUQEKZUQUOIZUQUEZEURUQOKUSUTUFUQUGUQUHUJUQUKULUM $.

    $( Nonzero complex number multiplication is an Abelian group operation.
       (Contributed by Steve Rodriguez, 12-Feb-2007.)
       (New usage is discouraged.) $)
    ablomul $p |- ( x. |` ( ( CC \ { 0 } ) X. ( CC \ { 0 } ) ) ) e. AbelOp $=
      ( vx vy vz cmul cc cc0 c1 cv co cvv wcel mulnzcnopr wa wceq ovres eldifsn
      wne jca sylibr eldifi csn cdif cres cdiv cnex difexg ax-mp mulcl ad2ant2r
      cxp w3a mulne0 syl2anb eqeltrd anim1i 3adant3 oveq1d mulass syl3an eqcomd
      3impa syl 3adant1 oveq2d fovcl sylan2 3impb 3eqtr3d 3eqtrd ax-1cn ax-1ne0
      eqeltrrd mpbir2an mulid2d eqtrd reccl recne0 sylbi mpancom recid2 isgrpoi
      mpan fdmi mulcom syl2an ancoms 3eqtr4d isabloi ) ABDEFUAZUBZWJUJZUCZWJABC
      GWLGAHZUDIZWJEJKWJJKUEEWIJUFUGLWMWJKZBHZWJKZCHZWJKZUKZWMWPWLIZWRWLIZXAWRD
      IZWMWPDIZWRDIZWMWPWRWLIZWLIZWTXAWJKZWSMZXBXCNWOWQWSXIWOWQMZXHWSXJXAXDWJWM
      WPWJWJDOZXJXDEKZXDFQZMZXDWJKWOWMEKZWMFQZMZWPEKZWPFQZMZXNWQWMEFPZWPEFPXQXT
      MXLXMXOXRXLXPXSWMWPUHUIWMWPULRUMXDEFPSUNUOVAXAWRWJWJDOVBWTXAXDWRDWOWQXAXD
      NWSXKUPUQWTXEWMWPWRDIZDIZWMXFDIZXGWOXOWQXRWSWREKXEYCNWMEWITZWPEWITZWREWIT
      WMWPWRURUSWTYBXFWMDWQWSYBXFNWOWQWSMZXFYBWPWRWJWJDOZUTVCZVDZWTYCWMYBWLIZYD
      XGWOWQWSYCYKNZYGWOYBWJKZYLYGXFYBWJYHWPWRWJWJWJWLLVEVLWOYMMYKYCWMYBWJWJDOU
      TVFVGYJWTYBXFWMWLYIVDVHVIVIGWJKZGEKGFQVJVKGEFPVMZWOGWMWLIZGWMDIZWMYNWOYPY
      QNYOGWMWJWJDOWBWOWMYEVNVOWOWNEKZWNFQZMZWNWJKZWOXQYTYAXQYRYSWMVPWMVQRVRWNE
      FPSZWOWNWMWLIZWNWMDIZGUUAWOUUCUUDNUUBWNWMWJWJDOVSWOXQUUDGNYAWMVTVRVOWAWKW
      JWLLWCXJXDWPWMDIZXAWPWMWLIZWOXOXRXDUUENWQYEYFWMWPWDWEXKWQWOUUFUUENWPWMWJW
      JDOWFWGWH $.

    $( The group identity element of nonzero complex number multiplication is
       one.  (Contributed by Steve Rodriguez, 23-Feb-2007.)  (Revised by Mario
       Carneiro, 17-Dec-2013.)  (New usage is discouraged.) $)
    mulid $p |- ( GId ` ( x. |` ( ( CC \ { 0 } ) X. ( CC \ { 0 } ) ) ) ) = 1 $=
      ( vy vx cmul cc cc0 csn cdif cxp cres cgi cfv cv co wceq wral crio c1 cgr
      wcel ax-mp cablo ablomul ablogrpo mulnzcnopr fdmi grporn grpoidval ax-1cn
      eqid wne ax-1ne0 eldifsn mpbir2an ovres mpan eldifi mulid2d eqtrd rgen wb
      wreu grpoideu oveq1 eqeq1d ralbidv riota2 mp2an mpbi eqtri ) CDEFZGZVKHZI
      ZJKZALZBLZVMMZVPNZBVKOZAVKPZQVMRSZVNVTNVMUASWAUBVMUCTZBAVNVMVKVMVKWBVLVKV
      MUDUEUFZVNUIUGTQVPVMMZVPNZBVKOZVTQNZWEBVKVPVKSZWDQVPCMZVPQVKSZWHWDWINWJQD
      SQEUJUHUKQDEULUMZQVPVKVKCUNUOWHVPVPDVJUPUQURUSWJVSAVKVAZWFWGUTWKWAWLWBBAV
      MVKWCVBTVSWFAVKQVOQNZVRWEBVKWMVQWDVPVOQVPVMVCVDVEVFVGVHVI $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Group homomorphism and isomorphism
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c GrpOpHom $.

  $( Extend class notation to include the class of group homomorphisms. $)
  cghom $a class GrpOpHom $.

  ${
    $d f g h s x y $.
    $( Define the set of group homomorphisms from ` g ` to ` h ` .
       (Contributed by Paul Chapman, 25-Feb-2008.)
       (New usage is discouraged.) $)
    df-ghom $a |- GrpOpHom = ( g e. GrpOp , h e. GrpOp |->
        { f | ( f : ran g --> ran h /\ A. x e. ran g A. y e. ran g
                     ( ( f ` x ) h ( f ` y ) ) = ( f ` ( x g y ) ) ) } ) $.
  $}

  $c GrpOpIso $.

  $( Extend class notation to include the class of group isomorphisms. $)
  cgiso $a class GrpOpIso $.

  ${
    $d f g h s $.
    $( Define the set of group isomorphisms from ` g ` to ` h ` .  (Contributed
       by Paul Chapman, 25-Feb-2008.)  (New usage is discouraged.) $)
    df-giso $a |- GrpOpIso = ( g e. GrpOp , h e. GrpOp |->
        { f e. ( g GrpOpHom h ) | f : ran g -1-1-onto-> ran h } ) $.
  $}

  ${
    $d f x y F $.  $d f g h x y G $.  $d f g h x y H $.  $d g h S $.
    elghomlem1.1 $e |- S = { f | ( f : ran G --> ran H /\ A. x e. ran G
      A. y e. ran G ( ( f ` x ) H ( f ` y ) ) = ( f ` ( x G y ) ) ) } $.
    $( Lemma for ~ elghom .  (Contributed by Paul Chapman, 25-Feb-2008.)
       (New usage is discouraged.) $)
    elghomlem1 $p |- ( ( G e. GrpOp /\ H e. GrpOp )
        -> ( G GrpOpHom H ) = S ) $=
      ( vg vh cgr wcel cvv co wceq crn cv cfv wral wf wa cghom rnexg fabexg cab
      syl2an rneq feq2d oveq fveq2d eqeq2d raleqbidv anbi12d abbidv wb feq3 syl
      eqeq1d 2ralbidv syl6eqr df-ghom ovmpt2g mpd3an3 ) EJKZFJKZCLKZEFUAMCNVCEO
      ZLKFOZLKVEVDEJUBFJUBAPZDPZQZBPZVIQZFMZVHVKEMZVIQZNZBVFRAVFRZDVFVGLLCGUCUE
      HIEFJJHPZOZIPZOZVISZVJVLVTMZVHVKVRMZVIQZNZBVSRZAVSRZTZDUDCUAVFWAVISZWCVON
      ZBVFRZAVFRZTZDUDZLVRENZWIWNDWPWBWJWHWMWPVSVFWAVIVREUFZUGWPWGWLAVSVFWQWPWF
      WKBVSVFWQWPWEVOWCWPWDVNVIVHVKVREUHUIUJUKUKULUMVTFNZWOVFVGVISZVQTZDUDCWRWN
      WTDWRWJWSWMVQWRWAVGNWJWSUNVTFUFWAVGVFVIUOUPWRWKVPABVFVFWRWCVMVOVJVLVTFUHU
      QURULUMGUSABDHIUTVAVB $.

    $( Lemma for ~ elghom .  (Contributed by Paul Chapman, 25-Feb-2008.)
       (New usage is discouraged.) $)
    elghomlem2 $p |- ( ( G e. GrpOp /\ H e. GrpOp ) -> ( F e. ( G GrpOpHom H )
    <-> ( F : ran G --> ran H /\ A. x e. ran G A. y e. ran G
          ( ( F ` x ) H ( F ` y ) ) = ( F ` ( x G y ) ) ) ) ) $=
      ( cgr wcel wa co crn wf cv cfv wceq wral cvv fveq1 elghomlem1 eleq2d elex
      cghom wb feq1 oveq12d eqeq12d 2ralbidv anbi12d elab2g biimpd mpcom wi fex
      rnexg expcom syl adantrd biimprd syli impbid2 adantr bitrd ) FIJZGIJZKZEF
      GUDLZJECJZFMZGMZENZAOZEPZBOZEPZGLZVMVOFLZEPZQZBVJRAVJRZKZVGVHCEABCDFGHUAU
      BVEVIWBUEVFVEVIWBESJZVIWBECUCWCVIWBVJVKDOZNZVMWDPZVOWDPZGLZVRWDPZQZBVJRAV
      JRZKWBDECSWDEQZWEVLWKWAVJVKWDEUFWLWJVTABVJVJWLWHVQWIVSWLWFVNWGVPGVMWDETVO
      WDETUGVRWDETUHUIUJHUKZULUMWBVEWCVIVEVLWCWAVEVJSJZVLWCUNFIUPVLWNWCVJVKSEUO
      UQURUSWCVIWBWMUTVAVBVCVD $.
  $}

  ${
    $d F f x y $.  $d G f x y $.  $d H f x y $.  $d X x y $.
    elghom.1 $e |- X = ran G $.
    elghom.2 $e |- W = ran H $.
    $( Membership in the set of group homomorphisms from ` G ` to ` H ` .
       (Contributed by Paul Chapman, 3-Mar-2008.)
       (New usage is discouraged.) $)
    elghom $p |- ( ( G e. GrpOp /\ H e. GrpOp ) ->
      ( F e. ( G GrpOpHom H ) <-> ( F : X --> W /\ A. x e. X A. y e. X
        ( ( F ` x ) H ( F ` y ) ) = ( F ` ( x G y ) ) ) ) ) $=
      ( vf cgr wcel wa co crn wf cv cfv wceq wral eqid elghomlem2 feq23i raleqi
      cghom cab raleqbii anbi12i syl6bbr ) DKLEKLMCDEUENLDOZEOZCPZAQZCRBQZCRENU
      MUNDNZCRSZBUJTZAUJTZMGFCPZUPBGTZAGTZMABUJUKJQZPUMVBRUNVBRENUOVBRSBUJTAUJT
      MJUFZJCDEVCUAUBUSULVAURGFUJUKCHIUCUTUQAGUJHUPBGUJHUDUGUHUI $.
  $}

  ${
    $d A x y $.  $d B y $.  $d F x y $.  $d G x y $.  $d H x y $.  $d X x y $.
    ghomlin.1 $e |- X = ran G $.
    $( Linearity of a group homomorphism.  (Contributed by Paul Chapman,
       3-Mar-2008.)  (New usage is discouraged.) $)
    ghomlin $p |- ( ( ( G e. GrpOp /\ H e. GrpOp /\ F e. ( G GrpOpHom H ) ) /\
                      ( A e. X /\ B e. X ) ) ->
                    ( ( F ` A ) H ( F ` B ) ) = ( F ` ( A G B ) ) ) $=
      ( vx vy cgr wcel co cv cfv wceq wral wa fveq2 fveq2d eqeq12d cghom w3a wf
      crn eqid elghom biimp3a simprd oveq1d oveq1 oveq2d oveq2 rspc2v mpan9 ) D
      JKZEJKZCDEUALKZUBZHMZCNZIMZCNZELZUSVADLZCNZOZIFPHFPZAFKBFKQACNZBCNZELZABD
      LZCNZOZURFEUDZCUCZVGUOUPUQVOVGQHICDEVNFGVNUEUFUGUHVFVMVHVBELZAVADLZCNZOHI
      ABFFUSAOZVCVPVEVRVSUTVHVBEUSACRUIVSVDVQCUSAVADUJSTVABOZVPVJVRVLVTVBVIVHEV
      ABCRUKVTVQVKCVABADULSTUMUN $.
  $}

  ${
    $d F x y $.  $d G x y $.  $d H x y $.
    ghomid.1 $e |- U = ( GId ` G ) $.
    ghomid.2 $e |- T = ( GId ` H ) $.
    $( A group homomorphism maps identity element to identity element.
       (Contributed by Paul Chapman, 3-Mar-2008.)
       (New usage is discouraged.) $)
    ghomid $p |- ( ( G e. GrpOp /\ H e. GrpOp /\ F e. ( G GrpOpHom H ) ) ->
                   ( F ` U ) = T ) $=
      ( vx vy cgr wcel co cfv wceq crn wa eqid 3ad2ant1 mpdan cv cghom grpoidcl
      w3a jca ghomlin grpolid fveq2d eqtrd wb wf elghom biimp3a simpld ffvelrnd
      wral wi grpoid ex 3ad2ant2 mpd mpbird ) DJKZEJKZCDEUALKZUCZBCMZANZVFVFELZ
      VFNZVEVHBBDLZCMZVFVEBDOZKZVMPVHVKNVEVMVMVBVCVMVDBDVLVLQZFUBZRZVPUDBBCDEVL
      VNUESVBVCVKVFNVDVBVJBCVBVMVJBNVOBBDVLVNFUFSUGRUHVEVFEOZKZVGVIUIZVEVLVQBCV
      EVLVQCUJZHTZCMITZCMELWAWBDLCMNIVLUOHVLUOZVBVCVDVTWCPHICDEVQVLVNVQQZUKULUM
      VPUNVCVBVRVSUPVDVCVRVSVFAEVQWDGUQURUSUTVA $.
  $}

  ${
    $d w z C $.  $d b c w x y z F $.  $d c w x y z G $.  $d a b c w x y z ph $.
    $d w ch $.  $d a b c x y z H $.  $d b w x y z X $.  $d a b c w x y z Y $.
    $d w D $.  $d w x y z O $.
    ghgrp.1 $e |- ( ph -> F : X -onto-> Y ) $.
    ${
      ghgrplem1.2 $e |- ( ( ph /\ w e. X ) -> ps ) $.
      ghgrplem1.3 $e |- ( C = ( F ` w ) -> ( ch <-> ps ) ) $.
      $( Lemma for ~ ghgrp .  (Contributed by Paul Chapman, 25-Apr-2008.)
         (Revised by Mario Carneiro, 12-May-2014.)
         (New usage is discouraged.) $)
      ghgrplem1 $p |- ( ( ph /\ C e. Y ) -> ch ) $=
        ( wcel cv cfv wceq wrex wfo foelrn sylan wa syl5ibrcom rexlimdva syldan
        imp ) AEHLZEDMZFNOZDGPZCAGHFQUEUHIDGHEFRSAUHCAUGCDGAUFGLTCUGBJKUAUBUDUC
        $.
    $}

    ghgrp.2 $e |- ( ( ph /\ ( x e. X /\ y e. X ) ) ->
                      ( F ` ( x G y ) ) = ( ( F ` x ) O ( F ` y ) ) ) $.
    ghgrp.3 $e |- H = ( O |` ( Y X. Y ) ) $.
    $( Lemma for ~ ghgrp .  (Contributed by Paul Chapman, 25-Apr-2008.)
       (Revised by Mario Carneiro, 12-May-2014.)
       (New usage is discouraged.) $)
    ghgrplem2 $p |- ( ( ph /\ ( C e. X /\ D e. X ) ) ->
                       ( F ` ( C G D ) ) = ( ( F ` C ) H ( F ` D ) ) ) $=
      ( vz vw wcel co cfv wceq wa cv wral ralrimivva oveq1 fveq2d fveq2 eqeq12d
      oveq1d oveq2 oveq2d cbvral2v sylib rspc2v mpan9 cxp cres oveqi wf wfo fof
      syl ffvelrn anim12dan sylan ovres syl5eq eqtr4d ) ADJQZEJQZUAZUAZDEGRZFSZ
      DFSZEFSZIRZVOVPHRZAOUBZPUBZGRZFSZVSFSZVTFSZIRZTZPJUCOJUCZVKVNVQTZABUBZCUB
      ZGRZFSZWIFSZWJFSZIRZTZCJUCBJUCWGAWPBCJJMUDWPWFVSWJGRZFSZWCWNIRZTBCOPJJWIV
      STZWLWRWOWSWTWKWQFWIVSWJGUEUFWTWMWCWNIWIVSFUGUIUHWJVTTZWRWBWSWEXAWQWAFWJV
      TVSGUJUFXAWNWDWCIWJVTFUGUKUHULUMWFWHDVTGRZFSZVOWDIRZTOPDEJJVSDTZWBXCWEXDX
      EWAXBFVSDVTGUEUFXEWCVOWDIVSDFUGUIUHVTETZXCVNXDVQXFXBVMFVTEDGUJUFXFWDVPVOI
      VTEFUGUKUHUNUOVLVRVOVPIKKUPUQZRZVQHXGVOVPNURVLVOKQZVPKQZUAZXHVQTAJKFUSZVK
      XKAJKFUTXLLJKFVAVBXLVIXIVJXJJKDFVCJKEFVCVDVEVOVPKKIVFVBVGVH $.

    ghgrp.4 $e |- X = ran G $.
    ghgrp.5 $e |- ( ph -> Y C_ A ) $.
    ghgrp.6 $e |- ( ph -> O Fn ( A X. A ) ) $.
    ${
      ghgrp.7 $e |- ( ph -> G e. GrpOp ) $.
      $( The image of a group ` G ` under a group homomorphism ` F ` is a
         group.  This is a stronger result than that usually found in the
         literature, since the target of the homomorphism (operator ` O ` in
         our model) need not have any of the properties of a group as a
         prerequisite.  (Contributed by Paul Chapman, 25-Apr-2008.)  (Revised
         by Mario Carneiro, 12-May-2014.)  (New usage is discouraged.) $)
      ghgrp $p |- ( ph -> H e. GrpOp ) $=
        ( wcel co wceq va vb vc vz cvv wfo crn cgr syl syl5eqel fornex sylc cgi
        rnexg cfv c0 wne wf fof eqid grpoidcl ffvelrnd ne0i cxp wfn cv wral wss
        cres xpss12 syl2anc fnssres fneq1i sylibr adantr ghgrplem2 grpocl 3expb
        wa sylan ffvelrnda syldan eqeltrrd anassrs oveq2 eleq1d ghgrplem1 oveq1
        ralrimiva ralbidv ffnov sylanbrc simprll simprlr simprr syl13anc fveq2d
        wi grpoass adantrr syl12anc syl3anc 3eqtr3d oveq1d oveq2d expr impancom
        simpl eqeq12d imbi2d 3imp2 cgs simprl grpodivcl grponpcan eqtr3d eqeq1d
        ex wrex rspcev cgn grpoinvcl grpoasscan1 jca eqeq2 rexbidv anbi12d impr
        simpld simprd isgrp2d ) AUAUBUCGUEJAIUERIJEUFZJUERAIFUGZUENAFUHRZYMUERQ
        FUHUNUIUJKIJUEEUKULAFUMUOZEUOZJRJUPUQAIJYOEAYLIJEURZKIJEUSUIZAYNYOIRQYO
        FINYOUTVAUIVBJYPVCUIAGJJVDZVEZUAVFZUBVFZGSZJRZUBJVGZUAJVGYSJGURAHYSVIZY
        SVEZYTAHDDVDZVEYSUUHVHZUUGPAJDVHZUUJUUIOOJDJDVJVKUUHYSHVLVKYSGUUFMVMVNA
        UUEUAJABVFZEUOZUUBGSZJRZUBJVGUUEBUUAEIJKAUUKIRZVSZUUNUBJUUPUULCVFZEUOZG
        SZJRZUUNCUUBEIJAYLUUOKVOAUUOUUQIRZUUTAUUOUVAVSZVSZUUKUUQFSZEUOZUUSJABCU
        UKUUQEFGHIJKLMVPZAUVBUVDIRZUVEJRAYNUVBUVGQYNUUOUVAUVGUUKUUQFINVQVRVTZAI
        JUVDEYRWAWBWCWDUUBUURTZUUMUUSJUUBUURUULGWEZWFWGWIUUAUULTZUUDUUNUBJUVKUU
        CUUMJUUAUULUUBGWHZWFWJWGWIUAUBJJJGWKWLAUUAJRZUUBJRZUCVFZJRZUUCUVOGSZUUA
        UUBUVOGSZGSZTZAUVMUVNUVPUVTWRZWRZAUVNUVPUUMUVOGSZUULUVRGSZTZWRZWRUWBBUU
        AEIJKAUVNUUOUWFAUUOUVPUUSUVOGSZUULUURUVOGSZGSZTZWRZWRUUOUWFWRCUUBEIJKAU
        UOUVAUWKAUUOUVAUWKAUVPUVBUWJAUVBUUSUDVFZEUOZGSZUULUURUWMGSZGSZTZWRUVBUW
        JWRUDUVOEIJKAUVBUWLIRZUWQAUVBUWRUWQAUVBUWRVSZVSZUVEUWMGSZUULUUQUWLFSZEU
        OZGSZUWNUWPUWTUVDUWLFSZEUOZUUKUXBFSZEUOZUXAUXDUWTUXEUXGEUWTYNUUOUVAUWRU
        XEUXGTAYNUWSQVOZAUUOUVAUWRWMZAUUOUVAUWRWNZAUVBUWRWOZUUKUUQUWLFINWSWPWQU
        WTAUVGUWRUXFUXATAUWSXHZAUVBUVGUWRUVHWTUXLABCUVDUWLEFGHIJKLMVPXAUWTAUUOU
        XBIRZUXHUXDTUXMUXJUWTYNUVAUWRUXNUXIUXKUXLUUQUWLFINVQXBABCUUKUXBEFGHIJKL
        MVPXAXCUWTUVEUUSUWMGAUVBUVEUUSTUWRUVFWTXDUWTUXCUWOUULGUWTAUVAUWRUXCUWOT
        UXMUXKUXLABCUUQUWLEFGHIJKLMVPXAXEXCXFXGUVOUWMTZUWJUWQUVBUXOUWGUWNUWIUWP
        UVOUWMUUSGWEUXOUWHUWOUULGUVOUWMUURGWEXEXIXJWGXGXFXGUVIUWFUWKUUOUVIUWEUW
        JUVPUVIUWCUWGUWDUWIUVIUUMUUSUVOGUVJXDUVIUVRUWHUULGUUBUURUVOGWHXEXIXJXJW
        GXGUVKUWAUWFUVNUVKUVTUWEUVPUVKUVQUWCUVSUWDUVKUUCUUMUVOGUVLXDUUAUULUVRGW
        HXIXJXJWGXRXKAUVMUVNVSVSZUVOUUAGSZUUBTZUCJXSZUUAUVOGSZUUBTZUCJXSZAUVMUV
        NUXSUYBVSZAUVNUVOUULGSZUUBTZUCJXSZUULUVOGSZUUBTZUCJXSZVSZWRUVNUYCWRBUUA
        EIJKAUVNUUOUYJAUUOUYDUURTZUCJXSZUYGUURTZUCJXSZVSZWRUUOUYJWRCUUBEIJKAUUO
        UVAUYOAUUOUVAUYOUVCUYLUYNUVCUUQUUKFXLUOZSZEUOZJRUYRUULGSZUURTZUYLUVCIJU
        YQEAYQUVBYRVOZUVCYNUVAUUOUYQIRZAYNUVBQVOZAUUOUVAWOZAUUOUVAXMZUUQUUKUYPF
        INUYPUTZXNXBZVBUVCUYQUUKFSZEUOZUYSUURUVCAVUBUUOVUIUYSTAUVBXHZVUGVUEABCU
        YQUUKEFGHIJKLMVPXAUVCVUHUUQEUVCYNUVAUUOVUHUUQTVUCVUDVUEUUQUUKUYPFINVUFX
        OXBWQXPUYKUYTUCUYRJUVOUYRTUYDUYSUURUVOUYRUULGWHXQXTVKUVCUUKFYAUOZUOZUUQ
        FSZEUOZJRUULVUNGSZUURTZUYNUVCIJVUMEVUAUVCYNVULIRZUVAVUMIRZVUCUVCYNUUOVU
        QVUCVUEUUKFVUKINVUKUTZYBVKVUDVULUUQFINVQXBZVBUVCUUKVUMFSZEUOZVUOUURUVCA
        UUOVURVVBVUOTVUJVUEVUTABCUUKVUMEFGHIJKLMVPXAUVCVVAUUQEUVCYNUUOUVAVVAUUQ
        TVUCVUEVUDUUKUUQFVUKINVUSYCXBWQXPUYMVUPUCVUNJUVOVUNTUYGVUOUURUVOVUNUULG
        WEXQXTVKYDXFXGUVIUYJUYOUUOUVIUYFUYLUYIUYNUVIUYEUYKUCJUUBUURUYDYEYFUVIUY
        HUYMUCJUUBUURUYGYEYFYGXJWGXGUVKUYCUYJUVNUVKUXSUYFUYBUYIUVKUXRUYEUCJUVKU
        XQUYDUUBUUAUULUVOGWEXQYFUVKUYAUYHUCJUVKUXTUYGUUBUUAUULUVOGWHXQYFYGXJWGY
        HZYIUXPUXSUYBVVCYJYK $.
    $}

    ghablo.7 $e |- ( ph -> G e. AbelOp ) $.
    $( The image of an Abelian group ` G ` under a group homomorphism ` F ` is
       an Abelian group (Contributed by Paul Chapman, 25-Apr-2008.)  (Revised
       by Mario Carneiro, 12-May-2014.)  (New usage is discouraged.) $)
    ghablo $p |- ( ph -> H e. AbelOp ) $=
      ( wcel co wceq va vb cgr cv crn wral cablo ablogrpo syl ghgrp cdm cxp wss
      wfn fndm resgrprn syl3anc eleq2d anbi12d biimpar cfv adantr simprl simprr
      wa wi ablocom fveq2d ghgrplem2 ancom2s 3eqtr3d oveq2 oveq1 eqeq12d imbi2d
      expr ghgrplem1 impancom impr syldan ralrimivva eqid isablo sylanbrc ) AGU
      CRZUAUDZUBUDZGSZWGWFGSZTZUBGUEZUFUAWKUFGUGRABCDEFGHIJKLMNOPAFUGRZFUCRQFUH
      UIUJZAWJUAUBWKWKAWFWKRZWGWKRZVEZWFJRZWGJRZVEZWJAWSWPAWQWNWRWOAJWKWFAHUKDD
      ULZTZWEJDUMJWKTAHWTUNXAPWTHUOUIWMOHGDJMUPUQZURAJWKWGXBURUSUTAWQWRWJAWRBUD
      ZEVAZWGGSZWGXDGSZTZVFWRWJVFBWFEIJKAWRXCIRZXGAXHXDCUDZEVAZGSZXJXDGSZTZVFXH
      XGVFCWGEIJKAXIIRZXHXMAXHXNXMAXHXNVEZVEZXCXIFSZEVAXIXCFSZEVAZXKXLXPXQXREXP
      WLXHXNXQXRTAWLXOQVBAXHXNVCAXHXNVDXCXIFINVGUQVHABCXCXIEFGHIJKLMVIAXNXHXSXL
      TABCXIXCEFGHIJKLMVIVJVKVJVPWGXJTZXGXMXHXTXEXKXFXLWGXJXDGVLWGXJXDGVMVNVOVQ
      VRWFXDTZWJXGWRYAWHXEWIXFWFXDWGGVMWFXDWGGVLVNVOVQVSVTWAUAUBGWKWKWBWCWD $.
  $}

  ${
    $d x y F $.  $d x y H $.  $d x y O $.  $d x y S $.  $d x y W $.
    $d x y Z $.  $d x y ph $.
    ghsubgo.1 $e |- ( ph -> S e. ( SubGrpOp ` G ) ) $.
    ghsubgo.2 $e |- X = ran G $.
    ghsubgo.3 $e |- ( ph -> F : X --> Y ) $.
    ghsubgo.4 $e |- ( ph -> Y C_ A ) $.
    ghsubgo.5 $e |- ( ph -> O Fn ( A X. A ) ) $.
    ghsubgo.6 $e |- ( ( ph /\ ( x e. X /\ y e. X ) ) ->
                     ( F ` ( x G y ) ) = ( ( F ` x ) O ( F ` y ) ) ) $.
    ghsubgo.7 $e |- Z = ran S $.
    ghsubgo.8 $e |- W = ( F " Z ) $.
    ghsubgo.9 $e |- H = ( O |` ( W X. W ) ) $.
    $( The image of a subgroup ` S ` of group ` G ` under a group homomorphism
       ` F ` on ` G ` is a group, and furthermore is Abelian if ` S ` is
       Abelian.  (Contributed by Paul Chapman, 25-Apr-2008.)  (Revised by Mario
       Carneiro, 12-May-2014.)  (New usage is discouraged.) $)
    ghsubgolem $p |- ( ph -> ( H e. GrpOp /\
                      ( S e. AbelOp -> H e. AbelOp ) ) ) $=
      ( cgr wcel cablo cres cima wfun cdm wss wfo ffun syl csubgo cfv subgornss
      wi wf wceq fdm sseqtr4d fores syl2anc cv wa ssel2 anim12dan sylan issubgo
      syldan simp2bi grpocl 3expb fvres subgoov fveq2d oveqan12d adantl 3eqtr4d
      eqtrd cxp xpeq12i reseq2i eqtri crn imassrn frn syl5ss sstrd ghgrp adantr
      co adantlr wfn simpr ghablo ex jca ) AHUCUDEUEUDZHUEUDZUQABCDFMUFZEHIMFMU
      GZAFUHZMFUIZUJMXBXAUKZAKLFURZXCPKLFULUMAMKXDAEGUNUOUDZMKUJZNGEMKOTUPUMZAX
      FXDKUSPKLFUTUMVAMFVBVCZABVDZMUDZCVDZMUDZVEZVEZXKXMGWLZFUOZXKFUOZXMFUOZIWL
      ZXKXMEWLZXAUOZXKXAUOZXMXAUOZIWLZAXOXKKUDZXMKUDZVEZXRYAUSAXHXOYIXIXHXLYGXN
      YHMKXKVFMKXMVFVGVHSVJXPYCYBFUOZXRXPYBMUDZYCYJUSAEUCUDZXOYKAXGYLNXGGUCUDYL
      EGUJGEVIVKUMZYLXLXNYKXKXMEMTVLVMVHYBMFVNUMXPYBXQFAXGXOYBXQUSNXKXMGEMTVOVH
      VPVTXOYFYAUSAXLXNYDXSYEXTIXKMFVNXMMFVNVQVRVSZHIJJWAZUFIXBXBWAZUFUBYOYPIJX
      BJXBUAUAWBWCWDZTAXBLDAXBFWEZLFMWFAXFYRLUJPKLFWGUMWHQWIZRYMWJAWSWTAWSVEBCD
      XAEHIMXBAXEWSXJWKAXOYCYFUSWSYNWMYQTAXBDUJWSYSWKAIDDWAWNWSRWKAWSWOWPWQWR
      $.

    $( The image of a subgroup ` S ` of group ` G ` under a group homomorphism
       ` F ` on ` G ` is a group.  (Contributed by NM, 25-Apr-2008.)  (Revised
       by Mario Carneiro, 12-May-2014.)  (New usage is discouraged.) $)
    ghsubgo $p |- ( ph -> H e. GrpOp ) $=
      ( cgr wcel cablo wi ghsubgolem simpld ) AHUCUDEUEUDHUEUDUFABCDEFGHIJKLMNO
      PQRSTUAUBUGUH $.

    ghsubablo.10 $e |- ( ph -> S e. AbelOp ) $.
    $( The image of an Abelian subgroup ` S ` of group ` G ` under a group
       homomorphism ` F ` on ` G ` is an Abelian group.  (Contributed by Mario
       Carneiro, 12-May-2014.)  (New usage is discouraged.) $)
    ghsubablo $p |- ( ph -> H e. AbelOp ) $=
      ( cablo wcel cgr wi ghsubgolem simprd mpd ) AEUDUEZHUDUEZUCAHUFUEUKULUGAB
      CDEFGHIJKLMNOPQRSTUAUBUHUIUJ $.
  $}

  ${
    $d x y z A $.  $d x y z ph $.  $d x y z X $.
    efghgrp.1 $e |- S = { y | E. x e. X y = ( exp ` ( A x. x ) ) } $.
    efghgrp.2 $e |- G = ( x. |` ( S X. S ) ) $.
    efghgrp.3 $e |- ( ph -> A e. CC ) $.
    efghgrp.4 $e |- ( ph -> X C_ CC ) $.
    efghgrp.5 $e |- ( + |` ( X X. X ) ) e. ( SubGrpOp ` + ) $.
    $( The image of a subgroup of the group ` + ` , under the exponential
       function of a scaled complex number, is an Abelian group.  (Contributed
       by Paul Chapman, 25-Apr-2008.)  (Revised by Mario Carneiro,
       12-May-2014.)  (New usage is discouraged.) $)
    efghgrp $p |- ( ph -> G e. AbelOp ) $=
      ( cmul cc cfv caddc wceq eqid wcel a1i vz cv co ce cmpt cxp cres crn cima
      cablo cab rnmpt eqtr4i df-ima wss resmpt syl rneqd syl5eq cdm cgr ax-addf
      wrex fdmi csubgo cnaddablo mp2an ablogrpo resgrprn syl3anc imaeq2d eqtr3d
      subgoablo xpeq12d reseq2d ax-mp grporn wa mulcl efcl sylan fmptd ssid wfn
      wf ax-mulf ffn efgh 3expb ghsubablo eqeltrd ) AFMBNDBUBZMUCZUDOZUEZPGGUFU
      GZUHZUIZWRUFZUGZUJAFMEEUFZUGWTIAXAWSMAEWREWRAEBGWNUEZUHZWRECUBZWNQBGVCCUK
      XCHBCGWNXBXBRULUMAWOGUIZXCWRAXEWOGUGZUHXCWOGUNAXFXBAGNUOZXFXBQKBNGWNUPUQU
      RUSAGWQWOAPUTNNUFZQZWPVASZXGGWQQXIAXHNPVBVDZTAWPUJSZXJXLAPUJSZWPPVEOSZXLV
      FLPWPVMVGTZWPVHUQKPWPNGWPRVIVJVKVLUSZXPVNVOUSACUANWPWOPWTMWRNNWQXNALTPNXM
      PVASVFPVHVPXKVQABNWNNWOADNSZWLNSZWNNSZJXQXRVRWMNSXSDWLVSWMVTUQWAWORZWBNNU
      OANWCTMXHWDZAXHNMWEYAWFXHNMWGVPTAXQXDNSZUAUBZNSZVRXDYCPUCWOOXDWOOYCWOOMUC
      QZJXQYBYDYEBDXDYCWOXTWHWIWAWQRWRRWTRXOWJWK $.
  $}

  ${
    $d x y C $.
    circgrp.1 $e |- C = ( `' abs " { 1 } ) $.
    circgrp.2 $e |- T = ( x. |` ( C X. C ) ) $.
    $( The circle group ` T ` is an Abelian group.  (Contributed by Paul
       Chapman, 25-Mar-2008.)  (Revised by Mario Carneiro, 13-May-2014.)
       (New usage is discouraged.) $)
    circgrp $p |- T e. AbelOp $=
      ( vy vx cablo wcel wtru ci cr cv cmul co ce cfv cmpt wceq cc a1i crn wrex
      cab wfo eqid efifo ax-mp rnmpt eqtr3i ax-icn ax-resscn readdsubgo efghgrp
      forn wss trud ) BGHIEFJABKEKJELMNOPZQZUAZAFLUQREKUBFUCKAURUDUSAREAURURUEZ
      CUFKAURUNUGEFKUQURUTUHUIDJSHIUJTKSUOIUKTULUMUP $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                   Additional material on rings and fields
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Definition and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c RingOps $.

  $( Extend class notation with the class of all unital rings. $)
  crngo $a class RingOps $.

  ${
    $d g h x y z $.
    $( Define the class of all unital rings.  (Contributed by Jeffrey Hankins,
       21-Nov-2006.)  (New usage is discouraged.) $)
    df-rngo $a |- RingOps = { <. g , h >. | ( ( g e. AbelOp /\
                               h : ( ran g X. ran g ) --> ran g ) /\
            ( A. x e. ran g A. y e. ran g A. z e. ran g
              ( ( ( x h y ) h z ) = ( x h ( y h z ) ) /\
                ( x h ( y g z ) ) = ( ( x h y ) g ( x h z ) ) /\
                ( ( x g y ) h z ) = ( ( x h z ) g ( y h z ) ) ) /\
        E. x e. ran g A. y e. ran g ( ( x h y ) = y /\ ( y h x ) = y ) ) ) } $.
  $}

  ${
    $d g h x y z $.
    $( The class of all unital rings is a relation.  (Contributed by FL,
       31-Aug-2009.)  (Revised by Mario Carneiro, 21-Dec-2013.)
       (New usage is discouraged.) $)
    relrngo $p |- Rel RingOps $=
      ( vg vh vx vy vz cv cablo wcel crn cxp wf wa wceq wral wrex crngo df-rngo
      co w3a relopabi ) AFZGHUAIZUBJUBBFZKLCFZDFZUCRZEFZUCRUDUEUGUCRZUCRMUDUEUG
      UARUCRUFUDUGUCRZUARMUDUEUARUGUCRUIUHUARMSEUBNDUBNCUBNUFUEMUEUDUCRUEMLDUBN
      CUBOLLABPCDEABQT $.
  $}

  ${
    $d g h x y z G $.  $d g h x y z H $.  $d g h x y z X $.
    isring.1 $e |- X = ran G $.
    $( The predicate "is a (unital) ring."  Definition of ring with unit in
       [Schechter] p. 187.  (Contributed by Jeffrey Hankins, 21-Nov-2006.)
       (Revised by Mario Carneiro, 21-Dec-2013.)
       (New usage is discouraged.) $)
    isrngo $p |- ( H e. A -> ( <. G , H >. e. RingOps <->
      ( ( G e. AbelOp /\ H : ( X X. X ) --> X ) /\
        ( A. x e. X A. y e. X A. z e. X
          ( ( ( x H y ) H z ) = ( x H ( y H z ) ) /\
            ( x H ( y G z ) ) = ( ( x H y ) G ( x H z ) ) /\
            ( ( x G y ) H z ) = ( ( x H z ) G ( y H z ) ) ) /\
          E. x e. X A. y e. X ( ( x H y ) = y /\ ( y H x ) = y ) ) ) ) ) $=
      ( vg vh wcel crngo cablo wa cv co wceq wral oveqd oveq123d cvv cop cxp wf
      w3a wrex wi wbr df-br relrngo brrelexi sylbir a1i elex ad2antrr crn copab
      wb df-rngo eleq2i simpl simpr rneqd syl6eqr xpeq12d feq123d anbi12d eqidd
      eleq1d eqeq12d 3anbi123d raleqbidv eqeq1d rexeqbidv opelopabga pm5.21ndd
      syl5bb expcom ) FDKZEUAKZEFUBZLKZEMKZGGUCZGFUDZNZAOZBOZFPZCOZFPZWGWHWJFPZ
      FPZQZWGWHWJEPZFPZWIWGWJFPZEPZQZWGWHEPZWJFPZWQWLEPZQZUEZCGRZBGRZAGRZWIWHQZ
      WHWGFPZWHQZNZBGRZAGUFZNZNZWBVTUGVSWBEFLUHVTEFLUIEFLUJUKULUMXOVTUGVSWCVTWE
      XNEMUNUOUMVTVSWBXOURWBWAIOZMKZXPUPZXRUCZXRJOZUDZNZWGWHXTPZWJXTPZWGWHWJXTP
      ZXTPZQZWGWHWJXPPZXTPZYCWGWJXTPZXPPZQZWGWHXPPZWJXTPZYJYEXPPZQZUEZCXRRZBXRR
      ZAXRRZYCWHQZWHWGXTPZWHQZNZBXRRZAXRUFZNZNZIJUQZKVTVSNXOLUUIWAABCIJUSUTUUHX
      OIJEFUADXPEQZXTFQZNZYBWFUUGXNUULXQWCYAWEUULXPEMUUJUUKVAZVIUULXSWDXRGXTFUU
      JUUKVBZUULXRGXRGUULXREUPGUULXPEUUMVCHVDZUUOVEUUOVFVGUULYTXGUUFXMUULYSXFAX
      RGUUOUULYRXEBXRGUUOUULYQXDCXRGUUOUULYGWNYLWSYPXCUULYDWKYFWMUULYCWIWJWJXTF
      UUNUULXTFWGWHUUNSZUULWJVHZTUULWGWGYEWLXTFUUNUULWGVHZUULXTFWHWJUUNSZTVJUUL
      YIWPYKWRUULWGWGYHWOXTFUUNUURUULXPEWHWJUUMSTUULYCWIYJWQXPEUUMUUPUULXTFWGWJ
      UUNSZTVJUULYNXAYOXBUULYMWTWJWJXTFUUNUULXPEWGWHUUMSUUQTUULYJWQYEWLXPEUUMUU
      TUUSTVJVKVLVLVLUULUUEXLAXRGUUOUULUUDXKBXRGUUOUULUUAXHUUCXJUULYCWIWHUUPVMU
      ULUUBXIWHUULXTFWHWGUUNSVMVGVLVNVGVGVOVQVRVP $.
  $}

  ${
    $d ph x y z $.  $d G x y z $.  $d H x y z $.  $d X x y z $.  $d U x y $.
    isringod.1 $e |- ( ph -> G e. AbelOp ) $.
    isringod.2 $e |- ( ph -> X = ran G ) $.
    isringod.3 $e |- ( ph -> H : ( X X. X ) --> X ) $.
    isringod.4 $e |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) )
                                  -> ( ( x H y ) H z ) = ( x H ( y H z ) ) ) $.
    isringod.5 $e |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) )
                          -> ( x H ( y G z ) ) = ( ( x H y ) G ( x H z ) ) ) $.
    isringod.6 $e |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) )
                          -> ( ( x G y ) H z ) = ( ( x H z ) G ( y H z ) ) ) $.
    isringod.7 $e |- ( ph -> U e. X ) $.
    isringod.8 $e |- ( ( ph /\ y e. X ) -> ( U H y ) = y ) $.
    isringod.9 $e |- ( ( ph /\ y e. X ) -> ( y H U ) = y ) $.
    $( Conditions that determine a ring.  (Changed label from ~ isrngd to
       ~ isrngod -NM 2-Aug-2013.)  (Contributed by Jeff Madsen, 19-Jun-2010.)
       (Revised by Mario Carneiro, 21-Dec-2013.)
       (New usage is discouraged.) $)
    isrngod $p |- ( ph -> <. G , H >. e. RingOps ) $=
      ( wcel co wral cop crngo cablo crn cxp wf wa wceq w3a wrex xpeq12d feq23d
      mpbid 3jca ralrimivvva raleqdv raleqbidv jca ralrimiva oveq1 eqeq1d oveq2
      cv anbi12d ralbidv rspcev syl2anc rexeqbidv jca31 cvv rnexg syl xpexg fex
      wb eqid isrngo mpbird ) AFGUAUBRZFUCRZFUDZWAUEZWAGUFZUGBVCZCVCZGSZDVCZGSW
      DWEWGGSZGSUHZWDWEWGFSGSWFWDWGGSZFSUHZWDWEFSWGGSWJWHFSUHZUIZDWATZCWATZBWAT
      ZWFWEUHZWEWDGSZWEUHZUGZCWATZBWAUJZUGZUGZAVTWCXCIAHHUEZHGUFWCKAXEHWBWAGAHW
      AHWAJJUKJULUMZAWPXBAWMDHTZCHTZBHTWPAWMBCDHHHAWDHRWEHRZWGHRUIUGWIWKWLLMNUN
      UOAXHWOBHWAJAXGWNCHWAJAWMDHWAJUPUQUQUMAWTCHTZBHUJZXBAEHREWEGSZWEUHZWEEGSZ
      WEUHZUGZCHTZXKOAXPCHAXIUGXMXOPQURUSXJXQBEHWDEUHZWTXPCHXRWQXMWSXOXRWFXLWEW
      DEWEGUTVAXRWRXNWEWDEWEGVBVAVDVEVFVGAXJXABHWAJAWTCHWAJUPVHUMURVIAGVJRZVSXD
      VOAWCWBVJRZXSXFAWAVJRZYAXTAVTYAIFUCVKVLZYBWAWAVJVJVMVGWBWAVJGVNVGBCDVJFGW
      AWAVPVQVLVR $.
  $}

  ${
    $d u x y z G $.  $d u x y z H $.  $d u x y z X $.  $d u x y z A $.
    $d y z B $.  $d z C $.  $d u x R $.
    ringi.1 $e |- G = ( 1st ` R ) $.
    ringi.2 $e |- H = ( 2nd ` R ) $.
    ringi.3 $e |- X = ran G $.
    $( The properties of a unital ring.  (Contributed by Steve Rodriguez,
       8-Sep-2007.)  (Proof shortened by Mario Carneiro, 21-Dec-2013.)
       (New usage is discouraged.) $)
    rngoi $p |- ( R e. RingOps -> ( ( G e. AbelOp /\ H : ( X X. X ) --> X ) /\
      ( A. x e. X A. y e. X A. z e. X
        ( ( ( x H y ) H z ) = ( x H ( y H z ) ) /\
          ( x H ( y G z ) ) = ( ( x H y ) G ( x H z ) ) /\
          ( ( x G y ) H z ) = ( ( x H z ) G ( y H z ) ) ) /\
        E. x e. X A. y e. X ( ( x H y ) = y /\ ( y H x ) = y ) ) ) ) $=
      ( crngo wcel cop wa cv co wceq wral cfv cvv cablo cxp wrex c1st c2nd wrel
      wf relrngo 1st2nd mpan opeq12i syl6reqr id eqeltrd wb fvex eqeltri isrngo
      w3a ax-mp sylib ) DKLZEFMZKLZEUALGGUBGFUGNAOZBOZFPZCOZFPVEVFVHFPZFPQVEVFV
      HEPFPVGVEVHFPZEPQVEVFEPVHFPVJVIEPQUSCGRBGRAGRVGVFQVFVEFPVFQNBGRAGUCNNZVBV
      CDKVBDDUDSZDUESZMZVCKUFVBDVNQUHDKUIUJEVLFVMHIUKULVBUMUNFTLVDVKUOFVMTIDUEU
      PUQABCTEFGJURUTVA $.

    $( Functionality of the multiplication operation of a ring.  (Contributed
       by Steve Rodriguez, 9-Sep-2007.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.) $)
    rngosm $p |- ( R e. RingOps -> H : ( X X. X ) --> X ) $=
      ( vx vy vz crngo wcel cablo cxp wf wa cv co wceq wral rngoi simpld simprd
      w3a wrex ) AKLZBMLZDDNDCOZUFUGUHPHQZIQZCRZJQZCRUIUJULCRZCRSUIUJULBRCRUKUI
      ULCRZBRSUIUJBRULCRUNUMBRSUDJDTIDTHDTUKUJSUJUICRUJSPIDTHDUEPHIJABCDEFGUAUB
      UC $.

    $( Closure of the multiplication operation of a ring.  (Contributed by
       Steve Rodriguez, 9-Sep-2007.)  (New usage is discouraged.) $)
    rngocl $p |- ( ( R e. RingOps /\ A e. X /\ B e. X ) -> ( A H B ) e. X ) $=
      ( crngo wcel cxp wf co rngosm fovrn syl3an1 ) CJKFFLFEMAFKBFKABENFKCDEFGH
      IOABFFFEPQ $.

    $( The multiplication operation of a unital ring has (one or more) identity
       elements.  (Contributed by Steve Rodriguez, 9-Sep-2007.)  (Revised by
       Mario Carneiro, 22-Dec-2013.)  (New usage is discouraged.) $)
    rngoid $p |- ( ( R e. RingOps /\ A e. X ) ->
                 E. u e. X ( ( u H A ) = A /\ ( A H u ) = A ) ) $=
      ( vx vy wcel cv co wceq wa wrex wral simprd eqeq12d crngo w3a cablo rngoi
      cxp wf r19.12 syl oveq2 id oveq1 anbi12d rexbidv rspccva sylan ) CUALZAMZ
      JMZENZUROZURUQENZUROZPZAFQZJFRZBFLUQBENZBOZBUQENZBOZPZAFQZUPVCJFRAFQZVEUP
      USKMZENUQURVMENZENOUQURVMDNENUSUQVMENZDNOUQURDNVMENVOVNDNOUBKFRJFRAFRZVLU
      PDUCLFFUEFEUFPVPVLPAJKCDEFGHIUDSSVCAJFFUGUHVDVKJBFURBOZVCVJAFVQUTVGVBVIVQ
      USVFURBURBUQEUIVQUJZTVQVAVHURBURBUQEUKVRTULUMUNUO $.

    $( The unit element of a ring is unique.  (Contributed by NM, 4-Apr-2009.)
       (Revised by Mario Carneiro, 21-Dec-2013.)
       (New usage is discouraged.) $)
    rngoideu $p |- ( R e. RingOps ->
                 E! u e. X A. x e. X ( ( u H x ) = x /\ ( x H u ) = x ) ) $=
      ( vy wcel cv co wceq wa wral weq ralimi oveq2 id crngo wrex wi wreu cablo
      cxp w3a rngoi simprr simpl eqeq12d rspcv syl5 simpr oveq1 im2anan9r eqtr2
      wf syl eqcomd syl6 rgen2a jctir eqeq1d anbi12d ralbidv reu4 sylibr ) CUAK
      ZBLZALZEMZVKNZVKVJEMZVKNZOZAFPZBFUBZVQJLZVKEMZVKNZVKVSEMZVKNZOZAFPZOZBJQZ
      UCZJFPBFPZOVQBFUDVIVRWIVIDUEKFFUFFEUROZVLVSEMVJWBEMNVJVKVSDMEMVLVJVSEMZDM
      NVJVKDMVSEMWKWBDMNUGJFPAFPBFPZVROOVRBAJCDEFGHIUHWJWLVRUIUSWHBJFVJFKZVSFKZ
      OWFWKVSNZWKVJNZOZWGWNVQWOWMWEWPVQVMAFPWNWOVPVMAFVMVOUJRVMWOAVSFAJQZVLWKVK
      VSVKVSVJESWRTUKULUMWEWCAFPWMWPWDWCAFWAWCUNRWCWPAVJFABQZWBWKVKVJVKVJVSEUOW
      STUKULUMUPWQVSVJWKVSVJUQUTVAVBVCVQWEBJFWGVPWDAFWGVMWAVOWCWGVLVTVKVJVSVKEU
      OVDWGVNWBVKVJVSVKESVDVEVFVGVH $.

    $( Distributive law for the multiplication operation of a ring.
       (Contributed by Steve Rodriguez, 9-Sep-2007.)  (Revised by Mario
       Carneiro, 21-Dec-2013.)  (New usage is discouraged.) $)
    rngodi $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                     ( A H ( B G C ) ) = ( ( A H B ) G ( A H C ) ) ) $=
      ( vx vy vz wcel cv co wceq wral wa oveq1 crngo w3a cablo cxp rngoi simprd
      wrex simpld simp2 ralimi oveq12d eqeq12d oveq2d oveq2 oveq1d rspc3v mpan9
      wf syl5 ) DUANZKOZLOZFPZMOZFPVAVBVDFPZFPQZVAVBVDEPZFPZVCVAVDFPZEPZQZVAVBE
      PVDFPVIVEEPQZUBZMGRZLGRZKGRZAGNBGNCGNUBZABCEPZFPZABFPZACFPZEPZQZUTVPVCVBQ
      VBVAFPVBQSLGRKGUGZUTEUCNGGUDGFURSVPWDSKLMDEFGHIJUEUFUHVPVKMGRZLGRZKGRVQWC
      VOWFKGVNWELGVMVKMGVFVKVLUIUJUJUJVKWCAVGFPZAVBFPZAVDFPZEPZQABVDEPZFPZVTWIE
      PZQKLMABCGGGVAAQZVHWGVJWJVAAVGFTWNVCWHVIWIEVAAVBFTVAAVDFTUKULVBBQZWGWLWJW
      MWOVGWKAFVBBVDETUMWOWHVTWIEVBBAFUNUOULVDCQZWLVSWMWBWPWKVRAFVDCBEUNUMWPWIW
      AVTEVDCAFUNUMULUPUSUQ $.

    $( Distributive law for the multiplication operation of a ring.
       (Contributed by Steve Rodriguez, 9-Sep-2007.)  (Revised by Mario
       Carneiro, 21-Dec-2013.)  (New usage is discouraged.) $)
    rngodir $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                      ( ( A G B ) H C ) = ( ( A H C ) G ( B H C ) ) ) $=
      ( vx vy vz wcel cv co wceq wral wa oveq2 crngo w3a cablo cxp rngoi simprd
      wrex simpld simp3 ralimi oveq1 oveq1d eqeq12d oveq2d oveq12d rspc3v mpan9
      wf syl5 ) DUANZKOZLOZFPZMOZFPVAVBVDFPZFPQZVAVBVDEPFPVCVAVDFPZEPQZVAVBEPZV
      DFPZVGVEEPZQZUBZMGRZLGRZKGRZAGNBGNCGNUBZABEPZCFPZACFPZBCFPZEPZQZUTVPVCVBQ
      VBVAFPVBQSLGRKGUGZUTEUCNGGUDGFURSVPWDSKLMDEFGHIJUEUFUHVPVLMGRZLGRZKGRVQWC
      VOWFKGVNWELGVMVLMGVFVHVLUIUJUJUJVLWCAVBEPZVDFPZAVDFPZVEEPZQVRVDFPZWIBVDFP
      ZEPZQKLMABCGGGVAAQZVJWHVKWJWNVIWGVDFVAAVBEUKULWNVGWIVEEVAAVDFUKULUMVBBQZW
      HWKWJWMWOWGVRVDFVBBAETULWOVEWLWIEVBBVDFUKUNUMVDCQZWKVSWMWBVDCVRFTWPWIVTWL
      WAEVDCAFTVDCBFTUOUMUPUSUQ $.

    $( Associative law for the multiplication operation of a ring.
       (Contributed by Steve Rodriguez, 9-Sep-2007.)  (Revised by Mario
       Carneiro, 21-Dec-2013.)  (New usage is discouraged.) $)
    rngoass $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                      ( ( A H B ) H C ) = ( A H ( B H C ) ) ) $=
      ( vx vy vz wcel cv co wceq wral wa ralimi crngo w3a wrex cablo cxp simprd
      wf rngoi simpld simp1 syl oveq1 oveq1d eqeq12d oveq2 oveq2d rspc3v mpan9
      ) DUANZKOZLOZFPZMOZFPZUTVAVCFPZFPZQZMGRZLGRZKGRZAGNBGNCGNUBABFPZCFPZABCFP
      ZFPZQZUSVGUTVAVCEPFPVBUTVCFPZEPQZUTVAEPVCFPVPVEEPQZUBZMGRZLGRZKGRZVJUSWBV
      BVAQVAUTFPVAQSLGRKGUCZUSEUDNGGUEGFUGSWBWCSKLMDEFGHIJUHUFUIWAVIKGVTVHLGVSV
      GMGVGVQVRUJTTTUKVGVOAVAFPZVCFPZAVEFPZQVKVCFPZABVCFPZFPZQKLMABCGGGUTAQZVDW
      EVFWFWJVBWDVCFUTAVAFULUMUTAVEFULUNVABQZWEWGWFWIWKWDVKVCFVABAFUOUMWKVEWHAF
      VABVCFULUPUNVCCQZWGVLWIVNVCCVKFUOWLWHVMAFVCCBFUOUPUNUQUR $.

    $( A ring element plus itself is two times the element.  (Contributed by
       Steve Rodriguez, 9-Sep-2007.)  (Revised by Mario Carneiro,
       22-Dec-2013.)  (New usage is discouraged.) $)
    rngo2 $p |- ( ( R e. RingOps /\ A e. X ) ->
                  E. x e. X ( A G A ) = ( ( x G x ) H A ) ) $=
      ( crngo wcel wa cv co wceq wrex rngoid oveq12 anidms eqcomd simpll simplr
      simpr rngodir syl13anc eqeq2d syl5ibr adantrd reximdva mpd ) CJKZBFKZLZAM
      ZBENZBOZBUNENBOZLZAFPBBDNZUNUNDNBENZOZAFPABCDEFGHIQUMURVAAFUMUNFKZLZUPVAU
      QUPVAVCUSUOUODNZOUPVDUSUPVDUSOUOBUOBDRSTVCUTVDUSVCUKVBVBULUTVDOUKULVBUAUM
      VBUCZVEUKULVBUBUNUNBCDEFGHIUDUEUFUGUHUIUJ $.
  $}

  ${
    $d G x y z $.  $d R x y z $.
    ringabl.1 $e |- G = ( 1st ` R ) $.
    $( A ring's addition operation is an Abelian group operation.  (Contributed
       by Steve Rodriguez, 9-Sep-2007.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.) $)
    rngoablo $p |- ( R e. RingOps -> G e. AbelOp ) $=
      ( vx vy vz crngo wcel cablo crn cxp c2nd cfv wa cv wceq wral eqid simpld
      co wf w3a wrex rngoi ) AGHZBIHZBJZUGKUGALMZUAZUEUFUINDOZEOZUHTZFOZUHTUJUK
      UMUHTZUHTPUJUKUMBTUHTULUJUMUHTZBTPUJUKBTUMUHTUOUNBTPUBFUGQEUGQDUGQULUKPUK
      UJUHTUKPNEUGQDUGUCNDEFABUHUGCUHRUGRUDSS $.
  $}

  ${
    ringgrp.1 $e |- G = ( 1st ` R ) $.
    $( A ring's addition operation is a group operation.  (Contributed by Steve
       Rodriguez, 9-Sep-2007.)  (New usage is discouraged.) $)
    rngogrpo $p |- ( R e. RingOps -> G e. GrpOp ) $=
      ( crngo wcel cablo cgr rngoablo ablogrpo syl ) ADEBFEBGEABCHBIJ $.
  $}

  ${
    ringgcl.1 $e |- G = ( 1st ` R ) $.
    ringgcl.2 $e |- X = ran G $.
    $( Closure law for the addition (group) operation of a ring.  (Contributed
       by Steve Rodriguez, 9-Sep-2007.)  (New usage is discouraged.) $)
    rngogcl $p |- ( ( R e. RingOps /\ A e. X /\ B e. X ) -> ( A G B ) e. X ) $=
      ( crngo wcel cgr co rngogrpo grpocl syl3an1 ) CHIDJIAEIBEIABDKEICDFLABDEG
      MN $.

    $( The addition operation of a ring is commutative.  (Contributed by Steve
       Rodriguez, 9-Sep-2007.)  (New usage is discouraged.) $)
    rngocom $p |- ( ( R e. RingOps /\ A e. X /\ B e. X ) ->
                      ( A G B ) = ( B G A ) ) $=
      ( crngo wcel cablo co wceq rngoablo ablocom syl3an1 ) CHIDJIAEIBEIABDKBAD
      KLCDFMABDEGNO $.

    $( The addition operation of a ring is associative.  (Contributed by Steve
       Rodriguez, 9-Sep-2007.)  (New usage is discouraged.) $)
    rngoaass $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                        ( ( A G B ) G C ) = ( A G ( B G C ) ) ) $=
      ( crngo wcel cgr w3a co wceq rngogrpo grpoass sylan ) DIJEKJAFJBFJCFJLABE
      MCEMABCEMEMNDEGOABCEFHPQ $.

    $( The addition operation of a ring is commutative.  (Contributed by Steve
       Rodriguez, 9-Sep-2007.)  (New usage is discouraged.) $)
    rngoa32 $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                      ( ( A G B ) G C ) = ( ( A G C ) G B ) ) $=
      ( crngo wcel cablo w3a co wceq rngoablo ablo32 sylan ) DIJEKJAFJBFJCFJLAB
      EMCEMACEMBEMNDEGOABCEFHPQ $.

    $( Rearrangement of 4 terms in a sum of ring elements.  (Contributed by
       Steve Rodriguez, 9-Sep-2007.)  (New usage is discouraged.) $)
    rngoa4 $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X ) /\
                   ( C e. X /\ D e. X ) ) ->
                     ( ( A G B ) G ( C G D ) ) = ( ( A G C ) G ( B G D ) ) ) $=
      ( crngo wcel cablo wa co wceq rngoablo ablo4 syl3an1 ) EJKFLKAGKBGKMCGKDG
      KMABFNCDFNFNACFNBDFNFNOEFHPABCDFGIQR $.

    $( Right cancellation law for the addition operation of a ring.
       (Contributed by Steve Rodriguez, 9-Sep-2007.)
       (New usage is discouraged.) $)
    rngorcan $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                       ( ( A G C ) = ( B G C ) <-> A = B ) ) $=
      ( crngo wcel cgr w3a co wceq wb rngogrpo grporcan sylan ) DIJEKJAFJBFJCFJ
      LACEMBCEMNABNODEGPABCEFHQR $.

    $( Left cancellation law for the addition operation of a ring.
       (Contributed by Steve Rodriguez, 9-Sep-2007.)
       (New usage is discouraged.) $)
    rngolcan $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                       ( ( C G A ) = ( C G B ) <-> A = B ) ) $=
      ( crngo wcel cgr w3a co wceq wb rngogrpo grpolcan sylan ) DIJEKJAFJBFJCFJ
      LCAEMCBEMNABNODEGPABCEFHQR $.
  $}

  ${
    ring0cl.1 $e |- G = ( 1st ` R ) $.
    ring0cl.2 $e |- X = ran G $.
    ring0cl.3 $e |- Z = ( GId ` G ) $.
    $( A ring has an additive identity element.  (Contributed by Steve
       Rodriguez, 9-Sep-2007.)  (New usage is discouraged.) $)
    rngo0cl $p |- ( R e. RingOps -> Z e. X ) $=
      ( crngo wcel cgr rngogrpo grpoidcl syl ) AHIBJIDCIABEKDBCFGLM $.

    $( The additive identity of a ring is a right identity element.
       (Contributed by Steve Rodriguez, 9-Sep-2007.)
       (New usage is discouraged.) $)
    rngo0rid $p |- ( ( R e. RingOps /\ A e. X ) -> ( A G Z ) = A ) $=
      ( crngo wcel cgr co wceq rngogrpo grporid sylan ) BIJCKJADJAECLAMBCFNAECD
      GHOP $.

    $( The additive identity of a ring is a left identity element.
       (Contributed by Steve Rodriguez, 9-Sep-2007.)
       (New usage is discouraged.) $)
    rngo0lid $p |- ( ( R e. RingOps /\ A e. X ) -> ( Z G A ) = A ) $=
      ( crngo wcel cgr co wceq rngogrpo grpolid sylan ) BIJCKJADJEACLAMBCFNAECD
      GHOP $.
  $}

  ${
    ringlz.1 $e |- Z = ( GId ` G ) $.
    ringlz.2 $e |- X = ran G $.
    ringlz.3 $e |- G = ( 1st ` R ) $.
    ringlz.4 $e |- H = ( 2nd ` R ) $.
    $( The zero of a unital ring is a left absorbing element.  (Contributed by
       FL, 31-Aug-2009.)  (New usage is discouraged.) $)
    rngolz $p |- ( ( R e. RingOps /\ A e. X ) -> ( Z H A ) = Z ) $=
      ( crngo wcel wa co wceq cgr rngogrpo grpoidcl grpolid adantr mpdan oveq1d
      syl rngo0cl simpr 3jca rngodir syldan simpl rngocl syl3anc grporid eqcomd
      w3a syl2anc 3eqtr3d wb grpolcan syl13anc mpbid ) BKLZAELZMZFADNZVDCNZVDFC
      NZOZVDFOZVCFFCNZADNZVDVEVFVCVIFADVAVIFOZVBVACPLZVKBCIQZVLFELZVKFCEHGRFFCE
      HGSUAUCTUBVAVBVNVNVBUNVJVEOVCVNVNVBVAVNVBBCEFIHGUDTZVOVAVBUEZUFFFABCDEIJH
      UGUHVCVLVDELZVDVFOVAVLVBVMTZVCVAVNVBVQVAVBUIVOVPFABCDEIJHUJUKZVLVQMVFVDVD
      FCEHGULUMUOUPVCVLVQVNVQVGVHUQVRVSVOVSVDFVDCEHURUSUT $.

    $( The zero of a unital ring is a right absorbing element.  (Contributed by
       FL, 31-Aug-2009.)  (New usage is discouraged.) $)
    rngorz $p |- ( ( R e. RingOps /\ A e. X ) -> ( A H Z ) = Z ) $=
      ( crngo wcel wa co wceq cgr rngogrpo grpoidcl grpolid adantr mpdan oveq2d
      syl w3a simpr rngo0cl rngodi syldan rngocl mpd3an3 eqcomd syl2anc 3eqtr3d
      3jca wb grporcan syl13anc mpbid ) BKLZAELZMZAFDNZVBCNZFVBCNZOZVBFOZVAAFFC
      NZDNZVBVCVDVAVGFADUSVGFOZUTUSCPLZVIBCIQZVJFELZVIFCEHGRFFCEHGSUAUCTUBUSUTU
      TVLVLUDVHVCOVAUTVLVLUSUTUEUSVLUTBCEFIHGUFTZVMUNAFFBCDEIJHUGUHVAVJVBELZVBV
      DOUSVJUTVKTZUSUTVLVNVMAFBCDEIJHUIUJZVJVNMVDVBVBFCEHGSUKULUMVAVJVNVLVNVEVF
      UOVOVPVMVPVBFVBCEHUPUQUR $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                     Examples of rings
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z $.
    $( The set of complex numbers is a (unital) ring.  (Contributed by Steve
       Rodriguez, 2-Feb-2007.)  (Revised by Mario Carneiro, 22-Dec-2013.)
       (New usage is discouraged.) $)
    cnrngo $p |- <. + , x. >. e. RingOps $=
      ( vx vy vz caddc cmul cop wcel cc wa cv co wceq w3a wral cnaddablo pm3.2i
      c1 eqeq1d cvv ax-mp crngo cablo cxp wrex ax-mulf mulass adddi adddir 3jca
      wf rgen3 ax-1cn mulid2 mulid1 jca rgen oveq1 oveq2 anbi12d ralbidv rspcev
      mp2an wb mulex cgr ablogrpo ax-addf fdmi grporn isrngo mpbir2an ) DEFUAGZ
      DUBGZHHUCZHEUJZIZAJZBJZEKZCJZEKVQVRVTEKZEKLZVQVRVTDKEKVSVQVTEKZDKLZVQVRDK
      VTEKWCWADKLZMZCHNBHNAHNZVSVRLZVRVQEKZVRLZIZBHNZAHUDZIZVMVOOUEPWGWMWFABCHH
      HVQHGVRHGZVTHGMWBWDWEVQVRVTUFVQVRVTUGVQVRVTUHUIUKQHGQVREKZVRLZVRQEKZVRLZI
      ZBHNZWMULWTBHWOWQWSVRUMVRUNUOUPWLXAAQHVQQLZWKWTBHXBWHWQWJWSXBVSWPVRVQQVRE
      UQRXBWIWRVRVQQVREURRUSUTVAVBPESGVLVPWNIVCVDABCSDEHDHVMDVEGODVFTVNHDVGVHVI
      VJTVK $.
  $}

  ${
    $d x y z A $.
    ringsn.1 $e |- A e. _V $.
    $( The _trivial_ or _zero_ ring defined on a singleton set ` { A } ` (see
       ~ http://en.wikipedia.org/wiki/Trivial&#x5F;ring ).  (Contributed by
       Steve Rodriguez, 10-Feb-2007.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.) $)
    rngosn $p |- <. { <. <. A , A >. , A >. } , { <. <. A , A >. , A >. } >.
                e. RingOps $=
      ( vx vy vz cop csn wcel wtru a1i wceq cv w3a adantl oveq12d syl6eq eqtr4d
      co elsni syl crngo cablo ablosn crn rnsnop eqcomi cgr cxp wfo wf ablogrpo
      opex grpofo fof 4syl wa 3anim123i simp1 simp2 cfv df-ov fvsn eqtri oveq1d
      simp3 oveq2d snid isrngod trud ) AAFZAFGZVKFUAHICDEAVKVKAGZVKUBHZIABUCJZV
      LVKUDZKIVOVLVJAAAULZUEUFZJIVMVKUGHVLVLUHZVLVKUIVRVLVKUJVNVKUKVKVLVQUMVRVL
      VKUNUOICLZVLHZDLZVLHZELZVLHZMZUPZVSAKZWAAKZWCAKZMZVSWAVKRZWCVKRZVSWAWCVKR
      ZVKRZKWEWJIVTWGWBWHWDWIVSASWAASZWCASUQNZWJWKVSWCWMVKWJWKAVSWJWKAAVKRZAWJV
      SAWAAVKWGWHWIURZWGWHWIUSZOWQVJVKUTAAAVKVAVJAVPBVBVCZPZWRQWJWCAWMWGWHWIVEZ
      WJWMWQAWJWAAWCAVKWSXBOWTPQZOTWFWJWNWKVSWCVKRZVKRKWPWJVSWKWMXDVKWJVSAWKWRX
      AQWJWAVSWCVKWJWAAVSWSWRQVDOTWFWJWLXDWMVKRKWPWJWKXDWCWMVKWJWAWCVSVKWJWAAWC
      WSXBQVFXCOTAVLHIABVGJWBAWAVKRZWAKIWBXEAWAWBXEWQAWBWAAAVKWOVFWTPWOQNWBWAAV
      KRZWAKIWBXFAWAWBXFWQAWBWAAAVKWOVDWTPWOQNVHVI $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Division Rings
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c DivRingOps $.

  $( Extend class notation with the class of all division rings. $)
  cdrng $a class DivRingOps $.

  ${
    $d g h $.
    $( Define the class of all division rings (sometimes called skew fields).
       A division ring is a unital ring where every element except the additive
       identity has a multiplicative inverse.  (Contributed by NM,
       4-Apr-2009.)  (New usage is discouraged.) $)
    df-drngo $a |- DivRingOps = { <. g , h >. | ( <. g , h >. e. RingOps
       /\ ( h |` (
 ( ran g \ { ( GId ` g ) } ) X. ( ran g \ { ( GId ` g ) } ) ) ) e. GrpOp ) } $.
  $}

  ${
    $d g h H $.  $d g h R $.  $d g h X $.  $d g h Z $.
    drngi.1 $e |- G = ( 1st ` R ) $.
    drngi.2 $e |- H = ( 2nd ` R ) $.
    drngi.3 $e |- X = ran G $.
    drngi.4 $e |- Z = ( GId ` G ) $.
    $( The properties of a division ring.  (Contributed by NM, 4-Apr-2009.)
       (New usage is discouraged.) $)
    drngoi $p |- ( R e. DivRingOps -> ( R e. RingOps /\
        ( H |` ( ( X \ { Z } ) X. ( X \ { Z } ) ) ) e. GrpOp ) ) $=
      ( vg vh cdrng wcel crngo cxp cgr wa cfv wceq eleq1d csn cdif cres c1st cv
      c2nd cop crn cgi copab opeq1 id syl6eqr rneqd fveq2d sneqd difeq12d xpeq2
      xpeq1 eqtrd reseq2d anbi12d anbi1d syl6reqr reseq1d anbi2d bitr4d elopabi
      syl opeq2 df-drngo eleq2s wrel relopabi 1st2nd mpan mpbird ) ALMZANMZCDEU
      AZUBZWAOZUCZPMZQAUDRZAUFRZUGZNMZWDQZWIAJUEZKUEZUGZNMZWKWJUHZWJUIRZUAZUBZW
      QOZUCZPMZQZJKUJLXAWEWKUGZNMZWKWBUCZPMZQZWIJKAWJWESZWMXCWTXEXGWLXBNWJWEWKU
      KTXGWSXDPXGWRWBWKXGWQWASZWRWBSXGWNDWPVTXGWNBUHDXGWJBXGWJWEBXGULFUMZUNHUMX
      GWOEXGWOBUIREXGWJBUIXIUOIUMUPUQXHWRWQWAOWBWQWAWQURWQWAWAUSUTVIVATVBWKWFSZ
      XFWHXEQWIXJXCWHXEXJXBWGNWKWFWEVJTVCXJWDXEWHXJWCXDPXJCWKWBXJWKWFCXJULGVDVE
      TVFVGVHJKVKZVLVRVSWHWDVRAWGNLVMVRAWGSXAJKLXKVNALVOVPTVCVQ $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Star Fields
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c *-Fld $.

  $( Extend class notation with the class of all star fields. $)
  csfld $a class *-Fld $.

  ${
    $d f n r x y $.
    $( Define the class of all star fields, which are all division rings with
       involutions.  (Contributed by NM, 29-Aug-2010.)
       (New usage is discouraged.) $)
    df-sfld $a |- *-Fld = { <. r , n >. | ( r e. DivRingOps /\
   n : ran ( 1st ` r ) --> ran ( 1st ` r ) /\
   A. x e. dom n A. y e. dom n
       ( ( n ` ( x ( 1st ` r ) y ) ) = ( ( n ` x ) ( 1st ` r ) ( n ` y ) ) /\
         ( n ` ( x ( 2nd ` r ) y ) ) = ( ( n ` y ) ( 2nd ` r ) ( n ` x ) ) /\
         ( n ` ( n ` x ) ) = x ) ) } $.
  $}

$(
  @{
    @d g h H @.  @d g h R @.  @d g h X @.  @d g h Z @.
    sfldi.1 @e |- R = ( 1st ` F ) @.
    sfldi.2 @e |- N = ( 2nd ` F ) @.
    sfldi.3 @e |- G = ( 1st ` R ) @.
    sfldi.4 @e |- H = ( 2nd ` R ) @.
    sfldi.5 @e |- X = ran G @.
    sfldi.6 @e |- Z = ( GId ` G ) @.
    @( The properties of a star field. @)
    sfldi @p |- ( F e. *-Fld -> ( R e. DivRingOps /\
   N : X --> X /\
   A. x e. X A. y e. X
       ( ( N ` ( x G y ) ) = ( ( N ` x ) G ( N ` y ) ) /\
         ( N ` ( x H y ) ) = ( ( N ` y ) H ( N ` x ) ) /\
         ( N ` ( N ` x ) ) = x ) ) ) @=
      (  ) ? @.
      @( [ ?] @) @( [9-Jun-2009] @)
  @}
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
             Fields and Rings
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Com2 $.

  $( Extend class notation with a class that adds commutativity to various
     flavors of rings. $)
  ccm2 $a class Com2 $.

  ${
    $d g h a b $.
    $( A device to add commutativity to various sorts of rings.  I use
       ` ran g ` because I suppose ` g ` has a neutral element and therefore is
       onto.  (Contributed by FL, 6-Sep-2009.)  (New usage is discouraged.) $)
    df-com2 $a |- Com2 = { <. g , h >. | A. a e. ran g A. b e. ran g
     ( a h b ) = ( b h a ) } $.
  $}

  ${
    $d G a b x y $.  $d H a b x y $.
    $( A device to add commutativity to various sorts of rings.  (Contributed
       by FL, 6-Sep-2009.)  (New usage is discouraged.) $)
    iscom2 $p |- ( ( G e. A /\ H e. B ) -> ( <. G , H >. e. Com2 <->
     A. a e. ran G A. b e. ran G ( a H b ) = ( b H a ) ) ) $=
      ( vy vx wcel wa cop ccm2 cv co wceq crn wral copab df-com2 oveq raleqbidv
      a1i eleq2d rneq raleqdv eqeq12d 2ralbidv opelopabg bitrd ) CAIDBIJZCDKZLI
      UKEMZFMZGMZNZUMULUNNZOZFHMZPZQZEUSQZHGRZIULUMDNZUMULDNZOZFCPZQEVFQZUJLVBU
      KLVBOUJHGEFSUBUCVAUQFVFQZEVFQVGHGCDABURCOZUTVHEUSVFURCUDZVIUQFUSVFVJUEUAU
      NDOZUQVEEFVFVFVKUOVCUPVDULUMUNDTUMULUNDTUFUGUHUI $.
  $}

  $c Fld $.

  $( Extend class notation with the class of all fields. $)
  cfld $a class Fld $.

  $( Add alternate definition. Add Kennington's one (=/= the zero ring),
       and Mizar's one: ` ( GId `` G ) =/= ( GId `` H ) ` $)
  $( Definition of a field.  A field is a commutative division ring.
     (Contributed by FL, 6-Sep-2009.)  (Revised by Jeff Madsen, 10-Jun-2010.)
     (New usage is discouraged.) $)
  df-fld $a |- Fld = ( DivRingOps i^i Com2 ) $.

  $( A field is a division ring.  (Contributed by Jeff Madsen, 10-Jun-2010.)
     (Revised by Mario Carneiro, 15-Dec-2013.)  (New usage is discouraged.) $)
  flddivrng $p |- ( K e. Fld -> K e. DivRingOps ) $=
    ( cfld cdrng ccm2 cin df-fld inss1 eqsstri sseli ) BCABCDECFCDGHI $.

  ${
    rngn0.1 $e |- G = ( 1st ` R ) $.
    rngn0.2 $e |- X = ran G $.
    $( The base set of a ring is not empty.  (Contributed by FL, 24-Jan-2010.)
       (New usage is discouraged.) $)
    rngon0 $p |- ( R e. RingOps -> X =/= (/) ) $=
      ( crngo wcel cgr c0 wne rngogrpo grpon0 syl ) AFGBHGCIJABDKBCELM $.
  $}

  ${
    $d G u x y $.  $d X u x y $.
    $( The range of an internal operation with a left and right identity
       element equals its base set.  (Contributed by FL, 24-Jan-2010.)
       (Revised by Mario Carneiro, 22-Dec-2013.)
       (New usage is discouraged.) $)
    rngmgmbs4 $p |- ( ( G : ( X X. X ) --> X /\
      E. u e. X A. x e. X ( ( u G x ) = x /\ ( x G u ) = x ) )
         -> ran G = X ) $=
      ( vy cxp wf cv co wceq wa wral wrex wfo crn r19.12 wcel simpl eqcomd syl
      oveq2 eqeq2d rspcev ex syl5 reximdv ralimia anim2i foov sylibr forn ) DDF
      ZDCGZBHZAHZCIZUOJZUOUNCIUOJZKZADLBDMZKZULDCNZCODJVAUMUOUNEHZCIZJZEDMZBDMZ
      ADLZKVBUTVHUMUTUSBDMZADLVHUSBADDPVIVGADUODQZUSVFBDUSUOUPJZVJVFUSUPUOUQURR
      SVJVKVFVEVKEUODVCUOJVDUPUOVCUOUNCUAUBUCUDUEUFUGTUHBEADDDCUIUJULDCUKT $.
  $}

  ${
    rnplrnml0.1 $e |- H = ( 2nd ` R ) $.
    rnplrnml0.2 $e |- G = ( 1st ` R ) $.
    $( In a unital ring the domain of the first variable of the addition equals
       the domain of the first variable of the multiplication.  (Contributed by
       FL, 24-Jan-2010.)  (New usage is discouraged.) $)
    rngodm1dm2 $p |- ( R e. RingOps -> dom dom G = dom dom H ) $=
      ( crngo wcel crn cxp wfo cdm wceq cgr rngogrpo eqid grpofo syl rngosm fdm
      wf fof wi wa eqtr dmeqd expcom eqcoms syl5com sylc ) AFGZBHZUKIZUKBJZULUK
      CTZBKZKCKZKLZUJBMGUMABENBUKUKOZPQABCUKEDURRUMUOULLZUNUQUMULUKBTUSULUKBUAU
      LUKBSQUNUPULLUSUQUBZULUKCSUTULUPUSULUPLZUQUSVAUCUOUPUOULUPUDUEUFUGQUHUI
      $.

    $( In a unital ring the range of the addition equals the domain of the
       first variable of the multiplication.  (Contributed by FL,
       24-Jan-2010.)  (New usage is discouraged.) $)
    rngorn1 $p |- ( R e. RingOps -> ran G = dom dom H ) $=
      ( crngo wcel crn cdm cgr wceq rngogrpo grporndm syl rngodm1dm2 eqtrd ) AF
      GZBHZBIIZCIIQBJGRSKABELBMNABCDEOP $.

    ${
      $d G x y z $.  $d H x y z $.  $d R x $.
      $( In a unital ring the range of the addition equals the range of the
         multiplication.  (Contributed by FL, 24-Jan-2010.)
         (New usage is discouraged.) $)
      rngorn1eq $p |- ( R e. RingOps -> ran G = ran H ) $=
        ( vx vy vz crngo wcel crn cxp wf cv co wceq wa wral wrex eqid cablo w3a
        rngosm rngoi simprr syl rngmgmbs4 syl2anc eqcomd ) AIJZCKZBKZUJULULLULC
        MZFNZGNZCOZUOPUOUNCOUOPQGULRFULSZUKULPABCULEDULTZUCUJBUAJUMQZUPHNZCOUNU
        OUTCOZCOPUNUOUTBOCOUPUNUTCOZBOPUNUOBOUTCOVBVABOPUBHULRGULRFULRZUQQQUQFG
        HABCULEDURUDUSVCUQUEUFGFCULUGUHUI $.
    $}
  $}

  ${
    $d H x y z $.  $d R x y z $.
    unmnd.1 $e |- H = ( 2nd ` R ) $.
    $( In a unital ring the multiplication is a monoid.  (Contributed by FL,
       24-Jan-2010.)  (Revised by Mario Carneiro, 22-Dec-2013.)
       (New usage is discouraged.) $)
    rngomndo $p |- ( R e. RingOps -> H e. MndOp ) $=
      ( vx vy vz wcel cdm cxp wf cv co wceq wral wa wrex w3a eqid wb cvv rngosm
      crngo cmndo cfv crn rngoass ralrimivvva cablo rngoi simprd rngorn1 xpid11
      c1st biimpri feq23 raleq raleqbi1dv rexeqbi1dv 3anbi123d eqcoms mpbir3and
      mpancom syl c2nd fvex eleq1 mpbiri ismndo1 mp2b sylibr ) AUBGZBHHZVLIZVLB
      JZDKZEKZBLZFKZBLVOVPVRBLZBLMZFVLNZEVLNZDVLNZVQVPMVPVOBLVPMOZEVLNZDVLPZQZB
      UCGZVKWGAUMUDZUEZWJIZWJBJZVTFWJNZEWJNZDWJNZWDEWJNZDWJPZAWIBWJWIRZCWJRZUAV
      KVTDEFWJWJWJVOVPVRAWIBWJWRCWSUFUGVKVTVOVPVRWILBLVQVOVRBLZWILMVOVPWILVRBLW
      TVSWILMQFWJNEWJNDWJNZWQVKWIUHGWLOXAWQODEFAWIBWJWRCWSUIUJUJVKWJVLMWGWLWOWQ
      QSZAWIBCWRUKXBVLWJVLWJMZVNWLWCWOWFWQVMWKMZXCVNWLSXDXCVLWJULUNVMVLWKWJBUOV
      BWBWNDVLWJWAWMEVLWJVTFVLWJUPUQUQWEWPDVLWJWDEVLWJUPURUSUTVCVABAVDUDZMZBTGZ
      WHWGSCXFXGXETGAVDVEBXETVFVGDEFTBVLVLRVHVIVJ $.
  $}

  $( In a unital ring the addition is an abelian group.  (Contributed by FL,
     31-Aug-2009.)  (New usage is discouraged.) $)
  rngoablo2 $p |- ( <. G , H >. e. RingOps -> G e. AbelOp ) $=
    ( cop crngo wcel c1st cfv cablo wbr wceq cvv wa wrel relrngo brrelex12 mpan
    df-br op1stg syl sylbir eqid rngoablo eqeltrrd ) ABCZDEZUDFGZAHUEABDIZUFAJZ
    ABDQUGAKEBKELZUHDMUGUINABDOPABKKRSTUDUFUFUAUBUC $.

  ${
    uridm.1 $e |- H = ( 2nd ` R ) $.
    uridm.2 $e |- X = ran ( 1st ` R ) $.
    ${
      uridm.3 $e |- U = ( GId ` H ) $.
      $( The unit of a ring is an identity element for the multiplication.
         (Contributed by FL, 18-Feb-2010.)  (New usage is discouraged.) $)
      rngoidmlem $p |- ( ( R e. RingOps /\ A e. X ) ->
        ( ( U H A ) = A /\ ( A H U ) = A ) ) $=
        ( crngo wcel co wceq wa wi crn cmndo cmagm cexid eqid ex mndomgmid 3syl
        cin rngomndo cmpidelt c1st cfv wb rngorn1eq eqtr eleq2d imbi1d syl mpan
        simpl mpcom mpbird imp ) BIJZAEJZCADKALACDKALMZUSUTVANZADOZJZVANZUSDPJD
        QRUCJZVEBDFUDDUAVFVDVAACDVCVCSHUETUBBUFUGZOZVCLZUSVBVEUHZBVGDFVGSUIEVHL
        ZVIUSVJNZGVKVIMEVCLZVLEVHVCUJVMUSVJVMUSMZUTVDVAVNEVCAVMUSUOUKULTUMUNUPU
        QUR $.

      $( The unit of a ring is an identity element for the multiplication.
         (Contributed by FL, 18-Apr-2010.)  (New usage is discouraged.) $)
      rngolidm $p |- ( ( R e. RingOps /\ A e. X ) -> ( U H A ) = A ) $=
        ( crngo wcel wa co wceq rngoidmlem simpld ) BIJAEJKCADLAMACDLAMABCDEFGH
        NO $.
    $}

    ${
      uridm2.2 $e |- U = ( GId ` H ) $.
      $( The unit of a ring is an identity element for the multiplication.
         (Contributed by FL, 18-Apr-2010.)  (New usage is discouraged.) $)
      rngoridm $p |- ( ( R e. RingOps /\ A e. X ) -> ( A H U ) = A ) $=
        ( crngo wcel wa co wceq rngoidmlem simprd ) BIJAEJKCADLAMACDLAMABCDEFGH
        NO $.
    $}
  $}

  ${
    $d A x $.  $d R x $.  $d X x $.
    on1el3.1 $e |- G = ( 1st ` R ) $.
    on1el3.2 $e |- X = ran G $.
    $( The only unital ring with a base set consisting in one element is the
       zero ring.  (Contributed by FL, 13-Feb-2010.)  (Proof shortened by Mario
       Carneiro, 30-Apr-2015.)  (New usage is discouraged.) $)
    rngosn3 $p |- ( ( R e. RingOps /\ A e. B ) -> ( X = { A } <-> R =
       <. { <. <. A , A >. , A >. } , { <. <. A , A >. , A >. } >. ) ) $=
      ( crngo wcel wa csn wceq cfv cop cxp wf adantr syl5ibcom cvv wb c2nd c1st
      cgr wfo rngogrpo grpofo fof 3syl xpeq12d feq23d cdm fdm syl eqcomd eqeq2d
      xpid11 syl6ib impbid simpr xpsng sylancom opex fsng sylancr 3bitrd eqeq1i
      id feq2d syl6bb anbi1d eqid rngosm sylibd pm4.71d wrel wss relrngo df-rel
      bitrd mpbi sseli eqop 3bitr4d ) CHIZABIZJZEAKZLZCUAMZAANZANKZLZJCUBMZWKLZ
      WLJZWHCWKWKNLZWFWHWNWLWFWHDWKLZWNWFWHWGWGOZWGDPZWJKZWGDPZWQWFWHWSWFEEOZED
      PZWHWSWDXCWEWDDUCIXBEDUDXCCDFUEDEGUFXBEDUGUHQZWHXBEWRWGDWHEWGEWGWHVGZXEUI
      ZXEUJRWFWSXBWRLZWHWFXBDUKZLWSXGWFXHXBWFXCXHXBLXDXBEDULUMUNWSXHWRXBWRWGDUL
      UOREWGUPUQURWFWRWTWGDWDWEWEWRWTLWDWEUSZAABBUTVAZVHWFWJSIZWEXAWQTAAVBZXIWJ
      ASBDVCVDVEDWMWKFVFVIVJWFWHWLWFWHWRWGWIPZWLWFXBEWIPZWHXMWDXNWECDWIEFWIVKGV
      LQWHXBEWRWGWIXFXEUJRWFXMWTWGWIPZWLWFWRWTWGWIXJVHWFXKWEXOWLTXLXIWJASBWIVCV
      DVSVMVNWFCSSOZIZWPWOTWDXQWEHXPCHVOHXPVPVQHVRVTWAQCWKWKSSWBUMWC $.

    ${
      $d A x $.  $d R x $.  $d X x $.
      $( The only unital ring with one element is the zero ring.  (Contributed
         by FL, 14-Feb-2010.)  (Revised by Mario Carneiro, 30-Apr-2015.)
         (New usage is discouraged.) $)
      rngosn4 $p |- ( ( R e. RingOps /\ A e. X ) -> ( X ~~ 1o <-> R =
       <. { <. <. A , A >. , A >. } , { <. <. A , A >. , A >. } >. ) ) $=
        ( crngo wcel wa c1o cen wbr csn wceq cop wb en1eqsn ex ensn1g breq1
        syl5ibrcom impbid adantl rngosn3 bitrd ) BGHZADHZIDJKLZDAMZNZBAAOAOMZUK
        ONUGUHUJPUFUGUHUJUGUHUJADQRUGUHUJUIJKLADSDUIJKTUAUBUCADBCDEFUDUE $.
    $}

    ${
      on1el3.3 $e |- Z = ( GId ` G ) $.
      $( The only unital ring with one element is the zero ring.  (Contributed
         by FL, 15-Feb-2010.)  (New usage is discouraged.) $)
      rngosn6 $p |- ( R e. RingOps -> ( X ~~ 1o <-> R =
        <. { <. <. Z , Z >. , Z >. } , { <. <. Z , Z >. , Z >. } >. ) ) $=
        ( crngo wcel c1o cen wbr cop csn wceq wb rngo0cl rngosn4 mpdan ) AHIDCI
        CJKLADDMDMNZTMOPABCDEFGQDABCEFRS $.
    $}
  $}

  ${
    $d H u x $.  $d X u x $.
    ring1cl.1 $e |- X = ran ( 1st ` R ) $.
    ring1cl.2 $e |- H = ( 2nd ` R ) $.
    ring1cl.3 $e |- U = ( GId ` H ) $.
    $( The unit of a ring belongs to the base set.  (Contributed by FL,
       12-Feb-2010.)  (New usage is discouraged.) $)
    rngo1cl $p |- ( R e. RingOps -> U e. X ) $=
      ( crngo wcel c2nd cfv crn cmagm cexid wa cmndo syl eqid cgi wceq rngomndo
      cin eleq1i mndoismgm mndoisexid jca sylbi elin sylibr fveq2i eqtri iorlid
      c1st wb rngorn1eq eqtr eleq2d sylancr mpbird ) AHIZBDIZBAJKZLZIZUTVBMNUBI
      ZVDUTVBMIZVBNIZOZVEUTCPIZVHACFUAVIVBPIZVHCVBPFUCVJVFVGVBUDVBUEUFUGQVBMNUH
      UIBVBVCVCRBCSKVBSKGCVBSFUJUKULQUTDAUMKZLZTZVLVCTZVAVDUNEAVKVBVBRVKRUOVMVN
      ODVCBDVLVCUPUQURUS $.
  $}

  ${
    $d R x $.  $d U x $.  $d X x $.  $d Z x $.
    uznzr.1 $e |- G = ( 1st ` R ) $.
    uznzr.2 $e |- H = ( 2nd ` R ) $.
    uznzr.3 $e |- Z = ( GId ` G ) $.
    uznzr.4 $e |- U = ( GId ` H ) $.
    uznzr.5 $e |- X = ran G $.
    $( In a unital ring the zero equals the unity iff the ring is the zero
       ring.  (Contributed by FL, 14-Feb-2010.)  (New usage is discouraged.) $)
    rngoueqz $p |- ( R e. RingOps -> ( X ~~ 1o <-> U = Z ) ) $=
      ( vx wcel c1o wceq wi wa syl ex wral cen wbr rngo0cl csn en1eqsn crn c1st
      crngo rneqi rngo1cl eleq2 biimpd elsni syl6com eqcomi syl5com com23 mpcom
      cfv eleq2s c0 wne rngon0 cv oveq2 ralrimivw rngorz ralrimiva eqtri r19.26
      rngoridm eqtr eqcoms imp31 ralimi eqsn ensn1g breq1 syl5ibr syl6bir com3l
      co sylbir com24 mpd com13 impbid ) AUHMZENUAUBZBFOZFEMZWHWIWJPACEFGKIUCZW
      KWIWHWJWKWIWHWJPWKWIQEFUDZOZWHWJFEUEWHBCUFZMWNWJPZABDWOCAUGUSZGUIZHJUJWPB
      EWOWNBEMZBWMMZWJWNWSWTEWMBUKULBFUMUNEWOKUOUTRUPSUQUREVAVBZWHWJWIPACEGKVCW
      JWHXAWIWJLVDZBDWBZXBFDWBZOZLETZWHXAWIPZWJXELEBFXBDVEVFWHXDFOZLETZXFXGPZWH
      XHLEXBACDEFIKGHVGVHXCXBOZLETZWHXIXJPWHXKLEXBABDEHEWOWQUFKWRVIJVKVHXLXFXIW
      HXGXLXFXIWHXGPZPZXLXFQXKXEQZLETZXNXKXELEVJXPXIXMXPXIQXOXHQZLETZXMXOXHLEVJ
      XRXBFOZLETZXMXQXSLEXKXEXHXSXEXHXSPZPXBXCXBXCOZXEYAYBXEQXBXDOZYAXBXCXDVLYC
      XHXSXBXDFVLSRSVMVNVOXAXTWHWIXAXTWNWHWIPLEFVPWHWIWNWMNUAUBZWHWKYDWLFEVQREW
      MNUAVRVSVTWARWCSWCSWDURWEUPWFURWG $.
  $}

  ${
    $d G g h $.  $d H g h $.  $d x y $.
    $( The predicate "is a division ring".  (Contributed by FL, 6-Sep-2009.)
       (New usage is discouraged.) $)
    isdivrngo $p |- ( H e. A -> ( <. G , H >. e. DivRingOps
     <-> ( <. G , H >. e. RingOps /\ ( H |` (
       ( ran G \ { ( GId ` G ) } ) X. ( ran G \ { ( GId ` G ) } ) ) )
         e. GrpOp ) ) ) $=
      ( vx vy vg vh wcel cop cdrng crngo crn cgi cfv csn cres cgr wa cv eleq1d
      cdif cxp cvv wbr df-br df-drngo relopabi brrelexi sylbir anim1i rngoablo2
      ancoms cablo elex ad2antrl simpl copab eleq2i wceq opeq1 rneq fveq2 sneqd
      syl jca difeq12d xpeq12d reseq2d anbi12d reseq1 opelopabg syl5bb pm5.21nd
      opeq2 ) CAHZBCIZJHZVPKHZCBLZBMNZOZUAZWBUBZPZQHZRZBUCHZVORZVQVOWHVQWGVOVQB
      CJUDWGBCJUEBCJDSZESZIKHWJWILWIMNOUAZWKUBPQHRDEJDEUFUGUHUIUJULVOWFRWGVOVRW
      GVOWEVRBUMHWGBCUKBUMUNVDUOVOWFUPVEVQVPFSZGSZIZKHZWMWLLZWLMNZOZUAZWSUBZPZQ
      HZRZFGUQZHWHWFJXDVPFGUFURXCBWMIZKHZWMWCPZQHZRWFFGBCUCAWLBUSZWOXFXBXHXIWNX
      EKWLBWMUTTXIXAXGQXIWTWCWMXIWSWBWSWBXIWPVSWRWAWLBVAXIWQVTWLBMVBVCVFZXJVGVH
      TVIWMCUSZXFVRXHWEXKXEVPKWMCBVNTXKXGWDQWMCWCVJTVIVKVLVM $.
  $}

  ${
    zrdivrng.1 $e |- A e. _V $.
    $( The zero ring is not a division ring.  (Contributed by FL,
       24-Jan-2010.)  (Proof shortened by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    zrdivrng $p |- -.
      <. { <. <. A , A >. , A >. } , { <. <. A , A >. , A >. } >.
         e. DivRingOps $=
      ( cop csn cdrng wcel c0 cgr 0ngrp crn cgi cfv cdif cres opex rnsnop gidsn
      cxp eqtri cvv sneqi difeq12i difid xpeq2i reseq2i res0 crngo wa isdivrngo
      xp0 wb snex ax-mp simprbi syl5eqelr mto ) AACZACZDZUSCZEFZGHFIVAGUSUSJZUS
      KLZDZMZVERZNZHVGUSGNGVFGUSVFVEGRGVEGVEVEADZVHMGVBVHVDVHUQAAAOPVCAABQUAUBV
      HUCSUDVEUJSUEUSUFSVAUTUGFZVGHFZUSTFVAVIVJUHUKURULTUSUSUIUMUNUOUP $.
  $}

  ${
    dvrunz.1 $e |- G = ( 1st ` R ) $.
    dvrunz.2 $e |- H = ( 2nd ` R ) $.
    dvrunz.3 $e |- X = ran G $.
    dvrunz.4 $e |- Z = ( GId ` G ) $.
    dvrunz.5 $e |- U = ( GId ` H ) $.
    $( In a division ring the unit is different from the zero.  (Contributed by
       FL, 14-Feb-2010.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    dvrunz $p |- ( R e. DivRingOps -> U =/= Z ) $=
      ( cdrng wcel cop csn wn cgi wceq wb syl wne cfv cvv fvex eqeltri zrdivrng
      c1o cen wbr crngo cdif cxp cres cgr drngoi simpld rngoueqz rngosn6 biimpd
      wi eleq1 syl6bi pm2.43a sylbird necon3bd mpi ) ALMZFFNFNOZVHNZLMZPBFUAFFC
      QUBUCJCQUDUEUFVGVJBFVGBFRZEUGUHUIZVJVGAUJMZVLVKSVGVMDEFOUKZVNULUMUNMACDEF
      GHIJUOUPZABCDEFGHJKIUQTVLVGVJVGVLAVIRZVGVJUTVGVMVLVPSVOACEFGIJURTVPVGVJAV
      ILVAUSVBVCVDVEVF $.
  $}

  ${
    zerdivemp.1 $e |- G = ( 1st ` R ) $.
    zerdivemp.2 $e |- H = ( 2nd ` R ) $.
    zerdivemp.3 $e |- Z = ( GId ` G ) $.
    zerdivemp.4 $e |- X = ran G $.
    zerdivemp.5 $e |- U = ( GId ` H ) $.
    ${
      $d A a $.  $d B a $.  $d H a $.  $d R a $.  $d X a $.  $d Z a $.
      $( In a unitary ring a left invertible element is not a zero divisor.
         (Contributed by FL, 18-Apr-2010.) $)
      zerdivemp1 $p |- ( ( R e. RingOps /\ A e. ( X \ Z ) /\
      E. a e. X ( a H A ) = U ) ->
         ( B e. X -> ( ( A H B ) = Z -> B = Z ) ) ) $=
        ( wcel co wceq wi w3a 3exp crngo cdif wrex oveq2 simpl1 simpr1 3ad2ant3
        cv wa eldifi adantl simpl3 rngoass syl13anc ex oveq1 rngorz 3adant3 crn
        eqtr c1st cfv rneqi eqtri 3adant2 simp1 simp2 simp3 3eqtr3d com14 com13
        rngolidm a1d sylc com15 com24 syl com25 com12 3imp syl6 3imp1 mpd 3exp1
        eqcoms syl5com rexlimiv ) CUAOZAGHUBOZIUHZAFPZDQZIGUCZBGOZABFPZHQZBHQZR
        RZWMWIWHWRWLWIWHWRRZRIGWJGOZWLWIWSWPWHWNWTWLWISZWQWPWJWOFPZWJHFPZQZWHWN
        XAWQRRWOHWJFUDWHXDWNXAWQWHXDWNSZXAUIZWKBFPZXBQZWQXFWHWTAGOZWNXHWHXDWNXA
        UEXEWTWLWIUFXAXIXEWIWTXIWLAGHUJUGUKWHXDWNXAULWJABCEFGJKMUMUNWHXDWNXAXHW
        QRXHXDWNXAWHWQXHXDXGXCQZWNXAWHWQRZRRXHXDXJXGXBXCUTUOXAWNXJXKWTWLWIWNXJX
        KRRZWLWTWIXLRZWLXGDBFPZQZWTXMRWKDBFUPXOXJWIWNWTXKXJWIWNWTXKRRRZRXNXGXNX
        GQZXJXPXQXJUIXNXCQZXPXNXGXCUTXRWTWNWIXKWHWTWNWIXRWQWHWTWNWIXRWQRZRZWHWT
        WNSXCHQZXNBQZXTWHWTYAWNWJCEFGHLMJKUQURWHWNYBWTBCDFGKGEUSCVAVBZUSMEYCJVC
        VDNVLVEWIYBYAXSXRYBYAWIWQXRYBYAWIWQRXRYBYASZWQWIYDXNXCBHXRYBYAVFXRYBYAV
        GXRYBYAVHVIVMTVJVKVNTVOVPVQUOWEVRVQVSVTVKWAVOWBWCWDWFVJTWGVKVT $.
    $}

    ${
      $d A a $.  $d R a $.  $d U a $.  $d X a $.  $d Z a $.
      $( In a unitary ring a left invertible element is different from zero iff
         ` 1 =/= 0 ` .  (Contributed by FL, 18-Apr-2010.) $)
      rngoridfz $p |- ( ( R e. RingOps /\ A e. X /\
         E. a e. X ( a H A ) = U ) -> ( A =/= Z <-> U =/= Z ) ) $=
        ( wcel co wceq w3a wi wa imp crngo cv wrex rngorz eqeq12 biimpd syl5com
        wb oveq2 ex com3l 3adant3 syl5 crn c1st cfv rneqi eqtri rngoridm expcom
        syl2anc 3ad2ant3 impbid 3exp1 rexlimiv com13 3imp necon3bid ) BUANZAFNZ
        HUBZAEOZCPZHFUCZQAGCGVIVJVNAGPZCGPZUHZVNVJVIVQVMVJVIVQRRHFVKFNZVMVJVIVQ
        VRVMVJQZVISZVOVPVOVLVKGEOZPZVTVPAGVKEUIVSVIWBVPRZVRVMVIWCRZVJVRVMWDVIVR
        VMWCVIVRVMWCRVIVRSWAGPZVMWCVKBDEFGKLIJUDVMWEWCVMWESWBVPVLCWAGUEUFUJUGUJ
        UKTULTUMVPACEOZAGEOZPZVTVOCGAEUIVSVIWHVORZVJVRVIWIRVMVIVJWIVIVJSWFAPZWG
        GPZWIABCEFJFDUNBUOUPZUNLDWLIUQURMUSABDEFGKLIJUDWJWKSWHVOWFAWGGUEUFVAUTV
        BTUMVCVDVEVFVGVH $.
    $}
  $}

$(
###############################################################################
               COMPLEX TOPOLOGICAL VECTOR SPACES (DEPRECATED)
###############################################################################
$)

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
      cmul cvc df-vc relopabi ) AFZGHIUDJZKUEBFZLMCFZUFNUGODFZUGEFZUDNUFNUHUGUF
      NZUHUIUFNUDNOEUEPUHUIQNUGUFNUJUIUGUFNZUDNOUHUITNUGUFNUHUKUFNOREIPRDIPRCUE
      PSABUACDEABUBUC $.
  $}

  ${
    $d g s w x y z G $.  $d g s w x y z S $.  $d g s W $.  $d g s w x y z X $.
    $d w x y z A $.  $d w x y z B $.  $d x y z C $.
    vci.1 $e |- G = ( 1st ` W ) $.
    vci.2 $e |- S = ( 2nd ` W ) $.
    vci.3 $e |- X = ran G $.
    $( The properties of a complex vector space, which is an Abelian group
       (i.e. the vectors, with the operation of vector addition) accompanied by
       a scalar multiplication operation on the field of complex numbers.  The
       variable ` W ` was chosen because ` _V ` is already used for the
       universal class.  (Contributed by NM, 3-Nov-2006.)
       (New usage is discouraged.) $)
    vci $p |- ( W e. CVecOLD ->
              ( G e. AbelOp /\
         S : ( CC X. X ) --> X /\ A. x e. X ( ( 1 S x ) = x /\
       A. y e. CC ( A. z e. X ( y S ( x G z ) ) = ( ( y S x ) G ( y S z ) )
         /\ A. z e. CC ( ( ( y + z ) S x ) = ( ( y S x ) G ( z S x ) ) /\
           ( ( y x. z ) S x ) = ( y S ( z S x ) ) ) ) ) ) ) $=
      ( vg vs cc cv co wceq wral wa oveq ralbidv cablo wcel cxp wf c1 caddc w3a
      cmul crn copab cvc c1st cfv wb eqeq2i eleq1 rneq syl6eqr xpeq2 feq2d feq3
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
      ( vx vy vz cvc wcel cablo cc cxp cv co wceq wral wa wf c1 cmul vci simp2d
      caddc ) CKLBMLNDODAUAUBHPZAQUGRIPZUGJPZBQAQUHUGAQZUHUIAQBQRJDSUHUIUFQUGAQ
      UJUIUGAQZBQRUHUIUCQUGAQUHUKAQRTJNSTINSTHDSHIJABCDEFGUDUE $.

    $( Closure of the scalar product of a complex vector space.  (Contributed
       by NM, 3-Nov-2006.)  (New usage is discouraged.) $)
    vccl $p |- ( ( W e. CVecOLD /\ A e. CC /\ B e. X ) -> ( A S B ) e. X ) $=
      ( cvc wcel cc cxp wf co vcsm fovrn syl3an1 ) EJKLFMFCNALKBFKABCOFKCDEFGHI
      PABFLFCQR $.

    $( Identity element for the scalar product of a complex vector space.
       (Contributed by NM, 3-Nov-2006.)  (New usage is discouraged.) $)
    vcid $p |- ( ( W e. CVecOLD /\ A e. X ) -> ( 1 S A ) = A ) $=
      ( vx vy vz cvc wcel c1 cv co wceq wral cc wa cablo cxp caddc cmul w3a vci
      wf simpl ralimi 3ad2ant3 syl oveq2 id eqeq12d rspccva sylan ) DLMZNIOZBPZ
      URQZIERZAEMNABPZAQZUQCUAMZSEUBEBUGZUTJOZURKOZCPBPVFURBPZVFVGBPCPQKERVFVGU
      CPURBPVHVGURBPZCPQVFVGUDPURBPVFVIBPQTKSRTJSRZTZIERZUEVAIJKBCDEFGHUFVLVDVA
      VEVKUTIEUTVJUHUIUJUKUTVCIAEURAQZUSVBURAURANBULVMUMUNUOUP $.

    $( Distributive law for the scalar product of a complex vector space.
       (Contributed by NM, 3-Nov-2006.)  (New usage is discouraged.) $)
    vcdi $p |- ( ( W e. CVecOLD /\ ( A e. CC /\ B e. X /\ C e. X ) ) ->
       ( A S ( B G C ) ) = ( ( A S B ) G ( A S C ) ) ) $=
      ( vy vx vz cc wcel w3a co wceq wral oveq1 cvc wi cv cablo cxp wf c1 caddc
      cmul wa vci simpl ralimi adantl 3ad2ant3 syl oveq2d oveq2 eqeq12d oveq12d
      oveq1d rspc3v syl5 3com12 impcom ) ANOZBGOZCGOZPFUAOZABCEQZDQZABDQZACDQZE
      QZRZVGVFVHVIVOUBVIKUCZLUCZMUCZEQZDQZVPVQDQZVPVRDQZEQZRZMGSZKNSZLGSZVGVFVH
      PVOVIEUDOZNGUEGDUFZUGVQDQVQRZWEVPVRUHQVQDQWAVRVQDQZEQRVPVRUIQVQDQVPWKDQRU
      JMNSZUJZKNSZUJZLGSZPWGLKMDEFGHIJUKWPWHWGWIWOWFLGWNWFWJWMWEKNWEWLULUMUNUMU
      OUPWDVOVPBVREQZDQZVPBDQZWBEQZRAWQDQZVLAVRDQZEQZRLKMBACGNGVQBRZVTWRWCWTXDV
      SWQVPDVQBVRETUQXDWAWSWBEVQBVPDURVAUSVPARZWRXAWTXCVPAWQDTXEWSVLWBXBEVPABDT
      VPAVRDTUTUSVRCRZXAVKXCVNXFWQVJADVRCBEURUQXFXBVMVLEVRCADURUQUSVBVCVDVE $.

    $( Distributive law for the scalar product of a complex vector space.
       (Contributed by NM, 3-Nov-2006.)  (New usage is discouraged.) $)
    vcdir $p |- ( ( W e. CVecOLD /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
      ( ( A + B ) S C ) = ( ( A S C ) G ( B S C ) ) ) $=
      ( vy vz vx cc wcel caddc co wceq wral oveq2 w3a cvc wi cv cablo cxp wf c1
      cmul wa vci simpl ralimi adantl 3ad2ant3 syl oveq12d eqeq12d oveq1 oveq1d
      oveq2d rspc3v syl5 3coml impcom ) ANOZBNOZCGOZUAFUBOZABPQZCDQZACDQZBCDQZE
      QZRZVHVFVGVIVOUCVIKUDZLUDZPQZMUDZDQZVPVSDQZVQVSDQZEQZRZLNSZKNSZMGSZVHVFVG
      UAVOVIEUEOZNGUFGDUGZUHVSDQVSRZVPVSVQEQDQWAVPVQDQEQRLGSZWDVPVQUIQVSDQVPWBD
      QRZUJZLNSZUJZKNSZUJZMGSZUAWGMKLDEFGHIJUKWRWHWGWIWQWFMGWPWFWJWOWEKNWNWEWKW
      MWDLNWDWLULUMUNUMUNUMUOUPWDVOVRCDQZVPCDQZVQCDQZEQZRAVQPQZCDQZVLXAEQZRMKLC
      ABGNNVSCRZVTWSWCXBVSCVRDTXFWAWTWBXAEVSCVPDTVSCVQDTUQURVPARZWSXDXBXEXGVRXC
      CDVPAVQPUSUTXGWTVLXAEVPACDUSUTURVQBRZXDVKXEVNXHXCVJCDVQBAPTUTXHXAVMVLEVQB
      CDUSVAURVBVCVDVE $.

    $( Associative law for the scalar product of a complex vector space.
       (Contributed by NM, 3-Nov-2006.)  (New usage is discouraged.) $)
    vcass $p |- ( ( W e. CVecOLD /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
      ( ( A x. B ) S C ) = ( A S ( B S C ) ) ) $=
      ( vy vz vx cc wcel w3a cmul co wceq wral cvc wi cv cablo cxp wf caddc vci
      c1 wa simpr ralimi adantl 3ad2ant3 syl oveq2 oveq2d eqeq12d oveq1d rspc3v
      oveq1 syl5 3coml impcom ) ANOZBNOZCGOZPFUAOZABQRZCDRZABCDRZDRZSZVGVEVFVHV
      MUBVHKUCZLUCZQRZMUCZDRZVNVOVQDRZDRZSZLNTZKNTZMGTZVGVEVFPVMVHEUDOZNGUEGDUF
      ZUIVQDRVQSZVNVQVOERDRVNVQDRZVNVODRERSLGTZVNVOUGRVQDRWHVSERSZWAUJZLNTZUJZK
      NTZUJZMGTZPWDMKLDEFGHIJUHWPWEWDWFWOWCMGWNWCWGWMWBKNWLWBWIWKWALNWJWAUKULUM
      ULUMULUNUOWAVMVPCDRZVNVOCDRZDRZSAVOQRZCDRZAWRDRZSMKLCABGNNVQCSZVRWQVTWSVQ
      CVPDUPXCVSWRVNDVQCVODUPUQURVNASZWQXAWSXBXDVPWTCDVNAVOQVAUSVNAWRDVAURVOBSZ
      XAVJXBVLXEWTVICDVOBAQUPUSXEWRVKADVOBCDVAUQURUTVBVCVD $.

    $( A vector plus itself is two times the vector.  (Contributed by NM,
       1-Feb-2007.)  (New usage is discouraged.) $)
    vc2 $p |- ( ( W e. CVecOLD /\ A e. X ) -> ( A G A ) = ( 2 S A ) ) $=
      ( cvc wcel wa c1 co c2 vcid oveq12d caddc df-2 oveq1i ax-1cn wceq mp3anr1
      cc vcdir mpanr1 syl5req eqtr3d ) DIJZAEJZKZLABMZUKCMZAACMNABMZUJUKAUKACAB
      CDEFGHOZUNPUJUMLLQMZABMZULNUOABRSUHLUCJZUIUPULUAZTUHUQUQUIURTLLABCDEFGHUD
      UBUEUFUG $.

    $( Subtractive distributive law for the scalar product of a complex vector
       space.  (Contributed by NM, 31-Jul-2007.)
       (New usage is discouraged.) $)
    vcsubdir $p |- ( ( W e. CVecOLD /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
      ( ( A - B ) S C ) = ( ( A S C ) G ( -u 1 S ( B S C ) ) ) ) $=
      ( cvc wcel cc w3a wa co cneg wceq oveq1d eqtr3d cmin c1 caddc negcl vcdir
      syl3anr2 negsub 3adant3 adantl cmul mulm1 ad2antrl vcass mp3anr1 3adantr1
      neg1cn oveq2d ) FKLZAMLZBMLZCGLZNZOZACDPZBQZCDPZEPZABUAPZCDPZVDUBQZBCDPDP
      ZEPVCAVEUCPZCDPZVGVIUTUSURVEMLVAVMVGRBUDAVECDEFGHIJUEUFVCVLVHCDVBVLVHRZUR
      USUTVNVAABUGUHUISTVCVFVKVDEURUTVAVFVKRUSURUTVAOOZVJBUJPZCDPZVFVKVOVPVECDU
      TVPVERURVABUKULSURVJMLUTVAVQVKRUPVJBCDEFGHIJUMUNTUOUQT $.
  $}

  ${
    $d x y z G $.  $d x y z W $.
    vcabl.1 $e |- G = ( 1st ` W ) $.
    $( Vector addition is an Abelian group operation.  (Contributed by NM,
       3-Nov-2006.)  (New usage is discouraged.) $)
    vcablo $p |- ( W e. CVecOLD -> G e. AbelOp ) $=
      ( vx vy vz cvc wcel cablo cc crn cxp c2nd cfv cv co wceq wral wa eqid vci
      wf c1 caddc cmul simp1d ) BGHAIHJAKZLUGBMNZUBUCDOZUHPUIQEOZUIFOZAPUHPUJUI
      UHPZUJUKUHPAPQFUGRUJUKUDPUIUHPULUKUIUHPZAPQUJUKUEPUIUHPUJUMUHPQSFJRSEJRSD
      UGRDEFUHABUGCUHTUGTUAUF $.

    $( Vector addition is a group operation.  (Contributed by NM, 4-Nov-2006.)
       (New usage is discouraged.) $)
    vcgrp $p |- ( W e. CVecOLD -> G e. GrpOp ) $=
      ( cvc wcel cablo cgr vcablo ablogrpo syl ) BDEAFEAGEABCHAIJ $.
  $}

  ${
    vcgcl.1 $e |- G = ( 1st ` W ) $.
    vcgcl.2 $e |- X = ran G $.
    $( Closure law for the vector addition (group) operation of a complex
       vector space.  (Contributed by NM, 1-Feb-2007.)
       (New usage is discouraged.) $)
    vcgcl $p |- ( ( W e. CVecOLD /\ A e. X /\ B e. X ) -> ( A G B ) e. X ) $=
      ( cvc wcel cgr co vcgrp grpocl syl3an1 ) DHICJIAEIBEIABCKEICDFLABCEGMN $.
  $}

  ${
    vccom.1 $e |- G = ( 1st ` W ) $.
    vccom.2 $e |- X = ran G $.
    $( Vector addition is commutative.  (Contributed by NM, 4-Nov-2006.)
       (New usage is discouraged.) $)
    vccom $p |- ( ( W e. CVecOLD /\ A e. X /\ B e. X ) ->
                ( A G B ) = ( B G A ) ) $=
      ( cvc wcel cablo co wceq vcablo ablocom syl3an1 ) DHICJIAEIBEIABCKBACKLCD
      FMABCEGNO $.

    $( Vector addition is associative.  (Contributed by NM, 4-Nov-2006.)
       (New usage is discouraged.) $)
    vcaass $p |- ( ( W e. CVecOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                ( ( A G B ) G C ) = ( A G ( B G C ) ) ) $=
      ( cvc wcel cgr w3a co wceq vcgrp grpoass sylan ) EIJDKJAFJBFJCFJLABDMCDMA
      BCDMDMNDEGOABCDFHPQ $.

    $( Commutative/associative law that swaps the last two terms in a triple
       vector sum.  (Contributed by NM, 5-Aug-2007.)
       (New usage is discouraged.) $)
    vca32 $p |- ( ( W e. CVecOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
     ( ( A G B ) G C ) = ( ( A G C ) G B ) ) $=
      ( cvc wcel cablo w3a co wceq vcablo ablo32 sylan ) EIJDKJAFJBFJCFJLABDMCD
      MACDMBDMNDEGOABCDFHPQ $.

    $( Rearrangement of 4 terms in a vector sum.  (Contributed by NM,
       5-Aug-2007.)  (New usage is discouraged.) $)
    vca4 $p |- ( ( W e. CVecOLD /\ ( A e. X /\ B e. X ) /\ ( C e. X /\ D e. X )
      ) -> ( ( A G B ) G ( C G D ) ) = ( ( A G C ) G ( B G D ) ) ) $=
      ( cvc wcel cablo wa co wceq vcablo ablo4 syl3an1 ) FJKELKAGKBGKMCGKDGKMAB
      ENCDENENACENBDENENOEFHPABCDEGIQR $.

    $( Right cancellation law for vector addition.  (Contributed by NM,
       4-Nov-2006.)  (New usage is discouraged.) $)
    vcrcan $p |- ( ( W e. CVecOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                  ( ( A G C ) = ( B G C ) <-> A = B ) ) $=
      ( cvc wcel cgr w3a co wceq wb vcgrp grporcan sylan ) EIJDKJAFJBFJCFJLACDM
      BCDMNABNODEGPABCDFHQR $.

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

    $( The zero vector is a left identity element.  (Contributed by NM,
       26-Apr-2007.)  (New usage is discouraged.) $)
    vc0lid $p |- ( ( W e. CVecOLD /\ A e. X ) -> ( Z G A ) = A ) $=
      ( cvc wcel cgr co wceq vcgrp grpolid sylan ) CIJBKJADJEABLAMBCFNAEBDGHOP
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
      ( cvc wcel wa cc0 co wceq c1 ax-1cn cc 0cn vc0rid caddc oveq1i vcdir vcid
      addid1i mp3anr1 mpanr1 3eqtr3a oveq1d 3eqtr2rd w3a wb mp3an2 vczcl adantr
      vccl simpr 3jca vclcan syldan mpbid ) DKLZAELZMZANABOZCOZAFCOZPZVFFPZVEVH
      AQABOZVFCOZVGACDEFGIJUAVEQNUBOZABOZVKVLAVMQABQRUFUCVCNSLZVDVNVLPZTVCQSLVO
      VDVPRQNABCDEGHIUDUGUHABCDEGHIUEZUIVEVKAVFCVQUJUKVCVDVFELZFELZVDULVIVJUMVE
      VRVSVDVCVOVDVRTNABCDEGHIUQUNVCVSVDCDEFGIJUOUPVCVDURUSVFFACDEGIUTVAVB $.

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
      ( wcel c1 co cfv wceq cc neg1cn cc0 ax-1cn eqtr3d cvc cneg cgi cgr adantr
      wa vcgrp vccl eqid grporid syl2anc simpr grpoinvcl sylan grpoass syl13anc
      mp3an2 vcid oveq2d caddc negidi addcomli oveq1i vcdir mp3anr1 vc0 3eqtr3a
      mpanr1 oveq1d grporinv grpolid ) EUAKZAFKZUFZLUBZABMZCUCNZCMZVPADNZVNCUDK
      ZVPFKZVRVPOVLVTVMCEGUGZUEZVLVOPKZVMWAQVOABCEFGHIUHUQZVPVQCFIVQUIZUJUKVNVQ
      VSCMZVRVSVNVPAVSCMZCMZWGVRVNVPACMZVSCMZWIWGVNVTWAVMVSFKZWKWIOWCWEVLVMULVL
      VTVMWLWBACDFIJUMUNZVPAVSCFIUOUPVNWJVQVSCVNVPLABMZCMZWJVQVNWNAVPCABCEFGHIU
      RUSVNVOLUTMZABMZRABMWOVQWPRABLVORSQLSVAVBVCVLLPKZVMWQWOOZSVLWDWRVMWSQVOLA
      BCEFGHIVDVEVHABCEFVQGHIWFVFVGTVITVNWHVQVPCVLVTVMWHVQOWBAVQCDFIWFJVJUNUSTV
      NVTWLWGVSOWCWMVSVQCFIWFVKUKTT $.
  $}

  ${
    vcrinv.1 $e |- G = ( 1st ` W ) $.
    vcrinv.2 $e |- S = ( 2nd ` W ) $.
    vcrinv.3 $e |- X = ran G $.
    vcrinv.4 $e |- Z = ( GId ` G ) $.
    $( A vector minus itself.  (Contributed by NM, 4-Dec-2006.)
       (New usage is discouraged.) $)
    vcrinv $p |- ( ( W e. CVecOLD /\ A e. X ) -> ( A G ( -u 1 S A ) ) = Z ) $=
      ( cvc wcel wa c1 cneg co cgn cfv eqid vcm oveq2d cgr vcgrp grporinv sylan
      wceq eqtrd ) DKLZAELZMZANOABPZCPAACQRZRZCPZFUJUKUMACABCULDEGHIULSZTUAUHCU
      BLUIUNFUFCDGUCAFCULEIJUOUDUEUG $.

    $( Minus a vector plus itself.  (Contributed by NM, 4-Dec-2006.)
       (New usage is discouraged.) $)
    vclinv $p |- ( ( W e. CVecOLD /\ A e. X ) -> ( ( -u 1 S A ) G A ) = Z ) $=
      ( cvc wcel wa c1 cneg co cgn cfv eqid vcm oveq1d cgr vcgrp grpolinv sylan
      wceq eqtrd ) DKLZAELZMZNOABPZACPACQRZRZACPZFUJUKUMACABCULDEGHIULSZTUAUHCU
      BLUIUNFUFCDGUCAFCULEIJUOUDUEUG $.
  $}

  ${
    vcni.1 $e |- G = ( 1st ` W ) $.
    vcni.2 $e |- S = ( 2nd ` W ) $.
    vcni.3 $e |- X = ran G $.
    $( Double negative of a vector.  (Contributed by NM, 6-Aug-2007.)
       (New usage is discouraged.) $)
    vcnegneg $p |- ( ( W e. CVecOLD /\ A e. X ) ->
                  ( -u 1 S ( -u 1 S A ) ) = A ) $=
      ( cvc wcel wa c1 cneg cmul co ax-1cn mul2negi 1t1e1 eqtri neg1cn cc vcass
      oveq1i wceq mp3anr1 mpanr1 vcid 3eqtr3a ) DIJZAEJZKLMZUKNOZABOZLABOUKUKAB
      OBOZAULLABULLLNOLLLPPQRSUCUIUKUAJZUJUMUNUDZTUIUOUOUJUPTUKUKABCDEFGHUBUEUF
      ABCDEFGHUGUH $.

    $( Distribution of negative over vector subtraction.  (Contributed by NM,
       6-Aug-2007.)  (New usage is discouraged.) $)
    vcnegsubdi2 $p |- ( ( W e. CVecOLD /\ A e. X /\ B e. X ) ->
              ( -u 1 S ( A G ( -u 1 S B ) ) ) = ( B G ( -u 1 S A ) ) ) $=
      ( cvc wcel w3a c1 cneg co wceq neg1cn vccl mp3an2 3adant2 cc vcdi mp3anr1
      3impb syld3an3 vcnegneg oveq2d 3adant3 vccom syld3an2 3eqtrd ) EJKZAFKZBF
      KZLZMNZAUPBCOZDOCOZUPACOZUPUQCOZDOZUSBDOZBUSDOZULUMUNUQFKZURVAPZULUNVDUMU
      LUPUAKZUNVDQUPBCDEFGHIRSTULUMVDVEULVFUMVDVEQUPAUQCDEFGHIUBUCUDUEUOUTBUSDU
      LUNUTBPUMBCDEFGHIUFTUGULUSFKZUMUNVBVCPULUMVGUNULVFUMVGQUPACDEFGHIRSUHUSBD
      EFGIUIUJUK $.

    $( Rearrangement of 4 terms in a mixed vector addition and subtraction.
       (Contributed by NM, 5-Aug-2007.)  (New usage is discouraged.) $)
    vcsub4 $p |- ( ( W e. CVecOLD /\ ( A e. X /\ B e. X ) /\ ( C e. X /\ D e. X
        )
              ) -> ( ( A G B ) G ( -u 1 S ( C G D ) ) ) =
            ( ( A G ( -u 1 S C ) ) G ( B G ( -u 1 S D ) ) ) ) $=
      ( cvc wcel wa co wceq neg1cn 3adant2 vccl mp3an2 w3a c1 cneg vcdi mp3anr1
      cc oveq2d anim12dan vca4 syld3an3 eqtrd ) GLMZAHMBHMNZCHMZDHMZNZUAZABFOZU
      BUCZCDFOEOZFOURUSCEOZUSDEOZFOZFOZAVAFOBVBFOFOZUQUTVCURFULUPUTVCPZUMULUSUF
      MZUNUOVFQUSCDEFGHIJKUDUERUGULUMUPVAHMZVBHMZNZVDVEPULUPVJUMULUNVHUOVIULVGU
      NVHQUSCEFGHIJKSTULVGUOVIQUSDEFGHIJKSTUHRABVAVBFGHIKUIUJUK $.
  $}

  ${
    $d g s x y z G $.  $d g s x y z S $.  $d g s x z X $.
    isvclem.1 $e |- X = ran G $.
    $( Lemma for ~ isvc .  (Contributed by NM, 31-May-2008.)
       (New usage is discouraged.) $)
    isvclem $p |- ( ( G e. _V /\ S e. _V ) -> ( <. G , S >. e. CVecOLD
     <-> ( G e. AbelOp /\ S : ( CC X. X ) --> X /\ A. x e. X ( ( 1 S x ) = x /\
       A. y e. CC ( A. z e. X ( y S ( x G z ) ) = ( ( y S x ) G ( y S z ) )
         /\ A. z e. CC ( ( ( y + z ) S x ) = ( ( y S x ) G ( z S x ) ) /\
           ( ( y x. z ) S x ) = ( y S ( z S x ) ) ) ) ) ) ) ) $=
      ( vg vs wcel cv cc wf co wceq wral wa cvv oveq ralbidv cop cvc crn cxp c1
      cablo caddc cmul w3a copab df-vc eleq2i eleq1 wb rneq syl6eqr xpeq2 feq2d
      bitrd syl oveq2d eqeq12d raleqbidv eqeq2d anbi1d anbi12d anbi2d 3anbi123d
      feq3 feq1 eqeq1d oveq12d eqtrd 3anbi23d opelopabg syl5bb ) EDUAZUBJVQHKZU
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

  ${
    $d x y z G $.
    $( Lemma for ~ vcoprne .  (Contributed by NM, 31-May-2008.)
       (New usage is discouraged.) $)
    vcoprnelem $p |- ( <. G , G >. e. CVecOLD -> G : ( CC X. CC ) --> CC ) $=
      ( vx vy vz cvv wcel cop cvc cc cxp wf syl wa cv co wceq wral wb wfn mpbid
      wrel wss vcrel df-rel mpbi sseli opelxp1 cablo crn c1 caddc cmul w3a eqid
      isvclem anidms biimpa simpr cgr ablogrpo wfo grpofo fofn ffn fndmu syl2an
      c0 wne grpon0 xpcan2 adantr sylan xpeq2 feq2d feq3 bitrd 3adant3 mpancom
      ) AEFZAAGZHFZIIJZIAKZWAVTEEJZFVSHWDVTHUAHWDUBUCHUDUEUFAAEEUGLVSWAMAUHFZIA
      UIZJZWFAKZUJBNZAOWIPCNZWIDNZAOAOWJWIAOZWJWKAOAOPDWFQWJWKUKOWIAOWLWKWIAOZA
      OPWJWKULOWIAOWJWMAOPMDIQMCIQMBWFQZUMZWCVSWAWOVSWAWORBCDAAWFWFUNZUOUPUQWEW
      HWCWNWEWHMZWHWCWEWHURWQWFIPZWHWCRWEAUSFZWHWRAUTWSWHMWFWFJZWGPZWRWSAWTSZAW
      GSXAWHWSWTWFAVAXBAWFWPVBWTWFAVCLWGWFAVDWTWGAVEVFWSXAWRRZWHWSWFVGVHXCAWFWP
      VIWFIWFVJLVKTVLWRWHWBWFAKWCWRWGWBWFAWFIIVMVNWFIWBAVOVPLTVQLVR $.
  $}

  $( The operations of a complex vector space cannot be identical.
     (Contributed by NM, 31-May-2008.)  (New usage is discouraged.) $)
  vcoprne $p |- ( <. G , S >. e. CVecOLD -> G =/= S ) $=
    ( cop cvc wcel wceq c1 cc0 cfv co cvv cnex syl2anc oveqd crn cdm eqid mpdan
    cc eqtr3d wne wn ax-1ne0 df-ne mpbi c1st cgi cxp wf vcoprnelem xpex sylancl
    fex op1stg ax-1cn rneqd cgr vcgrp eqeltrrd grporndm syl dmeqd dmxpid syl6eq
    c2nd fdm 3eqtrd syl5eleqr vc0rid vcid op2ndg eqtr4d 3eqtr2d wb vczcl vclcan
    w3a 3jca mpbid oveq2d 0cn vcz mpan2 eqtrd mto opeq2 eleq1d mtbii necon2ai )
    BACZDEZBABAFZBBCZDEZWKWNGHFZGHUAWOUBUCGHUDUEWNHWMUFIZUGIZWPJZGHWNWRHWQBJZHG
    BJZGWNWPBHWQWNBKEZXAWPBFWNSSUHZSBUIZXBKEXABUJZSSLLUKXBSKBUMULZXEBBKKUNMZNWN
    WQGHBWNGWQWPJZGGWPJZFZWQGFZWNXGGGGWMVEIZJZXHWNGWPOZEZXGGFWNGSXMUOWNXMBOZBPZ
    PZSWNWPBXFUPWNBUQEXOXQFWNWPBUQXFWPWMWPQZURUSBUTVAWNXQXBPSWNXPXBWNXCXPXBFXDX
    BSBVFVAVBSVCVDVGZVHZGWPWMXMWQXRXMQZWQQZVIRWNXNXLGFXTGXKWPWMXMXRXKQZYAVJRWNX
    KWPGGWNXKBWPWNXAXAXKBFXEXEBBKKVKMZXFVLNVMWNWQXMEZXNXNVQXIXJVNWNYEXNXNWPWMXM
    WQXRYAYBVOXTXTVRWQGGWPWMXMXRYAVPRVSZVTZWNWQWTGWNHWQXKJZWQWTWNHSEYHWQFWAHXKW
    PWMXMWQXRYCYAYBWBWCWNYHWSWTWNXKBHWQYDNYGWDTYFTVGWNHXMEWRHFWNHSXMWAXSVHHWPWM
    XMWQXRYAYBVIRTWEWLWMWJDBABWFWGWHWI $.

  $( The components of a complex vector space are sets.  (Contributed by NM,
     31-May-2008.)  (New usage is discouraged.) $)
  vcex $p |- ( <. G , S >. e. CVecOLD -> ( G e. _V /\ S e. _V ) ) $=
    ( cop cvc wcel wbr cvv wa df-br wrel cxp wss vcrel df-rel mpbi brel sylbir
    ) BACDEBADFBGEAGEHBADIBAGGDDJDGGKLMDNOPQ $.

  ${
    $d x y z G $.  $d x y z S $.  $d x z X $.
    isvc.1 $e |- X = ran G $.
    $( The predicate "is a complex vector space."  (Contributed by NM,
       31-May-2008.)  (New usage is discouraged.) $)
    isvc $p |- ( <. G , S >. e. CVecOLD <-> ( G e. AbelOp /\
         S : ( CC X. X ) --> X /\ A. x e. X ( ( 1 S x ) = x /\
       A. y e. CC ( A. z e. X ( y S ( x G z ) ) = ( ( y S x ) G ( y S z ) )
         /\ A. z e. CC ( ( ( y + z ) S x ) = ( ( y S x ) G ( z S x ) ) /\
           ( ( y x. z ) S x ) = ( y S ( z S x ) ) ) ) ) ) ) $=
      ( cop cvc wcel cvv wa cablo cc cxp cv co wceq wral cgr wf caddc cmul vcex
      c1 w3a elex adantr cnex ablogrpo crn rnexg syl5eqel syl xpexg sylancr fex
      sylan2 ancoms jca 3adant3 isvclem pm5.21nii ) EDHIJEKJZDKJZLZEMJZNFOZFDUA
      ZUEAPZDQVJRBPZVJCPZEQDQVKVJDQZVKVLDQEQRCFSVKVLUBQVJDQVMVLVJDQZEQRVKVLUCQV
      JDQVKVNDQRLCNSLBNSLAFSZUFDEUDVGVIVFVOVGVILVDVEVGVDVIEMUGUHVIVGVEVGVIVHKJZ
      VEVGNKJFKJZVPUIVGETJZVQEUJVRFEUKKGETULUMUNNFKKUOUPVHFKDUQURUSUTVAABCDEFGV
      BVC $.
  $}

  ${
    $d x y z G $.  $d x y z S $.  $d x y z X $.
    isvci.1 $e |- G e. AbelOp $.
    isvci.2 $e |- dom G = ( X X. X ) $.
    isvci.3 $e |- S : ( CC X. X ) --> X $.
    isvci.4 $e |- ( x e. X -> ( 1 S x ) = x ) $.
    isvci.5 $e |- ( ( y e. CC /\ x e. X /\ z e. X ) ->
                  ( y S ( x G z ) ) = ( ( y S x ) G ( y S z ) ) ) $.
    isvci.6 $e |- ( ( y e. CC /\ z e. CC /\ x e. X ) ->
                  ( ( y + z ) S x ) = ( ( y S x ) G ( z S x ) ) ) $.
    isvci.7 $e |- ( ( y e. CC /\ z e. CC /\ x e. X ) ->
                  ( ( y x. z ) S x ) = ( y S ( z S x ) ) ) $.
    isvci.8 $e |- W = <. G , S >. $.
    $( Properties that determine a complex vector space.  (Contributed by NM,
       5-Nov-2006.)  (New usage is discouraged.) $)
    isvci $p |- W e. CVecOLD $=
      ( wcel cc co wceq wral cop cvc cablo cxp wf c1 cv caddc cmul 3com12 3expa
      wa ralrimiva w3a jca 3comr rgen cgr ablogrpo grporn isvc mpbir3an eqeltri
      ax-mp ) FEDUAZUBOVEUBPEUCPZQGUDGDUEUFAUGZDRVGSZBUGZVGCUGZERDRVIVGDRZVIVJD
      RERSZCGTZVIVJUHRVGDRVKVJVGDRZERSZVIVJUIRVGDRVIVNDRSZULZCQTZULZBQTZULZAGTH
      JWAAGVGGPZVHVTKWBVSBQWBVIQPZULZVMVRWDVLCGWBWCVJGPZVLWCWBWEVLLUJUKUMWDVQCQ
      WBWCVJQPZVQWCWFWBVQWCWFWBUNVOVPMNUOUPUKUMUOUMUOUQABCDEGEGVFEURPHEUSVDIUTV
      AVBVC $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                 Examples of complex vector spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z $.
    $( The set of complex numbers is a complex vector space.  The vector
       operation is ` + ` , and the scalar product is ` x. ` .  (Contributed by
       NM, 5-Nov-2006.)  (New usage is discouraged.) $)
    cncvc $p |- <. + , x. >. e. CVecOLD $=
      ( vx vy vz cmul caddc cop cc cnaddablo cxp ax-addf fdmi ax-mulf cv mulid2
      adddi adddir mulass eqid isvci ) ABCDEEDFZGHGGIGEJKLAMZNBMZUACMZOUBUCUAPU
      BUCUAQTRS $.
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
     particular vector space ` U ` , it is not a function, unlike e.g.
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
    $d g s m n o t u w x y z $.  $d y G $.  $d y N $.  $d y S $.
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
    $d x y U $.
    vafval.2 $e |- G = ( +v ` U ) $.
    $( Value of the function for the vector addition (group) operation on a
       normed complex vector space.  (Contributed by NM, 23-Apr-2007.)
       (New usage is discouraged.) $)
    vafval $p |- G = ( 1st ` ( 1st ` U ) ) $=
      ( cpv cfv c1st cvv wcel wceq df-va fveq1i wf wfo fo1st fof ax-mp fvco3 c0
      ccom fvprc mpan syl5eq wn fveq2d 1st0 syl6req eqtrd pm2.61i eqtri ) BADEZ
      AFEZFEZCAGHZUJULIUMUJAFFSZEZULADUNJKGGFLZUMUOULIGGFMUPNGGFOPGGAFFQUAUBUMU
      CZUJRULADTUQULRFERUQUKRFAFTUDUEUFUGUHUI $.
  $}

  ${
    $d u U $.
    bafval.1 $e |- X = ( BaseSet ` U ) $.
    bafval.2 $e |- G = ( +v ` U ) $.
    $( Value of the function for the base set of a normed complex vector
       space.  (Contributed by NM, 23-Apr-2007.)  (Revised by Mario Carneiro,
       16-Nov-2013.)  (New usage is discouraged.) $)
    bafval $p |- X = ran G $=
      ( vu cba cfv cpv crn cvv wcel wceq cv fveq2 rneqd df-ba fvex c0 fvprc rn0
      rnex fvmpt wn eqcomi 3eqtr4a pm2.61i rneqi 3eqtr4i ) AGHZAIHZJZCBJAKLZUJU
      LMFAFNZIHZJULKGUNAMUOUKUNAIOPFQUKAIRUBUCUMUDZSSJZUJULUQSUAUEAGTUPUKSAITPU
      FUGDBUKEUHUI $.
  $}

  ${
    $d u U $.
    smfval.4 $e |- S = ( .sOLD ` U ) $.
    $( Value of the function for the scalar multiplication operation on a
       normed complex vector space.  (Contributed by NM, 24-Apr-2007.)
       (New usage is discouraged.) $)
    smfval $p |- S = ( 2nd ` ( 1st ` U ) ) $=
      ( cns cfv c1st c2nd cvv wcel wceq ccom df-sm fveq1i wf wfo fo1st ax-mp c0
      fof fvprc fvco3 mpan syl5eq wn fveq2d 2nd0 syl6req eqtrd pm2.61i eqtri )
      ABDEZBFEZGEZCBHIZUKUMJUNUKBGFKZEZUMBDUOLMHHFNZUNUPUMJHHFOUQPHHFSQHHBGFUAU
      BUCUNUDZUKRUMBDTURUMRGERURULRGBFTUEUFUGUHUIUJ $.
  $}

  ${
    $d x y U $.  $d x y z w $.
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
    $d x y U $.
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
      syl6eqr ) AFGZAAHIZAJIZKZCBKFLTAUCMNAFOPCUABUBDABEQRS $.
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
      cnmcv cxp nvss eqid nvop2 ibi sseldi opelxp1 1st2nd sylancr vafval smfval
      syl opeq12i syl6eqr ) BHIZDDJKZDLKZMZCAMUQNODNIZDUTPQUQDBUBKZMZNRUCZIVAUQ
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
      syl6eqr eqeq1d ralbidv 3anbi2d feq1 imbi1d oveq2d eqeq12d oveq12d breq12d
      fveq1 3anbi23d eloprabg syl5bb ) DCUDZEUDZUEJWHUAKZUBKZUDZLJZWIUFZMUCKZUI
      ZAKZWNNZUGOZWPWIUHNZOZUJZBKZWPWJPZWNNZXBUKNZWQULPZOZBQRZWPXBWIPZWNNZWQXBW
      NNZUMPZUNUOZBWMRZSZAWMRZSZUAUBUCUPZJDTJCTJETJSWGLJZFMEUIZWPENZUGOZWPGOZUJ
      ZXBWPCPZENZXEYAULPZOZBQRZWPXBDPZENZYAXBENZUMPZUNUOZBFRZSZAFRZSZUEXRWHABUA
      UCUBUQURXQDWJUDZLJZFMWNUIZWRYCUJZXHYJWNNZXLUNUOZBFRZSZAFRZSXSUUAUUBYEWNNZ
      XFOZBQRZUUESZAFRZSYRUAUBUCDCETTTWIDOZWLYTWOUUAXPUUGUUMWKYSLWIDWJUSUTUUMWM
      FMWNUUMWMDUFFWIDVAHVMZVBUUMXOUUFAWMFUUNUUMXAUUBXNUUEXHUUMWTYCWRUUMWSGWPUU
      MWSDUHNGWIDUHVCIVMVDVEUUMXMUUDBWMFUUNUUMXJUUCXLUNUUMXIYJWNWPXBWIDVFVGVHVI
      VJVIVKWJCOZYTXSUUGUULUUAUUOYSWGLWJCDVLUTUUOUUFUUKAFUUOXHUUJUUBUUEUUOXGUUI
      BQUUOXDUUHXFUUOXCYEWNXBWPWJCVFVGVNVOVPVOVJWNEOZUUAXTUULYQXSFMWNEVQUUPUUKY
      PAFUUPUUBYDUUJYIUUEYOUUPWRYBYCUUPWQYAUGWPWNEWCZVNVRUUPUUIYHBQUUPUUHYFXFYG
      YEWNEWCUUPWQYAXEULUUQVSVTVOUUPUUDYNBFUUPUUCYKXLYMUNYJWNEWCUUPWQYAXKYLUMUU
      QXBWNEWCWAWBVOVKVOWDWEWF $.
  $}

  ${
    $d x y G $.  $d x y S $.
    $( The components of a normed complex vector space are sets.  (Contributed
       by NM, 5-Jun-2008.)  (Revised by Mario Carneiro, 1-May-2015.)
       (New usage is discouraged.) $)
    nvex $p |- ( <. <. G , S >. , N >. e. NrmCVec
            -> ( G e. _V /\ S e. _V /\ N e. _V ) ) $=
      ( cop cnv wcel cvv wa w3a cvc nvvcop vcex syl nvss sseli opelxp2 sylanbrc
      cxp df-3an ) BADZCDZEFZBGFZAGFZHZCGFZUCUDUFIUBTJFUECTKABLMUBUAJGRZFUFEUGU
      ANOTCJGPMUCUDUFSQ $.
  $}

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
      cmul cc cle wbr nvex vcex adantr crn simpld rnexg syl syl5eqel fex sylan2
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
       14-Dec-2007.)  (New usage is discouraged.) $)
    nvadd12 $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                 ( A G ( B G C ) ) = ( B G ( A G C ) ) ) $=
      ( cnv wcel w3a wa co wceq nvcom 3adant3r3 oveq1d nvass 3ancoma sylan2b
      3eqtr3d ) DIJZAFJZBFJZCFJZKZLZABEMZCEMBAEMZCEMZABCEMEMBACEMEMZUGUHUICEUBU
      CUDUHUINUEABDEFGHOPQABCDEFGHRUFUBUDUCUEKUJUKNUCUDUESBACDEFGHRTUA $.

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

    $( Left cancellation law for vector addition.  (Contributed by NM,
       14-Dec-2007.)  (New usage is discouraged.) $)
    nvlcan $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                  ( ( C G A ) = ( C G B ) <-> A = B ) ) $=
      ( cnv wcel cgr w3a co wceq wb nvgrp bafval grpolcan sylan ) DIJEKJAFJBFJC
      FJLCAEMCBEMNABNODEHPABCEFDEFGHQRS $.

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
      vcid sylan ) CGHCIJZKHADHLABMANCUCUCOPABCQJZUCDCUDUDOZRBCFSCUDDEUETUAUB
      $.

    $( Associative law for the scalar product of a normed complex vector
       space.  (Contributed by NM, 17-Nov-2007.)
       (New usage is discouraged.) $)
    nvsass $p |- ( ( U e. NrmCVec /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
      ( ( A x. B ) S C ) = ( A S ( B S C ) ) ) $=
      ( cnv wcel c1st cfv cvc cc w3a cmul co wceq eqid nvvc vafval smfval vcass
      cpv bafval sylan ) EIJEKLZMJANJBNJCFJOABPQCDQABCDQDQREUGUGSTABCDEUDLZUGFE
      UHUHSZUADEHUBEUHFGUIUEUCUF $.

    $( Commutative law for the scalar product of a normed complex vector
       space.  (Contributed by NM, 14-Feb-2008.)
       (New usage is discouraged.) $)
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
      ( cnv wcel c1st cfv cvc co c2 wceq eqid nvvc vafval smfval bafval sylan
      vc2 ) CIJCKLZMJAEJAADNOABNPCUDUDQRABDUDECDGSBCHTCDEFGUAUCUB $.
  $}

  ${
    $d f g x y z $.
    vsfval.2 $e |- G = ( +v ` U ) $.
    vsfval.3 $e |- M = ( -v ` U ) $.
    $( Value of the function for the vector subtraction operation on a normed
       complex vector space.  (Contributed by NM, 15-Feb-2008.)  (Revised by
       Mario Carneiro, 27-Dec-2014.)  (New usage is discouraged.) $)
    vsfval $p |- M = ( /g ` G ) $=
      ( vg vx vy cnsb cfv cpv cgs cvv wcel wceq wf c1st c0 cgr cv df-vs wfo fof
      ccom fveq1i fo1st ax-mp fco mp2an df-va feq1i mpbir fvco3 mpan syl5eq cdm
      wn 0ngrp crn cgn co cmpt2 vex rnex mpt2ex df-gdiv dmmpti mtbir ndmfv mp1i
      eleq2i fvprc fveq2d 3eqtr4rd pm2.61i fveq2i 3eqtr4i ) AIJZAKJZLJZCBLJAMNZ
      VRVTOWAVRALKUDZJZVTAIWBUAUEMMKPZWAWCVTOWDMMQQUDZPZMMQPZWGWFMMQUBWGUFMMQUC
      UGZWHMMMQQUHUIMMKWEUJUKULMMALKUMUNUOWAUQZRLJZRVTVRRLUPZNZUQWJROWIWLRSNURW
      KSRFSGHFTZUSZWNGTHTWMUTJJWMVAZVBLGHWNWNWOWMFVCVDZWPVEGHFVFVGVKVHRLVIVJWIV
      SRLAKVLVMAIVLVNVOEBVSLDVPVQ $.
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
      ( vx cnv wcel cba cfv wf wfn cc eqid neg1cn sylancl ffn syl cgn cneg nvsf
      cxp c1 curry1f wf1o nvgrp bafval grpoinvf f1ofn 3syl cv wa co wceq adantr
      cgr curry1val nvinv eqtrd eqfnfvd ) BIJZHBKLZDCUALZVCVDVDDMZDVDNVCOVDUDZV
      DAMZUEUBZOJZVFABVDVDPZFUCZQOVDVIVDADGUFRVDVDDSTVCCURJVDVDVEUGVEVDNBCEUHCV
      EVDBCVDVKEUIVEPZUJVDVDVEUKULVCHUMZVDJZUNZVNDLZVIVNAUOZVNVELVPAVGNZVJVQVRU
      PVCVSVOVCVHVSVLVGVDASTUQQOVDVIVNADGUSRVNABCVEVDVKEFVMUTVAVB $.
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
      ( cnv wcel cv cgn cfv co cmpt2 c1 wceq cneg nvgrp bafval eqid grpodivfval
      cgr vsfval syl w3a nvinv 3adant2 oveq2d mpt2eq3dva eqtr4d ) DLMZFABGGANZB
      NZEOPZPZEQZRZABGGUPSUAUQCQZEQZRUOEUFMFVATDEIUBABFEURGDEGHIUCURUDZDEFIKUGU
      EUHUOABGGVCUTUOUPGMZUQGMZUIVBUSUPEUOVFVBUSTVEUQCDEURGHIJVDUJUKULUMUN $.
  $}

  ${
    nvzs.1 $e |- X = ( BaseSet ` U ) $.
    nvzs.3 $e |- M = ( -v ` U ) $.
    nvzs.4 $e |- S = ( .sOLD ` U ) $.
    nvzs.6 $e |- Z = ( 0vec ` U ) $.
    $( Two ways to express the negative of a vector.  (Contributed by NM,
       29-Feb-2008.)  (New usage is discouraged.) $)
    nvzs $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( Z M A ) = ( -u 1 S A ) ) $=
      ( cnv wcel wa co c1 cneg cpv cfv wceq simpl nvzcl adantr simpr syl3anc cc
      eqid nvmval neg1cn nvscl mp3an2 nv0lid syldan eqtrd ) CKLZAELZMZFADNZFOPZ
      ABNZCQRZNZUSUPUNFELZUOUQVASUNUOTUNVBUOCEFGJUAUBUNUOUCFABCUTDEGUTUFZIHUGUD
      UNUOUSELZVAUSSUNURUELUOVDUHURABCEGIUIUJUSCUTEFGVCJUKULUM $.
  $}

  ${
    $d x y U $.  $d x y X $.
    nvmf.1 $e |- X = ( BaseSet ` U ) $.
    nvmf.3 $e |- M = ( -v ` U ) $.
    $( Mapping for the vector subtraction operation.  (Contributed by NM,
       11-Sep-2007.)  (Revised by Mario Carneiro, 23-Dec-2013.)
       (New usage is discouraged.) $)
    nvmf $p |- ( U e. NrmCVec -> M : ( X X. X ) --> X ) $=
      ( vx vy cnv wcel cxp wf cv c1 cneg cns cfv co wral wa eqid cmpt2 simpl cc
      simprl neg1cn nvscl mp3an2 adantrl nvgcl syl3anc ralrimivva fmpt2 nvmfval
      cpv sylib feq1d mpbird ) AHIZCCJZCBKUSCFGCCFLZMNZGLZAOPZQZAUNPZQZUAZKZURV
      FCIZGCRFCRVHURVIFGCCURUTCIZVBCIZSZSURVJVDCIZVIURVLUBURVJVKUDURVKVMVJURVAU
      CIVKVMUEVAVBVCACDVCTZUFUGUHUTVDAVECDVETZUIUJUKFGCCVFCVGVGTULUOURUSCBVGFGV
      CAVEBCDVOVNEUMUPUQ $.

    $( Closure law for the vector subtraction operation of a normed complex
       vector space.  (Contributed by NM, 11-Sep-2007.)
       (New usage is discouraged.) $)
    nvmcl $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A M B ) e. X ) $=
      ( cnv wcel cxp wf co nvmf fovrn syl3an1 ) CHIEEJEDKAEIBEIABDLEICDEFGMABEE
      EDNO $.

    $( Cancellation law for vector subtraction.  ( ~ nnncan1 analog.)
       (Contributed by NM, 7-Mar-2008.)  (New usage is discouraged.) $)
    nvnnncan1 $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
         ( ( A M B ) M ( A M C ) ) = ( C M B ) ) $=
      ( cnv wcel cpv cfv cablo w3a co wceq eqid nvablo bafval vsfval sylan
      ablonnncan1 ) DIJDKLZMJAFJBFJCFJNABEOACEOEOCBEOPDUCUCQZRABCEUCFDUCFGUDSDU
      CEUDHTUBUA $.

    $( Cancellation law for vector subtraction.  ( ~ nnncan2 analog.)
       (Contributed by NM, 15-Feb-2008.)  (New usage is discouraged.) $)
    nvnnncan2 $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
         ( ( A M C ) M ( B M C ) ) = ( A M B ) ) $=
      ( cnv wcel cpv cfv cgr w3a co wceq eqid nvgrp bafval vsfval grponnncan2
      sylan ) DIJDKLZMJAFJBFJCFJNACEOBCEOEOABEOPDUCUCQZRABCEUCFDUCFGUDSDUCEUDHT
      UAUB $.
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
      cmul nvsass nvsid adantr adantlr nvsz anassrs 3adantl3 ex syl5bir orrd wi
      sylan2 nv0 oveq1 eqeq1d syl5ibrcom 3adant3 jaod impbid ) DUAJZAKJZBEJZUBZ
      ABCLZFMZANMZBFMZUCZVSWAWDVSWAOZWBWCWBUDANUEZWEWCANUFWEWFWCWEWFOPAUGLZVTCL
      ZWGFCLZBFWAWHWIMVSWFVTFWGCQUHVSWFWHBMWAVSWFOZWGAUPLZBCLZPBCLZWHBVQVPWFWLW
      MMVRVQWFOZWKPBCAUIUJRWJVPWGKJZVQVRWLWHMVPVQVRWFUKVQVPWFWOVRAULZRVPVQVRWFU
      MVPVQVRWFUNWGABCDEGHUQUOVSWMBMZWFVPVRWQVQBCDEGHURSUSTUTVSWFWIFMZWAVPVQWFW
      RVRVPVQWFWRWNVPWOWRWPWGCDFHIVAVHVBVCUTTVDVEVFVDVSWBWAWCVPVRWBWAVGVQVPVROW
      AWBNBCLZFMBCDEFGHIVIWBVTWSFANBCVJVKVLSVPVQWCWAVGVRVPVQOWAWCAFCLZFMACDFHIV
      AWCVTWTFBFACQVKVLVMVNVO $.
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
    nvsubadd.1 $e |- X = ( BaseSet ` U ) $.
    nvsubadd.2 $e |- G = ( +v ` U ) $.
    nvsubadd.3 $e |- M = ( -v ` U ) $.
    $( Relationship between vector subtraction and addition.  (Contributed by
       NM, 14-Dec-2007.)  (New usage is discouraged.) $)
    nvsubadd $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                ( ( A M B ) = C <-> ( B G C ) = A ) ) $=
      ( wcel w3a wa co wceq cfv eqid 3adant3r3 eqeq1d 3jca cnv c1 cns nvmval wb
      cc neg1cn nvscl mp3an2 3adant2 nvgcl syld3an3 simpr3 simpr2 nvlcan syldan
      simprr simprl adantrl nvadd12 nvrinv oveq2d nv0rid 3eqtrd 3adantr3 bitr3d
      cneg cn0v adantrr eqcom syl6bb bitrd ) DUAKZAGKZBGKZCGKZLZMZABFNZCOAUBVGZ
      BDUCPZNZENZCOZBCENZAOZVRVSWCCVMVNVOVSWCOVPABWADEFGHIWAQZJUDRSVRWDAWEOZWFV
      RBWCENZWEOZWDWHVMVQWCGKZVPVOLWJWDUEVRWKVPVOVMVNVOWKVPVMVNVOWBGKZWKVMVOWLV
      NVMVTUFKVOWLUGVTBWADGHWGUHUIZUJAWBDEGHIUKULRVMVNVOVPUMVMVNVOVPUNTWCCBDEGH
      IUOUPVRWIAWEVMVNVOWIAOVPVMVNVOMZMZWIABWBENZENZADVHPZENZAVMWNVOVNWLLWIWQOW
      OVOVNWLVMVNVOUQVMVNVOURVMVOWLVNWMUSTBAWBDEGHIUTUPWOWPWRAEVMVOWPWROVNBWADE
      GWRHIWGWRQZVAUSVBVMVNWSAOVOADEGWRHIWTVCVIVDVESVFAWEVJVKVL $.

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

    $( Associative-type law for vector addition and subtraction.  (Contributed
       by NM, 24-Jan-2008.)  (New usage is discouraged.) $)
    nvaddsubass $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
              ( ( A G B ) M C ) = ( A G ( B M C ) ) ) $=
      ( cnv wcel cgr w3a co wceq nvgrp bafval vsfval grpomuldivass sylan ) DKLE
      MLAGLBGLCGLNABEOCFOABCFOEOPDEIQABCFEGDEGHIRDEFIJSTUA $.

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
    nvsubsub23.1 $e |- X = ( BaseSet ` U ) $.
    nvsubsub23.3 $e |- M = ( -v ` U ) $.
    $( Swap subtrahend and result of vector subtraction.  (Contributed by NM,
       14-Dec-2007.)  (New usage is discouraged.) $)
    nvsubsub23 $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                ( ( A M B ) = C <-> ( A M C ) = B ) ) $=
      ( cnv wcel w3a wa cpv cfv co wceq eqid nvcom 3adant3r1 nvsubadd eqeq1d wb
      3ancomb sylan2b 3bitr4d ) DIJZAFJZBFJZCFJZKZLZBCDMNZOZAPCBULOZAPZABEOCPAC
      EOBPZUKUMUNAUFUHUIUMUNPUGBCDULFGULQZRSUAABCDULEFGUQHTUJUFUGUIUHKUPUOUBUGU
      HUIUCACBDULEFGUQHTUDUE $.

    $( Cancellation law for a normed complex vector space.  (Contributed by NM,
       17-Dec-2007.)  (New usage is discouraged.) $)
    nvnncan $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
         ( A M ( A M B ) ) = B ) $=
      ( wcel co c1 wceq eqid nvmval neg1cn nvscl mp3an2 3adant2 syl13anc oveq2d
      cfv cnv w3a cneg cns cpv cn0v nvmcl syld3an3 cc simp1 a1i simp2 nvdi cmul
      wa ax-1cn mul2negi 1t1e1 eqtri oveq1i syl5eq nvsass mp3anr1 mpanr1 eqtr3d
      nvsid 3eqtr4d 3adant3 simp3 nvass nvrinv oveq1d 3eqtr2d nv0lid 3eqtrd ) C
      UAHZAEHZBEHZUBZAABDIZDIZAJUCZVTCUDTZIZCUETZIZCUFTZBWEIZBVPVQVRVTEHWAWFKAB
      CDEFGUGAVTWCCWEDEFWELZWCLZGMUHVSWFAWBAWCIZBWEIZWEIZAWKWEIZBWEIZWHVSWDWLAW
      EVSWBAWBBWCIZWEIZWCIZWKWBWPWCIZWEIZWDWLVSVPWBUIHZVQWPEHZWRWTKVPVQVRUJZXAV
      SNUKVPVQVRULZVPVRXBVQVPXAVRXBNWBBWCCEFWJOPQWBAWPWCCWEEFWIWJUMRVSVTWQWBWCA
      BWCCWEDEFWIWJGMSVSBWSWKWEVPVRBWSKVQVPVRUOZWBWBUNIZBWCIZBWSXEXGJBWCIBXFJBW
      CXFJJUNIJJJUPUPUQURUSUTBWCCEFWJVFVAVPXAVRXGWSKZNVPXAXAVRXHNWBWBBWCCEFWJVB
      VCVDVEQSVGSVSVPVQWKEHZVRWOWMKXCXDVPVQXIVRVPXAVQXINWBAWCCEFWJOPVHVPVQVRVIA
      WKBCWEEFWIVJRVSWNWGBWEVPVQWNWGKVRAWCCWEEWGFWIWJWGLZVKVHVLVMVPVRWHBKVQBCWE
      EWGFWIXJVNQVO $.
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
      ( cnv wcel cr nvf ffvelrnda ) BGHDIACBCDEFJK $.

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
    nvdm.2 $e |- G = ( +v ` U ) $.
    nvdm.6 $e |- N = ( normCV ` U ) $.
    $( Two ways to express the set of vectors in a normed complex vector
       space.  (Contributed by NM, 31-Jan-2007.)
       (New usage is discouraged.) $)
    nvdm $p |- ( U e. NrmCVec -> ( X = dom N <-> X = ran G ) ) $=
      ( cnv wcel cdm crn cr wf wceq cba cfv eqid bafval eqcomi nvf fdm eqeq2d
      syl ) AGHZCIZBJZDUCUEKCLUDUEMACUEANOZUEABUFUFPEQRFSUEKCTUBUA $.
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
      eqid oveq2d eqeq12d oveq1 oveq1d rspc2v syl5 3impia 3com13 ) BFLZAMLZDUAL
      ZABCNZEOZAPOZBEOZQNZRZVLVMVNVTVNJSZKSZCNZEOZWAPOZWBEOZQNZRZJMTZKFTZVLVMUB
      VTVNWFUCRWBDUHOZRUDZWIWBWADUEOZNEOWFWAEOUFNUGUIJFTZUJZKFTZWJVNWMCUKULLFUM
      EUNWPKJCDWMEFWKGWMVCHWKVCIUOUPWOWIKFWLWIWNUQURUSWHVTWABCNZEOZWEVRQNZRKJBA
      FMWBBRZWDWRWGWSWTWCWQEWBBWACUTVAWTWFVRWEQWBBEVBVDVEWAARZWRVPWSVSXAWQVOEWA
      ABCVFVAXAWEVQVRQWAAPVBVGVEVHVIVJVK $.

    $( The norm of a scalar product with a nonnegative real.  (Contributed by
       NM, 1-Jan-2008.)  (New usage is discouraged.) $)
    nvsge0 $p |- ( ( U e. NrmCVec /\ ( A e. RR /\ 0 <_ A ) /\ B e. X ) ->
               ( N ` ( A S B ) ) = ( A x. ( N ` B ) ) ) $=
      ( cnv wcel cr cc0 cle wbr wa co cfv cmul wceq w3a cabs cc recn adantr nvs
      syl3an2 absid 3ad2ant2 oveq1d eqtrd ) DJKZALKZMANOZPZBFKZUAZABCQERZAUBRZB
      ERZSQZAUTSQUOULAUCKZUPURVATUMVBUNAUDUEABCDEFGHIUFUGUQUSAUTSUOULUSATUPAUHU
      IUJUK $.

    $( The norm of the negative of a vector.  (Contributed by NM,
       28-Nov-2006.)  (New usage is discouraged.) $)
    nvm1 $p |- ( ( U e. NrmCVec /\ A e. X ) ->
               ( N ` ( -u 1 S A ) ) = ( N ` A ) ) $=
      ( cnv wcel wa c1 cneg co cfv cabs cmul cc wceq neg1cn mp3an2 absnegi abs1
      nvs ax-1cn eqtri oveq1i nvcl recnd mulid2d syl5eq eqtrd ) CIJZAEJZKZLMZAB
      NDOZUPPOZADOZQNZUSUMUPRJUNUQUTSTUPABCDEFGHUDUAUOUTLUSQNUSURLUSQURLPOLLUEU
      BUCUFUGUOUSUOUSACDEFHUHUIUJUKUL $.
  $}

  ${
    nvdif.1 $e |- X = ( BaseSet ` U ) $.
    nvdif.2 $e |- G = ( +v ` U ) $.
    nvdif.4 $e |- S = ( .sOLD ` U ) $.
    nvdif.6 $e |- N = ( normCV ` U ) $.
    $( TODO - make this obsolete in favor of nvsub $)
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
      nvscl nvgcl syld3an3 nvcl syl2anc recnd mulid2d cabs absnegi eqtri oveq1i
      cc absi negcli nvs simp2 nvdi mp3anr1 syl12anc mulneg1i ixi negeqi ax-1cn
      wa negnegi nvsass mpanr1 nvsid 3eqtr3a oveq2d 3adant3 nvcom 3eqtrd fveq2d
      syld3an2 eqtr3d syl5eqr ) DUALZAGLZBGLZUBZMANBCOZEOZFPZQOZWJBNRZACOZEOZFP
      ZWGWJWGWJWGWDWIGLZWJUCLWDWEWFUDZWDWEWFWHGLZWPWDWFWRWEWDNURLZWFWRSNBCDGHJU
      GUEUFZAWHDEGHIUHUIZWIDFGHKUJUKULUMWGWKWLUNPZWJQOZWOXBMWJQXBNUNPMNSUOUSUPU
      QWGWLWICOZFPZXCWOWGWDWPXEXCTZWQXAWDWLURLZWPXFNSUTZWLWICDFGHJKVAUEUKWGXDWN
      FWGXDWMWLWHCOZEOZWMBEOZWNWGWDWEWRXDXJTZWQWDWEWFVBWTWDXGWEWRXLXHWLAWHCDEGH
      IJVCVDVEWGXIBWMEWDWFXIBTWEWDWFVJWLNQOZBCOZMBCOXIBXMMBCXMNNQOZRZMNNSSVFXPM
      RZRMXOXQVGVHMVIVKUPUPUQWDWSWFXNXITZSWDXGWSWFXRXHWLNBCDGHJVLVDVMBCDGHJVNVO
      UFVPWDWMGLZWEWFXKWNTWDWEXSWFWDXGWEXSXHWLACDGHJUGUEVQWMBDEGHIVRWAVSVTWBWCW
      B $.
  $}

  ${
    nvsub.1 $e |- X = ( BaseSet ` U ) $.
    nvsub.3 $e |- M = ( -v ` U ) $.
    nvsub.6 $e |- N = ( normCV ` U ) $.
    $( The norm of the difference between two vectors.  (Contributed by NM,
       14-Dec-2007.)  (New usage is discouraged.) $)
    nvsub $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
               ( N ` ( A M B ) ) = ( N ` ( B M A ) ) ) $=
      ( cnv wcel w3a c1 cneg cns cfv co eqid nvmval fveq2d nvdif 3com23 3eqtr4d
      cpv wceq ) CJKZAFKZBFKZLZAMNZBCOPZQCUDPZQZEPBUJAUKQULQZEPABDQZEPBADQZEPAB
      UKCULEFGULRZUKRZIUAUIUOUMEABUKCULDFGUQURHSTUIUPUNEUFUHUGUPUNUEBAUKCULDFGU
      QURHSUBTUC $.
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
      ( vx vy wcel cfv cc0 wceq wi cv co wral eqid fveq2 cnv wa cns cabs cc cpv
      cmul caddc cle wbr w3a cop cvc cr wf nvi simp3d simp1 ralimi eqeq1d eqeq1
      imbi12d rspccv 3syl imp nvz0 sylan9eqr ex adantr impbid ) BUAKZADKZUBACLZ
      MNZAENZVKVLVNVOOZVKIPZCLZMNZVQENZOZJPZVQBUCLZQCLWBUDLVRUGQNJUERZVQWBBUFLZ
      QCLVRWBCLUHQUIUJJDRZUKZIDRZWAIDRVLVPOVKWEWCULUMKDUNCUOWHIJWCBWECDEFWESWCS
      GHUPUQWGWAIDWAWDWFURUSWAVPIADVQANZVSVNVTVOWIVRVMMVQACTUTVQAEVAVBVCVDVEVKV
      OVNOVLVKVOVNVOVKVMECLMAECTBCEGHVFVGVHVIVJ $.
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
      simp3 syl oveq1 fveq2d fveq2 oveq1d oveq2 oveq2d rspc2v syl5 3impia 3comr
      breq12d ) AFLZBFLZCUALZABDMZENZAENZBENZOMZPQZVPVQVRWDVRJRZKRZDMZENZWEENZW
      FENZOMZPQZKFSZJFSZVPVQUBWDVRWIUGTWECUCNZTUHZWFWECUDNUENZMENWFUFNWIUIMTKUJ
      SZWMUKZJFSZWNVRDWQULUMLFUNEUOWTJKWQCDEFWOGHCUPNZWQXACXAUQURUSWOUQIUTVAWSW
      MJFWPWRWMVCVBVDWLWDAWFDMZENZWAWJOMZPQJKABFFWEATZWHXCWKXDPXEWGXBEWEAWFDVEV
      FXEWIWAWJOWEAEVGVHVOWFBTZXCVTXDWCPXFXBVSEWFBADVIVFXFWJWBWAOWFBEVGVJVOVKVL
      VMVN $.
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
      nvtri abs1 eqtri oveq1i nvcl recnd mulid2d syl5eq eqtr2d oveq2d 3brtr4d )
      CUAJZAFJZBFJZUBZAKUEZBCUCLZMZCUFLZMZELZAELZVOELZNMZABDMZELVSBELZNMOVIVJVK
      VOFJZVRWAOUGVIVKWDVJVIVMUDJZVKWDPVMBVNCFGVNQZUHRSAVOCVPEFGVPQZIURUIVLWBVQ
      EABVNCVPDFGWGWFHUJUKVLWCVTVSNVIVKWCVTULVJVIVKUMZVTVMUNLZWCTMZWCVIWEVKVTWJ
      ULPVMBVNCEFGWFIUORWHWJKWCTMWCWIKWCTWIKUNLKKUPUQUSUTVAWHWCWHWCBCEFGIVBVCVD
      VEVFSVGVH $.

    $( Triangle inequality for the norm of a vector difference.  (Contributed
       by NM, 24-Feb-2008.)  (New usage is discouraged.) $)
    nvmtri2 $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
          ( N ` ( A M C ) ) <_ ( ( N ` ( A M B ) ) + ( N ` ( B M C ) ) ) ) $=
      ( cnv wcel w3a wa co cfv cpv caddc cle nvmcl cgr wceq nvgrp bafval vsfval
      eqid grponpncan sylan eqcomd fveq2d wbr simpl 3adant3r3 3adant3r1 syl3anc
      nvtri eqbrtrd ) DKLZAGLZBGLZCGLZMZNZACEOZFPABEOZBCEOZDQPZOZFPZVEFPVFFPROZ
      SVCVDVHFVCVHVDURVGUALVBVHVDUBDVGVGUFZUCABCEVGGDVGGHVKUDDVGEVKIUEUGUHUIUJV
      CURVEGLZVFGLZVIVJSUKURVBULURUSUTVLVAABDEGHITUMURUTVAVMUSBCDEGHITUNVEVFDVG
      FGHVKJUPUOUQ $.
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
       (New usage is discouraged.) $)
    nvge0 $p |- ( ( U e. NrmCVec /\ A e. X ) -> 0 <_ ( N ` A ) ) $=
      ( wcel wa c2 cr cfv cc0 wbr co cle jctil c1 caddc wceq eqid cnv cmul nvcl
      clt 2re cneg cns cpv cn0v nvz0 adantr ax-1cn negidi oveq1i nv0 syl5req cc
      neg1cn nvdir mp3anr1 mpanr1 nvsid oveq1d 3eqtrd fveq2d eqtr3d nvscl nvtri
      mp3an2 mpd3an3 eqbrtrd nvm1 oveq2d 2timesd eqtr4d breqtrd prodge0 syl2anc
      recnd 2pos ) BUAGZADGZHZIJGZACKZJGZHLIUDMZLIWEUBNZOMZHLWEOMWCWFWDABCDEFUC
      ZUEPWCWIWGWCLWEQUFZABUGKZNZCKZRNZWHOWCLAWMBUHKZNZCKZWOOWCBUIKZCKZLWRWAWTL
      SWBBCWSWSTZFUJUKWCWSWQCWCWSQWKRNZAWLNZQAWLNZWMWPNZWQWCXCLAWLNWSXBLAWLQULU
      MUNAWLBDWSEWLTZXAUOUPWAWKUQGZWBXCXESZURWAQUQGXGWBXHULQWKAWLBWPDEWPTZXFUSU
      TVAWCXDAWMWPAWLBDEXFVBVCVDVEVFWAWBWMDGZWRWOOMWAXGWBXJURWKAWLBDEXFVGVIAWMB
      WPCDEXIFVHVJVKWCWOWEWERNWHWCWNWEWERAWLBCDEXFFVLVMWCWEWCWEWJVSVNVOVPVTPIWE
      VQVR $.
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
      eqid nvvop opeq1d syl5eqr eqtrd ) BHIZBBJKZBLKZMZCAMZDMZHNUFBUIOPBHQRUFUI
      UGDMUKDUHUGBDGSTUFUGUJDABCUGUGUAEFUBUCUDUE $.
  $}

  $( TODO?  is this needed? $)
  $( The vector addition and scalar product operations are not identical.
     (Contributed by NM, 31-May-2008.)  (New usage is discouraged.) $)
  nvoprne $p |- ( <. <. G , S >. , N >. e. NrmCVec -> G =/= S ) $=
    ( cop cnv wcel cvc wne nvvcop vcoprne syl ) BADZCDEFLGFBAHCLIABJK $.

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
      ( vx vy cmul caddc cabs cc cc0 cablo cgr cnaddablo ablogrpo ax-mp ax-addf
      wcel cxp fdmi cv wceq grporn cnid cncvc abs00 biimpa absmul abstri isnvi
      absf cfv ) CDEAFGHIFHFJPFKPLFMNHHQHFORUAUBUCUICSZHPUKGUJITUKITUKUDUEDSZUK
      UFUKULUGBUH $.
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
      ( caddc crn cpv cfv cc cba cnnvg rneqi cablo cgr cnaddablo ablogrpo ax-mp
      wcel cxp ax-addf fdmi eqid grporn bafval 3eqtr4i ) CDAEFZDGAHFZCUDABIJCGC
      KPCLPMCNOGGQGCRSUAAUDUEUETUDTUBUC $.
  $}

  $( Derive the associative law for complex number addition ~ addass to
     demonstrate the use of ~ cnnv , ~ cnnvg , and ~ cnnvba .  (Contributed by
     NM, 12-Jan-2008.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  cnnvdemo $p |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A + B ) + C ) =
      ( A + ( B + C ) ) ) $=
    ( caddc cmul cop cabs cnv wcel cc co wceq eqid cnnv cnnvba cnnvg nvass mpan
    w3a ) DEFGFZHIAJIBJICJISABDKCDKABCDKDKLTTMZNABCTDJTUAOTUAPQR $.

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
      ( vx vy cc cv cmin co cmpt2 c1 cneg cmul caddc cnsb wcel wceq mulm1 ax-mp
      cfv wa adantl oveq2d negsub eqtr2d mpt2eq3ia cxp wfn wf subf ffn fnov cnv
      mpbi cnnv cnnvba cnnvg cnnvs eqid nvmfval 3eqtr4i ) CDEECFZDFZGHZIZCDEEVA
      JKVBLHZMHZIZGANSZCDEEVCVFVAEOZVBEOZTZVFVAVBKZMHVCVKVEVLVAMVJVEVLPVIVBQUAU
      BVAVBUCUDUEGEEUFZUGZGVDPVMEGUHVNUIVMEGUJRCDEEGUKUMAULOVHVGPABUNCDLAMVHEAB
      UOABUPABUQVHURUSRUT $.
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
       distance function of its induced metric.  Problem 1 of [Kreyszig]
       p. 63.  (Contributed by NM, 4-Dec-2006.)  (New usage is discouraged.) $)
    nvnd $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( N ` A ) = ( A D Z ) ) $=
      ( cnv wcel wa co cnsb cfv wceq adantr eqid mpd3an3 nvzcl imsdval cneg cns
      c1 cpv nvmval cc neg1cn nvsz mpan2 oveq2d nv0rid 3eqtrd fveq2d eqtr2d ) C
      KLZAELZMZAFBNZAFCOPZNZDPZADPUQURFELZUTVCQUQVDURCEFGHUARZAFBCVADEGVASZIJUB
      TUSVBADUSVBAUEUCZFCUDPZNZCUFPZNZAFVJNZAUQURVDVBVKQVEAFVHCVJVAEGVJSZVHSZVF
      UGTUQVKVLQURUQVIFAVJUQVGUHLVIFQUIVGVHCFVNHUJUKULRACVJEFGVMHUMUNUOUP $.
  $}

  ${
    $d x y z U $.  $d x y z X $.
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
      ( wcel co wceq mp3an1 vx vy vz cba cfv cvv eqeltri cnv cxp cr imsdf ax-mp
      fvex wf cv wa cc0 c1 cneg imsdval2 eqeq1d wb cc neg1cn nvscl nvgcl sylan2
      mp3an12 nvz sylancr nvzcl w3a nvrcan mpan mp3an2 simpl adantl simpr nvass
      sylancom syl3anc nvlinv oveq2d nv0rid adantr 3eqtrd nv0lid eqeq12d bitr3d
      3bitrd caddc cle wbr syl2anc 3adant3 3adant2 nvtri 3adant1 simp1 3ad2ant3
      oveq1d eqtr3d fveq2d eqtr4d nvdif eqtrd oveq12d 3brtr4d 3coml ismeti ) UA
      UBUCAGGCUDUEUFICUDUMUGCUHQZGGUIUJAUNPACGIOUKULUAUOZGQZUBUOZGQZUPZXLXNARZU
      QSXLURUSZXNBRZDRZFUEZUQSZXTHSZXLXNSZXPXQYAUQXKXMXOXQYASZPXLXNABCDFGIJLNOU
      TTZVAXPXKXTGQZYBYCVBPXOXMXSGQZYGXKXRVCQZXOYHPVDXRXNBCGILVEVHZXKXMYHYGPXLX
      SCDGIJVFTVGZXTCFGHIMNVIVJXPXTXNDRZHXNDRZSZYCYDXMXOYGYNYCVBZYKYGHGQZXOYOXK
      YPPCGHIMVKULXKYGYPXOVLYOPXTHXNCDGIJVMVNVOVTXPYLXLYMXNXPYLXLXSXNDRZDRZXLHD
      RZXLXPXMYHXOYLYRSZXMXOVPXOYHXMYJVQXMXOVRXKXMYHXOVLYTPXLXSXNCDGIJVSVNWAXPY
      QHXLDXOYQHSZXMXKXOUUAPXNBCDGHIJLMWBVNVQWCXMYSXLSZXOXKXMUUBPXLCDGHIJMWDVNZ
      WEWFXOYMXNSZXMXKXOUUDPXNCDGHIJMWGVNVQWHWIWJUCUOZGQZXMXOXQUUEXLARZUUEXNARZ
      WKRZWLWMUUFXMXOVLZXLXRUUEBRZDRZUUEXSDRZDRZFUEZUULFUEZUUMFUEZWKRZXQUUIWLUU
      JUULGQZUUMGQZUUOUURWLWMZUUFXMUUSXOUUFXMUPZXMUUKGQZUUSUUFXMVRZUUFUVCXMXKYI
      UUFUVCPVDXRUUEBCGILVEVHWEZXKXMUVCUUSPXLUUKCDGIJVFTWNWOZUUFXOUUTXMXOUUFYHU
      UTYJXKUUFYHUUTPUUEXSCDGIJVFTVGWPXKUUSUUTUVAPUULUUMCDFGIJNWQTWNUUJXQYAUUOX
      MXOYEUUFYFWRUUJUUNXTFUUJUULUUEDRZXSDRZUUNXTUUJUUSUUFYHUVHUUNSZUVFUUFXMXOW
      SXOUUFYHXMYJWTXKUUSUUFYHVLUVIPUULUUEXSCDGIJVSVNWAUUJUVGXLXSDUUFXMUVGXLSXO
      UVBUVGXLUUKUUEDRZDRZYSXLUVBXMUVCUUFUVGUVKSZUVDUVEUUFXMVPXKXMUVCUUFVLUVLPX
      LUUKUUECDGIJVSVNWAUVBUVJHXLDUUFUVJHSZXMXKUUFUVMPUUEBCDGHIJLMWBVNWEWCXMUUB
      UUFUUCVQWFWOXAXBXCXDUUJUUGUUPUUHUUQWKUUFXMUUGUUPSXOUVBUUGUUEXRXLBRDRFUEZU
      UPXKUUFXMUUGUVNSPUUEXLABCDFGIJLNOUTTXKUUFXMUVNUUPSPUUEXLBCDFGIJLNXETXFWOU
      UFXOUUHUUQSZXMXKUUFXOUVOPUUEXNABCDFGIJLNOUTTWPXGXHXIXJ $.
  $}

  ${
    imsmet.1 $e |- X = ( BaseSet ` U ) $.
    imsmet.8 $e |- D = ( IndMet ` U ) $.
    $( The induced metric of a normed complex vector space is a metric space.
       Part of Definition 2.2-1 of [Kreyszig] p. 58.  (Contributed by NM,
       4-Dec-2006.)  (Revised by Mario Carneiro, 10-Sep-2015.)
       (New usage is discouraged.) $)
    imsmet $p |- ( U e. NrmCVec -> D e. ( Met ` X ) ) $=
      ( cnv wcel cims cfv cme caddc cmul cop cabs cif wceq fveq2 syl5eq eqid
      cba fveq2d eleq12d cns cpv cnmcv cn0v elimnvu imsmetlem dedth syl5eqel
      cgn ) BFGZABHIZCJIZEULUMUNGULBKLMNMZOZHIZUPTIZJIZGBUOBUPPZUMUQUNUSBUPHQUT
      CURJUTCBTIURDBUPTQRUAUBUQUPUCIZUPUPUDIZVBUKIZUPUEIZURUPUFIZURSVBSVCSVASVE
      SVDSUQSBUGUHUIUJ $.

    $( The induced metric of a normed complex vector space is an extended
       metric space.  (Contributed by Mario Carneiro, 10-Sep-2015.)
       (New usage is discouraged.) $)
    imsxmet $p |- ( U e. NrmCVec -> D e. ( *Met ` X ) ) $=
      ( cnv wcel cme cfv cxmt imsmet metxmet syl ) BFGACHIGACJIGABCDEKACLM $.
  $}

  ${
    nvelbl.1 $e |- X = ( BaseSet ` U ) $.
    nvelbl.3 $e |- M = ( -v ` U ) $.
    nvelbl.6 $e |- N = ( normCV ` U ) $.
    nvelbl.8 $e |- D = ( IndMet ` U ) $.
    $( Membership of a vector in a ball.  (Contributed by NM, 27-Dec-2007.)
       (Revised by Mario Carneiro, 10-Jan-2014.)
       (New usage is discouraged.) $)
    nvelbl $p |- ( ( ( U e. NrmCVec /\ R e. RR+ ) /\ ( P e. X /\ A e. X ) ) ->
                   ( A e. ( P ( ball ` D ) R ) <-> ( N ` ( A M P ) ) < R ) ) $=
      ( cnv wcel crp wa cfv co clt wbr cbl cxmt cxr wb imsxmet rpxr elbl3 sylan
      anim12i wceq imsdval 3com23 3expb adantlr breq1d bitrd ) EMNZDONZPZCHNZAH
      NZPZPZACDBUAQRNZACBRZDSTZACFRGQZDSTUSBHUBQNZDUCNZPVBVDVFUDUQVHURVIBEHILUE
      DUFUIABCDHUGUHVCVEVGDSUQVBVEVGUJZURUQUTVAVJUQVAUTVJACBEFGHIJKLUKULUMUNUOU
      P $.
  $}

  ${
    nvelbl2.1 $e |- X = ( BaseSet ` U ) $.
    nvelbl2.2 $e |- G = ( +v ` U ) $.
    nvelbl2.6 $e |- N = ( normCV ` U ) $.
    nvelbl2.8 $e |- D = ( IndMet ` U ) $.
    $( Membership of an off-center vector in a ball.  (Contributed by NM,
       27-Dec-2007.)  (Revised by Mario Carneiro, 10-Jan-2014.)
       (New usage is discouraged.) $)
    nvelbl2 $p |- ( ( ( U e. NrmCVec /\ R e. RR+ ) /\ ( P e. X /\ A e. X ) ) ->
                   ( ( P G A ) e. ( P ( ball ` D ) R ) <-> ( N ` A ) < R ) ) $=
      ( wcel wa co cfv clt wbr 3expb adantlr cnv crp cbl cnsb simprl nvgcl eqid
      wb jca nvelbl syldan wceq nvpncan2 fveq2d breq1d bitrd ) EUAMZDUBMZNZCHMZ
      AHMZNZNZCAFOZCDBUCPOMZVDCEUDPZOZGPZDQRZAGPZDQRUSVBUTVDHMZNVEVIUHVCUTVKUSU
      TVAUEUQVBVKURUQUTVAVKCAEFHIJUFSTUIVDBCDEVFGHIVFUGZKLUJUKVCVHVJDQVCVGAGUQV
      BVGAULZURUQUTVAVMCAEFVFHIJVLUMSTUNUOUP $.
  $}

  ${
    nvlmcl.1 $e |- X = ( BaseSet ` U ) $.
    nvlmcl.2 $e |- D = ( IndMet ` U ) $.
    nvlmcl.3 $e |- J = ( MetOpen ` D ) $.
    $( Closure of the limit of a converging vector sequence.  (Contributed by
       NM, 26-Dec-2007.)  (Revised by Mario Carneiro, 10-Sep-2015.)
       (New usage is discouraged.) $)
    nvlmcl $p |- ( ( U e. NrmCVec /\ F ( ~~>t ` J ) P ) -> P e. X ) $=
      ( cnv wcel ctopon cfv clm wbr cxmt imsxmet mopntopon syl lmcl sylan ) CJK
      ZEFLMKZDBENMOBFKUBAFPMKUCACFGHQAEFIRSBDEFTUA $.

    $d k D $.  $d k F $.  $d k J $.  $d k P $.  $d k R $.  $d k U $.  $d k X $.
    $d k ph $.
    nvlmle.5 $e |- N = ( normCV ` U ) $.
    nvlmle.6 $e |- ( ph -> U e. NrmCVec ) $.
    nvlmle.7 $e |- ( ph -> F : NN --> X ) $.
    nvlmle.8 $e |- ( ph -> F ( ~~>t ` J ) P ) $.
    nvlmle.9 $e |- ( ph -> R e. RR ) $.
    nvlmle.10 $e |- ( ( ph /\ k e. NN ) -> ( N ` ( F ` k ) ) <_ R ) $.
    $( If the norm of each member of a converging sequence is less than or
       equal to a given amount, so is the norm of the convergence value.
       (Contributed by NM, 25-Dec-2007.)  (Revised by Mario Carneiro,
       5-May-2014.)  (New usage is discouraged.) $)
    nvlmle $p |- ( ph -> ( N ` P ) <_ R ) $=
      ( wcel cfv cn0v co cle cnv wceq clm nvlmcl syl2anc eqid nvnd cxmt imsxmet
      wbr syl nvzcl xmetsym syl3anc eqtrd c1 cn cz 1z a1i rexrd cv wa ffvelrnda
      nnuz adantr eqbrtrrd lmle eqbrtrd ) ACIUAZEUBUAZCBUCZDUDAVNCVOBUCZVPAEUET
      ZCJTZVNVQUFOAVRGCHUGUAUNVSOQBCEGHJKLMUHUIZCBEIJVOKVOUJZNLUKUIABJULUATZVSV
      OJTZVQVPUFAVRWBOBEJKLUMUOZVTAVRWCOEJVOKWAUPUOZCVOBJUQURUSABCVODFGHUTJVAVI
      MWDUTVBTAVCVDQWEADRVEAFVFZVATZVGZWFGUAZIUAZVOWIBUCZDUDWHWJWIVOBUCZWKWHVRW
      IJTZWJWLUFAVRWGOVJAVAJWFGPVHZWIBEIJVOKWANLUKUIWHWBWMWCWLWKUFAWBWGWDVJWNAW
      CWGWEVJWIVOBJUQURUSSVKVLVM $.
  $}

  ${
    $d t u v w x y z $.
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
       by Jeffrey Hankins, 16-Jun-2009.)  (Revised by Mario Carneiro,
       10-Sep-2015.)  (New usage is discouraged.) $)
    vacn $p |- ( U e. NrmCVec -> G e. ( ( J tX J ) Cn J ) ) $=
      ( vz vw wcel co cfv cv clt wbr wa wral crp cr syl3anc vx vs vy vr cnv ctx
      ccn cba cxp wf wi wrex eqid nvgf c2 cdiv rphalfcl adantl caddc cme imsmet
      simplll syl simplrl adantr simprl metcl simplrr simprr ad2antlr lt2halves
      rpre cnsb cnmcv nvmcl nvtri wceq nvgcl imsdval nvaddsub4 syl122anc fveq2d
      eqtrd oveq12d 3brtr4d readdcld lelttr mpand syld ralrimivva breq2 anbi12d
      cle imbi1d 2ralbidv rspcev syl2anc ralrimiva wb imsxmet txmetcn mpbir2and
      cxmt ) BUEJZCDDUFKDUGKJZBUHLZXFUIXFCUJZUAMZHMZAKZUBMZNOZUCMZIMZAKZXKNOZPZ
      XHXMCKZXIXNCKZAKZUDMZNOZUKZIXFQHXFQZUBRULZUDRQZUCXFQUAXFQZBCXFXFUMZGUNXDY
      FUAUCXFXFXDXHXFJZXMXFJZPZPZYEUDRYLYARJZPZYAUOUPKZRJZXJYONOZXOYONOZPZYBUKZ
      IXFQHXFQZYEYMYPYLYAUQURYNYTHIXFXFYNXIXFJZXNXFJZPZPZYSXJXOUSKZYANOZYBUUEXJ
      SJZXOSJZYASJZYSUUGUKUUEAXFUTLJZYIUUBUUHUUEXDUUKXDYKYMUUDVBZABXFYHEVAVCZYN
      YIUUDXDYIYJYMVDVEZYNUUBUUCVFZXHXIAXFVGTZUUEUUKYJUUCUUIUUMYNYJUUDXDYIYJYMV
      HVEZYNUUBUUCVIZXMXNAXFVGTZYMUUJYLUUDYAVLVJZXJXOYAVKTUUEXTUUFWMOZUUGYBUUEX
      HXIBVMLZKZXMXNUVBKZCKZBVNLZLZUVCUVFLZUVDUVFLZUSKZXTUUFWMUUEXDUVCXFJZUVDXF
      JZUVGUVJWMOUULUUEXDYIUUBUVKUULUUNUUOXHXIBUVBXFYHUVBUMZVOTUUEXDYJUUCUVLUUL
      UUQUURXMXNBUVBXFYHUVMVOTUVCUVDBCUVFXFYHGUVFUMZVPTUUEXTXRXSUVBKZUVFLZUVGUU
      EXDXRXFJZXSXFJZXTUVPVQUULUUEXDYIYJUVQUULUUNUUQXHXMBCXFYHGVRTZUUEXDUUBUUCU
      VRUULUUOUURXIXNBCXFYHGVRTZXRXSABUVBUVFXFYHUVMUVNEVSTUUEUVOUVEUVFUUEXDYIYJ
      UUBUUCUVOUVEVQUULUUNUUQUUOUURXHXMXIXNBCUVBXFYHGUVMVTWAWBWCUUEXJUVHXOUVIUS
      UUEXDYIUUBXJUVHVQUULUUNUUOXHXIABUVBUVFXFYHUVMUVNEVSTUUEXDYJUUCXOUVIVQUULU
      UQUURXMXNABUVBUVFXFYHUVMUVNEVSTWDWEUUEXTSJZUUFSJUUJUVAUUGPYBUKUUEUUKUVQUV
      RUWAUUMUVSUVTXRXSAXFVGTUUEXJXOUUPUUSWFUUTXTUUFYAWGTWHWIWJYDUUAUBYORXKYOVQ
      ZYCYTHIXFXFUWBXQYSYBUWBXLYQXPYRXKYOXJNWKXKYOXONWKWLWNWOWPWQWRWJXDAXFXCLJZ
      UWCUWCXEXGYGPWSABXFYHEWTZUWDUWDUAUCUDUBIHAAACDDDXFXFXFFFFXATXB $.
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
      ex cme mp3an1 syl6 3impib imsmet syl3an1 c1 cneg cns nvabs wceq remetdval
      cpv syl imsdval2 3brtr4d jca31 3expa rpre lelttr expdimp syl2an ralrimdva
      an32s impr breq2 imbi1d ralbidv rspcev syl2anc ralrimivva cxmt wb imsxmet
      rexmet cioo crn ctg cmopn tgioo eqtri metcn sylancl mpbir2and ) BUANZECDU
      BONZBUCPZQEUDZJUIZKUIZAOZLUIZUEUFZXMEPZXNEPZUGUHUJQQUKULZOZMUIZUEUFZUMZKX
      KUNZLRUOZMRUNJXKUNZBEXKXKSZFUPXIYFJMXKRXIXMXKNZYBRNZTTYJXOYBUEUFZYCUMZKXK
      UNZYFXIYIYJUQXIYIYJYMXIYITZYJYLKXKYNXNXKNZTZYJYLYPYAQNZXOQNZTZYAXOURUFZTZ
      YBQNZYLYJXIYIYOUUAXIYIYOUSZYQYRYTXIYIYOYQXIYIYOTXRQNZXSQNZTZYQXIYIUUDYOUU
      EXIYIUUDXMBEXKYHFUTVDXIYOUUEXNBEXKYHFUTVDVAZXTQVEPNUUDUUEYQXTXTSZVBXRXSXT
      QVCVFVGVHXIAXKVEPNYIYOYRABXKYHGVIXMXNAXKVCVJUUCXRXSUHOUGPZXMVKVLXNBVMPZOB
      VQPZOEPYAXOURXMXNUUJBUUKEXKYHUUKSZUUJSZFVNUUCUUFYAUUIVOXIYIYOUUFUUGVHXRXS
      XTUUHVPVRXMXNAUUJBUUKEXKYHUULUUMFGVSVTWAWBYBWCYSUUBYTYLYSUUBTYTYKYCYQYRUU
      BYTYKTYCUMYAXOYBWDWBWEWHWFVDWGWIYEYMLYBRXPYBVOZYDYLKXKUUNXQYKYCXPYBXOUEWJ
      WKWLWMWNWOXIAXKWPPNXTQWPPNXJXLYGTWQABXKYHGWRXTUUHWSJMLKAXTECDXKQHDWTXAXBP
      XTXCPZIXTUUOUUHUUOSXDXEXFXGXH $.
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
      cioo crn ctg cfv nmcvcn sseldi ) BJKCDLMNZONZCDONZEDPKUJUKQDIRLCDSTABCUIE
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
        rpaddcl rpreccld syl5eqel cme a1i simplll simpllr nvscl syl3anc simprll
        imsmet simprlr metcl rpre ad2antlr mettri syl13anc cmul abscld peano2re
        syl rpred remulcld cnsb eqid nvmcl abssubd wceq cnmetdval syl2anc eqtrd
        simprrl eqbrtrrd ltled eqbrtrd lemul1ad mulcomd breqtrd absge0d pncan3d
        subcld rpcnd recnd fveq2d abstrid 1re imsdval cneg neg1cn oveq2d oveq1d
        letrd nvs 3eqtr2d lelttrd breq2 cxmt ltaddrp recgt1d syl5eqbr lemul12ad
        mpbid leadd2dd simprrr le2addd cpv imsdval2 mulcl mulm1d negsubd nvsass
        nvdir 3eqtr3d nvmdi oveq12d ax-1cn addassd adddird rpne0d oveq2i simplr
        3brtr4d divrecd syl6reqr ltp1d addcomd ltdiv23d expr ralrimivva anbi12d
        imbi1d 2ralbidv rspcev ralrimiva rgen2 cnxmet imsxmet cnfldtopn txmetcn
        wb mp3an mpbir2an ) DHGUDTGUETUFZUGJUHJDUIZAUJZUAUJZUKULUMZTZUBUJZUNUOZ
        BUJZUCUJZCTZUWLUNUOZURZUWHUWNDTZUWIUWODTZCTZKUJZUNUOZUSZUCJUPUAUGUPZUBU
        QUTZKUQUPZBJUPAUGUPZFVAUFZUWGRDFJPNVBVCUXGABUGJUWHUGUFZUWNJUFZURZUXFKUQ
        UXLUXBUQUFZURZEUQUFZUWKEUNUOZUWPEUNUOZURZUXCUSZUCJUPUAUGUPZUXFUXNEVDVDU
        WNIVEZUWHUKVEZVFTZVDVFTZUXBVGTZVFTZVGTZUQSUXNUYFUXNVDUQUFUYEUQUFZUYFUQU
        FZVMUXLUYDUQUFUXMUYHUXLUYCUXLUYAUYBUXLUXIUXKUYAVHUFZRUXJUXKVIZUWNFIJPQV
        JZVKZUXJUYBVHUFZUXKUWHVLVNZVOUXLUYAUYBUYMUYOUXLUXIUXKVPUYAVQUOZRUYKUWNF
        IJPQVRZVKUXJVPUYBVQUOUXKUWHVSVNVTWAUYDUXBWBWCZVDUYEWDVKZWEWFZUXNUXSUAUC
        UGJUXNUWIUGUFZUWOJUFZURZUXRUXCUXNVUCUXRURZURZUXAUWSUWIUWNDTZCTZVUFUWTCT
        ZVFTZUXBVUECJWGVEUFZUWSJUFZUWTJUFZUXAVHUFVUJVUEUXIVUJRCFJPLWNVCWHZVUEUX
        IUXJUXKVUKUXIVUERWHZUXJUXKUXMVUDWIZUXJUXKUXMVUDWJZUWHUWNDFJPNWKWLZVUEUX
        IVUAVUBVULVUNUXNVUAVUBUXRWMZUXNVUAVUBUXRWOZUWIUWODFJPNWKWLZUWSUWTCJWPWL
        VUEVUGVUHVUEVUJVUKVUFJUFZVUGVHUFVUMVUQVUEUXIVUAUXKVVAVUNVURVUPUWIUWNDFJ
        PNWKWLZUWSVUFCJWPWLVUEVUJVVAVULVUHVHUFVUMVVBVUTVUFUWTCJWPWLVOZUXMUXBVHU
        FUXLVUDUXBWQWRZVUEVUJVUKVULVVAUXAVUIVQUOVUMVUQVUTVVBUWSUWTVUFCJWSWTVUEV
        UIUYDEXATZUXBVVCVUEUYDEVUEUYCVHUFUYDVHUFVUEUYAUYBVUEUXIUXKUYJRVUPUYLVKZ
        VUEUWHVUOXBZVOUYCXCXDZVUEEUXNUXOVUDUYTVNZXEZXFVVDVUEUWHUWIULTZUKVEZUYAX
        ATZUWIUKVEZUWNUWOFXGVEZTZIVEZXATZVFTUYAEXATZUYBVDVFTZEXATZVFTZVUIVVEVQV
        UEVVMVVRVVSVWAVUEVVLUYAVUEVVKVUEUWHUWIVUOVURYDZXBZVVFXFVUEVVNVVQVUEUWIV
        URXBZVUEUXIVVPJUFZVVQVHUFRVUEUXIUXKVUBVWFVUNVUPVUSUWNUWOFVVOJPVVOXHZXIW
        LZVVPFIJPQVJVKZXFVUEUYAEVVFVVJXFVUEVVTEVUEUYNVVTVHUFVVGUYBXCXDZVVJXFVUE
        VVMEUYAXATVVSVQVUEVVLEUYAVWDVVJVVFVUEUXIUXKUYPRVUPUYQVKVUEVVLUWIUWHULTZ
        UKVEZEVQVUEUWHUWIVUOVURXJZVUEVWLEVUEVWKVUEUWIUWHVURVUOYDZXBZVVJVUEUWKVW
        LEUNVUEUWKVVLVWLVUEUXJVUAUWKVVLXKVUOVURUWHUWIUWJUWJXHXLXMVWMXNUXNVUCUXP
        UXQXOXPXQZXRXSVUEEUYAVUEEVVIYEZVUEUYAVVFYFZXTYAVUEVVNVVTVVQEVWEVWJVWIVV
        JVUEUWIVURYBVUEUXIVWFVPVVQVQUORVWHVVPFIJPQVRVKVUEVVNUYBVWLVFTZVVTVWEVUE
        UYBVWLVVGVWOVOVWJVUEUWHVWKVFTZUKVEVVNVWSVQVUEVWTUWIUKVUEUWHUWIVUOVURYCY
        GVUEUWHVWKVUOVWNYHXPVUEVWLVDUYBVWOVDVHUFZVUEYIWHZVVGVUEVWLEVDVWOVVJVXBV
        WPVUEEVDVVJVXBVUEEUYGVDUNSVUEVDUYFUNUOZUYGVDUNUOVUEVXAUYHVXCYIUXNUYHVUD
        UYRVNZVDUYEUUAVKVUEUYFUXNUYIVUDUYSVNZUUBUUEUUCXQYOUUFYOVUEVVQEVWIVVJVUE
        UWPVVQEUNVUEUXIUXKVUBUWPVVQXKVUNVUPVUSUWNUWOCFVVOIJPVWGQLYJWLUXNVUCUXPU
        XQUUGXPXQUUDUUHVUEVUGVVMVUHVVRVFVUEVUGUWSVDYKZVUFDTZFUUIVEZTZIVEZVVKUWN
        DTZIVEZVVMVUEUXIVUKVVAVUGVXJXKVUNVUQVVBUWSVUFCDFVXHIJPVXHXHZNQLUUJWLVUE
        VXKVXIIVUEUWHVXFUWIXATZVFTZUWNDTZUWSVXNUWNDTZVXHTZVXKVXIVUEUXIUXJVXNUGU
        FZUXKVXPVXRXKVUNVUOVUEVXFUGUFZVUAVXSYLVURVXFUWIUUKVKVUPUWHVXNUWNDFVXHJP
        VXMNUUOWTVUEVXOVVKUWNDVUEVXOUWHUWIYKZVFTVVKVUEVXNVYAUWHVFVUEUWIVURUULYM
        VUEUWHUWIVUOVURUUMXNYNVUEVXQVXGUWSVXHVUEUXIVXTVUAUXKVXQVXGXKVUNVXTVUEYL
        WHVURVUPVXFUWIUWNDFJPNUUNWTYMUUPYGVUEUXIVVKUGUFUXKVXLVVMXKVUNVWCVUPVVKU
        WNDFIJPNQYPWLYQVUEVUHVUFUWTVVOTZIVEZUWIVVPDTZIVEZVVRVUEUXIVVAVULVUHVYCX
        KVUNVVBVUTVUFUWTCFVVOIJPVWGQLYJWLVUEVYDVYBIVUEUXIVUAUXKVUBVYDVYBXKVUNVU
        RVUPVUSUWIUWNUWODFVVOJPVWGNUUQWTYGVUEUXIVUAVWFVYEVVRXKVUNVURVWHUWIVVPDF
        IJPNQYPWLYQUURVUEVVEUYAVVTVFTZEXATVWBVUEUYDVYFEXAVUEUYAUYBVDVWRVUEUYBVV
        GYFVDUGUFVUEUUSWHZUUTYNVUEUYAVVTEVWRVUEVVTVWJYFVWQUVAXNUVEVUEVVEUYDUYFV
        GTZUXBUNVUEVYHUYDUYGXATVVEVUEUYDUYFVUEUYDVVHYFVUEUYFVXEYEVUEUYFVXEUVBUV
        FEUYGUYDXASUVCUVGVUEUYDUXBUYFVVHUXLUXMVUDUVDVXEVUEUYEUYEVDVFTUYFUNVUEUY
        EVUEUYEVXDXEUVHVUEUYEVDVUEUYEVXDYEVYGUVIYAUVJXRYRYRUVKUVLUXEUXTUBEUQUWL
        EXKZUXDUXSUAUCUGJVYIUWRUXRUXCVYIUWMUXPUWQUXQUWLEUWKUNYSUWLEUWPUNYSUVMUV
        NUVOUVPXMUVQUVRUWJUGYTVEUFCJYTVEUFZVYJUWFUWGUXHURUWCUVSUXIVYJRCFJPLUVTV
        CZVYKABKUBUCUAUWJCCDHGGUGJJHOUWAMMUWBUWDUWE $.
    $}

    $( Scalar multiplication is jointly continuous in both arguments.
       (Contributed by NM, 16-Jun-2009.)  (Revised by Mario Carneiro,
       5-May-2014.)  (New usage is discouraged.) $)
    smcn $p |- ( U e. NrmCVec -> S e. ( ( K tX J ) Cn J ) ) $=
      ( wcel ctx co ccn caddc cns cfv cims cmopn syl5eq eqid vx vy cnv cmul cop
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
      ( vx vy cnv wcel cba cfv cv co eqid ctopon cc a1i cnmpt22f cneg cns cmpt2
      cpv ctx ccn nvmfval cxmt imsxmet mopntopon syl cnmpt1st ccnfld cnfldtopon
      c1 ctopn neg1cn cnmpt2c cnmpt2nd smcn vacn eqeltrd ) BJKZDHIBLMZVDHNZUOUA
      ZINZBUBMZOZBUDMZOUCCCUEOCUFOHIVHBVJDVDVDPZVJPZVHPZGUGVCHIVEVIVJCCCCCVDVDV
      CAVDUHMKCVDQMKABVDVKEUIACVDFUJUKZVNVCHICCVDVDVNVNULVCHIVFVGVHCCUMUPMZCCVD
      VDVNVNVCHIVFCCVOVDVDRVNVNVORQMKVCVOVOPZUNSVFRKVCUQSURVCHICCVDVDVNVNUSAVHB
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
    $d k n p u w x y z $.
    $( Define a function that maps a complex normed vector space to its inner
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
      ( cfv c4 co cv cexp cba vu cnv wcel cdip c1 cfz ci c2 cmul csu cdiv cmpt2
      cns cpv cnmcv fveq2 syl6eqr eqidd oveqd oveq123d fveq12d oveq1d sumeq2sdv
      wceq oveq2d mpt2eq123dv df-dip cvv fvex eqeltri mpt2ex fvmpt syl5eq ) EUB
      UCCEUDOABIIUEPUFQZUGFRSQZARZVOBRZDQZGQZHOZUHSQZUIQZFUJZPUKQZULZNUAEABUARZ
      TOZWGVNVOVPVOVQWFUMOZQZWFUNOZQZWFUOOZOZUHSQZUIQZFUJZPUKQZULWEUBUDWFEVDZAB
      WGWGWQIIWDWRWGETOZIWFETUPJUQZWTWRWPWCPUKWRVNWOWBFWRWNWAVOUIWRWMVTUHSWRWKV
      SWLHWRWLEUOOHWFEUOUPMUQWRVPVPWIVRWJGWRWJEUNOGWFEUNUPKUQWRVPURWRWHDVOVQWRW
      HEUMODWFEUMUPLUQUSUTVAVBVEVCVBVFABUAFVGABIIWDIWSVHJETVIVJZXAVKVLVM $.

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
      cmpt2 oveqd oveq1 fveq2d oveq1d oveq2d sumeq2sdv oveq2 eqid ovex sylan9eq
      csu ovmpt2 3impb ) EUCUDZAIUDZBIUDZABCOZUEPUFOZUGFUHQOZAVLBDOZGOZHUIZRQOZ
      SOZFVDZPTOZUJVGVHVIUKVJABUAUBIIVKVLUAUHZVLUBUHZDOZGOZHUIZRQOZSOZFVDZPTOZU
      MZOVSVGCWIABUAUBCDEFGHIJKLMNULUNUAUBABIIWHVSWIVKVLAWBGOZHUIZRQOZSOZFVDZPT
      OVTAUJZWGWNPTWOVKWFWMFWOWEWLVLSWOWDWKRQWOWCWJHVTAWBGUOUPUQURUSUQWABUJZWNV
      RPTWPVKWMVQFWPWLVPVLSWPWKVORQWPWJVNHWPWBVMAGWABVLDUTURUPUQURUSUQWIVAVRPTV
      BVEVCVF $.

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
      negcli mulm1d oveq2d mulneg1 oveq12d mp3an1 syl2anc oveq1d sub32d 3eqtr4d
      eqtrd wceq subdi wa nvsid fveq2d 3adant2 ipval2lem3 recnd mulid2d cn nnuz
      c3 df-4 oveq2 i4 syl6eq cn0 nnnn0 expcl adantl sylan2 mulcld df-3 i3 df-2
      i2 cz 1z exp1 ax-mp fsum1 1nn jctil eqidd fsump1i simprd subadd23d eqtr4d
      addcomd ) EUBNZAHNZBHNZUCZABCOPUDUEOQUAUFZROZAXRBDOZFOZGUGZSROZTOZUAUHZUD
      UIOABFOZGUGZSROZAPUJZBDOZFOZGUGZSROZULOZQAQBDOZFOZGUGZSROZAQUJZBDOZFOZGUG
      ZSROZULOZTOZUKOZUDUIOABCDEUAFGHIJKLMUMXPYDUUEUDUIXPQYQTOZYHYLTOZUKOZYRUUB
      TOZUKOZPAPBDOZFOZGUGZSROZTOZUKOZUUDYLULOZYGUKOZYDUUEXPUUJUUQUUOYGUKXPUUFY
      LULOZQUUBTOZUJZUKOUUSUUTULOZUUJUUQXPUUSUUTXPUUFYLXPQUNNZYQUNNZUUFUNNZUOXP
      UVCUVDUOABQCDEFGHIJKLMUPUQZQYQURUSZXPYHUNNYLUNNUTABYHCDEFGHIJKLMUPUQZVAXP
      UVCUUBUNNZUUTUNNUOXPYRUNNUVIQUOVCABYRCDEFGHIJKLMUPUQZQUUBURUSZVBXPUUHUUSU
      UIUVAUKXPUUHUUFYLUJZUKOUUSXPUUGUVLUUFUKXPYLUVHVDVEXPUUFYLUVGUVHVBVMXPUVCU
      VIUUIUVAVNUOUVJQUUBVFUSVGXPUUQUUFUUTULOZYLULOUVBXPUUDUVMYLULXPUVDUVIUUDUV
      MVNZUVFUVJUVCUVDUVIUVNUOQYQUUBVOVHVIVJXPUUFUUTYLUVGUVKUVHVKVMVLXPUUOPYGTO
      YGXPUUNYGPTXMXOUUNYGVNXNXMXOVPZUUMYFSRUVOUULYEGUVOUUKBAFBDEHIKVQVEVRVJVSV
      EXPYGXPYGABCDEFGHIJKLMVTWAZWBVMVGXPUDWCNYDUUPVNXPYCUUOUUJUUPUAWEPUDWCWDWF
      XQUDVNZXRPYBUUNTUVQXRQUDROPXQUDQRWGWHWIZUVQYAUUMSRUVQXTUULGUVQXSUUKAFUVQX
      RPBDUVRVJVEVRVJVGXPXQWCNZVPXRYBUVSXRUNNZXPUVSUVCXQWJNUVTUOXQWKQXQWLUSZWMU
      VSXPUVTYBUNNUWAABXRCDEFGHIJKLMUPWNWOZXPYCUUIUUHUUJUASPWEWCWDWPXQWEVNZXRYR
      YBUUBTUWCXRQWEROYRXQWEQRWGWQWIZUWCYAUUASRUWCXTYTGUWCXSYSAFUWCXRYRBDUWDVJV
      EVRVJVGUWBXPYCUUGUUFUUHUAPPSWCWDWRXQSVNZXRYHYBYLTUWEXRQSROYHXQSQRWGWSWIZU
      WEYAYKSRUWEXTYJGUWEXSYIAFUWEXRYHBDUWFVJVEVRVJVGUWBXPPPUEOYCUAUHUUFVNZPWCN
      XPPWTNUVEUWGXAUVGYCUUFUAPXQPVNZXRQYBYQTUWHXRQPROZQXQPQRWGUVCUWIQVNUOQXBXC
      WIZUWHYAYPSRUWHXTYOGUWHXSYNAFUWHXRQBDUWJVJVEVRVJVGXDUSXEXFXPUUHXGXHXPUUJX
      GXHXPUUPXGXHXIXPUUEUUDYMUKOUURXPYMUUDXPYGYLUVPUVHVAXPUVCUUCUNNUUDUNNUOXPY
      QUUBUVFUVJVAQUUCURUSZXLXPUUDYLYGUWKUVHUVPXJXKVLVJVM $.

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
      mp3an2 syld3an3 subcld ax-icn negcli mulcl sylancr addcld cc0 wne 4cn 4re
      4pos gt0ne0ii divcan2 mp3an23 syl eqtrd ) EUANZAHNZBHNZUBZOABCPZQPOABFPZG
      RZUCUDPZAUJUEZBDPZFPZGRZUCUDPZUFPZSASBDPZFPZGRZUCUDPZASUEZBDPZFPZGRZUCUDP
      ZUFPZQPZUGPZOUKPZQPZXFWDWEXGOQABCDEFGHIJKLMUHUIWDXFTNZXHXFULZWDWNXEWDWHWM
      WDWGWDWGWDWAWFHNWGUMNWAWBWCUNZABEFHIJUOWFEGHILUPUQURUSWDWLWDWLWDWAWKHNZWL
      UMNXKWAWBWCWJHNZXLWAWCXMWBWAWITNWCXMUTWIBDEHIKVAVCVBAWJEFHIJUOVDWKEGHILUP
      UQURUSVEWDSTNZXDTNXETNVFWDWRXCWDWQWDWQWDWAWPHNZWQUMNXKWAWBWCWOHNZXOWAWCXP
      WBWAXNWCXPVFSBDEHIKVAVCVBAWOEFHIJUOVDWPEGHILUPUQURUSWDXBWDXBWDWAXAHNZXBUM
      NXKWAWBWCWTHNZXQWAWCXRWBWAWSTNWCXRSVFVGWSBDEHIKVAVCVBAWTEFHIJUOVDXAEGHILU
      PUQURUSVESXDVHVIVJXIOTNOVKVLXJVMOVNVOVPXFOVQVRVSVT $.

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
        nvmval fveq2d oveq1d oveq2d wceq cc ax-icn nvscl mp3an2 syld3an3 mulm1i
        3adant2 wa oveq1i neg1cn nvsass mp3anr1 mpanr1 syl5reqr oveq12d eqtr4d
        eqtrd ) EUAPZAIPZBIPZUBZABCQABFQHUCRSQZAUDUEZBDQFQZHUCZRSQZUFQZTATBDQZF
        QHUCRSQZATUEZBDQZFQZHUCZRSQZUFQZUGQZUHQZUIUJQVRABGQZHUCZRSQZUFQZTWEAWDG
        QZHUCZRSQZUFQZUGQZUHQZUIUJQABCDEFHIJKLMNUKVQXCWMUIUJVQWQWCXBWLUHVQWPWBV
        RUFVQWOWARSVQWNVTHABDEFGIJKLOULUMUNUOVQXAWKTUGVQWTWJWEUFVQWSWIRSVQWRWHH
        VQWRAVSWDDQZFQZWHVNVOVPWDIPZWRXEUPVNVPXFVOVNTUQPZVPXFURTBDEIJLUSUTVCAWD
        DEFGIJKLOULVAVQXDWGAFVNVPXDWGUPVOVNVPVDWGVSTUGQZBDQZXDXHWFBDTURVBVEVNXG
        VPXIXDUPZURVNVSUQPXGVPXJVFVSTBDEIJLVGVHVIVJVCUOVMUMUNUOUOVKUNVL $.

      $( Lemma for ~ ipval3 .  (Contributed by NM, 1-Feb-2008.)
         (New usage is discouraged.) $)
      ipval2lem5 $p |- ( ( ( U e. NrmCVec /\ A e. X /\ B e. X ) /\ C e. CC ) ->
                 ( ( N ` ( A M ( C S B ) ) ) ^ 2 ) e. RR ) $=
        ( cnv wcel w3a co cc wa cfv cr simpl1 simpl2 nvscl 3expa 3adantl2 nvmcl
        3com23 syl3anc nvcl syl2anc resqcld ) FQRZAJRZBJRZSCUARZUBZACBETZHTZIUC
        ZUTUPVBJRZVCUDRUPUQURUSUEZUTUPUQVAJRZVDVEUPUQURUSUFUPURUSVFUQUPURUSVFUP
        USURVFCBEFJKMUGUKUHUIAVAFHJKPUJULVBFIJKNUMUNUO $.

      $( Lemma for ~ ipval3 .  (Contributed by NM, 1-Feb-2008.)
         (New usage is discouraged.) $)
      ipval2lem6 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                 ( ( N ` ( A M B ) ) ^ 2 ) e. RR ) $=
        ( wcel c1 co c2 cexp cnv w3a cfv cr wceq wa nvsid oveq2d fveq2d 3adant2
        oveq1d cc ax-1cn ipval2lem5 mpan2 eqeltrrd ) EUAPZAIPZBIPZUBZAQBDRZGRZH
        UCZSTRZABGRZHUCZSTRZUDUQUSVDVGUEURUQUSUFZVCVFSTVHVBVEHVHVABAGBDEIJLUGUH
        UIUKUJUTQULPVDUDPUMABQCDEFGHIJKLMNOUNUOUP $.

      $( Four times the inner product value ~ ipval3 , useful for simplifying
         certain proofs.  (Contributed by NM, 1-Feb-2008.)
         (New usage is discouraged.) $)
      4ipval3 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
          ( 4 x. ( A P B ) ) = ( ( ( ( N ` ( A G B ) ) ^ 2 ) -
                 ( ( N ` ( A M B ) ) ^ 2 ) ) +
                 ( _i x. ( ( ( N ` ( A G ( _i S B ) ) ) ^ 2 ) -
                 ( ( N ` ( A M ( _i S B ) ) ) ^ 2 ) ) ) ) ) $=
        ( wcel c4 co ci cc cnv w3a cmul cfv c2 cexp cmin caddc cdiv ipval3 wceq
        oveq2d ipval2lem3 recnd ipval2lem6 subcld ax-icn ipval2lem2 mpan2 mulcl
        ipval2lem5 sylancr addcld cc0 wne 4cn 4re 4pos gt0ne0ii divcan2 mp3an23
        cr syl eqtrd ) EUAPAIPBIPUBZQABCRZUCRQABFRHUDUEUFRZABGRHUDUEUFRZUGRZSAS
        BDRZFRHUDUEUFRZAVTGRHUDUEUFRZUGRZUCRZUHRZQUIRZUCRZWEVOVPWFQUCABCDEFGHIJ
        KLMNOUJULVOWETPZWGWEUKZVOVSWDVOVQVRVOVQABCDEFHIJKLMNUMUNVOVRABCDEFGHIJK
        LMNOUOUNUPVOSTPZWCTPWDTPUQVOWAWBVOWAVOWJWAVLPUQABSCDEFHIJKLMNURUSUNVOWB
        VOWJWBVLPUQABSCDEFGHIJKLMNOVAUSUNUPSWCUTVBVCWHQTPQVDVEWIVFQVGVHVIWEQVJV
        KVMVN $.
    $}
  $}

  ${
    $d k n p w x y z G $.  $d k n p w x y z N $.  $d k n p w x y z S $.
    $d k n p w x y z U $.  $d k x y z A $.  $d k x y z B $.  $d x y z X $.
    ipid.1 $e |- X = ( BaseSet ` U ) $.
    ipid.6 $e |- N = ( normCV ` U ) $.
    ipid.7 $e |- P = ( .iOLD ` U ) $.
    $( The inner product of a vector with itself is the square of the vector's
       norm.  Equation I4 of [Ponnusamy] p. 362.  (Contributed by NM,
       1-Feb-2007.)  (New usage is discouraged.) $)
    ipidsq $p |- ( ( U e. NrmCVec /\ A e. X ) ->
                ( A P A ) = ( ( N ` A ) ^ 2 ) ) $=
      ( wcel co cfv c2 cexp c1 ci cmul caddc wceq cc0 cc cnv wa cpv cneg cns c4
      cmin cdiv eqid ipval2 3anidm23 nv2 fveq2d cr cle wbr ltleii pm3.2i nvsge0
      2re 0re 2pos mp3an2 eqtrd oveq1d nvcl cn0 2cn 2nn0 mulexp mp3an13 syl sq2
      recnd oveq1i syl6eq cn0v nvrinv nvz0 adantr sq0id oveq12d 4cn sqcld mulcl
      sylancr subid1d cabs csqr renegcli absreim ax-icn ax-1cn mulneg2i mulid1i
      1re mp2an negeqi eqtri oveq2i fveq2i sqneg 3eqtr3i 3eqtr2i negcli 3eqtr4a
      ax-mp addcli nvs nvdir mp3anr1 mpanr1 nvsid 3eqtr3d oveq2d w3a ipval2lem4
      mpan2 subidd mul01i addid1d wne 4re 4pos gt0ne0ii divcan3 mp3an23 3eqtr2d
      eqtr2d ) CUAIZAEIZUBZAABJZAACUCKZJZDKZLMJZANUDZACUEKZJYNJZDKZLMJZUGJZOAOA
      YSJZYNJZDKZLMJZAOUDZAYSJZYNJZDKZLMJZUGJZPJZQJZUFUHJZUFADKZLMJZPJZUFUHJZUU
      RYJYKYMUUPRAABYSCYNDEFYNUIZYSUIZGHUJUKYLUUSUUOUFUHYLUUOUUSSQJUUSYLUUCUUSU
      UNSQYLUUCUUSSUGJUUSYLYQUUSUUBSUGYLYQLUUQPJZLMJZUUSYLYPUVCLMYLYPLAYSJZDKZU
      VCYLYOUVEDAYSCYNEFUVAUVBULUMYJLUNIZSLUOUPZUBYKUVFUVCRUVGUVHUTSLVAUTVBUQUR
      LAYSCDEFUVBGUSVCVDVEYLUVDLLMJZUURPJZUUSYLUUQTIZUVDUVJRZYLUUQACDEFGVFVNZLT
      IUVKLVGIUVLVHVILUUQLVJVKVLUVIUFUURPVMVOVPVDYLUUAYLUUACVQKZDKZSYLYTUVNDAYS
      CYNEUVNFUVAUVBUVNUIZVRUMYJUVOSRYKCDUVNUVPGVSVTVDWAWBYLUUSYLUFTIZUURTIZUUS
      TIWCYLUUQUVMWDZUFUURWEWFZWGVDYLUUNOSPJSYLUUMSOPYLUUMUUGUUGUGJSYLUULUUGUUG
      UGYLUUKUUFLMYLNUUHQJZAYSJZDKZNOQJZAYSJZDKZUUKUUFYLUWAWHKZUUQPJZUWDWHKZUUQ
      PJZUWCUWFUWGUWIUUQPUWGNLMJZUWKQJZWIKZNONPJZQJZWHKZUWINOYRPJZQJZWHKZUWKYRL
      MJZQJZWIKZUWGUWMNUNIZYRUNIUWSUXBRWPNWPWJNYRWKWQUWRUWAWHUWQUUHNQUWQUWNUDUU
      HONWLWMWNUWNOOWLWOZWRWSWTXAUXAUWLWIUWTUWKUWKQNTIZUWTUWKRWMNXBXGWTXAXCUXCU
      XCUWPUWMRWPWPNNWKWQUWOUWDWHUWNONQUXDWTXAXDVOYJUWATIYKUWCUWHRNUUHWMOWLXEZX
      HUWAAYSCDEFUVBGXIVCYJUWDTIYKUWFUWJRNOWMWLXHUWDAYSCDEFUVBGXIVCXFYLUWBUUJDY
      LUWBNAYSJZUUIYNJZUUJYJUUHTIZYKUWBUXHRZUXFYJUXEUXIYKUXJWMNUUHAYSCYNEFUVAUV
      BXJXKXLYLUXGAUUIYNAYSCEFUVBXMZVEVDUMYLUWEUUEDYLUWEUXGUUDYNJZUUEYJOTIZYKUW
      EUXLRZWLYJUXEUXMYKUXNWMNOAYSCYNEFUVAUVBXJXKXLYLUXGAUUDYNUXKVEVDUMXNVEXOYL
      UUGYJYKUUGTIZYJYKYKXPUXMUXOWLAAOBYSCYNDEFUVAUVBGHXQXRUKXSVDXOOWLXTVPWBYLU
      USUVTYAYIVEYLUVRUUTUURRZUVSUVRUVQUFSYBUXPWCUFYCYDYEUURUFYFYGVLYH $.

    $( Norm expressed in terms of inner product.  (Contributed by NM,
       11-Sep-2007.)  (New usage is discouraged.) $)
    ipnm $p |- ( ( U e. NrmCVec /\ A e. X ) ->
                ( N ` A ) = ( sqr ` ( A P A ) ) ) $=
      ( cnv wcel wa co csqr cfv c2 cexp ipidsq fveq2d nvcl nvge0 sqrsqd eqtr2d
      ) CIJAEJKZAABLZMNADNZOPLZMNUEUCUDUFMABCDEFGHQRUCUEACDEFGSACDEFGTUAUB $.
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
      wa expcl sylan2 mulcld fsumcl cc0 wne 4cn 4re 4pos gt0ne0ii divcl mp3an23
      syl eqeltrd ) DIJAEJBEJKZABCLMNOLZPHUFZQLZAVPBDUARZLDUBRZLDUCRZRUGQLZUDLZ
      HUEZNUHLZSABCVQDHVRVSEFVRTZVQTZVSTZGUIVMWBSJZWCSJZVMVNWAHVMMNUJVMVOVNJZUR
      VPVTWIVPSJZVMWIPSJVOUKJWJULWIVOVONUMUNPVOUSUOZUPWIVMWJVTSJWKABVPCVQDVRVSE
      FWDWEWFGUQUTVAVBWGNSJNVCVDWHVENVFVGVHWBNVIVJVKVL $.

    $( Mapping for the inner product operation.  (Contributed by NM,
       28-Jan-2008.)  (Revised by Mario Carneiro, 16-Nov-2013.)
       (New usage is discouraged.) $)
    ipf $p |- ( U e. NrmCVec -> P : ( X X. X ) --> CC ) $=
      ( vx vy vk cnv wcel cxp cc wf c4 co cv cexp cfv wral eqid c1 cfz ci cnmcv
      cns cpv c2 cmul csu cmpt2 w3a ipval dipcl eqeltrrd 3expib ralrimivv fmpt2
      cdiv sylib dipfval feq1d mpbird ) BIJZCCKZLAMVDLFGCCUANUBOUCHPQOZFPZVEGPZ
      BUERZOBUFRZOBUDRZRUGQOUHOHUINUROZUJZMZVCVKLJZGCSFCSVMVCVNFGCCVCVFCJZVGCJZ
      VNVCVOVPUKVFVGAOVKLVFVGAVHBHVIVJCDVITZVHTZVJTZEULVFVGABCDEUMUNUOUPFGCCVKL
      VLVLTUQUSVCVDLAVLFGAVHBHVIVJCDVQVRVSEUTVAVB $.

    $( The complex conjugate of an inner product reverses its arguments.
       Equation I1 of [Ponnusamy] p. 362.  (Contributed by NM, 1-Feb-2007.)
       (New usage is discouraged.) $)
    dipcj $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
               ( * ` ( A P B ) ) = ( B P A ) ) $=
      ( wcel co cfv c2 cexp cmin ci c4 cdiv wceq cc mpan2 cr cnv w3a ccj cpv c1
      cnmcv cneg cns cmul caddc eqid ipval2 fveq2d 3com23 ipval2lem3 ipval2lem4
      recnd neg1cn subcld ax-icn negcli sylancr addcld cc0 wne 4cn 4re gt0ne0ii
      mulcl 4pos cjdiv mp3an23 syl cjre ax-mp oveq2i ipval2lem2 resubcld cjreim
      syl2anc submul2 mp3an2 nvcom oveq1d nvdif oveq12d negsubdi2d eqcomd eqtrd
      nvpi oveq2d 3eqtrd syl5eq eqtr4d ) DUAHZAEHZBEHZUBZABCIZUCJABDUDJZIZDUFJZ
      JZKLIZAUEUGZBDUHJZIWTIXBJZKLIZMIZNANBXFIWTIXBJZKLIZANUGZBXFIWTIXBJZKLIZMI
      ZUIIZUJIZOPIZUCJZBACIZWRWSXRUCABCXFDWTXBEFWTUKZXFUKZXBUKZGULUMWRXTBAWTIZX
      BJZKLIZBXEAXFIWTIXBJZKLIZMIZNBNAXFIWTIXBJZKLIZBXLAXFIWTIXBJZKLIZMIZUIIZUJ
      IZOPIZXSWOWQWPXTYQQBACXFDWTXBEFYAYBYCGULUNWRXSXQUCJZOUCJZPIZYQWRXQRHZXSYT
      QZWRXIXPWRXDXHWRXDABCXFDWTXBEFYAYBYCGUOZUQWRXERHZXHRHURABXECXFDWTXBEFYAYB
      YCGUPSUSZWRNRHZXORHZXPRHUTWRXKXNWRUUFXKRHUTABNCXFDWTXBEFYAYBYCGUPSZWRXLRH
      ZXNRHNUTVAZABXLCXFDWTXBEFYAYBYCGUPSZUSZNXOVIVBVCUUAORHOVDVEUUBVFOVGVJVHXQ
      OVKVLVMWRYTYROPIYQYSOYRPOTHYSOQVGOVNVOVPWRYRYPOPWRYRXIXPMIZXINXOUGZUIIZUJ
      IZYPWRXITHXOTHYRUUMQWRXDXHUUCWRUUDXHTHURABXECXFDWTXBEFYAYBYCGVQSVRWRXKXNW
      RUUFXKTHUTABNCXFDWTXBEFYAYBYCGVQSWRUUIXNTHUUJABXLCXFDWTXBEFYAYBYCGVQSVRXI
      XOVSVTWRXIRHZUUGUUMUUPQZUUEUULUUQUUFUUGUURUTXINXOWAWBVTWRXIYIUUOYOUJWRXDY
      FXHYHMWRXCYEKLWRXAYDXBABDWTEFYAWCUMWDWRXGYGKLABXFDWTXBEFYAYBYCWEWDWFWRUUN
      YNNUIWRUUNXNXKMIYNWRXKXNUUHUUKWGWRXNYKXKYMMWRXMYJKLWRYJXMWOWQWPYJXMQBAXFD
      WTXBEFYAYBYCWJUNWHWDWRXJYLKLABXFDWTXBEFYAYBYCWJWDWFWIWKWFWLWDWMWIWNWN $.

    $( An inner product times its conjugate.  (Contributed by NM,
       23-Nov-2007.)  (New usage is discouraged.) $)
    ipipcj $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                ( ( A P B ) x. ( B P A ) ) = ( ( abs ` ( A P B ) ) ^ 2 ) ) $=
      ( cnv wcel w3a co cabs cfv c2 cexp ccj cmul dipcl absvalsqd dipcj oveq2d
      eqtr2d ) DHIAEIBEIJZABCKZLMNOKUDUDPMZQKUDBACKZQKUCUDABCDEFGRSUCUEUFUDQABC
      DEFGTUAUB $.

    $( Orthogonality (meaning inner product is 0) is commutative.  (Contributed
       by NM, 17-Apr-2008.)  (New usage is discouraged.) $)
    diporthcom $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X )
              -> ( ( A P B ) = 0 <-> ( B P A ) = 0 ) ) $=
      ( cnv wcel co cc0 wceq ccj cfv fveq2 cj0 syl6eq dipcj eqeq1d syl5ib w3a
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
      fveq2d oveq1d ipval2lem3 recnd subidd ax-icn negcli eqtr4d w3a ipval2lem4
      eqtrd oveq12d mul01i oveq2i 00id eqtri syl6eq 4cn 4re 4pos gt0ne0ii div0i
      cr ) CUAIZADIZUEZAEBJZAECUBKZJZCUCKZKZLMJZAUFUDZECUGKZJZWFJZWHKZLMJZNJZOA
      OEWLJZWFJZWHKZLMJZAOUDZEWLJZWFJZWHKZLMJZNJZUHJZPJZQUIJZRWBWCEDIZWEXJSWBXK
      WCCDEFGUJUKZAEBWLCWFWHDFWFULZWLULZWHULZHUMUNWDXJRQUIJRWDXIRQUIWDXIRORUHJZ
      PJZRWDWQRXHXPPWDWQWJWJNJRWDWPWJWJNWDWOWILMWDWNWGWHWDWMEAWFWBWMESZWCWBWKUO
      IXRUPWKWLCEXNGUQURUKTUSUTTWDWJWDWJWBWCXKWJWAIXLAEBWLCWFWHDFXMXNXOHVAUNVBV
      CVIWDXGROUHWDXGXAXANJRWDXFXAXANWDXEWTLMWDXDWSWHWDXCWRAWFWBXCWRSWCWBXCEWRW
      BXBUOIXCESOVDVEXBWLCEXNGUQURWBOUOIZWRESVDOWLCEXNGUQURVFUKTUSUTTWDXAWBWCXK
      XAUOIZXLWBWCXKVGXSXTVDAEOBWLCWFWHDFXMXNXOHVHURUNVCVITVJXQRRPJRXPRRPOVDVKV
      LVMVNVOUTQVPQVQVRVSVTVOVI $.

    $( Inner product with a zero first argument.  Part of proof of Theorem 6.44
       of [Ponnusamy] p. 361.  (Contributed by NM, 5-Feb-2007.)
       (New usage is discouraged.) $)
    dip0l $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( Z P A ) = 0 ) $=
      ( cnv wcel wa co ccj cfv cc0 wceq nvzcl adantr dipcj mpd3an3 dip0r fveq2d
      cj0 syl6eq eqtr3d ) CIJZADJZKZAEBLZMNZEABLZOUFUGEDJZUJUKPUFULUGCDEFGQRAEB
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
      cnmcv c2 cmul csu cdiv ctx eqid dipfval cxmt ctopon imsxmet mopntopon syl
      cmpt2 fzfid wa adantr cnfldtopon cn0 ax-icn cn elfznn adantl nnnn0d expcl
      sylancr cnmpt2c cnmpt1st cnmpt2nd smcn cnmpt22f vacn nmcnc cnmpt21f oveq1
      cmpt sqcn cnmpt21 mulcn fsum2cn cc0 wne 4cn nnne0i divccn mp2an eqeltrd
      4nn ) CUANZBJKCUBOZWSUCPUDQZUELUFZUGQZJUFZXBKUFZCUHOZQZCUIOZQZCUJOZOZUKUG
      QZULQZLUMZPUNQZVCDDUOQZERQJKBXECLXGXIWSWSUPZXGUPZXEUPZXIUPZFUQWRJKMXMMUFZ
      PUNQZXNDDEEWSWSSWRAWSURONDWSUSONZACWSXPGUTADWSHVAVBZYCWRJKWTXLLDEDWSWSIYC
      WRUCPVDYCWRXAWTNZVEZJKXBXKULDDEEEWSWSWRYBYDYCVFZYFYEJKXBDDEWSWSSYFYFESUSO
      NZYEEIVGZTZYEUESNXAVHNXBSNVIYEXAYDXAVJNWRXAPVKVLVMUEXAVNVOVPZYEJKMXJXTUKU
      GQZXKDDEEWSWSSYFYFYEJKXHXIDDDEWSWSYFYFYEJKXCXFXGDDDDDWSWSYFYFYEJKDDWSWSYF
      YFVQYEJKXBXDXEDDEDDWSWSYFYFYJYEJKDDWSWSYFYFVRWRXEEDUOQDRQNYDAXECDEGHXRIVS
      VFVTWRXGXODRQNYDACXGDGHXQWAVFVTWRXIDERQNYDACDEXIXSGHIWBVFWCYIMSYKWEEERQZN
      YEMEIWFTXTXJUKUGWDWGULEEUOQERQNYEEIWHTVTWIYGWRYHTMSYAWEYLNZWRPSNPWJWKYMWL
      PWQWMMPEIWNWOTXTXMPUNWDWGWP $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      Subspaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c SubSp $.

  $( Extend class notation with the class of all subspaces of complex normed
     vector spaces. $)
  css $a class SubSp $.

  ${
    $d u w $.
    $( Define the class of all subspaces of complex normed vector spaces.
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
      ( vu cnv wcel cfv cpv wss cns cnmcv fveq2 fvex css cv crab syl6eqr sseq2d
      w3a wceq 3anbi123d rabbidv df-ssp cpw cxp cvv eqeltri pwex xpex rabss cop
      wi wa elpw opelxpi syl2anbr biimpri syl2an 3impa eqid nvop eleq1d syl5ibr
      mprgbir ssexi fvmpt syl5eq ) CLMECUANAUBZONZDPZVOQNZBPZVORNZFPZUFZALUCZJK
      CVPKUBZONZPZVRWDQNZPZVTWDRNZPZUFZALUCWCLUAWDCUGZWKWBALWLWFVQWHVSWJWAWLWED
      VPWLWECONZDWDCOSGUDUEWLWGBVRWLWGCQNZBWDCQSHUDUEWLWIFVTWLWICRNZFWDCRSIUDUE
      UHUIAKUJWCDUKZBUKZULZFUKZULZWRWSWPWQDDWMUMGCOTUNUOBBWNUMHCQTUNUOUPFFWOUMI
      CRTUNUOUPWCWTPWBVOWTMZUSALWBALWTUQWBXAVOLMZVPVRURZVTURZWTMZVQVSWAXEVQVSUT
      XCWRMZVTWSMZXEWAVQVPWPMVRWQMXFVSVPDVOOTVAVRBVOQTVAVPVRWPWQVBVCXGWAVTFVORT
      VAVDXCVTWRWSVBVEVFXBVOXDWTVRVOVPVTVPVGVRVGVTVGVHVIVJVKVLVMVN $.
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
      ( vw cnv cfv wss wcel cv cpv cns cnmcv crab wa sspval eleq2d wceq syl6eqr
      w3a fveq2 sseq1d 3anbi123d elrab syl6bb ) CRUAZIFUAIQUBZUCSZETZUSUDSZBTZU
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
      wfun wf nvgf ffun funres adantr sspnv fnresdm cnmcv isssp simplbda simp1d
      ffn cns ssres eqsstr3d oprssov sylan eqcomd ralrimivva jctil sspba xpss12
      3jca wb syl2anc fnssres eqfnov mpbird ) AUAMZEDMZNZBCFFUBZUCZOZWAWAOZKUDZ
      LUDZBUEZWEWFWBUEZOZLFUFKFUFZNZVTWJWDVTWIKLFFVTWEFMWFFMNZNWHWGVTWBUIZBWAPZ
      BWBQZUGWLWHWGOVTWMWNWOVRWMVSVRCUIZWMVRAUHRZWQUBZWQCUJZWPACWQWQSZHUKZWRWQC
      ULTWACUMTUNVTWAFBUJZWNVTEUAMZXBADEJUOEBFGIUKTWAFBVATZVTBBWAUCZWBVTWNXEBOX
      DWABUPTVTBCQZXEWBQVTXFEVBRZAVBRZQZEUQRZAUQRZQZVRVSXCXFXIXLUGXGXHABCDXJXKE
      HIXHSXGSXKSXJSJURUSUTBCWAVCTVDVLWEWFFFWBBVEVFVGVHWASVIVTWNWBWAPZWCWKVMXDV
      TCWRPZWAWRQZXMVRXNVSVRWSXNXAWRWQCVATUNVTFWQQZXPXOADEWQFWTGJVJZXQFWQFWQVKV
      NWRWACVOVNKLFFFFBWBVPVNVQ $.

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
      ( vx vy wcel wa cc wceq wss cfv eqid syl cnv cxp cres cv co wral wfun wfn
      w3a cba wf nvsf ffun funres adantr sspnv ffn fnresdm cnmcv isssp simplbda
      cpv simp2d ssres eqsstr3d 3jca oprssov sylan eqcomd ralrimivva jctil ssid
      wb sspba xpss12 sylancr fnssres syl2anc eqfnov mpbird ) CUAMZEDMZNZABOFUB
      ZUCZPZWDWDPZKUDZLUDZAUEZWHWIWEUEZPZLFUFKOUFZNZWCWMWGWCWLKLOFWCWHOMWIFMNZN
      WKWJWCWEUGZAWDUHZAWEQZUIWOWKWJPWCWPWQWRWAWPWBWABUGZWPWAOCUJRZUBZWTBUKZWSB
      CWTWTSZHULZXAWTBUMTWDBUNTUOWCWDFAUKZWQWCEUAMZXECDEJUPAEFGIULTWDFAUQTZWCAA
      WDUCZWEWCWQXHAPXGWDAURTWCABQZXHWEQWCEVBRZCVBRZQZXIEUSRZCUSRZQZWAWBXFXLXIX
      OUIABCXJXKDXMXNEXKSXJSHIXNSXMSJUTVAVCABWDVDTVEVFWHWIOFWEAVGVHVIVJWDSVKWCW
      QWEWDUHZWFWNVMXGWCBXAUHZWDXAQZXPWAXQWBWAXBXQXDXAWTBUQTUOWCOOQFWTQXROVLCDE
      WTFXCGJVNOOFWTVOVPXAWDBVQVRKLOFOFAWEVSVRVT $.

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
      eqid jctil wb sspnv ffn 3syl cba cfv wss syl adantr sspba syl2anc fnssres
      wf xpss12 eqfnov mpbird ) EUAPZIHPZQZFGJJUBZUCZRZVKVKRZAUDZBUDZFSZVOVPVLS
      ZRZBJUEAJUEZQZVJVTVNVJVSABJJVJVOJPVPJPQZQVQVOVPGSZVRMWBVRWCRVJVOVPJJGUFUG
      UHUIVKUJUKVJFVKTZVLVKTZVMWAULVJIUAPVKCFVDWDEHILUMNVKCFUNUOVJGEUPUQZWFUBZT
      ZVKWGURZWEVHWHVIVHWGDGVDWHOWGDGUNUSUTVJJWFURZWJWIEHIWFJWFUJKLVAZWKJWFJWFV
      EVBWGVKGVCVBABJJJJFVLVFVBVG $.
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
    $d x y F $.  $d x y G $.  $d x y H $.  $d x y U $.  $d x y W $.
    $d x y Y $.
    sspz.z $e |- Z = ( 0vec ` U ) $.
    sspz.q $e |- Q = ( 0vec ` W ) $.
    sspz.h $e |- H = ( SubSp ` U ) $.
    $( The zero vector of a subspace is the same as the parent's.  (Contributed
       by NM, 28-Jan-2008.)  (New usage is discouraged.) $)
    sspz $p |- ( ( U e. NrmCVec /\ W e. H ) -> Q = Z ) $=
      ( cnv wcel wa cnsb cfv co cba wceq sspnv eqid syl nvmid nvzcl jca sspmval
      mpdan syl2anc sspba sseldd syldan 3eqtr3d ) BIJZDCJZKZAADLMZNZAABLMZNZAEU
      LADOMZJZURKZUNUPPULDIJZUSBCDHQZUTURURDUQAUQRZGUAZVCUBSAABCUMUODUQVBUORZUM
      RZHUCUDULUTURUNAPVAULUTURVAVCSZADUMUQAVBVEGTUEUJUKABOMZJUPEPULUQVGABCDVGU
      QVGRZVBHUFVFUGABUOVGEVHVDFTUHUI $.
  $}

  ${
    $d x H $.  $d x M $.  $d x N $.  $d x U $.  $d x W $.  $d x Y $.
    sspn.y $e |- Y = ( BaseSet ` W ) $.
    sspn.n $e |- N = ( normCV ` U ) $.
    sspn.m $e |- M = ( normCV ` W ) $.
    sspn.h $e |- H = ( SubSp ` U ) $.
    $( The norm on a subspace is a restriction of the norm on the parent
       space.  (Contributed by NM, 28-Jan-2008.)
       (New usage is discouraged.) $)
    sspn $p |- ( ( U e. NrmCVec /\ W e. H ) -> M = ( N |` Y ) ) $=
      ( vx cnv wcel cr wfn syl cfv wss eqid wceq wa wf sspnv nvf ffn cba adantr
      cres fnssres syl2anc cv wfun cdm ffun funres ad2antrr fnresdm cpv cns w3a
      sspba isssp simplbda simp3d ssres eqsstr3d eleq2d biimpar funssfv syl3anc
      fdm sylan eqcomd eqfnfvd ) ALMZEBMZUAZKFCDFUHZVQFNCUBZCFOZVQELMZVSABEJUCZ
      ECFGIUDZPFNCUEPZVQDAUFQZOZFWERVRFOVOWFVPVOWENDUBZWFADWEWESZHUDZWENDUEPUGA
      BEWEFWHGJVAWEFDUIUJVQKUKZFMZUAZWJVRQZWJCQZWLVRULZCVRRZWJCUMZMZWMWNTVOWOVP
      WKVODULZWOVOWGWSWIWENDUNPFDUOPUPVQWPWKVQCCFUHZVRVQVTWTCTWDFCUQPVQCDRZWTVR
      RVQEURQZAURQZRZEUSQZAUSQZRZXAVOVPWAXDXGXAUTXEXFAXBXCBCDEXCSXBSXFSXESHIJVB
      VCVDCDFVEPVFUGVQWAWKWRWBWAWRWKWAWQFWJWAVSWQFTWCFNCVKPVGVHVLWJVRCVIVJVMVN
      $.

    $( The norm on a subspace in terms of the norm on the parent space.
       (Contributed by NM, 28-Jan-2008.)  (New usage is discouraged.) $)
    sspnval $p |- ( ( U e. NrmCVec /\ W e. H /\ A e. Y ) ->
                    ( M ` A ) = ( N ` A ) ) $=
      ( cnv wcel cfv wceq wa cres sspn fveq1d fvres sylan9eq 3impa ) BLMZFCMZAG
      MZADNZAENZOUCUDPZUEUFAEGQZNUGUHADUIBCDEFGHIJKRSAGETUAUB $.
  $}

  ${
    $d k A $.  $d k B $.  $d k x y H $.  $d x y P $.  $d x y Q $.
    $d k x y U $.  $d k x y W $.  $d k x y Y $.
    sspi.y $e |- Y = ( BaseSet ` W ) $.
    sspi.p $e |- P = ( .iOLD ` U ) $.
    sspi.q $e |- Q = ( .iOLD ` W ) $.
    sspi.h $e |- H = ( SubSp ` U ) $.
    $( The inner product on a subspace in terms of the inner product on the
       parent space.  (Contributed by NM, 28-Jan-2008.)
       (New usage is discouraged.) $)
    sspival $p |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. Y /\ B e. Y ) ) ->
                    ( A Q B ) = ( A P B ) ) $=
      ( vk wcel wa c4 co cfv wceq eqid cnv c1 cfz ci cv cexp cns cpv cnmcv cmul
      c2 csu cdiv cn0 ax-icn elfznn nnnn0d expcl sylancr anim1i anim2i anass1rs
      cc sspnv nvscl 3expib anim2d imp nvgcl 3expb syldan sylan sspnval sspgval
      3expa wi syl sspsval adantrl oveq2d fveq2d sylan2 anassrs oveq1d sumeq2dv
      eqtrd ipval cba sspba sseld anim12d adantlr 3eqtr4d ) EUANZGFNZOZAHNZBHNZ
      OZOZUBPUCQZUDMUEZUFQZAXCBGUGRZQZGUHRZQZGUIRZRZUKUFQZUJQZMULZPUMQZXAXCAXCB
      EUGRZQZEUHRZQZEUIRZRZUKUFQZUJQZMULZPUMQZABDQZABCQZWTXLYBPUMWTXAXKYAMWTXBX
      ANZOZXJXTXCUJYGXIXSUKUFWPWSYFXIXSSZWSYFOWPWQXCVCNZWROZOZYHWQYFWRYKYFWROYJ
      WQYFYIWRYFUDVCNXBUNNYIUOYFXBXBPUPUQUDXBURUSUTVAVBWPYKOZXIXGXRRZXSWPYKXGHN
      ZXIYMSZWPGUANZYKYNEFGLVDZYPYKWQXEHNZOZYNYPYKYSYPYJYRWQYPYIWRYRXCBXDGHIXDT
      ZVEVFZVGVHYPWQYRYNAXEGXFHIXFTZVIVJVKVLWNWOYNYOXGEFXHXRGHIXRTZXHTZLVMVOVKY
      LXGXQXRYLXGAXEXPQZXQWPYKYSXGUUESWPYKYSWPYJYRWQWPYPYJYRVPYQUUAVQVGVHAXEEXF
      XPFGHIXPTZUUBLVNVKYLXEXOAXPWPYJXEXOSWQXCBXDXNEFGHIXNTZYTLVRVSVTWFWAWFWBWC
      WDVTWEWDWPYPWSYDXMSZYQYPWQWRUUHABDXDGMXFXHHIUUBYTUUDKWGVJVLWPWSAEWHRZNZBU
      UINZOZYEYCSZWPWSUULWPWQUUJWRUUKWPHUUIAEFGUUIHUUITZILWIZWJWPHUUIBUUOWJWKVH
      WNUULUUMWOWNUUJUUKUUMABCXNEMXPXRUUIUUNUUFUUGUUCJWGVJWLVKWM $.

    $( The inner product on a subspace is a restriction of the inner product on
       the parent space.  (Contributed by NM, 28-Jan-2008.)
       (New usage is discouraged.) $)
    sspi $p |- ( ( U e. NrmCVec /\ W e. H ) -> Q = ( P |` ( Y X. Y ) ) ) $=
      ( vx vy cc cv sspival ipf cba cfv eqid sspmlem ) KLMMCBADEFGJKNLNABCDEFGH
      IJOBEFGIPACCQRZUASHPT $.
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

  $( Define the class of all complete subspaces of a complex normed vector
     space. $)
  $(
  $c CSubSp $.
  ccs $a class SubSp $.
  df-cs $a |- CSubSp = { <. u , s >. | ( u e. NrmCVec /\ s =
       ( ( SubSp ` u ) |^| CBan ) ) } $.
  $)


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
       spaces.  In the literature, an operator may be a partial function, i.e.
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

    $( Define the norm of an operator between two normed complex vector
       spaces.  This definition produces an operator norm function for each
       pair of vector spaces ` <. u , w >. ` .  Based on definition of linear
       operator norm in [AkhiezerGlazman] p. 39, although we define it for all
       operators for convenience.  It isn't necessarily meaningful for
       nonlinear operators, since it doesn't take into account operator values
       at vectors with norm greater than 1.  See Equation 2 of [Kreyszig] p. 92
       for a definition that does (although it ignores the value at the zero
       vector).  However, operator norms are rarely if ever used for nonlinear
       operators.  (Contributed by NM, 6-Nov-2007.)
       (New usage is discouraged.) $)
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
    $d a o s t u w x y $.
    $( Define the adjoint of an operator (if it exists).  The domain of
       ` U adj W ` is the set of all operators from ` U ` to ` W ` that have an
       adjoint.  Definition 3.9-1 of [Kreyszig] p. 196, although we don't
       require that ` U ` and ` W ` be Hilbert spaces nor that the operators be
       linear.  Although we define it for any normed vector space for
       convenience, the definition is meaningful only for inner product
       spaces.  (Contributed by NM, 25-Jan-2008.)
       (New usage is discouraged.) $)
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
      ( vu vw cnv wcel wa clno co cv cfv wceq wral cc cmap crab cns cpv syl6eqr
      cba fveq2 oveq2d oveqd oveq123d fveq2d eqeq1d raleqbidv ralbidv rabeqbidv
      eqidd oveq1d eqeq2d 2ralbidv df-lno ovex rabex ovmpt2 syl5eq ) GUCUDKUCUD
      UEJGKUFUGAUHZBUHZEUGZCUHZHUGZDUHZUIZVQVRWBUIZFUGZVTWBUIZIUGZUJZCLUKBLUKZA
      ULUKZDMLUMUGZUNZTUAUBGKUCUCVQVRUAUHZUOUIZUGZVTWMUPUIZUGZWBUIZVQWDUBUHZUOU
      IZUGZWFWSUPUIZUGZUJZCWMURUIZUKZBXEUKZAULUKZDWSURUIZXEUMUGZUNWLUFWCXCUJZCL
      UKZBLUKZAULUKZDXILUMUGZUNWMGUJZXHXNDXJXOXPXELXIUMXPXEGURUILWMGURUSNUQZUTX
      PXGXMAULXPXFXLBXELXQXPXDXKCXELXQXPWRWCXCXPWQWAWBXPWOVSVTVTWPHXPWPGUPUIHWM
      GUPUSPUQXPWNEVQVRXPWNGUOUIEWMGUOUSRUQVAXPVTVHVBVCVDVEVEVFVGWSKUJZXNWJDXOW
      KXRXIMLUMXRXIKURUIMWSKURUSOUQVIXRXMWIAULXRXKWHBCLLXRXCWGWCXRXAWEWFWFXBIXR
      XBKUPUIIWSKUPUSQUQXRWTFVQWDXRWTKUOUIFWSKUOUSSUQVAXRWFVHVBVJVKVFVGABCUBUAD
      VLWJDWKMLUMVMVNVOVP $.

    $( The predicate "is a linear operator."  (Contributed by NM, 4-Dec-2007.)
       (Revised by Mario Carneiro, 16-Nov-2013.)
       (New usage is discouraged.) $)
    islno $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> ( T e. L <->
      ( T : X --> Y /\ A. x e. CC A. y e. X A. z e. X
      ( T ` ( ( x R y ) G z ) ) = ( ( x S ( T ` y ) ) H ( T ` z ) ) ) ) ) $=
      ( vw cnv wcel wa cv co cfv wceq wral cc cmap crab wf lnoval eleq2d oveq2d
      fveq1 oveq12d eqeq12d 2ralbidv ralbidv elrab cba cvv eqeltri elmap anbi1i
      fvex bitri syl6bb ) GUBUCKUBUCUDZFJUCFAUEZBUEZDUFCUEZHUFZUAUEZUGZVLVMVPUG
      ZEUFZVNVPUGZIUFZUHZCLUIBLUIZAUJUIZUAMLUKUFZULZUCZLMFUMZVOFUGZVLVMFUGZEUFZ
      VNFUGZIUFZUHZCLUIBLUIZAUJUIZUDZVKJWFFABCUADEGHIJKLMNOPQRSTUNUOWGFWEUCZWPU
      DWQWDWPUAFWEVPFUHZWCWOAUJWSWBWNBCLLWSVQWIWAWMVOVPFUQWSVSWKVTWLIWSVRWJVLEV
      MVPFUQUPVNVPFUQURUSUTVAVBWRWHWPMLFMKVCUGVDOKVCVHVELGVCUGVDNGVCVHVEVFVGVIV
      J $.

    $d t u w A $.  $d t w B $.  $d t C $.
    $( Basic linearity property of a linear operator.  (Contributed by NM,
       4-Dec-2007.)  (Revised by Mario Carneiro, 16-Nov-2013.)
       (New usage is discouraged.) $)
    lnolin $p |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) /\
       ( A e. CC /\ B e. X /\ C e. X ) ) ->
      ( T ` ( ( A R B ) G C ) ) = ( ( A S ( T ` B ) ) H ( T ` C ) ) ) $=
      ( vu vw vt cnv wcel w3a cv co cfv wceq wral cc wf wa islno biimp3a simprd
      oveq1 oveq1d fveq2d eqeq12d oveq2 fveq2 oveq2d rspc3v mpan9 ) GUDUEZKUDUE
      ZFJUEZUFZUAUGZUBUGZDUHZUCUGZHUHZFUIZVKVLFUIZEUHZVNFUIZIUHZUJZUCLUKUBLUKUA
      ULUKZAULUEBLUECLUEUFABDUHZCHUHZFUIZABFUIZEUHZCFUIZIUHZUJZVJLMFUMZWBVGVHVI
      WKWBUNUAUBUCDEFGHIJKLMNOPQRSTUOUPUQWAWJAVLDUHZVNHUHZFUIZAVQEUHZVSIUHZUJWC
      VNHUHZFUIZWGVSIUHZUJUAUBUCABCULLLVKAUJZVPWNVTWPWTVOWMFWTVMWLVNHVKAVLDURUS
      UTWTVRWOVSIVKAVQEURUSVAVLBUJZWNWRWPWSXAWMWQFXAWLWCVNHVLBADVBUSUTXAWOWGVSI
      XAVQWFAEVLBFVCVDUSVAVNCUJZWRWEWSWIXBWQWDFVNCWCHVBUTXBVSWHWGIVNCFVCVDVAVEV
      F $.
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
      cc 3jca lnolin mpdan nvlinv fveq2d simp2 lnof ffvelrnd syl2anc 3eqtr3d )
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
      fco mp2an w3a wa nvscl mp3an1 nvgcl sylan 3impa fvco3 sylancr id ffvelrni
      lnof 3pm3.2i lnolin mpan syl3an fveq2d simp2 oveq2d simp3 3eqtr4rd eqtr4d
      oveq12d rgen3 wb islno mpbir2an ) BAUDZFQZCUERZHUERZWDUFZUAUGZUBUGZCUHRZS
      ZUCUGZCUIRZSZWDRZWIWJWDRZHUHRZSZWMWDRZHUIRZSZUJZUCWFUKUBWFUKUAULUKZGUERZW
      GBUFZWFXEAUFZWHGUMQZHUMQZBEQZXFMNPBGEHXEWGXETZWGTZJVHUNCUMQZXHADQZXGLMOAC
      DGWFXEWFTZXKIVHUNZWFXEWGBAUOUPXCUAUBUCULWFWFWIULQZWJWFQZWMWFQZUQZWPWOARZB
      RZXBXTXGWOWFQZWPYBUJXPXQXRXSYCXQXRURWLWFQZXSYCXMXQXRYDLWIWJWKCWFXOWKTZUSU
      TXMYDXSYCLWLWMCWNWFXOWNTZVAUTVBVCWFXEWOBAVDVEXTWIWJARZGUHRZSWMARZGUIRZSZB
      RZWIYGBRZWRSZYIBRZXASZYBXBXQXQXRYGXEQZXSYIXEQZYLYPUJZXQVFWFXEWJAXPVGWFXEW
      MAXPVGXHXIXJUQXQYQYRUQYSXHXIXJMNPVIWIYGYIYHWRBGYJXAEHXEWGXKXLYJTZXATZYHTZ
      WRTZJVJVKVLXTYAYKBXMXHXNUQXTYAYKUJXMXHXNLMOVIWIWJWMWKYHACWNYJDGWFXEXOXKYF
      YTYEUUBIVJVKVMXTWSYNWTYOXAXTWQYMWIWRXTXGXRWQYMUJXPXQXRXSVNWFXEWJBAVDVEVOX
      TXGXSWTYOUJXPXQXRXSVPWFXEWMBAVDVEVSVQVRVTXMXIWEWHXDURWALNUAUBUCWKWRWDCWNX
      AFHWFWGXOXLYFUUAYEUUCKWBUPWC $.
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
      cc simpl nvsid syl2an oveq1d fveq2d simpl2 lnof ffvelrn syl2anc 3eqtr3d
      wf ) DNOZHNOZCGOZUAZAIOZBIOZUBZUBZPADUCQZRZBERZCQZPACQZHUCQZRZBCQZFRZABER
      ZCQVMVPFRVDPUIOVEVFVLVQSUDPABVIVNCDEFGHIHUEQZJVSTZKLVITZVNTZMUFUGVHVKVRCV
      HVJABEVDVAVEVJASVGVAVBVCUHVEVFUJZAVIDIJWAUKULUMUNVHVOVMVPFVHVBVMVSOZVOVMS
      VAVBVCVGUOVDIVSCUTVEWDVGCDGHIVSJVTMUPWCIVSACUQULVMVNHVSVTWBUKURUMUS $.
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
      c1 cc ancom2s nvmval2 3expb 3ad2antl1 fveq2d simpl2 wf lnof simpl ffvelrn
      syl2an simpr syl3anc 3eqtr4d ) DNOZHNOZCEOZUAZAIOZBIOZPZPZUIUBZBDUCQZRADU
      DQZRZCQZVMBCQZHUCQZRACQZHUDQZRZABFRZCQVTVRGRZVHVJVIVQWBSZVHVMUJOVJVIWEUEV
      MBAVNVSCDVOWAEHIHUFQZJWFTZVOTZWATZVNTZVSTZMUGUHUKVLWCVPCVEVFVKWCVPSZVGVEV
      IVJWLABVNDVOFIJWHWJKULUMUNUOVLVFVTWFOZVRWFOZWDWBSVEVFVGVKUPVHIWFCUQZVIWMV
      KCDEHIWFJWGMURZVIVJUSIWFACUTVAVHWOVJWNVKWPVIVJVBIWFBCUTVAVTVRVSHWAGWFWGWI
      WKLULVCVD $.
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
      cba adantr simpl2 wf lnof ffvelrnd eqtrd 3eqtr3d ) FNOZHNOZEGOZUAZAUBOZBI
      OZPZPZABCQZFUCRZFUDRZQZERZABERZDQZVQERZHUDRZQZVPERWBVOVKVLVMVQIOZVTWESVKV
      NUEVKVLVMUFZVKVLVMUGZVOVHWFVHVIVJVNUHZFIVQJVQTZUIUJABVQCDEFVRWDGHIHUTRZJW
      KTZVRTZWDTZKLMUKULVOVSVPEVOVHVPIOZVSVPSWIVOVHVLVMWOWIWGWHABCFIJKUMUNVPFVR
      IVQJWMWJUOUPUQVOWEWBHUCRZWDQZWBVKWEWQSVNVKWCWPWBWDVQEFGHIWKWPJWLWJWPTZMUR
      USVAVOVIWBWKOZWQWBSVHVIVJVNVBZVOVIVLWAWKOWSWTWGVOIWKBEVKIWKEVCVNEFGHIWKJW
      LMVDVAWHVEAWADHWKWLLUMUNWBHWDWKWPWLWNWRUOUPVFVG $.
  $}

  ${
    nvo00.1 $e |- X = ( BaseSet ` U ) $.
    $( Two ways to express a zero operator.  (Contributed by NM, 27-Nov-2007.)
       (New usage is discouraged.) $)
    nvo00 $p |- ( ( U e. NrmCVec /\ T : X --> Y ) ->
                  ( T = ( X X. { Z } ) <-> ran T = { Z } ) ) $=
      ( wf wfn c0 wne csn cxp wceq crn wb cnv wcel ffn cn0v cfv eqid nvzcl ne0i
      syl fconst5 syl2anr ) CDAGACHCIJZACEKZLMANUHMOBPQZCDARUIBSTZCQUGBCUJFUJUA
      UBCUJUCUDCEAUEUF $.
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
      co c1 clt csup fveq2 syl6eqr oveq2d fveq1d breq1d anbi1d rexeqbidv abbidv
      cmpt supeq1d mpteq12dv oveq1d eqeq2d anbi2d rexbidv df-nmoo ovmpt2 syl5eq
      ovex mptex ) DUCUDHUCUDUEGDHUFUMCJIPUMZBQZERZUNUGUHZAQZVRCQRZFRZUIZUEZBIU
      JZAUKZULUOUPZVEZOUAUBDHUCUCCUBQZSRZUAQZSRZPUMZVRWLTRZRZUNUGUHZWAWBWJTRZRZ
      UIZUEZBWMUJZAUKZULUOUPZVEWIUFCWKIPUMZVTWTUEZBIUJZAUKZULUOUPZVEWLDUIZCWNXD
      XEXIXJWMIWKPXJWMDSRIWLDSUQKURZUSXJULXCXHUOXJXBXGAXJXAXFBWMIXKXJWQVTWTXJWP
      VSUNUGXJVRWOEXJWODTREWLDTUQMURUTVAVBVCVDVFVGWJHUIZCXEXIVQWHXLWKJIPXLWKHSR
      JWJHSUQLURVHXLULXHWGUOXLXGWFAXLXFWEBIXLWTWDVTXLWSWCWAXLWBWRFXLWRHTRFWJHTU
      QNURUTVIVJVKVDVFVGABUBUACVLCVQWHJIPVOVPVMVN $.

    $( The operator norm function.  (Contributed by NM, 27-Nov-2007.)  (Revised
       by Mario Carneiro, 16-Nov-2013.)  (New usage is discouraged.) $)
    nmooval $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) ->
      ( N ` T ) = sup ( { x | E. z e. X
        ( ( L ` z ) <_ 1 /\ x = ( M ` ( T ` z ) ) ) } , RR* , < ) ) $=
      ( vt cfv wceq cxr clt cnv wcel wf cv c1 cle wbr wa wrex cab csup cmap cba
      co cvv fvex eqeltri elmap cmpt nmoofval fveq1d fveq1 fveq2d eqeq2d anbi2d
      rexbidv abbidv supeq1d eqid xrltso supex fvmpt sylan9eq sylan2br 3impa )
      DUAUBZHUAUBZIJCUCZCGQZBUDZEQUEUFUGZAUDZVTCQZFQZRZUHZBIUIZAUJZSTUKZRZVRVPV
      QUHZCJIULUNZUBZWJJICJHUMQUOLHUMUPUQIDUMQUOKDUMUPUQURWKWMVSCPWLWAWBVTPUDZQ
      ZFQZRZUHZBIUIZAUJZSTUKZUSZQWIWKCGXBABPDEFGHIJKLMNOUTVAPCXAWIWLXBWNCRZSWTW
      HTXCWSWGAXCWRWFBIXCWQWEWAXCWPWDWBXCWOWCFVTWNCVBVCVDVEVFVGVHXBVISWHTVJVKVL
      VMVNVO $.
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
      ( cnv wcel wf wa cv cfv c1 cle wbr cr wceq wrex ffvelrn nvcl sylan2 eleq1
      anassrs syl5ibr impcom adantrl exp31 rexlimdv abssdv ) FKLZGHCMZNZBOZDPQR
      SZAOZUQCPZEPZUAZNZBGUBATUPVCUSTLZBGUPUQGLZVCVDUPVENZVBVDURVBVFVDVFVDVBVAT
      LZUNUOVEVGUOVENUNUTHLVGGHUQCUCUTFEHIJUDUEUGUSVATUFUHUIUJUKULUM $.
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
      ( wcel cv cfv c1 cle wbr wceq wa wrex cnv cab cc0 nvz0 0le1 syl6eqbr eqid
      nvzcl jctir fveq2 breq1d fveq2d eqeq2d anbi12d rspcev syl2anc fvex anbi2d
      eqeq1 rexbidv elab sylibr ) DUALZBMZENZOPQZHCNZFNZVDCNZFNZRZSZBGTZVHVFAMZ
      VJRZSZBGTZAUBLVCHGLHENZOPQZVHVHRZSZVMDGHIJUHVCVSVTVCVRUCOPDEHJKUDUEUFVHUG
      UIVLWABHGVDHRZVFVSVKVTWBVEVROPVDHEUJUKWBVJVHVHWBVIVGFVDHCUJULUMUNUOUPVQVM
      AVHVGFUQVNVHRZVPVLBGWCVOVKVFVNVHVJUSURUTVAVB $.
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
      clt csup nmooval wss nmosetre ressxr syl6ss supxrcl syl 3adant1 eqeltrd
      cr ) BLMZDLMZEFANZUAACOJPZBQOZOUBUCUDKPVCAODQOZOUERJEUFKUGZSUHUIZSKJABVDV
      ECDEFGHVDTVETZIUJVAVBVGSMZUTVAVBRZVFSUKVIVJVFUSSKJAVDVEDEFHVHULUMUNVFUOUP
      UQUR $.

    $( The norm of an operator is nonnegative.  (Contributed by NM,
       8-Dec-2007.)  (New usage is discouraged.) $)
    nmooge0 $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) ->
                  0 <_ ( N ` T ) ) $=
      ( vz vx cnv wcel cc0 cfv cnmcv cxr eqid cle wbr wf w3a cn0v 0xr a1i simp2
      cr nvzcl ffvelrn sylan2 3adant2 nvcl syl2anc rexrd nmoxr nvge0 cv c1 wceq
      ancoms wa wrex cab clt wss nmosetre ressxr syl6ss nmosetn0 supxrub syl2an
      csup 3impa 3comr nmooval breqtrrd xrletrd ) BLMZDLMZEFAUAZUBZNBUCOZAOZDPO
      ZOZACOZNQMWAUDUEWAWEWAVSWCFMZWEUGMVRVSVTUFZVRVTWGVSVTVRWGVRVTWBEMWGBEWBGW
      BRZUHEFWBAUIUJUTUKZWCDWDFHWDRZULUMUNABCDEFGHIUOWAVSWGNWESTWHWJWCDWDFHWKUP
      UMWAWEJUQZBPOZOURSTKUQWLAOWDOUSVAJEVBKVCZQVDVLZWFSVSVTVRWEWOSTZVSVTVRWPVS
      VTVAZWNQVEWEWNMWPVRWQWNUGQKJAWMWDDEFHWKVFVGVHKJABWMWDEWBGWIWMRZVIWNWEVJVK
      VMVNKJABWMWDCDEFGHWRWKIVOVPVQ $.

    $( The norm of an operator is either real or plus infinity.  (Contributed
       by NM, 8-Dec-2007.)  (New usage is discouraged.) $)
    nmorepnf $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) ->
                   ( ( N ` T ) e. RR <-> ( N ` T ) =/= +oo ) ) $=
      ( vz vx cnv wcel cv cnmcv cfv cr cpnf wne eqid wf w3a c1 cle wceq wa wrex
      wbr cab cxr clt csup wss nmosetre cn0v nmosetn0 ne0i syl supxrre2 syl2anr
      wb c0 3impb nmooval eleq1d neeq1d 3bitr4d ) BLMZDLMZEFAUAZUBZJNZBOPZPUCUD
      UHKNVLAPDOPZPUEUFJEUGKUIZUJUKULZQMZVPRSZACPZQMVSRSVHVIVJVQVRVAZVIVJUFVOQU
      MVOVBSZVTVHKJAVMVNDEFHVNTZUNVHBUOPZAPVNPZVOMWAKJABVMVNEWCGWCTVMTZUPVOWDUQ
      URVOUSUTVCVKVSVPQKJABVMVNCDEFGHWEWBIVDZVEVKVSVPRWFVFVG $.

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
      ( cnv wcel wf w3a cfv cr cpnf wceq wn wb wo cmnf clt wbr wne df-ne syl6bb
      nmorepnf xor3 wa nbi2 simplbi sylbir mnfltxr 3syl ) BJKDJKEFALMZACNZOKZUP
      PQZRZSZUQURTZUAUPUBUCUOUQUPPUDUSABCDEFGHIUGUPPUEUFUTUQURSRZVAUQURUHVBVAUQ
      URUIRUQURUJUKULUPUMUN $.
  $}

  ${
    $d x y A $.  $d x y L $.  $d x y M $.  $d x y T $.  $d x y U $.
    $d x y W $.  $d x y X $.  $d x y Y $.
    nmolb.1 $e |- X = ( BaseSet ` U ) $.
    nmolb.2 $e |- Y = ( BaseSet ` W ) $.
    nmolb.l $e |- L = ( normCV ` U ) $.
    nmolb.m $e |- M = ( normCV ` W ) $.
    nmolb.3 $e |- N = ( U normOpOLD W ) $.
    $( A lower bound for an operator norm.  (Contributed by NM, 8-Dec-2007.)
       (New usage is discouraged.) $)
    nmoolb $p |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) /\
         ( A e. X /\ ( L ` A ) <_ 1 ) ) -> ( M ` ( T ` A ) ) <_ ( N ` T ) ) $=
      ( vy vx cfv cle wa wceq cnv wcel wf w3a c1 wbr cv wrex cab cxr clt wss cr
      nmosetre ressxr syl6ss 3adant1 fveq2 breq1d fveq2d eqeq2d anbi12d biantru
      csup eqid syl6bbr rspcev fvex eqeq1 anbi2d rexbidv sylibr supxrub nmooval
      elab syl2an adantr breqtrrd ) CUAUBZGUAUBZHIBUCZUDZAHUBADQZUERUFZSZSABQZE
      QZOUGZDQZUERUFZPUGZWHBQZEQZTZSZOHUHZPUIZUJUKVDZBFQZRWBWQUJULZWGWQUBZWGWRR
      UFWEVTWAWTVSVTWASWQUMUJPOBDEGHIKMUNUOUPUQWEWJWGWMTZSZOHUHZXAXCWDOAHWHATZX
      CWDWGWGTZSWDXEWJWDXBXFXEWIWCUERWHADURUSXEWMWGWGXEWLWFEWHABURUTVAVBXFWDWGV
      EVCVFVGWPXDPWGWFEVHWKWGTZWOXCOHXGWNXBWJWKWGWMVIVJVKVOVLWQWGVMVPWBWSWRTWEP
      OBCDEFGHIJKLMNVNVQVR $.
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
      mpan syl6ss bitrd wal eqeq1 anbi2d rexbidv ralab ralcom4 ancomsimp impexp
      bitri albii breq1 imbi2d ceqsalv ralbii r19.23v 3bitr3i bitr4i syl6bb
      fvex ) IJCUBZBUCUDZUEZCGUFZBSUGZRUHZBSUGZRAUHZEUFUISUGZUAUHZWQCUFZFUFZUJZ
      UEZAIUKZUAULZUMZWRXABSUGZTZAIUMZWLWNXEUCUNUQZBSUGZXFWJWNXKUOWKWJWMXJBSDUP
      UDHUPUDZWJWMXJUJPQUAACDEFGHIJKLMNOURUSUTVAWJXEUCVBWKXKXFUOWJXEVCUCXLWJXEV
      CVBQUAACEFHIJLNVDVHVEVIRXEBVFVGVJXFWRWOXAUJZUEZAIUKZWPTZRVKZXIXDXOWPRUAWS
      WOUJZXCXNAIXRXBXMWRWSWOXAVLVMVNVOXNWPTZRVKZAIUMXSAIUMZRVKXIXQXSARIVPXTXHA
      IXTXMWRWPTZTZRVKXHXSYCRXSXMWRUEWPTYCWRXMWPVQXMWRWPVRVSVTYBXHRXAWTFWIXMWPX
      GWRWOXABSWAWBWCVSWDYAXPRXNWPAIWEVTWFWGWH $.

    $( An upper bound for an operator norm.  (Contributed by NM, 12-Dec-2007.)
       (New usage is discouraged.) $)
    nmoub3i $p |- ( ( T : X --> Y /\ A e. RR /\ A. x e. X
  ( M ` ( T ` x ) ) <_ ( A x. ( L ` x ) ) ) -> ( N ` T ) <_ ( abs ` A ) ) $=
      ( wcel cle wbr wf cr cv cfv cmul co wral cabs wa c1 cnv nvcl mpan remulcl
      wi sylan2 adantr recn abscld syl2an ad2antrr cc0 simpl nvge0 adantl leabs
      jca lemul1a syl31anc w3a 1re a1i absge0d 3jca lemul2a sylan recnd mulid1d
      wceq breqtrd letrd adantlll ffvelrn sylancr adantlr adantll ad2antlr letr
      syl3anc mpan2d ex com23 ralimdva imp wb rexrd nmoubi biimpar syldan 3impa
      cxr ) IJCUAZBUBRZAUCZCUDZFUDZBXDEUDZUEUFZSTZAIUGZCGUDBUHUDZSTZXBXCUIZXJXG
      UJSTZXFXKSTZUOZAIUGZXLXMXJXQXMXIXPAIXMXDIRZUIZXNXIXOXSXNXIXOUOXSXNUIXIXHX
      KSTZXOXCXRXNXTXBXCXRUIZXNUIZXHXKXGUEUFZXKYAXHUBRZXNXRXCXGUBRZYDDUKRZXRYEP
      XDDEIKMULUMZBXGUNUPZUQYAYCUBRZXNXCXKUBRZYEYIXRXCBBURZUSZYGXKXGUNUTUQXCYJX
      RXNYLVAYAXHYCSTZXNYAXCYJYEVBXGSTZUIZBXKSTZYMXCXRVCXCYJXRYLUQZXRYOXCXRYEYN
      YGYFXRYNPXDDEIKMVDUMVGVEXCYPXRBVFUQBXKXGVHVIUQYBYCXKUJUEUFZXKSYAYEUJUBRZY
      JVBXKSTZUIZVJXNYCYRSTYAYEYSUUAXRYEXCYGVEYSYAVKVLYAYJYTYQXCYTXRXCBYKVMUQVG
      VNXGUJXKVOVPXCYRXKVSXRXNXCXKXCXKYLVQVRVAVTWAWBXSXIXTUIXOUOZXNXSXFUBRZYDYJ
      UUBXBXRUUCXCXBXRUIHUKRXEJRUUCQIJXDCWCXEHFJLNULWDWEXCXRYDXBYHWFXCYJXBXRYLW
      GXFXHXKWHWIUQWJWKWLWMWNXMXLXQXCXBXKXARXLXQWOXCXKYLWPAXKCDEFGHIJKLMNOPQWQU
      PWRWSWT $.

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
      cnv nmorepnf mp3an12 ffvelrn nvcl sylancr lenlt sylan an32s imbi2d syl6bb
      imnan ralbidva ralnex rexbidva rexnal 3bitr3d necon4abid ) HIBUAZAUBZDRUC
      UDUEZJUBZVOBRZERZUFUEZUGZAHUHZJSUIZBFRZUJVNWDSTZVPVSVQUDUEZUKZAHUIZJSUHZW
      DUJULZWCUMZABCDEFGHIJKLMNOPQUNCUPTGUPTZVNWEWJUOPQBCFGHIKLOUQURVNWIWBUMZJS
      UHWKVNWHWMJSVNVQSTZUGZWHWAUMZAHUIWMWOWGWPAHWOVOHTZUGZWGVPVTUMZUKWPWRWFWSV
      PVNWQWNWFWSUOZVNWQUGZVSSTZWNWTXAWLVRITXBQHIVOBUSVRGEILNUTVAVSVQVBVCVDVEVP
      VTVGVFVHWAAHVIVFVJWBJSVKVFVLVM $.

    $( An unbounded operator determines an unbounded sequence.  (Contributed by
       NM, 11-Jan-2008.)  (Revised by Mario Carneiro, 7-Apr-2013.)
       (New usage is discouraged.) $)
    nmounbseqi $p |- ( ( T : X --> Y /\ ( N ` T ) = +oo ) ->
         E. f ( f : NN --> X /\ A. k e. NN ( ( L ` ( f ` k ) ) <_ 1 /\
          k < ( M ` ( T ` ( f ` k ) ) ) ) ) ) $=
      ( vy cfv cn wf cpnf wceq wa cv c1 cle wbr clt wrex cr wral nmounbi biimpa
      wex wcel nnre imim1i ralimi2 cba fvex eqeltri nnenom breq1d fveq2d breq2d
      cvv fveq2 anbi12d axcc4 3syl ) IJAUAZAGSUBUCZUDRUEZESZUFUGUHZDUEZVNASZFSZ
      UIUHZUDZRIUJZDUKULZWBDTULTICUEZUAVQWDSZESZUFUGUHZVQWEASZFSZUIUHZUDZDTULUD
      CUOVLVMWCRABEFGHIJDKLMNOPQUMUNWBWBDUKTVQTUPVQUKUPWBVQUQURUSWAWKRICDTIBUTS
      VGKBUTVAVBVCVNWEUCZVPWGVTWJWLVOWFUFUGVNWEEVHVDWLVSWIVQUIWLVRWHFVNWEAVHVEV
      FVIVJVK $.

    $( An unbounded operator determines an unbounded sequence.  (Contributed by
       NM, 11-Jan-2008.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    nmounbseqiOLD $p |- ( ( T : X --> Y /\ ( N ` T ) = +oo ) ->
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
      wal bitr4i albii wex cba cvv fvex eqeltri nnenom wceq fveq2 breq1d fveq2d
      wn imbi12d notbid axcc4 con3i dfrex2 alinexa dfral2 rexbii rexnal 3imtr4i
      bitri nnre anim1i reximi2 syl sylbi nmobndi syl5ibr imp ) IJAUBZRICUCZUBZ
      DUCZWISZESZUDUEUFZDRUGZUHWLASZFSZWKUEUFZDRUIZTZCUOZAGSUJUKZXAXBWHUAUCZESZ
      UDUEUFZXCASZFSZWKUEUFZTZUAIUGZDUJUIZXAWJWNWRTZDRUIZTZCUOZXKWTXNCWTWJWOWST
      ZTXNWJWOWSULXMXPWJWNWRDRUMUNUPUQXOXJDRUIZXKWJXLVHZDRUGZUHCURZVHZXIVHZUAIU
      IZDRUGZVHZXOXQYDXTYBXRUAICDRIBUSSUTKBUSVAVBVCXCWLVDZXIXLYFXEWNXHWRYFXDWMU
      DUEXCWLEVEVFYFXGWQWKUEYFXFWPFXCWLAVEVGVFVIVJVKVLXOWJXSVHZTZCUOYAXNYHCXMYG
      WJXLDRVMUNUQWJXSCVNVSXQYCVHZDRUIYEXJYIDRXIUAIVOVPYCDRVQVSVRXJXJDRUJWKRUKW
      KUJUKXJWKVTWAWBWCWDUAABEFGHIJDKLMNOPQWEWFWG $.

    $( A bounded sequence determines a bounded operator.  (Contributed by NM,
       18-Jan-2008.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    nmobndseqiOLD $p |- ( ( T : X --> Y /\
         A. f ( ( f : NN --> X /\ A. k e. NN ( L ` ( f ` k ) ) <_ 1 ) ->
        E. k e. NN ( M ` ( T ` ( f ` k ) ) ) <_ k ) ) -> ( N ` T ) e. RR ) $=
      ( cn cfv cle vy wf cv c1 wbr wral wa wrex wi cr wcel impexp r19.35 imbi2i
      wal bitr4i albii nnex wceq breq1d fveq2d imbi12d ac6n nnre anim1i reximi2
      fveq2 syl sylbi nmobndi syl5ibr imp ) IJAUBZRICUCZUBZDUCZVNSZESZUDTUEZDRU
      FZUGVQASZFSZVPTUEZDRUHZUIZCUOZAGSUJUKZWFWGVMUAUCZESZUDTUEZWHASZFSZVPTUEZU
      IZUAIUFZDUJUHZWFVOVSWCUIZDRUHZUIZCUOZWPWEWSCWEVOVTWDUIZUIWSVOVTWDULWRXAVO
      VSWCDRUMUNUPUQWTWODRUHWPWNWQDUARICURWHVQUSZWJVSWMWCXBWIVRUDTWHVQEVGUTXBWL
      WBVPTXBWKWAFWHVQAVGVAUTVBVCWOWODRUJVPRUKVPUJUKWOVPVDVEVFVHVIUAABEFGHIJDKL
      MNOPQVJVKVL $.
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
      wceq breq1d rabeqbidv oveq2 syl6eqr df-blo cvv ovex eqeltri ovmpt2 syl5eq
      wa rabex ) CLUAFLUAUQBCFUBMANZEOZPQRZADUCZIJKCFLLUSJNZKNZSMZOZPQRZAVCVDTM
      ZUCVBUBUSCVDSMZOZPQRZACVDTMZUCVCCUFZVGVKAVHVLVCCVDTUDVMVFVJPQVMUSVEVIVCCV
      DSUDUEUGUHVDFUFZVKVAAVLDVNVLCFTMZDVDFCTUIHUJVNVJUTPQVNUSVIEVNVICFSMEVDFCS
      UIGUJUEUGUHKJAUKVAADDVOULHCFTUMUNURUOUP $.

    $( The predicate "is a bounded linear operator."  (Contributed by NM,
       6-Nov-2007.)  (New usage is discouraged.) $)
    isblo $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> ( T e. B <->
      ( T e. L /\ ( N ` T ) < +oo ) ) ) $=
      ( vt cnv wcel wa cv cfv cpnf clt wbr crab bloval eleq2d wceq fveq2 breq1d
      elrab syl6bb ) CKLFKLMZBALBJNZEOZPQRZJDSZLBDLBEOZPQRZMUGAUKBJACDEFGHITUAU
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
      ( vu vw cnv wcel c0o csn cxp cv cba cfv cn0v wceq wa fveq2 syl6eqr xpeq1d
      co sneqd xpeq2d df-0o cvv fvex eqeltri snex xpex ovmpt2 syl5eq ) AKLCKLUA
      BACMUEDENZOZHIJACKKIPZQRZJPZSRZNZOUQMDVBOURATZUSDVBVCUSAQRZDURAQUBFUCUDUT
      CTZVBUPDVEVAEVEVACSREUTCSUBGUCUFUGJIUHDUPDVDUIFAQUJUKEULUMUNUO $.

    $( Value of the zero operator.  (Contributed by NM, 28-Nov-2007.)
       (New usage is discouraged.) $)
    0oval $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ A e. X ) ->
            ( O ` A ) = Z ) $=
      ( cnv wcel w3a cfv csn cxp wceq wa 0ofval fveq1d cn0v 3adant3 cvv eqeltri
      fvex fvconst2 3ad2ant3 eqtrd ) BJKZDJKZAEKZLACMZAEFNOZMZFUHUIUKUMPUJUHUIQ
      ACULBCDEFGHIRSUAUJUHUMFPUIEFAFDTMUBHDTUDUCUEUFUG $.
  $}

  ${
    $d o u w U $.  $d o u w W $.  $d o u w X $.  $d o w Z $.
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
      oveq2d syl2anc oveq1d nvzcl syl nv0rid 3eqtrd eqtr4d ralrimivva ralrimiva
      wf islno mpbir2and ) AUAJZCUAJZKZDBJAUBLZCUBLZDVFGMZHMZAUDLZNZIMZAUELZNZD
      LZVNVODLZCUDLZNZVRDLZCUELZNZOZIVLPHVLPZGQPACVLVMDVLRZVMRZEUFVKWIGQVKVNQJZ
      KZWHHIVLVLWMVOVLJZVRVLJZKZKZWACUCLZWGWQVIVJVTVLJZWAWROVIVJWLWPUGZVIVJWLWP
      UHZWQVIVQVLJZWOWSWTWQVIWLWNXBWTVKWLWPUIZWMWNWOUJZVNVOVPAVLWJVPRZUKSWMWNWO
      ULZVQVRAVSVLWJVSRZUMSVTADCVLWRWJWRRZETSWQWGVNWRWCNZWRWFNWRWRWFNZWRWQWDXIW
      EWRWFWQWBWRVNWCWQVIVJWNWBWROWTXAXDVOADCVLWRWJXHETSUPWQVIVJWOWEWROWTXAXFVR
      ADCVLWRWJXHETSUNWQXIWRWRWFWQVJWLXIWROXAXCVNWCCWRWCRZXHUOUQURWQVJWRVMJZXJW
      ROXAWQVJXLXACVMWRWKXHUSUTWRCWFVMWRWKWFRZXHVAUQVBVCVDVEGHIVPWCDAVSWFBCVLVM
      WJWKXGXMXEXKFVGVH $.
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
      cnmcv cba cab wf 0oo nmooval mpd3an3 df-sn cn0v nvzcl nvz0 syl6eqbr fveq2
      wb 0le1 breq1d rspcev syl2anc biantrurd adantr 0oval 3expa ad2antlr eqtrd
      fveq2d eqeq2d anbi2d rexbidva r19.41v syl6rbb bitrd abbidv syl5req xrltso
      supeq1d wor 0xr supsn mp2an syl6eq ) AIJZCIJZKZDBLZMUAZNOUBZMWGWHGUCZAUEL
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
      ( cnv wcel wa clno co cnmoo cfv cr eqid 0lno cc0 nmoo0 0re syl6eqel
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
        cnv cr nvcl mpan recnd adantr wb fveq2 lno0 mp3an syl6eq syl6bi necon3d
        nvz recne0d simpr wo reccld wf lnof ffvelrni nvmul0or mp3an1 necon3abid
        imp syl2anc neanior syl6bbr mpbir2and nvscl nvgt0 sylancr ex adantl cle
        mpbid wrex cab cxr wss nmosetre mp2an ressxr sstri simpl necon3i sylan2
        nv1 1re syl6eqel w3a 3pm3.2i lnomul eqcomd fveq2d breq1d eqeq2d anbi12d
        csup eqle rspcev syl12anc fvex eqeq1 anbi2d rexbidv elab sylibr supxrub
        adantll wfn ffn ax-mp nmooval eqeq1i ad2antrr breqtrd 0re lenlt sylancl
        biimpi pm2.65d sylib 0oval mp3an12 eqtr4d ralrimiva eqfnfv nmoo0 impbii
        nne 0oo ) EJULZUMUNZENUNZUVAUIUOZEULZUVCNULZUNZUILUPZUVBUVAUVFUILUVAUVC
        LUQZURZUVDBUVEUVIUVDBUSZUTUVDBUNZUVIUVJUMVAUVCGULZVBVCZUVDDVCZIULZVDVEZ
        UVHUVJUVPVFUVAUVHUVJUVPUVHUVJURZUVNBUSZUVPUVQUVRUVMUMUSZUVJUVQUVLUVHUVL
        VGUQUVJUVHUVLFVHUQZUVHUVLVIUQRUVCFGLUAUGVJVKVLVMZUVHUVJUVLUMUSUVHUVLUMU
        VDBUVHUVLUMUNZUVCAUNZUVKUVTUVHUWBUWCVNRUVCFGLAUAUEUGWAVKUWCUVDAEULZBUVC
        AEVOUVTKVHUQZEHUQZUWDBUNRSTAEFHKLMBUAUBUEUFQVPVQVRZVSVTWLZWBUVHUVJWCUVQ
        UVRUVMUMUNUVKWDZUTUVSUVJURUVQUWIUVNBUVQUVMVGUQZUVDMUQZUVNBUNUWIVNZUVQUV
        LUWAUWHWEZUVHUWKUVJLMUVCEUVTUWEUWFLMEWFZRSTEFHKLMUAUBQWGVQZWHVMZUWEUWJU
        WKUWLSUVMUVDDKMBUBUDUFWIWJWMWKUVMUMUVDBWNWOWPUVQUWEUVNMUQZUVRUVPVNSUVQU
        WJUWKUWQUWMUWPUWEUWJUWKUWQSUVMUVDDKMUBUDWQWJWMZUVNKIMBUBUFUHWRWSXCWTXAU
        VIUVJUVPUTZUVIUVJURZUVOUMXBVEZUWSUWTUVOUJUOZGULZVAXBVEZUKUOZUXBEULZIULZ
        UNZURZUJLXDZUKXEZXFVDYFZUMXBUVHUVJUVOUXLXBVEZUVAUVQUXKXFXGUVOUXKUQZUXMU
        XKVIXFUWEUWNUXKVIXGSUWOUKUJEGIKLMUBUHXHXIXJXKUVQUXDUVOUXGUNZURZUJLXDZUX
        NUVQUVMUVCCVCZLUQZUXRGULZVAXBVEZUVOUXREULZIULZUNZUXQUVQUWJUVHUXSUWMUVHU
        VJXLZUVTUWJUVHUXSRUVMUVCCFLUAUCWQWJWMUVQUXTVIUQUXTVAUNZUYAUVQUXTVAVIUVJ
        UVHUVCAUSZUYFUVCAUVDBUWGXMUVTUVHUYGUYFRUVCCFGLAUAUCUEUGXOWJXNZXPXQUYHUX
        TVAYGWMUVQUVNUYBIUVQUYBUVNUVQUWJUVHUYBUVNUNZUWMUYEUVTUWEUWFXRUWJUVHURUY
        IUVTUWEUWFRSTXSUVMUVCCDEFHKLUAUCUDQXTVKWMYAYBUXPUYAUYDURUJUXRLUXBUXRUNZ
        UXDUYAUXOUYDUYJUXCUXTVAXBUXBUXRGVOYCUYJUXGUYCUVOUYJUXFUYBIUXBUXREVOYBYD
        YEYHYIUXJUXQUKUVOUVNIYJUXEUVOUNZUXIUXPUJLUYKUXHUXOUXDUXEUVOUXGYKYLYMYNY
        OUXKUVOYPWSYQUVAUXLUMUNZUVHUVJUVAUYLUUTUXLUMUVTUWEUWNUUTUXLUNRSUWOUKUJE
        FGIJKLMUAUBUGUHOUUAVQUUBUUHUUCUUDUVHUVJUXAUWSVNZUVAUVQUVOVIUQZUMVIUQUYM
        UVQUWEUWQUYNSUWRUVNKIMUBUHVJWSUUEUVOUMUUFUUGYQXCWTUUIUVDBUURUUJUVHUVEBU
        NZUVAUVTUWEUVHUYORSUVCFNKLBUAUFPUUKUULXAUUMUUNELYRZNLYRZUVBUVGVNUWNUYPU
        WOLMEYSYTLMNWFZUYQUVTUWEUYRRSFKLMNUAUBPUUSXILMNYSYTUILENUUOXIYOUVBUUTNJ
        ULZUMENJVOUVTUWEUYSUMUNRSFJKNOPUUPXIVRUUQ $.
    $}

    ${
      nmlno0i.u $e |- U e. NrmCVec $.
      nmlno0i.w $e |- W e. NrmCVec $.
      $( The norm of a linear operator is zero iff the operator is zero.
         (Contributed by NM, 6-Dec-2007.)  (New usage is discouraged.) $)
      nmlno0i $p |- ( T e. L -> ( ( N ` T ) = 0 <-> T = Z ) ) $=
        ( wcel cfv cc0 wceq wb cn0v cns cnmcv eqid cif fveq2 eqeq1d bibi12d cba
        eqeq1 cnv 0lno mp2an elimel nmlno0lem dedth ) ACLZADMZNOZAFOZPUMAFUAZDM
        ZNOZUQFOZPAFAUQOZUOUSUPUTVAUNURNAUQDUBUCAUQFUFUDBQMZEQMZBRMZERMZUQBBSMZ
        CESMZDEBUEMZEUEMZFGHIJKAFCBUGLEUGLFCLJKBCEFHIUHUIUJVHTVITVDTVETVBTVCTVF
        TVGTUKUL $.
    $}

    $( The norm of a linear operator is zero iff the operator is zero.
       (Contributed by NM, 24-Nov-2007.)  (New usage is discouraged.) $)
    nmlno0 $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) ->
       ( ( N ` T ) = 0 <-> T = Z ) ) $=
      ( wcel cfv cc0 wceq wb wi clno co cnmoo c0o oveq1 cnv caddc cmul cop cabs
      cif syl5eq eleq2d fveq1d eqeq1d eqeq2d bibi12d imbi12d oveq2 eqid elimnvu
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
      ( cc0 wcel cr cle wbr wa cv wne cfv cmul co wral wceq fveq2 fveq2d oveq2d
      wi breq12d id imp adantll 0le0 cn0v cnv cba eqid lno0 mp3an12 nvz0 syl6eq
      ax-mp adantr oveq2i recn mul01d syl5eq ad2antrl mpbiri pm2.61ne ex 3impia
      ralimdv wf lnof nmoub2i syl3an1 syld3an3 ) CFUAZBUBUAZTBUCUDZUEZAUFZKUGZW
      KCUHZGUHZBWKEUHZUIUJZUCUDZUPZAJUKZWQAJUKZCHUHBUCUDZWGWJWSWTWGWJUEZWRWQAJX
      BWRWQXBWRUEWQKCUHZGUHZBKEUHZUIUJZUCUDZWKKWKKULZWNXDWPXFUCXHWMXCGWKKCUMUNX
      HWOXEBUIWKKEUMUOUQWRWLWQXBWRWLWQWRURUSUTXBXGWRXBXGTTUCUDVAXBXDTXFTUCWGXDT
      ULWJWGXDIVBUHZGUHZTWGXCXIGDVCUAZIVCUAZWGXCXIULRSKCDFIJIVDUHZXILXMVEZMXIVE
      ZQVFVGUNXLXJTULSIGXIXOOVHVJVIVKWHXFTULWGWIWHXFBTUIUJTXETBUIXKXETULRDEKMNV
      HVJVLWHBBVMVNVOVPUQVQVKVRVSWAVTWGJXMCWBZWJWTXAXKXLWGXPRSCDFIJXMLXNQWCVGAB
      CDEGHIJXMLXNNOPRSWDWEWF $.
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
      csn cxp wfn wa fveq2 cba eqid lno0 sylan9eqr ex ralimdv wf ffn syl jctild
      fconstfv fconst2 syl6ib 0ofval 3adant3 eqeq2d sylibrd syl5bi necon1ad imp
      lnof fvex ) CMNZFMNZBDNZUAZBEOAUBZHOZAGUCZVRWABEWAPZVSHQZAGRZVRBEQZWBVTPZ
      AGRWDVTAGUDWFWCAGVSHUEUFSVRWDBGFUGTZUHZUIZQZWEVRWDBGUJZVSBTZWGQZAGRZUKZWJ
      VRWDWNWKVRWCWMAGVRWCWMWCVRWLHBTWGVSHBULHBCDFGFUMTZWGIWPUNZJWGUNZLUOUPUQUR
      VRGWPBUSWKBCDFGWPIWQLVMGWPBUTVAVBWOGWHBUSWJAGWGBVCGWGBFUGVNVDSVEVREWIBVOV
      PEWIQVQCEFGWGIWRKVFVGVHVIVJVKVL $.
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
        wb biimpar clt nvgt0 biimpa recgt0d wi 0re ltle sylancr mpd wf ffvelrni
        blof mp3an nvsge0 mp3an1 syl21anc cc recnd simpl clno w3a bloln 3pm3.2i
        lnomul syl2anc divrec2d 3eqtr4rd nvscl ancoms syldan nv1 nmoolb eqbrtrd
        eqle nmblore 3jca ledivmul2OLD mpbid 0le0 lno0 fveq2i nvz0 ax-mp oveq2i
        a1i eqtri recni mul01i 3brtr4i pm2.61ne ) AIRZACSZFSZCGSZAESZUAUBZUCUDZ
        DUESZCSZFSZYAYEESZUAUBZUCUDZAYEAYEUFZXTYGYCYIUCYKXSYFFAYECUGUHYKYBYHYAU
        AAYEEUGUIUJXRAYEULZUKZXTYBUMUBZYAUCUDZYDYMYNUNYBUMUBZADUOSZUBZCSZFSZYAU
        CYMYPXSHUOSZUBZFSZYPXTUAUBZYTYNYMYPUPRZTYPUCUDZXSHUQSZRZUUCUUDUFZYMYBXR
        YBUPRZYLDURRZXRUUJOADEIJKUSUTZVAZXRYBTULYLXRYBTAYEUUKXRYBTUFYKVFOADEIYE
        JYEVBZKVCUTVDVGZVEZYMTYPVHUDZUUFYMYBUUMXRYLTYBVHUDZUUKXRYLUURVFOADEIYEJ
        UUNKVIUTVJZVKYMTUPRUUEUUQUUFVLVMUUPTYPVNVOVPXRUUHYLIUUGACUUKHURRZCBRZIU
        UGCVQZOPQBCDHIUUGJUUGVBZNVSVTZVRZVAUUTUUEUUFUKUUHUUIPYPXSUUAHFUUGUVCUUA
        VBZLWAWBWCYMYSUUBFYMYPWDRZXRYSUUBUFZYMYPUUPWEZXRYLWFZUUKUUTCDHWGUBZRZWH
        UVGXRUKUVHUUKUUTUVLOPUUKUUTUVAUVLOPQBCDUVKHUVKVBZNWIVTZWJYPAYQUUACDUVKH
        IJYQVBZUVFUVMWKUTWLUHYMXTYBYMXTXRXTUPRZYLXRUUTUUHUVPPUVEXSHFUUGUVCLUSVO
        ZVAWEYMYBUUMWEUUOWMWNYMYRIRZYRESZUNUCUDZYTYAUCUDZYMUVGXRUVRUVIUVJUUKUVG
        XRUVROYPAYQDIJUVOWOWBZWLYMUVSUPRZUVSUNUFZUVTYMUUKUVRUWCOXRYLUVGUVRUVIUV
        GXRUVRUWBWPWQYRDEIJKUSVOUUKXRYLUWDOAYQDEIYEJUVOUUNKWRWBUVSUNXAWLUUKUUTU
        VBWHUVRUVTUKUWAUUKUUTUVBOPUVDWJYRCDEFGHIUUGJUVCKLMWSUTWLWTYMUVPUUJYAUPR
        ZWHZUURYOYDVFXRUWFYLXRUVPUUJUWEUVQUULUWEXRUUKUUTUVAUWEOPQBCDGHIUUGJUVCM
        NXBVTZXLXCVAUUSXTYBYAXDWLXEYJXRTTYGYIUCXFYGHUESZFSZTYFUWHFUUKUUTUVLYFUW
        HUFOPUVNYECDUVKHIUUGUWHJUVCUUNUWHVBZUVMXGVTXHUUTUWITUFPHFUWHUWJLXIXJXMY
        IYATUAUBTYHTYAUAUUKYHTUFODEYEUUNKXIXJXKYAYAUWGXNXOXMXPXLXQ $.
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
      nmblolbi wceq blof mp3an12 ffvelrnda 3adant3 3adant2 imsdval syl2anc clno
      3impb wf bloln lnosub mp3anl1 mpanl1 syl3an1 fveq2d eqtr4d 3adant1 oveq2d
      3brtr4d ) FAUAZDJUAZEJUAZUBZDEGUCTZUDZFTZIUETZTZFHTZWBGUETZTZUFUDZDFTZEFT
      ZCUDZWFDEBUDZUFUDUGVQVRVSWEWIUGUHZVRVSUIZVQWBJUAZWNGUJUAZVRVSWPRDEGWAJLWA
      UKZULUMWBAFGWGWDHIJLWGUKZWDUKZPQRSUOUNVEVTWLWJWKIUCTZUDZWDTZWEVTWJKUAZWKK
      UAZWLXCUPZVQVRXDVSVQJKDFWQIUJUAZVQJKFVFRSAFGIJKLMQUQURZUSUTVQVSXEVRVQJKEF
      XHUSVAXGXDXEXFSWJWKCIXAWDKMXAUKZWTOVBUMVCVTWCXBWDVQFGIVDUDZUAZVRVSWCXBUPZ
      WQXGVQXKRSAFGXJIXJUKZQVGURXKVRVSXLXGXKWOXLSWQXGXKWOXLRDEFGXJWAXAIJLWRXIXM
      VHVIVJVEVKVLVMVTWMWHWFUFVRVSWMWHUPZVQWQVRVSXNRDEBGWAWGJLWRWSNVBUMVNVOVP
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
      $( TODO - this needs to be broken up or shortened! $)
      $( Lemma for ~ blocni and ~ lnocni .  If a linear operator is continuous
         at any point, it is bounded.  (Contributed by NM, 17-Dec-2007.)
         (Revised by Mario Carneiro, 10-Jan-2014.)
         (New usage is discouraged.) $)
      blocnilem $p |- ( ( P e. X /\ T e. ( ( J CnP K ) ` P ) ) -> T e. B ) $=
        ( vz vx vy wcel ccnp co cfv wa cv cnmcv cmul cle wbr wral cr wrex c1 wi
        crp cxmt cba cnv imsxmet ax-mp eqid 1rp metcnpi3 mpanr2 mpanl12 rpreccl
        cdiv rpred ad2antlr cnsb wb wceq imsdval mp3an1 breq1d wf lnof ffvelrni
        mp3an syl2an 3pm3.2i lnosub mpan fveq2d eqtr4d imbi12d adantlr ralbidva
        w3a ancoms cn0v fveq2 oveq2d breq12d wne cns cpv simpll cc simpr adantr
        a1i nvcl cc0 clt nvgt0 biimpa elrpd rpdivcl rpcnd simprl nvscl nvpncan2
        syl3anc rprege0d nvsge0 rpcn ad2antrl recnd nvz biimpar adantl divcan1d
        necon3bid 3eqtrd rpre oveq1 syl syl2anc eqtrd rpcnne0 breq2d imp nvz0
        ex leidd eqbrtrd nvgcl rspcv sylancr 1re lemuldiv2d lnomul recdiv rpne0
        mpid eqtr2d 3bitr4d sylibd anassrs an32s lno0 fveq2i eqtri 0le0 eqbrtri
        divrec2d oveq2i mul01 syl5eq syl5breqr ad3antlr pm2.61ne sylbid ralbidv
        ralrimdva rspcev rexlimdva syl5 isblo3i mpbiran sylibr ) DKUEZEDGHUFUGU
        HUEZUIUBUJZEUHZJUKUHZUHZUCUJZUVTFUKUHZUHZULUGZUMUNZUBKUOZUCUPUQZEAUEZUV
        RUVSUWJUVSUWDDBUGZUDUJZUMUNZUWDEUHZDEUHZCUGZURUMUNZUSZUCKUOZUDUTUQZUVRU
        WJBKVAUHUEZCJVBUHZVAUHUEZUVSUXAFVCUEZUXBRBFKUALVDVEJVCUEZUXDSCJUXCUXCVF
        ZMVDVEUXBUXDUIUVSURUTUEUXAVGUDUCURBCDEGHKUXCNOVHVIVJUVRUWTUWJUDUTUVRUWM
        UTUEZUIZUWTUWJUXIUWTUIURUWMVLUGZUPUEZUWCUXJUWFULUGZUMUNZUBKUOZUWJUXHUXK
        UVRUWTUXHUXJUWMVKZVMVNUXIUWTUXNUXIUWTUWDDFVOUHZUGZUWEUHZUWMUMUNZUXQEUHZ
        UWBUHZURUMUNZUSZUCKUOZUXNUXIUWSUYCUCKUVRUWDKUEZUWSUYCVPZUXHUYEUVRUYFUYE
        UVRUIZUWNUXSUWRUYBUYGUWLUXRUWMUMUXEUYEUVRUWLUXRVQRUWDDBFUXPUWEKUAUXPVFZ
        UWEVFZLVRVSVTUYGUWQUYAURUMUYGUWQUWOUWPJVOUHZUGZUWBUHZUYAUYEUWOUXCUEZUWP
        UXCUEZUWQUYLVQZUVRKUXCUWDEUXEUXFEIUEZKUXCEWARSTEFIJKUXCUAUXGPWBWDZWCKUX
        CDEUYQWCUXFUYMUYNUYOSUWOUWPCJUYJUWBUXCUXGUYJVFZUWBVFZMVRVSWEUYGUXTUYKUW
        BUXEUXFUYPWNZUYGUXTUYKVQUXEUXFUYPRSTWFZUWDDEFIUXPUYJJKUAUYHUYRPWGWHWIWJ
        VTWKWOWLWMUXIUYDUXMUBKUXIUVTKUEZUIZUYDUXMVUCUYDUIUXMFWPUHZEUHZUWBUHZUXJ
        VUDUWEUHZULUGZUMUNZUVTVUDUVTVUDVQZUWCVUFUXLVUHUMVUJUWAVUEUWBUVTVUDEWQWI
        VUJUWFVUGUXJULUVTVUDUWEWQWRWSVUCUVTVUDWTZUYDUXMVUCVUKUIUYDUXMUXIVUBVUKU
        YDUXMUSUXIVUBVUKUIZUIZUYDDUWMUWFVLUGZUVTFXAUHZUGZFXBUHZUGZDUXPUGZEUHZUW
        BUHZURUMUNZUXMVUMUYDVUSUWEUHZUWMUMUNZVVBVUMVVCUWMUWMUMVUMVVCVUPUWEUHZVU
        NUWFULUGZUWMVUMVUSVUPUWEVUMUXEUVRVUPKUEZVUSVUPVQUXEVUMRXGZUVRUXHVULXCZV
        UMUXEVUNXDUEZVUBVVGVVHVUMVUNUXIUXHUWFUTUEZVUNUTUEVULUVRUXHXEZVULUWFVUBU
        WFUPUEZVUKUXEVUBVVMRUVTFUWEKUAUYIXHWHZXFVUBVUKXIUWFXJUNZUXEVUBVUKVVOVPR
        UVTFUWEKVUDUAVUDVFZUYIXKWHXLXMZUWMUWFXNWEZXOZUXIVUBVUKXPZVUNUVTVUOFKUAV
        UOVFZXQXSZDVUPFVUQUXPKUAVUQVFZUYHXRXSZWIVUMUXEVUNUPUEXIVUNUMUNUIZVUBVVE
        VVFVQVVHVUMVUNVVRXTZVVTVUNUVTVUOFUWEKUAVWAUYIYAXSVUMUWMUWFUXHUWMXDUEZUV
        RVULUWMYBVNZVUMUWFVUBVVMUXIVUKVVNYCYDZVULUWFXIWTZUXIVUBVWJVUKVUBUWFXIUV
        TVUDUXEVUBUWFXIVQVUJVPRUVTFUWEKVUDUAVVPUYIYEWHYIYFYGYHYJUXHUWMUWMUMUNUV
        RVULUXHUWMUWMYKUUAVNUUBVUMVURKUEZUYDVVDVVBUSZUSVUMUXEUVRVVGVWKVVHVVIVWB
        DVUPFVUQKUAVWCUUCXSUYCVWLUCVURKUWDVURVQZUXSVVDUYBVVBVWMUXRVVCUWMUMVWMUX
        QVUSUWEUWDVURDUXPYLZWIVTVWMUYAVVAURUMVWMUXTVUTUWBVWMUXQVUSEVWNWIWIVTWKU
        UDYMUUKVUMVUNUWCULUGZURUMUNUWCURVUNVLUGZUMUNVVBUXMVUMUWCURVUNVUBUWCUPUE
        ZUXIVUKVUBUXFUWAUXCUEZVWQSKUXCUVTEUYQWCZUWAJUWBUXCUXGUYSXHUUEYCURUPUEVU
        MUUFXGVVRUUGVUMVVAVWOURUMVUMVVAVUNUWAJXAUHZUGZUWBUHZVWOVUMVUTVXAUWBVUMV
        UTVUPEUHZVXAVUMVUSVUPEVWDWIVUMVVJVUBVXCVXAVQZVVSVVTUYTVVJVUBUIVXDVUAVUN
        UVTVUOVWTEFIJKUAVWAVWTVFZPUUHWHYNYOWIVUMUXFVWEVWRVXBVWOVQUXFVUMSXGVWFVU
        BVWRUXIVUKVWSYCVUNUWAVWTJUWBUXCUXGVXEUYSYAXSYOVTVUMUXLVWPUWCUMVUMVWPUWF
        UWMVLUGZUXLUXIUXHVVKVWPVXFVQZVULVVLVVQUXHVWGUWMXIWTZUIUWFXDUEVWJUIVXGVV
        KUWMYPUWFYPUWMUWFUUIWEWEVUMUWFUWMVWIVWHUXHVXHUVRVULUWMUUJVNUVBUULYQUUMU
        UNUUOYRUUPUXHVUIUVRVUBUYDUXHVUFXIVUHUMVUFXIXIUMVUFJWPUHZUWBUHZXIVUEVXIU
        WBUXEUXFUYPVUEVXIVQRSTVUDEFIJKUXCVXIUAUXGVVPVXIVFZPUUQWDUURUXFVXJXIVQSJ
        UWBVXIVXKUYSYSVEUUSUUTUVAUXHUXJXDUEZVUHXIVQUXHUXJUXOXOVXLVUHUXJXIULUGXI
        VUGXIUXJULUXEVUGXIVQRFUWEVUDVVPUYIYSVEUVCUXJUVDUVEYMUVFUVGUVHYTUVKUVIYR
        UWIUXNUCUXJUPUWDUXJVQZUWHUXMUBKVXMUWGUXLUWCUMUWDUXJUWFULYLYQUVJUVLYNYTU
        VMUVNYRUWKUYPUWJTUCUBAEFIUWEUWBJKUAUYIUYSPQRSUVOUVPUVQ $.
    $}

    $( A linear operator is continuous iff it is bounded.  Theorem 2.7-9(a) of
       [Kreyszig] p. 97.  (Contributed by NM, 18-Dec-2007.)  (Revised by Mario
       Carneiro, 10-Jan-2014.)  (New usage is discouraged.) $)
    blocni $p |- ( T e. ( J Cn K ) <-> T e. B ) $=
      ( wcel cfv vx vw vz vy ccn cn0v cba ccnp cnv eqid nvzcl ax-mp cxmt ctopon
      cme imsmet metxmet mopntopon toponunii cncnpi mpan2 blocnilem sylancr c0o
      co eleq1 wne wa wf cv clt wbr wral crp wrex cnmoo cdiv simprr cc0 nmblore
      wi cr mp3an12 wb nmlnogt0 biimpi anim12i elrp sylibr adantr rpdivcld cmul
      mp3an simprl metcl mp3an1 sylan simplrr ad2antrr ltmuldiv2 syl3anc cle id
      rpred ad2ant2r blometi 3expa lnof ffvelrni syl2an remulcl adantllr lelttr
      anassrs adantlrr mpand sylbird ralrimiva wceq breq2 imbi1d ralbidv rspcev
      syl2anc ralrimivva jctil metcn mp2an csn 0ofval cnconst2 eqeltri pm2.61ne
      cxp a1i impbii ) DFGUEVEZSZDASZYREUFTZEUGTZSZDYTFGUHVETSZYSEUISZUUBPEUUAY
      TUUAUJZYTUJUKULZYRUUBUUCUUFYTDFGUUAUUAFBUUAUMTSZFUUAUNTSZBUUAUOTSZUUGUUDU
      UIPBEUUAUUEJUPULZBUUAUQULZBFUUALURULZUSUTVAABCYTDEFGHIUUAJKLMNOPQRUUEVBVC
      YSYREIVDVEZYQSZDUUMDUUMYQVFYSDUUMVGZVHZUUAIUGTZDVIZUAVJZUBVJZBVEZUCVJZVKV
      LZUUSDTZUUTDTZCVEZUDVJZVKVLZWAZUBUUAVMZUCVNVOZUDVNVMUAUUAVMZVHZYRUUPUVLUU
      RUUPUVKUAUDUUAVNUUPUUSUUASZUVGVNSZVHZVHZUVGDEIVPVEZTZVQVEZVNSUVAUVTVKVLZU
      VHWAZUBUUAVMZUVKUVQUVGUVSUUPUVNUVOVRUUPUVSVNSZUVPUUPUVSWBSZVSUVSVKVLZVHZU
      WDYSUWEUUOUWFUUDIUISZYSUWEPQADEUVRIUUAUUQUUEUUQUJZUVRUJZOVTWCZUUOUWFUUDUW
      HDHSZUUOUWFWDPQRDEHUVRIUUMUWJUUMUJZNWEWMWFWGZUVSWHWIWJWKUVQUWBUBUUAUVQUUT
      UUASZVHZUWAUVSUVAWLVEZUVGVKVLZUVHUWPUVAWBSZUVGWBSZUWGUWRUWAWDUVQUVNUWOUWS
      UUPUVNUVOWNZUUIUVNUWOUWSUUJUUSUUTBUUAWOWPZWQUWPUVGUUPUVNUVOUWOWRXDZUUPUWG
      UVPUWOUWNWSUVAUVGUVSWTXAUWPUVFUWQXBVLZUWRUVHUVQYSUVNVHZUWOUXDYSUVNUXEUUOU
      VOUXEXCXEYSUVNUWOUXDABCUUSUUTDEUVRIUUAUUQUUEUWIJKUWJOPQXFXGWQUWPUVFWBSZUW
      QWBSZUWTUXDUWRVHUVHWAUVQUVNUWOUXFUXAUVNUVDUUQSZUVEUUQSZUXFUWOUUAUUQUUSDUU
      DUWHUWLUURPQRDEHIUUAUUQUUEUWINXHWMZXIUUAUUQUUTDUXJXICUUQUOTSZUXHUXIUXFUWH
      UXKQCIUUQUWIKUPULZUVDUVECUUQWOWPXJWQUUPUVNUWOUXGUVOYSUVNUWOUXGUUOYSUVNUWO
      UXGYSUWEUWSUXGUVNUWOVHUWKUXBUVSUVAXKXJXNXLXOUXCUVFUWQUVGXMXAXPXQXRUVJUWCU
      CUVTVNUVBUVTXSZUVIUWBUBUUAUXMUVCUWAUVHUVBUVTUVAVKXTYAYBYCYDYEUXJYFUUGCUUQ
      UMTSZYRUVMWDUUKUXKUXNUXLCUUQUQULZUAUDUCUBBCDFGUUAUUQLMYGYHWIUUNYSUUMUUAIU
      FTZYIYNZYQUUDUWHUUMUXQXSPQEUUMIUUAUXPUUEUXPUJZUWMYJYHUUHGUUQUNTSZUXPUUQSZ
      UXQYQSUULUXNUXSUXOCGUUQMURULUWHUXTQIUUQUXPUWIUXRUKULUXPFGUUAUUQYKWMYLYOYM
      YP $.

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
      ( co cv cfv cba vu vw cnv wcel wa caj wf wceq wral w3a copab cdip syl6eqr
      fveq2 feq2d eqidd feq23d oveqd eqeq2d raleqbidv 3anbi123d opabbidv eqeq1d
      ralbidv df-aj cmap cxp ovex xpex cvv fvex eqeltri anbi12i biimpri 3adant3
      elmap ssopab2i df-xp sseqtr4i ssexi ovmpt2 syl5eq ) GUCUDHUCUDUEDGHUFQIJC
      RZUGZJIKRZUGZARZWCSZBRZFQZWGWIWESZEQZUHZBJUIZAIUIZUJZCKUKZPUAUBGHUCUCUARZ
      TSZUBRZTSZWCUGZXAWSWEUGZWHWIWTULSZQZWGWKWRULSZQZUHZBXAUIZAWSUIZUJZCKUKWQU
      FIXAWCUGZXAIWEUGZXEWLUHZBXAUIZAIUIZUJZCKUKWRGUHZXKXQCKXRXBXLXCXMXJXPXRWSI
      XAWCXRWSGTSZIWRGTUNLUMZUOXRXAWSXAIWEXRXAUPXTUQXRXIXOAWSIXTXRXHXNBXAXRXGWL
      XEXRXFEWGWKXRXFGULSEWRGULUNNUMURUSVDUTVAVBWTHUHZXQWPCKYAXLWDXMWFXPWOYAIXA
      IJWCYAIUPYAXAHTSZJWTHTUNMUMZUQYAXAJIWEYCUOYAXOWNAIYAXNWMBXAJYCYAXEWJWLYAX
      DFWHWIYAXDHULSFWTHULUNOUMURVCUTVDVAVBABUBUACKVEWQJIVFQZIJVFQZVGZYDYEJIVFV
      HIJVFVHVIWQWCYDUDZWEYEUDZUEZCKUKYFWPYICKWDWFYIWOYIWDWFUEYGWDYHWFJIWCJYBVJ
      MHTVKVLZIXSVJLGTVKVLZVPIJWEYKYJVPVMVNVOVQCKYDYEVRVSVTWAWB $.
  $}

  ${
    $d o t u A $.  $d t T $.  $d o t u U $.
    hmoval.8 $e |- H = ( HmOp ` U ) $.
    hmoval.9 $e |- A = ( U adj U ) $.
    $( The set of Hermitian (self-adjoint) operators on a normed complex vector
       space.  (Contributed by NM, 26-Jan-2008.)  (Revised by Mario Carneiro,
       16-Nov-2013.)  (New usage is discouraged.) $)
    hmoval $p |- ( U e. NrmCVec -> H = { t e. dom A | ( A ` t ) = t } ) $=
      ( vu cnv wcel chmo cfv cv wceq cdm crab caj co oveq12 anidms syl6eqr ovex
      dmeqd fveq1d eqeq1d rabeqbidv df-hmo cvv eqeltri dmex rabex fvmpt syl5eq
      ) CHIDCJKALZBKZUMMZABNZOZEGCUMGLZURPQZKZUMMZAUSNZOUQHJURCMZVAUOAVBUPVCUSB
      VCUSCCPQZBVCUSVDMURCURCPRSFTZUBVCUTUNUMVCUMUSBVEUCUDUEGAUFUOAUPBBVDUGFCCP
      UAUHUIUJUKUL $.

    $( The predicate "is a hermitian operator."  (Contributed by NM,
       26-Jan-2008.)  (New usage is discouraged.) $)
    ishmo $p |- ( U e. NrmCVec ->
      ( T e. H <-> ( T e. dom A /\ ( A ` T ) = T ) ) ) $=
      ( vt cnv wcel cv cfv wceq cdm crab wa hmoval eleq2d fveq2 id eqeq12d
      elrab syl6bb ) CHIZBDIBGJZAKZUDLZGAMZNZIBUGIBAKZBLZOUCDUHBGACDEFPQUFUJGBU
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
    $d g n s w x y $.
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
    $d g n s Z $.
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
      vs c1 cmul crn coprab wa w3a df-ph elin2 rneq syl6eqr oveq fveq2d oveq12d
      eqeq1d raleqbidv oveq2d 2ralbidv fveq1 eqeq12d eloprabg anbi2d syl5bb ) G
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
      opeq2i cnv phnv eqid nvvc vcrel vafval smfval opeq12i syl6eqr 3syl opeq1d
      syl5eqr eqtrd ) BHIZBBJKZBLKZMZCAMZDMZHNUOBUROPBHQRUOURUPDMUTDUQUPBDGSUAU
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
      2cn mulcl sylan2 recl sylancr ppncand 2times eqcomd rgen2a wb addex mulex
      syl cr absf cnex fex mp2an cablo cgr cnaddablo ablogrpo ax-mp cxp ax-addf
      wf fdmi grporn isphg mp3an mpbir2an eqeltri ) AEFGHGZIBWQIJZWQUAJZCKZDKZE
      LHSMNLZWTUBUCXAFLZELZHSZMNLZELZMWTHSZMNLZXAHSZMNLZELZFLZOZDPUDCPUDZWQWQUE
      UFXNCDPWTPJZXAPJZUMZXGXBWTXAUGLZHSZMNLZELZXMXRXFYAXBEXRXEXTMNXRXDXSHXRXDW
      TXAUCZELXSXRXCYCWTEXQXCYCOXPXAUHUIUJWTXAUKQULUNUJXRYBXLXLELZXMXRYBXLMWTXA
      UOSZFLZUPSZFLZELZXLYHUGLZELYDXRXBYIYAYJEWTXAUQWTXAURUSXRXLYHXLXPXIPJXKPJX
      LPJZXQXPXHXPXHWTUTRVAXQXJXQXJXAUTRVAXIXKVBVCZXRMPJYGPJZYHPJVEXRYFPJZYMXQX
      PYEPJYNXAVDWTYEVFVGYNYGYFVHRVQMYGVFVIYLVJQXRYKYDXMOYLYKXMYDXLVKVLVQQQVMET
      JFTJHTJZWRWSXOUMVNVOVPPVRHWJPTJYOVSVTPVRTHWAWBCDTTTFEHPEPEWCJEWDJWEEWFWGP
      PWHPEWIWKWLWMWNWOWP $.
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
      cv wb eqid nvop eleq1 c1 cneg cpv eqeltri cnmcv bafval isphg mp3an nvmval
      fvex 3expa fveq2d oveq1d oveq2d eqeq1d ralbidva pm5.32i anbi1d syl5bb syl
      syl5rbb bitrd bianabs biadan2 ) CUALZCUBLZAUHZBUHZDMFNOPMZVSVTEMZFNZOPMZQ
      MZOVSFNOPMVTFNOPMQMUCMZRZBGUDZAGUDZCUEVRVQWIVRCDCUFNZUGFUGZRZVQVRWISZUIWJ
      CDFIWJUJZKUKWLVQWKUALZWMCWKUAULWOWKUBLZWAVSUMUNVTWJMDMZFNZOPMZQMZWFRZBGUD
      ZAGUDZSZWLWMDTLWJTLFTLWOXDUIDCUONTICUOVBUPCUFVBFCUQNTKCUQVBUPABTTTWJDFGCD
      GHIURUSUTWMVRXCSWLXDVRWIXCVRWHXBAGVRVSGLZSZWGXABGXFVTGLZSZWEWTWFXHWDWSWAQ
      XHWCWROPXHWBWQFVRXEXGWBWQRVSVTWJCDEGHIWNJVAVCVDVEVFVGVHVHVIWLVRWPXCCWKUBU
      LVJVMVKVNVLVOVP $.

    $( The parallelogram law for an inner product space.  (Contributed by NM,
       2-Apr-2007.)  (New usage is discouraged.) $)
    phpar2 $p |- ( ( U e. CPreHilOLD /\ A e. X /\ B e. X ) ->
      ( ( ( N ` ( A G B ) ) ^ 2 ) + ( ( N ` ( A M B ) ) ^ 2 ) ) =
        ( 2 x. ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) ) $=
      ( vx co cfv c2 cexp caddc cmul wceq oveq1d vy ccphlo wcel w3a cv wral cnv
      isph simprbi 3ad2ant1 wi oveq1 fveq2d oveq12d fveq2 oveq2d eqeq12d rspc2v
      oveq2 3adant1 mpd ) CUBUCZAGUCZBGUCZUDLUEZUAUEZDMZFNZOPMZVEVFEMZFNZOPMZQM
      ZOVEFNZOPMZVFFNZOPMZQMZRMZSZUAGUFLGUFZABDMZFNZOPMZABEMZFNZOPMZQMZOAFNZOPM
      ZBFNZOPMZQMZRMZSZVBVCWAVDVBCUGUCWALUACDEFGHIJKUHUIUJVCVDWAWOUKVBVTWOAVFDM
      ZFNZOPMZAVFEMZFNZOPMZQMZOWJVQQMZRMZSLUAABGGVEASZVMXBVSXDXEVIWRVLXAQXEVHWQ
      OPXEVGWPFVEAVFDULUMTXEVKWTOPXEVJWSFVEAVFEULUMTUNXEVRXCORXEVOWJVQQXEVNWIOP
      VEAFUOTTUPUQVFBSZXBWHXDWNXFWRWDXAWGQXFWQWCOPXFWPWBFVFBADUSUMTXFWTWFOPXFWS
      WEFVFBAEUSUMTUNXFXCWMORXFVQWLWJQXFVPWKOPVFBFUOTUPUPUQURUTVA $.
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
      c1 wral c1st vafval fvex eqeltri c2nd smfval nmcvfval 3pm3.2i phop eleq1d
      cop ibi cnv bafval isphg simplbda sylancr 3ad2ant1 wi oveq1 oveq12d fveq2
      fveq2d oveq2d eqeq12d oveq2 rspc2v 3adant1 mpd ) DUCLZAGLZBGLZUDUAUEZUBUE
      ZEMZFNZOPMZWBUHUFZWCCMZEMZFNZOPMZQMZOWBFNZOPMZWCFNZOPMZQMZRMZUGZUBGUIUAGU
      IZABEMZFNZOPMZAWGBCMZEMZFNZOPMZQMZOAFNZOPMZBFNZOPMZQMZRMZUGZVSVTWTWAVSESL
      ZCSLZFSLZUDZECUTFUTZUCLZWTXPXQXREDUJNZUJNSDEIUKYBUJULUMCYBUNNSCDJUOYBUNUL
      UMFDUNNSDFKUPDUNULUMUQVSYAVSDXTUCCDEFIJKURUSVAXSYAXTVBLWTUAUBSSSCEFGDEGHI
      VCVDVEVFVGVTWAWTXOVHVSWSXOAWCEMZFNZOPMZAWHEMZFNZOPMZQMZOXJWPQMZRMZUGUAUBA
      BGGWBAUGZWLYIWRYKYLWFYEWKYHQYLWEYDOPYLWDYCFWBAWCEVIVLTYLWJYGOPYLWIYFFWBAW
      HEVIVLTVJYLWQYJORYLWNXJWPQYLWMXIOPWBAFVKTTVMVNWCBUGZYIXHYKXNYMYEXCYHXGQYM
      YDXBOPYMYCXAFWCBAEVOVLTYMYGXFOPYMYFXEFYMWHXDAEWCBWGCVOVMVLTVJYMYJXMORYMWP
      XLXJQYMWOXKOPWCBFVKTVMVMVNVPVQVR $.
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
          oveq1i oveq12i 3eqtr3i eqtr4i add4i eqtr2i 3eqtri 3eqtr3ri addcli 4re
          ip0i 4pos gt0ne0ii divcan3i ) UAABGUBZCDUBZAUCUDZBEUBZGUBZCDUBZUEUBZU
          FUBZUAUGUBUAUHACDUBZUFUBZUFUBZUAUGUBWSXBWTXCUAUGUHUAXAUFUBZUFUBUHACGU
          BZIUIZUHUJUBZAWOCEUBZGUBZIUIZUHUJUBZUKUBZULAULCEUBZGUBZIUIZUHUJUBZAUL
          UDZCEUBZGUBZIUIZUHUJUBZUKUBZUFUBZUEUBZUFUBZXCWTXDYDUHUFFUPUMZAJUMZCJU
          MZXDYDUNFOUQZPRACDEFGIJKLMSNUOURUSUHUAXAUTVAYFYGYHXAVHUMYIPRACDFJKNVB
          URZVCYEWMCGUBZIUIZUHUJUBZWMXHGUBZIUIZUHUJUBZUKUBZWQCGUBZIUIZUHUJUBZWQ
          XHGUBZIUIZUHUJUBZUKUBZUEUBZULWMXMGUBZIUIZUHUJUBZWMXRGUBZIUIZUHUJUBZUK
          UBZUFUBZULWQXMGUBZIUIZUHUJUBZWQXRGUBZIUIZUHUJUBZUKUBZUFUBZUEUBZUEUBZY
          QUUMUEUBZUUDUVAUEUBZUEUBZWTYEUHXLUFUBZUHYCUFUBZUEUBUVCUHXLYCUTXGXKXGX
          FXEFIJKSYIYFYGYHXEJUMYIPRACFGJKLVDURVEVFVGXKXJXIFIJKSYIYFYGXHJUMZXIJU
          MYIPYFWOVHUMZYHUVIYIUCVIVJZRWOCEFJKMVKURZAXHFGJKLVDURVEVFVGVLULYBVMXP
          YAXPXOXNFIJKSYIYFYGXMJUMZXNJUMYIPYFULVHUMYHUVMYIVMRULCEFJKMVKURZAXMFG
          JKLVDURVEVFVGYAXTXSFIJKSYIYFYGXRJUMZXSJUMYIPYFXQVHUMYHUVOYIULVMVJRXQC
          EFJKMVKURZAXRFGJKLVDURVEVFVGVLZVNVOUUEUVGUVBUVHUEWMUCCEUBZGUBZIUIZUHU
          JUBZYPUKUBZWQUVRGUBZIUIZUHUJUBZUUCUKUBZUEUBUHAUVRGUBZIUIZUHUJUBZXKUKU
          BZUFUBUUEUVGABCDEFGUCIJKLMNOPQRSVIWIUWBYQUWFUUDUEUWAYMYPUKUVTYLUHUJUV
          SYKIUVRCWMGYFYHUVRCUNYIRCEFJKMVPVQZUSVRVSVSUWEYTUUCUKUWDYSUHUJUWCYRIU
          VRCWQGUWKUSVRVSVSVTUWJXLUHUFUWIXGXKUKUWHXFUHUJUWGXEIUVRCAGUWKUSVRVSVS
          USWAULUULUUTUEUBZUFUBULUHYBUFUBZUFUBUVBUVHUWLUWMULUFABCDEFGULIJKLMNOP
          QRSVMWIUSULUULUUTVMUUHUUKUUHUUGUUFFIJKSYIYFWMJUMZUVMUUFJUMYIYFYGBJUMZ
          UWNYIPQABFGJKLVDURZUVNWMXMFGJKLVDURVEVFVGUUKUUJUUIFIJKSYIYFUWNUVOUUIJ
          UMYIUWPUVPWMXRFGJKLVDURVEVFVGVLZUUPUUSUUPUUOUUNFIJKSYIYFWQJUMZUVMUUNJ
          UMYIYFYGWPJUMZUWRYIPYFUVJUWOUWSYIUVKQWOBEFJKMVKURAWPFGJKLVDURZUVNWQXM
          FGJKLVDURVEVFVGUUSUURUUQFIJKSYIYFUWRUVOUUQJUMYIUWTUVPWQXRFGJKLVDURVEV
          FVGVLZVOULUHYBVMUTUVQVCWAVTWBYQUUDUUMUVAYMYPYMYLYKFIJKSYIYFUWNYHYKJUM
          YIUWPRWMCFGJKLVDURVEVFVGYPYOYNFIJKSYIYFUWNUVIYNJUMYIUWPUVLWMXHFGJKLVD
          URVEVFVGVLYTUUCYTYSYRFIJKSYIYFUWRYHYRJUMYIUWTRWQCFGJKLVDURVEVFVGUUCUU
          BUUAFIJKSYIYFUWRUVIUUAJUMYIUWTUVLWQXHFGJKLVDURVEVFVGVLULUULVMUWQVNULU
          UTVMUXAVNWCWTUAWNUFUBZUAWRUFUBZUEUBUVFUAWNWRVAYFUWNYHWNVHUMYIUWPRWMCD
          FJKNVBURZYFUWRYHWRVHUMYIUWTRWQCDFJKNVBURZVOUXBUVDUXCUVEUEYFUWNYHUXBUV
          DUNYIUWPRWMCDEFGIJKLMSNUOURYFUWRYHUXCUVEUNYIUWTRWQCDEFGIJKLMSNUOURVTW
          DWEWFVSWSUAWNWRUXDUXEWGVAUAWHWJWKZWLXBUAUHXAUTYJVNVAUXFWLWA $.
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
        addid1i cn0v cfv eqid nvrinv mp2an oveq1i dip0l eqtri oveq2i w3a ax-1cn
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
        ( co wcel wceq mp2an c2 cdiv cmul cneg caddc 2cn 2ne0 recidi oveq1i cnv
        c1 w3a phnvi reccli nvgcl mp3an 3pm3.2i nvsass nvsid 3eqtr3i nvscl ip2i
        cc eqtr3i neg1cn ip1i cn0v cfv cablo wa c1st cvc eqid nvvc ax-mp vafval
        vcablo pm3.2i bafval ablo4 smfval vc2 nvrinv oveq12i nv0rid 3eqtri nvdi
        oveq2i eqtr4i ax-1cn divcan1i eqtri mulcomi mul2negi nv0lid 3eqtr2i
        1t1e1 ) ABGQZCDQZUAUKUAUBQZWREQZCDQUCQZXAWTAUKUDZBEQZGQZEQZGQZCDQZXAXCX
        FEQZGQZCDQZUEQACDQZBCDQZUEQUAXAEQZCDQWSXBXNWRCDUAWTUCQZWREQZUKWREQZXNWR
        XOUKWREUAUFUGUHUIFUJRZUAVCRZWTVCRZWRHRZULXPXNSFMUMZXSXTYAUFUAUFUGUNZXRA
        HRZBHRZYAYBNOABFGHIJUOUPZUQUAWTWREFHIKURTXRYAXQWRSYBYFWREFHIKUSTUTUIXAC
        DEFGHIJKLMXRXTYAXAHRYBYCYFWTWREFHIKVAUPZPVBVDXAXFCDEFGHIJKLMYGXRXTXEHRZ
        XFHRYBYCXRYDXDHRZYHYBNXRXCVCRZYEYIYBVEOXCBEFHIKVAUPZAXDFGHIJUOUPZWTXEEF
        HIKVAUPPVFXHXLXKXMUEXGACDWTWRXEGQZEQZWTUAUCQZAEQZXGAYNWTUAAEQZEQZYPYMYQ
        WTEYMAAGQZBXDGQZGQZYQFVGVHZGQZYQGVIRZYDYEVJZYDYIVJYMUUASFVKVHZVLRZUUDXR
        UUGYBFUUFUUFVMVNVOZGUUFFGJVPZVQVOZYDYENOVRZYDYINYKVRABAXDGHFGHIJVSZVTUP
        YSYQYTUUBGUUGYDYSYQSUUHNAEGUUFHUUIEFKWAZUULWBTXRYEYTUUBSYBOBEFGHUUBIJKU
        UBVMZWCTWDXRYQHRZUUCYQSYBXRXSYDUUOYBUFNUAAEFHIKVAUPYQFGHUUBIJUUNWETWFWH
        XRXTXSYDULYPYRSYBXTXSYDYCUFNUQWTUAAEFHIKURTWIXRXTYAYHULYNXGSYBXTYAYHYCY
        FYLUQWTWRXEEFGHIJKWGTYPUKAEQZAYOUKAEUKUAWJUFUGWKZUIXRYDUUPASYBNAEFHIKUS
        TWLUTUIXJBCDXJWTWRXCAEQZBGQZGQZEQZUKBEQZBXJXAWTUUSEQZGQZUVAXIUVCXAGXCWT
        UCQZXEEQZWTXCUCQZXEEQZXIUVCUVEUVGXEEXCWTVEYCWMUIXRYJXTYHULUVFXISYBYJXTY
        HVEYCYLUQXCWTXEEFHIKURTUVHWTXCXEEQZEQZUVCXRXTYJYHULUVHUVJSYBXTYJYHYCVEY
        LUQWTXCXEEFHIKURTUVIUUSWTEUVIUURXCXDEQZGQZUUSXRYJYDYIULUVIUVLSYBYJYDYIV
        ENYKUQXCAXDEFGHIJKWGTUVKBUURGXCXCUCQZBEQZUVBUVKBUVMUKBEUVMUKUKUCQUKUKUK
        WJWJWNWQWLUIXRYJYJYEULUVNUVKSYBYJYJYEVEVEOUQXCXCBEFHIKURTXRYEUVBBSYBOBE
        FHIKUSTZUTWHWLWHWLUTWHXRXTYAUUSHRZULUVAUVDSYBXTYAUVPYCYFXRUURHRZYEUVPYB
        XRYJYDUVQYBVENXCAEFHIKVAUPZOUURBFGHIJUOUPUQWTWRUUSEFGHIJKWGTWIUVAWTUABE
        QZEQZYOBEQZUVBUUTUVSWTEUUTAUURGQZBBGQZGQZUWCUVSUUDUUEUVQYEVJUUTUWDSUUJU
        UKUVQYEUVROVRABUURBGHUULVTUPUWDUUBUWCGQZUWCUWBUUBUWCGXRYDUWBUUBSYBNAEFG
        HUUBIJKUUNWCTUIXRUWCHRZUWEUWCSYBXRYEYEUWFYBOOBBFGHIJUOUPUWCFGHUUBIJUUNW
        OTWLUUGYEUWCUVSSUUHOBEGUUFHUUIUUMUULWBTWFWHXRXTXSYEULUWAUVTSYBXTXSYEYCU
        FOUQWTUABEFHIKURTYOUKBEUUQUIWPUVOWFUIWDWP $.
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
        mulid2d sylan9eq adantr exp31 a2d cn0v cfv eqid dip0l mp2an nv0 3eqtr4a
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
        c1 mulid1 negeqd eqtr2d adantr oveq1d neg1cn nvsass mpan mp3an2 mp3an12
        w3a ipasslem1 sylan2 oveq2d negsubd mulneg1 adantl adddid ipdiri mp3an3
        eqtrd mpdan cn0v eqid nvrinv dip0l mp2an syl6eq eqtr3d mul01d sylan9eqr
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
        cnv sylan dipcl mp3an13 syl mulcl syl2an nncn cc0 recidd oveq1d mulid2d
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
           ` ( ( w S A ) P B ) - ( w x. ( A P B ) ) ` is continuous on
           ` RR ` .  (Contributed by NM, 23-Aug-2007.)  (Revised by Mario
           Carneiro, 6-May-2014.)  (New usage is discouraged.) $)
        ipasslem7 $p |- F e. ( J Cn K ) $=
          ( cr cv co cmul cmin cmpt ccn wcel wtru cioo crn ctg cfv crest tgioo2
          eqtri ctopon cnfldtopon a1i wss ax-resscn cims cmopn cnmptid cxmt cnv
          cc phnvi eqid imsxmet ax-mp mopntopon mp1i cnmptc smcn cnmpt12f dipcn
          ctx dipcl mp3an mulcn subcn cnmpt1res trud eqeltri ) GAUBAUCZBEUDZCDU
          DZWGBCDUDZUEUDZUFUDZUGZIJUHUDZSWMWNUIUJAWLJIJVHUBIUKULUMUNJUBUOUDTJUA
          UPUQJVHURUNUIUJJUAUSUTZUBVHVAUJVBUTUJAWIWKUFJJJJVHWOUJAWHCDJFVCUNZVDU
          NZWQJVHWOUJAWGBEJJWQWQVHWOUJAJVHWOVEZUJABJWQVHKWOWPKVFUNUIZWQKURUNUIU
          JFVGUIZWSFPVIZWPFKLWPVJZVKVLWPWQKWQVJZVMVNZBKUIZUJQUTVOWTEJWQVSUDWQUH
          UDUIUJXAWPEFWQJXBXCNUAVPVNVQUJACJWQVHKWOXDCKUIZUJRUTVOWTDWQWQVSUDJUHU
          DUIUJXAWPDFWQJOXBXCUAVRVNVQUJAWGWJUEJJJJVHWOWRUJAWJJJVHVHWOWOWJVHUIZU
          JWTXEXFXGXAQRBCDFKLOVTWAUTVOUEJJVSUDJUHUDZUIUJJUAWBUTVQUFXHUIUJJUAWCU
          TVQWDWEWF $.
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
        rgen wfun cdm wb funmpt2 qssre dmmpti sseqtr4i funconstss mpbi qdensere
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
        phnvi cc nvscl mp3an 4ipval2 4re recni negcli dipcl mul12i nvgcl neg1cn
        nvcli sqcli subcli mulcli addcomi adddii w3a nvsass mp2an oveq1i eqtr3i
        3pm3.2i ixi oveq2i fveq2i mulneg1i negeqi ax-1cn negnegi 3eqtri 3eqtr3i
        nvsid oveq12i mulm1i negsubdi2i eqtr2i mulassi eqtr4i mulcomli gt0ne0ii
        mulid2i eqtri 4pos mulcani mpbi dipcj cjmuli cr 1re renegcli cjrebi cji
        mul2negi ) BQADRZCRZUAUBZQUCZBACRZSRZUAUBZXHBCRZQABCRZSRZXIXMUAUDXISRZU
        DXMSRZUEXIXMUEXRBXHFRZGUBZUFUGRZBUHUCZXHDRZFRZGUBZUFUGRZUIRZQBQXHDRZFRZ
        GUBZUFUGRZBXKXHDRZFRZGUBZUFUGRZUIRZSRZUJRZXSEUKTZBHTZXHHTZXRYSUEEMUMZOY
        TQUNTZAHTZUUBUUCULNQADEHIKUOUPZBXHCDEFGHIJKPLUQUPXSXKUDXLSRZSRZYSUDXKXL
        UDURUSZQULUTZYTUUAUUEXLUNTUUCONBACEHILVAUPZVBYSXKBAFRZGUBZUFUGRZBYCADRZ
        FRZGUBZUFUGRZUIRZQYBBXKADRZFRZGUBZUFUGRZUIRZSRZUJRZSRZUUHYSYRYHUJRZUVGY
        HYRYBYGYAYAXTEGHIPUUCYTUUAUUBXTHTUUCOUUFBXHEFHIJVCUPVEUSVFZYFYFYEEGHIPU
        UCYTUUAYDHTZYEHTUUCOYTYCUNTZUUBUVJUUCVDUUFYCXHDEHIKUOUPBYDEFHIJVCUPVEUS
        VFVGQYQULYLYPYKYKYJEGHIPUUCYTUUAYIHTZYJHTUUCOYTUUDUUBUVLUUCULUUFQXHDEHI
        KUOUPBYIEFHIJVCUPVEUSVFYOYOYNEGHIPUUCYTUUAYMHTZYNHTUUCOYTXKUNTZUUBUVMUU
        CUUJUUFXKXHDEHIKUOUPBYMEFHIJVCUPVEUSVFVGVHVIUVGXKUUSSRZXKUVESRZUJRUVHXK
        UUSUVEUUJUUNUURUUMUUMUULEGHIPUUCYTUUAUUEUULHTUUCONBAEFHIJVCUPVEUSVFZUUQ
        UUQUUPEGHIPUUCYTUUAUUOHTZUUPHTUUCOYTUVKUUEUVRUUCVDNYCADEHIKUOUPBUUOEFHI
        JVCUPVEUSVFZVGZQUVDULYBUVCUVIUVBUVBUVAEGHIPUUCYTUUAUUTHTZUVAHTUUCOYTUVN
        UUEUWAUUCUUJNXKADEHIKUOUPBUUTEFHIJVCUPVEUSVFVGZVHVJYRUVOYHUVPUJYRQUURUU
        NUIRZSRZQYCSRZUUSSRZUVOYQUWCQSYLUURYPUUNUIYKUUQUFUGYJUUPGYIUUOBFQQSRZAD
        RZYIUUOYTUUDUUDUUEVKUWHYIUEUUCUUDUUDUUEULULNVPQQADEHIKVLVMUWGYCADVQVNVO
        VRVSVNYOUUMUFUGYNUULGYMABFXKQSRZADRZUHADRZYMAUWIUHADUWIUWGUCYCUCUHQQULU
        LVTUWGYCVQWAUHWBWCWDZVNYTUVNUUDUUEVKUWJYMUEUUCUVNUUDUUEUUJULNVPXKQADEHI
        KVLVMYTUUEUWKAUEUUCNADEHIKWFVMWEVRVSVNWGVRUWDQYCUUSSRZSRUWFUWCUWMQSUWMU
        USUCUWCUUSUVTWHUUNUURUVQUVSWIWJVRQYCUUSULVDUVTWKWLUWEXKUUSSYCQXKVDULQUL
        WHZWMVNWDYHUWIUVDSRZUVPYHUHUVDSRZUWOYHUVDUWPYGUVCYBUIYFUVBUFUGYEUVAGYDU
        UTBFYCQSRZADRZYDUUTYTUVKUUDUUEVKUWRYDUEUUCUVKUUDUUEVDULNVPYCQADEHIKVLVM
        UWQXKADUWNVNVOVRVSVNVRUVDUWBWOWLUWIUHUVDSUWLVNWLXKQUVDUUJULUWBWKWPWGWLW
        LUUGUVFXKSYTUUAUUEUUGUVFUEUUCONBACDEFGHIJKPLUQUPVRWLWLWLXIXMUDYTUUAUUBX
        IUNTUUCOUUFBXHCEHILVAUPXKXLUUJUUKVHUUIUDURWQWNWRWSVSYTUUAUUBXJXOUEUUCOU
        UFBXHCEHILWTUPXNXKUAUBZXLUAUBZSRXQXKXLUUJUUKXAUWSQUWTXPSUWQUAUBYCUAUBZQ
        UAUBZSRZUWSQYCQVDULXAUWQXKUAUWNVSUXCYCXKSRUHQSRQUXAYCUXBXKSYCXBTUXAYCUE
        UHXCXDYCVDXEWSXFWGUHQWBULXGQULWOWDWEYTUUAUUEUWTXPUEUUCONBACEHILWTUPWGWP
        WE $.
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
        mpan mulass cnmcv cfv ipasslem10 oveq2i syl6eqr 3eqtr4d oveqan12d eqtrd
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
      wi cif fveq2 syl5eq eleq2d 3anbi123d oveq1d eqtrd oveq12d eqeq12d imbi12d
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
      caddc cif syl5eq eleq2d oveqd oveq1d eqtrd oveq2d eqeq12d imbi12d elimphu
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
      wb biimpi oveq12d 00id syl6eq oveq2d cc dipcl addcli addid1i syl5eq nvgcl
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
                ( sqr ` ( ( A P B ) x. ( C x. ( ( N ` B ) ^ 2 ) ) ) ) <_
                       ( ( N ` A ) x. ( N ` B ) ) ) $=
        ( co cfv c2 cexp cmul wceq csqr cle wbr cc0 cmin ccj phnvi cnv cc cjcli
        nvscl mp3an nvmcl nvcli sqge0i ccphlo w3a 3pm3.2i dipsubdi mp2an ipidsq
        wcel dipass dipassr2 oveq2i eqtri recni sqcli dipcl mulcli sub4 oveq12i
        mp4an oveq1i subdii 3eqtr4i 3eqtr3i breqtri subeq0i oveq2 mul01i syl6eq
        dipsubdir sylbir oveq2d resqcli subcli subid1i syl5breq sylib cr pm3.2i
        subge0i wa lemul1a mpan syl sqmuli syl6breqr wb mulge0i remulcli sqrlei
        mulcomi mulassi fveq2i nvge0 sqrsqi ax-mp 3brtr3g ) BADUAZCBHUBZUCUDUAZ
        UEUAZUFZCABDUAZUEUAZXSUEUAZUGUBZAHUBZXRUEUAZUCUDUAZUGUBZYBXTUEUAZUGUBYG
        UHYAYDYHUHUIZYEYIUHUIZYAYDYFUCUDUAZXSUEUAZYHUHYAYCYMUHUIZYDYNUHUIZYAUJY
        MYCUKUAZUHUIYOYAUJYQCULUBZXQXTUKUAZUEUAZUKUAZYQUHUJAYRBEUAZGUAZHUBZUCUD
        UAZUUAUHUUDUUCFHIJKFMUMZFUNVHZAIVHZUUBIVHZUUCIVHZUUFNUUGYRUOVHZBIVHZUUI
        UUFCRUPZOYRBEFIJQUQURZAUUBFGIJPUSURZUTVAUUCUUCDUAZUUCADUAZUUCUUBDUAZUKU
        AZUUEUUAFVBVHZUUJUUHUUIVCUUPUUSUFMUUJUUHUUIUUONUUNVDUUCAUUBDFGIJPLVEVFU
        UGUUJUUPUUEUFUUFUUOUUCDFHIJKLVGVFYMYRXQUEUAZUKUAZYCUUBUUBDUAZUKUAZUKUAZ
        YQUVAYRXTUEUAZUKUAZUKUAZUUSUUAUVEUVBYCUVFUKUAZUKUAZUVHUVDUVIUVBUKUVCUVF
        YCUKUVCYRBUUBDUAZUEUAZUVFUUTUUKUULUUIVCUVCUVLUFMUUKUULUUIUUMOUUNVDYRBUU
        BDEFIJQLVIVFUVKXTYRUEUVKCBBDUAZUEUAZXTUUTUULCUOVHZUULVCUVKUVNUFMUULUVOU
        ULOROVDBCBDEFIJQLVJVFUVMXSCUEUUGUULUVMXSUFUUFOBDFHIJKLVGVFVKVLVKVLVKVKY
        MUOVHUVAUOVHYCUOVHUVFUOVHUVJUVHUFYFYFAFHIJKUUFNUTZVMZVNYRXQUUMUUGUULUUH
        XQUOVHUUFONBADFIJLVOURZVPYCSVMZYRXTUUMCXSRXRXRBFHIJKUUFOUTZVMZVNVPZVPYM
        UVAYCUVFVQVSVLUUQUVBUURUVDUKUUQAADUAZUUBADUAZUKUAZUVBUUTUUHUUIUUHVCUUQU
        WEUFMUUHUUIUUHNUUNNVDAUUBADFGIJPLWIVFUWCYMUWDUVAUKUUGUUHUWCYMUFUUFNADFH
        IJKLVGVFUUTUUKUULUUHVCUWDUVAUFMUUKUULUUHUUMONVDYRBADEFIJQLVIVFVRVLUURAU
        UBDUAZUVCUKUAZUVDUUTUUHUUIUUIVCUURUWGUFMUUHUUIUUINUUNUUNVDAUUBUUBDFGIJP
        LWIVFUWFYCUVCUKUUTUUHUVOUULVCUWFYCUFMUUHUVOUULNROVDACBDEFIJQLVJVFVTVLVR
        YTUVGYQUKYRXQXTUUMUVRUWBWAVKWBWCWDYAUUAYQUJUKUAYQYAYTUJYQUKYAYSUJUFZYTU
        JUFXQXTUVRUWBWEUWHYTYRUJUEUAUJYSUJYRUEWFYRUUMWGWHWJWKYQYMYCYMYFUVPWLZVM
        UVSWMWNWHWOYMYCUWISWSWPYCWQVHZYMWQVHZXSWQVHZUJXSUHUIZWTZVCYOYPUWJUWKUWN
        SUWIUWLUWMXRUVTWLZXRUVTVAZWRVDYCYMXSXAXBXCYFXRUVQUWAXDXEUJYDUHUIZUJYHUH
        UIYKYLXFUJYCUHUIUWMUWQTUWPYCXSSUWOXGVFYGYFXRUVPUVTXHZVAYDYHYCXSSUWOXHYG
        UWRWLXIVFWPYDYJUGYDYBCUEUAZXSUEUAYJYCUWSXSUECYBRUUGUUHUULYBUOVHUUFNOABD
        FIJLVOURZXJVTYBCXSUWTRXSUWOVMXKVLXLUJYGUHUIZYIYGUFUJYFUHUIZUJXRUHUIZUXA
        UUGUUHUXBUUFNAFHIJKXMVFUUGUULUXCUUFOBFHIJKXMVFYFXRUVPUVTXGVFYGUWRXNXOXP
        $.
    $}

    ${
      siii2.3 $e |- M = ( -v ` U ) $.
      siii2.4 $e |- S = ( .sOLD ` U ) $.
      $( Lemma for ~ sii .  (Contributed by NM, 24-Nov-2007.)
         (New usage is discouraged.) $)
      siilem2 $p |- ( ( C e. CC /\ ( C x. ( A P B ) ) e. RR /\
                           0 <_ ( C x. ( A P B ) ) ) ->
                ( ( B P A ) = ( C x. ( ( N ` B ) ^ 2 ) ) ->
                  ( sqr ` ( ( A P B ) x. ( C x. ( ( N ` B ) ^ 2 ) ) ) ) <_
                         ( ( N ` A ) x. ( N ` B ) ) ) ) $=
        ( co cmul cc0 cc wcel cr cle wbr w3a cfv c2 cexp wceq csqr wi cif oveq1
        eqeq2d oveq2d fveq2d breq1d imbi12d eleq1 eleq1d breq2d 3anbi123d phnvi
        0cn cnv dipcl mp3an mul02i eqeltri 0le0 breqtrri 3pm3.2i elimhyp simp1i
        0re simp2i simp3i siilem1 dedth ) CUAUBZCABDRZSRZUCUBZTWCUDUEZUFZBADRZC
        BHUGZUHUIRZSRZUJZWBWJSRZUKUGZAHUGWHSRZUDUEZULWGWFCTUMZWISRZUJZWBWQSRZUK
        UGZWNUDUEZULCTCWPUJZWKWRWOXAXBWJWQWGCWPWISUNZUOXBWMWTWNUDXBWLWSUKXBWJWQ
        WBSXCUPUQURUSABWPDEFGHIJKLMNOPQWPUAUBZWPWBSRZUCUBZTXEUDUEZWFXDXFXGUFTUA
        UBZTWBSRZUCUBZTXIUDUEZUFCTXBWAXDWDXFWEXGCWPUAUTXBWCXEUCCWPWBSUNZVAXBWCX
        ETUDXLVBVCTWPUJZXHXDXJXFXKXGTWPUAUTXMXIXEUCTWPWBSUNZVAXMXIXETUDXNVBVCXH
        XJXKVEXITUCWBFVFUBAIUBBIUBWBUAUBFMVDNOABDFIJLVGVHVIZVPVJTTXIUDVKXOVLVMV
        NZVOXDXFXGXPVQXDXFXGXPVRVSVT $.
    $}

    $( Inference from ~ sii .  (Contributed by NM, 20-Nov-2007.)
       (New usage is discouraged.) $)
    siii $p |- ( abs ` ( A P B ) ) <_ ( ( N ` A ) x. ( N ` B ) ) $=
      ( co cfv cmul cle wbr wceq cc0 wcel cabs cn0v oveq2 cnv phnvi dip0r mp2an
      eqid syl6eq abs00bd nvge0 nvcli mulge0i syl6eqbr wne cexp cdiv csqr recni
      c2 ccj sqeq0i wb nvz bitri necon3bii dipcl mp3an resqcli divcan1zi sylbir
      cc dipcj syl6eqr oveq2d fveq2d absval ax-mp syl6reqr eqcomd cr wi divclzi
      ipipcj mulcomli oveq1i wa div23 mp3an12 syl5reqr abscli redivclzi eqeltrd
      clt sqgt0i sqge0i divge0 mpanl12 sylancr breqtrrd cns siilem2 syl3anc mpd
      mpan cnsb eqbrtrd pm2.61ine ) ABCMZUANZAENZBENZOMZPQBDUBNZBXNRZXJSXMPXOXI
      XOXIAXNCMZSBXNACUCDUDTZAFTZXPSRDJUEZKACDFXNGXNUHZIUFUGUIUJSXKPQZSXLPQZSXM
      PQXQXRYAXSKADEFGHUKUGXQBFTZYBXSLBDEFGHUKUGXKXLADEFGHXSKULBDEFGHXSLULZUMUG
      UNBXNUOZXJXIBACMZXLUTUPMZUQMZYGOMZOMZURNZXMPYEYKXIXIVANZOMZURNZXJYEYJYMUR
      YEYIYLXIOYEYIYFYLYEYGSUOZYIYFRYGSBXNYGSRXLSRZXOXLXLYDUSVBXQYCYPXOVCXSLBDE
      FXNGXTHVDUGZVEVFZYFYGXQYCXRYFVLTZXSLKBACDFGIVGVHZYGXLYDVIZUSZVJVKZXQXRYCY
      LYFRXSKLABCDFGIVMVHVNVOVPXIVLTZXJYNRXQXRYCUUDXSKLABCDFGIVGVHZXIVQVRVSYEYF
      YIRZYKXMPQZYEYIYFUUCVTYEYHVLTZYHXIOMZWATSUUIPQUUFUUGWBYEYOUUHYRYFYGYTUUBW
      CVKYEUUIXJUTUPMZYGUQMZWAYEUUKYFXIOMZYGUQMZUUIUULUUJYGUQXIYFUUJUUEYTXQXRYC
      XIYFOMUUJRXSKLABCDFGIWDVHWEWFYEYOUUMUUIRZYRYGVLTZYOUUNUUBYSUUDUUOYOWGUUNY
      TUUEYFXIYGWHWIXEVKWJZYEYOUUKWATYRUUJYGXJXIUUEWKZVIZUUAWLVKWMYESUUKUUIPYEY
      GWATZSYGWNQZSUUKPQZUUAYEXLSUOUUTXLSBXNYQVFXLYDWOVKUUJWATSUUJPQUUSUUTWGUVA
      UURXJUUQWPUUJYGWQWRWSUUPWTABYHCDXANZDDXFNZEFGHIJKLUVCUHUVBUHXBXCXDXGXH $.
  $}

  ${
    sii.1 $e |- X = ( BaseSet ` U ) $.
    sii.6 $e |- N = ( normCV ` U ) $.
    sii.7 $e |- P = ( .iOLD ` U ) $.
    sii.9 $e |- U e. CPreHilOLD $.
    $( Schwarz inequality.  Part of Lemma 3-2.1(a) of [Kreyszig] p. 137.  This
       is also called the Cauchy-Schwarz inequality by some authors and
       Bunjakovaskij-Cauchy-Schwarz inequality by others.  See also theorems
       ~ bcseqi , ~ bcsiALT , ~ bcsiHIL , ~ csbren .  (Contributed by NM,
       12-Jan-2008.)  (New usage is discouraged.) $)
    sii $p |- ( ( A e. X /\ B e. X ) ->
               ( abs ` ( A P B ) ) <_ ( ( N ` A ) x. ( N ` B ) ) ) $=
      ( wcel co cabs cfv cmul cle wbr cif wceq fveq2d cn0v oveq1 oveq1d breq12d
      fveq2 oveq2 oveq2d eqid elimph siii dedth2h ) AFKZBFKZABCLZMNZAENZBENZOLZ
      PQULADUANZRZBCLZMNZUTENZUQOLZPQUTUMBUSRZCLZMNZVCVEENZOLZPQABUSUSAUTSZUOVB
      URVDPVJUNVAMAUTBCUBTVJUPVCUQOAUTEUEUCUDBVESZVBVGVDVIPVKVAVFMBVEUTCUFTVKUQ
      VHVCOBVEEUEUGUDUTVECDEFGHIJADFUSGUSUHZJUIBDFUSGVLJUIUJUK $.
  $}

  ${
    $d x y H $.  $d x y U $.  $d x y W $.
    sspph.h $e |- H = ( SubSp ` U ) $.
    $( A subspace of an inner product space is an inner product space.
       (Contributed by NM, 1-Feb-2008.)  (New usage is discouraged.) $)
    sspph $p |- ( ( U e. CPreHilOLD /\ W e. H ) -> W e. CPreHilOLD ) $=
      ( vx vy wcel wa cfv co c2 cexp caddc cmul wceq sylan sspnval 3expa oveq1d
      eqid ccphlo cnv cv cpv cnmcv cnsb cba wral phnv sspnv sspba sseld anim12d
      wi phpar2 3expb adantlr syldan nvgcl sspgval fveq2d eqtrd sspmval oveq12d
      imp nvmcl sylanl1 adantrr adantrl oveq2d 3eqtr4d ralrimivva isph sylanbrc
      ) AUAGZCBGZHZCUBGZEUCZFUCZCUDIZJZCUEIZIZKLJZVSVTCUFIZJZWCIZKLJZMJZKVSWCIZ
      KLJZVTWCIZKLJZMJZNJZOZFCUGIZUHEWRUHCUAGVOAUBGZVPVRAUIZABCDUJZPVQWQEFWRWRV
      QVSWRGZVTWRGZHZHZVSVTAUDIZJZAUEIZIZKLJZVSVTAUFIZJZXHIZKLJZMJZKVSXHIZKLJZV
      TXHIZKLJZMJZNJZWJWPVQXDVSAUGIZGZVTYBGZHZXOYAOZVQXDYEVOWSVPXDYEUNWTWSVPHZX
      BYCXCYDYGWRYBVSABCYBWRYBTZWRTZDUKZULYGWRYBVTYJULUMPVEVOYEYFVPVOYCYDYFVSVT
      AXFXKXHYBYHXFTZXKTZXHTZUOUPUQURVOWSVPXDWJXOOWTYGXDHZWEXJWIXNMYNWEWBXHIZKL
      JXJYNWDYOKLYGXDWBWRGZWDYOOZYGVRXDYPXAVRXBXCYPVSVTCWAWRYIWATZUSUPPWSVPYPYQ
      WBABWCXHCWRYIYMWCTZDQRURSYNYOXIKLYNWBXGXHVSVTAWAXFBCWRYIYKYRDUTVASVBYNWHX
      MKLYNWHWGXHIZXMYGXDWGWRGZWHYTOZYGVRXDUUAXAVRXBXCUUAVSVTCWFWRYIWFTZVFUPPWS
      VPUUAUUBWGABWCXHCWRYIYMYSDQRURYNWGXLXHVSVTABWFXKCWRYIYLUUCDVCVAVBSVDVGXEW
      OXTKNVOWSVPXDWOXTOWTYNWLXQWNXSMYNWKXPKLYGXBWKXPOZXCWSVPXBUUDVSABWCXHCWRYI
      YMYSDQRVHSYNWMXRKLYGXCWMXROZXBWSVPXCUUEVTABWCXHCWRYIYMYSDQRVISVDVGVJVKVLE
      FCWAWFWCWRYIYRUUCYSVMVN $.
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
      ( cv cfv co wceq wral wf wa wcel wb ralcom ffvelrn ip2eqi syl2an anandirs
      ralbidva wfn ffn eqfnfv bitr4d syl5bb ) ALZBLZDMZCNULUMEMZCNOZBHPAGPUPAGP
      ZBHPZHGDQZHGEQZRZDEOZUPABGHUAVAURUNUOOZBHPZVBVAUQVCBHUSUTUMHSZUQVCTZUSVER
      UNGSUOGSVFUTVERHGUMDUBHGUMEUBAUNUOCFGIJKUCUDUEUFUSDHUGEHUGVBVDTUTHGDUHHGE
      UHBHDEUIUDUJUK $.

    $( Every operator has at most one adjoint.  (Contributed by NM,
       25-Jan-2008.)  (New usage is discouraged.) $)
    ajmoi $p |- E* s ( s : Y --> X /\
           A. x e. X A. y e. Y ( ( T ` x ) Q y ) = ( x P ( s ` y ) ) ) $=
      ( vt cv wf cfv co wceq wral wa wmo wi r19.26-2 eqtr2 ralimi sylbir phoeqi
      wal biimpa sylan2 an4s gen2 feq1 fveq1 oveq2d eqeq2d 2ralbidv anbi12d mo4
      mpbir ) HGINZOZANZEPBNZDQZVCVDVAPZCQZRZBHSAGSZTZIUAVJHGMNZOZVEVCVDVKPZCQZ
      RZBHSAGSZTZTVAVKRZUBZMUHIUHVSIMVBVLVIVPVRVIVPTZVBVLTZVGVNRZBHSZAGSZVRVTVH
      VOTZBHSZAGSWDVHVOABGHUCWFWCAGWEWBBHVEVGVNUDUEUEUFWAWDVRABCVAVKFGHJKLUGUIU
      JUKULVJVQIMVRVBVLVIVPHGVAVKUMVRVHVOABGHVRVGVNVEVRVFVMVCCVDVAVKUNUOUPUQURU
      SUT $.
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
      ( ccphlo wcel cnv wfun caddc cmul cop cabs cif caj co oveq1 syl5eq funeqd
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
      ( wcel cfv wceq cvv vt ccphlo cnv wf w3a cv co wral copab cio phnv ajfval
      wa sylan fveq1d 3adant3 cba fvex eqeltri fex mpan2 eqid feq1 fveq1 oveq1d
      eqeq1d 2ralbidv 3anbi13d fvopab5 syl 3anass baib iotabidv eqtrd 3ad2ant3
      ) GUBQZHUCQZIJFUDZUEFCRZFIJUAUFZUDZJIKUFZUDZAUFZVTRZBUFZEUGZWDWFWBRDUGZSZ
      BJUHAIUHZUEZUAKUIZRZWCWDFRZWFEUGZWHSZBJUHAIUHZUMZKUJZVPVQVSWMSVRVPVQUMFCW
      LVPGUCQVQCWLSGUKABUACDEGHIJKLMNOPULUNUOUPVRVPWMWSSVQVRWMVRWCWQUEZKUJZWSVR
      FTQZWMXASVRITQXBIGUQRTLGUQURUSIJTFUTVAWKWTUAKFWLTWLVBVTFSZWAVRWJWQWCIJVTF
      VCXCWIWPABIJXCWGWOWHXCWEWNWFEWDVTFVDVEVFVGVHVIVJVRWTWRKWTVRWRVRWCWQVKVLVM
      VNVOVN $.
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
     5-Dec-2006.)  (New usage is discouraged.) $)
  df-cbn $a |- CBan = { u e. NrmCVec |
    ( IndMet ` u ) e. ( CMet ` ( BaseSet ` u ) ) } $.

  ${
    $d u D $.  $d u U $.  $d u X $.
    iscbn.x $e |- X = ( BaseSet ` U ) $.
    iscbn.8 $e |- D = ( IndMet ` U ) $.
    $( A complex Banach space is a normed complex vector space with a complete
       induced metric.  (Contributed by NM, 5-Dec-2006.)
       (New usage is discouraged.) $)
    iscbn $p |- ( U e. CBan <-> ( U e. NrmCVec /\ D e. ( CMet ` X ) ) ) $=
      ( vu cv cims cfv cba cms wcel cnv ccbn wceq syl6eqr fveq2d eleq12d df-cbn
      fveq2 elrab2 ) FGZHIZUBJIZKIZLACKIZLFBMNUBBOZUCAUEUFUGUCBHIAUBBHTEPUGUDCK
      UGUDBJICUBBJTDPQRFSUA $.

    $( The induced metric on complex Banach space is complete.  (Contributed by
       NM, 8-Sep-2007.)  (New usage is discouraged.) $)
    cbncms $p |- ( U e. CBan -> D e. ( CMet ` X ) ) $=
      ( ccbn wcel cnv cms cfv iscbn simprbi ) BFGBHGACIJGABCDEKL $.
  $}

  $( Every complex Banach space is a normed complex vector space.  (Contributed
     by NM, 17-Mar-2007.)  (New usage is discouraged.) $)
  bnnv $p |- ( U e. CBan -> U e. NrmCVec ) $=
    ( ccbn wcel cnv cims cfv cba cms eqid iscbn simplbi ) ABCADCAEFZAGFZHFCLAMM
    ILIJK $.

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
      ( ccbn wcel cfv cms cnv wb sylan syl cims cres ccld bnnv sspnv eqid iscbn
      wa cxp baib wceq sspims eleq1d cbncms adantr cmetss 3bitrd ) BMNZECNZUHZE
      MNZEUAOZGPOZNZAGGUIUBZVCNZGDUCONZUTEQNZVAVDRURBQNZUSVHBUDZBCEKUESVAVHVDVB
      EGLVBUFZUGUJTUTVBVEVCURVIUSVBVEUKVJVBABCEGLIVKKULSUMUTAFPONZVFVGRURVLUSAB
      FHIUNUOADFGJUPTUQ $.
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
      ( ccbn wcel cnv caddc cmul cop cabs cims cfv cc cnnv cmin ccom eqid cnims
      cms eqcomi cncmet cnnvba fveq2i iscbn mpbir2an ) ACDAEDFGHIHZJKZLRKDABMUF
      INOZUFUGUEUEPUGPQSTUFALABUAAJKUFAUEJBUBSUCUD $.
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
          bnnv blocn2 ctopon cxmt cms cme cbncms cmetmet metxmet mp2b mopntopon
          id wb imsxmet iscncl mp2an sylib syl simpld ffvelrnda biantrurd fveq2
          adantlr breq1d elrab syl6bbr pm5.32da fveq2d a1i wfn ffn cxr cr nvzcl
          mp3an12 clt wi simpr syl2an adantr sylancr ralimdva cvv elssuni sseld
          cn0v sylan rexlimdva mpd wex sstr2 ex elpreima 3bitr4d eqrdv ad2antlr
          3syl nnre rexrd nvnd xmetsym eqtr4d rabbiia blcld simprd imaeq2 rspcv
          mpan sylc eqeltrd ralrimiva iincld syl2anr eqeltrrd mopntop toponunii
          ctop topcld pm2.61ne fmptd cpw frn cldss2 syl6ss arch ltle impr an32s
          sspwuni nvcl simpllr simplrl letr syl3anc mpan2d eqeltri rabex fvmpt2
          expr fvex mpan2 eleq2d ralbidv syl6bb bicomd sylan9bbr fnfvelrn syl6d
          sylbird dfss3 eqssd ne0i mpanl12 syl2anc ffvelrn sseldi elpwid ntrss3
          bcth2 cbl ntropn mopni2 mp3an1 syl6sseqr cdiv ntrss2 syl5com ad2antrr
          c2 w3a jctil rphalfcl rpxrd rpxr rphalflt 3jca blsscls2 breq2 rabbidv
          sseq1d rspcev 3syld syldan jcad eximdv n0 df-rex 3imtr4g reximdva ) A
          KUGZFUHZLUIUHUHZUJUKZKULUMZCUGZDUGZGUNZPUGZUOUPZDOUQZUYSURZPUSUMZCOUM
          ZKULUMAULLUTUHZFVAZFVOZVBZOVCZVUBAJULVUDEUGZUHZMUHZJUGZUOUPZEHVDZDOUQ
          ZVULFAVUTULVEZVFZVVCVULVEOVULVEZHUJHUJVCZVVCOVULVVGOVVCVVGVVBDOVDOVVC
          VCVVGVVBDOVVAEHVGVHVVBDOVIVJVKVLVVEHUJUKZVFEHVVADOUQZVPZVVCVULVVHVVJV
          VCVCVVEVVAEDHOVMVNVVHVVHVVIVULVEZEHVDVVJVULVEVVEVVHWTVVEVVKEHVVEVUQHV
          EZVFZVVIVUQVQZVUCMUHZVUTUOUPZCNVRUHZUQZVSZVULVVMBVVIVVSVVMBUGZOVEZVVT
          VUQUHZMUHZVUTUOUPZVFZVWAVWBVVRVEZVFZVVTVVIVEZVVTVVSVEZVVMVWAVWDVWFVVM
          VWAVFZVWDVWBVVQVEZVWDVFVWFVWJVWKVWDVVMOVVQVVTVUQAVVLOVVQVUQVAZVVDAVVL
          VFZVWLVVNVVTVSZVULVEZBNVTUHZWAUHZUTUHZVDZVWMVUQINWBUNZVEZVWLVWSVFZAHV
          WTVUQUDWCVXAVUQLVWQWDUNVEZVXBVWTGVWPVUQILVWQNTVWPWEZUAVWQWEZVWTWEIWFV
          EZIWGVEZUBIWIWHZUCWJLOWKUHVEZVWQVVQWKUHVEZVXCVXBXAGOWLUHVEZVXIGOWMUHV
          EZGOWNUHVEVXKVXFVXLUBGIORTWOWHZGOWPGOWQWRZGLOUAWSWHZVWPVVQWLUHVEZVXJN
          WGVEZVXPUCVWPNVVQVVQWEZVXDXBWHZVWPVWQVVQVXEWSWHBVUQLVWQOVVQXCXDXEXFZX
          GZXKZXHXIVVPVWDCVWBVVQVUCVWBVCVVOVWCVUTUOVUCVWBMXJXLXMXNXOVWHVWEXAVVM
          VVAVWDDVVTOVUDVVTVCZVUSVWCVUTUOVYCVURVWBMVUDVVTVUQXJXPXLZXMXQVVMVWLVU
          QOXRVWIVWGXAVYBOVVQVUQXSOVVTVVRVUQUUAUUEUUBUUCVVMVVRVWRVEZVWSVVSVULVE
          ZVVMVUTXTVEZVYEVVMVUTVVDVUTYAVEZAVVLVUTUUFZUUDUUGVXPNYNUHZVVQVEZVYGVY
          EVXSVXQVYKUCNVVQVYJVXRVYJWEZYBWHZCVWPVYJVUTVVRVWQVVQVXEVVPVYJVUCVWPUN
          ZVUTUOUPCVVQVUCVVQVEZVVOVYNVUTUOVYOVVOVUCVYJVWPUNZVYNVXQVYOVVOVYPVCUC
          VUCVWPNMVVQVYJVXRVYLSVXDUUHUUPVXPVYKVYOVYNVYPVCVXSVYMVYJVUCVWPVVQUUIY
          CUUJXLUUKUULYCXFAVVLVWSVVDVWMVWLVWSVXTUUMXKVWOVYFBVVRVWRVVTVVRVCVWNVV
          SVULVVTVVRVVNUUNVLUUOUUQUURUUSEHVVILUUTUVAUVBVVFVVELUVEVEZVVFVXKVYQVX
          NGLOUAUVCWHZLOOLVXOUVDZUVFWHXQUVGUFUVHZAVUOOAVUNOUVIZURVUOOURAVUNVULW
          UAAVUMVUNVULURVYTULVULFUVJXFLOVYSUVKZUVLVUNOUVQXEAVVTVUOVEZBOVDZOVUOU
          RAVWCQUGZUOUPZEHVDZQYAUMZBOVDWUDUEAWUHWUCBOAVWAVFZWUGWUCQYAWUIWUEYAVE
          ZVFZWUEVUTYDUPZJULUMZWUGWUCYEZWUJWUMWUIWUEJUVMVNWUKWULWUNJULWUKVVDVFW
          ULWUGVWDEHVDZWUCWUKVVDWULWUGWUOYEWUKVVDWULVFZVFZWUFVWDEHWUQVVLVFZWUFW
          UEVUTUOUPZVWDWUQWUSVVLWUKVVDWULWUSWUKWUJVYHWULWUSYEVVDWUIWUJYFVYIWUEV
          UTUVNYGUVOYHWURVWCYAVEZWUJVYHWUFWUSVFVWDYEWUKVVLWUTWUPWUIVVLWUTWUJWUI
          VVLVFVXQVWKWUTUCAVVLVWAVWKVWMOVVQVVTVUQVYAXHUVPVWBNMVVQVXRSUVRYIXKXKW
          UIWUJWUPVVLUVSWURVVDVYHWUKVVDWULVVLUVTVYIXFVWCWUEVUTUWAUWBUWCYJUWGWUI
          VVDWUOWUCYEWUJWUIVVDVFWUOVVTVUTFUHZVEZWUCVVDWVBVWAWUOVFZWUIWUOVVDWVBV
          VTVVCVEWVCVVDWVAVVCVVTVVDVVCYKVEWVAVVCVCVVBDOOIVRUHYKRIVRUWHUWDUWEJUL
          VVCYKFUFUWFUWIUWJVVBWUODVVTOVYCVVAVWDEHVYDUWKXMUWLWUIWUOWVCWUIVWAWUOA
          VWAYFXIUWMUWNWUIFULXRZVVDWVBWUCYEAWVDVWAAVUMWVDVYTULVULFXSXFYHWVDVVDV
          FZWVAVUOVVTWVEWVAVUNVEWVAVUOURULVUTFUWOWVAVUNYLXFYMYOUWQXKUWPYPYQYPYJ
          YQBOVUOUWRVJUWSVXLOUJUKZVUMVUPVFVUBVXMVXGIYNUHZOVEWVFVXHIOWVGRWVGWEYB
          OWVGUWTWRGKLFOUAUXGUXAUXBAVUAVUKKULAUYRULVEZVFZVUCUYTVEZCYRVUCOVEZVUJ
          VFZCYRVUAVUKWVIWVJWVLCWVIWVJWVKVUJWVIUYTOVUCWVIVYQUYSOURZUYTOURZVYRAV
          UMWVHWVMVYTVUMWVHVFZUYSOWVOVULWUAUYSWUBULVULUYRFUXCUXDUXEYOZUYSLOVYSU
          XFYIYMWVIWVJVUJWVIWVJVFVUCVVTGUXHUHUNZUYTURZBUSUMZVUJWVIUYTLVEZWVJWVS
          WVIVYQWVMWVTVYRWVPUYSLOVYSUXIYIZVXKWVTWVJWVSVXNBUYTGVUCLOUAUXJUXKYOWV
          IWVJWVKWVSVUJYEWVIUYTOVUCWVIWVTWVNWWAWVTUYTLVBOUYTLYLVYSUXLXFWCWVIWVK
          VFZWVRVUJBUSWWBVVTUSVEZVFZWVRWVQUYSURZVUEVVTUXQUXMUNZUOUPZDOUQZUYSURZ
          VUJWVIWVRWWEYEWVKWWCWVIUYTUYSURZWVRWWEWVIVYQWVMWWJVYRWVPUYSLOVYSUXNYI
          WVQUYTUYSYSUXOUXPWWDWWHWVQURZWWEWWIYEWWBVXKWVKVFWWFXTVEZVVTXTVEZWWFVV
          TYDUPZUXRWWKWWCWWBWVKVXKWVIWVKYFVXNUXSWWCWWLWWMWWNWWCWWFVVTUXTZUYAVVT
          UYBVVTUYCUYDDGVUCWWFWWHVVTLOUAWWHWEUYEYGWWHWVQUYSYSXFWWDWWFUSVEZWWIVU
          JYEWWCWWPWWBWWOVNWWPWWIVUJVUIWWIPWWFUSVUFWWFVCZVUHWWHUYSWWQVUGWWGDOVU
          FWWFVUEUOUYFUYGUYHUYIYTXFUYJYPUYKYQYTUYLUYMCUYTUYNVUJCOUYOUYPUYQYQ $.

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
          rpdivcld rpred wa cnmcv c1 cns cpv crab wss rabss sylib ad2antrr ccbn
          wi cnv bnnv ax-mp a1i rpcnd simpr eqid nvscl syl3anc nvgcl wceq oveq2
          cc crp breq1d eleq1 imbi12d rspccv sylc cmul cnsb cxmt cms cme cbncms
          cmetmet metxmet mp2b xmetsym imsdval nvpncan2 fveq2d 3eqtrd cc0 eqtrd
          rprege0d nvsge0 mulid1d eqcomd breq12d nvcl mpan adantl wb cn ralbidv
          breq2 cba fveq2 elrab sylancr adantr ccld mopntopon ffvelrnd syl32anc
          syl ctopon syld ralrimiva syl2anc 1re lemul2d bitr4d rabbidv cvv fvex
          eqeltri rabex fvmpt eleq2d syl6bb 3imtr3d com12 ad2antlr xmet0 rpge0d
          rsp eqbrtrd sylanbrc sseldd eleqtrd simprd r19.21bi wf ccnv cima cims
          cmopn cblo sselda ccn blocn2 imsxmet iscncl mp2an simpld nnred le2add
          syl22anc mpan2d clno mp3an12 lnosub lnomul 3eqtr3d ffvelrnda eqbrtrrd
          bloln nvmtri remulcld readdcld letr mpand lemuldiv2d sylibd cxr rpxrd
          adantld nmoubi mpbird rspcev ) AMMULUMZHUNUMZUOUPDUQZJOURUMZUSZUXCUTV
          AZDIVBZUXFRUQZUTVAZDIVBZRUOVCAUXCAUXBHAMMAMUHVDZUXLVEZUJVFZVGAUXGDIAU
          XDIUPZVHZUXGBUQZJVIUSZUSZVJUTVAZUXQUXDUSZNUSZUXCUTVAZVSZBPVBZUXPUYDBP
          UXPUXQPUPZVHZUXTGHUXQJVKUSZUMZJVLUSZUMZPUPZUYKUXDUSZNUSZMUTVAZDIVBZVH
          ZUYCUYGGUYKFUMZHUTVAZUYKMEUSZUPZUXTUYQUYGGCUQZFUMZHUTVAZVUBUYTUPZVSZC
          PVBZUYLUYSVUAVSZAVUGUXOUYFAVUDCPVMZUYTVNVUGUKVUDCPUYTVOVPVQUYGJVTUPZG
          PUPZUYIPUPZUYLVUJUYGJVRUPZVUJUCJWAWBZWCZAVUKUXOUYFUIVQZUYGVUJHWLUPZUY
          FVULVUOUYGHAHWMUPUXOUYFUJVQZWDZUXPUYFWEZHUXQUYHJPSUYHWFZWGWHZGUYIJUYJ
          PSUYJWFZWIWHZVUFVUHCUYKPVUBUYKWJZVUDUYSVUEVUAVVEVUCUYRHUTVUBUYKGFWKWN
          VUBUYKUYTWOWPWQWRUYGUYSHUXSWSUMZHVJWSUMZUTVAUXTUYGUYRVVFHVVGUTUYGUYRU
          YIUXRUSZVVFUYGUYRUYKGFUMZUYKGJWTUSZUMZUXRUSZVVHUYGFPXAUSUPZVUKUYLUYRV
          VIWJVVMUYGFPXBUSUPZFPXCUSUPVVMVUMVVNUCFJPSUAXDWBFPXEFPXFXGZWCVUPVVDGU
          YKFPXHWHUYGVUJUYLVUKVVIVVLWJVUOVVDVUPUYKGFJVVJUXRPSVVJWFZUXRWFZUAXIWH
          UYGVVKUYIUXRUYGVUJVUKVULVVKUYIWJVUOVUPVVBGUYIJUYJVVJPSVVCVVPXJWHZXKXL
          UYGVUJHUOUPXMHUTVAVHZUYFVVHVVFWJVUOUYGHVURXOZVUTHUXQUYHJUXRPSVVAVVQXP
          WHXNUYGVVGHUYGHVUSXQXRXSUYGUXSVJHUYFUXSUOUPZUXPVUJUYFVWAVUNUXQJUXRPSV
          VQXTYAYBVJUOUPUYGUUAWCVURUUBUUCAVUAUYQYCUXOUYFAVUAUYKVUBUXDUSZNUSZMUT
          VAZDIVBZCPVMZUPUYQAUYTVWFUYKAMYDUPUYTVWFWJUHKMVWCKUQZUTVAZDIVBZCPVMVW
          FYDEVWGMWJZVWIVWECPVWJVWHVWDDIVWGMVWCUTYFYEUUDUGVWECPPJYGUSUUESJYGUUF
          UUGUUHUUIYPZUUJVWEUYPCUYKPVVEVWDUYODIVVEVWCUYNMUTVVEVWBUYMNVUBUYKUXDY
          HXKWNYEYIUUKVQUULUYGUYPUYCUYLUYGUYPUYOUYCUXOUYPUYOVSAUYFUYPUXOUYOUYOD
          IUUQUUMUUNUYGUYOHUYBWSUMZUXBUTVAZUYCUYGUYOUYNGUXDUSZNUSZULUMZUXBUTVAZ
          VWMUYGUYOVWOMUTVAZVWQUXPVWRUYFAVWRDIAVUKVWRDIVBZAGVWFUPVUKVWSVHAGUYTV
          WFAVUIUYTGUKAVUKGGFUMZHUTVAZGVUIUPUIAVWTXMHUTAVVMVUKVWTXMWJVVOUIGFPUU
          OYJAHUJUUPUURVUDVXACGPVUBGWJZVUCVWTHUTVUBGGFWKWNYIUUSUUTVWKUVAVWEVWSC
          GPVXBVWDVWRDIVXBVWCVWOMUTVXBVWBVWNNVUBGUXDYHXKWNYEYIVPUVBUVCYKUYGUYNU
          OUPZVWOUOUPZMUOUPZVXEUYOVWRVHVWQVSUYGOVTUPZUYMOYGUSZUPZVXCUDUYGPVXGUY
          KUXDUXPPVXGUXDUVDZUYFUXPVXIUXDUVEUXQUVFLYLUSUPBOUVGUSZUVHUSZYLUSVBZUX
          PUXDJOUVIUMZUPZVXIVXLVHZAIVXMUXDUEUVJZVXNUXDLVXKUVKUMUPZVXOVXMFVXJUXD
          JLVXKOUAVXJWFZUBVXKWFZVXMWFZVUNUDUVLLPYQUSUPZVXKVXGYQUSUPZVXQVXOYCVVM
          VYAVVOFLPUBYMWBVXFVXJVXGXAUSUPVYBUDVXJOVXGVXGWFZVXRUVMVXJVXKVXGVXSYMX
          GBUXDLVXKPVXGUVNUVOVPYPUVPZYKZVVDYNZUYMONVXGVYCTXTYJZUYGVXFVWNVXGUPZV
          XDUDUYGPVXGGUXDVYEVUPYNZVWNONVXGVYCTXTYJZAVXEUXOUYFAMUHUVQVQZVYKUYNVW
          OMMUVRUVSUVTUYGVWLVWPUTVAZVWQVWMUYGUYMVWNOWTUSZUMZNUSZVWLVWPUTUYGVYOH
          UYAOVKUSZUMZNUSZVWLUYGVYNVYQNUYGVVKUXDUSZUYIUXDUSZVYNVYQUYGVVKUYIUXDV
          VRXKUYGVUJVXFUXDJOUWAUMZUPZUYLVUKVYSVYNWJVUOVXFUYGUDWCZUXPWUBUYFUXPVX
          NWUBVXPVUJVXFVXNWUBVUNUDVXMUXDJWUAOWUAWFZVXTUWHUWBYPYKZVVDVUPUYKGUXDJ
          WUAVVJVYMOPSVVPVYMWFZWUDUWCYOUYGVUJVXFWUBVUQUYFVYTVYQWJVUOWUCWUEVUSVU
          THUXQUYHVYPUXDJWUAOPSVVAVYPWFZWUDUWDYOUWEXKUYGVXFVVSUYAVXGUPZVYRVWLWJ
          WUCVVTUXPPVXGUXQUXDVYDUWFZHUYAVYPONVXGVYCWUGTXPWHXNUYGVXFVXHVYHVYOVWP
          UTVAWUCVYFVYIUYMVWNOVYMNVXGVYCWUFTUWIWHUWGUYGVWLUOUPVWPUOUPUXBUOUPZVY
          LVWQVHVWMVSUYGHUYBUYGHVURVGUYGVXFWUHUYBUOUPUDWUIUYAONVXGVYCTXTYJZUWJU
          YGUYNVWOVYGVYJUWKAWUJUXOUYFAUXBUXMVGVQZVWLVWPUXBUWLWHUWMYRUYGUYBUXBHW
          UKWULVURUWNUWOYRUWRYRYSUXPVXIUXCUWPUPZUXGUYEYCVYDAWUMUXOAUXCUXNUWQYKB
          UXCUXDJUXRNUXEOPVXGSVYCVVQTUXEWFVUNUDUWSYTUWTYSUXKUXHRUXCUOUXIUXCWJUX
          JUXGDIUXIUXCUXFUTYFYEUXAYT $.
      $}

      $d d ph $.
      $( Lemma for ~ ubth .  Prove the reverse implication, using ~ nmblolbi .
         (Contributed by Mario Carneiro, 11-Jan-2014.)
         (New usage is discouraged.) $)
      ubthlem3 $p |- ( ph ->
                ( A. x e. X E. c e. RR A. t e. T ( N ` ( t ` x ) ) <_ c <->
                  E. d e. RR A. t e. T ( ( U normOpOLD W ) ` t ) <_ d ) ) $=
        ( cle vz vu vy vr vn vm vk cv cfv wbr wral cr wrex cnmoo co wceq fveq2d
        fveq1 breq1d cbvralv breq2 ralbidv syl5bb cbvrexv fveq2 rexralbidv crab
        wa cmpt wss crp cblo adantr simpr sylib cbvrabv rabbidv syl5eq ubthlem1
        cn cbvmptv wcel ad3antrrr ad2antrr simplrl simplrr simprl ubthlem2 expr
        simprr rexlimdva rexlimdvva mpd syl5bir cnmcv cmul ccbn bnnv ax-mp eqid
        ex cnv nvcl mpan remulcl syl2an wf sselda adantlr ad2ant2r blof mp3an12
        cba syl simplr ffvelrnd cxr cmnf clt simpllr nmogtmnf syl22anc ad2antlr
        nmoxr xrre syl2anc nmblolbi cc0 nvge0 jca lemul1a syl31anc letrd rspcev
        ralimdva ee12an ralrimdva impbid ) ABUHZCUHZUIZHUIZKUHZTUJZCEUKZKULUMZB
        JUKZYTFIUNUOZUIZLUHZTUJZCEUKZLULUMZUUGUAUHZUBUHZUIZHUIZUUJTUJZUBEUKZLUL
        UMZUAJUKZAUUMUUTUUFUABJUUTUUNYTUIZHUIZUUCTUJZCEUKZKULUMUUNYSUPZUUFUUSUV
        ELKULUUSUVCUUJTUJZCEUKUUJUUCUPZUVEUURUVGUBCEUUOYTUPZUUQUVCUUJTUVIUUPUVB
        HUUNUUOYTURUQUSUTUVHUVGUVDCEUUJUUCUVCTVAVBVCVDUVFUVDUUDKCULEUVFUVCUUBUU
        CTUVFUVBUUAHUUNYSYTVEUQUSVFVCUTZAUVAUUMAUVAVHZUCUHZUUNDUOUDUHZTUJUAJVGU
        EUHZUFVTUUJUUOUIZHUIZUFUHZTUJZUBEUKZLJVGZVIZUIVJZUDVKUMZUCJUMUEVTUMUUMU
        VKBUCUACUWADEFUGUEGHIJUDKMNOPQRAEFIVLUOZVJZUVASVMUVKUVAUUGAUVAVNUVJVOZU
        FUGVTUVTUVCUGUHZTUJZCEUKZUAJVGZUVQUWGUPZUVTUVCUVQTUJZCEUKZUAJVGUWJUVSUW
        MLUAJUVSUUJYTUIZHUIZUVQTUJZCEUKUUJUUNUPZUWMUVRUWPUBCEUVIUVPUWOUVQTUVIUV
        OUWNHUUJUUOYTURUQUSUTUWQUWPUWLCEUWQUWOUVCUVQTUWQUWNUVBHUUJUUNYTVEUQUSVB
        VCVPUWKUWMUWIUAJUWKUWLUWHCEUVQUWGUVCTVAVBVQVRWAZVSUVKUWCUUMUEUCVTJUVKUV
        NVTWBZUVLJWBZVHZVHZUWBUUMUDVKUXBUVMVKWBZUWBUUMUXBUXCUWBVHZVHBUACUWADUVL
        UVMEFUGGUVNHIJKLMNOPQRAUWEUVAUXAUXDSWCUVKUUGUXAUXDUWFWDUWRUVKUWSUWTUXDW
        EUVKUWSUWTUXDWFUXBUXCUWBWGUXBUXCUWBWJWHWIWKWLWMXAWNAUULUUGLULAUUJULWBZV
        HZUULUUFBJUXFYSJWBZVHZUUJYSFWOUIZUIZWPUOZULWBZUULUUBUXKTUJZCEUKZUUFUXFU
        XEUXJULWBZUXLUXGAUXEVNFXBWBZUXGUXOFWQWBUXPQFWRWSZYSFUXIJMUXIWTZXCXDZUUJ
        UXJXEXFZUXHUUKUXMCEUXHYTEWBZUUKUXMUXHUYAUUKVHZVHZUUBUUIUXJWPUOZUXKUYCUU
        AIXMUIZWBZUUBULWBZUYCJUYEYSYTUYCYTUWDWBZJUYEYTXGZUXFUYAUYHUXGUUKAUYAUYH
        UXEAEUWDYTSXHXIXJZUXPIXBWBZUYHUYIUXQRUWDYTFIJUYEMUYEWTZUWDWTZXKXLXNZUXF
        UXGUYBXOZXPUYKUYFUYGRUUAIHUYEUYLNXCXDXNUYCUUIULWBZUXOUYDULWBUYCUUIXQWBZ
        UXEXRUUIXSUJZUUKUYPUYCUYIUYQUYNUXPUYKUYIUYQUXQRYTFUUHIJUYEMUYLUUHWTZYDX
        LXNAUXEUXGUYBXTZUYCUYIUYRUYNUXPUYKUYIUYRUXQRYTFUUHIJUYEMUYLUYSYAXLXNUXH
        UYAUUKWJZUUIUUJYEYBZUXGUXOUXFUYBUXSYCUUIUXJXEYFUXHUXLUYBUXTVMUYCUYHUXGU
        UBUYDTUJUYJUYOYSUWDYTFUXIHUUHIJMUXRNUYSUYMUXQRYGYFUYCUYPUXEUXOYHUXJTUJZ
        VHZUUKUYDUXKTUJVUBUYTUXGVUDUXFUYBUXGUXOVUCUXSUXPUXGVUCUXQYSFUXIJMUXRYIX
        DYJYCVUAUUIUUJUXJYKYLYMWIYOUUEUXNKUXKULUUCUXKUPUUDUXMCEUUCUXKUUBTVAVBYN
        YPYQWKYR $.
    $}

    ubth.3 $e |- M = ( U normOpOLD W ) $.
    $( Uniform Boundedness Theorem, also called the Banach-Steinhaus Theorem.
       Let ` T ` be a collection of bounded linear operators on a Banach
       space.  If, for every vector ` x ` , the norms of the operators' values
       are bounded, then the operators' norms are also bounded.  Theorem 4.7-3
       of [Kreyszig] p. 249.  See also
       ~ http://en.wikipedia.org/wiki/Uniform_boundedness_principle .
       (Contributed by NM, 7-Nov-2007.)  (Proof shortened by Mario Carneiro,
       11-Jan-2014.)  (New usage is discouraged.) $)
    ubth $p |- ( ( U e. CBan /\ W e. NrmCVec /\ T C_ ( U BLnOp W ) ) ->
                 ( A. x e. X E. c e. RR A. t e. T ( N ` ( t ` x ) ) <_ c <->
                   E. d e. RR A. t e. T ( M ` t ) <_ d ) ) $=
      ( cblo co cfv cle wbr wral cr ccbn wcel cnv wss cv wrex wb caddc cmul cop
      wi cabs cif cba cnmoo cnmcv wceq oveq1 sseq2d fveq2 syl5eq raleqdv fveq1d
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
        ( cr wss c0 wne cc0 cv cle wbr wral co cfv cmpt crn wf wcel wa cnv phnv
        ccphlo syl adantr css ccbn elin sylib simpld sspba syl2anc sselda nvmcl
        cin eqid syl3anc nvcl fmptd frn syl5eqss cdm cn0v simprd bnnv 3syl fvex
        dmmpti syl6eleqr ne0i wceq dm0rn0 eqeq1i bitr4i necon3bii ralrimiva cvv
        nvzcl nvge0 wb rgenw breq2 ralrnmpt ax-mp sylibr raleqi 3jca ) AFUDUEFU
        FUGZUHCUIZUJUKZCFULZAFBMDBUIZIUMZJUNZUOZUPZUDUCAMUDXNUQXOUDUEABMXMUDXNA
        XKMURZUSZGUTURZXLLURZXMUDURAXRXPAGVBURXRRGVAVCZVDZXQXRDLURZXKLURXSYAAYB
        XPTVDAMLXKAXRKGVEUNZURZMLUEXTAYDKVFURZAKYCVFVNURYDYEUSSKYCVFVGVHZVIGYCK
        LMNQYCVOVJVKVLDXKGILNOVMVPZXLGJLNPVQVKXNVOZVRMUDXNVSVCVTAXNWAZUFUGZXGAK
        WBUNZYIURYJAYKMYIAYEKUTURYKMURAYDYEYFWCKWDKMYKQYKVOWQWEBMXMXNXLJWFZYHWG
        WHYIYKWIVCYIUFFUFYIUFWJXOUFWJFUFWJXNWKFXOUFUCWLWMWNVHAXICXOULZXJAUHXMUJ
        UKZBMULZYMAYNBMXQXRXSYNYAYGXLGJLNPWRVKWOXMWPURZBMULYMYOWSYPBMYLWTXIYNBC
        MXMXNWPYHXHXMUHUJXAXBXCXDXICFXOUCXEXDXF $.

      minveco.s $e |- S = sup ( R , RR , `' < ) $.
      ${
        minvecolem2.1 $e |- ( ph -> B e. RR ) $.
        minvecolem2.2 $e |- ( ph -> 0 <_ B ) $.
        minvecolem2.3 $e |- ( ph -> K e. Y ) $.
        minvecolem2.4 $e |- ( ph -> L e. Y ) $.
        minvecolem2.5 $e |- ( ph -> ( ( A D K ) ^ 2 ) <_ ( ( S ^ 2 ) + B ) ) $.
        minvecolem2.6 $e |- ( ph -> ( ( A D L ) ^ 2 ) <_ ( ( S ^ 2 ) + B ) ) $.
        $( Lemma for ~ minveco .  Any two points ` K ` and ` L ` in ` Y ` are
           close to each other if they are close to the infimum of distance to
           ` A ` .  (Contributed by Mario Carneiro, 9-May-2014.)
           (New usage is discouraged.) $)
        minvecolem2 $p |- ( ph -> ( ( K D L ) ^ 2 ) <_ ( 4 x. B ) ) $=
          ( vx vw co c2 cexp c4 cmul cle wbr caddc c1 cdiv cpv cfv cns wcel 4re
          cr clt ccnv csup wss c0 wne cv wral cc0 minvecolem1 simp1d simp2d 0re
          wrex simp3d wceq breq1 ralbidv rspcev sylancr infmrcl syl3anc resqcld
          syl5eqel remulcl cme cnv ccphlo phnv syl imsmet css ccbn inss1 sseldi
          cin eqid sspba syl2anc sseldd metcl readdcld cc ax-1cn syl22anc nvgcl
          eqeltrrd nvmcl wb a1i mpbird fveq2d wa pm3.2i lemul2 mp3an3 mpbid 2re
          2pos 2cn oveq1i syl6eq syl13anc eqtr3d oveq12d oveq1d imsdval 3eqtr4d
          recnd halfcl mp1i sspgval sspnv sspsval nvscl nvcl infmrgelb syl31anc
          syl6breqr cmpt crn oveq2 eqeq2d sylancl fvex sylibr syl6eleqr infmrlb
          elrnmpti syl5eqbr le2sq2 4pos leadd1dd le2addd 2timesd breqtrrd sqmul
          phpar2 sq2 cabs nvs ltleii absid mp2an nvmdi 2ne0 recidi nvsid syl5eq
          nv2 nvsass nvaddsub4 syl122anc 3eqtr2d metsym nvnnncan1 2t2e4 mulassd
          oveq2d syl5eqr 3brtr4d letrd 4cn adddid breqtrd leadd2d ) AJKEUPZUQUR
          UPZUSDUTUPZVAVBUSGUQURUPZUTUPZUWSVCUPZUXBUWTVCUPZVAVBAUXCUSUXADVCUPZU
          TUPZUXDVAAUXCUSCVDUQVEUPZJKHVFVGZUPZHVHVGZUPZLUPZMVGZUQURUPZUTUPZUWSV
          CUPZUXFAUXBUWSAUSVKVIZUXAVKVIZUXBVKVIVJAGAGFVKVLVMVNZVKUGAFVKVOZFVPVQ
          ZUNVRZUOVRZVAVBZUOFVSZUNVKWEZUXSVKVIAUXTUYAVTUYCVAVBZUOFVSZABUOCEFHIL
          MNOPQRSTUAUBUCUDUEUFWAZWBZAUXTUYAUYHUYIWCZAVTVKVIZUYHUYFWDAUXTUYAUYHU
          YIWFZUYEUYHUNVTVKUYBVTWGUYDUYGUOFUYBVTUYCVAWHWIWJWKZUNUOFWLWMWOZWNZUS
          UXAWPWKZAUWRAEOWQVGVIZJOVIZKOVIZUWRVKVIAHWRVIZUYRAHWSVIZVUAUAHWTXAZEH
          OQUDXBXAZAPOJAVUANHXCVGZVIZPOVOVUCAVUEXDXGVUENVUEXDXEUBXFZHVUENOPQTVU
          EXHZXIXJZUJXKZAPOKVUIUKXKZJKEOXLWMWNZXMAUXOUWSAUXQUXNVKVIZUXOVKVIVJAU
          XMAVUAUXLOVIZUXMVKVIZVUCAVUACOVIZUXKOVIZVUNVUCUCAPOUXKVUIAUXGUXINVHVG
          ZUPZUXKPAVUAVUFUXGXNVIZUXIPVIZVUSUXKWGVUCVUGVDXNVIVUTAXOVDUUAUUBZAJKN
          VFVGZUPZUXIPAVUAVUFJPVIZKPVIZVVDUXIWGVUCVUGUJUKJKHVVCUXHVUENPTUXHXHZV
          VCXHZVUHUUCXPANWRVIZVVEVVFVVDPVIAVUAVUFVVIVUCVUGHVUENVUHUUDXJZUJUKJKN
          VVCPTVVHXQWMXRZUXGUXIVURUXJHVUENPTUXJXHZVURXHZVUHUUEXPAVVIVUTVVAVUSPV
          IVVJVVBVVKUXGUXIVURNPTVVMUUFWMXRZXKZCUXKHLOQRXSWMZUXLHMOQSUUGXJZWNZUS
          UXNWPWKZVULXMAUXQUXEVKVIZUXFVKVIVJAUXADUYPUHXMZUSUXEWPWKAUXBUXOUWSUYQ
          VVSVULAUXAUXNVAVBZUXBUXOVAVBZAGVKVIVTGVAVBVUOGUXMVAVBVWBUYOAVTUXSGVAA
          VTUXSVAVBZUYHUYMAUXTUYAUYFUYLVWDUYHXTUYJUYKUYNUYLAWDYAUNUOUOFVTUUHUUI
          YBUGUUJVVQAGUXSUXMVAUGAUXTUYFUXMFVIUXSUXMVAVBUYJUYNAUXMBPCBVRZLUPZMVG
          ZUUKZUULZFAUXMVWGWGZBPWEZUXMVWIVIAUXKPVIUXMUXMWGZVWKVVNUXMXHVWJVWLBUX
          KPVWEUXKWGZVWGUXMUXMVWMVWFUXLMVWEUXKCLUUMYCUUNWJUUOBPVWGUXMVWHVWHXHVW
          FMUUPUUTUUQUFUURUNUOUXMFUUSWMUVAGUXMUVBXPAUXRVUMVWBVWCXTZUYPVVRUXRVUM
          UXQVTUSVLVBZYDVWNUXQVWOVJUVCYEUXAUXNUSYFYGXJYHUVDAUQCJEUPZUQURUPZCKEU
          PZUQURUPZVCUPZUTUPZUQUQUXEUTUPZUTUPZUXPUXFVAAVWTVXBVAVBZVXAVXCVAVBZAV
          WTUXEUXEVCUPVXBVAAVWQVWSUXEUXEAVWPAUYRVUPUYSVWPVKVIVUDUCVUJCJEOXLWMWN
          ZAVWRAUYRVUPUYTVWRVKVIVUDUCVUKCKEOXLWMWNZVWAVWAULUMUVEAUXEAUXEVWAYTZU
          VFUVGAVWTVKVIZVXBVKVIZVXDVXEXTZAVWQVWSVXFVXGXMAUQVKVIZVVTVXJYIVWAUQUX
          EWPWKVXIVXJVXLVTUQVLVBZYDVXKVXLVXMYIYJYEVWTVXBUQYFYGXJYHACJLUPZCKLUPZ
          UXHUPZMVGZUQURUPZVXNVXOLUPZMVGZUQURUPZVCUPZUQVXNMVGZUQURUPZVXOMVGZUQU
          RUPZVCUPZUTUPZUXPVXAAVUBVXNOVIZVXOOVIZVYBVYHWGUAAVUAVUPUYSVYIVUCUCVUJ
          CJHLOQRXSWMAVUAVUPUYTVYJVUCUCVUKCKHLOQRXSWMVXNVXOHUXHLMOQVVGRSUVIWMAU
          XOVXRUWSVYAVCAUQUXMUTUPZUQURUPZUXOVXRAVYLUQUQURUPZUXNUTUPZUXOAUQXNVIZ
          UXMXNVIVYLVYNWGYKAUXMVVQYTUQUXMUVHWKVYMUSUXNUTUVJYLYMAVYKVXQUQURAUQUX
          LUXJUPZMVGZVYKVXQAVYQUQUVKVGZUXMUTUPZVYKAVUAVYOVUNVYQVYSWGVUCVYOAYKYA
          ZVVPUQUXLUXJHMOQVVLSUVLWMVYRUQUXMUTVXLVTUQVAVBVYRUQWGYIVTUQWDYIYJUVMU
          QUVNUVOYLYMAVYPVXPMAVYPUQCUXJUPZUQUXKUXJUPZLUPZCCUXHUPZUXILUPZVXPAVUA
          VYOVUPVUQVYPWUCWGVUCVYTUCVVOUQCUXKUXJHLOQRVVLUVPYNAWUDWUAUXIWUBLAVUAV
          UPWUDWUAWGVUCUCCUXJHUXHOQVVGVVLUWAXJAUQUXGUTUPZUXIUXJUPZUXIWUBAWUGVDU
          XIUXJUPZUXIWUFVDUXIUXJUQYKUVQUVRYLAVUAUXIOVIZWUHUXIWGVUCAVUAUYSUYTWUI
          VUCVUJVUKJKHUXHOQVVGXQWMZUXIUXJHOQVVLUVSXJUVTAVUAVYOVUTWUIWUGWUBWGVUC
          VYTVVBWUJUQUXGUXIUXJHOQVVLUWBYNYOYPAVUAVUPVUPUYSUYTWUEVXPWGVUCUCUCVUJ
          VUKCCJKHUXHLOQVVGRUWCUWDUWEYCYOYQYOAUWRVXTUQURAKJEUPZKJLUPZMVGZUWRVXT
          AVUAUYTUYSWUKWUMWGVUCVUKVUJKJEHLMOQRSUDYRWMAUYRUYSUYTUWRWUKWGVUDVUJVU
          KJKEOUWFWMAVXSWULMAVUAVUPUYSUYTVXSWULWGVUCUCVUJVUKCJKHLOQRUWGYNYCYSYQ
          YPAVWTVYGUQUTAVWQVYDVWSVYFVCAVWPVYCUQURAVUAVUPUYSVWPVYCWGVUCUCVUJCJEH
          LMOQRSUDYRWMYQAVWRVYEUQURAVUAVUPUYTVWRVYEWGVUCUCVUKCKEHLMOQRSUDYRWMYQ
          YPUWJYSAUXFUQUQUTUPZUXEUTUPVXCWUNUSUXEUTUWHYLAUQUQUXEVYTVYTVXHUWIUWKU
          WLUWMAUSUXADUSXNVIAUWNYAAUXAUYPYTADUHYTUWOUWPAUWSUWTUXBVULAUXQDVKVIUW
          TVKVIVJUHUSDWPWKUYQUWQYB $.
      $}

      ${
        minveco.f $e |- ( ph -> F : NN --> Y ) $.
        minveco.1 $e |- ( ( ph /\ n e. NN ) ->
            ( ( A D ( F ` n ) ) ^ 2 ) <_ ( ( S ^ 2 ) + ( 1 / n ) ) ) $.
        $( Lemma for ~ minveco .  The sequence formed by taking elements
           successively closer to the infimum is Cauchy.  (Contributed by Mario
           Carneiro, 8-May-2014.)  (New usage is discouraged.) $)
        minvecolem3 $p |- ( ph -> F e. ( Cau ` D ) ) $=
          ( vj vx vw cca cfv wcel cv co clt wbr cuz wral cn wrex crp wa c4 cexp
          c2 cdiv cfl c1 caddc cr cc0 cle cn0 4pos elrpii simpr rpexpcl sylancl
          4re rpdivcl sylancr rprege0 flge0nn0 nn0p1nn 4syl cmul cme ccphlo cnv
          cz 2z phnv imsmet 3syl ad2antrr wss css syl ccbn cin inss1 eqid sspba
          sseldi syl2anc adantr ffvelrnd sseldd nnuz uztrn2 sylan metcl syl3anc
          resqcld nnrpd rpreccld rpmulcl rpge0d ffvelrnda syldan ralrimiva wceq
          wf rpred fveq2 oveq2d oveq1d oveq2 breq12d wne w3a rspcev readdcld wb
          cc rpcnne0 mpbird eqidd rspcv sylc ccnv csup c0 minvecolem1 0re breq1
          ralbidv mpan 3anim3i infmrcl syl5eqel nnrecred eluzle adantl rpregt0d
          adantlr nngt0 jca lerec mpbid leadd2dd letrd minvecolem2 ax-mp recdiv
          flltp1 eqbrtrd ltrec1d pm3.2i ltmuldiv2 mp3an3 lelttrd ad2antlr lt2sq
          nnre metge0 syl21anc breq1d raleqbidv cxmt imsxmet 1z a1i fss iscauf
          ) AIDULUMUNUIUOZIUMZHUOZIUMZDUPZUJUOZUQURZHUWHUSUMZUTZUIVAVBZUJVCUTAU
          WQUJVCAUWMVCUNZVDZVEUWMVGVFUPZVHUPZVIUMZVJVKUPZVAUNZUXCIUMZUWKDUPZUWM
          UQURZHUXCUSUMZUTZUWQUWSUXAVCUNZUXAVLUNZVMUXAVNURVDUXBVOUNUXDUWSVEVCUN
          ZUWTVCUNZUXJVEWAVPVQZUWSUWRVGWLUNUXMAUWRVRWMUWMVGVSVTZVEUWTWBWCZUXAWD
          UXAWEUXBWFWGZUWSUXGHUXHUWSUWJUXHUNZVDZUXGUXFVGVFUPZUWTUQURZUXSUXTVEVJ
          UXCVHUPZWHUPZUWTUXSUXFUXSDNWIUMUNZUXENUNZUWKNUNZUXFVLUNZAUYDUWRUXRAGW
          JUNZGWKUNZUYDTGWNZDGNPUCWOWPWQZUXSONUXEAONWRZUWRUXRAUYIMGWSUMZUNUYLAU
          YHUYITUYJWTAUYMXAXBZUYMMUYMXAXCUAXFGUYMMNOPSUYMXDXEXGZWQZUXSVAOUXCIAV
          AOIYEZUWRUXRUGWQZUWSUXDUXRUXQXHZXIZXJZUXSONUWKUYPUXSVAOUWJIUYRUWSUXDU
          XRUWJVAUNZUXQVJUWJUXCVAXKXLXMZXIXJZUXEUWKDNXNXOZXPUXSUYCUXSUXLUYBVCUN
          ZUYCVCUNUXNUXSUXCUXSUXCUYSXQZXRVEUYBXSWCYFUXSUWTUWSUXMUXRUXOXHZYFZUXS
          BCUYBDEFGJUXEUWKKLMNOPQRSAUYHUWRUXRTWQAMUYNUNUWRUXRUAWQACNUNZUWRUXRUB
          WQZUCUDUEUFUXSUYBUWSVUFUXRUWSUXCUWSUXCUXQXQXRXHZYFZUXSUYBVULXTUYTUWSU
          XRVUBUWKOUNVUCUWSVAOUWJIAUYQUWRUGXHYAYBZUXSUXDCUWKDUPZVGVFUPZFVGVFUPZ
          VJUWJVHUPZVKUPZVNURZHVAUTZCUXEDUPZVGVFUPZVUQUYBVKUPZVNURZUYSAVVAUWRUX
          RAVUTHVAUHYCWQVUTVVEHUXCVAUWJUXCYDZVUPVVCVUSVVDVNVVFVUOVVBVGVFVVFUWKU
          XECDUWJUXCIYGYHYIVVFVURUYBVUQVKUWJUXCVJVHYJYHYKUUAUUBUXSVUPVUSVVDUXSV
          UOUXSUYDVUJUYFVUOVLUNUYKVUKUXSONUWKUYPVUNXJCUWKDNXNXOXPUXSVUQVURAVUQV
          LUNUWRUXRAFAFEVLUQUUCUUDZVLUFAEVLWRZEUUEYLZVMUKUOZVNURZUKEUTZYMVVHVVI
          UWMVVJVNURZUKEUTZUJVLVBZYMVVGVLUNABUKCDEGJKLMNOPQRSTUAUBUCUDUEUUFVVLV
          VOVVHVVIVMVLUNVVLVVOUUGVVNVVLUJVMVLUWMVMYDVVMVVKUKEUWMVMVVJVNUUHUUIYN
          UUJUUKUJUKEUULWPUUMXPWQZUXSUWJVUCUUNZYOUXSVUQUYBVVPVUMYOUWSUXRVUBVUTV
          UCAVUBVUTUWRUHUURYBUXSVURUYBVUQVVQVUMVVPUXSUXCUWJVNURZVURUYBVNURZUXRV
          VRUWSUXCUWJUUOUUPUXSUXCVLUNVMUXCUQURVDUWJVLUNZVMUWJUQURZVDZVVRVVSYPUX
          SUXCVUGUUQUXSVUBVWBVUCVUBVVTVWAUWJUVQUWJUUSUUTWTUXCUWJUVAXGUVBUVCUVDU
          VEUXSUYCUWTUQURZUYBUWTVEVHUPZUQURZUXSVWDUXCUXSUXMUXLVWDVCUNVUHUXNUWTV
          EWBVTVUGUXSVJVWDVHUPZUXAUXCUQUXSUWTYQUNUWTVMYLVDZVEYQUNVEVMYLVDZVWFUX
          AYDUXSUXMVWGVUHUWTYRWTUXLVWHUXNVEYRUVFUWTVEUVGVTUXSUXKUXAUXCUQURUXSUX
          AUWSUXJUXRUXPXHYFUXAUVHWTUVIUVJUXSUYBVLUNZUWTVLUNZVWCVWEYPZVUMVUIVWIV
          WJVEVLUNZVMVEUQURZVDVWKVWLVWMWAVPUVKUYBUWTVEUVLUVMXGYSUVNUXSUYGVMUXFV
          NURZUWMVLUNVMUWMVNURVDZUXGUYAYPVUEUXSUYDUYEUYFVWNUYKVUAVUDUXEUWKDNUVR
          XOUWRVWOAUXRUWMWDUVOUXFUWMUVPUVSYSYCUWPUXIUIUXCVAUWHUXCYDZUWNUXGHUWOU
          XHUWHUXCUSYGVWPUWLUXFUWMUQVWPUWIUXEUWKDUWHUXCIYGYIUVTUWAYNXGYCAUJUWKU
          WIDUIHIVJNVAXKAUYHUYIDNUWBUMUNTUYJDGNPUCUWCWPVJWLUNAUWDUWEAVUBVDUWKYT
          AUWHVAUNVDUWIYTAUYQUYLVANIYEUGUYOVAONIUWFXGUWGYS $.

        $( Lemma for ~ minveco . ` F ` is convergent in the subspace topology
           on ` Y ` .  (Contributed by Mario Carneiro, 7-May-2014.)
           (New usage is discouraged.) $)
        minvecolem4a $p |- ( ph -> F
                      ( ~~>t ` ( MetOpen ` ( D |` ( Y X. Y ) ) ) )
                      ( ( ~~>t ` ( MetOpen ` ( D |` ( Y X. Y ) ) ) ) ` F ) ) $=
          ( cxp cres cmopn cfv clm cdm wcel wbr cba cms cca cims cnv css ccphlo
          wceq phnv syl ccbn cin wa elin sylib simpld eqid sspims simprd cbncms
          syl2anc eqeltrrd minvecolem3 cxmt cn wf cme imsmet 3syl metxmet causs
          wb mpbid cmetcau cha wfun xmetres methaus lmfun funfvbrb ) AIDOOUIUJZ
          UKULZUMULZUNUOZIIWSULWSUPZAWQMUQULZURULZUOIWQUSULUOZWTAMUTULZWQXCAGVA
          UOZMGVBULZUOZXEWQVDAGVCUOZXFTGVEZVFAXHMVGUOZAMXGVGVHUOXHXKVIUAMXGVGVJ
          VKZVLXEDGXGMOSUCXEVMZXGVMVNVQAXKXEXCUOAXHXKXLVOXEMXBXBVMXMVPVFVRAIDUS
          ULUOZXDABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHVSADNVTULUOZWAOIWBXNXDWHAD
          NWCULUOZXOAXIXFXPTXJDGNPUCWDWEDNWFVFZUGDINOWGVQWIWQIWRXBWRVMZWJVQAWRW
          KUOZWSWLWTXAWHAXOWQNOVHZVTULUOXSXQDONWMWQWRXTXRWNWEWRWOIWSWPWEWI $.

        $( Lemma for ~ minveco .  The convergent point of the cauchy sequence
           ` F ` is a member of the base space.  (Contributed by Mario
           Carneiro, 16-Jun-2014.)  (New usage is discouraged.) $)
        minvecolem4b $p |- ( ph -> ( ( ~~>t ` J ) ` F ) e. X ) $=
          ( clm cfv cnv wcel css wss ccphlo phnv syl ccbn cin elin sylib simpld
          wa eqid sspba syl2anc cxp cres wfun wbr wceq cha cxmt imsxmet methaus
          cmopn lmfun minvecolem4a crest co c1 cvv cn nnuz cba fvex eqeltri a1i
          ctop mopntop ctopon xmetres2 mopntopon lmcl cz 1z lmss metrest fveq2d
          breqd bitrd mpbird funbrfv sylc eqeltrd sseldd ) AONIJUIUJZUJZAGUKULZ
          MGUMUJZULZONUNZAGUOULXITGUPUQZAXKMURULZAMXJURUSULXKXNVCUAMXJURUTVAVBG
          XJMNOPSXJVDVEVFZAXHIDOOVGVHZVPUJZUIUJZUJZOAXGVIZIXSXGVJZXHXSVKAJVLULZ
          XTADNVMUJULZYBAXIYCXMDGNPUCVNUQZDJNUDVOUQJVQUQAYAIXSXRVJZABCDEFGHIJKL
          MNOPQRSTUAUBUCUDUEUFUGUHVRZAYAIXSJOVSVTZUIUJZVJYEAXSIJYGWAWBOWCYGVDWD
          OWBULAOMWEUJWBSMWEWFWGWHAYCJWIULYDDJNUDWJUQAXQOWKUJULZYEXSOULAXPOVMUJ
          ULZYIAYCXLYJYDXODONWLVFXPXQOXQVDZWMUQYFXSIXQOWNVFZWAWOULAWPWHUGWQAYHX
          RIXSAYGXQUIAYCXLYGXQVKYDXODXPJXQNOXPVDUDYKWRVFWSWTXAXBIXSXGXCXDYLXEXF
          $.

        $( Lemma for ~ minveco .  The infimum of the distances to ` A ` is a
           real number.  (Contributed by Mario Carneiro, 16-Jun-2014.)
           (New usage is discouraged.) $)
        minvecolem4c $p |- ( ph -> S e. RR ) $=
          ( vx vw cr clt ccnv csup wss c0 wne cv cle wral wrex wcel minvecolem1
          wbr cc0 simp1d simp2d 0re simp3d breq1 ralbidv rspcev sylancr infmrcl
          wceq syl3anc syl5eqel ) AFEUKULUMUNZUKUFAEUKUOZEUPUQZUIURZUJURZUSVDZU
          JEUTZUIUKVAZVRUKVBAVSVTVEWBUSVDZUJEUTZABUJCDEGJKLMNOPQRSTUAUBUCUDUEVC
          ZVFAVSVTWGWHVGAVEUKVBWGWEVHAVSVTWGWHVIWDWGUIVEUKWAVEVOWCWFUJEWAVEWBUS
          VJVKVLVMUIUJEVNVPVQ $.

        minveco.t $e |- T = ( 1 /
      ( ( ( ( ( A D ( ( ~~>t ` J ) ` F ) ) + S ) / 2 ) ^ 2 ) - ( S ^ 2 ) ) ) $.
        $( Lemma for ~ minveco .  The convergent point of the cauchy sequence
           ` F ` attains the minimum distance, and so is closer to ` A ` than
           any other point in ` Y ` .  (Contributed by Mario Carneiro,
           7-May-2014.)  (New usage is discouraged.) $)
        minvecolem4 $p |- ( ph -> E. x e. Y A. y e. Y
                          ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) ) $=
          ( vw clm cfv wcel co cv cle wbr wral wrex cxp cres wfun wceq cxmt cha
          cmopn ccphlo cnv phnv imsxmet methaus lmfun minvecolem4a crest c1 cvv
          3syl cn eqid nnuz cba fvex eqeltri a1i syl mopntop ctopon wss css cin
          ctop ccbn wa elin sylib simpld sspba syl2anc xmetres2 mopntopon cz 1z
          lmcl metrest fveq2d breqd bitrd mpbird funbrfv eqeltrd syl3anc adantr
          lmss sylc cr metcl clt caddc cdiv cc0 cexp crp readdcld resqcld recnd
          c2 2timesd breq1d wb 3bitr2d 0re ralbidv rspcev metge0 ad2antrr letrd
          cmul wf minvecolem4b imsdval imsmet minvecolem4c sselda nvmcl nvcl wn
          cme ltnled cfl cuz cn0 cmin rehalfcld resubcld ltadd1d 2pos ltmuldiv2
          2re pm3.2i ccnv c0 wne minvecolem1 simp3d simp1d simp2d breq1 sylancr
          csup infmrgelb syl31anc addge0d divge0 syl21anc lt2sqd posdifd 3bitrd
          syl6breqr biimpa rpreccld syl5eqel rprege0d flge0nn0 nn0p1nn breqtrrd
          elrpd rexrd simpll uztrn2 sylan fss ffvelrnda nnrecred rpred peano2re
          nnzd reflcl nnred fllep1 eluzle adantl syl5eqbrr 1re nngt0d syl122anc
          lediv23 mpbid leaddsub2d le2sqd lmle leadd2d lemuldiv2 mp3an3 biimpar
          syldan ex sylbird pm2.18d cmpt crn elrnmpt1 sylancl syl6eleqr infmrlb
          simpr syl5eqbr eqbrtrrd ralrimiva oveq2 ) AKLUMUNZUNZQUODUYMMUPZNUNZD
          CUQZMUPZNUNZURUSZCQUTZDBUQZMUPZNUNZUYRURUSZCQUTZBQVAAUYMKEQQVBVCZVHUN
          ZUMUNZUNZQAUYLVDZKVUIUYLUSZUYMVUIVEAEPVFUNUOZLVGUOVUJAIVIUOZIVJUOZVUL
          UBIVKZEIPRUEVLZVSZELPUFVMLVNVSAVUKKVUIVUHUSZACDEFGIJKLMNOPQRSTUAUBUCU
          DUEUFUGUHUIUJVOZAVUKKVUILQVPUPZUMUNZUSVURAVUIKLVUTVQVRQVTVUTWAWBQVRUO
          AQOWCUNVRUAOWCWDWEWFAVUNVULLWMUOAVUMVUNUBVUOWGZVUPELPUFWHVSAVUGQWIUNU
          OZVURVUIQUOAVUFQVFUNUOZVVCAVULQPWJZVVDVUQAVUNOIWKUNZUOZVVEVVBAVVGOWNU
          OZAOVVFWNWLUOVVGVVHWOUCOVVFWNWPWQWRIVVFOPQRUAVVFWAWSWTZEQPXAWTVUFVUGQ
          VUGWAZXBWGVUSVUIKVUGQXEWTZVQXCUOAXDWFUIXOAVVAVUHKVUIAVUTVUGUMAVULVVEV
          UTVUGVEVUQVVIEVUFLVUGPQVUFWAUFVVJXFWTXGXHXIXJZKVUIUYLXKXPZVVKXLAUYSCQ
          AUYPQUOZWOZDUYMEUPZUYOUYRURAVVPUYOVEZVVNAVUNDPUOZUYMPUOZVVQVVBUDACDEF
          GIJKLMNOPQRSTUAUBUCUDUEUFUGUHUIUJUUAZDUYMEIMNPRSTUEUUBXMXNVVOVVPGUYRA
          VVPXQUOZVVNAEPUUIUNUOZVVRVVSVWAAVUMVUNVWBUBVUOEIPRUEUUCVSZUDVVTDUYMEP
          XRXMZXNAGXQUOZVVNACDEFGIJKLMNOPQRSTUAUBUCUDUEUFUGUHUIUJUUDZXNVVOVUNUY
          QPUOZUYRXQUOAVUNVVNVVBXNZVVOVUNVVRUYPPUOVWGVWHAVVRVVNUDXNAQPUYPVVIUUE
          DUYPIMPRSUUFXMUYQINPRTUUGWTAVVPGURUSZVVNAVWIAVWIUUHGVVPXSUSZVWIAGVVPV
          WFVWDUUJAVWJVWIAVWJVVPVVPGXTUPZYHYAUPZURUSZVWIAVWJWOZEUYMDVWLJKLHUUKU
          NZVQXTUPZPVWPUULUNZVWQWAUFAVULVWJVUQXNVWNVWPVWNHXQUOZYBHURUSWOVWOUUMU
          OVWPVTUOZVWNHVWNHVQVWLYHYCUPZGYHYCUPZUUNUPZYAUPZYDUKVWNVXBVWNVXBAVXBX
          QUOZVWJAVWTVXAAVWLAVWKAVVPGVWDVWFYEZUUOZYFZAGVWFYFZUUPZXNAVWJYBVXBXSU
          SZAVWJGVWLXSUSZVXAVWTXSUSVXJAVWJGGXTUPZVWKXSUSYHGYSUPZVWKXSUSZVXKAGVV
          PGVWFVWDVWFUUQAVXMVXLVWKXSAGAGVWFYGYIYJAVWEVWKXQUOZYHXQUOZYBYHXSUSZWO
          ZVXNVXKYKVWFVXEVXRAVXPVXQUUTUURUVAZWFZGVWKYHUUSXMYLAGVWLVWFVXFAYBFXQX
          SUVBUVKZGURAYBVYAURUSZYBULUQZURUSZULFUTZAFXQWJZFUVCUVDZVYEACULDEFILMN
          OPQRSTUAUBUCUDUEUFUGUVEZUVFZAVYFVYGVUAVYCURUSZULFUTZBXQVAZYBXQUOZVYBV
          YEYKAVYFVYGVYEVYHUVGZAVYFVYGVYEVYHUVHAVYMVYEVYLYMVYIVYKVYEBYBXQVUAYBV
          EVYJVYDULFVUAYBVYCURUVIYNYOUVJZVYMAYMWFBULULFYBUVLUVMXJUHUVTZAVXOYBVW
          KURUSVXRYBVWLURUSZVXEAVVPGVWDVWFAVWBVVRVVSYBVVPURUSVWCUDVVTDUYMEPYPXM
          VYPUVNVXTVWKYHUVOUVPZUVQAVXAVWTVXHVXGUVRUVSUWAZUWHUWBUWCZUWDHUWEVWOUW
          FVSZUWRAKUYMUYLUSVWJAKVUIUYMUYLVVLVVMUWGXNAVVRVWJUDXNVWNVWLAVWLXQUOZV
          WJVXFXNUWIVWNJUQZVWQUOZWOZDWUCKUNZEUPZVWLURUSWUGYHYCUPZVWTURUSWUEWUHV
          XAVQWUCYAUPZXTUPZVWTWUEWUGWUEAWUCVTUOZWUGXQUOZAVWJWUDUWJZVWNVWSWUDWUK
          WUAVQWUCVWPVTWBUWKUWLZAWUKWOZVWBVVRWUFPUOZWULAVWBWUKVWCXNZAVVRWUKUDXN
          ZAVTPWUCKAVTQKYTVVEVTPKYTUIVVIVTQPKUWMWTUWNZDWUFEPXRXMWTZYFWUEVXAWUIW
          UEGAVWEVWJWUDVWFYQYFZWUEWUCWUNUWOZYEAVWTXQUOVWJWUDVXGYQZWUEAWUKWUHWUJ
          URUSWUMWUNUJWTWUEWUJVWTURUSWUIVXBURUSZWUEVXCWUCURUSZWVDWUEVXCHWUCURUK
          WUEHVWPWUCWUEHVWNHYDUOWUDVYTXNUWPZWUEVWRVWOXQUOVWPXQUOWVFHUWSVWOUWQVS
          WUEWUCWUNUWTZWUEVWRHVWPURUSWVFHUXAWGWUDVWPWUCURUSVWNVWPWUCUXBUXCYRUXD
          WUEVQXQUOZVXDVXJWUCXQUOYBWUCXSUSWVEWVDYKWVHWUEUXEWFAVXDVWJWUDVXIYQVWN
          VXJWUDVYSXNWVGWUEWUCWUNUXFVQVXBWUCUXHUXGUXIWUEVXAWUIVWTWVAWVBWVCUXJXJ
          YRWUEWUGVWLWUTAWUBVWJWUDVXFYQWUEAWUKYBWUGURUSZWUMWUNWUOVWBVVRWUPWVIWU
          QWURWUSDWUFEPYPXMWTAVYQVWJWUDVYRYQUXKXJUXLAVWIVWMAVWIVVPVVPXTUPZVWKUR
          USYHVVPYSUPZVWKURUSZVWMAVVPGVVPVWDVWFVWDUXMAWVKWVJVWKURAVVPAVVPVWDYGY
          IYJAVWAVXOWVLVWMYKZVWDVXEVWAVXOVXRWVMVXSVVPVWKYHUXNUXOWTYLUXPUXQUXRUX
          SUXTXNVVOGVYAUYRURUHVVOVYFVYLUYRFUOVYAUYRURUSAVYFVVNVYNXNAVYLVVNVYOXN
          VVOUYRCQUYRUYAZUYBZFVVOVVNUYRVRUOUYRWVOUOAVVNUYGUYQNWDCQUYRWVNVRWVNWA
          UYCUYDUGUYEBULUYRFUYFXMUYHYRUYIUYJVUEUYTBUYMQVUAUYMVEZVUDUYSCQWVPVUCU
          YOUYRURWVPVUBUYNNVUAUYMDMUYKXGYJYNYOWT $.
      $}

      $( Lemma for ~ minveco .  Discharge the assumption about the sequence
         ` F ` by applying countable choice ~ ax-cc .  (Contributed by Mario
         Carneiro, 9-May-2014.)  (New usage is discouraged.) $)
      minvecolem5 $p |- ( ph -> E. x e. Y A. y e. Y
                        ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) ) $=
        ( vf vn vw vk cn cv wf cfv co c2 cexp c1 cdiv caddc cle wbr wral wa wex
        wrex wcel csqr wn clt cc0 nnrecgt0 adantl nnrecre ccnv csup wss wne w3a
        cr c0 minvecolem1 adantr simp1d simp2d simp3d wceq breq1 ralbidv rspcev
        0re sylancr infmrcl syl3anc syl5eqel ltaddposd mpbid readdcld addgegt0d
        resqcld sqge0d elrpd rpge0d resqrth syl2anc breqtrrd rpsqrcld rpred a1i
        infmrgelb syl31anc mpbird syl6breqr sqrge0d lt2sqd ltnled breq2i syl5bb
        wb cmpt crn raleqi cvv fvex rgenw eqid breq2 ralrnmpt ax-mp bitri mtbid
        syl6bb rexnal syl ad2antrr ccbn breq1d oveq1d cba oveq2 oveq2d cnv phnv
        sylibr ccphlo css cin inss1 sseldi sspba sselda nvmcl nvcl letrid nvge0
        ord le2sqd notbid imsdval 3imtr4d reximdva mpd ralrimiva eqeltri nnenom
        bitrd axcc4 clm cmin simprl simprr fveq2 breq12d rspccva sylan exlimddv
        minvecolem4 ) AUJNUFUKZULZDUGUKZUVQUMZEUNZUOUPUNZGUOUPUNZUQUVSURUNZUSUN
        ZUTVAZUGUJVBZVCZDBUKZJUNKUMDCUKZJUNZKUMZUTVACNVBBNVEUFADUWJEUNZUOUPUNZU
        WEUTVAZCNVEZUGUJVBUWHUFVDAUWPUGUJAUVSUJVFZVCZUWEVGUMZUWLUTVAZVHZCNVEZUW
        PUWRUWTCNVBZVHUXBUWRUWSGUTVAZUXCUWRGUWSVIVAZUXDVHUWRUXEUWCUWSUOUPUNZVIV
        AUWRUWCUWEUXFVIUWRVJUWDVIVAZUWCUWEVIVAUWQUXGAUVSVKVLZUWRUWDUWCUWQUWDVSV
        FAUVSVMVLZUWRGUWRGFVSVIVNVOZVSUEUWRFVSVPZFVTVQZUWIUHUKZUTVAZUHFVBZBVSVE
        ZUXJVSVFUWRUXKUXLVJUXMUTVAZUHFVBZAUXKUXLUXRVRUWQACUHDEFHIJKLMNOPQRSTUAU
        BUCUDWAWBZWCZUWRUXKUXLUXRUXSWDZUWRVJVSVFZUXRUXPWJUWRUXKUXLUXRUXSWEZUXOU
        XRBVJVSUWIVJWFUXNUXQUHFUWIVJUXMUTWGWHWIWKZBUHFWLWMWNZWSZWOWPUWRUWEVSVFZ
        VJUWEUTVAUXFUWEWFZUWRUWCUWDUYFUXIWQZUWRUWEUWRUWEUYIUWRUWCUWDUYFUXIUWRGU
        YEWTUXHWRXAZXBZUWEXCXDZXEUWRGUWSUYEUWRUWSUWRUWEUYJXFXGZUWRVJUXJGUTUWRVJ
        UXJUTVAZUXRUYCUWRUXKUXLUXPUYBUYNUXRXRUXTUYAUYDUYBUWRWJXHBUHUHFVJXIXJXKU
        EXLUWRUWEUYIUYKXMZXNXKUWRGUWSUYEUYMXOWPUWRUXDUWSUXMUTVAZUHFVBZUXCUXDUWS
        UXJUTVAZUWRUYQGUXJUWSUTUEXPUWRUXKUXLUXPUWSVSVFZUYRUYQXRUXTUYAUYDUYMBUHU
        HFUWSXIXJXQUYQUYPUHCNUWLXSZXTZVBZUXCUYPUHFVUAUDYAUWLYBVFZCNVBVUBUXCXRVU
        CCNUWKKYCYDUYPUWTCUHNUWLUYTYBUYTYEUXMUWLUWSUTYFYGYHYIYKYJUWTCNYLUUCUWRU
        XAUWOCNUWRUWJNVFZVCZUWEUWLUOUPUNZUTVAZVHVUFUWEUTVAZUXAUWOVUEVUGVUHVUEUW
        EVUFUWRUYGVUDUYIWBVUEUWLVUEHUUAVFZUWKMVFZUWLVSVFAVUIUWQVUDAHUUDVFZVUISH
        UUBYMZYNZVUEVUIDMVFZUWJMVFZVUJVUMAVUNUWQVUDUAYNZUWRNMUWJANMVPZUWQAVUILH
        UUEUMZVFVUQVULAVURYOUUFZVURLVURYOUUGTUUHHVURLMNORVURYEUUIXDWBUUJZDUWJHJ
        MOPUUKWMZUWKHKMOQUULXDZWSUUMUUOVUEUWTVUGVUEUWTUXFVUFUTVAVUGVUEUWSUWLUWR
        UYSVUDUYMWBVVBUWRVJUWSUTVAVUDUYOWBVUEVUIVUJVJUWLUTVAVUMVVAUWKHKMOQUUNXD
        UUPVUEUXFUWEVUFUTUWRUYHVUDUYLWBYPUVEUUQVUEUWNVUFUWEUTVUEUWMUWLUOUPVUEVU
        IVUNVUOUWMUWLWFVUMVUPVUTDUWJEHJKMOPQUBUURWMYQYPUUSUUTUVAUVBUWOUWFCNUFUG
        UJNLYRUMYBRLYRYCUVCUVDUWJUVTWFZUWNUWBUWEUTVVCUWMUWAUOUPUWJUVTDEYSYQYPUV
        FYMAUWHVCZBCDEFGUQDUVQIUVGUMUMEUNGUSUNUOURUNUOUPUNUWCUVHUNURUNZHUIUVQIJ
        KLMNOPQRAVUKUWHSWBALVUSVFUWHTWBAVUNUWHUAWBUBUCUDUEAUVRUWGUVIVVDUWGUIUKZ
        UJVFDVVFUVQUMZEUNZUOUPUNZUWCUQVVFURUNZUSUNZUTVAZAUVRUWGUVJUWFVVLUGVVFUJ
        UVSVVFWFZUWBVVIUWEVVKUTVVMUWAVVHUOUPVVMUVTVVGDEUVSVVFUVQUVKYTYQVVMUWDVV
        JUWCUSUVSVVFUQURYSYTUVLUVMUVNVVEYEUVPUVO $.

      $( Lemma for ~ minveco .  Any minimal point is less than ` S ` away from
         ` A ` .  (Contributed by Mario Carneiro, 9-May-2014.)
         (New usage is discouraged.) $)
      minvecolem6 $p |- ( ( ph /\ x e. Y ) ->
        ( ( ( A D x ) ^ 2 ) <_ ( ( S ^ 2 ) + 0 ) <->
          A. y e. Y ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) ) ) $=
        ( vw cv wcel wa co cexp cc0 caddc cle wbr cfv wral cnv wceq ccphlo phnv
        c2 syl adantr css wss ccbn cin inss1 sseldi eqid syl2anc sselda imsdval
        sspba syl3anc oveq1d cr clt ccnv csup c0 wrex minvecolem1 simp1d simp2d
        wne w3a 0re simp3d breq1 ralbidv infmrcl syl5eqel resqcld recnd addid1d
        a1i rspcev breq12d nvmcl nvcl nvge0 infmrgelb syl31anc mpbird syl6breqr
        wb le2sqd breq2i syl5bb 3bitr2d cmpt crn raleqi cvv fvex rgenw ralrnmpt
        breq2 ax-mp bitri syl6bb ) ABUGZNUHZUIZDYDEUJZVBUKUJZGVBUKUJZULUMUJZUNU
        OZDYDJUJZKUPZUFUGZUNUOZUFFUQZYMDCUGJUJZKUPZUNUOZCNUQZYFYKYMVBUKUJZYIUNU
        OYMGUNUOZYPYFYHUUAYJYIUNYFYGYMVBUKYFHURUHZDMUHZYDMUHZYGYMUSAUUCYEAHUTUH
        UUCSHVAVCZVDZAUUDYEUAVDZANMYDAUUCLHVEUPZUHNMVFUUFAUUIVGVHUUILUUIVGVITVJ
        HUUILMNORUUIVKVOVLVMZDYDEHJKMOPQUBVNVPVQYFYIYFYIYFGYFGFVRVSVTWAZVRUEYFF
        VRVFZFWBWGZYDYNUNUOZUFFUQZBVRWCZUUKVRUHYFUULUUMULYNUNUOZUFFUQZAUULUUMUU
        RWHYEACUFDEFHIJKLMNOPQRSTUAUBUCUDWDVDZWEZYFUULUUMUURUUSWFZYFULVRUHZUURU
        UPUVBYFWIWRZYFUULUUMUURUUSWJZUUOUURBULVRYDULUSUUNUUQUFFYDULYNUNWKWLWSVL
        ZBUFFWMVPWNZWOWPWQWTYFYMGYFUUCYLMUHZYMVRUHZUUGYFUUCUUDUUEUVGUUGUUHUUJDY
        DHJMOPXAVPZYLHKMOQXBVLZUVFYFUUCUVGULYMUNUOUUGUVIYLHKMOQXCVLYFULUUKGUNYF
        ULUUKUNUOZUURUVDYFUULUUMUUPUVBUVKUURXHUUTUVAUVEUVCBUFUFFULXDXEXFUEXGXIU
        UBYMUUKUNUOZYFYPGUUKYMUNUEXJYFUULUUMUUPUVHUVLYPXHUUTUVAUVEUVJBUFUFFYMXD
        XEXKXLYPYOUFCNYRXMZXNZUQZYTYOUFFUVNUDXOYRXPUHZCNUQUVOYTXHUVPCNYQKXQXRYO
        YSCUFNYRUVMXPUVMVKYNYRYMUNXTXSYAYBYC $.

      $( Lemma for ~ minveco .  Since any two minimal points are distance zero
         away from each other, the minimal point is unique.  (Contributed by
         Mario Carneiro, 9-May-2014.)  (New usage is discouraged.) $)
      minvecolem7 $p |- ( ph -> E! x e. Y A. y e. Y
                        ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) ) $=
        ( vw cv co cfv cle wbr wral wrex wa wceq wreu minvecolem5 wcel cexp cc0
        wi c2 caddc c4 cmul ccphlo ad2antrr css ccbn cin cr 0re simplrl simplrr
        a1i simprl simprr minvecolem2 ex wb minvecolem6 adantrr adantrl anbi12d
        0le0 4cn mul01i breq2i cme cnv phnv syl adantr imsmet inss1 sseldi eqid
        wss sspba syl2anc sseldd syl3anc sqge0d biantrud resqcld letri3 sylancl
        metcl recnd sqeq0 meteq0 bitrd 3bitr2d syl5bb 3imtr3d ralrimivva fveq2d
        cc oveq2 breq1d ralbidv reu4 sylanbrc ) ADBUGZJUHZKUIZDCUGJUHKUIZUJUKZC
        NULZBNUMYIDUFUGZJUHZKUIZYGUJUKZCNULZUNZYDYJUOZVAZUFNULBNULYIBNUPABCDEFG
        HIJKLMNOPQRSTUAUBUCUDUEUQAYQBUFNNAYDNURZYJNURZUNZUNZDYDEUHVBUSUHGVBUSUH
        UTVCUHZUJUKZDYJEUHVBUSUHUUBUJUKZUNZYDYJEUHZVBUSUHZVDUTVEUHZUJUKZYOYPUUA
        UUEUUIUUAUUEUNZCDUTEFGHIYDYJJKLMNOPQRAHVFURZYTUUESVGALHVHUIZVIVJZURYTUU
        ETVGADMURYTUUEUAVGUBUCUDUEUTVKURZUUJVLVOUTUTUJUKUUJWEVOAYRYSUUEVMAYRYSU
        UEVNUUAUUCUUDVPUUAUUCUUDVQVRVSUUAUUCYIUUDYNAYRUUCYIVTYSABCDEFGHIJKLMNOP
        QRSTUAUBUCUDUEWAWBAYSUUDYNVTYRAUFCDEFGHIJKLMNOPQRSTUAUBUCUDUEWAWCWDUUIU
        UGUTUJUKZUUAYPUUHUTUUGUJVDWFWGWHUUAUUOUUOUTUUGUJUKZUNZUUGUTUOZYPUUAUUPU
        UOUUAUUFUUAEMWIUIURZYDMURZYJMURZUUFVKURUUAHWJURZUUSAUVBYTAUUKUVBSHWKWLZ
        WMEHMOUBWNWLZUUANMYDANMWRZYTAUVBLUULURUVEUVCAUUMUULLUULVIWOTWPHUULLMNOR
        UULWQWSWTWMZAYRYSVPXAZUUANMYJUVFAYRYSVQXAZYDYJEMXHXBZXCXDUUAUUGVKURUUNU
        URUUQVTUUAUUFUVIXEVLUUGUTXFXGUUAUURUUFUTUOZYPUUAUUFXRURUURUVJVTUUAUUFUV
        IXIUUFXJWLUUAUUSUUTUVAUVJYPVTUVDUVGUVHYDYJEMXKXBXLXMXNXOXPYIYNBUFNYPYHY
        MCNYPYFYLYGUJYPYEYKKYDYJDJXSXQXTYAYBYC $.
    $}

    $( Minimizing vector theorem, or the Hilbert projection theorem.  There is
       exactly one vector in a complete subspace ` W ` that minimizes the
       distance to an arbitrary vector ` A ` in a parent inner product space.
       Theorem 3.3-1 of [Kreyszig] p. 144, specialized to subspaces instead of
       convex subsets.  (Contributed by NM, 11-Apr-2008.)  (Proof shortened by
       Mario Carneiro, 9-May-2014.)  (New usage is discouraged.) $)
    minveco $p |- ( ph -> E! x e. Y A. y e. Y
                   ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) ) $=
      ( vj cfv eqid cims cv co cmpt crn cr clt ccnv csup cmopn weq oveq2 fveq2d
      cbvmptv rneqi minvecolem7 ) ABCDEUASZRJDRUBZFUCZGSZUDZUEZVBUFUGUHUIZEUQUJ
      SZFGHIJKLMNOPQUQTVDTVACJDCUBZFUCZGSZUDRCJUTVGRCUKUSVFGURVEDFULUMUNUOVCTUP
      $.
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
      ( chlo wcel ccbn cms cfv hlobn cbncms syl ) BFGBHGACIJGBKABCDELM $.

    $( The induced metric on a complex Hilbert space.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hlmet $p |- ( U e. CHilOLD -> D e. ( Met ` X ) ) $=
      ( chlo wcel cms cfv cme hlcmet cmetmet syl ) BFGACHIGACJIGABCDEKACLM $.
  $}

  ${
    hlpar2.1 $e |- X = ( BaseSet ` U ) $.
    hlpar2.2 $e |- G = ( +v ` U ) $.
    hlpar2.3 $e |- M = ( -v ` U ) $.
    hlpar2.6 $e |- N = ( normCV ` U ) $.
    $( The parallelogram law satified by Hilbert space vectors.  (Contributed
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
    $( The parallelogram law satified by Hilbert space vectors.  (Contributed
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
      ( cba cfv cvv fvex eqeltri ) BADEFCADGH $.
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
      ( chlo wcel cba cfv cms cca clm cdm eqid hlcmet cmetcau sylan ) BGHABIJZK
      JHCALJHCDMJNHABSSOEPACDSFQR $.
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
                     Subspaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
  ${
    ssphl.h $e |- H = ( SubSp ` U ) $.
    $( A Banach subspace of an inner product space is a Hilbert space.
       (Contributed by NM, 11-Apr-2008.)  (New usage is discouraged.) $)
    ssphl $p |- ( ( U e. CPreHilOLD /\ W e. H /\ W e. CBan )
        -> W e. CHilOLD ) $=
      ( ccphlo wcel ccbn w3a chlo simp3 sspph 3adant3 ishlo sylanbrc ) AEFZCBFZ
      CGFZHQCEFZCIFOPQJOPRQABCDKLCMN $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                     Self-adjoint operators
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

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
        cabs lnof mp3an12 syl ffvelrnda nvcl wceq crab wfun cima cblo cmpt chlo
        wf sylancr ccphlo hlph ax-mp eqid ipblnfi fmptd ffun adantr id syl6eleq
        fvelima syl2an weq fveq2 breq1d elrab oveq2d mpteq2dv hlex mptex fveq1d
        ex fvmpt oveq1 ovex sylan9eqr ad2ant2lr rsp2 impl adantrr eqtrd cmul cc
        fveq2d simpl dipcl mp3an1 abscld mpan ad2antrl remulcld sii cc0 1re a1i
        nvge0 jca simprr lemul2a syl31anc recnd letrd syl5ibcom syld syl2anc wb
        wss mpbid ad2ant2r mpd 0re expr mulid1d breqtrd eqbrtrd fveq1 rexlimdva
        sylan2b ralrimiv breq2 ralbidv rspcev ralrimiva crn imassrn eqsstri frn
        syl5ss ccbn hlobn cnnv cnnvnm ubth simpr sylibr cdm fdm eleq2d funfvima
        biimpar sylan syldan syl6eleqr cnnvba nmblore simplr cexp adantl ipidsq
        rspcv c2 resqcl sqge0 absidd sqvald 3eqtrd nmblolbi eqbrtrrd w3a lemul1
        lemul1ad biimprd 3expia expdimp syl21anc mpid blof nmooge0 breq1 mpjaod
        wo leloe com23 ralrimdva reximdva nmobndi mpbird ltpnf isblo sylanbrc
        mp2an ) AHLUGZHIIUHUIZUJZUKULUMZHFUGZUCAUXLUNUGZUXMAUXOBUOZMUJZUPUQUMZU
        XPHUJZMUJZCUOZUQUMZURZBOUSZCUNUTZAEUOZINUHUIZUJZUYAUQUMZEKUSZCUNUTZUYEA
        UXPUYFUJZVDUJZDUOZUQUMZEKUSZDUNUTZBOUSZUYKAUYQBOAUXPOUGZVAZUXTUNUGZUYMU
        XTUQUMZEKUSZUYQUYTIVBUGZUXSOUGZVUAIUAVCZAOOUXPHAUXJOOHVQZUCVUDVUDUXJVUG
        VUFVUFHILIOOPPRVEVFVGZVHZUXSIMOPTVIVRZUYTVUBEKUYTUYFKUGZUYAJUJZUYFVJZCU
        YNMUJZUPUQUMZDOVKZUTZVUBUYTVUKVUQUYTJVLZUYFJVUPVMZUGVUQVUKAVURUYSAOINVN
        UIZJVQZVURADOEOUYFUYNHUJZGUIZVOZVUTJAUYNOUGVAVVBOUGVVDVUTUGAOOUYNHVUHVH
        EVVBVUTNGIVVDOPQIVPUGZIVSUGUAIVTWAZUBVUTWBZVVDWBWCVGUEWDZOVUTJWEVGZWFVU
        KUYFKVUSVUKWGUFWHCUYFVUPJWIWJWTUYTVUMVUBCVUPUYTUYAVUPUGZVAUXPVULUJZVDUJ
        ZUXTUQUMZVUMVUBVVJUYTUYAOUGZUYAMUJZUPUQUMZVAZVVMVUOVVPDUYAODCWKZVUNVVOU
        PUQUYNUYAMWLWMWNUYTVVQVAZVVLUXSUYAGUIZVDUJZUXTUQVVSVVKVVTVDVVSVVKUXPUYA
        HUJZGUIZVVTUYSVVNVVKVWCVJAVVPVVNUYSVVKUXPEOUYFVWBGUIZVOZUJVWCVVNUXPVULV
        WEDUYAVVDVWEOJVVREOVVCVWDVVRVVBVWBUYFGUYNUYAHWLWOWPUEEOVWDIOPWQZWRXAWSE
        UXPVWDVWCOVWEUYFUXPVWBGXBVWEWBUXPVWBGXCXAXDXEUYTVVNVWCVVTVJZVVPAUYSVVNV
        WGAVWGCOUSBOUSUYSVVNVAVWGURUDVWGBCOOXFVGXGXHXIXLVVSVWAUXTVVOXJUIZUXTVVS
        VVTUYTVUEVVNVVTXKUGZVVQVUIVVNVVPXMZVUDVUEVVNVWIVUFUXSUYAGIOPQXNXOWJXPVV
        SUXTVVOUYTVUAVVQVUJWFZVVNVVOUNUGZUYTVVPVUDVVNVWLVUFUYAIMOPTVIXQXRZXSVWK
        UYTVUEVVNVWAVWHUQUMVVQVUIVWJUXSUYAGIMOPTQVVFXTWJVVSVWHUXTUPXJUIZUXTUQVV
        SVWLUPUNUGZVUAYAUXTUQUMZVAZVVPVWHVWNUQUMVWMVWOVVSYBYCUYTVWQVVQUYTVUAVWP
        VUJUYTVUDVUEVWPVUFVUIUXSIMOPTYDZVRYEWFUYTVVNVVPYFVVOUPUXTYGYHVVSUXTVVSU
        XTVWKYIUUAUUBYJUUCUUFVUMVVLUYMUXTUQVUMVVKUYLVDUXPVULUYFUUDXLWMYKUUEYLUU
        GUYPVUCDUXTUNUYNUXTVJUYOVUBEKUYNUXTUYMUQUUHUUIUUJYMUUKAKVUTYOZUYRUYKYNZ
        AKJUULZVUTKVUSVXAUFJVUPUUMUUNAVVAVXAVUTYOVVHOVUTJUUOVGUUPIUUQUGZNVBUGZV
        WSVWTVVEVXBUAIUURWANUBUUSZBEKIUYGVDNODCPNUBUUTZUYGWBZUVAVFVGYPAUYJUYDCU
        NAUYAUNUGZVAZUYJUYCBOVXHUYSVAUXRUYJUYBVXHUYSUXRUYJUYBURVXHUYSUXRVAZVAZU
        YJUXPJUJZUYGUJZUYAUQUMZUYBVXJVXKKUGUYJVXMURVXJVXKVUSKVXJUXPVUPUGZVXKVUS
        UGZVXJVXIVXNVXHVXIUVBVUOUXRDUXPODBWKZVUNUXQUPUQUYNUXPMWLWMWNUVCAUYSVXNV
        XOURZVXGUXRAUYSUXPJUVDZUGZVXQAVXSUYSAVXROUXPAVVAVXROVJVVHOVUTJUVEVGUVFU
        VHAVURVXSVXQVVIVUPUXPJUVGUVIUVJYQYRUFUVKUYIVXMEVXKKUYFVXKVJUYHVXLUYAUQU
        YFVXKUYGWLWMUVRVGVXHUYSVXMUYBURUXRVXHUYSVXMUYBVXHUYSVXMVAZVAZYAUXTULUMZ
        UYBYAUXTVJZVYAVYBUXTUXTXJUIZUYAUXTXJUIZUQUMZUYBVYAVYDVXLUXTXJUIZVYEVYAU
        XTUXTAUYSVUAVXGVXMVUJYQZVYHXSVYAVXLUXTAUYSVXLUNUGZVXGVXMUYTVXKVUTUGZVYI
        AOVUTUXPJVVHVHZVUDVXCVYJVYIVUFVXDVUTVXKIUYGNOXKPNUBUVLZVXFVVGUVMVFVGYQZ
        VYHXSVYAUYAUXTAVXGVXTUVNZVYHXSVYAUXSVXKUJZVDUJZVYDVYGUQVYAVYPUXTUVSUVOU
        IZVDUJZVYQVYDVYAVYOVYQVDVYAVYOUXSUXSGUIZVYQAUYSVYOVYSVJVXGVXMUYTVYOUXSE
        OUYFUXSGUIZVOZUJZVYSUYTUXSVXKWUAUYSVXKWUAVJADUXPVVDWUAOJVXPEOVVCVYTVXPV
        VBUXSUYFGUYNUXPHWLWOWPUEEOVYTVWFWRXAUVPWSUYTVUEWUBVYSVJVUIEUXSVYTVYSOWU
        AUYFUXSUXSGXBWUAWBUXSUXSGXCXAVGXIYQVYAVUDVUEVYSVYQVJVUFAUYSVUEVXGVXMVUI
        YQZUXSGIMOPTQUVQVRXIXLVYAVUAVYRVYQVJVYHVUAVYQUXTUVTUXTUWAUWBVGVYAUXTVYA
        UXTVYHYIUWCUWDVYAVYJVUEVYPVYGUQUMAUYSVYJVXGVXMVYKYQWUCUXSVUTVXKIMVDUYGN
        OPTVXEVXFVVGVUFVXDUWEYMUWFVYAVXLUYAUXTVYMVYNVYHVYAVUDVUEVWPVUFWUCVWRVRZ
        VXHUYSVXMYFZUWIYJVYAVUAVXGVUAVYBVYFUYBURZURVYHVYNVYHVUAVXGVAVUAVYBWUFVU
        AVXGVUAVYBVAZWUFVUAVXGWUGUWGUYBVYFUXTUYAUXTUWHUWJUWKUWLUWMUWNVYAYAUYAUQ
        UMVYCUYBVYAYAVXLUYAYAUNUGZVYAYSYCVYMVYNVYAOXKVXKVQZYAVXLUQUMZAUYSWUIVXG
        VXMUYTVYJWUIVYKVUDVXCVYJWUIVUFVXDVUTVXKINOXKPVYLVVGUWOVFVGYQVUDVXCWUIWU
        JVUFVXDVXKIUYGNOXKPVYLVXFUWPVFVGWUEYJYAUXTUYAUQUWQYKVYAVWPVYBVYCUWSZWUD
        VYAWUHVUAVWPWUKYNYSVYHYAUXTUWTVRYPUWRYTXHYLYTUXAUXBUXCYRAVUGUXOUYEYNVUH
        BHIMMUXKIOOCPPTTUXKWBZVUFVUFUXDVGUXEUXLUXFVGVUDVUDUXNUXJUXMVAYNVUFVUFFH
        ILUXKIWULRSUXGUXIUXH $.
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
      wi cop cif clno cdip cba cblo oveq12 anidms syl5eq eleq2d oveqd raleqbidv
      eqeq12d anbi12d imbi12d cmpt cnmcv c1 cle wbr crab cima cnchl simpl simpr
      elimel oveq1 oveq1d oveq2d oveq2 cbvral2v cbvmptv mpteq2dv breq1d cbvrabv
      sylib imaeq2i htthlem dedth 3impib ) FUDUEZEGUEZANZBNZEOZDPZWMEOZWNDPZQZB
      HRZAHRZECUEZWKWLXAUFZXBUJEWKFUGUHUKUIUKZULZXEUMPZUEZWMWOXEUNOZPZWQWNXHPZQ
      ZBXEUOOZRZAXLRZUFZEXEXEUPPZUEZUJFXDFXEQZXCXOXBXQXRWLXGXAXNXRGXFEXRGFFUMPZ
      XFKXRXSXFQFXEFXEUMUQURUSUTXRWTXMAHXLXRHFUOOXLIFXEUOSUSZXRWSXKBHXLXTXRWPXI
      WRXJXRDXHWMWOXRDFUNOXHJFXEUNSUSZVAXRDXHWQWNYAVAVCVBVBVDXRCXPEXRCFFUPPZXPL
      XRYBXPQFXEFXEUPUQURUSUTVEXOUAUBUCMXPXHEXEAXLBXLWNWQXHPZVFZVFZYEWMXEVGOZOZ
      VHVIVJZAXLVKZVLXFYFXDXLXLTXHTXFTXPTYFTFXDUDXDXDTZVMVPYJXGXNVNXOXNUANZUBNZ
      EOZXHPZYKEOZYLXHPZQZUBXLRUAXLRXGXNVOXKYQYKWOXHPZYOWNXHPZQABUAUBXLXLWMYKQZ
      XIYRXJYSWMYKWOXHVQYTWQYOWNXHWMYKESVRVCWNYLQZYRYNYSYPUUAWOYMYKXHWNYLESVSWN
      YLYOXHVTVCWAWFAUCXLYDMXLMNZUCNZEOZXHPZVFZWMUUCQZYDMXLUUBWQXHPZVFUUFBMXLYC
      UUHWNUUBWQXHVQWBUUGMXLUUHUUEUUGWQUUDUUBXHWMUUCESVSWCUSWBYIUUCYFOZVHVIVJZU
      CXLVKYEYHUUJAUCXLUUGYGUUIVHVIWMUUCYFSWDWEWGWHWIWJ $.
  $}

