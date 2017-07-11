$( set.mm - Version of 2-Jul-2017 $)

$[ set_wo_mb_av.mm $]

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                Mathbox for Alexander van der Vekens
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Restricted quantification (extension)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    r19.32.1 $e |- F/ x ph $.
    $( Theorem 19.32 of [Margaris] p. 90 with restricted quantifiers, analogous
       to ~ r19.32v .
       (Contributed by Alexander van der Vekens, 29-Jun-2017.) $)
    r19.32 $p |- ( A. x e. A ( ph \/ ps ) <-> ( ph \/ A. x e. A ps ) ) $=
      ( wn wi wral wo nfn r19.21 df-or ralbii 3bitr4i ) AFZBGZCDHOBCDHZGABIZCDH
      AQIOBCDACEJKRPCDABLMAQLN $.
  $}

  ${
    $d x y A $.  $d y ph $.
    $( An equivalent expression for restricted existence, analogous to ~ exsb . 
       (Contributed by Alexander van der Vekens, 1-Jul-2017.) $)
    rexsb $p |- ( E. x e. A ph <-> E. y e. A A. x ( x = y -> ph ) ) $=
      ( weq wi wal nfv nfa1 ax11v ax-4 com12 impbid cbvrex ) ABCEZAFZBGZBCDACHP
      BIOAQABCJQOAPBKLMN $.

    $( An equivalent expression for restricted existence, analogous to ~ exsb .  
       (Contributed by Alexander van der Vekens, 1-Jul-2017.) $)
    rexrsb $p |- ( E. x e. A ph <-> E. y e. A A. x e. A ( x = y -> ph ) ) $=
      ( wrex weq wi wal wral rexsb cv wcel alral df-ral wa 19.27v eleq1 biimprd
      pm2.04 pm2.83 ax-mp imp alimi sylbir ex sylbi com12 impbid2 rexbiia bitri
      3syl ) ABDEBCFZAGZBHZCDEUMBDIZCDEABCDJUNUOCDCKZDLZUNUOUMBDMUOUQUNUOBKZDLZ
      UMGZBHZUQUNGUMBDNVAUQUNVAUQOUTUQOZBHUNUTUQBPVBUMBUTUQUMUTULUSAGGZULUQAGGZ
      UQUMGUSULASULUQUSGGVCVDGULUSUQURUPDQRULUQUSATUAULUQASUKUBUCUDUEUFUGUHUIUJ
      $.
  $}

  ${
    $d w x y z B $. $d w x z A $. $d z w ph $.
    $( An equivalent expression for double restricted existence, analogous to 
       ~ rexsb .
       (Contributed by Alexander van der Vekens, 1-Jul-2017.) $)
    2rexsb $p |- ( E. x e. A E. y e. B ph <-> E. z e. A E. w e. B 
                   A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $=
      ( wrex weq wi wal wa rexsb rexbii rexcom bitri impexp albii 19.21v bitr2i
      ) ACGHZBFHZCEIZAJZCKZBFHZEGHZBDIZUCLAJZCKZBKZEGHDFHZUBUEEGHZBFHUGUAUMBFAC
      EGMNUEBEFGOPUGUKDFHZEGHULUFUNEGUFUHUEJZBKZDFHUNUEBDFMUPUKDFUOUJBUJUHUDJZC
      KUOUIUQCUHUCAQRUHUDCSTRNPNUKEDGFOPP $.

    $( An equivalent expression for double restricted existence, analogous to
       ~ 2exsb . 
       (Contributed by Alexander van der Vekens, 1-Jul-2017.) $)
    2rexrsb $p |- ( E. x e. A E. y e. B ph <-> E. z e. A E. w e. B 
                   A. x e. A A. y e. B ( ( x = z /\ y = w ) -> ph ) ) $=
      ( wrex wi wral wa rexrsb rexbii rexcom bitri impexp ralbii r19.21v bitr2i
      weq ) ACGHZBFHZCETZAIZCGJZBFHZEGHZBDTZUCKAIZCGJZBFJZEGHDFHZUBUEEGHZBFHUGU
      AUMBFACEGLMUEBEFGNOUGUKDFHZEGHULUFUNEGUFUHUEIZBFJZDFHUNUEBDFLUPUKDFUOUJBF
      UJUHUDIZCGJUOUIUQCGUHUCAPQUHUDCGRSQMOMUKEDGFNOO $.
  $}

  ${
    $d x A $.  $d z A $.  $d x y B $.  $d z y B $.  $d w B $.
    cbvral2.1 $e |- F/ z ph $.
    cbvral2.2 $e |- F/ x ch $.
    cbvral2.3 $e |- F/ w ch $.
    cbvral2.4 $e |- F/ y ps $.
    cbvral2.5 $e |- ( x = z -> ( ph <-> ch ) ) $.
    cbvral2.6 $e |- ( y = w -> ( ch <-> ps ) ) $.
    $( Change bound variables of double restricted universal quantification,
       using implicit substitution, analogous to ~ cbvral2v .  
       (Contributed by Alexander van der Vekens, 2-Jul-2017.) $)
    cbvral2 $p |- ( A. x e. A A. y e. B ph <-> A. z e. A A. w e. B ps ) $=
      ( wral nfcv nfral weq cbvral ralbidv ralbii bitri ) AEIPZDHPCEIPZFHPBGIPZ
      FHPUDUEDFHAFEIFIQJRCDEIDIQKRDFSACEINUATUEUFFHCBEGILMOTUBUC $.

    $( Change bound variables of double restricted universal quantification,
       using implicit substitution, analogous to ~ cbvrex2v .  
       (Contributed by Alexander van der Vekens, 2-Jul-2017.) $)
    cbvrex2 $p |- ( E. x e. A E. y e. B ph <-> E. z e. A E. w e. B ps ) $=
      ( wrex nfcv nfrex weq cbvrex rexbidv rexbii bitri ) AEIPZDHPCEIPZFHPBGIPZ
      FHPUDUEDFHAFEIFIQJRCDEIDIQKRDFSACEINUATUEUFFHCBEGILMOTUBUC $.
  $}

  $( Split a biconditional and distribute 2 quantifiers, analogous to ~ 2albiim
     and ~ ralbiim .
     (Contributed by Alexander van der Vekens, 2-Jul-2017.) $)
  2ralbiim $p |- ( A. x e. A A. y e. B ( ph <-> ps ) <->
                   ( A. x e. A A. y e. B ( ph -> ps ) 
                     /\ A. x e. A A. y e. B ( ps -> ph ) ) ) $=
    ( wb wral wi wa ralbiim ralbii r19.26 bitri ) ABGDFHZCEHABIDFHZBAIDFHZJZCEH
    PCEHQCEHJORCEABDFKLPQCEMN $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           The empty set (extension)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y A $. $d x y B $.
    raaan2.1 $e |- F/ y ph $.
    raaan2.2 $e |- F/ x ps $.
    $( Rearrange restricted quantifiers with two different restricting classes, 
       analogous to ~ raaan . It is necessary that either both restricting 
       classes are empty or both are not empty.
       (Contributed by Alexander van der Vekens, 29-Jun-2017.) $)
    raaan2 $p |- ( ( A = (/) <-> B = (/) ) 
                   -> ( A. x e. A A. y e. B ( ph /\ ps ) <->
                        ( A. x e. A ph /\ A. y e. B ps ) ) ) $=
      ( c0 wceq wb wa wn wo wral rzal adantr wne df-ne sylbir dfbi3 adantl nfcv
      pm5.1 syl12anc r19.28z ralbidv nfral r19.27z sylan9bbr jaoi sylbi ) EIJZF
      IJZKUMUNLZUMMZUNMZLZNABLDFOZCEOZACEOZBDFOZLZKZUMUNUAUOVDURUOUTVAVBVDUMUTU
      NUSCEPQUMVAUNACEPQUNVBUMBDFPUBUTVCUDUEUQUTAVBLZCEOZUPVCUQFIRZUTVFKFISVGUS
      VECEABDFGUFUGTUPEIRVFVCKEISAVBCEBCDFCFUCHUHUITUJUKUL $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Restricted uniqueness and "at most one" quantification
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    rmoimi.1 $e |- ( ph -> ps ) $.
    $( Restricted "at most one" is preserved through implication (note wff
       reversal).  (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)
    rmoimi $p |- ( E* x e. A ps -> E* x e. A ph ) $=
      ( wi cv wcel a1i rmoimia ) ABCDABFCGDHEIJ $.
  $}

  $( Double restricted existential uniqueness in terms of restricted existence
     and restricted "at most one."  (Contributed by Alexander van der Vekens,
     17-Jun-2017.) $)
  2reu5a $p |- ( E! x e. A E! y e. B ph <->
                ( E. x e. A ( E. y e. B ph /\ E* y e. B ph )
                  /\ E* x e. A ( E. y e. B ph /\ E* y e. B ph ) ) ) $=
    ( wreu wrex wrmo wa reu5 rexbii rmobii anbi12i bitri ) ACEFZBDFOBDGZOBDHZIA
    CEGACEHIZBDGZRBDHZIOBDJPSQTORBDACEJZKORBDUALMN $.

  $( Restricted uniqueness implies restricted "at most one" through 
     implication, analogous to ~ euimmo . 
     (Contributed by Alexander van der Vekens, 25-Jun-2017.) $)
  reuimrmo $p |- ( A. x e. A ( ph -> ps ) 
                   -> ( E! x e. A ps -> E* x e. A ph ) ) $=
    ( wreu wrmo wi wral reurmo rmoim syl5 ) BCDEBCDFABGCDHACDFBCDIABCDJK $.

  ${
    $d x y A $.  $d y ph $.  $d y ps $.
    rmoanim.1 $e |- F/ x ph $.
    $( Introduction of a conjunct into restricted "at most one" quantifier,
       analogous to ~ moanim.
       (Contributed by Alexander van der Vekens, 25-Jun-2017.) $)
    rmoanim $p |- ( E* x e. A ( ph /\ ps ) <-> ( ph -> E* x e. A ps ) ) $=
      ( vy wa weq wi wral wex wrmo impexp ralbii r19.21 bitri exbii rmo2 imbi2i
      nfv 19.37v bitr4i 3bitr4i ) ABGZCFHZIZCDJZFKABUEIZCDJZIZFKZUDCDLABCDLZIZU
      GUJFUGAUHIZCDJUJUFUNCDABUEMNAUHCDEOPQUDCFDUDFTRUMAUIFKZIUKULUOABCFDBFTRSA
      UIFUAUBUC $.

    $( Introduction of a conjunct into restricted uniqueness quantifier,
       analogous to ~ euan .
       (Contributed by Alexander van der Vekens, 2-Jul-2017.) $)
    reuan $p |- ( E! x e. A ( ph /\ ps ) <-> ( ph /\ E! x e. A ps ) ) $=
      ( wa wreu wrex wrmo wi cv wcel simpl a1i rexlimi adantr simpr reximi reu5
      biimpa nfre1 ancrd impbid2 rmobida jca32 anbi2i 3imtr4i wb reubida impbii
      a1d ibar ) ABFZCDGZABCDGZFZUMCDHZUMCDIZFZABCDHZBCDIZFZFUNUPUSAUTVAUQAURUM
      ACDEUMAJCKDLZABMNOZPUQUTURUMBCDABQZRPUQURVAUQUMBCDUMCDUAUQVCFZUMBVEVFBAVF
      ABUQAVCVDPUKUBUCUDTUEUMCDSUOVBABCDSUFUGAUOUNABUMCDEABUMUHVCABULPUITUJ $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Analogs to 1.6.6 Existential uniqueness (double quantification)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d y A $. $d x y $. $d x B $. 
    $( Double restricted quantification with existential uniqueness, analogous 
       to ~ 2euex. (Contributed by Alexander van der Vekens, 24-Jun-2017.) $)
    2reurex $p |- ( E! x e. A E. y e. B ph -> E. y e. B E! x e. A ph ) $=
      ( wrex wreu wrmo wa reu5 excom nfcv nfre1 nfrmo cv wcel wi wral ex impcom
      ra4e a1d ralrimiv rmoim syl rmo5 sylib reximdai syl5bi sylbi ) ACEFZBDGUK
      BDFZUKBDHZIABDGZCEFZUKBDJUMULUOULABDFZCEFUMUOA??KUMUPUNCEUKCBDCDLACEMNUMC
      OEPZUPUNQZUMUQIABDHZURUQUMUSUQAUKQZBDRUMUSQUQUTBDUQUTBODPUQAUKACEUASUBUCA
      UKBDUDUETABDUFUGSUHUITUJ $.

    $( Double restricted quantification with restricted existential uniqueness 
       and restricted "at most one.", analogous to ~ 2eumo .
       (Contributed by Alexander van der Vekens, 24-Jun-2017.) $)
    2reurmo $p |- ( E! x e. A E* y e. B ph -> E* x e. A E! y e. B ph ) $=
      ( wreu wrmo wi reuimrmo cv wcel reurmo a1i mprg ) ACEFZACEGZHZPBDFOBDGHBD
      OPBDIQBJDKACELMN $.

    $( Double restricted existential uniqueness, analogous to ~ 2eu2ex .
       (Contributed by Alexander van der Vekens, 25-Jun-2017.) $)
    2reu2rex $p |- ( E! x e. A E! y e. B ph -> E. x e. A E. y e. B ph ) $=
      ( wreu wrex reurex reximi syl ) ACEFZBDFKBDGACEGZBDGKBDHKLBDACEHIJ $.

    $( A condition allowing swap of restricted "at most one" and restricted 
       existential quantifiers, analogous to ~ 2moswap .
       (Contributed by Alexander van der Vekens, 25-Jun-2017.) $)
    2rmoswap $p |- ( A. x e. A E* y e. B ph 
                   -> ( E* x e. A E. y e. B ph -> E* y e. B E. x e. A ph ) ) $=
      ( wrmo wral cv wcel wa wmo wrex wi df-rmo wal r19.42v df-rex bitri bitr3i
      wex ralbii df-ral moanimv albii bitr4i 2moswap exbii mobii 3imtr4g sylbi
      an12 ) ACEFZBDGCHEIZAJZCKZBDGZACELZBDFZABDLZCEFZMZULUOBDACENUAUPBHDIZUNJZ
      CKZBOZVAUPVBUOMZBOVEUOBDUBVDVFBVBUNCUCUDUEVEVCCTZBKZVCBTZCKZURUTVCBCUFURV
      BUQJZBKVHUQBDNVKVGBVKVBAJZCELZVGVBACEPVMUMVLJZCTVGVLCEQVNVCCUMVBAUKUGRSUH
      RUTUMUSJZCKVJUSCENVOVICVOUNBDLVIUMABDPUNBDQSUHRUIUJUJ $.

    $( Double restricted existential uniqueness implies double restricted 
       uniqueness quantification, analogous to ~ 2exeu .
       (Contributed by Alexander van der Vekens, 25-Jun-2017.) $)
    2rexreu $p |- ( ( E! x e. A E. y e. B ph /\ E! y e. B E. x e. A ph ) 
                  -> E! x e. A E! y e. B ph ) $=
      ( wrex wreu wa wrmo reurmo reurex rmoimi syl 2reurex anim12ci reu5 sylibr
      ) ACEFZBDGZABDFCEGZHACEGZBDFZUABDIZHUABDGSUCTUBSRBDIUCRBDJUARBDACEKLMACBE
      DNOUABDPQ $.
  $}

  ${
    $d x y A $. $d x B $.
    $( Double restricted existential uniqueness. This theorem shows a  
       condition under which a "naive" definition matches the correct one, 
       analogous to ~ 2eu1 .
       (Contributed by Alexander van der Vekens, 25-Jun-2017.) $)
    2reu1 $p |- ( A. x e. A E* y e. B ph -> ( E! x e. A E! y e. B ph 
                <-> ( E! x e. A E. y e. B ph /\ E! y e. B E. x e. A ph ) ) ) $=
      ( wrmo wral wreu wrex wa wi 2reu5a simprbi cv wcel simprr jca sylib com12
      reu5 adantr impcom ex rmoimia nfra1 rmoanim ancrd 2rmoswap imdistani syl6
      ra4 syl 2reu2rex rexcom jctild anbi12i an4 bitri syl6ibr 2rexreu impbid1
      ) ACEFZBDGZACEHBDHZACEIZBDHZABDIZCEHZJZVDVCVIVDVCVEBDIZVGCEIZJZVEBDFZVGCE
      FZJZJZVIVDVCVOVLVDVEVBJZBDFZVCVOKVDVQBDIVRABCDELMVRVCVMVCJVOVRVCVMVRVCVEJ
      ZBDFVCVMKVSVQBDBNDOZVSVQVTVSJVEVBVTVCVEPVSVTVBVCVTVBKVEVBBDUKUAUBQUCUDVCV
      EBDVBBDUEUFRUGVMVCVNVCVMVNABCDEUHSUIUJULVDVJVKABCDEUMZVDVJVKWAABCDEUNRQUO
      VIVJVMJZVKVNJZJVPVFWBVHWCVEBDTVGCETUPVJVMVKVNUQURUSSABCDEUTVA $.

    $( Double restricted existential uniqueness, analogous to ~ 2eu2 .
       (Contributed by Alexander van der Vekens, 29-Jun-2017.) $)
    2reu2 $p |- ( E! y e. B E. x e. A ph 
                  -> ( E! x e. A E! y e. B ph <-> E! x e. A E. y e. B ph ) ) $=
      ( wrex wreu wrmo wral wi reurmo 2rmorex wa 2reu1 simpl syl6bi 3syl expcom
      2rexreu impbid ) ABDFZCEGZACEGBDGZACEFBDGZUBUACEHACEHBDIZUCUDJUACEKACBEDL
      UEUCUDUBMUDABCDENUDUBOPQUDUBUCABCDESRT $.
  $}

  ${
    $d x y A $. $d x y B $.
    $( Double restricted existential uniqueness, analogous to ~ 2eu3 .
       (Contributed by Alexander van der Vekens, 29-Jun-2017.) $)
    2reu3 $p |- ( A. x e. A A. y e. B ( E* x e. A ph \/ E* y e. B ph ) ->
                ( ( E! x e. A E! y e. B ph /\ E! y e. B E! x e. A ph ) 
                <-> ( E! x e. A E. y e. B ph /\ E! y e. B E. x e. A ph ) ) ) $=
      ( wrmo wo wral wreu wa wrex orcom ralbii nfrmo1 r19.32 bitri 2reu1 biimpd
      wb 2rexreu nfcv nfral wi ancom syl6ib adantld adantrd jaoi ancoms impbid1
      jca sylbi ) ABDFZACEFZGZCEHZBDHZUMCEHZUNBDHZGZACEIBDIZABDICEIZJZACEKBDIZA
      BDKCEIZJZSUQURUNGZBDHUTUPVGBDUPUNURGZVGUPUNUMGZCEHVHUOVICEUMUNLMUNUMCEACE
      NOPUNURLPMURUNBDUMBCEBEUAABDNUBOPUTVCVFURVCVFUCUSURVBVFVAURVBVEVDJZVFURVB
      VJACBEDQRVEVDUDUEUFUSVAVFVBUSVAVFABCDEQRUGUHVFVAVBABCDETVEVDVBACBEDTUIUKU
      JUL $.
  $}

  ${
    $d z w ph $. $d w x y z A $.  $d w x y z B $. 
    $( Definition of double restricted existential uniqueness ("exactly one 
       ` x ` and exactly one ` y ` "), analogous to ~ 2eu4 with the additional 
       requirement that the restricting classes are not empty (which is not
       necessary as shown in ~ 2reu4 ).
       (Contributed by Alexander van der Vekens, 1-Jul-2017.) $)
    2reu4a $p |- ( ( A =/= (/) /\ B =/= (/) ) 
                -> ( ( E! x e. A E. y e. B ph /\ E! y e. B E. x e. A ph ) <->
                    ( E. x e. A E. y e. B ph  /\ E. z e. A E. w e. B 
                      A. x e. A A. y e. B ( ph -> ( x = z /\ y = w ) ) ) ) ) $=
      ( c0 wne wa wrex wreu weq wi wral wb a1i bitri r19.26 adantr reu3 anbi12i
      an4 rexcom anbi2i anidm cv wcel nfra1 r19.3rz bicomd anbi2d ralbii bitr4d
      jcab syl5rbb ad2antlr ralcom anbi12d syl5bb ralbidv r19.23v 2ralbii wn wo
      wceq df-ne biimpi anim12i olcd dfbi3 sylibr nfv nfim raaan2 syl 2rexbidva
      nfre1 3bitrd reeanv syl6rbb ) FHIZGHIZJZACGKZBFLZABFKZCGLZJZWEBFKZWEBDMZN
      ZBFOZDFKZJZWGCGKZWGCEMZNZCGOZEGKZJZJZWJWPJZWNWTJZJZWJAWKWQJNZCGOZBFOZEGKD
      FKZJWIXBPWDWFWOWHXAWEBDFUAWGCEGUAUBQXBXEPWDWJWNWPWTUCQWDXCWJXDXIXCWJPWDXC
      WJWJJWJWPWJWJACBGFUDUEWJUFRQWDXIWMWSJZEGKDFKXDWDXHXJDEFGWDDUGFUHEUGGUHJZJ
      ZXHAWKNZCGOZAWQNZBFOZJZCGOZBFOZWLWRJZCGOBFOZXJXLXHXNXOCGOZBFOZJZBFOZXSYEX
      NBFOZYCBFOZJZXLXHXNYCBFSXLYHYFYCJZXHXLYGYCYFWDYGYCPZXKWBYJWCWBYCYGYCBFYBB
      FUIUJUKTTULXHYIPXLXHXNYBJZBFOYIXGYKBFXGXMXOJZCGOYKXFYLCGAWKWQUOUMXMXOCGSR
      UMXNYBBFSRQUNUPXLXRYDBFXRXNCGOZXPCGOZJXLYDXNXPCGSXLYMXNYNYCXLXNYMWCXNYMPW
      BXKXNCGXMCGUIUJUQUKYNYCPXLXOCBGFURQUSUTVAUNXSYAPXLXQXTBCFGXNWLXPWRAWKCGVB
      AWQBFVBUBVCQWDYAXJPZXKWDFHVFZGHVFZPZYOWDYPYQJZYPVDZYQVDZJZVEYRWDUUBYSWBYT
      WCUUAWBYTFHVGVHWCUUAGHVGVHVIVJYPYQVKVLWLWRBCFGWEWKCACGVRWKCVMVNWGWQBABFVR
      WQBVMVNVOVPTVSVQWMWSDEFGVTWAUSVS $.

    $( Definition of double restricted existential uniqueness ("exactly one 
       ` x ` and exactly one ` y ` "), analogous to ~ 2eu4 .
       (Contributed by Alexander van der Vekens, 1-Jul-2017.) $)
    2reu4 $p |- ( ( E! x e. A E. y e. B ph /\ E! y e. B E. x e. A ph ) <->
                    ( E. x e. A E. y e. B ph  /\ E. z e. A E. w e. B 
                      A. x e. A A. y e. B ( ph -> ( x = z /\ y = w ) ) ) ) $=
      ( wrex wreu wa c0 wne weq wral reurex rexn0 syl anim12i cv wcel rexlimivv
      wi ne0i a1d adantr 2reu4a pm5.21nii ) ACGHZBFIZABFHZCGIZJFKLZGKLZJZUHBFHZ
      ABDMCEMJUBCGNBFNEGHDFHZJUIULUKUMUIUOULUHBFOUHBFPQUKUJCGHUMUJCGOUJCGPQRUOU
      NUPAUNBCFGBSZFTZCSZGTZJUNAURULUTUMFUQUCGUSUCRUDUAUEABCDEFGUFUG $.
  $}

  ${
    $d x A $.  $d x y B $. 
    $( Two equivalent expressions for double restricted existential uniqueness,
       analogous to ~ 2eu7 .
       (Contributed by Alexander van der Vekens, 2-Jul-2017.) $)
    2reu7 $p |- ( ( E! x e. A E. y e. B ph /\ E! y e. B E. x e. A ph ) <->
                  E! x e. A E! y e. B ( E. x e. A ph /\ E. y e. B ph ) ) $=
      ( wrex wreu wa nfcv nfre1 nfreu reuan ancom reubii 3bitri 3bitr4ri ) ABDF
      ZCEGZACEFZHZBDGRSBDGZHQSHZCEGZBDGUARHRSBDQBCEBEIABDJKLUCTBDUCSQHZCEGSRHTU
      BUDCEQSMNSQCEACEJLSRMONUARMP $.
  $}

  ${
    $d x y A $.  $d x y B $. 
    $( Two equivalent expressions for double restricted existential uniqueness,  
       analogous to ~ 2eu8 . Curiously, we can put ` E! ` on either of the 
       internal conjuncts but not both.  We can also commute 
       ` E! x e. A E! y e. B ` using ~ 2reu7 .  
       (Contributed by Alexander van der Vekens, 2-Jul-2017.) $)
    2reu8 $p |- ( E! x e. A E! y e. B ( E. x e. A ph /\ E. y e. B ph ) <->
                  E! x e. A E! y e. B ( E! x e. A ph /\ E. y e. B ph ) ) $=
      ( wrex wreu wa 2reu2 pm5.32i nfreu1 nfreu reuan ancom reubii nfre1 3bitri
      nfcv 3bitr4ri 2reu7 3bitr3ri ) ACEFZBDGZABDGZCEGZHZUCABDFZCEGZHUDUBHZCEGZ
      BDGZUGUBHCEGBDGUCUEUHACBEDIJUEUBHZBDGUEUCHUKUFUEUBBDUDBCEBERABDKLMUJULBDU
      JUBUDHZCEGUBUEHULUIUMCEUDUBNOUBUDCEACEPMUBUENQOUCUENSABCDETUA $.
  $}

$( (End of Alexander van der Vekens's mathbox.) $)

