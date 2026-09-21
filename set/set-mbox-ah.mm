$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Anthony Hart
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Propositional Calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( The first of three axioms in the Tarski-Bernays axiom system.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tb-ax1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( imim1 ) ABCD $.

  $( The second of three axioms in the Tarski-Bernays axiom system.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tb-ax2 $p |- ( ph -> ( ps -> ph ) ) $=
    ( ax-1 ) ABC $.

  $( The third of three axioms in the Tarski-Bernays axiom system.

     This axiom, along with ~ ax-mp , ~ tb-ax1 , and ~ tb-ax2 , can be used to
     derive any theorem or rule that uses only ` -> ` .  (Contributed by
     Anthony Hart, 16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  tb-ax3 $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    ( peirce ) ABC $.

  ${
    tbsyl.1 $e |- ( ph -> ps ) $.
    tbsyl.2 $e |- ( ps -> ch ) $.
    $( The weak syllogism from Tarski-Bernays'.  (Contributed by Anthony Hart,
       16-Aug-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    tbsyl $p |- ( ph -> ch ) $=
      ( wi tb-ax1 ax-mp ) BCFZACFZEABFIJFDABCGHH $.
  $}

  $( Lemma for ~ re1ax2 .  (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  re1ax2lem $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi tb-ax2 tb-ax1 tbsyl tb-ax3 mpsyl ) BBCDZCDZDAJDKACDZDBLDBJKDZKBJBDMBJE
    JBCFGMKCDKDKJKCFKCHGGAJCFBKLFI $.

  $( ~ ax-2 rederived from the Tarski-Bernays axiom system.  Often ~ tb-ax1 is
     replaced with this theorem to make a "standard" system.  This is because
     this theorem is easier to work with, despite it being longer.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  re1ax2 $p |-
              ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( wi re1ax2lem tb-ax1 tb-ax3 tbsyl ax-mp mpsyl ) ABCDDBACDZDZABDZKDZABCEAKD
    ZKDZLMODZNOKCDKDKAKCFKCGHMLODDLQDABKFMLOEIQPNDDPQNDDMOKFQPNEIJH $.

  $( Constructor theorem for ` -/\ ` .  (Contributed by Anthony Hart,
     1-Sep-2011.) $)
  naim1 $p |- ( ( ph -> ps ) -> ( ( ps -/\ ch ) -> ( ph -/\ ch ) ) ) $=
    ( wi wn wo wnan con3 orim1d wa pm3.13 pm3.14 imim12i df-nan 3imtr4g syl ) A
    BDZBEZCEZFZAEZSFZDZBCGZACGZDQRUASABHIUCBCJEZACJEZUDUEUFTUBUGBCKACLMBCNACNOP
    $.

  $( Constructor theorem for ` -/\ ` .  (Contributed by Anthony Hart,
     1-Sep-2011.) $)
  naim2 $p |- ( ( ph -> ps ) -> ( ( ch -/\ ps ) -> ( ch -/\ ph ) ) ) $=
    ( wi wn wo wnan con3 orim2d wa pm3.13 pm3.14 imim12i df-nan 3imtr4g syl ) A
    BDZCEZBEZFZRAEZFZDZCBGZCAGZDQSUARABHIUCCBJEZCAJEZUDUEUFTUBUGCBKCALMCBNCANOP
    $.

  ${
    naim1i.1 $e |- ( ph -> ps ) $.
    naim1i.2 $e |- ( ps -/\ ch ) $.
    $( Constructor rule for ` -/\ ` .  (Contributed by Anthony Hart,
       2-Sep-2011.) $)
    naim1i $p |- ( ph -/\ ch ) $=
      ( wi wnan naim1 mp2 ) ABFBCGACGDEABCHI $.
  $}

  ${
    naim2i.1 $e |- ( ph -> ps ) $.
    naim2i.2 $e |- ( ch -/\ ps ) $.
    $( Constructor rule for ` -/\ ` .  (Contributed by Anthony Hart,
       2-Sep-2011.) $)
    naim2i $p |- ( ch -/\ ph ) $=
      ( wi wnan naim2 mp2 ) ABFCBGCAGDEABCHI $.
  $}

  ${
    naim12i.1 $e |- ( ph -> ps ) $.
    naim12i.2 $e |- ( ch -> th ) $.
    naim12i.3 $e |- ( ps -/\ th ) $.
    $( Constructor rule for ` -/\ ` .  (Contributed by Anthony Hart,
       2-Sep-2011.) $)
    naim12i $p |- ( ph -/\ ch ) $=
      ( naim1i naim2i ) CDAFABDEGHI $.
  $}

  ${
    nabi1i.1 $e |- ( ph <-> ps ) $.
    nabi1i.2 $e |- ( ps -/\ ch ) $.
    $( Constructor rule for ` -/\ ` .  (Contributed by Anthony Hart,
       2-Sep-2011.) $)
    nabi1i $p |- ( ph -/\ ch ) $=
      ( wnan bicomi nanbi1i mpbi ) BCFACFEBACABDGHI $.
  $}

  ${
    nabi2i.1 $e |- ( ph <-> ps ) $.
    nabi2i.2 $e |- ( ch -/\ ps ) $.
    $( Constructor rule for ` -/\ ` .  (Contributed by Anthony Hart,
       2-Sep-2011.) $)
    nabi2i $p |- ( ch -/\ ph ) $=
      ( wnan bicomi nanbi2i mpbi ) CBFCAFEBACABDGHI $.
  $}

  ${
    nabi12i.1 $e |- ( ph <-> ps ) $.
    nabi12i.2 $e |- ( ch <-> th ) $.
    nabi12i.3 $e |- ( ps -/\ th ) $.
    $( Constructor rule for ` -/\ ` .  (Contributed by Anthony Hart,
       2-Sep-2011.) $)
    nabi12i $p |- ( ph -/\ ch ) $=
      ( nabi1i nabi2i ) CDAFABDEGHI $.
  $}

  $( The double nand. $)
  w3nand $a wff ( ph -/\ ps -/\ ch ) $.

  $( The double nand.  This definition allows to express the input of three
     variables only being false if all three are true.  (Contributed by Anthony
     Hart, 2-Sep-2011.) $)
  df-3nand $a |- ( ( ph -/\ ps -/\ ch ) <-> ( ph -> ( ps -> -. ch ) ) ) $.

  $( The double nand expressed in terms of pure nand.  (Contributed by Anthony
     Hart, 2-Sep-2011.) $)
  df3nandALT1 $p |- ( ( ph -/\ ps -/\ ch ) <->
                            ( ph -/\ ( ( ps -/\ ch ) -/\ ( ps -/\ ch ) ) ) ) $=
    ( wn wi wnan wa w3nand iman biimpi jca biranri impbii df-nan anbi12i bitr4i
    imnan imbi2i anbi2i 3bitr4i notbii df-3nand ) ABCDEZEZABCFZUEFZGZDZABCHAUFF
    AUEUEGZEAUIDZGZDUDUHAUIIUCUIAUCBCGDZULGZUIUCUMUCULULUCULBCQZJZUOKUCULULUNLM
    UEULUEULBCNZUPOPRUGUKUFUJAUEUENSUATABCUBAUFNT $.

  $( The double nand expressed in terms of negation and and not.  (Contributed
     by Anthony Hart, 13-Sep-2011.) $)
  df3nandALT2 $p |- ( ( ph -/\ ps -/\ ch ) <-> -. ( ph /\ ps /\ ch ) ) $=
    ( w3nand wn wi wa w3a df-3nand imnan imbi2i 3anass xchbinxr 3bitri ) ABCDAB
    CEFZFABCGZEZFZABCHZEABCIOQABCJKRAPGSAPJABCLMN $.

  $( Double and in terms of double nand.  (Contributed by Anthony Hart,
     2-Sep-2011.) $)
  andnand1 $p |- ( ( ph /\ ps /\ ch ) <->
                         ( ( ph -/\ ps -/\ ch ) -/\ ( ph -/\ ps -/\ ch ) ) ) $=
    ( w3a wn wi w3nand wnan wa 3anass pm4.63 anbi2i annim 3bitr2i notbii nannot
    df-3nand ) ABCDZABCEFZFZEZABCGZEUBUBHRABCIZIASEZIUAABCJUDUCABCKLASMNUBTABCQ
    OUBPN $.

  $( An ` -> ` nand relation.  (Contributed by Anthony Hart, 2-Sep-2011.) $)
  imnand2 $p |- ( ( -. ph -> ps ) <-> ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) $=
    ( wn wa wnan wi nannot anbi12i notbii iman df-nan 3bitr4i ) ACZBCZDZCAAEZBB
    EZDZCMBFPQEORMPNQAGBGHIMBJPQKL $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Predicate Calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Not all sets hold ` F. ` as true.  (Contributed by Anthony Hart,
     13-Sep-2011.) $)
  nalfal $p |- -. A. x F. $=
    ( wfal wal wn alfal falim sps mt2 ) BACBDACZAEBIDZAJFGH $.

  $( There does not exist a set such that ` T. ` is not true.  (Contributed by
     Anthony Hart, 13-Sep-2011.) $)
  nexntru $p |- -. E. x -. T. $=
    ( wtru wn tru notnoti nex ) BCABDEF $.

  $( There does not exist a set such that ` F. ` is true.  (Contributed by
     Anthony Hart, 13-Sep-2011.) $)
  nexfal $p |- -. E. x F. $=
    ( wfal fal nex ) BACD $.

  $( There does not exist exactly one set such that ` F. ` is true.
     (Contributed by Anthony Hart, 13-Sep-2011.) $)
  neufal $p |- -. E! x F. $=
    ( wfal weu wex nexfal euex mto ) BACBADAEBAFG $.

  $( There does not exist exactly one set such that ` T. ` is true.
     (Contributed by Anthony Hart, 13-Sep-2011.) $)
  neutru $p |- -. E! x T. $=
    ( wtru weu wn wex nexntru eunex mto ) BACBDAEAFBAGH $.

  $( There does not exist at most one set such that ` T. ` is true.
     (Contributed by Anthony Hart, 13-Sep-2011.) $)
  nmotru $p |- -. E* x T. $=
    ( wtru wmo wex weu wi wn extru neutru jcn mp2 moeu mtbir ) BACBADZBAEZFZNOG
    PGAHAINOJKBALM $.

  $( There exist at most one set such that ` F. ` is true.  (Contributed by
     Anthony Hart, 13-Sep-2011.) $)
  mofal $p |- E* x F. $=
    ( wfal wex wmo nexfal exmo mtpor ) BACBADAEBAFG $.

  ${
    nrmo.1 $e |- ( x e. A -> -. ph ) $.
    $( "At most one" restricted existential quantifier for a statement which is
       never true.  (Contributed by Thierry Arnoux, 27-Nov-2023.) $)
    nrmo $p |- E* x e. A ph $=
      ( wrmo cv wcel wa wmo wfal mofal wn imori ianor mpbir bifal mobii df-rmo
      wo ) ABCEBFCGZAHZBIZUBJBIBKUAJBUAUALTLALZSTUCDMTANOPQOABCRO $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Miscellaneous single axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A single axiom for propositional calculus discovered by C. A. Meredith.
     (Contributed by Anthony Hart, 13-Aug-2011.) $)
  meran1 $p |- ( -. ( -. ( -. ph \/ ps ) \/ ( ch \/ ( th \/ ta ) ) ) \/
                          ( -. ( -. th \/ ph ) \/ ( ch \/ ( ta \/ ph ) ) ) ) $=
    ( wn wo wi orc olc imim1i pm2.24 idd jaod com12 pm1.5 imor 3imtr3i orim2i
    ja pm2.3 pm2.21 jcn imim12i pm2.43d con4d 4syl 3syl 3imtr4i syl2im imori )
    AFZBGZFCDEGZGZGZDFZAGZFCEAGZGZGZUMUOHZURUTHUPVAVBABHZUOHZURDAHZUTVCUMUOABUM
    ULBIBULJTKDURADUQAADALDAMNOVCFZUOGZVEFZUTGZVDVEUTHVGCVFUNGZGCVHUSGZGVIVFCUN
    PVJVKCVJVFEDGGEVFDGZGEVHAGZGVKVFDEUAVFEDPVLVMEVCDHZVEAHVLVMVNAVEVNULVHULVCD
    ULVHHABUBDAUCUDUEUFVCDQVEAQRSEVHAPUGSCVHUSPUHVCUOQVEUTQUIUJUMUOQURUTQRUK $.

  $( A single axiom for propositional calculus discovered by C. A. Meredith.
     (Contributed by Anthony Hart, 13-Aug-2011.) $)
  meran2 $p |- ( -. ( -. ( -. ph \/ ps ) \/ ( ch \/ ( th \/ ta ) ) ) \/
                          ( -. ( -. ta \/ th ) \/ ( ch \/ ( ph \/ th ) ) ) ) $=
    ( wn wo meran1 imorri syl imori ) AFBGFCDEGGGZEFDGFCADGGGZLDFAGFCEAGGGZMLNA
    BCDEHINMDACEAHIJK $.

  $( A single axiom for propositional calculus discovered by C. A. Meredith.
     (Contributed by Anthony Hart, 13-Aug-2011.) $)
  meran3 $p |- ( -. ( -. ( -. ph \/ ps ) \/ ( ch \/ ( th \/ ta ) ) ) \/
                          ( -. ( -. ch \/ ph ) \/ ( ta \/ ( th \/ ph ) ) ) ) $=
    ( wn wo wi pm2.3 imim2i pm1.5 syl6 imor 3imtr3i meran1 imorri syl imori ) A
    FBGZFZCDEGGZGZCFAGFEDAGGGZUBTECDGGZGZUCSUAHZSUDHUBUEUFSCEDGGZUDUAUGSCDEIJCE
    DKLSUAMSUDMNUEUCABECDOPQR $.

  $( A single axiom for propositional calculus discovered by Mordchaj Wajsberg
     (Logical Works, Polish Academy of Sciences, 1977).  See:  Fitelson, _Some
     recent results in algebra and logical calculi obtained using automated
     reasoning_, 2003 (axiom W on slide 8).  (Contributed by Anthony Hart,
     13-Aug-2011.) $)
  waj-ax $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ ( ( ( th -/\ ch ) -/\
      ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) -/\ ( ph -/\ ( ph -/\ ps ) ) ) ) $=
    ( wnan wa wi nannan simpr imim2i pm2.27 anim2d expdimp syl5com con3d df-nan
    wn 3imtr4g nanim sylib pm3.21 adantr com12 a2i sylibr jca sylbi mpbir ) ABC
    EEZDCEZADEZUKEEZAABEEZEEUIULUMFZGUIABCFZGZUNABCHUPULUMUPUJUKGULUPDCFZQADFZQ
    UJUKUPURUQUPACGZURUQUOCABCIJADUSUQAUSCDACKLMNODCPADPRUJUKSTUPAABFZGZUMAUOUT
    UOAUTBVACBAUAUBUCUDAABHUEUFUGUIULUMHUH $.

  $( A single axiom for propositional calculus discovered by Jan Lukasiewicz.
     See:  Fitelson, _Some recent results in algebra and logical calculi
     obtained using automated reasoning_, 2003 (axiom L2 on slide 8).
     (Contributed by Anthony Hart, 14-Aug-2011.) $)
  lukshef-ax2 $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ ( ( ph -/\ ( ch -/\ ph ) )
           -/\ ( ( th -/\ ps ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( wnan wa wi nannan biimpi simpr imim2i simpl pm2.27 anim2d expdimp syl5com
    ancr anim1i wn df-nan syl2anc con3 3imtr4g biimpri nanim anim12i 4syl mpbir
    anim2i ) ABCEEZACAEEZDBEZADEZUMEEZEEUJUKUNFZGUJABCFZGZACAFGZADFZDBFZGZFZURU
    LUMGZFUOUJUQABCHIUQACGZVAVBUPCABCJKUQABGZUSUTUPBABCLKADVEUTAVEBDABMNOPVDURV
    AACQRUAVAVCURVAUTSUSSULUMUSUTUBDBTADTUCUIURUKVCUNUKURACAHUDVCUNULUMUEIUFUGU
    JUKUNHUH $.

  $( A single axiom for propositional calculus discovered by Ken Harris and
     Branden Fitelson.  See:  Fitelson, _Some recent results in algebra and
     logical calculi obtained using automated reasoning_, 2003 (axiom HF1 on
     slide 8).  (Contributed by Anthony Hart, 14-Aug-2011.) $)
  arg-ax $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ ( ( ph -/\ ( ps -/\ ch ) )
           -/\ ( ( th -/\ ch ) -/\ ( ( ch -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( wnan wa wi wn df-nan wo pm4.57 com12 pm3.45 anim12i jaob 3imtr4i biimtrid
    syl6 biimpri nannan orel2 simpr a1i jad syl pm3.22 con1d ancli mpbir ) ABCE
    EZUJDCEZCDEZADEZEEZEEUJUJUNFGUJUNABCFZGZUKULUMFZGUJUNUKDCFZHZUPUQDCIUPUSCDF
    ZHZADFZHZFZUQUPVDURVDHUTVBJZUPURUTVBKUPVEUTURUPCAJZCGZVEUTGZVFUPCVFAUOCAHVF
    CACUALUOCGVFBCUBUCUDLCCGZACGZFUTUTGZVBUTGZFVGVHVIVKVJVLCCDMACDMNCCAOUTUTVBO
    PUECDUFRQUGVAULVCUMULVACDISUMVCADISNRQABCTUKULUMTPUHUJUJUNTUI $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Connective Symmetry
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( In the paper "On Variable Functors of Propositional Arguments",
     Lukasiewicz introduced a system that can handle variable connectives.
     This was done by introducing a variable, marked with a lowercase delta,
     which takes a wff as input.  In the system, "delta ` ph ` " means that
     "something is true of ` ph ` ".  The expression "delta ` ph ` " can be
     substituted with ` -. ph ` , ` ps /\ ph ` , ` A. x ph ` , etc.

     Later on, Meredith discovered a single axiom, in the form of ` ( ` delta
     delta ` F. -> ` delta ` ph ` ` ) ` .  This represents the shortest theorem
     in the extended propositional calculus that cannot be derived as an
     instance of a theorem in propositional calculus.

     A symmetry with ` -. ` .  (Contributed by Anthony Hart, 4-Sep-2011.) $)
  negsym1 $p |- ( -. -. F. -> -. ph ) $=
    ( wfal wn fal pm2.24i ) BCACDE $.

  $( A symmetry with ` -> ` .

     See ~ negsym1 for more information.  (Contributed by Anthony Hart,
     4-Sep-2011.) $)
  imsym1 $p |- ( ( ps -> ( ps -> F. ) ) -> ( ps -> ph ) ) $=
    ( wfal wi pm2.21 falim imim2i ja ) BBCDBADBAECABAFGH $.

  $( A symmetry with ` <-> ` .

     See ~ negsym1 for more information.  (Contributed by Anthony Hart,
     4-Sep-2011.) $)
  bisym1 $p |- ( ( ps <-> ( ps <-> F. ) ) -> ( ps <-> ph ) ) $=
    ( wfal wb wn nbfal bibi2i pm5.19 pm2.21i sylbir ) BBCDZDBBEZDZBADZLKBBFGMNB
    HIJ $.

  $( A symmetry with ` /\ ` .

     See ~ negsym1 for more information.  (Contributed by Anthony Hart,
     4-Sep-2011.) $)
  consym1 $p |- ( ( ps /\ ( ps /\ F. ) ) -> ( ps /\ ph ) ) $=
    ( wfal wa wi falim ad2antll pm2.43i ) BBCDDZBADZCIJEZBBKFGH $.

  $( A symmetry with ` \/ ` .

     See ~ negsym1 for more information.  (Contributed by Anthony Hart,
     4-Sep-2011.) $)
  dissym1 $p |- ( ( ps \/ ( ps \/ F. ) ) -> ( ps \/ ph ) ) $=
    ( wo wfal orc falim orim2i jaoi ) BBACBDCBAEDABAFGH $.

  $( A symmetry with ` -/\ ` .

     See ~ negsym1 for more information.  (Contributed by Anthony Hart,
     4-Sep-2011.) $)
  nandsym1 $p |- ( ( ps -/\ ( ps -/\ F. ) ) -> ( ps -/\ ph ) ) $=
    ( wfal wnan wa wn df-nan biimpi anbi2i sylnib simpl fal intnan jctir sylibr
    nsyl ) BBCDZDZBAEZFBADRBBCEFZEZSRBQEZUARUBFBQGHQTBBCGIJSBTBAKCBLMNPBAGO $.

  $( A symmetry with ` A. ` .

     See ~ negsym1 for more information.  (Contributed by Anthony Hart,
     4-Sep-2011.)  (Proof shortened by Mario Carneiro, 11-Dec-2016.) $)
  unisym1 $p |- ( A. x A. x F. -> A. x ph ) $=
    ( wfal wal falim sps ) CBDABDZBCGBGEFF $.

  $( A symmetry with ` E. ` .

     See ~ negsym1 for more information.  (Contributed by Anthony Hart,
     4-Sep-2011.) $)
  exisym1 $p |- ( E. x E. x F. -> E. x ph ) $=
    ( wfal wex nfe1 falim eximi exlimi ) CBDABDBABECABAFGH $.

  $( A symmetry with ` E! ` .

     See ~ negsym1 for more information.  (Contributed by Anthony Hart,
     6-Sep-2011.) $)
  unqsym1 $p |- ( E! x E! x F. -> E! x ph ) $=
    ( wfal weu wex neufal nex euex mto pm2.21i ) CBDZBDZABDLKBEKBBFGKBHIJ $.

  $( A symmetry with ` E* ` .

     See ~ negsym1 for more information.  (Contributed by Anthony Hart,
     13-Sep-2011.) $)
  amosym1 $p |- ( E* x E* x F. -> E* x ph ) $=
    ( wfal wmo mofal a1i moimi ) ACBDZBHABEFG $.

  $( A symmetry with ` [ x / y ] ` .

     See ~ negsym1 for more information.  (Contributed by Anthony Hart,
     11-Sep-2011.) $)
  subsym1 $p |- ( [ y / x ] [ y / x ] F. -> [ y / x ] ph ) $=
    ( wfal wsb sbv falim sylbi sbimi ) DBCEZABCJDADBCFAGHI $.

$( (End of Anthony Hart's mathbox.) $)
