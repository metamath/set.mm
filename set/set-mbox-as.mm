$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Alan Sare
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  We are sad to report the passing of long-time contributor Alan Sare
  (Nov. 9, 1954 - Mar. 23, 2019).

  Alan's first contribution to Metamath was a shorter proof for ~ tfrlem8 in
  2008.

  He developed a tool called "completeusersproof" that assists developing
  proofs using his "virtual deduction" method:
  ~ https://us.metamath.org/other.html#completeusersproof .
  His virtual deduction method is explained in the comment for ~ wvd1 .

  Below are some excerpts from his first emails to NM in 2007:

  ...I have been interested in proving set theory theorems for many years for
  mental exercise.  I enjoy it.  I have used a book by Martin Zuckerman.  It is
  informal.  I am interested in completely and perfectly proving theorems.  Mr.
  Zuckerman leaves out most of the steps of a proof, of course, like most
  authors do, as you have noted.  A complete proof for higher theorems would
  require a volume of writing similar to the Metamath documents.  So I am
  frustrated when I am not capable of constructing a proof and Zuckerman leaves
  out steps I do not understand.  I could search for the steps in other texts,
  but I don't do that too much.  Metamath may be the answer for me....

  ...If we go beyond mathematics, I believe that it is possible to write down
  all human knowledge in a way similar to the way you have explicated large
  areas of mathematics.  Of course, that would be a much, much more difficult
  job.  For example, it is possible to take a hard science like physics,
  construct axioms based on experimental results, and to cast all of physics
  into a collection of axioms and theorems.  Maybe this has already been
  attempted, although I am not familiar with it.  When one then moves on to the
  soft sciences such as social science, this job gets much more difficult.  The
  key is:  All human thought consists of logical operations on abstract
  objects.  Usually, these logical operations are done informally.  There is no
  reason why one cannot take any subject and explicate it and take it down to
  the indivisible postulates in a formal rigorous way....

  ...When I read a math book or an engineering book I come across something I
  don't understand and I am compelled to understand it.  But, often it is
  hopeless.  I don't have the time.  Or, I would have to read the same thing by
  multiple authors in the hope that different authors would give parts of the
  working proof that others have omitted.  It is very inefficient.  Because I
  have always been inclined to "get to the bottom" for a 100% fully understood
  proof....

$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Auxiliary theorems for the Virtual Deduction tool
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    idiALT.1 $e |- ph $.
    $( Placeholder for ~ idi .  Though unnecessary, this theorem is sometimes
       used in proofs in this mathbox for pedagogical purposes.  (Contributed
       by Alan Sare, 31-Dec-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    idiALT $p |- ph $=
      (  ) B $.
  $}

  $( Exportation implication also converting the consequent from a
     biconditional to an implication.  Derived automatically from ~ exbirVD .
     (Contributed by Alan Sare, 31-Dec-2011.) $)
  exbir $p |- ( ( ( ph /\ ps ) -> ( ch <-> th ) ) ->
              ( ph -> ( ps -> ( th -> ch ) ) ) ) $=
    ( wa wb wi biimpr imim2i expd ) ABEZCDFZGABDCGZLMKCDHIJ $.

  $( Version of ~ 3impexp where in addition the consequent is commuted.
     (Contributed by Alan Sare, 31-Dec-2011.) $)
  3impexpbicom $p |- ( ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) <->
                     ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) ) $=
    ( w3a wb wi bicom imbi2 biimpcd mpi 3expd 3impexp biimpri imbitrrdi impbii
    ) ABCFZDEGZHZABCEDGZHHHZTABCUATSUAGZRUAHZDEIZUCTUDSUARJKLMUBRUASUDUBABCUANO
    UEPQ $.

  ${
    3impexpbicomi.1 $e |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) $.
    $( Inference associated with ~ 3impexpbicom .  Derived automatically from
       ~ 3impexpbicomiVD .  (Contributed by Alan Sare, 31-Dec-2011.) $)
    3impexpbicomi $p |- ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) $=
      ( wb w3a bicomd 3exp ) ABCEDGABCHDEFIJ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Supplementary unification deductions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    bi1imp.1 $e |- ( ph <-> ( ps -> ch ) ) $.
    $( Importation inference similar to ~ imp , except the outermost
       implication of the hypothesis is a biconditional.  (Contributed by Alan
       Sare, 6-Nov-2017.) $)
    bi1imp $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wi biimpi imp ) ABCABCEDFG $.
  $}

  ${
    bi2imp.1 $e |- ( ph <-> ( ps <-> ch ) ) $.
    $( Importation inference similar to ~ imp , except both implications of the
       hypothesis are biconditionals.  (Contributed by Alan Sare,
       6-Nov-2017.) $)
    bi2imp $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wb biimpi biimpa ) ABCABCEDFG $.
  $}

  ${
    bi3impb.1 $e |- ( ( ph /\ ( ps /\ ch ) ) <-> th ) $.
    $( Similar to ~ 3impb with implication in hypothesis replaced by
       biconditional.  (Contributed by Alan Sare, 6-Nov-2017.) $)
    bi3impb $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wa biimpi 3impb ) ABCDABCFFDEGH $.
  $}

  ${
    bi3impa.1 $e |- ( ( ( ph /\ ps ) /\ ch ) <-> th ) $.
    $( Similar to ~ 3impa with implication in hypothesis replaced by
       biconditional.  (Contributed by Alan Sare, 6-Nov-2017.) $)
    bi3impa $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wa biimpi 3impa ) ABCDABFCFDEGH $.
  $}

  ${
    bi23impib.1 $e |- ( ph -> ( ( ps /\ ch ) <-> th ) ) $.
    $( ~ 3impib with the inner implication of the hypothesis a biconditional.
       (Contributed by Alan Sare, 6-Nov-2017.) $)
    bi23impib $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wa biimpd 3impib ) ABCDABCFDEGH $.
  $}

  ${
    bi13impib.1 $e |- ( ph <-> ( ( ps /\ ch ) -> th ) ) $.
    $( ~ 3impib with the outer implication of the hypothesis a biconditional.
       (Contributed by Alan Sare, 6-Nov-2017.) $)
    bi13impib $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wa wi biimpi 3impib ) ABCDABCFDGEHI $.
  $}

  ${
    bi123impib.1 $e |- ( ph <-> ( ( ps /\ ch ) <-> th ) ) $.
    $( ~ 3impib with the implications of the hypothesis biconditionals.
       (Contributed by Alan Sare, 6-Nov-2017.) $)
    bi123impib $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wa wb biimpi bi23impib ) ABCDABCFDGEHI $.
  $}

  ${
    bi13impia.1 $e |- ( ( ph /\ ps ) <-> ( ch -> th ) ) $.
    $( ~ 3impia with the outer implication of the hypothesis a biconditional.
       (Contributed by Alan Sare, 6-Nov-2017.) $)
    bi13impia $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wa wi biimpi 3impia ) ABCDABFCDGEHI $.
  $}

  ${
    bi123impia.1 $e |- ( ( ph /\ ps ) <-> ( ch <-> th ) ) $.
    $( ~ 3impia with the implications of the hypothesis biconditionals.
       (Contributed by Alan Sare, 6-Nov-2017.) $)
    bi123impia $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wa wb biimpi biimp3a ) ABCDABFCDGEHI $.
  $}

  ${
    bi33imp12.1 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( ~ 3imp with innermost implication of the hypothesis a biconditional.
       (Contributed by Alan Sare, 6-Nov-2017.) $)
    bi33imp12 $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wb wi biimp syl6 3imp ) ABCDABCDFCDGECDHIJ $.
  $}

  ${
    bi13imp23.1 $e |- ( ph <-> ( ps -> ( ch -> th ) ) ) $.
    $( ~ 3imp with outermost implication of the hypothesis a biconditional.
       (Contributed by Alan Sare, 6-Nov-2017.) $)
    bi13imp23 $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wi biimpi 3imp ) ABCDABCDFFEGH $.
  $}

  ${
    bi13imp2.1 $e |- ( ph <-> ( ps -> ( ch <-> th ) ) ) $.
    $( Similar to ~ 3imp except the outermost and innermost implications are
       biconditionals.  (Contributed by Alan Sare, 6-Nov-2017.) $)
    bi13imp2 $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wb wi biimpi bi33imp12 ) ABCDABCDFGEHI $.
  $}

  ${
    bi12imp3.1 $e |- ( ph <-> ( ps <-> ( ch -> th ) ) ) $.
    $( Similar to ~ 3imp except all but innermost implication are
       biconditionals.  (Contributed by Alan Sare, 6-Nov-2017.) $)
    bi12imp3 $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wi wb biimpi bi23imp13 ) ABCDABCDFGEHI $.
  $}

  ${
    bi23imp1.1 $e |- ( ph -> ( ps <-> ( ch <-> th ) ) ) $.
    $( Similar to ~ 3imp except all but outermost implication are
       biconditionals.  (Contributed by Alan Sare, 6-Nov-2017.) $)
    bi23imp1 $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wb wi biimp biimtrdi 3imp ) ABCDABCDFCDGECDHIJ $.
  $}

  ${
    bi23imp0.1 $e |- ( ph <-> ( ps <-> ( ch <-> th ) ) ) $.
    $( Similar to ~ 3imp except all implications are biconditionals.
       (Contributed by Alan Sare, 6-Nov-2017.) $)
    bi123imp0 $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wb wi biimp syl6 sylbi 3imp ) ABCDABCDFZFZBCDGZGEMBLNBLHCDHIJK $.
  $}

  ${
    4animp1.1 $e |- ( ( ph /\ ps /\ ch ) -> ( ta <-> th ) ) $.
    $( A single hypothesis unification deduction with an assertion which is an
       implication with a 4-right-nested conjunction antecedent.  (Contributed
       by Alan Sare, 30-May-2018.) $)
    4animp1 $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $=
      ( wa simpr wb ad4ant123 mpbird ) ABGCGZDGEDLDHABCEDIDFJK $.
  $}

  ${
    4an31.1 $e |- ( ( ( ( ch /\ ps ) /\ ph ) /\ th ) -> ta ) $.
    $( A rearrangement of conjuncts for a 4-right-nested conjunction.
       (Contributed by Alan Sare, 30-May-2018.) $)
    4an31 $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $=
      ( wa an31 sylanb ) ABGCGCBGAGDEABCHFI $.
  $}

  ${
    4an4132.1 $e |- ( ( ( ( th /\ ch ) /\ ps ) /\ ph ) -> ta ) $.
    $( A rearrangement of conjuncts for a 4-right-nested conjunction.
       (Contributed by Alan Sare, 30-May-2018.) $)
    4an4132 $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $=
      ( wa simpr simplr jca simpllr simplll syl21anc ) ABGZCGZDGZDCGBAEPDCODHNC
      DIJABCDKABCDLFM $.
  $}

  $( Biconditional form of ~ expcomd .  (Contributed by Alan Sare,
     22-Jul-2012.)  (New usage is discouraged.) $)
  expcomdg $p |- ( ( ph -> ( ( ps /\ ch ) -> th ) ) <->
                                          ( ph -> ( ch -> ( ps -> th ) ) ) ) $=
    ( wa wi ancomst impexp bitri imbi2i ) BCEDFZCBDFFZAKCBEDFLBCDGCBDHIJ $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Conventional Metamath proofs, some derived from VD proofs
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( ~ idn3 without virtual deduction connectives.  Special theorem needed for
     the Virtual Deduction translation tool.  (Contributed by Alan Sare,
     23-Jul-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  iidn3 $p |- ( ph -> ( ps -> ( ch -> ch ) ) ) $=
    ( wi id 2a1i ) CCDABCEF $.

  ${
    ee222.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee222.2 $e |- ( ph -> ( ps -> th ) ) $.
    ee222.3 $e |- ( ph -> ( ps -> ta ) ) $.
    ee222.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( ~ e222 without virtual deduction connectives.  Special theorem needed
       for the Virtual Deduction translation tool.  (Contributed by Alan Sare,
       7-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee222 $p |- ( ph -> ( ps -> et ) ) $=
      ( wa imp syl3c ex ) ABFABKCDEFABCGLABDHLABEILJMN $.
  $}

  ${
    ee3bir.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    ee3bir.2 $e |- ( ta <-> th ) $.
    $( Right-biconditional form of ~ e3 without virtual deduction connectives.
       Special theorem needed for the Virtual Deduction translation tool.
       (Contributed by Alan Sare, 22-Jul-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ee3bir $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( biimpri syl8 ) ABCDEFEDGHI $.
  $}

  ${
    ee13.1 $e |- ( ph -> ps ) $.
    ee13.2 $e |- ( ph -> ( ch -> ( th -> ta ) ) ) $.
    ee13.3 $e |- ( ps -> ( ta -> et ) ) $.
    $( ~ e13 without virtual deduction connectives.  Special theorem needed for
       the Virtual Deduction translation tool.  (Contributed by Alan Sare,
       28-Oct-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee13 $p |- ( ph -> ( ch -> ( th -> et ) ) ) $=
      ( wi syl syl6d ) ACDEFHABEFJGIKL $.
  $}

  ${
    ee121.1 $e |- ( ph -> ps ) $.
    ee121.2 $e |- ( ph -> ( ch -> th ) ) $.
    ee121.3 $e |- ( ph -> ta ) $.
    ee121.4 $e |- ( ps -> ( th -> ( ta -> et ) ) ) $.
    $( ~ e121 without virtual deductions.  (Contributed by Alan Sare,
       13-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee121 $p |- ( ph -> ( ch -> et ) ) $=
      ( a1d ee222 ) ACBDEFABCGKHAECIKJL $.
  $}

  ${
    ee122.1 $e |- ( ph -> ps ) $.
    ee122.2 $e |- ( ph -> ( ch -> th ) ) $.
    ee122.3 $e |- ( ph -> ( ch -> ta ) ) $.
    ee122.4 $e |- ( ps -> ( th -> ( ta -> et ) ) ) $.
    $( ~ e122 without virtual deductions.  (Contributed by Alan Sare,
       13-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee122 $p |- ( ph -> ( ch -> et ) ) $=
      ( a1d ee222 ) ACBDEFABCGKHIJL $.
  $}

  ${
    ee333.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    ee333.2 $e |- ( ph -> ( ps -> ( ch -> ta ) ) ) $.
    ee333.3 $e |- ( ph -> ( ps -> ( ch -> et ) ) ) $.
    ee333.4 $e |- ( th -> ( ta -> ( et -> ze ) ) ) $.
    $( ~ e333 without virtual deductions.  (Contributed by Alan Sare,
       17-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee333 $p |- ( ph -> ( ps -> ( ch -> ze ) ) ) $=
      ( w3a 3imp syl3c 3exp ) ABCGABCLDEFGABCDHMABCEIMABCFJMKNO $.
  $}

  ${
    ee323.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    ee323.2 $e |- ( ph -> ( ps -> ta ) ) $.
    ee323.3 $e |- ( ph -> ( ps -> ( ch -> et ) ) ) $.
    ee323.4 $e |- ( th -> ( ta -> ( et -> ze ) ) ) $.
    $( ~ e323 without virtual deductions.  (Contributed by Alan Sare,
       17-Apr-2012.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee323 $p |- ( ph -> ( ps -> ( ch -> ze ) ) ) $=
      ( a1dd ee333 ) ABCDEFGHABECILJKM $.
  $}

  $( If the second and third disjuncts of a true triple disjunction are false,
     then the first disjunct is true.  Automatically derived from
     ~ 3ornot23VD .  (Contributed by Alan Sare, 31-Dec-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  3ornot23 $p |- ( ( -. ph /\ -. ps ) -> ( ( ch \/ ph \/ ps ) -> ch ) ) $=
    ( wn w3o wi idd pm2.21 3jaao 3anidm12 ) ADZBDZCABECFKCCKALBKCGACHBCHIJ $.

  $( ~ orbi1 with order of disjuncts reversed.  Derived from ~ orbi1rVD .
     (Contributed by Alan Sare, 31-Dec-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  orbi1r $p |- ( ( ph <-> ps ) -> ( ( ch \/ ph ) <-> ( ch \/ ps ) ) ) $=
    ( wb id orbi2d ) ABDZABCGEF $.

  $( ~ pm4.39 with a 3-conjunct antecedent.  This proof is ~ 3orbi123VD
     automatically translated and minimized.  (Contributed by Alan Sare,
     31-Dec-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  3orbi123 $p |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) /\ ( ta <-> et ) ) ->
                 ( ( ph \/ ch \/ ta ) <-> ( ps \/ th \/ et ) ) ) $=
    ( wb w3a simp1 simp2 simp3 3orbi123d ) ABGZCDGZEFGZHABCDEFMNOIMNOJMNOKL $.

  $( Closed form of ~ syl5 .  Derived automatically from ~ syl5impVD .
     (Contributed by Alan Sare, 31-Dec-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  syl5imp $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( th -> ps ) ->
                ( ph -> ( th -> ch ) ) ) ) $=
    ( wi pm2.04 imim2d com34 ) ABCEEZDBEDACIBACEDABCFGH $.

  $( The following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.  After the
     User's Proof was completed, it was minimized.  The completed User's Proof
     before minimization is not shown.  (Contributed by Alan Sare,
     18-Mar-2012.)  (Proof modification is discouraged.)
     (New usage is discouraged.)
     <HTML> <TABLE>
     <TR> <TD> 1::    <TD> ` |- ( ( ( ps /\ ch ) -> th ) <-> ( ps -> ( ch -> `
     ` th ) ) ) `
     <TR> <TD> qed:1: <TD> ` |- ( ( ph -> ( ( ps /\ ch ) -> th ) ) <-> ( ph `
     ` -> ( ps -> ( ch -> th ) ) ) ) `
     </TABLE> </HTML> $)
  impexpd $p |- ( ( ph -> ( ( ps /\ ch ) -> th ) ) <->
                 ( ph -> ( ps -> ( ch -> th ) ) ) ) $=
    ( wa wi impexp imbi2i ) BCEDFBCDFFABCDGH $.

  $( The following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant. The
     completed Virtual Deduction Proof (not shown) was minimized.  The
     minimized proof is shown.
     (Contributed by Alan Sare, 18-Mar-2012.)
     (Proof modification is discouraged.)  (New usage is discouraged.)
     <HTML> <TABLE>
     <TR> <TD> 1::      <TD> ` |- ( ( ph -> ( ps -> ( ch -> th ) ) ) `
     ` -> ( ph -> ( ch -> ( ps -> th ) ) ) ) `
     <TR> <TD> 2::      <TD> ` |- ( ( ph -> ( ch -> ( ps -> th ) ) ) `
     ` -> ( ch -> ( ph -> ( ps -> th ) ) ) ) `
     <TR> <TD> 3:1,2:   <TD> ` |- ( ( ph -> ( ps -> ( ch -> th ) ) ) `
     ` -> ( ch -> ( ph -> ( ps -> th ) ) ) ) `
     <TR> <TD> 4::      <TD> ` |- ( ( ch -> ( ph -> ( ps -> th ) ) ) `
     ` -> ( ph -> ( ch -> ( ps -> th ) ) ) ) `
     <TR> <TD> 5::      <TD> ` |- ( ( ph -> ( ch -> ( ps -> th ) ) ) `
     ` -> ( ph -> ( ps -> ( ch -> th ) ) ) ) `
     <TR> <TD> 6:4,5:   <TD> ` |- ( ( ch -> ( ph -> ( ps -> th ) ) ) `
     ` -> ( ph -> ( ps -> ( ch -> th ) ) ) ) `
     <TR> <TD> qed:3,6: <TD> ` |- ( ( ph -> ( ps -> ( ch -> th ) ) ) `
     ` <-> ( ch -> ( ph -> ( ps -> th ) ) ) ) `
     </TABLE> </HTML> $)
  com3rgbi $p |- ( ( ph -> ( ps -> ( ch -> th ) ) ) <->
                 ( ch -> ( ph -> ( ps -> th ) ) ) ) $=
    ( wi pm2.04 com24 com34 impbii ) ABCDEZEEZCABDEZEEZKBACDABJFGMACBDCALFHI $.

  $( The following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.  The
     completed Virtual Deduction Proof (not shown) was minimized.  The
     minimized proof is shown.  (Contributed by Alan Sare, 18-Mar-2012.)
     (Proof modification is discouraged.)  (New usage is discouraged.)
     <HTML> <TABLE>
     <TR> <TD> 1::      <TD> ` |- ( ( ph -> ( ( ps /\ ch ) -> th ) ) `
     ` <-> ( ph -> ( ps -> ( ch -> th ) ) ) ) `
     <TR> <TD> 2::      <TD> ` |- ( ( ps -> ( ch -> ( ph -> th ) ) ) `
     ` <-> ( ph -> ( ps -> ( ch -> th ) ) ) ) `
     <TR> <TD> qed:1,2: <TD> ` |- ( ( ph -> ( ( ps /\ ch ) -> th ) ) `
     ` <-> ( ps -> ( ch -> ( ph -> th ) ) ) ) `
     </TABLE> </HTML> $)
  impexpdcom $p |- ( ( ph -> ( ( ps /\ ch ) -> th ) ) <->
                      ( ps -> ( ch -> ( ph -> th ) ) ) ) $=
    ( wa wi impexpd com3rgbi bitr4i ) ABCEDFFABCDFFFBCADFFFABCDGBCADHI $.

  ${
    ee1111.1 $e |- ( ph -> ps ) $.
    ee1111.2 $e |- ( ph -> ch ) $.
    ee1111.3 $e |- ( ph -> th ) $.
    ee1111.4 $e |- ( ph -> ta ) $.
    ee1111.5 $e |- ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) $.
    $( Non-virtual deduction form of ~ e1111 .  (Contributed by Alan Sare,
       18-Mar-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.)
       The following User's Proof is a Virtual Deduction proof
       completed automatically by the tools program completeusersproof.cmd,
       which invokes Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof
       Assistant.  The completed Virtual Deduction Proof (not shown) was
       minimized.  The minimized proof is shown.
       <HTML> <TABLE>
       <TR> <TD> h1::     <TD> ` |- ( ph -> ps )  `
       <TR> <TD> h2::     <TD> ` |- ( ph -> ch ) `
       <TR> <TD> h3::     <TD> ` |- ( ph -> th ) `
       <TR> <TD> h4::     <TD> ` |- ( ph -> ta ) `
       <TR> <TD> h5::    <TD> ` |- ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) `
       <TR> <TD> 6:1,5:  <TD> ` |- ( ph -> ( ch -> ( th -> ( ta -> et ) ) ) ) `
       <TR> <TD> 7:6:    <TD> ` |- ( ch -> ( ph -> ( th -> ( ta -> et ) ) ) ) `
       <TR> <TD> 8:2,7:  <TD> ` |- ( ph -> ( ph -> ( th -> ( ta -> et ) ) ) ) `
       <TR> <TD> 9:8:     <TD> ` |- ( ph -> ( th -> ( ta -> et ) ) ) `
       <TR> <TD> 10:9:    <TD> ` |- ( th -> ( ph -> ( ta -> et ) ) ) `
       <TR> <TD> 11:3,10: <TD> ` |- ( ph -> ( ph -> ( ta -> et ) ) ) `
       <TR> <TD> 12:11:   <TD> ` |- ( ph -> ( ta -> et ) ) `
       <TR> <TD> 13:12:   <TD> ` |- ( ta -> ( ph -> et ) ) `
       <TR> <TD> 14:4,13: <TD> ` |- ( ph -> ( ph -> et ) ) `
       <TR> <TD> qed:14:  <TD> ` |- ( ph -> et )  `
       </TABLE> </HTML> $)
    ee1111 $p |- ( ph -> et ) $=
      ( wi syl3c mpd ) AEFJABCDEFLGHIKMN $.
  $}

  $( Logical equivalence of a 2-left-nested implication and a 1-left-nested
     implicated
     when two antecedents of the former implication are identical.
     (Contributed by Alan Sare, 18-Mar-2012.)
     (Proof modification is discouraged.)  (New usage is discouraged.)
     The following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant. The
     completed Virtual
     Deduction Proof (not shown) was minimized.  The minimized proof is
     shown.
     <HTML> <TABLE>
     <TR> <TD> 1::      <TD> ` |- ( ( ph -> ( ps -> ( ph -> ch ) ) ) `
     ` -> ( ph -> ( ph -> ( ps -> ch ) ) ) ) `
     <TR> <TD> 2::      <TD> ` |- ( ( ph -> ( ph -> ( ps -> ch ) ) ) `
     ` -> ( ph -> ( ps -> ch ) ) ) `
     <TR> <TD> 3:1,2:   <TD> ` |- ( ( ph -> ( ps -> ( ph -> ch ) ) ) `
     ` -> ( ph -> ( ps -> ch ) ) ) `
     <TR> <TD> 4::      <TD> ` |- ( ( ph -> ( ps -> ch ) ) -> ( ps `
     ` -> ( ph -> ch ) ) ) `
     <TR> <TD> 5:3,4:   <TD> ` |- ( ( ph -> ( ps -> ( ph -> ch ) ) ) `
     ` -> ( ps -> ( ph -> ch ) ) ) `
     <TR> <TD> 6::      <TD> ` |- ( ( ps -> ( ph -> ch ) ) -> ( ph `
     ` -> ( ps -> ( ph -> ch ) ) ) ) `
     <TR> <TD> qed:5,6: <TD> ` |- ( ( ph -> ( ps -> ( ph -> ch ) ) ) `
     ` <-> ( ps -> ( ph -> ch ) ) ) `
     </TABLE> </HTML> $)
  pm2.43bgbi $p |- ( ( ph -> ( ps -> ( ph -> ch ) ) ) <->
               ( ps -> ( ph -> ch ) ) ) $=
    ( wi mercolem6 ax-1 impbii ) ABACDDZDHABCEHAFG $.

  $( Logical equivalence of a 3-left-nested implication and a 2-left-nested
     implicated when two antecedents of the former implication are identical.
     (Contributed by Alan Sare, 18-Mar-2012.)
     (Proof modification is discouraged.)  (New usage is discouraged.)
     The following User's Proof is
     a Virtual Deduction proof completed automatically by the tools program
     completeusersproof.cmd, which invokes Mel L. O'Cat's mmj2 and Norm
     Megill's Metamath Proof Assistant.  The completed Virtual Deduction Proof
     (not shown) was minimized.  The minimized proof is shown.
     <HTML> <TABLE>
     <TR> <TD> 1::      <TD> ` |- ( ( ph -> ( ps -> ( ch -> ( ph -> th ) ) ) `
     ` ) -> ( ph -> ( ps -> ( ph -> ( ch -> th ) ) ) ) ) `
     <TR> <TD> 2::      <TD> ` |- ( ( ph -> ( ps -> ( ph -> ( ch -> th ) ) ) `
     ` ) -> ( ps -> ( ph -> ( ch -> th ) ) ) ) `
     <TR> <TD> 3:1,2:   <TD> ` |- ( ( ph -> ( ps -> ( ch -> ( ph -> th ) ) ) `
     ` ) -> ( ps -> ( ph -> ( ch -> th ) ) ) ) `
     <TR> <TD> 4::      <TD> ` |- ( ( ps -> ( ph -> ( ch -> th ) ) )  `
     ` -> ( ps -> ( ch -> ( ph -> th ) ) ) ) `
     <TR> <TD> 5:3,4:   <TD> ` |- ( ( ph -> ( ps -> ( ch -> ( ph -> th ) ) ) `
     ` ) -> ( ps -> ( ch -> ( ph -> th ) ) ) )  `
     <TR> <TD> 6::      <TD> ` |- ( ( ps -> ( ch -> ( ph -> th ) ) )  `
     ` -> ( ph -> ( ps -> ( ch -> ( ph -> th ) ) ) ) ) `
     <TR> <TD> qed:5,6: <TD> ` |- ( ( ph -> ( ps -> ( ch -> ( ph -> th ) ) ) `
     ` ) <-> ( ps -> ( ch -> ( ph -> th ) ) ) ) `
     </TABLE> </HTML> $)
  pm2.43cbi $p |- ( ( ph -> ( ps -> ( ch -> ( ph -> th ) ) ) ) <->
                   ( ps -> ( ch -> ( ph -> th ) ) ) ) $=
    ( wi wn pm2.24 com4l id ja ax-1 impbii ) ABCADEEEZEMAMMAAFBCDABCDEEGHMIJMAK
    L $.

  ${
    ee233.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee233.2 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
    ee233.3 $e |- ( ph -> ( ps -> ( th -> et ) ) ) $.
    ee233.4 $e |- ( ch -> ( ta -> ( et -> ze ) ) ) $.
    $( Non-virtual deduction form of ~ e233 .  (Contributed by Alan Sare,
       18-Mar-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.)
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant. The
       completed Virtual
       Deduction Proof (not shown) was minimized.  The minimized proof is
       shown.
       <HTML> <TABLE>
       <TR> <TD> h1::     <TD> ` |- ( ph -> ( ps -> ch ) )   `
       <TR> <TD> h2::     <TD> ` |- ( ph -> ( ps -> ( th -> ta ) ) )  `
       <TR> <TD> h3::     <TD> ` |- ( ph -> ( ps -> ( th -> et ) ) )  `
       <TR> <TD> h4::     <TD> ` |- ( ch -> ( ta -> ( et -> ze ) ) ) `
       <TR> <TD> 5:1,4:   <TD> ` |- ( ph -> ( ps -> ( ta -> ( et -> ze ) ) ) `
       ` ) `
       <TR> <TD> 6:5:     <TD> ` |- ( ta -> ( ph -> ( ps -> ( et -> ze ) ) ) `
       ` ) `
       <TR> <TD> 7:2,6:   <TD> ` |- ( ph -> ( ps -> ( th -> ( ph -> ( ps  `
       ` -> ( et -> ze ) ) ) ) ) ) `
       <TR> <TD> 8:7:     <TD> ` |- ( ps -> ( th -> ( ph -> ( ps -> ( et  `
       ` -> ze ) ) ) ) ) `
       <TR> <TD> 9:8:     <TD> ` |- ( th -> ( ph -> ( ps -> ( et -> ze ) ) ) `
       ` ) `
       <TR> <TD> 10:9:    <TD> ` |- ( ph -> ( ps -> ( th -> ( et -> ze ) ) ) `
       ` ) `
       <TR> <TD> 11:10:   <TD> ` |- ( et -> ( ph -> ( ps -> ( th -> ze ) ) ) `
       ` ) `
       <TR> <TD> 12:3,11: <TD> ` |- ( ph -> ( ps -> ( th -> ( ph -> ( ps  `
       ` -> ( th -> ze ) ) ) ) ) ) `
       <TR> <TD> 13:12:   <TD> ` |- ( ps -> ( th -> ( ph -> ( ps -> ( th  `
       ` -> ze ) ) ) ) ) `
       <TR> <TD> 14:13:   <TD> ` |- ( th -> ( ph -> ( ps -> ( th -> ze ) ) ) `
       ` ) `
       <TR> <TD> qed:14:  <TD> ` |- ( ph -> ( ps -> ( th -> ze ) ) ) `
       </TABLE> </HTML> $)
    ee233 $p |- ( ph -> ( ps -> ( th -> ze ) ) ) $=
      ( wi syl6 com3r syl8 pm2.43cbi mpbi com14 ) DABDGLZLZLZLZUABUBLZUBAUCLUCA
      BDFUAJDABFGBDABFGLZLZLZLZLZUGAUHLUHABDEUFIABEUDABCEUDLHKMNOABDUEPQBDAUDPQ
      ROABDTPQBDASPQDABGPQ $.
  $}

  $( Join three logical equivalences to form equivalence of implications.
     ~ imbi13 is ~ imbi13VD without virtual deductions and was automatically
     derived from ~ imbi13VD using the tools program
     translate..without..overwriting.cmd and Metamath's minimize command.
     (Contributed by Alan Sare, 18-Mar-2012.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  imbi13 $p |- ( ( ph <-> ps ) -> ( ( ch <-> th ) -> ( ( ta <-> et ) ->
               ( ( ph -> ( ch -> ta ) ) <-> ( ps -> ( th -> et ) ) ) ) ) ) $=
    ( wb wi imbi12 syl9r ) CDGEFGCEHZDFHZGABGAKHBLHGCDEFIABKLIJ $.

  ${
    ee33.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    ee33.2 $e |- ( ph -> ( ps -> ( ch -> ta ) ) ) $.
    ee33.3 $e |- ( th -> ( ta -> et ) ) $.
    $( Non-virtual deduction form of ~ e33 .  (Contributed by Alan Sare,
       18-Mar-2012.)  (Proof modification is discouraged.)
       (New usage is discouraged.)
       The following User's Proof is a Virtual Deduction proof
       completed automatically by the tools program completeusersproof.cmd,
       which invokes Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof
       Assistant.  The completed Virtual Deduction Proof (not shown) was
       minimized.  The minimized proof is shown.
       <HTML> <TABLE>
       <TR> <TD> h1::   <TD> ` |- ( ph -> ( ps -> ( ch -> th ) ) )  `
       <TR> <TD> h2::   <TD> ` |- ( ph -> ( ps -> ( ch -> ta ) ) )  `
       <TR> <TD> h3::   <TD> ` |- ( th -> ( ta -> et ) ) `
       <TR> <TD> 4:1,3: <TD> ` |- ( ph -> ( ps -> ( ch -> ( ta -> et ) ) ) ) `
       <TR> <TD> 5:4:   <TD> ` |- ( ta -> ( ph -> ( ps -> ( ch -> et ) ) ) ) `
       <TR> <TD> 6:2,5: <TD> ` |- ( ph -> ( ps -> ( ch -> ( ph -> ( ps -> `
       ` ( ch -> et ) ) ) ) ) ) `
       <TR> <TD> 7:6:   <TD> ` |- ( ps -> ( ch -> ( ph -> ( ps -> ( ch -> `
       ` et ) ) ) ) ) `
       <TR> <TD> 8:7:   <TD> ` |- ( ch -> ( ph -> ( ps -> ( ch -> et ) ) ) ) `
       <TR> <TD> qed:8: <TD> ` |- ( ph -> ( ps -> ( ch -> et ) ) ) `
       </TABLE> </HTML> $)
    ee33 $p |- ( ph -> ( ps -> ( ch -> et ) ) ) $=
      ( wi imim3i syl6c ) ABCDJCEJCFJGHDEFCIKL $.
  $}

  $( Biconditional contraposition variation.  This proof is ~ con5VD
     automatically translated and minimized.  (Contributed by Alan Sare,
     21-Apr-2013.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  con5 $p |- ( ( ph <-> -. ps ) -> ( -. ph -> ps ) ) $=
    ( wn wb biimpr con1d ) ABCZDBAAGEF $.

  ${
    con5i.1 $e |- ( ph <-> -. ps ) $.
    $( Inference form of ~ con5 .  (Contributed by Alan Sare, 21-Apr-2013.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    con5i $p |- ( -. ph -> ps ) $=
      ( wn wb wi con5 ax-mp ) ABDEADBFCABGH $.
  $}

  ${
    exlimexi.1 $e |- ( ps -> A. x ps ) $.
    exlimexi.2 $e |- ( E. x ph -> ( ph -> ps ) ) $.
    $( Inference similar to Theorem 19.23 of [Margaris] p. 90.  (Contributed by
       Alan Sare, 21-Apr-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    exlimexi $p |- ( E. x ph -> ps ) $=
      ( wex hbe1 exlimdh pm2.43i ) ACFZBJABCACGDEHI $.
  $}

  ${
    $d x y $.
    $( Equivalence for substitution.  Alternate proof of ~ sb5 .  This proof is
       ~ sb5ALTVD automatically translated and minimized.  (Contributed by Alan
       Sare, 21-Apr-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    sb5ALT $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $=
      ( wsb weq wa wex equsb1 sban simplbi2com mpi spsbe syl wi simpr a1i simpl
      hbs1 sbequ1 com12 syl6c exlimexi impbii ) ABCDZBCEZAFZBGZUDUFBCDZUGUDUEBC
      DZUHBCHUHUIUDUEABCIJKUFBCLMUFUDBABCRUGUFAUEUDUFANUGUEAOPUFUENUGUEAQPUEAUD
      ABCSTUAUBUC $.
  $}

  ${
    eexinst01.1 $e |- E. x ps $.
    eexinst01.2 $e |- ( ph -> ( ps -> ch ) ) $.
    eexinst01.3 $e |- ( ph -> A. x ph ) $.
    eexinst01.4 $e |- ( ch -> A. x ch ) $.
    $( ~ exinst01 without virtual deductions.  (Contributed by Alan Sare,
       21-Apr-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eexinst01 $p |- ( ph -> ch ) $=
      ( wex exlimdh mpi ) ABDICEABCDGHFJK $.
  $}

  ${
    eexinst11.1 $e |- ( ph -> E. x ps ) $.
    eexinst11.2 $e |- ( ph -> ( ps -> ch ) ) $.
    eexinst11.3 $e |- ( ph -> A. x ph ) $.
    eexinst11.4 $e |- ( ch -> A. x ch ) $.
    $( ~ exinst11 without virtual deductions.  (Contributed by Alan Sare,
       21-Apr-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eexinst11 $p |- ( ph -> ch ) $=
      ( wex exlimdh syl5com pm2.43i ) ACABDIACEABCDGHFJKL $.
  $}

  ${
    vk15.4j.1 $e |- -. ( E. x -. ph /\ E. x ( ps /\ -. ch ) ) $.
    vk15.4j.2 $e |- ( A. x ch -> -. E. x ( th /\ ta ) ) $.
    vk15.4j.3 $e |- -. A. x ( ta -> ph ) $.
    $( Excercise 4j of Unit 15 of "Understanding Symbolic Logic", Fifth Edition
       (2008), by Virginia Klenk.  This proof is the minimized Hilbert-style
       axiomatic version of the Fitch-style Natural Deduction proof found on
       page 442 of Klenk and was automatically derived from that proof.
       ~ vk15.4j is ~ vk15.4jVD automatically translated and minimized.
       (Contributed by Alan Sare, 21-Apr-2013.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    vk15.4j $p |- ( -. E. x -. th -> -. A. x ps ) $=
      ( wn wex wal wa wi exanali 19.21bi a1i 19.8a syl6 hbe1 mpbir alex biimpri
      simpl syl6an notnot con3 mpsylsyld hbn hbn1 eexinst01 exnal sylibr pm3.13
      wo ax-mp simpr syl pm2.53 mpsyl con5i con3d eexinst11 sylib ) DJZFKZJZBJZ
      FKZBFLJVGCJZVIFVGCFLZJZVJFKVGEAJZMZVLFVNFKEANFLJIEAFOUAZVKDEMZFKZJZNVGVNV
      RJZVLHVGVNVQVSVGDVNEVQVGDFDFLVGDFUBUCPVNENVGEVMUDQVPFRUEVQUFSVKVRUGUHVFFV
      EFTUIZCFUJUKCFULUMVGVJVHVIVGBCVGBCNZFVGBVJMFKZJZWAFLZVMFKZJZWCUOZVGWFJZWC
      WEWBMJWGGWEWBUNUPVGWEWHVGVNWEFVOVGVNVMWEVNVMNVGEVMUQQVMFRSVTVMFTUKWEUFURW
      FWCUSUTWBWDBCFOVAURPVBVHFRSVTVHFTVCBFULVD $.
  $}

  $( Converse of double negation.  Alternate proof of ~ notnotr .  This proof
     is ~ notnotrALTVD automatically translated and minimized.  (Contributed by
     Alan Sare, 21-Apr-2013.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  notnotrALT $p |- ( -. -. ph -> ph ) $=
    ( wn id pm2.21 mt4d ) ABZBZGAGCFGBDE $.

  $( Contraposition.  Alternate proof of ~ con3 .  This proof is ~ con3ALTVD
     automatically translated and minimized.  (Contributed by Alan Sare,
     21-Apr-2013.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  con3ALT2 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    ( wi wn notnotr imim1i con1d ) ABCADZBHDABAEFG $.

  ${
    $d A x $.  $d B x $.  $d C x $.  $d C y $.  $d D x $.  $d D y $.
    $( Quantification restricted to a subclass for two quantifiers. ~ ssralv
       for two quantifiers.  The proof of ~ ssralv2 was automatically generated
       by minimizing the automatically translated proof of ~ ssralv2VD .  The
       automatic translation is by the tools program
       translate__without__overwriting.cmd.  (Contributed by Alan Sare,
       18-Feb-2012.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ssralv2 $p |- ( ( A C_ B /\ C C_ D ) -> ( A. x e. B A. y e. D ph ->
                    A. x e. A A. y e. C ph ) ) $=
      ( wss wa wral nfv nfra1 cv wcel wi wal ssralv adantr df-ral imbitrdi syl6
      sp adantl syl6d ralrimd ) DEHZFGHZIZACGJZBEJZACFJZBDUHBKUIBELUHUJBMDNZUIU
      KUHUJULUIOZBPZUMUHUJUIBDJZUNUFUJUOOUGUIBDEQRUIBDSTUMBUBUAUGUIUKOUFACFGQUC
      UDUE $.
  $}

  $( ~ sbcor with a 3-disjuncts.  This proof is ~ sbc3orgVD automatically
     translated and minimized.  (Contributed by Alan Sare, 31-Dec-2011.)
     (Revised by NM, 24-Aug-2018.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  sbc3or $p |- ( [. A / x ]. ( ph \/ ps \/ ch ) <->
                ( [. A / x ]. ph \/ [. A / x ]. ps \/ [. A / x ]. ch ) ) $=
    ( w3o wsbc wo sbcor df-3or bicomi sbcbii orbi1i 3bitr3i bitr4i ) ABCFZDEGZA
    DEGZBDEGZHZCDEGZHZRSUAFABHZCHZDEGUCDEGZUAHQUBUCCDEIUDPDEPUDABCJKLUETUAABDEI
    MNRSUAJO $.

  ${
    $d x ps $.  $d x ch $.
    $( Closed form of ~ alrimi with 2 additional conjuncts having no
       occurrences of the quantifying variable.  This proof is
       ~ 19.21a3con13vVD automatically translated and minimized.  (Contributed
       by Alan Sare, 31-Dec-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    alrim3con13v $p |- ( ( ph -> A. x ph ) ->
                        ( ( ps /\ ph /\ ch ) -> A. x ( ps /\ ph /\ ch ) ) ) $=
      ( wal wi w3a simp1 ax-5 syl6 simp2 imim1i simp3 3jcad 19.26-3an imbitrrdi
      a1i ) AADEZFZBACGZBDEZRCDEZGTDESTUARUBSTBUATBFSBACHQBDIJTARBACKLSTCUBTCFS
      BACMQCDIJNBACDOP $.
  $}

  ${
    $d A y $.  $d B x $.  $d D x y $.
    $( ~ rspsbc with two quantifying variables.  This proof is ~ rspsbc2VD
       automatically translated and minimized.  (Contributed by Alan Sare,
       31-Dec-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    rspsbc2 $p |- ( A e. B -> ( C e. D -> ( A. x e. B A. y e. D ph ->
                  [. C / y ]. [. A / x ]. ph ) ) ) $=
      ( wcel wral wsbc idd wi rspsbc a1d sbcralg biimpd syl6d syl10 ) DEHZFGHZT
      ACGIZBEIZABDJZCGIZUCCFJSTKSTUBUABDJZUDSUBUELTUABDEMNSUEUDABCDGEOPQUCCFGMR
      $.
  $}

  ${
    $d x y $.
    $( Substitution of a setvar variable for another setvar variable in a
       3-conjunct formula.  Derived automatically from ~ sbcoreleleqVD .
       (Contributed by Alan Sare, 31-Dec-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sbcoreleleq $p |- ( A e. V -> ( [. A / y ]. ( x e. y \/ y e. x \/ x = y )
                <-> ( x e. A \/ A e. x \/ x = A ) ) ) $=
      ( wcel wel weq w3o wsbc cv sbc3or wb sbcel2gv sbcel1v a1i eqsbc2 3orbi123
      wceq 3impexpbicomi syl3c bitr4id ) CDEZABFZBAFZABGZHBCIUCBCIZUDBCIZUEBCIZ
      HZAJZCEZCUJEZUJCRZHZUCUDUEBCKUBUFUKLZUGULLZUHUMLZUNUILBUJCDMUPUBBCUJNOBCU
      JDPUOUPUQUIUNUFUKUGULUHUMQSTUA $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( If a class is transitive and any two distinct elements of the class are
       E-comparable, then every element of that class is transitive.  Derived
       automatically from ~ tratrbVD .  (Contributed by Alan Sare,
       31-Dec-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    tratrb $p |- ( ( Tr A /\ A. x e. A A. y e. A ( x e. y \/ y e. x \/ x = y )
                 /\ B e. A ) -> Tr B ) $=
      ( wtr wel weq w3o wral wcel w3a cv wa wi wal nfv nf3an wn a1i con3 nfra2w
      nfra1 simpl simpr pm3.2an3 syl6c en3lp syl6mpi eleq2 biimprcd pm3.2 syl10
      wceq syl6 en2lp wsbc simp3 simp1 trel ee121 ee122 ralcom 3ad2ant2 rspsbc2
      expd biimpi wb equid sbceq1a ax-mp imbitrrdi sbcoreleleq sylsyld 3ornot23
      biimpd ex ee222 alrimi dftr2 sylibr ) CEZABFZBAFZABGHZBCIZACIZDCJZKZWBBLZ
      DJZMZALZDJZNZBOZAODEWHWOAWAWFWGAWAAPWEACUBWGAPQWHWNBWAWFWGBWABPWDABCCUAWG
      BPQWHWKDWLJZRZWLDUMZRZWMWPWRHZWMWHWKWPWBWJWPKZNZXARWQWHWKWBWJXBWKWBNWHWBW
      JUCSZWKWJNWHWBWJUDSZWBWJWPUEUFWLWIDUGWPXATUHWHWKWRWBWCMZNXERWSWHWKWBWRWCX
      EXCWHWKWJWRWCNXDWRWCWJWLDWIUIUJUNWBWCUKULWLWIUOWRXETUHWHWGWKWDBDUPZWTWAWF
      WGUQZWHWKXFAWLUPZXFWHWGWKWLCJZWDACIBCIZXHXGWHWAWKWBWICJZXIWAWFWGURZXCWHWA
      WKWJWGXKXLXDXGWAWJWGXKCWIDUSVEUTWAWBXKXICWLWIUSVEVAWFWAXJWGWFXJWDABCCVBVF
      VCWDBADCWLCVDUTAAGXFXHVGAVHXFAWLVIVJVKWGXFWTABDCVLVOVMWQWSWTWMNWPWRWMVNVP
      VQVRVRABDVSVT $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( An element of an ordinal class is ordinal.  Proposition 7.6 of
       [TakeutiZaring] p. 36.  This is an alternate proof of ~ ordelord using
       the Axiom of Regularity indirectly through ~ dford2 . dford2 is a weaker
       definition of ordinal number.  Given the Axiom of Regularity, it need
       not be assumed that ` _E Fr A ` because this is inferred by the Axiom of
       Regularity. ~ ordelordALT is ~ ordelordALTVD without virtual deductions
       and was automatically derived from ~ ordelordALTVD using the tools
       program translate..without..overwriting.cmd and Metamath's minimize
       command.  (Contributed by Alan Sare, 18-Feb-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ordelordALT $p |- ( ( Ord A /\ B e. A ) -> Ord B ) $=
      ( vx vy word wcel wa wtr wel weq wral ordtr adantr dford2 simprbi 3orcomb
      w3o 2ralbii sylib simpr tratrb syl3anc wss trss wi ssralv2 syl3c sylanbrc
      sylc ex ) AEZBAFZGZBHZCDIZCDJZDCIZQZDBKCBKZBEUMAHZUOUQUPQZDAKCAKZULUNUKUT
      ULALMZUMURDAKCAKZVBUKVDULUKUTVDCDANOMZURVACDAAUOUPUQPRSUKULTZCDABUAUBUMBA
      UCZVGVDUSUMUTULVGVCVFABUDUIZVHVEVGVGVDUSUEURCDBABAUFUJUGCDBNUH $.
  $}

  $( Distribution of class substitution over a left-nested implication.
     Similar to ~ sbcimg . ~ sbcim2g is ~ sbcim2gVD without virtual deductions
     and was automatically derived from ~ sbcim2gVD using the tools program
     translate..without..overwriting.cmd and Metamath's minimize command.
     (Contributed by Alan Sare, 18-Mar-2012.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  sbcim2g $p |- ( A e. V -> ( [. A / x ]. ( ph -> ( ps -> ch ) ) <->
         ( [. A / x ]. ph -> ( [. A / x ]. ps -> [. A / x ]. ch ) ) ) ) $=
    ( wcel wi wsbc wb sbcimg biimpd imbi2 biimpcd syl6ci idd biimpr ee13 impbid
    sylibrd ) EFGZABCHZHDEIZADEIZBDEICDEIHZHZUAUCUDUBDEIZHZUGUEJZUFUAUCUHAUBDEF
    KZLBCDEFKZUIUHUFUGUEUDMNOUAUFUHUCUAUIUFUDUEUGUKUAUFPUGUEQRUJTS $.

  $( Implication form of ~ sbcbii . ~ sbcbi is ~ sbcbiVD without virtual
     deductions and was automatically derived from ~ sbcbiVD using the tools
     program translate..without..overwriting.cmd and Metamath's minimize
     command.  (Contributed by Alan Sare, 18-Mar-2012.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  sbcbi $p |- ( A e. V -> ( A. x ( ph <-> ps ) -> ( [. A / x ]. ph <->
                  [. A / x ]. ps ) ) ) $=
    ( wcel wb wal wsbc spsbc sbcbig sylibd ) DEFABGZCHMCDIACDIBCDIGMCDEJABCDEKL
    $.

  ${
    $d A x y z $.  $d V y z $.
    $( Formula-building inference rule for class substitution, substituting a
       class variable for the setvar variable of the transitivity predicate.
       ~ trsbc is ~ trsbcVD without virtual deductions and was automatically
       derived from ~ trsbcVD using the tools program
       translate..without..overwriting.cmd and Metamath's minimize command.
       (Contributed by Alan Sare, 18-Mar-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    trsbc $p |- ( A e. V -> ( [. A / x ]. Tr x <-> Tr A ) ) $=
      ( vz vy wcel wel wa wi wal wsbc cv wtr sbcal sbcel2gv pm3.31 pm3.3 impbii
      wb sbcbii sbcim2g imbi13 syl3c bitrd 3bitr3g albidv bitrid dftr2 3bitr4g
      sbcg ) BCFZDEGZEAGZHDAGZIZEJZDJZABKZULELZBFZHDLZBFZIZEJZDJZALZMZABKBMURUP
      ABKZDJUKVEUPDABNUKVHVDDVHUOABKZEJUKVDUOEABNUKVIVCEUKULUMUNIIZABKZULUTVBII
      ZVIVCUKVKULABKZUMABKZUNABKZIIZVLULUMUNABCUAUKVMULSVNUTSVOVBSVPVLSULABCUJA
      USBCOAVABCOVMULVNUTVOVBUBUCUDVJUOABVJUOULUMUNPULUMUNQRTVLVCULUTVBPULUTVBQ
      RUEUFUGUFUGVGUQABDEVFUHTDEBUHUI $.
  $}

  ${
    $d A q x y z $.
    $( The union of a class of transitive sets is transitive.  Alternate proof
       of ~ truni . ~ truniALT is ~ truniALTVD without virtual deductions and
       was automatically derived from ~ truniALTVD using the tools program
       translate..without..overwriting.cmd and Metamath's minimize command.
       (Contributed by Alan Sare, 18-Mar-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    truniALT $p |- ( A. x e. A Tr x -> Tr U. A ) $=
      ( vz vy vq cv wtr wral wel cuni wcel wa wal simpr a1i imbitrdi simpl 2a1i
      wi ee33 wex eluni wsbc rspsbc com12 syl6d trsbc biimpd trel expdcom ee233
      elunii ex alrimdv 19.23v mpdd alrimivv dftr2 sylibr ) AFGZABHZCDIZDFZBJZK
      ZLZCFZVDKZSZDMCMVDGVAVICDVAVFDEIZEFZBKZLZEUAZVHVAVFVEVNVFVESVAVBVENOEVCBU
      BPVAVFVMVHSZEMVNVHSVAVFVOEVAVFVMCEIZVLVHVAVFVBVMVJVKGZVPVFVBSVAVBVEQOVMVJ
      SVAVFVJVLQRVAVFVMVLUTAVKUCZVQVMVLSVAVFVJVLNRZVAVFVMVLVRVSVLVAVRUTAVKBUDUE
      UFVLVRVQAVKBUGUHTVQVBVJVPVKVGVCUIUJUKVSVPVLVHVGVKBULUMTUNVMVHEUOPUPUQCDVD
      URUS $.
  $}

  ${
    $d a b y $.  $d b x y $.
    $( Lemma for ~ onfrALT .  (Contributed by Alan Sare, 22-Jul-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    onfrALTlem5 $p |- ( [. ( a i^i x ) / b ]. ( ( b C_ ( a i^i x )
      /\ b =/= (/) ) -> E. y e. b ( b i^i y ) = (/) )
        <-> ( ( ( a i^i x ) C_ ( a i^i x ) /\ ( a i^i x ) =/= (/) ) ->
              E. y e. ( a i^i x ) ( ( a i^i x ) i^i y ) = (/) ) ) $=
      ( cv cin wss c0 wne wa wceq wrex wi wsbc cvv wb ax-mp bitri wex csb inex1
      wcel vex sbcimg sbcan sseq1 sbcie wn df-ne sbcbii sbcng bicomd necon3bbii
      eqsbc1 3bitr2i anbi12i wel df-rex sbcel2gv sbceqg csbin csbvarg csbconstg
      ineq12i eqtri csb0 eqeq12i exbii sbcex2 3bitr4i imbi12i ) DEZCEZAEZFZGZVL
      HIZJZVLBEZFZHKZBVLLZMDVONZVRDVONZWBDVONZMZVOVOGZVOHIZJZVOVSFZHKZBVOLZMVOO
      UBZWCWFPVMVNCUCUAZVRWBDVOOUDQWDWIWEWLWDVPDVONZVQDVONZJWIVPVQDVOUEWOWGWPWH
      VPWGDVOWNVLVOVOUFUGWPVLHKZUHZDVONZWQDVONZUHZWHVQWRDVOVLHUIUJWMXAWSPWNWMWS
      XAWQDVOOUKULQWTVOHWMWTVOHKPWNDVOHOUNQUMUOUPRWEBDUQZWAJZBSZDVONZWLWBXDDVOW
      ABVLURUJXCDVONZBSVSVOUBZWKJZBSXEWLXFXHBXFXBDVONZWADVONZJXHXBWADVOUEXIXGXJ
      WKWMXIXGPWNDVSVOOUSQXJDVOVTTZDVOHTZKZWKWMXJXMPWNDVOVTHOUTQXKWJXLHXKDVOVLT
      ZDVOVSTZFWJDVOVLVSVAXNVOXOVSWMXNVOKWNDVOOVBQWMXOVSKWNDVOVSOVCQVDVEDVOVFVG
      RUPRVHXCBDVOVIWKBVOURVJRVKR $.
  $}

  ${
    $d a x $.
    $( Lemma for ~ onfrALT .  (Contributed by Alan Sare, 22-Jul-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    onfrALTlem4 $p |- ( [. y / x ]. ( x e. a /\ ( a i^i x ) = (/) ) <->
                        ( y e. a /\ ( a i^i y ) = (/) ) ) $=
      ( wel cv cin c0 wceq wa wsbc sbcan sbcel1v csb wcel wb sbceqg ax-mp bitri
      cvv vex csbin csbconstg csbvarg ineq12i eqtri csb0 eqeq12i anbi12i ) ACDZ
      CEZAEZFZGHZIABEZJUIAUNJZUMAUNJZIBCDZUJUNFZGHZIUIUMAUNKUOUQUPUSAUNUJLUPAUN
      ULMZAUNGMZHZUSUNSNZUPVBOBTZAUNULGSPQUTURVAGUTAUNUJMZAUNUKMZFURAUNUJUKUAVE
      UJVFUNVCVEUJHVDAUNUJSUBQVCVFUNHVDAUNSUCQUDUEAUNUFUGRUHR $.
  $}

  ${
    $d a b y $.  $d b x y $.
    $( Lemma for ~ onfrALT .  (Contributed by Alan Sare, 22-Jul-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    onfrALTlem3 $p |- ( ( a C_ On /\ a =/= (/) ) ->
                        ( ( x e. a /\ -. ( a i^i x ) = (/) ) ->
                        E. y e. ( a i^i x ) ( ( a i^i x ) i^i y ) = (/) ) ) $=
      ( vb cv con0 wss c0 wne wa cin wceq wrex mpsylsyld cvv wcel cep wwe syl6
      wi wel ssid simpr a1i df-ne imbitrrdi pm3.2 wsbc wal vex inex2 inss2 word
      wn wfr simpl ssel syl2im eloni ordwe wess wefr imbitrdi spsbc onfrALTlem5
      dfepfr mpdd ) CEZFGZVHHIZJZACUAZVHAEZKZHLUNZJZVNVNGZVNHIZJZVNBEZKHLBVNMZV
      QVKVPVRVSVNUBVKVPVOVRVPVOTVKVLVOUCUDVNHUEUFVQVRUGNVKVPDEZVNGWBHIJWBVTKHLB
      WBMTZDVNUHZVSWATVNOPVKVPWCDUIZWDVMVHAUJUKVKVPVNQUOZWEVKVPVNQRZWFVNVMGVKVP
      VMQRZWGVHVMULVKVPVMUMZWHVKVPVMFPZWIVKVIVPVLWJVIVJUPVLVOUPVHFVMUQURVMUSSVM
      UTSVNVMQVANVNQVBSDBVNVFVCWCDVNOVDNABCDVEVCVG $.
  $}

  ${
    $d ch x $.  $d ph x $.  $d ps x $.
    ggen31.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( ~ gen31 without virtual deductions.  (Contributed by Alan Sare,
       22-Jul-2012.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ggen31 $p |- ( ph -> ( ps -> ( ch -> A. x th ) ) ) $=
      ( wal wi wa imp alrimdv ex ) ABCDEGHABICDEABCDHFJKL $.
  $}

  ${
    $d a y z $.  $d x y z $.
    $( Lemma for ~ onfrALT .  (Contributed by Alan Sare, 22-Jul-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    onfrALTlem2 $p |- ( ( a C_ On /\ a =/= (/) ) -> ( ( x e. a /\
                      -. ( a i^i x ) = (/) ) -> E. y e. a ( a i^i y ) =
                      (/) ) ) $=
      ( vz cv con0 wss c0 wa wel cin wceq wex wcel 2a1i sseli syl8 simpl ee33
      wi wne wrex wal simpr inss2 inss1 wtr word ssel syl2im eloni ordtr simpll
      wn syl6 trel expcomd ee233 elin simplbi2 simplbi2com exp4a ggen31 biimpri
      df-ss sseq0 ex pm3.21 alrimdv onfrALTlem3 df-rex imbitrdi syl6c imbitrrdi
      exim ) CEZFGZVPHUAZIZACJZVPAEZKZHLUNZIZBCJZVPBEZKZHLZIZBMZWHBVPUBVSWDWFWB
      NZWBWFKZHLZIZWITZBUCWNBMZWJVSWDWOBVSWDWNWHWEWIVSWDWNWGWLGZWMWHVSWDWNDEZWG
      NZWRWLNZTZDUCZWQVSWDWNXADVSWDWNWSWTVSWDWNWSIZDBJZWRWBNZWTVSWDXCWSXDXCWSTV
      SWDWNWSUDOZWGWFWRVPWFUEPQZVSWDXCDCJZDAJZXEVSWDXCWSXHXFWGVPWRVPWFUFPQVSWDW
      AUGZXCBAJZXDXIVSWDWAUHZXJVSWDWAFNZXLVSVQWDVTXMVQVRRVTWCRVPFWAUIUJWAUKUOWA
      ULUOVSWDXCWKXKXCWKTVSWDWKWMWSUMOWBWAWFVPWAUEPQXGXJXDXKXIWAWRWFUPUQURXEXHX
      IWRVPWAUSUTSWTXEXDWRWBWFUSVASVBVCWQXBDWGWLVEVDQWNWMTVSWDWKWMUDOWQWMWHWGWL
      VFVGSVSWDWNWKWEWNWKTVSWDWKWMROWBVPWFVPWAUFPQWHWEVHSVIVSWDWMBWBUBWPABCVJWM
      BWBVKVLWNWIBVOVMWHBVPVKVN $.
  $}

  ${
    $d ph y $.
    $( A theorem pertaining to the substitution for an existentially quantified
       variable when the substituted variable does not occur in the quantified
       wff.  (Contributed by Alan Sare, 22-Jul-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    cbvexsv $p |- ( E. x ph <-> E. y [ y / x ] ph ) $=
      ( cvv wrex wsb wex cbvrexsv rexv 3bitr3i ) ABDEABCFZCDEABGKCGABCDHABIKCIJ
      $.
  $}

  ${
    $d a x y $.
    $( Lemma for ~ onfrALT .  (Contributed by Alan Sare, 22-Jul-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    onfrALTlem1 $p |- ( ( a C_ On /\ a =/= (/) ) -> ( ( x e. a /\ ( a i^i x ) =
                      (/) ) -> E. y e. a ( a i^i y ) = (/) ) ) $=
      ( cv con0 wss c0 wne wa wel cin wceq wex wrex wsb wi a1i cbvexsv imbitrdi
      19.8a wsbc sbsbc onfrALTlem4 bitri exbii df-rex imbitrrdi ) CDZEFUHGHIZAC
      JUHADKGLIZBCJUHBDZKGLZIZBMZULBUHNUIUJUJABOZBMZUNUIUJUJAMZUPUJUQPUIUJATQUJ
      ABRSUOUMBUOUJAUKUAUMUJABUBABCUCUDUESULBUHUFUG $.
  $}

  ${
    $d a x y $.
    $( The membership relation is foundational on the class of ordinal numbers.
       ~ onfrALT is an alternate proof of ~ onfr . ~ onfrALTVD is the Virtual
       Deduction proof from which ~ onfrALT is derived.  The Virtual Deduction
       proof mirrors the working proof of ~ onfr which is the main part of the
       proof of Theorem 7.12 of the first edition of TakeutiZaring.  The proof
       of the corresponding Proposition 7.12 of [TakeutiZaring] p. 38 (second
       edition) does not contain the working proof equivalent of ~ onfrALTVD .
       This theorem does not rely on the Axiom of Regularity.  (Contributed by
       Alan Sare, 22-Jul-2012.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    onfrALT $p |- _E Fr On $=
      ( va vy vx con0 cep wfr cv wss c0 wne wa cin wceq wi dfepfr simpr wel wex
      wrex expd n0 wn onfrALTlem1 onfrALTlem2 pm2.61 syl6c exlimdv biimtrid mpd
      mpgbir ) DEFAGZDHZUKIJZKZUKBGLIMBUKSZNAABDOUNUMUOULUMPUMCAQZCRUNUOCUKUAUN
      UPUOCUNUPUKCGLIMZUONUQUBZUONUOUNUPUQUOCBAUCTUNUPURUOCBAUDTUQUOUEUFUGUHUIU
      J $.
  $}

  $( Closed form of right-to-left implication of ~ 19.41 , Theorem 19.41 of
     [Margaris] p. 90.  Derived from ~ 19.41rgVD .  (Contributed by Alan Sare,
     8-Feb-2014.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  19.41rg $p |- ( A. x ( ps -> A. x ps ) -> ( ( E. x ph /\ ps ) ->
                  E. x ( ph /\ ps ) ) ) $=
    ( wal wi wex wa sp pm3.21 a1i al2imi exim syl6 syld com23 impd ) BBCDZEZCDZ
    ACFZBABGZCFZSBTUBSBQTUBEZRCHSQAUAEZCDUCRBUDCBUDERBAIJKAUACLMNOP $.

  ${
    $d u x $.  $d u y $.  $d v x $.  $d v y $.
    $( Ordered pair membership in a class abstraction of ordered pairs.
       Compare to ~ elopab .  (Contributed by Alan Sare, 8-Feb-2014.)  (Revised
       by Mario Carneiro, 6-May-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    opelopab4 $p |- ( <. u , v >. e. { <. x , y >. | ph } <->
                     E. x E. y ( ( x = u /\ y = v ) /\ ph ) ) $=
      ( cv cop copab wcel wceq wex elopab vex eqcom bitr3i anbi1i 2exbii bitr4i
      wa opth ) EFZDFZGZABCHIUCBFZCFZGZJZASZCKBKUDUAJUEUBJSZASZCKBKABCUCLUJUHBC
      UIUGAUIUFUCJUGUDUEUAUBBMCMTUFUCNOPQR $.
  $}

  $( ~ pm13.193 for two variables. ~ pm13.193 is Theorem *13.193 in
     [WhiteheadRussell] p. 179.  Derived from ~ 2pm13.193VD .  (Contributed by
     Alan Sare, 8-Feb-2014.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  2pm13.193 $p |- ( ( ( x = u /\ y = v ) /\ [ u / x ] [ v / y ] ph ) <->
                    ( ( x = u /\ y = v ) /\ ph ) ) $=
    ( weq wa wsb simpll simplr simpr sbequ2 sylc jca31 sbequ1 impbii ) BEFZCDFZ
    GZACDHZBEHZGZSAGZUBQRAQRUAIZQRUAJZUBRTAUEUBQUATUDSUAKTBELMACDLMNUCQRUAQRAIZ
    QRAJZUCQTUAUFUCRATUGSAKACDOMTBEOMNP $.

  $( A closed form of ~ hbn . ~ hbnt is another closed form of ~ hbn .
     (Contributed by Alan Sare, 8-Feb-2014.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  hbntal $p |- ( A. x ( ph -> A. x ph ) -> A. x ( -. ph -> A. x -. ph ) ) $=
    ( wal wi wn hba1 axc7 con1i con3 al2imi syl5 alimi syl ) AABCZDZBCZPBCAEZQB
    CZDZBCOBFPSBQNEZBCZPRUAAABGHOTQBANIJKLM $.

  $( A closed form of ~ hbim .  Derived from ~ hbimpgVD .  (Contributed by Alan
     Sare, 8-Feb-2014.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  hbimpg $p |- ( ( A. x ( ph -> A. x ph ) /\ A. x ( ps -> A. x ps ) ) ->
                  A. x ( ( ph -> ps ) -> A. x ( ph -> ps ) ) ) $=
    ( wal wi wa hba1 hban wn hbntal adantr 19.21bi pm2.21 alimi syl6 simpr ax-1
    jad alrimih ) AACDEZCDZBBCDZEZCDZFZABEZUFCDZECUAUDCTCGUCCGHUEABUGUEAIZUHCDZ
    UGUEUHUIEZCUAUJCDUDACJKLUHUFCABMNOUEBUBUGUEUCCUAUDPLBUFCBAQNORS $.

  $( Closed form of ~ hbal .  Derived from ~ hbalgVD .  (Contributed by Alan
     Sare, 8-Feb-2014.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  hbalg $p |- ( A. y ( ph -> A. x ph ) ->
                  A. y ( A. y ph -> A. x A. y ph ) ) $=
    ( wal wi alim ax-11 syl6 axc4i ) AABDZEZACDZLBDZECKCDLJCDMAJCFACBGHI $.

  $( Closed form of ~ nfex .  Derived from ~ hbexgVD .  (Contributed by Alan
     Sare, 8-Feb-2014.)  (Revised by Mario Carneiro, 12-Dec-2016.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  hbexg $p |- ( A. x A. y ( ph -> A. x ph ) ->
                  A. x A. y ( E. y ph -> A. x E. y ph ) ) $=
    ( wal wi wex nfa2 wnf sp alimi nf5 sylibr nfexd sylib alrimi alcom ) AABDEZ
    CDZBDZACFZTBDEZBDZCDUACDBDSUBCQCBGZSTBHUBSABCUCSQBDABHRQBQCIJABKLMTBKNOUACB
    PN $.

  ${
    $d u x $.  $d u y $.  $d v x $.  $d v y $.
    $( Alternate form of ~ ax6e for non-distinct ` x ` , ` y ` and ` u = v ` .
       ~ ax6e2eq is derived from ~ ax6e2eqVD .  (Contributed by Alan Sare,
       25-Mar-2014.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax6e2eq $p |- ( A. x x = y -> ( u = v ->
                  E. x E. y ( x = u /\ y = v ) ) ) $=
      ( weq wal wa wex ax6ev hbae ax7 sps ancld eximdh mpi axc4i axc11 mpd syl
      wi 19.2 excomim equtrr anim2d 2eximdv syl5com ) ABEZAFZADEZBDEZGZBHAHZDCE
      ZUIBCEZGZBHAHUHUKAHZBHZULUHUPBFZUQUHUPAFURUGUPAUHUIAHUPADIUHUIUKAABAJUHUI
      UJUGUIUJTAABDKLMNOPUPABQRUPBUASUKBAUBSUMUKUOABUMUJUNUIDCBUCUDUEUF $.
  $}

  ${
    $d u x $.  $d u y $.  $d v x z $.  $d y z $.
    $( If at least two sets exist ( ~ dtru ), then the same is true expressed
       in an alternate form similar to the form of ~ ax6e . ~ ax6e2nd is
       derived from ~ ax6e2ndVD .  (Contributed by Alan Sare, 25-Mar-2014.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax6e2nd $p |- ( -. A. x x = y -> E. x E. y ( x = u /\ y = v ) ) $=
      ( vz weq wal wn wa wex wi cv cvv wcel vex id ax-5 syl idiALT alimi pm3.2i
      ax6e 19.42v biimpri ax-mp isset anbi1i exbii mpbi hbn1 wb equequ1 dvelimh
      hbnae 19.41rg exim pm2.27 mpsyl excomim ) ABFZAGHZADFZBCFZIZBJAJZKVAVDAJZ
      BJZVEVBAJZVCIZBJZVAVJVGKZVGDLZMNZVCIZBJZVJVMVCBJZIZVOVMVPDOBCUBUAVOVQVMVC
      BUCUDUEVNVIBVMVHVCAVLUFUGUHUIVAVIVFKZBGZVKVAVAVSVAPZVAVABGVSABBUNVAVRBVAV
      RKVAVCVCAGKZAGZVRVAVAWBVTVAVAAGWBUTAUJVAWAAVAWAKVAVAWAVTECFZVCABEWCAQVCEQ
      EBFZWCVCUKZKWDWDWEWDPEBCULRSUMRSTRRVBVCAUORSTRRVIVFBUPRVJVGUQURVDBAUSRS
      $.
  $}

  ${
    $d u x $.  $d u y $.  $d v x $.  $d v y $.
    $( "At least two sets exist" expressed in the form of ~ dtru is logically
       equivalent to the same expressed in a form similar to ~ ax6e if ~ dtru
       is false implies ` u = v ` . ~ ax6e2ndeq is derived from ~ ax6e2ndeqVD .
       (Contributed by Alan Sare, 25-Mar-2014.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax6e2ndeq $p |- ( ( -. A. x x = y \/ u = v ) <->
                        E. x E. y ( x = u /\ y = v ) ) $=
      ( cv wceq wal wn wo wa wex wi a1d wne biimprcd syl6 eximdv nfnae imbitrdi
      19.9 ax6e2nd ax6e2eq pm2.61i jaoi olc excom neeq1 adantrd simpr a1i neeq2
      syl6c sp necon3ai biimtrid orc pm2.61ine impbii ) AEZBEZFZAGZHZDEZCEZFZIZ
      USVDFZUTVEFZJZBKAKZVCVKVFABCDUAZVBVFVKLABCDUBVCVKVFVLMUCUDVKVGLVDVEVFVGVK
      VFVCUEMVDVENZVKVCVGVMVKVCBKZVCVKVJAKZBKVMVNVJABUFVMVOVCBVMVOVCAKVCVMVJVCA
      VMVJUSUTNZVCVMVJUSVENZVIVPVMVHVQVIVHVQVMUSVDVEUGOUHVJVILVMVHVIUIUJVIVPVQU
      TVEUSUKOULVBUSUTVAAUMUNPQVCAABARTSQUOVCBABBRTSVCVFUPPUQUR $.
  $}

  ${
    $d u x $.  $d u y $.  $d v x $.  $d v y $.
    $( Equivalence for double substitution ~ 2sb5 without distinct ` x ` ,
       ` y ` requirement. ~ 2sb5nd is derived from ~ 2sb5ndVD .  (Contributed
       by Alan Sare, 30-Apr-2014.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    2sb5nd $p |- ( ( -. A. x x = y \/ u = v ) -> ( [ u / x ] [ v / y ] ph
                 <-> E. x E. y ( ( x = u /\ y = v ) /\ ph ) ) ) $=
      ( cv wceq wal wn wo wa wex wsb wb ax6e2ndeq wi exbii nfs1v 19.41 bitr3i
      anabs5 2pm13.193 nfsb bitr2i anbi2i pm5.32 mpbir sylbi ) BFZCFZGBHIEFZDFZ
      GJUIUKGUJULGKZCLZBLZACDMZBEMZUMAKZCLZBLZNZBCDEOUOVAPUOUQKZUOUTKZNVBUOVBKV
      CUOUQUAVBUTUOUTUNUQKZBLVBUSVDBUSUMUQKZCLVDVEURCABCDEUBQUMUQCUPBECACDRUCST
      QUNUQBUPBERSUDUETUOUQUTUFUGUH $.
  $}

  ${
    $d u x $.  $d u y $.  $d v x $.  $d v y $.
    2uasbanh.1 $e |- ( ch <-> ( E. x E. y ( ( x = u /\ y = v ) /\ ph ) /\
                     E. x E. y ( ( x = u /\ y = v ) /\ ps ) ) ) $.
    $( Distribute the unabbreviated form of proper substitution in and out of a
       conjunction. ~ 2uasbanh is derived from ~ 2uasbanhVD .  (Contributed by
       Alan Sare, 31-May-2014.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    2uasbanh $p |- ( E. x E. y ( ( x = u /\ y = v ) /\ ( ph /\ ps ) ) <->
                ( E. x E. y ( ( x = u /\ y = v ) /\ ph ) /\
                E. x E. y ( ( x = u /\ y = v ) /\ ps ) ) ) $=
      ( weq wa wex simpl jca 2eximi wsb wb syl 2sb5nd mpbird sban simprl simprr
      simplbi wal wn ax6e2ndeq sylibr simprbi sbbii bitri sylanbrc mpbid sylbir
      wo impbii ) DGIEFIJZABJZJZEKDKZUPAJZEKDKZUPBJZEKDKZJZUSVAVCURUTDEURUPAUPU
      QLZUPABUAMNURVBDEURUPBVEUPABUBMNMVDCUSHCUQEFOZDGOZUSCAEFOZDGOZBEFOZDGOZVG
      CVIVACVAVCHUCZCDEIDUDUEGFIUNZVIVAPCUPEKDKZVMCVAVNVLUTUPDEUPALNQDEFGUFUGZA
      DEFGRQSCVKVCCVAVCHUHCVMVKVCPVOBDEFGRQSVGVHVJJZDGOVIVKJVFVPDGABEFTUIVHVJDG
      TUJUKCVMVGUSPVOUQDEFGRQULUMUO $.
  $}

  ${
    $d u x $.  $d u y $.  $d v x $.  $d v y $.
    $( Distribute the unabbreviated form of proper substitution in and out of a
       conjunction.  (Contributed by Alan Sare, 31-May-2014.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    2uasban $p |- ( E. x E. y ( ( x = u /\ y = v ) /\ ( ph /\ ps ) ) <->
               ( E. x E. y ( ( x = u /\ y = v ) /\ ph ) /\
               E. x E. y ( ( x = u /\ y = v ) /\ ps ) ) ) $=
      ( cv wceq wa wex biid 2uasbanh ) ABCGFGHDGEGHIZAIDJCJMBIDJCJIZCDEFNKL $.
  $}

  $( Absorption of an existential quantifier of a double existential quantifier
     of non-distinct variables. ~ e2ebind is derived from ~ e2ebindVD .
     (Contributed by Alan Sare, 27-Nov-2014.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  e2ebind $p |- ( A. x x = y -> ( E. x E. y ph <-> E. y ph ) ) $=
    ( wex wb wceq wal biidd drex1 drex2 excom bitrdi nfe1 19.9 bitr3di aecoms
    cv ) ACDZBDZRECBCQBQFCGZRCDZSRTUAABDZCDSRUBCBCAACBTAHIJACBKLRCACMNOP $.

  ${
    elpwgded.1 $e |- ( ph -> A e. _V ) $.
    elpwgded.2 $e |- ( ps -> A C_ B ) $.
    $( ~ elpwgdedVD in conventional notation.  (Contributed by Alan Sare,
       23-Apr-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    elpwgded $p |- ( ( ph /\ ps ) -> A e. ~P B ) $=
      ( cvv wcel wss cpw elpwg biimpar syl2an ) ACGHZCDIZCDJHZBEFNPOCDGKLM $.
  $}

  ${
    trelded.1 $e |- ( ph -> Tr A ) $.
    trelded.2 $e |- ( ps -> B e. C ) $.
    trelded.3 $e |- ( ch -> C e. A ) $.
    $( Deduction form of ~ trel .  In a transitive class, the membership
       relation is transitive.  (Contributed by Alan Sare, 3-Dec-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    trelded $p |- ( ( ph /\ ps /\ ch ) -> B e. A ) $=
      ( wtr wcel trel 3impib syl3an ) ADJZBEFKZCFDKZEDKZGHIOPQRDEFLMN $.
  $}

  ${
    jaoded.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jaoded.2 $e |- ( th -> ( ta -> ch ) ) $.
    jaoded.3 $e |- ( et -> ( ps \/ ta ) ) $.
    $( Deduction form of ~ jao .  Disjunction of antecedents.  (Contributed by
       Alan Sare, 3-Dec-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    jaoded $p |- ( ( ph /\ th /\ et ) -> ch ) $=
      ( wi wo jao 3imp syl3an ) ABCJZDECJZFBEKZCGHIOPQCBCELMN $.
  $}

  ${
    sbtT.1 $e |- ( T. -> ph ) $.
    $( A substitution into a theorem remains true. ~ sbt with the existence of
       no virtual hypotheses for the hypothesis expressed as the empty virtual
       hypothesis collection.  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sbtT $p |- [ y / x ] ph $=
      ( mptru sbt ) ABCADEF $.
  $}

  $( If a double conjunction is false and the second conjunct is true, then the
     first conjunct is false.
     ~ https://us.metamath.org/other/completeusersproof/not12an2impnot1vd.html
     is the Virtual Deduction proof verified by automatically transforming it
     into the Metamath proof of ~ not12an2impnot1 using completeusersproof,
     which is verified by the Metamath program.
     ~ https://us.metamath.org/other/completeusersproof/not12an2impnot1ro.html
     is a form of the completed proof which preserves the Virtual Deduction
     proof's step numbers and their ordering.  (Contributed by Alan Sare,
     13-Jun-2018.) $)
  not12an2impnot1 $p |- ( ( -. ( ph /\ ps ) /\ ps ) -> -. ph ) $=
    ( wa wn pm3.21 con3rr3 imp ) ABCZDBADBAHBAEFG $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  What is Virtual Deduction?
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c (. $. $( Left parenthesis for virtual deduction for virtual hypotheses.
      [21-Apr-2011] $)

  $c ). $. $( Right parenthesis for virtual deduction.
      [9-Nov-2011] $)

  $c ->. $. $( Symbol for virtual inference.
      [9-Nov-2011] $)

  $c ->.. $. $( Bold arrow of Kleene's classical system G1.
      [19-May-2013] $)

  $c ,. $. $( Comma between two adjacent virtual hypotheses.
      [28-Jul-2016] $)

  $( A Virtual Deduction proof in a Hilbert-style deductive system is the
     analogue of a sequent calculus proof.  A theorem is proven in a Gentzen
     system in order to prove it more directly, which may be more intuitive
     and easier for some people.  The analogue of this proof in Metamath's
     Hilbert-style system is verified by the Metamath program.

     <HTML> <TABLE> </TABLE> </HTML>

     Natural Deduction is a well-known proof method originally proposed by
     Gentzen in 1935 and comprehensively summarized by Prawitz in his 1965
     monograph "Natural deduction: a proof-theoretical study".  Gentzen
     wished to construct "a formalism that comes as close as possible to
     natural reasoning".  Natural deduction is a response to dissatisfaction
     with axiomatic proofs such as Hilbert-style axiomatic proofs, which the
     proofs of Metamath are.  In 1926, in Poland, Lukasiewicz advocated a
     more natural treatment of logic.  Jaskowski made the earliest attempts
     at defining a more natural deduction.  Natural deduction in its modern
     form was independently proposed by Gentzen.

     Sequent calculus, the chief alternative to Natural Deduction, was
     created by Gentzen.  The following is an excerpt from Stephen Cole
     Kleene's seminal 1952 book "Introduction to Metamathematics", which
     contains the first formulation of sequent calculus in the modern style.
     Kleene states on page 440:

     . . . the proof of his (Gentzen's) Hauptsatz or normal form theorem
     breaks down into a list of
     cases, each of which is simple to handle. . . .  Gentzen's normal form
     for proofs in the predicate calculus requires a different classification
     of the deductive steps than is given by the postulates of the formal
     system of predicate calculus of Chapter IV (Section 19).  The
     implication symbol ` -> ` (the Metamath symbol for implication has been
     substituted here for the symbol used by Kleene) has to be separated in
     its role of mediating inferences from its role as a component symbol of
     the formula being proved.  In the former role it will be replaced by a
     new formal symbol ` ->.. ` (read "gives" or "entails"), to which
     properties will be assigned similar to those of the informal symbol
     ` |- ` in our former derived rules.

     Gentzen's classification of the deductive operations is made explicit
     by setting up a new formal system of the predicate calculus.  The formal
     system of propositional and predicate calculus studied previously
     (Chapters IV ff.) we call now a "Hilbert-type system", and denote by
     H.  Precisely, H denotes any one or a particular one of several
     systems, according to whether we are considering propositional calculus
     or predicate calculus, in the classical or the intuitionistic version
     (Section 23), and according to the sense in which we are using "term"
     and "formula" (Sections 117, 25, 31, 37, 72-76).  The same respective
     choices will apply to the "Gentzen-type system G1" which we introduce
     now and the G2, G3 and G3a later.

     The transformation or deductive rules of G1 will apply to objects which
     are not formulas of the system H, but are built from them by an
     additional formation rule, so we use a new term "sequent" for these
     objects.  (Gentzen says "Sequenz", which we translate as "sequent",
     because we have already used "sequence" for any succession of objects,
     where the German is "Folge".)  A sequent is a formal expression of the
     form ` ph , ... , ps ->.. ch , ... , th ` where ` ph , ... , ps ` and
     ` ch , ... , th ` are sequences of a finite
     number of 0 or more formulas (substituting Metamath notation for
     Kleene's notation).  The part ` ph , ... , ps ` is the antecedent,
     and ` ch , ... , th ` the succedent of the sequent
     ` ph , ... , ps ->.. ch , ... , th ` .

     When the antecedent and the succedent each have a finite number of 1 or
     more formulas, the sequent ` ph , ... , ps ->.. ch , ... , th ` has the
     same interpretation for G1 as the formula
     ` ( ( ph /\ ... /\ ps ) -> ( ch \/ ... \/ th ) ) ` for H.
     The interpretation extends to the case of an antecedent of 0 formulas by
     regarding ` ( ph /\ ... /\ ps ) ` for 0 formulas (the
     "empty conjunction") as true and ` ( ch \/ ... \/ th ) ` for 0
     formulas (the "empty disjunction") as false.

     . . . As in Chapter V, we use Greek capitals . . . to stand for finite
     sequences of zero or more formulas, but now also as antecedent
     (succedent), or parts of antecedent (succedent), with separating formal
     commas included. . . .  (End of Kleene excerpt)

     In chapter V entitled "Formal Deduction" Kleene states, on page 86:

     Section 20.  Formal deduction.  Formal proofs of even quite elementary
     theorems tend to be long.  As a price for having analyzed logical
     deduction into simple steps, more of those steps have to be used.

     The purpose of formalizing a theory is to get an explicit definition of
     what constitutes proof in the theory.  Having achieved this, there is no
     need always to appeal directly to the definition.  The labor required to
     establish the formal provability of formulas can be greatly lessened by
     using metamathematical theorems concerning the existence of formal
     proofs.  If the demonstrations of those theorems do have the finitary
     character which metamathematics is supposed to have, the demonstrations
     will indicate, at least implicitly, methods for obtaining the formal
     proofs.  The use of the metamathematical theorems then amounts to
     abbreviation, often of very great extent, in the presentation of formal
     proofs.

     The simpler of such metamathematical theorems we shall call derived
     rules, since they express principles which can be said to be derived
     from the postulated rules by showing that the use of them as additional
     methods of inference does not increase the class of provable formulas.
     We shall seek by means of derived rules to bring the methods for
     establishing the facts of formal provability as close as possible to the
     informal methods of the theory which is being formalized.

     In setting up the formal system, proof was given the simplest possible
     structure, consisting of a single sequence of formulas.  Some of our
     derived rules, called "direct rules", will serve to abbreviate for us
     whole segments of such a sequence; we can then, so to speak, use these
     segments as prefabricated units in building proofs.

     But also, in mathematical practice, proofs are common which have a more
     complicated structure, employing "subsidiary deduction", i.e., deduction
     under assumptions for the sake of the argument, which assumptions are
     subsequently discharged.  For example, subsidiary deduction is used in a
     proof by reductio ad absurdum, and less obtrusively when we place the
     hypothesis of a theorem on a par with proved propositions to deduce the
     conclusion.  Other derived rules, called "subsidiary deduction rules",
     will give us this kind of procedure.

     We now introduce, by a metamathematical definition, the notion of
     "formal deducibility under assumptions".  Given a list
     ` ph , ... , ps ` of 0 or more (occurrences of) formulas, a finite
     sequence of one or more (occurrences of) formulas is called a (formal)
     deduction from
     the assumption formulas ` ph , ... , ps ` , if each formula of the
     sequence is either one of the formulas ` ph , ... , ps ` , or an
     axiom, or an immediate consequence of preceding formulas of a sequence.
     A deduction is said to be deducible from the assumption formulas (in
     symbols, ` ph , ... , ps |- ch ` ), and is called the conclusion
     (or endformula) of the deduction.  (The symbol ` |- ` may be read
     "yields".)  (End of Kleene excerpt)

     Gentzen's normal form is a certain direct fashion for proofs and
     deductions.  His sequent calculus, formulated in the modern style by
     Kleene, is the classical system G1.  In this system, the new formal
     symbol ` ->.. ` has properties similar to the informal symbol ` |- ` of
     Kleene's above language of formal deducibility under assumptions.

     Kleene states on page 440:

     . . .  This leads us to inquire whether there may not be a theorem about
     the predicate calculus asserting that, if a formula is provable (or
     deducible from other formulas), it is provable (or deducible) in a
     certain direct fashion; in other words, a theorem giving a normal form
     for proofs and deductions, the proofs and deduction in normal form being
     in some sense direct.  (End of Kleene excerpt)

     There is such a theorem, which was proven by Kleene.

     Formal proofs in H of even quite elementary theorems tend to be long.  As
     a price for having analyzed logical deduction into simple steps, more of
     those steps have to be used. The proofs of Metamath are fully detailed
     formal proofs.  We wish to have a means of writing rigorously verifiable
     mathematical proofs in a more direct fashion.  Natural Deduction is a
     system for proving theorems and deductions in a more direct fashion.
     However, Natural Deduction is not compatible for use with Metamath,
     which uses a Hilbert-type system.  Instead, Kleene's classical system G1
     may be used for proving Metamath deductions and theorems in a more
     direct fashion.

     The system of Metamath is an H system, not a Gentzen system.  Therefore,
     proofs in Kleene's classical system G1 ("G1") cannot be included in
     Metamath's system H, which we shall henceforth call "system H" or "H".
     However, we may translate proofs in G1 into proofs in H.

     By Kleene's THEOREM 47 (page 446)

     <HTML> <TABLE>
     <TR> <TD> if ` |- ->.. ph ` in G1 then ` |- ph ` in H
     </TABLE> </HTML>

     By Kleene's COROLLARY of THEOREM 47 (page 448)

     <HTML> <TABLE>
     <TR> <TD> if ` |- ph ->.. ps ` in G1 then ` |- (. ph ->. ps ). ` in H
     <TR> <TD> if ` |- ph ,. ps ->.. ch ` in G1 then
     ` |- (. (. ph ,. ps ). ->. ch ). ` in H
     <TR> <TD> if ` |- ph ,. ps ,. ch ->.. th ` in G1 then
     ` |- (. (. ph ,. ps ,. ch ). ->. th ). ` in H
     </TABLE> </HTML>

     ` ->. ` denotes the same connective denoted by ` -> ` . " , " , in the
     context of Virtual Deduction, denotes the same connective denoted by
     ` /\ ` .  This Virtual Deduction notation is specified by the following
     set.mm definitions:

     <HTML> <TABLE>
     <TR> <TD> ~ df-vd1 <TD> ` |- ( (. ph ->. ps ). <-> ( ph -> ps ) ) `
     <TR> <TD> ~ dfvd2an <TD> ` |- ( (. (. ph ,. ps ). ->. ch ). <-> `
     ` ( ( ph /\ ps ) -> ch ) ) `
     <TR> <TD> ~ dfvd3an <TD> ` |- ( (. (. ph ,. ps ,. ch ). ->. th ). <-> `
     ` ( ( ph /\ ps /\ ch ) -> th ) ) `
     </TABLE> </HTML>

     ` ->. ` replaces ` ->.. ` in the analogue in H of a sequent in G1 having
     a nonempty antecedent.  If ` ->. ` occurs as the outermost connective
     denoted by ` ->. ` or ` -> ` and occurs exactly once, we call the analogue
     in H of a sequent in G1 a "virtual deduction" because the corresponding
     ` ->.. ` of the sequent is assigned properties similar to ` |- ` .

     While sequent calculus proofs (proofs in G1) may have as steps
     sequents with 0, 1, or more formulas in the succedent, we shall only
     prove in G1 using sequents with exactly 1 formula in the succedent.

     The User proves in G1 in order to obtain the benefits of more direct
     proving using sequent calculus, then translates the proof in G1 into a
     proof in H.  The reference theorems and deductions to be used for proving
     in G1 are translations of theorems and deductions in set.mm.

     Each theorem ` |- ph ` in set.mm corresponds to the theorem
     ` |- ->.. ph ` in G1.  Deductions in G1 corresponding to deductions in H
     are similarly determined.  Theorems in H with one or more occurrences of
     either ` ->. ` or ` -> ` may also be translated into theorems in G1 for
     by replacing the outermost occurrence of ` ->. ` or ` -> ` of the theorem
     in H with ` ->.. ` .  Deductions in H may be translated into deductions
     in G1 in a similar manner.  The only theorems and deductions in H useful
     for proving in G1 for the purpose of obtaining proofs in H are those in
     which, for each hypothesis or assertion, there are 0 or 1 occurrences of
     ` ->. ` and it is the outermost occurrence of ` ->. ` or ` -> ` .
     Kleene's THEOREM 46 and its COROLLARY 2 are used for translating from H to
     G1.  By Kleene's THEOREM 46 (page 445)

     <HTML> <TABLE>
     <TR> <TD> if ` |- ph ` in H then ` |- ->.. ph ` in G1
     </TABLE> </HTML>

     By Kleene's COROLLARY 2 of THEOREM 46 (page 446)

     <HTML> <TABLE>
     <TR> <TD> if ` |- (. ph ->. ps ). ` in H  then ` |- ph ->.. ps ` in G1
     <TR> <TD> if ` |- (. (. ph ,. ps ). ->. ch ). ` in H then
     ` |- ph ,. ps ->.. ch ` in G1
     <TR> <TD> if ` |- (. (. ph ,. ps ,. ch ). ->. th ). ` in H then
     ` |- ph ,. ps ,. ch ->.. th ` in G1
     </TABLE> </HTML>

     To prove in H, the User simply proves in G1 and translates each G1-proof
     step into a H-proof step.  The translation is trivial and immediate.
     The proof in H is in Virtual Deduction notation.  It is a working proof
     in the sense that, if it has no errors, each theorem and deduction of
     the proof is true, but may or may not, after being translated into
     conventional notation, unify with any theorem or deduction scheme in
     set.mm.  Each theorem or deduction scheme in set.mm has a particular
     form.  The working proof written by the User (the "User's Proof" or
     "Virtual Deduction Proof") may contain theorems and deductions which
     would unify with a variant of a theorem or deduction scheme in set.mm,
     but not with any particular form of that theorem or deduction scheme
     in set.mm.

     The computer program completeusersproof.c may be applied to a Virtual
     Deduction proof to automatically add steps to the proof ("technical
     steps") which, if possible, transforms the form of a theorem or
     deduction of the Virtual Deduction proof not unifiable with a theorem or
     deduction scheme in set.mm into a variant form which is.  For theorems
     and deductions of the Virtual Deduction proof which are completable in
     this way, completeusersproof saves the User the extra work involved in
     satisfying the constraint that the theorem or deduction is in a form
     which unifies with a theorem or deduction scheme in set.mm.  mmj2, which
     is invoked by completeusersproof, automatically finds one of the
     reference theorems or deductions in set.mm which unifies with each
     theorem and deduction in the proof satisfying this constraint and labels
     the theorem or the assertion step of the deduction.

     The analogs in H of the postulates of G1 are the set.mm postulates.
     The postulates in G1 corresponding to the Metamath postulates are not
     the classical system G1 postulates of Kleene (pages 442 and 443).  set.mm
     has the predicate calculus postulates and other postulates.  The
     Kleene classical system G1 postulates correspond to predicate
     calculus postulates which differ from the Metamath system G1 postulates
     corresponding to the predicate calculus postulates of Metamath's system
     H.  Metamath's predicate calculus G1 postulates are presumably
     deducible from the Kleene classical G1 postulates and the Kleene
     classical G1 postulates are deducible from Metamath's G1 postulates.  It
     should be recognized that, because of the different postulates, the
     classical G1 system corresponding to Metamath's system H is not
     identical to Kleene's classical system G1.

     Why not create a separate database (setg.mm) of proofs in G1, avoiding
     the need to translate from H to G1 and from G1 back to H? The
     translations are trivial.  Sequents make the language more complex than
     is necessary.  More direct proving using sequent calculus may be done as
     a means towards the end of constructing proofs in H.  Then, the language
     may be kept as simple as possible.  A system G1 database would be
     redundant because it would duplicate the information contained in the
     corresponding system H database.

     For earlier proofs, each "User's Proof" in the web page description of
     a Virtual Deduction proof in set.mm is the analogue in H of the User's
     working proof in G1.  The User's Proof is automatically completed by
     completeusersproof.cmd (superseded by completeusersproof.c in September
     of 2016).  The completed proof is the Virtual Deduction proof, which is
     the analogue in H of the corresponding fully detailed proof in G1.  The
     completed Virtual Deduction proof of these earlier proofs may be
     automatically translated into a conventional Metamath proof.

     The input for completeusersproof.c is a Virtual Deduction proof.  Unlike
     completeusersproof.cmd, the completed proof is in conventional notation.
     completeusersproof.c eliminates the virtual deduction notation of the
     Virtual Deduction proof after utilizing the information it provides.

     Applying mmj2's unify command is essential to completeusersproof.  The
     mmj2 program is invoked within the completeusersproof.c function
     mmj2Unify().  The original mmj2 program was written by Mel L. O'Cat.
     Mario Carneiro has enhanced it.  mmj2Unify() is called multiple times
     during the execution of completeusersproof.

     A Virtual Deduction proof is a Metamath-specific version of a Natural
     Deduction Proof.  In order for mmj2 to complete a Virtual Deduction
     proof it is necessary that each theorem or deduction of the proof
     is in a form which unifies with a theorem or deduction scheme in set.mm.
     completeusersproof weakens this constraint.

     The User may write a Virtual Deduction proof and automatically transform
     it into a complete Metamath proof using the completeusersproof tool.
     The completed proof has been checked by the Metamath program.  The task
     of writing a complete Metamath proof is reduced to writing what is
     essentially a Natural Deduction Proof.

     The completeusersproof program and all associated files necessary to
     use it may be downloaded from the Metamath web site.  All syntax
     definitions, theorems, and deductions necessary to create Virtual
     Deduction proofs are contained in set.mm.  Examples of Virtual Deduction
     proofs in mmj2 Proof Worksheet .txt format are included in the
     completeusersproof download.

     ~ https://us.metamath.org/other/completeusersproof/suctrvd.html ,
     ~ https://us.metamath.org/other/completeusersproof/sineq0altvd.html ,
     ~ https://us.metamath.org/other/completeusersproof/iunconlem2vd.html ,
     ~ https://us.metamath.org/other/completeusersproof/isosctrlem1altvd.html ,
     and
     ~ https://us.metamath.org/other/completeusersproof/chordthmaltvd.html
     are examples of Virtual Deduction proofs.

     Generally, proving using Virtual Deduction and completeusersproof
     reduces the amount of Metamath-specific knowledge required by the User.
     Often, no knowledge of the specific theorems and deductions in set.mm
     is required to write some of the subproofs of a Virtual Deduction
     proof.  Often, no knowledge of the Metamath-specific names of reference
     theorems and deductions in set.mm is required for writing some of the
     subproofs of a User's Proof.  Often, the User may write subproofs of
     a proof using theorems or deductions commonly used in mathematics and
     correctly assume that some form of each is contained in set.mm and that
     completeusersproof will automatically generate the technical steps
     necessary to utilize them to complete the subproofs.  Often, the fraction
     of the work which may be considered tedious is reduced and the total
     amount of work is reduced. $)
  wvd1 $a wff (. ph ->. ps ). $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Virtual Deduction Theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Definition of virtual deduction.  (Contributed by Alan Sare, 21-Apr-2011.)
     (New usage is discouraged.) $)
  df-vd1 $a |- ( (. ph ->. ps ). <-> ( ph -> ps ) ) $.

  ${
    in1.1 $e |- (. ph ->. ps ). $.
    $( Inference form of ~ df-vd1 .  Virtual deduction introduction rule of
       converting the virtual hypothesis of a 1-virtual hypothesis virtual
       deduction into an antecedent.  (Contributed by Alan Sare, 14-Nov-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    in1 $p |- ( ph -> ps ) $=
      ( wvd1 wi df-vd1 mpbi ) ABDABECABFG $.
  $}

  ${
    iin1.1 $e |- ( ph -> ps ) $.
    $( ~ in1 without virtual deductions.  (Contributed by Alan Sare,
       23-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    iin1 $p |- ( ph -> ps ) $=
      (  ) C $.
  $}

  ${
    dfvd1ir.1 $e |- ( ph -> ps ) $.
    $( Inference form of ~ df-vd1 with the virtual deduction as the assertion.
       (Contributed by Alan Sare, 14-Nov-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dfvd1ir $p |- (. ph ->. ps ). $=
      ( wvd1 wi df-vd1 mpbir ) ABDABECABFG $.
  $}

  $( Virtual deduction identity rule which is ~ id with virtual deduction
     symbols.  (Contributed by Alan Sare, 24-Jun-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  idn1 $p |- (. ph ->. ph ). $=
    ( id dfvd1ir ) AAABC $.

  $( Left-to-right part of definition of virtual deduction.  (Contributed by
     Alan Sare, 21-Apr-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  dfvd1imp $p |- ( (. ph ->. ps ). -> ( ph -> ps ) ) $=
    ( wvd1 wi df-vd1 biimpi ) ABCABDABEF $.

  $( Right-to-left part of definition of virtual deduction.  (Contributed by
     Alan Sare, 21-Apr-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  dfvd1impr $p |- ( ( ph -> ps ) -> (. ph ->. ps ). ) $=
    ( wvd1 wi df-vd1 biimpri ) ABCABDABEF $.

  $( Syntax for a 2-hypothesis virtual deduction.
     (New usage is discouraged.) $)
  wvd2 $a wff (. ph ,. ps ->. ch ). $.

  $( Definition of a 2-hypothesis virtual deduction.  (Contributed by Alan
     Sare, 14-Nov-2011.)  (New usage is discouraged.) $)
  df-vd2 $a |- ( (. ph ,. ps ->. ch ). <-> ( ( ph /\ ps ) -> ch ) ) $.

  $( Definition of a 2-hypothesis virtual deduction.  (Contributed by Alan
     Sare, 14-Nov-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  dfvd2 $p |- ( (. ph ,. ps ->. ch ). <-> ( ph -> ( ps -> ch ) ) ) $=
    ( wvd2 wa wi df-vd2 impexp bitri ) ABCDABECFABCFFABCGABCHI $.

  $( Syntax for a 2-element virtual hypotheses collection.  (Contributed by
     Alan Sare, 23-Apr-2015.)  (New usage is discouraged.) $)
  wvhc2 $a wff (. ph ,. ps ). $.

  $( Definition of a 2-element virtual hypotheses collection.  (Contributed by
     Alan Sare, 23-Apr-2015.)  (New usage is discouraged.) $)
  df-vhc2 $a |- ( (. ph ,. ps ). <-> ( ph /\ ps ) ) $.

  $( Definition of a 2-hypothesis virtual deduction in vd conjunction form.
     (Contributed by Alan Sare, 23-Apr-2015.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  dfvd2an $p |- ( (. (. ph ,. ps ). ->. ch ). <-> ( ( ph /\ ps ) -> ch ) ) $=
    ( wvhc2 wvd1 wi wa df-vd1 df-vhc2 imbi1i bitri ) ABDZCELCFABGZCFLCHLMCABIJK
    $.

  ${
    dfvd2ani.1 $e |- (. (. ph ,. ps ). ->. ch ). $.
    $( Inference form of ~ dfvd2an .  (Contributed by Alan Sare, 23-Apr-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dfvd2ani $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wvhc2 wvd1 wa wi dfvd2an mpbi ) ABECFABGCHDABCIJ $.
  $}

  ${
    dfvd2anir.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Right-to-left inference form of ~ dfvd2an .  (Contributed by Alan Sare,
       23-Apr-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dfvd2anir $p |- (. (. ph ,. ps ). ->. ch ). $=
      ( wvhc2 wvd1 wa wi dfvd2an mpbir ) ABECFABGCHDABCIJ $.
  $}

  ${
    dfvd2i.1 $e |- (. ph ,. ps ->. ch ). $.
    $( Inference form of ~ dfvd2 .  (Contributed by Alan Sare, 14-Nov-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dfvd2i $p |- ( ph -> ( ps -> ch ) ) $=
      ( wvd2 wi dfvd2 mpbi ) ABCEABCFFDABCGH $.
  $}

  ${
    dfvd2ir.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Right-to-left inference form of ~ dfvd2 .  (Contributed by Alan Sare,
       14-Nov-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dfvd2ir $p |- (. ph ,. ps ->. ch ). $=
      ( wvd2 wi dfvd2 mpbir ) ABCEABCFFDABCGH $.
  $}

  $( Syntax for a 3-hypothesis virtual deduction.
     (New usage is discouraged.) $)
  wvd3 $a wff (. ph ,. ps ,. ch ->. th ). $.

  $( Syntax for a 3-element virtual hypotheses collection.  (Contributed by
     Alan Sare, 13-Jun-2015.)  (New usage is discouraged.) $)
  wvhc3 $a wff (. ph ,. ps ,. ch ). $.

  $( Definition of a 3-element virtual hypotheses collection.  (Contributed by
     Alan Sare, 13-Jun-2015.)  (New usage is discouraged.) $)
  df-vhc3 $a |- ( (. ph ,. ps ,. ch ). <-> ( ph /\ ps /\ ch ) ) $.

  $( Definition of a 3-hypothesis virtual deduction.  (Contributed by Alan
     Sare, 14-Nov-2011.)  (New usage is discouraged.) $)
  df-vd3 $a |- ( (. ph ,. ps ,. ch ->. th ). <->
               ( ( ph /\ ps /\ ch ) -> th ) ) $.

  $( Definition of a 3-hypothesis virtual deduction.  (Contributed by Alan
     Sare, 14-Nov-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  dfvd3 $p |- ( (. ph ,. ps ,. ch ->. th ). <->
               ( ph -> ( ps -> ( ch -> th ) ) ) ) $=
    ( wvd3 w3a wi df-vd3 wa df-3an imbi1i impexp bitri ) ABCDEABCFZDGZABCDGZGGZ
    ABCDHOABIZPGZQORCIZDGSNTDABCJKRCDLMABPLMM $.

  ${
    dfvd3i.1 $e |- (. ph ,. ps ,. ch ->. th ). $.
    $( Inference form of ~ dfvd3 .  (Contributed by Alan Sare, 14-Nov-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dfvd3i $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wvd3 wi dfvd3 mpbi ) ABCDFABCDGGGEABCDHI $.
  $}

  ${
    dfvd3ir.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Right-to-left inference form of ~ dfvd3 .  (Contributed by Alan Sare,
       14-Nov-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dfvd3ir $p |- (. ph ,. ps ,. ch ->. th ). $=
      ( wvd3 wi dfvd3 mpbir ) ABCDFABCDGGGEABCDHI $.
  $}

  $( Definition of a 3-hypothesis virtual deduction in vd conjunction form.
     (Contributed by Alan Sare, 13-Jun-2015.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  dfvd3an $p |- ( (. (. ph ,. ps ,. ch ). ->. th ). <->
                ( ( ph /\ ps /\ ch ) -> th ) ) $=
    ( wvhc3 wvd1 wi w3a df-vd1 df-vhc3 imbi1i bitri ) ABCEZDFMDGABCHZDGMDIMNDAB
    CJKL $.

  ${
    dfvd3ani.1 $e |- (. (. ph ,. ps ,. ch ). ->. th ). $.
    $( Inference form of ~ dfvd3an .  (Contributed by Alan Sare, 13-Jun-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dfvd3ani $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wvhc3 wvd1 w3a wi dfvd3an mpbi ) ABCFDGABCHDIEABCDJK $.
  $}

  ${
    dfvd3anir.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Right-to-left inference form of ~ dfvd3an .  (Contributed by Alan Sare,
       13-Jun-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dfvd3anir $p |- (. (. ph ,. ps ,. ch ). ->. th ). $=
      ( wvhc3 wvd1 w3a wi dfvd3an mpbir ) ABCFDGABCHDIEABCDJK $.
  $}

  ${
    vd01.1 $e |- ph $.
    $( A virtual hypothesis virtually infers a theorem.  (Contributed by Alan
       Sare, 14-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    vd01 $p |- (. ps ->. ph ). $=
      ( a1i dfvd1ir ) BAABCDE $.
  $}

  ${
    vd02.1 $e |- ph $.
    $( Two virtual hypotheses virtually infer a theorem.  (Contributed by Alan
       Sare, 14-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    vd02 $p |- (. ps ,. ch ->. ph ). $=
      ( wi a1i dfvd2ir ) BCACAEBACDFFG $.
  $}

  ${
    vd03.1 $e |- ph $.
    $( A theorem is virtually inferred by the 3 virtual hypotheses.
       (Contributed by Alan Sare, 12-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    vd03 $p |- (. ps ,. ch ,. th ->. ph ). $=
      ( wi a1i dfvd3ir ) BCDACDAFZFBICADEGGGH $.
  $}

  ${
    vd12.1 $e |- (. ph ->. ps ). $.
    $( A virtual deduction with 1 virtual hypothesis virtually inferring a
       virtual conclusion infers that the same conclusion is virtually inferred
       by the same virtual hypothesis and an additional hypothesis.
       (Contributed by Alan Sare, 12-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    vd12 $p |- (. ph ,. ch ->. ps ). $=
      ( in1 a1d dfvd2ir ) ACBABCABDEFG $.
  $}

  ${
    vd13.1 $e |- (. ph ->. ps ). $.
    $( A virtual deduction with 1 virtual hypothesis virtually inferring a
       virtual conclusion infers that the same conclusion is virtually inferred
       by the same virtual hypothesis and a two additional hypotheses.
       (Contributed by Alan Sare, 12-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    vd13 $p |- (. ph ,. ch ,. th ->. ps ). $=
      ( in1 a1d a1dd dfvd3ir ) ACDBACBDABCABEFGHI $.
  $}

  ${
    vd23.1 $e |- (. ph ,. ps ->. ch ). $.
    $( A virtual deduction with 2 virtual hypotheses virtually inferring a
       virtual conclusion infers that the same conclusion is virtually inferred
       by the same 2 virtual hypotheses and a third hypothesis.  (Contributed
       by Alan Sare, 12-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    vd23 $p |- (. ph ,. ps ,. th ->. ch ). $=
      ( dfvd2i a1dd dfvd3ir ) ABDCABCDABCEFGH $.
  $}

  $( The virtual deduction form of a 2-antecedent nested implication implies
     the 2-antecedent nested implication.  (Contributed by Alan Sare,
     21-Apr-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  dfvd2imp $p |- ( (. ph ,. ps ->. ch ). -> ( ph -> ( ps -> ch ) ) ) $=
    ( wvd2 wi dfvd2 biimpi ) ABCDABCEEABCFG $.

  $( A 2-antecedent nested implication implies its virtual deduction form.
     (Contributed by Alan Sare, 21-Apr-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  dfvd2impr $p |- ( ( ph -> ( ps -> ch ) ) -> (. ph ,. ps ->. ch ). ) $=
    ( wvd2 wi dfvd2 biimpri ) ABCDABCEEABCFG $.

  ${
    in2.1 $e |- (. ph ,. ps ->. ch ). $.
    $( The virtual deduction introduction rule of converting the end virtual
       hypothesis of 2 virtual hypotheses into an antecedent.  (Contributed by
       Alan Sare, 21-Apr-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    in2 $p |- (. ph ->. ( ps -> ch ) ). $=
      ( wi dfvd2i dfvd1ir ) ABCEABCDFG $.
  $}

  ${
    int2.1 $e |- (. (. ph ,. ps ). ->. ch ). $.
    $( The virtual deduction introduction rule of converting the end virtual
       hypothesis of 2 virtual hypotheses into an antecedent.  Conventional
       form of ~ int2 is ~ ex .  (Contributed by Alan Sare, 23-Apr-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    int2 $p |- (. ph ->. ( ps -> ch ) ). $=
      ( wi dfvd2ani ex dfvd1ir ) ABCEABCABCDFGH $.
  $}

  ${
    iin2.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( ~ in2 without virtual deductions.  (Contributed by Alan Sare,
       20-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    iin2 $p |- ( ph -> ( ps -> ch ) ) $=
      (  ) D $.
  $}

  ${
    in2an.1 $e |- (. ph ,. ( ps /\ ch ) ->. th ). $.
    $( The virtual deduction introduction rule converting the second conjunct
       of the second virtual hypothesis into the antecedent of the conclusion.
       ~ expd is the non-virtual deduction form of ~ in2an .  (Contributed by
       Alan Sare, 30-Jun-2012.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    in2an $p |- (. ph ,. ps ->. ( ch -> th ) ). $=
      ( wi wa dfvd2i expd dfvd2ir ) ABCDFABCDABCGDEHIJ $.
  $}

  ${
    in3.1 $e |- (. ph ,. ps ,. ch ->. th ). $.
    $( The virtual deduction introduction rule of converting the end virtual
       hypothesis of 3 virtual hypotheses into an antecedent.  (Contributed by
       Alan Sare, 12-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    in3 $p |- (. ph ,. ps ->. ( ch -> th ) ). $=
      ( wi dfvd3i dfvd2ir ) ABCDFABCDEGH $.
  $}

  ${
    iin3.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( ~ in3 without virtual deduction connectives.  Special theorem needed for
       the Virtual Deduction translation tool.  (Contributed by Alan Sare,
       23-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    iin3 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      (  ) E $.
  $}

  ${
    in3an.1 $e |- (. ph ,. ps ,. ( ch /\ th ) ->. ta ). $.
    $( The virtual deduction introduction rule converting the second conjunct
       of the third virtual hypothesis into the antecedent of the conclusion.
       ~ exp4a is the non-virtual deduction form of ~ in3an .  (Contributed by
       Alan Sare, 25-Jun-2012.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    in3an $p |- (. ph ,. ps ,. ch ->. ( th -> ta ) ). $=
      ( wi wa dfvd3i exp4a dfvd3ir ) ABCDEGABCDEABCDHEFIJK $.
  $}

  ${
    int3.1 $e |- (. (. ph ,. ps ,. ch ). ->. th ). $.
    $( The virtual deduction introduction rule of converting the end virtual
       hypothesis of 3 virtual hypotheses into an antecedent.  Conventional
       form of ~ int3 is ~ 3expia .  (Contributed by Alan Sare, 13-Jun-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    int3 $p |- (. (. ph ,. ps ). ->. ( ch -> th ) ). $=
      ( wi dfvd3ani 3expia dfvd2anir ) ABCDFABCDABCDEGHI $.
  $}

  $( Virtual deduction identity rule which is ~ idd with virtual deduction
     symbols.  (Contributed by Alan Sare, 21-Apr-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  idn2 $p |- (. ph ,. ps ->. ps ). $=
    ( idd dfvd2ir ) ABBABCD $.

  $( Virtual deduction identity rule. ~ simpr in conjunction form Virtual
     Deduction notation.  (Contributed by Alan Sare, 5-Sep-2016.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  iden2 $p |- (. (. ph ,. ps ). ->. ps ). $=
    ( wvhc2 wvd1 wa wi simpr dfvd2an mpbir ) ABCBDABEBFABGABBHI $.

  $( Virtual deduction identity rule for three virtual hypotheses.
     (Contributed by Alan Sare, 11-Jun-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  idn3 $p |- (. ph ,. ps ,. ch ->. ch ). $=
    ( wi idd a1i dfvd3ir ) ABCCBCCDDABCEFG $.

  ${
    $d x ph $.
    gen11.1 $e |- (. ph ->. ps ). $.
    $( Virtual deduction generalizing rule for one quantifying variable and one
       virtual hypothesis. ~ alrimiv is ~ gen11 without virtual deductions.
       (Contributed by Alan Sare, 21-Apr-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    gen11 $p |- (. ph ->. A. x ps ). $=
      ( wal wi wvd1 dfvd1imp ax-mp alrimiv dfvd1impr ) ABCEZFALGABCABGABFDABHIJ
      ALKI $.
  $}

  ${
    gen11nv.1 $e |- ( ph -> A. x ph ) $.
    gen11nv.2 $e |- (. ph ->. ps ). $.
    $( Virtual deduction generalizing rule for one quantifying variable and one
       virtual hypothesis without distinct variables. ~ alrimih is ~ gen11nv
       without virtual deductions.  (Contributed by Alan Sare, 12-Dec-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    gen11nv $p |- (. ph ->. A. x ps ). $=
      ( wal in1 alrimih dfvd1ir ) ABCFABCDABEGHI $.
  $}

  ${
    $d x ph $.  $d y ph $.
    gen12.1 $e |- (. ph ->. ps ). $.
    $( Virtual deduction generalizing rule for two quantifying variables and
       one virtual hypothesis. ~ gen12 is ~ alrimivv with virtual deductions.
       (Contributed by Alan Sare, 2-May-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    gen12 $p |- (. ph ->. A. x A. y ps ). $=
      ( wal in1 alrimivv dfvd1ir ) ABDFCFABCDABEGHI $.
  $}

  ${
    $d x ph $.  $d x ps $.
    gen21.1 $e |- (. ph ,. ps ->. ch ). $.
    $( Virtual deduction generalizing rule for one quantifying variables and
       two virtual hypothesis. ~ gen21 is ~ alrimdv with virtual deductions.
       (Contributed by Alan Sare, 25-Jul-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    gen21 $p |- (. ph ,. ps ->. A. x ch ). $=
      ( wal dfvd2i alrimdv dfvd2ir ) ABCDFABCDABCEGHI $.
  $}

  ${
    gen21nv.1 $e |- ( ph -> A. x ph ) $.
    gen21nv.2 $e |- ( ps -> A. x ps ) $.
    gen21nv.3 $e |- (. ph ,. ps ->. ch ). $.
    $( Virtual deduction form of ~ alrimdh .  (Contributed by Alan Sare,
       31-Dec-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    gen21nv $p |- (. ph ,. ps ->. A. x ch ). $=
      ( wal dfvd2i alrimdh dfvd2ir ) ABCDHABCDEFABCGIJK $.
  $}

  ${
    $d ch x $.  $d ph x $.  $d ps x $.
    gen31.1 $e |- (. ph ,. ps ,. ch ->. th ). $.
    $( Virtual deduction generalizing rule for one quantifying variable and
       three virtual hypothesis. ~ gen31 is ~ ggen31 with virtual deductions.
       (Contributed by Alan Sare, 22-Jun-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    gen31 $p |- (. ph ,. ps ,. ch ->. A. x th ). $=
      ( wal dfvd3i ggen31 dfvd3ir ) ABCDEGABCDEABCDFHIJ $.
  $}

  ${
    $d x ph $.  $d y ph $.  $d x ps $.  $d y ps $.
    gen22.1 $e |- (. ph ,. ps ->. ch ). $.
    $( Virtual deduction generalizing rule for two quantifying variables and
       two virtual hypothesis.  (Contributed by Alan Sare, 25-Jul-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    gen22 $p |- (. ph ,. ps ->. A. x A. y ch ). $=
      ( wal dfvd2i alrimdv dfvd2ir ) ABCEGZDGABKDABCEABCFHIIJ $.
  $}

  ${
    $d x ph $.  $d y ph $.  $d x ps $.  $d y ps $.
    ggen22.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( ~ gen22 without virtual deductions.  (Contributed by Alan Sare,
       25-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ggen22 $p |- ( ph -> ( ps -> A. x A. y ch ) ) $=
      ( wal alrimdv ) ABCEGDABCEFHH $.
  $}

  ${
    exinst.1 $e |- ( ps -> A. x ps ) $.
    exinst.2 $e |- (. E. x ph ,. ph ->. ps ). $.
    $( Existential Instantiation.  Virtual deduction form of ~ exlimexi .
       (Contributed by Alan Sare, 21-Apr-2013.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    exinst $p |- ( E. x ph -> ps ) $=
      ( wex dfvd2i exlimexi ) ABCDACFABEGH $.
  $}

  ${
    exinst01.1 $e |- E. x ps $.
    exinst01.2 $e |- (. ph ,. ps ->. ch ). $.
    exinst01.3 $e |- ( ph -> A. x ph ) $.
    exinst01.4 $e |- ( ch -> A. x ch ) $.
    $( Existential Instantiation.  Virtual Deduction rule corresponding to a
       special case of the Natural Deduction Sequent Calculus rule called Rule
       C in [Margaris] p. 79 and E ` E. ` in Table 1 on page 4 of the paper
       "Extracting information from intermediate T-systems" (2000) presented at
       IMLA99 by Mauro Ferrari, Camillo Fiorentini, and Pierangelo Miglioli.
       (Contributed by Alan Sare, 21-Apr-2013.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    exinst01 $p |- (. ph ->. ch ). $=
      ( dfvd2i eexinst01 dfvd1ir ) ACABCDEABCFIGHJK $.
  $}

  ${
    exinst11.1 $e |- (. ph ->. E. x ps ). $.
    exinst11.2 $e |- (. ph ,. ps ->. ch ). $.
    exinst11.3 $e |- ( ph -> A. x ph ) $.
    exinst11.4 $e |- ( ch -> A. x ch ) $.
    $( Existential Instantiation.  Virtual Deduction rule corresponding to a
       special case of the Natural Deduction Sequent Calculus rule called Rule
       C in [Margaris] p. 79 and E ` E. ` in Table 1 on page 4 of the paper
       "Extracting information from intermediate T-systems" (2000) presented at
       IMLA99 by Mauro Ferrari, Camillo Fiorentini, and Pierangelo Miglioli.
       (Contributed by Alan Sare, 21-Apr-2013.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    exinst11 $p |- (. ph ->. ch ). $=
      ( wex in1 dfvd2i eexinst11 dfvd1ir ) ACABCDABDIEJABCFKGHLM $.
  $}

  ${
    e1a.1 $e |- (. ph ->. ps ). $.
    e1a.2 $e |- ( ps -> ch ) $.
    $( A Virtual deduction elimination rule. ~ syl is ~ e1a without virtual
       deductions.  (Contributed by Alan Sare, 11-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    e1a $p |- (. ph ->. ch ). $=
      ( in1 syl dfvd1ir ) ACABCABDFEGH $.
  $}

  ${
    el1.1 $e |- (. ph ->. ps ). $.
    el1.2 $e |- ( ps -> ch ) $.
    $( A Virtual deduction elimination rule. ~ syl is ~ el1 without virtual
       deductions.  (Contributed by Alan Sare, 23-Apr-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    el1 $p |- (. ph ->. ch ). $=
      ( in1 syl dfvd1ir ) ACABCABDFEGH $.
  $}

  ${
    e1bi.1 $e |- (. ph ->. ps ). $.
    e1bi.2 $e |- ( ps <-> ch ) $.
    $( Biconditional form of ~ e1a . ~ sylib is ~ e1bi without virtual
       deductions.  (Contributed by Alan Sare, 15-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    e1bi $p |- (. ph ->. ch ). $=
      ( biimpi e1a ) ABCDBCEFG $.
  $}

  ${
    e1bir.1 $e |- (. ph ->. ps ). $.
    e1bir.2 $e |- ( ch <-> ps ) $.
    $( Right biconditional form of ~ e1a . ~ sylibr is ~ e1bir without virtual
       deductions.  (Contributed by Alan Sare, 24-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    e1bir $p |- (. ph ->. ch ). $=
      ( biimpri e1a ) ABCDCBEFG $.
  $}

  ${
    e2.1 $e |- (. ph ,. ps ->. ch ). $.
    e2.2 $e |- ( ch -> th ) $.
    $( A virtual deduction elimination rule. ~ syl6 is ~ e2 without virtual
       deductions.  (Contributed by Alan Sare, 21-Apr-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    e2 $p |- (. ph ,. ps ->. th ). $=
      ( dfvd2i syl6 dfvd2ir ) ABDABCDABCEGFHI $.
  $}

  ${
    e2bi.1 $e |- (. ph ,. ps ->. ch ). $.
    e2bi.2 $e |- ( ch <-> th ) $.
    $( Biconditional form of ~ e2 . ~ imbitrdi is ~ e2bi without virtual
       deductions.  (Contributed by Alan Sare, 10-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    e2bi $p |- (. ph ,. ps ->. th ). $=
      ( biimpi e2 ) ABCDECDFGH $.
  $}

  ${
    e2bir.1 $e |- (. ph ,. ps ->. ch ). $.
    e2bir.2 $e |- ( th <-> ch ) $.
    $( Right biconditional form of ~ e2 . ~ imbitrrdi is ~ e2bir without
       virtual deductions.  (Contributed by Alan Sare, 29-Apr-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    e2bir $p |- (. ph ,. ps ->. th ). $=
      ( biimpri e2 ) ABCDEDCFGH $.
  $}

  ${
    ee223.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee223.2 $e |- ( ph -> ( ps -> th ) ) $.
    ee223.3 $e |- ( ph -> ( ps -> ( ta -> et ) ) ) $.
    ee223.4 $e |- ( ch -> ( th -> ( et -> ze ) ) ) $.
    $( ~ e223 without virtual deductions.  (Contributed by Alan Sare,
       12-Dec-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee223 $p |- ( ph -> ( ps -> ( ta -> ze ) ) ) $=
      ( wi syl6 com34 com23 com12 syl8 pm2.43a pm2.43d mpdd ) ABDEGLIABEDGABEDG
      LZLABEBUABAEBUALZLABEAUBABEFAUBLJAFUBABFUAABDFGABCDFGLLHKMNOPQNRNSNT $.
  $}

  ${
    e223.1 $e |- (. ph ,. ps ->. ch ). $.
    e223.2 $e |- (. ph ,. ps ->. th ). $.
    e223.3 $e |- (. ph ,. ps ,. ta ->. et ). $.
    e223.4 $e |- ( ch -> ( th -> ( et -> ze ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       12-Dec-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e223 $p |- (. ph ,. ps ,. ta ->. ze ). $=
      ( wi in2 in1 in3 ee223 dfvd3ir ) ABEGABCDEFGABCLABCHMNABDLABDIMNABEFLZLAB
      RABEFJOMNKPQ $.
  $}

  ${
    e222.1 $e |- (. ph ,. ps ->. ch ). $.
    e222.2 $e |- (. ph ,. ps ->. th ). $.
    e222.3 $e |- (. ph ,. ps ->. ta ). $.
    e222.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       12-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e222 $p |- (. ph ,. ps ->. et ). $=
      ( wa dfvd2i imp wi syl2im pm2.43i syl5com ex dfvd2ir ) ABFABFABKZFTETFABE
      ABEILMTEFNZTCTDUAABCABCGLMABDABDHLMJOPQPRS $.
  $}

  ${
    e220.1 $e |- (. ph ,. ps ->. ch ). $.
    e220.2 $e |- (. ph ,. ps ->. th ). $.
    e220.3 $e |- ta $.
    e220.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e220 $p |- (. ph ,. ps ->. et ). $=
      ( vd02 e222 ) ABCDEFGHEABIKJL $.
  $}

  ${
    ee220.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee220.2 $e |- ( ph -> ( ps -> th ) ) $.
    ee220.3 $e |- ta $.
    ee220.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( ~ e220 without virtual deductions.  (Contributed by Alan Sare,
       12-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee220 $p |- ( ph -> ( ps -> et ) ) $=
      ( 2a1i ee222 ) ABCDEFGHEABIKJL $.
  $}

  ${
    e202.1 $e |- (. ph ,. ps ->. ch ). $.
    e202.2 $e |- th $.
    e202.3 $e |- (. ph ,. ps ->. ta ). $.
    e202.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e202 $p |- (. ph ,. ps ->. et ). $=
      ( vd02 e222 ) ABCDEFGDABHKIJL $.
  $}

  ${
    ee202.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee202.2 $e |- th $.
    ee202.3 $e |- ( ph -> ( ps -> ta ) ) $.
    ee202.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( ~ e202 without virtual deductions.  (Contributed by Alan Sare,
       13-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee202 $p |- ( ph -> ( ps -> et ) ) $=
      ( wi a1i ee222 ) ABCDEFGBDKADBHLLIJM $.
  $}

  ${
    e022.1 $e |- ph $.
    e022.2 $e |- (. ps ,. ch ->. th ). $.
    e022.3 $e |- (. ps ,. ch ->. ta ). $.
    e022.4 $e |- ( ph -> ( th -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e022 $p |- (. ps ,. ch ->. et ). $=
      ( vd02 e222 ) BCADEFABCGKHIJL $.
  $}

  ${
    ee022.1 $e |- ph $.
    ee022.2 $e |- ( ps -> ( ch -> th ) ) $.
    ee022.3 $e |- ( ps -> ( ch -> ta ) ) $.
    ee022.4 $e |- ( ph -> ( th -> ( ta -> et ) ) ) $.
    $( ~ e022 without virtual deductions.  (Contributed by Alan Sare,
       13-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee022 $p |- ( ps -> ( ch -> et ) ) $=
      ( wi a1i ee222 ) BCADEFCAKBACGLLHIJM $.
  $}

  ${
    e002.1 $e |- ph $.
    e002.2 $e |- ps $.
    e002.3 $e |- (. ch ,. th ->. ta ). $.
    e002.4 $e |- ( ph -> ( ps -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e002 $p |- (. ch ,. th ->. et ). $=
      ( vd02 e222 ) CDABEFACDGKBCDHKIJL $.
  $}

  ${
    ee002.1 $e |- ph $.
    ee002.2 $e |- ps $.
    ee002.3 $e |- ( ch -> ( th -> ta ) ) $.
    ee002.4 $e |- ( ph -> ( ps -> ( ta -> et ) ) ) $.
    $( ~ e002 without virtual deductions.  (Contributed by Alan Sare,
       13-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee002 $p |- ( ch -> ( th -> et ) ) $=
      ( wi a1i ee222 ) CDABEFDAKCADGLLDBKCBDHLLIJM $.
  $}

  ${
    e020.1 $e |- ph $.
    e020.2 $e |- (. ps ,. ch ->. th ). $.
    e020.3 $e |- ta $.
    e020.4 $e |- ( ph -> ( th -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e020 $p |- (. ps ,. ch ->. et ). $=
      ( vd02 e222 ) BCADEFABCGKHEBCIKJL $.
  $}

  ${
    ee020.1 $e |- ph $.
    ee020.2 $e |- ( ps -> ( ch -> th ) ) $.
    ee020.3 $e |- ta $.
    ee020.4 $e |- ( ph -> ( th -> ( ta -> et ) ) ) $.
    $( ~ e020 without virtual deductions.  (Contributed by Alan Sare,
       13-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee020 $p |- ( ps -> ( ch -> et ) ) $=
      ( wi a1i ee222 ) BCADEFCAKBACGLLHCEKBECILLJM $.
  $}

  ${
    e200.1 $e |- (. ph ,. ps ->. ch ). $.
    e200.2 $e |- th $.
    e200.3 $e |- ta $.
    e200.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e200 $p |- (. ph ,. ps ->. et ). $=
      ( vd02 e222 ) ABCDEFGDABHKEABIKJL $.
  $}

  ${
    ee200.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee200.2 $e |- th $.
    ee200.3 $e |- ta $.
    ee200.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( ~ e200 without virtual deductions.  (Contributed by Alan Sare,
       13-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee200 $p |- ( ph -> ( ps -> et ) ) $=
      ( wi a1i ee222 ) ABCDEFGBDKADBHLLBEKAEBILLJM $.
  $}

  ${
    e221.1 $e |- (. ph ,. ps ->. ch ). $.
    e221.2 $e |- (. ph ,. ps ->. th ). $.
    e221.3 $e |- (. ph ->. ta ). $.
    e221.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e221 $p |- (. ph ,. ps ->. et ). $=
      ( vd12 e222 ) ABCDEFGHAEBIKJL $.
  $}

  ${
    ee221.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee221.2 $e |- ( ph -> ( ps -> th ) ) $.
    ee221.3 $e |- ( ph -> ta ) $.
    ee221.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( ~ e221 without virtual deductions.  (Contributed by Alan Sare,
       13-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee221 $p |- ( ph -> ( ps -> et ) ) $=
      ( a1d ee222 ) ABCDEFGHAEBIKJL $.
  $}

  ${
    e212.1 $e |- (. ph ,. ps ->. ch ). $.
    e212.2 $e |- (. ph ->. th ). $.
    e212.3 $e |- (. ph ,. ps ->. ta ). $.
    e212.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e212 $p |- (. ph ,. ps ->. et ). $=
      ( vd12 e222 ) ABCDEFGADBHKIJL $.
  $}

  ${
    ee212.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee212.2 $e |- ( ph -> th ) $.
    ee212.3 $e |- ( ph -> ( ps -> ta ) ) $.
    ee212.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( ~ e212 without virtual deductions.  (Contributed by Alan Sare,
       13-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee212 $p |- ( ph -> ( ps -> et ) ) $=
      ( a1d ee222 ) ABCDEFGADBHKIJL $.
  $}

  ${
    e122.1 $e |- (. ph ->. ps ). $.
    e122.2 $e |- (. ph ,. ch ->. th ). $.
    e122.3 $e |- (. ph ,. ch ->. ta ). $.
    e122.4 $e |- ( ps -> ( th -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e122 $p |- (. ph ,. ch ->. et ). $=
      ( vd12 e222 ) ACBDEFABCGKHIJL $.
  $}

  ${
    e112.1 $e |- (. ph ->. ps ). $.
    e112.2 $e |- (. ph ->. ch ). $.
    e112.3 $e |- (. ph ,. th ->. ta ). $.
    e112.4 $e |- ( ps -> ( ch -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e112 $p |- (. ph ,. th ->. et ). $=
      ( vd12 e222 ) ADBCEFABDGKACDHKIJL $.
  $}

  ${
    ee112.1 $e |- ( ph -> ps ) $.
    ee112.2 $e |- ( ph -> ch ) $.
    ee112.3 $e |- ( ph -> ( th -> ta ) ) $.
    ee112.4 $e |- ( ps -> ( ch -> ( ta -> et ) ) ) $.
    $( ~ e112 without virtual deductions.  (Contributed by Alan Sare,
       13-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee112 $p |- ( ph -> ( th -> et ) ) $=
      ( a1d ee222 ) ADBCEFABDGKACDHKIJL $.
  $}

  ${
    e121.1 $e |- (. ph ->. ps ). $.
    e121.2 $e |- (. ph ,. ch ->. th ). $.
    e121.3 $e |- (. ph ->. ta ). $.
    e121.4 $e |- ( ps -> ( th -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e121 $p |- (. ph ,. ch ->. et ). $=
      ( vd12 e222 ) ACBDEFABCGKHAECIKJL $.
  $}

  ${
    e211.1 $e |- (. ph ,. ps ->. ch ). $.
    e211.2 $e |- (. ph ->. th ). $.
    e211.3 $e |- (. ph ->. ta ). $.
    e211.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e211 $p |- (. ph ,. ps ->. et ). $=
      ( vd12 e222 ) ABCDEFGADBHKAEBIKJL $.
  $}

  ${
    ee211.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee211.2 $e |- ( ph -> th ) $.
    ee211.3 $e |- ( ph -> ta ) $.
    ee211.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( ~ e211 without virtual deductions.  (Contributed by Alan Sare,
       13-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee211 $p |- ( ph -> ( ps -> et ) ) $=
      ( a1d ee222 ) ABCDEFGADBHKAEBIKJL $.
  $}

  ${
    e210.1 $e |- (. ph ,. ps ->. ch ). $.
    e210.2 $e |- (. ph ->. th ). $.
    e210.3 $e |- ta $.
    e210.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e210 $p |- (. ph ,. ps ->. et ). $=
      ( vd01 e211 ) ABCDEFGHEAIKJL $.
  $}

  ${
    ee210.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee210.2 $e |- ( ph -> th ) $.
    ee210.3 $e |- ta $.
    ee210.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( ~ e210 without virtual deductions.  (Contributed by Alan Sare,
       14-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee210 $p |- ( ph -> ( ps -> et ) ) $=
      ( a1d wi a1i ee222 ) ABCDEFGADBHKBELAEBIMMJN $.
  $}

  ${
    e201.1 $e |- (. ph ,. ps ->. ch ). $.
    e201.2 $e |- th $.
    e201.3 $e |- (. ph ->. ta ). $.
    e201.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e201 $p |- (. ph ,. ps ->. et ). $=
      ( vd01 e211 ) ABCDEFGDAHKIJL $.
  $}

  ${
    ee201.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee201.2 $e |- th $.
    ee201.3 $e |- ( ph -> ta ) $.
    ee201.4 $e |- ( ch -> ( th -> ( ta -> et ) ) ) $.
    $( ~ e201 without virtual deductions.  (Contributed by Alan Sare,
       14-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee201 $p |- ( ph -> ( ps -> et ) ) $=
      ( wi a1i a1d ee222 ) ABCDEFGBDKADBHLLAEBIMJN $.
  $}

  ${
    e120.1 $e |- (. ph ->. ps ). $.
    e120.2 $e |- (. ph ,. ch ->. th ). $.
    e120.3 $e |- ta $.
    e120.4 $e |- ( ps -> ( th -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       10-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e120 $p |- (. ph ,. ch ->. et ). $=
      ( vd12 e220 ) ACBDEFABCGKHIJL $.
  $}

  ${
    ee120.1 $e |- ( ph -> ps ) $.
    ee120.2 $e |- ( ph -> ( ch -> th ) ) $.
    ee120.3 $e |- ta $.
    ee120.4 $e |- ( ps -> ( th -> ( ta -> et ) ) ) $.
    $( Virtual deduction rule ~ e120 without virtual deduction symbols.
       (Contributed by Alan Sare, 14-Jul-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ee120 $p |- ( ph -> ( ch -> et ) ) $=
      ( a1d wi a1i ee222 ) ACBDEFABCGKHCELAECIMMJN $.
  $}

  ${
    e021.1 $e |- ph $.
    e021.2 $e |- (. ps ,. ch ->. th ). $.
    e021.3 $e |- (. ps ->. ta ). $.
    e021.4 $e |- ( ph -> ( th -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e021 $p |- (. ps ,. ch ->. et ). $=
      ( vd01 e121 ) BACDEFABGKHIJL $.
  $}

  ${
    ee021.1 $e |- ph $.
    ee021.2 $e |- ( ps -> ( ch -> th ) ) $.
    ee021.3 $e |- ( ps -> ta ) $.
    ee021.4 $e |- ( ph -> ( th -> ( ta -> et ) ) ) $.
    $( ~ e021 without virtual deductions.  (Contributed by Alan Sare,
       14-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee021 $p |- ( ps -> ( ch -> et ) ) $=
      ( wi a1i a1d ee222 ) BCADEFCAKBACGLLHBECIMJN $.
  $}

  ${
    e012.1 $e |- ph $.
    e012.2 $e |- (. ps ->. ch ). $.
    e012.3 $e |- (. ps ,. th ->. ta ). $.
    e012.4 $e |- ( ph -> ( ch -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e012 $p |- (. ps ,. th ->. et ). $=
      ( vd01 e112 ) BACDEFABGKHIJL $.
  $}

  ${
    ee012.1 $e |- ph $.
    ee012.2 $e |- ( ps -> ch ) $.
    ee012.3 $e |- ( ps -> ( th -> ta ) ) $.
    ee012.4 $e |- ( ph -> ( ch -> ( ta -> et ) ) ) $.
    $( ~ e012 without virtual deductions.  (Contributed by Alan Sare,
       14-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee012 $p |- ( ps -> ( th -> et ) ) $=
      ( wi a1i a1d ee222 ) BDACEFDAKBADGLLBCDHMIJN $.
  $}

  ${
    e102.1 $e |- (. ph ->. ps ). $.
    e102.2 $e |- ch $.
    e102.3 $e |- (. ph ,. th ->. ta ). $.
    e102.4 $e |- ( ps -> ( ch -> ( ta -> et ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e102 $p |- (. ph ,. th ->. et ). $=
      ( vd01 e112 ) ABCDEFGCAHKIJL $.
  $}

  ${
    ee102.1 $e |- ( ph -> ps ) $.
    ee102.2 $e |- ch $.
    ee102.3 $e |- ( ph -> ( th -> ta ) ) $.
    ee102.4 $e |- ( ps -> ( ch -> ( ta -> et ) ) ) $.
    $( ~ e102 without virtual deductions.  (Contributed by Alan Sare,
       14-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee102 $p |- ( ph -> ( th -> et ) ) $=
      ( a1d wi a1i ee222 ) ADBCEFABDGKDCLACDHMMIJN $.
  $}

  ${
    e22.1 $e |- (. ph ,. ps ->. ch ). $.
    e22.2 $e |- (. ph ,. ps ->. th ). $.
    e22.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       2-May-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e22 $p |- (. ph ,. ps ->. ta ). $=
      ( wi a1i e222 ) ABCCDEFFGCDEIICHJK $.
  $}

  ${
    e22an.1 $e |- (. ph ,. ps ->. ch ). $.
    e22an.2 $e |- (. ph ,. ps ->. th ). $.
    e22an.3 $e |- ( ( ch /\ th ) -> ta ) $.
    $( Conjunction form of ~ e22 .  (Contributed by Alan Sare, 11-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    e22an $p |- (. ph ,. ps ->. ta ). $=
      ( ex e22 ) ABCDEFGCDEHIJ $.
  $}

  ${
    ee22an.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee22an.2 $e |- ( ph -> ( ps -> th ) ) $.
    ee22an.3 $e |- ( ( ch /\ th ) -> ta ) $.
    $( ~ e22an without virtual deductions.  (Contributed by Alan Sare,
       8-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee22an $p |- ( ph -> ( ps -> ta ) ) $=
      ( ex syl6c ) ABCDEFGCDEHIJ $.
  $}

  ${
    e111.1 $e |- (. ph ->. ps ). $.
    e111.2 $e |- (. ph ->. ch ). $.
    e111.3 $e |- (. ph ->. th ). $.
    e111.4 $e |- ( ps -> ( ch -> ( th -> ta ) ) ) $.
    $( A virtual deduction elimination rule (see ~ syl3c ).  (Contributed by
       Alan Sare, 14-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e111 $p |- (. ph ->. ta ). $=
      ( in1 wi syl2im pm2.43i syl5com dfvd1ir ) AEAEADAEADHJADEKZABACPABFJACGJI
      LMNMO $.
  $}

  ${
    e1111.1 $e |- (. ph ->. ps ). $.
    e1111.2 $e |- (. ph ->. ch ). $.
    e1111.3 $e |- (. ph ->. th ). $.
    e1111.4 $e |- (. ph ->. ta ). $.
    e1111.5 $e |- ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       6-Mar-2012.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e1111 $p |- (. ph ->. et ). $=
      ( in1 ee1111 dfvd1ir ) AFABCDEFABGLACHLADILAEJLKMN $.
  $}

  ${
    e110.1 $e |- (. ph ->. ps ). $.
    e110.2 $e |- (. ph ->. ch ). $.
    e110.3 $e |- th $.
    e110.4 $e |- ( ps -> ( ch -> ( th -> ta ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e110 $p |- (. ph ->. ta ). $=
      ( vd01 e111 ) ABCDEFGDAHJIK $.
  $}

  ${
    ee110.1 $e |- ( ph -> ps ) $.
    ee110.2 $e |- ( ph -> ch ) $.
    ee110.3 $e |- th $.
    ee110.4 $e |- ( ps -> ( ch -> ( th -> ta ) ) ) $.
    $( ~ e110 without virtual deductions.  (Contributed by Alan Sare,
       22-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee110 $p |- ( ph -> ta ) $=
      ( a1i syl3c ) ABCDEFGDAHJIK $.
  $}

  ${
    e101.1 $e |- (. ph ->. ps ). $.
    e101.2 $e |- ch $.
    e101.3 $e |- (. ph ->. th ). $.
    e101.4 $e |- ( ps -> ( ch -> ( th -> ta ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e101 $p |- (. ph ->. ta ). $=
      ( vd01 e111 ) ABCDEFCAGJHIK $.
  $}

  ${
    ee101.1 $e |- ( ph -> ps ) $.
    ee101.2 $e |- ch $.
    ee101.3 $e |- ( ph -> th ) $.
    ee101.4 $e |- ( ps -> ( ch -> ( th -> ta ) ) ) $.
    $( ~ e101 without virtual deductions.  (Contributed by Alan Sare,
       23-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee101 $p |- ( ph -> ta ) $=
      ( a1i syl3c ) ABCDEFCAGJHIK $.
  $}

  ${
    e011.1 $e |- ph $.
    e011.2 $e |- (. ps ->. ch ). $.
    e011.3 $e |- (. ps ->. th ). $.
    e011.4 $e |- ( ph -> ( ch -> ( th -> ta ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e011 $p |- (. ps ->. ta ). $=
      ( vd01 e111 ) BACDEABFJGHIK $.
  $}

  ${
    ee011.1 $e |- ph $.
    ee011.2 $e |- ( ps -> ch ) $.
    ee011.3 $e |- ( ps -> th ) $.
    ee011.4 $e |- ( ph -> ( ch -> ( th -> ta ) ) ) $.
    $( ~ e011 without virtual deductions.  (Contributed by Alan Sare,
       25-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee011 $p |- ( ps -> ta ) $=
      ( a1i syl3c ) BACDEABFJGHIK $.
  $}

  ${
    e100.1 $e |- (. ph ->. ps ). $.
    e100.2 $e |- ch $.
    e100.3 $e |- th $.
    e100.4 $e |- ( ps -> ( ch -> ( th -> ta ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e100 $p |- (. ph ->. ta ). $=
      ( vd01 e111 ) ABCDEFCAGJDAHJIK $.
  $}

  ${
    ee100.1 $e |- ( ph -> ps ) $.
    ee100.2 $e |- ch $.
    ee100.3 $e |- th $.
    ee100.4 $e |- ( ps -> ( ch -> ( th -> ta ) ) ) $.
    $( ~ e100 without virtual deductions.  (Contributed by Alan Sare,
       23-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee100 $p |- ( ph -> ta ) $=
      ( a1i syl3c ) ABCDEFCAGJDAHJIK $.
  $}

  ${
    e010.1 $e |- ph $.
    e010.2 $e |- (. ps ->. ch ). $.
    e010.3 $e |- th $.
    e010.4 $e |- ( ph -> ( ch -> ( th -> ta ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e010 $p |- (. ps ->. ta ). $=
      ( vd01 e111 ) BACDEABFJGDBHJIK $.
  $}

  ${
    ee010.1 $e |- ph $.
    ee010.2 $e |- ( ps -> ch ) $.
    ee010.3 $e |- th $.
    ee010.4 $e |- ( ph -> ( ch -> ( th -> ta ) ) ) $.
    $( ~ e010 without virtual deductions.  (Contributed by Alan Sare,
       23-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee010 $p |- ( ps -> ta ) $=
      ( a1i syl3c ) BACDEABFJGDBHJIK $.
  $}

  ${
    e001.1 $e |- ph $.
    e001.2 $e |- ps $.
    e001.3 $e |- (. ch ->. th ). $.
    e001.4 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e001 $p |- (. ch ->. ta ). $=
      ( vd01 e111 ) CABDEACFJBCGJHIK $.
  $}

  ${
    ee001.1 $e |- ph $.
    ee001.2 $e |- ps $.
    ee001.3 $e |- ( ch -> th ) $.
    ee001.4 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
    $( ~ e001 without virtual deductions.  (Contributed by Alan Sare,
       23-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee001 $p |- ( ch -> ta ) $=
      ( a1i syl3c ) CABDEACFJBCGJHIK $.
  $}

  ${
    e11.1 $e |- (. ph ->. ps ). $.
    e11.2 $e |- (. ph ->. ch ). $.
    e11.3 $e |- ( ps -> ( ch -> th ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       14-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e11 $p |- (. ph ->. th ). $=
      ( wi a1i e111 ) ABBCDEEFBCDHHBGIJ $.
  $}

  ${
    e11an.1 $e |- (. ph ->. ps ). $.
    e11an.2 $e |- (. ph ->. ch ). $.
    e11an.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( Conjunction form of ~ e11 .  (Contributed by Alan Sare, 15-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    e11an $p |- (. ph ->. th ). $=
      ( ex e11 ) ABCDEFBCDGHI $.
  $}

  ${
    ee11an.1 $e |- ( ph -> ps ) $.
    ee11an.2 $e |- ( ph -> ch ) $.
    ee11an.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( ~ e11an without virtual deductions. ~ syl22anc is also ~ e11an without
       virtual deductions, exept with a different order of hypotheses.
       (Contributed by Alan Sare, 8-Jul-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ee11an $p |- ( ph -> th ) $=
      ( ex sylc ) ABCDEFBCDGHI $.
  $}

  ${
    e01.1 $e |- ph $.
    e01.2 $e |- (. ps ->. ch ). $.
    e01.3 $e |- ( ph -> ( ch -> th ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       25-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e01 $p |- (. ps ->. th ). $=
      ( vd01 e11 ) BACDABEHFGI $.
  $}

  ${
    e01an.1 $e |- ph $.
    e01an.2 $e |- (. ps ->. ch ). $.
    e01an.3 $e |- ( ( ph /\ ch ) -> th ) $.
    $( Conjunction form of ~ e01 .  (Contributed by Alan Sare, 11-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    e01an $p |- (. ps ->. th ). $=
      ( ex e01 ) ABCDEFACDGHI $.
  $}

  ${
    ee01an.1 $e |- ph $.
    ee01an.2 $e |- ( ps -> ch ) $.
    ee01an.3 $e |- ( ( ph /\ ch ) -> th ) $.
    $( ~ e01an without virtual deductions. ~ sylancr is also a form of ~ e01an
       without virtual deduction, except the order of the hypotheses is
       different.  (Contributed by Alan Sare, 25-Jul-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ee01an $p |- ( ps -> th ) $=
      ( sylancr ) BACDEFGH $.
  $}

  ${
    e10.1 $e |- (. ph ->. ps ). $.
    e10.2 $e |- ch $.
    e10.3 $e |- ( ps -> ( ch -> th ) ) $.
    $( A virtual deduction elimination rule (see ~ mpisyl ).  (Contributed by
       Alan Sare, 14-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e10 $p |- (. ph ->. th ). $=
      ( vd01 e11 ) ABCDECAFHGI $.
  $}

  ${
    e10an.1 $e |- (. ph ->. ps ). $.
    e10an.2 $e |- ch $.
    e10an.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( Conjunction form of ~ e10 .  (Contributed by Alan Sare, 15-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    e10an $p |- (. ph ->. th ). $=
      ( ex e10 ) ABCDEFBCDGHI $.
  $}

  ${
    ee10an.1 $e |- ( ph -> ps ) $.
    ee10an.2 $e |- ch $.
    ee10an.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( ~ e10an without virtual deductions. ~ sylancl is also ~ e10an without
       virtual deductions, except the order of the hypotheses is different.
       (Contributed by Alan Sare, 25-Jul-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ee10an $p |- ( ph -> th ) $=
      ( sylancl ) ABCDEFGH $.
  $}

  ${
    e02.1 $e |- ph $.
    e02.2 $e |- (. ps ,. ch ->. th ). $.
    e02.3 $e |- ( ph -> ( th -> ta ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       14-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e02 $p |- (. ps ,. ch ->. ta ). $=
      ( vd02 e22 ) BCADEABCFIGHJ $.
  $}

  ${
    e02an.1 $e |- ph $.
    e02an.2 $e |- (. ps ,. ch ->. th ). $.
    e02an.3 $e |- ( ( ph /\ th ) -> ta ) $.
    $( Conjunction form of ~ e02 .  (Contributed by Alan Sare, 15-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    e02an $p |- (. ps ,. ch ->. ta ). $=
      ( ex e02 ) ABCDEFGADEHIJ $.
  $}

  ${
    ee02an.1 $e |- ph $.
    ee02an.2 $e |- ( ps -> ( ch -> th ) ) $.
    ee02an.3 $e |- ( ( ph /\ th ) -> ta ) $.
    $( ~ e02an without virtual deductions.  (Contributed by Alan Sare,
       8-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee02an $p |- ( ps -> ( ch -> ta ) ) $=
      ( ex mpsylsyld ) ABCDEFGADEHIJ $.
  $}

  ${
    eel021.1 $e |- ph $.
    eel021.2 $e |- ( ( ps /\ ch ) -> th ) $.
    eel021.3 $e |- ( ( ph /\ th ) -> ta ) $.
    $( ~ el021old without virtual deductions.  (Contributed by Alan Sare,
       13-Jun-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eel021old $p |- ( ( ps /\ ch ) -> ta ) $=
      ( wa sylancr ) BCIADEFGHJ $.
  $}

  ${
    el021old.1 $e |- ph $.
    el021old.2 $e |- (. (. ps ,. ch ). ->. th ). $.
    el021old.3 $e |- ( ( ph /\ th ) -> ta ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       13-Jun-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    el021old $p |- (. (. ps ,. ch ). ->. ta ). $=
      ( wa dfvd2ani sylancr dfvd2anir ) BCEBCIADEFBCDGJHKL $.
  $}

  ${
    eel000cT.1 $e |- ph $.
    eel000cT.2 $e |- ps $.
    eel000cT.3 $e |- ch $.
    eel000cT.4 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eel000cT $p |- ( T. -> th ) $=
      ( wtru mp3an1 mpan ax-mp a1i ) DICDGBCDFABCDEHJKLM $.
  $}

  ${
    eel0TT.1 $e |- ph $.
    eel0TT.2 $e |- ( T. -> ps ) $.
    eel0TT.3 $e |- ( T. -> ch ) $.
    eel0TT.4 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eel0TT $p |- th $=
      ( wtru wa truan mp3an1 sylan sylbir syl mptru ) DICDGCICJDCKIBCDFABCDEHLM
      NOP $.
  $}

  ${
    eelT00.1 $e |- ( T. -> ph ) $.
    eelT00.2 $e |- ps $.
    eelT00.3 $e |- ch $.
    eelT00.4 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eelT00 $p |- th $=
      ( wa wtru w3a 3anass truan bitri syl3an1 sylbir mpan ax-mp ) CDGBCDFBCIZJ
      BCKZDTJSISJBCLSMNJABCDEHOPQR $.
  $}

  ${
    eelTTT.1 $e |- ( T. -> ph ) $.
    eelTTT.2 $e |- ( T. -> ps ) $.
    eelTTT.3 $e |- ( T. -> ch ) $.
    eelTTT.4 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eelTTT $p |- th $=
      ( wtru wa truan w3a 3anass bitri syl3an1 sylbir sylan syl mptru ) DICDGCI
      CJDCKIBCDFBCJZIBCLZDUAITJTIBCMTKNIABCDEHOPQPRS $.
  $}

  ${
    eelT11.1 $e |- ( T. -> ph ) $.
    eelT11.2 $e |- ( ps -> ch ) $.
    eelT11.3 $e |- ( ps -> th ) $.
    eelT11.4 $e |- ( ( ph /\ ch /\ th ) -> ta ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eelT11 $p |- ( ps -> ta ) $=
      ( wtru w3a wa 3anass truan anidm 3bitri syl3an1 syl3an2 syl3an3 sylbir )
      BJBBKZEUAJBBLZLUBBJBBMUBNBOPBJBDEHBJCDEGJACDEFIQRST $.
  $}

  ${
    eelT1.1 $e |- ( T. -> ph ) $.
    eelT1.2 $e |- ( ps -> ch ) $.
    eelT1.3 $e |- ( ( ph /\ ch ) -> th ) $.
    $( Syllogism inference combined with _modus ponens_.  (Contributed by Jeff
       Madsen, 2-Sep-2009.)  (Revised by Alan Sare, 23-Dec-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eelT1 $p |- ( ps -> th ) $=
      ( mptru sylancr ) BACDAEHFGI $.
  $}

  ${
    eelT12.1 $e |- ( T. -> ph ) $.
    eelT12.2 $e |- ( ps -> ch ) $.
    eelT12.3 $e |- ( th -> ta ) $.
    eelT12.4 $e |- ( ( ph /\ ch /\ ta ) -> et ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eelT12 $p |- ( ( ps /\ th ) -> et ) $=
      ( wa wtru w3a 3anass truan bitri syl3an1 syl3an2 syl3an3 sylbir ) BDKZLBD
      MZFUBLUAKUALBDNUAOPDLBEFIBLCEFHLACEFGJQRST $.
  $}

  ${
    eelTT1.1 $e |- ( T. -> ph ) $.
    eelTT1.2 $e |- ( T. -> ps ) $.
    eelTT1.3 $e |- ( ch -> th ) $.
    eelTT1.4 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eelTT1 $p |- ( ch -> ta ) $=
      ( wtru w3a wa 3anass anabs5 truan 3bitri syl3an1 syl3an2 syl3an3 sylbir )
      CJJCKZEUAJJCLZLUBCJJCMJCNCOPCJJDEHJJBDEGJABDEFIQRST $.
  $}

  ${
    eelT01.1 $e |- ( T. -> ph ) $.
    eelT01.2 $e |- ps $.
    eelT01.3 $e |- ( ch -> th ) $.
    eelT01.4 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eelT01 $p |- ( ch -> ta ) $=
      ( wtru w3a wa 3anass truan simpr jctl impbii 3bitri syl3an1 syl3an3
      sylbir ) CJBCKZEUBJBCLZLUCCJBCMUCNUCCBCOCBGPQRCJBDEHJABDEFISTUA $.
  $}

  ${
    eel0T1.1 $e |- ph $.
    eel0T1.2 $e |- ( T. -> ps ) $.
    eel0T1.3 $e |- ( ch -> th ) $.
    eel0T1.4 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eel0T1 $p |- ( ch -> ta ) $=
      ( wtru w3a wa 3anass simpr jctl impbii truan 3bitri syl3an2 syl3an3
      sylbir ) CAJCKZEUBAJCLZLZUCCAJCMUDUCAUCNUCAFOPCQRCAJDEHJABDEGISTUA $.
  $}

  ${
    eel12131.1 $e |- ( ph -> ps ) $.
    eel12131.2 $e |- ( ( ph /\ ch ) -> th ) $.
    eel12131.3 $e |- ( ( ph /\ ta ) -> et ) $.
    eel12131.4 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 17-Oct-2017.) $)
    eel12131 $p |- ( ( ph /\ ch /\ ta ) -> ze ) $=
      ( wi wa 3exp syl2imc ex pm2.43b com13 syl 3imp231 ) EACGEACGLZAEAUALZAEMF
      UBJCAFGCAFGLZACAUCLABACMDUCHIBDFGKNOPQRSPQT $.
  $}

  ${
    eel2131.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    eel2131.2 $e |- ( ( ph /\ th ) -> ta ) $.
    eel2131.3 $e |- ( ( ch /\ ta ) -> et ) $.
    $( ~ syl2an with antecedents in standard conjunction form.  (Contributed by
       Alan Sare, 26-Aug-2016.) $)
    eel2131 $p |- ( ( ph /\ ps /\ th ) -> et ) $=
      ( wa syl2an 3impdi ) ABDFABJCEFADJGHIKL $.
  $}

  ${
    eel3132.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    eel3132.2 $e |- ( ( th /\ ps ) -> ta ) $.
    eel3132.3 $e |- ( ( ch /\ ta ) -> et ) $.
    $( ~ syl2an with antecedents in standard conjunction form.  (Contributed by
       Alan Sare, 27-Aug-2016.) $)
    eel3132 $p |- ( ( ph /\ th /\ ps ) -> et ) $=
      ( wa syl2an 3impdir ) ABDFABJCEFDBJGHIKL $.
  $}

  ${
    eel0321old.1 $e |- ph $.
    eel0321old.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    eel0321old.3 $e |- ( ( ph /\ ta ) -> et ) $.
    $( ~ el0321old without virtual deductions.  (Contributed by Alan Sare,
       13-Jun-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eel0321old $p |- ( ( ps /\ ch /\ th ) -> et ) $=
      ( w3a sylancr ) BCDJAEFGHIK $.
  $}

  ${
    el0321old.1 $e |- ph $.
    el0321old.2 $e |- (. (. ps ,. ch ,. th ). ->. ta ). $.
    el0321old.3 $e |- ( ( ph /\ ta ) -> et ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       13-Jun-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    el0321old $p |- (. (. ps ,. ch ,. th ). ->. et ). $=
      ( dfvd3ani eel0321old dfvd3anir ) BCDFABCDEFGBCDEHJIKL $.
  $}

  ${
    eel2122old.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    eel2122old.2 $e |- ( ps -> th ) $.
    eel2122old.3 $e |- ( ps -> ta ) $.
    eel2122old.4 $e |- ( ( ch /\ th /\ ta ) -> et ) $.
    $( ~ el2122old without virtual deductions.  (Contributed by Alan Sare,
       13-Jun-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eel2122old $p |- ( ( ph /\ ps ) -> et ) $=
      ( wi wa 3exp syl syl5 syl7 ex pm2.43d imp ) ABFABFABBFKZABBTKBEABLZBFIBDU
      AEFKZHUACDUBKGCDEFJMNOPQRRS $.
  $}

  ${
    el2122old.1 $e |- (. (. ph ,. ps ). ->. ch ). $.
    el2122old.2 $e |- (. ps ->. th ). $.
    el2122old.3 $e |- (. ps ->. ta ). $.
    el2122old.4 $e |- ( ( ch /\ th /\ ta ) -> et ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       13-Jun-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    el2122old $p |- (. (. ph ,. ps ). ->. et ). $=
      ( dfvd2ani in1 eel2122old dfvd2anir ) ABFABCDEFABCGKBDHLBEILJMN $.
  $}

  ${
    eel0000.1 $e |- ph $.
    eel0000.2 $e |- ps $.
    eel0000.3 $e |- ch $.
    eel0000.4 $e |- th $.
    eel0000.5 $e |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $.
    $( Elimination rule similar to ~ mp4an , except with a left-nested
       conjunction unification theorem.  (Contributed by Alan Sare,
       17-Oct-2017.) $)
    eel0000 $p |- ta $=
      ( wi exp41 mp2 ) CDEHIABCDEKKFGABCDEJLMM $.
  $}

  ${
    eel00001.1 $e |- ph $.
    eel00001.2 $e |- ps $.
    eel00001.3 $e |- ch $.
    eel00001.4 $e |- th $.
    eel00001.5 $e |- ( ta -> et ) $.
    eel00001.6 $e |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ et ) -> ze ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 17-Oct-2017.) $)
    eel00001 $p |- ( ta -> ze ) $=
      ( wi wa exp41 mp2an mp2 syl ) EFGLCDFGNZJKABCDTNNHIABOCDFGMPQRS $.
  $}

  ${
    eel00000.1 $e |- ph $.
    eel00000.2 $e |- ps $.
    eel00000.3 $e |- ch $.
    eel00000.4 $e |- th $.
    eel00000.5 $e |- ta $.
    eel00000.6 $e |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) -> et ) $.
    $( Elimination rule similar ~ eel0000 , except with five hpothesis steps.
       (Contributed by Alan Sare, 17-Oct-2017.) $)
    eel00000 $p |- et $=
      ( wi wa exp41 mpan mp2 ) DEFJKBCDEFMMZHIABCRMGABNCDEFLOPQQ $.
  $}

  ${
    eel11111.1 $e |- ( ph -> ps ) $.
    eel11111.2 $e |- ( ph -> ch ) $.
    eel11111.3 $e |- ( ph -> th ) $.
    eel11111.4 $e |- ( ph -> ta ) $.
    eel11111.5 $e |- ( ph -> et ) $.
    eel11111.6 $e |- ( ( ( ( ( ps /\ ch ) /\ th ) /\ ta ) /\ et ) -> ze ) $.
    $( Five-hypothesis elimination deduction for an assertion with a singleton
       virtual hypothesis collection.  Similar to ~ syl113anc except the
       unification theorem uses left-nested conjunction.  (Contributed by Alan
       Sare, 17-Oct-2017.) $)
    eel11111 $p |- ( ph -> ze ) $=
      ( wi wa exp41 ex syl3c mp2d ) AEFGKLABCDEFGNNZHIJBCDTNBCODEFGMPQRS $.
  $}

  ${
    e12.1 $e |- (. ph ->. ps ). $.
    e12.2 $e |- (. ph ,. ch ->. th ). $.
    e12.3 $e |- ( ps -> ( th -> ta ) ) $.
    $( A virtual deduction elimination rule (see ~ sylsyld ).  (Contributed by
       Alan Sare, 21-Apr-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e12 $p |- (. ph ,. ch ->. ta ). $=
      ( vd12 e22 ) ACBDEABCFIGHJ $.
  $}

  ${
    e12an.1 $e |- (. ph ->. ps ). $.
    e12an.2 $e |- (. ph ,. ch ->. th ). $.
    e12an.3 $e |- ( ( ps /\ th ) -> ta ) $.
    $( Conjunction form of ~ e12 (see ~ syl6an ).  (Contributed by Alan Sare,
       11-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e12an $p |- (. ph ,. ch ->. ta ). $=
      ( ex e12 ) ABCDEFGBDEHIJ $.
  $}

  ${
    el12.1 $e |- (. ph ->. ps ). $.
    el12.2 $e |- (. ta ->. ch ). $.
    el12.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( Virtual deduction form of ~ syl2an .  (Contributed by Alan Sare,
       23-Apr-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    el12 $p |- (. (. ph ,. ta ). ->. th ). $=
      ( in1 syl2an dfvd2anir ) AEDABCDEABFIECGIHJK $.
  $}

  ${
    e20.1 $e |- (. ph ,. ps ->. ch ). $.
    e20.2 $e |- th $.
    e20.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( A virtual deduction elimination rule (see ~ syl6mpi ).  (Contributed by
       Alan Sare, 14-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e20 $p |- (. ph ,. ps ->. ta ). $=
      ( vd02 e22 ) ABCDEFDABGIHJ $.
  $}

  ${
    e20an.1 $e |- (. ph ,. ps ->. ch ). $.
    e20an.2 $e |- th $.
    e20an.3 $e |- ( ( ch /\ th ) -> ta ) $.
    $( Conjunction form of ~ e20 .  (Contributed by Alan Sare, 15-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    e20an $p |- (. ph ,. ps ->. ta ). $=
      ( ex e20 ) ABCDEFGCDEHIJ $.
  $}

  ${
    ee20an.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee20an.2 $e |- th $.
    ee20an.3 $e |- ( ( ch /\ th ) -> ta ) $.
    $( ~ e20an without virtual deductions.  (Contributed by Alan Sare,
       8-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee20an $p |- ( ph -> ( ps -> ta ) ) $=
      ( ex syl6mpi ) ABCDEFGCDEHIJ $.
  $}

  ${
    e21.1 $e |- (. ph ,. ps ->. ch ). $.
    e21.2 $e |- (. ph ->. th ). $.
    e21.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( A virtual deduction elimination rule (see ~ syl6ci ).  (Contributed by
       Alan Sare, 12-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e21 $p |- (. ph ,. ps ->. ta ). $=
      ( vd12 e22 ) ABCDEFADBGIHJ $.
  $}

  ${
    e21an.1 $e |- (. ph ,. ps ->. ch ). $.
    e21an.2 $e |- (. ph ->. th ). $.
    e21an.3 $e |- ( ( ch /\ th ) -> ta ) $.
    $( Conjunction form of ~ e21 .  (Contributed by Alan Sare, 15-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    e21an $p |- (. ph ,. ps ->. ta ). $=
      ( ex e21 ) ABCDEFGCDEHIJ $.
  $}

  ${
    ee21an.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee21an.2 $e |- ( ph -> th ) $.
    ee21an.3 $e |- ( ( ch /\ th ) -> ta ) $.
    $( ~ e21an without virtual deductions.  (Contributed by Alan Sare,
       8-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee21an $p |- ( ph -> ( ps -> ta ) ) $=
      ( ex syl6ci ) ABCDEFGCDEHIJ $.
  $}

  ${
    e333.1 $e |- (. ph ,. ps ,. ch ->. th ). $.
    e333.2 $e |- (. ph ,. ps ,. ch ->. ta ). $.
    e333.3 $e |- (. ph ,. ps ,. ch ->. et ). $.
    e333.4 $e |- ( th -> ( ta -> ( et -> ze ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       12-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e333 $p |- (. ph ,. ps ,. ch ->. ze ). $=
      ( w3a dfvd3i 3imp wi syl2im pm2.43i syl5com 3exp dfvd3ir ) ABCGABCGABCLZG
      UAFUAGABCFABCFJMNUAFGOZUADUAEUBABCDABCDHMNABCEABCEIMNKPQRQST $.
  $}

  ${
    e33.1 $e |- (. ph ,. ps ,. ch ->. th ). $.
    e33.2 $e |- (. ph ,. ps ,. ch ->. ta ). $.
    e33.3 $e |- ( th -> ( ta -> et ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       12-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e33 $p |- (. ph ,. ps ,. ch ->. et ). $=
      ( wi a1i e333 ) ABCDDEFGGHDEFJJDIKL $.
  $}

  ${
    e33an.1 $e |- (. ph ,. ps ,. ch ->. th ). $.
    e33an.2 $e |- (. ph ,. ps ,. ch ->. ta ). $.
    e33an.3 $e |- ( ( th /\ ta ) -> et ) $.
    $( Conjunction form of ~ e33 .  (Contributed by Alan Sare, 15-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    e33an $p |- (. ph ,. ps ,. ch ->. et ). $=
      ( ex e33 ) ABCDEFGHDEFIJK $.
  $}

  ${
    ee33an.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    ee33an.2 $e |- ( ph -> ( ps -> ( ch -> ta ) ) ) $.
    ee33an.3 $e |- ( ( th /\ ta ) -> et ) $.
    $( ~ e33an without virtual deductions.  (Contributed by Alan Sare,
       8-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee33an $p |- ( ph -> ( ps -> ( ch -> et ) ) ) $=
      ( ex ee33 ) ABCDEFGHDEFIJK $.
  $}

  ${
    e3.1 $e |- (. ph ,. ps ,. ch ->. th ). $.
    e3.2 $e |- ( th -> ta ) $.
    $( Meta-connective form of ~ syl8 .  (Contributed by Alan Sare,
       15-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e3 $p |- (. ph ,. ps ,. ch ->. ta ). $=
      ( wi a1i e33 ) ABCDDEFFDEHDGIJ $.
  $}

  ${
    e3bi.1 $e |- (. ph ,. ps ,. ch ->. th ). $.
    e3bi.2 $e |- ( th <-> ta ) $.
    $( Biconditional form of ~ e3 . ~ syl8ib is ~ e3bi without virtual
       deductions.  (Contributed by Alan Sare, 15-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    e3bi $p |- (. ph ,. ps ,. ch ->. ta ). $=
      ( biimpi e3 ) ABCDEFDEGHI $.
  $}

  ${
    e3bir.1 $e |- (. ph ,. ps ,. ch ->. th ). $.
    e3bir.2 $e |- ( ta <-> th ) $.
    $( Right biconditional form of ~ e3 .  (Contributed by Alan Sare,
       15-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e3bir $p |- (. ph ,. ps ,. ch ->. ta ). $=
      ( biimpri e3 ) ABCDEFEDGHI $.
  $}

  ${
    e03.1 $e |- ph $.
    e03.2 $e |- (. ps ,. ch ,. th ->. ta ). $.
    e03.3 $e |- ( ph -> ( ta -> et ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       12-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e03 $p |- (. ps ,. ch ,. th ->. et ). $=
      ( vd03 e33 ) BCDAEFABCDGJHIK $.
  $}

  ${
    ee03.1 $e |- ph $.
    ee03.2 $e |- ( ps -> ( ch -> ( th -> ta ) ) ) $.
    ee03.3 $e |- ( ph -> ( ta -> et ) ) $.
    $( ~ e03 without virtual deductions.  (Contributed by Alan Sare,
       17-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee03 $p |- ( ps -> ( ch -> ( th -> et ) ) ) $=
      ( a1i a1d a1dd ee33 ) BCDAEFBCADBACABGJKLHIM $.
  $}

  ${
    e03an.1 $e |- ph $.
    e03an.2 $e |- (. ps ,. ch ,. th ->. ta ). $.
    e03an.3 $e |- ( ( ph /\ ta ) -> et ) $.
    $( Conjunction form of ~ e03 .  (Contributed by Alan Sare, 12-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    e03an $p |- (. ps ,. ch ,. th ->. et ). $=
      ( ex e03 ) ABCDEFGHAEFIJK $.
  $}

  ${
    ee03an.1 $e |- ph $.
    ee03an.2 $e |- ( ps -> ( ch -> ( th -> ta ) ) ) $.
    ee03an.3 $e |- ( ( ph /\ ta ) -> et ) $.
    $( Conjunction form of ~ ee03 .  (Contributed by Alan Sare, 18-Jul-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ee03an $p |- ( ps -> ( ch -> ( th -> et ) ) ) $=
      ( ex ee03 ) ABCDEFGHAEFIJK $.
  $}

  ${
    e30.1 $e |- (. ph ,. ps ,. ch ->. th ). $.
    e30.2 $e |- ta $.
    e30.3 $e |- ( th -> ( ta -> et ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       12-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e30 $p |- (. ph ,. ps ,. ch ->. et ). $=
      ( vd03 e33 ) ABCDEFGEABCHJIK $.
  $}

  ${
    ee30.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    ee30.2 $e |- ta $.
    ee30.3 $e |- ( th -> ( ta -> et ) ) $.
    $( ~ e30 without virtual deductions.  (Contributed by Alan Sare,
       17-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee30 $p |- ( ph -> ( ps -> ( ch -> et ) ) ) $=
      ( wi a1i ee33 ) ABCDEFGBCEJZJAMBECHKKKIL $.
  $}

  ${
    e30an.1 $e |- (. ph ,. ps ,. ch ->. th ). $.
    e30an.2 $e |- ta $.
    e30an.3 $e |- ( ( th /\ ta ) -> et ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e30an $p |- (. ph ,. ps ,. ch ->. et ). $=
      ( ex e30 ) ABCDEFGHDEFIJK $.
  $}

  ${
    ee30an.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    ee30an.2 $e |- ta $.
    ee30an.3 $e |- ( ( th /\ ta ) -> et ) $.
    $( Conjunction form of ~ ee30 .  (Contributed by Alan Sare, 17-Jul-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ee30an $p |- ( ph -> ( ps -> ( ch -> et ) ) ) $=
      ( ex ee30 ) ABCDEFGHDEFIJK $.
  $}

  ${
    e13.1 $e |- (. ph ->. ps ). $.
    e13.2 $e |- (. ph ,. ch ,. th ->. ta ). $.
    e13.3 $e |- ( ps -> ( ta -> et ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       13-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e13 $p |- (. ph ,. ch ,. th ->. et ). $=
      ( vd13 e33 ) ACDBEFABCDGJHIK $.
  $}

  ${
    e13an.1 $e |- (. ph ->. ps ). $.
    e13an.2 $e |- (. ph ,. ch ,. th ->. ta ). $.
    e13an.3 $e |- ( ( ps /\ ta ) -> et ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e13an $p |- (. ph ,. ch ,. th ->. et ). $=
      ( ex e13 ) ABCDEFGHBEFIJK $.
  $}

  ${
    ee13an.1 $e |- ( ph -> ps ) $.
    ee13an.2 $e |- ( ph -> ( ch -> ( th -> ta ) ) ) $.
    ee13an.3 $e |- ( ( ps /\ ta ) -> et ) $.
    $( ~ e13an without virtual deductions.  (Contributed by Alan Sare,
       8-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee13an $p |- ( ph -> ( ch -> ( th -> et ) ) ) $=
      ( ex ee13 ) ABCDEFGHBEFIJK $.
  $}

  ${
    e31.1 $e |- (. ph ,. ps ,. ch ->. th ). $.
    e31.2 $e |- (. ph ->. ta ). $.
    e31.3 $e |- ( th -> ( ta -> et ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       13-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e31 $p |- (. ph ,. ps ,. ch ->. et ). $=
      ( vd13 e33 ) ABCDEFGAEBCHJIK $.
  $}

  ${
    ee31.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    ee31.2 $e |- ( ph -> ta ) $.
    ee31.3 $e |- ( th -> ( ta -> et ) ) $.
    $( ~ e31 without virtual deductions.  (Contributed by Alan Sare,
       25-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee31 $p |- ( ph -> ( ps -> ( ch -> et ) ) ) $=
      ( wi a1d ee33 ) ABCDEFGACEJBAECHKKIL $.
  $}

  ${
    e31an.1 $e |- (. ph ,. ps ,. ch ->. th ). $.
    e31an.2 $e |- (. ph ->. ta ). $.
    e31an.3 $e |- ( ( th /\ ta ) -> et ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e31an $p |- (. ph ,. ps ,. ch ->. et ). $=
      ( ex e31 ) ABCDEFGHDEFIJK $.
  $}

  ${
    ee31an.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    ee31an.2 $e |- ( ph -> ta ) $.
    ee31an.3 $e |- ( ( th /\ ta ) -> et ) $.
    $( ~ e31an without virtual deductions.  (Contributed by Alan Sare,
       14-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee31an $p |- ( ph -> ( ps -> ( ch -> et ) ) ) $=
      ( wi a1d ee33an ) ABCDEFGACEJBAECHKKIL $.
  $}

  ${
    e23.1 $e |- (. ph ,. ps ->. ch ). $.
    e23.2 $e |- (. ph ,. ps ,. th ->. ta ). $.
    e23.3 $e |- ( ch -> ( ta -> et ) ) $.
    $( A virtual deduction elimination rule (see ~ syl10 ).  (Contributed by
       Alan Sare, 12-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e23 $p |- (. ph ,. ps ,. th ->. et ). $=
      ( vd23 e33 ) ABDCEFABCDGJHIK $.
  $}

  ${
    e23an.1 $e |- (. ph ,. ps ->. ch ). $.
    e23an.2 $e |- (. ph ,. ps ,. th ->. ta ). $.
    e23an.3 $e |- ( ( ch /\ ta ) -> et ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e23an $p |- (. ph ,. ps ,. th ->. et ). $=
      ( ex e23 ) ABCDEFGHCEFIJK $.
  $}

  ${
    ee23an.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee23an.2 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
    ee23an.3 $e |- ( ( ch /\ ta ) -> et ) $.
    $( ~ e23an without virtual deductions.  (Contributed by Alan Sare,
       14-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee23an $p |- ( ph -> ( ps -> ( th -> et ) ) ) $=
      ( a1dd ee33an ) ABDCEFABCDGJHIK $.
  $}

  ${
    e32.1 $e |- (. ph ,. ps ,. ch ->. th ). $.
    e32.2 $e |- (. ph ,. ps ->. ta ). $.
    e32.3 $e |- ( th -> ( ta -> et ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       12-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e32 $p |- (. ph ,. ps ,. ch ->. et ). $=
      ( vd23 e33 ) ABCDEFGABECHJIK $.
  $}

  ${
    ee32.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    ee32.2 $e |- ( ph -> ( ps -> ta ) ) $.
    ee32.3 $e |- ( th -> ( ta -> et ) ) $.
    $( ~ e32 without virtual deductions.  (Contributed by Alan Sare,
       18-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee32 $p |- ( ph -> ( ps -> ( ch -> et ) ) ) $=
      ( a1dd ee33 ) ABCDEFGABECHJIK $.
  $}

  ${
    e32an.1 $e |- (. ph ,. ps ,. ch ->. th ). $.
    e32an.2 $e |- (. ph ,. ps ->. ta ). $.
    e32an.3 $e |- ( ( th /\ ta ) -> et ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       24-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e32an $p |- (. ph ,. ps ,. ch ->. et ). $=
      ( ex e32 ) ABCDEFGHDEFIJK $.
  $}

  ${
    ee32an.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    ee32an.2 $e |- ( ph -> ( ps -> ta ) ) $.
    ee32an.3 $e |- ( ( th /\ ta ) -> et ) $.
    $( ~ e33an without virtual deductions.  (Contributed by Alan Sare,
       14-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee32an $p |- ( ph -> ( ps -> ( ch -> et ) ) ) $=
      ( a1dd ee33an ) ABCDEFGABECHJIK $.
  $}

  ${
    e123.1 $e |- (. ph ->. ps ). $.
    e123.2 $e |- (. ph ,. ch ->. th ). $.
    e123.3 $e |- (. ph ,. ch ,. ta ->. et ). $.
    e123.4 $e |- ( ps -> ( th -> ( et -> ze ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       12-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e123 $p |- (. ph ,. ch ,. ta ->. ze ). $=
      ( vd13 vd23 e333 ) ACEBDFGABCEHLACDEIMJKN $.
  $}

  ${
    ee123.1 $e |- ( ph -> ps ) $.
    ee123.2 $e |- ( ph -> ( ch -> th ) ) $.
    ee123.3 $e |- ( ph -> ( ch -> ( ta -> et ) ) ) $.
    ee123.4 $e |- ( ps -> ( th -> ( et -> ze ) ) ) $.
    $( ~ e123 without virtual deductions.  (Contributed by Alan Sare,
       25-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ee123 $p |- ( ph -> ( ch -> ( ta -> ze ) ) ) $=
      ( wi a1d a1dd ee333 ) ACEBDFGAEBLCABEHMMACDEINJKO $.
  $}

  ${
    el123.1 $e |- (. ph ->. ps ). $.
    el123.2 $e |- (. ch ->. th ). $.
    el123.3 $e |- (. ta ->. et ). $.
    el123.4 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       13-Jun-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    el123 $p |- (. (. ph ,. ch ,. ta ). ->. ze ). $=
      ( in1 syl3an dfvd3anir ) ACEGABCDEFGABHLCDILEFJLKMN $.
  $}

  ${
    e233.1 $e |- (. ph ,. ps ->. ch ). $.
    e233.2 $e |- (. ph ,. ps ,. th ->. ta ). $.
    e233.3 $e |- (. ph ,. ps ,. th ->. et ). $.
    e233.4 $e |- ( ch -> ( ta -> ( et -> ze ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       29-Feb-2012.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e233 $p |- (. ph ,. ps ,. th ->. ze ). $=
      ( dfvd2i dfvd3i ee233 dfvd3ir ) ABDGABCDEFGABCHLABDEIMABDFJMKNO $.
  $}

  ${
    e323.1 $e |- (. ph ,. ps ,. ch ->. th ). $.
    e323.2 $e |- (. ph ,. ps ->. ta ). $.
    e323.3 $e |- (. ph ,. ps ,. ch ->. et ). $.
    e323.4 $e |- ( th -> ( ta -> ( et -> ze ) ) ) $.
    $( A virtual deduction elimination rule.  (Contributed by Alan Sare,
       17-Apr-2012.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e323 $p |- (. ph ,. ps ,. ch ->. ze ). $=
      ( dfvd3i dfvd2i ee323 dfvd3ir ) ABCGABCDEFGABCDHLABEIMABCFJLKNO $.
  $}

  ${
    e000.1 $e |- ph $.
    e000.2 $e |- ps $.
    e000.3 $e |- ch $.
    e000.4 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A virtual deduction elimination rule.  The non-virtual deduction form of
       ~ e000 is the virtual deduction form.  (Contributed by Alan Sare,
       14-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e000 $p |- th $=
      ( wi mp2 ax-mp ) CDGABCDIEFHJK $.
  $}

  ${
    e00.1 $e |- ph $.
    e00.2 $e |- ps $.
    e00.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Elimination rule identical to ~ mp2 .  The non-virtual deduction form is
       the virtual deduction form, which is ~ mp2 .  (Contributed by Alan Sare,
       14-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e00 $p |- ch $=
      ( mp2 ) ABCDEFG $.
  $}

  ${
    e00an.1 $e |- ph $.
    e00an.2 $e |- ps $.
    e00an.3 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Elimination rule identical to ~ mp2an .  The non-virtual deduction form
       is the virtual deduction form, which is ~ mp2an .  (Contributed by Alan
       Sare, 15-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e00an $p |- ch $=
      ( mp2an ) ABCDEFG $.
  $}

  ${
    eel00cT.1 $e |- ph $.
    eel00cT.2 $e |- ps $.
    eel00cT.3 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eel00cT $p |- ( T. -> ch ) $=
      ( wtru mpan ax-mp a1i ) CGBCEABCDFHIJ $.
  $}

  ${
    eelTT.1 $e |- ( T. -> ph ) $.
    eelTT.2 $e |- ( T. -> ps ) $.
    eelTT.3 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eelTT $p |- ch $=
      ( wtru wa truan sylan sylbir syl mptru ) CGBCEBGBHCBIGABCDFJKLM $.
  $}

  ${
    e0a.1 $e |- ph $.
    e0a.2 $e |- ( ph -> ps ) $.
    $( Elimination rule identical to ~ ax-mp .  The non-virtual deduction form
       is the virtual deduction form, which is ~ ax-mp .  (Contributed by Alan
       Sare, 14-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e0a $p |- ps $=
      ( ax-mp ) ABCDE $.
  $}

  ${
    eelT.1 $e |- ( T. -> ph ) $.
    eelT.2 $e |- ( ph -> ps ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 5-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eelT $p |- ps $=
      ( wtru syl mptru ) BEABCDFG $.
  $}

  ${
    eel0cT.1 $e |- ph $.
    eel0cT.2 $e |- ( ph -> ps ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eel0cT $p |- ( T. -> ps ) $=
      ( wtru ax-mp a1i ) BEABCDFG $.
  $}

  ${
    eelT0.1 $e |- ( T. -> ph ) $.
    eelT0.2 $e |- ps $.
    eelT0.3 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eelT0 $p |- ch $=
      ( wtru sylan mpan2 mptru ) CGBCEGABCDFHIJ $.
  $}

  ${
    e0bi.1 $e |- ph $.
    e0bi.2 $e |- ( ph <-> ps ) $.
    $( Elimination rule identical to ~ mpbi .  The non-virtual deduction form
       is the virtual deduction form, which is ~ mpbi .  (Contributed by Alan
       Sare, 15-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e0bi $p |- ps $=
      ( mpbi ) ABCDE $.
  $}

  ${
    e0bir.1 $e |- ph $.
    e0bir.2 $e |- ( ps <-> ph ) $.
    $( Elimination rule identical to ~ mpbir .  The non-virtual deduction form
       is the virtual deduction form, which is ~ mpbir .  (Contributed by Alan
       Sare, 15-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    e0bir $p |- ps $=
      ( mpbir ) BACDE $.
  $}

  ${
    uun0.1.1 $e |- ( T. -> ph ) $.
    uun0.1.2 $e |- ( ps -> ch ) $.
    uun0.1.3 $e |- ( ( T. /\ ps ) -> th ) $.
    $( Convention notation form of ~ un0.1 .  (Contributed by Alan Sare,
       23-Apr-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    uun0.1 $p |- ( ps -> th ) $=
      ( wtru wi tru wa pm3.2i simpri ex ax-mp ) HBDIJHBDHAIZBCIZKZHBKDIZRSPQEFL
      GLMNO $.
  $}

  ${
    un0.1.1 $e |- (. T. ->. ph ). $.
    un0.1.2 $e |- (. ps ->. ch ). $.
    un0.1.3 $e |- (. (. T. ,. ps ). ->. th ). $.
    $( ` T. ` is the constant true, a tautology (see ~ df-tru ).  Kleene's
       "empty conjunction" is logically equivalent to ` T. ` .  In a virtual
       deduction we shall interpret ` T. ` to be the empty wff or the empty
       collection of virtual hypotheses. ` T. ` in a virtual deduction
       translated into conventional notation we shall interpret to be Kleene's
       empty conjunction.  If ` th ` is true given the empty collection of
       virtual hypotheses and another collection of virtual hypotheses, then it
       is true given only the other collection of virtual hypotheses.
       (Contributed by Alan Sare, 23-Apr-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    un0.1 $p |- (. ps ->. th ). $=
      ( wtru in1 dfvd2ani uun0.1 dfvd1ir ) BDABCDHAEIBCFIHBDGJKL $.
  $}

  ${
    uunT1.1 $e |- ( ( T. /\ ph ) -> ps ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 3-Dec-2015.)  Proof was revised to
       accommodate a possible future version of ~ df-tru .  (Revised by David
       A. Wheeler, 8-May-2019.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    uunT1 $p |- ( ph -> ps ) $=
      ( wtru wn wo orc tru biid 2th exmid a1i biidd impbii bitri sylibr mpancom
      wb ) DABAAAEZFZDASGDAARZTDUAHAIJUATTUAAKLTAMNOPCQ $.
  $}

  ${
    uunT1p1.1 $e |- ( ( ph /\ T. ) -> ps ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uunT1p1 $p |- ( ph -> ps ) $=
      ( wtru wa ancom truan bitri sylbir ) AADEZBJDAEAADFAGHCI $.
  $}

  ${
    uunT21.1 $e |- ( ( T. /\ ( ph /\ ps ) ) -> ch ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 3-Dec-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uunT21 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa uunT1 ) ABECDF $.
  $}

  ${
    uun121.1 $e |- ( ( ph /\ ( ph /\ ps ) ) -> ch ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uun121 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa anabs5 sylbir ) ABEZAHECABFDG $.
  $}

  ${
    uun121p1.1 $e |- ( ( ( ph /\ ps ) /\ ph ) -> ch ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uun121p1 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa anabs1 sylbir ) ABEZHAECABFDG $.
  $}

  ${
    uun132.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uun132 $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( w3a wa 3anass sylbi ) ABCFABCGGDABCHEI $.
  $}

  ${
    uun132p1.1 $e |- ( ( ( ps /\ ch ) /\ ph ) -> th ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uun132p1 $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( w3a wa 3anass ancom bitri sylbi ) ABCFZBCGZAGZDLAMGNABCHAMIJEK $.
  $}

  ${
    anabss7p1.1 $e |- ( ( ( ps /\ ph ) /\ ph ) -> ch ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       This would have been named uun221 if the zeroth permutation did not
       exist in set.mm as ~ anabss7 .  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    anabss7p1 $p |- ( ( ps /\ ph ) -> ch ) $=
      ( anabss3 ) BACDE $.
  $}

  ${
    un10.1 $e |- (. (. ph ,. T. ). ->. ps ). $.
    $( A unionizing deduction.  (Contributed by Alan Sare, 28-Apr-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    un10 $p |- (. ph ->. ps ). $=
      ( wtru wa tru jctr dfvd2ani syl dfvd1ir ) ABAADEBADFGADBCHIJ $.
  $}

  ${
    un01.1 $e |- (. (. T. ,. ph ). ->. ps ). $.
    $( A unionizing deduction.  (Contributed by Alan Sare, 28-Apr-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    un01 $p |- (. ph ->. ps ). $=
      ( wtru wa tru jctl dfvd2ani syl dfvd1ir ) ABADAEBADFGDABCHIJ $.
  $}

  ${
    un2122.1 $e |- ( ( ( ph /\ ps ) /\ ps /\ ps ) -> ch ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 3-Dec-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    un2122 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa w3a 3anass anandir ancom anabs7 bitri bitr3i sylbir ) ABEZNBBFZCONBB
      EEZNNBBGPNBEZNABBHQBNENNBIABJKLKDM $.
  $}

  ${
    uun2131.1 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> th ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uun2131 $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( 3impdi ) ABCDEF $.
  $}

  ${
    uun2131p1.1 $e |- ( ( ( ph /\ ch ) /\ ( ph /\ ps ) ) -> th ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uun2131p1 $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wa ancom sylbi 3impdi ) ABCDABFZACFZFKJFDJKGEHI $.
  $}

  ${
    uunTT1.1 $e |- ( ( T. /\ T. /\ ph ) -> ps ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uunTT1 $p |- ( ph -> ps ) $=
      ( wtru w3a wa 3anass anabs5 truan 3bitri sylbir ) ADDAEZBLDDAFZFMADDAGDAH
      AIJCK $.
  $}

  ${
    uunTT1p1.1 $e |- ( ( T. /\ ph /\ T. ) -> ps ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uunTT1p1 $p |- ( ph -> ps ) $=
      ( wtru w3a wa 3ancomb 3anass anabs5 3bitri truan bitri sylbir ) ADADEZBND
      AFZANDDAEDOFODADGDDAHDAIJAKLCM $.
  $}

  ${
    uunTT1p2.1 $e |- ( ( ph /\ T. /\ T. ) -> ps ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uunTT1p2 $p |- ( ph -> ps ) $=
      ( wtru w3a wa 3anrot 3anass anabs5 3bitri truan bitri sylbir ) AADDEZBNDA
      FZANDDAEDOFOADDGDDAHDAIJAKLCM $.
  $}

  ${
    uunT11.1 $e |- ( ( T. /\ ph /\ ph ) -> ps ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uunT11 $p |- ( ph -> ps ) $=
      ( wtru w3a wa 3anass truan anidm 3bitri sylbir ) ADAAEZBLDAAFZFMADAAGMHAI
      JCK $.
  $}

  ${
    uunT11p1.1 $e |- ( ( ph /\ T. /\ ph ) -> ps ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uunT11p1 $p |- ( ph -> ps ) $=
      ( wtru w3a wa 3anrot 3anass truan 3bitri anidm bitri sylbir ) AADAEZBNAAF
      ZANDAAEDOFOADAGDAAHOIJAKLCM $.
  $}

  ${
    uunT11p2.1 $e |- ( ( ph /\ ph /\ T. ) -> ps ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uunT11p2 $p |- ( ph -> ps ) $=
      ( wtru w3a wa 3anrev 3anass truan 3bitri anidm bitri sylbir ) AAADEZBNAAF
      ZANDAAEDOFOAADGDAAHOIJAKLCM $.
  $}

  ${
    uunT12.1 $e |- ( ( T. /\ ph /\ ps ) -> ch ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uunT12 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa wtru w3a 3anass truan bitri sylbir ) ABEZFABGZCMFLELFABHLIJDK $.
  $}

  ${
    uunT12p1.1 $e |- ( ( T. /\ ps /\ ph ) -> ch ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uunT12p1 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa wtru w3a 3anass truan bitri ancom bitr4i sylbir ) ABEZFBAGZCOBAEZNOF
      PEPFBAHPIJABKLDM $.
  $}

  ${
    uunT12p2.1 $e |- ( ( ph /\ T. /\ ps ) -> ch ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uunT12p2 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa wtru w3a 3anrot 3anass bitri truan ancom bitr4i sylbir ) ABEZAFBGZCP
      BAEZOPFQEZQPFBAGRAFBHFBAIJQKJABLMDN $.
  $}

  ${
    uunT12p3.1 $e |- ( ( ps /\ T. /\ ph ) -> ch ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uunT12p3 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa wtru w3a 3ancoma 3anass bitri truan ancom bitr4i sylbir ) ABEZBFAGZC
      PBAEZOPFQEZQPFBAGRBFAHFBAIJQKJABLMDN $.
  $}

  ${
    uunT12p4.1 $e |- ( ( ph /\ ps /\ T. ) -> ch ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uunT12p4 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa wtru w3a 3anrot 3anass bitr3i truan bitri sylbir ) ABEZABFGZCOFNEZNO
      FABGPFABHFABIJNKLDM $.
  $}

  ${
    uunT12p5.1 $e |- ( ( ps /\ ph /\ T. ) -> ch ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uunT12p5 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa wtru w3a 3anrev 3anass bitri truan sylbir ) ABEZBAFGZCNFMEZMNFABGOBA
      FHFABIJMKJDL $.
  $}

  ${
    uun111.1 $e |- ( ( ph /\ ph /\ ph ) -> ps ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uun111 $p |- ( ph -> ps ) $=
      ( w3a wa 3anass anabs5 anidm 3bitri sylbir ) AAAADZBKAAAEZELAAAAFAAGAHICJ
      $.
  $}

  ${
    3anidm12p1.1 $e |- ( ( ph /\ ps /\ ph ) -> ch ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       ~ 3anidm12 denotes the deduction which would have been named uun112 if
       it did not pre-exist in set.mm.  This second permutation's name is based
       on this pre-existing name.  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    3anidm12p1 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( 3anidm13 ) ABCDE $.
  $}

  ${
    3anidm12p2.1 $e |- ( ( ps /\ ph /\ ph ) -> ch ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    3anidm12p2 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( w3a 3anrot sylbir 3anidm12 ) ABCAABEBAAECBAAFDGH $.
  $}

  ${
    uun123.1 $e |- ( ( ph /\ ch /\ ps ) -> th ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uun123 $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( w3a 3ancomb sylbir ) ABCFACBFDACBGEH $.
  $}

  ${
    uun123p1.1 $e |- ( ( ps /\ ph /\ ch ) -> th ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uun123p1 $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( 3com12 ) BACDEF $.
  $}

  ${
    uun123p2.1 $e |- ( ( ch /\ ph /\ ps ) -> th ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uun123p2 $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( 3coml ) CABDEF $.
  $}

  ${
    uun123p3.1 $e |- ( ( ps /\ ch /\ ph ) -> th ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uun123p3 $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( 3comr ) BCADEF $.
  $}

  ${
    uun123p4.1 $e |- ( ( ch /\ ps /\ ph ) -> th ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uun123p4 $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( 3com13 ) CBADEF $.
  $}

  ${
    uun2221.1 $e |- ( ( ph /\ ph /\ ( ps /\ ph ) ) -> ch ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 30-Dec-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uun2221 $p |- ( ( ps /\ ph ) -> ch ) $=
      ( wa w3a wi 3anass anabs5 bitri ancom anbi2i bitr4i imbi1i mpbi ) AABAEZF
      ZCGPCGDQPCQAABEZEZPQAPEZSQATETAAPHAPIJRPAABKZLMSRPABIUAJJNO $.
  $}

  ${
    uun2221p1.1 $e |- ( ( ph /\ ( ps /\ ph ) /\ ph ) -> ch ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uun2221p1 $p |- ( ( ps /\ ph ) -> ch ) $=
      ( wa w3a 3anrot imbi1i mpbir 3anass anabs5 bitri ancom anbi2i bitr4i mpbi
      wi ) AABAEZFZCQZRCQTARAFZCQDSUACAARGHISRCSAABEZEZRSAREZUCSAUDEUDAARJARKLU
      BRAABMZNOUCUBRABKUELLHP $.
  $}

  ${
    uun2221p2.1 $e |- ( ( ( ps /\ ph ) /\ ph /\ ph ) -> ch ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    uun2221p2 $p |- ( ( ps /\ ph ) -> ch ) $=
      ( wa w3a 3anrev imbi1i mpbir 3anass anabs5 bitri ancom anbi2i bitr4i mpbi
      wi ) AABAEZFZCQZRCQTRAAFZCQDSUACAARGHISRCSAABEZEZRSAREZUCSAUDEUDAARJARKLU
      BRAABMZNOUCUBRABKUELLHP $.
  $}

  ${
    3impdirp1.1 $e |- ( ( ( ch /\ ps ) /\ ( ph /\ ps ) ) -> th ) $.
    $( A deduction unionizing a non-unionized collection of virtual hypotheses.
       Commuted version of ~ 3impdir .  (Contributed by Alan Sare, 4-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    3impdirp1 $p |- ( ( ph /\ ch /\ ps ) -> th ) $=
      ( wa ancom sylbir 3impdir ) ABCDABFZCBFZFKJFDKJGEHI $.
  $}

  ${
    3impcombi.1 $e |- ( ( ph /\ ps /\ ph ) -> ( ch <-> th ) ) $.
    $( A 1-hypothesis propositional calculus deduction.  (Contributed by Alan
       Sare, 25-Sep-2017.) $)
    3impcombi $p |- ( ( ps /\ ph /\ ch ) -> th ) $=
      ( wi w3a biimpd 3anidm13 ancoms 3impia ) BACDABCDFZABLABAGCDEHIJK $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Theorems proved using Virtual Deduction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x A $.
    $( Virtual deduction proof of the left-to-right implication of ~ dftr4 .  A
       transitive class is a subset of its power class.  This proof corresponds
       to the virtual deduction proof of ~ dftr4 without accumulating results.
       (Contributed by Alan Sare, 29-Apr-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    trsspwALT $p |- ( Tr A -> A C_ ~P A ) $=
      ( vx wtr cpw wss cv wcel wi wal wb df-ss idn1 idn2 trss e12 vex e2bir in2
      elpw gen11 biimpr e01 in1 ) ACZAADZEZUFBFZAGZUGUEGZHZBIZJUDUKUFBAUEKUDUJB
      UDUHUIUDUHUGAEZUIUDUDUHUHULUDLUDUHMAUGNOUGABPSQRTUFUKUAUBUC $.
  $}

  ${
    $d x A $.
    $( Virtual deduction proof of ~ trsspwALT .  This proof is the same as the
       proof of ~ trsspwALT except each virtual deduction symbol is replaced by
       its non-virtual deduction symbol equivalent.  A transitive class is a
       subset of its power class.  (Contributed by Alan Sare, 23-Jul-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    trsspwALT2 $p |- ( Tr A -> A C_ ~P A ) $=
      ( vx wtr cpw wss wi cv wcel wal df-ss idd trss sylsyld vex elpw imbitrrdi
      wb id idiALT alrimiv biimpr mpsyl ) ACZAADZEZFUEBGZAHZUFUDHZFZBIZQUCUJUEB
      AUDJUCUIBUCUIFUCUGUFAEZUHUCUCUGUGUKUCRUCUGKAUFLMUFABNOPSTUEUJUAUBS $.
  $}

  ${
    $d x A $.
    $( Short predicate calculus proof of the left-to-right implication of
       ~ dftr4 .  A transitive class is a subset of its power class.  This
       proof was constructed by applying Metamath's minimize command to the
       proof of ~ trsspwALT2 , which is the virtual deduction proof ~ trsspwALT
       without virtual deductions.  (Contributed by Alan Sare, 30-Apr-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    trsspwALT3 $p |- ( Tr A -> A C_ ~P A ) $=
      ( vx wtr cpw cv wcel wss trss vex elpw imbitrrdi ssrdv ) ACZBAADZMBEZAFOA
      GONFAOHOABIJKL $.
  $}

  ${
    $d z A $.  $d y A $.  $d z y $.
    $( Virtual deduction proof of the right-to-left implication of ~ dftr4 .  A
       class which is a subclass of its power class is transitive.  This proof
       corresponds to the virtual deduction proof of ~ sspwtr without
       accumulating results.  (Contributed by Alan Sare, 2-May-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sspwtr $p |- ( A C_ ~P A -> Tr A ) $=
      ( vz vy cpw wss wtr cv wcel wa wi wal wb dftr2 idn1 idn2 simpr ssel elpwi
      e2 e12 simpl e22 in2 gen12 biimpr e01 in1 ) AADZEZAFZUJBGZCGZHZULAHZIZUKA
      HZJZCKBKZLUIURUJBCAMUIUQBCUIUOUPUIUOULAEZUMUPUIUOULUHHZUSUIUIUOUNUTUINUIU
      OUOUNUIUOOZUMUNPSAUHULQTULARSUIUOUOUMVAUMUNUASULAUKQUBUCUDUJURUEUFUG $.
  $}

  ${
    $d z A $.  $d y A $.  $d z y $.
    $( Virtual deduction proof of ~ sspwtr .  This proof is the same as the
       proof of ~ sspwtr except each virtual deduction symbol is replaced by
       its non-virtual deduction symbol equivalent.  A class which is a
       subclass of its power class is transitive.  (Contributed by Alan Sare,
       3-May-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    sspwtrALT $p |- ( A C_ ~P A -> Tr A ) $=
      ( vz vy cpw wss wtr wi wel cv wcel wa wal wb dftr2 simpr ssel elpwi syl56
      idd simpl syl6 syl6c alrimivv biimpr mpsyl idiALT ) AADZEZAFZGUIBCHZCIZAJ
      ZKZBIZAJZGZCLBLZMUHUQUIBCANUHUPBCUHUMUKAEZUJUOUMULUHUKUGJURUJULOAUGUKPUKA
      QRUHUMUMUJUHUMSUJULTUAUKAUNPUBUCUIUQUDUEUF $.
  $}

  ${
    $d z A $.  $d y A $.  $d z y $.
    $( Short predicate calculus proof of the right-to-left implication of
       ~ dftr4 .  A class which is a subclass of its power class is transitive.
       This proof was constructed by applying Metamath's minimize command to
       the proof of ~ sspwtrALT , which is the virtual deduction proof ~ sspwtr
       without virtual deductions.  (Contributed by Alan Sare, 3-May-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sspwtrALT2 $p |- ( A C_ ~P A -> Tr A ) $=
      ( vz vy cpw wss cv wcel wa wi wal wtr ssel adantld elpwi syl6 simpl syl6c
      a1i alrimivv dftr2 sylibr ) AADZEZBFZCFZGZUEAGZHZUDAGZIZCJBJAKUCUJBCUCUHU
      EAEZUFUIUCUHUEUBGZUKUCUGULUFAUBUELMUEANOUHUFIUCUFUGPRUEAUDLQSBCATUA $.
  $}

  ${
    $d z A $.  $d y A $.  $d z y $.
    $( Virtual deduction proof of ~ pwtr ; see ~ pwtrrVD for the converse.
       (Contributed by Alan Sare, 25-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    pwtrVD $p |- ( Tr A -> Tr ~P A ) $=
      ( vz vy wtr cpw cv wcel wa wi wal wb dftr2 idn1 idn2 simpr e2 elpwi simpl
      wss ssel e22 trss e12 vex elpw e2bir in2 gen12 biimpr e01 in1 ) ADZAEZDZU
      NBFZCFZGZUPUMGZHZUOUMGZIZCJBJZKULVBUNBCUMLULVABCULUSUTULUSUOASZUTULULUSUO
      AGZVCULMULUSUPASZUQVDULUSURVEULUSUSURULUSNZUQUROPUPAQPULUSUSUQVFUQURRPUPA
      UOTUAAUOUBUCUOABUDUEUFUGUHUNVBUIUJUK $.
  $}

  ${
    $d z A $.  $d y A $.  $d z y $.
    pwtrrVD.1 $e |- A e. _V $.
    $( Virtual deduction proof of ~ pwtr ; see ~ pwtrVD for the converse.
       (Contributed by Alan Sare, 25-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    pwtrrVD $p |- ( Tr ~P A -> Tr A ) $=
      ( vz vy cpw wtr cv wcel wa wi wal wb dftr2 wss idn1 idn2 simpr pwid trel
      e2 expd e120 elpwi simpl ssel e22 in2 gen12 biimpr e01 in1 ) AEZFZAFZUNCG
      ZDGZHZUPAHZIZUOAHZJZDKCKZLUMVBUNCDAMUMVACDUMUSUTUMUSUPANZUQUTUMUSUPULHZVC
      UMUMUSURAULHZVDUMOUMUSUSURUMUSPZUQURQTABRUMURVEVDULUPASUAUBUPAUCTUMUSUSUQ
      VFUQURUDTUPAUOUEUFUGUHUNVBUIUJUK $.
  $}

  ${
    $d y z A $.
    $( The successor of a transitive class is transitive.  The proof of
       ~ https://us.metamath.org/other/completeusersproof/suctrvd.html is a
       Virtual Deduction proof verified by automatically transforming it into
       the Metamath proof of ~ suctrALT using completeusersproof, which is
       verified by the Metamath program.  The proof of
       ~ https://us.metamath.org/other/completeusersproof/suctrro.html is a
       form of the completed proof which preserves the Virtual Deduction
       proof's step numbers and their ordering.  See ~ suctr for the original
       proof.  (Contributed by Alan Sare, 11-Apr-2009.)  (Revised by Alan Sare,
       12-Jun-2018.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    suctrALT $p |- ( Tr A -> Tr suc A ) $=
      ( vz vy wtr cv wcel csuc wa wi wal wceq w3a sssucid id simpld trel sselid
      adantl ex syl 3impib idiALT syl3an 3expia adantr eleqtrd wo simprd elsuci
      mpjaod alrimivv dftr2 biimpri ) ADZBEZCEZFZUPAGZFZHZUOURFZIZCJBJZURDZUNVB
      BCUNUTVAUNUTHUPAFZVAUPAKZUNUTVEVAUNUTVELAURUOAMZUNUNUTUQVEVEUOAFZUNNUTUQU
      SUTNZOZVENUNUQVELVHIUNUQVEVHAUOUPPUAUBUCQUDUTVFVAIUNUTVFVAUTVFHZAURUOVGVK
      UOUPAUTUQVFVJUEVFVFUTVFNRUFQSRUTVEVFUGZUNUTUSVLUTUQUSVIUHUPAUITRUJSUKVDVC
      BCURULUMT $.
  $}

  ${
    $d A x $.  $d B x $.
    $( Virtual deduction proof of ~ snssiALT .  (Contributed by Alan Sare,
       11-Sep-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    snssiALTVD $p |- ( A e. B -> { A } C_ B ) $=
      ( vx wcel csn wss cv wi wal wb df-ss wceq idn1 idn2 velsn e2bi eleq1a e12
      in2 gen11 biimpr e01 in1 ) ABDZAEZBFZUFCGZUEDZUGBDZHZCIZJUDUKUFCUEBKUDUJC
      UDUHUIUDUDUHUGALZUIUDMUDUHUHULUDUHNCAOPABUGQRSTUFUKUAUBUC $.
  $}

  ${
    $d A x $.  $d B x $.
    $( If a class is an element of another class, then its singleton is a
       subclass of that other class.  Alternate proof of ~ snssi .  This
       theorem was automatically generated from ~ snssiALTVD using a
       translation program.  (Contributed by Alan Sare, 11-Sep-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    snssiALT $p |- ( A e. B -> { A } C_ B ) $=
      ( vx wcel cv csn wal wss wceq velsn eleq1a biimtrid alrimiv df-ss sylibr
      wi ) ABDZCEZAFZDZRBDZPZCGSBHQUBCTRAIQUACAJABRKLMCSBNO $.
  $}

  ${
    snsslVD.1 $e |- A e. _V $.
    $( Virtual deduction proof of ~ snssl .  (Contributed by Alan Sare,
       25-Aug-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    snsslVD $p |- ( { A } C_ B -> A e. B ) $=
      ( csn wss wcel idn1 snid ssel2 e10an in1 ) ADZBEZABFZMMALFNMGACHLBAIJK $.
  $}

  ${
    snssl.1 $e |- A e. _V $.
    $( If a singleton is a subclass of another class, then the singleton's
       element is an element of that other class.  This theorem is the
       right-to-left implication of the biconditional ~ snss .  The proof of
       this theorem was automatically generated from ~ snsslVD using a tools
       command file, translateMWO.cmd, by translating the proof into its
       non-virtual deduction form and minimizing it.  (Contributed by Alan
       Sare, 25-Aug-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    snssl $p |- ( { A } C_ B -> A e. B ) $=
      ( csn wss wcel snid ssel2 mpan2 ) ADZBEAJFABFACGJBAHI $.
  $}

  $( Virtual deduction proof of ~ snelpwi .  (Contributed by Alan Sare,
     25-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  snelpwrVD $p |- ( A e. B -> { A } e. ~P B ) $=
    ( wcel csn cpw cvv wss snex idn1 snssi e1a elpwg biimprd e01 in1 ) ABCZADZB
    ECZQFCZPQBGZRAHPPTPIABJKSRTQBFLMNO $.

  ${
    $d A x $.
    $( Virtual deduction proof of ~ unipwr .  (Contributed by Alan Sare,
       25-Aug-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    unipwrVD $p |- A C_ U. ~P A $=
      ( vx cpw cuni wcel csn vex snid idn1 snelpwi e1a elunii e01an in1 ssriv
      cv ) BAACZDZBPZAEZSREZSSFZETUBQEZUASBGHTTUCTISAJKSUBQLMNO $.
  $}

  ${
    $d A x $.
    $( A class is a subclass of the union of its power class.  This theorem is
       the right-to-left subclass lemma of ~ unipw .  The proof of this theorem
       was automatically generated from ~ unipwrVD using a tools command file ,
       translateMWO.cmd , by translating the proof into its non-virtual
       deduction form and minimizing it.  (Contributed by Alan Sare,
       25-Aug-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    unipwr $p |- A C_ U. ~P A $=
      ( vx cpw cuni cv wcel csn vex snid snelpwi elunii sylancr ssriv ) BAACZDZ
      BEZAFPPGZFQNFPOFPBHIPAJPQNKLM $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Virtual deduction proof of ~ sstrALT2 .  (Contributed by Alan Sare,
       11-Sep-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    sstrALT2VD $p |- ( ( A C_ B /\ B C_ C ) -> A C_ C ) $=
      ( vx wss wa cv wcel wi wal wb df-ss idn1 simpr e1a simpl idn2 ssel2 e12an
      in2 gen11 biimpr e01 in1 ) ABEZBCEZFZACEZUHDGZAHZUICHZIZDJZKUGUMUHDACLUGU
      LDUGUJUKUGUFUJUIBHZUKUGUGUFUGMZUEUFNOUGUEUJUJUNUGUGUEUOUEUFPOUGUJQABUIRSB
      CUIRSTUAUHUMUBUCUD $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Virtual deduction proof of ~ sstr , transitivity of subclasses, Theorem
       6 of [Suppes] p. 23.  This theorem was automatically generated from
       ~ sstrALT2VD using the command file
       translate__without__overwriting.cmd .  It was not minimized because the
       automated minimization excluding duplicates generates a minimized proof
       which, although not directly containing any duplicates, indirectly
       contains a duplicate.  That is, the trace back of the minimized proof
       contains a duplicate.  This is undesirable because some step(s) of the
       minimized proof use the proven theorem.  (Contributed by Alan Sare,
       11-Sep-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    sstrALT2 $p |- ( ( A C_ B /\ B C_ C ) -> A C_ C ) $=
      ( vx wss cv wi wal wb wa df-ss id simpr syl simpl idd ssel2 syl6an idiALT
      wcel alrimiv biimpr mpsyl ) ACEZDFZATZUECTZGZDHZIABEZBCEZJZUIUDDACKULUHDU
      LUHGULUKUFUEBTZUGULULUKULLZUJUKMNULUJUFUFUMULULUJUNUJUKONULUFPABUEQRBCUEQ
      RSUAUDUIUBUC $.
  $}

  ${
    $d z A $.  $d y A $.  $d z y $.
    $( Virtual deduction proof of ~ suctrALT2 .  (Contributed by Alan Sare,
       11-Sep-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    suctrALT2VD $p |- ( Tr A -> Tr suc A ) $=
      ( vz vy wtr csuc cv wcel wa wi wal wb dftr2 wceq wss sssucid idn3 e03 in3
      wo e2 idn1 idn2 simpl trel expd e123 ssel eleq2 biimpcd simpr elsuci e222
      e23 jao in2 gen12 biimpr e01 in1 ) ADZAEZDZVBBFZCFZGZVDVAGZHZVCVAGZIZCJBJ
      ZKUTVJVBBCVALUTVIBCUTVGVHUTVGVDAGZVHIVDAMZVHIVKVLSZVHUTVGVKVHAVANZUTVGVKV
      CAGZVHAOZUTUTVGVEVKVKVOUTUAUTVGVGVEUTVGUBZVEVFUCTZUTVGVKPUTVEVKVOAVCVDUDU
      EUFAVAVCUGZQRUTVGVLVHVNUTVGVLVOVHVPUTVGVEVLVLVOVRUTVGVLPVLVEVOVDAVCUHUIUM
      VSQRUTVGVFVMUTVGVGVFVQVEVFUJTVDAUKTVKVHVLUNULUOUPVBVJUQURUS $.
  $}

  ${
    $d z A $.  $d y A $.  $d z y $.
    $( Virtual deduction proof of ~ suctr .  The successor of a transitive
       class is transitive.  This proof was generated automatically from the
       virtual deduction proof ~ suctrALT2VD using the tools command file
       translate__without__overwriting__minimize__excluding__duplicates.cmd .
       (Contributed by Alan Sare, 11-Sep-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    suctrALT2 $p |- ( Tr A -> Tr suc A ) $=
      ( vz vy wtr wel cv csuc wcel wa wi wal wceq wo wss sssucid trel expd ee03
      a1i syl6 adantrd ssel simpl eleq2 biimpcd simpr elsuci jao ee222 alrimivv
      dftr2 sylibr ) ADZBCEZCFZAGZHZIZBFZUPHZJZCKBKUPDUMVABCUMURUOAHZUTJUOALZUT
      JVBVCMZUTAUPNZUMURVBUSAHZUTAOZUMUNVBVFJUQUMUNVBVFAUSUOPQUAAUPUSUBZRVEUMUR
      VCVFUTVGUMURUNVCVFJURUNJUMUNUQUCSVCUNVFUOAUSUDUETVHRUMURUQVDURUQJUMUNUQUF
      SUOAUGTVBUTVCUHUIUJBCUPUKUL $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Virtual deduction proof of ~ elex2 .  (Contributed by Alan Sare,
       25-Sep-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    elex2VD $p |- ( A e. B -> E. x x e. B ) $=
      ( wcel cv wex wceq wi wal idn1 idn2 eleq1a e12 in2 gen11 elisset e1a exim
      e11 in1 ) BCDZAEZCDZAFZUAUBBGZUCHZAIUEAFZUDUAUFAUAUEUCUAUAUEUEUCUAJZUAUEK
      BCUBLMNOUAUAUGUHABCPQUEUCARST $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Virtual deduction proof of ~ elex22 .  (Contributed by Alan Sare,
       24-Oct-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    elex22VD $p |- ( ( A e. B /\ A e. C ) -> E. x ( x e. B /\ x e. C ) ) $=
      ( wcel wa cv wex wceq wi idn1 simpl e1a elisset wal idn2 eleq1a e12 simpr
      pm3.2 e22 in2 gen11 exim pm2.27 e11 in1 ) BCEZBDEZFZAGZCEZUKDEZFZAHZUJUKB
      IZAHZUQUOJZUOUJUHUQUJUJUHUJKZUHUILMZABCNMUJUPUNJZAOURUJVAAUJUPUNUJUPULUMU
      NUJUHUPUPULUTUJUPPZBCUKQRUJUIUPUPUMUJUJUIUSUHUISMVBBDUKQRULUMTUAUBUCUPUNA
      UDMUQUOUEUFUG $.
  $}

  ${
    $d x C $.
    $( Virtual deduction proof of ~ eqsbc2 .  (Contributed by Alan Sare,
       24-Oct-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eqsbc2VD $p |- ( A e. B -> ( [. A / x ]. C = x <-> C = A ) ) $=
      ( wcel cv wceq wsbc wb wi idn1 eqsbc1 e1a eqcom sbcbii idn2 biimp e12 in2
      biimpr a1i e2bi e2bir impbi e11 in1 ) BCEZDAFZGZABHZDBGZIZUGUJUKJUKUJJULU
      GUJUKUGUJBDGZUKUGUHDGZABHZUMIZUJUOUMUGUGUPUGKZABDCLMZUGUJUOIZUJUJUOUGUGUS
      UQUSUGUIUNABDUHNOUAMZUGUJPUJUOQRUOUMQRBDNZUBSUGUKUJUGUSUKUOUJUTUGUPUKUMUO
      URUGUKUKUMUGUKPVAUCUOUMTRUJUOTRSUJUKUDUEUF $.
  $}

  ${
    $d x y A $.
    $( Virtual deduction proof of ~ zfregs2 .  (Contributed by Alan Sare,
       24-Oct-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    zfregs2VD $p |- ( A =/= (/) -> -. A. x e. A E. y ( y e. A /\ y e. x ) ) $=
      ( c0 wne cv wcel wa wex wral wn wrex wal cin wceq idn1 zfregs rexbii e1bi
      wi e1a incom eqeq1i disj1 alinexa dfrex2 notnotr notnot impbii ralbii in1
      notbii ) CDEZBFZCGZUNAFZGZHBIZACJZKZUMURKZKZACJZKZUTUMVAACLZVDUMUOUQKTBMZ
      ACLZVEUMCUPNZDOZACLZVGUMUPCNZDOZACLZVJUMUMVMUMPACQUAVLVIACVKVHDUPCUBUCRSV
      IVFACBCUPUDRSVFVAACUOUQBUERSVAACUFSVCUSVBURACVBURURUGURUHUIUJULSUK $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x D $.
    $( Virtual deduction proof of ~ tpid3g .  (Contributed by Alan Sare,
       24-Oct-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    tpid3gVD $p |- ( A e. B -> A e. { C , D , A } ) $=
      ( vx wcel ctp cv wceq wex wi wal idn2 w3o cab 3mix3 e2 abid e2bir dftp2
      eleq2i eleq1 biimpd e22 in2 gen11 19.23v e1bi idn1 elisset e1a id e11 in1
      ) ABFZACDAGZFZUOEHZAIZEJZUQKZUTUQUOUSUQKZELVAUOVBEUOUSUQUOUSUSURUPFZUQUOU
      SMZUOUSURURCIZURDIZUSNZEOZFZVCUOUSVGVIUOUSUSVGVDUSVEVFPQVGERSUPVHURECDATU
      ASUSVCUQURAUPUBUCUDUEUFUSUQEUGUHUOUOUTUOUIEABUJUKVAULUMUN $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.
    $( Virtual deduction proof of ~ en3lplem1 .  (Contributed by Alan Sare,
       24-Oct-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    en3lplem1VD $p |- ( ( A e. B /\ B e. C /\ C e. A ) ->
                    ( x = A -> E. y ( y e. { A , B , C } /\ y e. x ) ) ) $=
      ( wcel w3a cv wceq ctp wa wex wi idn1 simp3 e1a tpid3g idn2 eleq2 biimprd
      e21 pm3.2 e12 elex22 e2 in2 in1 ) CDFZDEFZECFZGZAHZCIZBHZCDEJZFUNULFKBLZM
      UKUMUPUKUMEUOFZEULFZKZUPUKUQUMURUSUKUJUQUKUKUJUKNUHUIUJOPZECCDQPUKUMUMUJU
      RUKUMRUTUMURUJULCESTUAUQURUBUCBEUOULUDUEUFUG $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.
    $( Virtual deduction proof of ~ en3lplem2 .  (Contributed by Alan Sare,
       24-Oct-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    en3lplem2VD $p |- ( ( A e. B /\ B e. C /\ C e. A ) -> ( x e. { A , B , C }
                    -> E. y ( y e. { A , B , C } /\ y e. x ) ) ) $=
      ( wcel w3a cv ctp wa wex wi wceq wo idn3 en3lplem1VD e13 in3 eleq2i e2bi
      idn1 3anrot e1bi tprot anbi1i exbii e3bir jao e22 e1bir e3bi w3o cab idn2
      dftp2 abid df-3or e222 in2 in1 ) CDFZDEFZECFZGZAHZCDEIZFZBHZVFFZVHVEFZJZB
      KZLVDVGVLVDVGVECMZVEDMZNZVLLZVEEMZVLLVOVQNZVLVDVGVMVLLVNVLLVPVDVGVMVLVDVD
      VGVMVMVLVDUAZVDVGVMOABCDEPQRVDVGVNVLVDVGVNVHDECIZFZVJJZBKZVLVDVBVCVAGZVGV
      NVNWCVDVDWDVSVAVBVCUBUCVDVGVNOABDECPQVKWBBVIWAVJVFVTVHCDEUDSUEUFUGRVMVLVN
      UHUIVDVGVQVLVDVGVQVHECDIZFZVJJZBKZVLVDVCVAVBGZVGVQVQWHVDVDWIVSVCVAVBUBUJV
      DVGVQOABECDPQWGVKBWFVIVJWEVFVHECDUDSUEUFUKRVDVGVMVNVQULZVRVDVGVEWJAUMZFZW
      JVDVGVGWLVDVGUNVFWKVEACDEUOSTWJAUPTVMVNVQUQTVOVLVQUHURUSUT $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.
    $( Virtual deduction proof of ~ en3lp .  (Contributed by Alan Sare,
       24-Oct-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    en3lpVD $p |- -. ( A e. B /\ B e. C /\ C e. A ) $=
      ( vy vx ctp c0 wne wceq wo wcel w3a wn pm2.1 df-ne bicomi orbi1i cv con3i
      e1a mpbi wa wex wral zfregs2 wi wal en3lplem2VD alrimiv df-ral sylibr syl
      idn1 noel eleq2 notbid biimprd e10 tpid3g simp3 in1 jaoi ax-mp ) ABCFZGHZ
      VDGIZJZABKZBCKZCAKZLZMZVFMZVFJVGVFNVMVEVFVEVMVDGOPQUAVEVLVFVEDRZVDKVNERZK
      UBDUCZEVDUDZMVLEDVDUEVKVQVKVOVDKVPUFZEUGVQVKVREEDABCUHUIVPEVDUJUKSULVFVLV
      FVJMZVLVFCVDKZMZVSVFVFCGKZMZWAVFUMCUNVFWAWCVFVTWBVDGCUOUPUQURVJVTCAABUSST
      VKVJVHVIVJUTSTVAVBVC $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Theorems proved using Virtual Deduction with mmj2 assistance
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    pm3.26bi2VD.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Virtual deduction proof of ~ simplbi2 .  The following user's proof is
       completed by invoking mmj2's unify command and using mmj2's StepSelector
       to pick all remaining steps of the Metamath proof.
       <HTML> <TABLE>
       <TR> <TD> h1::        <TD> ` |- ( ph <-> ( ps /\ ch ) ) `
       <TR> <TD> 3:1,?: ~ e0a   <TD> ` |- ( ( ps /\ ch ) -> ph )  `
       <TR> <TD> qed:3,?: ~ e0a <TD> ` |- ( ps -> ( ch -> ph ) ) `
       </TABLE> </HTML>
       The proof of ~ simplbi2 was automatically derived from it.
       (Contributed by Alan Sare, 31-Dec-2011.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    simplbi2VD $p |- ( ps -> ( ch -> ph ) ) $=
      ( wa wi wb biimpr e0a pm3.3 ) BCEZAFZBCAFFAKGLDAKHIBCAJI $.
  $}

  $( Virtual deduction proof of ~ 3ornot23 .  The following user's proof is
     completed by invoking mmj2's unify command and using mmj2's StepSelector
     to pick all remaining steps of the Metamath proof.
     <HTML> <TABLE>
     <TR> <TD> 1::            <TD> ` |- (. ( -. ph /\ -. ps ) ->. ( -. ph `
     ` /\ -. ps ) ). `
     <TR> <TD> 2::            <TD> ` |- (. ( -. ph /\ -. ps ) ,. ( ch \/ ph `
     ` \/ ps ) ->. ( ch \/ ph \/ ps ) ). `
     <TR> <TD> 3:1,?: ~ e1a    <TD> ` |- (. ( -. ph /\ -. ps ) ->. -. ph ). `
     <TR> <TD> 4:1,?: ~ e1a    <TD> ` |- (. ( -. ph /\ -. ps ) ->. -. ps ). `
     <TR> <TD> 5:3,4,?: ~ e11  <TD> ` |- (. ( -. ph /\ -. ps ) ->. -. ( ph `
     ` \/ ps ) ). `
     <TR> <TD> 6:2,?: ~ e2     <TD> ` |- (. ( -. ph /\ -. ps ) ,. ( ch \/ ph `
     ` \/ ps ) ->. ( ch \/ ( ph \/ ps ) ) ).  `
     <TR> <TD> 7:5,6,?: ~ e12  <TD> ` |- (. ( -. ph /\ -. ps ) ,. ( ch \/ ph `
     ` \/ ps ) ->. ch ). `
     <TR> <TD> 8:7:           <TD> ` |- (. ( -. ph /\ -. ps ) ->. ( ( ch `
     ` \/ ph \/ ps ) -> ch ) ). `
     <TR> <TD> qed:8:         <TD> ` |- ( ( -. ph /\ -. ps ) -> ( ( ch `
     ` \/ ph \/ ps ) -> ch ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 31-Dec-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  3ornot23VD $p |- ( ( -. ph /\ -. ps ) -> ( ( ch \/ ph \/ ps ) -> ch ) ) $=
    ( wn wa w3o wi wo idn1 simpl e1a simpr ioran simplbi2 idn2 3orass biimpi e2
    e11 orel2 e12 in2 in1 ) ADZBDZEZCABFZCGUFUGCUFABHZDZUGCUHHZCUFUDUEUIUFUFUDU
    FIZUDUEJKUFUFUEUKUDUELKUIUDUEABMNSUFUGUGUJUFUGOUGUJCABPQRUHCTUAUBUC $.

  $( Virtual deduction proof of ~ orbi1r .  The following user's proof is
     completed by invoking mmj2's unify command and using mmj2's StepSelector
     to pick all remaining steps of the Metamath proof.
     <HTML> <TABLE>
     <TR> <TD> 1::         <TD> ` |- (. ( ph <-> ps ) ->. ( ph <-> ps ) ). `
     <TR> <TD> 2::         <TD> ` |- (. ( ph <-> ps ) ,. ( ch \/ ph ) `
     ` ->. ( ch \/ ph ) ). `
     <TR> <TD> 3:2,?: ~ e2    <TD> ` |- (. ( ph <-> ps ) ,. ( ch \/ ph ) `
     ` ->. ( ph \/ ch ) ). `
     <TR> <TD> 4:1,3,?: ~ e12 <TD> ` |- (. ( ph <-> ps ) ,. ( ch \/ ph ) `
     ` ->. ( ps \/ ch ) ). `
     <TR> <TD> 5:4,?: ~ e2    <TD> ` |- (. ( ph <-> ps ) ,. ( ch \/ ph ) `
     ` ->. ( ch \/ ps ) ). `
     <TR> <TD> 6:5:        <TD> ` |- (. ( ph <-> ps ) ->. ( ( ch \/ ph ) `
     ` -> ( ch \/ ps ) ) ). `
     <TR> <TD> 7::         <TD> ` |- (. ( ph <-> ps ) ,. ( ch \/ ps ) `
     ` ->. ( ch \/ ps ) ). `
     <TR> <TD> 8:7,?: ~ e2    <TD> ` |- (. ( ph <-> ps ) ,. ( ch \/ ps ) `
     ` ->. ( ps \/ ch ) ). `
     <TR> <TD> 9:1,8,?: ~ e12 <TD> ` |- (. ( ph <-> ps ) ,. ( ch \/ ps ) `
     ` ->. ( ph \/ ch ) ). `
     <TR> <TD> 10:9,?: ~ e2   <TD> ` |- (. ( ph <-> ps ) ,. ( ch \/ ps ) `
     ` ->. ( ch \/ ph ) ). `
     <TR> <TD> 11:10:      <TD> ` |- (. ( ph <-> ps ) ->. ( ( ch \/ ps ) `
     ` -> ( ch \/ ph ) ) ). `
     <TR> <TD> 12:6,11,?: ~ e11 <TD> ` |- (. ( ph <-> ps ) ->. ( ( ch `
     ` \/ ph ) <-> ( ch \/ ps ) ) ). `
     <TR> <TD> qed:12:     <TD> ` |- ( ( ph <-> ps ) -> ( ( ch \/ ph ) `
     ` <-> ( ch \/ ps ) ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 31-Dec-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  orbi1rVD $p |- ( ( ph <-> ps ) -> ( ( ch \/ ph ) <-> ( ch \/ ps ) ) ) $=
    ( wb wo wi idn1 idn2 pm1.4 e2 orbi1 biimpd e12 in2 biimprd impbi e11 in1 )
    ABDZCAEZCBEZDZSTUAFUATFUBSTUASTBCEZUASSTACEZUCSGZSTTUDSTHCAIJSUDUCABCKZLMBC
    IJNSUATSUAUDTSSUAUCUDUESUAUAUCSUAHCBIJSUDUCUFOMACIJNTUAPQR $.

  $( Virtual deduction proof of ~ bitr3 .  The following user's proof is
     completed by invoking mmj2's unify command and using mmj2's StepSelector
     to pick all remaining steps of the Metamath proof.
     <HTML> <TABLE>
     <TR> <TD> 1::           <TD> ` |- (. ( ph <-> ps ) ->. ( ph `
     ` <-> ps ) ). `
     <TR> <TD> 2:1,?: ~ e1a     <TD> ` |- (. ( ph <-> ps ) ->. ( ps `
     ` <-> ph ) ). `
     <TR> <TD> 3::           <TD> ` |- (. ( ph <-> ps ) ,. ( ph <-> ch ) `
     ` ->. ( ph <-> ch ) ). `
     <TR> <TD> 4:3,?: ~ e2      <TD> ` |- (. ( ph <-> ps ) ,. ( ph <-> ch ) `
     ` ->. ( ch <-> ph ) ). `
     <TR> <TD> 5:2,4,?: ~ e12   <TD> ` |- (. ( ph <-> ps ) ,. ( ph <-> ch ) `
     ` ->. ( ps <-> ch ) ). `
     <TR> <TD> 6:5:          <TD> ` |- (. ( ph <-> ps ) ->. ( ( ph `
     ` <-> ch ) -> ( ps <-> ch ) ) ). `
     <TR> <TD> qed:6:        <TD> ` |- ( ( ph <-> ps ) -> ( ( ph <-> ch ) `
     ` -> ( ps <-> ch ) ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 31-Dec-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  bitr3VD $p |- ( ( ph <-> ps ) -> ( ( ph <-> ch ) -> ( ps <-> ch ) ) ) $=
    ( wb id bicomd biantr ex syl2im ) ABDZBADZACDZCADZBCDZJABJEFLACLEFKMNBACGHI
    $.

  $( Virtual deduction proof of ~ 3orbi123 .  The following user's proof is
     completed by invoking mmj2's unify command and using mmj2's StepSelector
     to pick all remaining steps of the Metamath proof.
     <HTML> <TABLE>
     <TR> <TD> 1::         <TD> ` |- (. ( ( ph <-> ps ) /\ ( ch <-> th ) `
     ` /\ ( ta <-> et ) )  ->. ( ( ph <-> ps ) /\ ( ch <-> th ) /\ `
     ` ( ta <-> et ) ) ). `
     <TR> <TD> 2:1,?: ~ e1a   <TD> ` |- (. ( ( ph <-> ps ) /\ ( ch <-> th ) `
     ` /\ ( ta <-> et ) ) ->. ( ph <-> ps ) ). `
     <TR> <TD> 3:1,?: ~ e1a   <TD> ` |- (. ( ( ph <-> ps ) /\ ( ch <-> th ) `
     ` /\ ( ta <-> et ) ) ->. ( ch <-> th ) ). `
     <TR> <TD> 4:1,?: ~ e1a   <TD> ` |- (. ( ( ph <-> ps ) /\ ( ch <-> th ) `
     ` /\ ( ta <-> et ) ) ->. ( ta <-> et ) ). `
     <TR> <TD> 5:2,3,?: ~ e11 <TD> ` |- (. ( ( ph <-> ps ) /\ ( ch <-> th ) `
     ` /\ ( ta <-> et ) ) ->. ( ( ph \/ ch ) <-> ( ps \/ th ) ) ). `
     <TR> <TD> 6:5,4,?: ~ e11 <TD> ` |- (. ( ( ph <-> ps ) /\ ( ch <-> th ) `
     ` /\ ( ta <-> et ) ) ->. ( ( ( ph \/ ch ) \/ ta )  <-> ( ( ps \/ th ) `
     ` \/ et ) ) ). `
     <TR> <TD> 7:?:        <TD> ` |- ( ( ( ph \/ ch ) \/ ta ) <-> ( ph `
     ` \/ ch \/ ta ) ) `
     <TR> <TD> 8:6,7,?: ~ e10 <TD> ` |- (. ( ( ph <-> ps ) /\ ( ch <-> th ) `
     ` /\ ( ta <-> et ) ) ->. ( ( ph \/ ch \/ ta )  <-> ( ( ps \/ th ) `
     ` \/ et ) ) ). `
     <TR> <TD> 9:?:        <TD> ` |- ( ( ( ps \/ th ) \/ et ) <-> `
     ` ( ps \/ th \/ et ) ) `
     <TR> <TD> 10:8,9,?: ~ e10 <TD> ` |- (. ( ( ph <-> ps ) /\ ( ch `
     ` <-> th ) /\ ( ta <-> et ) ) ->. ( ( ph \/ ch \/ ta ) <-> ( ps \/ `
     ` th \/ et ) ) ). `
     <TR> <TD> qed:10:       <TD> ` |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) `
     ` /\ ( ta <-> et ) ) -> ( ( ph \/ ch \/ ta ) <-> ( ps \/ th `
     ` \/ et ) ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 31-Dec-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  3orbi123VD $p |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) /\ ( ta <-> et ) ) ->
                             ( ( ph \/ ch \/ ta ) <-> ( ps \/ th \/ et ) ) ) $=
    ( wb w3a w3o wo idn1 simp1 e1a simp2 pm4.39 ex e11 df-3or bicomi e10 simp3
    bitr3 com12 bitr in1 ) ABGZCDGZEFGZHZACEIZBDFIZGZUIUJBDJZFJZGZUNUKGZULUIACJ
    ZEJZUNGZURUJGZUOUIUQUMGZUHUSUIUFUGVAUIUIUFUIKZUFUGUHLMUIUIUGVBUFUGUHNMUFUGV
    AACBDOPQUIUIUHVBUFUGUHUAMVAUHUSUQEUMFOPQUJURACERSUTUSUOURUJUNUBUCTUKUNBDFRS
    UOUPULUJUNUKUDPTUE $.

  $( Virtual deduction proof of the analogue of ~ sbcor with three disjuncts.
     The following user's proof is
     completed by invoking mmj2's unify command and using mmj2's StepSelector
     to pick all remaining steps of the Metamath proof.
     <HTML> <TABLE>
     <TR> <TD> 1::           <TD> ` |- (. A e. B ->. A e. B ). `
     <TR> <TD> 2:1,?: ~ e1a     <TD> ` |- (. A e. B ->. ( [. A / x ]. ( ( ph `
     ` \/ ps ) \/ ch ) <-> ( [. A / x ]. ( ph \/ ps ) `
     ` \/ [. A / x ]. ch ) ) ). `
     <TR> <TD> 3::           <TD> ` |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ph `
     ` \/ ps \/ ch ) ) `
     <TR> <TD> 32:3:         <TD> ` |- A. x ( ( ( ph \/ ps ) \/ ch ) `
     ` <-> ( ph \/ ps \/ ch ) ) `
     <TR> <TD> 33:1,32,?: ~ e10 <TD> ` |- (. A e. B ->. [. A / x ]. ( ( ( ph `
     ` \/ ps ) \/ ch ) <-> ( ph \/ ps \/ ch ) ) ). `
     <TR> <TD> 4:1,33,?: ~ e11  <TD> ` |- (. A e. B ->. ( [. A / x ]. ( ( ph `
     ` \/ ps ) \/ ch ) <-> [. A / x ]. ( ph \/ ps \/ ch ) ) ). `
     <TR> <TD> 5:2,4,?: ~ e11   <TD> ` |- (. A e. B ->. ( [. A / x ]. ( ph `
     ` \/ ps \/ ch ) <-> ( [. A / x ]. ( ph \/ ps ) \/ [. A / x ]. ch ) ) ). `
     <TR> <TD> 6:1,?: ~ e1a     <TD> ` |- (. A e. B ->. ( [. A / x ]. ( ph `
     ` \/ ps ) <-> ( [. A / x ]. ph \/ [. A / x ]. ps ) ) ). `
     <TR> <TD> 7:6,?: ~ e1a     <TD> ` |- (. A e. B ->. ( ( [. A / x ]. ( ph `
     ` \/ ps ) \/ [. A / x ]. ch ) <-> ( ( [. A / x ]. ph \/ [. A / x ]. ps ) `
     ` \/ [. A / x ]. ch ) ) ). `
     <TR> <TD> 8:5,7,?: ~ e11   <TD> ` |- (. A e. B ->. ( [. A / x ]. ( ph `
     ` \/ ps \/ ch ) <-> ( ( [. A / x ]. ph \/ [. A / x ]. ps ) `
     ` \/ [. A / x ]. ch ) ) ). `
     <TR> <TD> 9:?:          <TD> ` |- ( ( ( [. A / x ]. ph `
     ` \/ [. A / x ]. ps ) \/ [. A / x ]. ch ) <-> ( [. A / x ]. ph `
     ` \/ [. A / x ]. ps \/ [. A / x ]. ch ) ) `
     <TR> <TD> 10:8,9,?: ~ e10  <TD> ` |- (. A e. B ->. ( [. A / x ]. ( ph `
     ` \/ ps \/ ch ) <-> ( [. A / x ]. ph \/ [. A / x ]. ps `
     ` \/ [. A / x ]. ch ) ) ). `
     <TR> <TD> qed:10:       <TD> ` |- ( A e. B -> ( [. A / x ]. ( ph `
     ` \/ ps \/ ch ) <-> ( [. A / x ]. ph \/ [. A / x ]. ps `
     ` \/ [. A / x ]. ch ) ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 31-Dec-2011.)  (Proof modification is
     discouraged.)  (New usage is discouraged.) $)
  sbc3orgVD $p |- ( A e. B -> ( [. A / x ]. ( ph \/ ps \/ ch ) <->
                  ( [. A / x ]. ph \/ [. A / x ]. ps \/ [. A / x ]. ch ) ) ) $=
    ( wcel w3o wsbc wb wo sbcor a1i e1a df-3or bicomi e10 e11 bibi1 biimprd wal
    idn1 ax-gen spsbc sbcbig biimpd bitr3 com12 orbi1 in1 ) EFGZABCHZDEIZADEIZB
    DEIZCDEIZHZJZUKUMUNUOKZUPKZJZUTUQJZURUKUMABKZDEIZUPKZJZVEUTJZVAUKVCCKZDEIZV
    EJZVIUMJZVFUKUKVJUKUBZVJUKVCCDELMNUKUKVHULJZDEIZVKVLUKUKVMDUAVNVLVMDULVHABC
    OPUCVMDEFUDQUKVNVKVHULDEFUEUFRVKVJVFVIUMVEUGUHRUKVDUSJZVGUKUKVOVLVOUKABDELM
    NVDUSUPUINVFVAVGUMVEUTSTRUQUTUNUOUPOPVAURVBUMUTUQSTQUJ $.

  ${
    $d x ps $.  $d x ch $.
    $( Virtual deduction proof of ~ alrim3con13v .  The following user's
       proof is completed by invoking mmj2's unify command and using mmj2's
       StepSelector to pick all remaining steps of the Metamath proof.
       <HTML> <TABLE>
       <TR> <TD> 1::            <TD> ` |- (. ( ph -> A. x ph ) `
       ` ->. ( ph -> A. x ph ) ). `
       <TR> <TD> 2::            <TD> ` |- (. ( ph -> A. x ph ) ,. ( ps /\ ph `
       ` /\
       ch ) ->. ( ps /\ ph /\ ch ) ). `
       <TR> <TD> 3:2,?: ~ e2       <TD> ` |- (. ( ph -> A. x ph ) ,. ( ps `
       ` /\ ph /\ ch ) ->. ps ). `
       <TR> <TD> 4:2,?: ~ e2       <TD> ` |- (. ( ph -> A. x ph ) ,. ( ps `
       ` /\ ph /\ ch ) ->. ph ). `
       <TR> <TD> 5:2,?: ~ e2       <TD> ` |- (. ( ph -> A. x ph ) ,. ( ps `
       ` /\ ph /\ ch ) ->. ch ). `
       <TR> <TD> 6:1,4,?: ~ e12    <TD> ` |- (. ( ph -> A. x ph ) ,. ( ps `
       ` /\ ph /\ ch ) ->. A. x ph ). `
       <TR> <TD> 7:3,?: ~ e2       <TD> ` |- (. ( ph -> A. x ph ) ,. ( ps `
       ` /\ ph /\ ch ) ->. A. x ps ). `
       <TR> <TD> 8:5,?: ~ e2       <TD> ` |- (. ( ph -> A. x ph ) ,. ( ps `
       ` /\ ph /\ ch ) ->. A. x ch ). `
       <TR> <TD> 9:7,6,8,?: ~ e222 <TD> ` |- (. ( ph -> A. x ph ) ,. ( ps `
       ` /\ ph /\ ch ) ->. ( A. x ps /\ A. x ph /\ A. x ch ) ). `
       <TR> <TD> 10:9,?: ~ e2      <TD> ` |- (. ( ph -> A. x ph ) ,. ( ps `
       ` /\ ph /\ ch ) ->. A. x ( ps /\ ph /\ ch ) ). `
       <TR> <TD> 11:10:in2      <TD> ` |- (. ( ph -> A. x ph ) ->. ( ( ps `
       ` /\ ph /\ ch ) -> A. x ( ps /\ ph /\ ch ) ) ). `
       <TR> <TD> qed:11:in1     <TD> ` |- ( ( ph -> A. x ph ) -> ( ( ps `
       ` /\ ph /\ ch ) -> A. x ( ps /\ ph /\ ch ) ) ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 31-Dec-2011.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    19.21a3con13vVD $p |- ( ( ph -> A. x ph ) ->
                         ( ( ps /\ ph /\ ch ) -> A. x ( ps /\ ph /\ ch ) ) ) $=
      ( wal wi w3a idn2 simp1 e2 ax-5 idn1 simp2 id e12 pm3.2an3 e222 19.26-3an
      simp3 biimpri in2 in1 ) AADEZFZBACGZUEDEZFUDUEUFUDUEBDEZUCCDEZGZUFUDUEUGU
      CUHUIUDUEBUGUDUEUEBUDUEHZBACIJBDKJUDUDUEAUCUDLUDUEUEAUJBACMJUDNOUDUECUHUD
      UEUECUJBACSJCDKJUGUCUHPQUFUIBACDRTJUAUB $.
  $}

  $( Virtual deduction proof of ~ exbir .  The following user's proof is
     completed by invoking mmj2's unify command and using mmj2's StepSelector
     to pick all remaining steps of the Metamath proof.
     <HTML> <TABLE>
     <TR> <TD> 1::         <TD> ` |- (. ( ( ph /\ ps ) -> ( ch <-> th ) ) `
     ` ->. ( ( ph /\ ps ) -> ( ch <-> th ) ) ). `
     <TR> <TD> 2::         <TD> ` |- (. ( ( ph /\ ps ) -> ( ch <-> th ) ) ,. `
     ` ( ph /\ ps ) ->. ( ph /\ ps ) ). `
     <TR> <TD> 3::         <TD> ` |- (. ( ( ph /\ ps ) -> ( ch <-> th ) ) ,. `
     ` ( ph /\ ps ) , th ->. th ). `
     <TR> <TD> 5:1,2,?: ~ e12 <TD> ` |- (. ( ( ph /\ ps ) -> ( ch `
     ` <-> th ) ) , ( ph /\ ps )  ->. ( ch <-> th ) ). `
     <TR> <TD> 6:3,5,?: ~ e32 <TD> ` |- (. ( ( ph /\ ps ) -> ( ch `
     ` <-> th ) ) , ( ph /\ ps ) , th ->. ch ). `
     <TR> <TD> 7:6:        <TD> ` |- (. ( ( ph /\ ps ) -> ( ch `
     ` <-> th ) ) , ( ph /\ ps ) ->. ( th -> ch ) ). `
     <TR> <TD> 8:7:        <TD> ` |- (. ( ( ph /\ ps ) -> ( ch <-> th ) ) `
     ` ->. ( ( ph /\ ps ) -> ( th -> ch ) ) ). `
     <TR> <TD> 9:8,?: ~ e1a   <TD> ` |- (. ( ( ph /\ ps ) -> ( ch `
     ` <-> th ) ) ->. ( ph -> ( ps -> ( th -> ch ) ) ) ). `
     <TR> <TD> qed:9:      <TD> ` |- ( ( ( ph /\ ps ) -> ( ch <-> th ) ) `
     ` -> ( ph -> ( ps -> ( th -> ch ) ) ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 13-Dec-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  exbirVD $p |- ( ( ( ph /\ ps ) -> ( ch <-> th ) ) ->
                                          ( ph -> ( ps -> ( th -> ch ) ) ) ) $=
    ( wa wb wi idn3 idn1 idn2 id e12 biimpr com12 e32 in3 in2 pm3.3 e1a in1 ) A
    BEZCDFZGZABDCGZGGZUCUAUDGUEUCUAUDUCUADCUCUADDUBCUCUADHUCUCUAUAUBUCIUCUAJUCK
    LUBDCCDMNOPQABUDRST $.

  ${
    exbiriVD.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Virtual deduction proof of ~ exbiri .  The following user's proof is
       completed by invoking mmj2's unify command and using mmj2's StepSelector
       to pick all remaining steps of the Metamath proof.
       <HTML> <TABLE>
       <TR> <TD> h1::        <TD> ` |- ( ( ph /\ ps ) -> ( ch <-> th ) ) `
       <TR> <TD> 2::         <TD> ` |- (. ph ->. ph ). `
       <TR> <TD> 3::         <TD> ` |- (. ph ,. ps ->. ps ). `
       <TR> <TD> 4::         <TD> ` |- (. ph ,. ps ,. th ->. th ). `
       <TR> <TD> 5:2,1,?: ~ e10 <TD> ` |- (. ph ->. ( ps -> ( ch <-> th ) ) ).
       `
       <TR> <TD> 6:3,5,?: ~ e21 <TD> ` |- (. ph ,. ps ->. ( ch <-> th ) ). `
       <TR> <TD> 7:4,6,?: ~ e32 <TD> ` |- (. ph ,. ps ,. th ->. ch ). `
       <TR> <TD> 8:7:        <TD> ` |- (. ph ,. ps ->. ( th -> ch ) ). `
       <TR> <TD> 9:8:        <TD> ` |- (. ph ->. ( ps -> ( th -> ch ) ) ). `
       <TR> <TD> qed:9:      <TD> ` |- ( ph -> ( ps -> ( th -> ch ) ) ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 31-Dec-2011.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    exbiriVD $p |- ( ph -> ( ps -> ( th -> ch ) ) ) $=
      ( wi wb idn3 idn2 wa idn1 pm3.3 com12 e10 pm2.27 e21 biimpr e32 in3 in2
      in1 ) ABDCFZFABUBABDCABDDCDGZCABDHABBBUCFZUCABIAAABJUCFZUDAKEUEAUDABUCLMN
      BUCOPUCDCCDQMRSTUA $.
  $}

  ${
    $d A y $.  $d B x $.  $d D x y $.
    $( Virtual deduction proof of ~ rspsbc2 .  The following user's proof is
       completed by invoking mmj2's unify command and using mmj2's StepSelector
       to pick all remaining steps of the Metamath proof.
       <HTML> <TABLE>
       <TR> <TD> 1::            <TD> ` |- (. A e. B ->. A e. B ). `
       <TR> <TD> 2::            <TD> ` |- (. A e. B ,. C e. D ->. C e. D ). `
       <TR> <TD> 3::            <TD> ` |- (. A e. B ,. C e. D ,. A. x e. B `
       ` A. y e. D ph ->. A. x e. B A. y e. D ph ). `
       <TR> <TD> 4:1,3,?: ~ e13    <TD> ` |- (. A e. B ,. C e. D ,. A. x e. B `
       ` A. y e. D ph ->. [. A / x ]. A. y e. D ph ). `
       <TR> <TD> 5:1,4,?: ~ e13    <TD> ` |- (. A e. B ,. C e. D ,. A. x e. B `
       ` A. y e. D ph ->. A. y e. D [. A / x ]. ph ). `
       <TR> <TD> 6:2,5,?: ~ e23    <TD> ` |- (. A e. B ,. C e. D ,. A. x e. B `
       ` A. y e. D ph ->. [. C / y ]. [. A / x ]. ph ). `
       <TR> <TD> 7:6:           <TD> ` |- (. A e. B ,. C e. D ->. ( A. x e. B `
       ` A. y e. D ph -> [. C / y ]. [. A / x ]. ph ) ). `
       <TR> <TD> 8:7:           <TD> ` |- (. A e. B ->. ( C e. D `
       ` -> ( A. x e. B A. y e. D ph -> [. C / y ]. [. A / x ]. ph ) ) ). `
       <TR> <TD> qed:8:         <TD> ` |- ( A e. B -> ( C e. D `
       ` -> ( A. x e. B A. y e. D ph -> [. C / y ]. [. A / x ]. ph ) ) ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 31-Dec-2011.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    rspsbc2VD $p |- ( A e. B -> ( C e. D -> ( A. x e. B A. y e. D ph ->
                                            [. C / y ]. [. A / x ]. ph ) ) ) $=
      ( wcel wral wsbc wi idn2 idn1 idn3 rspsbc e13 sbcralg biimpd e23 in3 in2
      in1 ) DEHZFGHZACGIZBEIZABDJZCFJZKZKUCUDUIUCUDUFUHUCUDUDUFUGCGIZUHUCUDLUCU
      CUDUFUEBDJZUJUCMZUCUCUDUFUFUKULUCUDUFNUEBDEOPUCUKUJABCDGEQRPUGCFGOSTUAUB
      $.
  $}

  $( Virtual deduction proof of ~ 3impexp .  The following user's proof is
     completed by invoking mmj2's unify command and using mmj2's StepSelector
     to pick all remaining steps of the Metamath proof.
     <HTML> <TABLE>
     <TR> <TD> 1::                <TD> ` |- (. ( ( ph /\ ps /\ ch ) `
     ` -> th ) ->. ( ( ph /\ ps /\ ch ) -> th ) ).  `
     <TR> <TD> 2::                <TD> ` |- ( ( ph /\ ps /\ ch ) `
     ` <-> ( ( ph /\ ps ) /\ ch ) )  `
     <TR> <TD> 3:1,2,?: ~ e10        <TD> ` |- (. ( ( ph /\ ps /\ ch ) `
     ` -> th ) ->. ( ( ( ph /\ ps ) /\ ch ) -> th ) ). `
     <TR> <TD> 4:3,?: ~ e1a          <TD> ` |- (. ( ( ph /\ ps /\ ch ) `
     ` -> th ) ->. ( ( ph /\ ps ) -> ( ch -> th ) ) ). `
     <TR> <TD> 5:4,?: ~ e1a          <TD> ` |- (. ( ( ph /\ ps /\ ch ) `
     ` -> th ) ->. ( ph -> ( ps -> ( ch -> th ) ) ) ). `
     <TR> <TD> 6:5:               <TD> ` |- ( ( ( ph /\ ps /\ ch ) -> th ) `
     ` -> ( ph -> ( ps -> ( ch -> th ) ) ) ) `
     <TR> <TD> 7::                <TD> ` |- (. ( ph -> ( ps -> ( ch `
     ` -> th ) ) ) ->. ( ph -> ( ps -> ( ch -> th ) ) ) ). `
     <TR> <TD> 8:7,?: ~ e1a          <TD> ` |- (. ( ph -> ( ps -> ( ch `
     ` -> th ) ) ) ->. ( ( ph /\ ps ) -> ( ch -> th ) ) ). `
     <TR> <TD> 9:8,?: ~ e1a          <TD> ` |- (. ( ph -> ( ps -> ( ch `
     ` -> th ) ) ) ->. ( ( ( ph /\ ps ) /\ ch ) -> th ) ). `
     <TR> <TD> 10:2,9,?: ~ e01       <TD> ` |- (. ( ph -> ( ps -> ( ch `
     ` -> th ) ) ) ->. ( ( ph /\ ps /\ ch ) -> th ) ). `
     <TR> <TD> 11:10:             <TD> ` |- ( ( ph -> ( ps -> ( ch `
     ` -> th ) ) ) -> ( ( ph /\ ps /\ ch ) -> th ) ) `
     <TR> <TD> qed:6,11,?: ~ e00     <TD> ` |- ( ( ( ph /\ ps /\ ch ) `
     ` -> th ) <-> ( ph -> ( ps -> ( ch -> th ) ) ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 31-Dec-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  3impexpVD $p |- ( ( ( ph /\ ps /\ ch ) -> th ) <->
                                          ( ph -> ( ps -> ( ch -> th ) ) ) ) $=
    ( w3a wi wb wa idn1 df-3an imbi1 biimpcd e10 pm3.3 e1a pm3.31 biimprd impbi
    in1 e01 e00 ) ABCEZDFZABCDFZFFZFUEUCFUCUEGUCUEUCABHZUDFZUEUCUFCHZDFZUGUCUCU
    BUHGZUIUCIABCJZUJUCUIUBUHDKZLMUFCDNOABUDNOSUEUCUJUEUIUCUKUEUGUIUEUEUGUEIABU
    DPOUFCDPOUJUCUIULQTSUCUERUA $.

  $( Virtual deduction proof of ~ 3impexpbicom .  The following user's proof is
     completed by invoking mmj2's unify command and using mmj2's StepSelector
     to pick all remaining steps of the Metamath proof.
     <HTML> <TABLE>
     <TR> <TD> 1::                <TD> ` |- (. ( ( ph /\ ps /\ ch ) `
     ` -> ( th <-> ta ) ) ->. ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) ). `
     <TR> <TD> 2::                <TD> ` |- ( ( th <-> ta ) <-> ( ta `
     ` <-> th ) ) `
     <TR> <TD> 3:1,2,?: ~ e10        <TD> ` |- (. ( ( ph /\ ps /\ ch ) `
     ` -> ( th <-> ta ) ) ->. ( ( ph /\ ps /\ ch ) -> ( ta <-> th ) ) ). `
     <TR> <TD> 4:3,?: ~ e1a          <TD> ` |- (. ( ( ph /\ ps /\ ch ) `
     ` -> ( th <-> ta ) ) ->. ( ph -> ( ps -> ( ch -> ( ta `
     ` <-> th ) ) ) ) ). `
     <TR> <TD> 5:4:               <TD> ` |- ( ( ( ph /\ ps /\ ch ) `
     ` -> ( th <-> ta ) ) -> ( ph -> ( ps -> ( ch -> ( ta `
     ` <-> th ) ) ) ) ) `
     <TR> <TD> 6::                <TD> ` |- (. ( ph -> ( ps -> ( ch `
     ` -> ( ta <-> th ) ) ) ) ->. ( ph -> ( ps -> ( ch -> ( ta `
     ` <-> th ) ) ) ) ). `
     <TR> <TD> 7:6,?: ~ e1a          <TD> ` |- (. ( ph -> ( ps -> ( ch `
     ` -> ( ta <-> th ) ) ) ) ->. ( ( ph /\ ps /\ ch ) -> ( ta `
     ` <-> th ) ) ). `
     <TR> <TD> 8:7,2,?: ~ e10        <TD> ` |- (. ( ph -> ( ps -> ( ch `
     ` -> ( ta <-> th ) ) ) ) ->. ( ( ph /\ ps /\ ch ) -> ( th `
     ` <-> ta ) ) ). `
     <TR> <TD> 9:8:               <TD> ` |- ( ( ph -> ( ps -> ( ch `
     ` -> ( ta <-> th ) ) ) ) -> ( ( ph /\ ps /\ ch ) -> ( th `
     ` <-> ta ) ) ) `
     <TR> <TD> qed:5,9,?: ~ e00      <TD> ` |- ( ( ( ph /\ ps /\ ch ) `
     ` -> ( th <-> ta ) ) <-> ( ph -> ( ps -> ( ch -> ( ta `
     ` <-> th ) ) ) ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 31-Dec-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  3impexpbicomVD $p |- ( ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) <->
                               ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) ) $=
    ( w3a wb wi bicom imbi2 biimpcd e10 3impexp biimpi e1a in1 biimpri biimprcd
    idn1 impbi e00 ) ABCFZDEGZHZABCEDGZHHHZHUFUDHUDUFGUDUFUDUBUEHZUFUDUDUCUEGZU
    GUDSDEIZUHUDUGUCUEUBJZKLUGUFABCUEMZNOPUFUDUFUGUHUDUFUFUGUFSUGUFUKQOUIUHUDUG
    UJRLPUDUFTUA $.

  ${
    3impexpbicomiVD.1 $e |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) $.
    $( Virtual deduction proof of ~ 3impexpbicomi .  The following user's proof
       is completed by invoking mmj2's unify command and using mmj2's
       StepSelector to pick all remaining steps of the Metamath proof.
       <HTML> <TABLE>
       <TR> <TD> h1::               <TD> ` |- ( ( ph /\ ps /\ ch ) -> ( th `
       ` <-> ta ) ) `
       <TR> <TD> qed:1,?: ~ e0a        <TD> ` |- ( ph -> ( ps -> ( ch `
       ` -> ( ta <-> th ) ) ) ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 31-Dec-2011.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    3impexpbicomiVD $p |- ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) $=
      ( w3a wb wi 3impexpbicom biimpi e0a ) ABCGDEHIZABCEDHIIIZFMNABCDEJKL $.
  $}

  ${
    $d x y $.
    $( Virtual deduction proof of ~ sbcoreleleq .  The following user's proof
       is completed by invoking mmj2's unify command and using mmj2's
       StepSelector to pick all remaining steps of the Metamath proof.
       <HTML> <TABLE>
       <TR> <TD> 1::            <TD> ` |- (. A e. B ->. A e. B ). `
       <TR> <TD> 2:1,?: ~ e1a      <TD> ` |- (. A e. B ->. ( [. A / y ]. x e. `
       ` y <-> x e. A ) ). `
       <TR> <TD> 3:1,?: ~ e1a      <TD> ` |- (. A e. B ->. ( [. A / y ]. y e. `
       ` x <-> A e. x ) ). `
       <TR> <TD> 4:1,?: ~ e1a      <TD> ` |- (. A e. B ->. ( [. A / y ]. x = `
       ` y <-> x = A ) ). `
       <TR> <TD> 5:2,3,4,?: ~ e111 <TD> ` |- (. A e. B ->. ( ( x e. A `
       ` \/ A e. x \/ x = A ) <-> ( [. A / y ]. x e. y \/ [. A / y ]. y e. x `
       ` \/ [. A / y ]. x = y ) ) ). `
       <TR> <TD> 6:1,?: ~ e1a      <TD> ` |- (. A e. B `
       ` ->. ( [. A / y ]. ( x e. y \/ y e. x \/ x = y ) <-> ( [. A / y ]. x `
       ` e. y \/ [. A / y ]. y e. x \/ [. A / y ]. x = y ) ) ). `
       <TR> <TD> 7:5,6: ~ e11      <TD> ` |- (. A e. B ->. ( [. A / y ]. ( x `
       ` e. y \/ y e. x \/ x = y ) <-> ( x e. A \/ A e. x \/ x = A ) ) ).  `
       <TR> <TD> qed:7:         <TD> ` |- ( A e. B -> ( [. A / y ]. ( x e. y `
       ` \/ y e. x \/ x = y ) <-> ( x e. A \/ A e. x \/ x = A ) ) )  `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 31-Dec-2011.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    sbcoreleleqVD $p |- ( A e. B
                        -> ( [. A / y ]. ( x e. y \/ y e. x \/ x = y )
                                       <-> ( x e. A \/ A e. x \/ x = A ) ) ) $=
      ( wcel cv wceq w3o wsbc wb sbcor a1i df-3or bicomi sbcbii 3bitr3d bitr4di
      wo orbi1d dfvd1ir sbcel2gv sbcel1v eqsbc2 3impexpbicomi e101 biantr e11an
      3orbi123 in1 ) CDEZAFZBFZEZULUKEZUKULGZHZBCIZUKCEZCUKEZUKCGZHZJZUJUQUMBCI
      ZUNBCIZUOBCIZHZJZVAVFJZVBUJVGUJUQVCVDRZVERZVFUJUMUNRZUORZBCIZVKBCIZVERZUQ
      VJVMVOJUJVKUOBCKLVMUQJUJVLUPBCUPVLUMUNUOMNOLUJVNVIVEVNVIJUJUMUNBCKLSPVCVD
      VEMQTUJVCURJZVDUSJZVEUTJZVHUJVPBUKCDUATBCUKUBUJVRBCUKDUCTVPVQVRVFVAVCURVD
      USVEUTUHUDUEUQVFVAUFUGUI $.
  $}

  ${
    $d A y $.  $d B x $.  $d x y $.
    $( Virtual deduction proof of ~ nfra2 .  The following user's proof is
       completed by invoking mmj2's unify command and using mmj2's
       StepSelector to pick all remaining steps of the Metamath proof.
       <HTML> <TABLE>
       <TR> <TD> 1::              <TD> ` |- ( A. y e. B A. x e. A ph -> `
       ` A. y A. y e. B A. x e. A ph ) `
       <TR> <TD> 2::              <TD> ` |- ( A. x e. A A. y e. B ph <-> `
       ` A. y e. B A. x e. A ph ) `
       <TR> <TD> 3:1,2,?: ~ e00   <TD> ` |- ( A. x e. A A. y e. B ph -> `
       ` A. y A. y e. B A. x e. A ph ) `
       <TR> <TD> 4:2:             <TD> ` |- A. y ( A. x e. A A. y e. B ph <-> `
       ` A. y e. B A. x e. A ph ) `
       <TR> <TD> 5:4,?: ~ e0a     <TD> ` |- ( A. y A. x e. A A. y e. B ph <-> `
       ` A. y A. y e. B A. x e. A ph ) `
       <TR> <TD> qed:3,5,?: ~ e00 <TD> ` |- ( A. x e. A A. y e. B ph -> `
       ` A. y A. x e. A A. y e. B ph ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 31-Dec-2011.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    hbra2VD $p |- ( A. x e. A A. y e. B ph -> A. y A. x e. A A. y e. B ph ) $=
      ( wral ralcom hbra1 hbxfrbi ) ACEFBDFABDFZCEFCABCDEGJCEHI $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( Virtual deduction proof of ~ tratrb .  The following user's proof is
       completed by invoking mmj2's unify command and using mmj2's StepSelector
       to pick all remaining steps of the Metamath proof.
       <HTML> <TABLE>
       <TR> <TD> 1::                <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) `
       ` ->. ( Tr A /\ A. x e. A A. y e. A ( x e. y \/ y e. x \/ x = y ) `
       ` /\ B e. A ) ). `
       <TR> <TD> 2:1,?: ~ e1a          <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) ->. Tr A ). `
       <TR> <TD> 3:1,?: ~ e1a          <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) `
       ` ->. A. x e. A A. y e. A ( x e. y \/ y e. x \/ x = y ) ). `
       <TR> <TD> 4:1,?: ~ e1a          <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) ->. B e. A ). `
       <TR> <TD> 5::                <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) ->. ( x e. y /\ y e. B ) ). `
       <TR> <TD> 6:5,?: ~ e2           <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) ->. x e. y ). `
       <TR> <TD> 7:5,?: ~ e2           <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) ->. y e. B ). `
       <TR> <TD> 8:2,7,4,?: ~ e121     <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) ->. y e. A ). `
       <TR> <TD> 9:2,6,8,?: ~ e122     <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) ->. x e. A ).  `
       <TR> <TD> 10::               <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) , B e. x ->. B e. x ). `
       <TR> <TD> 11:6,7,10,?: ~ e223   <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) , B e. x ->. ( x e. y /\ y e. B /\ B e. x ) ). `
       <TR> <TD> 12:11:             <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) ->. ( B e. x -> ( x e. y /\ y e. B /\ B e. x ) ) ). `
       <TR> <TD> 13::               <TD> ` |- -. ( x e. y /\ y e. B `
       ` /\ B e. x ) `
       <TR> <TD> 14:12,13,?: ~ e20     <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) ->. -. B e. x ). `
       <TR> <TD> 15::               <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) , x = B ->. x = B ). `
       <TR> <TD> 16:7,15,?: ~ e23      <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) , x = B ->. y e. x ). `
       <TR> <TD> 17:6,16,?: ~ e23      <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) , x = B ->. ( x e. y /\ y e. x ) ). `
       <TR> <TD> 18:17:             <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) ->. ( x = B -> ( x e. y /\ y e. x ) ) ). `
       <TR> <TD> 19::               <TD> ` |- -. ( x e. y /\ y e. x ) `
       <TR> <TD> 20:18,19,?: ~ e20     <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) ->. -. x = B ). `
       <TR> <TD> 21:3,?: ~ e1a         <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) ->. A. y e. A `
       ` A. x e. A ( x e. y \/ y e. x \/ x = y ) ). `
       <TR> <TD> 22:21,9,4,?: ~ e121   <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) ->. [. x / x ]. [. B / y ]. ( x e. y \/ y e. x `
       ` \/ x = y ) ). `
       <TR> <TD> 23:22,?: ~ e2         <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) ->. [. B / y ]. ( x e. y \/ y e. x \/ x = y ) ). `
       <TR> <TD> 24:4,23,?: ~ e12      <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) ->. ( x e. B \/ B e. x \/ x = B ) ). `
       <TR> <TD> 25:14,20,24,?: ~ e222 <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) , ( x e. y `
       ` /\ y e. B ) ->. x e. B ). `
       <TR> <TD> 26:25:             <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) ->. ( ( x e. y `
       ` /\ y e. B ) -> x e. B ) ). `
       <TR> <TD> 27::               <TD> ` |- ( A. x e. A A. y e. A ( x e. y `
       ` \/ y e. x \/ x = y ) -> A. y A. x e. A A. y e. A ( x e. y \/ `
       ` y e. x \/ x = y ) ) `
       <TR> <TD> 28:27,?: ~ e0a        <TD> ` |- ( ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) `
       ` -> A. y ( Tr A /\ A. x e. A A. y e. A ( x e. y \/ y e. x `
       ` \/ x = y ) /\ B e. A ) ) `
       <TR> <TD> 29:28,26:          <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) `
       ` ->. A. y ( ( x e. y /\ y e. B ) -> x e. B ) ). `
       <TR> <TD> 30::               <TD> ` |- ( A. x e. A A. y e. A ( x e. y `
       ` \/ y e. x \/ x = y ) -> A. x A. x e. A A. y e. A ( x e. y `
       ` \/ y e. x \/ x = y ) ) `
       <TR> <TD> 31:30,?: ~ e0a        <TD> ` |- ( ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) -> A. x ( Tr A `
       ` /\ A. x e. A A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) ) `
       <TR> <TD> 32:31,29:          <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) ->. A. x `
       ` A. y ( ( x e. y /\ y e. B ) -> x e. B ) ). `
       <TR> <TD> 33:32,?: ~ e1a        <TD> ` |- (. ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) ->. Tr B ). `
       <TR> <TD> qed:33:            <TD> ` |- ( ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) -> Tr B ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 31-Dec-2011.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    tratrbVD $p |- ( ( Tr A /\ A. x e. A A. y e. A
                         ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) -> Tr B ) $=
      ( wtr wel weq w3o wral wcel w3a cv wa wi wal hbra1 alrim3con13v wn e2 e1a
      e0a ax-5 hbral wceq idn2 simpl simpr idn3 pm3.2an3 e223 in3 con3 biimprcd
      en3lp e20 eleq2 e23 pm3.2 en2lp wsbc idn1 simp3 simp2 ralcom biimpi simp1
      trel expd e121 e122 rspsbc2 com13 wb equid sbceq2a sbcoreleleq biimpd e12
      ax-mp 3ornot23 ex e222 in2 gen11nv dftr2 biimpri in1 ) CEZABFZBAFZABGHZBC
      IZACIZDCJZKZDEZWOWIBLZDJZMZALZDJZNZBOZAOZWPWOXCAWMWMAONWOWOAONWLACPWMWHWN
      AQUAWOXBBWMWMBONWOWOBONWLBACWTCJZBUBWKBCPUCWMWHWNBQUAWOWSXAWOWSDWTJZRZWTD
      UDZRZXAXFXHHZXAWOWSXFWIWRXFKZNXKRXGWOWSXFXKWOWSWIWRXFXFXKWOWSWSWIWOWSUEZW
      IWRUFSZWOWSWSWRXLWIWRUGSZWOWSXFUHWIWRXFUIUJUKWTWQDUNXFXKULUOWOWSXHWIWJMZN
      XORXIWOWSXHXOWOWSWIXHWJXOXMWOWSWRXHXHWJXNWOWSXHUHXHWJWRWTDWQUPUMUQWIWJURU
      QUKWTWQUSXHXOULUOWOWNWSWKBDUTZXJWOWOWNWOVAZWHWMWNVBTZWOWSXPAWTUTZXPWOWKAC
      IBCIZWSXEWNXSWOWMXTWOWOWMXQWHWMWNVCTWMXTWKABCCVDVETWOWHWSWIWQCJZXEWOWOWHX
      QWHWMWNVFTZXMWOWHWSWRWNYAYBXNXRWHWRWNYACWQDVGVHVIWHWIYAXECWTWQVGVHVJXRWNX
      EXTXSWKBADCWTCVKVLVIXSXPAAGXSXPVMAVNXPAWTVOVSVESWNXPXJABDCVPVQVRXGXIXJXAN
      XFXHXAVTWAWBWCWDWDWPXDABDWEWFTWG $.
  $}

  $( Virtual deduction proof of ~ al2im .  The following user's proof is
     completed by invoking mmj2's unify command and using mmj2's StepSelector
     to pick all remaining steps of the Metamath proof.
     <HTML> <TABLE>
     <TR> <TD> 1::         <TD> ` |- (. A. x ( ph -> ( ps -> ch ) ) `
     ` ->. A. x ( ph -> ( ps -> ch ) ) ). `
     <TR> <TD> 2:1,?: ~ e1a   <TD> ` |- (. A. x ( ph -> ( ps -> ch ) ) `
     ` ->. ( A. x ph -> A. x ( ps -> ch ) ) ). `
     <TR> <TD> 3::         <TD> ` |- ( A. x ( ps -> ch ) -> ( A. x ps `
     ` -> A. x ch ) ) `
     <TR> <TD> 4:2,3,?: ~ e10 <TD> ` |- (. A. x ( ph -> ( ps -> ch ) ) `
     ` ->. ( A. x ph -> ( A. x ps -> A. x ch ) ) ). `
     <TR> <TD> qed:4:      <TD> ` |- ( A. x ( ph -> ( ps -> ch ) ) `
     ` -> ( A. x ph -> ( A. x ps -> A. x ch ) ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 31-Dec-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  al2imVD $p |- ( A. x ( ph -> ( ps -> ch ) ) ->
                                     ( A. x ph -> ( A. x ps -> A. x ch ) ) ) $=
    ( wi wal idn1 alim e1a imim1 e10 in1 ) ABCEZEDFZADFZBDFCDFEZEZNOMDFZEZRPEQN
    NSNGAMDHIBCDHORPJKL $.

  $( Virtual deduction proof of ~ syl5imp .  The following user's proof is
     completed by invoking mmj2's unify command and using mmj2's StepSelector
     to pick all remaining steps of the Metamath proof.
     <HTML> <TABLE>
     <TR> <TD> 1::         <TD> ` |- (. ( ph -> ( ps -> ch ) ) ->. ( ph `
     ` -> ( ps -> ch ) ) ). `
     <TR> <TD> 2:1,?: ~ e1a   <TD> ` |- (. ( ph -> ( ps -> ch ) ) ->. ( ps `
     ` -> ( ph -> ch ) ) ). `
     <TR> <TD> 3::         <TD> ` |- (. ( ph -> ( ps -> ch ) ) ,. ( th `
     ` -> ps ) ->. ( th -> ps ) ). `
     <TR> <TD> 4:3,2,?: ~ e21 <TD> ` |- (. ( ph -> ( ps -> ch ) ) ,. ( th `
     ` -> ps )  ->. ( th -> ( ph -> ch ) ) ). `
     <TR> <TD> 5:4,?: ~ e2    <TD> ` |- (. ( ph -> ( ps -> ch ) ) ,. ( th `
     ` -> ps )  ->. ( ph -> ( th -> ch ) ) ). `
     <TR> <TD> 6:5:        <TD> ` |- (. ( ph -> ( ps -> ch ) ) ->. ( ( th `
     ` -> ps ) -> ( ph -> ( th -> ch ) ) ) ). `
     <TR> <TD> qed:6:      <TD> ` |- ( ( ph -> ( ps -> ch ) ) -> ( ( th `
     ` -> ps ) -> ( ph -> ( th -> ch ) ) ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 31-Dec-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  syl5impVD $p |- ( ( ph -> ( ps -> ch ) ) ->
                                ( ( th -> ps ) -> ( ph -> ( th -> ch ) ) ) ) $=
    ( wi idn2 idn1 pm2.04 e1a imim1 e21 e2 in2 in1 ) ABCEEZDBEZADCEEZEOPQOPDACE
    ZEZQOPPBREZSOPFOOTOGABCHIDBRJKDACHLMN $.

  ${
    idiVD.1 $e |- ph $.
    $( Virtual deduction proof of ~ idiALT .  The following user's
       proof is completed by invoking mmj2's unify command and using mmj2's
       StepSelector to pick all remaining steps of the Metamath proof.
       <HTML> <TABLE>
       <TR> <TD> h1::        <TD> ` |- ph `
       <TR> <TD> qed:1,?: ~ e0a <TD> ` |- ph `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 31-Dec-2011.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    idiVD $p |- ph $=
      ( id e0a ) AABACD $.
  $}

  $( Closed form of ~ ancoms .  The following user's proof is completed by
     invoking mmj2's unify command and using mmj2's StepSelector to pick all
     remaining steps of the Metamath proof.
     <HTML> <TABLE>
     <TR> <TD> 1::         <TD> ` |- ( ( ph /\ ps ) <-> ( ps /\ ph ) )  `
     <TR> <TD> qed:1,?: ~ e0a <TD> ` |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ps `
     ` /\ ph ) -> ch ) ) `
     </TABLE> </HTML>
     The proof of ~ ancomst is derived automatically from it.  (Contributed by
     Alan Sare, 25-Dec-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ancomstVD $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ps /\ ph ) -> ch ) ) $=
    ( wa wb wi ancom imbi1 e0a ) ABDZBADZEJCFKCFEABGJKCHI $.

  ${
    $d A x $.  $d B x $.  $d C x $.  $d C y $.  $d D x $.  $d D y $.
    $( Quantification restricted to a subclass for two quantifiers.  ~ ssralv
       for two quantifiers.  The following User's Proof is a Virtual Deduction
       proof completed automatically by the tools program
       completeusersproof.cmd, which invokes Mel L. O'Cat's mmj2 and Norm
       Megill's Metamath Proof Assistant.  ~ ssralv2 is ~ ssralv2VD without
       virtual deductions and was automatically derived from ~ ssralv2VD .
       <HTML> <TABLE>
       <TR> <TD> 1::          <TD> ` |- (. ( A C_ B /\ C C_ D ) ->. ( A C_ B `
       ` /\ C C_ D ) ). `
       <TR> <TD> 2::          <TD> ` |- (. ( A C_ B /\ C C_ D ) ,. A. x e. B `
       ` A. y e. D ph ->. A. x e. B A. y e. D ph ). `
       <TR> <TD> 3:1:         <TD> ` |- (. ( A C_ B /\ C C_ D ) ->. A C_ B ). `
       <TR> <TD> 4:3,2:       <TD> ` |- (. ( A C_ B /\ C C_ D ) ,. A. x e. B `
       ` A. y e. D ph ->. A. x e. A A. y e. D ph ). `
       <TR> <TD> 5:4:         <TD> ` |- (. ( A C_ B /\ C C_ D ) ,. A. x e. B `
       ` A. y e. D ph ->. A. x ( x e. A -> A. y e. D ph ) ). `
       <TR> <TD> 6:5:         <TD> ` |- (. ( A C_ B /\ C C_ D ) ,. A. x e. B `
       ` A. y e. D ph ->. ( x e. A -> A. y e. D ph ) ). `
       <TR> <TD> 7::          <TD> ` |- (. ( A C_ B /\ C C_ D ) ,. A. x e. B `
       ` A. y e. D ph , x e. A ->. x e. A ). `
       <TR> <TD> 8:7,6:       <TD> ` |- (. ( A C_ B /\ C C_ D ) ,. A. x e. B `
       ` A. y e. D ph , x e. A ->. A. y e. D ph ). `
       <TR> <TD> 9:1:         <TD> ` |- (. ( A C_ B /\ C C_ D ) ->. C C_ D ). `
       <TR> <TD> 10:9,8:      <TD> ` |- (. ( A C_ B /\ C C_ D ) ,. A. x e. B `
       ` A. y e. D ph , x e. A ->. A. y e. C ph ). `
       <TR> <TD> 11:10:       <TD> ` |- (. ( A C_ B /\ C C_ D ) ,. A. x e. B `
       ` A. y e. D ph ->. ( x e. A -> A. y e. C ph ) ). `
       <TR> <TD> 12::         <TD> ` |- ( ( A C_ B /\ C C_ D ) `
       ` -> A. x ( A C_ B /\ C C_ D ) ) `
       <TR> <TD> 13::         <TD> ` |- ( A. x e. B A. y e. D ph `
       ` -> A. x A. x e. B A. y e. D ph ) `
       <TR> <TD> 14:12,13,11: <TD> ` |- (. ( A C_ B /\ C C_ D ) ,. A. x e. B `
       ` A. y e. D ph ->. A. x ( x e. A -> A. y e. C ph ) ). `
       <TR> <TD> 15:14:       <TD> ` |- (. ( A C_ B /\ C C_ D ) ,. A. x e. B `
       ` A. y e. D ph ->. A. x e. A A. y e. C ph ). `
       <TR> <TD> 16:15:       <TD> ` |- (. ( A C_ B /\ C C_ D ) `
       ` ->. ( A. x e. B A. y e. D ph -> A. x e. A A. y e. C ph ) ). `
       <TR> <TD> qed:16:      <TD> ` |- ( ( A C_ B /\ C C_ D ) `
       ` -> ( A. x e. B A. y e. D ph -> A. x e. A A. y e. C ph ) ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 10-Feb-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    ssralv2VD $p |- ( ( A C_ B /\ C C_ D ) ->
                      ( A. x e. B A. y e. D ph -> A. x e. A A. y e. C ph ) ) $=
      ( wss wa wral wi cv wcel wal ax-5 hbra1 e1a ssralv df-ral e2 simpr biimpi
      idn1 idn3 simpl idn2 e12 sp pm2.27 e32 e13 in3 gen21nv biimpri in2 in1 )
      DEHZFGHZIZACGJZBEJZACFJZBDJZKUSVAVCUSVABLDMZVBKZBNZVCUSVAVEBUSBOUTBEPUSVA
      VDVBUSURVAVDUTVBUSUSURUSUCZUQURUAQUSVAVDVDVDUTKZUTUSVAVDUDUSVAVHBNZVHUSVA
      UTBDJZVIUSUQVAVAVJUSUSUQVGUQURUEQUSVAUFUTBDERUGVJVIUTBDSUBTVHBUHTVDUTUIUJ
      ACFGRUKULUMVCVFVBBDSUNTUOUP $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( An element of an ordinal class is ordinal.  Proposition 7.6 of
       [TakeutiZaring] p. 36.  This is an alternate proof of ~ ordelord using
       the Axiom of Regularity indirectly through ~ dford2 .  dford2 is a
       weaker definition of ordinal number.  Given the Axiom of Regularity, it
       need not be assumed that ` _E Fr A ` because this is inferred by the
       Axiom of Regularity.  The following User's Proof is a Virtual Deduction
       proof completed automatically by the tools program
       completeusersproof.cmd, which invokes Mel L. O'Cat's mmj2 and Norm
       Megill's Metamath Proof Assistant.  ~ ordelordALT is ~ ordelordALTVD
       without virtual deductions and was automatically derived from
       ~ ordelordALTVD using the tools program
       translate..without..overwriting.cmd and the Metamath program "MM-PA>
       MINIMIZE__WITH *" command.
       <HTML> <TABLE>
       <TR> <TD> 1::        <TD> ` |- (. ( Ord A /\ B e. A ) ->. ( Ord A `
       ` /\ B e. A ) ). `
       <TR> <TD> 2:1:       <TD> ` |- (. ( Ord A /\ B e. A ) ->. Ord A ). `
       <TR> <TD> 3:1:       <TD> ` |- (. ( Ord A /\ B e. A ) ->. B e. A ). `
       <TR> <TD> 4:2:       <TD> ` |- (. ( Ord A /\ B e. A ) ->. Tr A ). `
       <TR> <TD> 5:2:       <TD> ` |- (. ( Ord A /\ B e. A ) ->. A. x e. A `
       ` A. y e. A ( x e. y \/ x = y \/ y e. x ) ). `
       <TR> <TD> 6:4,3:     <TD> ` |- (. ( Ord A /\ B e. A ) ->. B C_ A ). `
       <TR> <TD> 7:6,6,5:   <TD> ` |- (. ( Ord A /\ B e. A ) ->. A. x e. B `
       ` A. y e. B ( x e. y \/ x = y \/ y e. x ) ). `
       <TR> <TD> 8::        <TD> ` |- ( ( x e. y \/ x = y \/ y e. x ) `
       ` <-> ( x e. y \/ y e. x \/ x = y ) ) `
       <TR> <TD> 9:8:       <TD> ` |- A. y ( ( x e. y \/ x = y \/ y e. x ) `
       ` <-> ( x e. y \/ y e. x \/ x = y ) ) `
       <TR> <TD> 10:9:      <TD> ` |- A. y e. A ( ( x e. y \/ x = y `
       ` \/ y e. x ) <-> ( x e. y \/ y e. x \/ x = y ) ) `
       <TR> <TD> 11:10:     <TD> ` |- ( A. y e. A ( x e. y \/ x = y `
       ` \/ y e. x ) <-> A. y e. A ( x e. y \/ y e. x \/ x = y ) ) `
       <TR> <TD> 12:11:     <TD> ` |- A. x ( A. y e. A ( x e. y \/ x = y `
       ` \/ y e. x ) <-> A. y e. A ( x e. y \/ y e. x \/ x = y ) ) `
       <TR> <TD> 13:12:     <TD> ` |- A. x e. A ( A. y e. A ( x e. y `
       ` \/ x = y \/ y e. x ) <-> A. y e. A ( x e. y \/ y e. x \/ x = y ) ) `
       <TR> <TD> 14:13:     <TD> ` |- ( A. x e. A A. y e. A ( x e. y `
       ` \/ x = y \/ y e. x ) <-> A. x e. A A. y e. A ( x e. y \/ y e. x `
       ` \/ x = y ) ) `
       <TR> <TD> 15:14,5:   <TD> ` |- (. ( Ord A /\ B e. A ) ->. A. x e. A `
       ` A. y e. A ( x e. y \/ y e. x \/ x = y ) ). `
       <TR> <TD> 16:4,15,3: <TD> ` |- (. ( Ord A /\ B e. A ) ->. Tr B ). `
       <TR> <TD> 17:16,7:   <TD> ` |- (. ( Ord A /\ B e. A ) ->. Ord B ). `
       <TR> <TD> qed:17:    <TD> ` |- ( ( Ord A /\ B e. A ) -> Ord B ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 12-Feb-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    ordelordALTVD $p |- ( ( Ord A /\ B e. A ) -> Ord B ) $=
      ( vx vy word wcel wtr cv w3o wral e1a dford2 wb wal ax-gen alral e0a e111
      ralbi e11 wa wceq idn1 simpl ordtr simprbi 3orcomb e1bi simpr tratrb 3exp
      wss trss wi ssralv2 ex simplbi2 in1 ) AEZBAFZUAZBEZVABGZCHZDHZFZVDVEUBZVE
      VDFZIZDBJCBJZVBVAAGZVFVHVGIZDAJZCAJZUTVCVAUSVKVAVAUSVAUCZUSUTUDKZAUEKZVAV
      IDAJZCAJZVNVAUSVSVPUSVKVSCDALUFKZVRVMMZCAJZVSVNMWACNWBWACVIVLMZDAJZWAWCDN
      WDWCDVFVGVHUGOWCDAPQVIVLDASQOWACAPQVRVMCASQUHVAVAUTVOUSUTUIKZVKVNUTVCCDAB
      UJUKRVABAULZWFVSVJVAVKUTWFVQWEABUMTZWGVTWFWFVSVJUNVICDBABAUOUPRVBVCVJCDBL
      UQTUR $.
  $}

  $( If a class equals the union of two other classes, then it equals the union
     of those two classes commuted.  The following User's Proof is a Virtual
     Deduction proof completed automatically by the tools program
     completeusersproof.cmd, which invokes Mel L. O'Cat's mmj2 and Norm
     Megill's Metamath Proof Assistant.  ~ equncom is ~ equncomVD without
     virtual deductions and was automatically derived from ~ equncomVD .
     <HTML> <TABLE>
     <TR> <TD> 1::    <TD> ` |- (. A = ( B u. C ) ->. A = ( B u. C ) ). `
     <TR> <TD> 2::    <TD> ` |- ( B u. C ) = ( C u. B ) `
     <TR> <TD> 3:1,2: <TD> ` |- (. A = ( B u. C ) ->. A = ( C u. B ) ). `
     <TR> <TD> 4:3:   <TD> ` |- ( A = ( B u. C ) -> A = ( C u. B ) ) `
     <TR> <TD> 5::    <TD> ` |- (. A = ( C u. B ) ->. A = ( C u. B ) ). `
     <TR> <TD> 6:5,2: <TD> ` |- (. A = ( C u. B ) ->. A = ( B u. C ) ). `
     <TR> <TD> 7:6:   <TD> ` |- ( A = ( C u. B ) -> A = ( B u. C ) ) `
     <TR> <TD> 8:4,7: <TD> ` |- ( A = ( B u. C ) <-> A = ( C u. B ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 17-Feb-2012.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  equncomVD $p |- ( A = ( B u. C ) <-> A = ( C u. B ) ) $=
    ( cun wceq idn1 uncom eqeq1 biimprd e10 in1 eqeq2 biimprcd impbii ) ABCDZEZ
    ACBDZEZPRPPOQEZRPFBCGZPRSAOQHIJKRPRRSPRFTSPROQALMJKN $.

  ${
    equncomiVD.1 $e |- A = ( B u. C ) $.
    $( Inference form of ~ equncom .  The following User's Proof is a
       Virtual Deduction proof completed automatically by the tools program
       completeusersproof.cmd, which invokes Mel L. O'Cat's mmj2 and Norm
       Megill's Metamath Proof Assistant.  ~ equncomi is ~ equncomiVD without
       virtual deductions and was automatically derived from ~ equncomiVD .
       <HTML> <TABLE>
       <TR> <TD> h1::   <TD> ` |- A = ( B u. C ) `
       <TR> <TD> qed:1: <TD> ` |- A = ( C u. B ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 18-Feb-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    equncomiVD $p |- A = ( C u. B ) $=
      ( cun wceq equncom biimpi e0a ) ABCEFZACBEFZDJKABCGHI $.
  $}

  ${
    sucidALTVD.1 $e |- A e. _V $.
    $( A set belongs to its successor.  Alternate proof of ~ sucid .
       The following User's Proof is a Virtual Deduction proof
       completed automatically by the tools program
       completeusersproof.cmd, which invokes Mel L. O'Cat's mmj2 and Norm
       Megill's Metamath Proof Assistant.  ~ sucidALT is ~ sucidALTVD
       without virtual deductions and was automatically derived from
       ~ sucidALTVD . This proof illustrates that
       completeusersproof.cmd will generate a Metamath proof from any
       User's Proof which is "conventional" in the sense that no step
       is a virtual deduction, provided that all necessary unification
       theorems and transformation deductions are in set.mm.
       completeusersproof.cmd automatically converts such a
       conventional proof into a Virtual Deduction proof for which each
       step happens to be a 0-virtual hypothesis virtual deduction.
       The user does not need to search for reference theorem labels or
       deduction labels nor does he(she) need to use theorems and
       deductions which unify with reference theorems and deductions in
       set.mm.  All that is necessary is that each theorem or deduction
       of the User's Proof unifies with some reference theorem or
       deduction in set.mm or is a semantic variation of some theorem
       or deduction which unifies with some reference theorem or
       deduction in set.mm.  The definition of "semantic variation" has
       not been precisely defined.  If it is obvious that a theorem or
       deduction has the same meaning as another theorem or deduction,
       then it is a semantic variation of the latter theorem or
       deduction.  For example, step 4 of the User's Proof is a
       semantic variation of the definition (axiom)
       ` suc A = ( A u. { A } ) ` , which unifies with ~ df-suc , a
       reference definition (axiom) in set.mm.  Also, a theorem or
       deduction is said to be a semantic variation of another
       theorem or deduction if it is obvious upon cursory inspection
       that it has the same meaning as a weaker form of the latter
       theorem or deduction.  For example, the deduction ` Ord A `
       infers  ` A. x e. A A. y e. A ( x e. y \/ x = y \/ y e. x ) ` is a
       semantic variation of the theorem ` ( Ord A <-> ( Tr A /\ A. x e. A `
       ` A. y e. A ( x e. y \/ x = y \/ y e. x ) ) ) ` , which unifies with
       the set.mm reference definition (axiom) ~ dford2 .
       <HTML> <TABLE>
       <TR> <TD> h1::     <TD> ` |- A e. _V   `
       <TR> <TD> 2:1:     <TD> ` |- A e. { A } `
       <TR> <TD> 3:2:     <TD> ` |- A e. ( { A } u. A ) `
       <TR> <TD> 4::      <TD> ` |- suc A = ( { A } u. A ) `
       <TR> <TD> qed:3,4: <TD> ` |- A e. suc A  `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 18-Feb-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    sucidALTVD $p |- A e. suc A $=
      ( csn cun csuc wcel snid elun1 e0a df-suc equncomi eleqtrri ) AACZADZAEZA
      MFANFABGAMAHIOAMAJKL $.
  $}

  ${
    sucidALT.1 $e |- A e. _V $.
    $( A set belongs to its successor.  This proof was automatically derived
       from ~ sucidALTVD using translate__without__overwriting.cmd and
       minimizing.  (Contributed by Alan Sare, 18-Feb-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sucidALT $p |- A e. suc A $=
      ( csn cun csuc wcel snid elun1 ax-mp df-suc equncomi eleqtrri ) AACZADZAE
      ZAMFANFABGAMAHIOAMAJKL $.
  $}

  ${
    sucidVD.1 $e |- A e. _V $.
    $( A set belongs to its successor.  The following User's Proof is a
       Virtual Deduction proof completed automatically by the tools
       program completeusersproof.cmd, which invokes Mel L. O'Cat's mmj2
       and Norm Megill's Metamath Proof Assistant.
       ~ sucid is ~ sucidVD without virtual deductions and was automatically
       derived from ~ sucidVD .
       <HTML> <TABLE>
       <TR> <TD> h1::     <TD> ` |- A e. _V   `
       <TR> <TD> 2:1:     <TD> ` |- A e. { A } `
       <TR> <TD> 3:2:     <TD> ` |- A e. ( A u. { A } ) `
       <TR> <TD> 4::      <TD> ` |- suc A = ( A u. { A } ) `
       <TR> <TD> qed:3,4: <TD> ` |- A e. suc A  `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 18-Feb-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    sucidVD $p |- A e. suc A $=
      ( csn cun csuc wcel snid elun2 e0a df-suc eleqtrri ) AAACZDZAEALFAMFABGAL
      AHIAJK $.
  $}

  $( Implication form of ~ imbi12i .  The following User's Proof is a Virtual
     Deduction proof completed automatically by the tools program
     completeusersproof.cmd, which invokes Mel L. O'Cat's mmj2 and Norm
     Megill's Metamath Proof Assistant.  ~ imbi12 is ~ imbi12VD without virtual
     deductions and was automatically derived from ~ imbi12VD .
     <HTML> <TABLE>
     <TR> <TD> 1::      <TD> ` |- (. ( ph <-> ps ) ->. ( ph <-> ps ) ). `
     <TR> <TD> 2::      <TD> ` |- (. ( ph <-> ps ) ,. ( ch <-> th ) `
     ` ->. ( ch <-> th ) ). `
     <TR> <TD> 3::      <TD> ` |- (. ( ph <-> ps ) ,. ( ch <-> th ) ,. ( ph `
     ` -> ch ) ->. ( ph -> ch ) ). `
     <TR> <TD> 4:1,3:   <TD> ` |- (. ( ph <-> ps ) ,. ( ch <-> th ) ,. ( ph `
     ` -> ch ) ->. ( ps -> ch ) ). `
     <TR> <TD> 5:2,4:   <TD> ` |- (. ( ph <-> ps ) ,. ( ch <-> th ) ,. ( ph `
     ` -> ch ) ->. ( ps -> th ) ). `
     <TR> <TD> 6:5:     <TD> ` |- (. ( ph <-> ps ) ,. ( ch <-> th ) `
     ` ->. ( ( ph -> ch ) -> ( ps -> th ) ) ). `
     <TR> <TD> 7::      <TD> ` |- (. ( ph <-> ps ) ,. ( ch <-> th ) ,. ( ps `
     ` -> th ) ->. ( ps -> th ) ). `
     <TR> <TD> 8:1,7:   <TD> ` |- (. ( ph <-> ps ) ,. ( ch <-> th ) ,. ( ps `
     ` -> th ) ->. ( ph -> th ) ). `
     <TR> <TD> 9:2,8:   <TD> ` |- (. ( ph <-> ps ) ,. ( ch <-> th ) ,. ( ps `
     ` -> th ) ->. ( ph -> ch ) ). `
     <TR> <TD> 10:9:    <TD> ` |- (. ( ph <-> ps ) ,. ( ch <-> th ) `
     ` ->. ( ( ps -> th ) -> ( ph -> ch ) ) ). `
     <TR> <TD> 11:6,10: <TD> ` |- (. ( ph <-> ps ) ,. ( ch <-> th ) `
     ` ->. ( ( ph -> ch ) <-> ( ps -> th ) ) ). `
     <TR> <TD> 12:11:   <TD> ` |- (. ( ph <-> ps ) ->. ( ( ch <-> th ) `
     ` -> ( ( ph -> ch ) <-> ( ps -> th ) ) ) ). `
     <TR> <TD> qed:12:  <TD> ` |- ( ( ph <-> ps ) -> ( ( ch <-> th ) `
     ` -> ( ( ph -> ch ) <-> ( ps -> th ) ) ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 18-Mar-2012.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  imbi12VD $p |- ( ( ph <-> ps ) ->
                    ( ( ch <-> th ) -> ( ( ph -> ch ) <-> ( ps -> th ) ) ) ) $=
    ( wb wi idn2 idn1 idn3 biimpr imim1d e13 biimp imim2d e23 in3 impbi e22 in2
    in1 ) ABEZCDEZACFZBDFZEZFUAUBUEUAUBUCUDFUDUCFUEUAUBUCUDUAUBUBUCBCFZUDUAUBGZ
    UAUAUBUCUCUFUAHZUAUBUCIUABACABJKLUBCDBCDMNOPUAUBUDUCUAUBUBUDADFZUCUGUAUAUBU
    DUDUIUHUAUBUDIUAABDABMKLUBDCACDJNOPUCUDQRST $.

  $( Join three logical equivalences to form equivalence of implications.  The
     following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.  ~ imbi13
     is ~ imbi13VD without virtual deductions and was automatically derived
     from ~ imbi13VD .
     <HTML> <TABLE>
     <TR> <TD> 1::      <TD> ` |- (. ( ph <-> ps ) ->. ( ph <-> ps ) ). `
     <TR> <TD> 2::      <TD> ` |- (. ( ph <-> ps ) ,. ( ch <-> th ) `
     ` ->. ( ch <-> th ) ). `
     <TR> <TD> 3::      <TD> ` |- (. ( ph <-> ps ) ,. ( ch <-> th ) ,. ( ta `
     ` <-> et ) ->. ( ta <-> et ) ). `
     <TR> <TD> 4:2,3:   <TD> ` |- (. ( ph <-> ps ) ,. ( ch <-> th ) ,. ( ta `
     ` <-> et ) ->. ( ( ch -> ta ) <-> ( th -> et ) ) ). `
     <TR> <TD> 5:1,4:   <TD> ` |- (. ( ph <-> ps ) ,. ( ch <-> th ) ,. ( ta `
     ` <-> et ) ->. ( ( ph -> ( ch -> ta ) ) <-> ( ps -> ( th -> et ) ) ) ). `
     <TR> <TD> 6:5:     <TD> ` |- (. ( ph <-> ps ) ,. ( ch <-> th ) `
     ` ->. ( ( ta <-> et ) -> ( ( ph -> ( ch -> ta ) ) <-> ( ps -> ( th `
     ` -> et ) ) ) ) ). `
     <TR> <TD> 7:6:     <TD> ` |- (. ( ph <-> ps ) ->. ( ( ch <-> th ) `
     ` -> ( ( ta <-> et ) -> ( ( ph -> ( ch -> ta ) ) <-> ( ps -> ( th `
     ` -> et ) ) ) ) ) ).  `
     <TR> <TD> qed:7:   <TD> ` |- ( ( ph <-> ps ) -> ( ( ch <-> th ) `
     ` -> ( ( ta <-> et ) -> ( ( ph -> ( ch -> ta ) ) <-> ( ps -> ( th `
     ` -> et ) ) ) ) ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 18-Mar-2012.)  (Proof modification is
     discouraged.)  (New usage is discouraged.) $)
  imbi13VD $p |- ( ( ph <-> ps ) -> ( ( ch <-> th ) -> ( ( ta <-> et ) ->
                 ( ( ph -> ( ch -> ta ) ) <-> ( ps -> ( th -> et ) ) ) ) ) ) $=
    ( wb wi idn1 idn2 idn3 imbi12 e23 e13 in3 in2 in1 ) ABGZCDGZEFGZACEHZHBDFHZ
    HGZHZHRSUDRSTUCRRSTUAUBGZUCRIRSSTTUERSJRSTKCDEFLMABUAUBLNOPQ $.

  $( Distribution of class substitution over a left-nested implication.
     Similar to ~ sbcimg .
     The following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
     ~ sbcim2g is ~ sbcim2gVD without virtual deductions and was automatically
     derived from ~ sbcim2gVD .
     <HTML> <TABLE>
     <TR> <TD> 1::      <TD> ` |- (. A e. B ->. A e. B ). `
     <TR> <TD> 2::      <TD> ` |- (. A e. B ,. [. A / x ]. ( ph -> ( ps `
     ` -> ch ) ) ->. [. A / x ]. ( ph -> ( ps -> ch ) ) ). `
     <TR> <TD> 3:1,2:   <TD> ` |- (. A e. B ,. [. A / x ]. ( ph -> ( ps `
     ` -> ch ) ) ->. ( [. A / x ]. ph -> [. A / x ]. ( ps -> ch ) ) ). `
     <TR> <TD> 4:1:     <TD> ` |- (. A e. B ->. ( [. A / x ]. ( ps -> ch ) `
     ` <-> ( [. A / x ]. ps -> [. A / x ]. ch ) ) ). `
     <TR> <TD> 5:3,4:   <TD> ` |- (. A e. B ,. [. A / x ]. ( ph -> ( ps `
     ` -> ch ) ) ->. ( [. A / x ]. ph -> ( [. A / x ]. ps `
     ` -> [. A / x ]. ch ) ) ). `
     <TR> <TD> 6:5:     <TD> ` |- (. A e. B ->. ( [. A / x ]. ( ph -> ( ps `
     ` -> ch ) ) -> ( [. A / x ]. ph -> ( [. A / x ]. ps `
     ` -> [. A / x ]. ch ) ) ) ). `
     <TR> <TD> 7::      <TD> ` |- (. A e. B ,. ( [. A / x ]. ph `
     ` -> ( [. A / x ]. ps -> [. A / x ]. ch ) ) ->. ( [. A / x ]. ph `
     ` -> ( [. A / x ]. ps -> [. A / x ]. ch ) ) ). `
     <TR> <TD> 8:4,7:   <TD> ` |- (. A e. B ,. ( [. A / x ]. ph `
     ` -> ( [. A / x ]. ps -> [. A / x ]. ch ) ) ->. ( [. A / x ]. ph `
     ` -> [. A / x ]. ( ps -> ch ) ) ). `
     <TR> <TD> 9:1:     <TD> ` |- (. A e. B ->. ( [. A / x ]. ( ph -> ( ps `
     ` -> ch ) ) <-> ( [. A / x ]. ph -> [. A / x ]. ( ps -> ch ) ) ) ). `
     <TR> <TD> 10:8,9:  <TD> ` |- (. A e. B ,. ( [. A / x ]. ph `
     ` -> ( [. A / x ]. ps -> [. A / x ]. ch ) ) ->. [. A / x ]. ( ph -> ( ps `
     ` -> ch ) ) ). `
     <TR> <TD> 11:10:   <TD> ` |- (. A e. B ->. ( ( [. A / x ]. ph `
     ` -> ( [. A / x ]. ps -> [. A / x ]. ch ) ) -> [. A / x ]. ( ph -> ( ps `
     ` -> ch ) ) ) ). `
     <TR> <TD> 12:6,11: <TD> ` |- (. A e. B ->. ( [. A / x ]. ( ph `
     ` -> ( ps -> ch ) ) <-> ( [. A / x ]. ph -> ( [. A / x ]. ps `
     ` -> [. A / x ]. ch ) ) ) ). `
     <TR> <TD> qed:12:  <TD> ` |- ( A e. B -> ( [. A / x ]. ( ph -> ( ps `
     ` -> ch ) ) <-> ( [. A / x ]. ph -> ( [. A / x ]. ps `
     ` -> [. A / x ]. ch ) ) ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 18-Mar-2012.)  (Proof modification is
     discouraged.)  (New usage is discouraged.) $)
  sbcim2gVD $p |- ( A e. B -> ( [. A / x ]. ( ph -> ( ps -> ch ) ) <->
              ( [. A / x ]. ph -> ( [. A / x ]. ps -> [. A / x ]. ch ) ) ) ) $=
    ( wcel wi wsbc wb idn1 idn2 sbcimg biimpd e12 e1a imbi2 e21 in2 biimpr e11
    biimpcd imim2d com12 impbi in1 ) EFGZABCHZHDEIZADEIZBDEICDEIHZHZJZUGUIULHUL
    UIHUMUGUIULUGUIUJUHDEIZHZUNUKJZULUGUGUIUIUOUGKZUGUILUGUIUOAUHDEFMZNOUGUGUPU
    QBCDEFMPZUPUOULUNUKUJQUBRSUGULUIUGULUOUIUOJZUIUGUPULULUOUSUGULLUPUKUNUJUNUK
    TUCOUGUGUTUQURPUTUOUIUIUOTUDRSUIULUEUAUF $.

  $( Implication form of ~ sbcbii .
     The following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
     ~ sbcbi is ~ sbcbiVD without virtual deductions and was automatically
     derived from ~ sbcbiVD .
     <HTML> <TABLE>
     <TR> <TD> 1::           <TD> ` |- (. A e. B ->. A e. B ).  `
     <TR> <TD> 2::           <TD> ` |- (. A e. B ,. A. x ( ph <-> ps ) `
     ` ->. A. x ( ph <-> ps ) ). `
     <TR> <TD> 3:1,2:        <TD> ` |- (. A e. B ,. A. x ( ph <-> ps ) `
     ` ->. [. A / x ]. ( ph <-> ps ) ). `
     <TR> <TD> 4:1,3:        <TD> ` |- (. A e. B ,. A. x ( ph <-> ps ) `
     ` ->. ( [. A / x ]. ph <-> [. A / x ]. ps ) ). `
     <TR> <TD> 5:4:          <TD> ` |- (. A e. B ->. ( A. x ( ph <-> ps ) `
     ` -> ( [. A / x ]. ph <-> [. A / x ]. ps ) ) ). `
     <TR> <TD> qed:5:        <TD> ` |- ( A e. B -> ( A. x ( ph <-> ps ) `
     ` -> ( [. A / x ]. ph <-> [. A / x ]. ps ) ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 18-Mar-2012.)  (Proof modification is
     discouraged.)  (New usage is discouraged.) $)
  sbcbiVD $p |- ( A e. B ->
           ( A. x ( ph <-> ps ) -> ( [. A / x ]. ph <-> [. A / x ]. ps ) ) ) $=
    ( wcel wb wal wsbc wi idn1 idn2 spsbc e12 sbcbig biimpd in2 in1 ) DEFZABGZC
    HZACDIBCDIGZJSUAUBSSUATCDIZUBSKZSSUAUAUCUDSUALTCDEMNSUCUBABCDEOPNQR $.

  ${
    $d A x y z $.  $d B y z $.
    $( Formula-building inference rule for class substitution, substituting a
       class variable for the setvar variable of the transitivity predicate.
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ trsbc is ~ trsbcVD without virtual deductions and was automatically
       derived from ~ trsbcVD .
       <HTML> <TABLE>
       <TR> <TD> 1::        <TD> ` |- (. A e. B ->. A e. B ). `
       <TR> <TD> 2:1:       <TD> ` |- (. A e. B ->. ( [. A / x ]. z e. y `
       ` <-> z e. y ) ). `
       <TR> <TD> 3:1:       <TD> ` |- (. A e. B ->. ( [. A / x ]. y e. x `
       ` <-> y e. A ) ). `
       <TR> <TD> 4:1:       <TD> ` |- (. A e. B ->. ( [. A / x ]. z e. x `
       ` <-> z e. A ) ). `
       <TR> <TD> 5:1,2,3,4: <TD> ` |- (. A e. B ->. ( ( [. A / x ]. z e. y `
       ` -> ( [. A / x ]. y e. x -> [. A / x ]. z e. x ) ) <-> ( z e. y `
       ` -> ( y e. A ->  z e. A ) ) ) ). `
       <TR> <TD> 6:1:       <TD> ` |- (. A e. B ->. ( [. A / x ]. ( z e. y `
       ` -> ( y e. x ->  z e. x ) )  <-> ( [. A / x ]. z e. y -> `
       ` ( [. A / x ]. y e. x -> [. A / x ]. z e. x ) ) ) ). `
       <TR> <TD> 7:5,6:     <TD> ` |- (. A e. B ->. ( [. A / x ]. ( z e. y `
       ` -> ( y e. x ->  z e. x ) )  <-> ( z e. y -> ( y e. A `
       ` -> z e. A ) ) ) ). `
       <TR> <TD> 8::        <TD> ` |- ( ( z e. y -> ( y e. A `
       ` ->  z e. A ) ) <-> ( ( z e. y /\ y e. A ) ->  z e. A ) ) `
       <TR> <TD> 9:7,8:     <TD> ` |- (. A e. B ->. ( [. A / x ]. ( z e. y `
       ` -> ( y e. x ->  z e. x ) )  <-> ( ( z e. y /\ y e. A ) `
       ` ->  z e. A ) ) ). `
       <TR> <TD> 10::       <TD> ` |- ( ( z e. y -> ( y e. x `
       ` ->  z e. x ) ) <-> ( ( z e. y /\ y e. x ) ->  z e. x ) ) `
       <TR> <TD> 11:10:     <TD> ` |- A. x ( ( z e. y -> ( y e. x `
       ` ->  z e. x ) ) <-> ( ( z e. y /\ y e. x ) ->  z e. x ) ) `
       <TR> <TD> 12:1,11:   <TD> ` |- (. A e. B ->. ( [. A / x ]. ( z e. y `
       ` -> ( y e. x ->  z e. x ) ) <-> [. A / x ]. ( ( z e. y /\ y e. x ) `
       ` ->  z e. x ) ) ). `
       <TR> <TD> 13:9,12:   <TD> ` |- (. A e. B ->. ( [. A / x ]. ( ( z e. y `
       ` /\ y e. x ) ->  z e. x ) <-> ( ( z e. y /\ y e. A ) `
       ` ->  z e. A ) ) ). `
       <TR> <TD> 14:13:     <TD> ` |- (. A e. B ->. A. y ( [. A / x ]. ( ( z `
       ` e. y /\ y e. x ) ->  z e. x ) <-> ( ( z e. y /\ y e. A ) `
       ` ->  z e. A ) ) ). `
       <TR> <TD> 15:14:     <TD> ` |- (. A e. B ->. ( A. y [. A / x ]. ( ( z `
       ` e. y /\ y e. x ) ->  z e. x ) <->  A. y ( ( z e. y /\ y e. A ) `
       ` ->  z e. A ) ) ).  `
       <TR> <TD> 16:1:      <TD> ` |- (. A e. B ->. ( [. A / x ]. A. y ( ( z `
       ` e. y /\ y e. x ) ->  z e. x ) <-> A. y [. A / x ]. ( ( z e. y `
       ` /\ y e. x ) -> z e. x ) ) ). `
       <TR> <TD> 17:15,16:  <TD> ` |- (. A e. B ->. ( [. A / x ]. A. y ( ( z `
       ` e. y /\ y e. x ) ->  z e. x ) <-> A. y ( ( z e. y /\ y e. A ) `
       ` ->  z e. A ) ) ). `
       <TR> <TD> 18:17:     <TD> ` |- (. A e. B ->. A. z ( [. A / x ]. A. y ( (
       `
       ` z e. y /\ y e. x ) ->  z e. x ) <-> A. y ( ( z e. y /\ y e. A ) `
       ` ->  z e. A ) ) ). `
       <TR> <TD> 19:18:     <TD> ` |- (. A e. B ->. ( A. z [. A / x ]. A. y ( (
       `
       ` z e. y /\ y e. x ) ->  z e. x ) <-> A. z A. y ( ( z e. y `
       ` /\ y e. A ) -> z e. A ) ) ). `
       <TR> <TD> 20:1:      <TD> ` |- (. A e. B ->. ( [. A / x ]. A. z A. y ( (
       `
       ` z e. y /\ y e. x ) ->  z e. x ) <-> A. z [. A / x ]. A. y ( ( z `
       ` e. y /\ y e. x ) ->  z e. x ) ) ). `
       <TR> <TD> 21:19,20:  <TD> ` |- (. A e. B ->. ( [. A / x ]. A. z A. y ( (
       `
       ` z e. y /\ y e. x ) ->  z e. x ) <-> A. z A. y ( ( z e. y `
       ` /\ y e. A )  -> z e. A ) ) ). `
       <TR> <TD> 22::       <TD> ` |- ( Tr A <-> A. z A. y ( ( z e. y `
       ` /\ y e. A ) ->  z e. A ) ) `
       <TR> <TD> 23:21,22:  <TD> ` |- (. A e. B ->. ( [. A / x ]. A. z A. y ( (
       `
       ` z e. y /\ y e. x ) ->  z e. x ) <-> Tr A ) ). `
       <TR> <TD> 24::       <TD> ` |- ( Tr x <-> A. z A. y ( ( z e. y /\ y `
       ` e. x ) ->  z e. x ) ) `
       <TR> <TD> 25:24:     <TD> ` |- A. x ( Tr x <-> A. z A. y ( ( z e. y `
       ` /\ y e. x ) ->  z e. x ) ) `
       <TR> <TD> 26:1,25:   <TD> ` |- (. A e. B ->. ( [. A / x ]. Tr x `
       ` <-> [. A  / x ]. A. z A. y ( ( z e. y /\ y e. x ) ->  z e. x ) ) ). `
       <TR> <TD> 27:23,26:  <TD> ` |- (. A e. B ->. ( [. A / x ]. Tr x `
       ` <-> Tr A ) ). `
       <TR> <TD> qed:27:    <TD> ` |- ( A e. B -> ( [. A / x ]. Tr x `
       ` <-> Tr A ) ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 18-Mar-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    trsbcVD $p |- ( A e. B -> ( [. A / x ]. Tr x <-> Tr A ) ) $=
      ( vz vy wcel cv wtr wsbc wb wa wi wal e1a sbcel2gv a1i bibi1 biimprcd e11
      e10 idn1 sbcg imbi13 e1111 sbcim2g pm3.31 pm3.3 impbii ax-gen sbcbi bitr3
      biimprd com12 gen11 albi sbcal dftr2 biantr ex in1 ) BCFZAGZHZABIZBHZJZVA
      DGZEGZFZVHVBFZKVGVBFZLZEMZDMZABIZVEJZVDVOJZVFVAVOVIVHBFZKVGBFZLZEMZDMZJZV
      EWBJZVPVAVMABIZDMZWBJZVOWFJZWCVAWEWAJZDMWGVAWIDVAVLABIZEMZWAJZWEWKJZWIVAW
      JVTJZEMWLVAWNEVAVIVJVKLLZABIZVTJZWPWJJZWNVAWPVIVRVSLLZJZWSVTJZWQVAVIABIZV
      JABIZVKABIZLLZWSJZWPXEJZWTVAVAXBVIJZXCVRJZXDVSJZXFVAUAZVAVAXHXKVIABCUBNVA
      VAXIXKAVHBCONVAVAXJXKAVGBCONXHXIXJXFLLLVAXBVIXCVRXDVSUCPUDVAVAXGXKVIVJVKA
      BCUENXGWTXFWPXEWSQRSWSVTVIVRVSUFVIVRVSUGUHWTWQXAWPWSVTQULTVAVAWOVLJZAMWRX
      KXLAWOVLVIVJVKUFVIVJVKUGUHUIWOVLABCUJTWRWQWNWPWJVTUKUMSUNWJVTEUONVAVAWMXK
      WMVAVLEABUPPNWMWIWLWEWKWAQRSUNWEWADUONVAVAWHXKWHVAVMDABUPPNWHWCWGVOWFWBQR
      SDEBUQWCWDVPVOWBVEURUSTVAVAVCVNJZAMVQXKXMADEVBUQUIVCVNABCUJTVQVFVPVDVOVEQ
      RSUT $.
  $}

  ${
    $d A q x y z $.
    $( The union of a class of transitive sets is transitive.
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ truniALT is ~ truniALTVD without virtual deductions and was
       automatically derived from ~ truniALTVD .
       <HTML> <TABLE>
       <TR> <TD> 1::        <TD> ` |- (. A. x e. A Tr x ->. A. x e. A `
       ` Tr x ). `
       <TR> <TD> 2::        <TD> ` |- (. A. x e. A Tr x ,. ( z e. y `
       ` /\ y e. U. A ) ->. ( z e. y /\ y e. U. A ) ).  `
       <TR> <TD> 3:2:       <TD> ` |- (. A. x e. A Tr x ,. ( z e. y `
       ` /\ y e. U. A ) ->. z e. y ). `
       <TR> <TD> 4:2:       <TD> ` |- (. A. x e. A Tr x ,. ( z e. y `
       ` /\ y e. U. A ) ->. y e. U. A ). `
       <TR> <TD> 5:4:       <TD> ` |- (. A. x e. A Tr x ,. ( z e. y `
       ` /\ y e. U. A ) ->. E. q ( y e. q /\ q e. A ) ). `
       <TR> <TD> 6::        <TD> ` |- (. A. x e. A Tr x ,. ( z e. y `
       ` /\ y e. U. A ) , ( y e. q /\ q e. A ) ->. ( y e. q /\ q e. A ) ). `
       <TR> <TD> 7:6:       <TD> ` |- (. A. x e. A Tr x ,. ( z e. y `
       ` /\ y e. U. A ) , ( y e. q /\ q e. A ) ->. y e. q ). `
       <TR> <TD> 8:6:       <TD> ` |- (. A. x e. A Tr x ,. ( z e. y `
       ` /\ y e. U. A ) , ( y e. q /\ q e. A ) ->. q e. A ). `
       <TR> <TD> 9:1,8:     <TD> ` |- (. A. x e. A Tr x ,. ( z e. y `
       ` /\ y e. U. A ) , ( y e. q /\ q e. A ) ->. [ q / x ] Tr x ). `
       <TR> <TD> 10:8,9:    <TD> ` |- (. A. x e. A Tr x ,. ( z e. y `
       ` /\ y e. U. A ) , ( y e. q /\ q e. A ) ->. Tr q ). `
       <TR> <TD> 11:3,7,10: <TD> ` |- (. A. x e. A Tr x ,. ( z e. y `
       ` /\ y e. U. A ) , ( y e. q /\ q e. A ) ->. z e. q ). `
       <TR> <TD> 12:11,8:   <TD> ` |- (. A. x e. A Tr x ,. ( z e. y `
       ` /\ y e. U. A ) , ( y e. q /\ q e. A ) ->. z e. U. A ). `
       <TR> <TD> 13:12:     <TD> ` |- (. A. x e. A Tr x ,. ( z e. y `
       ` /\ y e. U. A ) ->. ( ( y e. q /\ q e. A ) -> z e. U. A ) ). `
       <TR> <TD> 14:13:     <TD> ` |- (. A. x e. A Tr x ,. ( z e. y `
       ` /\ y e. U. A ) ->. A. q ( ( y e. q /\ q e. A ) -> z e. U. A ) ). `
       <TR> <TD> 15:14:     <TD> ` |- (. A. x e. A Tr x ,. ( z e. y `
       ` /\ y e. U. A ) ->. ( E. q ( y e. q /\ q e. A ) -> z e. U. A ) ). `
       <TR> <TD> 16:5,15:   <TD> ` |- (. A. x e. A Tr x ,. ( z e. y `
       ` /\ y e. U. A ) ->. z e. U. A ). `
       <TR> <TD> 17:16:     <TD> ` |- (. A. x e. A Tr x ->. ( ( z e. y `
       ` /\ y e. U. A ) -> z e. U. A ) ). `
       <TR> <TD> 18:17:     <TD> ` |- (. A. x e. A Tr x `
       ` ->. A. z A. y ( ( z e. y /\ y e. U. A ) -> z e. U. A ) ). `
       <TR> <TD> 19:18:     <TD> ` |- (. A. x e. A Tr x ->. Tr U. A ). `
       <TR> <TD> qed:19:    <TD> ` |- ( A. x e. A Tr x -> Tr U. A ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 18-Mar-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    truniALTVD $p |- ( A. x e. A Tr x -> Tr U. A ) $=
      ( vz vy vq cv wtr wral cuni wel wcel wa wi wal simpr e2 biimpi simpl e33
      e3 wex idn2 eluni idn3 wsbc idn1 rspsbc com12 e13 trsbc trel expdcom e233
      biimpd elunii in3 gen21 19.23v pm2.27 e22 in2 gen12 dftr2 biimpri e1a in1
      ex ) AFGZABHZBIZGZVICDJZDFZVJKZLZCFZVJKZMZDNCNZVKVIVRCDVIVOVQVIVODEJZEFZB
      KZLZEUAZWDVQMZVQVIVOVNWDVIVOVOVNVIVOUBZVLVNOPVNWDEVMBUCQPVIVOWCVQMZENZWEV
      IVOWGEVIVOWCVQVIVOWCCEJZWBVQVIVOVLWCVTWAGZWIVIVOVOVLWFVLVNRPVIVOWCWCVTVIV
      OWCUDZVTWBRTVIVOWCWBVHAWAUEZWJVIVOWCWCWBWKVTWBOTZVIVIVOWCWBWLVIUFWMWBVIWL
      VHAWABUGUHUIWBWLWJAWABUJUNSWJVLVTWIWAVPVMUKULUMWMWIWBVQVPWABUOVGSUPUQWHWE
      WCVQEURQPWDVQUSUTVAVBVKVSCDVJVCVDVEVF $.
  $}

  ${
    ee33VD.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    ee33VD.2 $e |- ( ph -> ( ps -> ( ch -> ta ) ) ) $.
    ee33VD.3 $e |- ( th -> ( ta -> et ) ) $.
    $( Non-virtual deduction form of ~ e33 .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ ee33 is ~ ee33VD without virtual deductions and was automatically
       derived from ~ ee33VD .
       <HTML> <TABLE>
       <TR> <TD> h1::   <TD> ` |- ( ph -> ( ps -> ( ch -> th ) ) )  `
       <TR> <TD> h2::   <TD> ` |- ( ph -> ( ps -> ( ch -> ta ) ) )  `
       <TR> <TD> h3::   <TD> ` |- ( th -> ( ta -> et ) ) `
       <TR> <TD> 4:1,3: <TD> ` |- ( ph -> ( ps -> ( ch -> ( ta -> et ) ) ) ) `
       <TR> <TD> 5:4:   <TD> ` |- ( ta -> ( ph -> ( ps -> ( ch -> et ) ) ) ) `
       <TR> <TD> 6:2,5: <TD> ` |- ( ph -> ( ps -> ( ch -> ( ph -> ( ps `
       ` -> ( ch -> et ) ) ) ) ) ) `
       <TR> <TD> 7:6:   <TD> ` |- ( ps -> ( ch -> ( ph -> ( ps -> ( ch `
       ` -> et ) ) ) ) ) `
       <TR> <TD> 8:7:   <TD> ` |- ( ch -> ( ph -> ( ps -> ( ch -> et ) ) ) ) `
       <TR> <TD> qed:8: <TD> ` |- ( ph -> ( ps -> ( ch -> et ) ) ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 18-Mar-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ee33VD $p |- ( ph -> ( ps -> ( ch -> et ) ) ) $=
      ( wi syl8 com4r pm2.43cbi biimpi e0a ) CABCFJZJZJZJZRBSJZSATJZTABCERHABCE
      FABCDEFJGIKLKUATABCQMNOTSBCAPMNOSRCABFMNO $.
  $}

  ${
    $d A q x y z $.
    $( The intersection of a class of transitive sets is transitive.  Virtual
       deduction proof of ~ trintALT .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ trintALT is ~ trintALTVD without virtual deductions and was
       automatically derived from ~ trintALTVD .
       <HTML> <TABLE>
       <TR> <TD> 1::        <TD> ` |- (. A. x e. A Tr x ->. A. x e. A Tr x ). `
       <TR> <TD> 2::        <TD> ` |- (. A. x e. A Tr x ,. ( z e. y /\ y e. `
       ` |^| A ) ->. ( z e. y /\ y e. |^| A ) ). `
       <TR> <TD> 3:2:       <TD> ` |- (. A. x e. A Tr x ,. ( z e. y /\ y e. `
       ` |^| A ) ->. z e. y ). `
       <TR> <TD> 4:2:       <TD> ` |- (. A. x e. A Tr x ,. ( z e. y /\ y e. `
       ` |^| A ) ->. y e. |^| A ). `
       <TR> <TD> 5:4:       <TD> ` |- (. A. x e. A Tr x ,. ( z e. y /\ y e. `
       ` |^| A ) ->. A. q e. A y e. q ). `
       <TR> <TD> 6:5:       <TD> ` |- (. A. x e. A Tr x ,. ( z e. y /\ y e. `
       ` |^| A ) ->. ( q e. A -> y e. q ) ). `
       <TR> <TD> 7::        <TD> ` |- (. A. x e. A Tr x ,. ( z e. y /\ y e. `
       ` |^| A ) , q e. A ->. q e. A ). `
       <TR> <TD> 8:7,6:     <TD> ` |- (. A. x e. A Tr x ,. ( z e. y /\ y e. `
       ` |^| A ) , q e. A ->. y e. q ). `
       <TR> <TD> 9:7,1:     <TD> ` |- (. A. x e. A Tr x ,. ( z e. y /\ y e. `
       ` |^| A ) , q e. A ->. [ q / x ] Tr x ). `
       <TR> <TD> 10:7,9:    <TD> ` |- (. A. x e. A Tr x ,. ( z e. y /\ y e. `
       ` |^| A ) , q e. A ->. Tr q ). `
       <TR> <TD> 11:10,3,8: <TD> ` |- (. A. x e. A Tr x ,. ( z e. y /\ y e. `
       ` |^| A ) , q e. A ->. z e. q ). `
       <TR> <TD> 12:11:     <TD> ` |- (. A. x e. A Tr x ,. ( z e. y /\ y e. `
       ` |^| A ) ->. ( q e. A -> z e. q ) ). `
       <TR> <TD> 13:12:     <TD> ` |- (. A. x e. A Tr x ,. ( z e. y /\ y e. `
       ` |^| A ) ->. A. q ( q e. A -> z e. q ) ). `
       <TR> <TD> 14:13:     <TD> ` |- (. A. x e. A Tr x ,. ( z e. y /\ y e. `
       ` |^| A ) ->. A. q e. A z e. q ). `
       <TR> <TD> 15:3,14:   <TD> ` |- (. A. x e. A Tr x ,. ( z e. y /\ y e. `
       ` |^| A ) ->. z e. |^| A ). `
       <TR> <TD> 16:15:     <TD> ` |- (. A. x e. A Tr x ->. ( ( z e. y /\ y `
       ` e. |^| A ) -> z e. |^| A ) ). `
       <TR> <TD> 17:16:     <TD> ` |- (. A. x e. A Tr x ->. A. z A. y ( ( z `
       ` e. y /\ y e. |^| A ) -> z e. |^| A ) ). `
       <TR> <TD> 18:17:     <TD> ` |- (. A. x e. A Tr x ->. Tr |^| A ). `
       <TR> <TD> qed:18:    <TD> ` |- ( A. x e. A Tr x -> Tr |^| A ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 17-Apr-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    trintALTVD $p |- ( A. x e. A Tr x -> Tr |^| A ) $=
      ( vz vy vq cv wtr wral cint wcel wa wi wal idn2 simpl e2 wsbc idn3 elintg
      biimpri idn1 rspsbc e31 trsbc biimpd e33 simpr ibi rsp e32 trel expd e323
      pm2.27 in3 gen21 df-ral biimprd e22 in2 gen12 dftr2 e1a in1 ) AFGZABHZBIZ
      GZVFCFZDFZJZVJVGJZKZVIVGJZLZDMCMZVHVFVOCDVFVMVNVFVMVKVIEFZJZEBHZVNVFVMVMV
      KVFVMNZVKVLOPZVFVMVQBJZVRLZEMZVSVFVMWCEVFVMWBVRVFVMWBVQGZVKVJVQJZVRVFVMWB
      WBVEAVQQZWEVFVMWBRZVFVMWBWBVFWGWHVFUAVEAVQBUBUCWBWGWEAVQBUDUEUFWAVFVMWBWB
      WBWFLZWFWHVFVMWFEBHZWIVFVMVLWJVFVMVMVLVTVKVLUGPVLWJEVJBVGSUHPWFEBUIPWBWFU
      NUJWEVKWFVRVQVIVJUKULUMUOUPVSWDVREBUQTPVKVNVSEVIBVJSURUSUTVAVHVPCDVGVBTVC
      VD $.
  $}

  ${
    $d A q x y z $.
    $( The intersection of a class of transitive sets is transitive.  Exercise
       5(b) of [Enderton] p. 73. ~ trintALT is an alternate proof of ~ trint .
       ~ trintALT is ~ trintALTVD without virtual deductions and was
       automatically derived from ~ trintALTVD using the tools program
       translate..without..overwriting.cmd and the Metamath program "MM-PA>
       MINIMIZE__WITH *" command.  (Contributed by Alan Sare, 17-Apr-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    trintALT $p |- ( A. x e. A Tr x -> Tr |^| A ) $=
      ( vz vy vq cv wtr wral wel cint wcel wa wi wal simpl a1i wsbc elintg syl6
      iidn3 id rspsbc ee31 trsbc biimpd ee33 simpr ibi trel expd ee323 ralrimdv
      rsp biimprd syl6c alrimivv dftr2 sylibr ) AFGZABHZCDIZDFZBJZKZLZCFZVCKZMZ
      DNCNVCGUTVHCDUTVEVACEIZEBHZVGVEVAMUTVAVDOPZUTVEVIEBUTVEEFZBKZVLGZVADEIZVI
      UTVEVMVMUSAVLQZVNUTVEVMTZUTVEVMVMUTVPVQUTUAUSAVLBUBUCVMVPVNAVLBUDUEUFVKUT
      VEVOEBHZVMVOMUTVEVDVRVEVDMUTVAVDUGPVDVREVBBVCRUHSVOEBUMSVNVAVOVIVLVFVBUIU
      JUKULVAVGVJEVFBVBRUNUOUPCDVCUQUR $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.
    $( The first equality of Exercise 13 of [TakeutiZaring] p. 22.  Virtual
       deduction proof of ~ undif3 .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ undif3 is ~ undif3VD without virtual deductions and was automatically
       derived from ~ undif3VD .
       <HTML> <TABLE>
       <TR> <TD> 1::       <TD> ` |- ( x e. ( A u. ( B \ C ) ) <-> ( x e. A `
       ` \/ x e. ( B \ C ) ) ) `
       <TR> <TD> 2::       <TD> ` |- ( x e. ( B \ C ) <-> ( x e. B /\ -. x e. `
       ` C ) ) `
       <TR> <TD> 3:2:      <TD> ` |- ( ( x e. A \/ x e. ( B \ C ) ) <-> ( x `
       ` e. A \/ ( x e. B /\ -. x e. C ) ) ) `
       <TR> <TD> 4:1,3:    <TD> ` |- ( x e. ( A u. ( B \ C ) ) <-> ( x e. A `
       ` \/ ( x e. B /\ -. x e. C ) ) ) `
       <TR> <TD> 5::       <TD> ` |- (. x e. A ->. x e. A ). `
       <TR> <TD> 6:5:      <TD> ` |- (. x e. A ->. ( x e. A \/ x e. B ) ). `
       <TR> <TD> 7:5:      <TD> ` |- (. x e. A ->. ( -. x e. C \/ x e. A ) ). `
       <TR> <TD> 8:6,7:    <TD> ` |- (. x e. A ->. ( ( x e. A \/ x e. B ) /\ `
       ` ( -. x e. C \/ x e. A ) ) ). `
       <TR> <TD> 9:8:      <TD> ` |- ( x e. A -> ( ( x e. A \/ x e. B ) /\ ( `
       ` -. x e. C \/ x e. A ) ) ) `
       <TR> <TD> 10::      <TD> ` |- (. ( x e. B /\ -. x e. C ) ->. ( x e. B `
       ` /\ -. x e. C ) ). `
       <TR> <TD> 11:10:    <TD> ` |- (. ( x e. B /\ -. x e. C ) ->. x e. B ). `
       <TR> <TD> 12:10:    <TD> ` |- (. ( x e. B /\ -. x e. C ) ->. -. x e. C `
       ` ). `
       <TR> <TD> 13:11:    <TD> ` |- (. ( x e. B /\ -. x e. C ) ->. ( x e. A `
       ` \/ x e. B ) ). `
       <TR> <TD> 14:12:    <TD> ` |- (. ( x e. B /\ -. x e. C ) ->. ( -. x e. `
       ` C \/ x e. A ) ). `
       <TR> <TD> 15:13,14: <TD> ` |- (. ( x e. B /\ -. x e. C ) ->. ( ( x e. `
       ` A \/ x e. B ) /\ ( -. x e. C \/ x e. A ) ) ). `
       <TR> <TD> 16:15:    <TD> ` |- ( ( x e. B /\ -. x e. C ) -> ( ( x e. A `
       ` \/ x e. B ) /\ ( -. x e. C \/ x e. A ) ) ) `
       <TR> <TD> 17:9,16:  <TD> ` |- ( ( x e. A \/ ( x e. B /\ -. x e. C ) ) `
       ` -> ( ( x e. A \/ x e. B ) /\ ( -. x e. C \/ x e. A ) ) ) `
       <TR> <TD> 18::      <TD> ` |- (. ( x e. A /\ -. x e. C ) ->. ( x e. A `
       ` /\ -. x e. C ) ). `
       <TR> <TD> 19:18:    <TD> ` |- (. ( x e. A /\ -. x e. C ) ->. x e. A ). `
       <TR> <TD> 20:18:    <TD> ` |- (. ( x e. A /\ -. x e. C ) ->. -. x e. C `
       ` ). `
       <TR> <TD> 21:18:    <TD> ` |- (. ( x e. A /\ -. x e. C ) ->. ( x e. A `
       ` \/ ( x e. B /\ -. x e. C ) ) ). `
       <TR> <TD> 22:21:    <TD> ` |- ( ( x e. A /\ -. x e. C ) -> ( x e. A \/ `
       ` ( x e. B /\ -. x e. C ) ) ) `
       <TR> <TD> 23::      <TD> ` |- (. ( x e. A /\ x e. A ) ->. ( x e. A /\ `
       ` x e. A ) ). `
       <TR> <TD> 24:23:    <TD> ` |- (. ( x e. A /\ x e. A ) ->. x e. A ). `
       <TR> <TD> 25:24:    <TD> ` |- (. ( x e. A /\ x e. A ) ->. ( x e. A \/ `
       ` ( x e. B /\ -. x e. C ) ) ). `
       <TR> <TD> 26:25:    <TD> ` |- ( ( x e. A /\ x e. A ) -> ( x e. A \/ ( `
       ` x e. B /\ -. x e. C ) ) ) `
       <TR> <TD> 27:10:    <TD> ` |- (. ( x e. B /\ -. x e. C ) ->. ( x e. A `
       ` \/ ( x e. B /\ -. x e. C ) ) ). `
       <TR> <TD> 28:27:    <TD> ` |- ( ( x e. B /\ -. x e. C ) -> ( x e. A \/ `
       ` ( x e. B /\ -. x e. C ) ) ) `
       <TR> <TD> 29::      <TD> ` |- (. ( x e. B /\ x e. A ) ->. ( x e. B /\ `
       ` x e. A ) ). `
       <TR> <TD> 30:29:    <TD> ` |- (. ( x e. B /\ x e. A ) ->. x e. A ). `
       <TR> <TD> 31:30:    <TD> ` |- (. ( x e. B /\ x e. A ) ->. ( x e. A \/ `
       ` ( x e. B /\ -. x e. C ) ) ). `
       <TR> <TD> 32:31:    <TD> ` |- ( ( x e. B /\ x e. A ) -> ( x e. A \/ ( `
       ` x e. B /\ -. x e. C ) ) ) `
       <TR> <TD> 33:22,26: <TD> ` |- ( ( ( x e. A /\ -. x e. C ) \/ ( x e. A `
       ` /\ x e. A ) ) -> ( x e. A \/ ( x e. B /\ -. x e. C ) ) ) `
       <TR> <TD> 34:28,32: <TD> ` |- ( ( ( x e. B /\ -. x e. C ) \/ ( x e. B `
       ` /\ x e. A ) ) -> ( x e. A \/ ( x e. B /\ -. x e. C ) ) ) `
       <TR> <TD> 35:33,34: <TD> ` |- ( ( ( ( x e. A /\ -. x e. C ) \/ ( x e. `
       ` A /\ x e. A ) ) \/ ( ( x e. B /\ -. x e. C ) \/ ( x e. B /\ x e. A ) )
       ) `
       ` -> ( x e. A \/ ( x e. B /\ -. x e. C ) ) ) `
       <TR> <TD> 36::      <TD> ` |- ( ( ( ( x e. A /\ -. x e. C ) \/ ( x e. `
       ` A /\ x e. A ) ) \/ ( ( x e. B /\ -. x e. C ) \/ ( x e. B /\ x e. A ) )
       ) `
       ` <-> ( ( x e. A \/ x e. B ) /\ ( -. x e. C \/ x e. A ) ) ) `
       <TR> <TD> 37:36,35: <TD> ` |- ( ( ( x e. A \/ x e. B ) /\ ( -. x e. C `
       ` \/ x e. A ) ) -> ( x e. A \/ ( x e. B /\ -. x e. C ) ) ) `
       <TR> <TD> 38:17,37: <TD> ` |- ( ( x e. A \/ ( x e. B /\ -. x e. C ) ) `
       ` <-> ( ( x e. A \/ x e. B ) /\ ( -. x e. C \/ x e. A ) ) ) `
       <TR> <TD> 39::      <TD> ` |- ( x e. ( C \ A ) <-> ( x e. C /\ -. x e. `
       ` A ) ) `
       <TR> <TD> 40:39:    <TD> ` |- ( -. x e. ( C \ A ) <-> -. ( x e. C /\ `
       ` -. x e. A ) ) `
       <TR> <TD> 41::      <TD> ` |- ( -. ( x e. C /\ -. x e. A ) <-> ( -. x `
       ` e. C \/ x e. A ) ) `
       <TR> <TD> 42:40,41: <TD> ` |- ( -. x e. ( C \ A ) <-> ( -. x e. C \/ x `
       ` e. A ) ) `
       <TR> <TD> 43::      <TD> ` |- ( x e. ( A u. B ) <-> ( x e. A \/ x e. B `
       ` ) ) `
       <TR> <TD> 44:43,42: <TD> ` |- ( ( x e. ( A u. B ) /\ -. x e. ( C \ A ) `
       ` ) <-> ( ( x e. A \/ x e. B ) /\ ( -. x e. C /\ x e. A ) ) ) `
       <TR> <TD> 45::      <TD> ` |- ( x e. ( ( A u. B ) \ ( C \ A ) ) <-> ( `
       ` x e. ( A u. B ) /\ -. x e. ( C \ A ) ) ) `
       <TR> <TD> 46:45,44: <TD> ` |- ( x e. ( ( A u. B ) \ ( C \ A ) ) <-> ( `
       ` ( x e. A \/ x e. B ) /\ ( -. x e. C \/ x e. A ) ) ) `
       <TR> <TD> 47:4,38:  <TD> ` |- ( x e. ( A u. ( B \ C ) ) <-> ( ( x e. A `
       ` \/ x e. B ) /\ ( -. x e. C \/ x e. A ) ) ) `
       <TR> <TD> 48:46,47: <TD> ` |- ( x e. ( A u. ( B \ C ) ) <-> x e. ( ( A `
       ` u. B ) \ ( C \ A ) ) ) `
       <TR> <TD> 49:48:    <TD> ` |- A. x ( x e. ( A u. ( B \ C ) ) <-> x e. `
       ` ( ( A u. B ) \ ( C \ A ) ) ) `
       <TR> <TD> qed:49:   <TD> ` |- ( A u. ( B \ C ) ) = ( ( A u. B ) \ ( C `
       ` \ A ) ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 17-Apr-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    undif3VD $p |- ( A u. ( B \ C ) ) = ( ( A u. B ) \ ( C \ A ) ) $=
      ( vx cdif cun wcel wo wn elun eldif bitri idn1 orc e1a olc in1 simpl jaoi
      wa cv wb wal wceq orbi2i pm3.2 e11 simpr bicomi orcd sylbir impbii notbii
      anddi pm4.53 anbi12i bitr4i ax-gen dfcleq biimpri e0a ) DUAZABCEZFZGZVBAB
      FZCAEZEZGZUBZDUCZVDVHUDZVJDVEVBAGZVBBGZHZVBCGZIZVMHZTZVIVEVMVNVQTZHZVSVEV
      MVBVCGZHWAVBAVCJWBVTVMVBBCKUELWAVSVMVSVTVMVSVMVOVRVSVMVMVOVMMZVMVNNOVMVMV
      RWCVMVQPOVOVRUFZUGQVTVSVTVOVRVSVTVNVOVTVTVNVTMZVNVQROVNVMPOVTVQVRVTVTVQWE
      VNVQUHOVQVMNOWDUGQSVSVMVQTZVMVMTZHZVTVNVMTZHZHZWAVSWKVMVNVQVMUNUIWHWAWJWF
      WAWGWFWAWFWFWAWFMWFVMVTVMVQRUJOQWGWAWGVMWAWGWGVMWGMVMVMROVMVTNZOQSVTWAWIV
      TWAVTVTWAWEVTVMPOQWIWAWIVMWAWIWIVMWIMVNVMUHOWLOQSSUKULLVIVBVFGZVBVGGZIZTV
      SVBVFVGKWMVOWOVRVBABJWOVPVMITZIVRWNWPVBCAKUMVPVMUOLUPLUQURVLVKDVDVHUSUTVA
      $.
  $}

  ${
    $d A y $.  $d B y $.  $d C y $.  $d D y $.  $d x y $.
    $( Virtual deduction proof of ~ sbcssg .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ sbcssg is ~ sbcssgVD without virtual deductions and was automatically
       derived from ~ sbcssgVD .
       <HTML> <TABLE>
       <TR> <TD> 1::       <TD> ` |- (. A e. B ->. A e. B ). `
       <TR> <TD> 2:1:      <TD> ` |- (. A e. B ->. ( [. A / x ]. y e. C <-> y `
       ` e. [_ A / x ]_ C ) ). `
       <TR> <TD> 3:1:      <TD> ` |- (. A e. B ->. ( [. A / x ]. y e. D <-> y `
       ` e. [_ A / x ]_ D ) ). `
       <TR> <TD> 4:2,3:    <TD> ` |- (. A e. B ->. ( ( [. A / x ]. y e. C -> `
       ` [. A / x ]. y e. D ) <-> ( y e. [_ A / x ]_ C -> y e. [_ A / x ]_ D `
       `  ) ) ). `
       <TR> <TD> 5:1:      <TD> ` |- (. A e. B ->. ( [. A / x ]. ( y e. C -> `
       ` y e. D ) <-> ( [. A / x ]. y e. C -> [. A / x ]. y e. D ) ) ). `
       <TR> <TD> 6:4,5:    <TD> ` |- (. A e. B ->. ( [. A / x ]. ( y e. C -> `
       ` y e. D ) <-> ( y e. [_ A / x ]_ C -> y e. [_ A / x ]_ D ) ) ). `
       <TR> <TD> 7:6:      <TD> ` |- (. A e. B ->. A. y ( [. A / x ]. ( y e. `
       ` C -> y e. D ) <-> ( y e. [_ A / x ]_ C -> y e. [_ A / x ]_ D ) ) ). `
       <TR> <TD> 8:7:      <TD> ` |- (. A e. B ->. ( A. y [. A / x ]. ( y e. `
       ` C -> y e. D ) <-> A. y ( y e. [_ A / x ]_ C -> y e. [_ A / x ]_ D ) `
       ` ) ). `
       <TR> <TD> 9:1:      <TD> ` |- (. A e. B ->. ( [. A / x ]. A. y ( y e. `
       ` C -> y e. D ) <-> A. y [. A / x ]. ( y e. C -> y e. D ) ) ). `
       <TR> <TD> 10:8,9:   <TD> ` |- (. A e. B ->. ( [. A / x ]. A. y ( y e. `
       ` C -> y e. D ) <-> A. y ( y e. [_ A / x ]_ C -> y e. [_ A / x ]_ D ) `
       ` ) ). `
       <TR> <TD> 11::      <TD> ` |- ( C C_ D <-> A. y ( y e. C -> y e. D ) ) `
       <TR> <TD> 110:11:   <TD> ` |- A. x ( C C_ D <-> A. y ( y e. C -> y e. `
       ` D ) ) `
       <TR> <TD> 12:1,110: <TD> ` |- (. A e. B ->. ( [. A / x ]. C C_ D <-> `
       ` [. A / x ]. A. y ( y e. C -> y e. D ) ) ). `
       <TR> <TD> 13:10,12: <TD> ` |- (. A e. B ->. ( [. A / x ]. C C_ D <-> `
       ` A. y ( y e. [_ A / x ]_ C -> y e. [_ A / x ]_ D ) ) ). `
       <TR> <TD> 14::      <TD> ` |- ( [_ A / x ]_ C C_ [_ A / x ]_ D <-> A. `
       ` y ( y e. [_ A / x ]_ C -> y e. [_ A / x ]_ D ) ) `
       <TR> <TD> 15:13,14: <TD> ` |- (. A e. B ->. ( [. A / x ]. C C_ D <-> `
       ` [_ A / x ]_ C C_ [_ A / x ]_ D ) ). `
       <TR> <TD> qed:15:   <TD> ` |- ( A e. B -> ( [. A / x ]. C C_ D <-> [_ `
       ` A / x ]_ C C_ [_ A / x ]_ D ) ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 22-Jul-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sbcssgVD $p |- ( A e. B -> ( [. A / x ]. C C_ D
          <-> [_ A / x ]_ C C_ [_ A / x ]_ D ) ) $=
      ( vy wcel wss wsbc csb wb wi wal sbcel2 a1i e1a e11 bibi1 biimprcd df-ss
      cv idn1 imbi12 sbcimg gen11 albi sbcal ax-gen sbcbi e10 biantr ex in1 ) B
      CGZDEHZABIZABDJZABEJZHZKZUNUPFUAZUQGZVAURGZLZFMZKZUSVEKZUTUNVADGZVAEGZLZF
      MZABIZVEKZUPVLKZVFUNVJABIZFMZVEKZVLVPKZVMUNVOVDKZFMVQUNVSFUNVHABIZVIABIZL
      ZVDKZVOWBKZVSUNVTVBKZWAVCKZWCUNUNWEUNUBZWEUNABVADNOPUNUNWFWGWFUNABVAENOPV
      TVBWAVCUCQUNUNWDWGVHVIABCUDPWDVSWCVOWBVDRSQUEVOVDFUFPUNUNVRWGVRUNVJFABUGO
      PVRVMVQVLVPVERSQUNUNUOVKKZAMVNWGWHAFDETUHUOVKABCUIUJVNVFVMUPVLVERSQFUQURT
      VFVGUTUPVEUSUKULUJUM $.
  $}

  ${
    $d A y $.  $d B y $.  $d C y $.  $d D y $.  $d x y $.
    $( Virtual deduction proof of ~ csbin .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ csbin is ~ csbingVD without virtual deductions and was
       automatically derived from ~ csbingVD .
       <HTML> <TABLE>
       <TR> <TD> 1::       <TD> ` |- (. A e. B ->. A e. B ). `
       <TR> <TD> 2::       <TD> ` |- ( C i^i D ) = { y | ( y e. C /\ y e. D ) `
       ` } `
       <TR> <TD> 20:2:     <TD> ` |- A. x ( C i^i D ) = { y | ( y e. C /\ y `
       ` e. D ) } `
       <TR> <TD> 30:1,20:  <TD> ` |- (. A e. B ->. [. A / x ]. ( C i^i D ) = `
       ` { y | ( y e. C /\ y e. D ) } ). `
       <TR> <TD> 3:1,30:   <TD> ` |- (. A e. B ->. [_ A / x ]_ ( C i^i D ) = `
       ` [_ A / x ]_ { y | ( y e. C /\ y e. D ) } ). `
       <TR> <TD> 4:1:      <TD> ` |- (. A e. B ->. [_ A / x ]_ { y | ( y e. C `
       ` /\ y e. D ) } = { y | [. A / x ]. ( y e. C /\ y e. D ) } ). `
       <TR> <TD> 5:3,4:    <TD> ` |- (. A e. B ->. [_ A / x ]_ ( C i^i D ) = `
       ` { y | [. A / x ]. ( y e. C /\ y e. D ) } ). `
       <TR> <TD> 6:1:      <TD> ` |- (. A e. B ->. ( [. A / x ]. y e. C <-> y `
       ` e. [_ A / x ]_ C ) ). `
       <TR> <TD> 7:1:      <TD> ` |- (. A e. B ->. ( [. A / x ]. y e. D <-> y `
       ` e. [_ A / x ]_ D ) ). `
       <TR> <TD> 8:6,7:    <TD> ` |- (. A e. B ->. ( ( [. A / x ]. y e. C /\ `
       ` [. A / x ]. y e. D ) <-> ( y e. [_ A / x ]_ C /\ y e. [_ A / x ]_ D `
       ` ) ) ). `
       <TR> <TD> 9:1:      <TD> ` |- (. A e. B ->. ( [. A / x ]. ( y e. C /\ `
       ` y e. D ) <-> ( [. A / x ]. y e. C /\ [. A / x ]. y e. D ) ) ). `
       <TR> <TD> 10:9,8:   <TD> ` |- (. A e. B ->. ( [. A / x ]. ( y e. C /\ `
       ` y e. D ) <-> ( y e. [_ A / x ]_ C /\ y e. [_ A / x ]_ D ) ) ). `
       <TR> <TD> 11:10:    <TD> ` |- (. A e. B ->. A. y ( [. A / x ]. ( y e. `
       ` C /\ y e. D ) <-> ( y e. [_ A / x ]_ C /\ y e. [_ A / x ]_ D ) ) ). `
       <TR> <TD> 12:11:    <TD> ` |- (. A e. B ->. { y | [. A / x ]. ( y e. C `
       ` /\ y e. D ) } = { y | ( y e. [_ A / x ]_ C /\ y e. [_ A / x ]_ D ) }
       ). `
       <TR> <TD> 13:5,12:  <TD> ` |- (. A e. B ->. [_ A / x ]_ ( C i^i D ) = `
       ` { y | ( y e. [_ A / x ]_ C /\ y e. [_ A / x ]_ D ) } ). `
       <TR> <TD> 14::      <TD> ` |- ( [_ A / x ]_ C i^i [_ A / x ]_ D ) = { `
       ` y | ( y e. [_ A / x ]_ C /\ y e. [_ A / x ]_ D ) } `
       <TR> <TD> 15:13,14: <TD> ` |- (. A e. B ->. [_ A / x ]_ ( C i^i D ) = `
       ` ( [_ A / x ]_ C i^i [_ A / x ]_ D ) ). `
       <TR> <TD> qed:15:   <TD> ` |- ( A e. B -> [_ A / x ]_ ( C i^i D ) = ( `
       ` [_ A / x ]_ C i^i [_ A / x ]_ D ) ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 22-Jul-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    csbingVD $p |- ( A e. B -> [_ A / x ]_ ( C i^i D ) =
                                       ( [_ A / x ]_ C i^i [_ A / x ]_ D ) ) $=
      ( vy wcel cin csb wceq wa cab wsbc wal df-in e11 a1i e1a biimprd wb spsbc
      cv idn1 ax-gen e10 sbceqg biimpd csbab eqeq1 sbcan sbcel2 pm4.38 ex bibi1
      gen11 abbib biimpri eqeq2 biimprcd in1 ) BCGZABDEHZIZABDIZABEIZHZJZVAVCFU
      BZVDGZVHVEGZKZFLZJZVFVLJZVGVAVCVHDGZVHEGZKZABMZFLZJZVSVLJZVMVAVCABVQFLZIZ
      JZWCVSJZVTVAVAVBWBJZABMZWDVAUCZVAVAWFANWGWHWFAFDEOUDWFABCUAUEVAWGWDABVBWB
      CUFUGPVAVAWEWHWEVAVQAFBUHQRWDVTWEVCWCVSUISPVAVRVKTZFNZWAVAWIFVAVRVOABMZVP
      ABMZKZTZWMVKTZWIVAVAWNWHWNVAVOVPABUJQRVAWKVITZWLVJTZWOVAVAWPWHWPVAABVHDUK
      QRVAVAWQWHWQVAABVHEUKQRWPWQWOWKWLVIVJULUMPWNWIWOVRWMVKUNSPUOWAWJVRVKFUPUQ
      RVTVMWAVCVSVLUISPFVDVEOVNVGVMVFVLVCURUSUEUT $.
  $}

  ${
    $d a b y $.  $d b x y $.
    $( Virtual deduction proof of ~ onfrALTlem5 .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ onfrALTlem5 is ~ onfrALTlem5VD without virtual deductions and was
       automatically derived from ~ onfrALTlem5VD .
       <HTML> <TABLE>
       <TR> <TD> 1::        <TD> ` |- a e. _V `
       <TR> <TD> 2:1:       <TD> ` |- ( a i^i x ) e. _V `
       <TR> <TD> 3:2:       <TD> ` |- ( [. ( a i^i x ) / b ]. b = (/) <-> ( a `
       ` i^i x ) = (/) ) `
       <TR> <TD> 4:3:       <TD> ` |- ( -. [. ( a i^i x ) / b ]. b = (/) <-> `
       ` -. ( a i^i x ) = (/) ) `
       <TR> <TD> 5::        <TD> ` |- ( ( a i^i x ) =/= (/) <-> -. ( a i^i x `
       ` ) = (/) ) `
       <TR> <TD> 6:4,5:     <TD> ` |- ( -. [. ( a i^i x ) / b ]. b = (/) <-> `
       ` ( a i^i x ) =/= (/) ) `
       <TR> <TD> 7:2:       <TD> ` |- ( -. [. ( a i^i x ) / b ]. b = (/) <-> `
       ` [. ( a i^i x ) / b ]. -. b = (/) ) `
       <TR> <TD> 8::        <TD> ` |- ( b =/= (/) <-> -. b = (/) ) `
       <TR> <TD> 9:8:       <TD> ` |- A. b ( b =/= (/) <-> -. b = (/) ) `
       <TR> <TD> 10:2,9:    <TD> ` |- ( [. ( a i^i x ) / b ]. b =/= (/) <-> `
       ` [. ( a i^i x ) / b ]. -. b = (/) ) `
       <TR> <TD> 11:7,10:   <TD> ` |- ( -. [. ( a i^i x ) / b ]. b = (/) <-> `
       ` [. ( a i^i x ) / b ]. b =/= (/) ) `
       <TR> <TD> 12:6,11:   <TD> ` |- ( [. ( a i^i x ) / b ]. b =/= (/) <-> ( `
       ` a i^i x ) =/= (/) ) `
       <TR> <TD> 13:2:      <TD> ` |- ( [. ( a i^i x ) / b ]. b C_ ( a i^i x `
       ` ) <-> ( a i^i x ) C_ ( a i^i x ) ) `
       <TR> <TD> 14:12,13:  <TD> ` |- ( ( [. ( a i^i x ) / b ]. b C_ ( a i^i `
       ` x ) /\ [. ( a i^i x ) / b ]. b =/= (/) ) <-> ( ( a i^i x ) C_ ( a `
       ` i^i x ) /\ ( a i^i x ) =/= (/) ) ) `
       <TR> <TD> 15:2:      <TD> ` |- ( [. ( a i^i x ) / b ]. ( b C_ ( a i^i `
       ` x ) /\ b =/= (/) ) <-> ( [. ( a i^i x ) / b ]. b C_ ( a i^i x ) /\ `
       ` [. ( a i^i x ) / b ]. b =/= (/) ) ) `
       <TR> <TD> 16:15,14:  <TD> ` |- ( [. ( a i^i x ) / b ]. ( b C_ ( a i^i `
       ` x ) /\ b =/= (/) ) <-> ( ( a i^i x ) C_ ( a i^i x ) /\ ( a i^i x ) `
       ` =/= (/) ) ) `
       <TR> <TD> 17:2:      <TD> ` |- [_ ( a i^i x ) / b ]_ ( b i^i y ) = ( `
       ` [_ ( a i^i x ) / b ]_ b i^i [_ ( a i^i x ) / b ]_ y ) `
       <TR> <TD> 18:2:      <TD> ` |- [_ ( a i^i x ) / b ]_ b = ( a i^i x ) `
       <TR> <TD> 19:2:      <TD> ` |- [_ ( a i^i x ) / b ]_ y = y `
       <TR> <TD> 20:18,19:  <TD> ` |- ( [_ ( a i^i x ) / b ]_ b i^i [_ ( a `
       ` i^i x ) / b ]_ y ) = ( ( a i^i x ) i^i y ) `
       <TR> <TD> 21:17,20:  <TD> ` |- [_ ( a i^i x ) / b ]_ ( b i^i y ) = ( ( `
       ` a i^i x ) i^i y ) `
       <TR> <TD> 22:2:      <TD> ` |- ( [. ( a i^i x ) / b ]. ( b i^i y ) = `
       ` (/) <-> [_ ( a i^i x ) / b ]_ ( b i^i y ) = [_ ( a i^i x ) / b ]_ `
       ` (/) ) `
       <TR> <TD> 23:2:      <TD> ` |- [_ ( a i^i x ) / b ]_ (/) = (/) `
       <TR> <TD> 24:21,23:  <TD> ` |- ( [_ ( a i^i x ) / b ]_ ( b i^i y ) = `
       ` [_ ( a i^i x ) / b ]_ (/) <-> ( ( a i^i x ) i^i y ) = (/) ) `
       <TR> <TD> 25:22,24:  <TD> ` |- ( [. ( a i^i x ) / b ]. ( b i^i y ) = `
       ` (/) <-> ( ( a i^i x ) i^i y ) = (/) ) `
       <TR> <TD> 26:2:      <TD> ` |- ( [. ( a i^i x ) / b ]. y e. b <-> y e. `
       ` ( a i^i x ) ) `
       <TR> <TD> 27:25,26:  <TD> ` |- ( ( [. ( a i^i x ) / b ]. y e. b /\ [. `
       ` ( a i^i x ) / b ]. ( b i^i y ) = (/) ) <-> ( y e. ( a i^i x ) /\ ( ( `
       ` a i^i x ) i^i y ) = (/) ) ) `
       <TR> <TD> 28:2:      <TD> ` |- ( [. ( a i^i x ) / b ]. ( y e. b /\ ( b `
       ` i^i y ) = (/) ) <-> ( [. ( a i^i x ) / b ]. y e. b /\ [. ( a i^i x ) `
       ` / b ]. ( b i^i y ) = (/) ) ) `
       <TR> <TD> 29:27,28:  <TD> ` |- ( [. ( a i^i x ) / b ]. ( y e. b /\ ( b `
       ` i^i y ) = (/) ) <-> ( y e. ( a i^i x ) /\ ( ( a i^i x ) i^i y ) = `
       ` (/) ) ) `
       <TR> <TD> 30:29:     <TD> ` |- A. y ( [. ( a i^i x ) / b ]. ( y e. b `
       ` /\ ( b i^i y ) = (/) ) <-> ( y e. ( a i^i x ) /\ ( ( a i^i x ) i^i `
       ` y ) = (/) ) ) `
       <TR> <TD> 31:30:     <TD> ` |- ( E. y [. ( a i^i x ) / b ]. ( y e. b `
       ` /\ ( b i^i y ) = (/) ) <-> E. y ( y e. ( a i^i x ) /\ ( ( a i^i x ) `
       ` i^i y ) = (/) ) ) `
       <TR> <TD> 32::       <TD> ` |- ( E. y e. ( a i^i x ) ( ( a i^i x ) i^i `
       ` y ) = (/) <-> E. y ( y e. ( a i^i x ) /\ ( ( a i^i x ) i^i y ) = (/) `
       ` ) ) `
       <TR> <TD> 33:31,32:  <TD> ` |- ( E. y [. ( a i^i x ) / b ]. ( y e. b `
       ` /\ ( b i^i y ) = (/) ) <-> E. y e. ( a i^i x ) ( ( a i^i x ) i^i y ) `
       ` = (/) ) `
       <TR> <TD> 34:2:      <TD> ` |- ( E. y [. ( a i^i x ) / b ]. ( y e. b `
       ` /\ ( b i^i y ) = (/) ) <-> [. ( a i^i x ) / b ]. E. y ( y e. b /\ ( `
       ` b i^i y ) = (/) ) ) `
       <TR> <TD> 35:33,34:  <TD> ` |- ( [. ( a i^i x ) / b ]. E. y ( y e. b `
       ` /\ ( b i^i y ) = (/) ) <-> E. y e. ( a i^i x ) ( ( a i^i x ) i^i y `
       ` ) = (/) ) `
       <TR> <TD> 36::       <TD> ` |- ( E. y e. b ( b i^i y ) = (/) <-> E. y `
       ` ( y e. b /\ ( b i^i y ) = (/) ) ) `
       <TR> <TD> 37:36:     <TD> ` |- A. b ( E. y e. b ( b i^i y ) = (/) <-> `
       ` E. y ( y e. b /\ ( b i^i y ) = (/) ) ) `
       <TR> <TD> 38:2,37:   <TD> ` |- ( [. ( a i^i x ) / b ]. E. y e. b ( b `
       ` i^i y ) = (/) <-> [. ( a i^i x ) / b ]. E. y ( y e. b /\ ( b i^i y ) `
       ` = (/) ) ) `
       <TR> <TD> 39:35,38:  <TD> ` |- ( [. ( a i^i x ) / b ]. E. y e. b ( b `
       ` i^i y ) = (/) <-> E. y e. ( a i^i x ) ( ( a i^i x ) i^i y ) = (/) ) `
       <TR> <TD> 40:16,39:  <TD> ` |- ( ( [. ( a i^i x ) / b ]. ( b C_ ( a `
       ` i^i x ) /\ b =/= (/) ) -> [. ( a i^i x ) / b ]. E. y e. b ( b i^i `
       ` y ) = (/) ) <-> ( ( ( a i^i x ) C_ ( a i^i x ) /\ ( a i^i x ) =/= `
       ` (/) ) -> E. y e. ( a i^i x ) ( ( a i^i x ) i^i y ) = (/) ) ) `
       <TR> <TD> 41:2:      <TD> ` |- ( [. ( a i^i x ) / b ]. ( ( b C_ ( a `
       ` i^i x ) /\ b =/= (/) ) -> E. y e. b ( b i^i y ) = (/) ) <-> ( [. ( a `
       ` i^i x ) / b ]. ( b C_ ( a i^i x ) /\ b =/= (/) ) -> [. ( a i^i x ) / `
       ` b ]. E. y e. b ( b i^i y ) = (/) ) ) `
       <TR> <TD> qed:40,41: <TD> ` |- ( [. ( a i^i x ) / b ]. ( ( b C_ ( a `
       ` i^i x ) /\ b =/= (/) ) -> E. y e. b ( b i^i y ) = (/) ) <-> ( ( ( a `
       ` i^i x ) C_ ( a i^i x ) /\ ( a i^i x ) =/= (/) ) -> E. y e. ( a i^i x `
       ` ) ( ( a i^i x ) i^i y ) = (/) ) ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 22-Jul-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    onfrALTlem5VD $p |- ( [. ( a i^i x ) / b ].
       ( ( b C_ ( a i^i x ) /\ b =/= (/) ) -> E. y e. b ( b i^i y ) = (/) ) <->
           ( ( ( a i^i x ) C_ ( a i^i x ) /\ ( a i^i x ) =/= (/) ) ->
                         E. y e. ( a i^i x ) ( ( a i^i x ) i^i y ) = (/) ) ) $=
      ( cv cin wss c0 wne wa wceq wi wsbc cvv wcel wb e0a bitri wex csb wrex wn
      vex inex1 sbcimg sbcan sseq1 sbcie df-ne sbcbii bicomd necon3bbii 3bitr2i
      sbcng eqsbc1 anbi12i df-rex sbcel2gv sbceqg csbin csbvarg csbconstg eqtri
      ineq12i csb0 eqeq12i exbii sbcex2 3bitr4i imbi12i ) DEZCEZAEZFZGZVKHIZJZV
      KBEZFZHKZBVKUAZLDVNMZVQDVNMZWADVNMZLZVNVNGZVNHIZJZVNVRFZHKZBVNUAZLVNNOZWB
      WEPVLVMCUCUDZVQWADVNNUEQWCWHWDWKWCVODVNMZVPDVNMZJWHVOVPDVNUFWNWFWOWGVOWFD
      VNWMVKVNVNUGUHWOVKHKZUBZDVNMZWPDVNMZUBZWGVPWQDVNVKHUIUJWLWTWRPWMWLWRWTWPD
      VNNUNUKQWSVNHWLWSVNHKPWMDVNHNUOQULUMUPRWDVRVKOZVTJZBSZDVNMZWKWAXCDVNVTBVK
      UQUJXBDVNMZBSVRVNOZWJJZBSXDWKXEXGBXEXADVNMZVTDVNMZJXGXAVTDVNUFXHXFXIWJWLX
      HXFPWMDVRVNNURQXIDVNVSTZDVNHTZKZWJWLXIXLPWMDVNVSHNUSQXJWIXKHXJDVNVKTZDVNV
      RTZFWIDVNVKVRUTXMVNXNVRWLXMVNKWMDVNNVAQWLXNVRKWMDVNVRNVBQVDVCDVNVEVFRUPRV
      GXBBDVNVHWJBVNUQVIRVJR $.
  $}

  ${
    $d a x $.
    $( Virtual deduction proof of ~ onfrALTlem4 .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ onfrALTlem4 is ~ onfrALTlem4VD without virtual deductions and was
       automatically derived from ~ onfrALTlem4VD .
       <HTML> <TABLE>
       <TR> <TD> 1::        <TD> ` |- y e. _V `
       <TR> <TD> 2:1:       <TD> ` |- ( [. y / x ]. ( a i^i x ) = (/) <-> [_ `
       ` y / x ]_ ( a i^i x ) = [_ y / x ]_ (/) ) `
       <TR> <TD> 3:1:       <TD> ` |- [_ y / x ]_ ( a i^i x ) = ( [_ y / x ]_ `
       ` a i^i [_ y / x ]_ x ) `
       <TR> <TD> 4:1:       <TD> ` |- [_ y / x ]_ a = a `
       <TR> <TD> 5:1:       <TD> ` |- [_ y / x ]_ x = y `
       <TR> <TD> 6:4,5:     <TD> ` |- ( [_ y / x ]_ a i^i [_ y / x ]_ x ) = ( `
       ` a i^i y ) `
       <TR> <TD> 7:3,6:     <TD> ` |- [_ y / x ]_ ( a i^i x ) = ( a i^i y ) `
       <TR> <TD> 8:1:       <TD> ` |- [_ y / x ]_ (/) = (/) `
       <TR> <TD> 9:7,8:     <TD> ` |- ( [_ y / x ]_ ( a i^i x ) = [_ y / x ]_ `
       ` (/) <-> ( a i^i y ) = (/) ) `
       <TR> <TD> 10:2,9:    <TD> ` |- ( [. y / x ]. ( a i^i x ) = (/) <-> ( a `
       ` i^i y ) = (/) ) `
       <TR> <TD> 11:1:      <TD> ` |- ( [. y / x ]. x e. a <-> y e. a ) `
       <TR> <TD> 12:11,10:  <TD> ` |- ( ( [. y / x ]. x e. a /\ [. y / x ]. ( `
       ` a i^i x ) = (/) )  <-> ( y e. a /\ ( a i^i y ) = (/) ) ) `
       <TR> <TD> 13:1:      <TD> ` |- ( [. y / x ]. ( x e. a /\ ( a i^i x ) = `
       ` (/) ) <-> ( [. y / x ]. x e. a /\ [. y / x ]. ( a i^i x ) = (/) ) ) `
       <TR> <TD> qed:13,12: <TD> ` |- ( [. y / x ]. ( x e. a /\ ( a i^i x ) = `
       ` (/) ) <-> ( y e. a /\ ( a i^i y ) = (/) ) ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 22-Jul-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    onfrALTlem4VD $p |- ( [. y / x ]. ( x e. a /\ ( a i^i x ) = (/) ) <->
                                           ( y e. a /\ ( a i^i y ) = (/) ) ) $=
      ( wel cv cin c0 wceq wa wsbc sbcan sbcel1v csb cvv sbceqg csbin csbconstg
      wb elv bitri vex csbvargi ineq12i eqtri csb0 eqeq12i anbi12i ) ACDZCEZAEZ
      FZGHZIABEZJUHAUMJZULAUMJZIBCDZUIUMFZGHZIUHULAUMKUNUPUOURAUMUILUOAUMUKMZAU
      MGMZHZURUOVARBAUMUKGNOSUSUQUTGUSAUMUIMZAUMUJMZFUQAUMUIUJPVBUIVCUMVBUIHBAU
      MUINQSAUMBUAUBUCUDAUMUEUFTUGT $.
  $}

  ${
    $d a b y $.  $d b x y $.
    $( Virtual deduction proof of ~ onfrALTlem3 .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ onfrALTlem3 is ~ onfrALTlem3VD without virtual deductions and was
       automatically derived from ~ onfrALTlem3VD .
       <HTML> <TABLE>
       <TR> <TD> 1::          <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ->. ( a `
       ` C_ On /\ a =/= (/) ) ). `
       <TR> <TD> 2::          <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. ( x e. a /\ -. ( a i^i x ) = (/) ) ).
       `
       <TR> <TD> 3:2:         <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. x e. a ). `
       <TR> <TD> 4:1:         <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ->. a C_ `
       ` On ). `
       <TR> <TD> 5:3,4:       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. x e. On ). `
       <TR> <TD> 6:5:         <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. Ord x ). `
       <TR> <TD> 7:6:         <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. _E We x ). `
       <TR> <TD> 8::          <TD> ` |- ( a i^i x ) C_ x `
       <TR> <TD> 9:7,8:       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. _E We ( a i^i x ) ). `
       <TR> <TD> 10:9:        <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. _E Fr ( a i^i x ) ). `
       <TR> <TD> 11:10:       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. A. b ( ( b C_ ( a i^i x ) /\ b =/= `
       ` (/) ) -> E. y e. b ( b i^i y ) = (/) ) ). `
       <TR> <TD> 12::         <TD> ` |- x e. _V `
       <TR> <TD> 13:12,8:     <TD> ` |- ( a i^i x ) e. _V `
       <TR> <TD> 14:13,11:    <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. [. ( a i^i x ) / b ]. ( ( b C_ ( a `
       ` i^i x ) /\ b =/= (/) ) -> E. y e. b ( b i^i y ) = (/) ) ). `
       <TR> <TD> 15::         <TD> ` |- ( [. ( a i^i x ) / b ]. ( ( b C_ ( a `
       ` i^i x ) /\ b =/= (/) ) -> E. y e. b ( b i^i y ) = (/) ) <-> ( ( ( a
       i^i `
       ` x ) C_ ( a i^i x ) /\ ( a i^i x ) =/= (/) ) -> E. y e. ( a i^i x ) ( `
       ` ( a i^i x ) i^i y ) = (/) ) ) `
       <TR> <TD> 16:14,15:    <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. ( ( ( a i^i x ) C_ ( a i^i x ) /\ ( `
       ` a i^i x ) =/= (/) ) -> E. y e. ( a i^i x ) ( ( a i^i x ) i^i y ) = `
       ` (/) ) ). `
       <TR> <TD> 17::         <TD> ` |- ( a i^i x ) C_ ( a i^i x ) `
       <TR> <TD> 18:2:        <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. -. ( a i^i x ) = (/) ). `
       <TR> <TD> 19:18:       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. ( a i^i x ) =/= (/) ). `
       <TR> <TD> 20:17,19:    <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. ( ( a i^i x ) C_ ( a i^i x ) /\ ( a
       i^i `
       ` x ) =/= (/) ) ). `
       <TR> <TD> qed:16,20:   <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. E. y e. ( a i^i x ) ( ( a i^i x ) i^i
       y `
       ` ) = (/) ). `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 22-Jul-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    onfrALTlem3VD $p |- (. ( a C_ On /\ a =/= (/) ) ,.
                         ( x e. a /\ -. ( a i^i x ) = (/) ) ->.
                          E. y e. ( a i^i x ) ( ( a i^i x ) i^i y ) = (/) ). $=
      ( vb cv con0 wss c0 wne wa wcel cin wceq wrex wi cvv cep wwe simpl e2 wal
      wn wsbc vex inss2 ssexi wfr word idn2 idn1 e1a ssel com12 e21 eloni ordwe
      wess e20 wefr dfepfr biimpi spsbc e02 onfrALTlem5 e2bi ssid simpr biimpri
      df-ne pm3.2 id e22 ) CEZFGZVMHIZJZAEZVMKZVMVQLZHMUBZJZVSVSGZVSHIZJZVSBEZL
      HMBVSNZOZWDWFVPWADEZVSGWHHIJWHWELHMBWHNOZDVSUCZWGVSPKVPWAWIDUAZWJVSVQAUDV
      MVQUEZUFVPWAVSQUGZWKVPWAVSQRZWMVPWAVQQRZVSVQGZWNVPWAVQUHZWOVPWAVQFKZWQVPW
      AVRVNWRVPWAWAVRVPWAUIZVRVTSTVPVPVNVPUJVNVOSUKVNVRWRVMFVQULUMUNVQUOTVQUPTW
      LWPWOWNVSVQQUQUMURVSQUSTWMWKDBVSUTVATWIDVSPVBVCABCDVDVEWBVPWAWCWDVSVFVPWA
      VTWCVPWAWAVTWSVRVTVGTWCVTVSHVIVHTWBWCVJVCWGVKVL $.
  $}

  $( Virtual deduction proof of ~ simplbi2comt .
     The following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
     ~ simplbi2comt is ~ simplbi2comtVD without virtual deductions and was
     automatically derived from ~ simplbi2comtVD .
     <HTML> <TABLE>
     <TR> <TD> 1::    <TD> ` |- (. ( ph <-> ( ps /\ ch ) ) ->. ( ph <-> ( `
     ` ps /\ ch ) ) ). `
     <TR> <TD> 2:1:   <TD> ` |- (. ( ph <-> ( ps /\ ch ) ) ->. ( ( ps /\ ch `
     ` ) -> ph ) ). `
     <TR> <TD> 3:2:   <TD> ` |- (. ( ph <-> ( ps /\ ch ) ) ->. ( ps -> ( ch `
     ` -> ph ) ) ). `
     <TR> <TD> 4:3:   <TD> ` |- (. ( ph <-> ( ps /\ ch ) ) ->. ( ch -> ( ps `
     ` -> ph ) ) ). `
     <TR> <TD> qed:4: <TD> ` |- ( ( ph <-> ( ps /\ ch ) ) -> ( ch -> ( ps `
     ` -> ph ) ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 22-Jul-2012.)  (Proof modification is
     discouraged.)  (New usage is discouraged.) $)
  simplbi2comtVD $p |- ( ( ph <-> ( ps /\ ch ) ) -> ( ch -> ( ps -> ph ) ) ) $=
    ( wa wb wi idn1 biimpr e1a pm3.3 pm2.04 in1 ) ABCDZEZCBAFFZNBCAFFZONMAFZPNN
    QNGAMHIBCAJIBCAKIL $.

  ${
    $d a y z $.  $d x y z $.
    $( Virtual deduction proof of ~ onfrALTlem2 .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ onfrALTlem2 is ~ onfrALTlem2VD without virtual deductions and was
       automatically derived from ~ onfrALTlem2VD .
       <HTML> <TABLE>
       <TR> <TD> 1::          <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( ( y e. ( a i^i x ) /\ ( ( a i^i x )
       i^i `
       ` y ) = (/) ) /\ z e. ( a i^i y ) ) ->. ( ( y e. ( a i^i x ) /\ ( ( a
       i^i `
       ` x ) i^i y ) = (/) ) /\ z e. ( a i^i y ) ) ). `
       <TR> <TD> 2:1:         <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( ( y e. ( a i^i x ) /\ ( ( a i^i x )
       i^i `
       ` y ) = (/) ) /\ z e. ( a i^i y ) ) ->. z e. ( a i^i y ) ). `
       <TR> <TD> 3:2:         <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( ( y e. ( a i^i x ) /\ ( ( a i^i x )
       i^i `
       ` y ) = (/) ) /\ z e. ( a i^i y ) ) ->. z e. a ). `
       <TR> <TD> 4::          <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ->. ( a `
       ` C_ On /\ a =/= (/) ) ). `
       <TR> <TD> 5::          <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. ( x e. a /\ -. ( a i^i x ) = (/) ) ).
       `
       <TR> <TD> 6:5:         <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. x e. a ). `
       <TR> <TD> 7:4:         <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ->. a C_ `
       ` On ). `
       <TR> <TD> 8:6,7:       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. x e. On ). `
       <TR> <TD> 9:8:         <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. Ord x ). `
       <TR> <TD> 10:9:        <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. Tr x ). `
       <TR> <TD> 11:1:        <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( ( y e. ( a i^i x ) /\ ( ( a i^i x )
       i^i `
       ` y ) = (/) ) /\ z e. ( a i^i y ) ) ->.  y e. ( a i^i x ) ). `
       <TR> <TD> 12:11:       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( ( y e. ( a i^i x ) /\ ( ( a i^i x )
       i^i `
       ` y ) = (/) ) /\ z e. ( a i^i y ) ) ->. y e. x ). `
       <TR> <TD> 13:2:        <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( ( y e. ( a i^i x ) /\ ( ( a i^i x )
       i^i `
       ` y ) = (/) ) /\ z e. ( a i^i y ) ) ->. z e. y ). `
       <TR> <TD> 14:10,12,13: <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( ( y e. ( a i^i x ) /\ ( ( a i^i x )
       i^i `
       ` y ) = (/) ) /\ z e. ( a i^i y ) ) ->. z e. x ). `
       <TR> <TD> 15:3,14:     <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( ( y e. ( a i^i x ) /\ ( ( a i^i x )
       i^i `
       ` y ) = (/) ) /\ z e. ( a i^i y ) ) ->. z e. ( a i^i x ) ). `
       <TR> <TD> 16:13,15:    <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( ( y e. ( a i^i x ) /\ ( ( a i^i x )
       i^i `
       ` y ) = (/) ) /\ z e. ( a i^i y ) ) ->. z e. ( ( a i^i x ) i^i y ) ). `
       <TR> <TD> 17:16:       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( y e. ( a i^i x ) /\ ( ( a i^i x ) i^i
       y `
       ` ) = (/) ) ->. ( z e. ( a i^i y ) -> z e. ( ( a i^i x ) i^i y ) ) ). `
       <TR> <TD> 18:17:       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( y e. ( a i^i x ) /\ ( ( a i^i x ) i^i
       y `
       ` ) = (/) ) ->. A. z ( z e. ( a i^i y ) -> z e. ( ( a i^i x ) i^i y ) )
       ). `
       <TR> <TD> 19:18:       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( y e. ( a i^i x ) /\ ( ( a i^i x ) i^i
       y `
       ` ) = (/) ) ->. ( a i^i y ) C_ ( ( a i^i x ) i^i y ) ). `
       <TR> <TD> 20::         <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( y e. ( a i^i x ) /\ ( ( a i^i x ) i^i
       y `
       ` ) = (/) ) ->. ( y e. ( a i^i x ) /\ ( ( a i^i x ) i^i y ) = (/) ) ). `
       <TR> <TD> 21:20:       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( y e. ( a i^i x ) /\ ( ( a i^i x ) i^i
       y `
       ` ) = (/) ) ->. ( ( a i^i x ) i^i y ) = (/) ). `
       <TR> <TD> 22:19,21:    <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( y e. ( a i^i x ) /\ ( ( a i^i x ) i^i
       y `
       ` ) = (/) ) ->. ( a i^i y ) = (/) ). `
       <TR> <TD> 23:20:       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( y e. ( a i^i x ) /\ ( ( a i^i x ) i^i
       y `
       ` ) = (/) ) ->. y e. ( a i^i x ) ). `
       <TR> <TD> 24:23:       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( y e. ( a i^i x ) /\ ( ( a i^i x ) i^i
       y `
       ` ) = (/) ) ->. y e. a ). `
       <TR> <TD> 25:22,24:    <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) , ( y e. ( a i^i x ) /\ ( ( a i^i x ) i^i
       y `
       ` ) = (/) ) ->. ( y e. a /\ ( a i^i y ) = (/) ) ). `
       <TR> <TD> 26:25:       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. ( ( y e. ( a i^i x ) /\ ( ( a i^i x )
       `
       ` i^i y ) = (/) ) -> ( y e. a /\ ( a i^i y ) = (/) ) ) ). `
       <TR> <TD> 27:26:       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. A. y ( ( y e. ( a i^i x ) /\ ( ( a i^i
       x `
       ` ) i^i y ) = (/) ) -> ( y e. a /\ ( a i^i y ) = (/) ) ) ). `
       <TR> <TD> 28:27:       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. ( E. y ( y e. ( a i^i x ) /\ ( ( a i^i
       x `
       ` ) i^i y ) = (/) ) -> E. y ( y e. a /\ ( a i^i y ) = (/) ) ) ). `
       <TR> <TD> 29::         <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. E. y e. ( a i^i x ) ( ( a i^i x ) i^i
       y `
       ` ) = (/) ). `
       <TR> <TD> 30:29:       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. E. y ( y e. ( a i^i x ) /\ ( ( a i^i x
       ) `
       ` i^i y ) = (/) ) ). `
       <TR> <TD> 31:28,30:    <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. E. y ( y e. a /\ ( a i^i y ) = (/) )
       ). `
       <TR> <TD> qed:31:      <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. `
       ` a /\ -. ( a i^i x ) = (/) ) ->. E. y e. a ( a i^i y ) = (/) ). `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 22-Jul-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    onfrALTlem2VD $p |- (. ( a C_ On /\ a =/= (/) ) ,.
       ( x e. a /\ -. ( a i^i x ) = (/) ) ->. E. y e. a ( a i^i y ) = (/) ). $=
      ( vz cv con0 wss c0 wa wcel cin wceq wex wrex wi e3 sseli simpl e2 e33 wn
      wne wal idn3 simpr inss2 inss1 wtr word idn2 idn1 ssel com12 eloni simpll
      e1a ordtr trel expcomd e233 elin simplbi2 simplbi2com in3an gen31 biimpri
      e21 df-ss sseq0 ex pm3.21 in3 gen21 exim onfrALTlem3VD df-rex biimpi e22
      id ) CEZFGZVTHUBZIZAEZVTJZVTWDKZHLUAZIZBEZVTJZVTWIKZHLZIZBMZWLBVTNZWCWHWI
      WFJZWFWIKZHLZIZBMZWNOZWTWNWCWHWSWMOZBUCXAWCWHXBBWCWHWSWMWCWHWSWLWJWMWCWHW
      SWKWQGZWRWLWCWHWSDEZWKJZXDWQJZOZDUCZXCWCWHWSXGDWCWHWSXEXFWCWHWSXEIZXDWIJZ
      XDWFJZXFWCWHXIXEXJWCWHXIXIXEWCWHXIUDZWSXEUEPZWKWIXDVTWIUFQPZWCWHXIXDVTJZX
      DWDJZXKWCWHXIXEXOXMWKVTXDVTWIUGQPWCWHWDUHZXIWIWDJZXJXPWCWHWDUIZXQWCWHWDFJ
      ZXSWCWHWEWAXTWCWHWHWEWCWHUJWEWGRSWCWCWAWCUKWAWBRUPWAWEXTVTFWDULUMVGWDUNSW
      DUQSWCWHXIWPXRWCWHXIXIWPXLWPWRXEUOPWFWDWIVTWDUFQPXNXQXJXRXPWDXDWIURUSUTXK
      XOXPXDVTWDVAVBTXFXKXJXDWFWIVAVCTVDVEXCXHDWKWQVHVFPWCWHWSWSWRWCWHWSUDZWPWR
      UEPXCWRWLWKWQVIVJTWCWHWSWPWJWCWHWSWSWPYAWPWRRPWFVTWIVTWDUGQPWLWJVKTVLVMWS
      WMBVNSWCWHWRBWFNZWTABCVOYBWTWRBWFVPVQSXAVSVRWOWNWLBVTVPVFS $.
  $}

  ${
    $d a x y $.
    $( Virtual deduction proof of ~ onfrALTlem1 .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ onfrALTlem1 is ~ onfrALTlem1VD without virtual deductions and was
       automatically derived from ~ onfrALTlem1VD .
       <HTML> <TABLE>
       <TR> <TD> 1::      <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. a /\
       `
       ` ( a i^i x ) = (/) ) ->. ( x e. a /\ ( a i^i x ) = (/) ) ). `
       <TR> <TD> 2:1:     <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. a /\
       `
       ` ( a i^i x ) = (/) ) ->. E. x ( x e. a /\ ( a i^i x ) = (/) ) ). `
       <TR> <TD> 3:2:     <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. a /\
       `
       ` ( a i^i x ) = (/) ) ->. E. y [ y / x ] ( x e. a /\ ( a i^i x ) = (/) )
       `
       ` ). `
       <TR> <TD> 4::      <TD> ` |- ( [ y / x ] ( x e. a /\ ( a i^i x ) = (/) `
       ` ) <-> ( y e. a /\ ( a i^i y ) = (/) ) ) `
       <TR> <TD> 5:4:     <TD> ` |- A. y ( [ y / x ] ( x e. a /\ ( a i^i x ) `
       ` = (/) ) <-> ( y e. a /\ ( a i^i y ) = (/) ) ) `
       <TR> <TD> 6:5:     <TD> ` |- ( E. y [ y / x ] ( x e. a /\ ( a i^i x ) `
       ` = (/) ) <-> E. y ( y e. a /\ ( a i^i y ) = (/) ) ) `
       <TR> <TD> 7:3,6:   <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. a /\
       `
       ` ( a i^i x ) = (/) ) ->. E. y ( y e. a /\ ( a i^i y ) = (/) ) ). `
       <TR> <TD> 8::      <TD> ` |- ( E. y e. a ( a i^i y ) = (/) <-> E. y ( `
       ` y e. a /\ ( a i^i y ) = (/) ) ) `
       <TR> <TD> qed:7,8: <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. a /\
       `
       ` ( a i^i x ) = (/) ) ->. E. y e. a ( a i^i y ) = (/) ). `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 22-Jul-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    onfrALTlem1VD $p |- (. ( a C_ On /\ a =/= (/) ) ,.
          ( x e. a /\ ( a i^i x ) = (/) ) ->. E. y e. a ( a i^i y ) = (/) ). $=
      ( cv con0 wss c0 wne wa wcel cin wceq wex wrex wsb idn2 19.8a e2 cbvexsv
      wb biimpi wal wsbc sbsbc onfrALTlem4 bitri ax-gen exbi e2bi df-rex e2bir
      e0a ) CDZEFUMGHIZADZUMJUMUOKGLIZBDZUMJUMUQKGLZIZBMZURBUMNUNUPUPABOZBMZUTU
      NUPUPAMZVBUNUPUPVCUNUPPUPAQRVCVBUPABSUARVAUSTZBUBVBUTTVDBVAUPAUQUCUSUPABU
      DABCUEUFUGVAUSBUHULUIURBUMUJUK $.
  $}

  ${
    $d a x y $.
    $( Virtual deduction proof of ~ onfrALT .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ onfrALT is ~ onfrALTVD without virtual deductions and was
       automatically derived from ~ onfrALTVD .
       <HTML> <TABLE>
       <TR> <TD> 1::       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. a `
       ` /\ -. ( a i^i x ) = (/) ) ->. E. y e. a ( a i^i y ) = (/) ). `
       <TR> <TD> 2::       <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. a `
       ` /\ ( a i^i x ) = (/) ) ->. E. y e. a ( a i^i y ) = (/) ). `
       <TR> <TD> 3:1:      <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. x e. a ->.
       `
       ` ( -. ( a i^i x ) = (/) -> E. y e. a ( a i^i y ) = (/) ) ). `
       <TR> <TD> 4:2:      <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. x e. a ->.
       `
       ` ( ( a i^i x ) = (/) -> E. y e. a ( a i^i y ) = (/) ) ). `
       <TR> <TD> 5::       <TD> ` |- ( ( a i^i x ) = (/) \/ -. ( a i^i x ) = `
       ` (/) ) `
       <TR> <TD> 6:5,4,3:  <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ,. x e. a ->.
       `
       ` E. y e. a ( a i^i y ) = (/) ). `
       <TR> <TD> 7:6:      <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ->. ( x e. a `
       ` -> E. y e. a ( a i^i y ) = (/) ) ). `
       <TR> <TD> 8:7:      <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ->. A. x ( x `
       ` e. a -> E. y e. a ( a i^i y ) = (/) ) ). `
       <TR> <TD> 9:8:      <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ->. ( E. x x `
       ` e. a -> E. y e. a ( a i^i y ) = (/) ) ). `
       <TR> <TD> 10::      <TD> ` |- ( a =/= (/) <-> E. x x e. a ) `
       <TR> <TD> 11:9,10:  <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ->. ( a =/= `
       ` (/) -> E. y e. a ( a i^i y ) = (/) ) ). `
       <TR> <TD> 12::      <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ->. ( a C_ `
       ` On /\ a =/= (/) ) ). `
       <TR> <TD> 13:12:    <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ->. a =/= `
       ` (/) ). `
       <TR> <TD> 14:13,11: <TD> ` |- (. ( a C_ On /\ a =/= (/) ) ->. E. y e. `
       ` a ( a i^i y ) = (/) ). `
       <TR> <TD> 15:14:    <TD> ` |- ( ( a C_ On /\ a =/= (/) ) -> E. y e. a `
       ` ( a i^i y ) = (/) ) `
       <TR> <TD> 16:15:    <TD> ` |- A. a ( ( a C_ On /\ a =/= (/) ) -> E. y `
       ` e. a ( a i^i y ) = (/) ) `
       <TR> <TD> qed:16:   <TD> ` |- _E Fr On `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 22-Jul-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    onfrALTVD $p |- _E Fr On $=
      ( va vy vx cv con0 wss c0 wne wa cin wceq wrex wal cep wfr idn1 simpr e1a
      wi in2an wcel wex wb wn exmid onfrALTlem1VD onfrALTlem2VD pm2.61 a1i e022
      wo in2 gen11 19.23v biimpi n0 imbi1 biimprcd e10 pm2.27 e11 ax-gen dfepfr
      in1 biimpri e0a ) ADZEFZVGGHZIZVGBDJGKBVGLZSZAMZENOZVLAVJVKVJVIVIVKSZVKVJ
      VJVIVJPVHVIQRVJCDZVGUAZCUBZVKSZVIVRUCZVOVJVQVKSZCMZVSVJWACVJVQVKVGVPJGKZW
      CUDZUKZVJVQWCVKSZWDVKSZVKWCUEVJVQWCVKCBAUFTVJVQWDVKCBAUGTWFWGVKSSWEWCVKUH
      UIUJULUMWBVSVQVKCUNUORCVGUPVTVOVSVIVRVKUQURUSVIVKUTVAVDVBVNVMABEVCVEVF $.
  $}

  $( Virtual deduction proof of ~ csbeq2 .
     The following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
     ~ csbeq2 is ~ csbeq2gVD without virtual deductions and was
     automatically derived from ~ csbeq2gVD .
     <HTML> <TABLE>
     <TR> <TD> 1::       <TD> ` |- (. A e. V ->. A e. V  ). `
     <TR> <TD> 2:1:      <TD> ` |- (. A e. V ->. ( A. x B = C -> [. A / x ]. `
     ` B = C ) ). `
     <TR> <TD> 3:1:      <TD> ` |- (. A e. V ->. ( [. A / x ]. B = C <-> [_ A `
     ` / x ]_ B = [_ A / x ]_ C ) ). `
     <TR> <TD> 4:2,3:    <TD> ` |- (. A e. V ->. ( A. x B = C -> [_ A / x `
     ` ]_ B = [_ A / x ]_ C ) ). `
     <TR> <TD> qed:4:    <TD> ` |- ( A e. V -> ( A. x B = C -> [_ A / x ]_ `
     ` B = [_ A / x ]_ C ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 10-Nov-2012.)  (Proof modification is
     discouraged.)  (New usage is discouraged.) $)
  csbeq2gVD $p |- ( A e. V -> ( A. x B = C ->
                                           [_ A / x ]_ B = [_ A / x ]_ C ) ) $=
    ( wcel wceq wal csb wi wsbc wb idn1 spsbc e1a sbceqg imbi2 biimpcd e11 in1
    ) BEFZCDGZAHZABCIABDIGZJZUAUCUBABKZJZUFUDLZUEUAUAUGUAMZUBABENOUAUAUHUIABCDE
    POUHUGUEUFUDUCQRST $.

  ${
    $d A y $.  $d B y $.  $d V y $.  $d x y $.
    $( Virtual deduction proof of ~ csbsng .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ csbsng is ~ csbsngVD without virtual deductions and was automatically
       derived from ~ csbsngVD .
       <HTML> <TABLE>
       <TR> <TD> 1::           <TD> ` |- (. A e. V ->. A e. V ). `
       <TR> <TD> 2:1:          <TD> ` |- (. A e. V ->. ( [. A / x ]. y = B `
       ` <-> [_ A / x ]_ y = [_ A / x ]_ B ) ). `
       <TR> <TD> 3:1:          <TD> ` |- (. A e. V ->. [_ A / x ]_ y = y ). `
       <TR> <TD> 4:3:          <TD> ` |- (. A e. V ->. ( [_ A / x ]_ y = [_ A `
       ` / x ]_ B <-> y = [_ A / x ]_ B ) ). `
       <TR> <TD> 5:2,4:        <TD> ` |- (. A e. V ->. ( [. A / x ]. y = B `
       ` <-> y = [_ A / x ]_ B ) ). `
       <TR> <TD> 6:5:          <TD> ` |- (. A e. V ->. A. y ( [. A / x ]. y `
       ` = B <-> y = [_ A / x ]_ B ) ). `
       <TR> <TD> 7:6:          <TD> ` |- (. A e. V ->. { y | [. A / x ]. y = `
       ` B } = { y | y = [_ A / x ]_ B } ). `
       <TR> <TD> 8:1:          <TD> ` |- (. A e. V ->. { y | [. A / x ]. y = `
       ` B } = [_ A / x ]_ { y |  y = B } ). `
       <TR> <TD> 9:7,8:        <TD> ` |- (. A e. V ->. [_ A / x ]_ { y |  y `
       ` = B } = { y | y = [_ A / x ]_ B } ). `
       <TR> <TD> 10::          <TD> ` |- { B } = { y |  y = B } `
       <TR> <TD> 11:10:        <TD> ` |- A. x { B } = { y |  y = B } `
       <TR> <TD> 12:1,11:      <TD> ` |- (. A e. V ->. [_ A / x ]_ { B } = [_ `
       ` A / x ]_ { y |  y = B } ). `
       <TR> <TD> 13:9,12:      <TD> ` |- (. A e. V ->. [_ A / x ]_ { B } = { `
       ` y | y = [_ A / x ]_ B } ). `
       <TR> <TD> 14::          <TD> ` |- { [_ A / x ]_  B } = { y |  y = [_ A `
       ` / x ]_ B } `
       <TR> <TD> 15:13,14:     <TD> ` |- (. A e. V ->. [_ A / x ]_ { B } = { `
       ` [_ A / x ]_ B } ). `
       <TR> <TD> qed:15:       <TD> ` |- ( A e. V -> [_ A / x ]_ { B } = { [_ `
       ` A / x ]_ B } ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 10-Nov-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    csbsngVD $p |- ( A e. V -> [_ A / x ]_ { B } = { [_ A / x ]_ B } ) $=
      ( vy wcel csn csb wceq cv cab wb wal e1a eqeq1 e11 a1i df-sn e10 eqeq2 wi
      wsbc idn1 sbceqg csbconstg bibi1 biimprd gen11 abbib biimpri csbab eqcomd
      biimpcd ax-gen csbeq2 biimpd biimprcd in1 ) BDFZABCGZHZABCHZGZIZUSVAEJZVB
      IZEKZIZVCVGIZVDUSABVECIZEKZHZVGIZVAVLIZVHUSVJABUBZEKZVGIZVPVLIZVMUSVOVFLZ
      EMZVQUSVSEUSVOABVEHZVBIZLZWBVFLZVSUSUSWCUSUCZABVECDUDNUSWAVEIZWDUSUSWFWEA
      BVEDUENWAVEVBONWCVSWDVOWBVFUFUGPUHVQVTVOVFEUIUJNUSUSVRWEUSVLVPVLVPIUSVJAE
      BUKQULNVRVQVMVPVLVGOUMPUSUSUTVKIZAMZVNWEWGAECRUNWHVNUAUSABUTVKUOQSVMVNVHV
      LVGVATUPPEVBRVIVDVHVCVGVATUQSUR $.
  $}

  ${
    $d A w y z $.  $d B w y z $.  $d C w y z $.  $d V w y z $.  $d w x y z $.
    $( Virtual deduction proof of ~ csbxp .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ csbxp is ~ csbxpgVD without virtual deductions and was
       automatically derived from ~ csbxpgVD .
       <HTML> <TABLE>
       <TR> <TD> 1::       <TD> ` |- (. A e. V ->. A e. V ). `
       <TR> <TD> 2:1:      <TD> ` |- (. A e. V ->. ( [. A / x ]. w e. B <-> `
       ` [_ A / x ]_ w e. [_ A / x ]_ B ) ). `
       <TR> <TD> 3:1:      <TD> ` |- (. A e. V ->. [_ A / x ]_ w = w ). `
       <TR> <TD> 4:3:      <TD> ` |- (. A e. V ->. ( [_ A / x ]_ w e. [_ A / `
       ` x ]_ B <-> w e. [_ A / x ]_ B ) ). `
       <TR> <TD> 5:2,4:    <TD> ` |- (. A e. V ->. ( [. A / x ]. w e. B <-> w `
       ` e. [_ A / x ]_ B ) ). `
       <TR> <TD> 6:1:      <TD> ` |- (. A e. V ->. ( [. A / x ]. y e. C <-> `
       ` [_ A / x ]_ y e. [_ A / x ]_ C ) ). `
       <TR> <TD> 7:1:      <TD> ` |- (. A e. V ->. [_ A / x ]_ y = y ). `
       <TR> <TD> 8:7:      <TD> ` |- (. A e. V ->. ( [_ A / x ]_ y e. [_ A / `
       ` x ]_ C <-> y e. [_ A / x ]_ C ) ). `
       <TR> <TD> 9:6,8:    <TD> ` |- (. A e. V ->. ( [. A / x ]. y e. C <-> y `
       ` e. [_ A / x ]_ C ) ). `
       <TR> <TD> 10:5,9:   <TD> ` |- (. A e. V ->. ( ( [. A / x ]. w e. B /\ `
       ` [. A / x ]. y e. C ) <-> ( w e. [_ A / x ]_ B /\ `
       ` y e. [_ A / x ]_ C ) ) ). `
       <TR> <TD> 11:1:     <TD> ` |- (. A e. V ->. ( [. A / x ]. ( w e. B /\ `
       ` y e. C ) <-> ( [. A / x ]. w e. B /\ [. A / x ]. y e. C ) ) ). `
       <TR> <TD> 12:10,11: <TD> ` |- (. A e. V ->. ( [. A / x ]. ( w e. B /\ `
       ` y e. C ) <-> ( w e. [_ A / x ]_ B /\ y e. [_ A / x ]_ C ) ) ). `
       <TR> <TD> 13:1:     <TD> ` |- (. A e. V ->. ( [. A / x ]. z = <. w ,. `
       ` y >. <-> z = <. w , y >. ) ). `
       <TR> <TD> 14:12,13: <TD> ` |- (. A e. V ->. ( ( [. A / x ]. z = <. w `
       ` ,. y >. /\ [. A / x ]. ( w e. B /\ y e. C ) ) <-> ( z = <. w , y >. `
       ` /\ ( w e. [_ A / x ]_ B /\ y e. [_ A / x ]_ C ) ) ) ). `
       <TR> <TD> 15:1:     <TD> ` |- (. A e. V ->. ( [. A / x ]. ( z = <. w `
       ` ,. y >. /\ ( w e. B /\ y e. C ) ) <-> ( [. A / x ]. z = <. w , y >. `
       ` /\ [. A / x ]. ( w e. B /\ y e. C ) ) ) ). `
       <TR> <TD> 16:14,15: <TD> ` |- (. A e. V ->. ( [. A / x ]. ( z = <. w `
       ` ,. y >. /\ ( w e. B /\ y e. C ) ) <-> ( z = <. w , y >. /\ `
       ` ( w e. [_ A / x ]_ B /\ y e. [_ A / x ]_ C ) ) ) ). `
       <TR> <TD> 17:16:    <TD> ` |- (. A e. V ->. A. y ( [. A / x ]. ( z = `
       ` <. w , y >. /\ ( w e. B /\ y e. C ) ) <-> ( z = <. w , y >. /\ `
       ` ( w e. [_ A / x ]_ B /\ y e. [_ A / x ]_ C ) ) ) ). `
       <TR> <TD> 18:17:    <TD> ` |- (. A e. V ->. ( E. y [. A / x ]. ( z = `
       ` <. w , y >. /\ ( w e. B /\ y e. C ) ) <-> E. y ( z = <. w , y >. /\ `
       ` ( w e. [_ A / x ]_ B /\ y e. [_ A / x ]_ C ) ) ) ). `
       <TR> <TD> 19:1:     <TD> ` |- (. A e. V ->. ( [. A / x ]. E. y ( z = `
       ` <. w , y >. /\ ( w e. B /\ y e. C ) ) <-> E. y [. A / x ]. ( z = `
       ` <. w , y >. /\ ( w e. B /\ y e. C ) ) ) ). `
       <TR> <TD> 20:18,19: <TD> ` |- (. A e. V ->. ( [. A / x ]. E. y ( z = `
       ` <. w , y >. /\ ( w e. B /\ y e. C ) ) <-> E. y ( z = <. w , y >. /\ `
       ` ( w e. [_ A / x ]_ B /\ y e. [_ A / x ]_ C ) ) ) ). `
       <TR> <TD> 21:20:    <TD> ` |- (. A e. V ->. A. w ( [. A / x ]. E. y ( `
       ` z = <. w , y >. /\ ( w e. B /\ y e. C ) ) <-> E. y ( z = `
       ` <. w , y >. /\ ( w e. [_ A / x ]_ B /\ y e. [_ A / x ]_ C ) ) ) ). `
       <TR> <TD> 22:21:    <TD> ` |- (. A e. V ->. ( E. w [. A / x ]. E. y ( `
       ` z = <. w , y >. /\ ( w e. B /\ y e. C ) ) <-> E. w E. y ( z = `
       ` <. w , y >. /\ ( w e. [_ A / x ]_ B /\ y e. [_ A / x ]_ C ) ) ) ). `
       <TR> <TD> 23:1:     <TD> ` |- (. A e. V ->. ( [. A / x ]. E. w E. y ( `
       ` z = <. w , y >. /\ ( w e. B /\ y e. C ) ) <-> E. w [. A / x ]. E. y `
       ` ( z = <. w , y >. /\ ( w e. B /\ y e. C ) ) ) ). `
       <TR> <TD> 24:22,23: <TD> ` |- (. A e. V ->. ( [. A / x ]. E. w E. y ( `
       ` z = <. w , y >. /\ ( w e. B /\ y e. C ) ) <-> E. w E. y ( z = `
       ` <. w , y >. /\ ( w e. [_ A / x ]_ B /\ y e. [_ A / x ]_ C ) ) ) ). `
       <TR> <TD> 25:24:    <TD> ` |- (. A e. V ->. A. z ( [. A / x ]. E. w E. `
       ` y ( z = <. w , y >. /\ ( w e. B /\ y e. C ) ) <-> E. w E. y ( z = `
       ` <. w , y >. /\ ( w e. [_ A / x ]_ B /\ y e. [_ A / x ]_ C ) ) ) ). `
       <TR> <TD> 26:25:    <TD> ` |- (. A e. V ->. { z | [. A / x ]. E. w E. `
       ` y ( z = <. w , y >. /\ ( w e. B /\ y e. C ) ) } = { z | E. w E. y ( `
       ` z = <. w , y >. /\ ( w e. [_ A / x ]_ B /\ y e. [_ A / x ]_ C ) ) } `
       ` ). `
       <TR> <TD> 27:1:     <TD> ` |- (. A e. V ->. [_ A / x ]_ { z |  E. w E. `
       ` y ( z = <. w , y >. /\ ( w e. B /\ y e. C ) ) } = { z | [. A / x ]. `
       ` E. w E. y ( z = <. w , y >. /\ ( w e. B /\ y e. C ) ) } ). `
       <TR> <TD> 28:26,27: <TD> ` |- (. A e. V ->. [_ A / x ]_ { z |  E. w E. `
       ` y ( z = <. w , y >. /\ ( w e. B /\ y e. C ) ) } = { z | E. w E. y ( `
       ` z = <. w , y >. /\ ( w e. [_ A / x ]_ B /\ y e. [_ A / x ]_ C ) ) } `
       ` ). `
       <TR> <TD> 29::      <TD> ` |- { <. w ,. y >. | ( w e. B /\ y e. C ) } `
       ` = { z |  E. w E. y ( z = <. w , y >. /\ ( w e. B /\ y e. C ) ) } `
       <TR> <TD> 30::      <TD> ` |- ( B X. C ) = { <. w ,. y >. | ( w e. B `
       ` /\ y e. C ) } `
       <TR> <TD> 31:29,30: <TD> ` |- ( B X. C ) = { z |  E. w E. y ( z = <. w `
       ` , y >. /\ ( w e. B /\ y e. C ) ) } `
       <TR> <TD> 32:31:    <TD> ` |- A. x ( B X. C ) = { z |  E. w E. y ( z = `
       ` <. w , y >. /\ ( w e. B /\ y e. C ) ) } `
       <TR> <TD> 33:1,32:  <TD> ` |- (. A e. V ->.  [_ A / x ]_ ( B X. C ) = `
       ` [_ A / x ]_ { z |  E. w E. y ( z = <. w , y >. /\ ( w e. B /\ `
       ` y e. C ) ) } ). `
       <TR> <TD> 34:28,33: <TD> ` |- (. A e. V ->.  [_ A / x ]_ ( B X. C ) = `
       ` { z | E. w E. y ( z = <. w , y >. /\ ( w e. [_ A / x ]_ B /\ `
       ` y e. [_ A / x ]_ C ) ) } ). `
       <TR> <TD> 35::      <TD> ` |- { <. w ,. y >. | ( w e. [_ A / x ]_ B /\ `
       ` y e. [_ A / x ]_ C ) } = { z | E. w E. y ( z = <. w , y >. /\ `
       ` ( w e. [_ A / x ]_ B /\ y e. [_ A / x ]_ C ) ) } `
       <TR> <TD> 36::      <TD> ` |- ( [_ A / x ]_ B X. [_ A / x ]_ C ) = { `
       ` <. w , y >. | ( w e. [_ A / x ]_ B /\ y e. [_ A / x ]_ C ) } `
       <TR> <TD> 37:35,36: <TD> ` |- ( [_ A / x ]_ B X. [_ A / x ]_ C ) = { z `
       ` | E. w E. y ( z = <. w , y >. /\ ( w e. [_ A / x ]_ B /\ `
       ` y e. [_ A / x ]_ C ) ) } `
       <TR> <TD> 38:34,37: <TD> ` |- (. A e. V ->.  [_ A / x ]_ ( B X. C ) = `
       ` ( [_ A / x ]_ B X. [_ A / x ]_ C ) ). `
       <TR> <TD> qed:38:   <TD> ` |- ( A e. V ->  [_ A / x ]_ ( B X. C ) = ( `
       ` [_ A / x ]_ B X. [_ A / x ]_ C ) ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 10-Nov-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    csbxpgVD $p |- ( A e. V -> [_ A / x ]_ ( B X. C ) =
                                        ( [_ A / x ]_ B X. [_ A / x ]_ C ) ) $=
      ( vz vw vy wcel csb wceq wa wex wsbc wb a1i e1a bibi1 e11 biimprcd cxp cv
      cop cab wal idn1 sbcel12 csbconstg eleq1 biimprd pm4.38 sbcan sbcg expcom
      ex gen11 exbi sbcex2 abbib biimpri csbab eqeq2 biimpd copab df-xp df-opab
      eqtri ax-gen wi csbeq2 e10 in1 ) BEIZABCDUAZJZABCJZABDJZUAZKZVMVOFUBGUBZH
      UBZUCKZVTVPIZWAVQIZLZLZHMZGMZFUDZKZVRWIKZVSVMABWBVTCIZWADIZLZLZHMZGMZFUDZ
      JZWIKZVOWSKZWJVMWQABNZFUDZWIKZWSXCKZWTVMXBWHOZFUEZXDVMXFFVMWPABNZGMZWHOZX
      BXIOZXFVMXHWGOZGUEXJVMXLGVMWOABNZHMZWGOZXHXNOZXLVMXMWFOZHUEXOVMXQHVMWBABN
      ZWNABNZLZWFOZXMXTOZXQVMXSWEOZXRWBOZYAVMWLABNZWMABNZLZWEOZXSYGOZYCVMYEWCOZ
      YFWDOZYHVMYEABVTJZVPIZOZYMWCOZYJVMVMYNVMUFZYNVMABVTCUGPQVMYLVTKZYOVMVMYQY
      PABVTEUHQYLVTVPUIQYNYJYOYEYMWCRUJSVMYFABWAJZVQIZOZYSWDOZYKVMVMYTYPYTVMABW
      ADUGPQVMYRWAKZUUAVMVMUUBYPABWAEUHQYRWAVQUIQYTYKUUAYFYSWDRUJSYJYKYHYEYFWCW
      DUKUOSVMVMYIYPYIVMWLWMABULPQYIYCYHXSYGWERTSVMVMYDYPWBABEUMQYDYCYAXRXSWBWE
      UKUNSVMVMYBYPYBVMWBWNABULPQYBXQYAXMXTWFRTSUPXMWFHUQQVMVMXPYPXPVMWOHABURPQ
      XPXLXOXHXNWGRTSUPXHWGGUQQVMVMXKYPXKVMWPGABURPQXKXFXJXBXIWHRTSUPXDXGXBWHFU
      SUTQVMVMXEYPXEVMWQAFBVAPQXDXEWTXCWIWSVBVCSVMVMVNWRKZAUEZXAYPUUCAVNWNGHVDW
      RGHCDVEWNGHFVFVGVHUUDXAVIVMABVNWRVJPVKWTXAWJWSWIVOVBVCSVRWEGHVDWIGHVPVQVE
      WEGHFVFVGWKVSWJVRWIVOVBTVKVL $.
  $}

  $( Virtual deduction proof of ~ csbres .
     The following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
     ~ csbres is ~ csbresgVD without virtual deductions and was
     automatically derived from ~ csbresgVD .
     <HTML> <TABLE>
     <TR> <TD> 1::       <TD> ` |- (. A e. V ->. A e. V ). `
     <TR> <TD> 2:1:      <TD> ` |- (. A e. V ->. [_ A / x ]_  _V = _V ). `
     <TR> <TD> 3:2:      <TD> ` |- (. A e. V ->. ( [_ A / x ]_ C X. [_ A / `
     ` x ]_  _V ) = ( [_ A / x ]_ C X. _V ) ). `
     <TR> <TD> 4:1:      <TD> ` |- (. A e. V ->. [_ A / x ]_ ( C X. _V ) = `
     ` ( [_ A / x ]_ C X. [_ A / x ]_  _V ) ). `
     <TR> <TD> 5:3,4:    <TD> ` |- (. A e. V ->. [_ A / x ]_ ( C X. _V ) = `
     ` ( [_ A / x ]_ C X. _V ) ). `
     <TR> <TD> 6:5:      <TD> ` |- (. A e. V ->. ( [_ A / x ]_ B i^i [_ A / `
     ` x ]_ ( C X. _V ) ) = `
     ` ( [_ A / x ]_ B i^i ( [_ A / x ]_ C X. _V ) ) ). `
     <TR> <TD> 7:1:      <TD> ` |- (. A e. V ->. [_ A / x ]_ ( B i^i ( C X. `
     ` _V ) ) = ( [_ A / x ]_ B i^i [_ A / x ]_ ( C X. _V ) ) ). `
     <TR> <TD> 8:6,7:    <TD> ` |- (. A e. V ->. [_ A / x ]_ ( B i^i ( C X. `
     ` _V ) ) = ( [_ A / x ]_ B i^i ( [_ A / x ]_ C X. _V ) ) ). `
     <TR> <TD> 9::       <TD> ` |- ( B |`` C ) = ( B i^i ( C X. _V ) ) `
     <TR> <TD> 10:9:     <TD> ` |- A. x ( B |`` C ) = ( B i^i ( C X. _V ) ) `
     <TR> <TD> 11:1,10:  <TD> ` |- (. A e. V ->. [_ A / x ]_ ( B |`` C ) = `
     ` [_ A / x ]_ ( B i^i ( C X. _V ) ) ). `
     <TR> <TD> 12:8,11:  <TD> ` |- (. A e. V ->. [_ A / x ]_ ( B |`` C ) `
     ` = ( `
     ` [_ A / x ]_ B i^i ( [_ A / x ]_ C X. _V ) ) ). `
     <TR> <TD> 13::      <TD> ` |- ( [_ A / x ]_ B |`` [_ A / x ]_ C ) = ( `
     ` [_ A / x ]_ B i^i ( [_ A / x ]_ C X. _V ) ) `
     <TR> <TD> 14:12,13: <TD> ` |- (. A e. V ->. [_ A / x ]_ ( B |`` C ) = `
     ` ( `
     ` [_ A / x ]_ B |`` [_ A / x ]_ C ) ). `
     <TR> <TD> qed:14:   <TD> ` |- ( A e. V -> [_ A / x ]_ ( B |`` C ) = ( `
     ` [_ A / x ]_ B |`` [_ A / x ]_ C ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 10-Nov-2012.)  (Proof modification is
     discouraged.)  (New usage is discouraged.) $)
  csbresgVD $p |- ( A e. V -> [_ A / x ]_ ( B |` C ) =
                                        ( [_ A / x ]_ B |` [_ A / x ]_ C ) ) $=
    ( wcel cres csb wceq cvv cxp cin idn1 e1a a1i eqeq2 biimpd e11 df-res e10
    csbconstg xpeq2 csbxp ineq2 csbin wal ax-gen wi csbeq2 biimprcd in1 ) BEFZA
    BCDGZHZABCHZABDHZGZIZULUNUOUPJKZLZIZUQUTIZURULABCDJKZLZHZUTIZUNVEIZVAULUOAB
    VCHZLZUTIZVEVIIZVFULVHUSIZVJULUPABJHZKZUSIZVHVNIZVLULVMJIZVOULULVQULMZABJEU
    ANVMJUPUBNULULVPVRVPULABDJUCONVOVPVLVNUSVHPQRVHUSUOUDNULULVKVRVKULABCVCUEON
    VJVKVFVIUTVEPQRULULUMVDIZAUFZVGVRVSACDSUGVTVGUHULABUMVDUIOTVFVGVAVEUTUNPQRU
    OUPSVBURVAUQUTUNPUJTUK $.

  ${
    $d A w y $.  $d B w y $.  $d V w y $.  $d x w y $.
    $( Virtual deduction proof of ~ csbrn .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ csbrn is ~ csbrngVD without virtual deductions and was
       automatically derived from ~ csbrngVD .
       <HTML> <TABLE>
       <TR> <TD> 1::       <TD> ` |- (. A e. V ->. A e. V ). `
       <TR> <TD> 2:1:      <TD> ` |- (. A e. V ->. ( [. A / x ]. <. w ,. y >. `
       ` e. B <-> [_ A / x ]_ <. w , y >. e. [_ A / x ]_ B ) ). `
       <TR> <TD> 3:1:      <TD> ` |- (. A e. V ->. [_ A / x ]_ <. w ,. y >. = `
       ` <. w , y >. ). `
       <TR> <TD> 4:3:      <TD> ` |- (. A e. V ->. ( [_ A / x ]_ <. w ,. y >. `
       ` e. [_ A / x ]_ B <->  <. w , y >. e. [_ A / x ]_ B ) ). `
       <TR> <TD> 5:2,4:    <TD> ` |- (. A e. V ->. ( [. A / x ]. <. w ,. y >. `
       ` e. B <-> <. w , y >. e. [_ A / x ]_ B ) ). `
       <TR> <TD> 6:5:      <TD> ` |- (. A e. V ->. A. w ( [. A / x ]. <. w ,. `
       ` y >. e. B <-> <. w , y >. e. [_ A / x ]_ B ) ). `
       <TR> <TD> 7:6:      <TD> ` |- (. A e. V ->. ( E. w [. A / x ]. <. w ,. `
       ` y >. e. B <-> E. w <. w , y >. e. [_ A / x ]_ B ) ). `
       <TR> <TD> 8:1:      <TD> ` |- (. A e. V ->. ( E. w [. A / x ]. <. w ,. `
       ` y >. e. B <-> [. A / x ]. E. w  <. w , y >. e. B ) ). `
       <TR> <TD> 9:7,8:    <TD> ` |- (. A e. V ->. ( [. A / x ]. E. w  <. w `
       ` ,. y >. e. B <-> E. w <. w , y >. e. [_ A / x ]_ B ) ). `
       <TR> <TD> 10:9:     <TD> ` |- (. A e. V ->. A. y ( [. A / x ]. E. w `
       `  <. w , y >. e. B <-> E. w <. w , y >. e. [_ A / x ]_ B ) ). `
       <TR> <TD> 11:10:    <TD> ` |- (. A e. V ->. { y | [. A / x ]. E. w  <. `
       ` w , y >. e. B } = { y | E. w <. w , y >. e. [_ A / x ]_ B } ). `
       <TR> <TD> 12:1:     <TD> ` |- (. A e. V ->. [_ A / x ]_ { y |  E. w `
       ` <. w , y >. e. B } = { y | [. A / x ]. E. w  <. w , y >. e. B } ). `
       <TR> <TD> 13:11,12: <TD> ` |- (. A e. V ->. [_ A / x ]_ { y |  E. w `
       ` <. w , y >. e. B } = { y | E. w <. w , y >. e. [_ A / x ]_ B } ). `
       <TR> <TD> 14::      <TD> ` |- ran B = { y |  E. w  <. w ,. y >. e. B } `
       <TR> <TD> 15:14:    <TD> ` |- A. x ran B = { y |  E. w  <. w ,. y >. `
       ` e. B } `
       <TR> <TD> 16:1,15:  <TD> ` |- (. A e. V ->. [_ A / x ]_ ran B = [_ A / `
       ` x ]_ { y |  E. w  <. w , y >. e. B } ). `
       <TR> <TD> 17:13,16: <TD> ` |- (. A e. V ->. [_ A / x ]_ ran B = { y | `
       ` E. w <. w , y >. e. [_ A / x ]_ B } ). `
       <TR> <TD> 18::      <TD> ` |- ran [_ A / x ]_ B = { y |  E. w  <. w `
       ` ,. y >. e. [_ A / x ]_ B } `
       <TR> <TD> 19:17,18: <TD> ` |- (. A e. V ->. [_ A / x ]_ ran B = ran [_ `
       ` A / x ]_ B ). `
       <TR> <TD> qed:19:   <TD> ` |- ( A e. V -> [_ A / x ]_ ran B = ran [_ A `
       ` / x ]_ B ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 10-Nov-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    csbrngVD $p |- ( A e. V -> [_ A / x ]_ ran B = ran [_ A / x ]_ B ) $=
      ( vw vy wcel crn csb wceq cv wex cab wsbc wb wal a1i e1a e11 eqeq2 sbcex2
      idn1 sbcel12 csbconstg eleq1 bibi1 biimprd gen11 bicomd bitr3 com12 abbib
      cop exbi biimpri csbab biimpd dfrn3 ax-gen wi csbeq2 e10 biimprcd in1 ) B
      DGZABCHZIZABCIZHZJZVEVGEKFKUMZVHGZELZFMZJZVIVNJZVJVEABVKCGZELZFMZIZVNJZVG
      VTJZVOVEVRABNZFMZVNJZVTWDJZWAVEWCVMOZFPZWEVEWGFVEVQABNZELZVMOZWJWCOZWGVEW
      IVLOZEPWKVEWMEVEWIABVKIZVHGZOZWOVLOZWMVEVEWPVEUBZWPVEABVKCUCQRVEWNVKJZWQV
      EVEWSWRABVKDUDRWNVKVHUERWPWMWQWIWOVLUFUGSUHWIVLEUNRVEVEWLWRVEWCWJWCWJOVEV
      QEABUAQUIRWLWKWGWJWCVMUJUKSUHWEWHWCVMFULUORVEVEWFWRWFVEVRAFBUPQRWEWFWAWDV
      NVTTUQSVEVEVFVSJZAPZWBWRWTAEFCURUSXAWBUTVEABVFVSVAQVBWAWBVOVTVNVGTUQSEFVH
      URVPVJVOVIVNVGTVCVBVD $.
  $}

  $( Virtual deduction proof of ~ csbima12 .
     The following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
     ~ csbima12 is ~ csbima12gALTVD without virtual deductions and was
     automatically derived from ~ csbima12gALTVD .
     <HTML> <TABLE>
     <TR> <TD> 1::       <TD> ` |- (. A e. C ->. A e. C ). `
     <TR> <TD> 2:1:      <TD> ` |- (. A e. C ->. [_ A / x ]_ ( F |`` B ) = `
     ` ( `
     ` [_ A / x ]_ F |`` [_ A / x ]_ B ) ). `
     <TR> <TD> 3:2:      <TD> ` |- (. A e. C ->. `
     ` ran [_ A / x ]_ ( F |`` B ) `
     ` = ran ( [_ A / x ]_ F |`` [_ A / x ]_ B ) ). `
     <TR> <TD> 4:1:      <TD> ` |- (. A e. C ->. `
     ` [_ A / x ]_ ran ( F |`` B ) `
     ` = ran [_ A / x ]_ ( F |`` B ) ). `
     <TR> <TD> 5:3,4:    <TD> ` |- (. A e. C ->. `
     ` [_ A / x ]_ ran ( F |`` B ) `
     ` = ran ( [_ A / x ]_ F |`` [_ A / x ]_ B ) ). `
     <TR> <TD> 6::       <TD> ` |- ( F " B ) = ran ( F |`` B ) `
     <TR> <TD> 7:6:      <TD> ` |- A. x ( F " B ) = ran ( F |`` B ) `
     <TR> <TD> 8:1,7:    <TD> ` |- (. A e. C ->. [_ A / x ]_ ( F " B ) = [_ `
     ` A / x ]_ ran ( F |`` B ) ). `
     <TR> <TD> 9:5,8:    <TD> ` |- (. A e. C ->. [_ A / x ]_ ( F " B ) = `
     ` ran ( [_ A / x ]_ F |`` [_ A / x ]_ B ) ). `
     <TR> <TD> 10::      <TD> ` |- ( [_ A / x ]_ F " [_ A / x ]_ B ) = ran `
     ` ( [_ A / x ]_ F |`` [_ A / x ]_ B ) `
     <TR> <TD> 11:9,10:  <TD> ` |- (. A e. C ->. [_ A / x ]_ ( F " B ) = ( `
     ` [_ A / x ]_ F " [_ A / x ]_ B ) ). `
     <TR> <TD> qed:11:   <TD> ` |- ( A e. C -> [_ A / x ]_ ( F " B ) = ( [_ `
     ` A / x ]_ F " [_ A / x ]_ B ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 10-Nov-2012.)  (Proof modification is
     discouraged.)  (New usage is discouraged.) $)
  csbima12gALTVD $p |- ( A e. C -> [_ A / x ]_ ( F " B ) =
                                         ( [_ A / x ]_ F " [_ A / x ]_ B ) ) $=
    ( wcel cima csb wceq cres crn idn1 csbres a1i e1a eqeq2 biimpd e11 df-ima
    e10 rneq csbrn wal ax-gen wi csbeq2 biimprcd in1 ) BDFZABECGZHZABEHZABCHZGZ
    IZUIUKULUMJZKZIZUNUQIZUOUIABECJZKZHZUQIZUKVBIZURUIABUTHZKZUQIZVBVFIZVCUIVEU
    PIZVGUIUIVIUILZVIUIABECMNOVEUPUAOUIUIVHVJVHUIABUTUBNOVGVHVCVFUQVBPQRUIUIUJV
    AIZAUCZVDVJVKAECSUDVLVDUEUIABUJVAUFNTVCVDURVBUQUKPQRULUMSUSUOURUNUQUKPUGTUH
    $.

  ${
    $d A y z $.  $d B y z $.  $d V y z $.  $d x y z $.
    $( Virtual deduction proof of ~ csbuni .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ csbuni is ~ csbunigVD without virtual deductions and was
       automatically derived from ~ csbunigVD .
       <HTML> <TABLE>
       <TR> <TD> 1::       <TD> ` |- (. A e. V ->. A e. V ). `
       <TR> <TD> 2:1:      <TD> ` |- (. A e. V ->. ( [. A / x ]. z e. y <-> z `
       ` e. y ) ). `
       <TR> <TD> 3:1:      <TD> ` |- (. A e. V ->. ( [. A / x ]. y e. B <-> y `
       ` e. [_ A / x ]_ B ) ). `
       <TR> <TD> 4:2,3:    <TD> ` |- (. A e. V ->. ( ( [. A / x ]. z e. y /\ `
       ` [. A / x ]. y e. B ) <-> ( z e. y /\ y e. [_ A / x ]_ B ) ) ). `
       <TR> <TD> 5:1:      <TD> ` |- (. A e. V ->. ( [. A / x ]. ( z e. y /\ `
       ` y e. B ) <-> ( [. A / x ]. z e. y /\ [. A / x ]. y e. B ) ) ). `
       <TR> <TD> 6:4,5:    <TD> ` |- (. A e. V ->. ( [. A / x ]. ( z e. y /\ `
       ` y e. B ) <-> ( z e. y /\ y e. [_ A / x ]_ B ) ) ). `
       <TR> <TD> 7:6:      <TD> ` |- (. A e. V ->. A. y ( [. A / x ]. ( z e. `
       ` y /\ y e. B ) <-> ( z e. y /\ y e. [_ A / x ]_ B ) ) ). `
       <TR> <TD> 8:7:      <TD> ` |- (. A e. V ->. ( E. y [. A / x ]. ( z e. `
       ` y /\ y e. B ) <-> E. y ( z e. y /\ y e. [_ A / x ]_ B ) ) ). `
       <TR> <TD> 9:1:      <TD> ` |- (. A e. V ->. ( [. A / x ]. E. y ( z e. `
       ` y /\ y e. B ) <-> E. y [. A / x ]. ( z e. y /\ y e. B ) ) ). `
       <TR> <TD> 10:8,9:   <TD> ` |- (. A e. V ->. ( [. A / x ]. E. y ( z e. `
       ` y /\ y e. B ) <-> E. y ( z e. y /\ y e. [_ A / x ]_ B ) ) ). `
       <TR> <TD> 11:10:    <TD> ` |- (. A e. V ->. A. z ( [. A / x ]. E. y ( `
       ` z e. y /\ y e. B ) <-> E. y ( z e. y /\ y e. [_ A / x ]_ B ) ) ). `
       <TR> <TD> 12:11:    <TD> ` |- (. A e. V ->. { z | [. A / x ]. E. y ( `
       ` z e. y /\ y e. B ) } = { z | E. y ( z e. y /\ `
       ` y e. [_ A / x ]_ B ) } ). `
       <TR> <TD> 13:1:     <TD> ` |- (. A e. V ->. [_ A / x ]_ { z | E. y ( z `
       ` e. y /\ y e. B ) } = { z | [. A / x ]. E. y ( z e. y /\ y e. B ) } `
       ` ). `
       <TR> <TD> 14:12,13: <TD> ` |- (. A e. V ->. [_ A / x ]_ { z | E. y ( z `
       ` e. y /\ y e. B ) } = { z | E. y ( z e. y /\ `
       ` y e. [_ A / x ]_ B ) } ). `
       <TR> <TD> 15::      <TD> ` |- U. B = { z | E. y ( z e. y /\ y e. B ) } `
       <TR> <TD> 16:15:    <TD> ` |- A. x U. B = { z | E. y ( z e. y /\ y e. `
       ` B ) } `
       <TR> <TD> 17:1,16:  <TD> ` |- (. A e. V ->. [. A / x ]. U. B = { z | `
       ` E. y ( z e. y /\ y e. B ) } ). `
       <TR> <TD> 18:1,17:  <TD> ` |- (. A e. V ->. [_ A / x ]_ U. B = [_ A / `
       ` x ]_ { z | E. y ( z e. y /\ y e. B ) } ). `
       <TR> <TD> 19:14,18: <TD> ` |- (. A e. V ->. [_ A / x ]_ U. B = { z | `
       ` E. y ( z e. y /\ y e. [_ A / x ]_ B ) } ). `
       <TR> <TD> 20::      <TD> ` |- U. [_ A / x ]_ B = { z | E. y ( z e. y `
       ` /\ y e. [_ A / x ]_ B ) } `
       <TR> <TD> 21:19,20: <TD> ` |- (. A e. V ->. [_ A / x ]_ U. B = U. [_ A `
       ` / x ]_ B ). `
       <TR> <TD> qed:21:   <TD> ` |- ( A e. V -> [_ A / x ]_ U. B = U. [_ A / `
       ` x ]_ B ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 10-Nov-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    csbunigVD $p |- ( A e. V -> [_ A / x ]_ U. B = U. [_ A / x ]_ B ) $=
      ( vz vy wcel csb wceq wa wex cab wsbc wb wal e1a a1i e11 biimprcd eqeq2
      cuni wel cv idn1 sbcg sbcel2 pm4.38 sbcan bibi1 gen11 exbi sbcex2 biimpri
      ex abbib csbab biimpd df-uni ax-gen spsbc e10 sbceqg in1 ) BDGZABCUAZHZAB
      CHZUAZIZVDVFEFUBZFUCZVGGZJZFKZELZIZVHVOIZVIVDABVJVKCGZJZFKZELZHZVOIZVFWBI
      ZVPVDVTABMZELZVOIZWBWFIZWCVDWEVNNZEOZWGVDWIEVDVSABMZFKZVNNZWEWLNZWIVDWKVM
      NZFOWMVDWOFVDVJABMZVRABMZJZVMNZWKWRNZWOVDWPVJNZWQVLNZWSVDVDXAVDUDZVJABDUE
      PVDVDXBXCXBVDABVKCUFQPXAXBWSWPWQVJVLUGUNRVDVDWTXCWTVDVJVRABUHQPWTWOWSWKWR
      VMUISRUJWKVMFUKPVDVDWNXCWNVDVSFABULQPWNWIWMWEWLVNUISRUJWGWJWEVNEUOUMPVDVD
      WHXCWHVDVTAEBUPQPWGWHWCWFVOWBTUQRVDVDVEWAIZABMZWDXCVDVDXDAOXEXCXDAEFCURUS
      XDABDUTVAVDXEWDABVEWADVBUQRWCWDVPWBVOVFTUQREFVGURVQVIVPVHVOVFTSVAVC $.
  $}

  ${
    $d A y $.  $d F y $.  $d B y $.  $d C y $.  $d x y $.
    $( Virtual deduction proof of ~ csbfv12 .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ csbfv12 is ~ csbfv12gALTVD without virtual deductions and was
       automatically derived from ~ csbfv12gALTVD .
       <HTML> <TABLE>
       <TR> <TD> 1::           <TD> ` |- (. A e. C ->. A e. C ). `
       <TR> <TD> 2:1:          <TD> ` |- (. A e. C ->. [_ A / x ]_ { y } = { `
       ` y } ). `
       <TR> <TD> 3:1:          <TD> ` |- (. A e. C ->. [_ A / x ]_ ( F " { B `
       ` } ) = ( [_ A / x ]_ F " [_ A / x ]_ { B } ) ). `
       <TR> <TD> 4:1:          <TD> ` |- (. A e. C ->. [_ A / x ]_ { B } = { `
       ` [_ A / x ]_ B } ). `
       <TR> <TD> 5:4:          <TD> ` |- (. A e. C ->. ( [_ A / x ]_ F " [_ A `
       ` / x ]_ { B } ) = ( [_ A / x ]_ F " { [_ A / x ]_ B } ) ). `
       <TR> <TD> 6:3,5:        <TD> ` |- (. A e. C ->. [_ A / x ]_ ( F " { B `
       ` } ) = ( [_ A / x ]_ F " { [_ A / x ]_ B } ) ). `
       <TR> <TD> 7:1:          <TD> ` |- (. A e. C ->. ( [. A / x ]. ( F " { `
       ` B } ) = { y } <-> [_ A / x ]_ ( F " { B } ) = [_ A / x ]_ { y } ) ). `
       <TR> <TD> 8:6,2:        <TD> ` |- (. A e. C ->. ( [_ A / x ]_ ( F " { `
       ` B } ) = [_ A / x ]_ { y } <-> ( [_ A / x ]_ F " { [_ A / x ]_ B } ) `
       ` = { y } ) ). `
       <TR> <TD> 9:7,8:        <TD> ` |- (. A e. C ->. ( [. A / x ]. ( F " { `
       ` B } ) = { y } <-> ( [_ A / x ]_ F " { [_ A / x ]_ B } ) = { y } ) `
       ` ). `
       <TR> <TD> 10:9:         <TD> ` |- (. A e. C ->. A. y ( [. A / x ]. ( F `
       ` " { B } ) = { y } <-> ( [_ A / x ]_ F " { [_ A / x ]_ B } ) = `
       ` { y } ) ). `
       <TR> <TD> 11:10:        <TD> ` |- (. A e. C ->. { y | [. A / x ]. ( F `
       ` " { B } ) = { y } } = { y | ( [_ A / x ]_ F " { [_ A / x ]_ B } ) = `
       ` { y } } ). `
       <TR> <TD> 12:1:         <TD> ` |- (. A e. C ->. [_ A / x ]_ { y | ( F `
       ` " { B } ) = { y } } = { y | [. A / x ]. ( F " { B } ) = { y } } ). `
       <TR> <TD> 13:11,12:     <TD> ` |- (. A e. C ->. [_ A / x ]_ { y | ( F `
       ` " { B } ) = { y } } = { y | ( [_ A / x ]_ F " { [_ A / x ]_ B } ) = `
       ` { y `
       ` } } ). `
       <TR> <TD> 14:13:        <TD> ` |- (. A e. C ->. U. [_ A / x ]_ { y | ( `
       ` F " { B } ) = { y } } = U. { y | ( [_ A / x ]_ F " `
       ` { [_ A / x ]_ B } ) = `
       ` { y } } ). `
       <TR> <TD> 15:1:         <TD> ` |- (. A e. C ->. [_ A / x ]_ U. { y | ( `
       ` F " { B } ) = { y } } = U. [_ A / x ]_ { y | ( F " { B } ) = `
       ` { y } } ). `
       <TR> <TD> 16:14,15:     <TD> ` |- (. A e. C ->. [_ A / x ]_ U. { y | ( `
       ` F " { B } ) = { y } } = `
       ` U. { y | ( [_ A / x ]_ F " { [_ A / x ]_ B } ) = `
       ` { y } } ). `
       <TR> <TD> 17::          <TD> ` |- ( F `` B ) = `
       ` U. { y | ( F " { B } ) = `
       ` { y } } `
       <TR> <TD> 18:17:        <TD> ` |- A. x ( F `` B ) = U. { y | ( F " { B `
       ` } ) = { y } } `
       <TR> <TD> 19:1,18:      <TD> ` |- (. A e. C ->. [_ A / x ]_ ( F `` B ) `
       ` = [_ A / x ]_ U. { y | ( F " { B } ) = { y } } ). `
       <TR> <TD> 20:16,19:     <TD> ` |- (. A e. C ->. [_ A / x ]_ ( F `` B ) `
       ` = U. { y | ( [_ A / x ]_ F " { [_ A / x ]_ B } ) = { y } } ). `
       <TR> <TD> 21::          <TD> ` |- ( [_ A / x ]_ F `` [_ A / x ]_ B ) = `
       ` U. { y | ( [_ A / x ]_ F " { [_ A / x ]_ B } ) = { y } } `
       <TR> <TD> 22:20,21:     <TD> ` |- (. A e. C ->. [_ A / x ]_ ( F `` B ) `
       ` = ( [_ A / x ]_ F `` [_ A / x ]_ B ) ). `
       <TR> <TD> qed:22:       <TD> ` |- ( A e. C -> [_ A / x ]_ ( F `` B ) = `
       ` ( [_ A / x ]_ F `` [_ A / x ]_ B ) ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 10-Nov-2012.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    csbfv12gALTVD $p |- ( A e. C -> [_ A / x ]_ ( F ` B ) =
                                         ( [_ A / x ]_ F ` [_ A / x ]_ B ) ) $=
      ( vy cfv csb wceq csn cima cab cuni wb wal e1a a1i e11 eqeq2 biimpd eqeq1
      wcel cv wsbc sbceqg csbima12 csbsng imaeq2 biimprd csbconstg eqeq12 bibi1
      idn1 ex gen11 abbib biimpri csbab unieq csbuni dffv4 ax-gen wi csbeq2 e10
      biimprcd in1 ) BDUBZABCEGZHZABCHZABEHZGZIZVHVJVLVKJZKZFUCJZIZFLZMZIZVMVTI
      ZVNVHABECJZKZVQIZFLZMZHZVTIZVJWHIZWAVHABWFHZMZVTIZWHWLIZWIVHWKVSIZWMVHWEA
      BUDZFLZVSIZWKWQIZWOVHWPVRNZFOZWRVHWTFVHWPABWDHZABVQHZIZNZXDVRNZWTVHVHXEVH
      UMZABWDVQDUEPVHXBVPIZXCVQIZXFVHXBVLABWCHZKZIZXKVPIZXHVHVHXLXGXLVHABWCEUFQ
      PVHXJVOIZXMVHVHXNXGABCDUGPXJVOVLUHPXLXHXMXBXKVPUAUIRVHVHXIXGABVQDUJPXHXIX
      FXBVPXCVQUKUNRXEWTXFWPXDVRULUIRUOWRXAWPVRFUPUQPVHVHWSXGWSVHWEAFBURQPWRWSW
      OWQVSWKSTRWKVSUSPVHVHWNXGWNVHABWFUTQPWMWNWIWLVTWHSTRVHVHVIWGIZAOZWJXGXOAF
      CEVAVBXPWJVCVHABVIWGVDQVEWIWJWAWHVTVJSTRFVKVLVAWBVNWAVMVTVJSVFVEVG $.
  $}

  $( Virtual deduction proof of ~ con5 .
     The following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
     ~ con5 is ~ con5VD without virtual deductions and was automatically
     derived from ~ con5VD .
     <HTML> <TABLE>
     <TR> <TD> 1::    <TD> ` |- (. ( ph <-> -. ps ) ->. ( ph <-> -. ps ) ). `
     <TR> <TD> 2:1:   <TD> ` |- (. ( ph <-> -. ps ) ->. ( -. ps -> ph ) ). `
     <TR> <TD> 3:2:   <TD> ` |- (. ( ph <-> -. ps ) ->. ( -. ph -> -. -. ps `
     ` ) ). `
     <TR> <TD> 4::    <TD> ` |- ( ps <-> -. -. ps ) `
     <TR> <TD> 5:3,4: <TD> ` |- (. ( ph <-> -. ps ) ->. ( -. ph -> ps ) ). `
     <TR> <TD> qed:5: <TD> ` |- ( ( ph <-> -. ps ) -> ( -. ph -> ps ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 21-Apr-2013.)  (Proof modification is
     discouraged.)  (New usage is discouraged.) $)
  con5VD $p |- ( ( ph <-> -. ps ) -> ( -. ph -> ps ) ) $=
    ( wn wb wi idn1 biimpr e1a con3 notnotb imbi2 biimprcd e10 in1 ) ABCZDZACZB
    EZPQOCZEZBSDZRPOAEZTPPUBPFAOGHOAIHBJUARTBSQKLMN $.

  ${
    $d ph z $.  $d u v x z $.  $d u v y z $.
    $( Virtual deduction proof of ~ relopab .
       The following User's Proof is a Virtual Deduction proof completed
       automatically by the tools program completeusersproof.cmd, which invokes
       Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
       ~ relopab is ~ relopabVD without virtual deductions and was
       automatically derived from ~ relopabVD .
       <HTML> <TABLE>
       <TR> <TD> 1::          <TD> ` |- (. y = v ->. y = v ). `
       <TR> <TD> 2:1:         <TD> ` |- (. y = v ->. <. x ,. y >. = <. x ,. v `
       ` >. ). `
       <TR> <TD> 3::          <TD> ` |- (. y = v ,. x = u ->. x = u ). `
       <TR> <TD> 4:3:         <TD> ` |- (. y = v ,. x = u ->. <. x ,. v >. = <.
       `
       ` u , v >. ). `
       <TR> <TD> 5:2,4:       <TD> ` |- (. y = v ,. x = u ->. <. x ,. y >. = <.
       `
       ` u , v >. ). `
       <TR> <TD> 6:5:         <TD> ` |- (. y = v ,. x = u ->. ( z = <. x ,. y `
       ` >. -> z = <. u , v >. ) ). `
       <TR> <TD> 7:6:         <TD> ` |- (. y = v ->. ( x = u -> ( z = <. x ,. `
       ` y >. -> z = <. u , v >. ) ) ). `
       <TR> <TD> 8:7:         <TD> ` |- ( y = v -> ( x = u -> ( z = <. x ,. y `
       ` >. -> z = <. u , v >. ) ) ) `
       <TR> <TD> 9:8:         <TD> ` |- ( E. v y = v ->  E. v ( x = u -> ( z `
       ` = <. x , y >. -> z = <. u , v >. ) ) ) `
       <TR> <TD> 90::         <TD> ` |- ( v = y <-> y = v ) `
       <TR> <TD> 91:90:       <TD> ` |- ( E. v v = y <-> E. v y = v ) `
       <TR> <TD> 92::         <TD> ` |- E. v v = y `
       <TR> <TD> 10:91,92:    <TD> ` |- E. v y = v `
       <TR> <TD> 11:9,10:     <TD> ` |- E. v ( x = u -> ( z = <. x ,. y >. -> `
       ` z = <. u , v >. ) ) `
       <TR> <TD> 12:11:       <TD> ` |- ( x = u -> E. v ( z = <. x ,. y >. -> `
       ` z = <. u , v >. ) ) `
       <TR> <TD> 13::         <TD> ` |- ( E. v ( z = <. x ,. y >. -> z = <. u `
       ` , v >. ) -> ( z = <. x , y >. -> E. v z = <. u , v >. ) ) `
       <TR> <TD> 14:12,13:    <TD> ` |- ( x = u -> ( z = <. x ,. y >. -> E. v `
       ` z = <. u , v >. ) ) `
       <TR> <TD> 15:14:       <TD> ` |- ( E. u x = u -> E. u ( z = <. x ,. y `
       ` >. -> E. v z = <. u , v >. ) ) `
       <TR> <TD> 150::        <TD> ` |- ( u = x <-> x = u ) `
       <TR> <TD> 151:150:     <TD> ` |- ( E. u u = x <-> E. u x = u ) `
       <TR> <TD> 152::        <TD> ` |- E. u u = x `
       <TR> <TD> 16:151,152:  <TD> ` |- E. u x = u `
       <TR> <TD> 17:15,16:    <TD> ` |- E. u ( z = <. x ,. y >. -> E. v z = <.
       `
       ` u , v >. ) `
       <TR> <TD> 18:17:       <TD> ` |- ( z = <. x ,. y >. -> E. u E. v z = <.
       `
       ` u , v >. ) `
       <TR> <TD> 19:18:       <TD> ` |- ( E. y z = <. x ,. y >. -> E. y E. u `
       ` E. v z = <. u , v >. ) `
       <TR> <TD> 20::         <TD> ` |- ( E. y E. u E. v z = <. u ,. v >. -> `
       ` E. u E. v z = <. u , v >. ) `
       <TR> <TD> 21:19,20:    <TD> ` |- ( E. y z = <. x ,. y >. -> E. u E. v z
       `
       ` = <. u , v >. ) `
       <TR> <TD> 22:21:       <TD> ` |- ( E. x E. y z = <. x ,. y >. -> E. x `
       ` E. u E. v z = <. u , v >. ) `
       <TR> <TD> 23::         <TD> ` |- ( E. x E. u E. v z = <. u ,. v >. -> `
       ` E. u E. v z = <. u , v >. ) `
       <TR> <TD> 24:22,23:    <TD> ` |- ( E. x E. y z = <. x ,. y >. -> E. u `
       ` E. v z = <. u , v >. ) `
       <TR> <TD> 25:24:       <TD> ` |- { z | E. x E. y z = <. x ,. y >. } C_ `
       ` { z | E. u E. v z = <. u , v >. } `
       <TR> <TD> 26::         <TD> ` |- x e. _V `
       <TR> <TD> 27::         <TD> ` |- y e. _V `
       <TR> <TD> 28:26,27:    <TD> ` |- ( x e. _V /\ y e. _V ) `
       <TR> <TD> 29:28:       <TD> ` |- ( z = <. x ,. y >. <-> ( z = <. x ,. y
       `
       ` >. /\ ( x e. _V /\ y e. _V ) ) ) `
       <TR> <TD> 30:29:       <TD> ` |- ( E. y z = <. x ,. y >. <-> E. y ( z =
       `
       ` <. x , y >. /\ ( x e. _V /\ y e. _V ) ) ) `
       <TR> <TD> 31:30:       <TD> ` |- ( E. x E. y z = <. x ,. y >. <-> E. x `
       ` E. y ( z = <. x , y >. /\ ( x e. _V /\ y e. _V ) ) ) `
       <TR> <TD> 32:31:       <TD> ` |- { z | E. x E. y z = <. x ,. y >. } = {
       `
       ` z | E. x E. y ( z = <. x , y >. /\ ( x e. _V /\ y e. _V ) ) } `
       <TR> <TD> 320:25,32:   <TD> ` |- { z | E. x E. y ( z = <. x ,. y >. /\ `
       ` ( x e. _V /\ y e. _V ) ) } C_ { z | E. u E. v z = <. u , v >. } `
       <TR> <TD> 33::         <TD> ` |- u e. _V `
       <TR> <TD> 34::         <TD> ` |- v e. _V `
       <TR> <TD> 35:33,34:    <TD> ` |- ( u e. _V /\ v e. _V ) `
       <TR> <TD> 36:35:       <TD> ` |- ( z = <. u ,. v >. <-> ( z = <. u ,. v
       `
       ` >. /\ ( u e. _V /\ v e. _V ) ) ) `
       <TR> <TD> 37:36:       <TD> ` |- ( E. v z = <. u ,. v >. <-> E. v ( z =
       `
       ` <. u , v >. /\ ( u e. _V /\ v e. _V ) ) ) `
       <TR> <TD> 38:37:       <TD> ` |- ( E. u E. v z = <. u ,. v >. <-> E. u `
       ` E. v ( z = <. u , v >. /\ ( u e. _V /\ v e. _V ) ) ) `
       <TR> <TD> 39:38:       <TD> ` |- { z | E. u E. v z = <. u ,. v >. } = {
       `
       ` z | E. u E. v ( z = <. u , v >. /\ ( u e. _V /\ v e. _V ) ) } `
       <TR> <TD> 40:320,39:   <TD> ` |- { z | E. x E. y ( z = <. x ,. y >. /\ `
       ` ( x e. _V /\ y e. _V ) ) } C_ { z | E. u E. v ( z = <. u , v >. /\ `
       ` ( u e. _V /\ v e. _V ) ) } `
       <TR> <TD> 41::         <TD> ` |- { <. x ,. y >. | ( x e. _V /\ y e. _V `
       ` ) } = { z | E. x E. y ( z = <. x , y >. /\ ( x e. _V /\ y e. _V ) ) `
       ` } `
       <TR> <TD> 42::         <TD> ` |- { <. u ,. v >. | ( u e. _V /\ v e. _V `
       ` ) } = { z | E. u E. v ( z = <. u , v >. /\ ( u e. _V /\ v e. _V ) ) `
       ` } `
       <TR> <TD> 43:40,41,42: <TD> ` |- { <. x ,. y >. | ( x e. _V /\ y e. _V `
       ` ) } C_ { <. u , v >. | ( u e. _V /\ v e. _V ) } `
       <TR> <TD> 44::         <TD> ` |- { <. u ,. v >. | ( u e. _V /\ v e. _V `
       ` ) } = ( _V X. _V ) `
       <TR> <TD> 45:43,44:    <TD> ` |- { <. x ,. y >. | ( x e. _V /\ y e. _V `
       ` ) } C_ ( _V X. _V ) `
       <TR> <TD> 46:28:       <TD> ` |- ( ph -> ( x e. _V /\ y e. _V ) ) `
       <TR> <TD> 47:46:       <TD> ` |- { <. x ,. y >. | ph } C_ { <. x ,. y >.
       `
       ` | ( x e. _V /\ y e. _V ) } `
       <TR> <TD> 48:45,47:    <TD> ` |- { <. x ,. y >. | ph } C_ ( _V X. _V ) `
       <TR> <TD> qed:48:      <TD> ` |- Rel { <. x ,. y >. | ph } `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 9-Jul-2013.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    relopabVD $p |- Rel { <. x , y >. | ph } $=
      ( vu vv vz copab cvv cv wcel wa vex cop wceq wex cab exbii eximi biimpi
      wi cxp wss wrel pm3.2i a1i ssopab2i biantru abbii ax6ev equcom mpbi opeq2
      idn1 e1a idn2 opeq1 eqeq1 biimprd e12 eqeq2 biimpd in2 in1 19.37iv 19.37v
      e2 ax-mp 19.9v ss2abi eqsstrri sseqtri df-opab 3sstr4i df-xp eqcomi sstri
      syl df-rel biimpri e0a ) ABCGZHHUAZUBZWAUCZWABIZHJZCIZHJZKZBCGZWBAWIBCWIA
      WFWHBLCLUDZUEUFWJDIZHJZEIZHJZKZDEGZWBFIZWEWGMZNZWIKZCOZBOZFPZWRWLWNMZNZWP
      KZEOZDOZFPZWJWQXDXFEOZDOZFPZXJXDWTCOZBOZFPXMXOXCFXNXBBWTXACWIWTWKUGQQUHXO
      XLFXOXLBOZXLXNXLBXNXLCOZXLWTXLCWTXKDWEWLNZDOZWTXKTZDOWLWENZDOXSDBUIYAXRDD
      BUJQUKXRXTDXRWTXFTZEOZXTXRYBEWGWNNZEOZXRYBTZEOWNWGNZEOYEECUIYGYDEECUJQUKY
      DYFEYDYFYDXRYBYDXRWSXENZYBYDWSWEWNMZNZXRYIXENZYHYDYDYJYDUMWGWNWEULUNYDXRX
      RYKYDXRUOWEWLWNUPVFYJYHYKWSYIXEUQURUSYHWTXFWSXEWRUTVAVFVBVCRVGVDYCXTWTXFE
      VESVQRVGVDRXQXLXLCVHSVQRXPXLXLBVHSVQVIVJXLXIFXKXHDXFXGEWPXFWMWODLELUDUGQQ
      UHVKWIBCFVLWPDEFVLVMWBWQDEHHVNVOVKVPWDWCWAVRVSVT $.
  $}

  $( Virtual deduction proof of ~ 19.41rg .
     The following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.  ~ 19.41rg
     is ~ 19.41rgVD without virtual deductions and was automatically derived
     from ~ 19.41rgVD .  (Contributed by Alan Sare, 8-Feb-2014.)
     (Proof modification is discouraged.)  (New usage is discouraged.)
     <HTML> <TABLE>
     <TR> <TD> 1::       <TD> ` |- ( ps -> ( ph -> ( ph /\ ps ) ) ) `
     <TR> <TD> 2:1:      <TD> ` |- ( ( ps -> A. x ps ) -> ( ps -> ( ph -> ( `
     ` ph /\ ps ) ) ) ) `
     <TR> <TD> 3:2:      <TD> ` |- A. x ( ( ps -> A. x ps ) -> ( ps -> ( ph `
     ` -> ( ph /\ ps ) ) ) ) `
     <TR> <TD> 4:3:      <TD> ` |- ( A. x ( ps -> A. x ps ) -> ( A. x ps -> `
     ` A. x ( ph -> ( ph /\ ps ) ) ) ) `
     <TR> <TD> 5::       <TD> ` |- (. A. x ( ps -> A. x ps ) ->. A. x ( ps `
     ` -> A. x ps ) ). `
     <TR> <TD> 6:4,5:    <TD> ` |- (. A. x ( ps -> A. x ps ) ->. ( A. x ps `
     ` -> A. x ( ph -> ( ph /\ ps ) ) ) ). `
     <TR> <TD> 7::       <TD> ` |- (. A. x ( ps -> A. x ps ) ,. A. x ps ->. `
     ` A. x ps ). `
     <TR> <TD> 8:6,7:    <TD> ` |- (. A. x ( ps -> A. x ps ) ,. A. x ps ->. `
     ` A. x ( ph -> ( ph /\ ps ) ) ). `
     <TR> <TD> 9:8:      <TD> ` |- (. A. x ( ps -> A. x ps ) ,. A. x ps ->. `
     ` ( E. x ph -> E. x ( ph /\ ps ) ) ). `
     <TR> <TD> 10:9:     <TD> ` |- (. A. x ( ps -> A. x ps ) ->. ( A. x ps `
     ` -> ( E. x ph -> E. x ( ph /\ ps ) ) ) ). `
     <TR> <TD> 11:5:     <TD> ` |- (. A. x ( ps -> A. x ps ) ->. ( ps -> A. `
     ` x ps ) ). `
     <TR> <TD> 12:10,11: <TD> ` |- (. A. x ( ps -> A. x ps ) ->. ( ps -> ( `
     ` E. x ph -> E. x ( ph /\ ps ) ) ) ). `
     <TR> <TD> 13:12:    <TD> ` |- (. A. x ( ps -> A. x ps ) ->. ( E. x ph `
     ` -> ( ps -> E. x ( ph /\ ps ) ) ) ). `
     <TR> <TD> 14:13:    <TD> ` |- (. A. x ( ps -> A. x ps ) ->. ( ( E. x `
     ` ph /\ ps ) -> E. x ( ph /\ ps ) ) ). `
     <TR> <TD> qed:14:   <TD> ` |- ( A. x ( ps -> A. x ps ) -> ( ( E. x ph `
     ` /\ ps ) -> E. x ( ph /\ ps ) ) ) `
     </TABLE> </HTML> $)
  19.41rgVD $p |- ( A. x ( ps -> A. x ps ) ->
                                ( ( E. x ph /\ ps ) -> E. x ( ph /\ ps ) ) ) $=
    ( wal wi wex wa idn1 pm3.2 com12 a1i ax-gen al2im e0a e1a idn2 id e12 exim
    e2 in2 sp imim2 e11 pm2.04 pm3.31 in1 ) BBCDZEZCDZACFZBGABGZCFZEZUJUKBUMEEZ
    UNUJBUKUMEZEZUOUJUHUPEUIUQUJUHUPUJUHAULEZCDZUPUJUHUSEZUHUHUSUJUJUTUJHZUIBUR
    EZEZCDUJUTEVCCVBUIABULABIJKLUIBURCMNOUJUHPUTQRAULCSTUAUJUJUIVAUICUBOUHUPBUC
    UDBUKUMUEOUKBUMUFOUG $.

  $( Virtual deduction proof of ~ 2pm13.193 .
     The following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.
     ~ 2pm13.193 is ~ 2pm13.193VD without virtual deductions and was
     automatically derived from ~ 2pm13.193VD .  (Contributed by Alan Sare,
     8-Feb-2014.)
     (Proof modification is discouraged.)  (New usage is discouraged.)
     <HTML> <TABLE>
     <TR> <TD> 1::        <TD> ` |- (. ( ( x = u /\ y = v ) /\ [ u / x ] [ `
     ` v / y ] ph ) ->. ( ( x = u /\ y = v ) /\ [ u / x ] [ v / y ] ph ) ). `
     <TR> <TD> 2:1:       <TD> ` |- (. ( ( x = u /\ y = v ) /\ [ u / x ] [ `
     ` v / y ] ph ) ->. ( x = u /\ y = v ) ). `
     <TR> <TD> 3:2:       <TD> ` |- (. ( ( x = u /\ y = v ) /\ [ u / x ] [ `
     ` v / y ] ph ) ->. x = u ). `
     <TR> <TD> 4:1:       <TD> ` |- (. ( ( x = u /\ y = v ) /\ [ u / x ] [ `
     ` v / y ] ph ) ->. [ u / x ] [ v / y ] ph ). `
     <TR> <TD> 5:3,4:     <TD> ` |- (. ( ( x = u /\ y = v ) /\ [ u / x ] [ `
     ` v / y ] ph ) ->. ( [ u / x ] [ v / y ] ph /\ x = u ) ). `
     <TR> <TD> 6:5:       <TD> ` |- (. ( ( x = u /\ y = v ) /\ [ u / x ] [ `
     ` v / y ] ph ) ->. ( [ v / y ] ph /\ x = u ) ). `
     <TR> <TD> 7:6:       <TD> ` |- (. ( ( x = u /\ y = v ) /\ [ u / x ] [ `
     ` v / y ] ph ) ->. [ v / y ] ph ). `
     <TR> <TD> 8:2:       <TD> ` |- (. ( ( x = u /\ y = v ) /\ [ u / x ] [ `
     ` v / y ] ph ) ->. y = v ). `
     <TR> <TD> 9:7,8:     <TD> ` |- (. ( ( x = u /\ y = v ) /\ [ u / x ] [ `
     ` v / y ] ph ) ->. ( [ v / y ] ph /\ y = v ) ). `
     <TR> <TD> 10:9:      <TD> ` |- (. ( ( x = u /\ y = v ) /\ [ u / x ] [ `
     ` v / y ] ph ) ->. ( ph /\ y = v ) ). `
     <TR> <TD> 11:10:     <TD> ` |- (. ( ( x = u /\ y = v ) /\ [ u / x ] [ `
     ` v / y ] ph ) ->. ph ). `
     <TR> <TD> 12:2,11:   <TD> ` |- (. ( ( x = u /\ y = v ) /\ [ u / x ] [ `
     ` v / y ] ph ) ->. ( ( x = u /\ y = v ) /\ ph ) ). `
     <TR> <TD> 13:12:     <TD> ` |- ( ( ( x = u /\ y = v ) /\ [ u / x ] [ v `
     ` / y ] ph ) -> ( ( x = u /\ y = v ) /\ ph ) ) `
     <TR> <TD> 14::       <TD> ` |- (. ( ( x = u /\ y = v ) /\ ph ) ->. ( ( `
     ` x = u /\ y = v ) /\ ph ) ). `
     <TR> <TD> 15:14:     <TD> ` |- (. ( ( x = u /\ y = v ) /\ ph ) ->. ( x `
     ` = u /\ y = v ) ). `
     <TR> <TD> 16:15:     <TD> ` |- (. ( ( x = u /\ y = v ) /\ ph ) ->. y = `
     ` v ). `
     <TR> <TD> 17:14:     <TD> ` |- (. ( ( x = u /\ y = v ) /\ ph ) ->. ph `
     ` ). `
     <TR> <TD> 18:16,17:  <TD> ` |- (. ( ( x = u /\ y = v ) /\ ph ) ->. ( `
     ` ph /\ y = v ) ). `
     <TR> <TD> 19:18:     <TD> ` |- (. ( ( x = u /\ y = v ) /\ ph ) ->. ( [ `
     ` v / y ] ph /\ y = v ) ). `
     <TR> <TD> 20:15:     <TD> ` |- (. ( ( x = u /\ y = v ) /\ ph ) ->. x = `
     ` u ). `
     <TR> <TD> 21:19:     <TD> ` |- (. ( ( x = u /\ y = v ) /\ ph ) ->. [ v `
     ` / y ] ph ). `
     <TR> <TD> 22:20,21:  <TD> ` |- (. ( ( x = u /\ y = v ) /\ ph ) ->. ( [ `
     ` v / y ] ph /\ x = u ) ). `
     <TR> <TD> 23:22:     <TD> ` |- (. ( ( x = u /\ y = v ) /\ ph ) ->. ( [ `
     ` u / x ] [ v / y ] ph /\ x = u ) ). `
     <TR> <TD> 24:23:     <TD> ` |- (. ( ( x = u /\ y = v ) /\ ph ) ->. [ u `
     ` / x ] [ v / y ] ph ). `
     <TR> <TD> 25:15,24:  <TD> ` |- (. ( ( x = u /\ y = v ) /\ ph ) ->. ( ( `
     ` x = u /\ y = v ) /\ [ u / x ] [ v / y ] ph ) ). `
     <TR> <TD> 26:25:     <TD> ` |- ( ( ( x = u /\ y = v ) /\ ph ) -> ( ( x `
     ` = u /\ y = v ) /\ [ u / x ] [ v / y ] ph ) ) `
     <TR> <TD> qed:13,26: <TD> ` |- ( ( ( x = u /\ y = v ) /\ [ u / x ] [ v `
     ` / y ] ph ) <-> ( ( x = u /\ y = v ) /\ ph ) ) `
     </TABLE> </HTML> $)
  2pm13.193VD $p |- ( ( ( x = u /\ y = v ) /\ [ u / x ] [ v / y ] ph ) <->
                                              ( ( x = u /\ y = v ) /\ ph ) ) $=
    ( cv wceq wa wsb idn1 simpl e1a simpr pm3.21 sbequ2 imdistanri pm3.2 sbequ1
    e11 in1 impbii ) BFEFGZCFDFGZHZACDIZBEIZHZUDAHZUGUHUGUDAUHUGUGUDUGJZUDUFKLZ
    UGAUCHZAUGUEUCHZUKUGUEUCULUGUEUBHZUEUGUFUBHZUMUGUBUFUNUGUDUBUJUBUCKZLUGUGUF
    UIUDUFMLUBUFNSUBUFUEUEBEOPLUEUBKLUGUDUCUJUBUCMZLUEUCQSUCUEAACDOPLAUCKLUDAQS
    TUHUGUHUDUFUGUHUHUDUHJZUDAKLZUHUNUFUHUMUNUHUBUEUMUHUDUBURUOLUHULUEUHUKULUHU
    CAUKUHUDUCURUPLUHUHAUQUDAMLUCANSUCAUEACDRPLUEUCKLUBUENSUBUEUFUEBERPLUFUBKLU
    DUFQSTUA $.

  $( Virtual deduction proof of ~ hbimpg .
     The following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.  ~ hbimpg
     is ~ hbimpgVD without virtual deductions and was automatically derived
     from ~ hbimpgVD .  (Contributed by Alan Sare, 8-Feb-2014.)
     (Proof modification is discouraged.)  (New usage is discouraged.)
     <HTML> <TABLE>
     <TR> <TD> 1::       <TD> ` |- (. ( A. x ( ph -> A. x ph ) /\ A. x ( ps `
     ` -> A. x ps ) ) ->. ( A. x ( ph -> A. x ph ) /\ A. x ( ps -> `
     ` A. x ps ) ) ). `
     <TR> <TD> 2:1:      <TD> ` |- (. ( A. x ( ph -> A. x ph ) /\ A. x ( ps `
     ` -> A. x ps ) ) ->. A. x ( ph -> A. x ph ) ). `
     <TR> <TD> 3::       <TD> ` |- (. ( A. x ( ph -> A. x ph ) /\ A. x ( ps `
     ` -> A. x ps ) ) , -. ph ->. -. ph ). `
     <TR> <TD> 4:2:      <TD> ` |- (. ( A. x ( ph -> A. x ph ) /\ A. x ( ps `
     ` -> A. x ps ) ) ->. A. x ( -. ph -> A. x -. ph ) ). `
     <TR> <TD> 5:4:      <TD> ` |- (. ( A. x ( ph -> A. x ph ) /\ A. x ( ps `
     ` -> A. x ps ) ) ->. ( -. ph -> A. x -. ph ) ). `
     <TR> <TD> 6:3,5:    <TD> ` |- (. ( A. x ( ph -> A. x ph ) /\ A. x ( ps `
     ` -> A. x ps ) ) , -. ph ->. A. x -. ph ). `
     <TR> <TD> 7::       <TD> ` |- ( -. ph -> ( ph -> ps ) ) `
     <TR> <TD> 8:7:      <TD> ` |- ( A. x -. ph -> A. x ( ph -> ps ) ) `
     <TR> <TD> 9:6,8:    <TD> ` |- (. ( A. x ( ph -> A. x ph ) /\ A. x ( ps `
     ` -> A. x ps ) ) , -. ph ->. A. x ( ph -> ps ) ). `
     <TR> <TD> 10:9:     <TD> ` |- (. ( A. x ( ph -> A. x ph ) /\ A. x ( ps `
     ` -> A. x ps ) ) ->. ( -. ph -> A. x ( ph -> ps ) ) ). `
     <TR> <TD> 11::      <TD> ` |- ( ps -> ( ph -> ps ) ) `
     <TR> <TD> 12:11:    <TD> ` |- ( A. x ps -> A. x ( ph -> ps ) ) `
     <TR> <TD> 13:1:     <TD> ` |- (. ( A. x ( ph -> A. x ph ) /\ A. x ( ps `
     ` -> A. x ps ) ) ->. A. x ( ps -> A. x ps ) ). `
     <TR> <TD> 14:13:    <TD> ` |- (. ( A. x ( ph -> A. x ph ) /\ A. x ( ps `
     ` -> A. x ps ) ) ->. ( ps -> A. x ps ) ). `
     <TR> <TD> 15:14,12: <TD> ` |- (. ( A. x ( ph -> A. x ph ) /\ A. x ( ps `
     ` -> A. x ps ) ) ->. ( ps -> A. x ( ph -> ps ) ) ). `
     <TR> <TD> 16:10,15: <TD> ` |- (. ( A. x ( ph -> A. x ph ) /\ A. x ( ps `
     ` -> A. x ps ) ) ->. ( ( -. ph \/ ps ) -> A. x ( ph -> ps ) ) ). `
     <TR> <TD> 17::      <TD> ` |- ( ( ph -> ps ) <-> ( -. ph \/ ps ) ) `
     <TR> <TD> 18:16,17: <TD> ` |- (. ( A. x ( ph -> A. x ph ) /\ A. x ( ps `
     ` -> A. x ps ) ) ->. ( ( ph -> ps ) -> A. x ( ph -> ps ) ) ). `
     <TR> <TD> 19::      <TD> ` |- ( A. x ( ph -> A. x ph ) -> A. x A. x ( `
     ` ph -> A. x ph ) ) `
     <TR> <TD> 20::      <TD> ` |- ( A. x ( ps -> A. x ps ) -> A. x A. x ( `
     ` ps -> A. x ps ) ) `
     <TR> <TD> 21:19,20: <TD> ` |- ( ( A. x ( ph -> A. x ph ) /\ A. x ( ps `
     ` -> A. x ps ) ) -> A. x ( A. x ( ph -> A. x ph ) /\ A. x ( ps -> `
     ` A. x ps ) ) ) `
     <TR> <TD> 22:21,18: <TD> ` |- (. ( A. x ( ph -> A. x ph ) /\ A. x ( ps `
     ` -> A. x ps ) ) ->. A. x ( ( ph -> ps ) -> A. x ( ph -> ps ) ) ). `
     <TR> <TD> qed:22:   <TD> ` |- ( ( A. x ( ph -> A. x ph ) /\ A. x ( ps `
     ` -> A. x ps ) ) -> A. x ( ( ph -> ps ) -> A. x ( ph -> ps ) ) ) `
     </TABLE> </HTML> $)
  hbimpgVD $p |- ( ( A. x ( ph -> A. x ph ) /\ A. x ( ps -> A. x ps ) ) ->
                                A. x ( ( ph -> ps ) -> A. x ( ph -> ps ) ) ) $=
    ( wal wi wa hba1 hban wn wo wb idn2 idn1 simpl e1a hbntal pm2.27 alimi e10
    sp e21 pm2.21 in2 simpr ax-1 imim1 jao e11 imor imbi1 biimprcd gen11nv in1
    e2 ) AACDEZCDZBBCDZEZCDZFZABEZVACDZEZCDUTVCCUPUSCUOCGURCGHUTAIZBJZVBEZVAVEK
    ZVCUTVDVBEBVBEZVFUTVDVBUTVDVDCDZVBUTVDVDVDVIEZVIUTVDLUTVJCDZVJUTUPVKUTUTUPU
    TMZUPUSNOACPOVJCTOVDVIQUAVDVACABUBRUNUCUTURUQVBEVHUTUSURUTUTUSVLUPUSUDOURCT
    OBVACBAUERBUQVBUFSVDVBBUGUHABUIVGVCVFVAVEVBUJUKSULUM $.

  $( Virtual deduction proof of ~ hbalg .
     The following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.  ~ hbalg
     is ~ hbalgVD without virtual deductions and was automatically derived
     from ~ hbalgVD .  (Contributed by Alan Sare, 8-Feb-2014.)
     (Proof modification is discouraged.)  (New usage is discouraged.)
     <HTML> <TABLE>
     <TR> <TD> 1::        <TD> ` |- (. A. y ( ph -> A. x ph ) ->. A. y ( ph `
     ` -> A. x ph ) ). `
     <TR> <TD> 2:1:       <TD> ` |- (. A. y ( ph -> A. x ph ) ->. ( A. y ph `
     ` -> A. y A. x ph ) ). `
     <TR> <TD> 3::        <TD> ` |- ( A. y A. x ph -> A. x A. y ph ) `
     <TR> <TD> 4:2,3:     <TD> ` |- (. A. y ( ph -> A. x ph ) ->. ( A. y ph `
     ` -> A. x A. y ph ) ). `
     <TR> <TD> 5::        <TD> ` |- ( A. y ( ph -> A. x ph ) -> A. y A. y ( `
     ` ph -> A. x ph ) ) `
     <TR> <TD> 6:5,4:     <TD> ` |- (. A. y ( ph -> A. x ph ) ->. A. y ( A. `
     ` y ph -> A. x A. y ph ) ). `
     <TR> <TD> qed:6:     <TD> ` |- ( A. y ( ph -> A. x ph ) -> A. y ( A. y `
     ` ph -> A. x A. y ph ) ) `
     </TABLE> </HTML> $)
  hbalgVD $p |- ( A. y ( ph -> A. x ph ) ->
                                          A. y ( A. y ph -> A. x A. y ph ) ) $=
    ( wal wi hba1 idn1 alim e1a ax-11 imim1 e10 gen11nv in1 ) AABDZEZCDZACDZRBD
    ZEZCDQTCPCFQROCDZEZUASETQQUBQGAOCHIACBJRUASKLMN $.

  $( Virtual deduction proof of ~ hbexg .
     The following User's Proof is a Virtual Deduction proof completed
     automatically by the tools program completeusersproof.cmd, which invokes
     Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof Assistant.  ~ hbexg
     is ~ hbexgVD without virtual deductions and was automatically derived
     from ~ hbexgVD .  (Contributed by Alan Sare, 8-Feb-2014.)
     (Proof modification is discouraged.)  (New usage is discouraged.)
     <HTML> <TABLE>
     <TR> <TD> 1::        <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. A. x `
     ` A. y ( ph -> A. x ph ) ). `
     <TR> <TD> 2:1:       <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. A. y `
     ` A. x ( ph -> A. x ph ) ). `
     <TR> <TD> 3:2:       <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. A. x `
     ` ( ph -> A. x ph ) ). `
     <TR> <TD> 4:3:       <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. A. x `
     ` ( -. ph -> A. x -. ph ) ). `
     <TR> <TD> 5::        <TD> ` |- ( A. x A. y ( ph -> A. x ph ) <-> A. y `
     ` A. x ( ph -> A. x ph ) ) `
     <TR> <TD> 6::        <TD> ` |- ( A. y A. x ( ph -> A. x ph ) -> A. y `
     ` A. y A. x ( ph -> A. x ph ) ) `
     <TR> <TD> 7:5:       <TD> ` |- ( A. y A. x A. y ( ph -> A. x ph ) <-> `
     ` A. y A. y A. x ( ph -> A. x ph ) ) `
     <TR> <TD> 8:5,6,7:   <TD> ` |- ( A. x A. y ( ph -> A. x ph ) -> A. y `
     ` A. x A. y ( ph -> A. x ph ) ) `
     <TR> <TD> 9:8,4:     <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. A. y `
     ` A. x ( -. ph -> A. x -. ph ) ). `
     <TR> <TD> 10:9:      <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. A. x `
     ` A. y ( -. ph -> A. x -. ph ) ). `
     <TR> <TD> 11:10:     <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. A. y `
     ` ( -. ph -> A. x -. ph ) ). `
     <TR> <TD> 12:11:     <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. A. y `
     ` ( A. y -. ph -> A. x A. y -. ph ) ). `
     <TR> <TD> 13:12:     <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. ( A. `
     ` y -. ph -> A. x A. y -. ph ) ). `
     <TR> <TD> 14::       <TD> ` |- ( A. x A. y ( ph -> A. x ph ) -> A. x `
     ` A. x A. y ( ph -> A. x ph ) ) `
     <TR> <TD> 15:13,14:  <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. A. x `
     ` ( A. y -. ph -> A. x A. y -. ph ) ). `
     <TR> <TD> 16:15:     <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. A. x `
     ` ( -. A. y -. ph -> A. x -. A. y -. ph ) ). `
     <TR> <TD> 17:16:     <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. ( -. `
     ` A. y -. ph -> A. x -. A. y -. ph ) ). `
     <TR> <TD> 18::       <TD> ` |- ( E. y ph <-> -. A. y -. ph ) `
     <TR> <TD> 19:17,18:  <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. ( E. `
     ` y ph -> A. x -. A. y -. ph ) ). `
     <TR> <TD> 20:18:     <TD> ` |- ( A. x E. y ph <-> A. x -. A. y -. ph ) `
     <TR> <TD> 21:19,20:  <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. ( E. `
     ` y ph -> A. x E. y ph ) ). `
     <TR> <TD> 22:8,21:   <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. A. y `
     ` ( E. y ph -> A. x E. y ph ) ). `
     <TR> <TD> 23:14,22:  <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. A. x `
     ` A. y ( E. y ph -> A. x E. y ph ) ). `
     <TR> <TD> qed:23:    <TD> ` |- (. A. x A. y ( ph -> A. x ph ) ->. A. x `
     ` A. y ( E. y ph -> A. x E. y ph ) ). `
     </TABLE> </HTML> $)
  hbexgVD $p |- ( A. x A. y ( ph -> A. x ph ) ->
                                     A. x A. y ( E. y ph -> A. x E. y ph ) ) $=
    ( wal wi wex hba1 alcom albii 3imtr4i wn wb idn1 ax-11 e1a gen11nv biimprcd
    sp hbntal e10 hbalg df-ex imbi1 imbi2 in1 ) AABDEZCDZBDZACFZUIBDZEZCDZBDUHU
    LBUGBGZUHUKCUFBDZCDZUOCDUHUHCDUNCGUFBCHZUHUOCUPIJZUHUIAKZCDZKZBDZEZUJVALZUK
    UHUTVAEZUIUTLZVBUHVDBDZVDUHUSUSBDEZBDVFUHVGBUMUHVGCDZVGUHURURBDEZCDZVHUHVJB
    DZVJUHVIBDZCDVKUHVLCUQUHUNVLUHUOUNUHUHUOUHMUFBCNOUNCROABSOPVICBNOVJBROURBCU
    AOVGCROPUSBSOVDBROACUBZVEVBVDUIUTVAUCQTUIUTBVMIVCUKVBUJVAUIUDQTPPUE $.

  ${
    $d u x $.  $d u y $.  $d v x $.  $d v y $.
    $( The following User's Proof is a Virtual Deduction proof (see ~ wvd1 )
       completed automatically by a Metamath tools program invoking mmj2 and
       the Metamath Proof Assistant.  ~ ax6e2eq is ~ ax6e2eqVD without virtual
       deductions and was automatically derived from ~ ax6e2eqVD .
       (Contributed by Alan Sare, 25-Mar-2014.)
       (Proof modification is discouraged.)  (New usage is discouraged.)
       <HTML> <TABLE>
       <TR> <TD> 1::        <TD> ` |- (. A. x x = y ->. A. x x = y ). `
       <TR> <TD> 2::        <TD> ` |- (. A. x x = y ,. x = u ->. x = u ). `
       <TR> <TD> 3:1:       <TD> ` |- (. A. x x = y ->. x = y ). `
       <TR> <TD> 4:2,3:     <TD> ` |- (. A. x x = y ,. x = u ->. y = u ). `
       <TR> <TD> 5:2,4:     <TD> ` |- (. A. x x = y ,. x = u ->. ( x = u /\ y `
       ` = u ) ). `
       <TR> <TD> 6:5:       <TD> ` |- (. A. x x = y ->. ( x = u -> ( x = u /\ `
       ` y = u ) ) ). `
       <TR> <TD> 7:6:       <TD> ` |- ( A. x x = y -> ( x = u -> ( x = u /\ y `
       ` = u ) ) ) `
       <TR> <TD> 8:7:       <TD> ` |- ( A. x A. x x = y -> A. x ( x = u -> ( `
       ` x = u /\ y = u ) ) ) `
       <TR> <TD> 9::        <TD> ` |- ( A. x x = y <-> A. x A. x x = y ) `
       <TR> <TD> 10:8,9:    <TD> ` |- ( A. x x = y -> A. x ( x = u -> ( x = u `
       ` /\ y = u ) ) ) `
       <TR> <TD> 11:1,10:   <TD> ` |- (. A. x x = y ->. A. x ( x = u -> ( x = `
       ` u /\ y = u ) ) ). `
       <TR> <TD> 12:11:     <TD> ` |- (. A. x x = y ->. ( E. x x = u -> E. x `
       ` ( x = u /\ y = u ) ) ). `
       <TR> <TD> 13::       <TD> ` |- E. x x = u `
       <TR> <TD> 14:13,12:  <TD> ` |- (. A. x x = y ->. E. x ( x = u /\ y = u `
       ` ) ). `
       <TR> <TD> 140:14:    <TD> ` |- ( A. x x = y -> E. x ( x = u /\ y = u ) `
       ` ) `
       <TR> <TD> 141:140:   <TD> ` |- ( A. x x = y -> A. x E. x ( x = u /\ y `
       ` = u ) ) `
       <TR> <TD> 15:1,141:  <TD> ` |- (. A. x x = y ->. A. x E. x ( x = u /\ `
       ` y = u ) ). `
       <TR> <TD> 16:1,15:   <TD> ` |- (. A. x x = y ->. A. y E. x ( x = u /\ `
       ` y = u ) ). `
       <TR> <TD> 17:16:     <TD> ` |- (. A. x x = y ->. E. y E. x ( x = u /\ `
       ` y = u ) ). `
       <TR> <TD> 18:17:     <TD> ` |- (. A. x x = y ->. E. x E. y ( x = u /\ `
       ` y = u ) ). `
       <TR> <TD> 19::       <TD> ` |- (. u = v ->. u = v ). `
       <TR> <TD> 20::       <TD> ` |- (. u = v ,. ( x = u /\ y = u ) ->. ( x =
       `
       ` u /\ y = u ) ). `
       <TR> <TD> 21:20:     <TD> ` |- (. u = v ,. ( x = u /\ y = u ) ->. y = u
       `
       ` ). `
       <TR> <TD> 22:19,21:  <TD> ` |- (. u = v ,. ( x = u /\ y = u ) ->. y = v
       `
       ` ). `
       <TR> <TD> 23:20:     <TD> ` |- (. u = v ,. ( x = u /\ y = u ) ->. x = u
       `
       ` ). `
       <TR> <TD> 24:22,23:  <TD> ` |- (. u = v ,. ( x = u /\ y = u ) ->. ( x =
       `
       ` u /\ y = v ) ). `
       <TR> <TD> 25:24:     <TD> ` |- (. u = v ->. ( ( x = u /\ y = u ) -> ( `
       ` x = u /\ y = v ) ) ). `
       <TR> <TD> 26:25:     <TD> ` |- (. u = v ->. A. y ( ( x = u /\ y = u ) `
       ` -> ( x = u /\ y = v ) ) ). `
       <TR> <TD> 27:26:     <TD> ` |- (. u = v ->. ( E. y ( x = u /\ y = u ) `
       ` -> E. y ( x = u /\ y = v ) ) ). `
       <TR> <TD> 28:27:     <TD> ` |- (. u = v ->. A. x ( E. y ( x = u /\ y = `
       ` u ) -> E. y ( x = u /\ y = v ) ) ). `
       <TR> <TD> 29:28:     <TD> ` |- (. u = v ->. ( E. x E. y ( x = u /\ y = `
       ` u ) -> E. x E. y ( x = u /\ y = v ) ) ). `
       <TR> <TD> 30:29:     <TD> ` |- ( u = v -> ( E. x E. y ( x = u /\ y = u `
       ` ) -> E. x E. y ( x = u /\ y = v ) ) ) `
       <TR> <TD> 31:18,30:  <TD> ` |- (. A. x x = y ->. ( u = v -> E. x E. y `
       ` ( x = u /\ y = v ) ) ). `
       <TR> <TD> qed:31:    <TD> ` |- ( A. x x = y -> ( u = v -> E. x E. y ( `
       ` x = u /\ y = v ) ) ) `
       </TABLE> </HTML> $)
    ax6e2eqVD $p |- ( A. x x = y ->
                                 ( u = v -> E. x E. y ( x = u /\ y = v ) ) ) $=
      ( cv wceq wal wa wex wi idn1 sp idn2 e1a com12 e22 in2 in1 exim e2 impbii
      ax6ev hba1 ax7 e21 pm3.2 alimi sylbi pm2.27 e01 axc4i axc11 excomim simpr
      e11 19.2 equtrr e12 simpl pm3.21 gen11 pm2.04 e10 ) AEZBEZFZAGZDEZCEZFZVD
      VHFZVEVIFZHZBIZAIZJZVGVKVEVHFZHZBIZAIZVJVTVOJZJZVPVGVRAIZBIZVTVGWCBGZWDVG
      VGWCAGZWEVGKZVGVGWFWGVFWCAVGWCVKAIZVGWHWCJZWCADUBVGVKVRJZAGZWIVGVGWKWGVGV
      GAGZWKVGWLVFAUCVGALUAVGWJAVGWJVGVKVRVGVKVKVQVRVGVKMZVGVKVKVFVQWMVGVGVFWGV
      FALNVFVKVQABDUDOUEVKVQUFPQRUGUHNVKVRASNWHWCUIUJRUKNWCABULUOWCBUPNVRBAUMNV
      JWAVJVSVNJZAGWAVJWNAVJVRVMJZBGWNVJWOBVJVRVMVJVRVLVKVMVJVJVRVQVLVJKVJVRVRV
      QVJVRMZVKVQUNTDCBUQURVJVRVRVKWPVKVQUSTVLVKUTPQVAVRVMBSNVAVSVNASNRWBVTVPVJ
      VTVOVBOVCR $.
  $}

  ${
    $d u x $.  $d u y $.  $d v x z $.  $d y z $.
    $( The following User's Proof is a Virtual Deduction proof (see ~ wvd1 )
       completed automatically by a Metamath tools program invoking mmj2 and
       the Metamath Proof Assistant.  ~ ax6e2nd is ~ ax6e2ndVD without virtual
       deductions and was automatically derived from ~ ax6e2ndVD .
       (Contributed by Alan Sare, 25-Mar-2014.)
       (Proof modification is discouraged.)  (New usage is discouraged.)
       <HTML> <TABLE>
       <TR> <TD> 1::          <TD> ` |- E. y y = v `
       <TR> <TD> 2::          <TD> ` |- u e. _V `
       <TR> <TD> 3:1,2:       <TD> ` |- ( u e. _V /\ E. y y = v ) `
       <TR> <TD> 4:3:         <TD> ` |- E. y ( u e. _V /\ y = v ) `
       <TR> <TD> 5::          <TD> ` |- ( u e. _V <-> E. x x = u ) `
       <TR> <TD> 6:5:         <TD> ` |- ( ( u e. _V /\ y = v ) <-> ( E. x x = `
       ` u /\ y = v ) ) `
       <TR> <TD> 7:6:         <TD> ` |- ( E. y ( u e. _V /\ y = v ) <-> E. y `
       ` ( E. x x = u /\ y = v ) ) `
       <TR> <TD> 8:4,7:       <TD> ` |- E. y ( E. x x = u /\ y = v ) `
       <TR> <TD> 9::          <TD> ` |- ( z = v -> A. x z = v ) `
       <TR> <TD> 10::         <TD> ` |- ( y = v -> A. z y = v ) `
       <TR> <TD> 11::         <TD> ` |- (. z = y ->. z = y ). `
       <TR> <TD> 12:11:       <TD> ` |- (. z = y ->. ( z = v <-> y = v ) ). `
       <TR> <TD> 120:11:      <TD> ` |- ( z = y -> ( z = v <-> y = v ) ) `
       <TR> <TD> 13:9,10,120: <TD> ` |- ( -. A. x x = y -> ( y = v -> A. x y `
       ` = v ) ) `
       <TR> <TD> 14::         <TD> ` |- (. -. A. x x = y ->. -. A. x x = y ). `
       <TR> <TD> 15:14,13:    <TD> ` |- (. -. A. x x = y ->. ( y = v -> A. x `
       ` y = v ) ). `
       <TR> <TD> 16:15:       <TD> ` |- ( -. A. x x = y -> ( y = v -> A. x y `
       ` = v ) ) `
       <TR> <TD> 17:16:       <TD> ` |- ( A. x -. A. x x = y -> A. x ( y = v `
       ` -> A. x y = v ) ) `
       <TR> <TD> 18::         <TD> ` |- ( -. A. x x = y -> A. x -. A. x x = y `
       ` ) `
       <TR> <TD> 19:17,18:    <TD> ` |- ( -. A. x x = y -> A. x ( y = v -> A. `
       ` x y = v ) ) `
       <TR> <TD> 20:14,19:    <TD> ` |- (. -. A. x x = y ->. A. x ( y = v -> `
       ` A. x y = v ) ). `
       <TR> <TD> 21:20:       <TD> ` |- (. -. A. x x = y ->. ( ( E. x x = u `
       ` /\ y = v ) -> E. x ( x = u /\ y = v ) ) ). `
       <TR> <TD> 22:21:       <TD> ` |- ( -. A. x x = y -> ( ( E. x x = u /\ `
       ` y = v ) -> E. x ( x = u /\ y = v ) ) ) `
       <TR> <TD> 23:22:       <TD> ` |- ( A. y -. A. x x = y -> A. y ( ( E. x `
       ` x = u /\ y = v ) -> E. x ( x = u /\ y = v ) ) ) `
       <TR> <TD> 24::         <TD> ` |- ( -. A. x x = y -> A. y -. A. x x = y `
       ` ) `
       <TR> <TD> 25:23,24:    <TD> ` |- ( -. A. x x = y -> A. y ( ( E. x x = `
       ` u /\ y = v ) -> E. x ( x = u /\ y = v ) ) ) `
       <TR> <TD> 26:14,25:    <TD> ` |- (. -. A. x x = y ->. A. y ( ( E. x x `
       ` = u /\ y = v ) -> E. x ( x = u /\ y = v ) ) ). `
       <TR> <TD> 27:26:       <TD> ` |- (. -. A. x x = y ->. ( E. y ( E. x x `
       ` = u /\ y = v ) -> E. y E. x ( x = u /\ y = v ) ) ). `
       <TR> <TD> 28:8,27:     <TD> ` |- (. -. A. x x = y ->.  E. y E. x ( x = `
       ` u /\ y = v ) ). `
       <TR> <TD> 29:28:       <TD> ` |- (. -. A. x x = y ->.  E. x E. y ( x = `
       ` u /\ y = v ) ). `
       <TR> <TD> qed:29:      <TD> ` |- ( -. A. x x = y -> E. x E. y ( x = u `
       ` /\ y = v ) ) `
       </TABLE> </HTML> $)
    ax6e2ndVD $p |- ( -. A. x x = y -> E. x E. y ( x = u /\ y = v ) ) $=
      ( vz cv wceq wal wn wa wex wi cvv wcel idn1 ax-5 e1a in1 alimi syl pm3.2i
      vex ax6e 19.42v biimpri e0a isset anbi1i exbii mpbi hbnae hbn1 wb equequ1
      dvelimh 19.41rg exim pm2.27 e01 excomim ) AFZBFZGZAHIZVADFZGZVBCFZGZJZBKA
      KZVDVIAKZBKZVJVFAKZVHJZBKZVDVOVLLZVLVEMNZVHJZBKZVOVQVHBKZJZVSVQVTDUBBCUCU
      AVSWAVQVHBUDUEUFVRVNBVQVMVHAVEUGUHUIUJVDVNVKLZBHZVPVDVDWCVDOZVDVDBHWCABBU
      KVDWBBVDWBVDVHVHAHLZAHZWBVDVDWFWDVDVDAHWFVCAULVDWEAVDWEVDVDWEWDEFZVGGZVHA
      BEWHAPVHEPWGVBGZWHVHUMZWIWIWJWIOEBCUNQRUOQRSTQVFVHAUPQRSTQVNVKBUQQVOVLURU
      SVIBAUTQR $.
  $}

  ${
    $d u x $.  $d u y $.  $d v x $.  $d v y $.
    $( The following User's Proof is a Virtual Deduction proof (see ~ wvd1 )
       completed automatically by a Metamath tools program invoking mmj2 and
       the Metamath Proof Assistant. ~ ax6e2eq is ~ ax6e2ndeqVD without virtual
       deductions and was automatically derived from ~ ax6e2ndeqVD .
       (Contributed by Alan Sare, 25-Mar-2014.)
       (Proof modification is discouraged.)  (New usage is discouraged.)
       <HTML> <TABLE>
       <TR> <TD> 1::          <TD> ` |- (. u =/= v ->. u =/= v ). `
       <TR> <TD> 2::          <TD> ` |- (. u =/= v ,. ( x = u /\ y = v ) ->. (
       `
       ` x = u /\ y = v ) ). `
       <TR> <TD> 3:2:         <TD> ` |- (. u =/= v ,. ( x = u /\ y = v ) ->. x
       `
       ` = u ). `
       <TR> <TD> 4:1,3:       <TD> ` |- (. u =/= v ,. ( x = u /\ y = v ) ->. x
       `
       ` =/= v ). `
       <TR> <TD> 5:2:         <TD> ` |- (. u =/= v ,. ( x = u /\ y = v ) ->. y
       `
       ` = v ). `
       <TR> <TD> 6:4,5:       <TD> ` |- (. u =/= v ,. ( x = u /\ y = v ) ->. x
       `
       ` =/= y ). `
       <TR> <TD> 7::          <TD> ` |- ( A. x x = y -> x = y ) `
       <TR> <TD> 8:7:         <TD> ` |- ( -. x = y -> -. A. x x = y ) `
       <TR> <TD> 9::          <TD> ` |- ( -. x = y <-> x =/= y ) `
       <TR> <TD> 10:8,9:      <TD> ` |- ( x =/= y -> -. A. x x = y ) `
       <TR> <TD> 11:6,10:     <TD> ` |- (. u =/= v ,. ( x = u /\ y = v ) ->. `
       ` -. A. x x = y ). `
       <TR> <TD> 12:11:       <TD> ` |- (. u =/= v ->. ( ( x = u /\ y = v ) `
       ` -> -. A. x x = y ) ). `
       <TR> <TD> 13:12:       <TD> ` |- (. u =/= v ->. A. x ( ( x = u /\ y = `
       ` v ) -> -. A. x x = y ) ). `
       <TR> <TD> 14:13:       <TD> ` |- (. u =/= v ->. ( E. x ( x = u /\ y = `
       ` v ) -> E. x -. A. x x = y ) ). `
       <TR> <TD> 15::         <TD> ` |- ( -. A. x x = y -> A. x -. A. x x = y `
       ` ) `
       <TR> <TD> 19:15:       <TD> ` |- ( E. x -. A. x x = y <-> -. A. x x = `
       ` y ) `
       <TR> <TD> 20:14,19:    <TD> ` |- (. u =/= v ->. ( E. x ( x = u /\ y = `
       ` v ) -> -. A. x x = y ) ). `
       <TR> <TD> 21:20:       <TD> ` |- (. u =/= v ->. A. y ( E. x ( x = u /\ `
       ` y = v ) -> -. A. x x = y ) ). `
       <TR> <TD> 22:21:       <TD> ` |- (. u =/= v ->. ( E. y E. x ( x = u /\ `
       ` y = v ) -> E. y -. A. x x = y ) ). `
       <TR> <TD> 23::         <TD> ` |- ( E. x E. y ( x = u /\ y = v ) <-> E. `
       ` y E. x ( x = u /\ y = v ) ) `
       <TR> <TD> 24:22,23:    <TD> ` |- (. u =/= v ->. ( E. x E. y ( x = u /\ `
       ` y = v ) -> E. y -. A. x x = y ) ). `
       <TR> <TD> 25::         <TD> ` |- ( -. A. x x = y -> A. y -. A. x x = y `
       ` ) `
       <TR> <TD> 26:25:       <TD> ` |- ( E. y -. A. x x = y -> E. y A. y -. `
       ` A. x x = y ) `
       <TR> <TD> 260::        <TD> ` |- ( A. y -. A. x x = y -> A. y A. y -. `
       ` A. x x = y ) `
       <TR> <TD> 27:260:      <TD> ` |- ( E. y A. y -. A. x x = y <-> A. y -. `
       ` A. x x = y ) `
       <TR> <TD> 270:26,27:   <TD> ` |- ( E. y -. A. x x = y -> A. y -. A. x `
       ` x = y ) `
       <TR> <TD> 28::         <TD> ` |- ( A. y -. A. x x = y -> -. A. x x = y `
       ` ) `
       <TR> <TD> 29:270,28:   <TD> ` |- ( E. y -. A. x x = y -> -. A. x x = y `
       ` ) `
       <TR> <TD> 30:24,29:    <TD> ` |- (. u =/= v ->. ( E. x E. y ( x = u /\ `
       ` y = v ) -> -. A. x x = y ) ). `
       <TR> <TD> 31:30:       <TD> ` |- (. u =/= v ->. ( E. x E. y ( x = u /\ `
       ` y = v ) -> ( -. A. x x = y \/ u = v ) ) ). `
       <TR> <TD> 32:31:       <TD> ` |- ( u =/= v -> ( E. x E. y ( x = u /\ y `
       ` = v ) -> ( -. A. x x = y \/ u = v ) ) ) `
       <TR> <TD> 33::         <TD> ` |- (. u = v ->. u = v ). `
       <TR> <TD> 34:33:       <TD> ` |- (. u = v ->. ( E. x E. y ( x = u /\ y `
       ` = v ) -> u = v ) ). `
       <TR> <TD> 35:34:       <TD> ` |- (. u = v ->. ( E. x E. y ( x = u /\ y `
       ` = v ) -> ( -. A. x x = y \/ u = v ) ) ). `
       <TR> <TD> 36:35:       <TD> ` |- ( u = v -> ( E. x E. y ( x = u /\ y = `
       ` v ) -> ( -. A. x x = y \/ u = v ) ) ) `
       <TR> <TD> 37::         <TD> ` |- ( u = v \/ u =/= v ) `
       <TR> <TD> 38:32,36,37: <TD> ` |- ( E. x E. y ( x = u /\ y = v ) -> ( `
       ` -. A. x x = y \/ u = v ) ) `
       <TR> <TD> 39::         <TD> ` |- ( A. x x = y -> ( u = v -> E. x E. y `
       ` ( x = u /\ y = v ) ) ) `
       <TR> <TD> 40::         <TD> ` |- ( -. A. x x = y -> E. x E. y ( x = u `
       ` /\ y = v ) ) `
       <TR> <TD> 41:40:       <TD> ` |- ( -. A. x x = y -> ( u = v -> E. x E. `
       ` y ( x = u /\ y = v ) ) ) `
       <TR> <TD> 42::         <TD> ` |- ( A. x x = y \/ -. A. x x = y ) `
       <TR> <TD> 43:39,41,42: <TD> ` |- ( u = v -> E. x E. y ( x = u /\ y = v `
       ` ) ) `
       <TR> <TD> 44:40,43:    <TD> ` |- ( ( -. A. x x = y \/ u = v ) -> E. x `
       ` E. y ( x = u /\ y = v ) ) `
       <TR> <TD> qed:38,44:   <TD> ` |- ( ( -. A. x x = y \/ u = v ) <-> E. x `
       ` E. y ( x = u /\ y = v ) ) `
       </TABLE> </HTML> $)
    ax6e2ndeqVD $p |- ( ( -. A. x x = y \/ u = v ) <->
                                              E. x E. y ( x = u /\ y = v ) ) $=
      ( cv wceq wal wn wo wex wi jao e000 wne wb idn1 e2 biimprcd e1a e10 exmid
      wa ax6e2nd ax6e2eq a1d jaoi idn2 simpl neeq1 e12 simpr neeq2 df-ne bicomi
      e22 sp con3i sylbir gen11 exim nfnae 19.9 imbi2 biimpcd excom imbi1 hbnae
      in2 eximi nfa1 sylib syl imim1 orc imim2i in1 ax-1 exmidne com12 impbii
      olc ) AEZBEZFZAGZHZDEZCEZFZIZWBWGFZWCWHFZUBZBJAJZWFWNWIABCDUCZWEWIWNKZKWF
      WPKWEWFIWPABCDUDWFWNWIWOUEWEUAWEWPWFLMUFWGWHNZWNWJKZKZWIWRKZWIWQIZWRWQWRW
      QWNWFKZWRWQWNWFBJZKZXCWFKXBWQWMAJZBJZXCKZWNXFOZXDWQXEWFKZBGXGWQXIBWQXEWFA
      JZKZXJWFOZXIWQWMWFKZAGXKWQXMAWQWMWFWQWMWBWCNZWFWQWMWBWHNZWLXNWQWQWMWKXOWQ
      PWQWMWMWKWQWMUGZWKWLUHQWKXOWQWBWGWHUIRUJWQWMWMWLXPWKWLUKQWLXNXOWCWHWBULRU
      OXNWDHZWFXNXQWBWCUMUNWEWDWDAUPUQURQVHUSWMWFAUTSWFAABAVAVBXLXKXIXJWFXEVCVD
      TUSXEWFBUTSWMABVEXHXDXGWNXFXCVFRTXCWFBGZWFXCXRBJXRWFXRBABBVGVIXRBWFBVJVBV
      KWFBUPVLWNXCWFVMTWFWJWNWFWIVNVOSVPWIWRWIWNWIKZWRWIWIXSWIPWIWNVQSWIWJWNWIW
      FWAVOSVPWGWHVRWTWSXAWRKWIWRWQLVSMVT $.
  $}

  ${
    $d u x $.  $d u y $.  $d v x $.  $d v y $.
    $( The following User's Proof is a Virtual Deduction proof (see ~ wvd1 )
       completed automatically by a Metamath tools program invoking mmj2 and
       the Metamath Proof Assistant.  ~ 2sb5nd is ~ 2sb5ndVD without virtual
       deductions and was automatically derived from ~ 2sb5ndVD .
       (Contributed by Alan Sare, 30-Apr-2014.)
       (Proof modification is discouraged.)  (New usage is discouraged.)
       <HTML> <TABLE>
       <TR> <TD> 1::          <TD> ` |- ( ( ( x = u /\ y = v ) /\ [ u / x ] [ `
       ` v / y ] ph ) <-> ( ( x = u /\ y = v ) /\ ph ) ) `
       <TR> <TD> 2:1:         <TD> ` |- ( E. y ( ( x = u /\ y = v ) /\ [ u / `
       ` x ] [ v / y ] ph ) <-> E. y ( ( x = u /\ y = v ) /\ ph ) ) `
       <TR> <TD> 3::          <TD> ` |- ( [ v / y ] ph -> A. y [ v / y ] ph ) `
       <TR> <TD> 4:3:         <TD> ` |- [ u / x ] ( [ v / y ] ph -> A. y [ v `
       ` / y ] ph ) `
       <TR> <TD> 5:4:         <TD> ` |- ( [ u / x ] [ v / y ] ph -> [ u / x ] `
       ` A. y [ v / y ] ph ) `
       <TR> <TD> 6::          <TD> ` |- (. -. A. x x = y ->. -. A. x x = y ). `
       <TR> <TD> 7::          <TD> ` |- ( A. y y = x -> A. x x = y ) `
       <TR> <TD> 8:7:         <TD> ` |- ( -. A. x x = y -> -. A. y y = x ) `
       <TR> <TD> 9:6,8:       <TD> ` |- (. -. A. x x = y ->. -. A. y y = x ). `
       <TR> <TD> 10:9:        <TD> ` |- ( [ u / x ] A. y [ v / y ] ph <-> A. `
       ` y [ u / x ] [ v / y ] ph ) `
       <TR> <TD> 11:5,10:     <TD> ` |- ( [ u / x ] [ v / y ] ph -> A. y [ u `
       ` / x ] [ v / y ] ph ) `
       <TR> <TD> 12:11:       <TD> ` |- ( -. A. x x = y -> ( [ u / x ] [ v / `
       ` y ] ph -> A. y [ u / x ] [ v / y ] ph ) ) `
       <TR> <TD> 13::         <TD> ` |- ( [ u / x ] [ v / y ] ph -> A. x [ u `
       ` / x ] [ v / y ] ph ) `
       <TR> <TD> 14::         <TD> ` |- (. A. x x = y ->. A. x x = y ). `
       <TR> <TD> 15:14:       <TD> ` |- (. A. x x = y ->. ( A. x [ u / x ] [ `
       ` v / y ] ph -> A. y [ u / x ] [ v / y ] ph ) ). `
       <TR> <TD> 16:13,15:    <TD> ` |- (. A. x x = y ->. ( [ u / x ] [ v / y `
       ` ] ph -> A. y [ u / x ] [ v / y ] ph ) ). `
       <TR> <TD> 17:16:       <TD> ` |- ( A. x x = y -> ( [ u / x ] [ v / y ] `
       ` ph -> A. y [ u / x ] [ v / y ] ph ) ) `
       <TR> <TD> 19:12,17:    <TD> ` |- ( [ u / x ] [ v / y ] ph -> A. y [ u `
       ` / x ] [ v / y ] ph ) `
       <TR> <TD> 20:19:       <TD> ` |- ( E. y ( ( x = u /\ y = v ) /\ [ u / `
       ` x ] [ v / y ] ph )  <-> ( E. y ( x = u /\ y = v ) /\ `
       ` [ u / x ] [ v / y ] ph ) ) `
       <TR> <TD> 21:2,20:     <TD> ` |- ( E. y ( ( x = u /\ y = v ) /\ ph ) `
       ` <-> ( E. y ( x = u /\ y = v ) /\ [ u / x ] [ v / y ] ph ) ) `
       <TR> <TD> 22:21:       <TD> ` |- ( E. x E. y ( ( x = u /\ y = v ) /\ `
       ` ph ) <-> E. x ( E. y ( x = u /\ y = v ) /\ `
       ` [ u / x ] [ v / y ] ph ) ) `
       <TR> <TD> 23:13:       <TD> ` |- ( E. x ( E. y ( x = u /\ y = v ) /\ [ `
       ` u / x ] [ v / y ] ph ) <-> ( E. x E. y ( x = u /\ y = v ) /\ `
       ` [ u / x ] [ v / y ] ph ) ) `
       <TR> <TD> 24:22,23:    <TD> ` |- ( ( E. x E. y ( x = u /\ y = v ) /\ [ `
       ` u / x ] [ v / y ] ph ) <-> E. x E. y ( ( x = u /\ y = v ) /\ ph ) ) `
       <TR> <TD> 240:24:      <TD> ` |- ( ( E. x E. y ( x = u /\ y = v ) /\ ( `
       ` E. x E. y ( x = u /\ y = v ) /\ [ u / x ] [ v / y ] ph ) ) <-> `
       ` ( E. x E. y ( x = u /\ y = v ) /\ E. x E. y ( ( x = u /\ y = v ) /\ `
       ` ph ) ) ) `
       <TR> <TD> 241::        <TD> ` |- ( ( E. x E. y ( x = u /\ y = v ) /\ ( `
       ` E. x E. y ( x = u /\ y = v ) /\ [ u / x ] [ v / y ] ph ) ) <-> `
       ` ( E. x E. y ( x = u /\ y = v ) /\ [ u / x ] [ v / y ] ph ) ) `
       <TR> <TD> 242:241,240: <TD> ` |- ( ( E. x E. y ( x = u /\ y = v ) /\ [ `
       ` u / x ] [ v / y ] ph ) <-> ( E. x E. y ( x = u /\ y = v ) /\ `
       ` E. x E. y ( ( x = u /\ y = v ) /\ ph ) ) ) `
       <TR> <TD> 243::        <TD> ` |- ( ( E. x E. y ( x = u /\ y = v ) -> ( `
       ` [ u / x ] [ v / y ] ph <-> E. x E. y ( ( x = u /\ y = v ) /\ `
       ` ph ) ) ) <->  ( ( E. x E. y ( x = u /\ y = v ) /\ `
       ` [ u / x ] [ v / y ] ph ) <-> ( E. x E. y ( x = u /\ y = v ) /\ `
       ` E. x E. y ( ( x = u /\ y = v ) /\ ph ) ) ) ) `
       <TR> <TD> 25:242,243:  <TD> ` |- ( E. x E. y ( x = u /\ y = v ) -> ( [ `
       ` u / x ] [ v / y ] ph <-> E. x E. y ( ( x = u /\ y = v ) /\ ph ) ) ) `
       <TR> <TD> 26::         <TD> ` |- ( ( -. A. x x = y \/ u = v ) <-> E. x `
       ` E. y ( x = u /\ y = v ) ) `
       <TR> <TD> qed:25,26:   <TD> ` |- ( ( -. A. x x = y \/ u = v ) -> ( [ u `
       ` / x ] [ v / y ] ph <-> E. x E. y ( ( x = u /\ y = v ) /\ ph ) ) ) `
       </TABLE> </HTML> $)
    2sb5ndVD $p |- ( ( -. A. x x = y \/ u = v ) ->
                        ( [ u / x ] [ v / y ] ph <->
                                  E. x E. y ( ( x = u /\ y = v ) /\ ph ) ) ) $=
      ( cv wceq wal wn wa wex wsb wb wi exbii hbs1 idn1 e1a e01 in1 axc11 imim1
      wo ax6e2ndeq anabs5 2pm13.193 sbt sbi1 axc11n con3i sbal2 biimpcd pm2.61i
      e0a imbi2 nf5i 19.41 bitr3i bitr2i anbi2i pm5.32 mpbir sylbi ) BFZCFZGBHZ
      IZEFZDFZGUCVDVHGVEVIGJZCKZBKZACDLZBELZVJAJZCKZBKZMZBCDEUDVLVRNVLVNJZVLVQJ
      ZMVSVLVSJVTVLVNUEVSVQVLVQVKVNJZBKVSVPWABVPVJVNJZCKWAWBVOCABCDEUFOVJVNCVNC
      VFVNVNCHZNZVFWDVNVNBHZNVFWEWCNZWDVMBEPZVFVFWFVFQVNBCUARVNWEWCUBSTVGWDVNVM
      CHZBELZNZVGWIWCMZWDVMWHNZBELWJWLBEACDPUGVMWHBEUHUNVGVEVDGCHZIZWKVGVGWNVGQ
      WMVFCBUIUJRVMCBEUKRWKWJWDWIWCVNUOULSTUMUPUQUROVKVNBVNBWGUPUQUSUTURVLVNVQV
      AVBVC $.
  $}

  ${
    $d u x $.  $d u y $.  $d v x $.  $d v y $.
    2uasbanhVD.1 $e |- ( ch <-> ( E. x E. y ( ( x = u /\ y = v ) /\ ph ) /\
                                  E. x E. y ( ( x = u /\ y = v ) /\ ps ) ) ) $.
    $( The following User's Proof is a Virtual Deduction proof (see ~ wvd1 )
       completed automatically by a Metamath tools program invoking mmj2 and
       the Metamath Proof Assistant.  ~ 2uasbanh is ~ 2uasbanhVD without
       virtual deductions and was automatically derived from ~ 2uasbanhVD .
       (Contributed by Alan Sare, 31-May-2014.)
       (Proof modification is discouraged.)  (New usage is discouraged.)
       <HTML> <TABLE>
       <TR> <TD> h1::         <TD> ` |- ( ch <-> ( E. x E. y ( ( x = u /\ y = `
       ` v ) /\ ph ) /\ E. x E. y ( ( x = u /\ y = v ) /\ ps ) ) ) `
       <TR> <TD> 100:1:       <TD> ` |- ( ch -> ( E. x E. y ( ( x = u /\ y = `
       ` v ) /\ ph ) /\ E. x E. y ( ( x = u /\ y = v ) /\ ps ) ) ) `
       <TR> <TD> 2:100:       <TD> ` |- (. ch ->. ( E. x E. y ( ( x = u /\ y `
       ` = v ) /\ ph ) /\ E. x E. y ( ( x = u /\ y = v ) /\ ps ) ) ). `
       <TR> <TD> 3:2:         <TD> ` |- (. ch ->. E. x E. y ( ( x = u /\ y = `
       ` v ) /\ ph ) ). `
       <TR> <TD> 4:3:         <TD> ` |- (. ch ->. E. x E. y ( x = u /\ y = v `
       ` ) ). `
       <TR> <TD> 5:4:         <TD> ` |- (. ch ->. ( -. A. x x = y \/ u = v ) `
       ` ). `
       <TR> <TD> 6:5:         <TD> ` |- (. ch ->. ( [ u / x ] [ v / y ] ph `
       ` <-> E. x E. y ( ( x = u /\ y = v ) /\ ph ) ) ). `
       <TR> <TD> 7:3,6:       <TD> ` |- (. ch ->. [ u / x ] [ v / y ] ph ). `
       <TR> <TD> 8:2:         <TD> ` |- (. ch ->. E. x E. y ( ( x = u /\ y = `
       ` v ) /\ ps ) ). `
       <TR> <TD> 9:5:         <TD> ` |- (. ch ->. ( [ u / x ] [ v / y ] ps `
       ` <-> E. x E. y ( ( x = u /\ y = v ) /\ ps ) ) ). `
       <TR> <TD> 10:8,9:      <TD> ` |- (. ch ->. [ u / x ] [ v / y ] ps ). `
       <TR> <TD> 101::        <TD> ` |- ( [ v / y ] ( ph /\ ps ) <-> ( [ v / `
       ` y ] ph /\ [ v / y ] ps ) ) `
       <TR> <TD> 102:101:     <TD> ` |- ( [ u / x ] [ v / y ] ( ph /\ ps ) `
       ` <-> [ u / x ] ( [ v / y ] ph /\ [ v / y ] ps ) ) `
       <TR> <TD> 103::        <TD> ` |- ( [ u / x ] ( [ v / y ] ph /\ [ v / y `
       ` ] ps ) <-> ( [ u / x ] [ v / y ] ph /\ [ u / x ] [ v / y ] ps ) ) `
       <TR> <TD> 104:102,103: <TD> ` |- ( [ u / x ] [ v / y ] ( ph /\ ps ) `
       ` <->  ( [ u / x ] [ v / y ] ph /\ [ u / x ] [ v / y ] ps ) ) `
       <TR> <TD> 11:7,10,104: <TD> ` |- (. ch ->. [ u / x ] [ v / y ] ( ph /\ `
       ` ps ) ). `
       <TR> <TD> 110:5:       <TD> ` |- (. ch ->. ( [ u / x ] [ v / y ] ( ph `
       ` /\ ps ) <-> E. x E. y ( ( x = u /\ y = v ) /\ ( ph /\ ps ) ) ) ). `
       <TR> <TD> 12:11,110:   <TD> ` |- (. ch ->. E. x E. y ( ( x = u /\ y = `
       ` v ) /\ ( ph /\ ps ) ) ). `
       <TR> <TD> 120:12:      <TD> ` |- ( ch -> E. x E. y ( ( x = u /\ y = v `
       ` ) /\ ( ph /\ ps ) ) ) `
       <TR> <TD> 13:1,120:    <TD> ` |- ( ( E. x E. y ( ( x = u /\ y = v ) /\ `
       ` ph ) /\ E. x E. y ( ( x = u /\ y = v ) /\ ps ) ) -> `
       ` E. x E. y ( ( x = u `
       ` /\ y = v ) /\ ( ph /\ ps ) ) ) `
       <TR> <TD> 14::         <TD> ` |- (. ( ( x = u /\ y = v ) /\ ( ph /\ ps `
       ` ) ) ->. ( ( x = u /\ y = v ) /\ ( ph /\ ps ) ) ). `
       <TR> <TD> 15:14:       <TD> ` |- (. ( ( x = u /\ y = v ) /\ ( ph /\ ps `
       ` ) ) ->. ( x = u /\ y = v ) ). `
       <TR> <TD> 16:14:       <TD> ` |- (. ( ( x = u /\ y = v ) /\ ( ph /\ ps `
       ` ) ) ->. ( ph /\ ps ) ). `
       <TR> <TD> 17:16:       <TD> ` |- (. ( ( x = u /\ y = v ) /\ ( ph /\ ps `
       ` ) ) ->. ph ). `
       <TR> <TD> 18:15,17:    <TD> ` |- (. ( ( x = u /\ y = v ) /\ ( ph /\ ps `
       ` ) ) ->. ( ( x = u /\ y = v ) /\ ph ) ). `
       <TR> <TD> 19:18:       <TD> ` |- ( ( ( x = u /\ y = v ) /\ ( ph /\ ps `
       ` ) ) -> ( ( x = u /\ y = v ) /\ ph ) ) `
       <TR> <TD> 20:19:       <TD> ` |- ( E. y ( ( x = u /\ y = v ) /\ ( ph `
       ` /\ ps ) ) -> E. y ( ( x = u /\ y = v ) /\ ph ) ) `
       <TR> <TD> 21:20:       <TD> ` |- ( E. x E. y ( ( x = u /\ y = v ) /\ ( `
       ` ph /\ ps ) ) -> E. x E. y ( ( x = u /\ y = v ) /\ ph ) ) `
       <TR> <TD> 22:16:       <TD> ` |- (. ( ( x = u /\ y = v ) /\ ( ph /\ ps `
       ` ) ) ->. ps ). `
       <TR> <TD> 23:15,22:    <TD> ` |- (. ( ( x = u /\ y = v ) /\ ( ph /\ ps `
       ` ) ) ->. ( ( x = u /\ y = v ) /\ ps ) ). `
       <TR> <TD> 24:23:       <TD> ` |- ( ( ( x = u /\ y = v ) /\ ( ph /\ ps `
       ` ) ) -> ( ( x = u /\ y = v ) /\ ps ) ) `
       <TR> <TD> 25:24:       <TD> ` |- ( E. y ( ( x = u /\ y = v ) /\ ( ph `
       ` /\ ps ) ) -> E. y ( ( x = u /\ y = v ) /\ ps ) ) `
       <TR> <TD> 26:25:       <TD> ` |- ( E. x E. y ( ( x = u /\ y = v ) /\ ( `
       ` ph /\ ps ) ) -> E. x E. y ( ( x = u /\ y = v ) /\ ps ) ) `
       <TR> <TD> 27:21,26:    <TD> ` |- ( E. x E. y ( ( x = u /\ y = v ) /\ ( `
       ` ph /\ ps ) ) -> ( E. x E. y ( ( x = u /\ y = v ) /\ ph ) /\ `
       ` E. x E. y ( `
       ` ( x = u /\ y = v ) /\ ps ) ) ) `
       <TR> <TD> qed:13,27:   <TD> ` |- ( E. x E. y ( ( x = u /\ y = v ) /\ ( `
       ` ph /\ ps ) ) <-> ( E. x E. y ( ( x = u /\ y = v ) /\ ph ) /\ `
       ` E. x E. y ( `
       ` ( x = u /\ y = v ) /\ ps ) ) ) `
       </TABLE> </HTML> $)
    2uasbanhVD $p |- ( E. x E. y ( ( x = u /\ y = v ) /\ ( ph /\ ps ) ) <->
                                ( E. x E. y ( ( x = u /\ y = v ) /\ ph ) /\
                                  E. x E. y ( ( x = u /\ y = v ) /\ ps ) ) ) $=
      ( cv wceq wa wex simpl e1a simpr e11 in1 eximi wsb wb idn1 biimpi dfvd1ir
      pm3.2 jca wal wn 2eximi ax6e2ndeq biimpri 2sb5nd biimpr com12 sbbii bitri
      wo sban simplbi2comt com13 e110 biimp sylbir impbii ) DIZGIZJEIZFIZJKZABK
      ZKZELZDLZVHAKZELZDLZVHBKZELZDLZKZVLVOVRVKVNDVJVMEVJVMVJVHAVMVJVJVHVJUAZVH
      VIMNZVJVIAVJVJVIVTVHVIONZABMNVHAUDPQRRVKVQDVJVPEVJVPVJVHBVPWAVJVIBWBABONV
      HBUDPQRRUEVSCVLHCVLCVIEFSZDGSZWDVLTZVLCAEFSZDGSZBEFSZDGSZWDWGWIKZTZWDCVOW
      GVOTZWGCVSVOCVSCVSHUBUCZVOVRMNZCVDVFJDUFUGVEVGJUPZWLCVHELDLZWOCVOWPWNVMVH
      DEVHAMUHNWOWPDEFGUIUJNZADEFGUKNWLVOWGWGVOULUMPCVRWIVRTZWICVSVRWMVOVRONCWO
      WRWQBDEFGUKNWRVRWIWIVRULUMPWDWFWHKZDGSWJWCWSDGABEFUQUNWFWHDGUQUOWKWIWGWDW
      DWGWIURUSUTCWOWEWQVIDEFGUKNWEWDVLWDVLVAUMPQVBVC $.
  $}

  $( The following User's Proof is a Virtual Deduction proof (see ~ wvd1 )
     completed automatically by a Metamath tools program invoking mmj2 and the
     Metamath Proof Assistant.  ~ e2ebind is ~ e2ebindVD without virtual
     deductions and was automatically derived from ~ e2ebindVD .
     <HTML> <TABLE>
     <TR> <TD> 1::          <TD> ` |- ( ph <-> ph ) `
     <TR> <TD> 2:1:         <TD> ` |- ( A. y y = x -> ( ph <-> ph ) ) `
     <TR> <TD> 3:2:         <TD> ` |- ( A. y y = x -> ( E. y ph <-> E. x ph `
     ` ) ) `
     <TR> <TD> 4::          <TD> ` |- (. A. y y = x ->. A. y y = x ). `
     <TR> <TD> 5:3,4:       <TD> ` |- (. A. y y = x ->. ( E. y ph <-> E. x `
     ` ph ) ). `
     <TR> <TD> 6::          <TD> ` |- ( A. y y = x -> A. y A. y y = x ) `
     <TR> <TD> 7:5,6:       <TD> ` |- (. A. y y = x ->. A. y ( E. y ph <-> `
     ` E. x ph ) ). `
     <TR> <TD> 8:7:         <TD> ` |- (. A. y y = x ->. ( E. y E. y ph <-> `
     ` E. y E. x ph ) ). `
     <TR> <TD> 9::          <TD> ` |- ( E. y E. x ph <-> E. x E. y ph ) `
     <TR> <TD> 10:8,9:      <TD> ` |- (. A. y y = x ->. ( E. y E. y ph <-> `
     ` E. x E. y ph ) ). `
     <TR> <TD> 11::         <TD> ` |- ( E. y ph -> A. y E. y ph ) `
     <TR> <TD> 12:11:       <TD> ` |- ( E. y E. y ph <-> E. y ph ) `
     <TR> <TD> 13:10,12:    <TD> ` |- (. A. y y = x ->. ( E. x E. y ph <-> `
     ` E. y ph ) ). `
     <TR> <TD> 14:13:       <TD> ` |- ( A. y y = x -> ( E. x E. y ph <-> E. `
     ` y ph ) ) `
     <TR> <TD> 15::         <TD> ` |- ( A. y y = x <-> A. x x = y ) `
     <TR> <TD> qed:14,15:   <TD> ` |- ( A. x x = y -> ( E. x E. y ph <-> E. `
     ` y ph ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 27-Nov-2014.)  (Proof modification is
     discouraged.)  (New usage is discouraged.) $)
  e2ebindVD $p |- ( A. x x = y -> ( E. x E. y ph <-> E. y ph ) ) $=
    ( cv wceq wal wex wb axc11n hba1 idn1 biid a1i drex1 e1a gen11nv exbi excom
    bibi1 e10 biimprd nfe1 19.9 bitr3 in1 syl ) BDZCDZEBFUHUGEZCFZACGZBGZUKHZBC
    IUJUMUJUKCGZULHZUNUKHUMUJUNABGZCGZHZUQULHZUOUJUKUPHZCFURUJUTCUICJUJUJUTUJKA
    ACBAAHUJALMNOPUKUPCQOACBRURUOUSUNUQULSUATUKCACUBUCUNULUKUDTUEUF $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Virtual Deduction transcriptions of textbook proofs
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y $.
    $( The following User's Proof is a Natural Deduction Sequent Calculus
       transcription of the Fitch-style Natural Deduction proof of Unit 20
       Excercise 3.a., which is ~ sb5 , found in the "Answers to Starred
       Exercises" on page 457 of "Understanding Symbolic Logic", Fifth
       Edition (2008), by Virginia Klenk.  The same proof may also be
       interpreted as a Virtual Deduction Hilbert-style axiomatic proof.  It
       was completed automatically by the tools program completeusersproof.cmd,
       which invokes Mel L. O'Cat's mmj2 and Norm Megill's Metamath Proof
       Assistant.  ~ sb5ALT is ~ sb5ALTVD without virtual deductions and
       was automatically derived from ~ sb5ALTVD .
       <HTML> <TABLE>
       <TR> <TD> 1::        <TD> ` |- (. [ y / x ] ph ->. [ y / x ] ph ). `
       <TR> <TD> 2::        <TD> ` |- [ y / x ] x = y `
       <TR> <TD> 3:1,2:     <TD> ` |- (. [ y / x ] ph ->. [ y / x ] ( x = y `
       ` /\ ph ) ). `
       <TR> <TD> 4:3:       <TD> ` |- (. [ y / x ] ph ->.  E. x ( x = y /\ ph `
       ` ) ). `
       <TR> <TD> 5:4:       <TD> ` |- ( [ y / x ] ph -> E. x ( x = y /\ ph ) `
       ` ) `
       <TR> <TD> 6::        <TD> ` |- (. E. x ( x = y /\ ph ) ->. E. x ( x = `
       ` y /\ ph ) ). `
       <TR> <TD> 7::        <TD> ` |- (. E. x ( x = y /\ ph ) ,. ( x = y /\ ph
       `
       ` ) ->. ( x = y /\ ph ) ). `
       <TR> <TD> 8:7:       <TD> ` |- (. E. x ( x = y /\ ph ) ,. ( x = y /\ ph
       `
       ` ) ->. ph ). `
       <TR> <TD> 9:7:       <TD> ` |- (. E. x ( x = y /\ ph ) ,. ( x = y /\ ph
       `
       ` ) ->. x = y ). `
       <TR> <TD> 10:8,9:    <TD> ` |- (. E. x ( x = y /\ ph ) ,. ( x = y /\ ph
       `
       ` ) ->. [ y / x ] ph ). `
       <TR> <TD> 101::      <TD> ` |- ( [ y / x ] ph -> A. x [ y / x ] ph ) `
       <TR> <TD> 11:101,10: <TD> ` |- ( E. x ( x = y /\ ph ) -> [ y / x ] ph `
       ` ) `
       <TR> <TD> 12:5,11:   <TD> ` |- ( ( [ y / x ] ph ->  E. x ( x = y /\ ph `
       ` ) ) /\ ( E. x ( x = y /\ ph ) -> [ y / x ] ph ) ) `
       <TR> <TD> qed:12:    <TD> ` |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) `
       ` ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 21-Apr-2013.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    sb5ALTVD $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $=
      ( wsb cv wceq wa wex wi wb idn1 equsb1 sban simplbi2com e10 spsbe e1a in1
      hbs1 e2 idn2 simpr simpl sbequ1 com12 e22 exinst pm3.2i impbi imp e0a ) A
      BCDZBECEFZAGZBHZIZUOULIZGULUOJZUPUQULUOULUNBCDZUOULULUMBCDZUSULKBCLUSUTUL
      UMABCMNOUNBCPQRUNULBABCSUOUNAUMULUOUNUNAUOUNUAZUMAUBTUOUNUNUMVAUMAUCTUMAU
      LABCUDUEUFUGUHUPUQURULUOUIUJUK $.
  $}

  ${
    vk15.4jVD.1 $e |- -. ( E. x -. ph /\ E. x ( ps /\ -. ch ) ) $.
    vk15.4jVD.2 $e |- ( A. x ch -> -. E. x ( th /\ ta ) ) $.
    vk15.4jVD.3 $e |- -. A. x ( ta -> ph ) $.
    $( The following User's Proof is a Natural Deduction Sequent Calculus
       transcription of the Fitch-style Natural Deduction proof of Unit 15
       Excercise 4.f. found in the "Answers to Starred Exercises" on page 442
       of "Understanding Symbolic Logic", Fifth Edition (2008), by Virginia
       Klenk.  The same proof may also be interpreted to be a Virtual Deduction
       Hilbert-style axiomatic proof.  It was completed automatically by the
       tools program completeusersproof.cmd, which invokes Mel L. O'Cat's mmj2
       and Norm Megill's Metamath Proof Assistant.  ~ vk15.4j is ~ vk15.4jVD
       without virtual deductions and was automatically derived
       from ~ vk15.4jVD .  Step numbers greater than 25 are additional steps
       necessary for the sequent calculus proof not contained in the
       Fitch-style proof.  Otherwise, step i of the User's Proof corresponds to
       step i of the Fitch-style proof.
       <HTML> <TABLE>
       <TR> <TD> h1::               <TD> ` |- -. ( E. x -. ph /\ E. x ( ps /\ `
       ` -. ch ) ) `
       <TR> <TD> h2::               <TD> ` |- ( A. x ch -> -. E. x ( th /\ ta `
       ` ) ) `
       <TR> <TD> h3::               <TD> ` |- -. A. x ( ta -> ph ) `
       <TR> <TD> 4::                <TD> ` |- (. -. E. x -. th ->. -. E. x -. `
       ` th ). `
       <TR> <TD> 5:4:               <TD> ` |- (. -. E. x -. th ->. A. x th ). `
       <TR> <TD> 6:3:               <TD> ` |- E. x ( ta /\ -. ph ) `
       <TR> <TD> 7::                <TD> ` |- (. -. E. x -. th ,. ( ta /\ -. `
       ` ph ) ->. ( ta /\ -. ph ) ). `
       <TR> <TD> 8:7:               <TD> ` |- (. -. E. x -. th ,. ( ta /\ -. `
       ` ph ) ->. ta ). `
       <TR> <TD> 9:7:               <TD> ` |- (. -. E. x -. th ,. ( ta /\ -. `
       ` ph ) ->. -. ph ). `
       <TR> <TD> 10:5:              <TD> ` |- (. -. E. x -. th ->. th ). `
       <TR> <TD> 11:10,8:           <TD> ` |- (. -. E. x -. th ,. ( ta /\ -. `
       ` ph ) ->. ( th /\ ta ) ). `
       <TR> <TD> 12:11:             <TD> ` |- (. -. E. x -. th ,. ( ta /\ -. `
       ` ph ) ->. E. x ( th /\ ta ) ). `
       <TR> <TD> 13:12:             <TD> ` |- (. -. E. x -. th ,. ( ta /\ -. `
       ` ph ) ->. -. -. E. x ( th /\ ta ) ). `
       <TR> <TD> 14:2,13:           <TD> ` |- (. -. E. x -. th ,. ( ta /\ -. `
       ` ph ) ->. -. A. x ch ). `
       <TR> <TD> 140::              <TD> ` |- ( E. x -. th -> A. x E. x -. th `
       ` ) `
       <TR> <TD> 141:140:           <TD> ` |- ( -. E. x -. th -> A. x -. E. x `
       ` -. th ) `
       <TR> <TD> 142::              <TD> ` |- ( A. x ch -> A. x A. x ch ) `
       <TR> <TD> 143:142:           <TD> ` |- ( -. A. x ch -> A. x -. A. x ch `
       ` ) `
       <TR> <TD> 144:6,14,141,143:  <TD> ` |- (. -. E. x -. th ->. -. A. x ch `
       ` ). `
       <TR> <TD> 15:1:              <TD> ` |- ( -. E. x -. ph \/ -. E. x ( ps `
       ` /\ -. ch ) ) `
       <TR> <TD> 16:9:              <TD> ` |- (. -. E. x -. th ,. ( ta /\ -. `
       ` ph ) ->. E. x -. ph ). `
       <TR> <TD> 161::              <TD> ` |- ( E. x -. ph -> A. x E. x -. ph `
       ` ) `
       <TR> <TD> 162:6,16,141,161:  <TD> ` |- (. -. E. x -. th ->. E. x -. ph `
       ` ). `
       <TR> <TD> 17:162:            <TD> ` |- (. -. E. x -. th ->. -. -. E. x `
       ` -. ph ). `
       <TR> <TD> 18:15,17:          <TD> ` |- (. -. E. x -. th ->. -. E. x ( `
       ` ps /\ -. ch ) ). `
       <TR> <TD> 19:18:             <TD> ` |- (. -. E. x -. th ->. A. x ( ps `
       ` -> ch ) ). `
       <TR> <TD> 20:144:            <TD> ` |- (. -. E. x -. th ->. E. x -. ch `
       ` ). `
       <TR> <TD> 21::               <TD> ` |- (. -. E. x -. th ,. -. ch ->. -.
       `
       ` ch ). `
       <TR> <TD> 22:19:             <TD> ` |- (. -. E. x -. th ->. ( ps -> ch `
       ` ) ). `
       <TR> <TD> 23:21,22:          <TD> ` |- (. -. E. x -. th ,. -. ch ->. -.
       `
       ` ps ). `
       <TR> <TD> 24:23:             <TD> ` |- (. -. E. x -. th ,. -. ch ->. E.
       `
       ` x -. ps ). `
       <TR> <TD> 240::              <TD> ` |- ( E. x -. ps -> A. x E. x -. ps `
       ` ) `
       <TR> <TD> 241:20,24,141,240: <TD> ` |- (. -. E. x -. th ->. E. x -. ps `
       ` ). `
       <TR> <TD> 25:241:            <TD> ` |- (. -. E. x -. th ->. -. A. x ps `
       ` ). `
       <TR> <TD> qed:25:            <TD> ` |- ( -. E. x -. th -> -. A. x ps ) `
       </TABLE> </HTML>
       (Contributed by Alan Sare, 21-Apr-2013.)  (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    vk15.4jVD $p |- ( -. E. x -. th -> -. A. x ps ) $=
      ( wn wex wal wa wi exanali biimpri e1a e2 19.8a hbe1 idn1 alex idn2 simpl
      e0a sp pm3.2 e12 notnot con3 e02 hbn hba1 exinst01 exnal wo pm3.13 pm2.53
      simpr e01 con5i com12 e21 exinst11 biimpi in1 ) DJZFKZJZBFLJZVIBJZFKZVJVI
      CJZVLFVICFLZJZVMFKZVIEAJZMZVOFEANFLJZVRFKZIVTVSEAFOPUEZVNDEMZFKZJZNVIVRWD
      JZVOHVIVRWCWEVIVRWBWCVIDVREWBVIDFLZDVIVIWFVIUAWFVIDFUBPQDFUFQVIVRVREVIVRU
      CZEVQUDRDEUGUHWBFSRWCUIRVNWDUJUKVHFVGFTULZVNFCFUMULUNVPVOCFUOPQVIVMVKVLVI
      VMVMBCNZVKVIVMUCVIWIFLZWIVIBVMMFKZJZWJVQFKZJZWLUPZVIWNJZWLWMWKMJWOGWMWKUQ
      UEVIWMWPVIVRWMFWAVIVRVQWMVIVRVRVQWGEVQUSRVQFSRWHVQFTUNWMUIQWNWLURUTWKWJBC
      FOVAQWIFUFQWIVMVKBCUJVBVCVKFSRWHVKFTVDVLVJBFUOVEQVF $.
  $}

  $( The following User's Proof is a Natural Deduction Sequent Calculus
     transcription of the Fitch-style Natural Deduction proof of Theorem 5 of
     Section 14 of [Margaris] p. 59 (which is ~ notnotr ).  The same proof
     may also be interpreted as a Virtual Deduction Hilbert-style
     axiomatic proof.  It was completed automatically by the tools program
     completeusersproof.cmd, which invokes Mel L. O'Cat's mmj2 and Norm
     Megill's Metamath Proof Assistant.  ~ notnotrALT is ~ notnotrALTVD
     without virtual deductions and was automatically derived
     from ~ notnotrALTVD .  Step i of the User's Proof corresponds to
     step i of the Fitch-style proof.
     <HTML> <TABLE>
     <TR> <TD> 1::    <TD> ` |- (. -. -. ph ->. -. -. ph ). `
     <TR> <TD> 2::    <TD> ` |- ( -. -. ph -> ( -. ph -> -. -. -. ph ) ) `
     <TR> <TD> 3:1:   <TD> ` |- (. -. -. ph ->. ( -. ph -> -. -. -. ph ) ). `
     <TR> <TD> 4::    <TD> ` |- ( ( -. ph -> -. -. -. ph ) -> ( -. -. ph -> `
     ` ph ) ) `
     <TR> <TD> 5:3:   <TD> ` |- (. -. -. ph ->. ( -. -. ph -> ph ) ). `
     <TR> <TD> 6:5,1: <TD> ` |- (. -. -. ph ->. ph ). `
     <TR> <TD> qed:6: <TD> ` |- ( -. -. ph -> ph ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 21-Apr-2013.)  (Proof modification is
     discouraged.)  (New usage is discouraged.) $)
  notnotrALTVD $p |- ( -. -. ph -> ph ) $=
    ( wn wi idn1 pm2.21 e1a con4 id e11 in1 ) ABZBZALLACZLALKLBZCZMLLOLDZKNEFAL
    GFPMHIJ $.

  $( The following User's Proof is a Natural Deduction Sequent Calculus
     transcription of the Fitch-style Natural Deduction proof of Theorem 7 of
     Section 14 of [Margaris] p. 60 (which is ~ con3 ).  The same proof may
     also be interpreted to be a Virtual Deduction Hilbert-style axiomatic
     proof.  It was completed automatically by the tools program
     completeusersproof.cmd, which invokes Mel L. O'Cat's mmj2 and Norm
     Megill's Metamath Proof Assistant.  ~ con3ALT2 is ~ con3ALTVD without
     virtual deductions and was automatically derived from ~ con3ALTVD .
     Step i of the User's Proof corresponds to step i of the Fitch-style proof.
     <HTML> <TABLE>
     <TR> <TD> 1::     <TD> ` |- (. ( ph -> ps ) ->. ( ph -> ps ) ). `
     <TR> <TD> 2::     <TD> ` |- (. ( ph -> ps ) ,. -. -. ph ->. -. -. ph ). `
     <TR> <TD> 3::     <TD> ` |- ( -. -. ph -> ph ) `
     <TR> <TD> 4:2:    <TD> ` |- (. ( ph -> ps ) ,. -. -. ph ->. ph ). `
     <TR> <TD> 5:1,4:  <TD> ` |- (. ( ph -> ps ) ,. -. -. ph ->. ps ). `
     <TR> <TD> 6::     <TD> ` |- ( ps -> -. -. ps ) `
     <TR> <TD> 7:6,5:  <TD> ` |- (. ( ph -> ps ) ,. -. -. ph ->. -. -. ps ). `
     <TR> <TD> 8:7:    <TD> ` |- (. ( ph -> ps ) ->. ( -. -. ph -> -. -. ps `
     ` ) ). `
     <TR> <TD> 9::     <TD> ` |- ( ( -. -. ph -> -. -. ps ) -> ( -. ps -> `
     ` -. ph ) ) `
     <TR> <TD> 10:8:   <TD> ` |- (. ( ph -> ps ) ->. ( -. ps -> -. ph ) ). `
     <TR> <TD> qed:10: <TD> ` |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) `
     </TABLE> </HTML>
     (Contributed by Alan Sare, 21-Apr-2013.)  (Proof modification is
     discouraged.)  (New usage is discouraged.) $)
  con3ALTVD $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    ( wi wn idn1 idn2 notnotr e2 id e12 notnot in2 con4 e1a in1 ) ABCZBDZADZCZP
    RDZQDZCSPTUAPTBUAPPTABPEPTTAPTFAGHPIJBKHLRQMNO $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Theorems proved using conjunction-form Virtual Deduction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    elpwgdedVD.1 $e |- (. ph ->. A e. _V ). $.
    elpwgdedVD.2 $e |- (. ps ->. A C_ B ). $.
    $( Membership in a power class.  Theorem 86 of [Suppes] p. 47.  Derived
       from ~ elpwg .  In form of VD deduction with ` ph ` and ` ps ` as
       variable virtual hypothesis collections based on Mario Carneiro's
       metavariable concept. ~ elpwgded is ~ elpwgdedVD using conventional
       notation.  (Contributed by Alan Sare, 23-Apr-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    elpwgdedVD $p |- (. (. ph ,. ps ). ->. A e. ~P B ). $=
      ( cvv wcel wss cpw elpwg biimpar el12 ) ACGHZCDIZCDJHZBEFNPOCDGKLM $.
  $}

  ${
    $d x A $.  $d x B $.
    $( If a class is a subclass of another class, then its power class is a
       subclass of that other class's power class.  Left-to-right implication
       of Exercise 18 of [TakeutiZaring] p. 18.  For the biconditional, see
       ~ sspwb .  The proof ~ sspwimp , using conventional notation, was
       translated from virtual deduction form, ~ sspwimpVD , using a
       translation program.  (Contributed by Alan Sare, 23-Apr-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sspwimp $p |- ( A C_ B -> ~P A C_ ~P B ) $=
      ( vx wss cpw cv wcel wi wal cvv wa wtru vex a1i id syl sstr ancoms syl2an
      elpwi elpwgded uun0.1 ex alrimiv df-ss biimpri iin1 ) ABDZAEZBEZDZUHCFZUI
      GZULUJGZHZCIZUKUHUOCUHUMUNULJGZUHUMKZULBDZUNUQLCMNZUHUHULADZUSUMUHOUMUMVA
      UMOULATPVAUHUSULABQRSZLURULBUTVBUAUBUCUDUKUPCUIUJUEUFPUG $.
  $}

  ${
    $d x A $.  $d x B $.
    $( The following User's Proof is a Virtual Deduction proof (see ~ wvd1 )
       using conjunction-form virtual hypothesis collections.  It was completed
       manually, but has the potential to be completed automatically by a tools
       program which would invoke Mel L. O'Cat's mmj2 and Norm Megill's
       Metamath Proof Assistant.
       ~ sspwimp is ~ sspwimpVD without virtual deductions and was derived
       from ~ sspwimpVD .  (Contributed by Alan Sare, 23-Apr-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.)
       <HTML> <TABLE>
       <TR> <TD> 1::    <TD> ` |- (. A C_ B ->. A C_ B ). `
       <TR> <TD> 2::    <TD> ` |- (. ` .............. ` x e. ~P A `
       ` ->. x e. ~P A ). `
       <TR> <TD> 3:2:   <TD> ` |- (. ` .............. ` x e. ~P A `
       ` ->. x C_ A ). `
       <TR> <TD> 4:3,1: <TD> ` |- (. (. A C_ B ,. x e. ~P A ). ->. x C_ B ). `
       <TR> <TD> 5::    <TD> ` |- x e. _V `
       <TR> <TD> 6:4,5: <TD> ` |- (. (. A C_ B ,. x e. ~P A ). ->. x e. ~P B `
       ` ). `
       <TR> <TD> 7:6:   <TD> ` |- (. A C_ B ->. ( x e. ~P A -> x e. ~P B ) `
       ` ). `
       <TR> <TD> 8:7:   <TD> ` |- (. A C_ B ->. A. x ( x e. ~P A -> x e. `
       ` ~P B ) ). `
       <TR> <TD> 9:8:   <TD> ` |- (. A C_ B ->. ~P A C_ ~P B ). `
       <TR> <TD> qed:9: <TD> ` |- ( A C_ B -> ~P A C_ ~P B ) `
       </TABLE> </HTML> $)
    sspwimpVD $p |- ( A C_ B -> ~P A C_ ~P B ) $=
      ( vx wss cpw cv wcel wi wal cvv wvhc2 wtru vex vd01 idn1 elpwi el1 ancoms
      sstr el12 elpwgdedVD un0.1 int2 gen11 df-ss biimpri in1 ) ABDZAEZBEZDZUHC
      FZUIGZULUJGZHZCIZUKUHUOCUHUMUNULJGZUHUMKZULBDZUNUQLCMNZUHUHULADZUSUMUHOUM
      UMVAUMOULAPQVAUHUSULABSRTZLURULBUTVBUAUBUCUDUKUPCUIUJUEUFQUG $.
  $}

  ${
    $d x A $.  $d x B $.
    $( If a class is a subclass of another class, then its power class is a
       subclass of that other class's power class.  Left-to-right implication
       of Exercise 18 of [TakeutiZaring] p. 18. ~ sspwimpcf , using
       conventional notation, was translated from its virtual deduction form,
       ~ sspwimpcfVD , using a translation program.  (Contributed by Alan Sare,
       13-Jun-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    sspwimpcf $p |- ( A C_ B -> ~P A C_ ~P B ) $=
      ( vx wss cpw cv wcel wi wal cvv vex elpwi syl sstr2 impcom syl2an biimpar
      id elpwg eel021old ex alrimiv df-ss biimpri iin1 ) ABDZAEZBEZDZUFCFZUGGZU
      JUHGZHZCIZUIUFUMCUFUKULUJJGZUFUKUJBDZULCKUFUFUJADZUPUKUFRUKUKUQUKRUJALMUQ
      UFUPUJABNOPUOULUPUJBJSQTUAUBUIUNCUGUHUCUDMUE $.
  $}

  ${
    $d x A $.  $d x B $.
    $( The following User's Proof is a Virtual Deduction proof (see ~ wvd1 )
       using conjunction-form virtual hypothesis collections.  It was completed
       automatically by a tools program which would invokes Mel L. O'Cat's mmj2
       and Norm Megill's Metamath Proof Assistant.
       ~ sspwimpcf is ~ sspwimpcfVD without virtual deductions and was derived
       from ~ sspwimpcfVD .
       The version of completeusersproof.cmd used is capable of only generating
       conjunction-form unification theorems, not unification deductions.
       (Contributed by Alan Sare, 13-Jun-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.)
       <HTML> <TABLE>
       <TR> <TD> 1::    <TD> ` |- (. A C_ B ->. A C_ B ). `
       <TR> <TD> 2::    <TD> ` |- (. ` ........... ` x e. ~P A `
       ` ->. x e. ~P A ). `
       <TR> <TD> 3:2:   <TD> ` |- (. ` ........... ` x e. ~P A `
       ` ->. x C_ A ). `
       <TR> <TD> 4:3,1: <TD> ` |- (. (. A C_ B ,. x e. ~P A ). ->. x C_ B ). `
       <TR> <TD> 5::    <TD> ` |- x e. _V `
       <TR> <TD> 6:4,5: <TD> ` |- (. (. A C_ B ,. x e. ~P A ). ->. x e. ~P B `
       ` ). `
       <TR> <TD> 7:6:   <TD> ` |- (. A C_ B ->. ( x e. ~P A -> x e. ~P B ) `
       ` ). `
       <TR> <TD> 8:7:   <TD> ` |- (. A C_ B ->. A. x ( x e. ~P A -> x e. `
       ` ~P B ) ). `
       <TR> <TD> 9:8:   <TD> ` |- (. A C_ B ->. ~P A C_ ~P B ). `
       <TR> <TD> qed:9: <TD> ` |- ( A C_ B -> ~P A C_ ~P B ) `
       </TABLE> </HTML> $)
    sspwimpcfVD $p |- ( A C_ B -> ~P A C_ ~P B ) $=
      ( vx wss cpw cv wcel wal cvv vex idn1 elpwi el1 sstr2 impcom el12 biimpar
      wi elpwg el021old int2 gen11 df-ss biimpri in1 ) ABDZAEZBEZDZUFCFZUGGZUJU
      HGZRZCHZUIUFUMCUFUKULUJIGZUFUKUJBDZULCJUFUFUJADZUPUKUFKUKUKUQUKKUJALMUQUF
      UPUJABNOPUOULUPUJBISQTUAUBUIUNCUGUHUCUDMUE $.
  $}

  ${
    $d z A $.  $d y A $.  $d z y A $.
    $( The successor of a transitive class is transitive. ~ suctrALTcf , using
       conventional notation, was translated from virtual deduction form,
       ~ suctrALTcfVD , using a translation program.  (Contributed by Alan
       Sare, 13-Jun-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    suctrALTcf $p |- ( Tr A -> Tr suc A ) $=
      ( vz vy wtr csuc cv wcel wa wi wal wceq wo wss sssucid id syl trel 3impib
      simpl ex syl3an ssel2 eel0321old 3expia eleq2 biimpac syl2an simpr elsuci
      eel021old jao 3imp eel2122old alrimivv dftr2 biimpri iin1 ) ADZAEZDZURBFZ
      CFZGZVBUSGZHZVAUSGZIZCJBJZUTURVGBCURVEVFURVEVBAGZVFIZVBAKZVFIZVIVKLZVFURV
      EVIVFAUSMZURVEVIVAAGZVFANZURURVEVCVIVIVOUROVEVEVCVEOZVCVDSPZVIOURVCVIVOAV
      AVBQRUAAUSVAUBZUCUDVEVKVFVNVEVKVOVFVPVEVCVKVOVKVRVKOVKVCVOVBAVAUEUFUGVSUJ
      TVEVDVMVEVEVDVQVCVDUHPVBAUIPVJVLVMVFVIVFVKUKULUMTUNUTVHBCUSUOUPPUQ $.
  $}

  ${
    $d z A $.  $d y A $.  $d z y A $.
    $( The following User's Proof is a Virtual Deduction proof (see ~ wvd1 )
       using conjunction-form virtual hypothesis collections.  The
       conjunction-form version of completeusersproof.cmd.  It allows the User
       to avoid superflous virtual hypotheses.  This proof was completed
       automatically by a tools program which invokes Mel L. O'Cat's
       mmj2 and Norm Megill's Metamath Proof Assistant. ~ suctrALTcf
       is ~ suctrALTcfVD without virtual deductions and was derived
       automatically from ~ suctrALTcfVD .  The version of
       completeusersproof.cmd used is capable of only generating
       conjunction-form unification theorems, not unification deductions.
       (Contributed by Alan Sare, 13-Jun-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.)
       <HTML> <TABLE>
       <TR> <TD> 1::         <TD> ` |- (. Tr A ->. Tr A ). `
       <TR> <TD> 2::         <TD> ` |- (. ` ......... ` ( z e. y /\ y e. `
       ` suc A ) ->. ( z e. y /\ y e. suc A ) ). `
       <TR> <TD> 3:2:        <TD> ` |- (. ` ......... ` ( z e. y /\ y e. `
       ` suc A )  ->. z e. y ). `
       <TR> <TD> 4::         <TD> ` |- (. ` ...................................
       ....... ` y e. A ->. y e. A ). `
       <TR> <TD> 5:1,3,4:    <TD> ` |- (. (. Tr A ,. ( z e. y /\ y e. suc A ) `
       ` , y e. A ). ->. z e. A ). `
       <TR> <TD> 6::         <TD> ` |- A C_ suc A `
       <TR> <TD> 7:5,6:      <TD> ` |- (. (. Tr A ,. ( z e. y /\ y e. suc A ) `
       ` , y e. A ). ->. z e. suc A ). `
       <TR> <TD> 8:7:        <TD> ` |- (. (. Tr A ,. ( z e. y /\ y e. suc A ) `
       ` ). ->. ( y e. A -> z e. suc A ) ). `
       <TR> <TD> 9::         <TD> ` |- (. ` ...................................
       ...... ` y = A ->. y = A ). `
       <TR> <TD> 10:3,9:     <TD> ` |- (. ` ........ ` (. ( z e. y /\ y e. `
       ` suc A ) , y = A ). ->. z e. A ). `
       <TR> <TD> 11:10,6:    <TD> ` |- (. ` ........ ` (. ( z e. y /\ y e. `
       ` suc A ) , y = A ). ->. z e. suc A ). `
       <TR> <TD> 12:11:      <TD> ` |- (. ` .......... ` ( z e. y /\ y e. `
       ` suc A ) ->. ( y = A -> z e. suc A ) ). `
       <TR> <TD> 13:2:       <TD> ` |- (. ` .......... ` ( z e. y /\ y e. `
       ` suc A )  ->. y e. suc A ). `
       <TR> <TD> 14:13:      <TD> ` |- (. ` .......... ` ( z e. y /\ y e. `
       ` suc A ) ->. ( y e. A \/ y = A ) ). `
       <TR> <TD> 15:8,12,14: <TD> ` |- (. (. Tr A ,. ( z e. y /\ y e. suc A ) `
       ` ). ->. z e. suc A ). `
       <TR> <TD> 16:15:      <TD> ` |- ` ` (. Tr A ->. ( ( z e. y /\ y e. `
       ` suc A ) -> z e. suc A ) ). `
       <TR> <TD> 17:16:      <TD> ` |- ` ` (. Tr A ->. A. z A. y ( ( z e. `
       ` y /\ y e. suc A ) -> z e. suc A ) ). `
       <TR> <TD> 18:17:      <TD> ` |- ` ` (. Tr A ->. Tr suc A ). `
       <TR> <TD> qed:18:     <TD> ` |- ( Tr A -> Tr suc A ) `
       </TABLE> </HTML> $)
    suctrALTcfVD $p |- ( Tr A -> Tr suc A ) $=
      ( vz vy wtr csuc cv wcel wa wi wal wceq wss sssucid idn1 simpl el1 3impib
      wo trel int2 el123 ssel2 el0321old int3 eleq2 biimpac el12 el021old simpr
      elsuci jao 3imp el2122old gen12 dftr2 biimpri in1 ) ADZAEZDZURBFZCFZGZVBU
      SGZHZVAUSGZIZCJBJZUTURVGBCURVEVFURVEVBAGZVFIZVBAKZVFIZVIVKRZVFURVEVIVFAUS
      LZURVEVIVAAGZVFAMZURURVEVCVIVIVOURNVEVEVCVENZVCVDOPZVINURVCVIVOAVAVBSQUAA
      USVAUBZUCUDVEVKVFVNVEVKVOVFVPVEVCVKVOVKVRVKNVKVCVOVBAVAUEUFUGVSUHTVEVDVMV
      EVEVDVQVCVDUIPVBAUJPVJVLVMVFVIVFVKUKULUMTUNUTVHBCUSUOUPPUQ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Theorems with a VD proof in conventional notation derived from a VD proof
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d z A $.  $d y A $.  $d z y A $.
    $( The successor of a transitive class is transitive. ~ suctrALT3 is the
       completed proof in conventional notation of the Virtual Deduction proof
       ~ https://us.metamath.org/other/completeusersproof/suctralt3vd.html .
       It was completed manually.  The potential for automated derivation from
       the VD proof exists.  See ~ wvd1 for a description of Virtual Deduction.
       Some sub-theorems of the proof were completed using a unification
       deduction (e.g., the sub-theorem whose assertion is step 19 used
       ~ jaoded ).  Unification deductions employ Mario Carneiro's metavariable
       concept.  Some sub-theorems were completed using a unification theorem
       (e.g., the sub-theorem whose assertion is step 24 used ~ dftr2 ) .
       (Contributed by Alan Sare, 3-Dec-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    suctrALT3 $p |- ( Tr A -> Tr suc A ) $=
      ( vz vy wtr csuc wi cv wcel wa wal wceq w3a sssucid simpld trelded sselid
      id 3expia ex syl eleq2 biimpac syl2an simprd elsuci jaoded alrimivv dftr2
      wo un2122 biimpri idiALT ) ADZAEZDZFUMBGZCGZHZUQUNHZIZUPUNHZFZCJBJZUOUMVB
      BCUMUTVAUMUTVAUMUTIUQAHZVAUTUQAKZUTUMUTVDVAUMUTVDLAUNUPAMZUMUTVDAUPUQUMQU
      TURUSUTQZNZVDQOPRUTVEVAUTVEIAUNUPVFUTURVEUPAHZVEVHVEQVEURVIUQAUPUAUBUCPSU
      TUSVDVEUIUTURUSVGUDUQAUETUFUJSUGUOVCBCUNUHUKTUL $.
  $}

  ${
    $d x A $.  $d x B $.
    $( If a class is a subclass of another class, then its power class is a
       subclass of that other class's power class.  Left-to-right implication
       of Exercise 18 of [TakeutiZaring] p. 18. ~ sspwimpALT is the completed
       proof in conventional notation of the Virtual Deduction proof
       ~ https://us.metamath.org/other/completeusersproof/sspwimpaltvd.html .
       It was completed manually.  The potential for automated derivation from
       the VD proof exists.  See ~ wvd1 for a description of Virtual Deduction.
       Some sub-theorems of the proof were completed using a unification
       deduction (e.g., the sub-theorem whose assertion is step 9 used
       ~ elpwgded ).  Unification deductions employ Mario Carneiro's
       metavariable concept.  Some sub-theorems were completed using a
       unification theorem (e.g., the sub-theorem whose assertion is step 5
       used ~ elpwi ).  (Contributed by Alan Sare, 3-Dec-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sspwimpALT $p |- ( A C_ B -> ~P A C_ ~P B ) $=
      ( vx wss cpw wi cv wcel wal wa wtru cvv vex a1i id syl sylan9ssr elpwgded
      elpwi uunT1 ex alrimiv df-ss biimpri idiALT ) ABDZAEZBEZDZFUFCGZUGHZUJUHH
      ZFZCIZUIUFUMCUFUKULUFUKJZULKUOUJBUJLHKCMNUKUFUJABUKUKUJADUKOUJASPUFOQRTUA
      UBUIUNCUGUHUCUDPUE $.
  $}

  ${
    $d q x A $.
    unisnALT.1 $e |- A e. _V $.
    $( A set equals the union of its singleton.  Theorem 8.2 of [Quine] p. 53.
       The User manually input on a mmj2 Proof Worksheet, without labels, all
       steps of ~ unisnALT except 1, 11, 15, 21, and 30.  With execution of the
       mmj2 unification command, mmj2 could find labels for all steps except
       for 2, 12, 16, 22, and 31 (and the then non-existing steps 1, 11, 15,
       21, and 30). mmj2 could not find reference theorems for those five steps
       because the hypothesis field of each of these steps was empty and none
       of those steps unifies with a theorem in set.mm.  Each of these five
       steps is a semantic variation of a theorem in set.mm and is 2-step
       provable. mmj2 does not have the ability to automatically generate the
       semantic variation in set.mm of a theorem in a mmj2 Proof Worksheet
       unless the theorem in the Proof Worksheet is labeled with a 1-hypothesis
       deduction whose hypothesis is a theorem in set.mm which unifies with the
       theorem in the Proof Worksheet.  The stepprover.c program, which invokes
       mmj2, has this capability. stepprover.c automatically generated steps 1,
       11, 15, 21, and 30, labeled all steps, and generated the RPN proof of
       ~ unisnALT .  Roughly speaking, stepprover.c added to the Proof
       Worksheet a labeled duplicate step of each non-unifying theorem for each
       label in a text file, labels.txt, containing a list of labels provided
       by the User.  Upon mmj2 unification, stepprover.c identified a label for
       each of the five theorems which 2-step proves it.  For ~ unisnALT , the
       label list is a list of all 1-hypothesis propositional calculus
       deductions in set.mm. stepproverp.c is the same as stepprover.c except
       that it intermittently pauses during execution, allowing the User to
       observe the changes to a text file caused by the execution of particular
       statements of the program.  (Contributed by Alan Sare, 19-Aug-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    unisnALT $p |- U. { A } = A $=
      ( vx vq csn cuni cv wcel wi wal wss wa biimpi id syl ax-gen ax-mp sylancl
      df-ss biimpri eluni simpl simpr elsni eleq2 biimpac syl2anc 19.23v pm3.35
      wex wceq snid elunii eqssi ) AEZFZACGZUPHZUQAHZIZCJZUPAKZUTCURUQDGZHZVCUO
      HZLZDUJZVGUSIZUSURVGDUQUOUAMVFUSIZDJZVHVIDVFVDVCAUKZUSVFVFVDVFNZVDVEUBOVF
      VEVKVFVFVEVLVDVEUCOVCAUDOVKVDUSVCAUQUEUFUGPVJVHVFUSDUHMQVGUSUIRPVBVACUPAS
      TQUSURIZCJZAUPKZVMCUSUSAUOHURUSNABULUQAUOUMRPVOVNCAUPSTQUN $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Theorems with a proof in conventional notation derived from a VD proof
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Theorems with a proof in conventional notation automatically derived by
  completeusersproof.c from a Virtual Deduction User's Proof.

$)

  $( Converse of double negation.  Theorem *2.14 of [WhiteheadRussell] p. 102.
     Proof derived by completeusersproof.c from User's Proof in
     VirtualDeductionProofs.txt.  (Contributed by Alan Sare, 11-Sep-2016.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  notnotrALT2 $p |- ( -. -. ph -> ph ) $=
    ( notnotr ) AB $.

  ${
    $d x A $.  $d x B $.
    $( If a class is a subclass of another class, then its power class is a
       subclass of that other class's power class.  Left-to-right implication
       of Exercise 18 of [TakeutiZaring] p. 18.  Proof derived by
       completeusersproof.c from User's Proof in VirtualDeductionProofs.txt.
       The User's Proof in html format is displayed in
       ~ https://us.metamath.org/other/completeusersproof/sspwimpaltvd.html .
       (Contributed by Alan Sare, 11-Sep-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sspwimpALT2 $p |- ( A C_ B -> ~P A C_ ~P B ) $=
      ( vx wss cpw cv wa cvv vex elpwi id sylan9ssr elpwg biimpar sylancr ssrdv
      wcel ex ) ABDZCAEZBEZSCFZTQZUBUAQZSUCGUBHQZUBBDZUDCIUCSUBABUBAJSKLUEUDUFU
      BBHMNORP $.
  $}

  $( Absorption of an existential quantifier of a double existential quantifier
     of non-distinct variables.  The proof is derived by completeusersproof.c
     from User's Proof in VirtualDeductionProofs.txt.  The User's Proof in html
     format is displayed in ~ e2ebindVD .  (Contributed by Alan Sare,
     11-Sep-2016.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  e2ebindALT $p |- ( A. x x = y -> ( E. x E. y ph <-> E. y ph ) ) $=
    ( weq wal wex wb axc11n nfe1 19.9 excom nfa1 id a1i drex1 syl alrimi impcom
    biid sylancr exbi bitr ex bitr3 ) BCDBECBDZCEZACFZBFZUGGZBCHUFUGCFZUGGZUJUH
    GZUIUGCACIJUFABFZCFZUHGZUJUNGZULACBKUFUGUMGZCEUPUFUQCUECLUFUFUQUFMAACBAAGUF
    ASNOPQUGUMCUAPUPUOULUPUOULUJUNUHUBUCRTULUKUIUJUHUGUDRTP $.

  ${
    $d u x $.  $d u y $.  $d v x z $.  $d y z $.
    $( If at least two sets exist ( ~ dtru ), then the same is true expressed
       in an alternate form similar to the form of ~ ax6e .  The proof is
       derived by completeusersproof.c from User's Proof in
       VirtualDeductionProofs.txt.  The User's Proof in html format is
       displayed in ~ ax6e2ndVD .  (Contributed by Alan Sare, 11-Sep-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax6e2ndALT $p |- ( -. A. x x = y -> E. x E. y ( x = u /\ y = v ) ) $=
      ( vz cv wceq wal wn wa wex wi cvv wcel ax-mp id ax-5 syl idiALT alimi vex
      ax6e pm3.2i 19.42v biimpri isset anbi1i exbii mpbi hbnae hbn1 equequ1 a1i
      wb dvelimh 19.41rg exim pm3.35 sylancr excomim ) AFZBFZGZAHIZVADFZGZVBCFZ
      GZJZBKAKZLVDVIAKZBKZVJVDVFAKZVHJZBKZVOVLLZVLVEMNZVHJZBKZVOVQVHBKZJZVSVQVT
      DUABCUBUCVSWAVQVHBUDUEOVRVNBVQVMVHAVEUFUGUHUIVDVNVKLZBHZVPVDVDWCVDPZVDVDB
      HWCABBUJVDWBBVDWBLVDVHVHAHLZAHZWBVDVDWFWDVDVDAHWFVCAUKVDWEAVDWELVDVDWEWDE
      FZVGGZVHABEWHAQVHEQWGVBGZWILZWIWHVHUNLZWIPWKWJEBCULUMOUORSTRRVFVHAUPRSTRR
      VNVKBUQRVOVLURUSVIBAUTRS $.
  $}

  ${
    $d u x $.  $d u y $.  $d v x $.  $d v y $.
    $( "At least two sets exist" expressed in the form of ~ dtru is logically
       equivalent to the same expressed in a form similar to ~ ax6e if ~ dtru
       is false implies ` u = v ` .  Proof derived by completeusersproof.c from
       User's Proof in VirtualDeductionProofs.txt.  The User's Proof in html
       format is displayed in ~ ax6e2ndeqVD .  (Contributed by Alan Sare,
       11-Sep-2016.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax6e2ndeqALT $p |- ( ( -. A. x x = y \/ u = v ) <->
                        E. x E. y ( x = u /\ y = v ) ) $=
      ( cv wceq wal wn wo wa wex wi jao mp3an wne nfa1 19.9 sp syl sylancr 3imp
      ax6e2nd ax6e2eq a1d exmid jaoi hbnae eximi sylib wb excom nfn simpr simpl
      pm13.181 ancoms syl2an2r neeq2 biimparc syl2anc df-ne bicomi con3i sylbir
      id ex alrimiv exim imbi2 biimpa biimpar pm3.34 orc imim2i idiALT ax-1 olc
      imbi1 exmidne 3imp21 impbii ) AEZBEZFZAGZHZDEZCEZFZIZWBWGFZWCWHFZJZBKAKZW
      FWNWIABCDUBZWEWIWNLZLZWFWPLZWEWFIZWPABCDUCWFWNWIWOUDWEUEWQWRWSWPWEWPWFMUA
      NUFWGWHOZWNWJLZLZWIXALZWIWTIZXAXBWTWNWFLZXAWTWFBKZWFLWNXFLZXEXFWFBGZWFXFX
      HBKXHWFXHBABBUGUHXHBWFBPQUIWFBRSWTWNWMAKZBKZUJZXJXFLZXGWMABUKWTXIWFLZBGXL
      WTXMBWTWFAKZWFUJZXIXNLZXMWFAWEAWDAPULQWTWMWFLZAGXPWTXQAWTWMWFWTWMJZWBWCOZ
      WFXRWBWHOZWLXSWTWTWMWKXTWTVEXRWMWKWTWMUMZWKWLUNSWKWTXTWBWGWHUOUPUQXRWMWLY
      AWKWLUMSWLXSXTWCWHWBURUSUTXSWDHZWFXSYBWBWCVAVBWEWDWDARVCVDSVFVGWMWFAVHSXO
      XPXMXNWFXIVIVJTVGXIWFBVHSXKXGXLWNXJXFVRVKTWNXFWFVLTWFWJWNWFWIVMVNSVOXCWIW
      NWILZXAWIWIYCWIVEWIWNVPSWIWJWNWIWFVQVNSVOWGWHVSXCXBXDXAWIXAWTMVTNWA $.
  $}

  ${
    $d u x $.  $d u y $.  $d v x $.  $d v y $.
    $( Equivalence for double substitution ~ 2sb5 without distinct ` x ` ,
       ` y ` requirement. ~ 2sb5nd is derived from ~ 2sb5ndVD .  The proof is
       derived by completeusersproof.c from User's Proof in
       VirtualDeductionProofs.txt.  The User's Proof in html format is
       displayed in ~ 2sb5ndVD .  (Contributed by Alan Sare, 19-Sep-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    2sb5ndALT $p |- ( ( -. A. x x = y \/ u = v ) -> ( [ u / x ] [ v / y ] ph
                 <-> E. x E. y ( ( x = u /\ y = v ) /\ ph ) ) ) $=
      ( cv wceq wal wn wa wex wsb wb wi exbii hbs1 id syl sylancr 19.41 wo sbi1
      ax6e2ndeq anabs5 2pm13.193 axc11 pm3.33 ax-mp con3i sbal2 biimpac pm2.61i
      sbt axc11n imbi2 nf5i bitr3i nfs1v bitr2i anbi2i pm5.32 mpbir sylbi ) BFZ
      CFZGBHZIZEFZDFZGUAVDVHGVEVIGJZCKZBKZACDLZBELZVJAJZCKZBKZMZBCDEUCVLVRNVLVN
      JZVLVQJZMVSVLVSJVTVLVNUDVSVQVLVQVKVNJZBKVSVPWABVPVJVNJZCKWAWBVOCABCDEUEOV
      JVNCVNCVFVNVNCHZNZVFVNVNBHZNWEWCNZWDVMBEPVFVFWFVFQVNBCUFRVNWEWCUGSVGVNVMC
      HZBELZNZWHWCMZWDVMWGNZBELWIWKBEACDPUMVMWGBEUBUHVGVEVDGCHZIZWJVGVGWMVGQWLV
      FCBUNUIRVMCBEUJRWJWIWDWHWCVNUOUKSULUPTUQOVKVNBVMBEURTUSUTUQVLVNVQVAVBVC
      $.
  $}

  ${
    $d A v w x y $.  $d B v w x y $.  $d C v w x y $.  $d D v w x y $.
    $d F v w $.  $d ph v w $.  $d P v w x y $.
    chordthmALT.angdef $e |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } )
                                  |-> ( Im ` ( log ` ( y / x ) ) ) ) $.
    chordthmALT.A $e |- ( ph -> A e. CC ) $.
    chordthmALT.B $e |- ( ph -> B e. CC ) $.
    chordthmALT.C $e |- ( ph -> C e. CC ) $.
    chordthmALT.D $e |- ( ph -> D e. CC ) $.
    chordthmALT.P $e |- ( ph -> P e. CC ) $.
    chordthmALT.AneP $e |- ( ph -> A =/= P ) $.
    chordthmALT.BneP $e |- ( ph -> B =/= P ) $.
    chordthmALT.CneP $e |- ( ph -> C =/= P ) $.
    chordthmALT.DneP $e |- ( ph -> D =/= P ) $.
    chordthmALT.APB $e |- ( ph -> ( ( A - P ) F ( B - P ) ) = _pi ) $.
    chordthmALT.CPD $e |- ( ph -> ( ( C - P ) F ( D - P ) ) = _pi ) $.
    chordthmALT.Q $e |- ( ph -> Q e. CC ) $.
    chordthmALT.ABcirc $e |- ( ph -> ( abs ` ( A - Q ) ) =
                              ( abs ` ( B - Q ) ) ) $.
    chordthmALT.ACcirc $e |- ( ph -> ( abs ` ( A - Q ) ) =
                              ( abs ` ( C - Q ) ) ) $.
    chordthmALT.ADcirc $e |- ( ph -> ( abs ` ( A - Q ) ) =
                              ( abs ` ( D - Q ) ) ) $.
    $( The intersecting chords theorem. If points A, B, C, and D lie on a
       circle (with center Q, say), and the point P is on the interior of the
       segments AB and CD, then the two products of lengths PA ` x. ` PB and
       PC ` x. ` PD are equal. The Euclidean plane is identified with the
       complex plane, and the fact that P is on AB and on CD is expressed by
       the hypothesis that the angles APB and CPD are equal to ` _pi ` . The
       result is proven by using ~ chordthmlem5 twice to show that PA
       ` x. ` PB and PC ` x. ` PD both equal BQ<HTML><sup>2</sup></HTML> ` - `
       PQ<HTML><sup>2</sup></HTML>. This is similar to the proof of the
       theorem given in Euclid's _Elements_, where it is Proposition III.35.
       Proven by David Moews on 28-Feb-2017 as ~ chordthm .
       ~ https://us.metamath.org/other/completeusersproof/chordthmaltvd.html is
       a Virtual
       Deduction User's Proof transcription of ~ chordthm . That VD User's
       Proof was input into completeusersproof, automatically generating this
       ~ chordthmALT Metamath proof.  (Contributed by Alan Sare, 19-Sep-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    chordthmALT $p |- ( ph -> ( ( abs ` ( P - A ) ) x.
                       ( abs ` ( P - B ) ) ) = ( ( abs ` ( P - C ) ) x.
                       ( abs ` ( P - D ) ) ) ) $=
      ( vv vw cv cc0 c1 cioo co wcel cmul cmin caddc wceq wex cabs cfv wrex cpi
      wa necomd angpieqvd mpbid df-rex biimpi syl adantr w3a cexp eqtr3d oveq1d
      c2 3ad2ant1 cc cicc ioossicc 3ad2ant2 3ad2ant3 chordthmlem5 3expb 3adant2
      id sselid 3adant3 3eqtr4d 3expia exlimdv mpd ex ) AUGUIZUJUKULUMZUNZHWNFU
      OUMUKWNUPUMGUOUMUQUMURZVDZUGUSZHDUPUMUTVAHEUPUMUTVAUOUMZHFUPUMUTVAHGUPUMU
      TVAUOUMZURZAWQUGWOVBZWSAFHUPUMGHUPUMJUMVCURXCUBABCUGFHGJKNPOSAGHTVEVFVGXC
      WSWQUGWOVHVIVJAWRXBUGAWRXBAWRVDZUHUIZWOUNZHXEDUOUMUKXEUPUMEUOUMUQUMURZVDZ
      UHUSZXBAXIWRAXGUHWOVBZXIADHUPUMEHUPUMJUMVCURXJUAABCUHDHEJKLPMQAEHRVEVFVGX
      JXIXGUHWOVHVIVJVKXDXHXBUHAWRXHXBAWRXHVLEIUPUMUTVAZVPVMUMZHIUPUMUTVAVPVMUM
      ZUPUMZGIUPUMUTVAZVPVMUMZXMUPUMZWTXAAWRXNXQURXHAXLXPXMUPAXKXOVPVMADIUPUMUT
      VAZXKXOUDUFVNVOVOVQAXHWTXNURZWRAXFXGXSAXFXGVLDEHIXEAXFDVRUNXGLVQAXFEVRUNX
      GMVQAXFIVRUNZXGUCVQXFAXEUJUKVSUMZUNXGXFWOYAXEUJUKVTZXFWFWGWAXGAXGXFXGWFWB
      AXFXRXKURXGUDVQWCWDWEAWRXAXQURZXHAWPWQYCAWPWQVLFGHIWNAWPFVRUNWQNVQAWPGVRU
      NWQOVQAWPXTWQUCVQWPAWNYAUNWQWPWOYAWNYBWPWFWGWAWQAWQWPWQWFWBAWPFIUPUMUTVAZ
      XOURWQAXRYDXOUEUFVNVQWCWDWHWIWJWKWLWMWKWL $.
  $}

  $( Lemma for ~ isosctr .  This proof was automatically derived by
     completeusersproof from its Virtual Deduction proof counterpart
     ~ https://us.metamath.org/other/completeusersproof/isosctrlem1altvd.html .
     As it is verified by the Metamath program, ~ isosctrlem1ALT verifies
     ~ https://us.metamath.org/other/completeusersproof/isosctrlem1altvd.html .
     (Contributed by Alan Sare, 22-Apr-2018.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  isosctrlem1ALT $p |- ( ( A e. CC /\ ( abs ` A ) = 1 /\ -. 1 = A ) ->
                         ( Im ` ( log ` ( 1 - A ) ) ) =/= _pi ) $=
    ( cc wcel cfv c1 wceq cmin co cpi cr wa ax-1cn a1i adantr cc0 wi idiALT cle
    pire wbr cabs wn w3a clog cim id subcld subeq0 biimpd sylancr con3d biimpri
    wne df-ne syl6 imp logcld imcld 3adant2 c2 cdiv 2re 2ne0 redivcli cneg cicc
    cxr neghalfpirx rexri cre recld recnd subidd releabsd adantl breqtrd lesub1
    1re ax-mp 3impcombi mp3an2ani eqbrtrrd wtru rered mptru oveq1 eqcomd eqtrid
    resub argrege0 3coml 3com13 eel12131 iccleub mp3an12i pipos elrpii rphalflt
    clt crp lelttrd ltned ) ABCZAUADZEFZEAFZUBZUCZEAGHZUDDZUEDZIXCXGXKJCXEXCXGK
    ZXJXLXIXCXIBCZXGXCEAEBCZXCLMXCUFZUGZNXCXGXIOUMZXCXGXIOFZUBZXQXCXRXFXCXNXCXR
    XFPZLXOXNXCKZXTPYAXRXFEAUHUIQUJUKXQXSXIOUNULUOUPZUQURUSZXHXKIUTVAHZIYCYDJCX
    HIUTSVBVCVDZMIJCXHSMYDVEZVGCYDVGCXHXKYFYDVFHCZXKYDRTVHYDYEVIXCXMXEOXIVJDZRT
    ZXGXQYGXPXCXEKZOEAVJDZGHZYHRYJYKYKGHZOYLRXCYMOFXEXCYKXCYKXCAXOVKZVLVMNEJCZX
    CYKJCZXEYKERTZYMYLRTZXNYOLYOXNVRMVSZYNYJYKXDERXCYKXDRTXEXCAXOVNNXEXEXCXEUFV
    OVPYOYPYQUCYRPYPYOYQYRYKEYKVQVTQWAWBXCYLYHFXEXCYLEVJDZYKGHZYHYTEFZYLUUAFUUB
    WCEYOWCYSMWDWEUUBUUAYLYTEYKGWFWGVSXCXNXCUUAYHFZLXOYAUUCPYAYHUUAEAWIWGQUJWHN
    VPYBXQYIXMYGXMXQYIYGXIWJWKWLWMYFYDXKWNWOYDIWSTZXHIWTCUUDISWPWQIWRVSMXAXB $.

  ${
    $d k u v ph $.  $d k u w $.  $d A k $.  $d A u $.  $d A v $.  $d A w $.
    $d B u $.  $d B v $.  $d B w $.  $d J k $.  $d J u $.  $d J v $.  $d P k $.
    $d X k $.  $d X u $.  $d X v $.
    iunconnlem2.1 $e |- ( ps <-> ( ( ( ( ( ( ph /\ u e. J ) /\ v e. J ) /\
    ( u i^i U_ k e. A B ) =/= (/) ) /\ ( v i^i U_ k e. A B ) =/= (/) ) /\
    ( u i^i v ) C_ ( X \ U_ k e. A B ) ) /\ U_ k e. A B C_ ( u u. v ) ) ) $.
    iunconnlem2.2 $e |- ( ph -> J e. ( TopOn ` X ) ) $.
    iunconnlem2.3 $e |- ( ( ph /\ k e. A ) -> B C_ X ) $.
    iunconnlem2.4 $e |- ( ( ph /\ k e. A ) -> P e. B ) $.
    iunconnlem2.5 $e |- ( ( ph /\ k e. A ) -> ( J |`t B ) e. Conn ) $.
    $( The indexed union of connected overlapping subspaces sharing a common
       point is connected.  This proof was automatically derived by
       completeusersproof from its Virtual Deduction proof counterpart
       ~ https://us.metamath.org/other/completeusersproof/iunconlem2vd.html .
       As it is verified by the Metamath program, ~ iunconnlem2 verifies
       ~ https://us.metamath.org/other/completeusersproof/iunconlem2vd.html .
       (Contributed by Alan Sare, 22-Apr-2018.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    iunconnlem2 $p |- ( ph -> ( J |`t U_ k e. A B ) e. Conn ) $=
      ( wcel c0 syl wa nfcv vw ctopon cfv ciun wss cv cin wne cdif w3a cun wral
      wn wi crest co cconn ex ralrimiv iunss biimpri biimpi simprd wrex simp-4r
      wo wex n0 inss2 sselid eliun rexn0 exlimiv wnf nfan nfiu1 nfin nfne nfdif
      id nfv nfss nfbii mpbir simp-6l ralrimi r19.2z ancoms syl2anc sseldd elun
      sylan sylbir simp-6r simp-5r simpllr simplr iunconnlem eqsstrid sseqtrrdi
      incom uncom pm4.56 idiALT pm2.65da ex3 3impd 3expia impd connsub biimp3ar
      ralrimivv syl3anc ) AIJUBUCPZHEFUDZJUEZDUFZXOUGZQUHZCUFZXOUGZQUHZXQXTUGZJ
      XOUIZUEZUJXOXQXTUKZUEZUMZUNZCIULDIULZIXOUOUPUQPZLAFJUEZHEULZXPAYLHEAHUFEP
      ZYLMURUSXPYMHEFJUTVARAYIDCIIAXQIPZXTIPZYIAYOYPYIUNAYOYPYIAYOYPUJXSYBYEYHA
      YOYPXSYBYEYHUNZUNAYOSZYPSZXSSZYBYQYTYBSZYEYHUUAYESZYGGXQPZGXTPZVFZUUBYGSZ
      BUUEKBGYFPZUUEBXOYFGBUUBYGBUUFKVBZVCZBGFPZHEVDZGXOPZBEQUHZUUJHEULZUUKBUAU
      FZXRPZUAVGZUUMBXSUUQBUUFXSUUHYSXSYBYEYGVERZXSUUQUAXRVHVBRUUPUUMUAUUPUUOFP
      ZHEVDZUUMUUPUUOXOPZUUTUUPXRXOUUOXQXOVIUUPVTVJUVAUUTHUUOEFVKVBRUUSHEVLRVMR
      BUUJHEBHVNUUFHVNUUBYGHUUAYEHYTYBHYSXSHYRYPHYRHWAYPHWAVOHXRQHXQXOHXQTHEFVP
      ZVQHQTZVRVOHYAQHXTXOHXTTUVBVQUVCVRVOHYCYDHYCTHJXOHJTUVBVSWBVOHXOYFUVBHYFT
      WBVOBUUFHKWCWDZBYNUUJBAYNUUJBUUFAUUHAYOYPXSYBYEYGWERZNWLZURWFUUNUUMUUKUUM
      UUNUUKUUJHEWGWHWHWIUULUUKHGEFVKVARWJUUGUUEGXQXTWKVBRWMUUFBUUEUMZKBUUCUMZU
      UDUMZUVGBEFGXQHIXTJBAXNUVELRZBAYNYLUVEMWLZUVFBAYNIFUOUPUQPUVEOWLZBUUFYOUU
      HAYOYPXSYBYEYGWNRZBUUFYPUUHYRYPXSYBYEYGWORZBUUFYBUUHYTYBYEYGWPRBUUFYEUUHU
      UAYEYGWQRZUUIUVDWRBEFGXTHIXQJUVJUVKUVFUVLUVNUVMUURBXTXQUGYCYDXTXQXAUVOWSB
      XOYFXTXQUKUUIXTXQXBWTUVDWRUVHUVISZUVGUNUVPUVGUUCUUDXCVBXDWIWMXEURURXFXGXH
      URXIXLXNXPYKYJDCXOIJXJXKXM $.
  $}

  ${
    $d k u v ph $.  $d A k u v $.  $d B u v $.  $d J k u v $.  $d P k $.
    $d X k u v $.
    iunconnALT.1 $e |- ( ph -> J e. ( TopOn ` X ) ) $.
    iunconnALT.2 $e |- ( ( ph /\ k e. A ) -> B C_ X ) $.
    iunconnALT.3 $e |- ( ( ph /\ k e. A ) -> P e. B ) $.
    iunconnALT.4 $e |- ( ( ph /\ k e. A ) -> ( J |`t B ) e. Conn ) $.
    $( The indexed union of connected overlapping subspaces sharing a common
       point is connected.  This proof was automatically derived by
       completeusersproof from its Virtual Deduction proof counterpart
       ~ https://us.metamath.org/other/completeusersproof/iunconaltvd.html .
       As it is verified by the Metamath program, ~ iunconnALT verifies
       ~ https://us.metamath.org/other/completeusersproof/iunconaltvd.html .
       (Contributed by Alan Sare, 22-Apr-2018.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    iunconnALT $p |- ( ph -> ( J |`t U_ k e. A B ) e. Conn ) $=
      ( vu vv cv wcel wa cin c0 wne wss ciun cdif cun biid iunconnlem2 ) AALNZF
      OPMNZFOPUFEBCUAZQRSPUGUHQRSPUFUGQGUHUBTPUHUFUGUCTPZMLBCDEFGUIUDHIJKUE $.
  $}

  $( A complex number whose sine is zero is an integer multiple of ` _pi ` .
     The Virtual Deduction form of the proof is
     ~ https://us.metamath.org/other/completeusersproof/sineq0altvd.html .  The
     Metamath form of the proof is ~ sineq0ALT .  The Virtual Deduction proof
     is based on Mario Carneiro's revision of Norm Megill's proof of ~ sineq0 .
     The Virtual Deduction proof is verified by automatically transforming it
     into the Metamath form of the proof using completeusersproof, which is
     verified by the Metamath program.  The proof of
     ~ https://us.metamath.org/other/completeusersproof/sineq0altro.html is a
     form of the completed proof which preserves the Virtual Deduction proof's
     step numbers and their ordering.  (Contributed by Alan Sare, 13-Jun-2018.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  sineq0ALT $p |- ( A e. CC -> ( ( sin ` A ) = 0 <-> ( A / _pi ) e. ZZ ) ) $=
    ( cc wcel csin cfv cc0 wceq cpi co wa c2 cmul a1i adantr ci ce c1 fveq2d wn
    cabs cdiv cz crp cr cmo pire pipos elrpii wne 2cn 2re ax-mp id mulcld caddc
    2ne0 ax-icn mul12d 2timesd eqtr3d efadd syl2anc eqtrd cneg sinval sylan9req
    cmin efcl syl negicn subcld 2mulicn 2muline0 diveq0ad mpbid subeq0ad oveq2d
    eqtr4d adddird negidi oveq1i eqtr3di mul02d ef0 3eqtrd abs1 eqtrdi biimparc
    wb absefib ancoms syl2an2r mulre 4animp1 4an31 syl1111anc clt wbr wo modcld
    w3a cioo recnd sincld cfl cle 0re ltleii gt0ne0 3com23 mp3an redivcld flcld
    3adant3 znegcld wi abssinper eqcomd ex mpd zcnd negcld recni mulcomd negeqd
    mulneg1d oveq2 ad3antrrr 4an4132 negsubd modval mpan2 abs0 cxr rexri notbii
    sylib sylancr biimp3a mp3an2i adantl abs00d bicomi ltne neneqd expcom con3i
    notnotb mpi sylbir sinq12gt0 elioo2 mp2an 3anan12 modlt jca not12an2impnot1
    nsyl modge0 leloe idiALT pm2.53 imp mod0 3com12 divcan1d sinkpi impbid ) AB
    CZADEZFGZAHUAIZUBCZUVIUVKUVMHUCCZUVIUVKJZAUDCZAHUEIZFGZUVMHUFUGUHZUVOKFUIZK
    UDCZUVIKALIZUDCZUVPUVTUVOUPMUWAUVOKBCZUWAUJUWAUWDUKMULMUVIUVIUVKUVIUMZNZUVI
    UWBBCZUVKOUWBLIZPEZTEZQGZUWCUVIKAUWDUVIUJMZUWEUNUVOUWJQTEQUVOUWIQTUVOUWIOAL
    IZPEZUWNLIZQUVIUWIUWOGUVKUVIUWIUWMUWMUOIZPEZUWOUVIUWHUWPPUVIKUWMLIUWHUWPUVI
    KOAUWLOBCUVIUQMZUWEURUVIUWMUVIOAUWRUWEUNZUSUTRUVIUWMBCZUWTUWQUWOGUWSUWSUWMU
    WMVAVBVCNUVOUWOUWMOVDZALIZUOIZPEZFPEZQUVOUWOUWNUXBPEZLIZUXDUVOUWNUXFUWNLUVO
    UWNUXFVGIZFGZUWNUXFGZUVOUXHKOLIZUAIZFGZUXIUVIUVKUXLUVJFAVEUVKUMZVFUVIUXMUXI
    WIUVKUVIUXHUXKUVIUWNUXFUVIUWTUWNBCUWSUWMVHVIZUVIUXBBCZUXFBCUVIUXAAUXABCUVIV
    JMZUWEUNZUXBVHVIZVKUXKBCUVIVLMUXKFUIUVIVMMVNNVOUVIUXIUXJWIUVKUVIUWNUXFUXOUX
    SVPNVOVQUVIUXDUXGGZUVKUVIUWTUXPUXTUWSUXRUWMUXBVAVBNVRUVIUXDUXEGUVKUVIUXCFPU
    VIUXCFALIZFUVIOUXAUOIZALIUXCUYAUVIOUXAAUWRUXQUWEVSUYBFALOUQVTWAWBUVIAUWEWCV
    CRNUXEQGUVOWDMWEVCRWFWGUWKUWGUWCUWGUWCUWKUWBWJWHWKWLUVTUWAUVIUWCUVPUVIUWAUV
    TUWCUVPAKWMWNWOWPZUVOFUVQUVOFUVQWQWRZSZUYDFUVQGZWSZUYFUVOUYDUVQUDCZUVQHWQWR
    ZJZJZSZUYJUYEUVOUYHUYDUYIXAZSZUYLUVOUVQFHXBICZSUYNUVOFUVQDEZWQWRZUYOUVOUYPF
    GZUYQSZUVOUYPUVOUVQUVOUVQUVOAHUYCUVNUVOUVSMWTZXCXDUVOUVJTEZUYPTEZFUVOVUAAHU
    VLXEEZLIZVGIZDEZTEZVUBUVOVUAAVUCVDZHLIZUOIZDEZTEZVUGUVOVUHUBCZVUAVULGZUVOVU
    CUVOUVLUVOAHUYCHUDCZUVOUFMHFUIZUVOVUOFHXFWRZFHWQWRZVUPUFFHXGUFUGXHUGVUOVURV
    UQVUPVUOVURVUPVUQHXIXNXJXKZMXLXMZXOUVIVUMVUNXPUVKUVIVUMVUNUVIVUMJVULVUAAVUH
    XQXRXSNXTUVOVUKVUFTUVOVUJVUEDUVOVUJAVUDVDZUOIZVUEUVOUVIVUIBCZVVABCZVUIVVAGZ
    VUJVVBGZUWFUVOVUHHUVOVUCUVOVUCVUTYAZYBHBCZUVOHUFYCZMZUNUVOVUDUVOHVUCVVJVVGU
    NZYBUVOVUIVUCHLIZVDVVAUVOVUCHVVGVVJYFUVOVVLVUDUVOVUCHVVGVVJYDYEVCUVIVVCVVDV
    VEVVFVVEVVFVVDVVCUVIVUIVVAAUOYGYHYIWPUVOAVUDUWFVVKYJVCRRVCUVOUVPVUBVUGGZUYC
    UVPUVNVVMUVSUVPUVNJZUYPVUFTVVNUVQVUEDAHYKRRYLVIVRUVKVUAFGUVIUVKVUAFTEFUVKUV
    JFTUXNRYMWGUUAUTUUBUYRUYRSZSZUYSUYRVVPUYRUUHUUCUYQVVOUYQFUDCZVVOXGVVQUYQVVO
    VVQUYQJUYPFFUYPUUDUUEUUFUUIUUGUUJVIUVQUUKUURUYOUYMFYNCHYNCUYOUYMWIFXGYOHUFY
    OFHUVQUULUUMYPYQUYMUYKUYHUYDUYIUUNYPYQUVOUYHUYIUYTUVOUVNUVPUYIUVSUYCUVPUVNU
    YIAHUUOWKYRUUPUYDUYJUUQVBVVQUVOUYHFUVQXFWRZUYGXGUYTUVOUVNUVPVVRUVSUYCUVPUVN
    VVRAHUUSWKYRVVQUYHVVRXAUYGXPVVQUYHVVRUYGFUVQUUTYSUVAYTUYGUYEUYFUYGUYEUYFUYD
    UYFUVBUVCWKVBXRUVPUVNUVRUVMUVPUVNUVRUVMAHUVDYSUVEYTXSUVIUVMUVKUVIUVMUVJUVLH
    LIZDEZFUVIVVSADUVIAHUWEVVHUVIVVIMVUPUVIVUSMUVFRUVMUVMVVTFGUVMUMUVLUVGVIVFXS
    UVH $.

$( (End of Alan Sare's mathbox.) $)
