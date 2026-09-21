$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Wolf Lammen
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  ${
    wl-section-prop.hyp $e |- ph $.
    $( Intuitionistic logic is now developed separately, so we need not first
       focus on intuitionally valid axioms ~ ax-1 and ~ ax-2 any longer.

       Alternatively, I start from Jan Lukasiewicz's axiom system here, i.e.,
       ~ ax-mp , ~ ax-luk1 , ~ ax-luk2 and ~ ax-luk3 .  I rather copy this
       system than use ~ luk-1 to ~ luk-3 , since the latter are theorems,
       while we need axioms here.

       (Contributed by Wolf Lammen, 23-Feb-2018.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    wl-section-prop $p |- ph $=
      (  ) B $.
  $}

  $( 1 of 3 axioms for propositional calculus due to Lukasiewicz.  Copy of
     ~ luk-1 and ~ imim1 , but introduced as an axiom.  It focuses on a basic
     property of a valid implication, namely that the consequent has to be true
     whenever the antecedent is.  So if ` ph ` and ` ps ` are somehow
     parametrized expressions, then ` ph -> ps ` states that ` ph ` strengthen
     ` ps ` , in that ` ph ` holds only for a (often proper) subset of those
     parameters making ` ps ` true.  We easily accept, that when ` ps ` is
     stronger than ` ch ` and, at the same time ` ph ` is stronger than
     ` ps ` , then ` ph ` must be stronger than ` ch ` .  This transitivity is
     expressed in this axiom.

     A particular result of this strengthening property comes into play if the
     antecedent holds unconditionally.  Then the consequent must hold
     unconditionally as well.  This specialization is the foundational idea
     behind logical conclusion.  Such conclusion is best expressed in so-called
     immediate versions of this axiom like ~ imim1i or ~ syl .  Note that these
     forms are weaker replacements (i.e. just frequent specialization) of the
     closed form presented here, hence a mere convenience.

     We can identify in this axiom up to three antecedents, followed by a
     consequent.  The number of antecedents is not really fixed; the fewer we
     are willing to "see", the more complex the consequent grows.  On the other
     side, since ` ch ` is a variable capable of assuming an implication
     itself, we might find even more antecedents after some substitution of
     ` ch ` .  This shows that the ideas of antecedent and consequent in
     expressions like this depends on, and can adapt to, our current
     interpretation of the whole expression.

     In this axiom, up to two antecedents happen to be of complex nature
     themselves, i.e. are an embedded implication.  Logically, this axiom is a
     compact notion of simpler expressions, which I will later coin implication
     chains.  Herein all antecedents and the consequent appear as simple
     variables, or their negation.  Any propositional expression is equivalent
     to a set of such chains.  This axiom, for example, is dissected into
     following chains, from which it can be recovered losslessly:

     ` ( ps -> ( ch -> ( ph -> ch ) ) ) ` ;
     ` ( -. ph -> ( ch -> ( ph -> ch ) ) ) ` ;
     ` ( ps -> ( -. ps -> ( ph -> ch ) ) ) ` ;
     ` ( -. ph -> ( -. ps -> ( ph -> ch ) ) ) ` .  (Contributed by Wolf Lammen,
     17-Dec-2018.)  (New usage is discouraged.) $)
  ax-luk1 $a |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $.

  $( 2 of 3 axioms for propositional calculus due to Lukasiewicz.  Copy of
     ~ luk-2 or ~ pm2.18 , but introduced as an axiom.  The core idea behind
     this axiom is, that if something can be implied from both an antecedent,
     and separately from its negation, then the antecedent is irrelevant to the
     consequent, and can safely be dropped.  This is perhaps better seen from
     the following slightly extended version (related to ~ pm2.65 ):

     ` ( ( ph -> ph ) -> ( ( -. ph -> ph ) -> ph ) ) ` .  (Contributed by Wolf
     Lammen, 17-Dec-2018.)  (New usage is discouraged.) $)
  ax-luk2 $a |- ( ( -. ph -> ph ) -> ph ) $.

  $( 3 of 3 axioms for propositional calculus due to Lukasiewicz.  Copy of
     ~ luk-3 and ~ pm2.24 , but introduced as an axiom.

     One might think that the similar ~ pm2.21 ` ( -. ph -> ( ph -> ps ) ) ` is
     a valid replacement for this axiom.  But this is not true, ~ ax-3 is not
     derivable from this modification.

     This can be shown by designing carefully operators ` -. ` and ` -> ` on a
     finite set of primitive statements.  In propositional logic such
     statements are ` T. ` and ` F. ` , but we can assume more and other
     primitives in our universe of statements. So we denote our primitive
     statements as phi0 , phi1 and phi2.  The actual meaning of the statements
     are not important in this context, it rather counts how they behave under
     our operations ` -. ` and ` -> ` , and which of them we assume to hold
     unconditionally (phi1, phi2).  For our disproving model, I give that
     information in tabular form below.  The interested reader may check by
     hand, that all possible interpretations of ~ ax-mp , ~ ax-luk1 , ~ ax-luk2
     and ~ pm2.21 result in phi1 or phi2, meaning they always hold.  But for
     ~ wl-luk-ax3 we can find a counter example resulting in phi0, not a
     statement always true.

     The verification of a particular set of axioms in a given model is tedious
     and error prone, so I wrote a computer program, first checking this for
     me, and second, hunting for a counter example.  Here is the result, after
     9165 fruitlessly computer generated models:

     <HTML>
     <br><br>
     ax-3 fails for phi2, phi2<br>
     number of statements: 3<br>
     always true phi1 phi2
     <br><br>
     Negation is defined as<br>
     ----------------------------------------------------------------------
     <table border="1">
     <tr><td>-. phi0</td><td>-. phi1</td><td>-. phi2</td></tr>
     <tr><td>phi1</td><td>phi0</td><td>phi1</td></tr></table>
     <br>
     Implication is defined as<br>
     ----------------------------------------------------------------------
     <table border=1>
     <tr><td>p->q</td><td>q: phi0</td><td>q: phi1</td><td>q: phi2</td></tr>
     <tr><td>p: phi0</td><td>phi1</td><td>phi1</td><td>phi1</td></tr>
     <tr><td>p: phi1</td><td>phi0</td><td>phi1</td><td>phi1</td></tr>
     <tr><td>p: phi2</td><td>phi0</td><td>phi0</td><td>phi0</td></tr>
     </table><br></HTML>
     (Contributed by Wolf Lammen, 17-Dec-2018.)  (New usage is discouraged.) $)
  ax-luk3 $a |- ( ph -> ( -. ph -> ps ) ) $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  1. Bootstrapping
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    wl-section-boot.hyp $e |- ph $.
    $( In this section, I provide the first steps needed for convenient
       proving.  The presented theorems follow no common concept other than
       being useful in themselves, and apt to rederive ~ ax-1 , ~ ax-2 and
       ~ ax-3 .  (Contributed by Wolf Lammen, 17-Dec-2018.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    wl-section-boot $p |- ph $=
      (  ) B $.
  $}

  ${
    wl-luk-imim1i.1 $e |- ( ph -> ps ) $.
    $( Inference adding common consequents in an implication, thereby
       interchanging the original antecedent and consequent.  Copy of ~ imim1i
       with a different proof.  (Contributed by Wolf Lammen, 17-Dec-2018.) $)
    wl-luk-imim1i $p |- ( ( ps -> ch ) -> ( ph -> ch ) ) $=
      ( wi ax-luk1 ax-mp ) ABEBCEACEEDABCFG $.
  $}

  ${
    wl-luk-syl.1 $e |- ( ph -> ps ) $.
    wl-luk-syl.2 $e |- ( ps -> ch ) $.
    $( An inference version of the transitive laws for implication ~ luk-1 .
       Copy of ~ syl with a different proof.  (Contributed by Wolf Lammen,
       17-Dec-2018.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    wl-luk-syl $p |- ( ph -> ch ) $=
      ( wi wl-luk-imim1i ax-mp ) BCFACFEABCDGH $.
  $}

  ${
    wl-luk-imtrid.1 $e |- ( ph -> ps ) $.
    wl-luk-imtrid.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A syllogism rule of inference.  The first premise is used to replace the
       second antecedent of the second premise.  Copy of ~ syl5 with a
       different proof.  (Contributed by Wolf Lammen, 17-Dec-2018.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    wl-luk-imtrid $p |- ( ch -> ( ph -> th ) ) $=
      ( wi wl-luk-imim1i wl-luk-syl ) CBDGADGFABDEHI $.
  $}

  ${
    wl-luk-pm2.18d.1 $e |- ( ph -> ( -. ps -> ps ) ) $.
    $( Deduction based on reductio ad absurdum.  Copy of ~ pm2.18d with a
       different proof.  (Contributed by Wolf Lammen, 17-Dec-2018.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    wl-luk-pm2.18d $p |- ( ph -> ps ) $=
      ( wn wi ax-luk2 wl-luk-syl ) ABDBEBCBFG $.
  $}

  ${
    wl-luk-con4i.1 $e |- ( -. ph -> -. ps ) $.
    $( Inference rule.  Copy of ~ con4i with a different proof.  (Contributed
       by Wolf Lammen, 17-Dec-2018.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    wl-luk-con4i $p |- ( ps -> ph ) $=
      ( wn ax-luk3 wl-luk-imtrid wl-luk-pm2.18d ) BAADBDBACBAEFG $.
  $}

  ${
    wl-luk-pm2.24i.1 $e |- ph $.
    $( Inference rule.  Copy of ~ pm2.24i with a different proof.  (Contributed
       by Wolf Lammen, 17-Dec-2018.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    wl-luk-pm2.24i $p |- ( -. ph -> ps ) $=
      ( wn wi ax-luk3 ax-mp ) AADBECABFG $.
  $}

  ${
    wl-luk-a1i.1 $e |- ph $.
    $( Inference rule.  Copy of ~ a1i with a different proof.  (Contributed by
       Wolf Lammen, 17-Dec-2018.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    wl-luk-a1i $p |- ( ps -> ph ) $=
      ( wn wl-luk-pm2.24i wl-luk-con4i ) ABABDCEF $.
  $}

  ${
    wl-luk-mpi.1 $e |- ps $.
    wl-luk-mpi.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A nested _modus ponens_ inference.  Copy of ~ mpi with a different
       proof.  (Contributed by Wolf Lammen, 17-Dec-2018.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    wl-luk-mpi $p |- ( ph -> ch ) $=
      ( wn wl-luk-a1i wl-luk-imtrid wl-luk-pm2.18d ) ACCFZBACBJDGEHI $.
  $}

  ${
    wl-luk-imim2i.1 $e |- ( ph -> ps ) $.
    $( Inference adding common antecedents in an implication.  Copy of ~ imim2i
       with a different proof.  (Contributed by Wolf Lammen, 17-Dec-2018.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    wl-luk-imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $=
      ( wi ax-luk1 wl-luk-mpi ) CAEABECBEDCABFG $.
  $}

  ${
    wl-luk-imtrdi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    wl-luk-imtrdi.2 $e |- ( ch -> th ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  Copy of ~ syl6 with a different
       proof.  (Contributed by Wolf Lammen, 17-Dec-2018.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    wl-luk-imtrdi $p |- ( ph -> ( ps -> th ) ) $=
      ( wi wl-luk-imim2i wl-luk-syl ) ABCGBDGECDBFHI $.
  $}

  $( ~ ax-3 proved from Lukasiewicz's axioms.  (Contributed by Wolf Lammen,
     17-Dec-2018.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  wl-luk-ax3 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $=
    ( wn wi ax-luk3 ax-luk1 wl-luk-imtrid ax-luk2 wl-luk-imtrdi ) ACZBCZDZBJADZ
    ABKADLMBAEJKAFGAHI $.

  $( ~ ax-1 proved from Lukasiewicz's axioms.  (Contributed by Wolf Lammen,
     17-Dec-2018.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  wl-luk-ax1 $p |- ( ph -> ( ps -> ph ) ) $=
    ( wn wi ax-luk3 wl-luk-ax3 wl-luk-syl ) AACBCZDBADAHEABFG $.

  $( This theorem, called "Assertion", can be thought of as closed form of
     _modus ponens_ ~ ax-mp .  Theorem *2.27 of [WhiteheadRussell] p. 104.
     Copy of ~ pm2.27 with a different proof.  (Contributed by Wolf Lammen,
     17-Dec-2018.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  wl-luk-pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $=
    ( wi wn wl-luk-ax1 ax-luk1 wl-luk-syl ax-luk2 wl-luk-imtrdi ) AABCZBDZBCZBA
    KACJLCAKEKABFGBHI $.

  ${
    wl-luk-com12.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference that swaps (commutes) antecedents in an implication.  Copy of
       ~ com12 with a different proof.  (Contributed by Wolf Lammen,
       17-Dec-2018.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    wl-luk-com12 $p |- ( ps -> ( ph -> ch ) ) $=
      ( wi wl-luk-pm2.27 wl-luk-imtrid ) ABCEBCDBCFG $.
  $}

  $( From a wff and its negation, anything follows.  Theorem *2.21 of
     [WhiteheadRussell] p. 104.  Also called the Duns Scotus law.  Copy of
     ~ pm2.21 with a different proof.  (Contributed by Wolf Lammen,
     17-Dec-2018.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  wl-luk-pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( wn ax-luk3 wl-luk-com12 ) AACBABDE $.

  ${
    wl-luk-con1i.1 $e |- ( -. ph -> ps ) $.
    $( A contraposition inference.  Copy of ~ con1i with a different proof.
       (Contributed by Wolf Lammen, 17-Dec-2018.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    wl-luk-con1i $p |- ( -. ps -> ph ) $=
      ( wn wl-luk-pm2.21 wl-luk-imtrid wl-luk-pm2.18d ) BDZAADBHACBAEFG $.
  $}

  ${
    wl-luk-ja.1 $e |- ( -. ph -> ch ) $.
    wl-luk-ja.2 $e |- ( ps -> ch ) $.
    $( Inference joining the antecedents of two premises.  Copy of ~ ja with a
       different proof.  (Contributed by Wolf Lammen, 17-Dec-2018.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    wl-luk-ja $p |- ( ( ph -> ps ) -> ch ) $=
      ( wi wn wl-luk-con1i wl-luk-imim2i wl-luk-imtrid wl-luk-pm2.18d ) ABFZCCG
      ALCACDHBCAEIJK $.
  $}

  $( A closed form of syllogism (see ~ syl ).  Theorem *2.05 of
     [WhiteheadRussell] p. 100.  Copy of ~ imim2 with a different proof.
     (Contributed by Wolf Lammen, 17-Dec-2018.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  wl-luk-imim2 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    ( wi ax-luk1 wl-luk-com12 ) CADABDCBDCABEF $.

  ${
    wl-luk-a1d.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing an embedded antecedent.  Copy of ~ imim2 with a
       different proof.  (Contributed by Wolf Lammen, 17-Dec-2018.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    wl-luk-a1d $p |- ( ph -> ( ch -> ps ) ) $=
      ( wi wl-luk-ax1 wl-luk-syl ) ABCBEDBCFG $.
  $}

  $( ~ ax-2 proved from Lukasiewicz's axioms.  (Contributed by Wolf Lammen,
     17-Dec-2018.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  wl-luk-ax2 $p |- ( ( ph -> ( ps -> ch ) )
      -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( wi wn wl-luk-pm2.21 wl-luk-a1d wl-luk-imim2 wl-luk-ja ) ABCDABDZACDZDAEKJ
    ACFGBCAHI $.

  $( Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  Copy
     of ~ id with a different proof.  (Contributed by Wolf Lammen,
     17-Dec-2018.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  wl-luk-id $p |- ( ph -> ph ) $=
    ( wn wi ax-luk3 ax-luk2 wl-luk-syl ) AABACAAADAEF $.

  $( Converse of double negation.  Theorem *2.14 of [WhiteheadRussell] p. 102.
     In classical logic (our logic) this is always true.  In intuitionistic
     logic this is not always true; in intuitionistic logic, when this is true
     for some ` ph ` , then ` ph ` is stable.  Copy of ~ notnotr with a
     different proof.  (Contributed by Wolf Lammen, 17-Dec-2018.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
  wl-luk-notnotr $p |- ( -. -. ph -> ph ) $=
    ( wn wl-luk-id wl-luk-con1i ) AABZECD $.

  $( Swap antecedents.  Theorem *2.04 of [WhiteheadRussell] p. 100.  This was
     the third axiom in Frege's logic system, specifically Proposition 8 of
     [Frege1879] p. 35.  Copy of ~ pm2.04 with a different proof.  (Contributed
     by Wolf Lammen, 7-Jul-2019.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  wl-luk-pm2.04 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi wl-luk-ax1 wl-luk-ax2 wl-luk-imtrid ) BABDABCDDACDBAEABCFG $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Implication chains
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    wl-section-impchain.hyp $e |- ph $.
    $( An implication like ` ( ps -> ph ) ` with one antecedent can easily be
       extended by prepending more and more antecedents, as in
       ` ( ch -> ( ps -> ph ) ) ` or ` ( th -> ( ch -> ( ps -> ph ) ) ) ` .  I
       call these expressions implication chains, and the number of antecedents
       (number of nodes minus one) denotes their length.  A given length often
       marks just a required minimum value, since the consequent ` ph ` itself
       may represent an implication, or even an implication chain, such hiding
       part of the whole chain.  As an extension, it is useful to consider a
       single variable ` ph ` as a degenerate implication chain of length zero.

       Implication chains play a particular role in logic, as all propositional
       expressions turn out to be convertible to one or more implication
       chains, their nodes as simple as a variable, or its negation.

       So there is good reason to focus on implication chains as a sort of
       normalized expressions, and build some general theorems around them,
       with proofs using recursive patterns.  This allows for theorems
       referring to longer and longer implication chains in an automated way.

       The theorem names in this section contain the text fragment 'impchain'
       to point out their relevance to implication chains, followed by a number
       indicating the (minimal) length of the longest chain involved.
       (Contributed by Wolf Lammen, 6-Jul-2019.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    wl-section-impchain $p |- ph $=
      (  ) B $.
  $}

  $( This series of theorems provide a means of exchanging the consequent of an
     implication chain via a simple implication.  In the main part, Theorems
     ~ ax-mp , ~ syl , ~ syl6 , ~ syl8 form the beginning of this series.
     These theorems are replicated here, but with proofs that aim at a
     recursive scheme, allowing to base a proof on that of the previous one in
     the series.  (Contributed by Wolf Lammen, 17-Nov-2019.) $)
  wl-impchain-mp-x $p |- T. $=
    ( tru ) A $.

  ${
    $( Exchange the consequent of an implication chain of length 0. $)
    wl-impchain-mp-0.a $e |- ps $.
    $( Use to replace the consequent. $)
    wl-impchain-mp-0.b $e |- ( ps -> ph ) $.
    $( This theorem is the start of a proof recursion scheme where we replace
       the consequent of an implication chain.  The number '0' in the theorem
       name indicates that the modified chain has no antecedents.

       This theorem is in fact a copy of ~ ax-mp , and is repeated here to
       emphasize the recursion using similar theorem names.  (Contributed by
       Wolf Lammen, 6-Jul-2019.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    wl-impchain-mp-0 $p |- ph $=
      ( ax-mp ) BACDE $.
  $}

  ${
    $( Exchange the consequent of an implication chain of length 1. $)
    wl-impchain-mp-1.a $e |- ( ch -> ps ) $.
    $( Use to replace the consequent. $)
    wl-impchain-mp-1.b $e |- ( ps -> ph ) $.
    $( This theorem is in fact a copy of ~ wl-luk-syl , and repeated here to
       demonstrate a recursive proof scheme.  The number '1' in the theorem
       name indicates that a chain of length 1 is modified.  (Contributed by
       Wolf Lammen, 6-Jul-2019.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    wl-impchain-mp-1 $p |- ( ch -> ph ) $=
      ( wi wl-luk-imim2i wl-impchain-mp-0 ) CAFCBFDBACEGH $.
  $}

  ${
    $( Exchange the consequent of an implication chain of length 2. $)
    wl-impchain-mp-2.a $e |- ( th -> ( ch -> ps ) ) $.
    $( Use to replace the consequent. $)
    wl-impchain-mp-2.b $e |- ( ps -> ph ) $.
    $( This theorem is in fact a copy of ~ wl-luk-imtrdi , and repeated here to
       demonstrate a recursive proof scheme.  The number '2' in the theorem
       name indicates that a chain of length 2 is modified.  (Contributed by
       Wolf Lammen, 6-Jul-2019.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    wl-impchain-mp-2 $p |- ( th -> ( ch -> ph ) ) $=
      ( wi wl-luk-imim2i wl-impchain-mp-1 ) CAGCBGDEBACFHI $.
  $}

  $( It is often convenient to have the antecedent under focus in first
     position, so we can apply immediate theorem forms (as opposed to
     deduction, tautology form).  This series of theorems swaps the first with
     the last antecedent in an implication chain.  This kind of swapping is
     self-inverse, whence we prefer it over, say, rotating theorems.  A
     consequent can hide a tail of a longer chain, so theorems of this series
     appear as swapping a pair of antecedents with fixed offsets.  This form of
     swapping antecedents is flexible enough to allow for any permutation of
     antecedents in an implication chain.

     The first elements of this series correspond to ~ com12 , ~ com13 ,
     ~ com14 and ~ com15 in the main part.

     The proofs of this series aim at automated proving using a simple
     recursive scheme.  It employs the previous theorem in the series along
     with a sample from the ~ wl-impchain-mp-x series developed before.
     (Contributed by Wolf Lammen, 17-Nov-2019.) $)
  wl-impchain-com-1.x $p |- T. $=
    ( tru ) A $.

  ${
    wl-impchain-com-1.1.a $e |- ( ps -> ph ) $.
    $( A degenerate form of antecedent swapping.  The number '1' in the theorem
       name indicates that it handles a chain of length 1.

       Since there is just one antecedent in the chain, there is nothing to
       swap.  Nondegenerated forms begin with ~ wl-impchain-com-1.2 , for more
       see there.  (Contributed by Wolf Lammen, 7-Jul-2019.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    wl-impchain-com-1.1 $p |- ( ps -> ph ) $=
      (  ) C $.
  $}

  ${
    wl-impchain-com.1.2.a $e |- ( ch -> ( ps -> ph ) ) $.
    $( This theorem is in fact a copy of ~ wl-luk-com12 , and repeated here to
       demonstrate a simple proof scheme.  The number '2' in the theorem name
       indicates that a chain of length 2 is modified.

       See ~ wl-impchain-com-1.x for more information how this proof is
       generated.  (Contributed by Wolf Lammen, 7-Jul-2019.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    wl-impchain-com-1.2 $p |- ( ps -> ( ch -> ph ) ) $=
      ( wi wl-impchain-com-1.1 wl-luk-pm2.04 wl-impchain-mp-0 ) CAEZBBIECBAEZEJ
      CDFCBAGHF $.
  $}

  ${
    wl-impchain-com-1.3.h1 $e |- ( th -> ( ch -> ( ps -> ph ) ) ) $.
    $( This theorem is in fact a copy of ~ com13 , and repeated here to
       demonstrate a simple proof scheme.  The number '3' in the theorem name
       indicates that a chain of length 3 is modified.

       See ~ wl-impchain-com-1.x for more information how this proof is
       generated.  (Contributed by Wolf Lammen, 7-Jul-2019.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    wl-impchain-com-1.3 $p |- ( ps -> ( ch -> ( th -> ph ) ) ) $=
      ( wi wl-impchain-com-1.2 wl-luk-pm2.04 wl-impchain-mp-1 ) DAFZBCBJFDBAFZF
      CKCDEGDBAHIG $.
  $}

  ${
    wl-impchain-com-1.4.h1 $e |- ( et -> ( th -> ( ch -> ( ps -> ph ) ) ) ) $.
    $( This theorem is in fact a copy of ~ com14 , and repeated here to
       demonstrate a simple proof scheme.  The number '4' in the theorem name
       indicates that a chain of length 4 is modified.

       See ~ wl-impchain-com-1.x for more information how this proof is
       generated.  (Contributed by Wolf Lammen, 7-Jul-2019.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    wl-impchain-com-1.4 $p |- ( ps -> ( th -> ( ch -> ( et -> ph ) ) ) ) $=
      ( wi wl-impchain-com-1.3 wl-luk-pm2.04 wl-impchain-mp-2 ) EAGZBDCBKGEBAGZ
      GDCLCDEFHEBAIJH $.
  $}

  $( This series of theorems allow swapping any two antecedents in an
     implication chain.  The theorem names follow a pattern wl-impchain-com-n.m
     with integral numbers n < m, that swaps the m-th antecedent with n-th one
     in an implication chain.  It is sufficient to restrict the length of the
     chain to m, too, since the consequent can be assumed to be the tail right
     of the m-th antecedent of any arbitrary sized implication chain.  We
     further assume n > 1, since the ~ wl-impchain-com-1.x series already
     covers the special case n = 1.

     Being able to swap any two antecedents in an implication chain lays the
     foundation of permuting its antecedents arbitrarily.

     The proofs of this series aim at automated proofing using a simple scheme.
     Any instance of this series is a triple step of swapping the first and
     n-th antecedent, then the first and the m-th, then the first and the n-th
     antecedent again.  Each of these steps is an instance of the
     ~ wl-impchain-com-1.x series.  (Contributed by Wolf Lammen,
     17-Nov-2019.) $)
  wl-impchain-com-n.m $p |- T. $=
    ( tru ) A $.

  ${
    wl-impchain-com-2.3.h1 $e |- ( th -> ( ch -> ( ps -> ph ) ) ) $.
    $( This theorem is in fact a copy of ~ com23 .  It starts a series of
       theorems named after ~ wl-impchain-com-n.m .  For more information see
       there.  (Contributed by Wolf Lammen, 12-Nov-2019.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    wl-impchain-com-2.3 $p |- ( th -> ( ps -> ( ch -> ph ) ) ) $=
      ( wi wl-impchain-com-1.2 wl-impchain-com-1.3 ) CAFDBABDCBAFCDEGHG $.
  $}

  ${
    wl-impchain-com-2.4.h1 $e |- ( et -> ( th -> ( ch -> ( ps -> ph ) ) ) ) $.
    $( This theorem is in fact a copy of ~ com24 .  It is another instantiation
       of theorems named after ~ wl-impchain-com-n.m .  For more information
       see there.  (Contributed by Wolf Lammen, 17-Nov-2019.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    wl-impchain-com-2.4 $p |- ( et -> ( ps -> ( ch -> ( th -> ph ) ) ) ) $=
      ( wi wl-impchain-com-1.2 wl-impchain-com-1.4 ) CDAGGEBABCEDCBAGGDEFHIH $.
  $}

  ${
    wl-impchain-com-3.2.1.h1 $e |- ( th -> ( ch -> ( ps -> ph ) ) ) $.
    $( This theorem is in fact a copy of ~ com3r .  The proof is an example of
       how to arrive at arbitrary permutations of antecedents, using only
       swapping theorems.  The recursion principle is to first swap the correct
       antecedent to the position just before the consequent, and then employ a
       theorem handling an implication chain of length one less to reorder the
       others.  (Contributed by Wolf Lammen, 17-Nov-2019.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    wl-impchain-com-3.2.1 $p |- ( ps -> ( th -> ( ch -> ph ) ) ) $=
      ( wi wl-impchain-com-2.3 wl-impchain-com-1.2 ) CAFBDABCDEGH $.
  $}

  $( If an implication chain is assumed (hypothesis) or proven (theorem) to
     hold, then we may add any extra antecedent to it, without changing its
     truth.  This is expressed in its simplest form in ~ wl-luk-a1i , that
     allows prepending an arbitrary antecedent to an implication chain.  Using
     our antecedent swapping theorems described in ~ wl-impchain-com-n.m , we
     may then move such a prepended antecedent to any desired location within
     all antecedents.  The first series of theorems of this kind adds a single
     antecedent somewhere to an implication chain.  The appended number in the
     theorem name indicates its position within all antecedents, 1 denoting the
     head position.  A second theorem series extends this idea to multiple
     additions (TODO).

     Adding antecedents to an implication chain usually weakens their
     universality.  The consequent afterwards depends on more conditions than
     before, which renders the implication chain less versatile.  So you find
     this proof technique mostly when you adjust a chain to a hypothesis of a
     rule.  A common case are syllogisms merging two implication chains into
     one.

     The first elements of the first series correspond to ~ a1i , ~ a1d and
     ~ a1dd in the main part.

     The proofs of this series aim at automated proving using a simple
     recursive scheme.  It employs the previous theorem in the series along
     with a sample from the ~ wl-impchain-com-1.x series developed before.
     (Contributed by Wolf Lammen, 20-Jun-2020.) $)
  wl-impchain-a1-x $p |- T. $=
    ( tru ) A $.

  ${
    wl-impchain-a1-1.a $e |- ph $.
    $( Inference rule, a copy of ~ a1i .  Head start of a recursive proof
       pattern.  (Contributed by Wolf Lammen, 20-Jun-2020.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    wl-impchain-a1-1 $p |- ( ps -> ph ) $=
      ( wl-luk-a1i ) ABCD $.
  $}

  ${
    wl-impchain-a1-2.a $e |- ( ph -> ps ) $.
    $( Inference rule, a copy of ~ a1d .  First recursive proof based on the
       previous instance.  (Contributed by Wolf Lammen, 20-Jun-2020.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    wl-impchain-a1-2 $p |- ( ph -> ( ch -> ps ) ) $=
      ( wi wl-impchain-a1-1 wl-impchain-com-1.2 ) BACABECDFG $.
  $}

  ${
    wl-impchain-a1-3.a $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference rule, a copy of ~ a1dd .  A recursive proof depending on
       previous instances, and demonstrating the proof pattern.  (Contributed
       by Wolf Lammen, 20-Jun-2020.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    wl-impchain-a1-3 $p |- ( ph -> ( ps -> ( th -> ch ) ) ) $=
      ( wi wl-impchain-a1-2 wl-impchain-com-2.3 ) CBDAABCFDEGH $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Theorems around the conditional operator
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( If one case of an ` if- ` condition is false, the other automatically
     follows.  (Contributed by Wolf Lammen, 21-Jul-2024.) $)
  wl-ifp-ncond1 $p |- ( -. ps ->
                              ( if- ( ph , ps , ch ) <-> ( -. ph /\ ch ) ) ) $=
    ( wn wif wa wo df-ifp wb simpr con3i biorf syl bitr4id ) BDZABCEABFZADCFZGZ
    QABCHOPDQRIPBABJKPQLMN $.

  $( If one case of an ` if- ` condition is false, the other automatically
     follows.  (Contributed by Wolf Lammen, 21-Jul-2024.) $)
  wl-ifp-ncond2 $p |- ( -. ch -> ( if- ( ph , ps , ch ) <-> ( ph /\ ps ) ) ) $=
    ( wn wif wa wl-ifp-ncond1 ifpn notnotb anbi1i 3bitr4g ) CDADZCBELDZBFABCEAB
    FLCBGABCHAMBAIJK $.

  $( If one case of an ` if- ` condition is a consequence of the other, the
     expression in ~ df-ifp can be shortened.  (Contributed by Wolf Lammen,
     12-Jun-2024.) $)
  wl-ifpimpr $p |- ( ( ch -> ps ) ->
                       ( if- ( ph , ps , ch ) <-> ( ( ph /\ ps ) \/ ch ) ) ) $=
    ( wi wa wn wo wb pm4.72 biimpi orcom bitrdi anbi2d andi orbi1d df-ifp biidd
    wif cases orbi2i orass bitr4i 3bitr4g ) CBDZABEZAFZCEZGUEACEZGZUGGZABCRUECG
    ZUDUEUIUGUDUEABCGZEUIUDBULAUDBCBGZULUDBUMHCBIJCBKLMABCNLOABCPUKUEUHUGGZGUJC
    UNUEACCCACQUFCQSTUEUHUGUAUBUC $.

  $( If one case of an ` if- ` condition is a consequence of the other, the
     expression in ~ dfifp4 can be shortened.  (Contributed by Wolf Lammen,
     18-Jun-2024.) $)
  wl-ifp4impr $p |- ( ( ch -> ps ) ->
                       ( if- ( ph , ps , ch ) <-> ( ( ph \/ ch ) /\ ps ) ) ) $=
    ( wi wif wa wo wl-ifpimpr wb pm4.71 biimpi orbi2d andir bitr4di bitrd ) CBD
    ZABCEABFZCGZACGBFZABCHPRQCBFZGSPCTQPCTICBJKLACBMNO $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Alternative development of hadd, cadd
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Alternative definition of ~ whad based on ~ hadifp .  See ~ df-had to
     learn how it is currently introduced.  The only use case so far is being a
     binary addition primitive for ~ df-sad .  If inputs are viewed as binary
     digits (true is 1, false is 0), the result is what a binary single-bit
     addition with carry-in yields in the low bit of their sum.

     The core meaning is to check whether an odd number of three inputs are
     true.  The ` \/_ ` operation tests this for two inputs.  So, if the first
     input is true, the two remaining inputs need to amount to an even (or: not
     an odd) number, else to an odd number.

     The idea of an odd number of inputs being true carries over to other than
     3 inputs by recursion:  In an informal notation we depend the case with
     n+1 inputs, ` ph ` being the additional one, recursively on that of n
     inputs:  "(n+1)-xor" ` <-> if- ( ph , -. ` "n-xor" ` , ` "n-xor" ` ) ` .
     The base case is "0-xor" being ` F. ` , because zero inputs never contain
     an odd number among them.  Then we find, after simplifying, in our
     informal notation:

     "2-xor" ` ( ph , ps ) <-> ( ph \/_ ps ) ` (see ~ wl-2xor ).

     Our definition here follows exactly the above pattern.

     In microprocessor technology an addition limited to a range (a one-bit
     range in our case) is called a "wrap-around operation".  The name "had",
     as in ~ df-had , by contrast, is somehow suggestive of a "half adder"
     instead.  Such a circuit, for one, takes two inputs only, no carry-in, and
     then yields two outputs - both sum and carry.  That's why we use "3xor"
     instead of "had" here.  (Contributed by Wolf Lammen, 24-Apr-2024.) $)
  wl-df-3xor $p |- ( hadd ( ph , ps , ch )
               <-> if- ( ph , -. ( ps \/_ ch ) , ( ps \/_ ch ) ) ) $=
    ( whad wb wxo wif wn hadifp wtru xnor a1i biidd ifpbi23d mptru bitri ) ABCD
    ABCEZBCFZGZARHZRGZABCISUAEJAQRTRQTEJBCKLJRMNOP $.

  $( Alternative definition of ~ wl-df-3xor , using triple exclusive
     disjunction, or XOR3.  You can add more input by appending each one with a
     ` \/_ ` .  Copy of ~ hadass .  (Contributed by Mario Carneiro,
     4-Sep-2016.) df-had redefined.  (Revised by Wolf Lammen, 1-May-2024.) $)
  wl-df3xor2 $p |- ( hadd ( ph , ps , ch ) <-> ( ph \/_ ( ps \/_ ch ) ) ) $=
    ( wxo wn wif whad ifpn wl-df-3xor wb df-xor nbbn ifpdfbi 3bitr2i 3bitr4i )
    ABCDZEZPFAEZPQFZABCGAPDZAQPHABCITAPJERPJSAPKAPLRPMNO $.

  $( Alternative form of ~ wl-df3xor2 .  Copy of ~ df-had .  (Contributed by
     Mario Carneiro, 4-Sep-2016.) df-had redefined.  (Revised by Wolf Lammen,
     1-May-2024.) $)
  wl-df3xor3 $p |- ( hadd ( ph , ps , ch ) <-> ( ( ph \/_ ps ) \/_ ch ) ) $=
    ( whad wxo wl-df3xor2 xorass bitr4i ) ABCDABCEEABECEABCFABCGH $.

  $( If the first input is true, then triple xor is equivalent to the
     biconditionality of the other two inputs.  (Contributed by Mario Carneiro,
     4-Sep-2016.) df-had redefined.  (Revised by Wolf Lammen, 24-Apr-2024.) $)
  wl-3xortru $p |- ( ph -> ( hadd ( ph , ps , ch ) <-> -. ( ps \/_ ch ) ) ) $=
    ( whad wxo wn wif wl-df-3xor ifptru bitrid ) ABCDABCEZFZKGALABCHALKIJ $.

  $( If the first input is false, then triple xor is equivalent to the
     exclusive disjunction of the other two inputs.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) df-had redefined.  (Revised by Wolf Lammen,
     29-Apr-2024.) $)
  wl-3xorfal $p |- ( -. ph -> ( hadd ( ph , ps , ch ) <-> ( ps \/_ ch ) ) ) $=
    ( whad wxo wn wif wl-df-3xor ifpfal bitrid ) ABCDABCEZFZKGAFKABCHALKIJ $.

  $( Triple xor can be replaced with a triple biconditional.  Unlike ` \/_ ` ,
     you cannot add more inputs by simply stacking up more biconditionals, and
     still express an "odd number of inputs".  (Contributed by Wolf Lammen,
     24-Apr-2024.) $)
  wl-3xorbi $p |- ( hadd ( ph , ps , ch ) <-> ( ph <-> ( ps <-> ch ) ) ) $=
    ( whad wxo wb wn wl-df3xor2 df-xor xor3 xnor bibi2i bitr4i 3bitri ) ABCDABC
    EZEAOFGZABCFZFZABCHAOIPAOGZFRAOJQSABCKLMN $.

  $( Alternative form of ~ wl-3xorbi .  (Contributed by Mario Carneiro,
     4-Sep-2016.) df-had redefined.  (Revised by Wolf Lammen, 24-Apr-2024.) $)
  wl-3xorbi2 $p |- ( hadd ( ph , ps , ch ) <-> ( ( ph <-> ps ) <-> ch ) ) $=
    ( whad wb wl-3xorbi biass bitr4i ) ABCDABCEEABECEABCFABCGH $.

  ${
    wl-3xorbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    wl-3xorbid.2 $e |- ( ph -> ( th <-> ta ) ) $.
    wl-3xorbid.3 $e |- ( ph -> ( et <-> ze ) ) $.
    $( Equivalence theorem for triple xor.  (Contributed by Mario Carneiro,
       4-Sep-2016.) df-had redefined.  (Revised by Wolf Lammen,
       24-Apr-2024.) $)
    wl-3xorbi123d $p |- ( ph ->
      ( hadd ( ps , th , et ) <-> hadd ( ch , ta , ze ) ) ) $=
      ( wb whad bibi12d wl-3xorbi2 3bitr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIM
      JMBDFNCEGNO $.
  $}

  ${
    wl-3xorbii.1 $e |- ( ps <-> ch ) $.
    wl-3xorbii.2 $e |- ( th <-> ta ) $.
    wl-3xorbii.3 $e |- ( et <-> ze ) $.
    $( Equivalence theorem for triple xor.  Copy of ~ hadbi123i .  (Contributed
       by Mario Carneiro, 4-Sep-2016.) $)
    wl-3xorbi123i $p |- ( hadd ( ps , th , et ) <-> hadd ( ch , ta , ze ) ) $=
      ( whad wb wtru a1i wl-3xorbi123d mptru ) ACEJBDFJKLABCDEFABKLGMCDKLHMEFKL
      IMNO $.
  $}

  $( Rotation law for triple xor.  (Contributed by Mario Carneiro, 4-Sep-2016.)
     df-had redefined.  (Revised by Wolf Lammen, 24-Apr-2024.) $)
  wl-3xorrot $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ps , ch , ph ) ) $=
    ( wb whad bicom wl-3xorbi wl-3xorbi2 3bitr4i ) ABCDZDJADABCEBCAEAJFABCGBCAH
    I $.

  $( Commutative law for triple xor.  Copy of ~ hadcoma .  (Contributed by
     Mario Carneiro, 4-Sep-2016.)  (Proof shortened by Wolf Lammen,
     17-Dec-2023.) $)
  wl-3xorcoma $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ps , ph , ch ) ) $=
    ( wb whad bicom bibi1i wl-3xorbi2 3bitr4i ) ABDZCDBADZCDABCEBACEJKCABFGABCH
    BACHI $.

  $( Commutative law for triple xor.  (Contributed by Mario Carneiro,
     4-Sep-2016.) df-had redefined.  (Revised by Wolf Lammen, 24-Apr-2024.) $)
  wl-3xorcomb $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ph , ch , ps ) ) $=
    ( whad wl-3xorcoma wl-3xorrot bitri ) ABCDBACDACBDABCEBACFG $.

  $( Flipping the first input flips the triple xor. ~ wl-3xorrot can rotate any
     input to the front, so flipping any one of them does the same.
     (Contributed by Wolf Lammen, 1-May-2024.) $)
  wl-3xornot1 $p |- ( -. hadd ( ph , ps , ch )
                                          <-> hadd ( -. ph , ps , ch ) ) $=
    ( wn whad wb wl-3xorbi nbbn xchbinxr bitr2i ) ADZBCEKBCFZFZABCEZDKBCGMALFNA
    LHABCGIJ $.

  $( Triple xor distributes over negation.  Copy of ~ hadnot .  (Contributed by
     Mario Carneiro, 4-Sep-2016.)  (Proof shortened by Wolf Lammen,
     11-Jul-2020.) $)
  wl-3xornot $p |- ( -. hadd ( ph , ps , ch ) <->
                                         hadd ( -. ph , -. ps , -. ch ) ) $=
    ( wb wn whad notbi bibi1i xor3 wl-3xorbi2 xchnxbir 3bitr4i ) ABDZCEZDZAEZBE
    ZDZNDABCFZEPQNFMRNABGHMCDOSMCIABCJKPQNJL $.

  $( In the recursive scheme

     "(n+1)-xor" ` <-> if- ( ph , -. ` "n-xor" ` , ` "n-xor" ` ) `

     we set n = 0 to formally arrive at an expression for "1-xor".  The base
     case "0-xor" is replaced with ` F. ` , as a sequence of 0 inputs never has
     an odd number being part of it.  (Contributed by Wolf Lammen,
     11-May-2024.) $)
  wl-1xor $p |- ( if- ( ps , -. F. , F. ) <-> ps ) $=
    ( wfal wn wif wtru wb tbtru biimpi notfal bitr4di nbfal casesifp bicomi ) A
    ABCZBDAANBAAENAAEFAGHIJACABFAKHLM $.

  $( In the recursive scheme

     "(n+1)-xor" ` <-> if- ( ph , -. ` "n-xor" ` , ` "n-xor" ` ) `

     we set n = 1 to formally arrive at an expression for "2-xor".  It is based
     on "1-xor", that is known to be equivalent to its only input (see
     ~ wl-1xor ).  (Contributed by Wolf Lammen, 11-May-2024.) $)
  wl-2xor $p |- ( if- ( ph , -. ps , ps ) <-> ( ph \/_ ps ) ) $=
    ( wn wb wif wxo ifpdfbi df-xor nbbn bitr4i ifpn 3bitr4ri ) ACZBDZMBBCZEABFZ
    AOBEMBGPABDCNABHABIJAOBKL $.

  $( Alternative definition of ~ wcad .  See ~ df-cad to learn how it is
     currently introduced.  The only use case so far is being a binary addition
     primitive for ~ df-sad .  If inputs are viewed as binary digits (true is
     1, false is 0), the result is whether ordinary binary full addition yields
     a carry bit.  That is what the name ~ df-cad is derived from:  "carry of
     an addition".  Here we stick with this abbreviated form of our notation
     above, but still use "adder carry" as a shorthand for "at least 2 out of
     3" in text.

     The core meaning is to check whether at least two of three inputs are
     true.  So, if the first input is true, at least one of the two remaining
     must be true, else even both.  This theorem is the in-between of "at least
     1 out of 3", given by triple disjunction ~ df-3or , and "(at least) 3 out
     of 3", expressed by triple conjunction ~ df-3an .

     The notion above can be generalized to other input numbers with other
     minimum values as follows.  Let us introduce informally a logical
     operation "n-mintru-m" taking n inputs, and requiring at least m of them
     be true to let the operation itself be true.  There now exists a recursive
     scheme to define it for increasing n, m.  We start with the base case n =
     0.  Here "n-mintru-0" is equivalent to ` T. ` (any sequence of inputs
     contains at least zero true inputs), the other "0-mintru-m" is for any m >
     0 equivalent to ` F. ` , because a sequence of zero inputs never has a
     positive number of them true.  The general case adds a new input ` ph ` to
     a given sequence of n inputs, and reduces that case for all integers m to
     that of the smaller sequence by recursion, informally written as:

     "(n+1)-mintru-(m+1)" ` <-> if- ( ph , ` "n-mintru-m" ` , `
     "n-mintru-(m+1)" ` ) `

     Our definition here matches "3-mintru-2" with inputs ` ph ` , ` ps ` and
     ` ch ` .  Starting from the base cases we find after simplifications:
     "2-mintru-2" ` ( ps , ch ) <-> ( ps /\ ch ) ` ( ~ wl-2mintru2 ), and
     "2-mintru-1" ` ( ps , ch ) <-> ( ps \/ ch ) ` ( ~ wl-2mintru1 ).  Plugging
     these expressions into the formula above for n = 3, m = 2 yields exactly
     our definition here.  (Contributed by Wolf Lammen, 2-May-2024.) $)
  wl-df-3mintru2 $p |- ( cadd ( ph , ps , ch )
               <-> if- ( ph , ( ps \/ ch ) , ( ps /\ ch ) ) ) $=
    ( wcad wo wa wif cadrot cadifp bitri ) ABCDBCADABCEBCFGABCHBCAIJ $.

  $( The adder carry in disjunctive normal form.  An alternative highly
     symmetric definition emphasizing the independence of order of the inputs
     ` ph ` , ` ps ` and ` ch ` .  Copy of ~ cador .  (Contributed by Mario
     Carneiro, 4-Sep-2016.) df-cad redefined.  (Revised by Wolf Lammen,
     12-Jun-2024.) $)
  wl-df2-3mintru2 $p |- ( cadd ( ph , ps , ch ) <->
        ( ( ph /\ ps ) \/ ( ph /\ ch ) \/ ( ps /\ ch ) ) ) $=
    ( wo wa wcad w3o andi orbi1i wif wl-df-3mintru2 wi animorl wl-ifpimpr ax-mp
    wb bitri df-3or 3bitr4i ) ABCDZEZBCEZDZABEZACEZDZUBDABCFZUDUEUBGUAUFUBABCHI
    UGATUBJZUCABCKUBTLUHUCPBCCMATUBNOQUDUEUBRS $.

  $( The adder carry in conjunctive normal form.  An alternative highly
     symmetric definition emphasizing the independence of order of the inputs
     ` ph ` , ` ps ` and ` ch ` .  Copy of ~ cadan .  (Contributed by Mario
     Carneiro, 4-Sep-2016.) df-cad redefined.  (Revised by Wolf Lammen,
     18-Jun-2024.) $)
  wl-df3-3mintru2 $p |- ( cadd ( ph , ps , ch ) <->
        ( ( ph \/ ps ) /\ ( ph \/ ch ) /\ ( ps \/ ch ) ) ) $=
    ( wa wo wcad w3a ordi anbi1i wl-df-3mintru2 wi wb animorl wl-ifp4impr ax-mp
    wif bitri df-3an 3bitr4i ) ABCDZEZBCEZDZABEZACEZDZUBDABCFZUDUEUBGUAUFUBABCH
    IUGAUBTPZUCABCJTUBKUHUCLBCCMAUBTNOQUDUEUBRS $.

  $( An alternative definition of the adder carry.  Copy of ~ df-cad .
     (Contributed by Mario Carneiro, 4-Sep-2016.) df-cad redefined.  (Revised
     by Wolf Lammen, 19-Jun-2024.) $)
  wl-df4-3mintru2 $p |- ( cadd ( ph , ps , ch ) <->
        ( ( ph /\ ps ) \/ ( ch /\ ( ph \/_ ps ) ) ) ) $=
    ( wa w3o wo wcad wxo 3orass wl-df2-3mintru2 wn biancomi anbi1ci anass bitri
    xor2 orbi2i pm5.63 andir 3bitr2i 3bitr4i ) ABDZACDZBCDZEUBUCUDFZFZABCGUBCAB
    HZDZFZUBUCUDIABCJUIUBUBKZABFZCDZDZFUBULFUFUHUMUBUHUJUKDZCDUMUGUNCUGUJUKABPL
    MUJUKCNOQUBULRULUEUBABCSQTUA $.

  $( Using the recursion formula:

     "(n+1)-mintru-(m+1)" ` <-> if- ( ph , ` "n-mintru-m" ` , `
     "n-mintru-(m+1)" ` ) `

     for "1-mintru-1" (meaning "at least 1 out of 1 input is true") by plugging
     in n = 0, m = 0, and simplifying.  The expressions "0-mintru-0" and
     "0-mintru-1" are base cases of the recursion, meaning "in a sequence of
     zero inputs, at least 0 / 1 input is true", respectively equivalent to
     ` T. ` / ` F. ` .

     Negating an "n-mintru1" operation means:  All n inputs ` ph ` .. ` th `
     are false.  This is also conveniently expressed as ` -. ( ph \/ ` ..
     ` \/ th ) ` .  Applying this idea here (n = 1) yields the obvious result
     that in an input sequence of size 1 only then all will be false, if its
     single input is.  (Contributed by Wolf Lammen, 10-May-2024.) $)
  wl-1mintru1 $p |- ( if- ( ch , T. , F. ) <-> ch ) $=
    ( wtru wfal wif wb tbtru biimpi wn nbfal casesifp bicomi ) AABCDAABCAABEAFG
    AHACEAIGJK $.

  $( Using the recursion formula:

     "(n+1)-mintru-(m+1)" ` <-> if- ( ph , ` "n-mintru-m" ` , `
     "n-mintru-(m+1)" ` ) `

     for "1-mintru-2" (meaning "at least 2 out of a single input are true") by
     plugging in n = 0, m = 1, and simplifying.  The expressions "0-mintru-1"
     and "0-mintru-2" are base cases of the recursion, meaning "in a sequence
     of zero inputs at least 1 / 2 input is true", evaluate both to ` F. ` .

     Since no sequence of inputs has a longer subsequence of whatever property,
     the resulting ` F. ` is to be expected.

     Negating a "n-mintru2" operation has an interesting interpretation: at
     most one input is true, so all inputs exclude each other mutually.  Such
     an exclusion is expressed by a NAND operation ` ( ph -/\ ps ) ` , not by a
     XOR. Applying this idea here (n = 1) leads to the obvious "In a single
     input sequence 'at most one is true' always holds".  (Contributed by Wolf
     Lammen, 10-May-2024.) $)
  wl-1mintru2 $p |- ( if- ( ch , F. , F. ) <-> F. ) $=
    ( wfal ifpid ) ABC $.

  $( Using the recursion formula

     "(n+1)-mintru-(m+1)" ` <-> if- ( ph , ` "n-mintru-m" ` , `
     "n-mintru-(m+1)" ` ) `

     for "2-mintru-1" (meaning "at least 1 out of 2 inputs is true") by
     plugging in n = 1, m = 0, and simplifying.  The expression "1-mintru-0" is
     a base case (meaning at least zero inputs out of 1 are true), evaluating
     to ` T. ` , and ~ wl-1mintru1 shows "1-mintru-1" is equivalent to the only
     input.

     Negating an "n-mintru1" operation means:  All n inputs ` ph ` .. ` th `
     are false.  This is also conveniently expressed as ` -. ( ph \/ ` ..
     ` \/ th ) ` , in accordance with the result here.  (Contributed by Wolf
     Lammen, 10-May-2024.) $)
  wl-2mintru1 $p |- ( if- ( ps , T. , ch ) <-> ( ps \/ ch ) ) $=
    ( wtru wif wi wo wa dfifp3 trud bitru anbi1i truan 3bitri ) ACBDACEZABFZGCO
    GOACBHNCONAIJKOLM $.

  $( Using the recursion formula

     "(n+1)-mintru-(m+1)" ` <-> if- ( ph , ` "n-mintru-m" ` , `
     "n-mintru-(m+1)" ` ) `

     for "2-mintru-2" (meaning "2 out of 2 inputs are true") by plugging in n =
     1, m = 1, and simplifying.  See ~ wl-1mintru1 and ~ wl-1mintru2 to see
     that "1-mintru-1" / "1-mintru-2" evaluate to ` ch ` / ` F. ` respectively.

     Negating a "n-mintru2" operation means 'at most one input is true', so all
     inputs exclude each other mutually.  Such an exclusion is expressed by a
     NAND operation ` ( ph -/\ ps ) ` , not by a XOR. Applying this idea here
     (n = 2) yields the expected NAND in case of a pair of inputs.
     (Contributed by Wolf Lammen, 10-May-2024.) $)
  wl-2mintru2 $p |- ( if- ( ps , ch , F. ) <-> ( ps /\ ch ) ) $=
    ( wfal wif wi wa dfifp7 falim a1bi bitr4i ) ABCDCAEZABFZELABCGKLAHIJ $.

  $( Assuming "(n+1)-maxtru1" ` <-> -. ` "(n+1)-mintru-2", we can deduce from
     the recursion formula given in ~ wl-df-3mintru2 , that a similiar one

     "(n+1)-maxtru1" ` <-> if- ( ph , ` -.  "n-mintru-1" ` , ` "n-maxtru1"
     ` ) `

     is valid for expressing 'at most one input is true'.  This can also be
     rephrased as a mutual exclusivity of propositional expressions (no two of
     a sequence of inputs can simultaneously be true).  Of course, this
     suggests that all inputs depend on variables ` et ` , ` ze ` ...  Whatever
     wellformed expression we plugin for these variables, it will render at
     most one of the inputs true.

     The here introduced mutual exclusivity is possibly useful for case
     studies, where we want the cases be sort of 'disjoint'.  One can further
     imagine that a complete case scenario demands that the 'at most' is
     sharpened to 'exactly one'.  This does not impose any difficulty here, as
     one of the inputs will then be the negation of all others be or'ed.  As
     one input is determined, 'at most one' is sufficient to describe the
     general form here.

     Since ` cadd ` is an alias for 'at least 2 out of three are true', its
     negation is under focus here.  (Contributed by Wolf Lammen,
     23-Jun-2024.) $)
  wl-df3maxtru1 $p |- ( -. cadd ( ph , ps , ch ) <->
                        if- ( ph , ( ps -\/ ch ) , ( ps -/\ ch ) ) ) $=
    ( wcad wn wo wa wif wnor wnan cadnot wl-df-3mintru2 ifpn wb wtru a1i df-nor
    nanor ioran bitri ifpbi23d mptru bitr2i 3bitri ) ABCDEAEZBEZCEZDUEUFUGFZUFU
    GGZHZABCIZBCJZHZABCKUEUFUGLUMUEULUKHZUJAUKULMUNUJNOUEULUKUHUIULUHNOBCRPUKUI
    NOUKBCFEUIBCQBCSTPUAUBUCUD $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  An alternative axiom ~ ax-13
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x z $.  $d y z $.
    $( A version of ~ ax13v with a distinctor instead of a distinct variable
       condition.

       Had we additionally required ` x ` and ` y ` be distinct, too, this
       theorem would have been a direct consequence of ~ ax-5 .  So essentially
       this theorem states, that a distinct variable condition between set
       variables can be replaced with a distinctor expression.  (Contributed by
       Wolf Lammen, 23-Jul-2021.) $)
    ax-wl-13v $a |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $.
  $}

  ${
    $d x z w $.  $d y w $.
    $( A version of ~ ax-wl-13v with one distinct variable restriction dropped.
       For convenience, ` y ` is kept on the right side of equations.  This
       proof bases on ideas from NM, 24-Dec-2015.  (Contributed by Wolf Lammen,
       23-Jul-2021.) $)
    wl-ax13lem1 $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      ( vw weq wex wal equvinva ax-wl-13v equeucl alimdv syl9 impd exlimdv syl5
      wa wn ) CBEZCDEZBDEZPZDFABEAGQZRAGZCBDHUBUAUCDUBSTUCUBTTAGSUCABDISTRACBDJ
      KLMNO $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Bootstrapping set theory with classes
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x A $.  $d x B $.
    $( <HTML><br><b>Disclaimer:</b></HTML> The material presented here is just
       my (WL's) personal perception.  I am not an expert in this field, so
       some or all of the text here can be misleading, or outright wrong.  This
       and the following texts should be read as explorations rather than as
       definite statements, open to doubt, alternatives, and reinterpretation.

       <HTML><h3>Preface</h3></HTML>

       Three specific theorems are under focus in the following pages:
       ~ df-cleq , ~ df-clel , and ~ df-clab .  Only technical concepts
       necessary to explain these will be introduced, along with a selection of
       supporting theorems.  The three theorems are central to a bootstrapping
       process that introduces objects into set.mm.  We will first examine how
       Metamath in general creates basic new ideas from scratch, and then look
       at how these methods are applied specifically to classes, capable of
       representing objects in set theory.

       In Zermelo-Fraenkel set theory with the axiom of choice (ZFC), these
       three theorems are (more or less) independent of each other, which means
       they can be introduced in different orders.  From my own experience,
       another order has pedagogical advantages: it helps grasping not only the
       overall concept better, but also the intricate details that I first
       found difficult to comprehend.  Reordering theorems, though
       syntactically possible, sometimes may cause doubts when intermediate
       results are not strictly tied to ZFC only.

       The purpose of set.mm is to provide a formal framework capable of
       proving the results of ZFC, provided that formulas are properly
       interpreted.  In fact, there is freedom of interpretation.  The database
       set.mm develops from the very beginning, where nothing is assumed or
       fixed, and gradually builts up to the full abstraction of ZFC. Along the
       way, results are only preliminary, and one may at any point branch off
       and pursue a different path toward another variant of set theory.  This
       openess is already visible in axiom ~ ax-mp , where the symbol ` -> `
       can be understood as as implication, bi-conditional, or conjunction.
       The notation and symbol shapes are suggestive, but their interpretation
       is not mandatory.  The point here is that Metamath, as a purely
       syntactic system, can sometimes allow freedoms, unavailable to
       semantically fixed systems, which presuppose only a single ultimate
       goal.

       (Contributed by Wolf Lammen, 28-Sep-2025.) $)
    wl-cleq-0 $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $=
      ( dfcleq ) ABCD $.
  $}

  ${
    $d x A $.  $d x B $.
    $( <HTML><br><b>Disclaimer:</b></HTML> The material presented here is just
       my (WL's) personal perception.  I am not an expert in this field, so
       some or all of the text here can be misleading, or outright wrong.  This
       text should be read as an exploration rather than as definite
       statements, open to doubt, alternatives, and reinterpretation.

       <HTML><h3>Grammars and Parsable contents</h3></HTML>

       A Metamath program is a text-based tool.  Its input consists of
       primarily human-readable and editable text stored in *.mm files.  For
       automated processing, these files follow a strict structure.  This
       enables automated analysis of their contents, verification of proofs,
       proof assistance, and the generation of output files - for example, the
       HTML page of this dummy theorem.  A set.mm file contains numerous such
       structured instructions serving these purposes.

       This page provides a brief explanation of the general concepts behind
       structured text, as exemplified by set.mm.  The study of structured text
       originated in linguistics, and later computer science formalized it
       further for text like data and program code.  The rules describing such
       structures are collectively known as _grammar_.  Metamath also
       introduces a grammar to support automation and establish a high degree
       of confidence in its correctness.  It could have been described using
       the terminology of earlier scientific disciplines, but instead it uses
       its own language.

       When a text exhibits a sufficiently regular structure, its form can be
       described by a set of syntax rules, or grammar.  Such rules consist of
       terminal symbols (fixed, literal elements) and non-terminal symbols,
       which can recursively be expanded using the grammar's _rewrite_ rules.
       A program component that applies a grammar to text is called a _parser_.
       The parser decomposes the text into smaller parts, called _syntactic
       units_, while often maintaining contextual information.  These units may
       then be handed over to subsequent components for further processing,
       such as populating a database or generating output.

       In these pages, we restrict our attention to strictly formatted material
       consisting of formulas with logical and mathematical content.  These
       syntactic units are embedded in higher-level structures such as
       chapters, together with commands that, for example, control the HTML
       output.

       Conceptually, the parsing process can be viewed as consisting of two
       stages.  The top-level stage applies a simple built-in grammar to
       identify its structural units.  Each unit is a text region marked on
       both sides with predefined tokens (in Metamath: keywords), beginning
       with the escape character "$".  Text regions containing logical or
       mathematical formulas are then passed to a second-stage parser, which
       applies a different grammar.  Unlike the first, this grammar is not
       built-in but is dynamically constructed.

       In what follows, we will ignore the first stage of parsing, since its
       role is only to extract the relevant material embedded within text
       primarily intended for human readers.

       (Contributed by Wolf Lammen, 18-Aug-2025.) $)
    wl-cleq-1 $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $=
      ( dfcleq ) ABCD $.
  $}

  ${
    $d x A $.  $d x B $.
    $( <HTML><br><b>Disclaimer:</b></HTML> The material presented here is just
       my (WL's) personal perception.  I am not an expert in this field, so
       some or all of the text here can be misleading, or outright wrong.  This
       text should be read as an exploration rather than as definite
       statements, open to doubt, alternatives, and reinterpretation.

       <HTML><h3>Vocabulary</h3></HTML>

       <HTML><b>Sentence:<br></b></HTML>
       A _sentence_ or _closed form theorem_ is a theorem without any
       hypothesis, as opposed to the inference form.  Although distinct
       variable conditions can be viewed as a particular kind of hypothesis, in
       Metamath they are treated as side conditions, and do not affect formal
       structure of the theorem.  Expressions such as ` F/ x ph ` or the
       distinctor ` A. x ( x = y ) ` play a similar role, but appear as
       separate hypotheses, or they can simply serve as the first antecedent
       in a sentence.

       <HTML><b>Bound / Free / Dependent:<br></b></HTML>
       In formal theories, variables are used to represent
       objects,  allowing for general statements about relations rather than
       individual cases.  In Metamath, for example, mathematical objects are
       represented by variables of type "setvar".

       An occurrence of such a variable in any formula ` ph ` is said to be
       bound.  if ` ph ` quantifies that variable, as in ` A. x ph ` .
       Variables not bound by a quantifier are called free.  Variables of type
       "class" are always free, since quantifiers do not apply to them.

       A free variable often indicates a parameter dependency; however, the
       formula ` x = x ` shows that this is not necessarily the case.  In
       Metamath, a variable expressing a real dependency is also called
       "effectively free" (see ~ nfequid , with thanks to SN for pointing out
       this theorem).

       <HTML><b>Instance:<br></b></HTML>
       A formula of type "class" that is not a mere variable is called an
       _instance_ of any "class" type variable.  An instance may represent a
       single object, or it may still describe a family of objects, when
       variables expressing dependencies occur within that formula.

       <HTML><b>Attribute:<br></b></HTML>
       Objects possess properties, some of which may uniquely identify them.
       In logic, properties are also known as attributes.  They are described
       by formulas depending on a variable, which can then be substituted with
       a specific object.  If the resulting statement is true, that particular
       attribute is said to apply to the object.

       Multiple objects forming an instance may share common attributes.  A
       variable inherits the attributes of the instance it represents.

       (Contributed by Wolf Lammen, 12-Oct-2025.) $)
    wl-cleq-2 $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $=
      ( dfcleq ) ABCD $.
  $}

  ${
    $d x A $.  $d x B $.
    $( <HTML><br><b>Disclaimer:</b></HTML> The material presented here is just
       my (WL's) personal perception.  I am not an expert in this field, so
       some or all of the text here can be misleading, or outright wrong.  This
       text should be read as an exploration rather than as definite
       statements, open to doubt, alternatives, and reinterpretation.

       <HTML><h3>Introducing a New Concept:  Well-formed formulas</h3></HTML>

       The parser that processes strictly formatted Metamath text with logical
       or mathematical content constructs its grammar dynamically.  New syntax
       rules are added on the fly whenever they are needed to parse upcoming
       formulas.  Only a minimal set of built-in rules - those required to
       introduce new grammar rules - is predefined; everything else must be
       supplied by set.mm itself as syntactic units identified by the
       first-stage parser.  Text regions beginning with the tokens "$c" or
       "$v", for example, are part of such grammar extensions.

       We will outline the extension process used when introducing an entirely
       new concept that cannot build on any prior material.  As a simple
       example, we will trace here the steps involved in defining formulas, the
       expressions used for hypotheses and statements - a concept first-order
       logic needs from the very beginning to articulate its ideas.

       1. <HTML><b>Introduce a type code</b></HTML>

       To mark new formulas and variables later used in theorems, the constant
       "wff" is reserved.  It abbreviates "well-formed formula", a term that
       already suggests that such formulas must be syntactically valid and
       therefore parseable to enable automatic processing.

       2. <HTML><b>Introduce variables</b></HTML>

       Variables with unique names such as ` ph ` , ` ps ` , ..., intended to
       later represent formulas of type "wff".  In grammar terms, they
       correspond to non-terminal symbols.  These variables are marked with the
       type "wff".  Variables are fundamental in Metamath, since they enable
       substitution during proofs: variables of a particular type can be
       consistently replaced by any formula of the same type.  In grammar
       terms, this corresponds to applying a rewrite rule.  At this step,
       however, no rewrite rule exists; we can only substitute one "wff"
       variable for another.  This suffices only for very elementary theorems
       such as ~ idi .

       In the formal language of Metamath these variables are not interpreted
       with concrete statements, but serve purely as placeholders for
       substitution.

       3. <HTML><b>Add primitive formulas</b></HTML>

       Rewrite rules describing primitive formulas of type "wff" are then added
       to the grammar.  Typically, they describe an operator (a constant in the
       grammar) applied to one or more variables, possibly of different types
       (e.g. ` A. x ph ` , although at this stage only "wff" is available).
       Since variables are non-terminal symbols, more complex formulas can be
       constructed from primitive ones, by consistently replacing variables
       with any wff formula - whether involving the same operator or different
       ones introduced by other rewrite rules.  Whenever such a replacement
       introduces variables again, they may in turn recursively be replaced.

       If an operator takes two variables of type wff, it is called a binary
       connective in logic.  The first such operator encountered is
       ` ( ph -> ps ) ` .  Based on its token, its intended meaning is material
       implication, though this interpretation is not fixed from the outset.

       4. <HTML><b>Specify the properties of primitive formulas</b></HTML>

       Once the biconditional connective is available for formulas, new
       connectives can be defined by specifying replacement formulas that rely
       solely on previously introduced material.  Such definitions makes it
       possible to eliminate the definiens.

       At the very beginning, however, this is not possible for well-formed
       formulas, since little or no prior material exists.  Instead, the
       semantics of an expression such as ` ( ph -> ps ) ` are progressively
       constrained by axioms - that is, theorems without proof.  The first such
       axiom for material implication is ~ ax-mp , with additional axioms
       following later.

       (Contributed by Wolf Lammen, 21-Aug-2025.) $)
    wl-cleq-3 $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $=
      ( dfcleq ) ABCD $.
  $}

  ${
    $d x A $.  $d x B $.
    $( <HTML><br><b>Disclaimer:</b></HTML> The material presented here is just
       my (WL's) personal perception.  I am not an expert in this field, so
       some or all of the text here can be misleading, or outright wrong.  This
       text should be read as an exploration rather than as definite
       statements, open to doubt, alternatives, and reinterpretation.

       <HTML><h3>Introducing a New Concept:  Classes</h3></HTML>

       In ~ wl-cleq-3 we examined how the basic notion of a well-formed formula
       is introduced in set.mm.  A similar process is used to add the notion of
       a class to Metamath.  This process is somewhat more involved, since
       two parallel variants are established: sets and the broader notion of
       classes, which include sets (see 3a. below).

       In Zermelo-Fraenkel set theory (ZF) classes will serve as a convenient
       shorthand that simplifies formulas and proofs.  Ultimately, only sets
       - a part of all classes - are intended to exist as actual objects.

       In the First Order Logic (FOL) portion of set.mm objects themselves are
       not used - only variables representing them.  It is not even assumed
       that objects must be sets at all.  In principle, the universe of
       discourse could consist of anything - vegetables, text strings, and
       so on.  For this reason, the type code "setvar", used for object
       variables, is somewhat of a misnomer.  Its final meaning - and the name
       that goes with it - becomes justified only in later developments.

       We will now revisit the four basic steps presented in ~ wl-cleq-3 ,
       this time focusing on object variables and paying special attention to
       the additional complexities that arise from extending sets to classes.

       1. <HTML><b>Introduce type codes</b></HTML>

       1a.  Reserve a type code for classes, specifically the grammar constant
       "class".  Initially, this type code applies to class variables and will
       later, beyond these four steps, also be assigned to formulas that
       define specific classes, i.e. instances.

       1b.  Reserve a type code for set variables, represented by the grammar
       constant "setvar".  The name itself indicates that this type code will
       never be assigned to a formula describing a specific set, but only to
       variables containing such objects.

       2. <HTML><b>Introduce variables</b></HTML>

       2a.  Use variables with unique names such as ` A ` , ` B ` , ..., to
       represent classes.  These class variables are assigned the type code
       "class", ensuring that only formulas of type "class" can be substituted
       for them during proofs.

       2b.  Use variables with unique names such as ` a ` , ` b `  , ..., to
       represent sets.  These variables are assigned the type code "setvar".
       During a substitution in a proof, a variable of type "setvar" may only
       be replaced with another variable of this type.  No specific formula,
       or object, of this type exists.

       3. <HTML><b>Add primitive formulas</b></HTML>

       3a.  Add the rewrite rule ~ cv to set.mm, allowing variables of type
       "setvar" to also aquire type "class".  In this way, a variable of
       "setvar" type can serve as a substitute for a class variable.

       3b.  Add the rewrite rules ~ wcel and ~ wceq to set.mm, making the
       formulas ` A e. B ` and ` A = B ` valid well-formed formulas (wff).
       Since variables of type "setvar" can be substituted for class variables,
       ` x e. y ` and ` x = y ` are also provably valid wff.

       In the FOL part of set.mm, only these specific formulas play a role and
       are therefore treated as primitive there.  The underlying universe may
       not contain sets, and the notion of a class is not even be required.

       Additional mixed-type formulas, such as ` x e. A ` , ` A e. x ` ,
       ` x = A ` , and ` A = x ` exist.  When the theory is later refined
       to distinguish between sets and classes, the results from FOL remain
       valid and naturally extend to these mixed cases.  These cases will
       occasionally be examined individually in subsequent discussions.

       4. <HTML><b>Specify the properties of primitive formulas</b></HTML>

       In FOL in set.mm, the formulas ` x = y ` and ` x e. y ` cannot be
       derived from earlier material, and therefore cannot be defined.
       Instead, their fundamental properties are established through axioms,
       namely ~ ax-6 through ~ ax-9 , ~ ax-13 , and ~ ax-ext .

       Similarly, axioms establish the properties of the primitive formulas
       ` A = B ` and ` A e. B ` , ensuring that they extend the FOL
       counterparts ` x = y ` and ` x e. y ` in a consistent and meaningful
       way.

       At the same time, a criterion must be developed to distinguish sets
       from classes.  Since set variables can only be substituted by other set
       variables, equality must permit the assignment of class terms known to
       represent sets to those variables.

       (Contributed by Wolf Lammen, 25-Aug-2025.) $)
    wl-cleq-4 $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $=
      ( dfcleq ) ABCD $.
  $}

  ${
    $d x A $.  $d x B $.
    $( <HTML><br><b>Disclaimer:</b></HTML> The material presented here is just
       my (WL's) personal perception.  I am not an expert in this field, so
       some or all of the text here can be misleading, or outright wrong.  This
       text should be read as an exploration rather than as definite
       statements, open to doubt, alternatives, and reinterpretation.

       <HTML><h3>Semantics of Equality</h3></HTML>

       There is a broadly shared understanding of what equality between objects
       expresses, extending beyond mathematics or set theory.  Equality
       constitutes an equivalence relation among objects ` x ` , ` y ` , and
       ` z ` within the universe under consideration:

       1.  Reflexivity ` x = x `

       2.  Symmetry ` ( x = y -> y = x ) `

       3.  Transitivity ` (( x = y /\ x = z ) -> y = z ) `

       4.  Identity of Indiscernables (Leibniz's Law): distinct (i.e.,
       unequal), objects cannot share all the same properties (or attributes).

       In formal theories using variables, the attributes of a variable are
       assumed to mirror those of the instance it denotes.  For both variables
       and objects, items (1) - (4) must either be derived or postulated as
       axioms.

       If the theory allows substituting instances for variables, then the
       equality rules for objects follow directly from those governing
       variables.  However, if variables and instances are formally
       distinguished, this distinction introduces an additional metatheoretical
       attribute, relevant for (4).

       A similar issue arises when equality is considered between different
       types of variables sharing properties.  Such mixed-type equalities are
       subject to restrictions:  reflexivity does not apply, since the two
       sides represent different kinds of entities.  Nevertheless, symmetry and
       various forms of transitivity typically remain valid, and must be proven
       or established within the theory.

       In set.mm formulas express attributes.  Therefore, equal instances must
       behave identically, yielding the same results when substituted into any
       formula.  To verify equality, it suffices to consider only primitive
       operations involving free variables, since all formulas - once
       definitions are eliminated - reduce to these.  Equality itself
       introduces no new attribute (an object is always different from all
       others), and can thus be excluded from this examination.

       <HTML><h3>Equality in First Order Logic (FOL)</h3></HTML>

       In the FOL component of set.mm, the notion of an "object" is absent.
       Only set variables are used to formulate theorems, and their attributes
       - expressed through an unspecified membership operator - are
       addressed at a later stage.

       Instead, several axioms address equality directly: ~ ax-6 , ~ ax-7 ,
       ~ ax-8 , ~ ax-9 and ~ ax-12 , and ~ ax-13 .  In practice, restricted
       versions with distinct variable conditions are used ( ~ ax6v ,
       ~ ax12v ).  The unrestricted forms together with axiom ~ ax-13 , allow
       for the elimination of distinct variable conditions, this benefit is
       considered too minor for routine use.

       Equality in FOL is formalized as follows:

       2a.  Equivalence Relation.  Essentially covered by ~ ax-7 , with some
       support of ~ ax-6 .

       2b.  Leibniz's Law for the primitive ` e. ` operator.  Captured by
       ~ ax-8 and ~ ax-9 .

       2c.  General formulation.  Given in ~ sbequ12 .

       2d.  Implicit substitution.  Assuming Leibniz's Law holds for a
       particular expression, various theorems extend its validity to other,
       derived expressions, often introducing quantification (see for example
       ~ cbvalvw ).

       The auxiliary axioms ~ ax-10 , ~ ax-11 , ax-12  are provable (see
       ~ ax10w , for example) if you can substitute ` y ` for ` x ` in a
       formula ` ph ` that contains no occurrence of ` y ` and leaves no
       remaining trace of ` x ` after substitution.  An implicit substitution
       is then established by setting the resulting formula equivalent to
       ` ph ` under the assumption ` x = y ` .  Ordinary FOL substitution
       ` [ y / x ] ph ` is insufficient in this context, since ` x ` still
       occurs in the substituted formula.  A simple textual replacement of the
       token ` x ` by ` y ` in ` ph ` might seem an intuitive solution, but
       such operations are out of the formal scope of Metamath.

       2e.  Axiom of Extensionality.  In its elaborated form ( ~ axextb ), it
       states that the determining attributes of a set ` x ` are the elements
       ` z ` it contains, as expressed by ` z e. x ` .  This is the only
       primitive operation relevant for equality between set variables.

       <HTML><h3>Equality between classes</h3></HTML>

       In set.mm class variables of type "class" are introduced analoguously
       to set variables.  Besides the primitive operations equality and
       membership, class builders allow other syntactical constructs to
       substitute for class variables, enabling them to represent class
       instances.

       One such builder ( ~ cv ) allows set variables to replace class
       variables.  Another ( ~ df-clab ) introduces a class instance, known as
       class abstraction.  Since a class abstraction can freely substitute for
       a class variable, formulas hold for both alike.  Hence, there is no
       need to distinguish between class variables and abstractions; the term
       _class_ will denote "class variable or class abstraction".

       Set variables, however, are treated separately, as they are not of type
       "class".

       3a.  Equivalence Relation.  Axiom ~ df-cleq , from which class versions
       of (1a) - (1c) can be derived, guarantees that equality between class
       variables form an equivalence relation.  Since both class abstractions
       and set variables can substitute for class variables, this equivalence
       extends to all mixed equalities, including those with set variables,
       since they automatically convert to classes upon substitution.

       3b.  Attributes.  The primitive operation of membership constitutes the
       fundamental attributes of a class.  Axiom ~ df-clel reduces possible
       membership relations between class variables to those between a set
       variable and a class variable.  Axiom ~ df-cleq extends ~ axextb to
       classes, stating that classes are fully determined by their set members.

       A class builder may introduce a new attribute for classes.  An equation
       involving such a class instance may express this attribute.  In the case
       of the class builder ~ cv , an attribute called sethood is in fact
       introduced:  A class is a set if it can be equated with some set
       variable.

       Class abstractions supported by class builder ~ df-clab also formally
       introduce attributes.  Whether a class can be expressed as an
       abstraction with a specific predicate may be relevant in analysis.
       However, since theorem ~ df-clab is a definition (and hence eliminable),
       these attributes can also be expressed in other ways.

       3c.  Conservativity.  Because set variables can substitute for class
       variables, all axioms and definitions must be consistent with theorems
       in FOL.  To ensure this, hypotheses are added to axioms and definitions
       that mirror the structure of their statement, but with class variables
       replaced by set variables.  Since theorems cannot be applied without
       first proving their hypotheses, conservativity thus is enforced.

       3d.  Leibniz's Law.  Besides equality membership is (and remains) the
       only primitive operator between classes.  Axioms ~ df-cleq and
       ~ df-clel provide class versions of ~ ax-8 and ~ ax-9 , ensuring that
       membership is consistent with Leibniz's Law.

       Sethood, being based on mixed-type equality, preserves its value among
       equal classes.

       As long as additional class builders beyond those mentioned are only
       defined, the reasoning given for class abstraction above applies
       generally, and Leibniz's Law continues to hold.

       3e.  Backward Compatability.  A class ` A ` equal to a set should be
       substitutable for a free set variable ` x ` in any theorem, yielding a
       valid result, provided ` x ` and ` A ` are distinct.  Sethood is
       conveniently expressed by ` E. z z = A ` ; this assumption is added as
       an antecedent to the corresponding FOL theorem.

       However, since direct substitution is disallowed, a deduction version of
       an FOL theorem cannot be simply converted.  Instead, the proof must be
       replayed, consistently replacing ` x ` with ` A ` .  Ultimately, this
       process reduces to the FOL axioms, or their deduction form.

       If these axioms hold when ` A ` replaces ` x ` - under the above
       assumptions - then the replacement can be considered generally valid.
       The affected FOL axioms are ~ ax-6 (in the form ~ ax6ev ), ~ ax-7 ,
       ~ ax-8 , ~ ax-9 , ~ ax-12 ( ~ ax12v2 ), and to some extent ~ ax-13
       ( ~ ax13v ).  Since ZF (Zermelo-Fraenkel) set theory does not allow
       quantifification over class variables, no similar class-based versions
       of the quantified FOL axioms exist.

       (Contributed by Wolf Lammen, 18-Sep-2025.) $)
    wl-cleq-5 $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $=
      ( dfcleq ) ABCD $.
  $}

  ${
    $d x A $.  $d x B $.
    $( <HTML><br><b>Disclaimer:</b></HTML> The material presented here is just
       my (WL's) personal perception.  I am not an expert in this field, so
       some or all of the text here can be misleading, or outright wrong.  This
       text should be read as an exploration rather than as definite
       statements, open to doubt, alternatives, and reinterpretation.

       <HTML><h3>Eliminability of Classes</h3></HTML>

       One requirement of Zermelo-Fraenkel set theory (ZF) is that it can be
       formulated entirely without referring to classes.  Since set.mm
       implements ZF, it must therefore be possible to eliminate all classes
       from its formalization.

       <HTML><b>Eliminating Variables of Propositional Logic</b></HTML>

       Classical propositional logic concerns statements that are either true
       or false.  For example, "A minute has 60 seconds" is such a statement,
       as is "English is not a language".  Our development
       of propositional logic applies to all such statements,  regardless of
       their subject matter.  Any particular topic, or universe of discourse is
       encompassed by the general theorems of propositional logic.

       In ZF, however, the objects of study are sets - mathematical entities.
       The flexibility of propsitional variables is not required here.
       Instead, ZF introduces two primitive connectives between sets:
       ` x = y ` and ` x e. y ` .  ZF is concerned only with logical schemata
       constructed solely from these primitives.  Thus, before we can eliminate
       classes, we must first eliminate propositional variables like ` ph `
       and ` ps ` .  We will describe this process constructively.

       We begin by restricting ourselves to propositional schemata that consist
       only of the primitives of ZF, without any propositional variables.
       Extending this step to first-order Logic (FOL) - by introducing
       quantifiers - yields the fundamental predicates of ZF,  that is,
       the basic formulas expressible within it.

       For convenience, we may again allow propositional variables, but under
       the strict assumption that they always represent fundamental predicates
       of ZF.

       Predicates of level 0 are exactly of this kind: no classes occurs in
       them, and they can be reduced directly to fundamental predicates in ZF.

       <HTML><b>Introducing eliminable classes</b></HTML>

       The following construction is inspired by a paragraph in Azriel Levy's
       "Basic set theory" concerning eliminable classes.

       A class can only occur in combination with one of the operators ` = ` or
       ` e. ` .  This applies in particular to class abstractions, which are
       the only kind of classes permtted in this step of extending level-0
       predicates in ZF.  The definitions ~  df-cleq and ~ df-clel show that
       equality and membership ultimately reduce to expressions of the form
       ` x e. A ` .  For a class abstraction ` { y | ph } ` , the resulting
       term amounts to ` [ x / y ] ph ` .  If ` ph ` is a level-0 predicate,
       then this too is a level-0 expression - fully compatible with ZF.

       A level-1 class abstraction is a class ` { y | ph } ` where ` ph ` is a
       level-0 predicate.  A level-1 class abstraction can occur in an equality
       or membership relation with another level-1 class abstractions or a set
       variable, and such terms reduce to fundamental predicates.  Predicates
       of either level-0, or containing level-1 class abstractions are called
       level-1 predicates.  After eliminating all level-1 abstractions from
       such a predicate a level-0 expression is the result.

       Analoguously, we can define level-2 class abstractions, where the
       predicate ` ph ` in ` { y | ph } ` is a level-1 predicate.  Again,
       ` x e. { y | ph } ` reduces to a level-1 expression, which in turn can
       be reduced to a level-0 one.  By similar reasoning, equality and
       membership between at most level-2 class abstractions also reduce to
       level-0 expressions.  A predicate containing at most level-2 class
       abstractions is called a level-2 predicate.

       This iterative construction process can be continued to define a
       predicate of any level.  They can be reduced to fundamental predicates
       in ZF.

       <HTML><b>Introducing eliminable class variables</b></HTML>

       We have seen that propositional variables must be restricted to
       representing only primitive connectives to maintain compatibility with
       ZF.  Similarly, class variables can be restricted to representing class
       abstractions of finite level.  Such class variables are eliminable, and
       even definitions like ~ df-un ` ( A u. B ) ` introduce no difficulty,
       since the resulting union remains of finite level.

       <HTML><b>Limitations of eliminable class variables</b></HTML>

       Where does this construction reach its limits?

       1. Infinite constructions.  Suppose we wish to add up an infinite series
       of real numbers, where each term defines its successor using a class
       abstraction one level higher than that of the previous term.  Such a
       summation introduces terms of arbitrary high level.  While each
       individual term remains reducable in ZF, the infinite sum expression may
       not be reducable without special care.

       2. Class builders.  Every class builder other than ~ cv must be a
       definition, making its elimination straightforward.  The class
       abstraction ~ df-clab described above is a special case.

       Since set variables themselves can be expressed as class abstractions
       - namely ` x = { y | y e. x } ` (see ~ cvjust ) - this formulation does
       not conflict with the use of class builder ~ cv .

       The above conditions apply only to substitution.  The expression
       ` A = { x | x e. A } ` ( ~ abid1 ) is a valid and provable equation, and
       it should not be interpreted as an assignment that binds a particular
       instance to ` A ` .

       (Contributed by Wolf Lammen, 13-Oct-2025.) $)
    wl-cleq-6 $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $=
      ( dfcleq ) ABCD $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Disclaimer:  The material presented here is just my (WL's) personal
       perception.  I am not an expert in this field, so some or all of the
       text here can be misleading, or outright wrong.

       This text should be read as an exploration rather than as a definite
       statement, open to doubt, alternatives, and reinterpretation.

       At the point where ~ df-cleq is introduced, the foundations of set
       theory are being established through the notion of a class.  A central
       property of classes is what elements, expressed by the membership
       operator ` e. ` , belong to them .  Quantification ( ` A. x ` ) applies
       only to objects that a variable of kind setvar can represent.  These
       objects will henceforth be called sets.  Some classes may not be sets;
       these are called proper classes.  It remains open at this stage whether
       membership can involve them.

       The formula given in ~ df-cleq (restated below) asserts that two classes
       are equal if and only if they have exactly the same sets as elements.
       If proper classes are also admitted as elements, then two equal classes
       could still differ by such elements, potentially violating Leibniz's
       Law.  A future axiom ~ df-clel addresses this issue; ~ df-cleq alone
       does not.

       **Primitive connectives and class builders**

       Specially crafted primitive operators on classes or class builders could
       introduce properties of classes beyond membership, not reflected in the
       formula here.  This again risks violating Leibniz's Law.  Therefore, the
       introduction of any future primitive operator or class builder must
       include a conservativity check to ensure consistency with Leibniz's Law.

       **This axiom covers only some principles of equality**

       The notion of equality expressed in this axiom does not automatically
       coincide with the general notion of equality.  Some principles are,
       however, already captured:  Equality is shown to be an equivalence
       relation, covering transivity ( ~ eqtr ), reflexivity ( ~ eqid ) and
       symmetry ( ~ eqcom ).  It also yields the class-level version of
       ~ ax-ext (the backward direction of ~ df-cleq ) holds.

       If we assume ` x = A ` holds, then substituting the free set variable
       ` y ` with ` A ` in ~ ax6ev and ~ ax12v2 yields provable theorems (see
       ~ wl-isseteq , and ~ wl-ax12v2cl ).  However, a bound variable cannot be
       replaced with a class variable, since quantification over classes is not
       permitted.  Taken together with the results from the previous paragraph,
       this shows that a class variable equal to a set behaves the same as a
       set variable, provided it is not quantified.

       **Conservativity**

       Moreover, this axiom is already partly derivable if all class variables
       are replaced by variables of type "setvar".  In that case, the statement
       reduces to an instance of ~ axextb .  This shows that the class builder
       ~ cv is consistent with this axiom.

       **Eliminable operator**

       Finally, this axiom supports the idea that proper classes, and operators
       between them, should be eliminable, as required by ZF:  It reduces
       equality to their membership properties.  However, since the term
       ` x e. A ` is still undefined, elimination reduces equality to just
       something not yet clarified.

       **Axiom vs Definition**

       Up to this point, the only content involving class variables comes from
       the syntax definitions ~ wceq and ~ wcel .  Axioms are therefore
       required to progressively refine the semantics of classes until provable
       results coincide with our intended conception of set theory.  This
       refinement process is explained in Step 4 of ~ wl-cleq-2 .

       From this perspective, ~ df-cleq is in fact an axiom in disguise and
       would more appropriately be named ax-cleq.

       At first glance, one might think that ` A = B ` is defined by the
       right-hand side of the biconditional.  This would make ` x e. A ` , i.e.
       membership of a set in a class, the more primitive concept, from which
       equality of classes could be derived.  Such a viewpoint would be
       coherent if the properties of membership could be fully determined by
       other axioms.  In my (WL's') opinion, however, the more direct and
       fruitful approach is not to construct class equality from membership,
       but to treat equality itself as axiomatic.

       (Contributed by Wolf Lammen, 25-Aug-2025.) $)
    ax-wl-cleq $a |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Disclaimer:  The material presented here is just my (WL's) personal
       perception.  I am not an expert in this field, so some or all of the
       text here can be misleading, or outright wrong.

       This text should be read as an exploration rather than as a definite
       statement, open to doubt, alternatives, and reinterpretation.

       The formula in ~ df-clel (restated below) states that only those classes
       for which ` E. x x = A ` holds can be members of classes.  Thus, a
       member of a class is always equal to a set, which excludes proper
       classes from class membership.

       As explained in ~ wl-cleq-4 , item 3, ` E. x x = A ` is a sufficient
       criterion for a class to be a set, provided that Leibniz's Law holds for
       equality.  Therefore this axiom is often rephrased as: classes contain
       only sets as members.

       **Principles of equality**

       Using this axiom we can derive the class-level counterparts of ~ ax-8
       (see ~ eleq2 ) and ~ ax-9 (see ~ eleq1 ).  Since ~ ax-wl-cleq already
       asserts that equality between classes is an equivalence relation, the
       operators ` = ` and ` e. ` alone cannot distinguish equal classes.
       Hence, if membership is the only property that matters for classes,
       Leibniz's Law will hold.  Later, however, additional class builders may
       introduce further properties of classes.  A conservativity check for
       such builders can ensure this does not occur.

       **Eliminability**

       If we replace the class variable ` A ` with a set variable ` z ` in this
       axiom, the auxiliary variable ` x ` can be eliminated, leaving only the
       trivial result ` ( z e. B <-> z e. B ) ` .  Thus, ~ df-clel by itself
       does not determine when a set is a member of a class.  From this
       perspective, ~ df-clel is in fact an axiom in disguise and would more
       appropriately be called ax-clel.

       Overall, our axiomization leaves the meaning of fundamental expressions
       ` x e. A ` or ` x e. B ` open.  All other fundamental formulas of set
       theory ( ` A ` not a set variable, ` A e. B ` , ` x = B ` ` A = B ` )
       can be reduced solely to the basic formulas ` x e. A ` or ` x e. B ` .

       If an axiomatization leaves a fundamental formula like ` x e. A `
       unspecified, we could in principle define it bi-conditionally by any
       formula whatsoever - for example, the trivial ` T. ` .  This, however,
       is not the approach we take.  Instead, an appropriate class builder such
       as ~ df-clab fills this gap.

       (Contributed by Wolf Lammen, 26-Aug-2025.) $)
    ax-wl-clel $a |- ( A e. B <-> E. x ( x = A /\ x e. B ) ) $.
  $}

  $( Disclaimer:  The material presented here is just my (WL's) personal
     perception.  I am not an expert in this field, so some or all of the text
     here can be misleading, or outright wrong.

     This text should be seen as an exploration, rather than viewing it as set
     in stone, no doubt or alternatives possible.

     We now introduce the notion of class abstraction, which allows us to
     describe a specific class, in contrast to class variables that can stand
     for any class indiscriminately.

     A new syntactic form is introduced for class abstractions,
     ` { y | ph } ` , read as "the class of sets ` y ` such that
     ` ph ( y ) ` ".  This form is assigned the type "class" in ~ cab , so it
     can consistently substitute for a class variable during the syntactic
     construction process.

     **Eliminability**

     The axioms ~ ax-wl-cleq and ~ ax-wl-clel leave only ` x e. A `
     unspecified.  The definition of this class builder directly corresponds to
     that expression.  When a class abstraction replaces the variable ` A ` and
     ` B ` , then ` A = B ` and ` A e. B ` can be expressed in terms of these
     abstractions.

     For general eliminability two conditions are needed:

     1.  Any class builder must replace ` x e. A ` with an expression
     containing no class variables.  If necessary, class variables must be
     eliminated via a finite recursive process.

     2.  There must only be finitely many class builders.  If a class variable
     could range over infinitely many builders, eliminability would fail, since
     unknown future builders would always need to be considered.

     Condition (2) is met in set.mm by defining no class builder beyond ~ cv
     and ~ df-clab .  Thus we may assume that a class variable represents
     either a set variable, or a class abstraction:

     a.  If it represents a set variable, substitution eliminates it
     immediately.

     b.  If it equals a set variable ` x ` , then by ~ cvjust it can be
     replaced with ` { y | y e. x } ` .

     c.  If it represents a proper class, then it equals some abstraction
     ` { x | ph } ` .  If ` ph ` contains no class variables, elimination using
     ` ph ` is possible.  The same holds if finite sequence of elimination
     steps renders ` ph ` free of class variables.

     d.  It represents a proper class, but ` ph ` in ` { x | ph } ` still
     contains non-eliminable class variables, then eliminability fails.  A
     simple example is ` { x | x e. A } ` .  Class variables can only appear in
     fundamental expressions ` A = B ` or ` A e. B ` , Both can be reduced to
     forms involving ` z e. A ` .  Thus, in the expression
     ` z e. { x | x e. A } ` , we still must eliminate ` A ` .  Applying
     ~ df-clab reduces it back to ` z e. A ` , returning us to the starting
     point.

     Case (d) shows that in full generality, a class variable cannot always be
     eliminated, something Zermelo-Fraenkel set theory (ZF) requires.  If the
     universe contained only finitely many sets, a free class variable ` A `
     could be expressed as a finite disjunction of possiblities, hence
     eliminable.  But in ZF's richer universe, in a definition of an
     unrestricted class variable ` A = { x | ph } ` the variable ` ph ` will
     contain ` A ` in some way, violating condition (1) above.  Thus
     constraints are needed.  In ZF, any formula containing class variables
     assumes that non-set class variables can be be replaced by ` { x | ph } `
     where ` ph ` itself contains no class variables.  There is, however, no
     way to state this condition in a formal way in set.mm.

     Class abstractions themselves, however, can be eliminated, so df-clab is a
     definition.

     **Definition checker**

     How can case (d) be avoided?  A solution is to restrict generality:
     require that in the definition of any concrete class abstraction
     ` { x | ph } ` , the formula ` ph ` is either free of class variables or
     built only from previously defined constructions.  Such a restriction
     could be part of the definition checker.

     In practice, the Metamath definition checker requires definitions to
     follow the specific pattern " ` |- { x | ph } = ... ` ".  Although
     ~ df-clab does not conform to this pattern, it nevertheless permits
     elimination of class abstractions.  Eliminability is the essential
     property of a valid definition, so ~ df-clab can legitimately be regarded
     as one.

     For further material on the elimination of class abstractions, see BJ's
     work beginning with ~ eliminable1 and one comment in
     https://github.com/metamath/set.mm/pull/4971.

     (Contributed by Wolf Lammen, 28-Aug-2025.) $)
  wl-df-clab $p |- ( x e. { y | ph } <-> [ x / y ] ph ) $=
    ( df-clab ) ABCD $.

  ${
    $d A y $.  $d x y $.
    $( A class equal to a set variable implies it is a set.  Note that ` A `
       may be dependent on ` x ` .  The consequent, resembling ~ ax6ev , is the
       accepted expression for the idea of a class being a set.  Sometimes a
       simpler expression like the antecedent here, or in ~ elisset , is
       already sufficient to mark a class variable as a set.  (Contributed by
       Wolf Lammen, 7-Sep-2025.) $)
    wl-isseteq $p |- ( x = A -> E. y y = A ) $=
      ( cv wceq weq wex ax6ev eqeq2 biimpd eximdv mpi ) ADZCEZBAFZBGBDZCEZBGBAH
      NOQBNOQMCPIJKL $.
  $}

  ${
    $d z ph $.  $d x z A $.  $d y z A $.
    $( The class version of ~ ax12v2 , where the set variable ` y ` is replaced
       with the class variable ` A ` .  This is possible if ` A ` is known to
       be a set, expressed by the antecedent.

       Theorem ~ ax12v is a specialization of ~ ax12v2 .  So any proof using
       ~ ax12v will still hold if ~ ax12v2 is used instead.

       Theorem ~ ax12v2 expresses that two equal set variables cannot be
       distinguished by whatever complicated formula ` ph ` if one is replaced
       with the other in it.  This theorem states a similar result for a class
       variable known to be a set:  All sets equal to the class variable behave
       the same if they replace the class variable in ` ph ` .

       Most axioms in FOL containing an equation correspond to a theorem where
       a class variable known to be a set replaces a set variable in the
       formula.  Some exceptions cannot be avoided:  The set variable must
       nowhere be bound.  And it is not possible to state a distinct variable
       condition where a class ` A ` is different from another, or distinct
       from a variable with type wff.  So ~ ax-12 proper is out of reach: you
       cannot replace ` y ` in ` A. y ph ` with a class variable.

       But where such limitations are not violated, the proof of the FOL
       theorem should carry over to a version where a class variable, known to
       be set, appears instead of a set variable.  (Contributed by Wolf Lammen,
       8-Aug-2020.) $)
    wl-ax12v2cl $p |- ( E. y y = A ->
                   ( x = A -> ( ph -> A. x ( x = A -> ph ) ) ) ) $=
      ( vz cv wceq wex wal eqeq1 cbvexvw weq ax12v imbi1d albidv imbi2d imbi12d
      wi eqeq2 mpbii exlimiv sylbir ) CFZDGZCHEFZDGZEHBFZDGZAUHARZBIZRZRZUFUDEC
      UEUCDJKUFULEUFBELZAUMARZBIZRZRULABEMUFUMUHUPUKUEDUGSZUFUOUJAUFUNUIBUFUMUH
      AUQNOPQTUAUB $.
  $}

  $( Define class abstractions, that is, classes of the form ` { y | ph } ` ,
     which is read "the class of sets ` y ` such that ` ph ( y ) ` ".

     A few remarks are in order:

     1.  The axiomatic statement ~ df-clab does not define the class
     abstraction ` { y | ph } ` itself, that is, it does not have the form
     ` |- { y | ph } = ... ` that a standard definition should have (for a good
     reason: equality itself has not yet been defined or axiomatized for class
     abstractions; it is defined later in ~ df-cleq ).  Instead, ~ df-clab has
     the form ` |- ( x e. { y | ph } <-> ... ) ` , meaning that it only defines
     what it means for a setvar to be a member of a class abstraction.  As a
     consequence, one can say that ~ df-clab defines class abstractions if and
     only if a class abstraction is completely determined by which elements
     belong to it, which is the content of the axiom of extensionality
     ~ ax-ext .  Therefore, ~ df-clab can be considered a definition only in
     systems that can prove ~ ax-ext (and the necessary first-order logic).

     2.  As in all definitions, the definiendum (the left-hand side of the
     biconditional) has no disjoint variable conditions.  In particular, the
     setvar variables ` x ` and ` y ` need not be distinct, and the formula
     ` ph ` may depend on both ` x ` and ` y ` .  This is necessary, as with
     all definitions, since if there was for instance a disjoint variable
     condition on ` x , y ` , then one could not do anything with expressions
     like ` x e. { x | ph } ` which are sometimes useful to shorten proofs
     (because of ~ abid ).  Most often, however, ` x ` does not occur in
     ` { y | ph } ` and ` y ` is free in ` ph ` .

     3.  Remark 1 stresses that ~ df-clab does not have the standard form of a
     definition for a class, but one could be led to think it has the standard
     form of a definition for a formula.  However, it also fails that test
     since the membership predicate ` e. ` has already appeared earlier
     (outside of syntax e.g. in ~ ax-8 ).  Indeed, the definiendum extends, or
     "overloads", the membership predicate ` e. ` from formulas of the form
     "setvar ` e. ` setvar" to formulas of the form "setvar ` e. ` class
     abstraction".  This is possible because of ~ wcel and ~ cab , and it can
     be called an "extension" of the membership predicate because of ~ wel ,
     whose proof uses ~ cv .  An _a posteriori_ justification for ~ cv is given
     by ~ cvjust , stating that every setvar can be written as a class
     abstraction (though conversely not every class abstraction is a set, as
     illustrated by Russell's paradox ~ ru ).

     4.  Proof techniques.  Because class variables can be substituted with
     compound expressions and setvar variables cannot, it is often useful to
     convert a theorem containing a free setvar variable to a more general
     version with a class variable.  This is done with theorems such as
     ~ vtoclg which is used, for example, to convert ~ elirrv to ~ elirr .

     5.  Definition or axiom?  The question arises with the three axiomatic
     statements introducing classes, ~ df-clab , ~ df-cleq , and ~ df-clel , to
     decide if they qualify as definitions or if they should be called axioms.
     Under the strict definition of "definition" (see ~ conventions ), they are
     not definitions (see Remarks 1 and 3 above, and similarly for ~ df-cleq
     and ~ df-clel ).  One could be less strict and decide to call "definition"
     every axiomatic statement which provides an eliminable and conservative
     extension of the considered axiom system.  But the notion of
     conservativity may be given two different meanings in set.mm, due to the
     difference between the "scheme level" of set.mm and the "object level" of
     classical treatments.  For a proof that these three axiomatic statements
     yield an eliminable and weakly (that is, object-level) conservative
     extension of FOL= plus ~ ax-ext , see Appendix of [Levy] p. 357.

     6.  This definition (or axiom) is a _class builder_ introducing the class
     ` { x | ph } ` , also called a _class abstraction_ or _class
     comprehension_, i.e., it specifies a class by a condition determining its
     members.  Another class-building operator (but no class abstraction) is
     ~ cv , which asserts that every set is a class.  The converse need not
     hold: not every class is a set.  A class that is not a set is called a
     _proper class_.  From ~ ru , it follows that this abstraction yields
     proper classes, e.g. ` { x | x = x } ` .

     7.  References and history.  The concept of class abstraction dates back
     to at least Frege, and is used by Whitehead and Russell.  This definition
     is Definition 2.1 of [Quine] p. 16 and Axiom 4.3.1 of [Levy] p. 12.  It is
     called the "axiom of class comprehension" by [Levy] p. 358, who treats the
     theory of classes as an extralogical extension to predicate logic and set
     theory axioms.  He calls the construction ` { y | ph } ` a "class term".
     For a full description of how classes are introduced and how to recover
     the primitive language, see the books of Quine and Levy (and the comment
     of ~ eqabb for a quick overview).  For a general discussion of the theory
     of classes, see ~ mmset.html#class .  (Contributed by NM, 26-May-1993.)
     (Revised by BJ, 19-Aug-2023.) $)
  wl-df.clab $p |- ( x e. { y | ph } <-> [ x / y ] ph ) $=
    ( df-clab ) ABCD $.

  ${
    $d x y z t u v A $.  $d x y z t u v B $.
    wl-df.cleq.1 $e |- ( y = z <-> A. u ( u e. y <-> u e. z ) ) $.
    wl-df.cleq.2 $e |- ( t = t <-> A. v ( v e. t <-> v e. t ) ) $.
    $( Define the equality connective between classes.  Definition 2.7 of
       [Quine] p. 18.  Also Definition 4.5 of [TakeutiZaring] p. 13; Chapter 4
       provides its justification and methods for eliminating it.  Note that
       its elimination will not necessarily result in a single wff in the
       original language but possibly a "scheme" of wffs.

       The hypotheses express that all instances of the conclusion where class
       variables are replaced with setvar variables hold.  Therefore, this
       definition merely extends to class variables something that is true for
       setvar variables, hence is conservative.  This is only a proof sketch of
       conservativity; for details see Appendix of [Levy] p. 357.  This is the
       reason why we call this axiomatic statement a "definition", even though
       it does not have the usual form of a definition.  If we required a
       definition to have the usual form, we would call ~ df-cleq an axiom.

       See also comments under ~ df-clab , ~ df-clel , and ~ eqabb .

       In the form of ~ dfcleq , this is called the "axiom of extensionality"
       by [Levy] p. 338, who treats the theory of classes as an extralogical
       extension to our logic and set theory axioms.  It characterizes classes
       as collections of sets.

       While the three class definitions ~ df-clab , ~ df-cleq , and ~ df-clel
       are eliminable and conservative and thus meet the requirements for sound
       definitions, they are technically axioms in that they do not satisfy the
       requirements for the current definition checker.  The proofs of
       conservativity require external justification that is beyond the scope
       of the definition checker.

       For a general discussion of the theory of classes, see
       ~ mmset.html#class .  (Contributed by NM, 15-Sep-1993.)  (Revised by BJ,
       24-Jun-2019.) $)
    wl-df.cleq $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $=
      ( df-cleq ) ABCDEFGHIJK $.
  $}

  ${
    $d x y z t u v A $.  $d x y z t u v B $.
    $( This theorem is a conservative extension of ~ ax-ext to classes, with no
       hypotheses.  It is not complete, since ~ ax-8 can be derived (see
       ~ in-ax8 ) via alpha-renaming.

       Although unsuitable for general use, it is adequate for the development
       of theorems unaffected by alpha-renaming, including:

       1.  Theorems with no bound variables in the hypotheses or conclusion
       (see ~ eqriv ).

       2.  Theorems using the same bound variable throughout (see ~ abbib ).

       3.  Theorems with distinct bound variables arising only through implicit
       substitution (see ~ eqabbw ).

       Remark: the proof uses ~ axextb to prove the hypothesis of ~ df-cleq
       that is a degenerate instance, but it could be proved also from minimal
       propositional calculus and { ~ ax-gen , ~ equid }.  (Contributed by NM,
       15-Sep-1993.)  (Revised by BJ, 24-Jun-2019.) $)
    wl-dfcleq.basic $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $=
      ( vy vz vv vu vt axextb wl-df.cleq ) ADEFGHBCDEGIHHFIJ $.
    $( $j usage 'wl-dfcleq.basic' avoids 'ax-8' 'ax-10' 'ax-11' 'ax-12'
      'ax-13' 'df-clab' 'df-clel'; $)
  $}

  ${
    $d x y A $.  $d x y B $.
    wl-dfcleq.just.1 $e |- ( A. x ( x e. A <-> x e. B )
                                            <-> A. y ( y e. A <-> y e. B ) ) $.
    wl-dfcleq.just.id $e |- A = A $.
    wl-dfcleq.just.trans $e |- ( A = B -> ( B = C -> C = A ) ) $.
    wl-dfcleq.just.ax8 $e |- ( A = B -> ( A e. C -> B e. C ) ) $.
    wl-dfcleq.just.ax9 $e |- ( A = B -> ( C e. A -> C e. B ) ) $.
    $( The hypotheses added to this version of ~ df-cleq address the following:

       1.  Equality of classes is an equivalence relation, as expected of
       equality.

       2.  Equality of classes obeys the Law of Indiscernibles (Leibniz's Law),
       and is compatible with class membership.

       3.  Alpha-renaming is explicitly permitted.

       (Contributed by Wolf Lammen, 7-Apr-2026.) $)
    wl-dfcleq.just $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $=
      ( wl-dfcleq.basic ) ACDK $.
  $}

  ${
    $d x y z t u v A $.  $d x y z t u v B $.
    wl-df.clel.1 $e |- ( y e. z <-> E. u ( u = y /\ u e. z ) ) $.
    wl-df.clel.2 $e |- ( t e. t <-> E. v ( v = t /\ v e. t ) ) $.
    $( Define the membership connective between classes.  Theorem 6.3 of
       [Quine] p. 41, or Proposition 4.6 of [TakeutiZaring] p. 13, which we
       adopt as a definition.  See these references for its metalogical
       justification.

       The hypotheses assert that every instance of the conclusion obtained by
       substituting the class variables with set variables already holds.
       Thus, this definition extends to class variables a relation already
       valid for set variables, and is therefore conservative.  This only
       sketches the conservativity arguement; for details see Appendix of
       [Levy] p. 357.  For this reason we regard this statement as a
       "definition", even though it does not have the usual form of a
       definition.  Under a stricter syntactic criterion, ~ df-clel would
       instead be an axiom.

       See also comments under ~ df-clab , ~ df-cleq , and ~ eqabb .

       Alternate characterizations of ` A e. B ` when either ` A ` or ` B ` is
       a set are given by ~ clel2g , ~ clel3g , and ~ clel4g .

       [Levy] p. 338 refers to this as the "axiom of membership", treating the
       theory of classes as an extralogical extension to our logic and set
       theory axioms.

       Under this definition, class members can only be sets; classes are
       therefore collections of sets.  Although the extensionality expressed in
       ~ df-cleq already points in this direction, an unusual interpretation of
       equality could still permit proper classes as members.

       Although the class definitions ~ df-clab , ~ df-cleq , and ~ df-clel are
       eliminable and conservative, and hence meet the requirements for sound
       definitions, they are technically axioms in that they do not satisfy the
       syntactic requirements enforced by the current definition checker.  The
       conservativity proofs require external justification beyond the scope of
       the checker.

       For a general discussion of the theory of classes, see
       ~ mmset.html#class .  (Contributed by NM, 26-May-1993.)  (Revised by BJ,
       27-Jun-2019.) $)
    wl-df.clel $p |- ( A e. B <-> E. x ( x = A /\ x e. B ) ) $=
      ( df-clel ) ABCDEFGHIJK $.
  $}

  ${
    $d x y z t u v A $.  $d x y z t u v B $.
    $( This theorem gives a conservative extension of membership of classes,
       without hypotheses.  Conservativity alone, however, is insufficient,
       since issues involving alpha-renaming can still arise, see ~ in-ax8 .

       Although unsuitable for general use, it is adequate for the development
       of theorems unaffected by alpha-renaming, including:

       1.  Theorems whose hypotheses and conclusion contain no bound variables
       (see ~ eleq1w ).

       2.  Theorems using the same bound variable throughout (see ~ elex2 ).

       3.  Theorems in which distinct bound variables arise only through
       implicit substitution (see ~ eqabbw ).

       (Contributed by BJ, 27-Jun-2019.) $)
    wl-dfclel.basic $p |- ( A e. B <-> E. x ( x = A /\ x e. B ) ) $=
      ( vy vz vv vu vt cleljust wl-df.clel ) ADEFGHBCDEGIHHFIJ $.
    $( $j usage 'wl-dfclel.basic' avoids 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'
       'ax-ext' 'df-clab' 'df-cleq'; $)
  $}


  ${
    $d x y A $.  $d x y B $.
    wl-dfclel.just.1 $e |- ( E. x ( x = A /\ x e. B )
                                            <-> E. y ( y = A /\ y e. B ) ) $.
    $( Add a hypothesis to ~ wl-dfclel.basic , that permits alpha-renaming.
       (Contributed by Wolf Lammen, 7-Apr-2026.) $)
    wl-dfclel.just $p |- ( A e. B <-> E. x ( x = A /\ x e. B ) ) $=
      ( wl-dfclel.basic ) ACDF $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x C $.
    $( The defining characterization of class equality.  This version of
       ~ df-cleq has no restrictions, unlike the forms on which it is based.
       It is proved in Tarski's FOL from the axiom of extensionality
       ( ~ ax-ext ), the definition of class equality ( ~ df-cleq ), and the
       definition of class membership ( ~ df-clel ).

       Its forward implication is known as "class extensionality".
       (Contributed by NM, 15-Sep-1993.)  (Revised by BJ, 24-Jun-2019.)  Base
       on ~ wl-dfcleq.just .  (Revised by Wolf Lammen, 7-Apr-2026.) $)
    wl-dfcleq $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $=
      ( vy cC cv wcel wb weq eleq1w bibi12d wa wex biimpd eximdv dfclel 3imtr4g
      wceq wal wi cbvalvw eqid eqtr eqcomd ex eqeq2 wl-dfcleq.basic biimp alimi
      anim1d eqcoms imim12d spimvw syl sylbi anim2d wl-dfcleq.just ) ADBCEAFZBG
      ZURCGZHDFZBGZVACGZHZADADIZUSVBUTVCADBJZADCJKUABUBBCRZCERZEBRVGVHLBEBCEUCU
      DUEVGURBRZUREGZLZAMURCRZVJLZAMBEGCEGVGVKVMAVGVIVLVJVGVIVLBCURUFNUJOABEPAC
      EPQVGURERZUSLZAMVNUTLZAMEBGECGVGVOVPAVGUSUTVNVGVDDSZUSUTTZDBCUGVQVBVCTZDS
      VRVDVSDVBVCUHUIVSVRDADAIZUSVBVCUTUSVBTURVAVEUSVBVFNUKVTVCUTDACJNULUMUNUOU
      POAEBPAECPQUQ $.
  $}

  ${
    $d x y A B $.
    $( The defining characterization of class membership.  Unlike the forms on
       which it is based, it is unrestricted.  Proven in Tarski's FOL, from the
       axiom of (set) extensionality ( ~ ax-ext ), the definitions ~ df-clel
       and df-cleq .  (Contributed by BJ, 27-Jun-2019.)  Base on
       ~ wl-dfclel.just .  (Revised by Wolf Lammen, 13-Apr-2026.) $)
    wl-dfclel $p |- ( A e. B <-> E. x ( x = A /\ x e. B ) ) $=
      ( vy cv wceq wcel wa weq eqeq1 eleq1w anbi12d cbvexvw wl-dfclel.just ) AD
      BCAEZBFZOCGZHDEZBFZRCGZHADADIPSQTORBJADCKLMN $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Other stuff
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
  Most of the theorems in the section "Logical implication" are about
  handling chains of implications: ` ph -> ( ps -> ( ch -> ... ) ) `.  With
  respect to chains, a rich set of rules clarify

  - how to swap antecedents (com12, ...);

  - how to drop antecedents (ax-mp, pm2.43, ...);

  - how to add antecedents (a1i, ...)

  - how to replace an antecedent (syl, ...);

  - how to replace a consequent (ax-mp, syl, ...);

  - what is, when an antecedent equals the consequent (ax-1, id, ...).

  In all these cases, the operands of the chain have no inner structure, or
  it is of no importance.  These chains are called "simple" here.

  There is less support, when the operands are structured themselves.  Some
  kinds of inner structure involving the ` -. ` operator are best handled by
  the symmetric operators ` /\ ` and ` \/ `.  But a nested, simple chain
  has no such convenient replacement.  I can focus on antecedents here,
  since a consequent representing a chain is, in conjunction with its
  antecedents, just an extended simple chain again.

  The following theorems show, how operations on nested chains appear
  somehow mirrored: The minor premises of the syllogisms look reverted, in
  comparison to their normal counterparts, and while adding an antecedent to
  a chain via ~ a1i is easy, in nested chains they can be easily dropped.

$)

  ${
    wl-mps.1 $e |- ( ph -> ( ps -> ch ) ) $.
    wl-mps.2 $e |- ( ( ph -> ch ) -> th ) $.
    $( Replacing a nested consequent.  A sort of _modus ponens_ in antecedent
       position.  (Contributed by Wolf Lammen, 20-Sep-2013.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    wl-mps $p |- ( ( ph -> ps ) -> th ) $=
      ( wi a2i syl ) ABGACGDABCEHFI $.
  $}

  ${
    wl-syls1.1 $e |- ( ps -> ch ) $.
    wl-syls1.2 $e |- ( ( ph -> ch ) -> th ) $.
    $( Replacing a nested consequent.  A sort of syllogism in antecedent
       position.  (Contributed by Wolf Lammen, 20-Sep-2013.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    wl-syls1 $p |- ( ( ph -> ps ) -> th ) $=
      ( wi a1i wl-mps ) ABCDBCGAEHFI $.
  $}

  ${
    wl-syls2.1 $e |- ( ph -> ps ) $.
    wl-syls2.2 $e |- ( ( ph -> ch ) -> th ) $.
    $( Replacing a nested antecedent.  A sort of syllogism in antecedent
       position.  (Contributed by Wolf Lammen, 20-Sep-2013.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    wl-syls2 $p |- ( ( ps -> ch ) -> th ) $=
      ( wi imim1i syl ) BCGACGDABCEHFI $.
  $}

  ${
    wl-embant.1 $e |- ph $.
    wl-embant.2 $e |- ( ps -> ch ) $.
    $( A true wff can always be added as a nested antecedent to an antecedent.
       Note: this theorem is intuitionistically valid.  (Contributed by Wolf
       Lammen, 4-Oct-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    wl-embant $p |- ( ( ph -> ps ) -> ch ) $=
      ( wi imim2i mpi ) ABFACDBCAEGH $.
  $}

  $( In a conjunctive normal form a pair of nodes like
     ` ( ph \/ ps ) /\ ( -. ph \/ ch ) ` eliminates the need of a node
     ` ( ps \/ ch ) ` .  This theorem allows simplifications in that respect.
     (Contributed by Wolf Lammen, 20-Jun-2020.) $)
  wl-orel12 $p |- ( ( ( ph \/ ps ) /\ ( -. ph \/ ch ) ) -> ( ps \/ ch ) ) $=
    ( wo wn wa pm2.1 orel1 orc syl6com wi notnot syl olc jaao mpi ) ABDZAEZCDZF
    RADBCDZAGQRTSARQBTABHBCIJASCTARESCKALRCHMCBNJOP $.

  $( A particular instance of ~ orddi and ~ anddi converting between
     disjunctive and conjunctive normal forms, when both ` ph ` and ` -. ph `
     appear.  This theorem in fact rephrases ~ cases2 , and is related to
     ~ consensus .  I restate it here in DNF and CNF. The proof deliberately
     does not use ~ df-ifp and ~ dfifp4 , by which it can be shortened.
     (Contributed by Wolf Lammen, 21-Jun-2020.)
     (Proof modification is discouraged.) $)
  wl-cases2-dnf $p |- ( ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) <->
              ( ( -. ph \/ ps ) /\ ( ph \/ ch ) ) ) $=
    ( wa wn exmid biantrur orcom anbi12i anass orddi 3bitr4ri wl-orel12 pm4.71i
    wo ancom 3bitr2i ) ABDAEZCDOZACOZRBOZDZCBOZDZUBUATDTUAUCDZDAROZTDZBROZBCOZD
    ZDUDSTUGUEUJUFTAFGUAUHUCUIRBHCBHIITUAUCJABRCKLUBUCACBMNTUAPQ $.

  ${
    $d x y z $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.  Part of
       Lemma 7 of [KalishMontague] p. 86.  (Contributed by Wolf Lammen,
       5-Mar-2023.) $)
    wl-cbvmotv $p |- ( E* x T. -> E* y T. ) $=
      ( vz wtru weq wi wal wex wmo ax7v2 imim2d cbvalivw eximi dfmo 3imtr4i ) D
      ACEZFZAGZCHDBCEZFZBGZCHDAIDBIRUACQTABABEPSDABCJKLMDACNDBCNO $.
  $}

  ${
    $d x w $.  $d y w $.  $d z w $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.  Part of
       Lemma 7 of [KalishMontague] p. 86.  (Contributed by Wolf Lammen,
       5-Mar-2023.) $)
    wl-moteq $p |- ( E* x T. -> y = z ) $=
      ( vw wtru wmo weq wi wal wex dfmo stdpc5v tru pm2.24i aeveq exlimiv sylbi
      ja syl ) EAFEADGZHAIZDJBCGZEADKUAUBDUAETAIZHUBETALEUCUBEUBMNADBCORSPQ $.
  $}

  ${
    $d u v $.  $d v x $.  $d v y $.  $d v z $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.  Part of
       Lemma 7 of [KalishMontague] p. 86.  (Contributed by Wolf Lammen,
       5-Mar-2023.) $)
    wl-motae $p |- ( E* u T. -> A. x y = z ) $=
      ( vv wtru wmo weq wal wl-cbvmotv wl-moteq alrimiv syl ) FDGFEGZBCHZAIDEJN
      OAEBCKLM $.
  $}

  ${
    $d x y $.
    $( Two ways to express "at most one thing exists" or, in this context
       equivalently, "exactly one thing exists" .  The equivalence results from
       the presence of ~ ax-6 in the proof, that ensures "at least one thing
       exists".  For other equivalences see ~ wl-euae and ~ exists1 .  Gerard
       Lang pointed out, that ` E. y A. x x = y ` with disjoint ` x ` and ` y `
       ( ~ dfmo , ~ trut ) also means "exactly one thing exists" .
       (Contributed by NM, 5-Apr-2004.)  State the theorem using truth constant
       ` T. ` .  (Revised by BJ, 7-Oct-2022.)  Reduce axiom dependencies, and
       use ` E* ` .  (Revised by Wolf Lammen, 7-Mar-2023.) $)
    wl-moae $p |- ( E* x T. <-> A. x x = y ) $=
      ( wtru wmo weq wal wl-motae wi wex hbaev 19.8w ax-1 alimi syl dfmo sylibr
      eximi impbii ) CADZABEZAFZAABAGUACTHZAFZBIZSUAUABIUDUABABBJKUAUCBTUBATCLM
      QNCABOPR $.
  $}

  ${
    $d x y $.
    $( Two ways to express "exactly one thing exists" .  (Contributed by Wolf
       Lammen, 5-Mar-2023.) $)
    wl-euae $p |- ( E! x T. <-> A. x x = y ) $=
      ( wtru weu wex wmo wa weq wal df-eu extru biantrur wl-moae 3bitr2i ) CADC
      AEZCAFZGPABHAICAJOPAKLABMN $.
  $}

  ${
    $d x y $.
    wl-nax6im.1 $e |- ( -. E. x x = y -> ph ) $.
    $( The following series of theorems are centered around the empty domain,
       where no set exists.  As a consequence, a set variable like ` x ` has no
       instance to assign to.  An expression like ` x = y ` is not really
       meaningful then.  What does it evaluate to, true or false?  In fact, the
       grammar extension ~ weq requires us to formally assign a boolean value
       to an equation, say always false, unless you want to give up on
       ~ exmid , for example.  Whatever it is, we start out with the
       contraposition of ~ ax-6 , that guarantees the existence of at least one
       set.  Our hypothesis here expresses tentatively it might not hold.  We
       can simplify the antecedent then, to the point where we do not need
       equation any more.  This suggests what a decent characterization of the
       empty domain of discourse could be.  (Contributed by Wolf Lammen,
       12-Mar-2023.) $)
    wl-nax6im $p |- ( -. E. x T. -> ph ) $=
      ( weq wex wtru trud eximi nsyl5 ) BCEZBFGBFAKGBKHIDJ $.
  $}

  $( This specialization of ~ hbae does not depend on ~ ax-11 .  (Contributed
     by Wolf Lammen, 8-Aug-2021.) $)
  wl-hbae1 $p |- ( A. x x = y -> A. y A. x x = y ) $=
    ( weq wal axc11n axc4i syl ) ABCADZBACZBDHBDABEIHBBAEFG $.

  ${
    $d x y z $.
    $( An instance of ~ hbn1w applied to equality.  (Contributed by Wolf
       Lammen, 7-Apr-2021.) $)
    wl-naevhba1v $p |- ( -. A. x x = y -> A. x -. A. x x = y ) $=
      ( vz weq equequ1 hbn1w ) ABDCBDACACBEF $.
  $}

  ${
    $d x z $.  $d y z $.
    $( Prove an instance of ~ sp from ~ ax-13 and Tarski's FOL only, without
       distinct variable conditions.  The antecedent ` A. x x = y ` holds in a
       multi-object universe only if ` y ` is substituted for ` x ` , or vice
       versa, i.e. both variables are effectively the same.  The converse
       ` -. A. x x = y ` indicates that both variables are distinct, and it so
       provides a simple translation of a distinct variable condition to a
       logical term.  In case studies ` A. x x = y ` and ` -. A. x x = y ` can
       help eliminating distinct variable conditions.

       The antecedent ` A. x x = y ` is expressed in the theorem's name by the
       abbreviation ae standing for 'all equal'.

       Note that we cannot provide a logical predicate telling us directly
       whether a logical expression contains a particular variable, as such a
       construct would usually contradict ~ ax-12 .

       Note that this theorem is also provable from ~ ax-12 alone, so you can
       pick the axiom it is based on.

       Compare this result to ~ 19.3v and ~ spaev having distinct variable
       conditions, but a smaller footprint on axiom usage.  (Contributed by
       Wolf Lammen, 5-Apr-2021.) $)
    wl-spae $p |- ( A. x x = y -> x = y ) $=
      ( vz weq wal wi wa aeveq adantl a1d ax13v equtrr al2imi con3d syl6 impcom
      wn com13 con4d pm2.61dan ax6evr exlimiiv ) BCDZABDZAEZUDFZCUCACDZAEZUFUCU
      HGUDUEUHUDUCACABHIJUCUHQZGUDUEUIUCUDQZUEQZFUJUCUIUKUJUCUCAEZUIUKFABCKULUE
      UHUCUDUGABCALMNORPSTCBUAUB $.
  $}

  ${
    $d x z $.
    $( Under the assumption ` -. x = y ` a specialized version of ~ sp is
       provable from Tarski's FOL and ~ ax13v only.  Note that this reverts the
       implication in ~ ax13lem1 , so in fact
       ` ( -. x = y -> ( A. x z = y <-> z = y ) ) ` holds.  (Contributed by
       Wolf Lammen, 17-Apr-2021.) $)
    wl-speqv $p |- ( -. x = y -> ( A. x z = y -> z = y ) ) $=
      ( weq wal wex wn 19.2 ax13lem2 syl5 ) CBDZAEKAFABDGKKAHABCIJ $.

    $( Under the assumption ` -. x = y ` a specialized version of ~ 19.8a is
       provable from Tarski's FOL and ~ ax13v only.  Note that this reverts the
       implication in ~ ax13lem2 , so in fact
       ` ( -. x = y -> ( E. x z = y <-> z = y ) ) ` holds.  (Contributed by
       Wolf Lammen, 17-Apr-2021.) $)
    wl-19.8eqv $p |- ( -. x = y -> ( z = y -> E. x z = y ) ) $=
      ( weq wn wal wex ax13lem1 19.2 syl6 ) ABDECBDZKAFKAGABCHKAIJ $.

    $( Under the assumption ` -. x = y ` the reverse direction of ~ 19.2 is
       provable from Tarski's FOL and ~ ax13v only.  Note that in conjunction
       with ~ 19.2 in fact ` ( -. x = y -> ( A. x z = y <-> E. x z = y ) ) `
       holds.  (Contributed by Wolf Lammen, 17-Apr-2021.) $)
    wl-19.2reqv $p |- ( -. x = y -> ( E. x z = y -> A. x z = y ) ) $=
      ( weq wn wex wal ax13lem2 ax13lem1 syld ) ABDECBDZAFKKAGABCHABCIJ $.
  $}

  ${
    $d x ph $.
    $( If ` x ` is not present in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by Wolf Lammen, 11-Jan-2020.) $)
    wl-nfalv $p |- F/ x A. y ph $=
      ( wal ax-5 hbal nf5i ) ACDBABCABEFG $.
  $}

  $( An antecedent is irrelevant to a not-free property, if it always holds.  I
     used this variant of ~ nfim in ~ dvelimdf to simplify the proof.
     (Contributed by Wolf Lammen, 14-Oct-2018.) $)
  wl-nfimf1 $p |- ( A. x ph -> ( F/ x ( ph -> ps ) <-> F/ x ps ) ) $=
    ( wal wi nfa1 wb pm5.5 sps nfbidf ) ACDABEZBCACFAKBGCABHIJ $.

  $( Unlike ~ nfae , this specialized theorem avoids ~ ax-11 .  (Contributed by
     Wolf Lammen, 26-Jun-2019.) $)
  wl-nfae1 $p |- F/ x A. y y = x $=
    ( weq wal aecom nfa1 nfxfr ) BACBDABCZADABAEHAFG $.

  $( Unlike ~ nfnae , this specialized theorem avoids ~ ax-11 .  (Contributed
     by Wolf Lammen, 27-Jun-2019.) $)
  wl-nfnae1 $p |- F/ x -. A. y y = x $=
    ( weq wal wl-nfae1 nfn ) BACBDAABEF $.

  $( A transitive law for variable identifying expressions.  (Contributed by
     Wolf Lammen, 30-Jun-2019.) $)
  wl-aetr $p |- ( A. x x = y -> ( A. x x = z -> A. y y = z ) ) $=
    ( weq wal ax7 al2imi axc11 syld ) ABDZAEACDZAEBCDZAELBEJKLAABCFGLABHI $.

  $( Same as ~ axc11r , but using ~ ax12 instead of ~ ax-12 directly.  This
     better reflects axiom usage in theorems dependent on it.  (Contributed by
     NM, 25-Jul-2015.)  Avoid direct use of ~ ax-12 .  (Revised by Wolf Lammen,
     30-Mar-2024.) $)
  wl-axc11r $p |- ( A. y y = x -> ( A. x ph -> A. y ph ) ) $=
    ( weq wal wi ax12 sps pm2.27 al2imi syld ) CBDZCEABEZLAFZCEZACELMOFCACBGHLN
    ACLAIJK $.

  ${
    wl-dral1d.1 $e |- F/ x ph $.
    wl-dral1d.2 $e |- F/ y ph $.
    wl-dral1d.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( A version of ~ dral1 with a context.  Note:  At first glance one might
       be tempted to generalize this (or a similar) theorem by weakening the
       first two hypotheses adding a ` x = y ` , ` A. x x = y ` or ` ph `
       antecedent. ~ wl-equsal1i and ~ nf5di show that this is in fact
       pointless.  (Contributed by Wolf Lammen, 28-Jul-2019.) $)
    wl-dral1d $p |- ( ph -> ( A. x x = y -> ( A. x ps <-> A. y ch ) ) ) $=
      ( weq wal wb wi com12 pm5.74d sps dral1 19.21 3bitr3g pm5.74rd ) DEIZDJZA
      BDJZCEJZKUAAUBUCUAABLZDJACLZEJAUBLAUCLUDUEDETUDUEKDTABCATBCKHMNOPABDFQACE
      GQRSM $.
  $}

  ${
    wl-cbvalnaed.1 $e |- F/ x ph $.
    wl-cbvalnaed.2 $e |- F/ y ph $.
    wl-cbvalnaed.3 $e |- ( ph -> ( -. A. x x = y -> F/ y ps ) ) $.
    wl-cbvalnaed.4 $e |- ( ph -> ( -. A. x x = y -> F/ x ch ) ) $.
    wl-cbvalnaed.5 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( ~ wl-cbvalnae with a context.  (Contributed by Wolf Lammen,
       28-Jul-2019.) $)
    wl-cbvalnaed $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( weq wal wb wl-dral1d imp wn wa nfnae nfan wnf wl-nfnae1 wi adantr cbv2
      pm2.61dan ) ADEKZDLZBDLCELMZAUGUHABCDEFGJNOAUGPZQBCDEAUIDFDEDRSAUIEGEDUAS
      AUIBETHOAUICDTIOAUFBCMUBUIJUCUDUE $.
  $}

  ${
    wl-cbvalnae.1 $e |- ( -. A. x x = y -> F/ y ph ) $.
    wl-cbvalnae.2 $e |- ( -. A. x x = y -> F/ x ps ) $.
    wl-cbvalnae.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A more general version of ~ cbval when nonfree properties depend on a
       distinctor.  Such expressions arise in proofs aiming at the elimination
       of distinct variable constraints, specifically in application of
       ~ dvelimf , ~ nfsb2 or ~ dveeq1 .  (Contributed by Wolf Lammen,
       4-Jun-2019.) $)
    wl-cbvalnae $p |- ( A. x ph <-> A. y ps ) $=
      ( wal wb wtru nftru weq wn wnf wi a1i wl-cbvalnaed mptru ) ACHBDHIJABCDCK
      DKCDLZCHMZADNOJEPTBCNOJFPSABIOJGPQR $.
  $}

  $( The semantics of ` E. x y = z ` .  (Contributed by Wolf Lammen,
     27-Apr-2018.) $)
  wl-exeq $p |- ( E. x y = z <-> ( y = z \/ A. x x = y \/ A. x x = z ) ) $=
    ( weq wex wal w3o wo wn nfeqf 19.9d impancom orrd expcom sylibr ax6e eximii
    wa wi 19.35i 3orass 3orrot 19.8a ax7 com12 3jaoi impbii ) BCDZAEZUHABDZAFZA
    CDZAFZGZUIUKUMUHGZUNUIUKUMUHHZHUOUIUKUPUKIZUIUPUQUIRUMUHUQUMIZUIUHUHUQURRAB
    CAJKLMNMUKUMUHUAOUHUKUMUBOUHUIUKUMUHAUCUJUHAULUJUHSAACPUJULUHABCUDZUEQTULUH
    AUJULUHSAABPUSQTUFUG $.

  $( The semantics of ` A. x y = z ` .  (Contributed by Wolf Lammen,
     27-Apr-2018.) $)
  wl-aleq $p |- ( A. x y = z <-> ( y = z /\ ( A. x x = y <-> A. x x = z ) ) )
    $=
    ( weq wal wb wa equequ2 alimi albi syl jca ax7 al2imi a1dd axc9 bija impcom
    sp wi impbii ) BCDZAEZUBABDZAEZACDZAEZFZGUCUBUHUBASUCUDUFFZAEUHUBUIABCAHIUD
    UFAJKLUHUBUCUEUGUBUCTUEUGUCUBUDUFUBAABCMNOBCAPQRUA $.

  $( Extend ~ nfeqf to an equivalence.  (Contributed by Wolf Lammen,
     31-Jul-2019.) $)
  wl-nfeqfb $p |- ( F/ x y = z <-> ( A. x x = y <-> A. x x = z ) ) $=
    ( weq wnf wal wb wa nf5r imp wl-aleq simprbi syl wn w3a nf5rd w3o wex alnex
    nfnt wl-exeq xchbinx 3ioran sylbb 3simpc pm5.21 4syl pm2.61dan al2imi nftht
    ax7 syl6 nfeqf ex bija impbii ) BCDZAEZABDZAFZACDZAFZGZURUQVCURUQHUQAFZVCUR
    UQVDUQAIJVDUQVCABCKLMURUQNZHVEAFZVEUTNZVBNZOZVGVHHVCURVEVFURVEAUQATPJVFUQUT
    VBQZNVIVFUQARVJUQASABCUAUBUQUTVBUCUDVEVGVHUEUTVBUFUGUHUTVBURUTVBVDURUSVAUQA
    ABCUKUIUQAUJULVGVHURBCAUMUNUOUP $.

  $( If ` y ` is not free in ` ph ` , ` x ` is not free in ` [ y / x ] ph ` .
     Closed form of ~ nfs1 .  (Contributed by Wolf Lammen, 27-Jul-2019.) $)
  wl-nfs1t $p |- ( F/ y ph -> F/ x [ y / x ] ph ) $=
    ( weq wal wnf wsb wi wb sbequ12r equcoms sps drnf1 biimprd wn nfsb2 pm2.61i
    a1d ) BCDZBEZACFZABCGZBFZHTUCUAUBABCSUBAIZBUDCBACBJKLMNTOUCUAABCPRQ $.

  ${
    $d x y $.  $d x ps $.
    wl-equsalvw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Version of ~ equsalv with a disjoint variable condition, and of ~ equsal
       with two disjoint variable conditions, which requires fewer axioms.  See
       also the dual form ~ equsexvw .

       This theorem lays the foundation to a transformation of expressions
       called substitution of set variables in a wff.  Only in this particular
       context we additionally assume ` ph ` and ` y ` disjoint, stated here as
       ` ph ( x ) ` .  Similarly the disjointness of ` ps ` and ` x ` is
       expressed by ` ps ( y ) ` .  Both ` ph ` and ` ps ` may still depend on
       other set variables, but that is irrelevant here.

       We want to transform ` ph ( x ) ` into ` ps ( y ) ` such that ` ps `
       depends on ` y ` the same way as ` ph ` depends on ` x ` .  This
       dependency is expressed in our hypothesis (called implicit
       substitution): ` ( x = y -> ( ph <-> ps ) ) ` .  For primitive enough
       ` ph ` a sort of textual substitution of ` x ` by ` y ` is sufficient
       for such transformation.  But note: ` ph ` must not contain wff
       variables, and the substitution is no proper textual substitution
       either.  We still need grammar information to not accidently replace the
       x in a token 'x.' denoting multiplication, but only catch set variables
       ` x ` .  Our current stage of development allows only equations and
       quantifiers make up such primitives.  Thanks to ~ equequ1 and ~ cbvalvw
       we can then prove in a mechanical way that in fact the implicit
       substitution holds for each instance.

       If ` ph ` contains wff variables we cannot use textual transformation
       any longer, since we don't know how to replace ` y ` for ` x ` in
       placeholders of unknown structure.  Our theorem now states, that the
       generic expression ` A. x ( x = y -> ph ) ` formally behaves as if such
       a substitution was possible and made.

       (Contributed by BJ, 31-May-2019.) $)
    wl-equsalvw $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( weq wi wal wex 19.23v pm5.74i albii ax6ev a1bi 3bitr4i ) CDFZBGZCHPCIZB
      GPAGZCHBPBCJSQCPABEKLRBCDMNO $.
    $( $j usage 'equsalvw' avoids 'ax-7' 'ax-12' 'ax-13'; $)
  $}

  ${
    wl-equsald.1 $e |- F/ x ph $.
    wl-equsald.2 $e |- ( ph -> F/ x ch ) $.
    wl-equsald.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Deduction version of ~ equsal .  (Contributed by Wolf Lammen,
       27-Jul-2019.) $)
    wl-equsald $p |- ( ph -> ( A. x ( x = y -> ps ) <-> ch ) ) $=
      ( weq wi wal wex wnf wb 19.23t syl pm5.74d albid ax6e a1bi a1i 3bitr4d )
      ADEIZCJZDKZUCDLZCJZUCBJZDKCACDMUEUGNGUCCDOPAUHUDDFAUCBCHQRCUGNAUFCDESTUAU
      B $.

    $d x y $.
    $( Deduction version of ~ equsal .  (Contributed by Wolf Lammen,
       27-Jul-2019.) $)
    wl-equsaldv $p |- ( ph -> ( A. x ( x = y -> ps ) <-> ch ) ) $=
      ( weq wi wal wex wnf wb 19.23t syl pm5.74d albid ax6ev a1bi a1i 3bitr4d )
      ADEIZCJZDKZUCDLZCJZUCBJZDKCACDMUEUGNGUCCDOPAUHUDDFAUCBCHQRCUGNAUFCDESTUAU
      B $.
  $}

  ${
    wl-equsal.1 $e |- F/ x ps $.
    wl-equsal.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  (Contributed by NM,
       2-Jun-1993.)  (Proof shortened by Andrew Salmon, 12-Aug-2011.)  (Revised
       by Mario Carneiro, 3-Oct-2016.)  It seems proving ~ wl-equsald first,
       and then deriving more specialized versions ~ wl-equsal and
       ~ wl-equsal1t then is more efficient than the other way round, which is
       possible, too.  See also ~ equsal .  (Revised by Wolf Lammen,
       27-Jul-2019.)  (Proof modification is discouraged.) $)
    wl-equsal $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( weq wi wal wb wtru nftru wnf a1i wl-equsald mptru ) CDGZAHCIBJKABCDCLBC
      MKENQABJHKFNOP $.
  $}

  $( The expression ` x = y ` in antecedent position plays an important role in
     predicate logic, namely in implicit substitution.  However, occasionally
     it is irrelevant, and can safely be dropped.  A sufficient condition for
     this is when ` x ` (or ` y ` or both) is not free in ` ph ` .

     This theorem is more fundamental than ~ equsal , ~ spimt or ~ sbft , to
     which it is related.  (Contributed by Wolf Lammen, 19-Aug-2018.) $)
  wl-equsal1t $p |- ( F/ x ph -> ( A. x ( x = y -> ph ) <-> ph ) ) $=
    ( wnf nfnf1 id wb weq biid 2a1i wl-equsald ) ABDZAABCABELFAAGLBCHAIJK $.

  $( This simple equivalence eases substitution of one expression for the
     other.  (Contributed by Wolf Lammen, 1-Sep-2018.) $)
  wl-equsalcom $p |- ( A. x ( x = y -> ph ) <-> A. x ( y = x -> ph ) ) $=
    ( weq wi equcom imbi1i albii ) BCDZAECBDZAEBIJABCFGH $.

  ${
    wl-equsal1i.1 $e |- ( F/ x ph \/ F/ y ph ) $.
    wl-equsal1i.2 $e |- ( x = y -> ph ) $.
    $( The antecedent ` x = y ` is irrelevant, if one or both setvar variables
       are not free in ` ph ` .  (Contributed by Wolf Lammen, 1-Sep-2018.) $)
    wl-equsal1i $p |- ph $=
      ( wnf wo weq wi wal sp alcoms wl-equsal1t imbitrid wl-equsalcom biimtrrid
      gen2 biimpd spsd jaoi mp2 ) ABFZACFZGBCHAIZCJZBJZADUDBCEQUBUFAIUCUFUDBJZU
      BAUDUGCBUGCKLABCMNUCUEABUECBHAICJZUCAACBOUCUHAACBMRPSTUA $.
  $}

  ${
    $d x y $.
    $( A more general version of ~ sbid2vw .  (Contributed by Wolf Lammen,
       14-May-2019.) $)
    wl-sbid2ft $p |- ( F/ x ph -> ( [ y / x ] [ x / y ] ph <-> ph ) ) $=
      ( wsb weq wi wal wnf sb6 nfnf1 id wb sbequ12r a1i wl-equsaldv bitrid ) AC
      BDZBCDBCEZQFBGABHZAQBCISQABCABJSKRQALFSABCMNOP $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Change bounded variables in a special case.  The reverse direction seems
       to involve ~ ax-11 .  My hope is that I will in some future be able to
       prove ~ mo3 with reversed quantifiers not using ~ ax-11 .  See also the
       remark in ~ mo4 , which lead me to this effort.  (Contributed by Wolf
       Lammen, 5-Mar-2024.) $)
    wl-cbvalsbi $p |- ( A. x ph -> A. y [ y / x ] ph ) $=
      ( wal wsb stdpc4 alrimiv ) ABDABCECABCFG $.
    $( $j usage 'wl-cbvalsbi' avoids 'ax-11'; $)
  $}

  $( Substitution with a variable not free in antecedent affects only the
     consequent.  Closed form of ~ sbrim .  (Contributed by Wolf Lammen,
     26-Jul-2019.) $)
  wl-sbrimt $p |- ( F/ x ph ->
                     ( [ y / x ] ( ph -> ps ) <-> ( ph -> [ y / x ] ps ) ) ) $=
    ( wi wsb wnf sbim sbft imbi1d bitrid ) ABECDFACDFZBCDFZEACGZAMEABCDHNLAMACD
    IJK $.

  $( Substitution with a variable not free in antecedent affects only the
     consequent.  Closed form of ~ sbrim .  (Contributed by Wolf Lammen,
     26-Jul-2019.) $)
  wl-sblimt $p |- ( F/ x ps ->
                ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> ps ) ) ) $=
    ( wi wsb wnf sbim sbft imbi2d bitrid ) ABECDFACDFZBCDFZEBCGZLBEABCDHNMBLBCD
    IJK $.

  ${
    $d x y $.
    $( Commutation of quantification and substitution variables based on fewer
       axioms than ~ sb9 .  (Contributed by Wolf Lammen, 27-Apr-2025.) $)
    wl-sb9v $p |- ( A. x [ x / y ] ph <-> A. y [ y / x ] ph ) $=
      ( weq wi wal wsb alcom sb6 equcom imbi1i albii bitri 3bitr4i ) BCDZAEZCFZ
      BFPBFZCFACBGZBFABCGZCFPBCHSQBSCBDZAEZCFQACBIUBPCUAOACBJKLMLTRCABCILN $.
      $( $j usage 'wl-sb9v' avoids 'ax-10' 'ax-13'; $)

    $( Substitution of variable in universal quantifier.  Closed form of
       ~ sb8f .  (Contributed by Wolf Lammen, 27-Apr-2025.) $)
    wl-sb8ft $p |- ( A. x F/ y ph -> ( A. x ph <-> A. y [ y / x ] ph ) ) $=
      ( wnf wal wsb wb sbft alimi albi syl wl-sb9v bitr3di ) ACDZBEZACBFZBEZABE
      ZABCFCEOPAGZBEQRGNSBACBHIPABJKABCLM $.

    $( Substitution of variable in existentialal quantifier.  Closed form of
       ~ sb8ef .  (Contributed by Wolf Lammen, 27-Apr-2025.) $)
    wl-sb8eft $p |- ( A. x F/ y ph -> ( E. x ph <-> E. y [ y / x ] ph ) ) $=
      ( wnf wal wex wsb wn wb nfnt alimi wl-sb8ft syl alnex albii bitri 3bitr3g
      sbn con4bid ) ACDZBEZABFZABCGZCFZUAAHZBEZUEBCGZCEZUBHUDHZUAUECDZBEUFUHITU
      JBACJKUEBCLMABNUHUCHZCEUIUGUKCABCROUCCNPQS $.
  $}

  $( Substitution of variable in universal quantifier.  Closed form of ~ sb8 .
     (Contributed by Wolf Lammen, 27-Jul-2019.) $)
  wl-sb8t $p |- ( A. x F/ y ph -> ( A. x ph <-> A. y [ y / x ] ph ) ) $=
    ( wnf wal wsb nfa1 nfnf1 nfal sp wl-nfs1t sps weq wb wi sbequ12 a1i cbv2 )
    ACDZBEZAABCFZBCSBGSCBACHISBJSUABDBABCKLBCMAUANOTABCPQR $.

  $( Substitution of variable in universal quantifier.  Closed form of ~ sb8e .
     (Contributed by Wolf Lammen, 27-Jul-2019.) $)
  wl-sb8et $p |- ( A. x F/ y ph -> ( E. x ph <-> E. y [ y / x ] ph ) ) $=
    ( wnf wal wex wsb wn wb nfnbi albii wl-sb8t sylbi alnex sbn 3bitr3g con4bid
    bitri ) ACDZBEZABFZABCGZCFZTAHZBEZUDBCGZCEZUAHUCHZTUDCDZBEUEUGISUIBACJKUDBC
    LMABNUGUBHZCEUHUFUJCABCOKUBCNRPQ $.

  $( Closed form of ~ sbhb .  Characterizing the expression ` ph -> A. x ph `
     using a substitution expression.  (Contributed by Wolf Lammen,
     28-Jul-2019.) $)
  wl-sbhbt $p |- ( A. x F/ y ph ->
                     ( ( ph -> A. x ph ) <-> A. y ( ph -> [ y / x ] ph ) ) ) $=
    ( wnf wal wi wsb wl-sb8t imbi2d wb 19.21t sps bitr4d ) ACDZBEZAABEZFAABCGZC
    EZFZAQFCEZOPRAABCHINTSJBAQCKLM $.

  $( Two ways expressing that ` x ` is effectively not free in ` ph ` .
     Simplified version of ~ sbnf2 .  Note:  This theorem shows that ~ sbnf2
     has unnecessary distinct variable constraints.  (Contributed by Wolf
     Lammen, 28-Jul-2019.) $)
  wl-sbnf1 $p |- ( A. x F/ y ph ->
                          ( F/ x ph <-> A. x A. y ( ph -> [ y / x ] ph ) ) ) $=
    ( wnf wal wi wsb nf5 nfa1 wl-sbhbt albid bitrid ) ABDAABEFZBEACDZBEZAABCGFC
    EZBEABHOMPBNBIABCJKL $.

  ${
    $d x w $.  $d y w $.  $d z w $.
    $( ~ equsb3 with a distinctor.  (Contributed by Wolf Lammen,
       27-Jun-2019.) $)
    wl-equsb3 $p |- ( -. A. y y = z -> ( [ x / y ] y = z <-> x = z ) ) $=
      ( vw weq wal wn wsb nfna1 nfeqf2 wb wi equequ1 a1i sbbidv sbco2vv 3bitr3g
      sbied equsb3 ) BCEZBFGZTBDHZDAHDCEZDAHTBAHACEUAUBUCDAUATUCBDTBIBCDJBDETUC
      KLUABDCMNROTBADPDACSQ $.
  $}

  $( Substitution applied to an atomic wff.  The distinctor antecedent is more
     general than a distinct variable condition.  (Contributed by Wolf Lammen,
     26-Jun-2019.) $)
  wl-equsb4 $p |- ( -. A. x x = z -> ( [ y / x ] y = z <-> y = z ) ) $=
    ( weq wal wn wsb wb wnf nfeqf ex sbft syl6com sbequ12r equcoms sps pm2.61d2
    ) ACDAEFZABDZAEZBCDZABGUAHZTFZRUAAIZUBUCRUDBCAJKUAABLMSUBAUBBAUABANOPQ $.

  ${
    wl-2sb6d.1 $e |- ( ph -> -. A. y y = x ) $.
    wl-2sb6d.2 $e |- ( ph -> -. A. y y = w ) $.
    wl-2sb6d.3 $e |- ( ph -> -. A. y y = z ) $.
    wl-2sb6d.4 $e |- ( ph -> -. A. x x = z ) $.
    $( Version of ~ 2sb6 with a context, and distinct variable conditions
       replaced with distinctors.  (Contributed by Wolf Lammen, 4-Aug-2019.) $)
    wl-2sb6d $p |- ( ph -> ( [ z / x ] [ w / y ] ps <->
                          A. x A. y ( ( x = z /\ y = w ) -> ps ) ) ) $=
      ( weq wal wn wa wsb wi wb sb4b nfnae nfan jca wl-nfnae1 imbi2d impexp wnf
      albii nfeqf 19.21t syl bitr2id sylan9bb albid syl12anc ) ACEKZCLMZDFKZDLM
      ZDCKDLMZDEKDLMZNZBDFOZCEOZUNUPNBPZDLZCLZQJHAURUSGIUAUOVBUNVAPZCLUQUTNZVEV
      ACERVGVFVDCUQUTCDFCSURUSCCDUBDECSTTUQVFUNUPBPZDLZPZUTVDUQVAVIUNBDFRUCVDUN
      VHPZDLZUTVJVCVKDUNUPBUDUFUTUNDUEVLVJQCEDUGUNVHDUHUIUJUKULUKUM $.
  $}

  ${
    $d u v x $.  $d u v y $.  $d u v w $.  $d u v z $.  $d u v ph $.
    $( Lemma used to prove ~ wl-sbcom2d .  (Contributed by Wolf Lammen,
       10-Aug-2019.)  (New usage is discouraged.) $)
    wl-sbcom2d-lem1 $p |- ( ( u = y /\ v = w ) -> ( -. A. x x = w ->
       ( [ u / x ] [ v / z ] ph <-> [ y / x ] [ w / z ] ph ) ) ) $=
      ( weq wal wn wsb wb wa nfna1 nfeqf2 nfan1 sbequ adantl sbbid ancoms expr
      sylan9bbr ) GCHZFEHZBEHZBIJZADFKZBGKZADEKZBCKZLUDUFMUHUIBGKZUCUJUFUDUHUKL
      UFUDMUGUIBGUFUDBUEBNBEFOPUDUGUILUFAFEDQRSTUIGCBQUBUA $.
  $}

  ${
    $d u v x $.  $d u v y $.  $d u v ph $.
    $( Lemma used to prove ~ wl-sbcom2d .  (Contributed by Wolf Lammen,
       10-Aug-2019.)  (New usage is discouraged.) $)
    wl-sbcom2d-lem2 $p |- ( -. A. y y = x -> ( [ u / x ] [ v / y ] ph
            <-> A. x A. y ( ( x = u /\ y = v ) -> ph ) ) ) $=
      ( weq wal wn id naev wl-2sb6d ) CBFCGHZABCEDLICBDCJCBECJCBEBJK $.
  $}

  ${
    $d u v x $.  $d u v y $.  $d u v w $.  $d u v z $.  $d u v ph $.
    $d u v ps $.
    wl-sbcom2d.1 $e |- ( ph -> -. A. x x = w ) $.
    wl-sbcom2d.2 $e |- ( ph -> -. A. x x = z ) $.
    wl-sbcom2d.3 $e |- ( ph -> -. A. z z = y ) $.
    $( Version of ~ sbcom2 with a context, and distinct variable conditions
       replaced with distinctors.  (Contributed by Wolf Lammen, 4-Aug-2019.) $)
    wl-sbcom2d $p |- ( ph -> ( [ w / z ] [ y / x ] ps <->
                               [ y / x ] [ w / z ] ps ) ) $=
      ( vu vv weq wex wsb wb wi ax6ev wa wal wn wl-sbcom2d-lem2 ancomst naecoms
      alcom 2albii bitri bitrdi bitr4d syl adantl wl-sbcom2d-lem1 syl5 3bitr3rd
      imp ancoms exp31 exlimdv exlimiv mp2 ) JDLZJMKFLZKMZABCDNEFNZBEFNCDNZOZPZ
      JDQKFQUTVBVFPJUTVAVFKUTVAAVEUTVARZARBEKNCJNZBCJNEKNZVDVCAVHVIOZVGACELCSTZ
      VJHVKVHEKLZCJLZRBPZCSESZVIVHVOOECECLESTVHVMVLRBPZESCSZVOBCEKJUAVQVPCSESVO
      VPCEUDVPVNECVMVLBUBUEUFUGUCBECJKUAUHUIUJVGAVHVDOZACFLCSTVGVRGBCDEFKJUKULU
      NVGAVIVCOZVAUTAVSPAEDLESTVAUTRVSIBEFCDJKUKULUOUNUMUPUQURUS $.
  $}

  $( A theorem used in elimination of disjoint variable restrictions by
     replacing them with distinctors.  (Contributed by Wolf Lammen,
     25-Jul-2019.) $)
  wl-sbalnae $p |- ( ( -. A. x x = y /\ -. A. x x = z ) ->
           ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
    ( weq wal wn wa wsb wb sb4b nfnae nfan wnf nfeqf 19.21t albid sbequ12 sps
    wi bicomd syl sylan9bbr alcom bitrdi adantl bitr4d ex dral2 bitr3d pm2.61d2
    ) BCEBFGZBDEBFGZHZCDEZCFZABFZCDIZACDIZBFZJZUNUPGZVAUNVBHURUOATZBFZCFZUTVBUR
    UOUQTZCFUNVEUQCDKUNVFVDCULUMCBCCLBDCLMUNUOBNZVFVDJCDBOVGVDVFUOABPUAUBQUCVBU
    TVEJUNVBUTVCCFZBFVEVBUSVHBCDBLACDKQVCBCUDUEUFUGUHUPUQURUTUOUQURJCUQCDRSAUSC
    DBUOAUSJCACDRSUIUJUK $.

  ${
    $d x y $.
    $( A theorem used in elimination of disjoint variable restriction on ` x `
       and ` y ` by replacing it with a distinctor ` -. A. x x = z ` .
       (Contributed by NM, 15-May-1993.)  Proof is based on ~ wl-sbalnae now.
       See also ~ sbal1 .  (Revised by Wolf Lammen, 25-Jul-2019.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    wl-sbal1 $p |- ( -. A. x x = z ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      ( weq wal wn wsb wb naev wl-sbalnae mpancom ) BCEBFGBDEBFGABFCDHACDHBFIBD
      CBJABCDKL $.
  $}

  ${
    $d x z $.
    $( Move quantifier in and out of substitution.  Revised to remove a
       distinct variable constraint.  (Contributed by NM, 2-Jan-2002.)  Proof
       is based on ~ wl-sbalnae now.  See also ~ sbal2 .  (Revised by Wolf
       Lammen, 25-Jul-2019.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    wl-sbal2 $p |- ( -. A. x x = y ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      ( weq wal wn wsb wb naev wl-sbalnae mpdan ) BCEBFGBDEBFGABFCDHACDHBFIBCDB
      JABCDKL $.
  $}

  $( ~ spsbbi applied twice.  (Contributed by Wolf Lammen, 5-Aug-2023.) $)
  wl-2spsbbi $p |- ( A. a A. b ( ph <-> ps ) ->
       ( [ y / b ] [ x / a ] ph <-> [ y / b ] [ x / a ] ps ) ) $=
    ( wb wal wsb alcom nfa1 sp sbbid sps sylbi ) ABGZFHEHPEHZFHZAECIZFDIBECIZFD
    IGPEFJRSTFDQFKQSTGFQABECPEKPELMNMO $.

  ${
    $d x y $.
    $( This theorem provides a basic working step in proving theorems about
       ` E* ` or ` E! ` .  (Contributed by Wolf Lammen, 3-Oct-2019.) $)
    wl-lem-exsb $p |- ( x = y -> ( ph <-> A. x ( x = y -> ph ) ) ) $=
      ( weq wi wal ax12v2 sp com12 impbid ) BCDZAKAEZBFZABCGMKALBHIJ $.
  $}

  $( This theorem provides a basic working step in proving theorems about
     ` E* ` or ` E! ` .  (Contributed by Wolf Lammen, 3-Oct-2019.) $)
  wl-lem-nexmo $p |- ( -. E. x ph -> A. x ( ph -> x = z ) ) $=
    ( wex wn wal weq wi alnex pm2.21 alimi sylbir ) ABDEAEZBFABCGZHZBFABIMOBANJ
    KL $.

  ${
    $d x z $.
    $( The antecedent ` A. x ( ph -> x = z ) ` relates to ` E* x ph ` , but is
       better suited for usage in proofs.  Note that no distinct variable
       restriction is placed on ` ph ` .

       This theorem provides a basic working step in proving theorems about
       ` E* ` or ` E! ` .  (Contributed by Wolf Lammen, 3-Oct-2019.) $)
    wl-lem-moexsb $p |- ( A. x ( ph -> x = z ) ->
                          ( E. x ph <-> [ z / x ] ph ) ) $=
      ( weq wi wal wex wsb nfa1 nfs1v sp ax12v2 syli sb6 imbitrrdi exlimd spsbe
      impbid1 ) ABCDZEZBFZABGABCHZUAAUBBTBIABCJUAASAEBFZUBAUASUCTBKABCLMABCNOPA
      BCQR $.
  $}

  ${
    wl-alanbii.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( This theorem extends ~ alanimi to a biconditional.  Recurrent usage
       stacks up more quantifiers.  (Contributed by Wolf Lammen,
       4-Oct-2019.) $)
    wl-alanbii $p |- ( A. x ph <-> ( A. x ps /\ A. x ch ) ) $=
      ( wal wa albii 19.26 bitri ) ADFBCGZDFBDFCDFGAKDEHBCDIJ $.
  $}

  ${
    $d u x $.  $d u y $.  $d u ph $.  $d u ps $.
    wl-mo2df.1 $e |- F/ x ph $.
    wl-mo2df.2 $e |- F/ y ph $.
    wl-mo2df.3 $e |- ( ph -> -. A. x x = y ) $.
    wl-mo2df.4 $e |- ( ph -> F/ y ps ) $.
    $( Version of ~ mof with a context and a distinctor replacing a distinct
       variable condition.  This version should be used only to eliminate
       disjoint variable conditions.  (Contributed by Wolf Lammen,
       11-Aug-2019.) $)
    wl-mo2df $p |- ( ph -> ( E* x ps <-> E. y A. x ( ps -> x = y ) ) ) $=
      ( vu wmo weq wi wal wex dfmo wn wnf nfeqf1 naecoms wb syl nfimd wa nfeqf2
      nfald nfnae nfan1 equequ2 imbi2d adantl albid sylan ex cbvexd bitrid ) BC
      JBCIKZLZCMZINABCDKZLZCMZDNBCIOAURVAIDFAUQDCEABUPDHAUSCMPZUPDQZGVCDCDCIRSU
      AUBUEAIDKZURVATZAVBVDVEGVBVDUCUQUTCVBVDCCDCUFCDIUDUGVDUQUTTVBVDUPUSBIDCUH
      UIUJUKULUMUNUO $.
  $}

  $( Closed form of ~ mof with a distinctor avoiding distinct variable
     conditions.  (Contributed by Wolf Lammen, 20-Sep-2020.) $)
  wl-mo2tf $p |- ( ( -. A. x x = y /\ A. x F/ y ph ) ->
          ( E* x ph <-> E. y A. x ( ph -> x = y ) ) ) $=
    ( weq wal wn wnf wa nfnae nfa1 nfan nfnf1 nfal simpl sp adantl wl-mo2df ) B
    CDBEFZACGZBEZHABCRTBBCBISBJKRTCBCCISCBACLMKRTNTSRSBOPQ $.

  ${
    $d u x $.  $d u y $.  $d u ph $.  $d u ps $.
    wl-eudf.1 $e |- F/ x ph $.
    wl-eudf.2 $e |- F/ y ph $.
    wl-eudf.3 $e |- ( ph -> -. A. x x = y ) $.
    wl-eudf.4 $e |- ( ph -> F/ y ps ) $.
    $( Version of ~ eu6 with a context and a distinctor replacing a distinct
       variable condition.  This version should be used only to eliminate
       disjoint variable conditions.  (Contributed by Wolf Lammen,
       23-Sep-2020.) $)
    wl-eudf $p |- ( ph -> ( E! x ps <-> E. y A. x ( ps <-> x = y ) ) ) $=
      ( vu weu weq wb wal wex eu6 wn wnf nfeqf1 naecoms syl nfbid nfald equequ2
      wa nfnae nfeqf2 nfan1 bibi2d adantl albid sylan ex cbvexd bitrid ) BCJBCI
      KZLZCMZINABCDKZLZCMZDNBCIOAUQUTIDFAUPDCEABUODHAURCMPZUODQZGVBDCDCIRSTUAUB
      AIDKZUQUTLZAVAVCVDGVAVCUDUPUSCVAVCCCDCUECDIUFUGVCUPUSLVAVCUOURBIDCUCUHUIU
      JUKULUMUN $.
  $}

  $( Closed form of ~ eu6 with a distinctor avoiding distinct variable
     conditions.  (Contributed by Wolf Lammen, 23-Sep-2020.) $)
  wl-eutf $p |- ( ( -. A. x x = y /\ A. x F/ y ph ) ->
          ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) ) $=
    ( weq wal wn wnf wa nfnae nfa1 nfan nfnf1 nfal simpl sp adantl wl-eudf ) BC
    DBEFZACGZBEZHABCRTBBCBISBJKRTCBCCISCBACLMKRTNTSRSBOPQ $.

  ${
    $d x z $.  $d y z $.
    $( ~ euequ proved with a distinctor.  (Contributed by Wolf Lammen,
       23-Sep-2020.) $)
    wl-euequf $p |- ( -. A. x x = y -> E! x x = y ) $=
      ( vz weq wal wn wb wex weu ax6ev nfv nfna1 nfeqf2 equequ2 equcoms alrimdd
      wi a1i eximd mpi eu6 sylibr ) ABDZAEFZUCACDGZAEZCHZUCAIUDCBDZCHUGCBJUDUHU
      FCUDCKUDUHUEAUCALABCMUHUEQUDUEBCBCANORPSTUCACUAUB $.
  $}

  ${
    $d u x y $.  $d u ph $.
    $( Closed form of ~ mof .  (Contributed by Wolf Lammen, 18-Aug-2019.) $)
    wl-mo2t $p |- ( A. x F/ y ph ->
                      ( E* x ph <-> E. y A. x ( ph -> x = y ) ) ) $=
      ( vu wmo weq wi wal wex wnf dfmo nfnf1 nfal nfa1 nfvd nfimd nfald equequ2
      sp wb imbi2d albidv a1i cbvexdw bitrid ) ABEABDFZGZBHZDIACJZBHZABCFZGZBHZ
      CIABDKUJUHUMDCUICBACLMUJUGCBUIBNUJAUFCUIBSUJUFCOPQDCFZUHUMTGUJUNUGULBUNUF
      UKADCBRUAUBUCUDUE $.
  $}

  ${
    $d x y u $.  $d ph u $.
    $( Closed form of ~ mo3 .  (Contributed by Wolf Lammen, 18-Aug-2019.) $)
    wl-mo3t $p |- ( A. x F/ y ph -> ( E* x ph <->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) ) $=
      ( vu wnf wal wmo wsb wa weq wi nfa1 nfmo1 nfnf1 nfal sp nfmodv wex alrimd
      nfan1 dfmo spsbim equsb3 imbitrdi anim12d equtr2 syl6 sylbi adantl alrimi
      exlimiv ex nfs1v pm3.3 com23 sps aleximi alcoms wl-sb8eft wl-mo2t imbi12d
      moabs bitrid imbitrrid impbid ) ACEZBFZABGZAABCHZIZBCJZKZCFZBFZVGVHVMBVFB
      LZABMVGVHVMVGVHIVLCVGVHCVFCBACNOVGACBVOVFBPQTVHVLVGVHABDJZKZBFZDRVLABDUAV
      RVLDVRVJVPCDJZIVKVRAVPVIVSVQBPVRVIVPBCHVSAVPBCUBBCDUCUDUEBCDUFUGUKUHUIUJU
      LSVNVHVGVICRZAVKKZBFZCRZKZVLWDCBVLBFZVIWBCWEVIWABVLBLABCUMVLVIWAKBVLAVIVK
      AVIVKUNUOUPSUQURVHABRZVHKVGWDABVBVGWFVTVHWCABCUSABCUTVAVCVDVE $.
  $}

  ${
    $d x z $.  $d y z $.
    $( Closed form of ~ nfsbv .  (Contributed by Wolf Lammen, 2-May-2025.) $)
    wl-nfsbtv $p |- ( A. x F/ z ph -> F/ z [ y / x ] ph ) $=
      ( wnf wal wsb stdpc4 sbnf sylib ) ADEZBFKBCGABCGDEKBCHADBCIJ $.
  $}

  ${
    $d u v x $.  $d u v y $.  $d u v ph $.
    $( Substitution of variable in universal quantifier.  Closed form of
       ~ sb8eu .  (Contributed by Wolf Lammen, 11-Aug-2019.) $)
    wl-sb8eut $p |- ( A. x F/ y ph -> ( E! x ph <-> E! y [ y / x ] ph ) ) $=
      ( vu vv wnf wal weq wb wex wsb weu nfnf1 nfal equsb3 sblbis nfa1 sp nfsbd
      eu6 nfvd nfbid nfxfrd wi sbequ a1i cbvald nfv bicomi albii 3bitr3g exbidv
      sb8 3bitr4g ) ACFZBGZABDHZIZBGZDJABCKZCDHZIZCGZDJABLUTCLUPUSVCDUPURBEKZEG
      ZURBCKZCGUSVCUPVDVFECUOCBACMNVDABEKZEDHZIUPCUQVHABEBEDOPUPVGVHCUPABECUOBQ
      UOBRSUPVHCUAUBUCECHVDVFIUDUPURECBUEUFUGUSVEURBEUREUHUMUIVFVBCUQVAABCBCDOP
      UJUKULABDTUTCDTUN $.
  $}

  ${
    $d u v x y $.  $d u v ph $.
    $( Substitution of variable in universal quantifier.  Closed form of
       ~ sb8euv .  (Contributed by Wolf Lammen, 3-May-2025.) $)
    wl-sb8eutv $p |- ( A. x F/ y ph -> ( E! x ph <-> E! y [ y / x ] ph ) ) $=
      ( vu vv wnf wal weq wb wex wsb weu nfnf1 nfal equsb3 wl-nfsbtv nfvd nfbid
      sblbis eu6 nfxfrd wi sbequ a1i cbvaldw sb8v bicomi 3bitr3g exbidv 3bitr4g
      albii ) ACFZBGZABDHZIZBGZDJABCKZCDHZIZCGZDJABLUQCLUMUPUTDUMUOBEKZEGZUOBCK
      ZCGUPUTUMVAVCECULCBACMNVAABEKZEDHZIUMCUNVEABEBEDOSUMVDVECABECPUMVECQRUAEC
      HVAVCIUBUMUOECBUCUDUEUPVBUOBEUFUGVCUSCUNURABCBCDOSUKUHUIABDTUQCDTUJ $.
  $}

  $( Substitution of variable in universal quantifier.  Closed form of
     ~ sb8mo .  (Contributed by Wolf Lammen, 11-Aug-2019.) $)
  wl-sb8mot $p |- ( A. x F/ y ph -> ( E* x ph <-> E* y [ y / x ] ph ) ) $=
    ( wnf wal wex weu wi wsb wmo wl-sb8et wl-sb8eut imbi12d moeu 3bitr4g ) ACDB
    EZABFZABGZHABCIZCFZSCGZHABJSCJPQTRUAABCKABCLMABNSCNO $.

  ${
    $d x y $.
    $( Substitution of variable in universal quantifier.  Closed form of
       ~ sb8mo without ~ ax-13 , but requiring ` x ` and ` y ` being disjoint.

       This theorem relates to ~ wl-mo3t , since replacing ` ph ` with
       ` [ y / x ] ph ` in the latter yields subexpressions like
       ` [ x / y ] [ y / x ] ph ` , which can be reduced to ` ph ` via ~ sbft
       and ~ sbco .  So ` E* x ph <-> E* y [ y / x ] ph ` is provable from
       ~ wl-mo3t in a simple fashion.  From an educational standpoint, one
       would assume ~ wl-mo3t to be more fundamental, as it hints how the "at
       most one" objects on both sides of the biconditional correlate (they are
       the same), if they exist at all, and then prove this theorem from it.
       (Contributed by Wolf Lammen, 3-May-2025.) $)
    wl-sb8motv $p |- ( A. x F/ y ph -> ( E* x ph <-> E* y [ y / x ] ph ) ) $=
      ( wnf wal wex weu wi wsb wmo wl-sb8eft wl-sb8eutv imbi12d moeu 3bitr4g )
      ACDBEZABFZABGZHABCIZCFZSCGZHABJSCJPQTRUAABCKABCLMABNSCNO $.
  $}

  ${
    $d A y $.  $d x y $.
    $( A closed form of ~ issetf .  The proof here is a modification of a
       subproof in ~ vtoclgft , where it could be used to shorten the proof.
       (Contributed by Wolf Lammen, 25-Jan-2025.) $)
    wl-issetft $p |- ( F/_ x A -> ( A e. _V <-> E. x x = A ) ) $=
      ( vy cvv wcel cv wceq wex wnfc isset wn wal nfv nfnfc1 nfcvd id nfnd nfvd
      nfeqd alnex weq wb wi eqeq1 notbid a1i cbv2w 3bitr3g con4bid bitrid ) BDE
      CFZBGZCHZABIZAFZBGZAHZCBJUNUMUQUNULKZCLUPKZALUMKUQKUNURUSCAUNCMABNUNULAUN
      AUKBUNAUKOUNPSQUNUSCRCAUAZURUSUBUCUNUTULUPUKUOBUDUEUFUGULCTUPATUHUIUJ $.
  $}

  ${
    wl-axc11rc11.1 $e |- ( A. y y = x -> ( A. y y = x -> A. x y = x ) ) $.
    wl-axc11rc11.2 $e |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $.
    $( Proving ~ axc11r from ~ axc11 .  The hypotheses are two instances of
       ~ axc11 used in the proof here.  Some systems introduce ~ axc11 as an
       axiom, see for example System S2 in
       ~ https://us.metamath.org/downloads/finiteaxiom.pdf .

       By contrast, this database sees the variant ~ axc11r , directly derived
       from ~ ax-12 , as foundational.  Later ~ axc11 is proven somewhat
       trickily, requiring ~ ax-10 and ~ ax-13 , see its proof.  (Contributed
       by Wolf Lammen, 18-Jul-2023.) $)
    wl-axc11rc11 $p |- ( A. y y = x -> ( A. x ph -> A. y ph ) ) $=
      ( weq wal wi pm2.43i equcomi alimi 3syl ) CBFZCGZMBGZBCFZBGABGACGHNODIMPB
      CBJKEL $.
  $}

  ${
    $d x y $.  $d x ph $.
    $( Variant of ~ df-clab , where the element ` x ` is required to be
       disjoint from the class it is taken from.  This restriction meets
       similar ones found in other definitions and axioms like ~ ax-ext ,
       ~ df-clel and ~ df-cleq . ` x e. A ` with ` A ` depending on ` x ` can
       be the source of side effects, that you rather want to be aware of.  So
       here we eliminate one possible way of letting this slip in instead.

       An expression ` x e. A ` with ` x ` , ` A ` not disjoint, is now only
       introduced either via ~ ax-8 , ~ ax-9 , or ~ df-clel .  Theorem
       ~ cleljust shows that a possible choice does not matter.

       The original ~ df-clab can be rederived, see ~ wl-dfclab .  In an
       implementation this theorem is the only user of df-clab.  (Contributed
       by NM, 26-May-1993.)  Element and class are disjoint.  (Revised by Wolf
       Lammen, 31-May-2023.) $)
    wl-clabv $p |- ( x e. { y | ph } <-> [ x / y ] ph ) $=
      ( df-clab ) ABCD $.
  $}

  ${
    $d z x $.  $d z y $.  $d z ph $.
    $( Rederive ~ df-clab from ~ wl-clabv .  (Contributed by Wolf Lammen,
       31-May-2023.)  (Proof modification is discouraged.) $)
    wl-dfclab $p |- ( x e. { y | ph } <-> [ x / y ] ph ) $=
      ( vz cv cab wcel weq wa wex wsb dfclel wl-clabv sbequ bitrid exbii 19.41v
      pm5.32i ax6ev biantrur bitr4i 3bitri ) BEZACFZGDBHZDEUDGZIZDJUEACBKZIZDJZ
      UHDUCUDLUGUIDUEUFUHUFACDKUEUHADCMADBCNORPUJUEDJZUHIUHUEUHDQUKUHDBSTUAUB
      $.
  $}

  ${
    $d x y ph $.  $d y ps $.
    $( Using class abstraction in a context, requiring ` x ` and ` ph `
       disjoint, but based on fewer axioms than ~ wl-clabt .  (Contributed by
       Wolf Lammen, 29-May-2023.) $)
    wl-clabtv $p |- ( ph -> { x | ps } = { x | ( ph -> ps ) } ) $=
      ( vy cab wi wsb cv wcel biimt sbbidv df-clab 3bitr4g eqrdv ) ADBCEZABFZCE
      ZABCDGPCDGDHZOIRQIABPCDABJKBDCLPDCLMN $.
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    wl-clabt.nf $e |- F/ x ph $.
    $( Using class abstraction in a context.  For a version based on fewer
       axioms see ~ wl-clabtv .  (Contributed by Wolf Lammen, 29-May-2023.) $)
    wl-clabt $p |- ( ph -> { x | ps } = { x | ( ph -> ps ) } ) $=
      ( vy cab wi wsb cv wcel biimt sbbid df-clab 3bitr4g eqrdv ) AEBCFZABGZCFZ
      ABCEHQCEHEIZPJSRJABQCEDABKLBECMQECMNO $.
  $}

  ${
    $d x y $.  $d y ph $.  $d x ps $.
    wl-eujustlem1.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Version of ~ cbvexvw with references to ~ ax-6 listed as antecedents.
       (Contributed by Wolf Lammen, 18-Feb-2026.) $)
    wl-eujustlem1 $p |- ( ( A. y E. x x = y /\ A. x E. y x = y )
                          -> ( E. x ph <-> E. y ps ) ) $=
      ( weq wex wal wa notbid biimpcd aleximi ax5e alimdv com12 biimprcd anbiim
      wn syl6 df-ex 3bitr4g ) CDFZCGZDHZUBDGZCHZIZARZCHZRBRZDHZRACGBDGUGUIUKUDU
      FUIUKUIUDUKUIUCUJDUIUCUJCGUJUHUBUJCUBUHUJUBABEJZKLUJCMSNOUKUFUIUKUEUHCUKU
      EUHDGUHUJUBUHDUBUHUJULPLUHDMSNOQJACTBDTUA $.
  $}


$( (End of Wolf Lammen's mathbox.) $)
