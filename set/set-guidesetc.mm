$(
###############################################################################
  GUIDES AND MISCELLANEA
###############################################################################
$)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Guides (conventions, explanations, and examples)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Conventions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  <HTML>
  <p>
  This section describes the conventions we use.  These conventions often refer
  to existing mathematical practices, which are discussed in more detail in
  other references.

  They are organized as follows:
  <ul>
  <li> ~ conventions : general conventions</li>
  <li> ~ conventions-labels : conventions related to labels</li>
  <li> ~ conventions-comments : conventions related to comments</li>
  </ul>

  <p>
  Logic and set theory provide a foundation for all of mathematics.  To learn
  about them, you should study one or more of the references listed below.  We
  indicate references using square brackets.  The textbooks provide a
  motivation for what we are doing, whereas Metamath lets you see in detail all
  hidden and implicit steps.  Most standard theorems are accompanied by
  citations.  Some closely followed texts include the following:
  <ul>
  <li>Axioms of propositional calculus - [Margaris].</li>
  <li>Axioms of predicate calculus - [Megill] (System S3' in the article
      referenced).</li>
  <li>Theorems of propositional calculus - [WhiteheadRussell].</li>
  <li>Theorems of pure predicate calculus - [Margaris].</li>
  <li>Theorems of equality and substitution - [Monk2], [Tarski], [Megill].</li>
  <li>Axioms of set theory - [BellMachover].</li>
  <li>Development of set theory - [TakeutiZaring].  (The first part of [Quine]
      has a good explanation of the powerful device of "virtual" or
      class abstractions, which is essential to our development.)</li>
  <li>Construction of real and complex numbers - [Gleason].</li>
  <li>Theorems about real numbers - [Apostol].</li>
  </ul>
  </HTML>

$)

  ${
    $( Dummy premise for ~ conventions . $)
    conventions.1 $e |- ph $.
    $(
       <HTML>
       <p>Here are some of the conventions we use in the Metamath Proof
       Explorer (MPE, set.mm), and how they correspond to typical textbook
       language (skipping the many cases where they are identical).
       For more specific conventions, see:
       <ul>
       <li> ~ conventions-labels : conventions related to labels</li>
       <li> ~ conventions-comments : conventions related to comments</li>
       </ul>

       <ul>
       <li><p><b>Notation.</b>
       Where possible, the notation attempts to conform to modern
       conventions, with variations due to our choice of the axiom system
       or to make proofs shorter.  However, our notation is strictly
       sequential (left-to-right). For example, summation is written in the
       form ` sum_ k e. A B ` ( ~ df-sum ) which denotes that index
       variable ` k ` ranges over ` A ` when evaluating ` B ` .  Thus,
       ` sum_ k e. NN ( 1 / ( 2 ^ k ) ) = 1 ` means 1/2 + 1/4 + 1/8 + ...
       = 1 ( ~ geoihalfsum ).
       The notation is usually explained in more detail when first introduced.
       </li>

       <li><p><b>Axiomatic assertions ($a).</b>
       All axiomatic assertions ($a statements)
       starting with " ` |- ` " have labels starting
       with "ax-" (axioms) or "df-" (definitions).  A statement with a
       label starting with "ax-" corresponds to what is traditionally
       called an axiom.  A statement with a label starting with "df-"
       introduces new symbols or a new relationship among symbols
       that can be eliminated; they always extend the definition of
       a wff or class.  Metamath blindly treats $a statements as new
       given facts but does not try to justify them.  The mmj2 program
       will justify the definitions as sound as discussed below,
       except for four of them ( ~ df-bi , ~ df-clab , ~ df-cleq , ~ df-clel )
       that require a more complex metalogical justification by hand.
       </li>

       <li><p><b>Proven axioms.</b>
       In some cases we wish to treat an expression as an axiom in
       later theorems, even though it can be proved.  For example,
       we derive the postulates or axioms of complex arithmetic as
       theorems of ZFC set theory.  For convenience, after deriving
       the postulates, we reintroduce them as new axioms on
       top of set theory.  This lets us easily identify which axioms
       are needed for a particular complex number proof, without the
       obfuscation of the set theory used to derive them.  For more, see
       ~ mmcomplex.html .  When we wish
       to use a previously-proven assertion as an axiom, our convention
       is that we use the
       regular "ax-NAME" label naming convention to define the axiom,
       but we precede it with a proof of the same statement with the label
       "axNAME" .  An example is the complex arithmetic axiom ~ ax-1cn ,
       proven by the preceding theorem ~ ax1cn .
       The Metamath program will warn if an axiom does not match the preceding
       theorem that justifies it if the names match in this way.
       </li>

       <li><p><b>Definitions (df-...).</b>
       We encourage definitions to include hypertext links to proven examples.
       </li>

       <li><p><b>Statements with hypotheses.</b>
       Many theorems and some axioms, such as ~ ax-mp , have hypotheses that
       must be satisfied in order for the conclusion to hold, in this case min
       and maj.  When displayed in summarized form such as in the "Theorem
       List" page (to get to it, click on "Nearby theorems" on the ~ ax-mp
       page), the hypotheses are connected with an ampersand and separated from
       the conclusion with a double right arrow, such as in
       " ` |- ph & |- ( ph -> ps ) => |- ps ` ".  These symbols are not part of
       the Metamath language but are just informal notation meaning "and" and
       "implies".
       </li>

       <li><p><b>Discouraged use and modification.</b>
       If something should only be used in limited ways, it is marked with
       "(New usage is discouraged.)". This is used, for example, when something
       can be constructed in more than one way, and we do not want later
       theorems to depend on that specific construction.
       This marking is also used if we want later proofs to use proven axioms.
       For example, we want later proofs to
       use ~ ax-1cn (not ~ ax1cn ) and ~ ax-1ne0 (not ~ ax1ne0 ), as these
       are proven axioms for complex arithmetic.  Thus, both
       ~ ax1cn and ~ ax1ne0 are marked as "(New usage is discouraged.)".
       In some cases a proof should not normally be changed, e.g., when it
       demonstrates some specific technique.
       These are marked with "(Proof modification is discouraged.)".
       </li>

       <li><p><b>New definitions infrequent.</b>
       Typically, we are minimalist when introducing new definitions; they are
       introduced only when a clear advantage becomes apparent for reducing
       the number of symbols, shortening proofs, etc.  We generally avoid
       the introduction of gratuitous definitions because each one requires
       associated theorems and additional elimination steps in proofs.
       For example, we use ` < ` and ` <_ ` for inequality expressions, and
       use ` ( ( sin `` ( _i x. A ) ) / _i ) ` instead of ` ( sinh `` A ) `
       for the hyperbolic sine.
       </li>

       <li><p><b>Minimizing axiom dependencies.</b>
       We prefer proofs that depend on fewer and/or weaker axioms, even if
       the proofs are longer.  In particular, because of the non-constructive
       nature of the axiom of choice ~ df-ac , we prefer proofs that do not use
       it, or use weaker versions like countable choice ~ ax-cc or dependent
       choice ~ ax-dc .  An example is our proof of the Schroeder-Bernstein
       Theorem ~ sbth , which does not use the axiom of choice.  Similarly,
       any theorem in first-order logic (FOL) that contains only setvar
       variables that are all mutually distinct, and has no wff variables, can
       be proved without using ~ ax-10 through ~ ax-13 , by using ~ ax10w
       through ~ ax13w instead.

       <p>We do not try to similarly reduce dependencies on definitions, since
       definitions are conservative (they do not increase the proving power of
       a deductive system), and are introduced in order to be used to increase
       readability).  An exception is made for Definitions ~ df-clab ,
       ~ df-cleq , and ~ df-clel , since they can be considered as axioms under
       some definitions of what a definition is exactly (see their comments).
       </li>

       <li><p><b>Alternate proofs (ALT).</b>
       If a different proof is shorter or clearer but uses more or stronger
       axioms, we make that proof an "alternate" proof (marked with an ALT
       label suffix), even if this alternate proof was formalized first.
       We then make the proof that requires fewer axioms the main proof.
       Alternate proofs can also occur in other cases when an alternate proof
       gives some particular insight.  Their comment should begin with
       "Alternate proof of ~~ xxx " followed by a description of the
       specificity of that alternate proof.  There can be multiple alternates.
       Alternate (*ALT) theorems should have "(Proof modification is
       discouraged.)  (New usage is discouraged.)" in their comment and should
       follow the main statement, so that people reading the text in order will
       see the main statement first.  The alternate and main statement comments
       should use hyperlinks to refer to each other.
       </li>

       <li><p><b>Alternate versions (ALTV).</b>
       The suffix ALTV is reserved for theorems (or definitions) which are
       alternate versions, or variants, of an existing theorem.  This is
       reserved to statements in mathboxes and is typically used temporarily,
       when it is not clear yet which variant to use.  If it is decided that
       both variants should be kept and moved to the main part of set.mm, then
       a label for the variant should be found with a more explicit suffix
       indicating how it is a variant (e.g., commutation of some subformula,
       antecedent replaced with hypothesis, (un)curried variant, biconditional
       instead of implication, etc.).  There is no requirement to add
       discouragement tags, but their comment should have a link to the main
       version of the statement and describe how it is a variant of it.
       </li>

       <li><p><b>Old (OLD) versions or proofs.</b>
       If a proof, definition, axiom, or theorem is going to be removed, we
       often stage that change by first renaming its label with an OLD suffix
       (to make it clear that it is going to be removed).  Old (*OLD)
       statements should have
       "(Proof modification is discouraged.)  (New usage is discouraged.)" and
       "Obsolete version of ~~ xxx as of dd-Mmm-yyyy." (not enclosed in
       parentheses) in the comment.  An old statement should follow the main
       statement, so that people reading the text in order will see the main
       statement first.  This typically happens when a shorter proof to an
       existing theorem is found: the existing theorem is kept as an *OLD
       statement for one year.  When a proof is shortened automatically (using
       the Metamath program "MM-PA> MINIMIZE__WITH *" command), then it is not
       necessary to keep the old proof, nor to add credit for the shortening.
       </li>

       <li><p><b>Variables.</b>
       Propositional variables (variables for well-formed formulas or wffs) are
       represented with lowercase Greek letters and are generally used
       in this order:
       ` ph ` = phi, ` ps ` = psi, ` ch ` = chi, ` th ` = theta,
       ` ta ` = tau, ` et ` = eta, ` ze ` = zeta, and ` si ` = sigma.
       Individual setvar variables are represented with lowercase Latin letters
       and are generally used in this order:
       ` x ` , ` y ` , ` z ` , ` w ` , ` v ` , ` u ` , and ` t ` .
       In addition, the surreal number section uses subscripted lowercase
       Latin letters such as ` xO ` , ` xL ` , and ` xR ` .  These match
       the conventional literature on surreal numbers.  These variables
       should not be used outside of that section.
       Variables that represent classes are often represented by
       uppercase Latin letters:
       ` A ` , ` B ` , ` C ` , ` D ` , ` E ` , and so on.
       There are other symbols that also represent class variables and suggest
       specific purposes, e.g., ` .0. ` for a zero element (e.g., ~ fsuppcor )
       and connective symbols such as ` .+ ` for some group addition operation
       (e.g., ~ grpinva ).
       Class variables are selected in alphabetical order starting
       from ` A ` if there is no reason to do otherwise, but many
       assertions select different class variables or a different order
       to make their intended meaning clearer.
       </li>

       <li><p><b>Turnstile.</b>
       "` |- ` ", meaning "It is provable that", is the first token
       of all assertions
       and hypotheses that aren't syntax constructions.  This is a standard
       convention in logic.  For us, it also prevents any ambiguity with
       statements that are syntax constructions, such as "wff ` -. ph ` ".
       </li>

       <li><p><b>Biconditional ( ` <-> ` ).</b>
       There are basically two ways to maximize the effectiveness of
       biconditionals ( ` <-> ` ):
       you can either have one-directional simplifications of all theorems
       that <i>produce</i> biconditionals, or you can have one-directional
       simplifications of theorems that <i>consume</i> biconditionals.
       Some tools (like Lean) follow the first approach, but set.mm follows
       the second approach. Practically, this means that in set.mm, for
       every theorem that uses an implication in the hypothesis, like
       ~ ax-mp , there is a corresponding version with a biconditional or a
       reversed biconditional, like ~ mpbi / ~ mpbir .  We prefer this
       second approach because the number of duplications in the second
       approach is bounded by the size of the propositional calculus section,
       which is much smaller than the number of possible theorems in all later
       sections that produce biconditionals.  So although theorems like
       ~ biimpi / ~ biimpri are available, in most cases there is already a
       theorem that combines it with your theorem of choice, like ~ sylbi /
       ~ sylbir , ~ sylib / ~ sylibr , ~ sylbb / ~ sylbbr , their deduction
       versions, ~ mpbir2an , ~ 3imtr4i ...
       </li>

       <li><p><b>Quantifiers.</b>
       The quantifiers are named as follows:
       <ul>
       <li> ` A. ` : universal quantifier ( ~ wal );</li>
       <li> ` E. ` : existential quantifier ( ~ df-ex );</li>
       <li> ` E* ` : at-most-one quantifier ( ~ df-mo );</li>
       <li> ` E! ` : unique existential quantifier ( ~ df-eu ).</li>
       </ul>
       <p>The phrase "uniqueness quantifier" is avoided since it is ambiguous:
       it can be understood as claiming either uniqueness ( ` E* ` ) or unique
       existence ( ` E! ` ).
       </li>

       <li><p><b>Substitution.</b>
       The expression "` [ y / x ] ph ` " should be read "the formula that
       results from the proper substitution of ` y ` for ` x ` in the formula
       ` ph ` ".  See ~ df-sb and the related ~ df-sbc and ~ df-csb .
       </li>

       <li><p><b>Is-a-set.</b>
       " ` A e. _V ` " should be read "Class ` A ` is a set (i.e., exists)."
       This is a convention based on Definition 2.9 of [Quine] p. 19.
       See ~ df-v and ~ isset .
       However, instead of using ` I e. _V ` in the antecedent of a theorem for
       some variable ` I ` , we now prefer to use ` I e. V ` (or another
       variable if ` V ` is not available) to make it more general.  That way
       we can often avoid extra uses of ~ elex and ~ syl in the common case
       where ` I ` is already a member of something.  For hypotheses
       ($e statement) of theorems (mostly in inference form), however,
       ` |- A e. _V ` is used rather than ` |- A e. V ` (e.g., ~ difexi ).
       This is because ` A e. _V ` is almost always satisfied using an
       existence theorem stating " ` ... e. _V ` ", and a hard-coded ` _V ` in
       the $e statement saves a couple of syntax building steps that substitute
       ` _V ` into ` V `. Notice that this does not hold for hypotheses of
       theorems in deduction form: Here still ` |- ( ph -> A e. V ) ` should be
       used rather than ` |- ( ph -> A e. _V ) `.
       </li>

       <li><p><b>Converse.</b>
       The symbol " ` ``' ` " denotes the converse of a relation, so
       " ` ``' R ` " denotes the converse of the class ` R ` , which is
       typically a relation in that context (see ~ df-cnv ). The converse of a
       relation ` R ` is sometimes denoted by R<sup>-1</sup> in textbooks,
       especially when ` R ` is a function, but we avoid this notation since it
       is generally not a genuine inverse (see ~ f1cocnv1 and ~ funcocnv2 for
       cases where it is a left or right-inverse).  This can be used to define
       a subset, e.g., ~ df-tan notates "the set of values whose cosine is a
       nonzero complex number" as ` ( ``' cos " ( CC \ { 0 } ) ) ` .
       </li>

       <li><p><b>Function application.</b>
       The symbols "( ` F `` x ` )" should be read "the value
       of (function) ` F ` at ` x ` " and has the same meaning as the more
       familiar but ambiguous notation F(x).  For example,
       ` ( cos `` 0 ) = 1 ` (see ~ cos0 ).  The left apostrophe notation
       originated with Peano and was adopted in Definition *30.01 of
       [WhiteheadRussell] p. 235, Definition 10.11 of [Quine] p. 68, and
       Definition 6.11 of [TakeutiZaring] p. 26.  See ~ df-fv .
       In the ASCII (input) representation there are spaces around the grave
       accent; there is a single accent when it is used directly,
       and it is doubled within comments.
       </li>

       <li><p><b>Infix and parentheses.</b>
       When a function that takes two classes and produces a class
       is applied as part of an infix expression, the expression is always
       surrounded by parentheses (see ~ df-ov ).
       For example, the ` + ` in ` ( 2 + 2 ) ` ; see ~ 2p2e4 .
       Function application is itself an example of this.
       Similarly, predicate expressions
       in infix form that take two or three wffs and produce a wff
       are also always surrounded by parentheses, such as
       ` ( ph -> ps ) ` , ` ( ph \/ ps ) ` , ` ( ph /\ ps ) ` , and
       ` ( ph <-> ps ) `
       (see ~ wi , ~ df-or , ~ df-an , and ~ df-bi respectively).
       In contrast, a binary relation (which compares two _classes_ and
       produces a _wff_) applied in an infix expression is _not_
       surrounded by parentheses.
       This includes set membership ` A e. B ` (see ~ wel ),
       equality ` A = B ` (see ~ df-cleq ),
       subset ` A C_ B ` (see ~ df-ss ), and
       less-than ` A < B ` (see ~ df-lt ).  For the general definition
       of a binary relation in the form ` A R B ` , see ~ df-br .
       For example, ` 0 < 1 ` (see ~ 0lt1 ) does not use parentheses.
       </li>

       <li><p><b>Unary minus.</b>
       The symbol ` -u ` is used to indicate a unary minus, e.g., ` -u 1 ` .
       It is specially defined because it is so commonly used.
       See ~ cneg .
       </li>

       <li><p><b>Function definition.</b>
       Functions are typically defined by first defining the constant symbol
       (using $c) and declaring that its symbol is a class with the
       label cNAME (e.g., ~ ccos ).
       The function is then defined labeled df-NAME; definitions
       are typically given using the maps-to notation (e.g., ~ df-cos ).
       Typically, there are other proofs such as its
       closure labeled NAMEcl (e.g., ~ coscl ), its
       function application form labeled NAMEval (e.g., ~ cosval ),
       and at least one simple value (e.g., ~ cos0 ).
       Another way to define functions is to use recursion (for more details
       about recursion see below).  For an example of how to define functions
       that aren't primitive recursive using recursion, see the Ackermann
       function definition ~ df-ack (which is based on the sequence builder
       ` seq `, see ~ df-seq ).
       </li>

       <li><p><b>Factorial.</b>
       The factorial function is traditionally a postfix operation,
       but we treat it as a normal function applied in prefix form, e.g.,
       ` ( ! `` 4 ) = ; 2 4 ` ( ~ df-fac and ~ fac4 ).
       </li>

       <li><p><b>Unambiguous symbols.</b>
       A given symbol has a single unambiguous meaning in general.
       Thus, where the literature might use the same symbol with different
       meanings, here we use different (variant) symbols for different
       meanings.  These variant symbols often have suffixes, subscripts,
       or underlines to distinguish them.  For example, here
       "` 0 ` " always means the value zero ( ~ df-0 ), while
       "` 0g ` " is the group identity element ( ~ df-0g ),
       "` 0. ` " is the poset zero ( ~ df-p0 ),
       "` 0p ` " is the zero polynomial ( ~ df-0p ),
       "` 0vec ` " is the zero vector in a normed subcomplex vector space
       ( ~ df-0v ), and
       "` .0. ` " is a class variable for use as a connective symbol
       (this is used, for example, in ~ p0val ).
       There are other class variables used as connective symbols
       where traditional notation would use ambiguous symbols, including
       "` .1. ` ", "` .+ ` ", "` .* ` ", and "` .|| ` ".
       These symbols are very similar to traditional notation, but because
       they are different symbols they eliminate ambiguity.
       </li>

       <li><p><b>ASCII representation of symbols.</b>
       We must have an ASCII representation for each symbol.
       We generally choose short sequences, ideally digraphs, and generally
       choose sequences that vaguely resemble the mathematical symbol.
       Here are some of the conventions we use when selecting an
       ASCII representation.

       <p>We generally do not include parentheses inside a symbol because
       that confuses text editors (such as emacs).
       Greek letters for wff variables always use the first two letters
       of their English names, making them easy to type and easy to remember.
       Symbols that almost look like letters, such as ` A. ` ,
       are often represented by that letter followed by a period.
       For example, "A." is used to represent ` A. ` ,
       "e." is used to represent ` e. ` , and
       "E." is used to represent ` E. ` .
       Single letters are now always variable names, so constants that are
       often shown as single letters are now typically preceded with "&#95;"
       in their ASCII representation, for example,
       "&#95;i" is the ASCII representation for the imaginary unit ` _i ` .
       A script font constant is often the letter
       preceded by "&#126;" meaning "curly", such as "&#126;P" to represent
       the power class ` ~P ` .

       <p>Originally, all setvar and class variables used only single letters
       a-z and A-Z, respectively.  A big change in recent years was to
       allow the use of certain symbols as variable names to make formulas
       more readable, such as a variable representing an additive group
       operation. The convention is to take the original constant token
       (in this case "+" which means complex number addition) and put
       a period in front of it to result in the ASCII representation of the
       variable ".+", shown as ` .+ ` , that can
       be used instead of say the letter "P" that had to be used before.

       <p>Choosing tokens for more advanced concepts that have no standard
       symbols but are represented by words in books, is hard. A few are
       reasonably obvious, like "Grp" for group and "Top" for topology,
       but often they seem to end up being either too long or too
       cryptic.  It would be nice if the math community came up with
       standardized short abbreviations for English math terminology,
       like they have more or less done with symbols, but that probably
       won't happen any time soon.

       <p>Another informal convention that we have somewhat followed, that is
       also not uncommon in the literature, is to start tokens with a
       capital letter for collection-like objects and lower case for
       function-like objects.  For example, we have the collections On
       (ordinal numbers), Fin, Prime, Grp, and we have the functions sin,
       tan, log, sup.  Predicates like Ord and Lim also tend to start
       with upper case, but in a sense they are really collection-like,
       e.g., Lim indirectly represents the collection of limit ordinals,
       but it cannot be an actual class since not all limit ordinals
       are sets.
       This initial upper versus lower case letter convention is sometimes
       ambiguous.  In the past there's been a debate about whether
       domain and range are collection-like or function-like, thus whether
       we should use Dom, Ran or dom, ran.  Both are used in the literature.
       In the end dom, ran won out for aesthetic reasons
       (Norm Megill simply just felt they looked nicer).
       </li>

       <li><p><b>Typography conventions.</b>
       Class symbols for functions (e.g., ` abs ` , ` sin ` )
       should usually not have leading or trailing blanks in their
       HTML representation.
       This is in contrast to class symbols for operations
       (e.g., ` gcd ` , ` sadd ` , ` eval ` ), which usually do
       include leading and trailing blanks in their representation.
       If a class symbol is used for a function as well as an operation
       (according to Definition ~ df-ov , each operation value can be
       written as function value of an ordered pair), the convention for its
       primary usage should be used, e.g., ` ( iEdg `` G ) ` versus
       ` ( V iEdg E ) ` for the edges of a graph ` G = <. V , E >. ` .
       </li>

       <li><p><b>LaTeX definitions.</b>
       Each token has a "LaTeX definition" which is used by the Metamath
       program to output tex files.  When writing LaTeX definitions,
       contributors should favor simplicity over perfection of the display, and
       should only use core LaTeX symbols or symbols from standard packages; if
       packages other than amssymb, amsmath, mathtools, mathrsfs, phonetic are
       needed, this should be discussed.  A useful resource is
       <a href="https://www.ctan.org/pkg/comprehensive">The Comprehensive LaTeX
       Symbol List</a>.
       </li>

       <li><p><b>Number construction independence.</b>
       There are many ways to model complex numbers.
       After deriving the complex number postulates we
       reintroduce them as new axioms on top of set theory.
       This lets us easily identify which axioms are needed
       for a particular complex number proof, without the obfuscation
       of the set theory used to derive them.
       This also lets us be independent of the specific construction,
       which we believe is valuable.
       See ~ mmcomplex.html for details.
       Thus, for example, we don't allow the use of ` (/) e/ CC ` ,
       as handy as that would be, because that would be
       construction-specific.  We want proofs about ` CC ` to be independent
       of whether or not ` (/) e. CC ` .
       </li>

       <li><p><b>Minimize hypotheses.</b>
       In most cases we try to minimize hypotheses, so that the statement be
       more general and easier to use.  There are exceptions.  For example, we
       intentionally add hypotheses if they help make proofs independent of a
       particular construction (e.g., the contruction of the complex numbers
       ` CC ` ).  We also intentionally add hypotheses for many real and
       complex number theorems to expressly state their domains even when they
       are not needed.  For example, we could show that
       ` |- ( A < B -> B =/= A ) ` without any hypotheses, but we require that
       theorems using this result prove that ` A ` and ` B ` are real numbers,
       so that the statement we use is ~ ltnei .  Here are the reasons as
       discussed in ~ https://groups.google.com/g/metamath/c/2AW7T3d2YiQ :
       <ol>
       <li>Having the hypotheses immediately shows the intended domain of
       applicability (is it ` RR ` , ` RR* ` , ` _om ` , or something else?),
       without having to trace back to definitions.</li>
       <li>Having the hypotheses forces the intended use of the statement,
       which generally is desirable.</li>
       <li>Many out-of-domain values are dependent on contingent details of
       definitions, so hypothesis-free theorems would be non-portable and
       "brittle".</li>
       <li>Only a few theorems can have their hypotheses removed in this
       fashion, due to coincidences for our particular set-theoretical
       definitions.  The poor user (especially a novice learning, e.g., real
       number arithmetic) is going to be confused not knowing when hypotheses
       are needed and when they are not.  For someone who has not traced back
       the set-theoretical foundations of the definitions, it is seemingly
       random and is not intuitive at all.</li>
       <li>Ultimately, this is a matter of consensus, and the consensus in
       the group was in favor of keeping sometimes redundant hypotheses.</li>
       </ol>
       </li>

       <li><p><b>Natural numbers.</b>
       There are different definitions of "natural" numbers in the literature.
       We use ` NN ` ( ~ df-nn ) for the set of positive integers starting
       from 1, and ` NN0 ` ( ~ df-n0 ) for the set of nonnegative integers
       starting at zero.
       </li>

       <li><p><b>Decimal numbers.</b>
       Numbers larger than nine are often expressed in base 10 using the
       decimal constructor ~ df-dec , e.g., ` ; ; ; 4 0 0 1 ` (see ~ 4001prm
       for a proof that 4001 is prime).
       </li>

       <li><p><b>Theorem forms.</b>
       We will use the following descriptive terms to categorize theorems:
       <ul>
       <li>A theorem is in <b>"closed form"</b> if it has no $e hypotheses
       (e.g., ~ unss ).  The term "tautology" is also used, especially in
       propositional calculus.  This form was formerly called "theorem form"
       or "closed theorem form".</li>
       <li>A theorem is in <b>"deduction form"</b> (or is a "deduction") if it
       has zero or more $e hypotheses, and the hypotheses and the conclusion
       are implications that share the same antecedent.  More precisely, the
       conclusion is an implication with a wff variable as the antecedent
       (usually ` ph `), and every hypothesis ($e statement) is either:
       <ol>
       <li>an implication with the same antecedent as the conclusion, or</li>
       <li>a definition.  A definition can be for a class variable (this is a
       class variable followed by ` = `, e.g., the definition of ` D ` in
       ~ lhop ) or a wff variable (this is a wff variable followed by
       ` <-> `); class variable definitions are more common.</li>
       </ol>
       In practice, a proof of a theorem in deduction form will also contain
       many steps that are implications where the antecedent is either that
       wff variable (usually ` ph `) or is a conjunction ` ( ph i^i ... ) `
       including that wff variable (` ph `).  E.g., ~ a1d , ~ unssd .
       Although they are no real deductions, theorems without $e hypotheses,
       but in the form ` ( ph -> ... ) `, are also said to be in "deduction
       form".  Such theorems usually have a two step proof, applying ~ a1i to a
       given theorem, and are used as convenience theorems to shorten many
       proofs.  E.g., ~ eqidd , which is used more than 1500 times. </li>
       <li> A theorem is in <b>"inference form"</b> (or is an "inference") if
       it has one or more $e hypotheses, but is not in deduction form,
       i.e., there is no common antecedent (e.g., ~ unssi ).</li>
       </ul>

       <p>Any theorem whose conclusion is an implication has an <b>associated
       inference</b>, whose hypotheses are the hypotheses of that theorem
       together with the antecedent of its conclusion, and whose conclusion is
       the consequent of that conclusion.  When both theorems are in set.mm,
       then the associated inference is often labeled by adding the suffix "i"
       to the label of the original theorem (for instance, ~ con3i is the
       inference associated with ~ con3 ).  The inference associated with a
       theorem is easily derivable from that theorem by a simple use of
       ~ ax-mp .  The other direction is the subject of the Deduction Theorem
       discussed below.  We may also use the term "associated inference" when
       the above process is iterated.  For instance, ~ syl is <em>an</em>
       inference associated with ~ imim1 because it is <em>the</em> inference
       associated with ~ imim1i which is itself <em>the</em> inference
       associated with ~ imim1 .

       <p>"Deduction form" is the preferred form for theorems because this form
       allows to easily use the theorem in places where (in traditional
       textbook formalizations) the standard Deduction Theorem (see below)
       would be used. We call this approach <b>"deduction style"</b>.
       In contrast, we usually avoid theorems in "inference form" when that
       would end up requiring us to use the deduction theorem.

       <p>Deductions have a label suffix of "d", especially if there are other
       forms of the same theorem (e.g., ~ pm2.43d ).  The labels for inferences
       usually have the suffix "i" (e.g., ~ pm2.43i ).  The labels of theorems
       in "closed form" would have no special suffix (e.g., ~ pm2.43 ) or, if
       the non-suffixed label is already used, then we add the suffix "t" (for
       "theorem" or "tautology", e.g., ~ ancomst or ~ nfimt ).  When an
       inference with an "is a set" hypothesis (e.g., ` A e. _V `) is converted
       to a theorem (in closed form) by replacing the hypothesis with an
       antecedent of the form ` ( A e. V -> `, we sometimes suffix the closed
       form with "g" (for "more general") as in ~ uniex versus ~ uniexg .  In
       this case, the inference often has no suffix "i".

       <p>When submitting a new theorem, a revision of a theorem, or an upgrade
       of a theorem from a Mathbox to the Main database, please use the
       general form to be the default form of the theorem, without the suffix
       "g" . For example, "brresg" lost its suffix "g" when it was revised for
       some other reason, and now it is ~ brres .  Its inference form which was
       the original "brres", now is ~ brresi .  The same holds for the suffix
       "t".
       </li>

       <li><p><b>Deduction theorem.</b>
       The Deduction Theorem is a metalogical theorem that provides an
       algorithm for constructing a proof of a theorem from the proof of its
       corresponding deduction (its associated inference).  See for instance
       Theorem 3 in [Margaris] p. 56.  In ordinary mathematics, no one actually
       carries out the algorithm, because (in its most basic form) it involves
       an exponential explosion of the number of proof steps as more hypotheses
       are eliminated.  Instead, in ordinary mathematics the Deduction Theorem
       is invoked simply to claim that something can be done in principle,
       without actually doing it.  For more details, see ~ mmdeduction.html .
       The Deduction Theorem is a metalogical theorem that cannot be applied
       directly in Metamath, and the explosion of steps would be a problem
       anyway, so alternatives are used.  One alternative we use sometimes is
       the "weak deduction theorem" ~ dedth , which works in certain cases in
       set theory.  We also sometimes use ~ dedhb .  However, the primary
       mechanism we use today for emulating the deduction theorem is to write
       proofs in deduction form (aka "deduction style") as described earlier;
       the prefixed ` ph -> ` mimics the context in a deduction proof system.
       In practice this mechanism works very well.  This approach is described
       in the deduction form and natural deduction page ~ mmnatded.html ; a
       list of translations for common natural deduction rules is given in
       ~ natded .
       </li>

       <li><p><b>Recursion.</b>
       We define recursive functions using various "recursion constructors".
       These allow to define, with compact direct definitions, functions
       that are usually defined in textbooks with indirect self-referencing
       recursive definitions.  This produces compact definition and much
       simpler proofs, and greatly reduces the risk of creating unsound
       definitions.  Examples of recursion constructors include
       ` recs ( F ) ` in ~ df-recs , ` rec ( F , I ) ` in ~ df-rdg ,
       ` seqom ( F , I ) ` in ~ df-seqom , and ` seq M ( .+ , F ) ` in
       ~ df-seq .  These have characteristic function ` F ` and initial value
       ` I ` .  ( ` gsum ` in ~ df-gsum isn't really designed for arbitrary
       recursion, but you could do it with the right magma.)  The logically
       primary one is ~ df-recs , but for the "average user" the most useful
       one is probably ~ df-seq - provided that a countable sequence is
       sufficient for the recursion.
       </li>

       <li><p><b>Extensible structures.</b>
       Mathematics includes many structures such as ring, group, poset, etc.
       We define an "extensible structure" which is then used to define group,
       ring, poset, etc.  This allows theorems from more general structures
       (groups) to be reused for more specialized structures (rings) without
       having to reprove them.  See ~ df-struct .
       </li>

       <li><p><b>Undefined results and "junk theorems".</b>
       Some expressions are only expected to be meaningful in certain contexts.
       For example, consider Russell's definition description binder iota,
       where ` ( iota x ph ) ` is meant to be "the ` x ` such that ` ph ` "
       (where ` ph ` typically depends on x).
       What should that expression produce when there is no such ` x ` ?
       In set.mm we primarily use one of two approaches.
       One approach is to make the expression evaluate to the empty set
       whenever the expression is being used outside of its expected context.
       While not perfect, it makes it a bit more clear when something
       is undefined, and it has the advantage that it makes more
       things equal outside their domain which can remove hypotheses when
       you feel like exploiting these so-called junk theorems.
       Note that Quine does this with iota (his definition of iota
       evaluates to the empty set when there is no unique value of ` x ` ).
       Quine has no problem with that and we don't see why we should,
       so we define iota exactly the same way that Quine does.
       The main place where you see this being systematically exploited is in
       "reverse closure" theorems like ` A e. ( F `` B ) -> B e. dom F ` ,
       which is useful when ` F ` is a family of sets. (by this we
       mean it's a set set even in a type theoretic interpretation.)

       <p>The second approach uses "(New usage is discouraged.)" to prevent
       unintentional uses of certain properties.
       For example, you could define some construct df-NAME whose
       usage is discouraged, and prove only the specific properties
       you wish to use (and add those proofs to the list of permitted uses
       of "discouraged" information). From then on, you can only use
       those specific properties without a warning.
       Other approaches often have hidden problems.
       For example, you could try to "not define undefined terms"
       by creating definitions like ${ $d ` y x ` $.  $d ` y ph ` $.
       df-iota $a ` |- ( E! x ph -> ( iota x ph ) = U. { x | ph } ) ` $. $}.
       This will be rejected by the definition checker, but the bigger
       theoretical reason to reject this axiom is that it breaks equality -
       the metatheorem ` ( x = y -> ` P(x) ` = ` P(y) ` ) ` fails
       to hold if definitions don't unfold without some assumptions.
       (That is, ~ iotabidv is no longer provable and must be added
       as an axiom.) It is important for every syntax constructor to
       satisfy equality theorems *unconditionally*, e.g., expressions
       like ` ( 1 / 0 ) = ( 1 / 0 ) ` should not be rejected.
       This is forced on us by the context free term
       language, and anything else requires a lot more infrastructure
       (e.g., a type checker) to support without making everything else
       more painful to use.

       <p>Another approach would be to try to make nonsensical
       statements syntactically invalid, but that can create its own
       complexities; in some cases that would make parsing itself undecidable.
       In practice this does not seem to be a serious issue.
       No one does these things deliberately in "real" situations,
       and some knowledgeable people (such as Mario Carneiro)
       have never seen this happen accidentally.
       Norman Megill doesn't agree that these "junk" consequences are
       necessarily bad anyway, and they can significantly shorten proofs
       in some cases. This database would be much larger if, for example,
       we had to condition ~ fvex on the argument being in the domain
       of the function. It is impossible to derive a contradiction
       from sound definitions (i.e. that pass the definition check),
       assuming ZFC is consistent, and he doesn't see the point of all the
       extra busy work and huge increase in set.mm size that would result
       from restricting *all* definitions.
       So instead of implementing a complex system to counter a
       problem that does not appear to occur in practice, we use
       a significantly simpler set of approaches.
       </li>

       <li><p><b>Organizing proofs.</b>
       Humans have trouble understanding long proofs.  It is often preferable
       to break longer proofs into smaller parts (just as with traditional
       proofs).  In Metamath this is done by creating separate proofs of the
       separate parts.

       A proof with the sole purpose of supporting a final proof is a lemma;
       the naming convention for a lemma is the final proof label followed by
       "lem", and a number if there is more than one.  E.g., ~ sbthlem1 is the
       first lemma for ~ sbth .  The comment should begin with "Lemma for",
       followed by the final proof label, so that it can be suppressed in
       theorem lists (see the Metamath program "MM> WRITE THEOREM_LIST"
       command).

       Also, consider proving reusable results separately, so that others will
       be able to easily reuse that part of your work.
       </li>

       <li><p><b>Limit proof size.</b>
       It is often preferable to break longer proofs into
       smaller parts, just as you would do with traditional proofs.
       One reason is that humans have trouble understanding long proofs.
       Another reason is that it's generally best to prove
       reusable results separately,
       so that others will be able to easily reuse them.
       Finally, the Metamath program "MM-PA> MINIMIZE__WITH *" command can take
       much longer with very long proofs.
       We encourage proofs to be no more than 200 essential steps, and
       generally no more than 500 essential steps,
       though these are simply guidelines and not hard-and-fast rules.
       Much smaller proofs are fine!
       We also acknowledge that some proofs, especially autogenerated ones,
       should sometimes not be broken up (e.g., because
       breaking them up might be useless and inefficient due to many
       interconnections and reused terms within the proof).
       In Metamath, breaking up longer proofs is done by creating multiple
       separate proofs of separate parts.
       A proof with the sole purpose of supporting a final proof is a
       lemma; the naming convention for a lemma is the final proof's name
       followed by "lem", and a number if there is more than one. E.g.,
       ~ sbthlem1 is the first lemma for ~ sbth .
       </li>

       <li><p><b>Proof stubs.</b>
       It's sometimes useful to record partial proof results, e.g.,
       incomplete proofs or proofs that depend on something else not fully
       proven.
       Some systems (like Lean) support a "sorry" axiom, which lets you assert
       anything is true, but this can quickly run into trouble, because
       the Metamath tooling is smart and may end up using it
       to prove everything.
       If you want to create a proof based on some other claim, without
       proving that claim, you can choose to define the claim as an axiom.
       If you temporarily define a claim as an axiom, we encourage you to
       include "Temporarily provided as axiom" in its comment.
       Such incomplete work will generally only be accepted in a mathbox
       until the rest of the work is complete.
       When you're working on your personal copy of the database
       you can use "?" in proofs to indicate an unknown step.
       However, since proofs with "?" will (obviously) fail
       verification, we don't accept proofs with unknown steps in
       the public database.
       </li>

       <li><p><b>Hypertext links.</b>
       We strongly encourage comments to have many links to related material,
       with accompanying text that explains the relationship.  These can help
       readers understand the context.  Links to other statements, or to
       HTTP/HTTPS URLs, can be inserted in ASCII source text by prepending a
       space-separated tilde (e.g., " ~~ df-prm " results in " ~ df-prm ").
       When the Metamath program is used to generate HTML, it automatically
       inserts hypertext links for syntax used (e.g., every symbol used), every
       axiom and definition depended on, the justification for each step in a
       proof, and to both the next and previous assertions.
       </li>

       <li><p><b>Hypertext links to section headers.</b>
       Some section headers have text under them that describes or explains the
       section.  However, they are not part of the description of axioms or
       theorems, and there is no way to link to them directly.  To provide for
       this, section headers with accompanying text (indicated with "*"
       prefixed to ~ mmtheorems.html#mmdtoc entries) have an anchor in
       ~ mmtheorems.html whose name is the first $a or $p statement that
       follows the header.  For example there is a glossary under the section
       heading called GRAPH THEORY.  The first $a or $p statement that follows
       is ~ cedgf .  To reference it we link to the anchor using a
       space-separated tilde followed by the space-separated link
       mmtheorems.html#cedgf, which will become the hyperlink
       ~ mmtheorems.html#cedgf .  Note that no theorem in set.mm is allowed to
       begin with "mm" (this is enforced by the Metamath program "MM> VERIFY
       MARKUP" command).  Whenever the program sees a tilde reference beginning
       with "http:", "https:", or "mm", the reference is assumed to be a link
       to something other than a statement label, and the tilde reference is
       used as is.  This can also be useful for relative links to other pages
       such as ~ mmcomplex.html .
       </li>

       <li><p><b>Bibliography references.</b>
       Please include a bibliographic reference to any external material used.
       A name in square brackets in a comment indicates a
       bibliographic reference. The full reference must be of the form
       KEYWORD IDENTIFIER? NOISEWORD(S)* &#91;AUTHOR(S)&#93; p. NUMBER -
       note that this is a very specific form that requires a page number.
       There should be no comma between the author reference and the
       "p." (a constant indicator).
       Whitespace, comma, period, or semicolon should follow NUMBER.
       An example is Theorem 3.1 of [Monk1] p. 22,
       The KEYWORD, which is not case-sensitive,
       must be one of the following: Axiom, Chapter, Compare, Condition,
       Corollary, Definition, Equation, Example, Exercise, Figure, Item,
       Lemma, Lemmas, Line, Lines, Notation, Part, Postulate, Problem,
       Property, Proposition, Remark, Rule, Scheme, Section, or Theorem.
       The IDENTIFIER is optional, as in for example
       "Remark in [Monk1] p. 22".
       The NOISEWORDS(S) are zero or more from the list: from, in, of, on.
       The AUTHOR(S) must be present in the file identified with the
       htmlbibliography assignment (e.g., mmset.html) as a named anchor
       (NAME=).  If there is more than one document by the same author(s),
       add a numeric suffix (as shown here).
       The NUMBER is a page number, and may be any alphanumeric string such as
       an integer or Roman numeral.
       Note that we _require_ page numbers in comments for individual
       $a or $p statements.  We allow names in square brackets without
       page numbers (a reference to an entire document) in
       heading comments.
       If this is a new reference, please also add it to the
       "Bibliography" section of mmset.html.
       (The file mmbiblio.html is automatically rebuilt, e.g.,
       using the Metamath program "MM> WRITE BIBLIOGRAPHY" command.)
       </li>

       <li><p><b>Acceptable shorter proofs.</b>
       Shorter proofs are welcome, and any shorter proof we accept
       will be acknowledged in the theorem description.  However,
       in some cases a proof may be "shorter" or not depending on
       how it is formatted.  This section provides general guidelines.

       <p>Usually we automatically accept shorter proofs that (1)
       shorten the set.mm file (with compressed proofs), (2) reduce
       the size of the HTML file generated with SHOW STATEMENT xx
       / HTML, (3) use only existing, unmodified theorems in the
       database (the order of theorems may be changed, though), and
       (4) use no additional axioms.
       Usually we will also automatically accept a _new_ theorem
       that is used to shorten multiple proofs, if the total size
       of set.mm (including the comment of the new theorem, not
       including the acknowledgment) decreases as a result.

       <p>In borderline cases, we typically place more importance on
       the number of compressed proof steps and less on the length
       of the label section (since the names are in principle
       arbitrary).  If two proofs have the same number of compressed
       proof steps, we will typically give preference to the one
       with the smaller number of different labels, or if these
       numbers are the same, the proof with the smaller number of
       symbols in the proof display on an HTML page containing the
       theorem.  If the difference in size is so insignificant that
       it is hardly detectable to a human reader, we prefer to keep the
       older proof, in honor of the first author coming up with a short
       proof.  The community may decide to override these rules
       after a discussion, if non-technical reasons like aesthetics
       prefer a particular version.

       <p>Some theorems have a longer proof than necessary in order
       to avoid the use of certain axioms.  To indicate this, a
       <code>$j usage</code>
       comment should be used just after the proof, for example
       <code>$<span></span>( $<span></span>j usage '19.21v' avoids
       'ax-6' 'ax-7' 'ax-12'; $<span></span>)</code>.</p>

       <p>Other theorems have a longer proof than necessary for
       pedagogical or other reasons.  These theorems will (or should) have
       a "(Proof modification is discouraged.)" tag in their
       description.  For example, ~ idALT shows a proof directly from
       axioms.  Shorter proofs for such cases won't be accepted,
       of course, unless the criteria described continues to be
       satisfied.</p>
       </li>

       <li><p><b>Information on syntax, axioms, and definitions.</b>
       For a hyperlinked list of syntax, axioms, and definitions, see
       ~ mmdefinitions.html .
       If you have questions about a specific symbol or axiom, it is best
       to go directly to its definition to learn more about it.
       The generated HTML for each theorem and axiom includes hypertext
       links to each symbol's definition.
       </li>

       <li><p><b>Reserved symbols: 'LETTER.</b>
       Some symbols are reserved for potential future use.
       Symbols with the pattern 'LETTER are reserved for possibly
       representing characters (this is somewhat similar to Lisp).
       We would expect '\n to represent newline, 'sp for space, and perhaps
       '\x24 for the dollar character.
       </li>
       </ul>

       <p><b>The challenge of varying mathematical conventions</b>

       <br><br>

       We try to follow mathematical conventions, but in many cases
       different texts use different conventions.
       In those cases we pick some reasonably common convention and stick to
       it.
       We have already mentioned that the term "natural number" has
       varying definitions (some start from 0, others start from 1), but
       that is not the only such case.

       A useful example is the set of metavariables used to represent
       arbitrary well-formed formulas (wffs).
       We use an open phi, &#x3c6;, to represent the first arbitrary wff in an
       assertion with one or more wffs; this is a common convention and
       this symbol is easily distinguished from the empty set symbol.
       That said, it is impossible to please everyone or simply "follow
       the literature" because there are many different conventions for
       a variable that represents any arbitrary wff.
       To demonstrate the point,
       here are some conventions for variables that represent an arbitrary
       wff and some texts that use each convention:

       <ul>
       <li>open phi &#x3c6; (and so on): Tarski's papers,
       Rasiowa &amp; Sikorski's
       <i>The Mathematics of Metamathematics</i> (1963),
       Monk's <i>Introduction to Set Theory</i> (1969),
       Enderton's <i>Elements of Set Theory</i> (1977),
       Bell &amp; Machover's <i>A Course in Mathematical Logic</i> (1977),
       Jech's <i>Set Theory</i> (1978),
       Takeuti &amp; Zaring's
       <i>Introduction to Axiomatic Set Theory</i> (1982).
       <li>closed phi &#x3d5; (and so on):
       Levy's <i>Basic Set Theory</i> (1979),
       Kunen's <i>Set Theory</i> (1980),
       Paulson's <i>Isabelle: A Generic Theorem Prover</i> (1994),
       Huth and Ryan's <i>Logic in Computer Science</i> (2004/2006).
       <li>Greek &alpha;, &beta;, &gamma;:
       Duffy's <i>Principles of Automated Theorem Proving</i> (1991).
       <li>Roman A, B, C:
       Kleene's <i>Introduction to Metamathematics</i> (1974),
       Smullyan's <i>First-Order Logic</i> (1968/1995).
       <li>script A, B, C:
       Hamilton's <i>Logic for Mathematicians</i> (1988).
       <li>italic A, B, C:
       Mendelson's <i>Introduction to Mathematical Logic</i> (1997).
       <li>italic P, Q, R:
       Suppes's <i>Axiomatic Set Theory</i> (1972),
       Gries and Schneider's <i>A Logical Approach to Discrete Math</i>
       (1993/1994),
       Rosser's <i>Logic for Mathematicians</i> (2008).
       <li>italic p, q, r:
       Quine's <i>Set Theory and Its Logic</i> (1969),
       Kuratowski &amp; Mostowski's <i>Set Theory</i> (1976).
       <li>italic X, Y, Z:
       Dijkstra and Scholten's
       <i>Predicate Calculus and Program Semantics</i> (1990).
       <li>Fraktur letters:
       Fraenkel et. al's <i>Foundations of Set Theory</i> (1973).
       </ul>

       <p><b>Distinctness or freeness</b>

       <br><br>

       Here are some conventions that address distinctness or freeness of a
       variable:

       <ul>
       <li> ` F/ x ph ` is read " ` x ` is not free in (wff) ` ph ` ";
       see ~ df-nf (whose description has some important technical
       details).  Similarly, ` F/_ x A ` is read ` x ` is not free in (class)
       ` A ` , see ~ df-nfc .</li>

       <li>"$d ` x y ` $." should be read "Assume ` x ` and ` y ` are distinct
       variables."</li>

       <li>"$d ` ph x ` $." should be read "Assume ` x ` does not occur in
       ` phi `."  Sometimes a theorem is proved using ` F/ x ph `  ( ~ df-nf )
       in place of "$d ` ph x ` $." when a more general result is desired;
       ~ ax-5 can be used to derive the $d version.  For an example of
       how to get from the $d version back to the $e version, see the
       proof of ~ euf from ~ eu6 .</li>

       <li>"$d ` A x ` $." should be read "Assume ` x ` is not a variable
       occurring in class ` A `."</li>

       <li>"$d ` A x ` $.  $d ` ps x ` $.
       $e |- ` ( x = A -> ( ph <-> ps ) ) ` $." is an idiom often used instead
       of explicit substitution, meaning "Assume ` psi ` results from the
       proper substitution of ` A ` for ` x ` in ` phi `."  Therefore, we often
       use the term "implicit substitution" for such a hypothesis.</li>

       <li>Class and wff variables should appear at the beginning of distinct
       variable conditions, and setvars should be in alphabetical order.
       E.g., "$d ` Z x y ` $.",  "$d ` ps a x ` $.".  This convention should
       be applied for new theorems (formerly, the class and wff variables
       mostly appear at the end) and will be assured by a formatter in the
       future.</li>

       <li>" ` |- ( -. A. x x = y -> ... ) ` " occurs early in some cases, and
       should be read "If x and y are distinct
       variables, then..."  This antecedent provides us with a technical
       device (called a "distinctor" in Section 7 of [Megill] p. 444)
       to avoid the need for the
       $d statement early in our development of predicate calculus, permitting
       unrestricted substitutions as conceptually simple as those in
       propositional calculus.  However, the $d eventually becomes a
       requirement, and after that this device is rarely used.</li>
       </ul>

       <p>There is a general technique to replace a <tt>$d x A</tt> or
       <tt>$d x ph</tt> condition in a theorem with the corresponding
       ` F/_ x A ` or ` F/ x ph ` ; here it is.
       ` |- ` T[x, A] where $d ` x A `,
       and you wish to prove ` |- F/_ x A => |- ` T[x, A].
       You apply the theorem substituting ` y ` for ` x ` and ` A ` for ` A ` ,
       where ` y ` is a new dummy variable, so that
       <tt>$d y A</tt> is satisfied.
       You obtain ` |- ` T[y, A], and apply chvar to obtain ` |- `
       T[x, A] (or just use ~ mpbir if T[x, A] binds ` x `).
       The side goal is ` |- ( x = y -> ( ` T[y, A] ` <-> ` T[x, A] ` ) ) ` ,
       where you can use equality theorems, except
       that when you get to a bound variable you use a non-dv bound variable
       renamer theorem like ~ cbval . The section
       ~ mmtheorems32.html#mm3146s also describes the
       metatheorem that underlies this.

       <p><b>Additional rules for definitions</b>

       <p>Standard Metamath verifiers do not distinguish between axioms and
       definitions (both are $a statements).
       In practice, we require that definitions (1) be conservative
       (a definition should not allow an expression
       that previously qualified as a wff but was not provable
       to become provable) and be eliminable
       (there should exist an algorithmic method for converting any
       expression using the definition into
       a logically equivalent expression that previously qualified as a wff).
       To ensure this, we have additional rules on almost all definitions
       ($a statements with a label that does not begin with ax-).
       These additional rules are not applied in a few cases where they
       are too strict ( ~ df-bi , ~ df-clab , ~ df-cleq , and ~ df-clel );
       see those definitions for more information.
       These additional rules for definitions are checked by at least
       mmj2's definition check (see
       <A HREF="https://github.com/digama0/mmj2/blob/master/"
       >mmj2 master</a> file mmj2jar/macros/definitionCheck.js).
       This definition check relies on the database being very much like
       set.mm, down to the names of certain constants and types, so it
       cannot apply to all Metamath databases... but it is useful in set.mm.
       In this definition check, a $a-statement with a given label and
       typecode ` |- ` passes the test if and only if it
       respects the following rules (these rules require that we have
       an unambiguous tree parse, which is checked separately):

       <ol>
       <li><p>The expression must be a biconditional or an equality (i.e. its
       root-symbol must be ` <-> ` or ` = `).
       If the proposed definition passes this first rule, we then
       define its definiendum as its left hand side (LHS) and
       its definiens as its right hand side (RHS).
       We define the *defined symbol* as the root-symbol of the LHS.
       We define a *dummy variable* as a variable occurring
       in the RHS but not in the LHS.
       Note that the "root-symbol" is the root of the considered tree;
       it need not correspond to a single token in the database
       (e.g., see ~ w3o or ~ wsb ).
       </li>
       <li><p>The defined expression must not appear in any statement
       between its syntax axiom ($a ` wff `) and its definition,
       and the defined expression must not be used in its definiens.
       See ~ df-3an for an example where the same symbol is used in
       different ways (this is allowed).
       </li>
       <li><p>No two variables occurring in the LHS may share a
       disjoint variable (DV) condition.
       </li>
       <li><p>All dummy variables are required to be disjoint from any
       other (dummy or not) variable occurring in this labeled expression.
       </li>
       <li><p>Either
       <br>(a) there must be no non-setvar dummy variables, or
       <br>(b) there must be a justification theorem.
       <p>The justification theorem must be of form
       ` |- ( ` definiens root-symbol definiens' ` ) `
       where definiens' is definiens but the dummy variables are all
       replaced with other unused dummy variables of the same type.
       Note that root-symbol is ` <-> ` or ` = ` , and that setvar
       variables are simply variables with the ` setvar ` typecode.
       </li>
       <li><p>One of the following must be true:
       <br>(a) there must be no setvar dummy variables,
       <br>(b) there must be a justification theorem as described in rule 5, or
       <br>(c) if there are setvar dummy variables, every one must not be free.
       <p>That is, it must be true that
       ` ( ph -> A. x ph ) ` for each setvar dummy variable ` x `
       where ` ph ` is the definiens.
       We use two different tests for nonfreeness; one must succeed
       for each setvar dummy variable ` x ` .
       The first test requires that the setvar dummy variable ` x `
       be syntactically bound
       (this is sometimes called the "fast" test, and this implies
       that we must track binding operators).
       The second test requires a successful
       search for the directly-stated proof of ` ( ph -> A. x ph ) `
       Part c of this rule is how most setvar dummy variables
       are handled.
       </li>
       </ol>

       <p>Rule 3 may seem unnecessary, but it is needed.
       Without this rule, you can define something like
       <pre>
       cbar $a wff Foo x y $.
       ${ $d x y $. df-foo $a |- ( Foo x y &lt;-&gt; x = y ) $. $}</pre>
       and now "Foo x x" is not eliminable;
       there is no way to prove that it means anything in particular,
       because the definitional theorem that is supposed to be
       responsible for connecting it to the original language wants
       nothing to do with this expression, even though it is well formed.

       <p>A justification theorem for a definition (if used this way)
       must be proven before the definition that depends on it.
       One example of a justification theorem is ~ vjust .
       Definition ~ df-v ` |- _V = { x | x = x } ` is justified
       by the justification theorem ~ vjust
       ` |- { x | x = x } = { y | y = y }  ` .
       Another example of a justification theorem is ~ trujust ;
       Definition ~ df-tru ` |- ( T. <-> ( A. x x = x -> A. x x = x ) ) `
       is justified by ~ trujust ` |- ( ( A. x x = x -> A. x x = x ) <->
       ( A. y y = y -> A. y y = y ) ) ` .

       <p>Here is more information about our processes for checking and
       contributing to this work:

       <ul>
       <li><p><b>Multiple verifiers.</b>
       This entire file is verified by multiple independently-implemented
       verifiers when it is checked in, giving us extremely high
       confidence that all proofs follow from the assumptions.
       The checkers also check for various other problems such as
       overly long lines.
       </li>

       <li><p><b>Discouraged information.</b>
       A separate file named "discouraged" lists all
       discouraged statements and uses of them, and this file is checked.
       If you change the use of discouraged things, you will need to change
       this file.
       This makes it obvious when there is a change to anything discouraged
       (triggering further review).
       </li>

       <li><p><b>LRParser check.</b>
       Metamath verifiers ensure that $p statements follow from previous
       $a and $p statements.
       However, by itself the Metamath language permits certain kinds of
       syntactic ambiguity that we choose to avoid in this database.
       Thus, we require that this database unambiguously parse
       using the "LRParser" check (implemented by at least mmj2).
       (For details, see <A
       HREF="https://github.com/digama0/mmj2/blob/master/"
       >mmj2 master</A> file src/mmj/verify/LRParser.java).
       This check
       <A HREF="https://github.com/metamath/set.mm/pull/754"
       >counters, for example, a devious ambiguous construct
       developed by saueran at oregonstate dot edu</A>
       posted on Mon, 11 Feb 2019 17:32:32 -0800 (PST)
       based on creating definitions with mismatched parentheses.
       <!-- Devious Construct:
       ${
       wleftp $a wff ( ( ph ) $.
       wbothp $a wff ( ph ) $.
       df-leftp $a |- ( ( ( ph ) <-> -. ph ) $.
       df-bothp $a |- ( ( ph ) <-> ph ) $.
       anything $p |- ph $=
       ( wbothp wn wi wleftp df-leftp biimpi df-bothp mpbir mpbi simplim
       ax-mp) ABZAMACZDZCZMOEZOCQAEZNDZRNAFGSHIOFJMNKLAHJ $.
       $}
       -->

       <li><p><b>Proposing specific changes.</b>
       Please propose specific changes as pull requests (PRs) against the
       "develop" branch of set.mm, at:
       ~ https://github.com/metamath/set.mm/tree/develop .
       </li>

       <li><p><b>Community.</b>
       We encourage anyone interested in Metamath to join our mailing list:
       ~ https://groups.google.com/g/metamath .
       </li>
       </ul>
       </HTML>

       (Contributed by the Metamath team, 27-Dec-2016.)  Date of last revision.
       (Revised by the Metamath team, 23-Oct-2025.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    conventions $p |- ph $=
      (  ) B $.
  $}

  ${
    conventions-labels.1 $e |- ph $.
    $(
       <HTML>
       <p>
       The following gives conventions used in the Metamath Proof Explorer
       (MPE, set.mm) regarding labels.
       For other conventions, see ~ conventions and links therein.
       </p>

       <p>
       Every statement has a unique identifying label, which serves the
       same purpose as an equation number in a book.
       We use various label naming conventions to provide
       easy-to-remember hints about their contents.
       Labels are not a 1-to-1 mapping, because that would create
       long names that would be difficult to remember and tedious to type.
       Instead, label names are relatively short while
       suggesting their purpose.
       Names are occasionally changed to make them more consistent or
       as we find better ways to name them.
       Here are a few of the label naming conventions:
       </p>

       <ul>
       <li><b>Axioms, definitions, and wff syntax.</b>
       As noted earlier, axioms are named "ax-NAME",
       proofs of proven axioms are named "axNAME", and
       definitions are named "df-NAME".
       Wff syntax declarations have labels beginning with "w"
       followed by short fragment suggesting its purpose.
       </li>

       <li><b>Hypotheses.</b>
       Hypotheses have the name of the final axiom or theorem, followed by
       ".", followed by a unique id (these ids are usually consecutive integers
       starting with 1, e.g., for ~ rgen "rgen.1 $e |- ( x e. A -> ph ) $."
       or letters corresponding to the (main) class variable used in the
       hypothesis, e.g., for ~ mdet0 : "mdet0.d $e |- D = ( N maDet R ) $.").
       </li>

       <li><b>Common names.</b>
       If a theorem has a well-known name, that name (or a short version of it)
       is sometimes used directly. Examples include
       ~ barbara and ~ stirling .
       </li>

       <li><b>Principia Mathematica.</b>
       Proofs of theorems from Principia Mathematica often use a special
       naming convention: "pm" followed by its identifier.
       For example, Theorem *2.27 of [WhiteheadRussell] p. 104 is named
       ~ pm2.27 .
       </li>

       <li><b>19.x series of theorems.</b>
       Similar to the conventions for the theorems from Principia Mathematica,
       theorems from Section 19 of [Margaris] p. 90 often use a special naming
       convention: "19." resp. "r19." (for corresponding restricted quantifier
       versions) followed by its identifier.
       For example, Theorem 38 from Section 19 of [Margaris] p. 90 is labeled
       ~ 19.38 , and the restricted quantifier version of Theorem 21 from
       Section 19 of [Margaris] p. 90 is labeled ~ r19.21 .
       </li>

       <li><b>Characters to be used for labels.</b>
       Although the specification of Metamath allows for dots/periods "." in
       any label, it is usually used only in labels for hypotheses (see above).
       Exceptions are the labels of theorems from Principia Mathematica and the
       19.x series of theorems from Section 19 of [Margaris] p. 90 (see above)
       and ~ 0.999... .  Furthermore, the underscore "_" should not be used.
       Finally, only lower case characters should be used (except the special
       suffixes OLD, ALT, and ALTV mentioned in bullet point "Suffixes"), at
       least in main set.mm (exceptions are tolerated in mathboxes).
       </li>

       <li><b>Syntax label fragments.</b>
       Most theorems are named using a concatenation of syntax label fragments
       (omitting variables) that represent the important part of the theorem's
       main conclusion.  Almost every syntactic construct has a definition
       labeled "df-NAME", and normally NAME is the syntax label fragment. For
       example, the class difference construct ` ( A \ B ) `  is defined in
       ~ df-dif , and thus its syntax label fragment is "dif".  Similarly, the
       subclass relation ` A C_ B ` has syntax label fragment "ss"
       because it is defined in ~ df-ss .  Most theorem names follow from
       these fragments, for example, the theorem proving ` ( A \ B ) C_ A `
       involves a class difference ("dif") of a subset ("ss"), and thus is
       labeled ~ difss .  There are many other syntax label fragments, e.g.,
       singleton construct ` { A } ` has syntax label fragment "sn" (because it
       is defined in ~ df-sn ), and the pair construct ` { A , B } ` has
       fragment "pr" ( from ~ df-pr ).  Digits are used to represent
       themselves.  Suffixes (e.g., with numbers) are sometimes used to
       distinguish multiple theorems that would otherwise produce the same
       label.
       </li>

       <li><b>Phantom definitions.</b>
       In some cases there are common label fragments for something that could
       be in a definition, but for technical reasons is not.  The is-element-of
       (is member of) construct ` A e. B ` does not have a df-NAME definition;
       in this case its syntax label fragment is "el".  Thus, because the
       theorem beginning with ` ( A e. ( B \ { C } ) ` uses is-element-of
       ("el") of a class difference ("dif") of a singleton ("sn"), it is
       labeled ~ eldifsn .  An "n" is often used for negation ( ` -. ` ), e.g.,
       ~ nan .
       </li>

       <li><b>Exceptions.</b>
       Sometimes there is a definition df-NAME but the label fragment is not
       the NAME part.  The definition should note this exception as part of its
       definition.  In addition, the table below attempts to list all such
       cases and marks them in bold.  For example, the label fragment "cn"
       represents complex numbers ` CC ` (even though its definition is in
       ~ df-c ) and "re" represents real numbers ` RR ` (Definition ~ df-r ).
       The empty set ` (/) ` often uses fragment 0, even though it is defined
       in ~ df-nul .  The syntax construct ` ( A + B ) ` usually uses the
       fragment "add" (which is consistent with ~ df-add ), but "p" is used as
       the fragment for constant theorems.  Equality ` ( A = B ) ` often uses
       "e" as the fragment.  As a result, "two plus two equals four" is labeled
       ~ 2p2e4 .
       </li>

       <li><b>Other markings.</b>
       In labels we sometimes use "com" for "commutative", "ass" for
       "associative", "rot" for "rotation", and "di" for "distributive".
       </li>

       <li><b>Focus on the important part of the conclusion.</b>
       Typically the conclusion is the part the user is most interested in.
       So, a rough guideline is that a label typically provides a hint
       about only the conclusion; a label rarely says anything about the
       hypotheses or antecedents.
       If there are multiple theorems with the same conclusion
       but different hypotheses/antecedents, then the labels will need
       to differ; those label differences should emphasize what is different.
       There is no need to always fully describe the conclusion; just
       identify the important part. For example,
       ~ cos0 is the theorem that provides the value for the cosine of 0;
       we would need to look at the theorem itself to see what that value is.
       The label "cos0" is concise and we use it instead of "cos0eq1".
       There is no need to add the "eq1", because there will never be a case
       where we have to disambiguate between different values produced by
       the cosine of zero, and we generally prefer shorter labels if
       they are unambiguous.
       </li>

       <li><b>Closures and values.</b>
       As noted above, if a function df-NAME is defined, there is typically a
       proof of its value labeled "NAMEval" and of its closure labeled
       "NAMEcl".  E.g., for cosine ( ~ df-cos ) we have value ~ cosval and
       closure ~ coscl .
       </li>

       <li><b>Special cases.</b>
       Sometimes, syntax and related markings are insufficient to distinguish
       different theorems.  For example, there are over a hundred different
       implication-only theorems.  They are grouped in a more ad-hoc way that
       attempts to make their distinctions clearer.  These often use
       abbreviations such as "mp" for "modus ponens", "syl" for syllogism, and
       "id" for "identity".  It is especially hard to give good names in the
       propositional calculus section because there are so few primitives.
       However, in most cases this is not a serious problem.  There are a few
       very common theorems like ~ ax-mp and ~ syl that you will have no
       trouble remembering, a few theorem series like syl*anc and simp* that
       you can use parametrically, and a few other useful glue things for
       destructuring 'and's and 'or's (see ~ natded for a list), and that is
       about all you need for most things.  As for the rest, you can just
       assume that if it involves at most three connectives, then it is
       probably already proved in set.mm, and searching for it will give you
       the label.
       </li>

       <li><b>Suffixes.</b>
       Suffixes are used to indicate the form of a theorem (inference,
       deduction, or closed form, see above).
       Additionally, we sometimes suffix with "v" the label of a theorem adding
       a disjoint variable condition, as in ~ 19.21v versus ~ 19.21 .  This
       often permits to prove the result using fewer axioms, and/or to
       eliminate a nonfreeness hypothesis (such as ` F/ x ph ` in ~ 19.21 ).
       If no constraint is put on axiom use, then the v-version can be proved
       from the original theorem using ~ nfv .  If two (resp. three) such
       disjoint variable conditions are added, then the suffix "vv" (resp.
       "vvv") is used, e.g., ~ exlimivv .
       Conversely, we sometimes suffix with "f" the label of a theorem
       introducing such a hypothesis to eliminate the need for the disjoint
       variable condition; e.g., ~ euf derived from ~ eu6 .  The "f" stands
       for "not free in" which is less restrictive than "does not occur in."
       The suffix "b" often means "biconditional" ( ` <-> ` , "iff" , "if and
       only if"), e.g., ~ sspwb .
       We sometimes suffix with "s" the label of an inference that manipulates
       an antecedent, leaving the consequent unchanged.  The "s" means that the
       inference eliminates the need for a syllogism ( ~ syl ) -type inference
       in a proof.  A theorem label is suffixed with "ALT" if it provides an
       alternate less-preferred proof of a theorem (e.g., the proof is
       clearer but uses more axioms than the preferred version).
       The "ALT" may be further suffixed with a number if there is more
       than one alternate theorem.
       Furthermore, a theorem label is suffixed with "OLD" if there is a new
       version of it and the OLD version is obsolete (and will be removed
       within one year).

       Finally, it should be mentioned that suffixes can be combined, for
       example in ~ cbvaldva ( ~ cbval in deduction form "d" with a not free
       variable replaced by a disjoint variable condition "v" with a
       conjunction as antecedent "a").  As a general rule, the suffixes for
       the theorem forms ("i", "d" or "g") should be the first of multiple
       suffixes, as for example in ~ vtocldf .

       Here is a non-exhaustive list of common suffixes:
       <ul>
       <li> a : theorem having a conjunction as antecedent</li>
       <li> b : theorem expressing a logical equivalence</li>
       <li> c : contraction (e.g., ~ sylc , ~ syl2anc ), commutes
       (e.g., ~ biimpac )</li>
       <li> d : theorem in deduction form</li>
       <li> f : theorem with a hypothesis such as ` F/ x ph `</li>
       <li> g : theorem in closed form having an "is a set" antecedent</li>
       <li> i : theorem in inference form</li>
       <li> l : theorem concerning something at the left</li>
       <li> r : theorem concerning something at the right</li>
       <li> r : theorem with something reversed (e.g., a biconditional)</li>
       <li> s : inference that manipulates an antecedent ("s" refers to an
       application of ~ syl that is eliminated)</li>
       <li> t : theorem in closed form (not having an "is a set" antecedent)
       </li>
       <li> v : theorem with one (main) disjoint variable condition</li>
       <li> vv : theorem with two (main) disjoint variable conditions</li>
       <li> w : weak(er) form of a theorem</li>
       <li> ALT : alternate proof of a theorem</li>
       <li> ALTV : alternate version of a theorem or definition (mathbox
       only)</li>
       <li> OLD : old/obsolete version of a theorem (or proof) or definition
       </li>
       </ul>
       </li>

       <li><b>Reuse.</b>
       When creating a new theorem or axiom, try to reuse abbreviations used
       elsewhere.  A comment should explain the first use of an abbreviation.
       </li>
       </ul>

       <p>
       The following table shows some commonly used abbreviations in labels, in
       alphabetical order.  For each abbreviation we provide a mnenomic, the
       source theorem or the assumption defining it, an expression showing what
       it looks like, whether or not it is a "syntax fragment" (an abbreviation
       that indicates a particular kind of syntax), and hyperlinks to label
       examples that use the abbreviation.  The abbreviation is bolded if there
       is a df-NAME definition but the label fragment is not NAME.  This is
       <i>not</i> a complete list of abbreviations, though we do want this to
       eventually be a complete list of exceptions.
       <table border="1" id="naming-abbreviation-table">
       <tr><th>Abbreviation</th><th>Mnenomic</th><th>Source</th>
       <th>Expression</th><th>Syntax?</th><th>Example(s)</th></tr>
       <tr><td>a</td><td>and (suffix)</td><td> </td>
       <td> </td><td>No</td><td> ~ biimpa , ~ rexlimiva </td></tr>
       <tr><td>abl</td><td>Abelian group</td><td> ~ df-abl </td>
       <td> ` Abel ` </td><td>Yes</td><td> ~ ablgrp , ~ zringabl </td></tr>
       <tr><td>abs</td><td>absorption</td><td> </td> <td> </td><td>No</td>
       <td> ~ ressabs </td></tr>
       <tr><td>abs</td><td>absolute value (of a complex number)</td>
       <td> ~ df-abs </td><td> ` ( abs `` A ) ` </td><td>Yes</td>
       <td> ~ absval , ~ absneg , ~ abs1 </td></tr>
       <tr><td>ad</td><td>adding</td><td> </td>
       <td> </td><td>No</td><td> ~ adantr , ~ ad2antlr </td></tr>
       <tr><td>add</td><td>add (see "p")</td><td> ~ df-add </td>
       <td> ` ( A + B ) ` </td><td>Yes</td>
       <td> ~ addcl , ~ addcom , ~ addass </td></tr>
       <tr><td>al</td><td>"for all"</td><td> </td>
       <td> ` A. x ph ` </td><td>No</td><td> ~ alim , ~ alex </td></tr>
       <tr><td>ALT</td><td>alternative/less preferred (suffix)</td><td> </td>
       <td> </td><td>No</td><td> ~ idALT </td></tr>
       <tr><td>an</td><td>and</td><td> ~ df-an </td>
       <td> ` ( ph /\ ps ) ` </td><td>Yes</td>
       <td> ~ anor , ~ iman , ~ imnan </td></tr>
       <tr><td>ant</td><td>antecedent</td><td> </td>
       <td> </td><td>No</td><td> ~ adantr </td></tr>
       <tr><td>ass</td><td>associative</td><td> </td>
       <td> </td><td>No</td><td> ~ biass , ~ orass , ~ mulass </td></tr>
       <tr><td>asym</td><td>asymmetric, antisymmetric</td><td> </td>
       <td> </td><td>No</td><td> ~ intasym , ~ asymref , ~ posasymb </td></tr>
       <tr><td>ax</td><td>axiom</td><td> </td>
       <td> </td><td>No</td><td> ~ ax6dgen , ~ ax1cn </td></tr>
       <tr><td><b>bas</b>, base </td>
       <td>base (set of an extensible structure)</td><td> ~ df-base </td>
       <td> ` ( Base `` S ) ` </td><td>Yes</td>
       <td> ~ baseval , ~ ressbas , ~ cnfldbas </td></tr>
       <tr><td><b>b</b>, bi</td><td>biconditional ("iff", "if and only if")
       </td><td> ~ df-bi </td><td> ` ( ph <-> ps ) ` </td><td>Yes</td>
       <td> ~ impbid , ~ sspwb </td></tr>
       <tr><td>br</td><td>binary relation</td><td> ~ df-br </td>
       <td> ` A R B ` </td><td>Yes</td><td> ~ brab1 , ~ brun </td></tr>
       <tr><td>c</td><td>commutes, commuted (suffix)</td><td></td><td></td>
       <td>No</td><td> ~ biimpac </td></tr>
       <tr><td>c</td><td>contraction (suffix)</td><td></td><td></td>
       <td>No</td><td> ~ sylc , ~ syl2anc </td></tr>
       <tr><td>cbv</td><td>change bound variable</td><td> </td><td> </td>
       <td>No</td><td> ~ cbvalivw , ~ cbvrex </td></tr>
       <tr><td>cdm</td><td>codomain</td><td></td>
       <td></td><td>No</td><td> ~ ffvelcdm , ~ focdmex </td></tr>
       <tr><td>cl</td><td>closure</td><td> </td><td> </td><td>No</td>
       <td> ~ ifclda , ~ ovrcl , ~ zaddcl </td></tr>
       <tr><td><b>cn</b></td><td>complex numbers</td><td> ~ df-c </td>
       <td> ` CC ` </td><td>Yes</td><td> ~ nnsscn , ~ nncn </td></tr>
       <tr><td>cnfld</td><td>field of complex numbers</td><td> ~ df-cnfld </td>
       <td> ` CCfld ` </td><td>Yes</td><td> ~ cnfldbas , ~ cnfldinv </td></tr>
       <tr><td>cntz</td><td>centralizer</td><td> ~ df-cntz </td>
       <td> ` ( Cntz `` M ) ` </td><td>Yes</td>
       <td> ~ cntzfval , ~ dprdfcntz </td></tr>
       <tr><td>cnv</td><td>converse</td><td> ~ df-cnv </td>
       <td> ` ``' A ` </td><td>Yes</td><td> ~ opelcnvg , ~ f1ocnv </td></tr>
       <tr><td>co</td><td>composition</td><td> ~ df-co </td>
       <td> ` ( A o. B ) ` </td><td>Yes</td><td> ~ cnvco , ~ fmptco </td></tr>
       <tr><td>com</td><td>commutative</td><td> </td>
       <td> </td><td>No</td><td> ~ orcom , ~ bicomi , ~ eqcomi </td></tr>
       <tr><td>con</td><td>contradiction, contraposition</td><td> </td>
       <td> </td><td>No</td><td> ~ condan , ~ con2d </td></tr>
       <tr><td>csb</td><td>class substitution</td><td> ~ df-csb </td>
       <td> ` [_ A / x ]_ B ` </td><td>Yes</td>
       <td> ~ csbid , ~ csbie2g </td></tr>
       <tr><td>cyg</td><td>cyclic group</td><td> ~ df-cyg </td>
       <td> ` CycGrp ` </td><td>Yes</td>
       <td> ~ iscyg , ~ zringcyg </td></tr>
       <tr><td>d</td><td>deduction form (suffix)</td><td> </td>
       <td> </td><td>No</td><td> ~ idd , ~ impbid </td></tr>
       <tr><td>df</td><td>(alternate) definition (prefix)</td><td> </td>
       <td> </td><td>No</td><td> ~ dfrel2 , ~ dffn2 </td></tr>
       <tr><td>di, distr</td><td>distributive</td><td> </td>
       <td> </td><td>No</td>
       <td> ~ andi , ~ imdi , ~ ordi , ~ difindi , ~ ndmovdistr </td></tr>
       <tr><td>dif</td><td>class difference</td><td> ~ df-dif </td>
       <td> ` ( A \ B ) ` </td><td>Yes</td>
       <td> ~ difss , ~ difindi </td></tr>
       <tr><td>div</td><td>division</td><td> ~ df-div </td>
       <td> ` ( A / B ) ` </td><td>Yes</td>
       <td> ~ divcl , ~ divval , ~ divmul </td></tr>
       <tr><td>dm</td><td>domain</td><td> ~ df-dm </td>
       <td> ` dom A ` </td><td>Yes</td><td> ~ dmmpt , ~ iswrddm0 </td></tr>
       <tr><td><b>e, eq, equ</b></td><td>equals (equ for setvars, eq for
           classes)</td><td> ~ df-cleq </td>
       <td> ` A = B ` </td><td>Yes</td>
       <td> ~ 2p2e4 , ~ uneqri , ~ equtr </td></tr>
       <tr><td>edg</td><td>edge</td><td> ~ df-edg </td>
       <td> ` ( Edg `` G ) ` </td><td>Yes</td>
       <td> ~ edgopval , ~ usgredgppr </td></tr>
       <tr><td>el</td><td>element of</td><td> </td>
       <td> ` A e. B ` </td><td>Yes</td>
       <td> ~ eldif , ~ eldifsn , ~ elssuni </td></tr>
       <tr><td>en</td><td>equinumerous</td><td> df-en </td>
       <td> ` A ~~ B ` </td><td>Yes</td><td> ~ domen , ~ enfi </td></tr>
       <tr><td>eu</td><td>"there exists exactly one"</td><td> ~ eu6 </td>
       <td> ` E! x ph ` </td><td>Yes</td><td> ~ euex , ~ euabsn </td></tr>
       <tr><td>ex</td><td>exists (i.e. is a set)</td><td> </td>
       <td> ` e. _V ` </td><td>No</td><td> ~ brrelex1 , ~ 0ex </td></tr>
       <tr><td>ex, e</td><td>"there exists (at least one)"</td>
       <td> ~ df-ex </td>
       <td> ` E. x ph ` </td><td>Yes</td><td> ~ exim , ~ alex </td></tr>
       <tr><td>exp</td><td>export</td><td> </td>
       <td> </td><td>No</td><td> ~ expt , ~ expcom </td></tr>
       <tr><td>f</td><td>"not free in" (suffix)</td><td> </td>
       <td> </td><td>No</td><td> ~ equs45f , ~ sbf </td></tr>
       <tr><td>f</td><td>function</td><td> ~ df-f </td>
       <td> ` F : A --> B ` </td><td>Yes</td><td> ~ fssxp , ~ opelf </td></tr>
       <tr><td>fal</td><td>false</td><td> ~ df-fal </td>
       <td> ` F. ` </td><td>Yes</td><td> ~ bifal , ~ falantru </td></tr>
       <tr><td>fi</td><td>finite intersection</td><td> ~ df-fi </td>
       <td> ` ( fi `` B ) ` </td><td>Yes</td><td> ~ fival , ~ inelfi </td></tr>
       <tr><td><b>fi</b>, fin</td><td>finite</td><td> ~ df-fin </td>
       <td> ` Fin ` </td><td>Yes</td>
       <td> ~ isfi , ~ snfi , ~ onfin </td></tr>
       <tr><td><b>fld</b></td><td>field (Note: there is an alternative
       definition ` Fld ` of a field, see ~ df-fld )</td><td> ~ df-field </td>
       <td> ` Field ` </td><td>Yes</td><td> ~ isfld , ~ fldidom </td></tr>
       <tr><td>fn</td><td>function with domain</td><td> ~ df-fn </td>
       <td> ` A Fn B ` </td><td>Yes</td><td> ~ ffn , ~ fndm </td></tr>
       <tr><td>frgp</td><td>free group</td><td> ~ df-frgp </td>
       <td> ` ( freeGrp `` I ) ` </td><td>Yes</td>
       <td> ~ frgpval , ~ frgpadd </td></tr>
       <tr><td>fsupp</td><td>finitely supported function</td>
       <td> ~ df-fsupp </td><td> ` R finSupp Z ` </td><td>Yes</td>
       <td> ~ isfsupp , ~ fdmfisuppfi , ~ fsuppco </td></tr>
       <tr><td>fun</td><td>function</td><td> ~ df-fun </td>
       <td> ` Fun F ` </td><td>Yes</td><td> ~ funrel , ~ ffun </td></tr>
       <tr><td>fv</td><td>function value</td><td> ~ df-fv </td>
       <td> ` ( F `` A ) ` </td><td>Yes</td><td> ~ fvres , ~ swrdfv </td></tr>
       <tr><td>fz</td><td>finite set of sequential integers</td>
       <td> ~ df-fz </td>
       <td> ` ( M ... N ) ` </td><td>Yes</td><td> ~ fzval , ~ eluzfz </td></tr>
       <tr><td>fz0</td><td>finite set of sequential nonnegative integers</td>
       <td>  </td>
       <td> ` ( 0 ... N ) ` </td><td>Yes</td><td> ~ nn0fz0 , ~ fz0tp </td></tr>
       <tr><td>fzo</td><td>half-open integer range</td><td> ~ df-fzo </td>
       <td> ` ( M ..^ N ) ` </td><td>Yes</td>
       <td> ~ elfzo , ~ elfzofz </td></tr>
       <tr><td>g</td><td>more general (suffix); eliminates "is a set"
       hypotheses</td><td> </td>
       <td> </td><td>No</td><td> ~ uniexg </td></tr>
       <tr><td>gr</td><td>graph</td><td> </td>
       <td> </td><td>No</td><td> ~ uhgrf , ~ isumgr , ~ usgrres1 </td></tr>
       <tr><td>grp</td><td>group</td><td> ~ df-grp </td>
       <td> ` Grp ` </td><td>Yes</td><td> ~ isgrp , ~ tgpgrp </td></tr>
       <tr><td>gsum</td><td>group sum</td><td> ~ df-gsum </td>
       <td> ` ( G gsum F ) ` </td><td>Yes</td>
       <td> ~ gsumval , ~ gsumwrev </td></tr>
       <tr><td>hash</td><td>size (of a set)</td><td> ~ df-hash </td>
       <td> ` ( # `` A ) ` </td><td>Yes</td>
       <td> ~ hashgval , ~ hashfz1 , ~ hashcl </td></tr>
       <tr><td>hb</td><td>hypothesis builder (prefix)</td><td> </td>
       <td> </td><td>No</td><td> ~ hbxfrbi , ~ hbald , ~ hbequid </td></tr>
       <tr><td>hm</td><td>(monoid, group, ring, ...) homomorphism</td>
       <td> </td><td> </td><td>No</td>
       <td> ~ ismhm , ~ isghm , ~ isrhm </td></tr>
       <tr><td>i</td><td>inference (suffix)</td><td> </td>
       <td> </td><td>No</td><td> ~ eleq1i , ~ tcsni </td></tr>
       <tr><td>i</td><td>implication (suffix)</td><td> </td>
       <td> </td><td>No</td><td> ~ brwdomi , ~ infeq5i  </td></tr>
       <tr><td>id</td><td>identity</td><td> </td>
       <td> </td><td>No</td><td> ~ biid </td></tr>
       <tr><td>iedg</td><td>indexed edge</td><td> ~ df-iedg </td>
       <td> ` ( iEdg `` G ) ` </td><td>Yes</td>
       <td> ~ iedgval0 , ~ edgiedgb </td></tr>
       <tr><td>idm</td><td>idempotent</td><td> </td>
       <td> </td><td>No</td><td> ~ anidm , ~ tpidm13 </td></tr>
       <tr><td>im, <b>imp</b></td><td>implication (label often omitted)</td>
       <td> ~ df-im </td><td> ` ( A -> B ) ` </td><td>Yes</td>
       <td> ~ iman , ~ imnan , ~ impbidd </td></tr>
       <tr><td>im</td><td>(group, ring, ...) isomorphism</td><td> </td>
       <td> </td><td>No</td><td> ~ isgim , ~ rimrcl </td></tr>
       <tr><td>ima</td><td>image</td><td> ~ df-ima </td>
       <td> ` ( A " B ) ` </td><td>Yes</td><td> ~ resima , ~ imaundi </td></tr>
       <tr><td>imp</td><td>import</td><td> </td>
       <td> </td><td>No</td><td> ~ biimpa , ~ impcom </td></tr>
       <tr><td>in</td><td>intersection</td><td> ~ df-in </td>
       <td> ` ( A i^i B ) ` </td><td>Yes</td><td> ~ elin , ~ incom </td></tr>
       <tr><td>inf</td><td>infimum</td><td> ~ df-inf </td>
       <td> ` inf ( RR+ , RR* , < ) ` </td><td>Yes</td>
       <td> ~ fiinfcl , ~ infiso </td></tr>
       <tr><td>is...</td><td>is (something a) ...?</td><td> </td>
       <td> </td><td>No</td><td> ~ isring </td></tr>
       <tr><td>j</td><td>joining, disjoining</td><td> </td>
       <td> </td><td>No</td><td> ~ jc , ~ jaoi  </td></tr>
       <tr><td>l</td><td>left</td><td> </td>
       <td> </td><td>No</td><td> ~ olcd , ~ simpl  </td></tr>
       <tr><td>map</td><td>mapping operation or set exponentiation</td>
       <td> ~ df-map </td><td> ` ( A ^m B ) ` </td><td>Yes</td>
       <td> ~ mapvalg , ~ elmapex </td></tr>
       <tr><td>mat</td><td>matrix</td><td> ~ df-mat </td>
       <td> ` ( N Mat R ) ` </td><td>Yes</td>
       <td> ~ matval , ~ matring </td></tr>
       <tr><td>mdet</td><td>determinant (of a square matrix)</td>
       <td> ~ df-mdet </td><td> ` ( N maDet R ) ` </td><td>Yes</td>
       <td> ~ mdetleib , ~ mdetrlin </td></tr>
       <tr><td>mgm</td><td>magma</td><td> ~ df-mgm </td>
       <td> ` Magma ` </td><td>Yes</td>
       <td> ~ mgmidmo , ~ mgmlrid , ~ ismgm </td></tr>
       <tr><td>mgp</td><td>multiplicative group</td><td> ~ df-mgp </td>
       <td> ` ( mulGrp `` R ) ` </td><td>Yes</td>
       <td> ~ mgpress , ~ ringmgp </td></tr>
       <tr><td>mnd</td><td>monoid</td><td> ~ df-mnd </td>
       <td> ` Mnd ` </td><td>Yes</td><td> ~ mndass , ~ mndodcong </td></tr>
       <tr><td>mo</td><td>"there exists at most one"</td><td> ~ df-mo </td>
       <td> ` E* x ph ` </td><td>Yes</td><td> ~ eumo , ~ moim </td></tr>
       <tr><td>mp</td><td>modus ponens</td><td> ~ ax-mp </td>
       <td> </td><td>No</td><td> ~ mpd , ~ mpi </td></tr>
       <tr><td>mpo</td><td>maps-to notation for an operation</td>
       <td> ~ df-mpo </td><td> ` ( x e. A , y e. B |-> C ) ` </td><td>Yes</td>
       <td> ~ mpompt , ~ resmpo </td></tr>
       <tr><td>mpt</td><td>modus ponendo tollens</td><td></td>
       <td> </td><td>No</td><td> ~ mptnan , ~ mptxor </td></tr>
       <tr><td>mpt</td><td>maps-to notation for a function</td>
       <td> ~ df-mpt </td><td> ` ( x e. A |-> B ) ` </td><td>Yes</td>
       <td> ~ fconstmpt , ~ resmpt </td></tr>
       <tr><td>mul</td><td>multiplication (see "t")</td><td> ~ df-mul </td>
       <td> ` ( A x. B ) ` </td><td>Yes</td>
       <td> ~ mulcl , ~ divmul , ~ mulcom , ~ mulass </td></tr>
       <tr><td>n, not</td><td>not</td><td> </td>
       <td> ` -. ph ` </td><td>Yes</td>
       <td> ~ nan , ~ notnotr </td></tr>
       <tr><td>ne</td><td>not equal</td><td>df-ne</td><td> ` A =/= B ` </td>
       <td>Yes</td><td> ~ exmidne , ~ neeqtrd </td></tr>
       <tr><td>nel</td><td>not element of</td><td>df-nel</td><td> ` A e/ B `
       </td>
       <td>Yes</td><td> ~ neli , ~ nnel </td></tr>
       <tr><td>ne0</td><td>not equal to zero (see n0)</td><td></td>
       <td> ` =/= 0 ` </td><td>No</td>
       <td> ~ negne0d , ~ ine0 , ~ gt0ne0 </td></tr>
       <tr><td>nf</td><td> "not free in" (prefix)</td><td> ~ df-nf </td>
       <td> `  F/ x ph ` </td><td>Yes</td><td> ~ nfnd </td></tr>
       <tr><td>ngp</td><td>normed group</td><td> ~ df-ngp </td>
       <td> ` NrmGrp ` </td><td>Yes</td><td>  ~ isngp , ~ ngptps </td></tr>
       <tr><td>nm</td><td>norm (on a group or ring)</td><td> ~ df-nm </td>
       <td> ` ( norm `` W ) ` </td><td>Yes</td>
       <td>  ~ nmval , ~ subgnm </td></tr>
       <tr><td>nn</td><td>positive integers</td><td> ~ df-nn </td>
       <td> ` NN ` </td><td>Yes</td><td>  ~ nnsscn , ~ nncn </td></tr>
       <tr><td><b>nn0</b></td><td>nonnegative integers</td><td> ~ df-n0 </td>
       <td> ` NN0 ` </td><td>Yes</td><td>  ~ nnnn0 , ~ nn0cn </td></tr>
       <tr><td>n0</td><td>not the empty set (see ne0)</td><td></td>
       <td> ` =/= (/) ` </td><td>No</td><td> ~ n0i , ~ vn0 , ~ ssn0 </td></tr>
       <tr><td>OLD</td><td>old, obsolete (to be removed soon)</td><td> </td>
       <td> </td><td>No</td><td> ~ 19.43OLD </td></tr>
       <tr><td>on</td><td>ordinal number</td><td> ~ df-on </td>
       <td> ` A e. On ` </td><td>Yes</td>
       <td>  ~ elon , ~ 1on ~ onelon </td></tr>
       <tr><td>op</td><td>ordered pair</td><td> ~ df-op </td>
       <td> ` <. A , B >. ` </td><td>Yes</td><td>  ~ dfopif , ~ opth </td></tr>
       <tr><td>or</td><td>or</td><td> ~ df-or </td>
       <td> ` ( ph \/ ps ) ` </td><td>Yes</td>
       <td> ~ orcom , ~ anor </td></tr>
       <tr><td>ot</td><td>ordered triple</td><td> ~ df-ot </td>
       <td> ` <. A , B , C >. ` </td><td>Yes</td>
       <td>  ~ euotd , ~ fnotovb </td></tr>
       <tr><td>ov</td><td>operation value</td><td> ~ df-ov </td>
       <td> ` ( A F B ) ` </td><td>Yes
       </td><td>  ~ fnotovb , ~ fnovrn </td></tr>
       <tr><td><b>p</b></td><td>plus (see "add"), for all-constant
       theorems</td><td> ~ df-add </td>
       <td> ` ( 3 + 2 ) = 5 ` </td><td>Yes</td>
       <td> ~ 3p2e5 </td></tr>
       <tr><td>pfx</td><td>prefix</td><td> ~ df-pfx </td>
       <td> ` ( W prefix L ) ` </td><td>Yes</td>
       <td> ~ pfxlen , ~ ccatpfx </td></tr>
       <tr><td>pm</td><td>Principia Mathematica</td><td> </td>
       <td> </td><td>No</td><td> ~ pm2.27 </td></tr>
       <tr><td>pm</td><td>partial mapping (operation)</td><td> ~ df-pm </td>
       <td> ` ( A ^pm B ) ` </td><td>Yes</td><td> ~ elpmi , ~ pmsspw </td></tr>
       <tr><td>pr</td><td>pair</td><td> ~ df-pr </td>
       <td> ` { A , B } ` </td><td>Yes</td>
       <td> ~ elpr , ~ prcom , ~ prid1g , ~ prnz </td></tr>
       <tr><td>prm, <b>prime</b></td><td>prime (number)</td><td> ~ df-prm </td>
       <td> ` Prime ` </td><td>Yes</td><td> ~ 1nprm , ~ dvdsprime </td></tr>
       <tr><td>pss</td><td>proper subset</td><td> ~ df-pss </td>
       <td> ` A C. B ` </td><td>Yes</td><td> ~ pssss , ~ sspsstri </td></tr>
       <tr><td>q</td><td> rational numbers ("quotients")</td><td> ~ df-q </td>
       <td> ` QQ ` </td><td>Yes</td><td> ~ elq </td></tr>
       <tr><td>r</td><td>reversed (suffix)</td><td> </td>
       <td> </td><td>No</td><td> ~ pm4.71r , ~ caovdir  </td></tr>
       <tr><td>r</td><td>right</td><td> </td>
       <td> </td><td>No</td><td> ~ orcd , ~ simprl  </td></tr>
       <tr><td>rab</td><td>restricted class abstraction</td>
       <td> ~ df-rab </td><td> ` { x e. A | ph } ` </td><td>Yes</td>
       <td> ~ rabswap , ~ df-oprab </td></tr>
       <tr><td>ral</td><td>restricted universal quantification</td>
       <td> ~ df-ral </td><td> ` A. x e. A ph ` </td><td>Yes</td>
       <td> ~ ralnex , ~ ralrnmpo </td></tr>
       <tr><td>rcl</td><td>reverse closure</td><td> </td>
       <td> </td><td>No</td><td> ~ ndmfvrcl , ~ nnarcl </td></tr>
       <tr><td><b>re</b></td><td>real numbers</td><td> ~ df-r </td>
       <td> ` RR ` </td><td>Yes</td><td> ~ recn , ~ 0re </td></tr>
       <tr><td>rel</td><td>relation</td><td> ~ df-rel </td><td> ` Rel A ` </td>
       <td>Yes</td><td> ~ brrelex1 , ~ relmpoopab </td></tr>
       <tr><td>res</td><td>restriction</td><td> ~ df-res </td>
       <td> ` ( A |`` B ) ` </td><td>Yes</td>
       <td> ~ opelres , ~ f1ores </td></tr>
       <tr><td>reu</td><td>restricted existential uniqueness</td>
       <td> ~ df-reu </td><td> ` E! x e. A ph ` </td><td>Yes</td>
       <td> ~ nfreud , ~ reurex </td></tr>
       <tr><td>rex</td><td>restricted existential quantification</td>
       <td> ~ df-rex </td><td> ` E. x e. A ph ` </td><td>Yes</td>
       <td> ~ rexnal , ~ rexrnmpo </td></tr>
       <tr><td>rmo</td><td>restricted "at most one"</td>
       <td> ~ df-rmo </td><td> ` E* x e. A ph ` </td><td>Yes</td>
       <td> ~ nfrmod , ~ nrexrmo </td></tr>
       <tr><td>rn</td><td>range</td><td> ~ df-rn </td><td> ` ran A ` </td>
       <td>Yes</td><td> ~ elrng , ~ rncnvcnv </td></tr>
       <tr><td>ring</td><td>(unital) ring</td><td> ~ df-ring </td>
       <td> ` Ring ` </td><td>Yes</td>
       <td> ~ ringidval , ~ isring , ~ ringgrp </td></tr>
       <tr><td>rng</td><td>non-unital ring</td><td> ~ df-rng </td>
       <td> ` Rng ` </td><td>Yes</td>
       <td> ~ isrng , ~ rngabl , ~ rnglz </td></tr>
       <tr><td>rot</td><td>rotation</td><td> </td>
       <td> </td><td>No</td><td> ~ 3anrot , ~ 3orrot </td></tr>
       <tr><td>s</td><td>eliminates need for syllogism (suffix)</td>
       <td> </td> <td> </td><td>No</td><td> ~ ancoms </td></tr>
       <tr><td>sb</td><td>(proper) substitution (of a set)</td>
       <td> ~ df-sb </td><td> ` [ y / x ] ph ` </td><td>Yes</td>
       <td> ~ spsbe , ~ sbimi </td></tr>
       <tr><td>sbc</td><td>(proper) substitution of a class</td>
       <td> ~ df-sbc </td><td> ` [. A / x ]. ph ` </td><td>Yes</td>
       <td> ~ sbc2or , ~ sbcth </td></tr>
       <tr><td>sca</td><td>scalar</td><td> ~ df-sca </td>
       <td> ` ( Scalar `` H ) ` </td><td>Yes</td>
       <td> ~ resssca , ~ mgpsca </td></tr>
       <tr><td>simp</td><td>simple, simplification</td><td> </td>
       <td> </td><td>No</td><td> ~ simpl , ~ simp3r3 </td></tr>
       <tr><td>sn</td><td>singleton</td><td> ~ df-sn </td>
       <td> ` { A } ` </td><td>Yes</td><td> ~ eldifsn </td></tr>
       <tr><td>sp</td><td>specialization</td><td> </td>
       <td> </td><td>No</td><td> ~ spsbe , ~ spei </td></tr>
       <tr><td>ss</td><td>subset</td><td> ~ df-ss </td>
       <td> ` A C_ B ` </td><td>Yes</td><td> ~ difss </td></tr>
       <tr><td>struct</td><td>structure</td><td> ~ df-struct </td>
       <td> ` Struct ` </td><td>Yes</td><td> ~ brstruct , ~ structfn </td></tr>
       <tr><td>sub</td><td>subtract</td><td> ~ df-sub </td>
       <td> ` ( A - B ) ` </td><td>Yes</td>
       <td> ~ subval , ~ subaddi </td></tr>
       <tr><td>sup</td><td>supremum</td><td> ~ df-sup </td>
       <td> ` sup ( A , B , < ) ` </td><td>Yes</td>
       <td> ~ fisupcl , ~ supmo </td></tr>
       <tr><td>supp</td><td>support (of a function)</td><td> ~ df-supp </td>
       <td> ` ( F supp Z ) ` </td><td>Yes</td>
       <td> ~ ressuppfi , ~ mptsuppd </td></tr>
       <tr><td>swap</td><td>swap (two parts within a theorem)</td>
       <td> </td><td> </td><td>No</td><td> ~ rabswap , ~ 2reuswap </td></tr>
       <tr><td>syl</td><td>syllogism</td><td> ~ syl </td>
       <td> </td><td>No</td><td> ~ 3syl </td></tr>
       <tr><td>sym</td><td>symmetric</td><td> </td>
       <td> </td><td>No</td><td> ~ df-symdif , ~ cnvsym </td></tr>
       <tr><td>symg</td><td>symmetric group</td><td> ~ df-symg </td>
       <td> ` ( SymGrp `` A ) ` </td><td>Yes</td>
       <td> ~ symghash , ~ pgrpsubgsymg </td></tr>
       <tr><td><b>t</b></td>
       <td>times (see "mul"), for all-constant theorems</td>
       <td> ~ df-mul </td>
       <td> ` ( 3 x. 2 ) = 6 ` </td><td>Yes</td>
       <td> ~ 3t2e6 </td></tr>
       <tr>
         <td>th, t</td>
         <td>theorem</td>
         <td></td>
         <td></td>
         <td>No</td>
         <td> ~ nfth , ~ sbcth , ~ weth , ~ ancomst </td>
       </tr>
       <tr><td>tp</td><td>triple</td><td> ~ df-tp </td>
       <td> ` { A , B , C } ` </td><td>Yes</td>
       <td> ~ eltpi , ~ tpeq1 </td></tr>
       <tr><td>tr</td><td>transitive</td><td> </td>
       <td> </td><td>No</td><td> ~ bitrd , ~ biantr </td></tr>
       <tr>
         <td>tru, t</td>
         <td>true, truth</td>
         <td> ~ df-tru </td>
         <td> ` T. ` </td>
         <td>Yes</td>
         <td> ~ bitru , ~ truanfal , ~ biimt </td>
       </tr>
       <tr><td>un</td><td>union</td><td> ~ df-un </td>
       <td> ` ( A u. B ) ` </td><td>Yes</td>
       <td> ~ uneqri , ~ uncom </td></tr>
       <tr><td>unit</td><td>unit (in a ring)</td>
       <td> ~ df-unit </td><td> ` ( Unit `` R ) ` </td><td>Yes</td>
       <td> ~ isunit , ~ nzrunit </td></tr>
       <tr>
         <td>v</td>
         <td>set<b>v</b>ar (especially for specializations of
             theorems when a class is replaced by a setvar variable)</td>
         <td></td>
         <td>x</td>
         <td>Yes</td>
         <td> ~ cv , ~ vex , ~ velpw , ~ vtoclf </td>
       </tr>
       <tr>
         <td>v</td>
         <td>disjoint variable condition used in place of nonfreeness
             hypothesis (suffix)</td>
         <td></td>
         <td></td>
         <td>No</td>
         <td> ~ spimv </td>
       </tr>
       <tr>
         <td>vtx</td>
         <td>vertex</td>
         <td> ~ df-vtx </td>
         <td> ` ( Vtx `` G ) ` </td>
         <td>Yes</td>
         <td> ~ vtxval0 , ~ opvtxov </td>
       </tr>
       <tr>
         <td>vv</td>
         <td>two disjoint variable conditions used in place of nonfreeness
             hypotheses (suffix)</td>
         <td></td>
         <td></td>
         <td>No</td>
         <td> ~ 19.23vv </td>
       </tr>
       <tr><td>w</td><td>weak (version of a theorem) (suffix)</td><td> </td>
       <td> </td><td>No</td><td> ~ ax11w , ~ spnfw </td></tr>
       <tr><td><b>wrd</b></td><td>word</td>
       <td> ~ df-word </td><td> ` Word S ` </td><td>Yes</td>
       <td> ~ iswrdb , ~ wrdfn , ~ ffz0iswrd </td></tr>
       <tr><td>xp</td><td>cross product (Cartesian product)</td>
       <td> ~ df-xp </td><td> ` ( A X. B ) ` </td><td>Yes</td>
       <td> ~ elxp , ~ opelxpi , ~ xpundi </td></tr>
       <tr><td>xr</td><td>eXtended reals</td><td> ~ df-xr </td>
       <td> ` RR* ` </td><td>Yes</td><td> ~ ressxr , ~ rexr , ~ 0xr </td></tr>
       <tr><td>z</td><td> integers (from German "Zahlen")</td>
       <td> ~ df-z </td><td> ` ZZ ` </td><td>Yes</td>
       <td> ~ elz , ~ zcn </td></tr>
       <tr><td>zn</td><td> ring of integers ` mod N ` </td><td> ~ df-zn </td>
       <td> ` ( Z/nZ `` N ) ` </td><td>Yes</td>
       <td> ~ znval , ~ zncrng , ~ znhash </td></tr>
       <tr><td>zring</td><td>ring of integers</td><td> ~ df-zring </td>
       <td> ` ZZring ` </td><td>Yes</td><td> ~ zringbas , ~ zringcrng
       </td></tr>
       <tr><td><b>0, z</b></td>
       <td>slashed zero (empty set)</td><td> ~ df-nul </td>
       <td> ` (/) ` </td><td>Yes</td>
       <td> ~ n0i , ~ vn0 ; ~ snnz , ~ prnz </td></tr>
       </table>
       </HTML>

       (Contributed by the Metamath team, 27-Dec-2016.)  Date of last revision.
       (Revised by the Metamath team, 22-Sep-2022.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    conventions-labels $p |- ph $=
      (  ) B $.
  $}

  ${
    conventions-comments.1 $e |- ph $.
    $(
       <HTML>
       <p>
       The following gives conventions used in the Metamath Proof Explorer
       (MPE, set.mm) regarding comments, and more generally nonmathematical
       conventions.
       For other conventions, see ~ conventions and links therein.
       </p>

       <ul>
       <li><b>Input format.</b>
       <p>
       The input format is ASCII.  Tab characters are not allowed.  If
       non-ASCII characters have to be displayed in comments, use embedded
       mathematical symbols when they have been defined (e.g., "`` -> ``" for
       " ` -> ` ") or HTML entities (e.g., "&amp;eacute;" for "&eacute;").
       Default indentation is by two spaces.  Lines are hard-wrapped to be at
       most 79-character long, excluding the newline character (this can be
       achieved, except currently for section comments, by the Metamath program
       "MM> WRITE SOURCE set.mm / REWRAP" command or by running the script
       scripts/rewrap).  The file ends with an empty line.  There are no
       trailing spaces.  As for line wrapping in statements, we try to break
       lines before the most important token.
       </p>
       </li>

       <li><b>Language and spelling.</b>
       <p>
       The MPE uses American English, e.g., we write "neighborhood" instead of
       the British English "neighbourhood".  An exception is the word "analog",
       which can be either a noun or an adjective (furthermore, "analog" has
       the confounding meaning "not digital"); therefore, "analogue" is used
       for the noun and "analogous" for the adjective.  We favor regular
       plurals, e.g., "formulas" instead of "formulae", "lemmas" instead of
       "lemmata".  We use the serial comma (Oxford comma) in enumerations.  We
       use commas after "i.e." and "e.g.".
       </p>
       <p>
       We avoid beginning a sentence with a symbol (for instance, by writing
       "The function F is ..." instead of "F is...").</p>
       <p>
       Since comments may contain many space-separated symbols, we use the
       older convention of two spaces after a period ending a sentence, to
       better separate sentences (this is also achieved by the Metamath program
       "MM> WRITE SOURCE set.mm / REWRAP" command).
       <p>
       <p>
       When compound words have several variants, we prefer the concatenated
       variant (e.g., nonempty, nontrivial, nonpositive, nonzero,
       nonincreasing, nondegenerate...).
       </p>
       </li>

       <li><b>Quotation style.</b>
       <p>
       We use the "logical quotation style", which means that when a quoted
       text is followed by punctuation not pertaining to the quote, then the
       quotation mark precedes the punctuation (like at the beginning of this
       sentence).  We use the double quote as default quotation mark (since the
       single quote also serves as apostrophe), and the single quote in the
       case of a nested quotation.
       </p>
       </li>

       <li><b>Sectioning and section headers.</b>
       <p>
       The database set.mm has a sectioning system with four levels of titles,
       signaled by "decoration lines" which are 79-character long repetitions
       of ####, #*#*, =-=-, and -.-. (in descending order of sectioning level).
       Sections of any level are separated by two blank lines (if there is a
       "@( Begin $[ ... $] @)" comment (where "@" is actually "$") before a
       section header, then the double blank line should go before that
       comment, which is considered as belonging to that section).  The format
       of section headers is best seen in the source file (set.mm); it is as
       follows:
       <ul>
       <li>a line with "@(" (with the "@" replaced by "$");</li>
       <li>a decoration line;</li>
       <li>section title indented with two spaces;</li>
       <li>a (matching) decoration line;</li>
       <li>[blank line; header comment indented with two spaces;
       blank line;]</li>
       <li>a line with "@)" (with the "@" replaced by "$");</li>
       <li>one blank line.</li>
       </ul>
       <p>
       As everywhere else, lines are hard-wrapped to be 79-character long.  It
       is expected that in a future version, the Metamath program "MM> WRITE
       SOURCE set.mm / REWRAP" command will reformat section headers to
       automatically conform with this format.
       </p>
       </li>

       <li><b>Comments.</b>
       <p>
       As for formatting of the file set.mm, and in particular formatting and
       layout of the comments, the foremost rule is consistency.  The first
       sections of set.mm, in particular Part 1 "Classical first-order logic
       with equality" can serve as a model for contributors.  Some formatting
       rules are enforced when using the Metamath program "MM> WRITE SOURCE
       set.mm / REWRAP" command.  Here are a few other rules, which are
       not enforced, but that we try to follow:
       <ul>
       <li>
       A math string in a comment should be surrounded by space-separated
       backquotes on the same line, and if it is too long it should be broken
       into multiple adjacent math strings on multiple lines.
       </li>
       <li>
       The file set.mm should have a double blank line between sections, and at
       no other places.  In particular, there are no triple blank lines.
       </li>
       <li>
       The header comments should be spaced as those of Part 1, namely, with
       a blank line before and after the comment, and an indentation of two
       spaces.
       </li>
       <li>
       As of 20-Sep-2022, section comments are not rewrapped by the Metamath
       program "MM> WRITE SOURCE set.mm / REWRAP" command, though this is
       expected in a future version.  Similar spacing and wrapping should be
       used as for other comments: double spaces after a period ending a
       sentence, line wrapping with line width of 79, and no trailing spaces
       at the end of lines.
       </li>
       </ul>
       <br>
       </li>

       <li><b>Contributors.</b>
       <p>
       Each assertion (theorem, definition or axiom) has a contribution tag of
       the form "(Contributed by xxx, dd-Mmm-yyyy.)" (see Metamath Book,
       p. 142).  The date cannot serve as a proof of anteriority since there is
       currently no formal guarantee that the date is correct (a claim of
       anteriority can be backed, for instance, by the uploading of a result to
       a public repository with verifiable date).  The contributor is the first
       person who proved (or stated, in the case of a definition or axiom) the
       statement.  The list of contributors appears at the beginning of set.mm.
       </p>
       <p>
       An exception should be made if a theorem is essentially an extract or a
       variant of an already existing theorem, in which case the contributor
       should be that of the statement from which it is derived, with the
       modification signaled by a "(Revised by xxx, dd-Mmm-yyyy.)" tag.
       </p>
       </li>

       <li><b>Usage of parentheticals.</b>
       <p>
       Usually, the comment of a theorem should contain at most one of the
       "Revised by" and "Proof shortened by" parentheticals, see Metamath Book,
       pp. 142-143 (there must always be a "Contributed by" parenthetical for
       every theorem).  Exceptions for "Proof shortened by" parentheticals
       are essential additional shortenings by a different person.  If a proof
       is shortened by the same person, the date within the "Proof shortened
       by" parenthetical should be updated only.  This also holds for "Revised
       by" parentheticals, except that also more than one of such
       parentheticals for the same person are acceptable (if there are good
       reasons for this). A revision tag is optionally preceded by a short
       description of the revision.  Since this is somewhat subjective,
       judgment and intellectual honesty should be applied, with collegial
       settlement in case of dispute.
       </p>
       </li>

       <li><b>Explaining new labels.</b>
       <p>
       A comment should explain the first use of an abbreviation within a
       label.  This is often in a definition (e.g., Definition ~ df-an
       introduces the abbreviation "an" for conjunction ("and")), but not
       always (e.g., Theorem ~ alim introduces the abbreviation "al" for
       the universal quantifier ("for all")).  See ~ conventions-labels for a
       table of abbreviations.
       </p>
       </li>
       </ul>
       </HTML>

       (Contributed by the Metamath team, 27-Dec-2016.)  Date of last revision.
       (Revised by the Metamath team, 22-Sep-2022.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    conventions-comments $p |- ph $=
      (  ) B $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Natural deduction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
   $( Note:  validator.w3.org  rejects "&sacute;" so I changed it to
      "&#347;" - NM 22-Jun-2017 $)
   $( Dummy premise for ~ natded . $)
    natded.1 $e |- ph $.
    $(
       Here are typical natural deduction (ND) rules in the style of Gentzen
       and Ja&#347;kowski, along with MPE translations of them.  This also
       shows the recommended theorems when you find yourself needing these
       rules (the recommendations encourage a slightly different proof style
       that works more naturally with set.mm).  A decent list of the standard
       rules of natural deduction can be found beginning with definition /\I in
       [Pfenning] p. 18.  For information about ND and Metamath, see the
       <A HREF="mmnatded.html">page on Deduction Form and Natural Deduction
       in Metamath Proof Explorer</A>.  Many more citations could be added.

       <HTML>
       <P>
       <TABLE ALIGN=CENTER BORDER CELLSPACING=0 WIDTH="95%">
       <TR><TH>Name</TH><TH>Natural Deduction Rule</TH><TH>Translation</TH>
       <TH>Recommendation</TH><TH>Comments</TH></TR>
       <TR><TD> IT </TD>
       <TD> ` _G |- ps ` => ` _G |- ps ` </TD>
       <TD> ~ idi </TD>
       <TD> nothing </TD><TD>Reiteration is always redundant in Metamath.
       Definition "new rule" in [Pfenning] p. 18,
       definition IT in [Clemente] p. 10. </TD>
       </TR>

       <TR><TD> ` /\ `I</TD>
       <TD> ` _G |- ps ` & ` _G |- ch ` => ` _G |- ps /\ ch ` </TD>
       <TD> ~ jca </TD>
       <TD> ~ jca , ~ pm3.2i </TD>
       <TD>Definition ` /\ `I in [Pfenning] p. 18,
       definition I` /\ `m,n in [Clemente] p. 10, and
       definition ` /\ `I in [Indrzejczak] p. 34
       (representing both Gentzen's system NK and Ja&#347;kowski)</TD>
       </TR>

       <TR><TD> ` /\ `E<SUB>L</SUB></TD>
       <TD> ` _G |- ps /\ ch ` => ` _G |- ps ` </TD>
       <TD> ~ simpld </TD>
       <TD> ~ simpld , ~ adantr </TD>
       <TD>Definition ` /\ `E<SUB>L</SUB> in [Pfenning] p. 18,
       definition E` /\ `(1) in [Clemente] p. 11, and
       definition ` /\ `E in [Indrzejczak] p. 34
       (representing both Gentzen's system NK and Ja&#347;kowski)</TD>
       </TR>

       <TR><TD> ` /\ `E<SUB>R</SUB></TD>
       <TD> ` _G |- ps /\ ch ` => ` _G |- ch ` </TD>
       <TD> ~ simprd </TD>
       <TD> ~ simpr , ~ adantl </TD>
       <TD>Definition ` /\ `E<SUB>R</SUB> in [Pfenning] p. 18,
       definition E` /\ `(2) in [Clemente] p. 11, and
       definition ` /\ `E in [Indrzejczak] p. 34
       (representing both Gentzen's system NK and Ja&#347;kowski)</TD>
       </TR>

       <TR><TD> ` -> `I </TD>
       <TD> ` _G , ps |- ch ` => ` _G |- ps -> ch ` </TD>
       <TD> ~ ex </TD><TD> ~ ex </TD>
       <TD>Definition ` -> `I in [Pfenning] p. 18,
       definition I=>m,n in [Clemente] p. 11, and
       definition ` -> `I in [Indrzejczak] p. 33. </TD>
       </TR>

       <TR><TD> ` -> `E </TD>
       <TD> ` _G |- ps -> ch ` & ` _G |- ps ` => ` _G |- ch ` </TD>
       <TD> ~ mpd </TD><TD> ~ ax-mp , ~ mpd , ~ mpdan , ~ imp </TD>
       <TD>Definition ` -> `E in [Pfenning] p. 18,
       definition E=>m,n in [Clemente] p. 11, and
       definition ` -> `E in [Indrzejczak] p. 33. </TD>
       </TR>

       <TR><TD> ` \/ `I<SUB>L</SUB> </TD><TD> ` _G |- ps ` =>
       ` _G |- ps \/ ch ` </TD>
       <TD> ~ olcd </TD>
       <TD> ~ olc , ~ olci , ~ olcd </TD>
       <TD>Definition ` \/ `I in [Pfenning] p. 18,
       definition I` \/ `n(1) in [Clemente] p. 12</TD>
       </TR>

       <TR><TD> ` \/ `I<SUB>R</SUB> </TD><TD> ` _G |- ch ` =>
       ` _G |- ps \/ ch ` </TD>
       <TD> ~ orcd </TD>
       <TD> ~ orc , ~ orci , ~ orcd </TD>
       <TD>Definition ` \/ `I<SUB>R</SUB> in [Pfenning] p. 18,
       definition I` \/ `n(2) in [Clemente] p. 12. </TD>
       </TR>

       <TR><TD> ` \/ `E </TD><TD> ` _G |- ps \/ ch ` & ` _G , ps |- th ` &
       ` _G , ch |- th ` => ` _G |- th ` </TD>
       <TD> ~ mpjaodan </TD>
       <TD> ~ mpjaodan , ~ jaodan , ~ jaod </TD>
       <TD>Definition ` \/ `E in [Pfenning] p. 18,
       definition E` \/ `m,n,p in [Clemente] p. 12. </TD>
       </TR>

       <!-- This is NOT quite the same as Pfenning page 22, because they do not
       use falsum.  (Instead, they use an arbitrary atomic propositional letter
       in place of F. -->
       <TR><TD> ` -. `I </TD><TD> ` _G , ps |- F. ` => ` _G |- -. ps ` </TD>
       <TD> ~ inegd </TD><TD> ~ pm2.01d </TD>
       <TD></TD>
       </TR>

       <TR><TD> ` -. `I </TD><TD> ` _G , ps |- th ` & ` _G |- -. th ` =>
       ` _G |- -. ps ` </TD>
       <TD> ~ mtand </TD><TD> ~ mtand </TD>
       <TD>definition I` -. `m,n,p in [Clemente] p. 13. </TD>
       </TR>

       <TR><TD> ` -. `I </TD><TD> ` _G , ps |- ch ` & ` _G , ps |- -. ch ` =>
       ` _G |- -. ps ` </TD>
       <TD> ~ pm2.65da </TD><TD> ~ pm2.65da </TD>
       <TD>Contradiction.</TD>
       </TR>

       <TR><TD> ` -. `I </TD>
       <TD> ` _G , ps |- -. ps ` => ` _G |- -. ps ` </TD>
       <TD> ~ pm2.01da </TD><TD> ~ pm2.01d , ~ pm2.65da , ~ pm2.65d </TD>
       <TD>For an alternative falsum-free natural deduction ruleset</TD>
       </TR>

       <TR><TD> ` -. `E </TD>
       <TD> ` _G |- ps ` & ` _G |- -. ps ` => ` _G |- F. ` </TD>
       <TD> ~ pm2.21fal </TD>
       <TD> ~ pm2.21dd </TD><TD></TD>
       </TR>

       <TR><TD> ` -. `E </TD>
       <TD> ` _G , -. ps |- F. ` => ` _G |- ps ` </TD>
       <TD> </TD>
       <TD> ~ pm2.21dd </TD>
       <TD>definition ` -> `E in [Indrzejczak] p. 33. </TD>
       </TR>

       <TR><TD> ` -. `E </TD>
       <TD> ` _G |- ps ` & ` _G |- -. ps ` => ` _G |- th ` </TD>
       <TD> ~ pm2.21dd </TD><TD> ~ pm2.21dd , ~ pm2.21d , ~ pm2.21 </TD>
       <TD>For an alternative falsum-free natural deduction ruleset.
       Definition ` -. `E in [Pfenning] p. 18. </TD>
       </TR>

       <TR><TD> ` T. `I </TD><TD> ` _G |- T. ` </TD>
       <TD> ~ trud </TD><TD> ~ tru , ~ trud , ~ mptru </TD>
       <TD>Definition ` T. `I in [Pfenning] p. 18. </TD>
       </TR>

       <TR><TD> ` F. `E </TD><TD> ` _G , F. |- th ` </TD>
       <TD> ~ falimd </TD><TD> ~ falim </TD>
       <TD>Definition ` F. `E in [Pfenning] p. 18. </TD>
       </TR>

       <TR><TD> ` A. `I </TD>
       <TD> ` _G |- [ a / x ] ps ` => ` _G |- A. x ps ` </TD>
       <TD> ~ alrimiv </TD><TD> ~ alrimiv , ~ ralrimiva </TD>
       <TD>Definition ` A. `I<SUP>a</SUP> in [Pfenning] p. 18,
       definition I` A. `n in [Clemente] p. 32. </TD>
       </TR>

       <TR><TD> ` A. `E </TD>
       <TD> ` _G |- A. x ps ` => ` _G |- [ t / x ] ps ` </TD>
       <TD> ~ spsbcd </TD><TD> ~ spcv , ~ rspcv </TD>
       <TD>Definition ` A. `E in [Pfenning] p. 18,
       definition E` A. `n,t in [Clemente] p. 32. </TD>
       </TR>

       <TR><TD> ` E. `I </TD>
       <TD> ` _G |- [ t / x ] ps ` => ` _G |- E. x ps ` </TD>
       <TD> ~ spesbcd </TD><TD> ~ spcev , ~ rspcev </TD>
       <TD>Definition ` E. `I in [Pfenning] p. 18,
       definition I` E. `n,t in [Clemente] p. 32. </TD>
       </TR>

       <TR><TD> ` E. `E </TD>
       <TD> ` _G |- E. x ps ` & ` _G , [ a / x ] ps |- th ` =>
       ` _G |- th ` </TD>
       <TD> ~ exlimddv </TD><TD> ~ exlimddv , ~ exlimdd ,
       ~ exlimdv , ~ rexlimdva </TD>
       <TD>Definition ` E. `E<SUP>a,u</SUP> in [Pfenning] p. 18,
       definition E` E. `m,n,p,a in [Clemente] p. 32. </TD>
       </TR>

       <TR><TD> ` F. `C </TD>
       <TD> ` _G , -. ps |- F. ` => ` _G |- ps ` </TD>
       <TD> ~ efald </TD><TD> ~ efald </TD>
       <TD>Proof by contradiction (classical logic),
       definition ` F. `C in [Pfenning] p. 17. </TD>
       </TR>

       <TR><TD> ` F. `C </TD>
       <TD> ` _G , -. ps |- ps ` => ` _G |- ps ` </TD>
       <TD> ~ pm2.18da </TD><TD> ~ pm2.18da , ~ pm2.18d , ~ pm2.18 </TD>
       <TD>For an alternative falsum-free natural deduction ruleset</TD>
       </TR>

       <TR><TD> ` -. -. `C </TD>
       <TD> ` _G |- -. -. ps ` => ` _G |- ps ` </TD>
       <TD> ~ notnotrd </TD><TD> ~ notnotrd , ~ notnotr </TD>
       <TD>Double negation rule (classical logic),
       definition NNC in [Pfenning] p. 17,
       definition E` -. `n in [Clemente] p. 14. </TD>
       </TR>

       <TR><TD> EM </TD><TD> ` _G |- ps \/ -. ps ` </TD>
       <TD> ~ exmidd </TD><TD> ~ exmid </TD>
       <TD>Excluded middle (classical logic),
       definition XM in [Pfenning] p. 17,
       proof 5.11 in [Clemente] p. 14. </TD>
       </TR>

       <TR><TD> ` = `I </TD><TD> ` _G |- A = A ` </TD>
       <TD> ~ eqidd </TD><TD> ~ eqid , ~ eqidd </TD>
       <TD>Introduce equality,
       definition =I in [Pfenning] p. 127. </TD>
       </TR>

       <!-- In Metamath, no need to introduce E1 and E2 separately. -->
       <TR><TD> ` = `E </TD><TD> ` _G |- A = B ` & ` _G [. A / x ]. ps ` =>
       ` _G |- [. B / x ]. ps ` </TD>
       <TD> ~ sbceq1dd </TD><TD> ~ sbceq1d , equality theorems </TD>
       <TD>Eliminate equality,
       definition =E in [Pfenning] p. 127. (Both E1 and E2.) </TD>
       </TR>
       </TABLE>
       </HTML>

       <p>
       Note that MPE uses classical logic, not intuitionist logic.  As is
       conventional, the "I" rules are introduction rules, "E" rules are
       elimination rules, the "C" rules are conversion rules, and ` _G `
       represents the set of (current) hypotheses.  We use wff variable names
       beginning with ` ps ` to provide a closer representation of the Metamath
       equivalents (which typically use the antecedent ` ph ` to represent the
       context ` _G ` ).

       Most of this information was developed by Mario Carneiro and posted on
       3-Feb-2017.  For more information, see the
       <A HREF="mmnatded.html">page on Deduction Form and Natural Deduction
       in Metamath Proof Explorer</A>.

       For annotated examples where some traditional ND rules
       are directly applied in MPE, see ~ ex-natded5.2 , ~ ex-natded5.3 ,
       ~ ex-natded5.5 , ~ ex-natded5.7 , ~ ex-natded5.8 , ~ ex-natded5.13 ,
       ~ ex-natded9.20 , and ~ ex-natded9.26 .
       </p>

       (Contributed by DAW, 4-Feb-2017.)  (New usage is discouraged.) $)
    natded $p |- ph $=
      (  ) B $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Natural deduction examples
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  These are examples of how natural deduction rules can be applied in Metamath
  (both as line-for-line translations of ND rules, and as a way to apply
  deduction forms without being limited to applying ND rules).  For more
  information, see ~ natded and ~ mmnatded.html .  Since these examples should
  not be used within proofs of other theorems, especially in mathboxes, they
  are marked with "(New usage is discouraged.)".

$)

  ${
    ex-natded5.2.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    ex-natded5.2.2 $e |- ( ph -> ( ch -> ps ) ) $.
    ex-natded5.2.3 $e |- ( ph -> ch ) $.
    $( Theorem 5.2 of [Clemente] p. 15, translated line by line using the
       interpretation of natural deduction in Metamath.
       For information about ND and Metamath, see the
       <A HREF="mmnatded.html">page on Deduction Form and Natural Deduction
       in Metamath Proof Explorer</A>.
       The original proof, which uses Fitch style, was written as follows:

       <HTML>
       <TABLE BORDER>
       <TR><TH NOWRAP>#</TH><TH>MPE#</TH><TH>ND Expression</TH>
       <TH NOWRAP>MPE Translation</TH><TH>ND Rationale</TH>
       <TH>MPE Rationale</TH></TR>
       <TR><TD>1</TD><TD>5</TD><TD NOWRAP> ` ( ( ps /\ ch ) -> th ) ` </TD>
       <TD NOWRAP> ` ( ph -> ( ( ps /\ ch ) -> th ) ) ` </TD>
       <TD>Given</TD>
       <TD>$e. </TD></TR>
       <TR><TD>2</TD><TD>2</TD><TD NOWRAP> ` ( ch -> ps ) ` </TD>
       <TD NOWRAP> ` ( ph -> ( ch -> ps ) ) ` </TD>
       <TD>Given</TD>
       <TD>$e. </TD></TR>
       <TR><TD>3</TD><TD>1</TD><TD> ` ch ` </TD>
       <TD> ` ( ph -> ch ) ` </TD>
       <TD>Given</TD>
       <TD>$e. </TD></TR>
       <TR><TD>4</TD><TD>3</TD><TD> ` ps ` </TD>
       <TD> ` ( ph -> ps ) ` </TD>
       <TD> ` -> `E 2,3</TD>
       <TD> ~ mpd , the MPE equivalent of ` -> `E, 1,2</TD></TR>
       <TR><TD>5</TD><TD>4</TD><TD> ` ( ps /\ ch ) ` </TD>
       <TD> ` ( ph -> ( ps /\ ch ) ) ` </TD>
       <TD> ` /\ `I 4,3</TD>
       <TD> ~ jca , the MPE equivalent of ` /\ `I, 3,1</TD></TR>
       <TR><TD>6</TD><TD>6</TD><TD> ` th ` </TD>
       <TD> ` ( ph -> th ) ` </TD>
       <TD> ` -> `E 1,5</TD>
       <TD> ~ mpd , the MPE equivalent of ` -> `E, 4,5</TD></TR>
       </TABLE>
       </HTML>

       The original used Latin letters for predicates;
       we have replaced them with
       Greek letters to follow Metamath naming conventions and so that
       it is easier to follow the Metamath translation.
       The Metamath line-for-line translation of this
       natural deduction approach precedes every line with an antecedent
       including ` ph ` and uses the Metamath equivalents
       of the natural deduction rules.
       Below is the final Metamath proof (which reorders some steps).
       A much more efficient proof, using more of Metamath and MPE's
       capabilities, is shown in ~ ex-natded5.2-2 .
       A proof without context is shown in ~ ex-natded5.2i .
       (Contributed by Mario Carneiro, 9-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ex-natded5.2 $p |- ( ph -> th ) $=
      ( wa mpd jca ) ABCHDABCACBGFIGJEI $.

    $( A more efficient proof of Theorem 5.2 of [Clemente] p. 15.  Compare with
       ~ ex-natded5.2 and ~ ex-natded5.2i .  (Contributed by Mario Carneiro,
       9-Feb-2017.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ex-natded5.2-2 $p |- ( ph -> th ) $=
      ( mpd mp2and ) ABCDACBGFHGEI $.
  $}

  ${
    ex-natded5.2i.1 $e |- ( ( ps /\ ch ) -> th ) $.
    ex-natded5.2i.2 $e |- ( ch -> ps ) $.
    ex-natded5.2i.3 $e |- ch $.
    $( The same as ~ ex-natded5.2 and ~ ex-natded5.2-2 but with no context.
       (Contributed by Mario Carneiro, 9-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ex-natded5.2i $p |- th $=
      ( wa ax-mp pm3.2i ) ABGCABBAFEHFIDH $.
  $}

  ${
    ex-natded5.3.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ex-natded5.3.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Theorem 5.3 of [Clemente] p. 16, translated line by line using an
       interpretation of natural deduction in Metamath.
       A much more efficient proof, using more of Metamath and MPE's
       capabilities, is shown in ~ ex-natded5.3-2 .
       A proof without context is shown in ~ ex-natded5.3i .
       For information about ND and Metamath, see the <HTML>
       <A HREF="mmnatded.html">page on Deduction Form and Natural Deduction
       in Metamath Proof Explorer</A></HTML>.
       The original proof, which uses Fitch style, was written as follows:

       <HTML>
       <TABLE BORDER>
       <TR><TH NOWRAP>#</TH><TH>MPE#</TH><TH>ND Expression</TH>
       <TH NOWRAP>MPE Translation</TH><TH>ND Rationale</TH>
       <TH>MPE Rationale</TH></TR>
       <TR><TD>1</TD><TD>2;3</TD><TD NOWRAP> ` ( ps -> ch ) ` </TD>
       <TD NOWRAP> ` ( ph -> ( ps -> ch ) ) ` </TD>
       <TD>Given</TD>
       <TD>$e; ~ adantr to move it into the ND hypothesis</TD></TR>
       <TR><TD>2</TD><TD>5;6</TD><TD NOWRAP> ` ( ch -> th ) ` </TD>
       <TD NOWRAP> ` ( ph -> ( ch -> th ) ) ` </TD>
       <TD>Given</TD>
       <TD>$e; ~ adantr to move it into the ND hypothesis</TD></TR>
       <TR><TD>3</TD><TD>1</TD><TD> ...| ` ps ` </TD>
       <TD> ` ( ( ph /\ ps ) -> ps ) ` </TD>
       <TD>ND hypothesis assumption</TD>
       <TD> ~ simpr , to access the new assumption </TD></TR>
       <TR><TD>4</TD><TD>4</TD><TD> ... ` ch ` </TD>
       <TD> ` ( ( ph /\ ps ) -> ch ) ` </TD>
       <TD> ` -> `E 1,3</TD>
       <TD> ~ mpd , the MPE equivalent of ` -> `E, 1.3.
       ~ adantr was used to transform its dependency
       (we could also use ~ imp to get this directly from 1)
       </TD></TR>
       <TR><TD>5</TD><TD>7</TD><TD> ... ` th ` </TD>
       <TD> ` ( ( ph /\ ps ) -> th ) ` </TD>
       <TD> ` -> `E 2,4</TD>
       <TD> ~ mpd , the MPE equivalent of ` -> `E, 4,6.
       ~ adantr was used to transform its dependency</TD></TR>
       <TR><TD>6</TD><TD>8</TD><TD> ... ` ( ch /\ th ) ` </TD>
       <TD> ` ( ( ph /\ ps ) -> ( ch /\ th ) ) ` </TD>
       <TD> ` /\ `I 4,5</TD>
       <TD> ~ jca , the MPE equivalent of ` /\ `I, 4,7</TD></TR>
       <TR><TD>7</TD><TD>9</TD><TD NOWRAP> ` ( ps -> ( ch /\ th ) ) ` </TD>
       <TD NOWRAP> ` ( ph -> ( ps -> ( ch /\ th ) ) ) ` </TD>
       <TD> ` -> `I 3,6</TD>
       <TD> ~ ex , the MPE equivalent of ` -> `I, 8</TD></TR>
       </TABLE>
       </HTML>

       The original used Latin letters for predicates;
       we have replaced them with
       Greek letters to follow Metamath naming conventions and so that
       it is easier to follow the Metamath translation.
       The Metamath line-for-line translation of this
       natural deduction approach precedes every line with an antecedent
       including ` ph ` and uses the Metamath equivalents
       of the natural deduction rules.
       (Contributed by Mario Carneiro, 9-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ex-natded5.3 $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
      ( wa simpr wi adantr mpd jca ex ) ABCDGABGZCDNBCABHABCIBEJKZNCDOACDIBFJKL
      M $.

    $( A more efficient proof of Theorem 5.3 of [Clemente] p. 16.  Compare with
       ~ ex-natded5.3 and ~ ex-natded5.3i .  (Contributed by Mario Carneiro,
       9-Feb-2017.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ex-natded5.3-2 $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
      ( syld jcad ) ABCDEABCDEFGH $.
  $}

  ${
    ex-natded5.3i.1 $e |- ( ps -> ch ) $.
    ex-natded5.3i.2 $e |- ( ch -> th ) $.
    $( The same as ~ ex-natded5.3 and ~ ex-natded5.3-2 but with no context.
       Identical to ~ jccir , which should be used instead.  (Contributed by
       Mario Carneiro, 9-Feb-2017.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ex-natded5.3i $p |- ( ps -> ( ch /\ th ) ) $=
      ( syl jca ) ABCDABCDEFG $.
  $}

  ${
    ex-natded5.5.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ex-natded5.5.2 $e |- ( ph -> -. ch ) $.
    $( Theorem 5.5 of [Clemente] p. 18, translated line by line using the
       usual translation of natural deduction (ND) in the
       Metamath Proof Explorer (MPE) notation.
       For information about ND and Metamath, see the
       <A HREF="mmnatded.html">page on Deduction Form and Natural Deduction
       in Metamath Proof Explorer</A>.
       The original proof, which uses Fitch style, was written as follows
       (the leading "..." shows an embedded ND hypothesis, beginning with
       the initial assumption of the ND hypothesis):

       <HTML>
       <TABLE BORDER>
       <TR><TH NOWRAP>#</TH><TH>MPE#</TH><TH>ND Expression</TH>
       <TH NOWRAP>MPE Translation</TH><TH>ND Rationale</TH>
       <TH>MPE Rationale</TH></TR>
       <TR><TD>1</TD><TD>2;3</TD>
       <TD NOWRAP> ` ( ps -> ch ) ` </TD>
       <TD NOWRAP> ` ( ph -> ( ps -> ch ) ) ` </TD>
       <TD>Given</TD>
       <TD>$e; ~ adantr to move it into the ND hypothesis</TD></TR>
       <TR><TD>2</TD><TD>5</TD><TD NOWRAP> ` -. ch ` </TD>
       <TD NOWRAP> ` ( ph -> -. ch ) ` </TD><TD>Given</TD>
       <TD>$e; we'll use ~ adantr to move it into the ND hypothesis</TD></TR>
       <TR><TD>3</TD><TD>1</TD>
       <TD> ...| ` ps ` </TD><TD> ` ( ( ph /\ ps ) -> ps ) ` </TD>
       <TD>ND hypothesis assumption</TD>
       <TD> ~ simpr </TD></TR>
       <TR><TD>4</TD><TD>4</TD><TD> ... ` ch ` </TD>
       <TD> ` ( ( ph /\ ps ) -> ch ) ` </TD>
       <TD> ` -> `E 1,3</TD>
       <TD> ~ mpd 1,3</TD></TR>
       <TR><TD>5</TD><TD>6</TD><TD> ... ` -. ch ` </TD>
       <TD> ` ( ( ph /\ ps ) -> -. ch ) ` </TD>
       <TD>IT 2</TD>
       <TD> ~ adantr 5</TD></TR>
       <TR><TD>6</TD><TD>7</TD><TD> ` -. ps ` </TD>
       <TD> ` ( ph -> -. ps ) ` </TD>
       <TD> ` /\ `I 3,4,5</TD>
       <TD> ~ pm2.65da 4,6</TD></TR>
       </TABLE>
       </HTML>

       The original used Latin letters; we have replaced them with
       Greek letters to follow Metamath naming conventions and so that
       it is easier to follow the Metamath translation.
       The Metamath line-for-line translation of this
       natural deduction approach precedes every line with an antecedent
       including ` ph ` and uses the Metamath equivalents
       of the natural deduction rules.
       To add an assumption, the antecedent is modified to include it
       (typically by using ~ adantr ; ~ simpr is useful when you want to
       depend directly on the new assumption).
       Below is the final Metamath proof (which reorders some steps).

       A much more efficient proof is ~ mtod ;
       a proof without context is shown in ~ mto .

       (Contributed by David A. Wheeler, 19-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ex-natded5.5 $p |- ( ph -> -. ps ) $=
      ( wa simpr wi adantr mpd wn pm2.65da ) ABCABFBCABGABCHBDIJACKBEIL $.
  $}

  ${
    ex-natded5.7.1 $e |- ( ph -> ( ps \/ ( ch /\ th ) ) ) $.
    $( Theorem 5.7 of [Clemente] p. 19, translated line by line using the
       interpretation of natural deduction in Metamath.
       A much more efficient proof, using more of Metamath and MPE's
       capabilities, is shown in ~ ex-natded5.7-2 .
       For information about ND and Metamath, see the <HTML>
       <A HREF="mmnatded.html">page on Deduction Form and Natural Deduction
       in Metamath Proof Explorer</A></HTML>.
       The original proof, which uses Fitch style, was written as follows:

       <HTML>
       <TABLE BORDER>
       <TR><TH NOWRAP>#</TH><TH>MPE#</TH><TH>ND Expression</TH>
       <TH NOWRAP>MPE Translation</TH><TH>ND Rationale</TH>
       <TH>MPE Rationale</TH></TR>
       <TR><TD>1</TD><TD>6</TD>
       <TD NOWRAP> ` ( ps \/ ( ch /\ th ) ) ` </TD>
       <TD NOWRAP> ` ( ph -> ( ps \/ ( ch /\ th ) ) ) ` </TD>
       <TD>Given</TD>
       <TD>$e. No need for ~ adantr because we do not move this
       into an ND hypothesis</TD></TR>
       <TR><TD>2</TD><TD>1</TD><TD NOWRAP> ...| ` ps ` </TD>
       <TD NOWRAP> ` ( ( ph /\ ps ) -> ps ) ` </TD>
       <TD>ND hypothesis assumption (new scope)</TD>
       <TD> ~ simpr </TD></TR>
       <TR><TD>3</TD><TD>2</TD><TD> ... ` ( ps \/ ch ) ` </TD>
       <TD> ` ( ( ph /\ ps ) -> ( ps \/ ch ) ) ` </TD>
       <TD> ` \/ `I<SUB>L</SUB> 2</TD>
       <TD> ~ orcd , the MPE equivalent of ` \/ `I<SUB>L</SUB>, 1</TD></TR>
       <TR><TD>4</TD><TD>3</TD><TD> ...| ` ( ch /\ th ) ` </TD>
       <TD> ` ( ( ph /\ ( ch /\ th ) ) -> ( ch /\ th ) ) ` </TD>
       <TD>ND hypothesis assumption (new scope)</TD>
       <TD> ~ simpr </TD></TR>
       <TR><TD>5</TD><TD>4</TD><TD> ... ` ch ` </TD>
       <TD> ` ( ( ph /\ ( ch /\ th ) ) -> ch ) `  </TD>
       <TD> ` /\ `E<SUB>L</SUB> 4</TD>
       <TD> ~ simpld , the MPE equivalent of ` /\ `E<SUB>L</SUB>, 3</TD></TR>
       <TR><TD>6</TD><TD>6</TD><TD> ... ` ( ps \/ ch ) ` </TD>
       <TD> ` ( ( ph /\ ( ch /\ th ) ) -> ( ps \/ ch ) ) `  </TD>
       <TD> ` \/ `I<SUB>R</SUB> 5</TD>
       <TD> ~ olcd , the MPE equivalent of ` \/ `I<SUB>R</SUB>, 4</TD></TR>
       <TR><TD>7</TD><TD>7</TD><TD NOWRAP> ` ( ps \/ ch ) ` </TD>
       <TD NOWRAP> ` ( ph -> ( ps \/ ch ) ) ` </TD>
       <TD> ` \/ `E 1,3,6</TD>
       <TD> ~ mpjaodan , the MPE equivalent of ` \/ `E, 2,5,6 </TD></TR>
       </TABLE>
       </HTML>

       The original used Latin letters for predicates;
       we have replaced them with
       Greek letters to follow Metamath naming conventions and so that
       it is easier to follow the Metamath translation.
       The Metamath line-for-line translation of this
       natural deduction approach precedes every line with an antecedent
       including ` ph ` and uses the Metamath equivalents
       of the natural deduction rules.
       (Contributed by Mario Carneiro, 9-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ex-natded5.7 $p |- ( ph -> ( ps \/ ch ) ) $=
      ( wo wa simpr orcd simpld olcd mpjaodan ) ABBCFCDGZABGBCABHIAMGZCBNCDAMHJ
      KEL $.

    $( A more efficient proof of Theorem 5.7 of [Clemente] p. 19.  Compare with
       ~ ex-natded5.7 .  (Contributed by Mario Carneiro, 9-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ex-natded5.7-2 $p |- ( ph -> ( ps \/ ch ) ) $=
      ( wa wo simpl orim2i syl ) ABCDFZGBCGEKCBCDHIJ $.
  $}

  ${
    ex-natded5.8.1 $e |- ( ph -> ( ( ps /\ ch ) -> -. th ) ) $.
    ex-natded5.8.2 $e |- ( ph -> ( ta -> th ) ) $.
    ex-natded5.8.3 $e |- ( ph -> ch ) $.
    ex-natded5.8.4 $e |- ( ph -> ta ) $.
    $( Theorem 5.8 of [Clemente] p. 20, translated line by line using the
       usual translation of natural deduction (ND) in the
       Metamath Proof Explorer (MPE) notation.
       For information about ND and Metamath, see the
       <A HREF="mmnatded.html">page on Deduction Form and Natural Deduction
       in Metamath Proof Explorer</A>.
       The original proof, which uses Fitch style, was written as follows
       (the leading "..." shows an embedded ND hypothesis, beginning with
       the initial assumption of the ND hypothesis):

       <HTML>
       <TABLE BORDER>
       <TR><TH NOWRAP>#</TH><TH>MPE#</TH><TH>ND Expression</TH>
       <TH NOWRAP>MPE Translation</TH><TH>ND Rationale</TH>
       <TH>MPE Rationale</TH></TR>
       <TR><TD>1</TD><TD>10;11</TD>
       <TD NOWRAP> ` ( ( ps /\ ch ) -> -. th ) ` </TD>
       <TD NOWRAP> ` ( ph -> ( ( ps /\ ch ) -> -. th ) ) ` </TD>
       <TD>Given</TD>
       <TD>$e; ~ adantr to move it into the ND hypothesis</TD></TR>
       <TR><TD>2</TD><TD>3;4</TD><TD NOWRAP> ` ( ta -> th ) ` </TD>
       <TD NOWRAP> ` ( ph -> ( ta -> th ) ) ` </TD><TD>Given</TD>
       <TD>$e; ~ adantr to move it into the ND hypothesis</TD></TR>
       <TR><TD>3</TD><TD>7;8</TD>
       <TD> ` ch ` </TD><TD> ` ( ph -> ch ) ` </TD>
       <TD>Given</TD>
       <TD>$e; ~ adantr to move it into the ND hypothesis</TD></TR>
       <TR><TD>4</TD><TD>1;2</TD><TD> ` ta ` </TD><TD> ` ( ph -> ta ) ` </TD>
       <TD>Given</TD>
       <TD>$e. ~ adantr to move it into the ND hypothesis</TD></TR>
       <TR><TD>5</TD><TD>6</TD><TD> ...| ` ps ` </TD>
       <TD> ` ( ( ph /\ ps ) -> ps ) ` </TD>
       <TD>ND Hypothesis/Assumption</TD>
       <TD> ~ simpr . New ND hypothesis scope, each reference outside
       the scope must change antecedent ` ph ` to ` ( ph /\ ps ) `.</TD></TR>
       <TR><TD>6</TD><TD>9</TD><TD> ... ` ( ps /\ ch ) ` </TD>
       <TD> ` ( ( ph /\ ps ) -> ( ps /\ ch ) ) ` </TD>
       <TD> ` /\ `I 5,3</TD>
       <TD> ~ jca ( ` /\ `I), 6,8 ( ~ adantr to bring in scope)</TD></TR>
       <TR><TD>7</TD><TD>5</TD><TD> ... ` -. th ` </TD>
       <TD> ` ( ( ph /\ ps ) -> -. th ) ` </TD>
       <TD> ` -> `E 1,6</TD>
       <TD> ~ mpd ( ` -> `E), 2,4</TD></TR>
       <TR><TD>8</TD><TD>12</TD><TD> ... ` th ` </TD>
       <TD> ` ( ( ph /\ ps ) -> th ) ` </TD>
       <TD> ` -> `E 2,4</TD>
       <TD> ~ mpd ( ` -> `E), 9,11;
       note the contradiction with ND line 7 (MPE line 5)</TD></TR>
       <TR><TD>9</TD><TD>13</TD><TD> ` -. ps ` </TD>
       <TD> ` ( ph -> -. ps ) ` </TD>
       <TD> ` -. `I 5,7,8</TD>
       <TD> ~ pm2.65da ( ` -. `I), 5,12; proof by contradiction.
       MPE step 6 (ND#5) does not need a reference here, because
       the assumption is embedded in the antecedents</TD></TR>
       </TABLE>
       </HTML>

       The original used Latin letters; we have replaced them with
       Greek letters to follow Metamath naming conventions and so that
       it is easier to follow the Metamath translation.
       The Metamath line-for-line translation of this
       natural deduction approach precedes every line with an antecedent
       including ` ph ` and uses the Metamath equivalents
       of the natural deduction rules.
       To add an assumption, the antecedent is modified to include it
       (typically by using ~ adantr ; ~ simpr is useful when you want to
       depend directly on the new assumption).
       Below is the final Metamath proof (which reorders some steps).

       A much more efficient proof, using more of Metamath and MPE's
       capabilities, is shown in ~ ex-natded5.8-2 .

       (Contributed by Mario Carneiro, 9-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ex-natded5.8 $p |- ( ph -> -. ps ) $=
      ( wa adantr wi mpd wn simpr jca pm2.65da ) ABDABJZEDAEBIKAEDLBGKMRBCJZDNZ
      RBCABOACBHKPASTLBFKMQ $.

    $( A more efficient proof of Theorem 5.8 of [Clemente] p. 20.  For a longer
       line-by-line translation, see ~ ex-natded5.8 .  (Contributed by Mario
       Carneiro, 9-Feb-2017.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ex-natded5.8-2 $p |- ( ph -> -. ps ) $=
      ( mpd wn mpan2d mt2d ) ABDAEDIGJABCDKHFLM $.
  $}

  ${
    ex-natded5.13.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    ex-natded5.13.2 $e |- ( ph -> ( ps -> th ) ) $.
    ex-natded5.13.3 $e |- ( ph -> ( -. ta -> -. ch ) ) $.
    $( Theorem 5.13 of [Clemente] p. 20, translated line by line using the
       interpretation of natural deduction in Metamath.
       For information about ND and Metamath, see the
       <A HREF="mmnatded.html">page on Deduction Form and Natural Deduction
       in Metamath Proof Explorer</A>.
       A much more efficient proof, using more of Metamath and MPE's
       capabilities, is shown in ~ ex-natded5.13-2 .
       The original proof, which uses Fitch style, was written as follows
       (the leading "..." shows an embedded ND hypothesis, beginning with
       the initial assumption of the ND hypothesis):

       <HTML>
       <TABLE BORDER>
       <TR><TH NOWRAP>#</TH><TH>MPE#</TH><TH>ND Expression</TH>
       <TH NOWRAP>MPE Translation</TH><TH>ND Rationale</TH>
       <TH>MPE Rationale</TH></TR>
       <TR><TD>1</TD><TD>15</TD><TD NOWRAP> ` ( ps \/ ch ) ` </TD>
       <TD NOWRAP> ` ( ph -> ( ps \/ ch ) ) ` </TD>
       <TD>Given</TD>
       <TD>$e. </TD></TR>
       <TR><TD>2;3</TD><TD>2</TD><TD NOWRAP> ` ( ps -> th ) ` </TD>
       <TD NOWRAP> ` ( ph -> ( ps -> th ) ) ` </TD><TD>Given</TD>
       <TD>$e. ~ adantr to move it into the ND hypothesis</TD></TR>
       <TR><TD>3</TD><TD>9</TD><TD> ` ( -. ta -> -. ch ) ` </TD>
       <TD> ` ( ph -> ( -. ta -> -. ch ) ) ` </TD>
       <TD>Given</TD>
       <TD>$e. ~ ad2antrr to move it into the ND sub-hypothesis</TD></TR>
       <TR><TD>4</TD><TD>1</TD><TD> ...| ` ps ` </TD>
       <TD> ` ( ( ph /\ ps ) -> ps ) ` </TD>
       <TD>ND hypothesis assumption</TD>
       <TD> ~ simpr </TD></TR>
       <TR><TD>5</TD><TD>4</TD><TD> ... ` th ` </TD>
       <TD> ` ( ( ph /\ ps ) -> th ) ` </TD>
       <TD> ` -> `E 2,4</TD>
       <TD> ~ mpd 1,3</TD></TR>
       <TR><TD>6</TD><TD>5</TD><TD> ... ` ( th \/ ta ) ` </TD>
       <TD> ` ( ( ph /\ ps ) -> ( th \/ ta ) ) ` </TD>
       <TD> ` \/ `I 5</TD>
       <TD> ~ orcd 4</TD></TR>
       <TR><TD>7</TD><TD>6</TD><TD> ...| ` ch ` </TD>
       <TD> ` ( ( ph /\ ch ) -> ch ) ` </TD>
       <TD>ND hypothesis assumption</TD>
       <TD> ~ simpr </TD></TR>
       <TR><TD>8</TD><TD>8</TD><TD> ... ...| ` -. ta ` </TD>
       <TD> ` ( ( ( ph /\ ch ) /\ -. ta ) -> -. ta ) ` </TD>
       <TD>(sub) ND hypothesis assumption</TD>
       <TD> ~ simpr </TD></TR>
       <TR><TD>9</TD><TD>11</TD><TD> ... ... ` -. ch ` </TD>
       <TD> ` ( ( ( ph /\ ch ) /\ -. ta ) -> -. ch ) ` </TD>
       <TD> ` -> `E 3,8</TD>
       <TD> ~ mpd 8,10</TD></TR>
       <TR><TD>10</TD><TD>7</TD><TD> ... ... ` ch ` </TD>
       <TD> ` ( ( ( ph /\ ch ) /\ -. ta ) -> ch ) ` </TD>
       <TD> IT 7</TD>
       <TD> ~ adantr 6</TD></TR>
       <TR><TD>11</TD><TD>12</TD><TD> ... ` -. -. ta ` </TD>
       <TD> ` ( ( ph /\ ch ) -> -. -. ta ) ` </TD>
       <TD> ` -. `I 8,9,10</TD>
       <TD> ~ pm2.65da 7,11</TD></TR>
       <TR><TD>12</TD><TD>13</TD><TD> ... ` ta ` </TD>
       <TD> ` ( ( ph /\ ch ) -> ta ) ` </TD>
       <TD> ` -. `E 11</TD>
       <TD> ~ notnotrd 12</TD></TR>
       <TR><TD>13</TD><TD>14</TD><TD> ... ` ( th \/ ta ) ` </TD>
       <TD> ` ( ( ph /\ ch ) -> ( th \/ ta ) ) ` </TD>
       <TD> ` \/ `I 12</TD>
       <TD> ~ olcd 13</TD></TR>
       <TR><TD>14</TD><TD>16</TD><TD> ` ( th \/ ta ) ` </TD>
       <TD> ` ( ph -> ( th \/ ta ) ) ` </TD>
       <TD> ` \/ `E 1,6,13</TD>
       <TD> ~ mpjaodan 5,14,15</TD></TR>
       </TABLE>
       </HTML>

       The original used Latin letters; we have replaced them with
       Greek letters to follow Metamath naming conventions and so that
       it is easier to follow the Metamath translation.
       The Metamath line-for-line translation of this
       natural deduction approach precedes every line with an antecedent
       including ` ph ` and uses the Metamath equivalents
       of the natural deduction rules.
       To add an assumption, the antecedent is modified to include it
       (typically by using ~ adantr ; ~ simpr is useful when you want to
       depend directly on the new assumption).
       (Contributed by Mario Carneiro, 9-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ex-natded5.13 $p |- ( ph -> ( th \/ ta ) ) $=
      ( wo wa simpr wi adantr mpd orcd wn ad2antrr pm2.65da notnotrd olcd
      mpjaodan ) ABDEICABJZDEUBBDABKABDLBGMNOACJZEDUCEUCEPZCUCCUDACKMUCUDJUDCPZ
      UCUDKAUDUELCUDHQNRSTFUA $.

    $( A more efficient proof of Theorem 5.13 of [Clemente] p. 20.  Compare
       with ~ ex-natded5.13 .  (Contributed by Mario Carneiro, 9-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ex-natded5.13-2 $p |- ( ph -> ( th \/ ta ) ) $=
      ( wo con4d orim12d mpd ) ABCIDEIFABDCEGAECHJKL $.
  $}

  ${
    ex-natded9.20.1 $e |- ( ph -> ( ps /\ ( ch \/ th ) ) ) $.
    $( Theorem 9.20 of [Clemente] p. 43, translated line by line using the
       usual translation of natural deduction (ND) in the
       Metamath Proof Explorer (MPE) notation.
       For information about ND and Metamath, see the
       <A HREF="mmnatded.html">page on Deduction Form and Natural Deduction
       in Metamath Proof Explorer</A>.
       The original proof, which uses Fitch style, was written as follows
       (the leading "..." shows an embedded ND hypothesis, beginning with
       the initial assumption of the ND hypothesis):

       <HTML>
       <TABLE BORDER>
       <TR><TH NOWRAP>#</TH><TH>MPE#</TH><TH>ND Expression</TH>
       <TH NOWRAP>MPE Translation</TH><TH>ND Rationale</TH>
       <TH>MPE Rationale</TH></TR>
       <TR><TD>1</TD><TD>1</TD>
       <TD NOWRAP> ` ( ps /\ ( ch \/ th ) ) ` </TD>
       <TD NOWRAP> ` ( ph ->  ( ps /\ ( ch \/ th ) ) ) ` </TD>
       <TD>Given</TD>
       <TD>$e</TD></TR>
       <TR><TD>2</TD><TD>2</TD><TD NOWRAP> ` ps ` </TD>
       <TD NOWRAP> ` ( ph -> ps ) ` </TD>
       <TD>` /\ `E<SUB>L</SUB> 1</TD>
       <TD> ~ simpld 1</TD></TR>
       <TR><TD>3</TD><TD>11</TD>
       <TD> ` ( ch \/ th ) ` </TD>
       <TD> ` ( ph -> ( ch \/ th ) ) ` </TD>
       <TD> ` /\ `E<SUB>R</SUB> 1</TD>
       <TD>  ~ simprd 1</TD></TR>
       <TR><TD>4</TD><TD>4</TD>
       <TD> ...| ` ch ` </TD>
       <TD> ` ( ( ph /\ ch ) -> ch ) ` </TD>
       <TD>ND hypothesis assumption</TD>
       <TD> ~ simpr </TD></TR>
       <TR><TD>5</TD><TD>5</TD>
       <TD> ... ` ( ps /\ ch ) ` </TD>
       <TD> ` ( ( ph /\ ch ) -> ( ps /\ ch ) ) ` </TD>
       <TD> ` /\ `I 2,4</TD>
       <TD> ~ jca 3,4</TD></TR>
       <TR><TD>6</TD><TD>6</TD>
       <TD> ... ` ( ( ps /\ ch ) \/ ( ps /\ th ) ) ` </TD>
       <TD> ` ( ( ph /\ ch ) -> ( ( ps /\ ch ) \/ ( ps /\ th ) ) ) ` </TD>
       <TD> ` \/ `I<SUB>R</SUB> 5</TD>
       <TD> ~ orcd 5</TD></TR>
       <TR><TD>7</TD><TD>8</TD>
       <TD> ...| ` th ` </TD>
       <TD> ` ( ( ph /\ th ) -> th ) ` </TD>
       <TD>ND hypothesis assumption</TD>
       <TD> ~ simpr </TD></TR>
       <TR><TD>8</TD><TD>9</TD>
       <TD> ... ` ( ps /\ th ) ` </TD>
       <TD> ` ( ( ph /\ th ) -> ( ps /\ th ) ) ` </TD>
       <TD> ` /\ `I 2,7</TD>
       <TD> ~ jca 7,8</TD></TR>
       <TR><TD>9</TD><TD>10</TD>
       <TD> ... ` ( ( ps /\ ch ) \/ ( ps /\ th ) ) ` </TD>
       <TD> ` ( ( ph /\ th ) -> ( ( ps /\ ch ) \/ ( ps /\ th ) ) ) ` </TD>
       <TD> ` \/ `I<SUB>L</SUB> 8</TD>
       <TD> ~ olcd 9</TD></TR>
       <TR><TD>10</TD><TD>12</TD>
       <TD> ` ( ( ps /\ ch ) \/ ( ps /\ th ) ) ` </TD>
       <TD> ` ( ph -> ( ( ps /\ ch ) \/ ( ps /\ th ) ) ) ` </TD>
       <TD> ` \/ `E 3,6,9</TD>
       <TD> ~ mpjaodan 6,10,11</TD></TR>
       </TABLE>
       </HTML>

       The original used Latin letters; we have replaced them with
       Greek letters to follow Metamath naming conventions and so that
       it is easier to follow the Metamath translation.
       The Metamath line-for-line translation of this
       natural deduction approach precedes every line with an antecedent
       including ` ph ` and uses the Metamath equivalents
       of the natural deduction rules.
       To add an assumption, the antecedent is modified to include it
       (typically by using ~ adantr ; ~ simpr is useful when you want to
       depend directly on the new assumption).
       Below is the final Metamath proof (which reorders some steps).

       A much more efficient proof is ~ ex-natded9.20-2 .
       (Contributed by David A. Wheeler, 19-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ex-natded9.20 $p |- ( ph -> ( ( ps /\ ch ) \/ ( ps /\ th ) ) ) $=
      ( wa wo simpld adantr simpr jca orcd olcd simprd mpjaodan ) ACBCFZBDFZGDA
      CFZPQRBCABCABCDGZEHZIACJKLADFZQPUABDABDTIADJKMABSENO $.

    $( A more efficient proof of Theorem 9.20 of [Clemente] p. 45.  Compare
       with ~ ex-natded9.20 .  (Contributed by David A. Wheeler, 19-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ex-natded9.20-2 $p |- ( ph -> ( ( ps /\ ch ) \/ ( ps /\ th ) ) ) $=
      ( wa wo simpld anim1i orcd olcd simprd mpjaodan ) ACBCFZBDFZGDACFNOABCABC
      DGZEHZIJADFONABDQIKABPELM $.
  $}

  ${
    $d x y ph $.
    ex-natded9.26.1 $e |- ( ph -> E. x A. y ps ) $.
    $( Theorem 9.26 of [Clemente] p. 45, translated line by line using an
       interpretation of natural deduction in Metamath.  This proof has some
       additional complications due to the fact that Metamath's existential
       elimination rule does not change bound variables, so we need to verify
       that ` x ` is bound in the conclusion.
       For information about ND and Metamath, see the
       <A HREF="mmnatded.html">page on Deduction Form and Natural Deduction
       in Metamath Proof Explorer</A>.
       The original proof, which uses Fitch style, was written as follows
       (the leading "..." shows an embedded ND hypothesis, beginning with
       the initial assumption of the ND hypothesis):

       <HTML>
       <TABLE BORDER>
       <TR><TH NOWRAP>#</TH><TH>MPE#</TH><TH>ND Expression</TH>
       <TH NOWRAP>MPE Translation</TH><TH>ND Rationale</TH>
       <TH>MPE Rationale</TH></TR>
       <TR><TD>1</TD><TD>3</TD><TD NOWRAP> ` E. x A. y ps ( x , y ) ` </TD>
       <TD NOWRAP> ` ( ph -> E. x A. y ps ) ` </TD>
       <TD>Given</TD>
       <TD>$e. </TD></TR>
       <TR><TD>2</TD><TD>6</TD><TD NOWRAP> ...| ` A. y ps ( x , y ) ` </TD>
       <TD NOWRAP> ` ( ( ph /\ A. y ps ) -> A. y ps ) ` </TD>
       <TD>ND hypothesis assumption</TD>
       <TD> ~ simpr . Later statements will have this scope.</TD></TR>
       <TR><TD>3</TD><TD>7;5,4</TD><TD> ... ` ps ( x , y ) ` </TD>
       <TD> ` ( ( ph /\ A. y ps ) -> ps ) ` </TD>
       <TD> ` A. `E 2,y </TD>
       <TD> ~ spsbcd (` A. `E), 5,6. To use it we need ~ a1i and ~ vex .
       This could be immediately done with ~ 19.21bi , but we want to show
       the general approach for substitution.
       </TD></TR>
       <TR><TD>4</TD><TD>12;8,9,10,11</TD><TD> ... ` E. x ps ( x , y ) ` </TD>
       <TD> ` ( ( ph /\ A. y ps ) -> E. x ps ) ` </TD>
       <TD> ` E. `I 3,a</TD>
       <TD> ~ spesbcd (` E. `I), 11.
       To use it we need ~ sylibr , which in turn requires ~ sylib and
       two uses of ~ sbcid .
       This could be more immediately done using ~ 19.8a , but we want to show
       the general approach for substitution.
       </TD></TR>
       <TR><TD>5</TD><TD>13;1,2</TD><TD> ` E. x ps ( x , y ) ` </TD>
       <TD> ` ( ph -> E. x ps ) ` </TD><TD> ` E. `E 1,2,4,a</TD>
       <TD> ~ exlimdd (` E. `E), 1,2,3,12.
       We'll need supporting
       assertions that the variable is free (not bound),
       as provided in ~ nfv and ~ nfe1 (MPE# 1,2)</TD></TR>
       <TR><TD>6</TD><TD>14</TD><TD> ` A. y E. x ps ( x , y ) ` </TD>
       <TD> ` ( ph -> A. y E. x ps ) ` </TD>
       <TD> ` A. `I 5</TD>
       <TD> ~ alrimiv (` A. `I), 13</TD></TR>
       </TABLE>
       </HTML>

       The original used Latin letters for predicates;
       we have replaced them with
       Greek letters to follow Metamath naming conventions and so that
       it is easier to follow the Metamath translation.
       The Metamath line-for-line translation of this
       natural deduction approach precedes every line with an antecedent
       including ` ph ` and uses the Metamath equivalents
       of the natural deduction rules.
       Below is the final Metamath proof (which reorders some steps).

       Note that in the original proof, ` ps ( x , y ) ` has explicit
       parameters.  In Metamath, these parameters are always implicit, and the
       parameters upon which a wff variable can depend are recorded in the
       "allowed substitution hints" below.

       A much more efficient proof, using more of Metamath and MPE's
       capabilities, is shown in ~ ex-natded9.26-2 .

       (Contributed by Mario Carneiro, 9-Feb-2017.)
       (Revised by David A. Wheeler, 18-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ex-natded9.26 $p |- ( ph -> A. y E. x ps ) $=
      ( wex wal nfv nfe1 wa cv wsbc cvv wcel vex a1i simpr spsbcd sbcid sylib
      sylibr spesbcd exlimdd alrimiv ) ABCFZDABDGZUECACHBCIEAUFJZBCCKZUGBBCUHLU
      GBDDKZLBUGBDUIMUIMNUGDOPAUFQRBDSTBCSUAUBUCUD $.

    $( A more efficient proof of Theorem 9.26 of [Clemente] p. 45.  Compare
       with ~ ex-natded9.26 .  (Contributed by Mario Carneiro, 9-Feb-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ex-natded9.26-2 $p |- ( ph -> A. y E. x ps ) $=
      ( wex wal sp eximi syl alrimiv ) ABCFZDABDGZCFLEMBCBDHIJK $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definitional examples
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Example for ~ df-or .  Example by David A. Wheeler.  (Contributed by Mario
     Carneiro, 9-May-2015.) $)
  ex-or $p |- ( 2 = 3 \/ 4 = 4 ) $=
    ( c4 wceq c2 c3 eqid olci ) AABCDBAEF $.

  $( Example for ~ df-an .  Example by David A. Wheeler.  (Contributed by Mario
     Carneiro, 9-May-2015.) $)
  ex-an $p |- ( 2 = 2 /\ 3 = 3 ) $=
    ( c2 wceq c3 eqid pm3.2i ) AABCCBADCDE $.

  $( Example for ~ df-dif .  Example by David A. Wheeler.  (Contributed by
     Mario Carneiro, 6-May-2015.) $)
  ex-dif $p |- ( { 1 , 3 } \ { 1 , 8 } ) = { 3 } $=
    ( c1 c3 cpr c8 cdif csn cun df-pr difeq1i difundir c0 wss wceq snsspr1 mpbi
    ssdif0 cin incom wcel 3eqtri 1re 1lt3 gtneii 3re ltneii nelpri disjsn mpbir
    wn 3lt8 eqtri disj3 eqcomi uneq12i uncom un0 ) ABCZADCZEAFZBFZGZUREUSUREZUT
    UREZGZUTUQVAURABHIUSUTURJVDKUTGUTKGUTVBKVCUTUSURLVBKMADNUSURPOUTVCUTURQZKMU
    TVCMVEURUTQZKUTURRVFKMBURSUIBADABUAUBUCBDUDUJUEUFURBUGUHUKUTURULOUMUNKUTUOU
    TUPTT $.

  $( Example for ~ df-un .  Example by David A. Wheeler.  (Contributed by Mario
     Carneiro, 6-May-2015.) $)
  ex-un $p |- ( { 1 , 3 } u. { 1 , 8 } ) = { 1 , 3 , 8 } $=
    ( c1 c3 cpr csn c8 cun ctp unass wss wceq snsspr1 ssequn2 mpbi uneq1i df-pr
    eqtr3i uneq2i df-tp 3eqtr4i ) ABCZADZEDZFZFZTUBFZTAECZFABEGTUAFZUBFUDUETUAU
    BHUGTUBUATIUGTJABKUATLMNPUFUCTAEOQABERS $.

  $( Example for ~ df-in .  Example by David A. Wheeler.  (Contributed by Mario
     Carneiro, 6-May-2015.) $)
  ex-in $p |- ( { 1 , 3 } i^i { 1 , 8 } ) = { 1 } $=
    ( c1 c3 cpr c8 cin csn cun df-pr ineq2i indi wceq snsspr1 sseqin2 mpbi wcel
    c0 wss wn gtneii eqtri 1re 1lt8 3re 3lt8 nelpri disjsn mpbir uneq12i un0 )
    ABCZADCZEUJAFZDFZGZEZULUKUNUJADHIUOUJULEZUJUMEZGZULUJULUMJURULPGULUPULUQPUL
    UJQUPULKABLULUJMNUQPKDUJORDABADUAUBSBDUCUDSUEUJDUFUGUHULUITTT $.

  $( Example for ~ df-uni .  Example by David A. Wheeler.  (Contributed by
     Mario Carneiro, 2-Jul-2016.) $)
  ex-uni $p |- U. { { 1 , 3 } , { 1 , 8 } } = { 1 , 3 , 8 } $=
    ( c1 c3 cpr c8 cuni cun ctp prex unipr ex-un eqtri ) ABCZADCZCELMFABDGLMABH
    ADHIJK $.

  $( Example for ~ df-ss .  Example by David A. Wheeler.  (Contributed by Mario
     Carneiro, 6-May-2015.) $)
  ex-ss $p |- { 1 , 2 } C_ { 1 , 2 , 3 } $=
    ( c1 c2 cpr c3 csn cun ctp ssun1 df-tp sseqtrri ) ABCZKDEZFABDGKLHABDIJ $.

  $( Example for ~ df-pss .  Example by David A. Wheeler.  (Contributed by
     Mario Carneiro, 6-May-2015.) $)
  ex-pss $p |- { 1 , 2 } C. { 1 , 2 , 3 } $=
    ( c1 c2 cpr c3 ctp wpss wss wne ex-ss wcel wn 3ex tpid3 1re 1lt3 gtneii 2re
    2lt3 nelpri nelne1 mp2an necomi df-pss mpbir2an ) ABCZABDEZFUEUFGUEUFHIUFUE
    DUFJDUEJKUFUEHABDLMDABADNOPBDQRPSDUFUETUAUBUEUFUCUD $.

  $( Example for ~ df-pw .  Example by David A. Wheeler.  (Contributed by Mario
     Carneiro, 2-Jul-2016.) $)
  ex-pw $p |- ( A = { 3 , 5 , 7 } -> ~P A =
    ( ( { (/) } u. { { 3 } , { 5 } , { 7 } } ) u.
      ( { { 3 , 5 } , { 3 , 7 } , { 5 , 7 } } u. { { 3 , 5 , 7 } } ) ) ) $=
    ( c3 c5 c7 ctp wceq cpw c0 csn cun cpr pweq df-tp uneq2i unass eqtr4i tpass
    uneq12i uneq1i 3eqtr4i qdass qdassr pwtp un4 eqtrdi ) ABCDEZFAGUFGZHIZBIZCI
    ZDIZEZJZBCKZBDKZCDKZEZUFIZJZJZAUFLHUIKUJUNKJZUKUOKUPUFKJZJHUIUJEZUNIZJZUKIZ
    UOUPUFEZJZJZUGUTVAVEVBVHHUIUJUNUAUKUOUPUFUBRBCDUCUTVCVFJZVDVGJZJVIUMVJUSVKU
    MUHUIUJKZJZVFJZVJUMUHVLVFJZJVNULVOUHUIUJUKMNUHVLVFOPVCVMVFHUIUJQSPVDUOUPKZJ
    ZURJVDVPURJZJUSVKVDVPUROUQVQURUNUOUPQSVGVRVDUOUPUFMNTRVCVDVFVGUDPTUE $.

  $( Example for ~ df-pr .  (Contributed by Mario Carneiro, 7-May-2015.) $)
  ex-pr $p |- ( A e. { 1 , -u 1 } -> ( A ^ 2 ) = 1 ) $=
    ( c1 cneg cpr wcel wceq wo c2 cexp elpri oveq1 sq1 eqtrdi neg1sqe1 jaoi syl
    co ) ABBCZDEABFZARFZGAHIQZBFZABRJSUBTSUABHIQBABHIKLMTUARHIQBARHIKNMOP $.

  $( Example for ~ df-br .  Example by David A. Wheeler.  (Contributed by Mario
     Carneiro, 6-May-2015.) $)
  ex-br $p |- ( R = { <. 2 , 6 >. , <. 3 , 9 >. } -> 3 R 9 ) $=
    ( c2 c6 cop c3 c9 cpr wceq wcel wbr opex prid2 id eleqtrrid df-br sylibr )
    ABCDZEFDZGZHZRAIEFAJTRSAQREFKLTMNEFAOP $.

  ${
    $d x y $.
    $( Example for ~ df-opab .  Example by David A. Wheeler.  (Contributed by
       Mario Carneiro, 18-Jun-2015.) $)
    ex-opab $p |- ( R = { <. x , y >. |
        ( x e. CC /\ y e. CC /\ ( x + 1 ) = y ) } -> 3 R 4 ) $=
      ( cv cc wcel c1 caddc co wceq w3a copab c3 wbr 3cn 4cn 3p1e4 elexi eleq1
      c4 oveq1 eqeq1d 3anbi13d eqeq2 3anbi23d eqid brab mpbir3an breq mpbiri )
      CADZEFZBDZEFZUKGHIZUMJZKZABLZJMTCNMTURNZUSMEFZTEFZMGHIZTJZOPQUQUTUNVBUMJZ
      KUTVAVCKABMTURMEORTEPRUKMJZULUTUPVDUNUKMESVEUOVBUMUKMGHUAUBUCUMTJUNVAVDVC
      UTUMTESUMTVBUDUEURUFUGUHMTCURUIUJ $.
  $}

  $( Example for ~ df-eprel .  Example by David A. Wheeler.  (Contributed by
     Mario Carneiro, 18-Jun-2015.) $)
  ex-eprel $p |- 5 _E { 1 , 5 } $=
    ( c5 c1 cpr cep wbr wcel cn 5nn elexi prid2 prex epeli mpbir ) ABACZDEANFBA
    AGHIJANBAKLM $.

  $( Example for ~ df-id .  Example by David A. Wheeler.  (Contributed by Mario
     Carneiro, 18-Jun-2015.) $)
  ex-id $p |- ( 5 _I 5 /\ -. 4 _I 5 ) $=
    ( c5 cid wbr c4 wn wceq eqid cr 5re elexi ideq mpbir 4re 4lt5 ltneii pm3.2i
    nemtbir ) AABCZDABCZERAAFAGAAAHIJZKLSDADAMNODATKQP $.

  $( Example for ~ df-po .  Example by David A. Wheeler.  (Contributed by Mario
     Carneiro, 18-Jun-2015.) $)
  ex-po $p |- ( < Po RR /\ -. <_ Po RR ) $=
    ( cr clt wpo cle wn wor ltso sopo ax-mp cc0 wbr 0le0 0re poirr mpan2 pm3.2i
    wcel mt2 ) ABCZADCZEABFSGABHITJJDKZLTJAQUAEMAJDNORP $.

  $( Example for ~ df-xp .  Example by David A. Wheeler.  (Contributed by Mario
     Carneiro, 7-May-2015.) $)
  ex-xp $p |- ( { 1 , 5 } X. { 2 , 7 } ) =
      ( { <. 1 , 2 >. , <. 1 , 7 >. } u. { <. 5 , 2 >. , <. 5 , 7 >. } ) $=
    ( c1 c5 cpr c2 c7 cxp csn cun cop df-pr xpeq12i xpun 1ex 2nn elexi xpsn 7nn
    cn uneq12i eqtr4i 5nn 3eqtri ) ABCZDECZFAGZBGZHZDGZEGZHZFUEUHFZUEUIFZHZUFUH
    FZUFUIFZHZHADIZAEIZCZBDIZBEIZCZHUCUGUDUJABJDEJKUEUFUHUILUMUSUPVBUMUQGZURGZH
    USUKVCULVDADMDRNOZPAEMERQOZPSUQURJTUPUTGZVAGZHVBUNVGUOVHBDBRUAOZVEPBEVIVFPS
    UTVAJTSUB $.

  $( Example for ~ df-cnv .  Example by David A. Wheeler.  (Contributed by
     Mario Carneiro, 6-May-2015.) $)
  ex-cnv $p |- `' { <. 2 , 6 >. , <. 3 , 9 >. }
      = { <. 6 , 2 >. , <. 9 , 3 >. } $=
    ( c2 c6 cop csn c3 c9 cun ccnv cpr cnvun cn 2nn elexi 6nn cnvsn 3nn uneq12i
    9nn eqtri df-pr cnveqi 3eqtr4i ) ABCZDZEFCZDZGZHZBACZDZFECZDZGZUCUEIZHUIUKI
    UHUDHZUFHZGUMUDUFJUOUJUPULABAKLMBKNMOEFEKPMFKRMOQSUNUGUCUETUAUIUKTUB $.

  $( Example for ~ df-co .  Example by David A. Wheeler.  (Contributed by Mario
     Carneiro, 7-May-2015.) $)
  ex-co $p |- ( ( exp o. cos ) ` 0 ) = _e $=
    ( cc0 ccos cfv ce c1 ccom ceu cos0 fveq2i cc wcel wceq cosf 0cn fvco3 mp2an
    wf df-e 3eqtr4i ) ABCZDCZEDCADBFCZGTEDHIJJBQAJKUBUALMNJJADBOPRS $.

  $( Example for ~ df-dm .  Example by David A. Wheeler.  (Contributed by Mario
     Carneiro, 7-May-2015.) $)
  ex-dm $p |- ( F = { <. 2 , 6 >. , <. 3 , 9 >. } -> dom F = { 2 , 3 } ) $=
    ( c2 c6 cop c3 c9 cpr wceq cdm dmeq cn 6nn elexi 9nn dmprop eqtrdi ) ABCDEF
    DGZHAIQIBEGAQJBCEFCKLMFKNMOP $.

  $( Example for ~ df-rn .  Example by David A. Wheeler.  (Contributed by Mario
     Carneiro, 7-May-2015.) $)
  ex-rn $p |- ( F = { <. 2 , 6 >. , <. 3 , 9 >. } -> ran F = { 6 , 9 } ) $=
    ( c2 c6 cop c3 c9 cpr wceq crn rneq csn cun df-pr rneqi cn 2nn elexi rnsnop
    rnun 3nn uneq12i eqtr4i 3eqtri eqtrdi ) ABCDZEFDZGZHAIUGIZCFGZAUGJUHUEKZUFK
    ZLZIUJIZUKIZLZUIUGULUEUFMNUJUKSUOCKZFKZLUIUMUPUNUQBCBOPQREFEOTQRUACFMUBUCUD
    $.

  $( Example for ~ df-res .  Example by David A. Wheeler.  (Contributed by
     Mario Carneiro, 7-May-2015.) $)
  ex-res $p |- ( ( F = { <. 2 , 6 >. , <. 3 , 9 >. } /\ B = { 1 , 2 } ) ->
         ( F |` B ) = { <. 2 , 6 >. } ) $=
    ( c2 c6 cop c3 c9 cpr wceq c1 cres csn cun eqtrdi c0 2re elexi wcel gtneii
    cr simpl df-pr reseq1d resundir wrel cdm wss relsnop dmsnopss snsspr2 simpr
    wa 6re sseqtrrid sstrid relssres sylancr 1re 1lt3 2lt3 nelpri eleq2d mtbiri
    wn ressnop0 syl uneq12d un0 eqtrd ) BCDEZFGEZHZIZAJCHZIZULZBAKZVJLZAKZVKLZA
    KZMZVRVPVQVRVTMZAKWBVPBWCAVPBVLWCVMVOUAVJVKUBNUCVRVTAUDNVPWBVROMVRVPVSVRWAO
    VPVRUEVRUFZAUGVSVRICDCTPQDTUMQUHVPWDCLZACDUIVPVNWEAJCUJVMVOUKZUNUOVRAUPUQVP
    FARZVDWAOIVPWGFVNRFJCJFURUSSCFPUTSVAVPAVNFWFVBVCFGAVEVFVGVRVHNVI $.

  $( Example for ~ df-ima .  Example by David A. Wheeler.  (Contributed by
     Mario Carneiro, 7-May-2015.) $)
  ex-ima $p |- ( ( F = { <. 2 , 6 >. , <. 3 , 9 >. } /\ B = { 1 , 2 } ) ->
         ( F " B ) = { 6 } ) $=
    ( c2 c6 cop c3 c9 cpr wceq c1 wa cima csn crn cres df-ima ex-res eqtrid 2ex
    rneqd rnsnop eqtrdi ) BCDEZFGEHIAJCHIKZBALZUCMZNZDMUDUEBAOZNUGBAPUDUHUFABQT
    RCDSUAUB $.

  $( Example for ~ df-fv .  Example by David A. Wheeler.  (Contributed by Mario
     Carneiro, 7-May-2015.) $)
  ex-fv $p |- ( F = { <. 2 , 6 >. , <. 3 , 9 >. } -> ( F ` 3 ) = 9 ) $=
    ( c2 c6 cop c3 c9 cpr wceq cfv fveq1 wne 2re 2lt3 ltneii 3ex cr elexi fvpr2
    9re ax-mp eqtrdi ) ABCDEFDGZHEAIEUBIZFEAUBJBEKUCFHBELMNBECFOFPSQRTUA $.

  $( Example for ~ df-1st .  Example by David A. Wheeler.  (Contributed by
     Mario Carneiro, 18-Jun-2015.) $)
  ex-1st $p |- ( 1st ` <. 3 , 4 >. ) = 3 $=
    ( c3 c4 3ex cr 4re elexi op1st ) ABCBDEFG $.

  $( Example for ~ df-2nd .  Example by David A. Wheeler.  (Contributed by
     Mario Carneiro, 18-Jun-2015.) $)
  ex-2nd $p |- ( 2nd ` <. 3 , 4 >. ) = 4 $=
    ( c3 c4 3ex cr 4re elexi op2nd ) ABCBDEFG $.

  $( Example for ~ df-dec , 1000 + 2000 = 3000.

     This proof disproves (by counterexample) the assertion of Hao Wang, who
     stated, "There is a theorem in the primitive notation of set theory that
     corresponds to the arithmetic theorem 1000 + 2000 = 3000.  The formula
     would be forbiddingly long... even if (one) knows the definitions and is
     asked to simplify the long formula according to them, chances are he will
     make errors and arrive at some incorrect result."  (Hao Wang, "Theory and
     practice in mathematics" , In Thomas Tymoczko, editor, _New Directions in
     the Philosophy of Mathematics_, pp 129-152, Birkauser Boston, Inc.,
     Boston, 1986.  (QA8.6.N48).  The quote itself is on page 140.)

     This is noted in _Metamath:  A Computer Language for Pure Mathematics_ by
     Norman Megill (2007) section 1.1.3.  Megill then states, "A number of
     writers have conveyed the impression that the kind of absolute rigor
     provided by Metamath is an impossible dream, suggesting that a complete,
     formal verification of a typical theorem would take millions of steps in
     untold volumes of books...  These writers assume, however, that in order
     to achieve the kind of complete formal verification they desire one must
     break down a proof into individual primitive steps that make direct
     reference to the axioms.  This is not necessary.  There is no reason not
     to make use of previously proved theorems rather than proving them over
     and over...  A hierarchy of theorems and definitions permits an
     exponential growth in the formula sizes and primitive proof steps to be
     described with only a linear growth in the number of symbols used.  Of
     course, this is how ordinary informal mathematics is normally done anyway,
     but with Metamath it can be done with absolute rigor and precision."

     The proof here starts with ` ( 2 + 1 ) = 3 ` , commutes it, and repeatedly
     multiplies both sides by ten.  This is certainly longer than traditional
     mathematical proofs, e.g., there are a number of steps explicitly shown
     here to show that we're allowed to do operations such as multiplication.
     However, while longer, the proof is clearly a manageable size - even
     though every step is rigorously derived all the way back to the primitive
     notions of set theory and logic.  And while there's a risk of making
     errors, the many independent verifiers make it much less likely that an
     incorrect result will be accepted.

     This proof heavily relies on the decimal constructor ~ df-dec developed by
     Mario Carneiro in 2015.  The underlying Metamath language has an
     intentionally very small set of primitives; it doesn't even have a
     built-in construct for numbers.  Instead, the digits are defined using
     these primitives, and the decimal constructor is used to make it easy to
     express larger numbers as combinations of digits.

     (Contributed by David A. Wheeler, 29-Jun-2016.)  (Shortened by Mario
     Carneiro using the arithmetic algorithm in mmj2, 30-Jun-2016.) $)
  1kp2ke3k $p |- ( ; ; ; 1 0 0 0 + ; ; ; 2 0 0 0 ) = ; ; ; 3 0 0 0 $=
    ( c1 cc0 cdc c2 c3 1nn0 0nn0 deccl 2nn0 eqid 1p2e3 00id decadd ) ABCZBCZBDB
    CZBCZBEBCZBCBOBCZQBCZNBABFGHZGHGPBDBIGHZGHGSJTJNBPBRBOQUAGUBGOJQJABDBEBNPFG
    IGNJPJKLMLMLM $.

  $( Example for ~ df-fl .  Example by David A. Wheeler.  (Contributed by Mario
     Carneiro, 18-Jun-2015.) $)
  ex-fl $p |- ( ( |_ ` ( 3 / 2 ) ) = 1 /\ ( |_ ` -u ( 3 / 2 ) ) = -u 2 ) $=
    ( c3 c2 co c1 wceq cneg wbr clt 1re 3re 2cn eqbrtri wb 2re mpbi cr wa mp2an
    wcel cz cdiv cfl cfv caddc rehalfcli cmul mullidi 2lt3 2pos ltmuldivi ax-mp
    cle cc0 ltleii 3lt4 2t2e4 breqtrri pm3.2i ltdivmul mp3an mpbir df-2 breqtri
    c4 1z flbi mpbir2an renegcli ltnegi cmin negcli ax-1cn negdi2 negnegi eqtri
    cc oveq1i 2m1e1 readdcli ltnegcon1i 2z znegcl ) ABUACZUBUCDEZWCFZUBUCBFZEZW
    DDWCULGZWCDDUDCZHGZDWCIAJUEZDBUFCZAHGZDWCHGZWLBAHBKUGUHLUMBHGZWMWNMUIDABIJN
    UJUKOZUNWCBWIHWCBHGZABBUFCZHGZAVDWRHUOUPUQAPSBPSZWTWOQWQWSMJNWTWONUIURABBUS
    UTVAZVBVCWCPSDTSWDWHWJQMWKVEWCDVFRVGWGWFWEULGZWEWFDUDCZHGZWFWEBNVHZWCWKVHZW
    QWFWEHGXAWCBWKNVIOUNXCFZWCHGXDXGBDVJCZWCHXGWFFZDVJCZXHWFVPSDVPSXGXJEBKVKVLW
    FDVMRXIBDVJBKVNVQVOXHDWCHVRWPLLXCWCWFDXEIVSWKVTOWEPSWFTSZWGXBXDQMXFBTSXKWAB
    WBUKWEWFVFRVGUR $.

  $( Example for ~ df-ceil .  (Contributed by AV, 4-Sep-2021.) $)
  ex-ceil $p |- ( ( |^ ` ( 3 / 2 ) ) = 2 /\ ( |^ ` -u ( 3 / 2 ) ) = -u 1 ) $=
    ( c3 c2 cdiv co cfl cfv c1 wceq cneg cceil ex-fl wcel 3re rehalfcli ceilval
    wa cr ax-mp negnegi eqtrid renegcli recni eqcomi fveq2i eqeq1i biimpi negeq
    negeqd 2cn eqtrdi anim12ci ) ABCDZEFZGHZULIZEFZBIZHZPULJFZBHZUOJFZGIZHZPKUN
    VCURUTUNVAUOIZEFZIZVBUOQLVAVFHULAMNZUAUOORUNVEGUNVEGHUMVEGULVDEVDULULULVGUB
    SUCUDUEUFUHTURUSUPIZBULQLUSVHHVGULORURVHUQIBUPUQUGBUISUJTUKR $.

  $( Example for ~ df-mod .  (Contributed by AV, 3-Sep-2021.) $)
  ex-mod $p |- ( ( 5 mod 3 ) = 2 /\ ( -u 7 mod 2 ) = 1 ) $=
    ( c5 c3 cmo co c2 wceq c7 cneg c1 caddc 3p2e5 eqcomi cn clt wbr cdvds mp2an
    wcel wb cz oveq1i cn0 2nn0 3nn 2lt3 addmodid mp3an eqtri wn 2re 2lt7 ltneii
    cuz cfv cprime 2nn 1lt2 eluz2b2 mpbir2an 7prm dvdsprm nemtbir nnzi dvdsnegb
    2z 7nn mtbi znegcl mod2eq1n2dvds mp2b mpbir pm3.2i ) ABCDZEFGHZECDIFZVMBEJD
    ZBCDZEAVPBCVPAKLUAEUBRBMREBNOVQEFUCUDUEEBUFUGUHVOEVNPOZUIZEGPOZVRVTEGEGUJUK
    ULEEUMUNRZGUORVTEGFSWAEMRIENOUPUQEURUSUTGEVAQVBETRGTRZVTVRSVEGVFVCZEGVDQVGW
    BVNTRVOVSSWCGVHVNVIVJVKVL $.

  $( Example for ~ df-exp .  (Contributed by AV, 4-Sep-2021.) $)
  ex-exp $p |- ( ( 5 ^ 2 ) = ; 2 5 /\ ( -u 3 ^ -u 2 ) = ( 1 / 9 ) ) $=
    ( c5 c2 cexp co cdc wceq c3 cneg c1 c9 cdiv c4 caddc cmul cc ax-mp c6 eqtri
    wcel c8 df-5 oveq1i 4cn binom21 2nn0 4nn0 4p1e5 sq4e2t8 8cn 8t2e16 mulcomli
    2cn 2t4e8 oveq12i 1nn0 6nn0 8nn0 eqid 1p1e2 8p6e14 addcomli decaddci decsuc
    6cn cn0 3cn negcli expneg mp2an sqneg sq3 oveq2i pm3.2i ) ABCDZBAEZFGHZBHCD
    ZIJKDZFVNLIMDZBCDZVOAVSBCUAUBVTLBCDZBLNDZMDZIMDZVOLOSVTWDFUCLUDPBLAWCUEUFUG
    WCIQEZTMDBLEWAWEWBTMWABTNDWEUHTBWEUIULUJUKRUMUNIQLBWETUOUPUQWEURUSUFTQILEUI
    VDUTVAVBRVCRRVQIVPBCDZKDZVRVPOSBVESVQWGFGVFVGUEVPBVHVIWFJIKWFGBCDZJGOSWFWHF
    VFGVJPVKRVLRVM $.

  $( Example for ~ df-fac .  (Contributed by AV, 4-Sep-2021.) $)
  ex-fac $p |- ( ! ` 5 ) = ; ; 1 2 0 $=
    ( c5 cfa cfv c4 c1 caddc co cmul c2 cdc cc0 df-5 fveq2i 4nn0 eqtri 2nn0 5cn
    0nn0 2cn mulcomli wcel wceq facp1 ax-mp fac4 4p1e5 oveq12i 5nn0 eqid 5t2e10
    cn0 1nn0 addlidi decaddi 4cn 5t4e20 decmul1c ) ABCZDBCZDEFGZHGZEIJZKJZURUTB
    CZVAAUTBLMDUKUAVDVAUBNDUCUDOVAIDJZAHGVCUSVEUTAHUEUFUGIDVBKAIVEUHPNVEUIRPEKI
    IAHGIULRPAIEKJQSUJTISUMUNADIKJQUOUPTUQOO $.

  $( Example for ~ df-bc .  (Contributed by AV, 4-Sep-2021.) $)
  ex-bc $p |- ( 5 _C 3 ) = ; 1 0 $=
    ( c5 c3 cbc co c4 c1 caddc cc0 cdc df-5 oveq1i cmin c6 4bc3eq4 3m1e2 oveq2i
    c2 4bc2eq6 eqtri wcel oveq12i cn0 cz wceq 4nn0 3z bcpasc mp2an 6cn addcomli
    4cn 6p4e10 3eqtr3i ) ABCDEFGDZBCDZFHIZAUNBCJKEBCDZEBFLDZCDZGDZEMGDUOUPUQEUS
    MGNUSEQCDMURQECOPRSUAEUBTBUCTUTUOUDUEUFBEUGUHMEUPUIUKULUJUMS $.

  $( Example for ~ df-hash .  (Contributed by AV, 4-Sep-2021.) $)
  ex-hash $p |- ( # ` { 0 , 1 , 2 } ) = 3 $=
    ( cc0 c1 c2 ctp chash cfv cpr csn caddc co c3 cun df-tp fveq2i cfn wcel cin
    wceq eqtri cz c0 prfi snfi 2ne0 necomi nelpri disjsn mpbir hashun prhash2ex
    wn 1ne2 mp3an 2z hashsng ax-mp oveq12i 2p1e3 ) ABCDZEFZABGZEFZCHZEFZIJZKUTV
    AVCLZEFZVEUSVFEABCMNVAOPVCOPVAVCQUARZVGVERABUBCUCVHCVAPUKCABUDBCULUEUFVACUG
    UHVAVCUIUMSVECBIJKVBCVDBIUJCTPVDBRUNCTUOUPUQURSS $.

  $( Example for ~ df-sqrt .  (Contributed by AV, 4-Sep-2021.) $)
  ex-sqrt $p |- ( sqrt ` ; 2 5 ) = 5 $=
    ( c5 c2 cexp co csqrt cfv wceq c3 cneg c1 c9 cdiv ex-exp simpli fveq2i wcel
    cdc cr cc0 5re cle wbr 0re 5pos ltleii sqrtsq mp2an eqtr3i ) ABCDZEFZBAQZEF
    AUIUKEUIUKGHIBICDJKLDGMNOARPSAUAUBUJAGTSAUCTUDUEAUFUGUH $.

  $( Example for ~ df-abs .  (Contributed by AV, 4-Sep-2021.) $)
  ex-abs $p |- ( abs ` -u 2 ) = 2 $=
    ( c2 cneg cabs cfv 2cn absnegi wcel cc0 cle wbr wceq 0le2 absid mp2an eqtri
    cr 2re ) ABCDACDZAAEFAPGHAIJRAKQLAMNO $.

  $( Example for ~ df-dvds : 3 divides into 6.  (Contributed by David A.
     Wheeler, 19-May-2015.) $)
  ex-dvds $p |- 3 || 6 $=
    ( c2 cz wcel c3 c6 w3a cmul co wceq cdvds wbr 2z 6nn nnzi 3pm3.2i caddc 3cn
    3z 2timesi 3p3e6 eqtri dvds0lem mp2an ) ABCZDBCZEBCZFADGHZEIDEJKUDUEUFLREMN
    OUGDDPHEDQSTUAADEUBUC $.

  $( Example for ~ df-gcd .  (Contributed by AV, 5-Sep-2021.) $)
  ex-gcd $p |- ( -u 6 gcd 9 ) = 3 $=
    ( c6 cneg c9 cgcd co c3 cz wcel wceq mp2an caddc eqcomi oveq2i eqtri gcdadd
    nnzi 3z cc0 3re 3eqtr3i 6nn 9nn neggcd 6cn 6p3e9 addcomli gcdcom 3p3e6 cabs
    3cn cfv gcdid ax-mp cr cle wbr 0re 3pos ltleii absid ) ABCDEZACDEZFAGHZCGHV
    AVBIAUAPZCUBPACUCJVBAFAKEZDEZFCVEADVECAFCUDUJUEUFLMAFDEZFFFKEZDEZVFFVGFADEZ
    VIVCFGHZVGVJIVDQAFUGJAVHFDVHAUHLMNVCVKVGVFIVDQAFOJFFDEZFUIUKZVIFVKVLVMIQFUL
    UMVKVKVLVIIQQFFOJFUNHRFUOUPVMFISRFUQSURUSFUTJTTNN $.

  $( Example for ~ df-lcm .  (Contributed by AV, 5-Sep-2021.) $)
  ex-lcm $p |- ( 6 lcm 9 ) = ; 1 8 $=
    ( c6 c9 co cmul cgcd cdiv c3 cc wcel cc0 wa wceq 6nn 9nn cz nnzi pm3.2i 3cn
    ax-mp 3ne0 clcm c1 cdc wne nnmulcli nncni lcmcl nn0cnd neggcd eqcomi ex-gcd
    c8 cneg eqtri eqeltri eqnetri w3a lcmgcdnn mp1i eqcomd divmul3 mpbird mp3an
    cn oveq2i 6cn 9cn divassi 3t3e9 oveq1i divcan3i 6t3e18 3eqtri ) ABUACZABDCZ
    ABECZFCZVOGFCZUBULUCZVOHIZVNHIZVPHIZVPJUDZKZVNVQLVOABMNUEUFAOIZBOIZKZWAWEWF
    AMPBNPQZWGVNABUGUHSWBWCVPGHVPAUMBECZGWIVPWGWIVPLWHABUISUJUKUNZRUOVPGJWJTUPQ
    VTWAWDUQZVQVNWKVQVNLVOVNVPDCZLWKWLVOAVDIZBVDIZKWLVOLWKWMWNMNQABURUSUTVOVNVP
    VAVBUTVCVPGVOFWJVEVRABGFCZDCAGDCVSABGVFVGRTVHWOGADWOGGDCZGFCGBWPGFWPBVIUJVJ
    GGRRTVKUNVEVLVMVM $.

  $( Example for ~ df-prmo : ` ( #p `` 1 0 ) = 2 x. 3 x. 5 x. 7 ` .
     (Contributed by AV, 6-Sep-2021.) $)
  ex-prmo $p |- ( #p ` ; 1 0 ) = ; ; 2 1 0 $=
    ( c1 cc0 cdc cprmo cfv cmin co c9 cprime wcel cmul wceq prmonn2 ax-mp eqtri
    cif cn fveq2i c8 c7 10nn 10nprm iffalsei 10m1e9 9nn 9nprm 9m1e8 8nprm 8m1e7
    c2 8nn 7nn 7prm iftruei c3 7nn0 3nn0 c6 7m1e6 prmo6 7cn 3cn 7t3e21 mulcomli
    0nn0 mul02i decmul1 3eqtri ) ABCZDEZVIAFGZDEZHDEZUJACZBCZVJVIIJZVLVIKGZVLPZ
    VLVIQJVJVRLUAVIMNVPVQVLUBUCOVKHDUDRVMHAFGZDEZSDEZVOVMHIJZVTHKGZVTPZVTHQJVMW
    DLUEHMNWBWCVTUFUCOVSSDUGRWASAFGZDEZTDEZVOWASIJZWFSKGZWFPZWFSQJWAWJLUKSMNWHW
    IWFUHUCOWETDUIRWGTIJZTAFGZDEZTKGZWMPZWNVOTQJWGWOLULTMNWKWNWMUMUNUOBVNBTWMUP
    UQVEWMURDEUOBCWLURDUSRUTOTUOVNVAVBVCVDTVAVFVGVHVHVHVH $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Other examples
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y $.  $d h m n $.
    $( Proof illustrating the comment of ~ aev2 .  (Contributed by BJ,
       30-Mar-2021.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    aevdemo $p |- ( A. x x = y ->
          ( ( E. a A. b c = d \/ E. e f = g ) /\ A. h ( i = j -> k = l ) ) ) $=
      ( vm vn weq wal wex aev wo wi 19.2d olcd aeveq a1d alrimiv syl jca ) ABQA
      RZLMQKRJSZDEQZCSZUAGHQZINQZUBZFRZUJUMUKUJULCABCEDTUCUDUJOPQORZUQABOPOTURU
      PFURUOUNOPINUEUFUGUHUI $.
  $}

  ${
    $d N k $.  $d k n $.
    $( Example of a proof by induction (divisibility result).  (Contributed by
       Stanislas Polu, 9-Mar-2020.)  (Revised by BJ, 24-Mar-2020.) $)
    ex-ind-dvds $p |- ( N e. NN0 -> 3 || ( ( 4 ^ N ) + 2 ) ) $=
      ( c3 c4 cexp co c2 caddc cdvds c1 wceq oveq2 oveq1d breq2d wcel cmul cmin
      wbr cz a1i 3cn vk vn cv cc0 3z iddvds ax-mp numexp0 oveq1i 1p2e3 breqtrri
      4nn0 eqtri wa simpl nn0expcld nn0zd 2z zaddcld 4z zmulcld id adantr simpr
      cn0 dvdsmultr1d dvdsmul1 dvds2subd nn0cnd 2cnd cc 4cn adddird 2cn mulcomi
      mp2an oveq2d expp1d ax-1cn 3p1e4 addcomli eqcomi mvrraddi oveq2i 3eqtr3ri
      subdii 2t1e2 oveq12d mulcld addsubassd eqtr4d 3eqtr4rd breqtrrd ex nn0ind
      ) BCUAUCZDEZFGEZHQBCUDDEZFGEZHQBCUBUCZDEZFGEZHQZBCXAIGEZDEZFGEZHQZBCADEZF
      GEZHQUAUBAWPUDJZWRWTBHXKWQWSFGWPUDCDKLMWPXAJZWRXCBHXLWQXBFGWPXACDKLMWPXEJ
      ZWRXGBHXMWQXFFGWPXECDKLMWPAJZWRXJBHXNWQXIFGWPACDKLMBBWTHBRNZBBHQUEBUFUGWT
      IFGEBWSIFGCULUHUIUJUMUKXAVENZXDXHXPXDUNZBXCCOEZBFOEZPEZXGHXQBXRXSXOXQUESZ
      XQXCCXQXBFXQXBXQCXACVENZXQULSXPXDUOUPUQFRNZXQURSZUSCRNXQUTSZVAXQBFYAYDVAX
      QBXCCYAXQXBFXPXBRNXDXPXBXPCXAYBXPULSXPVBZUPZUQVCYDUSYEXPXDVDVFBXSHQZXQXOY
      CYHUEURBFVGVPSVHXPXGXTJXDXPXRFBOEZPEXBCOEZFCOEZGEZYIPEZXTXGXPXRYLYIPXPXBF
      CXPXBYGVIZXPVJZCVKNXPVLSZVMLXPXSYIXRPXSYIJXPBFTVNVOSVQXPXGYJYKYIPEZGEYMXP
      XFYJFYQGXPCXAYPYFVRFYQJXPFCBPEZOEFIOEYQFYRIFOCIBVSTIBGECBICTVSVTWAWBWCWDF
      CBVNVLTWFWGWESWHXPYJYKYIXPXBCYNYPWIXPFCYOYPWIXPFBYOBVKNXPTSWIWJWKWLVCWMWN
      WO $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d F x y $.  $d G x y $.
    ex-fpar.h $e |- H = ( ( `' ( 1st |` ( _V X. _V ) )
                        o. ( F o. ( 1st |` ( _V X. _V ) ) ) )
                i^i ( `' ( 2nd |` ( _V X. _V ) )
                       o. ( G o. ( 2nd |` ( _V X. _V ) ) ) ) ) $.
    ex-fpar.a $e |- A = ( 0 [,) +oo ) $.
    ex-fpar.b $e |- B = RR $.
    ex-fpar.f $e |- F = ( sqrt |` A ) $.
    ex-fpar.g $e |- G = ( sin |` B ) $.
    $( Formalized example provided in the comment for ~ fpar .  (Contributed by
       AV, 3-Jan-2024.) $)
    ex-fpar $p |- ( ( X e. A /\ Y e. B )
                    -> ( X ( + o. H ) Y ) = ( ( sqrt ` X ) + ( sin ` Y ) ) ) $=
      ( caddc cfv csqrt csin wfn wceq cc cr vx vy wcel wa ccom co cop df-ov cxp
      cv cmpo cres cc0 cpnf cico wss sqrtf ffn ax-mp rge0ssre ax-resscn fnssres
      wf sstri reseq2i fneq1i sylibr mp2an wb id fneq12d mpbir sinf fpar fnmpoi
      a1i opex opelxpi fvco2 sylancr simpl simpr fvproj fveq2d fveq1i oveqan12d
      fvres eqtrid eqtr3id 3eqtrd ) FAUCZGBUCZUDZFGMEUEZUFFGUGZWNNZFONZGPNZMUFZ
      FGWNUHWMWPWOENZMNZFCNZGDNZUGZMNZWSWMEABUIZQWOXFUCWPXARUAUBABUAUJCNZUBUJDN
      ZUGZECAQZDBQZEUAUBABXIUKRXJOAULZUMUNUOUFZQZOSQZXMSUPZXNSSOVCXOUQSSOURUSXM
      TSUTVAVDXOXPUDOXMULZXMQXNSXMOVBXMXLXQAXMOIVEVFVGVHCXLRZXJXNVIKXRAXMCXLXRV
      JAXMRXRIVPVKUSVLXKPBULZTQZPSQZTSUPZXTSSPVCYAVMSSPURUSVAYAYBUDPTULZTQXTSTP
      VBTXSYCBTPJVEVFVGVHDXSRZXKXTVILYDBTDXSYDVJBTRYDJVPVKUSVLUAUBABCDEHVNVHZXG
      XHVQVOFGABVRXFMEWOVSVTWMWTXDMWMUAUBABCDEFGYEWKWLWAWKWLWBWCWDWMXEXBXCMUFWS
      XBXCMUHWKWLXBWQXCWRMWKXBFXLNWQFCXLKWEFAOWGWHWLXCGXSNWRGDXSLWEGBPWGWHWFWIW
      JWH $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Humor
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  April Fool's theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x F $.
    $( Poisson d'Avril's Theorem.  This theorem is noted for its
       _Selbstdokumentieren_ property, which means, literally,
       "self-documenting" and recalls the principle of _quidquid german dictum
       sit, altum viditur_, often used in set theory.  Starting with the
       seemingly simple yet profound fact that any object ` x ` equals itself
       (proved by Tarski in 1965; see Lemma 6 of [Tarski] p. 68), we
       demonstrate that the power set of the real numbers, as a relation on the
       value of the imaginary unit, does not conjoin with an empty relation on
       the product of the additive and multiplicative identity elements,
       leading to this startling conclusion that has left even seasoned
       professional mathematicians scratching their heads.  (Contributed by
       Prof.  Loof Lirpa, 1-Apr-2005.)  (Proof modification is discouraged.)
       (New usage is discouraged.)

       _A reply to skeptics can be found at ~ mmnotes.txt , under the
       1-Apr-2006 entry_. $)
    avril1 $p |- -. ( A ~P RR ( _i ` 1 ) /\ F (/) ( 0 x. 1 ) ) $=
      ( vy vx vz c1 ci cfv cr cpw wbr cc0 c0 wa wn cv c0r cop wcel wceq cmul co
      c1r cio cnr csn cxp cvv weq equid dfnul2 con2bii mpbi eleq1 mtbii vtocleg
      eqabri elex con3i pm2.61i df-br 0cn opeq2i eleq1i bitri mtbir intnan df-i
      mulridi fveq1i df-fv eqtri breq2i df-r wss cab sseq2 abbidv df-pw 3eqtr4g
      ax-mp breqi anbi1i notbii mpbir ) AFGHZIJZKZBLFUAUBZMKZNZOAFCPQUCRZKCUDZU
      EQUFUGZJZKZWJNZOWJWPWJBLRZMSZWRUHSZWSOZXADWRUHDPZWRTXBMSZWSDDUIZXCODUJXCX
      DXDODMDUKUQULUMXBWRMUNUOUPWSWTWRMURUSUTWJBWIRZMSWSBWIMVAXEWRMWILBLVBVIVCV
      DVEVFVGWKWQWHWPWJWHAWMWGKWPWFWMAWGWFFWLHWMFGWLVHVJCFWLVKVLVMAWMWGWOIWNTZW
      GWOTVNXFEPZIVOZEVPXGWNVOZEVPWGWOXFXHXIEIWNXGVQVREIVSEWNVSVTWAWBVEWCWDWE
      $.
  $}

  $( The law of excluded middle.  Act III, Theorem 1 of Shakespeare, _Hamlet,
     Prince of Denmark_ (1602).  Its author leaves its proof as an exercise for
     the reader - "To be, or not to be: that is the question" - starting a
     trend that has become standard in modern-day textbooks, serving to make
     the frustrated reader feel inferior, or in some cases to mask the fact
     that the author does not know its solution.  (Contributed by Prof.  Loof
     Lirpa, 1-Apr-2006.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  2bornot2b $p |- ( 2 x. B \/ -. 2 x. B ) $=
    ( c2 cmul wbr wn wo wi ax-1 mpd df-or mpbir ) BACDZLEZFMMGMLMGZMMLHMNHILMJK
    $.

  $( The classic "Hello world" benchmark has been translated into 314 computer
     programming languages - see ~ http://helloworldcollection.de .  However,
     for many years it eluded a proof that it is more than just a conjecture,
     even though a wily mathematician once claimed, "I have discovered a truly
     marvelous proof of this, which this margin is too narrow to contain."
     Using an IBM 709 mainframe, a team of mathematicians led by Prof.  Loof
     Lirpa, at the New College of Tahiti, were finally able to put it to rest
     with a remarkably short proof only four lines long.  (Contributed by Prof.
     Loof Lirpa, 1-Apr-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  helloworld $p |- -. ( h e. ( L L 0 ) /\ W (/) ( R. 1 d ) ) $=
    ( cnr cv c1 co c0 wbr cc0 wcel cop noel df-br mtbir intnan ) CEDFGHZIJZAFBK
    BHLSCRMZILTNCRIOPQ $.

  $( One plus one equals two.  Using proof-shortening techniques pioneered by
     Mr.  Mel L. O'Cat, along with the latest supercomputer technology, Prof.
     Loof Lirpa and colleagues were able to shorten Whitehead and Russell's
     360-page proof that 1+1=2 in _Principia Mathematica_ to this remarkable
     proof only two steps long, thus establishing a new world's record for this
     famous theorem.  (Contributed by Prof.  Loof Lirpa, 1-Apr-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  1p1e2apr1 $p |- ( 1 + 1 ) = 2 $=
    ( c2 c1 caddc co df-2 eqcomi ) ABBCDEF $.

  ${
    $d x A $.
    $( Law of identity (reflexivity of class equality).  Theorem 6.4 of [Quine]
       p. 41.

       This law is thought to have originated with Aristotle (_Metaphysics_,
       Book VII, Part 17).  It is one of the three axioms of Ayn Rand's
       philosophy (_Atlas Shrugged_, Part Three, Chapter VII).  While some have
       proposed extending Rand's axiomatization to include Compassion and
       Kindness, others fear that such an extension may flirt with logical
       inconsistency.  (Contributed by Stefan Allan, 1-Apr-2009.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eqid1 $p |- A = A $=
      ( vx cv wcel biid eqriv ) BAABCADEF $.
  $}

  ${
    $d x y z $.
    $( Division by zero is forbidden!  If we try, we encounter the DO NOT ENTER
       sign, which in mathematics means it is foolhardy to venture any further,
       possibly putting the underlying fabric of reality at risk.  Based on a
       dare by David A. Wheeler.  (Contributed by Mario Carneiro, 1-Apr-2014.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    1div0apr $p |- ( 1 / 0 ) = (/) $=
      ( vx vy vz cdiv cdm cc cc0 csn cdif wceq c1 wcel wa wn co c0 cv cmul crio
      cxp df-div riotaex dmmpo eqid eldifsni adantl necon2bi ax-mp ndmovg mp2an
      wne ) DEFFGHIZTJKFLZGULLZMZNZKGDOPJABFULBQCQROAQJZCFSDABCUAUQCFUBUCGGJUPG
      UDUOGGUNGGUKUMGFGUEUFUGUHKGFULDUIUJ $.
  $}

  $( Nothing seems to be impossible to Prof.  Lirpa.  After years of intensive
     research, he managed to find a proof that when given a chance to reach
     infinity, one could indeed go beyond, thus giving formal soundness to Buzz
     Lightyear's motto "To infinity... and beyond!"  (Contributed by Prof.
     Loof Lirpa, 1-Apr-2020.)  (Revised by Thierry Arnoux, 2-Aug-2020.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  topnfbey $p |- ( B e. ( 0 ... +oo ) -> +oo < B ) $=
    ( cc0 cpnf cfz co wcel clt wbr c0 noel cz wa wn wceq cxr pnfxr xrltnr ax-mp
    cr zre ltpnf syl mto intnan cxp cpw fzf fdmi ndmov eleq2i mtbir pm2.21i ) A
    BCDEZFZCAGHUNAIFAJUMIABKFZCKFZLMUMINUPUOUPCCGHZCOFUQMPCQRUPCSFUQCTCUAUBUCUD
    BCKDKKUEKUFDUGUHUIRUJUKUL $.

  ${
    $( 9 + 10 is not equal to 21.  This disproves a popular meme which asserts
       that 9 + 10 does equal 21.  See
       ~ https://www.quora.com/Can-someone-try-to-prove-to-me-that-9+10-21 for
       attempts to prove that 9 + 10 = 21, and see https://tinyurl.com/9p10e21
       for the history of the 9 + 10 = 21 meme.  (Contributed by BTernaryTau,
       25-Aug-2023.) $)
    9p10ne21 $p |- ( 9 + ; 1 0 ) =/= ; 2 1 $=
      ( c9 c1 cc0 cdc caddc co 10nn0 nn0cni 9cn dec10p addcomli 1nn0 9nn0 deccl
      c2 nn0rei 2nn0 9lt10 1lt2 decltc ltneii eqnetri ) ABCDZEFBADZOBDZUCAUDUCG
      HIAJKUDUEUDBALMNPBOABLQMLRSTUAUB $.

    $( 9 + 10 equals 21.  This astonishing thesis lives as a meme on the
       internet, and may be believed by quite some people.  At least repeated
       requests to falsify it are a permanent part of the story.  Prof.  Loof
       Lirpa did not rest until he finally came up with a computer verifiable
       mathematical proof, that only a fool can think so.  (Contributed by
       Prof.  Loof Lirpa, 26-Aug-2023.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    9p10ne21fool $p |- ( ( 9 + ; 1 0 ) = ; 2 1 -> F (/) ( 0 x. 1 ) ) $=
      ( c9 c1 cc0 cdc caddc co c2 wceq wn cmul c0 wbr wne 9p10ne21 df-ne pm2.21
      wi mpbi ax-mp ) BCDEFGZHCEZIZJZUCADCKGLMZRUAUBNUDOUAUBPSUCUEQT $.
  $}

  $( This factoid is e.g. useful for ~ nrt2irr .  Andrew has a proof, I'll have
     a go at formalizing it after my coffee break.  In the mean time let's add
     it as an axiom.  (Contributed by Prof.  Loof Lirpa, 1-Apr-2025.)
     (New usage is discouraged.) $)
  ax-flt $a |- ( ( N e. ( ZZ>= ` 3 ) /\ ( X e. NN /\ Y e. NN /\ Z e. NN ) )
    -> ( ( X ^ N ) + ( Y ^ N ) ) =/= ( Z ^ N ) ) $.

  ${
    $d N p q $.
    $( The ` N ` -th root of 2 is irrational for ` N ` greater than ` 2 ` .
       For ` N = 2 ` , see ~ sqrt2irr .  This short and rather elegant proof
       has the minor disadvantage that it refers to ~ ax-flt , which is still
       to be formalized.  For a proof not requiring ~ ax-flt , see ~ rtprmirr .
       (Contributed by Prof.  Loof Lirpa, 1-Apr-2025.)
       (Proof modification is discouraged.) $)
    nrt2irr $p |- ( N e. ( ZZ>= ` 3 ) -> -. ( 2 ^c ( 1 / N ) ) e. QQ ) $=
      ( vp vq wcel c2 cdiv co ccxp cv wceq cn wrex wa wne cexp cc cc0 a1i nnrpd
      cr c3 cuz cfv c1 cq wn wral cmul 2cnd simprr eluz3nn adantr nnnn0d expcld
      nncnd nnne0d expne0d divcan4d caddc 2timesd simpl simprl syl13anc eqnetrd
      nnzd ax-flt wb mulcld div11 syl112anc necon3bid eqnetrrd expdivd neeqtrrd
      mpbird divcld divne0d cxpexpzd 2re cle wbr rpdivcld rpred rpge0d recxpcld
      nnred cxpge0d rpreccld recxpf1lem mpbid nnrecred recnd cxpcld cxpne0d crp
      0le2 cxpcom syl3anc cxproot syl2anc 3eqtr3d neeqtrd neneqd ralrimivva clt
      ralnex2 sylib 2rp cxpgt0d biantrud elpqb bitrdi mtbird ) AUAUBUCDZEUDAFGZ
      HGZUEDZXPBIZCIZFGZJZCKLBKLZXNYAUFZCKUGBKUGYBUFXNYCBCKKXNXRKDZXSKDZMZMZXPX
      TYGXPXTAHGZXOHGZXTYGEYHNXPYINYGEXTAOGZYHYGEXRAOGZXSAOGZFGZYJYGEYLUHGZYLFG
      ZEYMYGEYLYGUIZYGXSAYGXSXNYDYEUJZUOZYGAXNAKDZYFAUKZULZUMZUNZYGXSAYRYGXSYQU
      PZYGAUUAVEZUQZURYGYOYMNYNYKNYGYNYLYLUSGZYKYGYLUUCUTYGXNYEYEYDUUGYKNXNYFVA
      YQYQXNYDYEVBZAXSXSXRVFVCVDYGYOYMYNYKYGYNPDYKPDYLPDYLQNYOYMJYNYKJVGYGEYLYP
      UUCVHYGXRAYGXRUUHUOZUUBUNUUCUUFYNYKYLVIVJVKVOVLYGXRXSAUUIYRUUDUUBVMVNYGXT
      AYGXRXSUUIYRUUDVPZYGXRXSUUIYRYGXRUUHUPUUDVQZUUEVRVNYGEYHXPYIYGEYHXOETDYGV
      SRQEVTWAYGWPRYGXTAYGXTYGXRXSYGXRUUHSYGXSYQSWBZWCZYGXTUULWDZYGAUUAWFZWEYGX
      TAUUMUUNUUOWGYGAYGAUUASWHWIVKWJYGXTXOHGZAHGZUUPAOGZYIXTYGUUPAYGXTXOUUJYGX
      OYGAUUAWKZWLZWMYGXTXOUUJUUKUUTWNUUEVRYGXTWODXOTDATDUUQYIJUULUUSUUOXTXOAWQ
      WRYGXTPDYSUURXTJUUJUUAXTAWSWTXAXBXCXDYABCKKXFXGXNXQXQQXPXEWAZMYBXNUVAXQXN
      EXOEWODXNXHRXNAYTWKXIXJBCXPXKXLXM $.
  $}

  $( One's wisdom on matters of the universe can be refuted on April Fool's
     day.  (Contributed by Prof.  Loof Lirpa, 1-Apr-2026.)
     (New usage is discouraged.) $)
  nowisdomv $p |- -. W <" _I 5 "> dom _V $=
    ( cvv cdm cid c5 cs2 wbr cop wcel c0 wn wceq dmv vprc eqneltri opprc2 ax-mp
    wfun wnel cword cc0 chash cfv cfzo wfn s2cli wrdfn fnfun mp2b 0nelfun df-br
    co neli mtbir ) ABCZDEFZGAUOHZUPIUQJUPUOBIKUQJLUOBBMNOAUOPQJUPUPRZJUPSUPBTI
    UPUAUPUBUCUDULZUEURDEUFBUPUGUSUPUHUIUPUJQUMOAUOUPUKUN $.


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  (Future - to be reviewed and classified)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Planar incidence geometry
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Token for the class of planar incidence geometries. $)
  $c Plig $.

  $( Extend class notation with the class of all planar incidence
     geometries. $)
  cplig $a class Plig $.

  ${
    $d x a b c l $.
    $( Define the class of planar incidence geometries.  We use Hilbert's
       axioms and adapt them to planar geometry.  We use ` e. ` for the
       incidence relation.  We could have used a generic binary relation, but
       using ` e. ` allows to reuse previous results.  Much of what follows is
       directly borrowed from Aitken, _Incidence-Betweenness Geometry_, 2008,
       ~ http://public.csusm.edu/aitken_html/m410/betweenness.08.pdf .

       The class ` Plig ` is the class of planar incidence geometries, where a
       planar incidence geometry is defined as a set of lines satisfying three
       axioms.  In the definition below, ` x ` denotes a planar incidence
       geometry, so ` U. x ` denotes the union of its lines, that is, the set
       of points in the plane, ` l ` denotes a line, and ` a , b , c ` denote
       points.  Therefore, the axioms are: 1) for all pairs of (distinct)
       points, there exists a unique line containing them; 2) all lines contain
       at least two points; 3) there exist three non-collinear points.
       (Contributed by FL, 2-Aug-2009.) $)
    df-plig $a |- Plig = { x | (
     A. a e. U. x A. b e. U. x ( a =/= b -> E! l e. x ( a e. l /\ b e. l ) ) /\
     A. l e. x E. a e. U. x E. b e. U. x ( a =/= b /\ a e. l /\ b e. l ) /\
     E. a e. U. x E. b e. U. x E. c e. U. x A. l e. x
                                       -. ( a e. l /\ b e. l /\ c e. l ) ) } $.
  $}

  ${
    $d a b c l x G $.  $d a b c x P $.
    isplig.1 $e |- P = U. G $.
    $( The predicate "is a planar incidence geometry" for sets.  (Contributed
       by FL, 2-Aug-2009.) $)
    isplig $p |- ( G e. A -> ( G e. Plig <->
         ( A. a e. P A. b e. P ( a =/= b -> E! l e. G ( a e. l /\ b e. l ) ) /\
           A. l e. G E. a e. P E. b e. P ( a =/= b /\ a e. l /\ b e. l ) /\
           E. a e. P E. b e. P E. c e. P A. l e. G
                                     -. ( a e. l /\ b e. l /\ c e. l ) ) ) ) $=
      ( vx cv wne wel wreu wi cuni wral w3a wrex raleqbidv rexeqbidv wa wn wceq
      cplig unieq eqtr4di reueq1 imbi2d rexeqdv raleqbi1dv raleq df-plig elab2g
      3anbi123d ) DJEJKZDGLZEGLZUAZGIJZMZNZEUSOZPZDVBPZUOUPUQQZEVBRZDVBRZGUSPZU
      PUQFGLQUBZGUSPZFVBRZEVBRZDVBRZQUOURGCMZNZEBPZDBPZVEEBRZDBRZGCPZVIGCPZFBRZ
      EBRZDBRZQICUDAUSCUCZVDVQVHVTVMWDWEVCVPDVBBWEVBCOBUSCUEHUFZWEVAVOEVBBWFWEU
      TVNUOURGUSCUGUHSSVGVSGUSCWEVFVRDVBBWFWEVEEVBBWFUITUJWEVLWCDVBBWFWEVKWBEVB
      BWFWEVJWAFVBBWFVIGUSCUKTTTUNIDEFGULUM $.

    $( The predicate "is a planar incidence geometry".  (Contributed by BJ,
       2-Dec-2021.) $)
    ispligb $p |- ( G e. Plig <-> ( G e. _V /\
         ( A. a e. P A. b e. P ( a =/= b -> E! l e. G ( a e. l /\ b e. l ) ) /\
           A. l e. G E. a e. P E. b e. P ( a =/= b /\ a e. l /\ b e. l ) /\
           E. a e. P E. b e. P E. c e. P A. l e. G
                                     -. ( a e. l /\ b e. l /\ c e. l ) ) ) ) $=
      ( cplig wcel cvv cv wne wel wa wreu wi wral w3a wrex wn isplig biadanii
      elex ) BHIBJICKDKLZCFMZDFMZNFBOPDAQCAQUDUEUFRDASCASFBQUEUFEFMRTFBQEASDASC
      ASRBHUCJABCDEFGUAUB $.
  $}

  ${
    $d a b c l G $.  $d a b c P $.
    tncp.1 $e |- P = U. G $.
    $( In any planar incidence geometry, there exist three non-collinear
       points.  (Contributed by FL, 3-Aug-2009.) $)
    tncp $p |- ( G e. Plig -> E. a e. P E. b e. P E. c e. P A. l e. G
                                         -. ( a e. l /\ b e. l /\ c e. l ) ) $=
      ( cplig wcel cv wne wel wa wreu wi wral w3a wrex wn isplig ibi simp3d ) B
      HIZCJDJKZCFLZDFLZMFBNODAPCAPZUDUEUFQDARCARFBPZUEUFEFLQSFBPEARDARCARZUCUGU
      HUIQHABCDEFGTUAUB $.
  $}

  ${
    $d a b c l G $.  $d a b l L $.  $d a b c l P $.
    l2p.1 $e |- P = U. G $.
    $( For any line in a planar incidence geometry, there exist two different
       points on the line.  (Contributed by AV, 28-Nov-2021.) $)
    l2p $p |- ( ( G e. Plig /\ L e. G )
                -> E. a e. P E. b e. P ( a =/= b /\ a e. L /\ b e. L ) ) $=
      ( vl vc cplig wcel cv wne w3a wrex wi wel wa wreu wral eleq2 wceq pm2.43i
      wn isplig 3anbi23d 2rexbidv rspccv 3ad2ant2 biimtrdi imp ) BIJZCBJZDKZEKZ
      LZUMCJZUNCJZMZEANDANZUKULUSOZUKUKUODGPZEGPZQGBROEASDASZUOVAVBMZEANDANZGBS
      ZVAVBHGPMUCGBSHANEANDANZMUTIABDEHGFUDVFVCUTVGVEUSGCBGKZCUAZVDURDEAAVIVAUP
      VBUQUOVHCUMTVHCUNTUEUFUGUHUIUBUJ $.

    $d d G $.  $d a b c d l L $.  $d d P $.
    $( For any line in a planar incidence geometry, there exists a point not on
       the line.  (Contributed by Jeff Hankins, 15-Aug-2009.) $)
    lpni $p |- ( ( G e. Plig /\ L e. G ) -> E. a e. P a e/ L ) $=
      ( vb vl vc vd wcel cv wrex w3a wn eleq2 notbid weq eleq1w rspcev ex cplig
      wnel wral wi tncp wa wceq 3anbi123d rspccv w3o 3jaao 3ianor df-nel rexbii
      3imtr4g syl9r 3expia rexlimdv rexlimivv syl imp ) BUAJZCBJZDKZCUBZDALZVBF
      KZGKZJZHKZVHJZIKZVHJZMZNZGBUCZIALZHALFALVCVFUDZABFHIGEUEVQVRFHAAVGAJZVJAJ
      ZUFVPVRIAVSVTVLAJZVPVRUDVPVCVGCJZVJCJZVLCJZMZNZVSVTWAMZVFVOWFGCBVHCUGZVNW
      EWHVIWBVKWCVMWDVHCVGOVHCVJOVHCVLOUHPUIWGWBNZWCNZWDNZUJVDCJZNZDALZWFVFVSWI
      WNVTWJWAWKVSWIWNWMWIDVGADFQWLWBDFCRPSTVTWJWNWMWJDVJADHQWLWCDHCRPSTWAWKWNW
      MWKDVLADIQWLWDDICRPSTUKWBWCWDULVEWMDAVDCUMUNUOUPUQURUSUTVA $.
  $}

  ${
    $d a b G $.  $d a b A $.
    $( There is no "one-point line" in a planar incidence geometry.
       (Contributed by BJ, 2-Dec-2021.)  (Proof shortened by AV,
       5-Dec-2021.) $)
    nsnlplig $p |- ( G e. Plig -> -. { A } e. G ) $=
      ( va vb cplig wcel csn wa cv wne w3a cuni wrex wn eqid l2p wceq elsni syl
      wi weq eqtr3 eqneqall syl2an impcom 3impb a1i rexlimivv pm2.01da ) BEFZAG
      ZBFZUJULHCIZDIZJZUMUKFZUNUKFZKZDBLZMCUSMULNZUSBUKCDUSOPURUTCDUSUSURUTTUMU
      SFUNUSFHUOUPUQUTUPUQHUOUTUPUMAQZUNAQZUOUTTZUQUMARUNARVAVBHCDUAVCUMUNAUBUT
      UMUNUCSUDUEUFUGUHSUI $.
  $}

  ${
    $d a b G $.  $d a b A $.
    $( Alternate version of ~ nsnlplig using the predicate ` e/ ` instead of
       ` -. e. ` and whose proof is shorter.  (Contributed by AV, 5-Dec-2021.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    nsnlpligALT $p |- ( G e. Plig -> { A } e/ G ) $=
      ( va vb cplig wcel csn wnel wa cv wne w3a cuni wrex eqid l2p wi elsni syl
      wceq weq eqtr3 eqneqall syl2an impcom 3impb rexlimivv simpr pm2.61danel
      a1i ) BEFZAGZBHZULBUKULBFICJZDJZKZUNULFZUOULFZLZDBMZNCUTNUMUTBULCDUTOPUSU
      MCDUTUTUSUMQUNUTFUOUTFIUPUQURUMUQURIUPUMUQUNATZUOATZUPUMQZURUNARUOARVAVBI
      CDUAVCUNUOAUBUMUNUOUCSUDUEUFUJUGSUKUMUHUI $.
  $}

  $( There is no "empty line" in a planar incidence geometry.  (Contributed by
     AV, 28-Nov-2021.)  (Proof shortened by BJ, 2-Dec-2021.) $)
  n0lplig $p |- ( G e. Plig -> -. (/) e. G ) $=
    ( cplig wcel cvv csn c0 nsnlplig wceq vprc snprc mpbi eqcomi eleq1i sylnibr
    wn ) ABCDEZACFACDAGFPAPFDDCOPFHIDJKLMN $.

  ${
    $d a b G $.
    $( Alternate version of ~ n0lplig using the predicate ` e/ ` instead of
       ` -. e. ` and whose proof bypasses ~ nsnlplig .  (Contributed by AV,
       28-Nov-2021.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    n0lpligALT $p |- ( G e. Plig -> (/) e/ G ) $=
      ( va vb cplig wcel c0 wnel wa cv wne w3a cuni wrex eqid l2p noel 3ad2ant2
      wi pm2.21i a1i rexlimivv syl simpr pm2.61danel ) ADEZFAGZFAUEFAEHBIZCIZJZ
      UGFEZUHFEZKZCALZMBUMMUFUMAFBCUMNOULUFBCUMUMULUFRUGUMEUHUMEHUJUIUFUKUJUFUG
      PSQTUAUBUEUFUCUD $.
  $}

  ${
    $d a b c l G $.  $d a b c P $.  $d a b l A $.  $d a b l B $.
    eulplig.1 $e |- P = U. G $.
    $( Through two distinct points of a planar incidence geometry, there is a
       unique line.  (Contributed by BJ, 2-Dec-2021.) $)
    eulplig $p |- ( ( G e. Plig /\ ( ( A e. P /\ B e. P ) /\ A =/= B ) ) ->
                                            E! l e. G ( A e. l /\ B e. l ) ) $=
      ( va vb vc cplig wcel wa wne cv wreu wel wi wral w3a wrex wn isplig simp1
      ibi wceq simpl simpr neeq12d eleq1 bi2anan9 reubidv imbi12d rspc2gv com23
      imp com12 3syl ) DJKZACKBCKLZABMZLZAENZKZBVBKZLZEDOZURGNZHNZMZGEPZHEPZLZE
      DOZQZHCRGCRZVIVJVKSHCTGCTEDRZVJVKIEPSUAEDRICTHCTGCTZSZVOVAVFQURVRJCDGHIEF
      UBUDVOVPVQUCVAVOVFUSUTVOVFQUSVOUTVFVNUTVFQGHABCCVGAUEZVHBUEZLZVIUTVMVFWAV
      GAVHBVSVTUFVSVTUGUHWAVLVEEDVSVJVCVTVKVDVGAVBUIVHBVBUIUJUKULUMUNUOUPUQUO
      $.
  $}

  $( Any planar incidence geometry ` G ` can be regarded as a hypergraph with
     its points as vertices and its lines as edges.  See ~ incistruhgr for a
     generalization of this case for arbitrary incidence structures (planar
     incidence geometries are such incidence structures).  (Proposed by Gerard
     Lang, 24-Nov-2021.)  (Contributed by AV, 28-Nov-2021.) $)
  pliguhgr $p |- ( G e. Plig -> <. U. G , ( _I |` G ) >. e. UHGraph ) $=
    ( cplig wcel cuni cid cres cop cuhgr cdm cpw c0 csn cdif wf wf1o wi f1oi wb
    wss cvv f1of pwuni wa cin wceq wn n0lplig adantr disjsn sylibr adantl mpbid
    reldisj mpan2 fss sylan2 mp2b ffdmd uniexg resiexg isuhgrop syl2anc mpbird
    ex ) ABCZADZEAFZGHCZVGIVFJZKLZMZVGNZVEAVKVGAAVGOAAVGNZVEAVKVGNZPAQAAVGUAVMV
    EVNVEVMAVKSZVNVEAVISZVOAUBVEVPUCZAVJUDKUEZVOVQKACUFZVRVEVSVPAUGUHAKUIUJVPVR
    VORVEAVJVIUMUKULUNAAVKVGUOUPVDUQURVEVFTCVGTCVHVLRABUSABUTVGVFTTVAVBVC $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Aliases kept to prevent broken links
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section contains a few aliases that we temporarily keep to prevent
  broken links.  If you land on any of these, please let the originating site
  and/or us know that the link that made you land here should be changed.

$)

  ${
    dummylink.1 $e |- ph $.
    dummylink.2 $e |- ps $.
    $( Alias for ~ a1ii that may be referenced in some older works, and kept
       here to prevent broken links.

       If you landed here, please let the originating site and/or us know that
       the link that made you land here should be changed to a link to ~ a1ii .

       (Contributed by NM, 7-Feb-2006.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dummylink $p |- ph $=
      (  ) C $.
  $}

  $( Alias for ~ idALT that may be referenced in some older works, and kept
     here to prevent broken links.

     If you landed here, please let the originating site and/or us know that
     the link that made you land here should be changed to a link to ~ idALT .

     (Contributed by NM, 30-Sep-1992.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  id1 $p |- ( ph -> ph ) $=
    ( idALT ) AB $.

