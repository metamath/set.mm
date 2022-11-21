$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Metamath source file: axioms for Peano arithmetic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( Copyright (GPL) 2004 Robert Solovay, PO Box 5949, Eugene OR, 97405   $)
$( Comments welcome; email to:  solovay at gmail dot com $)

$( Version of 22-Jun-2021 $)
$( Replaces prior version of 13-July-04 $)
$( 22-Jun-2021 (Patrick Brosnan) - Add missing distinct variable constraints
   to pa_ax7 $)
$( 7-Oct-2004 (N. Megill) - Minor fixes to conform to strict Metamath spec $)
$( 11-Oct-2004 (N. Megill) - "$a implies" --> "$a |- implies" at line 224 $)
$( 24-Jun-2006 (N. Megill) - Made label and math symbol names spaces
       disjoint, as required by the 24-Jun-2006 modification of the Metamath
       specification.  Specifically, the labels binop, logbinop, binpred,
       and quant were changed to binop_, logbinop_, binpred_, and quant_
       respectively. $)
$( 11-Nov-2014 (N. Megill) - updated R. Solovay's email address $)

$( This file is a mixture of two sorts of things:

1) Formal metamath axioms and supporting material. [$f and $d
   statements for example.]

2) Informal metamathematical arguments that show our axioms suffice to
   "do Peano in metamath".

All our metamathematical arguments are quite constructive and
certainly could be formalized in Primitive Recursive Arithmetic. $)

$( We shall slightly deviate from the treatment in Appendix C of the
metamath book. We assume that for each constant c an infinite subset
of the variables is preassigned to that constant.

In particular we will have a constant var. Among our other constants
will be all the symbols of Peano arithmetic except the variables. The
variables of the formal language of Peano Arithmetic will be
identified with the variables attached to the constant symbol var. In
this way each well formed formula or term of PA will *be* a certan
metamath expression. $)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
            Syntax
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c |-  wff term var $.

$( The next set of axioms will give the inductive definition of
terms. We will be using Polish notation in our formal development of
the syntax of PA. $)

$v s t u s0 s1 t0 t1 $.

ts $f term s $.
tt $f term t $.
tu $f term u $.
ts0 $f term s0 $.
ts1 $f term s1 $.
tt0 $f term t0 $.
tt1 $f term t1 $.

$v v x y z $.
varv $f var v $.
varx $f var x $.
vary $f var y $.
varz $f var z $.

$c 0 S + * $.

$( It is often possible to treat + and * in parallel. The following
device allows us to do this. $)

$c BINOP $.
$v binop $.
binop_ $f BINOP binop $.
binop_plus $a BINOP + $.
binop_times $a BINOP * $.

tvar $a term v $.
tzero $a term 0 $.
tsucc $a term S s $.
tbinop $a term binop s t $.

$( The next set of axioms will give the inductive definition of wff $)

$c not or and implies iff $.
$c LOGBINOP $.
$v logbinop $.
logbinop_ $f LOGBINOP logbinop $.
logbinopor $a LOGBINOP or $.
logbinopand $a LOGBINOP and $.
logbinopimplies $a LOGBINOP implies $.
logbinopiff $a LOGBINOP iff $.

$c = < $.
$c BINPRED $.
$v binpred $.
binpred_ $f BINPRED binpred $.
binpred_equals $a BINPRED = $.
binpred_less_than $a BINPRED < $.

$c forall exists $.
$c QUANT $.
$v quant $.
quant_ $f QUANT quant $.
quant_all $a QUANT forall $.
quant_ex $a QUANT exists $.

$v phi psi chi $.
wff_phi $f wff phi $.
wff_psi $f wff psi $.
wff-chi $f wff chi $.

wff_atom $a wff binpred s t $.
wff_not $a wff not psi $.
wff_logbinop $a wff logbinop psi phi $.
wff_quant $a wff quant v phi $.

$( This completes our description of the syntactic categories of wff
and term $)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
            "Correct" axioms
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( In the various sections of this file we will be adding various
axioms [$a statements]. The crucial correctness property that they
will have is the following:

     Consider a substitution instance of the axiom such that the only
     variables remaining in the instance [in either hypothesis or
     conclusion] are of type var. Then if all the hypotheses [$e
     statements] have the form
          |- phi
     [where phi is a theorem of PA] then the conclusion is also a
     theorem of PA.

     The verification that the various axioms we add are correct in
     this sense will be "left to the reader". Usually the proof that I
     have in mind is a semantic one based upon the consideration of
     models of PA. $)
$( I will give a discussion at the end of this document as to why
     sticking with this correctness condition on axioms suffices to
     guarantee that only correct theorems of Peano arithmetic are
     proved.
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
         Propositional logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( We follow closely the treatment in set.mm. We do have to change the
axioms "into Polish". $)

ax-1 $a |- implies phi implies psi phi $.

ax-2 $a |- implies
              implies phi implies psi chi
              implies
                 implies phi psi
                 implies phi chi  $.
ax-3 $a |- implies
              implies not phi not psi
              implies psi phi $.

$( Modus ponens: $)
${
   min $e |- phi $.
   maj $e |- implies phi psi $.
   ax-mp $a |- psi $.
$}

bi1 $a |- implies
          iff phi psi
          implies phi psi $.
bi2 $a |- implies
          iff phi psi
          implies psi phi $.
bi3 $a |- implies
          implies phi psi
          implies
             implies psi phi
             iff phi psi $.
df-an $a |- iff
               and phi psi
               not implies phi not psi $.
df-or $a |- iff
               or phi psi
               implies not phi psi $.

$( Equality axioms $)

$( From here on out, I won't make an effort to cordinate labels
between my axioms and those of set.mm $)

eq-refl $a |- = t t $.
eq-sym $a |- implies = s t = t s $.
eq-trans $a |- implies
                and = s t = t u
                = s u $.
eq-congr $a |- implies
            and = s0 s1 = t0 t1
            iff binpred s0 t0 binpred s1 t1 $.

$( The next two axioms were missing in the previous draft of
peano.mm. They are definitely needed. $)

eq-suc $a |- implies
                  = s t
                  = S s S t $.
eq-binop $a |- implies
                  and = s0 s1 = t0 t1
                  = binop s0 t0 binop s1 t1 $.

$( Lemma 1 $)

$( Lemma 1 of the 2004 version of this document was not needed in the
subsequent development and has been deleted. I decided not to change
the numbering of subsequent lemmas. $)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
             Free and bound variables; alpha equivalence
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( It will be useful to warm up with some familiar concepts. Let PHI
   be a well-formed formula of Peano arithmetic. Then Phi is a finite
   sequence of symbols, s_1 ... s_n.

   Following Shoenfield's treatment in "Mathematical Logic" we use the
   term "designator" for a sequence of symbols that is either a term
   or a wff. A basic result says that each s_i is the initial symbol
   of precisely one subsequence of s_1 ... s_n which is a designator.

   Suppose that s_i is a variable. We say that s_i is bound in PHI if
   there is a subformula of PHI containing s_i whose initial symbol is
   a quantifier and whose second symbol is the same variable as s_i.

   [Otherwise s_i is *free* in PHI.]

   If s_i is a bound variable, then there is a shortest subformula of
   PHI in which s_i is bound. The quantifier beginning this subformula
   is the quantifier that *binds* s_i. $)

$( alpha equivalence $)

$( Let Phi_1 and Phi_2 be well-formed formulas of PA. Say Phi_1 is s_1
... s_n and Phi_2 is t_1 ... t_m.

    We say that Phi_1 and Phi_2 are alpha-equialent if:

1) n = m.

2) Let 1 <= i <= n. Then s_i is a constant iff t_i is; in that case,
   they are the *same* constant.

3) Let 1 <= i <= n. Suppose that s_i is a variable. [So t_i is a
   variable as well.] Then s_i is free in Phi_1 iff t_i is free in
   Phi_2. If s_i is free in Phi_1, then s_i = t_i.

4) Let 1 <= i <= n. Suppose that s_i is a variable that is bound in
   Phi_1. [It follows that t_i is a variable that is bound in Phi_2.]
   Let s_j be the quantifier that binds s_i. Then t_j is the
   quantifier that binds t_i.

[This ends the definition of alpha-equivalence.]

It is indeed true that alpha-equivalence is an equivalence relation.
$)

$( Trim formulas $)

$( The following concept is non-standard. A well-formed formula of PA
is *trim* if:

   1) No variable occurs both free and bound in Phi.

   2) Distinct quantifiers bind distinct variables.

[So
exists x exists x = x x
is not trim since the two quantifiers both bind the variable x.]

   Clearly every formula is alpha-equivalent to some trim
   formula. Moreover, we can assume that the bound variables of this
   trim equivalent avoid some specified finite set of variables.
$)

$( Here is the next Lemma we are heading toward. We can add a finite
number of correct axioms to our file so that once this is done, if
Phi_1 and Phi_2 are alpha-equivalent formulas then [subject to the
requirement that any pair of distinct  variables appearing in Phi_1 or
Phi_2 is declared disjoint]

      |- iff Phi_1 Phi_2
is a theorem of Metmath [i.e. follows from the given axioms].

In view of the remarks about trim formulas, we are reduced to the
following special case: Phi_2 is trim and no bound variable of Phi_2
appears [free or bound] in Phi_1.

We fix Phi_1 and Phi_2 subject to this restriction. We will develop
the axioms we need in the course of the proof. Of course, the reader
should verify that we could have specified them in advance. In
particular the additional axioms we list will not depend on Phi_1 or Phi_2. $)

$( Our proof strategy is as follows;

To each subformula Psi of Phi_1, we shall attach a claim C(Psi) [which
will also be a well-formed formula of PA]. We will prove in Metamath
the various claims C(Psi). The construction of these proofs will be an
inductive one [by induction on the length of the subformula,
say]. From the claim C(Phi_1), the desired equivalence of Phi_1 and
Phi_2 will easily follow. $)

$( Weak alpha-equivalence $)

$( Before describing the claims C(Psi), I need to introduce the notion
of weak alpha-equivalence. Let Psi_1 and Psi_2 be two well-formed
formulas of PA.

Say Psi_1 is s_1 ... s_m and Psi_2 is t_1 ... t_n.

Then Psi_1 and Psi_2 are weakly alpha equivalent iff:

1) m = n;

2) Let 1 <= i <= n. Then s_i is a constant iff t_i is; in that case,
   they are the *same* constant.

3) Let 1 <= i <= n. Suppose that s_i is a variable. [So t_i is a
   variable as well.] Then s_i is free in Psi_1 iff t_i is free in
   Psi_2.

3a) Let 1 <= i < j <= n. Suppose that s_i and s_j are variables free
in Psi_1. [It follows that t_i and t_j are free variables in Psi_2.]
Then s_i = s_j iff t_i = t_j.

4) Let 1 <= i <= n. Suppose that s_i is a variable that is bound in
   Psi_1. [It follows that t_i is a variable that is bound in Psi_2.]
   Let s_j be the quantifier that binds s_i. Then t_j is the
   quantifier that binds t_i.

[This ends the definition of weak alpha-equivalence.] $)

$( I need a pedantic fact:

   Proposition 2.1. Let Phi_1 = s_1,..., s_m and Phi_2 = t_1...t_m be
   as above. Let 1 <= i <= j <= m. Then s_i ... s_j is a term
   [formula] iff t_i ... t_j is.

   The proof is by induction on j - i and is straightforward. [It
   splits into cases according to what s_i is.] $)

$( The following explains the importance of "weak alpha equivalence":

   Proposition 2.2.
   Let Psi_1 be a subformula of Phi_1, and Psi_2 the corresponding
   subformula of Phi_2. (Cf. the "pedantic fact" just above.) Then
   Psi_1 and Psi_2 are weakly alpha equivalent.

   Only clause 3a) of the definition of weak alpha equivalence
   requires discussion:

   Say Psi_1 occupies positions i ... j of Phi_1. Let i <= a < b <= j
   and let s_a and s_b be the same variable x. We suppose that s_a and
   s_b are free in Psi_1. We shall show that t_a = t_b. {This will
   prove one direction of the iff; the other direction is proved
   similarly.}

   If s_a and s_b are both free in Phi_1 then our claim is clear since
   Phi_1 and Phi_2 are alpha equivalent. If not, let Theta_1 be the
   smallest subformula of Phi_1 in which one of s_a and s_b is
   bound. Then both s_a and s_b are bound by the quantifer that begins
   Theta_1.

   Let Theta_2 be the subformula of Phi_2 that corresponds to
   Theta_1. Using the alpha equivalence of Phi_1 and Phi_2 we see that
   both t_a and t_b are bound by the quantifer that begins
   Theta_2. Hence t_a = t_b.

   $)

   $( We are now able to begin the definition of C(Psi_1) for Psi_1 a
   subformula of Phi_1. It will have the form

   implies H(Psi_1)
           iff Psi_1 Psi_2

   where Psi_2 is the subformula of Phi_2 that corresponds to Psi_1.

  It remains to describe H(Psi_1):

  Let w be a variable that does not appear [free or bound] in either
  Phi_1 or Phi_2. Let x_1 ... x_r be the free variables appearing in
  Psi_1 [listed without repetitions]. Because Psi_1  is weakly alpha
  equivalent to Psi_2, we can define a bijection between the free
  variables of Psi_1 and those of Psi_2 thus. If x_i appears freely in
  position j of Psi_1 then the corresponding free variable of Psi_2,
  say y_i, appears in position j of Psi_2.

  H(Psi_1) is the conjunction of the following equalities:

  1) = w w ;

  2) = x_i y_i (for i = 1 ... r).

  This completes our description of C(Psi_1). $)

  $( Consider first C(Phi_1). Because Phi_1 is alpha equivalent to
  Phi_2, H(Phi_1) is the conjunction of equalities of the form = a a .
  Hence Metamath can prove H(Phi_1) and can see that C(Phi_1) is
  equivalent to the equivalence:

      iff Phi_1 Phi_2
  $)

$( So it will be sufficient to see that Metamath [after enrichment with
some additional correct axioms] can prove C(Psi_1) for every
subformula Psi_1 of Phi_1. The proof of this proceeds by induction on
the length of Psi_1.

If Psi_1 is atomic, our claim is easily proved using the equality
axioms.

The cases when Psi_1 is built up from smaller formulas using propositional
connectives are easily handled since Metamath knows propositional
logic.

$)

$( It remains to consider the case when Psi_1 has the form Q x Chi_1
where Q is a quantifier.

It is clear that Psi_2 has the form Q y Chi_2 [where Chi_2 is the
subformula of Phi_2 that corresponds to Chi_1]. We will consider two
cases;

Case A: x = y;

Case B: x != y. $)

$( To handle Case A we adjoin the following axiom [which the reader
should verify is correct]. $)

${ $d phi x $.
   alpha_hyp1 $e |- implies phi
              iff psi chi $.
   alpha_1 $a |- implies phi
              iff quant x psi
                  quant x chi $. $}

$( We apply this axiom with H(Psi_1) in the role of phi and Q in the
role of quant. Chi_1 is in the role of psi and Chi_2 is in the role of
chi.

To see that the needed instance of alpha_hyp1 holds, note that
H(Chi_1) is either H(Psi_1) [up to a possible rearrangement of
conjuncts] or the conjunction of H(Psi_1) with the conjunct
= x x

So our needed instance follows from C(Chi_1), equality axioms and
propositional logic $)

$( We turn to case B. It is worthwhile to remind the reader that Phi_2
has been chosen so that no bound variable of Phi_2 appears either free
or bound in Phi_1.

Proposition 2.3. y does not appear [free or bound] in Psi_1. x does
not appear [free or bound] in Psi_2.

Proof: y appears bound in Psi_2. Hence it doesn't even appear [free or
bound] in Phi_1.

Suppose that x appears in Psi_2. Then this appearence must be free in
Phi_2. {Otherwise, x would not appear in Phi_1 but it is the second
symbol of Psi_1.} So at the same spot in Psi_1 x also appears, and
this occurrence is free in Phi_1. {This follows from the fact that
Phi_1 and Phi_2 are alpha equivalent.} But clearly this occurrence of
x in Psi_1 will be bound by the quantifier that starts
Psi_1. Contradiction! $)

$( Proposition 2.3 has the following immediate consequence:

Proposition 2.4: Neither of the variables x or y occurs in H(Psi_1).

	    Also it is easy to check that [up to propositional logic]
	    H(Chi_1) is either H(Psi_1) or the conjunction of H(Psi_1)
	    with
                    = x y

It follows that from C(Chi_1) one can deduce [using propositonal
logic] the following:

(A) implies H(Psi_1)
            implies = x y
            iff Chi_1 Chi_2 $)

$( Next we introduce the following Metamath axiom [which the reader
should verify is correct] $)

${ $d phi x $.

   alpha_hyp2 $e |- implies phi chi $.
   alpha_2    $a |- implies phi forall x chi $.
$}

$( Using this axiom we can deduce from (A) and Proposition 2.4
the following:

(B) implies H(Psi_1)
            forall x forall y implies = x y
                                      iff Chi_1 Chi_2
$)

$( We need to introduce another axiom [which the reader should verify
is correct] $)

${ $d phi y $.
   $d psi x $.
   $d x y $.
   alpha_3 $a |- implies forall x forall y implies = x y
                                   iff phi psi
                         iff quant x phi quant y psi $.
$}

$( From this axiom, (B) and Proposition 2.3 we easily deduce:

(C) implies H(Psi_1)
            iff Psi_1 Psi_2

which is C(Psi_1) $)

$( The following lemma should now be clear to the reader:

Lemma 2. Let Phi and Phi* be alpha equivalent formulas of PA. Then
using the axioms so far introduced, we can prove in Metamath the
sequence

|- iff Phi_1 Phi_2

from the disjointness assumption that all the distinct variables
appearing in Phi_1 or Phi_2 are asserted to be distinct in a $d
assumption.  $)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                Axioms and inference rules of predicate logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( Our next task is to prove the rule of inference and the axiom
associated to the "forall" quantifier. $)

$( Let's start with the rule of inference. We have to show that if

|- implies phi chi

and phi does not contain x free then also

|- implies phi forall x chi.

   But this is easy. In view of what we have just shown, it is ok to
   replace phi by an alpha-equivalent formula that does not contain x
   at all. {In both our hypothesis and conclusion.}

   But then we just need to invoke the axiom alpha_2. $)

$( We now turn to the axiom of "forall elimination". To state it we
introduce the familiar notion of substituting a term for the free
occurrences of a variable. So let phi be a formula, x a variable and t
a term. By phi[t/x] we mean the formula obtained by simultaneously
replacing each free occurrence of x in phi by a copy of the term t. {A
more rigorous definition would proceed by induction on the structure
of phi.}

   We say that t is substitutable for x at the free occurrence of x in
   phi [or just "substitutable" if we are being terse] if no variable
   occuring in t falls under the scope of any quantifer of
   phi. {Again, I am presuming this notion known; otherwise, I'd be
   more careful with this definition.}

   The final group of axioms of predicate calculus that we need to
   derive have the following form:

(*)   implies
        forall x phi
        phi[t/x]

   **where** t is substitutable for x in phi.

Our next step is to show that it suffices to prove the following
special case of this axiom. phi x and t satisfy the following three
conditions:


	(1) The variable x does not appear in the term t.

        (2) No bound variable of phi appears in t.

        (3) The variable x does not appear bound in phi.

We can see this as follows. We can clearly find a formula
   forall y psi
which is alpha equivalent to forall x phi such that:
     (1') The variable y does not appear in the term t;
     (2') No bound variable of psi appears in t;
     (3') The variable y does not appear bound in psi.

Using the fact that t is substitutable for x in phi we easily see that
phi[t/x] is alpha equivalent to psi[t/y]. It follows that (*) is
alpha-equivalent to:
(**)  implies
        forall y psi
        psi[t/y]

Hence Metamath can prove the equivalence of (*) and (**). But in view
of (1') through (3'), the instance (**) of for all elimination meets
our additional requirements (1) through (3).

In the remainder of our discussion we shall assume then that phi, x
and t meet the requirements (1) through (3). Note that it follows from
(2) that t is substitutable for x in phi.

[N.B. We cannot assume that the variables appearing in t do not appear
in phi.]

Here is the key idea of our approach: The formula phi[t/x] (under the
hypotheses (1) -- (3) just given) is equivalent to:

forall x implies
            = x t
            phi

$)

$( We start by adding the following [correct!] axiom $)

${ $d x t $.
   all_elim $a |- implies
                   forall x phi
                   forall x implies
                              = x t
                              phi $.
$}

$( Using this axiom we can reduce our proof that Metamath proves all
instances of "all elimination" to the following lemma:

Lemma 3. Let t be a term of PA and phi a formula of PA. We assume:
1) The variable x does not occur in t;
2) No bound variable of phi appears in t.
3) The variable x does not occur bound in phi.

Then [after adding finitely many additional correct axioms whose
choice does not depend on phi] we can prove in Metamath:

|- iff
     forall x implies
        = x t
        phi
    phi[t/x]

$)

$( We shall need a preliminary result:

Proposition 3.1 Let phi t and x obey our standing hypotheses 1) --
3). Let psi be a subformula of phi.

Then [after adding finitely many additional correct axioms whose
choice does not depend on phi] we can prove in Metamath:

|- implies = x t
           iff psi psi[t/x]

The construction of such proofs [like many previous arguments] is by
induction on the tree of subformulas of phi. $)

$( The first case is when psi is atomic. This case is easily handled
using the equality axioms.

The second case is when the principal connective of psi is a
propositional connective. This case follows easily using propositional
logic from our inductive hypotheses concerning the subformulas of psi.

$)

$( The final case is when the principal connective of psi is a
quantifier. This case is handled using the following axiom: $)

${ $d x y $.
   $d y t $.
   all_elim_hyp2 $e |- implies = x t
                    iff phi chi $.
   all_elim2 $a |- implies = x t
                   iff quant y phi
                       quant y chi $.
$}

$( The proof of Proposition 3.1 is now complete. We apply it to phi
and get that Metamath proves:
|- implies = x t
           iff phi phi[t/x]

Here phi and t stand for the particular wff and term of t under
discussion and are not literal metavariables of Metamath.

We also know at this point that Metamath proves:

|- implies forall x phi
           forall x implies = x t
                    phi

We would be done if we could prove in Metamath:

|- implies forall x implies = x t
                            phi
           phi[t/x]

But this will follow easily from the next axiom [which is inelegant
but correct].

 $)

${
$d x chi $.
$d x t $.

 all_elim3_hyp1 $e |- implies = x t
                           iff phi chi $.
all_elim3 $a |- implies forall x implies = x t
                                         phi
                     chi $. $}

$( This completes our discussion of "forall-elimination". $)
$( It is time to introduce the definition of the
"exists" quantifier $)

exists_def $a |- iff
              exists x phi
              not forall x not phi $.

$( Of course, the axiom and rule of inference for "exists" follow from
this definition and the corresponding inference rule or axiom scheme
for "forall". $)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
         The non-logical axioms of Peano Arithmetic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( At this point, we know that Metamath can prove any logically valid
wff of PA. It remains to add the axioms of PA. $)

$( First we give the particular axioms of PA. Then we discuss the
induction scheme $)

pa_ax1 $a |- not = 0 S x $.
pa_ax2 $a |- implies = S x S y
                     = x y $.
pa_ax3 $a |- = x
               + x 0 $.
pa_ax4 $a |- = S + x y
               + x S y $.
pa_ax5 $a |- = 0
               * x 0 $.
pa_ax6 $a |- = + * x y x
               * x S y $.
${
  $d z x $.  $d z y $.
  pa_ax7 $a |- iff
               < x y
               exists z = y + x S z $.
$}

$( It suffices to give the induction axiom for the case when phi does
not contain x free. For the usual form of the axiom follows from this
special case by first order logic. $)

${
$d phi x $.
$d x y $.
induction $a
|- implies
   and forall y implies = y 0 phi
       forall x implies forall y implies = y x phi
                        forall y implies = y S x phi
   forall x forall y implies = y x phi $.
$}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
           Discussion of correctness
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
Let's agree that when I say "Metamath proves PHI" I mean "Metamath"
enriched with all the preceding axioms in this document.

The issue is the following. For what formulas Phi is there a proof in
Metamath from no $e type assumptions of the sequencce
    |- Phi.

(Recall that I am identifying the well-formed formulas of Peano with
certain of the Metamath strings of symbols. This is done by
identifying the object variables of our language with the
metavariables of type var.)

The claim is that these are precisely those Phi which are theorems of
the usual formulation of Peano Arithmetic.

One direction should be clear by this point. We have developed the
first order predicate calculus within Metamath and included the usual
axioms of Peano arithmetic [or equivalents]. So any theorem of Peano
Arithmetic [as usually formulated] can be proved in Metamath.

To go in the other direction, suppose that there is a proof in
Metamath of |- Phi. So the final line of the proof contains only
variables of type var. But there might well be variables of other
kinds in the body of the proof. For example, there might be a variable
phi of kind wff.

The critical such variables are those that appear in lines of the
proof beginning with |-.  What we do is replace such variables (of
kind different than var) [one by one] by sequences of constants of the
same type.  (So phi might be replaced by the three symbol string "= 0
0".) It is not hard to see that after this substitution the result can
be massaged to a correct proof. There are two points to notice.

     a) Since the string by which we replaced the variable contains no
     variables itself the process converges and no disjointness
     conditions [$d restrictions] are violated.

     b) We may have to add a trivial few lines to prove the "type
     assertion". In our example, the line "wff phi" will be replaced
     by the line "wff = 0 0". This line is no longer immediate but
     must be proved by a four line argument.

At the end, there results a proof where all the lines that begin with
"|-" contain only variables of type var. But now our correctness
assumptions allow us to verify step by step that each such line is a
theorem of Peano arithmetic.
$)

$( For Emacs $)
$( Local Variables: $)
$( eval:'(show-paren-mode t) $)
$( End: $)
