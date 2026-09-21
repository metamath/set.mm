$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Peter Mazsa
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Contents: ~ https://us.metamath.org/mpeuni/mmtheorems.html#dtl:20.22 $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Notations
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c |X. $. $( Range Cartesian product symbol. $)

  $c QMap $. $( The class of quotient maps $)
  $c AdjLiftMap $. $( The class of adjoined lift maps $)
  $c BlockLiftMap $. $( The class of block lift maps $)
  $c SucMap $. $( The class of successor maps $)
  $c Suc $. $( The class of successors $)
  $c pre $. $( Predecessor of a class symbol $)
  $c BlockLiftFix $. $( The class of equilibrium block lifts $)
  $c ShiftStable $. $( The shift stability class $)

  $c ,~ $. $( Class of cosets symbol $)
  $c ~ $. $( Class of coelements symbol $)

  $c Rels $. $( The class of relations $)

  $c _S $. $( The class of subset relations $)

  $c Refs $. $( The class of all reflexive sets (used only once) $)
  $c RefRels $. $( The class of reflexive relations $)
  $c RefRel $. $( Reflexive relation predicate $)

  $c CnvRefs $. $( The class of all converse reflexive sets (used only
                   once) $)
  $c CnvRefRels $. $( The class of converse reflexive relations $)
  $c CnvRefRel $. $( Converse reflexive relation predicate $)

  $c Syms $. $( The class of all symmetric sets (used only once) $)
  $c SymRels $. $( The class of symmetric relations $)
  $c SymRel $. $( Symmetric relation predicate $)

  $c Trs $. $( The class of all transitive sets versus the transitive class
               defined in ~ df-tr (used only once) $)
  $c TrRels $. $( The class of transitive relations $)
  $c TrRel $. $( Transitive relation predicate $)

  $c EqvRels $. $( The class of equivalence relations $)
  $c EqvRel $. $( Equivalence relation predicate $)

  $c CoElEqvRels $. $( The class of coelement equivalence relations $)
  $c CoElEqvRel $. $( Coelement equivalence relation predicate $)

  $c Redunds $. $( The class of redundants $)
  $c Redund $. $( Redundancy predicate $)
  $c redund $. $( Redundancy operator for propositions $)

  $c DomainQss $. $( The class of all domain quotients $)
  $c DomainQs $. $( Domain quotient predicate $)

  $c Ers $. $( The class of equivalence relations on their domain
               quotients $)
  $c ErALTV $. $( Equivalence relation on its domain quotient predicate $)

  $c CoMembErs $. $( The class of comember equivalence relations $)
  $c CoMembEr $. $( Comember equivalence relation predicate $)

  $c PetErs $. $( The class of blocklift-stable equivalence-side general
                  partition-equivalence spans $)
  $c Pet2Ers $. $( The class of grade- and blocklift-stable equivalence-side
                   general partition-equivalence spans $)

  $c Funss $. $( The class of all function sets (used only once) $)
  $c FunsALTV $. $( The class of functions, i.e., function relations $)
  $c FunALTV $. $( Function predicate $)

  $c Disjss $. $( The class of all disjoint sets (used only once) $)
  $c Disjs $. $( The class of disjoints, i.e., disjoint relations $)
  $c Disj $. $( Disjoint predicate $)

  $c ElDisjs $. $( The class of disjoint elements, i.e., disjoint element
                   relation $)
  $c ElDisj $. $( Disjoint elementhood predicate $)

  $c AntisymRel $. $( Antisymmetric relation predicate $)

  $c Parts $. $( The class of all partitions, i.e., partition relations $)
  $c Part $. $( Partition predicate $)

  $c MembParts $. $( The class of member partition relations $)
  $c MembPart $. $( Member partition predicate $)

  $c PetParts $. $( The class of blocklift-stable partition-side general
                    partition-equivalence spans $)
  $c Pet2Parts $. $( The class of grade- and blocklift-stable partition-side
                     general partition-equivalence spans $)

  $( Extend the definition of a class to include the range Cartesian product
     class. $)
  cxrn $a class ( A |X. B ) $.

  $( Extend the definition of a class to include the quotient map of a
     class. $)
  cqmap $a class QMap R $.

  $( Extend the definition of a class to include the class of adjoined lift
     maps. $)
  cadjliftmap $a class ( R AdjLiftMap A ) $.
  $( Extend the definition of a class to include the class of block lift
     maps. $)
  cblockliftmap $a class ( R BlockLiftMap A ) $.
  $( Extend the definition of a class to include the class of successor
     maps. $)
  csucmap $a class SucMap $.
  $( Extend the definition of a class to include the class of successors. $)
  csuccl $a class Suc $.
  $( Extend the definition of a class to include the predecessor of a class. $)
  cpre $a class pre N $.
  $( Extend the definition of a class to include the class of equilibrium block
     lifts. $)
  cblockliftfix $a class BlockLiftFix $.
  $( Extend the definition of a class to include the shift stability class. $)
  cshiftstable $a class ( S ShiftStable F ) $.

  $( Extend the definition of a class to include the class of cosets by a
     class.  (Read: the class of cosets by ` R ` .) $)
  ccoss $a class ,~ R $.
  $( Extend the definition of a class to include the class of coelements on a
     class.  (Read: the class of coelements on ` A ` .) $)
  ccoels $a class ~ A $.

  $( Extend the definition of a class to include the relation class. $)
  crels $a class Rels $.

  $( Extend the definition of a class to include the subset class. $)
  cssr $a class _S $.

  $( Extend the definition of a class to include the reflexivity class. $)
  crefs $a class Refs $.
  $( Extend the definition of a class to include the reflexive relations
     class. $)
  crefrels $a class RefRels $.
  $( Extend the definition of a wff to include the reflexive relation
     predicate.  (Read: ` R ` is a reflexive relation.) $)
  wrefrel $a wff RefRel R $.

  $( Extend the definition of a class to include the converse reflexivity
     class. $)
  ccnvrefs $a class CnvRefs $.
  $( Extend the definition of a class to include the converse reflexive
     relations class. $)
  ccnvrefrels $a class CnvRefRels $.
  $( Extend the definition of a wff to include the converse reflexive relation
     predicate.  (Read: ` R ` is a converse reflexive relation.) $)
  wcnvrefrel $a wff CnvRefRel R $.

  $( Extend the definition of a class to include the symmetry class. $)
  csyms $a class Syms $.
  $( Extend the definition of a class to include the symmetry relations
     class. $)
  csymrels $a class SymRels $.
  $( Extend the definition of a wff to include the symmetry relation predicate.
     (Read: ` R ` is a symmetric relation.) $)
  wsymrel $a wff SymRel R $.

  $( Extend the definition of a class to include the transitivity class (but
     cf. the transitive class defined in ~ df-tr ). $)
  ctrs $a class Trs $.
  $( Extend the definition of a class to include the transitive relations
     class. $)
  ctrrels $a class TrRels $.
  $( Extend the definition of a wff to include the transitive relation
     predicate.  (Read: ` R ` is a transitive relation.) $)
  wtrrel $a wff TrRel R $.

  $( Extend the definition of a class to include the equivalence relations
     class. $)
  ceqvrels $a class EqvRels $.
  $( Extend the definition of a wff to include the equivalence relation
     predicate.  (Read: ` R ` is an equivalence relation.) $)
  weqvrel $a wff EqvRel R $.

  $( Extend the definition of a class to include the coelement equivalence
     relations class. $)
  ccoeleqvrels $a class CoElEqvRels $.
  $( Extend the definition of a wff to include the coelement equivalence
     relation predicate.  (Read: the coelement equivalence relation on
     ` A ` .) $)
  wcoeleqvrel $a wff CoElEqvRel A $.

  $( Extend the definition of a class to include the redundancy class. $)
  credunds $a class Redunds $.
  $( Extend the definition of a wff to include the redundancy predicate.
     (Read: ` A ` is redundant with respect to ` B ` in ` C ` .) $)
  wredund $a wff A Redund <. B , C >. $.
  $( Extend wff definition to include the redundancy operator for
     propositions. $)
  wredundp $a wff redund ( ph , ps , ch ) $.

  $( Extend the definition of a class to include the domain quotients class. $)
  cdmqss $a class DomainQss $.
  $( Extend the definition of a wff to include the domain quotient predicate.
     (Read: the domain quotient of ` R ` is ` A ` .) $)
  wdmqs $a wff R DomainQs A $.

  $( Extend the definition of a class to include the equivalence relations on
     their domain quotients class. $)
  cers $a class Ers $.
  $( Extend the definition of a wff to include the equivalence relation on its
     domain quotient predicate.  (Read: ` R ` is an equivalence relation on its
     domain quotient ` A ` .) $)
  werALTV $a wff R ErALTV A $.

  $( Extend the definition of a class to include the blocklift-stable
     equivalence relations class. $)
  cpeters $a class PetErs $.
  $( Extend the definition of a class to include the grade- and
     blocklift-stable equivalence relations class. $)
  cpet2ers $a class Pet2Ers $.

  $( Extend the definition of a class to include the comember equivalence
     relations class. $)
  ccomembers $a class CoMembErs $.
  $( Extend the definition of a wff to include the comember equivalence
     relation predicate.  (Read: the comember equivalence relation on ` A ` ,
     or, the restricted coelement equivalence relation on its domain quotient
     ` A ` .) $)
  wcomember $a wff CoMembEr A $.

  $( Extend the definition of a class to include the function set class. $)
  cfunss $a class Funss $.
  $( Extend the definition of a class to include the functions class, i.e., the
     function relations class. $)
  cfunsALTV $a class FunsALTV $.
  $( Extend the definition of a wff to include the function predicate, i.e.,
     the function relation predicate.  (Read: ` F ` is a function.) $)
  wfunALTV $a wff FunALTV F $.

  $( Extend the definition of a class to include the disjoint set class. $)
  cdisjss $a class Disjss $.
  $( Extend the definition of a class to include the disjoints class, i.e., the
     disjoint relations class. $)
  cdisjs $a class Disjs $.
  $( Extend the definition of a wff to include the disjoint predicate, i.e.,
     the disjoint relation predicate.  (Read: ` R ` is a disjoint.) $)
  wdisjALTV $a wff Disj R $.

  $( Extend the definition of a class to include the disjoint elements class,
     i.e., the disjoint element relations class. $)
  celdisjs $a class ElDisjs $.
  $( Extend the definition of a wff to include the disjoint element predicate,
     i.e., the disjoint element relation predicate.  (Read: the elements of
     ` A ` are disjoint.) $)
  weldisj $a wff ElDisj A $.

  $( Extend the definition of a wff to include the antisymmetry relation
     predicate.  (Read: ` R ` is an antisymmetric relation.) $)
  wantisymrel $a wff AntisymRel R $.

  $( Extend the definition of a class to include the partitions class, i.e.,
     the partition relations class. $)
  cparts $a class Parts $.
  $( Extend the definition of a wff to include the partition predicate, i.e.,
     the partition relation predicate.  (Read: ` A ` is a partition by
     ` R ` .) $)
  wpart $a wff R Part A $.

  $( Extend the definition of a class to include the member partitions class,
     i.e., the member partition relations class. $)
  cmembparts $a class MembParts $.
  $( Extend the definition of a wff to include the member partition predicate,
     i.e., the member partition relation predicate.  (Read: ` A ` is a member
     partition.) $)
  wmembpart $a wff MembPart A $.

  $( Extend the definition of a class to include the blocklift-stable
     partitions class. $)
  cpetparts $a class PetParts $.
  $( Extend the definition of a class to include the grade- and
     blocklift-stable partitions class. $)
  cpet2parts $a class Pet2Parts $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Preparatory theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    el2v1.1 $e |- ( ( x e. _V /\ ph ) -> ps ) $.
    $( New way ( ~ elv , and the theorems beginning with "el2v" or "el3v") to
       shorten some proofs.  (Contributed by Peter Mazsa, 23-Oct-2018.) $)
    el2v1 $p |- ( ph -> ps ) $=
      ( cv cvv wcel vex mpan ) CEFGABCHDI $.
  $}

  ${
    el3v1.1 $e |- ( ( x e. _V /\ ps /\ ch ) -> th ) $.
    $( New way ( ~ elv , and the theorems beginning with "el2v" or "el3v") to
       shorten some proofs.  (Contributed by Peter Mazsa, 16-Oct-2020.) $)
    el3v1 $p |- ( ( ps /\ ch ) -> th ) $=
      ( cv cvv wcel vex mp3an1 ) DFGHABCDIEJ $.
  $}

  ${
    el3v2.1 $e |- ( ( ph /\ y e. _V /\ ch ) -> th ) $.
    $( New way ( ~ elv , and the theorems beginning with "el2v" or "el3v") to
       shorten some proofs.  (Contributed by Peter Mazsa, 16-Oct-2020.) $)
    el3v2 $p |- ( ( ph /\ ch ) -> th ) $=
      ( cv cvv wcel vex mp3an2 ) ADFGHBCDIEJ $.
  $}

  ${
    el3v12.1 $e |- ( ( x e. _V /\ y e. _V /\ ch ) -> th ) $.
    $( New way ( ~ elv , and the theorems beginning with "el2v" or "el3v") to
       shorten some proofs.  (Contributed by Peter Mazsa, 11-Jul-2021.) $)
    el3v12 $p |- ( ch -> th ) $=
      ( cv cvv wcel el3v1 el2v1 ) ABDDFGHABCEIJ $.
  $}

  ${
    el3v13.1 $e |- ( ( x e. _V /\ ps /\ z e. _V ) -> th ) $.
    $( New way ( ~ elv , and the theorems beginning with "el2v" or "el3v") to
       shorten some proofs.  (Contributed by Peter Mazsa, 11-Jul-2021.) $)
    el3v13 $p |- ( ps -> th ) $=
      ( cv cvv wcel el3v3 el2v1 ) ABCCFGHABDEIJ $.
  $}

  ${
    el3v23.1 $e |- ( ( ph /\ y e. _V /\ z e. _V ) -> th ) $.
    $( New way ( ~ elv , and the theorems beginning with "el2v" or "el3v") to
       shorten some proofs.  (Contributed by Peter Mazsa, 11-Jul-2021.) $)
    el3v23 $p |- ( ph -> th ) $=
      ( cv cvv wcel el3v3 elvd ) ABCACFGHBDEIJ $.
  $}

  $( Multiple commutations in conjunction.  (Contributed by Peter Mazsa,
     7-Mar-2020.) $)
  anan $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ ( ( ph /\ th ) /\ ta ) ) <->
               ( ( ps /\ th ) /\ ( ph /\ ( ch /\ ta ) ) ) ) $=
    ( wa an4 anandi ancom bitr3i anbi1i anass 3bitri ) ABFZCFADFZEFFNOFZCEFZFBD
    FZAFZQFRAQFFNCOEGPSQPARFSABDHARIJKRAQLM $.

  ${
    triantru3.1 $e |- ph $.
    triantru3.2 $e |- ps $.
    $( A wff is equivalent to its conjunctions with truths.  (Contributed by
       Peter Mazsa, 30-Nov-2018.) $)
    triantru3 $p |- ( ch <-> ( ph /\ ps /\ ch ) ) $=
      ( wa w3a biantrur 3anass 3bitr4i ) BCFZAKFCABCGAKDHBCEHABCIJ $.
  $}

  ${
    biorfd.1 $e |- ( ph -> -. ps ) $.
    $( A wff is equivalent to its disjunction with falsehood, deduction form.
       (Contributed by Peter Mazsa, 22-Aug-2023.) $)
    biorfd $p |- ( ph -> ( ch <-> ( ps \/ ch ) ) ) $=
      ( wn wo wb biorf syl ) ABECBCFGDBCHI $.
  $}

  $( Substitution of equal classes in binary relation.  (Contributed by Peter
     Mazsa, 14-Jun-2024.) $)
  eqbrtr $p |- ( ( A = B /\ B R C ) -> A R C ) $=
    ( wceq wbr breq1 biimpar ) ABEACDFBCDFABCDGH $.

  $( Substitution of equal classes in a binary relation.  (Contributed by Peter
     Mazsa, 14-Jun-2024.) $)
  eqbrb $p |- ( ( A = B /\ A R C ) <-> ( A = B /\ B R C ) ) $=
    ( wceq wbr wa simpl eqbrtr jca eqcom anbi1i 3imtr3i impbii ) ABEZACDFZGZOBC
    DFZGZBAEZPGZTRGQSUATRTPHBACDIJTOPBAKZLTORUBLMSOPORHABCDIJN $.

  $( Substitution of equal classes into element relation.  (Contributed by
     Peter Mazsa, 22-Jul-2017.) $)
  eqeltr $p |- ( ( A = B /\ B e. C ) -> A e. C ) $=
    ( wceq wcel eleq1 biimpar ) ABDACEBCEABCFG $.

  $( Substitution of equal classes into element relation.  (Contributed by
     Peter Mazsa, 17-Jul-2019.) $)
  eqelb $p |- ( ( A = B /\ A e. C ) <-> ( A = B /\ B e. C ) ) $=
    ( wceq wcel wa simpl eqeltr jca eqcom anbi1i 3imtr3i impbii ) ABDZACEZFZNBC
    EZFZBADZOFZSQFPRTSQSOGBACHISNOBAJZKSNQUAKLRNONQGABCHIM $.

  ${
    eqeqan2d.1 $e |- ( ph -> C = D ) $.
    $( Implication of introducing a new equality.  (Contributed by Peter Mazsa,
       17-Apr-2019.) $)
    eqeqan2d $p |- ( ( A = B /\ ph ) -> ( A = C <-> B = D ) ) $=
      ( wceq wb eqeq12 sylan2 ) ABCGDEGBDGCEGHFBCDEIJ $.
  $}

  $( The restriction to a disjoint is the empty class.  (Contributed by Peter
     Mazsa, 24-Jul-2024.) $)
  disjresin $p |- ( ( A i^i B ) = (/) -> ( R |` ( A i^i B ) ) = (/) ) $=
    ( cin c0 wceq cres reseq2 res0 eqtrdi ) ABDZEFCKGCEGEKECHCIJ $.

  $( The intersection of restrictions to disjoint is the empty class.
     (Contributed by Peter Mazsa, 24-Jul-2024.) $)
  disjresdisj $p |- ( ( A i^i B ) = (/) ->
                      ( ( R |` A ) i^i ( R |` B ) ) = (/) ) $=
    ( cin c0 wceq cres resindi disjresin eqtr3id ) ABDZEFCAGCBGDCKGECABHABCIJ
    $.

  $( The difference between restrictions to disjoint is the first restriction.
     (Contributed by Peter Mazsa, 24-Jul-2024.) $)
  disjresdif $p |- ( ( A i^i B ) = (/) ->
                     ( ( R |` A ) \ ( R |` B ) ) = ( R |` A ) ) $=
    ( cin c0 wceq cres cdif disjresdisj disjdif2 syl ) ABDEFCAGZCBGZDEFLMHLFABC
    ILMJK $.

  $( Lemma for ~ ressucdifsn2 .  (Contributed by Peter Mazsa, 24-Jul-2024.) $)
  disjresundif $p |- ( ( A i^i B ) = (/) ->
                       ( ( R |` ( A u. B ) ) \ ( R |` B ) ) = ( R |` A ) ) $=
    ( cin c0 wceq cun cres cdif resundi difeq1i difun2 eqtri disjresdif eqtrid
    ) ABDEFCABGHZCBHZIZCAHZQIZSRSQGZQITPUAQCABJKSQLMABCNO $.

  $( Two ways of expressing the restriction of an intersection.  (Contributed
     by Peter Mazsa, 5-Jun-2021.) $)
  inres2 $p |- ( ( R |` A ) i^i S ) = ( ( R i^i S ) |` A ) $=
    ( cres cin inres ineqcomi incom reseq1i eqtr4i ) BADZCECBEZADZBCEZADCKMCBAF
    GNLABCHIJ $.

  $( Equality theorem for composition of two classes.  (Contributed by Peter
     Mazsa, 23-Sep-2021.) $)
  coideq $p |- ( A = B -> ( A o. A ) = ( B o. B ) ) $=
    ( wceq ccom coeq1 coeq2 eqtrd ) ABCAADBADBBDABAEABBFG $.

  $( If there is no case where wff is true, it is true for at most one case.
     (Contributed by Peter Mazsa, 27-Sep-2021.) $)
  nexmo1 $p |- ( -. E. x ph -> E* x ph ) $=
    ( wex wn weu wi wmo pm2.21 moeu sylibr ) ABCZDKABEZFABGKLHABIJ $.

  $( Implication of a class abstraction.  (Contributed by Peter Mazsa,
     16-Apr-2019.) $)
  eqab2 $p |- ( A. x ( x e. A <-> ph ) -> A. x e. A ph ) $=
    ( cv wcel wb wal wi biimp alimi ralrid ) BDCEZAFZBGABCMLAHBLAIJK $.

  ${
    $d A y $.  $d x y $.
    $( Double restricted universal quantification, special case.  (Contributed
       by Peter Mazsa, 17-Jun-2020.) $)
    r2alan $p |- ( A. x A. y ( ( ( x e. A /\ y e. B ) /\ ph ) -> ps ) <->
                   A. x e. A A. y e. B ( ph -> ps ) ) $=
      ( cv wcel wa wi wal wral impexp 2albii r2al bitr4i ) CGEHDGFHIZAIBJZDKCKQ
      ABJZJZDKCKSDFLCELRTCDQABMNSCDEFOP $.
  $}

  ${
    ssrabi.1 $e |- ( ph -> ps ) $.
    $( Inference of restricted abstraction subclass from implication.
       (Contributed by Peter Mazsa, 26-Oct-2022.) $)
    ssrabi $p |- { x e. A | ph } C_ { x e. A | ps } $=
      ( wi cv wcel a1i ss2rabi ) ABCDABFCGDHEIJ $.
  $}

  ${
    rabimbieq.1 $e |- B = { x e. A | ph } $.
    rabimbieq.2 $e |- ( x e. A -> ( ph <-> ps ) ) $.
    $( Restricted equivalent wff's correspond to restricted class abstractions
       which are equal with the same class.  (Contributed by Peter Mazsa,
       22-Jul-2021.) $)
    rabimbieq $p |- B = { x e. A | ps } $=
      ( crab rabbiia eqtri ) EACDHBCDHFABCDGIJ $.
  $}

  ${
    $d C x $.
    abeqin.1 $e |- A = ( B i^i C ) $.
    abeqin.2 $e |- B = { x | ph } $.
    $( Intersection with class abstraction.  (Contributed by Peter Mazsa,
       21-Jul-2021.) $)
    abeqin $p |- A = { x e. C | ph } $=
      ( cin cab crab ineq1i dfrab2 3eqtr4i ) DEHABIZEHCABEJDNEGKFABELM $.
  $}

  ${
    $d C x $.
    abeqinbi.1 $e |- A = ( B i^i C ) $.
    abeqinbi.2 $e |- B = { x | ph } $.
    abeqinbi.3 $e |- ( x e. C -> ( ph <-> ps ) ) $.
    $( Intersection with class abstraction and equivalent wff's.  (Contributed
       by Peter Mazsa, 21-Jul-2021.) $)
    abeqinbi $p |- A = { x e. C | ps } $=
      ( abeqin rabimbieq ) ABCFDACDEFGHJIK $.
  $}

  ${
    $d A x $.
    eqrabi.1 $e |- ( x e. A <-> ( x e. B /\ ph ) ) $.
    $( Class element of a restricted class abstraction.  (Contributed by Peter
       Mazsa, 24-Jul-2021.) $)
    eqrabi $p |- A = { x e. B | ph } $=
      ( cv wcel wa cab crab eqabi df-rab eqtr4i ) CBFDGAHZBIABDJNBCEKABDLM $.
  $}

  ${
    $d A x $.  $d C x $.  $d ps x $.
    rabeqel.1 $e |- B = { x e. A | ph } $.
    rabeqel.2 $e |- ( x = C -> ( ph <-> ps ) ) $.
    $( Class element of a restricted class abstraction.  (Contributed by Peter
       Mazsa, 24-Jul-2021.) $)
    rabeqel $p |- ( C e. B <-> ( ps /\ C e. A ) ) $=
      ( wcel elrab2 biancomi ) FEIBFDIABCFDEHGJK $.
  $}

  ${
    $d A u v $.  $d B u v $.  $d u v x y $.
    eqrelf.1 $e |- F/_ x A $.
    eqrelf.2 $e |- F/_ x B $.
    eqrelf.3 $e |- F/_ y A $.
    eqrelf.4 $e |- F/_ y B $.
    $( The equality connective between relations.  (Contributed by Peter Mazsa,
       25-Jun-2019.) $)
    eqrelf $p |- ( ( Rel A /\ Rel B ) ->
      ( A = B <-> A. x A. y ( <. x , y >. e. A <-> <. x , y >. e. B ) ) ) $=
      ( vu vv wrel wa wceq cv cop wcel wb wal nfv nfel2 bibi12d cbval2v bitr4di
      eqrel nfbi opeq12 eleq1d ) CKDKLCDMINZJNZOZCPZUJDPZQZJRIRANZBNZOZCPZUPDPZ
      QZBRARIJCDUDUSUMABIJUSISUSJSUKULAAUJCETAUJDFTUEUKULBBUJCGTBUJDHTUEUNUHMUO
      UIMLZUQUKURULUTUPUJCUNUOUHUIUFZUGUTUPUJDVAUGUAUBUC $.
  $}

  $( Binary relation on the converse of an intersection with a Cartesian
     product.  (Contributed by Peter Mazsa, 27-Jul-2019.) $)
  br1cnvinxp $p |- ( C `' ( R i^i ( A X. B ) ) D <->
                     ( ( C e. B /\ D e. A ) /\ D R C ) ) $=
    ( cxp cin ccnv wbr wcel wa relinxp relbrcnv brinxp2 ancom anbi1i 3bitri ) C
    DEABFGZHIDCRIDAJZCBJZKZDCEIZKTSKZUBKCDRABELMABDCENUAUCUBSTOPQ $.

  $( Elementhood in a converse ` R ` -coset when ` R ` is a relation.
     (Contributed by Peter Mazsa, 9-Dec-2018.) $)
  releleccnv $p |- ( Rel R -> ( A e. [ B ] `' R <-> A R B ) ) $=
    ( ccnv cec wcel wbr wrel wb relcnv relelec ax-mp relbrcnvg bitrid ) ABCDZEF
    ZBAOGZCHABCGOHPQICJABOKLBACMN $.

  ${
    $d A x $.  $d B x $.  $d R x $.  $d S x $.
    $( Equality of converse ` R ` -coset and converse ` S ` -coset when ` R `
       and ` S ` are relations.  (Contributed by Peter Mazsa, 27-Jul-2019.) $)
    releccnveq $p |- ( ( Rel R /\ Rel S ) ->
                       ( [ A ] `' R = [ B ] `' S <->
                         A. x ( x R A <-> x S B ) ) ) $=
      ( ccnv cec wceq cv wcel wb wal wrel wbr dfcleq releleccnv bi2bian9 albidv
      wa bitrid ) BDFGZCEFGZHAIZUAJZUCUBJZKZALDMZEMZSZUCBDNZUCCENZKZALAUAUBOUIU
      FULAUGUDUJUHUEUKUCBDPUCCEPQRT $.
  $}

  ${
    $d A x y $.
    $( Cartesian product of a class and the universe.  (Contributed by Peter
       Mazsa, 6-Oct-2020.) $)
    xpv $p |- ( A X. _V ) = { <. x , y >. | x e. A } $=
      ( cvv cxp cv wcel wa copab df-xp wb vex iba ax-mp opabbii eqtr4i ) CDEAFC
      GZBFDGZHZABIQABIABCDJQSABRQSKBLRQMNOP $.
  $}

  ${
    $d A x y $.
    $( Cartesian product of the universe and a class.  (Contributed by Peter
       Mazsa, 3-Dec-2020.) $)
    vxp $p |- ( _V X. A ) = { <. x , y >. | y e. A } $=
      ( cvv cxp ccnv cv wcel copab xpv cnveqi cnvxp cnvopab 3eqtr3i ) CDEZFBGCH
      ZBAIZFDCEPABIOQBACJKCDLPBAMN $.
  $}

  $( Negated elementhood of ordered pair.  (Contributed by Peter Mazsa,
     14-Jan-2019.) $)
  opelvvdif $p |- ( ( A e. V /\ B e. W ) ->
                    ( <. A , B >. e. ( ( _V X. _V ) \ R ) <->
                      -. <. A , B >. e. R ) ) $=
    ( wcel wa cop cvv cxp cdif wn eldif opelvvg biantrurd bitr4id ) ADFBEFGZABH
    ZIIJZCKFRSFZRCFLZGUARSCMQTUAABDENOP $.

  ${
    $d x y $.
    $( Ordered-pair class abstraction defined by a negation.  (Contributed by
       Peter Mazsa, 25-Jun-2019.) $)
    vvdifopab $p |- ( ( _V X. _V ) \ { <. x , y >. | ph } ) =
                    { <. x , y >. | -. ph } $=
      ( cvv cxp copab cdif wn wceq cv cop wcel wb wal opabidw wrel nfcv nfopab1
      nfdif nfopab2 notbii opelvvdif 3bitr4i relxp reldif ax-mp relopabv eqrelf
      el2v gen2 mp2an mpbir ) DDEZABCFZGZAHZBCFZIZBJZCJZKZUOLZVAUQLZMZCNBNZVDBC
      VAUNLZHZUPVBVCVFAABCOUAVBVGMBCUSUTUNDDUBUIUPBCOUCUJUOPZUQPURVEMUMPVHDDUDU
      MUNUEUFUPBCUGBCUOUQBUMUNBUMQABCRSUPBCRCUMUNCUMQABCTSUPBCTUHUKUL $.
  $}

  $( Binary relation with universal complement is the negation of the relation.
     (Contributed by Peter Mazsa, 1-Jul-2018.) $)
  brvdif $p |- ( A ( _V \ R ) B <-> -. A R B ) $=
    ( cvv cdif wbr wn brv brdif mpbiran ) ABDCEFABDFABCFGABHABDCIJ $.

  $( Binary relation with universal complement.  (Contributed by Peter Mazsa,
     14-Jul-2018.) $)
  brvdif2 $p |- ( A ( _V \ R ) B <-> -. <. A , B >. e. R ) $=
    ( cvv cdif wbr cop wcel brvdif df-br xchbinx ) ABDCEFABCFABGCHABCIABCJK $.

  $( Binary relation with the complement under the universal class of ordered
     pairs.  (Contributed by Peter Mazsa, 9-Nov-2018.) $)
  brvvdif $p |- ( ( A e. V /\ B e. W ) ->
                  ( A ( ( _V X. _V ) \ R ) B <-> -. A R B ) ) $=
    ( wcel wa cop cvv cxp cdif wn wbr opelvvdif df-br notbii 3bitr4g ) ADFBEFGA
    BHZIIJCKZFRCFZLABSMABCMZLABCDENABSOUATABCOPQ $.

  $( Binary relation with the complement under the universal class of ordered
     pairs is the same as with universal complement.  (Contributed by Peter
     Mazsa, 28-Nov-2018.) $)
  brvbrvvdif $p |- ( ( A e. V /\ B e. W ) ->
                     ( A ( ( _V X. _V ) \ R ) B <-> A ( _V \ R ) B ) ) $=
    ( wcel wa cvv cxp cdif wbr wn brvvdif brvdif bitr4di ) ADFBEFGABHHICJKABCKL
    ABHCJKABCDEMABCNO $.

  $( The converse of the binary epsilon relation.  (Contributed by Peter Mazsa,
     30-Jan-2018.) $)
  brcnvep $p |- ( A e. V -> ( A `' _E B <-> B e. A ) ) $=
    ( cep ccnv wbr wcel rele relbrcnv epelg bitrid ) ABDEFBADFACGBAGABDHIBACJK
    $.

  $( Elementhood in the ` R ` -coset of ` A ` .  Theorem 72 of [Suppes] p. 82.
     (I think we should replace ~ elecg with this original form of Suppes.
     Peter Mazsa).  (Contributed by Mario Carneiro, 9-Jul-2014.) $)
  elecALTV $p |- ( ( A e. V /\ B e. W ) -> ( B e. [ A ] R <-> A R B ) ) $=
    ( wcel wa csn cima cop cec wbr elimasng df-ec eleq2i df-br 3bitr4g ) ADFBEF
    GBCAHIZFABJCFBACKZFABCLCABDEMSRBACNOABCPQ $.

  $( Restricted converse epsilon binary relation.  (Contributed by Peter Mazsa,
     10-Feb-2018.) $)
  brcnvepres $p |- ( ( B e. V /\ C e. W ) ->
                     ( B ( `' _E |` A ) C <-> ( B e. A /\ C e. B ) ) ) $=
    ( wcel cep ccnv cres wbr wa brres brcnvep anbi2d sylan9bbr ) CEFBCGHZAIJBAF
    ZBCPJZKBDFZQCBFZKABCPELSRTQBCDMNO $.

  $( Binary relation on a restriction.  (Contributed by Peter Mazsa,
     2-Jan-2019.)  (Revised by Peter Mazsa, 16-Dec-2021.) $)
  brres2 $p |- ( B ( R |` A ) C <-> B ( R i^i ( A X. ran ( R |` A ) ) ) C ) $=
    ( cres crn wcel wbr wa cxp cin pm5.32i relres relelrni pm4.71ri w3a brinxp2
    brres df-3an 3anan12 3bitr2i 3bitr4i ) CDAEZFZGZBCUCHZIUEBAGZBCDHZIZIZUFBCD
    AUDJKHZUEUFUIABCDUDRLUFUEBCUCDAMNOUKUGUEIUHIUGUEUHPUJAUDBCDQUGUEUHSUGUEUHTU
    AUB $.

  $( Binary relation on the converse of a restriction.  (Contributed by Peter
     Mazsa, 27-Jul-2019.) $)
  br1cnvres $p |- ( B e. V ->
                    ( B `' ( R |` A ) C <-> ( C e. A /\ C R B ) ) ) $=
    ( cres ccnv wbr cvv cxp cin wcel wa df-res cnveqi breqi wb br1cnvinxp anass
    elex bitri baib syl bitrid ) BCDAFZGZHBCDAIJKZGZHZBELZCALZCBDHZMZBCUFUHUEUG
    DANOPUJBILZUIUMQBETUIUNUMUIUNUKMULMUNUMMAIBCDRUNUKULSUAUBUCUD $.

  $( Elementhood in the converse restricted coset of ` B ` .  (Contributed by
     Peter Mazsa, 21-Sep-2018.) $)
  elec1cnvres $p |- ( B e. V ->
                      ( C e. [ B ] `' ( R |` A ) <-> ( C e. A /\ C R B ) ) ) $=
    ( cres ccnv cec wcel wbr wa wrel wb relcnv relelec ax-mp br1cnvres bitrid )
    CBDAFZGZHIZBCTJZBEICAICBDJKTLUAUBMSNCBTOPABCDEQR $.

  ${
    $d A x $.  $d B x $.  $d R x $.  $d V x $.
    $( Converse restricted coset of ` B ` .  (Contributed by Peter Mazsa,
       22-Mar-2019.)  (Revised by Peter Mazsa, 21-Oct-2021.) $)
    ec1cnvres $p |- ( B e. V -> [ B ] `' ( R |` A ) = { x e. A | x R B } ) $=
      ( wcel cres ccnv cec cv wbr wa cab crab elec1cnvres eqabdv df-rab eqtr4di
      ) CEFZCDBGHIZAJZBFUACDKZLZAMUBABNSUCATBCUADEOPUBABQR $.
  $}

  ${
    $d A y $.  $d B y $.  $d R y $.
    $( Elementhood in the domain of a restriction.  (Contributed by Peter
       Mazsa, 9-Jan-2019.) $)
    eldmres $p |- ( B e. V ->
                    ( B e. dom ( R |` A ) <-> ( B e. A /\ E. y B R y ) ) ) $=
      ( wcel cres cdm cv wbr wex wa eldmg wb cvv brres elv exbii 19.42v bitri
      bitrdi ) CEFCDBGZHFCAIZUBJZAKZCBFZCUCDJZAKLZACUBEMUEUFUGLZAKUHUDUIAUDUINA
      BCUCDOPQRUFUGASTUA $.
  $}

  ${
    $d A x $.  $d B x $.  $d R x $.  $d V x $.
    $( Element of the range of a restriction.  (Contributed by Peter Mazsa,
       26-Dec-2018.) $)
    elrnres $p |- ( B e. V -> ( B e. ran ( R |` A ) <-> E. x e. A x R B ) ) $=
      ( wcel cres crn cv wbr wex wrex elrng brres exbidv bitrd df-rex bitr4di
      wa ) CEFZCDBGZHFZAIZBFUCCDJZSZAKZUDABLTUBUCCUAJZAKUFACUAEMTUGUEABUCCDENOP
      UDABQR $.
  $}

  ${
    $d A y $.  $d B y $.  $d R y $.
    $( Element of the domain of a restriction to a singleton.  (Contributed by
       Peter Mazsa, 12-Jun-2024.) $)
    eldmressnALTV $p |- ( B e. V ->
        ( B e. dom ( R |` { A } ) <-> ( B = A /\ A e. dom R ) ) ) $=
      ( vy wcel csn cres cdm wceq wa wbr wex eldmres elsng eldmg bicomd anbi12d
      cv bitrd eqelb bitrdi ) BDFZBCAGZHIFZBAJZBCIZFZKZUFAUGFKUCUEBUDFZBESCLEMZ
      KUIEUDBCDNUCUJUFUKUHBADOUCUHUKEBCDPQRTBAUGUAUB $.
  $}

  ${
    $d A x $.  $d B x $.  $d R x $.  $d W x $.
    $( Element of the range of a restriction to a singleton.  (Contributed by
       Peter Mazsa, 12-Jun-2024.) $)
    elrnressn $p |- ( ( A e. V /\ B e. W ) ->
                      ( B e. ran ( R |` { A } ) <-> A R B ) ) $=
      ( vx wcel csn cres crn cv wbr wrex elrnres breq1 rexsng sylan9bbr ) BEGBC
      AHZIJGFKZBCLZFRMADGABCLZFRBCENTUAFADSABCOPQ $.
  $}

  ${
    $d A y $.  $d R y $.  $d V y $.
    $( Elementhood in a domain.  (Contributed by Peter Mazsa, 24-Oct-2018.) $)
    eldm4 $p |- ( A e. V -> ( A e. dom R <-> E. y y e. [ A ] R ) ) $=
      ( wcel cdm cv wbr wex cec eldmg wb cvv elecALTV elvd exbidv bitr4d ) BDEZ
      BCFEBAGZCHZAISBCJEZAIABCDKRUATARUATLABSCDMNOPQ $.
  $}

  ${
    $d A y $.  $d B y $.  $d R y $.  $d V y $.
    $( Elementhood in the domain of a restriction.  (Contributed by Peter
       Mazsa, 21-Aug-2020.) $)
    eldmres2 $p |- ( B e. V ->
        ( B e. dom ( R |` A ) <-> ( B e. A /\ E. y y e. [ B ] R ) ) ) $=
      ( wcel cres cdm cv wbr wex wa cec eldmres eldmg eldm4 bitr3d anbi2d bitrd
      ) CEFZCDBGHFCBFZCAIZDJAKZLUAUBCDMFAKZLABCDENTUCUDUATCDHFUCUDACDEOACDEPQRS
      $.
  $}

  ${
    $d A y $.  $d B y $.  $d R y $.  $d V y $.
    $( Elementhood in the domain of a restriction.  (Contributed by Peter
       Mazsa, 23-Nov-2025.) $)
    eldmres3 $p |- ( B e. V ->
        ( B e. dom ( R |` A ) <-> ( B e. A /\ [ B ] R =/= (/) ) ) ) $=
      ( vy wcel cres cdm cv cec wex wa c0 wne eldmres2 n0 anbi2i bitr4di ) BDFB
      CAGHFBAFZEIBCJZFEKZLSTMNZLEABCDOUBUASETPQR $.
  $}

  ${
    eceq1i.1 $e |- A = B $.
    $( Equality theorem for ` C ` -coset of ` A ` and ` C ` -coset of ` B ` ,
       inference version.  (Contributed by Peter Mazsa, 11-May-2021.) $)
    eceq1i $p |- [ A ] C = [ B ] C $=
      ( wceq cec eceq1 ax-mp ) ABEACFBCFEDABCGH $.
  $}

  ${
    $d A x $.  $d B x $.  $d R x $.
    $( Restricted coset of ` B ` .  (Contributed by Peter Mazsa,
       9-Dec-2018.) $)
    ecres $p |- [ B ] ( R |` A ) = { x | ( B e. A /\ B R x ) } $=
      ( wcel cv wbr wa cres cec wb cvv elecres elv eqabi ) CBECAFZDGHZACDBIJZPR
      EQKABCPDLMNO $.
  $}

  ${
    $d A x $.  $d B x $.  $d V x $.
    $( Restricted converse epsilon coset of ` B ` .  (Contributed by Peter
       Mazsa, 11-Feb-2018.)  (Revised by Peter Mazsa, 21-Oct-2021.) $)
    eccnvepres $p |- ( B e. V ->
                       [ B ] ( `' _E |` A ) = { x e. B | B e. A } ) $=
      ( wcel cv cep ccnv wbr wa cab cres cec crab brcnvep anbi1cd abbidv df-rab
      ecres 3eqtr4g ) CDEZCBEZCAFZGHZIZJZAKUCCEZUBJZAKCUDBLMUBACNUAUFUHAUAUEUGU
      BCUCDOPQABCUDSUBACRT $.
  $}

  $( Elementhood in the converse epsilon coset of ` A ` is elementhood in
     ` A ` .  (Contributed by Peter Mazsa, 27-Jan-2019.) $)
  eleccnvep $p |- ( A e. V -> ( B e. [ A ] `' _E <-> B e. A ) ) $=
    ( cep ccnv cec wcel wbr wrel wb relcnv relelec ax-mp brcnvep bitrid ) BADEZ
    FGZABPHZACGBAGPIQRJDKBAPLMABCNO $.

  ${
    $d A x $.  $d V x $.
    $( The converse epsilon coset of a set is the set.  (Contributed by Peter
       Mazsa, 27-Jan-2019.) $)
    eccnvep $p |- ( A e. V -> [ A ] `' _E = A ) $=
      ( vx wcel cep ccnv cec cv eleccnvep eqrdv ) ABDCAEFGAACHBIJ $.
  $}

  $( Property of epsilon relation, see also ~ extid , ~ extssr and the comment
     of ~ df-ssr .  (Contributed by Peter Mazsa, 10-Jul-2019.) $)
  extep $p |- ( ( A e. V /\ B e. W ) ->
                ( [ A ] `' _E = [ B ] `' _E <-> A = B ) ) $=
    ( wcel cep ccnv cec eccnvep eqeqan12d ) ACEBDEAFGZHABKHBACIBDIJ $.

  $( Property of the epsilon relation.  (Contributed by Peter Mazsa,
     27-Apr-2020.) $)
  disjeccnvep $p |- ( ( A e. V /\ B e. W ) ->
    ( ( [ A ] `' _E i^i [ B ] `' _E ) = (/) <-> ( A i^i B ) = (/) ) ) $=
    ( wcel wa cep ccnv cec cin c0 eccnvep ineqan12d eqeq1d ) ACEZBDEZFAGHZIZBQI
    ZJABJKOPRASBACLBDLMN $.

  $( The restricted converse epsilon coset of an element of the restriction is
     the element itself.  (Contributed by Peter Mazsa, 16-Jul-2019.) $)
  eccnvepres2 $p |- ( B e. A -> [ B ] ( `' _E |` A ) = B ) $=
    ( wcel cep ccnv cres cec elecreseq eccnvep eqtrd ) BACBDEZAFGBKGBABKHBAIJ
    $.

  $( Condition for a restricted converse epsilon coset of a set to be the set
     itself.  (Contributed by Peter Mazsa, 11-May-2021.) $)
  eccnvepres3 $p |- ( B e. dom ( `' _E |` A ) ->
                      [ B ] ( `' _E |` A ) = B ) $=
    ( cep ccnv cres cdm wcel cec resdmres eceq2i eccnvepres2 eqtr3id ) BCDZAEZF
    ZGBNHBMOEZHBPNBMAIJOBKL $.

  ${
    $d A u x $.  $d B u $.  $d R u x $.
    $( Elementhood in a restricted domain quotient set.  (Contributed by Peter
       Mazsa, 21-Aug-2020.) $)
    eldmqsres $p |- ( B e. V ->
       ( B e. ( dom ( R |` A ) /. ( R |` A ) ) <->
         E. u e. A ( E. x x e. [ u ] R /\ B = [ u ] R ) ) ) $=
      ( wcel cres cdm cqs cv cec wceq wrex wex wa elqsg wb cvv eldmres2 pm5.32i
      elv anbi1i elecreseq eqeq2d anbi2i an21 an12 3bitr4i bitri rexbii2 bitrdi
      ) DFGDECHZIZUMJGDBKZUMLZMZBUNNAKUOELZGAOZDURMZPZBCNBUNDUMFQUQVABUNCUOUNGZ
      UQPUOCGZUSPZUQPZVCVAPZVBVDUQVBVDRBACUOESTUBUCUSVCUQPZPUSVCUTPZPVEVFVGVHUS
      VCUQUTVCUPURDCUOEUDUEUAUFVCUSUQUGVCUSUTUHUIUJUKUL $.
  $}

  ${
    $d A u x $.  $d B u x $.  $d R u x $.
    $( Elementhood in a restricted domain quotient set.  (Contributed by Peter
       Mazsa, 22-Aug-2020.) $)
    eldmqsres2 $p |- ( B e. V ->
       ( B e. ( dom ( R |` A ) /. ( R |` A ) ) <->
         E. u e. A E. x e. [ u ] R B = [ u ] R ) ) $=
      ( wcel cres cdm cqs cv cec wex wceq wa wrex eldmqsres df-rex 19.41v bitri
      rexbii bitr4di ) DFGDECHZIUCJGAKBKELZGZAMDUDNZOZBCPUFAUDPZBCPABCDEFQUHUGB
      CUHUEUFOAMUGUFAUDRUEUFASTUAUB $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d C x y $.
    $( Subclass theorem for quotient sets.  (Contributed by Peter Mazsa,
       12-Sep-2020.) $)
    qsss1 $p |- ( A C_ B -> ( A /. C ) C_ ( B /. C ) ) $=
      ( vy vx wss cv cec wceq wrex cab cqs ssrexv ss2abdv df-qs 3sstr4g ) ABFZD
      GEGCHIZEAJZDKREBJZDKACLBCLQSTDREABMNEDACOEDBCOP $.
  $}

  ${
    qseq1i.1 $e |- A = B $.
    $( Equality theorem for quotient set, inference form.  (Contributed by
       Peter Mazsa, 3-Jun-2021.) $)
    qseq1i $p |- ( A /. C ) = ( B /. C ) $=
      ( wceq cqs qseq1 ax-mp ) ABEACFBCFEDABCGH $.
  $}

  $( Binary relation on a restriction.  (Contributed by Peter Mazsa,
     2-Jan-2019.) $)
  brinxprnres $p |- ( C e. V ->
                      ( B ( R i^i ( A X. ran ( R |` A ) ) ) C <->
                        ( B e. A /\ B R C ) ) ) $=
    ( cres crn cxp cin wbr wcel wa brres2 brres bitr3id ) BCDADAFZGHIJBCPJCEKBA
    KBCDJLABCDMABCDENO $.

  ${
    $d A w x y z $.  $d R w x y z $.
    $( Restriction of a class as a class of ordered pairs.  (Contributed by
       Peter Mazsa, 2-Jan-2019.) $)
    inxprnres $p |- ( R i^i ( A X. ran ( R |` A ) ) ) =
                      { <. x , y >. | ( x e. A /\ x R y ) } $=
      ( vz vw cres crn cxp cin cv wcel wbr wa copab relinxp relopabv wb cvv weq
      cop eleq1w breq1 anbi12d breq2 anbi2d opelopabg el2v brinxprnres 3bitr2ri
      elv df-br eqrelriiv ) EFDCDCGHZIJZAKZCLZUPBKZDMZNZABOZCUNDPUTABQEKZFKZUAZ
      VALZVBCLZVBVCDMZNZVBVCUOMZVDUOLVEVHREFUTVFVBURDMZNVHABVBVCSSAETUQVFUSVJAE
      CUBUPVBURDUCUDBFTVJVGVFURVCVBDUEUFUGUHVIVHRFCVBVCDSUIUKVBVCUOULUJUM $.
  $}

  ${
    $d A x y $.  $d R x y $.
    $( Alternate definition of the restriction of a class.  (Contributed by
       Peter Mazsa, 2-Jan-2019.) $)
    dfres4 $p |- ( R |` A ) = ( R i^i ( A X. ran ( R |` A ) ) ) $=
      ( vx vy cres cv wcel wbr wa copab crn cxp cin dfres2 inxprnres eqtr4i ) B
      AEZCFZAGRDFBHICDJBAQKLMCDABNCDABOP $.
  $}

  ${
    $d A u $.  $d B u $.  $d V u $.  $d W u $.
    $( Equivalent expressions with existential quantification.  (Contributed by
       Peter Mazsa, 10-Sep-2021.) $)
    exan3 $p |- ( ( A e. V /\ B e. W ) ->
                  ( E. u ( A e. [ u ] R /\ B e. [ u ] R ) <->
                    E. u ( u R A /\ u R B ) ) ) $=
      ( wcel wa cv cec wbr wb cvv elecALTV el2v1 bi2anan9 exbidv ) BEGZCFGZHBAI
      ZDJZGZCUAGZHTBDKZTCDKZHARUBUDSUCUERUBUDLATBDMENOSUCUELATCDMFNOPQ $.
  $}

  ${
    $d B u $.  $d C u $.  $d V u $.  $d W u $.
    $( Equivalent expressions with existential quantification.  (Contributed by
       Peter Mazsa, 2-May-2021.) $)
    exanres $p |- ( ( B e. V /\ C e. W ) ->
        ( E. u ( u ( R |` A ) B /\ u ( S |` A ) C ) <->
          E. u e. A ( u R B /\ u S C ) ) ) $=
      ( wcel wa cv cres wbr wex wrex brres bi2anan9 anandi bitr4di exbidv
      df-rex ) CGIZDHIZJZAKZCEBLMZUEDFBLMZJZANUEBIZUECEMZUEDFMZJZJZANULABOUDUHU
      MAUDUHUIUJJZUIUKJZJUMUBUFUNUCUGUOBUECEGPBUEDFHPQUIUJUKRSTULABUAS $.
  $}

  ${
    $d B u $.  $d C u $.  $d V u $.  $d W u $.
    $( Equivalent expressions with restricted existential quantification.
       (Contributed by Peter Mazsa, 10-Sep-2021.) $)
    exanres3 $p |- ( ( B e. V /\ C e. W ) ->
        ( E. u e. A ( B e. [ u ] R /\ C e. [ u ] S ) <->
          E. u e. A ( u R B /\ u S C ) ) ) $=
      ( wcel wa cv cec wbr wb cvv elecALTV el2v1 bi2anan9 rexbidv ) CGIZDHIZJCA
      KZELIZDUBFLIZJUBCEMZUBDFMZJABTUCUEUAUDUFTUCUENAUBCEOGPQUAUDUFNAUBDFOHPQRS
      $.
  $}

  ${
    $d B u $.  $d C u $.  $d V u $.  $d W u $.
    $( Equivalent expressions with existential quantification.  (Contributed by
       Peter Mazsa, 10-Sep-2021.) $)
    exanres2 $p |- ( ( B e. V /\ C e. W ) ->
        ( E. u ( u ( R |` A ) B /\ u ( S |` A ) C ) <->
          E. u e. A ( B e. [ u ] R /\ C e. [ u ] S ) ) ) $=
      ( wcel wa cv cres wbr wex wrex cec exanres exanres3 bitr4d ) CGIDHIJAKZCE
      BLMTDFBLMJANTCEMTDFMJABOCTEPIDTFPIJABOABCDEFGHQABCDEFGHRS $.
  $}

  ${
    $d A x y $.
    $( Restricted converse epsilon relation as a class of ordered pairs.
       (Contributed by Peter Mazsa, 10-Feb-2018.) $)
    cnvepres $p |- ( `' _E |` A ) = { <. x , y >. | ( x e. A /\ y e. x ) } $=
      ( cep ccnv cres cv wcel wbr wa copab dfres2 wb cvv brcnvep anbi2i opabbii
      elv eqtri ) DEZCFAGZCHZUABGZTIZJZABKUBUCUAHZJZABKABCTLUEUGABUDUFUBUDUFMAU
      AUCNORPQS $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( Equality of relations.  (Contributed by Peter Mazsa, 8-Mar-2019.) $)
    eqrel2 $p |- ( ( Rel A /\ Rel B ) ->
                   ( A = B <-> A. x A. y ( x A y <-> x B y ) ) ) $=
      ( wrel wa wss cv wbr wi wal wceq wb ssrel3 bi2anan9 eqss 2albiim 3bitr4g
      ) CEZDEZFCDGZDCGZFAHZBHZCIZUCUDDIZJBKAKZUFUEJBKAKZFCDLUEUFMBKAKSUAUGTUBUH
      ABCDNABDCNOCDPUEUFABQR $.
  $}

  $( Range of converse is the domain.  (Contributed by Peter Mazsa,
     12-Feb-2018.) $)
  rncnv $p |- ran `' A = dom A $=
    ( cdm ccnv crn dfdm4 eqcomi ) ABACDAEF $.

  ${
    $d R x $.
    $( Alternate definition of domain.  (Contributed by Peter Mazsa,
       2-Mar-2018.) $)
    dfdm6 $p |- dom R = { x | [ x ] R =/= (/) } $=
      ( cv cec c0 wne cdm ecdmn0 eqabi ) ACZBDEFABGJBHI $.
  $}

  ${
    $d R x $.
    $( Alternate definition of range.  (Contributed by Peter Mazsa,
       1-Aug-2018.) $)
    dfrn6 $p |- ran R = { x | [ x ] `' R =/= (/) } $=
      ( crn ccnv cdm cv cec c0 wne cab df-rn dfdm6 eqtri ) BCBDZEAFNGHIAJBKANLM
      $.
  $}

  ${
    $d A x y $.
    $( The range of the restricted converse epsilon is the union of the
       restriction.  (Contributed by Peter Mazsa, 11-Feb-2018.)  (Revised by
       Peter Mazsa, 26-Sep-2021.) $)
    rncnvepres $p |- ran ( `' _E |` A ) = U. A $=
      ( vx vy cv wcel wa copab crn wex cab ccnv cres cuni rnopab cnvepres rneqi
      cep wrex dfuni2 df-rex abbii eqtri 3eqtr4i ) BDZAECDUDEZFZBCGZHUFBIZCJZQK
      ALZHAMZUFBCNUJUGBCAOPUKUEBARZCJUICBASULUHCUEBATUAUBUC $.
  $}

  ${
    dmecd.1 $e |- ( ph -> dom R = A ) $.
    dmecd.2 $e |- ( ph -> [ B ] R = [ C ] R ) $.
    $( Equality of the coset of ` B ` and the coset of ` C ` implies
       equivalence of domain elementhood (equivalence is not necessary as
       opposed to ~ ereldm ).  (Contributed by Peter Mazsa, 9-Oct-2018.) $)
    dmecd $p |- ( ph -> ( B e. A <-> C e. A ) ) $=
      ( cdm wcel cec c0 wne neeq1d ecdmn0 3bitr4g eleq2d 3bitr3d ) ACEHZIZDRIZC
      BIDBIACEJZKLDEJZKLSTAUAUBKGMCENDENOARBCFPARBDFPQ $.
  $}

  ${
    dmec2d.1 $e |- ( ph -> [ B ] R = [ C ] R ) $.
    $( Equality of the coset of ` B ` and the coset of ` C ` implies
       equivalence of domain elementhood (equivalence is not necessary as
       opposed to ~ ereldm ).  (Contributed by Peter Mazsa, 12-Oct-2018.) $)
    dmec2d $p |- ( ph -> ( B e. dom R <-> C e. dom R ) ) $=
      ( cdm eqidd dmecd ) ADFZBCDAIGEH $.
  $}

  $( Property of the identity binary relation.  (Contributed by Peter Mazsa,
     18-Dec-2021.) $)
  brid $p |- ( A _I B <-> B _I A ) $=
    ( cid wbr ccnv cnvi breqi reli relbrcnv bitr3i ) ABCDABCEZDBACDABKCFGABCHIJ
    $.

  $( For sets, the identity binary relation is the same as equality.
     (Contributed by Peter Mazsa, 24-Jun-2020.)  (Revised by Peter Mazsa,
     18-Dec-2021.) $)
  ideq2 $p |- ( A e. V -> ( A _I B <-> A = B ) ) $=
    ( cid wbr wcel wceq brid ideqg eqcom bitrdi bitrid ) ABDEBADEZACFZABGZABHNM
    BAGOBACIBAJKL $.

  $( Condition for the identity restriction to be a subclass of identity
     intersection with a Cartesian product.  (Contributed by Peter Mazsa,
     19-Jul-2018.) $)
  idresssidinxp $p |- ( A C_ B -> ( _I |` A ) C_ ( _I i^i ( A X. B ) ) ) $=
    ( wss cid cres cxp resss a1i idssxp xpss2 sstrid ssind ) ABCZDAEZDABFZNDCMD
    AGHMNAAFOAIABAJKL $.

  $( Condition for the identity restriction to be equal to the identity
     intersection with a Cartesian product.  (Contributed by Peter Mazsa,
     19-Jul-2018.) $)
  idreseqidinxp $p |- ( A C_ B -> ( _I i^i ( A X. B ) ) = ( _I |` A ) ) $=
    ( wss cid cxp cin cres inxpssres a1i idresssidinxp eqssd ) ABCZDABEFZDAGZMN
    CLABDHIABJK $.

  $( Property of identity relation, see also ~ extep , ~ extssr and the comment
     of ~ df-ssr .  (Contributed by Peter Mazsa, 5-Jul-2019.) $)
  extid $p |- ( A e. V -> ( [ A ] `' _I = [ B ] `' _I <-> A = B ) ) $=
    ( cid ccnv cec wceq csn wcel cnvi eceq2i ecidsn eqtri eqeq12i sneqbg bitrid
    ) ADEZFZBQFZGAHZBHZGACIABGRTSUARADFTQDAJKALMSBDFUAQDBJKBLMNABCOP $.

  ${
    $d A x y $.  $d B x y $.  $d R x y $.  $d S x y $.
    $( Two ways to say that an intersection with a Cartesian product is a
       subclass.  (Contributed by Peter Mazsa, 16-Jul-2019.) $)
    inxpss $p |- ( ( R i^i ( A X. B ) ) C_ S <->
                   A. x e. A A. y e. B ( x R y -> x S y ) ) $=
      ( cv cxp cin wbr wi wal wcel wa wss wral brinxp2 imbi1i impexp bitri wrel
      2albii wb relinxp ssrel3 ax-mp r2al 3bitr4i ) AGZBGZECDHIZJZUIUJFJZKZBLAL
      ZUICMUJDMNZUIUJEJZUMKZKZBLALUKFOZURBDPACPUNUSABUNUPUQNZUMKUSULVAUMCDUIUJE
      QRUPUQUMSTUBUKUAUTUOUCCDEUDABUKFUEUFURABCDUGUH $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d R x y $.
    $( Two ways to say that an intersection of the identity relation with a
       Cartesian product is a subclass.  (Contributed by Peter Mazsa,
       16-Jul-2019.) $)
    idinxpss $p |- ( ( _I i^i ( A X. B ) ) C_ R <->
                     A. x e. A A. y e. B ( x = y -> x R y ) ) $=
      ( cid cxp cin wss cv wbr wi wral weq inxpss wb cvv ideqg elv imbi1i bitri
      2ralbii ) FCDGHEIAJZBJZFKZUCUDEKZLZBDMACMABNZUFLZBDMACMABCDFEOUGUIABCDUEU
      HUFUEUHPBUCUDQRSTUBUA $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d R x y $.
    $( Two ways to say that an intersection of the identity relation with a
       Cartesian product is a subclass.  (Contributed by Peter Mazsa,
       12-Dec-2023.) $)
    ref5 $p |- ( ( _I i^i ( A X. B ) ) C_ R <-> A. x e. ( A i^i B ) x R x ) $=
      ( vy cv wceq wbr wral wcel cid cxp cin wss equcom imbi1i ralbii ceqsralbv
      wi breq2 bitr3i idinxpss ralin 3bitr4i ) AFZEFZGZUEUFDHZSZECIZABIUECJUEUE
      DHZSZABIKBCLMDNUKABCMIUJULABUJUFUEGZUHSZECIULUNUIECUMUGUHEAOPQUHUKEUECUFU
      EUEDTRUAQAEBCDUBUKABCUCUD $.
  $}

  ${
    $d x y $.  $d A y $.
    $( Two ways to say that an intersection with a Cartesian product is a
       subclass (see also ~ inxpss ).  (Contributed by Peter Mazsa,
       8-Mar-2019.) $)
    inxpss3 $p |- ( A. x A. y
        ( x ( R i^i ( A X. B ) ) y -> x ( S i^i ( A X. B ) ) y ) <->
        A. x e. A A. y e. B ( x R y -> x S y ) ) $=
      ( cv cxp cin wbr wi wal wcel wral brinxp2 imbi12i imdistan bitr4i 2albii
      wa r2al ) AGZBGZECDHZIJZUBUCFUDIJZKZBLALUBCMUCDMTZUBUCEJZUBUCFJZKZKZBLALU
      KBDNACNUGULABUGUHUITZUHUJTZKULUEUMUFUNCDUBUCEOCDUBUCFOPUHUIUJQRSUKABCDUAR
      $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d R x y $.  $d S x y $.
    $( Two ways to say that intersections with Cartesian products are in a
       subclass relation.  (Contributed by Peter Mazsa, 8-Mar-2019.) $)
    inxpss2 $p |- ( ( R i^i ( A X. B ) ) C_ ( S i^i ( A X. B ) ) <->
                    A. x e. A A. y e. B ( x R y -> x S y ) ) $=
      ( cxp cin wss cv wbr wi wal wral wrel wb relinxp ssrel3 ax-mp inxpss3
      bitri ) ECDGZHZFUBHZIZAJZBJZUCKUFUGUDKLBMAMZUFUGEKUFUGFKLBDNACNUCOUEUHPCD
      EQABUCUDRSABCDEFTUA $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d R x y $.
    $( Two ways to say that intersections with Cartesian products are in a
       subclass relation, special case of ~ inxpss2 .  (Contributed by Peter
       Mazsa, 4-Jul-2019.) $)
    inxpssidinxp $p |- ( ( R i^i ( A X. B ) ) C_ ( _I i^i ( A X. B ) ) <->
                         A. x e. A A. y e. B ( x R y -> x = y ) ) $=
      ( cxp cin cid wss cv wbr wi wral weq inxpss2 wb cvv ideqg elv imbi2i
      2ralbii bitri ) ECDFZGHUCGIAJZBJZEKZUDUEHKZLZBDMACMUFABNZLZBDMACMABCDEHOU
      HUJABCDUGUIUFUGUIPBUDUEQRSTUAUB $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d R x y $.
    $( Two ways to say that intersections with Cartesian products are in a
       subclass relation, special case of ~ inxpss2 .  (Contributed by Peter
       Mazsa, 6-Mar-2019.) $)
    idinxpssinxp $p |- ( ( _I i^i ( A X. B ) ) C_ ( R i^i ( A X. B ) ) <->
                         A. x e. A A. y e. B ( x = y -> x R y ) ) $=
      ( cid cxp cin wss cv wbr wi wral weq inxpss2 wb cvv ideqg elv imbi1i
      2ralbii bitri ) FCDGZHEUCHIAJZBJZFKZUDUEEKZLZBDMACMABNZUGLZBDMACMABCDFEOU
      HUJABCDUFUIUGUFUIPBUDUEQRSTUAUB $.
  $}

  ${
    $d A x $.  $d R x $.
    $( Identity intersection with a square Cartesian product in subclass
       relation with an intersection with the same Cartesian product.
       (Contributed by Peter Mazsa, 4-Mar-2019.)
       (Proof modification is discouraged.) $)
    idinxpssinxp2 $p |- ( ( _I i^i ( A X. A ) ) C_ ( R i^i ( A X. A ) ) <->
                          A. x e. A x R x ) $=
      ( cid cxp cin wss cv wcel wbr wa wral idinxpresid sseq1i idrefALT brinxp2
      cres pm4.24 anbi1i bitr4i ralbii 3bitri ralanid bitri ) DBBEZFZCUEFZGZAHZ
      BIZUIUICJZKZABLZUKABLUHDBQZUGGUIUIUGJZABLUMUFUNUGBMNABUGOUOULABUOUJUJKZUK
      KULBBUIUICPUJUPUKUJRSTUAUBUKABUCUD $.
  $}

  ${
    $d A x $.  $d R x $.
    $( Identity intersection with a square Cartesian product in subclass
       relation with an intersection with the same Cartesian product.
       (Contributed by Peter Mazsa, 16-Mar-2019.)
       (Proof modification is discouraged.) $)
    idinxpssinxp3 $p |- ( ( _I i^i ( A X. A ) ) C_ ( R i^i ( A X. A ) ) <->
                          ( _I |` A ) C_ R ) $=
      ( vx cid cxp cin wss cv wbr wral cres idinxpssinxp2 idrefALT bitr4i ) DAA
      EZFBOFGCHZPBICAJDAKBGCABLCABMN $.
  $}

  ${
    $d A x y $.  $d R x y $.
    $( Identity intersection with a square Cartesian product in subclass
       relation with an intersection with the same Cartesian product (see also
       ~ idinxpssinxp2 ).  (Contributed by Peter Mazsa, 8-Mar-2019.) $)
    idinxpssinxp4 $p |- ( A. x e. A A. y e. A ( x = y -> x R y ) <->
                          A. x e. A x R x ) $=
      ( weq cv wbr wi wral cid cxp cin wss idinxpssinxp idinxpssinxp2 bitr3i )
      ABEAFZBFDGHBCIACIJCCKZLDRLMQQDGACIABCCDNACDOP $.
  $}

  ${
    $d R x y $.
    $( Two ways of saying a relation is symmetric.  (Contributed by FL,
       31-Aug-2009.) $)
    relcnveq3 $p |- ( Rel R ->
                      ( R = `' R <-> A. x A. y ( x R y -> y R x ) ) ) $=
      ( ccnv wceq wss wa wrel cv wbr wi wal eqss cnvsym biimpi a1d adantl com12
      dfrel2 cnvss sseq1 syl5ibcom sylbir sylbi biimpri jca2 impbid bitrid ) CC
      DZECUIFZUICFZGZCHZAIZBIZCJUOUNCJKBLALZCUIMUMULUPULUMUPUKUMUPKUJUKUPUMUKUP
      ABCNZOPQRUMUPUJUKUMUIDZCEZUPUJKCSUPUSUJUPUKUSUJKUQUKURUIFUSUJUICTURCUIUAU
      BUCRUDUKUPUQUEUFUGUH $.
  $}

  ${
    $d R x y $.
    $( Two ways of saying a relation is symmetric.  (Contributed by Peter
       Mazsa, 23-Aug-2018.) $)
    relcnveq $p |- ( Rel R -> ( `' R C_ R <-> `' R = R ) ) $=
      ( vx vy wrel ccnv wceq wss cv wbr wi wal relcnveq3 cnvsym bitr4di bitr3di
      eqcom ) ADZAAEZFZRAGZRAFQSBHZCHZAIUBUAAIJCKBKTBCALBCAMNARPO $.
  $}

  ${
    $d R x y $.
    $( Two ways of saying a relation is symmetric.  (Contributed by Peter
       Mazsa, 28-Apr-2019.) $)
    relcnveq2 $p |- ( Rel R ->
                      ( `' R = R <-> A. x A. y ( x R y <-> y R x ) ) ) $=
      ( wrel ccnv wss wa cv wbr wi wal wceq wb cnvsym a1i dfrel2 biimpi bitr3di
      sseq1d relbrcnvg imbi12d 2albidv bitrd anbi12d eqss 2albiim 3bitr4g ) CDZ
      CEZCFZCUIFZGAHZBHZCIZUMULCIZJBKAKZUOUNJZBKAKZGUICLUNUOMBKAKUHUJUPUKURUJUP
      MUHABCNOUHUKULUMUIIZUMULUIIZJZBKAKZURUHUIEZUIFUKVBUHVCCUIUHVCCLCPQSABUINR
      UHVAUQABUHUSUOUTUNULUMCTUMULCTUAUBUCUDUICUEUNUOABUFUG $.
  $}

  ${
    $d R x y $.
    $( Two ways of saying a relation is symmetric.  (Contributed by Peter
       Mazsa, 28-Apr-2019.) $)
    relcnveq4 $p |- ( Rel R ->
                      ( `' R C_ R <-> A. x A. y ( x R y <-> y R x ) ) ) $=
      ( wrel ccnv wss wceq cv wbr wb wal relcnveq relcnveq2 bitrd ) CDCEZCFOCGA
      HZBHZCIQPCIJBKAKCLABCMN $.
  $}

  ${
    $d A u v $.  $d R u v $.
    $( Simplification of a special quotient set.  (Contributed by Peter Mazsa,
       2-Sep-2020.) $)
    qsresid $p |- ( A /. ( R |` A ) ) = ( A /. R ) $=
      ( vu vv cv cres cec wceq wrex cab cqs wcel elecreseq eqeq2d rexbiia abbii
      df-qs 3eqtr4i ) CEZDEZBAFZGZHZDAIZCJSTBGZHZDAIZCJAUAKABKUDUGCUCUFDATALUBU
      ESATBMNOPDCAUAQDCABQR $.
  $}

  ${
    $d A x $.  $d R x $.
    $( Two ways of expressing that the empty set is not an element of a
       quotient set.  (Contributed by Peter Mazsa, 5-Dec-2019.) $)
    n0elqs $p |- ( -. (/) e. ( A /. R ) <-> A C_ dom R ) $=
      ( vx cv cdm wcel wral cec c0 wne wss cqs ecdmn0 ralbii wrex rexbii notbii
      wn wceq 3bitr4ri dfss3 nne dfral2 0ex elqs eqcom bitri ) CDZBEZFZCAGUHBHZ
      IJZCAGZAUIKIABLFZRZUJULCAUHBMNCAUIUAULRZCAOZRUKISZCAOZRUMUOUQUSUPURCAUKIU
      BPQULCAUCUNUSUNIUKSZCAOUSCAIBUDUEUTURCAIUKUFPUGQTT $.
  $}

  $( Two ways of expressing that the empty set is not an element of a quotient
     set.  (Contributed by Peter Mazsa, 25-Jul-2021.) $)
  n0elqs2 $p |- ( -. (/) e. ( A /. R ) <-> dom ( R |` A ) = A ) $=
    ( c0 cqs wcel wn cdm wss cres wceq n0elqs ssdmres bitri ) CABDEFABGHBAIGAJA
    BKABLM $.

  $( The range of a restriction is equal to the union of the quotient set.
     (Contributed by Peter Mazsa, 19-May-2018.) $)
  rnresequniqs $p |- ( ( R |` A ) e. V -> ran ( R |` A ) = U. ( A /. R ) ) $=
    ( cres wcel cqs cuni cima crn uniqs df-ima eqtr2di ) BADZCEABFGBAHMIABCJBAK
    L $.

  ${
    $d A x y $.
    $( Two ways of expressing that the empty set is not an element of a class.
       (Contributed by Peter Mazsa, 31-Jan-2018.) $)
    n0el2 $p |- ( -. (/) e. A <-> dom ( `' _E |` A ) = A ) $=
      ( vy vx cv wcel wex wral wa copab cdm wceq cep ccnv cres dmopab3 cnvepres
      c0 wn n0el dmeqi eqeq1i 3bitr4i ) BDCDZEZBFCAGUCAEUDHCBIZJZAKQAERLMANZJZA
      KUDCBAOCBASUHUFAUGUECBAPTUAUB $.
  $}

  ${
    $d A x y $.  $d V x $.
    $( Sethood condition for the restricted converse epsilon relation.
       (Contributed by Peter Mazsa, 24-Sep-2018.) $)
    cnvepresex $p |- ( A e. V -> ( `' _E |` A ) e. _V ) $=
      ( vx vy wcel cep ccnv cres cv wa copab cvv cnvepres cab abid2 vex eqeltri
      id a1i opabex3d eqeltrid ) ABEZFGAHCIZAEZDIUCEZJCDKLCDAMUBUECDABUBRUEDNZL
      EUBUDJUFUCLDUCOCPQSTUA $.
  $}

  $( The image of converse epsilon.  (Contributed by Peter Mazsa,
     22-Mar-2023.) $)
  cnvepima $p |- ( A e. V -> ( `' _E " A ) = U. A ) $=
    ( wcel cep ccnv cqs cuni cima cres cvv wceq cnvepresex uniqs unieqi eqtr3di
    syl qsid ) ABCZADEZFZGZSAHZAGRSAIJCUAUBKABLASJMPTAAQNO $.

  $( Sufficient condition for the intersection relation to be a set.
     (Contributed by Peter Mazsa, 24-Nov-2019.) $)
  inex3 $p |- ( ( A e. V \/ B e. W ) -> ( A i^i B ) e. _V ) $=
    ( wcel cin cvv inex1g inex2g jaoi ) ACEABFGEBDEABCHBADIJ $.

  $( Sufficient condition for an intersection with a Cartesian product to be a
     set.  (Contributed by Peter Mazsa, 10-May-2019.) $)
  inxpex $p |- ( ( R e. W \/ ( A e. U /\ B e. V ) ) ->
                 ( R i^i ( A X. B ) ) e. _V ) $=
    ( wcel cxp cin cvv wa inex1g xpexg inex2g syl jaoi ) CFGCABHZIJGZADGBEGKZCQ
    FLSQJGRABDEMQCJNOP $.

  ${
    eqres.1 $e |- R = ( S |` C ) $.
    $( Converting a class constant definition by restriction (like ~ df-ers or
       ~ df-parts ) into a binary relation.  (Contributed by Peter Mazsa,
       1-Oct-2018.) $)
    eqres $p |- ( B e. V -> ( A R B <-> ( A e. C /\ A S B ) ) ) $=
      ( wbr cres wcel wa breqi brres bitrid ) ABDHABECIZHBFJACJABEHKABDOGLCABEF
      MN $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x y z ps $.
    brrabga.1 $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
    ${
      brrabga.2 $e |- R = { <. <. x , y >. , z >. | ph } $.
      $( The law of concretion for operation class abstraction.  (Contributed
         by Peter Mazsa, 24-Oct-2022.) $)
      brrabga $p |- ( ( A e. V /\ B e. W /\ C e. X ) ->
                      ( <. A , B >. R C <-> ps ) ) $=
        ( cop wbr coprab wcel w3a df-br eleq2i bitri eloprabga bitrid ) FGOZHIP
        ZUEHOZACDEQZRZFJRGKRHLRSBUFUGIRUIUEHITIUHUGNUAUBABCDEFGHJKLMUCUD $.
    $}

    ${
      brcnvrabga.2 $e |- R = `' { <. <. y , z >. , x >. | ph } $.
      $( The law of concretion for the converse of operation class abstraction.
         (Contributed by Peter Mazsa, 25-Oct-2022.) $)
      brcnvrabga $p |- ( ( A e. V /\ B e. W /\ C e. X ) ->
                         ( A R <. B , C >. <-> ps ) ) $=
        ( wbr ccnv wcel wrel cv wceq cop coprab relcnv releqi mpbir relbrcnv wb
        w3a 3coml cnveqi reloprab dfrel2 mpbi eqtri brrabga 3comr bitr3id ) FGH
        UAZIOURFIPZOZFJQZGKQZHLQZUHBURFIIRADECUBZPZRVDUCIVENUDUEUFVBVCVAUTBUGAB
        DECGHFUSKLJCSFTDSGTESHTABUGMUIUSVEPZVDIVENUJVDRVFVDTADECUKVDULUMUNUOUPU
        Q $.
    $}
  $}

  $( Equality conditions for ordered pairs ` <. A , A >. ` and
     ` <. B , B >. ` .  (Contributed by Peter Mazsa, 22-Jul-2019.)  (Revised by
     Thierry Arnoux, 16-Feb-2022.) $)
  opideq $p |- ( A e. V -> ( <. A , A >. = <. B , B >. <-> A = B ) ) $=
    ( wcel cop wceq wa wb opthg anidms anidm bitrdi ) ACDZAAEBBEFZABFZOGZOMNPHA
    ABBCCIJOKL $.

  ${
    $d A x y $.
    $( A subclass of the identity relation is the intersection of identity
       relation with Cartesian product of the domain and range of the class.
       (Contributed by Peter Mazsa, 22-Jul-2019.) $)
    iss2 $p |- ( A C_ _I <-> A = ( _I i^i ( dom A X. ran A ) ) ) $=
      ( vx vy cid wss cdm crn cxp wceq cv cop wcel wb wal wa jca2 biimtrid wrel
      vex wi cin ssel opeldm opelrn jcad anandi imbitrrdi wbr df-br ideq bitr3i
      wex eldm2 opeq2 eleq1d biimprcd sylcom exlimdv syl5ibcom imp adantrd impd
      imbi2d impbid opelinxp biancomi bitr4di alrimivv reli relss relinxp eqrel
      ex mpi sylancl mpbird inss1 sseq1 mpbiri impbii ) ADEZADAFZAGZHZUAZIZWAWF
      BJZCJZKZALZWIWELZMZCNBNZWAWLBCWAWJWIDLZWGWBLZWHWCLZOZOZWKWAWJWRWAWJWNWOOZ
      WNWPOZOWRWAWJWSWTWAWJWNWOADWIUBZWGWHABSZCSZUCPWAWJWNWPXAWGWHAXBXCUDPUEWNW
      OWPUFUGWAWNWQWJWNWGWHIZWAWQWJTZWNWGWHDUHXDWGWHDUIWGWHXCUJUKZWAXDXEWAXDOWO
      WJWPWAXDWOWJTZWAWOWGWGKZALZTXDXGWOWJCULWAXICWGAXBUMWAWJXICWAWJWNXIXAWNXDW
      JXIXFXDXIWJXDXHWIAWGWHWGUNUOZUPQUQURQXDXIWJWOXJVCUSUTVAVMQVBVDWKWNWQWBWCW
      GWHDVEVFVGVHWAARZWERWFWMMWADRXKVIADVJVNWBWCDVKBCAWEVLVOVPWFWAWEDEDWDVQAWE
      DVRVSVT $.
  $}

  ${
    $d A u $.  $d R u $.  $d V u $.
    $( Elementhood in a domain of a converse.  (Contributed by Peter Mazsa,
       25-May-2018.) $)
    eldmcnv $p |- ( A e. V -> ( A e. dom `' R <-> E. u u R A ) ) $=
      ( wcel ccnv cdm cv wbr wex eldmg wb cvv brcnvg elvd exbidv bitrd ) BDEZBC
      FZGEBAHZSIZAJTBCIZAJABSDKRUAUBARUAUBLABTDMCNOPQ $.
  $}

  $( Alternate definition of the relation predicate.  (Contributed by Peter
     Mazsa, 6-Nov-2018.) $)
  dfrel5 $p |- ( Rel R <-> ( R |` dom R ) = R ) $=
    ( wrel ccnv wceq cdm cres dfrel2 resdm2 eqeq1i bitr4i ) ABACCZADAAEFZADAGLK
    AAHIJ $.

  $( Alternate definition of the relation predicate.  (Contributed by Peter
     Mazsa, 14-Mar-2019.) $)
  dfrel6 $p |- ( Rel R <-> ( R i^i ( dom R X. ran R ) ) = R ) $=
    ( wrel cdm cres wceq crn cxp cin dfrel5 dfres3 eqeq1i bitri ) ABAACZDZAEAMA
    FGHZAEAINOAAMJKL $.

  $( Converse restricted to range is converse.  (Contributed by Peter Mazsa,
     3-Sep-2021.) $)
  cnvresrn $p |- ( `' R |` ran R ) = `' R $=
    ( ccnv crn cres cdm df-rn reseq2i wrel wceq relcnv dfrel5 mpbi eqtri ) ABZA
    CZDNNEZDZNOPNAFGNHQNIAJNKLM $.

  $( Subset of restriction, special case.  (Contributed by Peter Mazsa,
     10-Apr-2023.) $)
  relssinxpdmrn $p |- ( Rel R ->
                        ( R C_ ( S i^i ( dom R X. ran R ) ) <-> R C_ S ) ) $=
    ( wrel wss cdm crn cxp wa cin relssdmrn biantrud ssin bitr2di ) ACZABDZOAAE
    AFGZDZHABPIDNQOAJKABPLM $.

  $( Two ways to say that a relation is a subclass.  (Contributed by Peter
     Mazsa, 11-Apr-2023.) $)
  cnvref4 $p |- ( Rel R ->
      ( ( R i^i ( dom R X. ran R ) ) C_ ( S i^i ( dom R X. ran R ) ) <->
        R C_ S ) ) $=
    ( wrel cdm crn cxp cin wceq dfrel6 biimpi dmeqd rneqd xpeq12d ineq2d sseq2d
    wss wb relxp relin2 relssinxpdmrn mp2b sseq1d bitrid bitr3d ) ACZAADZAEZFZG
    ZBUIDZUIEZFZGZPZUIBUHGZPABPZUEUMUOUIUEULUHBUEUJUFUKUGUEUIAUEUIAHAIJZKUEUIAU
    QLMNOUNUIBPZUEUPUHCUICUNURQUFUGRAUHSUIBTUAUEUIABUQUBUCUD $.

  ${
    $d R x y $.
    $( Two ways to say that a relation is a subclass of the identity relation.
       (Contributed by Peter Mazsa, 26-Jun-2019.) $)
    cnvref5 $p |- ( Rel R -> ( R C_ _I <-> A. x A. y ( x R y -> x = y ) ) ) $=
      ( wrel cid wss cv wbr wi wal ssrel3 wb cvv ideqg elv imbi2i 2albii bitrdi
      wceq ) CDCEFAGZBGZCHZTUAEHZIZBJAJUBTUASZIZBJAJABCEKUDUFABUCUEUBUCUELBTUAM
      NOPQR $.
  $}

  ${
    $d A x $.  $d B x $.  $d R x $.  $d V x $.  $d W x $.
    $( Two ways of saying that the coset of ` A ` and the coset of ` B ` have
       no elements in common.  (Contributed by Peter Mazsa, 1-Dec-2018.) $)
    ecin0 $p |- ( ( A e. V /\ B e. W ) ->
                  ( ( [ A ] R i^i [ B ] R ) = (/) <->
                    A. x ( A R x -> -. B R x ) ) ) $=
      ( cec cin c0 wceq cv wcel wn wi wal wa wbr disj1 wb cvv elecg adantr elvd
      el2v1 elecALTV adantl notbid imbi12d albidv bitrid ) BDGZCDGZHIJAKZUKLZUM
      ULLZMZNZAOBELZCFLZPZBUMDQZCUMDQZMZNZAOAUKULRUTUQVDAUTUNVAUPVCURUNVASZUSUR
      VEAUMBDTEUAUDUBUTUOVBUSUOVBSZURUSVFACUMDFTUEUCUFUGUHUIUJ $.
  $}

  ${
    $d A x $.  $d B x $.  $d R x $.  $d V x $.  $d W x $.
    $( Two ways of saying that the coset of ` A ` and the coset of ` B ` have
       some elements in common.  (Contributed by Peter Mazsa, 23-Jan-2019.) $)
    ecinn0 $p |- ( ( A e. V /\ B e. W ) ->
                     ( ( [ A ] R i^i [ B ] R ) =/= (/) <->
                       E. x ( A R x /\ B R x ) ) ) $=
      ( wcel wa cec cin c0 wne cv wbr wn wi wal wex ecin0 necon3abid notnotb
      anbi2i exbii exanali bitri bitr4di ) BEGCFGHZBDICDIJZKLBAMZDNZCUIDNZOZPAQ
      ZOZUJUKHZARZUGUMUHKABCDEFSTUPUJULOZHZARUNUOURAUKUQUJUKUAUBUCUJULAUDUEUF
      $.
  $}

  ${
    $d B z $.  $d C z $.  $d D z $.  $d x z $.  $d y z $.
    $( Equivalence of restricted universal quantifications.  (Contributed by
       Peter Mazsa, 29-May-2018.) $)
    ineleq $p |- ( A. x e. A A. y e. B ( x = y \/ ( C i^i D ) = (/) ) <->
                   A. x e. A A. z A. y e. B
                   ( ( z e. C /\ z e. D ) -> x = y ) ) $=
      ( cv wceq cin c0 wo wral wcel wa wi wal wex bitri ralbii orcom df-or neq0
      wn elin exbii imbi1i 19.23v bitr4i 3bitri ralcom4 ) AHBHIZFGJZKIZLZBEMZCH
      ZFNUQGNOZULPZBEMCQZADUPUSCQZBEMUTUOVABEUOUNULLUNUDZULPZVAULUNUAUNULUBVCUR
      CRZULPVAVBVDULVBUQUMNZCRVDCUMUCVEURCUQFGUEUFSUGURULCUHUIUJTUSBCEUKST $.
  $}

  ${
    $d A x y z $.  $d B y z $.  $d C x z $.  $d R x y z $.
    inecmo.1 $e |- ( x = y -> B = C ) $.
    $( Equivalence of a double restricted universal quantification and a
       restricted "at most one" inside a universal quantification.
       (Contributed by Peter Mazsa, 29-May-2018.) $)
    inecmo $p |- ( Rel R ->
        ( A. x e. A A. y e. A ( x = y \/ ( [ B ] R i^i [ C ] R ) = (/) ) <->
          A. z E* x e. A B R z ) ) $=
      ( wrel cv wceq cec wral wcel wa wi wal wbr relelec bitr4id cin c0 wo wrmo
      ineleq ralcom4 bitri breq1d rmo4 anbi12d imbi1d 2ralbidv albidv ) GIZAJBJ
      KZEGLZFGLZUAUBKUCBDMADMZCJZUPNZUSUQNZOZUOPZBDMZADMZCQZEUSGRZADUDZCQURVDCQ
      ADMVFABCDDUPUQUEVDACDUFUGUNVHVECUNVHVGFUSGRZOZUOPZBDMADMVEVGVIABDUOEFUSGH
      UHUIUNVCVKABDDUNVBVJUOUNUTVGVAVIUSEGSUSFGSUJUKULTUMT $.
  $}

  ${
    $d A u v x $.  $d R u v x $.
    $( Equivalence of a double restricted universal quantification and a
       restricted "at most one" inside a universal quantification.
       (Contributed by Peter Mazsa, 29-May-2018.)  (Revised by Peter Mazsa,
       2-Sep-2021.) $)
    inecmo2 $p |-
         ( ( A. u e. A A. v e. A ( u = v \/ ( [ u ] R i^i [ v ] R ) = (/) ) /\
             Rel R ) <->
           ( A. x E* u e. A u R x /\ Rel R ) ) $=
      ( wrel cv wceq cec cin c0 wo wral wbr wrmo wal id inecmo pm5.32ri ) EFCGZ
      BGZHZTEIUAEIJKHLBDMCDMTAGENCDOAPCBADTUAEUBQRS $.
  $}

  ${
    $d B x y z $.  $d F x y z $.
    $( Equivalence of a double restricted universal quantification and a
       restricted "at most one" inside a universal quantification.
       (Contributed by Peter Mazsa, 2-Sep-2021.) $)
    ineccnvmo $p |-
        ( A. y e. B A. z e. B ( y = z \/ ( [ y ] `' F i^i [ z ] `' F ) = (/) )
            <->
          A. x E* y e. B x F y ) $=
      ( cv wceq ccnv cec cin c0 wo wral wbr wrmo wal wrel wb relcnv cvv id el2v
      inecmo ax-mp brcnvg rmobii albii bitri ) BFZCFZGZUIEHZIUJULIJKGLCDMBDMZUI
      AFZULNZBDOZAPZUNUIENZBDOZAPULQUMUQRESBCADUIUJULUKUAUCUDUPUSAUOURBDUOURRBA
      UIUNTTEUEUBUFUGUH $.
  $}

  $( Equivalence of an "at most one" and an "at most one" restricted to the
     range inside a universal quantification.  (Contributed by Peter Mazsa,
     3-Sep-2021.) $)
  alrmomorn $p |- ( A. x E* y e. ran R x R y <-> A. x E* y x R y ) $=
    ( cv wbr crn wrmo wmo wcel wa df-rmo ccnv cres cnvresrn breqi cvv brres elv
    wb bitri brcnvg el2v anbi2i 3bitr3i mobii albii ) ADZBDZCEZBCFZGZUIBHZAUKUH
    UJIZUIJZBHULUIBUJKUNUIBUHUGCLZUJMZEZUHUGUOEZUNUIUHUGUPUOCNOUQUMURJZUNUQUSSA
    UJUHUGUOPQRURUIUMURUISBAUHUGPPCUAUBZUCTUTUDUETUF $.

  ${
    $d R u $.  $d R x $.
    $( Equivalence of an "at most one" and an "at most one" restricted to the
       domain inside a universal quantification.  (Contributed by Peter Mazsa,
       5-Sep-2021.) $)
    alrmomodm $p |- ( Rel R ->
                      ( A. x E* u e. dom R u R x <-> A. x E* u u R x ) ) $=
      ( wrel cv wbr cdm wrmo wmo wcel wa df-rmo cres wb cvv brres resdm bitr3id
      elv breqd mobidv bitrid albidv ) CDZBEZAEZCFZBCGZHZUGBIZAUIUEUHJUGKZBIUDU
      JUGBUHLUDUKUGBUKUEUFCUHMZFZUDUGUMUKNAUHUEUFCOPSUDULCUEUFCQTRUAUBUC $.
  $}

  ${
    $d R u $.  $d u x $.
    $( "At most one" can be restricted to the range.  (Contributed by Peter
       Mazsa, 2-Feb-2026.) $)
    ralmo $p |- ( A. x E* u u R x <-> A. x e. ran R E* u u R x ) $=
      ( cv wbr wmo wal crn wcel wi wa cvv brelrng el3v12 pm4.71ri mobii moanimv
      wral bitri albii df-ral bitr4i ) BDZADZCEZBFZAGUDCHZIZUFJZAGUFAUGRUFUIAUF
      UHUEKZBFUIUEUJBUEUHUEUHBAUCUDCLLMNOPUHUEBQSTUFAUGUAUB $.
  $}

  ${
    $d R u x $.
    $( On the range, "at most one" becomes "exactly one".  (Contributed by
       Peter Mazsa, 27-Sep-2018.)  (Revised by Peter Mazsa, 2-Feb-2026.) $)
    ralrnmo $p |- ( A. x e. ran R E* u u R x <-> A. x e. ran R E! u u R x ) $=
      ( cv wbr wmo crn wral wex wa weu wcel dfrn2 eqabri biimpi biantrurd df-eu
      ralbiia ralbii bitr4i ) BDADZCEZBFZACGZHUBBIZUCJZAUDHUBBKZAUDHUCUFAUDUAUD
      LZUEUCUHUEUEAUDBACMNOPRUGUFAUDUBBQST $.
  $}

  $( Sethood of the domain quotient under sethood of ` R ` .  (Contributed by
     Peter Mazsa, 2-Nov-2018.) $)
  dmqsex $p |- ( R e. V -> ( dom R /. R ) e. _V ) $=
    ( wcel cdm cvv cqs dmexg qsexg syl ) ABCADZECJAFECABGJAEHI $.

  ${
    $d R t u $.
    $( On the quotient carrier, "at most one" and "exactly one" coincide for
       coset witnesses.  (Contributed by Peter Mazsa, 6-Feb-2026.) $)
    raldmqsmo $p |- ( A. u e. ( dom R /. R ) E* t e. dom R u = [ t ] R <->
                      A. u e. ( dom R /. R ) E! t e. dom R u = [ t ] R ) $=
      ( cv cec wceq cdm wrmo wreu cqs wcel wrex wa eqabri biimpi biantrurd reu5
      df-qs bitr4di ralbiia ) ADZBDCEFZBCGZHZUBBUCIZAUCCJZUAUFKZUDUBBUCLZUDMUEU
      GUHUDUGUHUHAUFBAUCCRNOPUBBUCQST $.
  $}

  ${
    $d A x $.  $d B x $.  $d x y $.
    $( Pull a restricted universal quantifier into the body (for ` E* ` ).
       (Contributed by Peter Mazsa, 9-May-2019.) $)
    ralrmo3 $p |- ( A. y e. B E* x e. A ph <->
                    A. y E* x e. A ( y e. B /\ ph ) ) $=
      ( wrmo wral cv wcel wi wal wa df-ral nfv rmoanim albii bitr4i ) ABDFZCEGC
      HEIZRJZCKSALBDFZCKRCEMUATCSABDSBNOPQ $.
  $}

  ${
    $d R t u $.  $d V t u $.
    $( Equivalence between "exactly one" on the quotient carrier and "at most
       one" globally.  Provides a type-safe way to talk about unique
       representatives either as ` E! ` on the intended carrier or as a global
       ` E* ` statement.  (Contributed by Peter Mazsa, 6-Feb-2026.) $)
    raldmqseu $p |- ( R e. V ->
                      ( A. u e. ( dom R /. R ) E! t e. dom R u = [ t ] R <->
                        A. u E* t e. dom R u = [ t ] R ) ) $=
      ( cv cec wceq cdm wreu cqs wral wcel wa wrmo wal raldmqsmo ralrmo3 bitr3i
      ancom bitrid eqelb 3bitr3i eceldmqs anbi1d rmobidv rmoanid bitrdi albidv
      ) AEZBEZCFZGZBCHZIAUMCJZKZUIUNLZULMZBUMNZAOZCDLZULBUMNZAOUOVAAUNKUSABCPUL
      BAUMUNQRUTURVAAUTURUJUMLZULMZBUMNVAUTUQVCBUMUQUKUNLZULMZUTVCULUPMULVDMUQV
      EUIUKUNUAULUPSULVDSUBUTVDVBULUJCDUCUDTUEULBUMUFUGUHT $.
  $}

  ${
    $d x y $.
    rsp3.1 $e |- F/_ x A $.
    rsp3.2 $e |- F/_ y A $.
    rsp3.3 $e |- F/ y ph $.
    rsp3.4 $e |- F/ x ps $.
    rsp3.5 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( From a restricted universal statement over ` A ` , specialize to an
       arbitrary element ` y e. A ` , cf. ~ rsp .  (Contributed by Peter Mazsa,
       9-Feb-2026.) $)
    rsp3 $p |- ( A. x e. A ph -> ( y e. A -> ps ) ) $=
      ( wral cv wcel wi cbvralfw rsp sylbi ) ACEKBDEKDLEMBNABCDEFGHIJOBDEPQ $.

    $( From a restricted universal statement over ` A ` , specialize to an
       arbitrary element class, cf. ~ rsp3 .  (Contributed by Peter Mazsa,
       9-Feb-2026.) $)
    rsp3eq $p |- ( A. x e. A ph -> ( ( y = B /\ B e. A ) -> ps ) ) $=
      ( cv wceq wcel wa wral eqeltr rsp3 syl5 ) DLZFMFENOTENACEPBTFEQABCDEGHIJK
      RS $.
  $}

  ${
    $d F u x y $.
    $( Equivalence of a double universal quantification restricted to the range
       and an "at most one" inside a universal quantification.  (Contributed by
       Peter Mazsa, 4-Sep-2021.) $)
    ineccnvmo2 $p |- ( A. x e. ran F A. y e. ran F
                       ( x = y \/ ( [ x ] `' F i^i [ y ] `' F ) = (/) ) <->
                       A. u E* x u F x ) $=
      ( cv wceq ccnv cec cin c0 crn wral wbr wrmo wal ineccnvmo alrmomorn bitri
      wo wmo ) AEZBEZFUADGZHUBUCHIJFSBDKZLAUDLCEUADMZAUDNCOUEATCOCABUDDPCADQR
      $.
  $}

  ${
    $d R u v x $.
    $( Equivalence of a double universal quantification restricted to the
       domain and an "at most one" inside a universal quantification.
       (Contributed by Peter Mazsa, 5-Sep-2021.) $)
    inecmo3 $p |- ( ( A. u e. dom R A. v e. dom R
          ( u = v \/ ( [ u ] R i^i [ v ] R ) = (/) ) /\ Rel R ) <->
        ( A. x E* u u R x /\ Rel R ) ) $=
      ( cv wceq cec cin c0 wo cdm wral wrel wbr wrmo wal wmo inecmo2 alrmomodm
      wa pm5.32ri bitri ) CEZBEZFUCDGUDDGHIFJBDKZLCUELDMZTUCAEDNZCUEOAPZUFTUGCQ
      APZUFTABCUEDRUFUHUIACDSUAUB $.
  $}

  $( Uniqueness is equivalent to non-existence or unique existence.  Alternate
     definition of the at-most-one quantifier, in terms of the existential
     quantifier and the unique existential quantifier.  (Contributed by Peter
     Mazsa, 19-Nov-2024.) $)
  moeu2 $p |- ( E* x ph <-> ( -. E. x ph \/ E! x ph ) ) $=
    ( wmo wex weu wi wn wo moeu imor bitri ) ABCABDZABEZFLGMHABILMJK $.

  $( "At most one" picks a variable value, eliminating an existential
     quantifier.  The proof begins with references *2.21 ( ~ pm2.21 ) and
     *14.26 ( ~ eupickbi ) from [WhiteheadRussell] p. 104 and p. 183.
     (Contributed by Peter Mazsa, 18-Nov-2024.)
     (Proof modification is discouraged.) $)
  mopickr $p |- ( ( E* x ps /\ E. x ( ph /\ ps ) ) -> ( ps -> ph ) ) $=
    ( wmo wa wex wi exancom wn weu wo moeu2 19.8a con3i pm2.21 syl a1d eupickbi
    wal sp biimtrdi jaoi sylbi biimtrid imp ) BCDZABECFZBAGZUGBAECFZUFUHABCHUFB
    CFZIZBCJZKUIUHGZBCLUKUMULUKUHUIUKBIUHBUJBCMNBAOPQULUIUHCSUHBACRUHCTUAUBUCUD
    UE $.

  $( Sufficient condition for transitivity of conjunctions inside existential
     quantifiers.  (Contributed by Peter Mazsa, 2-Oct-2018.) $)
  moantr $p |- ( E* x ps ->
                 ( ( E. x ( ph /\ ps ) /\ E. x ( ps /\ ch ) ) ->
                   E. x ( ph /\ ch ) ) ) $=
    ( wmo wa wex wi w3a exancom anbi1i anbi2i 3anass bitr4i mopick2 sylbi exbii
    exsimpr syl impexp mpbi ) BDEZABFDGZBCFDGZFZFZACFZDGZHUBUEUHHHUFBACIZDGZUHU
    FUBBAFDGZUDIZUJUFUBUKUDFZFULUEUMUBUCUKUDABDJKLUBUKUDMNBACDOPUJBUGFZDGUHUIUN
    DBACMQBUGDRPSUBUEUHTUA $.

  ${
    $d x y $.
    brabidgaw.1 $e |- R = { <. x , y >. | ph } $.
    $( The law of concretion for a binary relation.  Special case of ~ brabga .
       Version of ~ brabidga with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by Peter Mazsa, 24-Nov-2018.)  (Revised
       by GG, 2-Apr-2024.) $)
    brabidgaw $p |- ( x R y <-> ph ) $=
      ( cv wbr copab cop wcel breqi df-br opabidw 3bitri ) BFZCFZDGOPABCHZGOPIQ
      JAOPDQEKOPQLABCMN $.
    $( $j usage 'brabidgaw' avoids 'ax-13'; $)
  $}

  ${
    brabidga.1 $e |- R = { <. x , y >. | ph } $.
    $( The law of concretion for a binary relation.  Special case of ~ brabga .
       Usage of this theorem is discouraged because it depends on ~ ax-13 , see
       ~ brabidgaw for a weaker version that does not require it.  (Contributed
       by Peter Mazsa, 24-Nov-2018.)  (New usage is discouraged.) $)
    brabidga $p |- ( x R y <-> ph ) $=
      ( cv wbr copab cop wcel breqi df-br opabid 3bitri ) BFZCFZDGOPABCHZGOPIQJ
      AOPDQEKOPQLABCMN $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d R x y $.
    $( Intersection with a Cartesian product.  (Contributed by Peter Mazsa,
       18-Jul-2019.) $)
    inxp2 $p |- ( R i^i ( A X. B ) ) =
                { <. x , y >. | ( ( x e. A /\ y e. B ) /\ x R y ) } $=
      ( cxp cin cv copab wcel wa wrel wceq relinxp dfrel4v mpbi brinxp2 opabbii
      wbr eqtri ) ECDFGZAHZBHZUASZABIZUBCJUCDJKUBUCESKZABIUALUAUEMCDENABUAOPUDU
      FABCDUBUCEQRT $.
  $}

  ${
    opabf.1 $e |- -. ph $.
    $( A class abstraction of a collection of ordered pairs with a negated wff
       is the empty set.  (Contributed by Peter Mazsa, 21-Oct-2019.)  (Proof
       shortened by Thierry Arnoux, 18-Feb-2022.) $)
    opabf $p |- { <. x , y >. | ph } = (/) $=
      ( copab c0 wceq wn wal gen2 opab0 mpbir ) ABCEFGAHZCIBIMBCDJABCKL $.
  $}

  $( The empty-coset of a class is the empty set.  (Contributed by Peter Mazsa,
     19-May-2019.) $)
  ec0 $p |- [ A ] (/) = (/) $=
    ( c0 cec csn cima df-ec 0ima eqtri ) ABCBADZEBABFIGH $.

  $( Intersection with a converse, binary relation.  (Contributed by Peter
     Mazsa, 24-Mar-2024.) $)
  brcnvin $p |- ( ( A e. V /\ B e. W ) ->
                  ( A ( R i^i `' S ) B <-> ( A R B /\ B S A ) ) ) $=
    ( ccnv cin wbr wa wcel brin brcnvg anbi2d bitrid ) ABCDGZHIABCIZABPIZJAEKBF
    KJZQBADIZJABCPLSRTQABEFDMNO $.

  ${
    $d A x $.  $d R x y $.
    $( Subclass of a domain.  (Contributed by Peter Mazsa, 15-Sep-2018.) $)
    ssdmral $p |- ( A C_ dom R <-> A. x e. A E. y x R y ) $=
      ( cdm wss cv wcel wral wbr wex dfss3 wb cvv eldmg elv ralbii bitri ) CDEZ
      FAGZSHZACITBGDJBKZACIACSLUAUBACUAUBMABTDNOPQR $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Range Cartesian product
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define the range Cartesian product of two classes.  Definition from
     [Holmes] p. 40.  Membership in this class is characterized by ~ xrnss3v
     and ~ brxrn .  This is Scott Fenton's ~ df-txp with a different symbol,
     see ~ https://github.com/metamath/set.mm/issues/2469 .  (Contributed by
     Scott Fenton, 31-Mar-2012.) $)
  df-xrn $a |- ( A |X. B ) = ( ( `' ( 1st |` ( _V X. _V ) ) o. A ) i^i
                               ( `' ( 2nd |` ( _V X. _V ) ) o. B ) ) $.

  ${
    $d A x y z $.  $d B x y z $.
    $( A range Cartesian product is a subset of the class of ordered triples.
       This is Scott Fenton's ~ txpss3v with a different symbol, see
       ~ https://github.com/metamath/set.mm/issues/2469 .  (Contributed by
       Scott Fenton, 31-Mar-2012.) $)
    xrnss3v $p |- ( A |X. B ) C_ ( _V X. ( _V X. _V ) ) $=
      ( vx vy vz cxrn c1st cvv cxp cres ccnv ccom c2nd cin df-xrn inss1 cv wcel
      wbr vex relco wa wex cop brcnv brresi simplbi sylbi adantl exlimiv opelco
      opelxp mpbiran 3imtr4i relssi sstri eqsstri ) ABFGHHIZJZKZALZMURJKBLZNZHU
      RIZABOVCVAVDVAVBPCDVAVDUTAUACQZEQZASZVFDQZUTSZUBZEUCVHURRZVEVHUDZVARVLVDR
      ZVJVKEVIVKVGVIVHVFUSSZVKVFVHUSETZDTZUEVNVKVHVFGSURVHVFGVOUFUGUHUIUJEVEVHU
      TACTZVPUKVMVEHRVKVQVEVHHURULUMUNUOUPUQ $.
  $}

  $( A range Cartesian product is a relation.  This is Scott Fenton's ~ txprel
     with a different symbol, see
     ~ https://github.com/metamath/set.mm/issues/2469 .  (Contributed by Scott
     Fenton, 31-Mar-2012.) $)
  xrnrel $p |- Rel ( A |X. B ) $=
    ( cxrn wrel cvv cxp wss xrnss3v xpss sstri df-rel mpbir ) ABCZDMEEFZGMENFNA
    BHENIJMKL $.

  ${
    $d A x $.  $d A y $.  $d B x $.  $d B y $.  $d C x $.  $d C y $.  $d R x $.
    $d S y $.  $d V x $.  $d V y $.  $d W x $.  $d W y $.  $d X x $.  $d X y $.
    $( Characterize a ternary relation over a range Cartesian product.
       Together with ~ xrnss3v , this characterizes elementhood in a range
       cross.  (Contributed by Peter Mazsa, 27-Jun-2021.) $)
    brxrn $p |- ( ( A e. V /\ B e. W /\ C e. X ) ->
                  ( A ( R |X. S ) <. B , C >. <-> ( A R B /\ A S C ) ) ) $=
      ( vx vy wcel wbr c1st cvv c2nd wa wb wex mpan2 elv w3a cop cxrn cres ccnv
      cxp ccom cin df-xrn breqi brin cv wceq opex brcog 3ad2ant1 brcnvg opelvvg
      a1i brres biantrurd bitr4id br1steqg bitrd 3adant1 bitrid exbidv ceqsexgv
      anbi1cd breq2 3ad2ant2 3bitrd br2ndeqg 3ad2ant3 anbi12d ) AFKZBGKZCHKZUAZ
      ABCUBZDEUCZLZAVTMNNUFZUDZUEZDUGZOWCUDZUEZEUGZUHZLZAVTWFLZAVTWILZPZABDLZAC
      ELZPWBWKQVSAVTWAWJDEUIUJUSWKWNQVSAVTWFWIUKUSVSWLWOWMWPVSWLAIULZDLZWQVTWEL
      ZPZIRZWQBUMZWRPZIRZWOVPVQWLXAQZVRVPVTNKZXEBCUNZIAVTWEDFNUOSUPVSWTXCIVSWSX
      BWRWSVTWQWDLZVSXBWSXHQZIWQNKXFXIXGWQVTNNWDUQSTVQVRXHXBQVPVQVRPZXHVTWQMLZX
      BXJXHVTWCKZXKPZXKXHXMQIWCVTWQMNUTTXJXLXKBCGHURZVAVBBCWQGHVCVDVEVFVIVGVQVP
      XDWOQVRWRWOIBGWQBADVJVHVKVLVSWMAJULZELZXOVTWHLZPZJRZXOCUMZXPPZJRZWPVPVQWM
      XSQZVRVPXFYCXGJAVTWHEFNUOSUPVSXRYAJVSXQXTXPXQVTXOWGLZVSXTXQYDQZJXONKXFYEX
      GXOVTNNWGUQSTVQVRYDXTQVPXJYDVTXOOLZXTXJYDXLYFPZYFYDYGQJWCVTXOONUTTXJXLYFX
      NVAVBBCXOGHVMVDVEVFVIVGVRVPYBWPQVQXPWPJCHXOCAEVJVHVNVLVOVL $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d R x y $.  $d S x y $.  $d V x y $.
    $( A characterization of the range Cartesian product.  (Contributed by
       Peter Mazsa, 14-Oct-2020.) $)
    brxrn2 $p |- ( A e. V ->
                   ( A ( R |X. S ) B <->
                     E. x E. y ( B = <. x , y >. /\ A R x /\ A S y ) ) ) $=
      ( cxrn wbr cv cop wceq wa wex wcel w3a cvv cxp xrnss3v brel elvv pm4.71ri
      simprd sylib 19.41vv breq2 pm5.32i 2exbii 3bitr2i wb el3v23 anbi2d 3anass
      brxrn bitr4di 2exbidv bitrid ) CDEFHZIZDAJZBJZKZLZCVBURIZMZBNANZCGOZVCCUT
      EIZCVAFIZPZBNANUSVCBNANZUSMVCUSMZBNANVFUSVKUSDQQRZOZVKUSCQOVNCDQVMUREFSTU
      CABDUAUDUBVCUSABUEVLVEABVCUSVDDVBCURUFUGUHUIVGVEVJABVGVEVCVHVIMZMVJVGVDVO
      VCVGVDVOUJABCUTVAEFGQQUNUKULVCVHVIUMUOUPUQ $.
  $}

  ${
    $d R u x y z $.  $d S u x y z $.
    $( Alternate definition of the range Cartesian product.  (Contributed by
       Peter Mazsa, 20-Feb-2022.) $)
    dfxrn2 $p |- ( R |X. S ) =
                 `' { <. <. x , y >. , u >. | ( u R x /\ u S y ) } $=
      ( vz cxrn cv wbr copab cop coprab ccnv wa wrel wceq xrnrel cvv wex wb cxp
      dfrel4v mpbi breq2 wcel w3a brxrn2 brxrn el3v anbi2i 3anass bitr4i 2exbii
      elv copsex2gb 3bitr2i simplbi cnvoprab oprabbii cnveqi 3eqtr2i ) DEGZCHZF
      HZVBIZCFJZVCAHZBHZKZVBIZABCLZMVCVGDIZVCVHEIZNZABCLZMVBOVBVFPDEQCFVBUBUCVJ
      VEABCFVDVIVCVBUDZVEVDRRUAUEZVEVEVDVIPZVLVMUFZBSASZVRVJNZBSASVQVENVEVTTCAB
      VCVDDERUGUNWAVSABWAVRVNNVSVJVNVRVJVNTCABVCVGVHDERRRUHUIZUJVRVLVMUKULUMVEV
      JABVDVPUOUPUQURVKVOVJVNABCWBUSUTVA $.
  $}

  $( The range product with converse epsilon relation.  (Contributed by Peter
     Mazsa, 22-Jun-2020.)  (Revised by Peter Mazsa, 22-Nov-2025.) $)
  brxrncnvep $p |- ( ( A e. V /\ B e. W /\ C e. X ) ->
        ( A ( R |X. `' _E ) <. B , C >. <-> ( C e. A /\ A R B ) ) ) $=
    ( wcel w3a cop cep ccnv cxrn wbr wa brxrn wb brcnvep anbi1cd 3ad2ant1 bitrd
    ) AEHZBFHZCGHZIABCJDKLZMNABDNZACUENZOZCAHZUFOZABCDUEEFGPUBUCUHUJQUDUBUGUIUF
    ACERSTUA $.

  ${
    $d R x y z $.  $d S x y z $.
    $( Domain of the range product.  (Contributed by Peter Mazsa, 19-Apr-2020.)
       (Revised by Peter Mazsa, 22-Nov-2025.) $)
    dmxrn $p |- dom ( R |X. S ) = ( dom R i^i dom S ) $=
      ( vz vx vy cxrn cdm cv wbr wex cab cin wa exdistrv coprab ccnv crn dfxrn2
      abbii df-dm dmeqi df-rn rnoprab 3eqtr2i inab 3eqtr4i ineq12i eqtr4i ) ABF
      ZGZCHZDHAIZDJZCKZUKEHBIZEJZCKZLZAGZBGZLULUOMZEJDJZCKZUMUPMZCKUJURVBVDCULU
      ODENSUJVADECOZPZGVEQVCUIVFDECABRUAVEUBVADECUCUDUMUPCUEUFUSUNUTUQCDATCEBTU
      GUH $.
  $}

  ${
    $d x y $.
    $( Domain of converse epsilon relation.  (Contributed by Peter Mazsa,
       30-Jan-2018.)  (Revised by Peter Mazsa, 23-Nov-2025.) $)
    dmcnvep $p |- dom `' _E = ( _V \ { (/) } ) $=
      ( vx vy cep ccnv cdm cv wbr wex cab wcel cvv c0 csn cdif df-dm wb brcnvep
      elv exbii abbii wceq wn df-sn difeq2i notab neq0 3eqtr2ri 3eqtri ) CDZEAF
      ZBFZUIGZBHZAIUKUJJZBHZAIZKLMZNZABUIOUMUOAULUNBULUNPAUJUKKQRSTURKUJLUAZAIZ
      NUSUBZAIUPUQUTKALUCUDUSAUEVAUOABUJUFTUGUH $.
  $}

  $( Domain of the range product with converse epsilon relation.  (Contributed
     by Peter Mazsa, 23-Nov-2025.) $)
  dmxrncnvep $p |- dom ( R |X. `' _E ) = ( dom R \ { (/) } ) $=
    ( cep ccnv cxrn cdm cin cvv c0 csn cdif dmxrn dmcnvep ineq2i invdif 3eqtri
    ) ABCZDEAEZPEZFQGHIZJZFQSJAPKRTQLMQSNO $.

  $( Domain of the restricted converse epsilon relation.  (Contributed by Peter
     Mazsa, 28-Jan-2026.) $)
  dmcnvepres $p |- dom ( `' _E |` A ) = ( A \ { (/) } ) $=
    ( cep ccnv cres cdm cin cvv c0 csn cdif dmres dmcnvep ineq2i invdif 3eqtri
    ) BCZADEAPEZFAGHIZJZFARJPAKQSALMARNO $.

  $( Domain of the union with the converse epsilon, restricted.  (Contributed
     by Peter Mazsa, 28-Jan-2026.) $)
  dmuncnvepres $p |- dom ( ( R u. `' _E ) |` A ) =
                     ( A i^i ( dom R u. ( _V \ { (/) } ) ) ) $=
    ( cep ccnv cun cres cdm cin cvv c0 csn cdif dmres dmun dmcnvep uneq2i eqtri
    ineq2i ) BCDZEZAFGATGZHABGZIJKLZEZHTAMUAUDAUAUBSGZEUDBSNUEUCUBOPQRQ $.

  $( Domain of the combined relation of two special relations, see
     ~ blockadjliftmap .  (Contributed by Peter Mazsa, 28-Jan-2026.) $)
  dmxrnuncnvepres $p |- dom ( ( ( R |X. `' _E ) u. `' _E ) |` A ) =
                        ( A \ { (/) } ) $=
    ( cep ccnv cxrn cun cres cdm cvv c0 csn cdif dmuncnvepres dmxrncnvep uneq1i
    cin difundir unv difeq1i 3eqtr2i ineq2i invdif 3eqtri ) BCDZEZUDFAGHAUEHZIJ
    KZLZFZPAUHPAUGLAUEMUIUHAUIBHZUGLZUHFUJIFZUGLUHUFUKUHBNOUJIUGQULIUGUJRSTUAAU
    GUBUC $.

  ${
    $d A x $.  $d R x $.  $d S x $.  $d V x $.
    $( The union coset of ` A ` .  (Contributed by Peter Mazsa,
       28-Jan-2026.) $)
    ecun $p |- ( A e. V -> [ A ] ( R u. S ) = ( [ A ] R u. [ A ] S ) ) $=
      ( vx wcel cv wbr cab cun wo cec wceq unab a1i dfec2 uneq12d cvv elecALTV
      wb elvd brun bitrdi eqabdv 3eqtr4rd ) ADFZAEGZBHZEIZAUGCHZEIZJZUHUJKZEIZA
      BLZACLZJABCJZLZULUNMUFUHUJENOUFUOUIUPUKEABDPEACDPQUFUMEURUFUGURFZAUGUQHZU
      MUFUSUTTEAUGUQDRSUAAUGBCUBUCUDUE $.
  $}

  $( The restricted union coset of ` B ` .  (Contributed by Peter Mazsa,
     28-Jan-2026.) $)
  ecunres $p |- ( B e. V ->
     [ B ] ( ( R u. S ) |` A ) = ( [ B ] ( R |` A ) u. [ B ] ( S |` A ) ) ) $=
    ( wcel cun cres cec resundir eceq2i ecun eqtrid ) BEFBCDGAHZIBCAHZDAHZGZIBO
    IBPIGNQBCDAJKBOPELM $.

  $( The restricted union with converse epsilon relation coset of ` B ` .
     (Contributed by Peter Mazsa, 28-Jan-2026.) $)
  ecuncnvepres $p |- ( B e. A ->
                       [ B ] ( ( R u. `' _E ) |` A ) = ( B u. [ B ] R ) ) $=
    ( wcel cep ccnv cun cres ecunres elecreseq eccnvepres2 uneq12d eqtrd eqtrdi
    cec uncom ) BADZBCEFZGAHOZBCOZBGZBTGQSBCAHOZBRAHOZGUAABCRAIQUBTUCBABCJABKLM
    TBPN $.

  $( Equality theorem for the range Cartesian product.  (Contributed by Peter
     Mazsa, 16-Dec-2020.) $)
  xrneq1 $p |- ( A = B -> ( A |X. C ) = ( B |X. C ) ) $=
    ( wceq c1st cvv cxp cres ccnv ccom c2nd cxrn coeq2 ineq1d df-xrn 3eqtr4g
    cin ) ABDZEFFGZHIZAJZKSHICJZQTBJZUBQACLBCLRUAUCUBABTMNACOBCOP $.

  ${
    xrneq1i.1 $e |- A = B $.
    $( Equality theorem for the range Cartesian product, inference form.
       (Contributed by Peter Mazsa, 16-Dec-2020.) $)
    xrneq1i $p |- ( A |X. C ) = ( B |X. C ) $=
      ( wceq cxrn xrneq1 ax-mp ) ABEACFBCFEDABCGH $.
  $}

  ${
    xrneq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality theorem for the range Cartesian product, deduction form.
       (Contributed by Peter Mazsa, 7-Sep-2021.) $)
    xrneq1d $p |- ( ph -> ( A |X. C ) = ( B |X. C ) ) $=
      ( wceq cxrn xrneq1 syl ) ABCFBDGCDGFEBCDHI $.
  $}

  $( Equality theorem for the range Cartesian product.  (Contributed by Peter
     Mazsa, 16-Dec-2020.) $)
  xrneq2 $p |- ( A = B -> ( C |X. A ) = ( C |X. B ) ) $=
    ( wceq c1st cvv cxp cres ccnv ccom c2nd cxrn coeq2 ineq2d df-xrn 3eqtr4g
    cin ) ABDZEFFGZHICJZKSHIZAJZQTUABJZQCALCBLRUBUCTABUAMNCAOCBOP $.

  ${
    xrneq2i.1 $e |- A = B $.
    $( Equality theorem for the range Cartesian product, inference form.
       (Contributed by Peter Mazsa, 16-Dec-2020.) $)
    xrneq2i $p |- ( C |X. A ) = ( C |X. B ) $=
      ( wceq cxrn xrneq2 ax-mp ) ABECAFCBFEDABCGH $.
  $}

  ${
    xrneq2d.1 $e |- ( ph -> A = B ) $.
    $( Equality theorem for the range Cartesian product, deduction form.
       (Contributed by Peter Mazsa, 7-Sep-2021.) $)
    xrneq2d $p |- ( ph -> ( C |X. A ) = ( C |X. B ) ) $=
      ( wceq cxrn xrneq2 syl ) ABCFDBGDCGFEBCDHI $.
  $}

  $( Equality theorem for the range Cartesian product.  (Contributed by Peter
     Mazsa, 16-Dec-2020.) $)
  xrneq12 $p |- ( ( A = B /\ C = D ) -> ( A |X. C ) = ( B |X. D ) ) $=
    ( wceq cxrn xrneq1 xrneq2 sylan9eq ) ABECDEACFBCFBDFABCGCDBHI $.

  ${
    xrneq12i.1 $e |- A = B $.
    xrneq12i.2 $e |- C = D $.
    $( Equality theorem for the range Cartesian product, inference form.
       (Contributed by Peter Mazsa, 16-Dec-2020.) $)
    xrneq12i $p |- ( A |X. C ) = ( B |X. D ) $=
      ( wceq cxrn xrneq12 mp2an ) ABGCDGACHBDHGEFABCDIJ $.
  $}

  ${
    xrneq12d.1 $e |- ( ph -> A = B ) $.
    xrneq12d.2 $e |- ( ph -> C = D ) $.
    $( Equality theorem for the range Cartesian product, deduction form.
       (Contributed by Peter Mazsa, 18-Dec-2021.) $)
    xrneq12d $p |- ( ph -> ( A |X. C ) = ( B |X. D ) ) $=
      ( wceq cxrn xrneq12 syl2anc ) ABCHDEHBDICEIHFGBCDEJK $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d R x y $.  $d S x y $.  $d V x y $.
    $( Elementhood in the ` ( R |X. S ) ` -coset of ` A ` .  (Contributed by
       Peter Mazsa, 18-Apr-2020.)  (Revised by Peter Mazsa, 21-Sep-2021.) $)
    elecxrn $p |- ( A e. V -> ( B e. [ A ] ( R |X. S ) <->
                    E. x E. y ( B = <. x , y >. /\ A R x /\ A S y ) ) ) $=
      ( cxrn cec wcel wbr cv cop wceq w3a wex wrel wb xrnrel relelec brxrn2
      ax-mp bitrid ) DCEFHZIJZCDUDKZCGJDALZBLZMNCUGEKCUHFKOBPAPUDQUEUFREFSDCUDT
      UBABCDEFGUAUC $.
  $}

  ${
    $d A x y z $.  $d R x y z $.  $d S x y z $.  $d V x y z $.
    $( The ` ( R |X. S ) ` -coset of ` A ` .  (Contributed by Peter Mazsa,
       18-Apr-2020.)  (Revised by Peter Mazsa, 21-Sep-2021.) $)
    ecxrn $p |- ( A e. V ->
                  [ A ] ( R |X. S ) = { <. y , z >. | ( A R y /\ A S z ) } ) $=
      ( vx wcel cxrn cec cv wbr wa copab cop wceq wex w3a elecxrn 3anass 2exbii
      bitrdi elopab bitr4di eqrdv ) CFHZGCDEIJZCAKZDLZCBKZELZMZABNZUFGKZUGHZUNU
      HUJOPZULMZBQAQZUNUMHUFUOUPUIUKRZBQAQURABCUNDEFSUSUQABUPUIUKTUAUBULABUNUCU
      DUE $.
  $}

  ${
    $d A y z $.  $d R y z $.  $d S y z $.  $d V y z $.
    $( The ` ( R |X. S ) ` -coset of a set is a relation.  (Contributed by
       Peter Mazsa, 15-Oct-2020.) $)
    relecxrn $p |- ( A e. V -> Rel [ A ] ( R |X. S ) ) $=
      ( vy vz wcel cxrn cec wrel cv wbr wa copab relopab ecxrn releqd mpbiri )
      ADGZABCHIZJAEKBLAFKCLMZEFNZJUAEFOSTUBEFABCDPQR $.
  $}

  ${
    $d A x y $.  $d R x y $.  $d S x y $.  $d V x y $.
    $( The ` ( R |X. S ) ` -coset of a set is the Cartesian product of its
       ` R ` -coset and ` S ` -coset.  (Contributed by Peter Mazsa,
       16-Oct-2020.) $)
    ecxrn2 $p |- ( A e. V -> [ A ] ( R |X. S ) = ( [ A ] R X. [ A ] S ) ) $=
      ( vx vy cxrn cec wrel cxp wa wcel wceq relecxrn cv wbr cvv elecALTV elvd
      wb relxp jctir cop brxrn el3v23 opex mpan2 anbi12d 3bitr4d opelxp bitr4di
      eqrelrdv2 mpancom ) ABCGZHZIZABHZACHZJZIZKADLZUOUSMVAUPUTABCDNUQURUAUBVAE
      FUOUSVAEOZFOZUCZUOLZVBUQLZVCURLZKZVDUSLVAAVDUNPZAVBBPZAVCCPZKZVEVHVAVIVLT
      EFAVBVCBCDQQUDUEVAVDQLVEVITVBVCUFAVDUNDQRUGVAVFVJVGVKVAVFVJTEAVBBDQRSVAVG
      VKTFAVCCDQRSUHUIVBVCUQURUJUKULUM $.
  $}

  ${
    $d A y z $.  $d R y z $.  $d V y z $.
    $( The ` ( R |X. ``' _E ) ` -coset of a set.  (Contributed by Peter Mazsa,
       22-May-2021.) $)
    ecxrncnvep $p |- ( A e. V ->
        [ A ] ( R |X. `' _E ) = { <. y , z >. | ( z e. A /\ A R y ) } ) $=
      ( wcel cep ccnv cxrn cec cv wa copab ecxrn brcnvep anbi1cd opabbidv eqtrd
      wbr ) CEFZCDGHZIJCAKDSZCBKZUASZLZABMUCCFZUBLZABMABCDUAENTUEUGABTUDUFUBCUC
      EOPQR $.
  $}

  $( The ` ( R |X. ``' _E ) ` -coset of a set is the Cartesian product of its
     ` R ` -coset and the set.  (Contributed by Peter Mazsa, 25-Jan-2026.) $)
  ecxrncnvep2 $p |- ( A e. V -> [ A ] ( R |X. `' _E ) = ( [ A ] R X. A ) ) $=
    ( wcel cep ccnv cxrn cec cxp ecxrn2 eccnvep xpeq2d eqtrd ) ACDZABEFZGHABHZA
    OHZIPAIABOCJNQAPACKLM $.

  ${
    $d A u v $.  $d R u v $.  $d V u $.
    $( Double restricted quantification over the union of a set and its
       singleton.  (Contributed by Peter Mazsa, 22-Aug-2023.) $)
    disjressuc2 $p |- ( A e. V ->
       ( A. u e. ( A u. { A } ) A. v e. ( A u. { A } )
           ( u = v \/ ( [ u ] R i^i [ v ] R ) = (/) ) <->
         ( A. u e. A A. v e. A ( u = v \/ ( [ u ] R i^i [ v ] R ) = (/) ) /\
           A. u e. A ( [ u ] R i^i [ A ] R ) = (/) ) ) ) $=
      ( wcel cv wceq cec c0 wo wral wa eqeq1 eceq1 ineq1d eqeq1d orbi12d anbi2i
      cin csn cun eqeq2 ineq2d 2ralunsn eqid biantru bitr4di eqcom bitrdi incom
      orci w3a eqtrdi cbvralvw biimpi pm4.71i 3anass df-3an elneq neneqd biorfd
      3bitr2ri ralbiia ) CEFZBGZAGZHZVFDIZVGDIZTZJHZKZACCUAUBZLBVNLZVMACLBCLZVF
      CHZVICDIZTZJHZKZBCLZMZVPVTBCLZMVEVOWCCVGHZVRVJTZJHZKZACLZMZWCVEVOWCWICCHZ
      VRVRTZJHZKZMZMWJVMWAWHWNBACCEVQVHWEVLWGVFCVGNVQVKWFJVQVIVRVJVFCDOZPQRVGCH
      ZVHVQVLVTVGCVFUCWQVKVSJWQVJVRVIVGCDOUDQRVQVQWKVTWMVFCCNVQVSWLJVQVIVRVRWPP
      QRUEWIWOWCWNWIWKWMCUFULUGSUHWCVPWBWIMZMVPWBWIUMWJWBWRVPWBWIWBWIWAWHBACVHV
      QWEVTWGVHVQWQWEVFVGCNVGCUIUJVHVSWFJVHVSVJVRTWFVHVIVJVRVFVGDOPVJVRUKUNQRUO
      UPUQSVPWBWIURVPWBWIUSVCUJWDWBVPVTWABCVFCFZVQVTWSVFCVFCUTVAVBVDSUH $.
  $}

  ${
    $d A y z $.  $d B y z $.  $d R y z $.  $d S y z $.  $d V y z $.
    $d W y z $.
    $( Two ways of saying that ` ( R |X. S ) ` -cosets are disjoint.
       (Contributed by Peter Mazsa, 19-Jun-2020.)  (Revised by Peter Mazsa,
       21-Aug-2023.) $)
    disjecxrn $p |- ( ( A e. V /\ B e. W ) ->
       ( ( [ A ] ( R |X. S ) i^i [ B ] ( R |X. S ) ) = (/) <->
         ( ( [ A ] R i^i [ B ] R ) = (/) \/
           ( [ A ] S i^i [ B ] S ) = (/) ) ) ) $=
      ( vy vz wcel wa cec cin c0 wceq wne cv wbr wex copab bitrdi wo cxrn ecxrn
      ineqan12d inopab eqtrdi an4 opabbii neeq1d opabn0 exdistrv ecinn0 anbi12d
      wn bitr4d neanior necon4abid ) AEIZBFIZJZACKBCKLZMNADKBDKLZMNUAZACDUBZKZB
      VDKZLZMUTVGMOZVAMOZVBMOZJZVCUNUTVHAGPZCQZBVLCQZJZGRZAHPZDQZBVQDQZJZHRZJZV
      KUTVHVOVTJZHRGRZWBUTVHWCGHSZMOWDUTVGWEMUTVGVMVRJZVNVSJZJZGHSZWEUTVGWFGHSZ
      WGGHSZLWIURUSVEWJVFWKGHACDEUCGHBCDFUCUDWFWGGHUEUFWHWCGHVMVRVNVSUGUHUFUIWC
      GHUJTVOVTGHUKTUTVIVPVJWAGABCEFULHABDEFULUMUOVAMVBMUPTUQ $.
  $}

  $( Two ways of saying that cosets are disjoint, special case of ~ disjecxrn .
     (Contributed by Peter Mazsa, 12-Jul-2020.)  (Revised by Peter Mazsa,
     25-Aug-2023.) $)
  disjecxrncnvep $p |- ( ( A e. V /\ B e. W ) ->
      ( ( [ A ] ( R |X. `' _E ) i^i [ B ] ( R |X. `' _E ) ) = (/) <->
        ( ( A i^i B ) = (/) \/ ( [ A ] R i^i [ B ] R ) = (/) ) ) ) $=
    ( wcel wa cep ccnv cxrn cec cin c0 wceq disjecxrn bitrdi disjeccnvep orbi1d
    wo orcom bitrd ) ADFBEFGZACHIZJZKBUDKLMNZAUCKBUCKLMNZACKBCKLMNZSZABLMNZUGSU
    BUEUGUFSUHABCUCDEOUGUFTPUBUFUIUGABDEQRUA $.

  ${
    $d A u v $.  $d R u v $.  $d V u $.
    $( Double restricted quantification over the union of a set and its
       singleton.  (Contributed by Peter Mazsa, 22-Aug-2023.) $)
    disjsuc2 $p |- ( A e. V ->
       ( A. u e. ( A u. { A } ) A. v e. ( A u. { A } )
           ( u = v \/
             ( [ u ] ( R |X. `' _E ) i^i [ v ] ( R |X. `' _E ) ) = (/) ) <->
         ( A. u e. A A. v e. A
            ( u = v \/
              ( [ u ] ( R |X. `' _E ) i^i [ v ] ( R |X. `' _E ) ) = (/) ) /\
           A. u e. A
              ( ( u i^i A ) = (/) \/
                ( [ u ] R i^i [ A ] R ) = (/) ) ) ) ) $=
      ( wcel cv wceq cep ccnv cxrn cec cin c0 wo csn cun wral wa disjressuc2 wb
      cvv disjecxrncnvep el2v1 ralbidv anbi2d bitrd ) CEFZBGZAGZHUIDIJKZLZUJUKL
      MNHOZACCPQZRBUNRUMACRBCRZULCUKLMNHZBCRZSUOUICMNHUIDLCDLMNHOZBCRZSABCUKETU
      HUQUSUOUHUPURBCUHUPURUABUICDUBEUCUDUEUFUG $.
  $}

  ${
    $d A u x y z $.  $d B u x y z $.  $d C u x y z $.  $d R u x y z $.
    $d S u x y z $.
    $( Intersection of a range Cartesian product with a Cartesian product.
       (Contributed by Peter Mazsa, 7-Apr-2020.) $)
    xrninxp $p |- ( ( R |X. S ) i^i ( A X. ( B X. C ) ) ) =
        `' { <. <. y , z >. , u >. |
                   ( ( y e. B /\ z e. C ) /\
                     ( u e. A /\ u ( R |X. S ) <. y , z >. ) ) } $=
      ( vx cxrn cxp cin cv wcel wbr wa copab ccnv cop coprab w3a df-3an 3anan12
      inxp2 bitr3i opabbii eqtri cnvopab breq2 anbi2d dfoprab4 cnveqi 3eqtr2i
      wceq ) GHJZDEFKZKLZIMZUPNZCMZDNZUTURUOOZPZPZCIQZVDICQZRAMZENBMZFNPVAUTVGV
      HSZUOOZPZPABCTZRUQVAUSPVBPZCIQVECIDUPUOUDVMVDCIVMVAUSVBUAVDVAUSVBUBVAUSVB
      UCUEUFUGVDICUHVFVLVCVKABCIEFURVIUNVBVJVAURVIUTUOUIUJUKULUM $.
  $}

  ${
    $d A u x $.  $d B u x $.  $d C u x $.  $d R u x $.  $d S u x $.
    $( Intersection of a range Cartesian product with a Cartesian product.
       (Contributed by Peter Mazsa, 8-Apr-2020.) $)
    xrninxp2 $p |- ( ( R |X. S ) i^i ( A X. ( B X. C ) ) ) =
        { <. u , x >. |
             ( x e. ( B X. C ) /\ ( u e. A /\ u ( R |X. S ) x ) ) } $=
      ( cxrn cxp cin cv wcel wa wbr copab inxp2 an21 opabbii eqtri ) FGHZCDEIZI
      JBKZCLZAKZUALZMUBUDTNZMZBAOUEUCUFMMZBAOBACUATPUGUHBAUCUEUFQRS $.
  $}

  $( Sufficient condition for the intersection of a range Cartesian product
     with a Cartesian product to be a set.  (Contributed by Peter Mazsa,
     12-Apr-2020.) $)
  xrninxpex $p |- ( ( A e. V /\ B e. W /\ C e. X ) ->
                    ( ( R |X. S ) i^i ( A X. ( B X. C ) ) ) e. _V ) $=
    ( wcel cxrn cxp cin cvv wa xpexg inxpex olcs sylan2 3impb ) AFIZBGIZCHIZDEJ
    ZABCKZKLMIZUAUBNTUDMIZUEBCGHOUCMITUFNUEAUDUCFMMPQRS $.

  ${
    $d A u x y z $.  $d B u x y z $.  $d C u x y z $.  $d R u x y z $.
    $d S u x y z $.
    $( Two ways to express the intersection of a range Cartesian product with a
       Cartesian product.  (Contributed by Peter Mazsa, 10-Apr-2020.) $)
    inxpxrn $p |- ( ( R i^i ( A X. B ) ) |X. ( S i^i ( A X. C ) ) ) =
                  ( ( R |X. S ) i^i ( A X. ( B X. C ) ) ) $=
      ( vu vx vy vz cxp cin cxrn cv wcel wbr wa w3a wex anbi2i 3bitri xrnrel wb
      relinxp cop wceq cvv brxrn2 elv xrninxp2 brabidgaw 3anass brinxp2 anbi12i
      2exbii anan bitri anass eqelb opelxp bitr2i anbi1i 3bitr2i bitr4i 19.42vv
      ancom an12 3bitr4ri eqbrriv ) FGDABJKZEACJKZLZDELZABCJZJKZVIVJUAAVMVLUCGM
      ZVMNZFMZANZVQVOVLOZPZPZVPVRVOHMZIMZUDZUEZVQWBDOZVQWCEOZQZIRHRZPZPZVQVOVNO
      VQVOVKOZVTWJVPVSWIVRVSWIUBFHIVQVODEUFUGUHSSWAFGVNGFABCDEUIUJWLWEVQWBVIOZV
      QWCVJOZQZIRHRZWEWMWNPZPZIRHRZWKWLWPUBFHIVQVOVIVJUFUGUHWOWRHIWEWMWNUKUNWSV
      PVRWHPZPZIRHRVPWTIRHRZPWKWRXAHIWRVPWEVRWFWGPZPZPZPZXAWRWEVPPZXDPZVPWEPZXD
      PXFWRWEWBBNZWCCNZPZXDPZPWEXLPZXDPXHWQXMWEWQVRXJPWFPZVRXKPWGPZPXMWMXOWNXPA
      BVQWBDULACVQWCEULUMVRXJWFXKWGUOUPSWEXLXDUQXNXGXDXGWEWDVMNZPXNVOWDVMURXQXL
      WEWBWCBCUSSUTVAVBXGXIXDWEVPVEVAVPWEXDUQTXEWTVPXEVRWEXCPZPWTWEVRXCVFWHXRVR
      WEWFWGUKSVCSUPUNVPWTHIVDXBWJVPVRWHHIVDSTTVGVH $.
  $}

  ${
    $d A y z $.  $d B y z $.  $d R y z $.  $d S y z $.  $d V y z $.
    $( The converse of a binary relation over a range Cartesian product.
       (Contributed by Peter Mazsa, 11-Jul-2021.) $)
    br1cnvxrn2 $p |- ( B e. V -> ( A `' ( R |X. S ) B <->
                       E. y E. z ( A = <. y , z >. /\ B R y /\ B S z ) ) ) $=
      ( cxrn ccnv wbr wcel cv cop wceq w3a wex xrnrel relbrcnv brxrn2 bitrid )
      CDEFHZIJDCUAJDGKCALZBLZMNDUBEJDUCFJOBPAPCDUAEFQRABDCEFGST $.
  $}

  ${
    $d A y z $.  $d B y z $.  $d R y z $.  $d S y z $.  $d V y z $.
    $( Elementhood in the converse range Cartesian product coset of ` A ` .
       (Contributed by Peter Mazsa, 11-Jul-2021.) $)
    elec1cnvxrn2 $p |- ( B e. V -> ( B e. [ A ] `' ( R |X. S ) <->
                         E. y E. z ( A = <. y , z >. /\ B R y /\ B S z ) ) ) $=
      ( cxrn ccnv cec wcel wbr cv cop wceq w3a wex wrel wb relcnv relelec ax-mp
      br1cnvxrn2 bitrid ) DCEFHZIZJKZCDUFLZDGKCAMZBMZNODUIELDUJFLPBQAQUFRUGUHSU
      ETDCUFUAUBABCDEFGUCUD $.
  $}

  ${
    $d R u w x y $.  $d S u w x y $.
    $( Range of the range Cartesian product of classes.  (Contributed by Peter
       Mazsa, 1-Jun-2020.) $)
    rnxrn $p |- ran ( R |X. S ) =
                { <. x , y >. | E. u ( u R x /\ u S y ) } $=
      ( vw cv cop wceq wbr w3a wex cab wa cxrn crn copab 3anass 3exbii abbii c0
      exrot3 19.42v 2exbii 3bitri ccnv cec wne dfrn6 n0 wb cvv elec1cnvxrn2 elv
      wcel exbii bitri eqtri df-opab 3eqtr4i ) FGZAGZBGZHIZCGZVBDJZVEVCEJZKZBLA
      LZCLZFMZVDVFVGNZCLZNZBLALZFMDEOZPZVMABQVJVOFVJVDVLNZBLALCLVRCLZBLALVOVHVR
      CABVDVFVGRSVRCABUBVSVNABVDVLCUCUDUETVQVAVPUFUGZUAUHZFMVKFVPUIWAVJFWAVEVTU
      OZCLVJCVTUJWBVICWBVIUKCABVAVEDEULUMUNUPUQTURVMABFUSUT $.
  $}

  ${
    $d A u x y $.  $d R u x y $.  $d S u x y $.
    $( Range of a range Cartesian product with a restricted relation.
       (Contributed by Peter Mazsa, 5-Dec-2021.) $)
    rnxrnres $p |- ran ( R |X. ( S |` A ) ) =
                   { <. x , y >. | E. u e. A ( u R x /\ u S y ) } $=
      ( cres cxrn crn cv wbr wa wex copab wrex rnxrn wcel wb cvv bitr4i opabbii
      brres elv anbi2i an12 exbii df-rex eqtri ) EFDGZHICJZAJEKZUJBJZUIKZLZCMZA
      BNUKUJULFKZLZCDOZABNABCEUIPUOURABUOUJDQZUQLZCMURUNUTCUNUKUSUPLZLUTUMVAUKU
      MVARBDUJULFSUBUCUDUSUKUPUETUFUQCDUGTUAUH $.
  $}

  ${
    $d A u x y $.  $d R u x y $.
    $( Range of a range Cartesian product with a restriction of the converse
       epsilon relation.  (Contributed by Peter Mazsa, 6-Dec-2021.) $)
    rnxrncnvepres $p |- ran ( R |X. ( `' _E |` A ) ) =
                        { <. x , y >. | E. u e. A ( y e. u /\ u R x ) } $=
      ( cep ccnv cres cxrn crn cv wbr wa wrex copab wcel rnxrnres cvv brcnvep
      wb elv anbi1ci rexbii opabbii eqtri ) EFGZDHIJCKZAKELZUGBKZUFLZMZCDNZABOU
      IUGPZUHMZCDNZABOABCDEUFQULUOABUKUNCDUJUMUHUJUMTCUGUIRSUAUBUCUDUE $.
  $}

  ${
    $d A u x y $.  $d R u x y $.
    $( Range of a range Cartesian product with a restriction of the identity
       relation.  (Contributed by Peter Mazsa, 6-Dec-2021.) $)
    rnxrnidres $p |- ran ( R |X. ( _I |` A ) ) =
                     { <. x , y >. | E. u e. A ( u = y /\ u R x ) } $=
      ( cid cres cxrn crn cv wbr wa wrex copab wceq rnxrnres wb cvv ideqg elv
      anbi1ci rexbii opabbii eqtri ) EFDGHICJZAJEKZUEBJZFKZLZCDMZABNUEUGOZUFLZC
      DMZABNABCDEFPUJUMABUIULCDUHUKUFUHUKQBUEUGRSTUAUBUCUD $.
  $}

  $( Two ways to express restriction of range Cartesian product, see also
     ~ xrnres2 , ~ xrnres3 .  (Contributed by Peter Mazsa, 5-Jun-2021.) $)
  xrnres $p |- ( ( R |X. S ) |` A ) = ( ( R |` A ) |X. S ) $=
    ( c1st cvv cxp cres ccnv ccom c2nd cxrn ineq1i df-xrn reseq1i inres2 eqtr4i
    cin resco 3eqtr4i ) DEEFZGHZBIZAGZJTGHCIZQZUABAGZIZUDQBCKZAGZUFCKUCUGUDUABA
    RLUIUBUDQZAGUEUHUJABCMNAUBUDOPUFCMS $.

  $( Two ways to express restriction of range Cartesian product, see also
     ~ xrnres , ~ xrnres3 .  (Contributed by Peter Mazsa, 6-Sep-2021.) $)
  xrnres2 $p |- ( ( R |X. S ) |` A ) = ( R |X. ( S |` A ) ) $=
    ( c1st cvv cxp cres ccnv ccom c2nd resco ineq2i df-xrn reseq1i inres eqtr4i
    cin cxrn 3eqtr4i ) DEEFZGHBIZJTGHZCIZAGZQZUAUBCAGZIZQBCRZAGZBUFRUDUGUAUBCAK
    LUIUAUCQZAGUEUHUJABCMNUAUCAOPBUFMS $.

  $( Two ways to express restriction of range Cartesian product, see also
     ~ xrnres , ~ xrnres2 .  (Contributed by Peter Mazsa, 28-Mar-2020.) $)
  xrnres3 $p |- ( ( R |X. S ) |` A ) = ( ( R |` A ) |X. ( S |` A ) ) $=
    ( c1st cvv cxp cres ccnv ccom c2nd cin cxrn ineq12i df-xrn reseq1i resindir
    resco eqtri 3eqtr4i ) DEEFZGHZBIZAGZJTGHZCIZAGZKZUABAGZIZUDCAGZIZKBCLZAGZUH
    UJLUCUIUFUKUABAQUDCAQMUMUBUEKZAGUGULUNABCNOUBUEAPRUHUJNS $.

  $( Two ways to express restriction of range Cartesian product.  (Contributed
     by Peter Mazsa, 29-Dec-2020.) $)
  xrnres4 $p |- ( ( R |X. S ) |` A ) =
      ( ( R |X. S ) i^i ( A X. ( ran ( R |` A ) X. ran ( S |` A ) ) ) ) $=
    ( cxrn cres crn cxp cin xrnres3 dfres4 xrneq12i inxpxrn 3eqtri ) BCDZAEBAEZ
    CAEZDBAOFZGHZCAPFZGHZDNAQSGGHABCIORPTABJACJKAQSBCLM $.

  $( Sufficient condition for a restricted range Cartesian product to be a set.
     (Contributed by Peter Mazsa, 16-Dec-2020.)  (Revised by Peter Mazsa,
     7-Sep-2021.) $)
  xrnresex $p |- ( ( A e. V /\ R e. W /\ ( S |` A ) e. X ) ->
                   ( R |X. ( S |` A ) ) e. _V ) $=
    ( wcel cres w3a cxrn cvv xrnres3 xrnres2 eqtr3i crn cxp cin dfres4 eqeltrid
    rnexg xrneq12i simp1 resexg syl 3ad2ant2 3ad2ant3 inxpxrn xrninxpex syl3anc
    eqeltrrid ) ADGZBEGZCAHZFGZIZBUMJZBAHZUMJZKBCJZAHURUPABCLABCMNUOURBAUQOZPQZ
    CAUMOZPQZJZKUQVAUMVCABRACRUAUOUKUTKGZVBKGZVDKGUKULUNUBULUKVEUNULUQKGVEBAEUC
    UQKTUDUEUNUKVFULUMFTUFUKVEVFIVDUSAUTVBPPQKAUTVBBCUGAUTVBBCDKKUHSUISUJ $.

  $( Sufficient condition for a range Cartesian product with restricted
     identity to be a set.  (Contributed by Peter Mazsa, 31-Dec-2021.) $)
  xrnidresex $p |- ( ( A e. V /\ R e. W ) ->
                     ( R |X. ( _I |` A ) ) e. _V ) $=
    ( wcel cid cres cvv cxrn resiexg adantr xrnresex mpd3an3 ) ACEZBDEZFAGZHEZB
    PIHENQOACJKABFCDHLM $.

  $( Sufficient condition for a range Cartesian product with restricted
     converse epsilon to be a set.  (Contributed by Peter Mazsa, 16-Dec-2020.)
     (Revised by Peter Mazsa, 23-Sep-2021.) $)
  xrncnvepresex $p |- ( ( A e. V /\ R e. W ) ->
                        ( R |X. ( `' _E |` A ) ) e. _V ) $=
    ( wcel cep ccnv cres cvv cxrn cnvepresex adantr xrnresex mpd3an3 ) ACEZBDEZ
    FGZAHZIEZBRJIEOSPACKLABQCDIMN $.

  $( Domain of the range product with restricted converse epsilon relation.
     (Contributed by Peter Mazsa, 23-Nov-2025.) $)
  dmxrncnvepres $p |- dom ( R |X. ( `' _E |` A ) ) =
                      ( dom ( R |` A ) \ { (/) } ) $=
    ( cres cep ccnv cxrn cdm c0 csn cdif xrnres xrnres2 eqtr3i dmeqi dmxrncnvep
    ) BACZDEZFZGBQACFZGPGHIJRSBQFACRSABQKABQLMNPOM $.

  $( Domain of the range product with restricted converse epsilon relation.
     (Contributed by Peter Mazsa, 29-Jan-2026.) $)
  dmxrncnvepres2 $p |- dom ( R |X. ( `' _E |` A ) ) =
                       ( A i^i ( dom R \ { (/) } ) ) $=
    ( cres cdm c0 csn cdif cin cep ccnv cxrn dmres difeq1i dmxrncnvepres indif2
    3eqtr4i ) BACDZEFZGABDZHZRGBIJACKDASRGHQTRBALMABNASROP $.

  $( Element of the domain of the range product with restricted converse
     epsilon relation.  (Contributed by Peter Mazsa, 23-Nov-2025.) $)
  eldmxrncnvepres $p |- ( B e. V ->
      ( B e. dom ( R |X. ( `' _E |` A ) ) <->
        ( B e. A /\ B =/= (/) /\ [ B ] R =/= (/) ) ) ) $=
    ( wcel cres cdm wne cec cep ccnv cxrn w3a eldmres3 anbi1d csn dmxrncnvepres
    c0 wa cdif eleq2i eldifsn bitri 3anan32 3bitr4g ) BDEZBCAFGZEZBRHZSZBAEZBCI
    RHZSZUISBCJKAFLGZEZUKUIULMUFUHUMUIABCDNOUOBUGRPTZEUJUNUPBACQUABUGRUBUCUKUIU
    LUDUE $.

  ${
    $d A y $.  $d B x $.  $d B y $.  $d R y $.
    $( Element of the domain of the range product with restricted converse
       epsilon relation.  This identifies the domain of the ~ pet span
       ` ( R |X. ( ``' _E |`` A ) ) ` : a ` B ` belongs to the domain of the
       span exactly when ` B ` is in ` A ` and has at least one ` x e. B ` and
       ` y ` with ` B R y ` .  (Contributed by Peter Mazsa, 23-Nov-2025.) $)
    eldmxrncnvepres2 $p |- ( B e. V ->
      ( B e. dom ( R |X. ( `' _E |` A ) ) <->
        ( B e. A /\ E. x x e. B /\ E. y B R y ) ) ) $=
      ( wcel cres cdm c0 wne wa cv wbr wex cep ccnv cxrn w3a eldmres wb anbi12d
      n0 a1i csn cdif dmxrncnvepres eleq2i eldifsn bitri 3anan32 3bitr4g ) DFGZ
      DECHIZGZDJKZLZDCGZDBMENBOZLZAMDGAOZLDEPQCHRIZGZURVAUSSUMUOUTUPVABCDEFTUPV
      AUAUMADUCUDUBVCDUNJUEUFZGUQVBVDDCEUGUHDUNJUIUJURVAUSUKUL $.
  $}

  $( An ` ( R |X. ( ``' _E |`` A ) ) ` -coset in its domain quotient.
     (Contributed by Peter Mazsa, 23-Nov-2025.) $)
  eceldmqsxrncnvepres $p |- ( ( A e. V /\ B e. W /\ R e. X ) ->
       ( [ B ] ( R |X. ( `' _E |` A ) ) e.
         ( dom ( R |X. ( `' _E |` A ) ) /. ( R |X. ( `' _E |` A ) ) ) <->
       ( B e. A /\ B =/= (/) /\ [ B ] R =/= (/) ) ) ) $=
    ( wcel w3a cep ccnv cres cxrn cec cdm cqs c0 wne wb wa cvv eceldmqs 3adant2
    xrncnvepresex syl eldmxrncnvepres 3ad2ant2 bitrd ) ADGZBEGZCFGZHBCIJAKLZMUK
    NZUKOGZBULGZBAGBPQBCMPQHZUHUJUMUNRZUIUHUJSUKTGUPACDFUCBUKTUAUDUBUIUHUNUORUJ
    ABCEUEUFUG $.

  ${
    $d A y $.  $d B x $.  $d B y $.  $d R y $.
    $( An ` ( R |X. ( ``' _E |`` A ) ) ` -coset in its domain quotient.  In the
       ~ pet span ` ( R |X. ( ``' _E |`` A ) ) ` , a block [ B ] lies in the
       domain quotient exactly when its representative ` B ` belongs to ` A `
       and actually fires at least one arrow (has some ` x e. B ` and some
       ` y ` with ` B R y ` ).  (Contributed by Peter Mazsa, 23-Nov-2025.) $)
    eceldmqsxrncnvepres2 $p |- ( ( A e. V /\ B e. W /\ R e. X ) ->
       ( [ B ] ( R |X. ( `' _E |` A ) ) e.
        ( dom ( R |X. ( `' _E |` A ) ) /. ( R |X. ( `' _E |` A ) ) ) <->
       ( B e. A /\ E. x x e. B /\ E. y B R y ) ) ) $=
      ( wcel w3a cep ccnv cres cxrn cec cdm cv wex wb cvv cqs wbr xrncnvepresex
      wa eceldmqs syl 3adant2 eldmxrncnvepres2 3ad2ant2 bitrd ) CFIZDGIZEHIZJDE
      KLCMNZOUNPZUNUAIZDUOIZDCIAQDIARDBQEUBBRJZUKUMUPUQSZULUKUMUDUNTIUSCEFHUCDU
      NTUEUFUGULUKUQURSUMABCDEGUHUIUJ $.
  $}

  $( Binary relation on an intersection is a special case of binary relation on
     range Cartesian product.  (Contributed by Peter Mazsa, 21-Aug-2021.) $)
  brin2 $p |- ( ( A e. V /\ B e. W ) ->
                ( A ( R i^i S ) B <-> A ( R |X. S ) <. B , B >. ) ) $=
    ( wcel wa cin wbr cop cxrn brin wb brxrn 3anidm23 bitr4id ) AEGZBFGZHABCDIJ
    ABCJABDJHZABBKCDLJZABCDMRSUATNABBCDEFFOPQ $.

  $( Binary relation on an intersection is a special case of binary relation on
     range Cartesian product.  (Contributed by Peter Mazsa, 21-Aug-2021.)
     (Avoid depending on this detail.) $)
  brin3 $p |- ( ( A e. V /\ B e. W ) ->
                ( A ( R i^i S ) B <-> A ( R |X. S ) { { B } } ) ) $=
    ( wcel wa cin wbr cop cxrn csn brin2 wceq opidg adantl breq2d bitrd ) AEGZB
    FGZHZABCDIJABBKZCDLZJABMMZUDJABCDEFNUBUCUEAUDUAUCUEOTBFPQRS $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Relations
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define the relations class.  Proper class relations (like ` _I ` , see
     ~ reli ) are not elements of it.  The element of this class and the
     relation predicate are the same when ` R ` is a set (see ~ elrelsrel ).

     The class of relations is a great tool we can use when we define classes
     of different relations as nullary class constants as required by the 2.
     point in our Guidelines ~ https://us.metamath.org/mpeuni/mathbox.html .
     When we want to define a specific class of relations as a nullary class
     constant, the appropriate method is the following:

     1.  We define the specific nullary class constant for general sets (see
     e.g. ~ df-refs ), then

     2. we get the required class of relations by the intersection of the class
     of general sets above with the class of relations ~ df-rels (see
     ~ df-refrels and the resulting ~ dfrefrels2 and ~ dfrefrels3 ).

     3.  Finally, in order to be able to work with proper classes (like
     ~ iprc ) as well, we define the predicate of the relation (see
     ~ df-refrel ) so that it is true for the relevant proper classes (see
     ~ refrelid ), and that the element of the class of the required relations
     (e.g. ~ elrefrels3 ) and this predicate are the same in case of sets (see
     ~ elrefrelsrel ).  (Contributed by Peter Mazsa, 13-Jun-2018.) $)
  df-rels $a |- Rels = ~P ( _V X. _V ) $.

  $( The element of the relations class ( ~ df-rels ) and the relation
     predicate ( ~ df-rel ) are the same when ` R ` is a set.  (Contributed by
     Peter Mazsa, 14-Jun-2018.) $)
  elrels2 $p |- ( R e. V -> ( R e. Rels <-> R C_ ( _V X. _V ) ) ) $=
    ( crels wcel cvv cxp cpw wss df-rels eleq2i elpwg bitrid ) ACDAEEFZGZDABDAM
    HCNAIJAMBKL $.

  $( The element of the relations class ( ~ df-rels ) and the relation
     predicate are the same when ` R ` is a set.  (Contributed by Peter Mazsa,
     24-Nov-2018.) $)
  elrelsrel $p |- ( R e. V -> ( R e. Rels <-> Rel R ) ) $=
    ( wcel crels cvv cxp wss wrel elrels2 df-rel bitr4di ) ABCADCAEEFGAHABIAJK
    $.

  $( The element of the relations class is a relation.  (Contributed by Peter
     Mazsa, 20-Jul-2019.) $)
  elrelsrelim $p |- ( R e. Rels -> Rel R ) $=
    ( crels wcel wrel elrelsrel ibi ) ABCADABEF $.

  $( Equivalent expressions for an element of the relations class.
     (Contributed by Peter Mazsa, 21-Jul-2021.) $)
  elrels5 $p |- ( R e. V -> ( R e. Rels <-> ( R |` dom R ) = R ) ) $=
    ( wcel crels wrel cdm cres wceq elrelsrel dfrel5 bitrdi ) ABCADCAEAAFGAHABI
    AJK $.

  $( Equivalent expressions for an element of the relations class.
     (Contributed by Peter Mazsa, 21-Jul-2021.) $)
  elrels6 $p |- ( R e. V ->
                  ( R e. Rels <-> ( R i^i ( dom R X. ran R ) ) = R ) ) $=
    ( wcel crels wrel cdm crn cxp cin wceq elrelsrel dfrel6 bitrdi ) ABCADCAEAA
    FAGHIAJABKALM $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Quotient map (coset map)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d R x $.
    $( Define the quotient map (coset map), see also ~ dfqmap2 and ~ dfqmap3 .
       ` QMap R ` is the "send a generator / domain element to its ` R `
       -coset" map: it maps each ` x e. dom R ` to the block ` [ x ] R ` .
       Makes the quotient operation ` /. ` structurally explicit as the range
       of a canonical map (see ~ dfqs2 , ~ rnqmap ).  This is crucial for

       (i) modular "two-layer" characterizations (map layer + carrier layer)
       such as ~ dfdisjs6 / ~ dfdisjs7 ,

       (ii) transport of properties between a relation and its induced
       quotient-carrier (e.g.  "elements are blocks" via ~ rnqmap ), and

       (iii) expressing stability/invariance constraints as ordinary conditions
       on a graph (e.g. ` ran QMap r e. ElDisjs ` , ` QMap r e. Disjs ` ).
       (Contributed by Peter Mazsa, 12-Feb-2026.) $)
    df-qmap $a |- QMap R = ( x e. dom R |-> [ x ] R ) $.
  $}

  ${
    $d R x $.
    $( Alternate definition of the quotient map: ` QMap ` in image-of-singleton
       form.  (Contributed by Peter Mazsa, 14-Feb-2026.) $)
    dfqmap2 $p |- QMap R = ( x e. dom R |-> ( R " { x } ) ) $=
      ( cqmap cdm cv cec cmpt csn cima df-qmap df-ec mpteq2i eqtri ) BCABDZAEZB
      FZGANBOHIZGABJANPQOBKLM $.
  $}

  ${
    $d R x y $.
    $( Alternate definition of the quotient map: ` QMap ` as ordered-pair class
       abstraction.  Gives the raw set-builder characterization for extensional
       proofs, ` Rel ` proofs ( ~ relqmap ), and composition/intersection
       manipulations.  (Contributed by Peter Mazsa, 14-Feb-2026.) $)
    dfqmap3 $p |- QMap R = { <. x , y >. | ( x e. dom R /\ y = [ x ] R ) } $=
      ( cqmap cdm cv cec cmpt wcel wceq wa copab df-qmap df-mpt eqtri ) CDACEZA
      FZCGZHQPIBFRJKABLACMABPRNO $.
  $}

  ${
    $d A x y z $.  $d R x y z $.
    $( ` QMap ` fibers are singletons of blocks.  Makes ` QMap ` behave like a
       "block constructor function" on ` dom R ` .  (Contributed by Peter
       Mazsa, 14-Feb-2026.) $)
    ecqmap $p |- ( A e. dom R -> [ A ] QMap R = { [ A ] R } ) $=
      ( vy vx vz cdm wcel cqmap cec cv wbr cab csn wceq cin wa wb eqtr4di eqtrd
      cvv dfec2 eleq1 adantr eqeqan2d ancoms anbi12d dfqmap3 brabga elvd abbidv
      eceq1 inab wal ax-5 abv sylibr ineq1d inv1 ineqcomi eqtrdi df-sn ) ABFZGZ
      ABHZIACJZVDKZCLZABIZMZCAVDVBUAVCVGVEVHNZCLZVIVCVGVCCLZVKOZVKVCVGVCVJPZCLV
      MVCVFVNCVCVFVNQCDJZVBGZEJZVOBIZNZPVNDEAVEVDVBTVOANZVQVENZPVPVCVSVJVTVPVCQ
      WAVOAVBUBUCWAVTVSVJQVTVQVEVRVHVOABUKUDUEUFDEBUGUHUIUJVCVJCULRVCVMTVKOVKVC
      VLTVKVCVCCUMVLTNVCCUNVCCUOUPUQVKTVKVKURUSUTSCVHVARS $.
  $}

  $( Fiber of ` QMap ` equals singleton quotient: a conceptual bridge between
     "map fibers" and quotients.  (Contributed by Peter Mazsa, 19-Feb-2026.) $)
  ecqmap2 $p |- ( A e. dom R -> [ A ] QMap R = ( { A } /. R ) ) $=
    ( cdm wcel cqmap cec csn cqs ecqmap snecg eqtrd ) ABCZDABEFABFGAGBHABIABLJK
    $.

  ${
    $d R x $.
    $( Quotient map exists if ` R ` exists.  Type-safety: ensures ` QMap ` is a
       set under the standard "relation sethood" hypothesis.  (Contributed by
       Peter Mazsa, 12-Feb-2026.) $)
    qmapex $p |- ( R e. V -> QMap R e. _V ) $=
      ( vx wcel cqmap cdm cv cec cmpt cvv df-qmap dmexg mptexd eqeltrid ) ABDZA
      ECAFZCGAHZIJCAKOCPQJABLMN $.
  $}

  ${
    $d R x $.
    $( Quotient map is a relation.  Guarantees that ` QMap ` can be composed,
       restricted, and used in other relation infrastructure (e.g., membership
       in ` Disjs ` , ` Rels ` -based typing).  (Contributed by Peter Mazsa,
       12-Feb-2026.) $)
    relqmap $p |- Rel QMap R $=
      ( vx cqmap wrel cdm cv cec cmpt mptrel df-qmap releqi mpbir ) ACZDBAEZBFA
      GZHZDBNOIMPBAJKL $.
  $}

  ${
    $d R x $.  $d V x $.
    $( ` QMap ` preserves the domain.  Confirms that ` QMap ` is defined
       exactly on the points where cosets ` [ x ] R ` make sense (those in
       ` dom R ` ).  (Contributed by Peter Mazsa, 14-Feb-2026.) $)
    dmqmap $p |- ( R e. V -> dom QMap R = dom R ) $=
      ( vx wcel cqmap cdm cv cec cvv df-qmap ecexg adantr dmmptd ) ABDZCAEAFZCG
      ZAHZICAJNQIDPODPBAKLM $.
  $}

  ${
    $d R x $.
    $( The range of the quotient map is the quotient carrier.  It lets us
       replace quotient-carrier reasoning by map/range reasoning (and
       conversely) via ~ df-qmap and ~ dfqs2 .  (Contributed by Peter Mazsa,
       12-Feb-2026.) $)
    rnqmap $p |- ran QMap R = ( dom R /. R ) $=
      ( vx cqmap crn cdm cv cec cmpt cqs df-qmap rneqi dfqs2 eqtr4i ) ACZDBAEZB
      FAGHZDOAINPBAJKBOALM $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Lifts, shifts, successor, and predecessor
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define the adjoined lift map.  Given a relation ` R ` and a carrier/set
     ` A ` , we form the adjoined relation ` ( R u. ``' _E ) ` (i.e., "follow
     ` R ` or follow elements"), restricted to ` A ` , and map each domain
     element ` m ` to its coset ` [ m ] ` under that restricted adjoined
     relation, see its expanded version ~ dfadjliftmap .  Thus, for ` m ` in
     its domain, we have ` ( m u. [ m ] R ) ` , see ~ dfadjliftmap2 .

     Its key special case is successor: for ` R = _I ` and ` A = dom _I ` , or
     ` A = _V ` , the adjoined relation is ` ( _I u. ``' _E ) ` , and the coset
     becomes ` [ m ] ( _I u. ``' _E ) = ( m u. { m } ) ` .  So
     ` ( _I AdjLiftMap dom _I ) ` or ` ( _I AdjLiftMap _V ) ` (see ~ dfsucmap2
     and ~ dfsucmap3 ) are exactly the successor map ` m |-> suc m ` (cf.
     ~ dfsucmap4 ), which is a prerequisite for accepting the adjoining lift as
     the right generalization of successor.

     A maximally generic form would be "( R F LiftMap A )" defined as
     ` ( m e. dom ( ( R F ``' _E ) |`` A ) |-> `
     ` [ m ] ( ( R F ``' _E ) |`` A ) ) ` where ` F ` is an object-level binary
     operator on relations (used via ~ df-ov ).  However, ` u. ` and ` |X. `
     are introduced in set.mm as class constructors (e.g. ~ df-un ), not as an
     object-level binary function symbol ` F ` that can be passed as a
     parameter.  To make the generic ` F ` -pattern literally usable, we would
     need to reify union and ` |X. ` as function-objects, which is additional
     infrastructure.  To avoid introducing operator-as-function objects solely
     to support ` F ` , we define:

     ` AdjLiftMap ` directly using ~ df-un , and

     ` BlockLiftMap ` directly using the existing ` |X. ` constructor
     ~ dfxrn2 ,

     so we treat any "generic ` F ` -LiftMap" as optional future
     generalization, not a dependency.

     We prefer to avoid defining too many concepts.  For this reason, we will
     not introduce

     a named "adjoining relation",

     a named carrier "adjoining lift" "( R AdjLift A )", in place of
     ` ran ( R AdjLiftMap A ) ` , which is
     ` ( dom ( ( R u. ``' _E ) |`` A ) /. ( ( R u. ``' _E ) |`` A ) ) ` , cf.
     ~ dfqs2 ,

     or the equilibrium condition "AdjLiftFix" , in place of
     ` { <. r , a >. | `
     ` ( dom ( ( R u. ``' _E ) |`` A ) /. ( ( R u. ``' _E ) |`` A ) ) = a } `
     (cf. its analog ~ df-blockliftfix ).  These are definable by simple
     expansions and/or domain-quotient theorems when needed.

     A "two-stage" construction is obtained by first forming the block relation
     ` ( R |X. ``' _E ) ` and then adjoining elements as "BlockAdj" .
     Combined, it uses the relation ` ( ( R |X. ``' _E ) u. ``' _E ) ` , which
     for ` m ` in its domain ` ( A \ { (/) } ) ` gives
     ` ( m u. [ m ] ( R |X. ``' _E ) ) ` , yielding "BlockAdjLiftMap" (cf.
     ~ blockadjliftmap ) and "BlockAdjLiftFix".  We only introduce these if a
     downstream theorem actually requires them.  (Contributed by Peter Mazsa,
     24-Jan-2026.)  (Revised by Peter Mazsa, 22-Feb-2026.) $)
  df-adjliftmap $a |- ( R AdjLiftMap A ) = QMap ( ( R u. `' _E ) |` A ) $.

  ${
    $d A m $.  $d R m $.
    $( Alternate (expanded) definition of the adjoined lift map.  (Contributed
       by Peter Mazsa, 28-Jan-2026.)  (Revised by Peter Mazsa, 22-Feb-2026.) $)
    dfadjliftmap $p |- ( R AdjLiftMap A ) =
     ( m e. dom ( ( R u. `' _E ) |` A ) |-> [ m ] ( ( R u. `' _E ) |` A ) ) $=
      ( cadjliftmap cep ccnv cun cres cqmap cdm cv cec cmpt df-adjliftmap eqtri
      df-qmap ) ABDBEFGAHZICQJCKQLMABNCQPO $.
  $}

  ${
    $d A m $.  $d R m $.
    $( Alternate definition of the adjoined lift map.  (Contributed by Peter
       Mazsa, 28-Jan-2026.) $)
    dfadjliftmap2 $p |- ( R AdjLiftMap A ) =
      ( m e. ( A i^i ( dom R u. ( _V \ { (/) } ) ) ) |->
        ( m u. [ m ] R ) ) $=
      ( cadjliftmap cep ccnv cun cres cdm cv cec cmpt cvv csn cdif dfadjliftmap
      c0 cin wcel wceq elinel1 dmuncnvepres eleq2s ecuncnvepres mpteq2ia 3eqtri
      syl mpteq1i ) ABDCBEFGAHZIZCJZUIKZLCUJUKUKBKGZLCABIMQNOGZRZUMLABCPCUJULUM
      UKUJSUKASZULUMTUPUKUOUJUKAUNUAABUBZUCAUKBUDUGUECUJUOUMUQUHUF $.
  $}

  ${
    $d A m n $.  $d R m n $.
    $( A "two-stage" construction is obtained by first forming the block
       relation ` ( R |X. ``' _E ) ` and then adjoining elements as "BlockAdj".
       Combined, it uses the relation ` ( ( R |X. ``' _E ) u. ``' _E ) ` .
       (Contributed by Peter Mazsa, 28-Jan-2026.) $)
    blockadjliftmap $p |- ( ( R |X. `' _E ) AdjLiftMap A ) =
        { <. m , n >. | ( m e. ( A \ { (/) } ) /\
                          n = ( m u. ( [ m ] R X. m ) ) ) } $=
      ( cep ccnv cxrn cadjliftmap cun cres cdm cv cec cmpt wcel wa copab c0 csn
      wceq cdif cxp dfadjliftmap df-mpt dmxrnuncnvepres eleq2i ecuncnvepres syl
      anbi1i eldifi cvv ecxrncnvep2 uneq2i eqtrdi eqeq2d pm5.32i opabbii 3eqtri
      elv bitri ) ABEFZGZHCVBVAIAJZKZCLZVCMZNVEVDOZDLZVFTZPZCDQVEARSZUAZOZVHVEV
      EBMVEUBZIZTZPZCDQAVBCUCCDVDVFUDVJVQCDVJVMVIPVQVGVMVIVDVLVEABUEUFUIVMVIVPV
      MVFVOVHVMVFVEVEVBMZIZVOVMVEAOVFVSTVEAVKUJAVEVBUGUHVRVNVEVRVNTCVEBUKULUSUM
      UNUOUPUTUQUR $.
  $}

  $( Define the block lift map.  Given a relation ` R ` and a carrier/set
     ` A ` , we form the block relation ` ( R |X. ``' _E ) ` (i.e., "follow
     both ` R ` and element"), restricted to ` A ` (or, equivalently, "follow
     both ` R ` and elements-of-A", cf. ~ xrnres2 ).  Then map each domain
     element ` m ` to its coset ` [ m ] ` under that restricted block relation.

     For ` m ` in the domain, which requires
     ` ( m e. A /\ m =/= (/) /\ [ m ] R =/= (/) ) ` (cf. ~ eldmxrncnvepres ),
     the fiber has the product form
     ` [ m ] ( R |X. ``' _E ) = ( [ m ] R X. m ) ` , so the block relation
     lifts a block ` m ` to the rectangular grid "external labels ` X. `
     internal members", see ~ dfblockliftmap2 .  Contrast: while the adjoined
     lift, via ` ( R u. ``' _E ) ` , attaches neighbors and members in a single
     relation (see ~ dfadjliftmap2 ), the block lift labels each internal
     member by each external neighbor.

     For the general case and a two-stage construction (first block lift, then
     adjoin membership), see the comments to ~ df-adjliftmap .  For the
     equilibrium condition, see ~ df-blockliftfix .  (Contributed by Peter
     Mazsa, 24-Jan-2026.)  (Revised by Peter Mazsa, 22-Feb-2026.) $)
  df-blockliftmap $a |- ( R BlockLiftMap A ) =
                          QMap ( R |X. ( `' _E |` A ) ) $.

  ${
    $d A m $.  $d R m $.
    $( Alternate definition of the block lift map.  (Contributed by Peter
       Mazsa, 29-Jan-2026.)  (Revised by Peter Mazsa, 22-Feb-2026.) $)
    dfblockliftmap $p |- ( R BlockLiftMap A ) =
    ( m e. dom ( R |X. ( `' _E |` A ) ) |-> [ m ] ( R |X. ( `' _E |` A ) ) ) $=
      ( cblockliftmap cep ccnv cres cxrn cqmap cdm cmpt df-blockliftmap df-qmap
      cv cec eqtri ) ABDBEFAGHZICQJCNQOKABLCQMP $.
  $}

  ${
    $d A m $.  $d R m $.
    $( Alternate definition of the block lift map.  (Contributed by Peter
       Mazsa, 29-Jan-2026.) $)
    dfblockliftmap2 $p |- ( R BlockLiftMap A ) =
       ( m e. ( A i^i ( dom R \ { (/) } ) ) |-> ( [ m ] R X. m ) ) $=
      ( cblockliftmap cep ccnv cres cxrn cdm cv cec cmpt cxp csn dfblockliftmap
      c0 cdif cin wcel wceq elinel1 dmxrncnvepres2 eleq2s elecreseq ecxrncnvep2
      xrnres2 eceq2i eqtr3id eqtrd syl mpteq2ia mpteq1i 3eqtri ) ABDCBEFZAGHZIZ
      CJZUOKZLCUPUQBKUQMZLCABIPNQZRZUSLABCOCUPURUSUQUPSUQASZURUSTVBUQVAUPUQAUTU
      AABUBZUCVBURUQBUNHZKZUSVBURUQVDAGZKVEVFUOUQABUNUFUGAUQVDUDUHUQBAUEUIUJUKC
      UPVAUSVCULUM $.
  $}

  ${
    $d m n $.
    $( Define the successor map, directly as the graph of the successor
       operation, using only elementary set theory (ordered-pair class
       abstraction).  This avoids committing to any particular construction of
       the successor function/class from other operators (e.g. a
       union/composition presentation), while remaining provably equivalent to
       those presentations (cf. ~ dfsucmap2 and ~ dfsucmap3 vs. ~ df-succf and
       ~ dfsuccf2 ).  For maximum mappy shape, see ~ dfsucmap4 .

       We also treat the successor relation as the default shift relation for
       grading/tower arguments (cf. ~ df-shiftstable ).  Because it is used
       pervasively in shift-lift infrastructure, we adopt the short name SucMap
       rather than the fully systematic "SucAdjLiftMap".

       You may also define the predecessor relation as the converse graph
       "PreMap" as ` ``' SucMap ` , which reverses successor edges ( cf.
       ~ cnvopab ) and sends each successor to its (unique) predecessor when it
       exists.  (Contributed by Peter Mazsa, 25-Jan-2026.) $)
    df-sucmap $a |- SucMap = { <. m , n >. | suc m = n } $.
  $}

  ${
    $d B n $.  $d m n $.  $d R n $.
    $( Alternate definition of the successor map.  (Contributed by Peter Mazsa,
       28-Jan-2026.) $)
    dfsucmap3 $p |- SucMap = ( _I AdjLiftMap _V ) $=
      ( vn vm cv wceq copab cvv cid cep cun cdm cec cmpt csn 3eqtri wcel wo wbr
      wb elv wrel csuc cadjliftmap csucmap eqcom opabbii ccnv cres dfadjliftmap
      dmresv c0 cdif dmun dmi dmcnvep uneq12i undifabs eqtri elecALTV el2v brun
      orcom equcom ideqg velsn 3bitr4i brcnvep orbi12i 3bitri elun eqriv relcnv
      reli relun mpbir2an dfrel3 mpbi eceq2i df-suc mpteq12i df-sucmap 3eqtr4ri
      3eqtr4i mptv ) ACZBCZUAZDZBAEZWFWDDZBAEFGUBZUCWGWIBAWDWFUDUEWJBGHUFZIZFUG
      ZJZWEWMKZLBFWFLWHFGBUHBWNWOFWFWNWLJZFWLUIWPGJZWKJZIFFUJMZUKZIFGWKULWQFWRW
      TUMUNUOFWSUPNUQWEWLKZWEWEMZIZWOWFAXAXCWDXBOZWDWEOZPZXEXDPWDXAOZWDXCOXDXEV
      AXGWEWDWLQZWEWDGQZWEWDWKQZPXFXGXHRBAWEWDWLFFURUSWEWDGWKUTXIXDXJXEWEWDDZWD
      WEDXIXDBAVBXIXKRAWEWDFVCSAWEVDVEXJXERBWEWDFVFSVGVHWDWEXBVIVEVJWMWLWEWLTZW
      MWLDXLGTWKTVLHVKGWKVMVNWLVOVPVQWEVRWBVSBAWFWCNBAVTWA $.
  $}

  $( Alternate definition of the successor map.  (Contributed by Peter Mazsa,
     28-Jan-2026.) $)
  dfsucmap2 $p |- SucMap = ( _I AdjLiftMap dom _I ) $=
    ( vm csucmap cvv cid cadjliftmap cdm dfsucmap3 cep ccnv cun cres cv cec dmi
    cmpt reseq2i dmeqi eceq2i mpteq12i dfadjliftmap 3eqtr4i eqtr4i ) BCDEZDFZDE
    ZGADHIJZUDKZFZALZUGMZOAUFCKZFZUIUKMZOUEUCAUHUJULUMUGUKUDCUFNPZQUGUKUIUNRSUD
    DATCDATUAUB $.

  ${
    $d m n $.
    $( Alternate definition of the successor map.  (Contributed by Peter Mazsa,
       28-Jan-2026.) $)
    dfsucmap4 $p |- SucMap = ( m e. _V |-> suc m ) $=
      ( vn cv csuc wceq copab cvv cmpt csucmap eqcom opabbii df-sucmap 3eqtr4ri
      mptv ) BCZACDZEZABFPOEZABFAGPHIQRABOPJKABPNABLM $.
  $}

  ${
    $d M m n $.  $d N m n $.
    $( Binary relation form of the successor map, general version.
       (Contributed by Peter Mazsa, 6-Jan-2026.) $)
    brsucmap $p |- ( ( M e. V /\ N e. W ) -> ( M SucMap N <-> suc M = N ) ) $=
      ( vm vn cv csuc wceq csucmap suceq id eqeqan12d df-sucmap brabga ) EGZHZF
      GZIAHZBIEFABJCDPAIRBIZQSRBPAKTLMEFNO $.
  $}

  ${
    $d m n $.
    $( The successor map is a relation.  (Contributed by Peter Mazsa,
       7-Jan-2026.) $)
    relsucmap $p |- Rel SucMap $=
      ( vm vn cv csuc wceq csucmap df-sucmap relopabi ) ACDBCEABFABGH $.
  $}

  ${
    $d m n $.
    $( The domain of the successor map is the universe.  (Contributed by Peter
       Mazsa, 7-Jan-2026.) $)
    dmsucmap $p |- dom SucMap = _V $=
      ( vm vn csucmap cdm cvv ssv wss cv wbr wex wral csuc wceq wcel sucexg elv
      isseti wb brsucmap mpbir el2v eqcom bitri exbii rgenw ssdmral eqssi ) CDZ
      EUHFEUHGAHZBHZCIZBJZAEKULAEULUJUILZMZBJBUMUMENAUIEOPQUKUNBUKUMUJMZUNUKUOR
      ABUIUJEESUAUMUJUBUCUDTUEABECUFTUG $.
  $}

  $( Define ` Suc ` as the class of all successors, i.e. the range of the
     successor map: ` n e. Suc ` iff ` E. m suc m = n ` (see ~ dfsuccl2 ).  By
     injectivity of ` suc ` ( ~ suc11reg ), every ` n e. Suc ` has at most one
     predecessor, which is exactly what ` pre n ` ( ~ df-pre ) names.  Cf.
     ~ dfsuccl3 and ~ dfsuccl4 .  (Contributed by Peter Mazsa, 25-Jan-2026.) $)
  df-succl $a |- Suc = ran SucMap $.

  ${
    $d m n $.
    $( Alternate definition of the class of all successors.  (Contributed by
       Peter Mazsa, 29-Jan-2026.) $)
    dfsuccl2 $p |- Suc = { n | E. m suc m = n } $=
      ( csuccl csucmap crn cv csuc wceq copab wex cab df-succl df-sucmap rnopab
      rneqi 3eqtri ) CDEAFGBFHZABIZEQAJBKLDRABMOQABNP $.
  $}

  ${
    $d N l m $.
    $( There is at most one predecessor of ` N ` .  (Contributed by Peter
       Mazsa, 12-Jan-2026.) $)
    mopre $p |- E* m suc m = N $=
      ( vl cv csuc wceq wmo wa wal eqtr3 suc11reg sylib gen2 suceq eqeq1d mpbir
      wi mo4 ) ADZEZBFZAGUACDZEZBFZHZSUBFZQZCIAIUGACUETUCFUFTUCBJSUBKLMUAUDACUF
      TUCBSUBNORP $.
  $}

  ${
    $d N m $.
    $( Whenever a predecessor exists, it exists alone.  (Contributed by Peter
       Mazsa, 12-Jan-2026.) $)
    exeupre2 $p |- ( E. m suc m = N <-> E! m suc m = N ) $=
      ( cv csuc wceq wmo wex weu wb mopre moeuex ax-mp ) ACDBEZAFMAGMAHIABJMAKL
      $.
  $}

  ${
    $d m n $.
    $( Alternate definition of the class of all successors.  (Contributed by
       Peter Mazsa, 30-Jan-2026.) $)
    dfsuccl3 $p |- Suc = { n | E! m suc m = n } $=
      ( csuccl cv csuc wceq wex cab weu dfsuccl2 exeupre2 abbii eqtri ) CADEBDZ
      FZAGZBHOAIZBHABJPQBANKLM $.
  $}

  ${
    $d m n $.
    $( Alternate definition that incorporates the most desirable properties of
       the successor class.  (Contributed by Peter Mazsa, 30-Jan-2026.) $)
    dfsuccl4 $p |- Suc = { n | E! m e. n ( m C_ n /\ suc m = n ) } $=
      ( csuccl cv csuc wceq weu cab wss wreu dfsuccl3 wcel w3a cvv sucidg eleq2
      wa elv mpbii sssucid sseq2 jca pm4.71ri df-3an 3anass eubii df-reu bitr4i
      3bitr2i abbii eqtri ) CADZEZBDZFZAGZBHULUNIZUOQZAUNJZBHABKUPUSBUPULUNLZUR
      QZAGUSUOVAAUOUTUQQZUOQUTUQUOMVAUOVBUOUTUQUOULUMLZUTVCAULNORUMUNULPSUOULUM
      IUQULTUMUNULUASUBUCUTUQUOUDUTUQUOUEUIUFURAUNUGUHUJUK $.
  $}

  ${
    $d N m $.
    $( Define the term-level successor-predecessor.  It is the unique ` m `
       with ` suc m = N ` when such an ` m ` exists; otherwise ` pre N ` is the
       arbitrary default chosen by ` iota ` .  See its alternate definitions
       ~ dfpre , ~ dfpre2 , ~ dfpre3 and ~ dfpre4 .

       Our definition is a special case of the widely recognised general ` R `
       -predecessor class ~ df-pred (the class of all elements ` m ` of ` A `
       such that ` m R N ` , ~ dfpred3g , cf. also ~ df-bnj14 ) in several
       respects.  Its most abstract property as a specialisation is that it has
       a unique existing value by default.  This is in contrast to the general
       version.  The uniqueness (conditional on existence) is implied by the
       property of this specific instance of the general case involving the
       successor map ~ df-sucmap in place of ` R ` , so that ` m SucMap N ` ,
       cf. ~ sucmapleftuniq , which originates from ~ suc11reg .  Existence
       ` E. m m SucMap N ` holds exactly on ` N e. ran SucMap ` , cf. ~ elrng .

       Note that ` dom SucMap = _V ` (see ~ dmsucmap ), so the equivalent
       definition ~ dfpre uses ` ( iota m m e. Pred ( SucMap , _V , N ) ) ` .
       (Contributed by Peter Mazsa, 27-Jan-2026.) $)
    df-pre $a |- pre N = ( iota m m e. Pred ( SucMap , dom SucMap , N ) ) $.
  $}

  ${
    $d N m $.
    $( Alternate definition of the successor-predecessor.  (Contributed by
       Peter Mazsa, 27-Jan-2026.) $)
    dfpre $p |- pre N = ( iota m m e. Pred ( SucMap , _V , N ) ) $=
      ( cpre csucmap cdm cpred wcel cio cvv df-pre wceq dmsucmap predeq2 eleq2i
      cv ax-mp iotabii eqtri ) BCAOZDEZDBFZGZAHSIDBFZGZAHABJUBUDAUAUCSTIKUAUCKL
      TIDBMPNQR $.
  $}

  ${
    $d N m $.  $d V m $.
    $( Alternate definition of the successor-predecessor.  (Contributed by
       Peter Mazsa, 12-Jan-2026.) $)
    dfpre2 $p |- ( N e. V -> pre N = ( iota m m SucMap N ) ) $=
      ( wcel cpre cv cvv csucmap cpred cio wbr dfpre wb elpredg iotabidv eqtrid
      elvd ) BCDZBEAFZGHBIDZAJSBHKZAJABLRTUAARTUAMAGCHBSNQOP $.
  $}

  ${
    $d N m $.  $d V m $.
    $( Alternate definition of the successor-predecessor.  (Contributed by
       Peter Mazsa, 12-Jan-2026.) $)
    dfpre3 $p |- ( N e. V -> pre N = ( iota m suc m = N ) ) $=
      ( wcel cpre cv csucmap wbr cio csuc dfpre2 wb cvv brsucmap el2v1 iotabidv
      wceq eqtrd ) BCDZBEAFZBGHZAITJBQZAIABCKSUAUBASUAUBLATBMCNOPR $.
  $}

  ${
    $d A m $.  $d N m $.  $d R m $.  $d V m $.
    $( Alternate definition of the predecessor class when ` N ` is a set.
       (Contributed by Peter Mazsa, 26-Jan-2026.) $)
    dfpred4 $p |- ( N e. V -> Pred ( R , A , N ) = [ N ] `' ( R |` A ) ) $=
      ( vm wcel cpred cv wbr crab cres ccnv cec dfpred3g ec1cnvres eqtr4d ) CDF
      ABCGEHCBIEAJCBAKLMEABDCNEACBDOP $.
  $}

  ${
    $d N m $.  $d V m $.
    $( Alternate definition of the predecessor of the ` N ` set.  The
       ` ``' SucMap ` is just the "PreMap"; we did not define it because we do
       not expect to use it extensively in future (cf. the comments of
       ~ df-sucmap ).  (Contributed by Peter Mazsa, 26-Jan-2026.) $)
    dfpre4 $p |- ( N e. V -> pre N = ( iota m m e. [ N ] `' SucMap ) ) $=
      ( wcel cpre cv csucmap cdm cpred cio ccnv cec cres dfpred4 wrel relsucmap
      df-pre wceq dfrel5 mpbi cnveqi eceq2i eqtrdi eleq2d iotabidv eqtrid ) BCD
      ZBEAFZGHZGBIZDZAJUHBGKZLZDZAJABQUGUKUNAUGUJUMUHUGUJBGUIMZKZLUMUIGBCNUPULB
      UOGGOUOGRPGSTUAUBUCUDUEUF $.
  $}

  ${
    $d a r $.
    $( Define the equilibrium / fixed-point condition for "block carriers".

       Start with a candidate block-family ` a ` (a set whose elements you
       intend to treat as blocks).  Combine it with a relation ` r ` by forming
       the block-lift span ` T = ( r |X. ( ``' _E |`` a ) ) ` .  For a block
       ` u e. a ` , the fiber ` [ u ] T ` is the set of all outputs produced
       from "external targets" of ` r ` together with "internal members" of
       ` u ` ; in other words, ` T ` is the mechanism that generates new blocks
       from old ones.

       Now apply the standard quotient construction ` ( dom T /. T ) ` .  This
       produces the family of all T-blocks (the cosets ` [ x ] T ` of witnesses
       ` x ` in the domain of ` T ` ).  In general, this operation can change
       your carrier: starting from ` a ` , it may generate a different
       block-family ` ( dom T /. T ) ` .

       The equation
       ` ( dom ( r |X. ( ``' _E |`` a ) ) /. ( r |X. ( ``' _E |`` a ) ) ) = a `
       says exactly: if you generate blocks from ` a ` using the lift
       determined by ` r ` (cf. ~ df-blockliftmap ), you get back the same
       ` a ` .  So ` a ` is stable under the block-generation operator induced
       by ` r ` .  This is why it is a genuine fixpoint/equilibrium condition:
       one application of the "make-the-blocks" operator causes no carrier
       drift, i.e. no hidden refinement/coarsening of what counts as a block.

       Here, the quotient ` ( dom T /. T ) ` is the standard carrier of ` T `
       -blocks; see ~ dfqs2 for the quotient-as-range viewpoint.

       This is an untyped equilibrium predicate on pairs ` <. r , a >. ` .  No
       hypothesis ` r e. Rels ` is built into the definition, because the
       fixpoint equation depends only on those ordered pairs ` <. x , y >. `
       that belong to ` r ` and hence can witness an atomic instance
       ` x r y ` ; extra non-ordered-pair "junk" elements in ` r ` are ignored
       automatically by the relational membership predicate.

       When later work needs ` r ` to be relation-typed (e.g. to intersect with
       ` ( Rels X. _V ) ` -style typedness modules, or to apply ` Rels ` -based
       infrastructure uniformly), the additional typing constraint
       ` r e. Rels ` should be imposed locally as a separate conjunct (rather
       than being baked into this equilibrium module).  (Contributed by Peter
       Mazsa, 25-Jan-2026.)  (Revised by Peter Mazsa, 20-Feb-2026.) $)
    df-blockliftfix $a |- BlockLiftFix = { <. r , a >. |
       ( dom ( r |X. ( `' _E |` a ) ) /. ( r |X. ( `' _E |` a ) ) ) = a } $.
  $}

  $( Define shift-stability, a general "procedure" pattern for "the one-step
     backward shift/transport of ` F ` along ` S ` ", and then ` i^i F `
     enforces "and it already holds here".

     Let ` F ` be a relation encoding a property that depends on a "level"
     coordinate (for example, a feasibility condition indexed by a carrier, a
     grade, or a stage in a construction).  Let ` S ` be a shift relation
     between levels (for example, the successor map ` SucMap ` , or any other
     grading step).

     The composed relation ` ( S o. F ) ` transports ` F ` one step along the
     shift: ` r ( S o. F ) n ` means there exists a predecessor level ` m `
     such that ` r F m ` and ` m S n ` (e.g., ` m SucMap n ` ).  We do not
     introduce a separate notation for "Shift" because it is simply the
     standard relational composition ~ df-co .

     The intersection ` ( ( S o. F ) i^i F ) ` is the locally shift-stable
     fragment of ` F ` : it consists exactly of those points where the property
     holds at some immediate predecessor that shifts to ` n ` and also holds at
     level ` n ` .  In other words, it isolates the part of ` F ` that is
     already compatible with one-step tower coherence.

     This definition packages a common construction pattern used throughout the
     development:  "constrain by one-step stability under a chosen shift, then
     additionally constrain by ` F ` ".  Iterating the operator
     ` ( X |-> ( ( S o. X ) i^i X ) ` corresponds to multi-step/tower
     coherence; the one-step definition here is the economical kernel from
     which such "tower" readings can be developed when needed.  (Contributed by
     Peter Mazsa, 25-Jan-2026.) $)
  df-shiftstable $a |- ( S ShiftStable F ) = ( ( S o. F ) i^i F ) $.

  $( Equality theorem for shift-stability of two classes.  (Contributed by
     Peter Mazsa, 19-Feb-2026.) $)
  shiftstableeq2 $p |- ( F = G ->
                         ( S ShiftStable F ) = ( S ShiftStable G ) ) $=
    ( wceq ccom cin cshiftstable coeq2 id ineq12d df-shiftstable 3eqtr4g ) BCDZ
    ABEZBFACEZCFABGACGMNOBCBCAHMIJABKACKL $.

  $( One-to-one relationship between the successor operation and the singleton.
     (Contributed by Peter Mazsa, 31-Dec-2024.) $)
  suceqsneq $p |- ( A e. V -> ( suc A = suc B <-> { A } = { B } ) ) $=
    ( wcel csuc wceq csn suc11reg sneqbg bitr4id ) ACDAEBEFABFAGBGFABHABCIJ $.

  $( Absorption of union with a singleton by difference.  (Contributed by Peter
     Mazsa, 24-Jul-2024.) $)
  sucdifsn2 $p |- ( ( A u. { A } ) \ { A } ) = A $=
    ( csn cin c0 wceq cun cdif disjcsn undif5 ax-mp ) AABZCDEAKFKGAEAHAKIJ $.

  $( The difference between the successor and the singleton of a class is the
     class.  (Contributed by Peter Mazsa, 20-Sep-2024.) $)
  sucdifsn $p |- ( suc A \ { A } ) = A $=
    ( csuc csn cdif cun df-suc difeq1i sucdifsn2 eqtri ) ABZACZDAKEZKDAJLKAFGAH
    I $.

  $( The difference between restrictions to the successor and the singleton of
     a class is the restriction to the class, see ~ ressucdifsn .  (Contributed
     by Peter Mazsa, 24-Jul-2024.) $)
  ressucdifsn2 $p |- ( ( R |` ( A u. { A } ) ) \ ( R |` { A } ) ) =
                     ( R |` A ) $=
    ( csn cin c0 wceq cun cres cdif disjcsn disjresundif ax-mp ) AACZDEFBAMGHBM
    HIBAHFAJAMBKL $.

  $( The difference between restrictions to the successor and the singleton of
     a class is the restriction to the class.  (Contributed by Peter Mazsa,
     20-Sep-2024.) $)
  ressucdifsn $p |- ( ( R |` suc A ) \ ( R |` { A } ) ) = ( R |` A ) $=
    ( csuc cres csn cdif cun df-suc reseq2i difeq1i ressucdifsn2 eqtri ) BACZDZ
    BAEZDZFBAOGZDZPFBADNRPMQBAHIJABKL $.

  $( A set is succeeded by its successor.  (Contributed by Peter Mazsa,
     7-Jan-2026.) $)
  sucmapsuc $p |- ( M e. V -> M SucMap suc M ) $=
    ( wcel csuc csucmap wbr wceq eqid cvv wb sucexg brsucmap mpdan mpbiri ) ABC
    ZAADZEFZPPGZPHOPICQRJABKAPBILMN $.

  $( Left uniqueness of the successor mapping.  (Contributed by Peter Mazsa,
     8-Jan-2026.) $)
  sucmapleftuniq $p |- ( ( L e. V /\ M e. W /\ N e. X ) ->
                         ( ( L SucMap N /\ M SucMap N ) -> L = M ) ) $=
    ( wcel w3a csucmap wa csuc wceq wb brsucmap bi2anan9 3impdir eqtr3 biimtrdi
    wbr suc11reg imbitrdi ) ADGZBEGZCFGZHZACISZBCISZJZAKZBKZLZABLUEUHUICLZUJCLZ
    JZUKUBUDUCUHUNMUBUDJUFULUCUDJUGUMACDFNBCEFNOPUIUJCQRABTUA $.

  ${
    $d N m $.  $d V m $.
    $( Whenever a predecessor exists, it exists alone.  (Contributed by Peter
       Mazsa, 12-Jan-2026.) $)
    exeupre $p |- ( N e. V -> ( E. m m SucMap N <-> E! m m SucMap N ) ) $=
      ( wcel cv csucmap wbr wex csuc wceq weu wb brsucmap el2v1 exbidv exeupre2
      cvv bitrdi eubidv bitr4d ) BCDZAEZBFGZAHZUBIBJZAKZUCAKUAUDUEAHUFUAUCUEAUA
      UCUELAUBBQCMNZOABPRUAUCUEAUGST $.
  $}

  ${
    $d N m $.
    $( The successor-predecessor exists.  (Contributed by Peter Mazsa,
       12-Jan-2026.) $)
    preex $p |- pre N e. _V $=
      ( vm cpre cv csucmap cdm cpred wcel cio cvv df-pre iotaex eqeltri ) ACBDE
      FEAGHZBIJBAKNBLM $.
  $}

  ${
    $d N m $.  $d V m $.
    $( Unique predecessor exists on the range of the successor map.
       (Contributed by Peter Mazsa, 12-Jan-2026.) $)
    eupre2 $p |- ( N e. V -> ( N e. ran SucMap <-> E! m m SucMap N ) ) $=
      ( wcel csucmap crn cv wbr wex weu elrng exeupre bitrd ) BCDBEFDAGBEHZAINA
      JABECKABCLM $.
  $}

  ${
    $d N m $.  $d V m $.
    $( Unique predecessor exists on the successor class.  (Contributed by Peter
       Mazsa, 27-Jan-2026.) $)
    eupre $p |- ( N e. V -> ( N e. Suc <-> E! m m SucMap N ) ) $=
      ( csuccl wcel csucmap crn cv wbr weu df-succl eleq2i eupre2 bitrid ) BDEB
      FGZEBCEAHBFIAJDOBKLABCMN $.
  $}

  ${
    $d N m $.
    $( ` pre ` is really a predecessor (when it should be).  This correctness
       theorem for ` pre ` makes it usable in proofs without unfolding
       ` iota ` .  This theorem gives one witness; ~ preuniqval gives it is the
       only one.  (Contributed by Peter Mazsa, 12-Jan-2026.) $)
    presucmap $p |- ( N e. ran SucMap -> pre N SucMap N ) $=
      ( vm csucmap crn wcel cpre wbr cv cio wceq dfpre2 eqcomd cvv weu wb preex
      eupre2 ibi breq1 iota2 sylancr mpbird ) ACDZEZAFZACGZBHZACGZBIZUEJZUDUEUI
      BAUCKLUDUEMEUHBNZUFUJOAPUDUKBAUCQRUHUFBUEMUGUEACSTUAUB $.
  $}

  ${
    $d N m $.
    $( Uniqueness/canonicity of ` pre ` . ~ presucmap gives one witness; this
       theorem gives it is the only one.  It turns any predecessor proof into
       an equality with ` pre N ` .  (Contributed by Peter Mazsa,
       12-Jan-2026.) $)
    preuniqval $p |- ( N e. ran SucMap -> A. m ( m SucMap N -> m = pre N ) ) $=
      ( csucmap crn wcel cv wbr cpre wceq wi presucmap cvv preex sucmapleftuniq
      wa mp3an1 el2v1 mpand eqcom imbitrdi alrimiv ) BCDZEZAFZBCGZUDBHZIZJAUCUE
      UFUDIZUGUCUFBCGZUEUHBKUCUIUEOUHJZAUFLEUDLEUCUJBMUFUDBLLUBNPQRUFUDSTUA $.
  $}

  $( ` suc ` is a right-inverse of ` pre ` on ` Suc ` .  This theorem states
     the partial inverse relation in the direction we most often need.
     (Contributed by Peter Mazsa, 27-Jan-2026.) $)
  sucpre $p |- ( N e. Suc -> suc pre N = N ) $=
    ( cpre csuc wceq csucmap crn csuccl wcel wbr presucmap cvv wb brsucmap mpan
    preex mpbid df-succl eleq2s ) ABZCADZAEFZGAUAHZSAEIZTAJSKHUBUCTLAOSAKUAMNPQ
    R $.

  $( ` pre ` is a left-inverse of ` suc ` .  This theorem gives a clean rewrite
     rule that eliminates ` pre ` on explicit successors.  (Contributed by
     Peter Mazsa, 12-Jan-2026.) $)
  presuc $p |- ( M e. V -> pre suc M = M ) $=
    ( wcel csuc cpre wceq csucmap wbr sucmapsuc crn relsucmap relelrni df-succl
    csuccl eleqtrrdi sucpre 3syl suc11reg sylib ) ABCZADZEZDUAFZUBAFTAUAGHZUANC
    UCABIUDUAGJNAUAGKLMOUAPQUBARS $.

  $( Predecessor is a subset of its successor.  (Contributed by Peter Mazsa,
     12-Jan-2026.) $)
  press $p |- ( N e. Suc -> pre N C_ N ) $=
    ( csuccl wcel cpre csuc sssucid sucpre sseqtrid ) ABCADZEIAIFAGH $.

  $( Predecessor is a subset of its successor.  (Contributed by Peter Mazsa,
     12-Jan-2026.) $)
  preel $p |- ( N e. Suc -> pre N e. N ) $=
    ( csuccl wcel cpre csuc preex sucid sucpre eleqtrid ) ABCADZJEAJAFGAHI $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Cosets by ` R `
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d R u x y $.
    $( Define the class of cosets by ` R ` : ` x ` and ` y ` are cosets by
       ` R ` iff there exists a set ` u ` such that both ` u R x ` and
       ` u R y ` hold, i.e., both ` x ` and ` y ` are are elements of the ` R `
       -coset of ` u ` (see ~ dfcoss2 and the comment of ~ dfec2 ). ` R ` is
       usually a relation.

       This concept simplifies theorems relating partition and equivalence: the
       left side of these theorems relate to ` R ` , the right side relate to
       ` ,~ R ` (see e.g. ~ pet ).  Without the definition of ` ,~ R ` we
       should have to relate the right side of these theorems to a composition
       of a converse (cf. ~ dfcoss3 ) or to the range of a range Cartesian
       product of classes (cf. ~ dfcoss4 ), which would make the theorems
       complicated and confusing.  Alternate definition is ~ dfcoss2 .
       Technically, we can define it via composition ( ~ dfcoss3 ) or as the
       range of a range Cartesian product ( ~ dfcoss4 ), but neither of these
       definitions reveal directly how the cosets by ` R ` relate to each
       other.  We define functions ( ~ df-funsALTV , ~ df-funALTV ) and
       disjoints ( ~ dfdisjs , ~ dfdisjs2 , ~ df-disjALTV , ~ dfdisjALTV2 )
       with the help of it as well.  (Contributed by Peter Mazsa,
       9-Jan-2018.) $)
    df-coss $a |- ,~ R = { <. x , y >. | E. u ( u R x /\ u R y ) } $.
  $}

  $( Define the class of coelements on the class ` A ` , see also the alternate
     definition ~ dfcoels .  Possible definitions are the special cases of
     ~ dfcoss3 and ~ dfcoss4 .  (Contributed by Peter Mazsa, 20-Nov-2019.) $)
  df-coels $a |- ~ A = ,~ ( `' _E |` A ) $.

  ${
    $d R u x y $.
    $( Alternate definition of the class of cosets by ` R ` : ` x ` and ` y `
       are cosets by ` R ` iff there exists a set ` u ` such that both ` x `
       and ` y ` are are elements of the ` R ` -coset of ` u ` (see also the
       comment of ~ dfec2 ). ` R ` is usually a relation.  (Contributed by
       Peter Mazsa, 16-Jan-2018.) $)
    dfcoss2 $p |- ,~ R =
                  { <. x , y >. | E. u ( x e. [ u ] R /\ y e. [ u ] R ) } $=
      ( ccoss cv wbr wa wex copab cec wcel df-coss wb cvv elecALTV el2v anbi12i
      exbii opabbii eqtr4i ) DECFZAFZDGZUBBFZDGZHZCIZABJUCUBDKZLZUEUILZHZCIZABJ
      ABCDMUMUHABULUGCUJUDUKUFUJUDNCAUBUCDOOPQUKUFNCBUBUEDOOPQRSTUA $.
  $}

  ${
    $d R u x y $.
    $( Alternate definition of the class of cosets by ` R ` (see the comment of
       ~ df-coss ).  (Contributed by Peter Mazsa, 27-Dec-2018.) $)
    dfcoss3 $p |- ,~ R = ( R o. `' R ) $=
      ( vx vu vy cv ccnv wbr wa wex copab ccom ccoss wb cvv brcnvg anbi1i exbii
      el2v opabbii df-co df-coss 3eqtr4ri ) BEZCEZAFZGZUDDEAGZHZCIZBDJUDUCAGZUG
      HZCIZBDJAUEKALUIULBDUHUKCUFUJUGUFUJMBCUCUDNNAORPQSBDCAUETBDCAUAUB $.
  $}

  ${
    $d R u x y $.
    $( Alternate definition of the class of cosets by ` R ` (see the comment of
       ~ df-coss ).  (Contributed by Peter Mazsa, 12-Jul-2021.) $)
    dfcoss4 $p |- ,~ R = ran ( R |X. R ) $=
      ( vu vx vy ccoss cv wbr wa wex copab cxrn crn df-coss rnxrn eqtr4i ) AEBF
      ZCFAGPDFAGHBICDJAAKLCDBAMCDBAANO $.
  $}

  ${
    $d R u x y $.
    $( Class of cosets by the converse of ` R ` .  (Contributed by Peter Mazsa,
       17-Jun-2020.) $)
    cosscnv $p |- ,~ `' R = { <. x , y >. | E. u ( x R u /\ y R u ) } $=
      ( ccnv ccoss cv wbr wa wex copab df-coss wb cvv brcnvg el2v anbi12i exbii
      opabbii eqtri ) DEZFCGZAGZUAHZUBBGZUAHZIZCJZABKUCUBDHZUEUBDHZIZCJZABKABCU
      ALUHULABUGUKCUDUIUFUJUDUIMCAUBUCNNDOPUFUJMCBUBUENNDOPQRST $.
  $}

  ${
    $d A u v x $.  $d R u v x $.
    $( Class of cosets by the converse of a restriction.  (Contributed by Peter
       Mazsa, 8-Jun-2020.) $)
    coss1cnvres $p |- ,~ `' ( R |` A ) =
        { <. u , v >. |
             ( ( u e. A /\ v e. A ) /\ E. x ( u R x /\ v R x ) ) } $=
      ( cres ccnv ccoss cv wbr wex copab wcel df-coss cvv br1cnvres elv anbi12i
      wa wb an4 bitr4i exbii 19.42v bitri opabbii eqtri ) EDFGZHAIZCIZUHJZUIBIZ
      UHJZSZAKZCBLUJDMZULDMZSZUJUIEJZULUIEJZSZAKSZCBLCBAUHNUOVBCBUOURVASZAKVBUN
      VCAUNUPUSSZUQUTSZSVCUKVDUMVEUKVDTADUIUJEOPQUMVETADUIULEOPQRUPUQUSUTUAUBUC
      URVAAUDUEUFUG $.
  $}

  ${
    $d A u v x $.
    $( Special case of ~ coss1cnvres .  (Contributed by Peter Mazsa,
       8-Jun-2020.) $)
    coss2cnvepres $p |- ,~ `' ( `' _E |` A ) =
        { <. u , v >. |
             ( ( u e. A /\ v e. A ) /\ E. x ( x e. u /\ x e. v ) ) } $=
      ( cep ccnv cres ccoss cv wcel wa wbr wex copab coss1cnvres wb cvv brcnvep
      elv anbi12i exbii anbi2i opabbii eqtri ) EFZDGFHCIZDJBIZDJKZUFAIZUELZUGUI
      UELZKZAMZKZCBNUHUIUFJZUIUGJZKZAMZKZCBNABCDUEOUNUSCBUMURUHULUQAUJUOUKUPUJU
      OPCUFUIQRSUKUPPBUGUIQRSTUAUBUCUD $.
  $}

  $( If ` A ` is a set then the class of cosets by ` A ` is a set.
     (Contributed by Peter Mazsa, 4-Jan-2019.) $)
  cossex $p |- ( A e. V -> ,~ A e. _V ) $=
    ( wcel ccoss ccnv ccom cvv dfcoss3 cnvexg coexg mpdan eqeltrid ) ABCZADAAEZ
    FZGAHMNGCOGCABIANBGJKL $.

  $( If ` A ` is a set then the class of cosets by the converse of ` A ` is a
     set.  (Contributed by Peter Mazsa, 18-Oct-2019.) $)
  cosscnvex $p |- ( A e. V -> ,~ `' A e. _V ) $=
    ( wcel ccnv cvv ccoss cnvexg cossex syl ) ABCADZECJFECABGJEHI $.

  $( Sufficient condition for a restricted converse epsilon coset to be a set.
     (Contributed by Peter Mazsa, 24-Sep-2021.) $)
  1cosscnvepresex $p |- ( A e. V -> ,~ ( `' _E |` A ) e. _V ) $=
    ( wcel cep ccnv cres cvv ccoss cnvepresex cossex syl ) ABCDEAFZGCLHGCABILGJ
    K $.

  $( Sufficient condition for a restricted converse epsilon range Cartesian
     product to be a set.  (Contributed by Peter Mazsa, 23-Sep-2021.) $)
  1cossxrncnvepresex $p |- ( ( A e. V /\ R e. W ) ->
                             ,~ ( R |X. ( `' _E |` A ) ) e. _V ) $=
    ( wcel wa cep ccnv cres cxrn cvv ccoss xrncnvepresex cossex syl ) ACEBDEFBG
    HAIJZKEPLKEABCDMPKNO $.

  ${
    $d R u x y $.
    $( Cosets by ` R ` is a relation.  (Contributed by Peter Mazsa,
       27-Dec-2018.) $)
    relcoss $p |- Rel ,~ R $=
      ( vu vx vy cv wbr wa wex ccoss df-coss relopabiv ) BEZCEAFLDEAFGBHCDAICDB
      AJK $.
  $}

  $( Coelements on ` A ` is a relation.  (Contributed by Peter Mazsa,
     5-Oct-2021.) $)
  relcoels $p |- Rel ~ A $=
    ( ccoels wrel cep ccnv cres ccoss relcoss df-coels releqi mpbir ) ABZCDEAFZ
    GZCMHLNAIJK $.

  ${
    $d A x y z $.  $d B x y z $.
    $( Subclass theorem for the classes of cosets by ` A ` and ` B ` .
       (Contributed by Peter Mazsa, 11-Nov-2019.) $)
    cossss $p |- ( A C_ B -> ,~ A C_ ,~ B ) $=
      ( vx vy vz wss cv wbr wa wex copab ccoss anim12d eximdv ssopab2dv df-coss
      ssbr 3sstr4g ) ABFZCGZDGZAHZTEGZAHZIZCJZDEKTUABHZTUCBHZIZCJZDEKALBLSUFUJD
      ESUEUICSUBUGUDUHABTUAQABTUCQMNODECAPDECBPR $.
  $}

  ${
    $d A u x y $.  $d B u x y $.
    $( Equality theorem for the classes of cosets by ` A ` and ` B ` .
       (Contributed by Peter Mazsa, 9-Jan-2018.) $)
    cosseq $p |- ( A = B -> ,~ A = ,~ B ) $=
      ( vu vx vy wceq cv wbr wa wex copab ccoss anbi12d exbidv opabbidv df-coss
      breq 3eqtr4g ) ABFZCGZDGZAHZTEGZAHZIZCJZDEKTUABHZTUCBHZIZCJZDEKALBLSUFUJD
      ESUEUICSUBUGUDUHTUAABQTUCABQMNODECAPDECBPR $.
  $}

  ${
    cosseqi.1 $e |- A = B $.
    $( Equality theorem for the classes of cosets by ` A ` and ` B ` ,
       inference form.  (Contributed by Peter Mazsa, 9-Jan-2018.) $)
    cosseqi $p |- ,~ A = ,~ B $=
      ( wceq ccoss cosseq ax-mp ) ABDAEBEDCABFG $.
  $}

  ${
    cosseqd.1 $e |- ( ph -> A = B ) $.
    $( Equality theorem for the classes of cosets by ` A ` and ` B ` ,
       deduction form.  (Contributed by Peter Mazsa, 4-Nov-2019.) $)
    cosseqd $p |- ( ph -> ,~ A = ,~ B ) $=
      ( wceq ccoss cosseq syl ) ABCEBFCFEDBCGH $.
  $}

  ${
    $d A u x y $.  $d R u x y $.
    $( The class of cosets by a restriction.  (Contributed by Peter Mazsa,
       20-Apr-2019.) $)
    1cossres $p |- ,~ ( R |` A ) =
                   { <. x , y >. | E. u e. A ( u R x /\ u R y ) } $=
      ( cres ccoss cv wbr wa wex copab wrex df-coss wcel df-rex cvv brres elv
      wb anandi anbi12i bitr4i exbii bitri opabbii eqtr4i ) EDFZGCHZAHZUHIZUIBH
      ZUHIZJZCKZABLUIUJEIZUIULEIZJZCDMZABLABCUHNUSUOABUSUIDOZURJZCKUOURCDPVAUNC
      VAUTUPJZUTUQJZJUNUTUPUQUAUKVBUMVCUKVBTADUIUJEQRSUMVCTBDUIULEQRSUBUCUDUEUF
      UG $.
  $}

  ${
    $d A u x y $.
    $( Alternate definition of the class of coelements on the class ` A ` .
       (Contributed by Peter Mazsa, 20-Apr-2019.) $)
    dfcoels $p |- ~ A = { <. x , y >. | E. u e. A ( x e. u /\ y e. u ) } $=
      ( ccoels cep ccnv cres ccoss cv wbr wa wrex copab wel df-coels wb brcnvep
      cvv elv 1cossres anbi12i rexbii opabbii 3eqtri ) DEFGZDHICJZAJZUFKZUGBJZU
      FKZLZCDMZABNACOZBCOZLZCDMZABNDPABCDUFUAUMUQABULUPCDUIUNUKUOUIUNQCUGUHSRTU
      KUOQCUGUJSRTUBUCUDUE $.
  $}

  ${
    $d A u x y $.  $d B u x y $.  $d R u x y $.  $d V u $.  $d W u $.
    $( ` A ` and ` B ` are cosets by ` R ` : a binary relation.  (Contributed
       by Peter Mazsa, 27-Dec-2018.) $)
    brcoss $p |- ( ( A e. V /\ B e. W ) ->
                   ( A ,~ R B <-> E. u ( u R A /\ u R B ) ) ) $=
      ( vx vy cv wbr wa wex ccoss wceq breq2 bi2anan9 exbidv df-coss brabga ) A
      IZGIZDJZTHIZDJZKZALTBDJZTCDJZKZALGHBCDMEFUABNZUCCNZKUEUHAUIUBUFUJUDUGUABT
      DOUCCTDOPQGHADRS $.
  $}

  ${
    $d A u $.  $d B u $.  $d R u $.  $d V u $.  $d W u $.
    $( Alternate form of the ` A ` and ` B ` are cosets by ` R ` binary
       relation.  (Contributed by Peter Mazsa, 26-Mar-2019.) $)
    brcoss2 $p |- ( ( A e. V /\ B e. W ) ->
       ( A ,~ R B <-> E. u ( A e. [ u ] R /\ B e. [ u ] R ) ) ) $=
      ( wcel wa ccoss wbr cv wex cec brcoss exan3 bitr4d ) BEGCFGHBCDIJAKZBDJQC
      DJHALBQDMZGCRGHALABCDEFNABCDEFOP $.
  $}

  ${
    $d A u $.  $d B u $.  $d R u $.  $d V u $.  $d W u $.
    $( Alternate form of the ` A ` and ` B ` are cosets by ` R ` binary
       relation.  (Contributed by Peter Mazsa, 26-Mar-2019.) $)
    brcoss3 $p |- ( ( A e. V /\ B e. W ) ->
       ( A ,~ R B <-> ( [ A ] `' R i^i [ B ] `' R ) =/= (/) ) ) $=
      ( vu wcel wa cv ccnv wbr wex cec cin c0 wne wb cvv brcnvg elvd bi2anan9
      ccoss exbidv ecinn0 brcoss 3bitr4rd ) ADGZBEGZHZAFIZCJZKZBUJUKKZHZFLUJACK
      ZUJBCKZHZFLAUKMBUKMNOPABCUBKUIUNUQFUGULUOUHUMUPUGULUOQFAUJDRCSTUHUMUPQFBU
      JERCSTUAUCFABUKDEUDFABCDEUEUF $.
  $}

  ${
    $d A u $.  $d B u $.  $d R u $.  $d V u $.  $d W u $.
    $( For sets, the ` A ` and ` B ` cosets by ` R ` binary relation and the
       ` B ` and ` A ` cosets by ` R ` binary relation are the same.
       (Contributed by Peter Mazsa, 27-Dec-2018.) $)
    brcosscnvcoss $p |- ( ( A e. V /\ B e. W ) ->
                          ( A ,~ R B <-> B ,~ R A ) ) $=
      ( vu wcel wa cv wbr wex ccoss wb exancom a1i brcoss ancoms 3bitr4d ) ADGZ
      BEGZHZFIZACJZUBBCJZHFKZUDUCHFKZABCLZJBAUGJZUEUFMUAUCUDFNOFABCDEPTSUHUFMFB
      ACEDPQR $.
  $}

  ${
    $d A u x y $.  $d B u x y $.  $d C u x y $.
    $( ` B ` and ` C ` are coelements : a binary relation.  (Contributed by
       Peter Mazsa, 14-Jan-2020.)  (Revised by Peter Mazsa, 5-Oct-2021.) $)
    brcoels $p |- ( ( B e. V /\ C e. W ) ->
                    ( B ~ A C <-> E. u e. A ( B e. u /\ C e. u ) ) ) $=
      ( vx vy cv wcel wa wrex ccoels wceq eleq1 bi2anan9 rexbidv dfcoels brabga
      ) GIZAIZJZHIZUAJZKZABLCUAJZDUAJZKZABLGHCDBMEFTCNZUCDNZKUEUHABUIUBUFUJUDUG
      TCUAOUCDUAOPQGHABRS $.
  $}

  ${
    $d R x y z $.  $d S x y z $.
    $( Two ways of saying that cosets by cosets by ` R ` is a subclass.
       (Contributed by Peter Mazsa, 17-Sep-2021.) $)
    cocossss $p |- ( ,~ ,~ R C_ S <->
       A. x A. y A. z ( ( x ,~ R y /\ y ,~ R z ) -> x S z ) ) $=
      ( ccoss wss cv wbr wi wal wa wrel wb relcoss wex cvv el2v bitri albii
      ssrel3 ax-mp brcoss brcosscnvcoss anbi1i exbii imbi1i 19.23v bitr4i alcom
      ) DFZFZEGZAHZCHZULIZUNUOEIZJZCKZAKZUNBHZUKIZVAUOUKIZLZUQJZCKBKZAKULMUMUTN
      UKOACULEUAUBUSVFAUSVEBKZCKVFURVGCURVDBPZUQJVGUPVHUQUPVAUNUKIZVCLZBPZVHUPV
      KNACBUNUOUKQQUCRVJVDBVIVBVCVIVBNBAVAUNDQQUDRUEUFSUGVDUQBUHUITVECBUJSTS $.
  $}

  ${
    $d R x y $.
    $( The converse of cosets by ` R ` are cosets by ` R ` .  (Contributed by
       Peter Mazsa, 3-May-2019.) $)
    cnvcosseq $p |- `' ,~ R = ,~ R $=
      ( vx vy ccoss ccnv wss wceq cv wbr wal cvv brcosscnvcoss el2v biimpi gen2
      wi wb cnvsym mpbir wrel relcoss relcnveq ax-mp mpbi ) ADZEZUEFZUFUEGZUGBH
      ZCHZUEIZUJUIUEIZPZCJBJUMBCUKULUKULQBCUIUJAKKLMNOBCUERSUETUGUHQAUAUEUBUCUD
      $.
  $}

  $( Cosets by ` ,~ R ` binary relation.  (Contributed by Peter Mazsa,
     25-Aug-2019.) $)
  br2coss $p |- ( ( A e. V /\ B e. W ) ->
      ( A ,~ ,~ R B <-> ( [ A ] ,~ R i^i [ B ] ,~ R ) =/= (/) ) ) $=
    ( wcel wa ccoss wbr ccnv cec cin c0 brcoss3 cnvcosseq eceq2i ineq12i neeq1i
    wne bitrdi ) ADFBEFGABCHZHIAUAJZKZBUBKZLZMSAUAKZBUAKZLZMSABUADENUEUHMUCUFUD
    UGUBUAACOZPUBUABUIPQRT $.

  ${
    $d A u $.  $d B u $.  $d C u $.  $d R u $.  $d V u $.  $d W u $.
    $( ` B ` and ` C ` are cosets by a restriction: a binary relation.
       (Contributed by Peter Mazsa, 30-Dec-2018.) $)
    br1cossres $p |- ( ( B e. V /\ C e. W ) ->
      ( B ,~ ( R |` A ) C <-> E. u e. A ( u R B /\ u R C ) ) ) $=
      ( wcel wa cres ccoss wbr cv wex wrex brcoss exanres bitrd ) CFHDGHICDEBJZ
      KLAMZCSLTDSLIANTCELTDELIABOACDSFGPABCDEEFGQR $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.  $d R x $.  $d V x $.  $d W x $.
    $( ` B ` and ` C ` are cosets by a restriction: a binary relation.
       (Contributed by Peter Mazsa, 3-Jan-2018.) $)
    br1cossres2 $p |- ( ( B e. V /\ C e. W ) ->
                        ( B ,~ ( R |` A ) C <->
                          E. x e. A ( B e. [ x ] R /\ C e. [ x ] R ) ) ) $=
      ( wcel wa cres ccoss wbr cv wrex cec br1cossres exanres3 bitr4d ) CFHDGHI
      CDEBJKLAMZCELSDELIABNCSEOZHDTHIABNABCDEFGPABCDEEFGQR $.
  $}

  $( Binary relation on a restriction to a singleton.  (Contributed by Peter
     Mazsa, 11-Jun-2024.) $)
  brressn $p |- ( ( B e. V /\ C e. W ) ->
                  ( B ( R |` { A } ) C <-> ( B = A /\ B R C ) ) ) $=
    ( wcel wa csn cres wbr wceq wb brres adantl elsng adantr anbi1d bitrd ) BEG
    ZCFGZHZBCDAIZJKZBUCGZBCDKZHZBALZUFHUAUDUGMTUCBCDFNOUBUEUHUFTUEUHMUABAEPQRS
    $.

  ${
    $d A a u $.  $d R a u $.
    $( A class ' R ' restricted to the singleton of the class ' A ' is the
       ordered pair class abstraction of the class ' A ' and the sets in
       relation ' R ' to ' A ' (and not in relation to the singleton ' { A
       } ' ).  (Contributed by Peter Mazsa, 16-Jun-2024.) $)
    ressn2 $p |- ( R |` { A } ) = { <. a , u >. | ( a = A /\ A R u ) } $=
      ( csn cres cv wcel wbr copab wceq dfres2 velsn anbi1i eqbrb bitri opabbii
      wa eqtri ) CBEZFDGZTHZUAAGZCIZRZDAJUABKZBUCCIRZDAJDATCLUEUGDAUEUFUDRUGUBU
      FUDDBMNUABUCCOPQS $.
  $}

  ${
    $d A x $.  $d V x $.
    $( Any class ' R ' restricted to the singleton of the set ' A ' (see
       ~ ressn2 ) is reflexive, see also ~ refrelressn .  (Contributed by Peter
       Mazsa, 12-Jun-2024.) $)
    refressn $p |- ( A e. V ->
        A. x e. ( dom ( R |` { A } ) i^i ran ( R |` { A } ) )
          x ( R |` { A } ) x ) $=
      ( wcel cv csn cres wbr cdm crn cin wceq wa wi elin wb cvv adantr sylbi
      eldmressnALTV elv simplbi a1i elrnressn elvd biimpd adantld eqcomd breq1d
      biimtrid mpbidi jcad brressn el2v imbitrrdi ralrimiv ) BDEZAFZUSCBGHZIZAU
      TJZUTKZLZURUSVDEZUSBMZUSUSCIZNZVAURVEVFVGVEVFOURVEUSVBEZUSVCEZNZVFUSVBVCP
      ZVIVFVJVIVFBCJEZVIVFVMNQABUSCRUAUBUCZSTUDVEBUSCIZVGURVEVKURVOVLURVJVOVIUR
      VJVOURVJVOQABUSCDRUEUFUGUHUKVEVKVOVGQZVLVIVPVJVIBUSUSCVIUSBVNUIUJSTULUMVA
      VHQAABUSUSCRRUNUOUPUQ $.
  $}

  $( Every class ' R ' restricted to the singleton of the class ' A ' (see
     ~ ressn2 ) is antisymmetric.  (Contributed by Peter Mazsa,
     11-Jun-2024.) $)
  antisymressn $p |-
      A. x A. y ( ( x ( R |` { A } ) y /\ y ( R |` { A } ) x ) -> x = y ) $=
    ( cv csn cres wbr wa wceq wi wb cvv brressn el2v simplbi eqtr3 syl2an gen2
    ) AEZBEZDCFGZHZUATUBHZITUAJZKABUCTCJZUACJZUEUDUCUFTUADHZUCUFUHILABCTUADMMNO
    PUDUGUATDHZUDUGUIILBACUATDMMNOPTUACQRS $.

  $( Any class ' R ' restricted to the singleton of the class ' A ' (see
     ~ ressn2 ) is transitive, see also ~ trrelressn .  (Contributed by Peter
     Mazsa, 16-Jun-2024.) $)
  trressn $p |-
      A. x A. y A. z ( ( x ( R |` { A } ) y /\ y ( R |` { A } ) z ) ->
                       x ( R |` { A } ) z ) $=
    ( cv csn cres wbr wa wi wal wceq eqbrb anbi12i 3imtr4i wb cvv brressn el2v
    an3 gen2 ax-gen ) AFZBFZEDGHZIZUECFZUFIZJZUDUHUFIZKZCLBLAULBCUDDMZUDUEEIJZU
    EDMZUEUHEIJZJZUMUDUHEIJZUJUKUMDUEEIZJZUODUHEIZJZJUMVAJUQURUMUSUOVAUAUNUTUPV
    BUDDUEENUEDUHENOUDDUHENPUGUNUIUPUGUNQABDUDUEERRSTUIUPQBCDUEUHERRSTOUKURQACD
    UDUHERRSTPUBUC $.

  ${
    $d A x $.  $d B x $.  $d R x $.  $d V x $.  $d W x $.
    $( ` A ` and ` B ` are cosets by relation ` R ` : a binary relation.
       (Contributed by Peter Mazsa, 22-Apr-2021.) $)
    relbrcoss $p |- ( ( A e. V /\ B e. W ) ->
                      ( Rel R ->
        ( A ,~ R B <-> E. x e. dom R ( A e. [ x ] R /\ B e. [ x ] R ) ) ) ) $=
      ( wcel wa wrel ccoss wbr cv cec cdm wrex wb cres resdm cosseqd breqd ex
      adantl br1cossres2 adantr bitr3d ) BEGCFGHZDIZBCDJZKZBALDMZGCUJGHADNZOZPU
      FUGHBCDUKQZJZKZUIULUGUOUIPUFUGUNUHBCUGUMDDRSTUBUFUOULPUGAUKBCDEFUCUDUEUA
      $.
  $}

  ${
    $d A u $.  $d B u $.  $d C u $.  $d R u $.  $d S u $.  $d V u $.  $d W u $.
    $( ` B ` and ` C ` are cosets by an intersection with a restriction: a
       binary relation.  (Contributed by Peter Mazsa, 31-Dec-2021.) $)
    br1cossinres $p |- ( ( B e. V /\ C e. W ) ->
        ( B ,~ ( R i^i ( S |` A ) ) C <->
          E. u e. A ( ( u S B /\ u R B ) /\ ( u S C /\ u R C ) ) ) ) $=
      ( cres cin ccoss wbr wcel wa cv wrex inres cosseqi breqi brin br1cossres
      anbi12i an2anr bitri rexbii bitrdi bitrid ) CDEFBIJZKZLCDEFJZBIZKZLZCGMDH
      MNZAOZCFLZUOCELZNUODFLZUODELZNNZABPZCDUIULUHUKEFBQRSUNUMUOCUJLZUODUJLZNZA
      BPVAABCDUJGHUAVDUTABVDUQUPNZUSURNZNUTVBVEVCVFUOCEFTUODEFTUBUQUPUSURUCUDUE
      UFUG $.
  $}

  ${
    $d A u $.  $d B u $.  $d C u $.  $d D u $.  $d E u $.  $d R u $.  $d S u $.
    $d V u $.  $d W u $.  $d X u $.  $d Y u $.
    $( ` <. B , C >. ` and ` <. D , E >. ` are cosets by an range Cartesian
       product with a restriction: a binary relation.  (Contributed by Peter
       Mazsa, 8-Jun-2021.) $)
    br1cossxrnres $p |-
      ( ( ( B e. V /\ C e. W ) /\ ( D e. X /\ E e. Y ) ) ->
        ( <. B , C >. ,~ ( R |X. ( S |` A ) ) <. D , E >. <->
          E. u e. A ( ( u S C /\ u R B ) /\ ( u S E /\ u R D ) ) ) ) $=
      ( cop cres cxrn wbr wcel wa cvv wb ccoss cv wrex xrnres2 breqi br1cossres
      cosseqi mp2an brxrn el3v1 bi2anan9 an2anr bitrdi rexbidv bitrid bitr3id
      opex ) CDMZEHMZFGBNOZUAZPURUSFGOZBNZUAZPZCIQZDJQZRZEKQZHLQZRZRZAUBZDGPZVM
      CFPZRVMHGPZVMEFPZRRZABUCZURUSVDVAVCUTBFGUDUGUEVEVMURVBPZVMUSVBPZRZABUCZVL
      VSURSQUSSQVEWCTCDUQEHUQABURUSVBSSUFUHVLWBVRABVLWBVOVNRZVQVPRZRVRVHVTWDVKW
      AWEVFVGVTWDTAVMCDFGSIJUIUJVIVJWAWETAVMEHFGSKLUIUJUKVOVNVQVPULUMUNUOUP $.
  $}

  ${
    $d A u $.  $d B u $.  $d C u $.  $d R u $.  $d V u $.  $d W u $.
    $( ` B ` and ` C ` are cosets by an intersection with the restricted
       identity class: a binary relation.  (Contributed by Peter Mazsa,
       31-Dec-2021.) $)
    br1cossinidres $p |- ( ( B e. V /\ C e. W ) ->
        ( B ,~ ( R i^i ( _I |` A ) ) C <->
          E. u e. A ( ( u = B /\ u R B ) /\ ( u = C /\ u R C ) ) ) ) $=
      ( wcel wa cid cres cin wbr wrex wceq wb cvv ideq2 elv anbi1i br1cossinres
      ccoss cv anbi12i rexbii bitrdi ) CFHDGHICDEJBKLUBMAUCZCJMZUGCEMZIZUGDJMZU
      GDEMZIZIZABNUGCOZUIIZUGDOZULIZIZABNABCDEJFGUAUNUSABUJUPUMURUHUOUIUHUOPAUG
      CQRSTUKUQULUKUQPAUGDQRSTUDUEUF $.
  $}

  ${
    $d A u $.  $d B u $.  $d C u $.  $d R u $.  $d V u $.  $d W u $.
    $( ` B ` and ` C ` are cosets by an intersection with the restricted
       converse epsilon class: a binary relation.  (Contributed by Peter Mazsa,
       31-Dec-2021.) $)
    br1cossincnvepres $p |- ( ( B e. V /\ C e. W ) ->
        ( B ,~ ( R i^i ( `' _E |` A ) ) C <->
          E. u e. A ( ( B e. u /\ u R B ) /\ ( C e. u /\ u R C ) ) ) ) $=
      ( wcel wa cep ccnv cres cin wbr wrex wb cvv brcnvep elv anbi1i cv anbi12i
      ccoss br1cossinres rexbii bitrdi ) CFHDGHICDEJKZBLMUCNAUAZCUGNZUHCENZIZUH
      DUGNZUHDENZIZIZABOCUHHZUJIZDUHHZUMIZIZABOABCDEUGFGUDUOUTABUKUQUNUSUIUPUJU
      IUPPAUHCQRSTULURUMULURPAUHDQRSTUBUEUF $.
  $}

  ${
    $d A u $.  $d B u $.  $d C u $.  $d D u $.  $d E u $.  $d R u $.  $d V u $.
    $d W u $.  $d X u $.  $d Y u $.
    $( ` <. B , C >. ` and ` <. D , E >. ` are cosets by a range Cartesian
       product with the restricted identity class: a binary relation.
       (Contributed by Peter Mazsa, 8-Jun-2021.) $)
    br1cossxrnidres $p |-
        ( ( ( B e. V /\ C e. W ) /\ ( D e. X /\ E e. Y ) ) ->
          ( <. B , C >. ,~ ( R |X. ( _I |` A ) ) <. D , E >. <->
            E. u e. A ( ( u = C /\ u R B ) /\ ( u = E /\ u R D ) ) ) ) $=
      ( wcel wa cop cid wbr wrex wceq wb cvv cres ccoss br1cossxrnres ideq2 elv
      cxrn cv anbi1i anbi12i rexbii bitrdi ) CHLDILMEJLGKLMMCDNEGNFOBUAUFUBPAUG
      ZDOPZULCFPZMZULGOPZULEFPZMZMZABQULDRZUNMZULGRZUQMZMZABQABCDEFOGHIJKUCUSVD
      ABUOVAURVCUMUTUNUMUTSAULDTUDUEUHUPVBUQUPVBSAULGTUDUEUHUIUJUK $.
  $}

  ${
    $d A u $.  $d B u $.  $d C u $.  $d D u $.  $d E u $.  $d R u $.  $d V u $.
    $d W u $.  $d X u $.  $d Y u $.
    $( ` <. B , C >. ` and ` <. D , E >. ` are cosets by a range Cartesian
       product with the restricted converse epsilon class: a binary relation.
       (Contributed by Peter Mazsa, 12-May-2021.) $)
    br1cossxrncnvepres $p |-
      ( ( ( B e. V /\ C e. W ) /\ ( D e. X /\ E e. Y ) ) ->
        ( <. B , C >. ,~ ( R |X. ( `' _E |` A ) ) <. D , E >. <->
          E. u e. A ( ( C e. u /\ u R B ) /\ ( E e. u /\ u R D ) ) ) ) $=
      ( wcel wa cop wbr wrex wb cvv brcnvep elv ccnv cres cxrn cv br1cossxrnres
      cep ccoss anbi1i anbi12i rexbii bitrdi ) CHLDILMEJLGKLMMCDNEGNFUFUAZBUBUC
      UGOAUDZDULOZUMCFOZMZUMGULOZUMEFOZMZMZABPDUMLZUOMZGUMLZURMZMZABPABCDEFULGH
      IJKUEUTVEABUPVBUSVDUNVAUOUNVAQAUMDRSTUHUQVCURUQVCQAUMGRSTUHUIUJUK $.
  $}

  $( The domain of cosets is the domain of converse.  (Contributed by Peter
     Mazsa, 4-Jan-2019.) $)
  dmcoss3 $p |- dom ,~ R = dom `' R $=
    ( ccoss cdm ccnv ccom dfcoss3 dmeqi crn wss wceq rncnv dmcosseq ax-mp eqtri
    eqimssi ) ABZCAADZEZCZQCZPRAFGQHZACZISTJUAUBAKOAQLMN $.

  $( The domain of cosets is the range.  (Contributed by Peter Mazsa,
     27-Dec-2018.) $)
  dmcoss2 $p |- dom ,~ R = ran R $=
    ( ccoss cdm ccnv crn dmcoss3 df-rn eqtr4i ) ABCADCAEAFAGH $.

  ${
    $d R x y $.
    $( The range of cosets is the domain of them (this should be ~ rncoss but
       there exists a theorem with this name already).  (Contributed by Peter
       Mazsa, 12-Dec-2019.) $)
    rncossdmcoss $p |- ran ,~ R = dom ,~ R $=
      ( vy vx cv ccoss wbr wex cab crn cdm brcosscnvcoss el2v exbii abbii dfrn2
      wb cvv df-dm 3eqtr4i ) BDZCDZAEZFZBGZCHUATUBFZBGZCHUBIUBJUDUFCUCUEBUCUEPB
      CTUAAQQKLMNBCUBOCBUBRS $.
  $}

  $( The domain of cosets of the restricted converse epsilon relation is the
     union of the restriction.  (Contributed by Peter Mazsa, 18-May-2019.)
     (Revised by Peter Mazsa, 26-Sep-2021.) $)
  dm1cosscnvepres $p |- dom ,~ ( `' _E |` A ) = U. A $=
    ( cep ccnv cres ccoss cdm crn cuni dmcoss2 rncnvepres eqtri ) BCADZEFLGAHLI
    AJK $.

  $( The domain of coelements in ` A ` is the union of ` A ` .  (Contributed by
     Rodolfo Medina, 14-Oct-2010.)  (Revised by Peter Mazsa, 5-Apr-2018.)
     (Revised by Peter Mazsa, 26-Sep-2021.) $)
  dmcoels $p |- dom ~ A = U. A $=
    ( ccoels cdm cep ccnv cres ccoss cuni df-coels dmeqi dm1cosscnvepres eqtri
    ) ABZCDEAFGZCAHMNAIJAKL $.

  ${
    $d A u $.  $d R u $.  $d V u $.
    $( Elementhood in the domain of cosets.  (Contributed by Peter Mazsa,
       29-Mar-2019.) $)
    eldmcoss $p |- ( A e. V -> ( A e. dom ,~ R <-> E. u u R A ) ) $=
      ( ccoss cdm wcel ccnv cv wbr wex dmcoss3 eleq2i eldmcnv bitrid ) BCEFZGBC
      HFZGBDGAIBCJAKPQBCLMABCDNO $.
  $}

  ${
    $d A u $.  $d R u $.  $d V u $.
    $( Elementhood in the domain of cosets.  (Contributed by Peter Mazsa,
       28-Dec-2018.) $)
    eldmcoss2 $p |- ( A e. V -> ( A e. dom ,~ R <-> A ,~ R A ) ) $=
      ( vu wcel ccoss cdm cv wbr wex eldmcoss wa wb brcoss anidms exbii bitr4di
      pm4.24 bitr4d ) ACEZABFZGEDHABIZDJZAAUAIZDABCKTUDUBUBLZDJZUCTUDUFMDAABCCN
      OUBUEDUBRPQS $.
  $}

  ${
    $d A u $.  $d B u $.  $d R u $.  $d V u $.
    $( Elementhood in the domain of restricted cosets.  (Contributed by Peter
       Mazsa, 30-Dec-2018.) $)
    eldm1cossres $p |- ( B e. V ->
                         ( B e. dom ,~ ( R |` A ) <-> E. u e. A u R B ) ) $=
      ( wcel cres ccoss cdm cv wbr wex wrex eldmcoss brres exbidv bitrd bitr4di
      wa df-rex ) CEFZCDBGZHIFZAJZBFUDCDKZSZALZUEABMUAUCUDCUBKZALUGACUBENUAUHUF
      ABUDCDEOPQUEABTR $.
  $}

  ${
    $d A x $.  $d B x $.  $d R x $.  $d V x $.
    $( Elementhood in the domain of restricted cosets.  (Contributed by Peter
       Mazsa, 30-Dec-2018.) $)
    eldm1cossres2 $p |- ( B e. V ->
        ( B e. dom ,~ ( R |` A ) <-> E. x e. A B e. [ x ] R ) ) $=
      ( wcel cres ccoss cdm cv wbr wrex cec eldm1cossres elecALTV el2v1 rexbidv
      wb cvv bitr4d ) CEFZCDBGHIFAJZCDKZABLCUBDMFZABLABCDENUAUDUCABUAUDUCRAUBCD
      SEOPQT $.
  $}

  $( Lemma for the left side of the ~ refrelcoss3 reflexivity theorem.
     (Contributed by Peter Mazsa, 1-Apr-2019.) $)
  refrelcosslem $p |- A. x e. dom ,~ R x ,~ R x $=
    ( cv ccoss cdm wcel wral wbr ralel wb cvv eldmcoss2 elv ralbii mpbi ) ACZBD
    ZEZFZARGPPQHZARGARISTARSTJAPBKLMNO $.

  ${
    $d R x y $.
    $( The class of cosets by ` R ` is reflexive, see ~ dfrefrel3 .
       (Contributed by Peter Mazsa, 30-Jul-2019.) $)
    refrelcoss3 $p |-
        ( A. x e. dom ,~ R A. y e. ran ,~ R ( x = y -> x ,~ R y ) /\
          Rel ,~ R ) $=
      ( weq cv ccoss wbr wi crn wral cdm wrel refrelcosslem idinxpssinxp4 mpbir
      rncossdmcoss raleqi ralbii relcoss pm3.2i ) ABDAEZBECFZGHZBUBIZJZAUBKZJZU
      BLUGUCBUFJZAUFJZUIUAUAUBGAUFJACMABUFUBNOUEUHAUFUCBUDUFCPQROCST $.
  $}

  ${
    $d R x y $.
    $( The class of cosets by ` R ` is reflexive, see ~ dfrefrel2 .
       (Contributed by Peter Mazsa, 30-Jul-2019.) $)
    refrelcoss2 $p |- ( ( _I i^i ( dom ,~ R X. ran ,~ R ) ) C_ ,~ R /\
                        Rel ,~ R ) $=
      ( vx vy cid ccoss cdm crn cxp cin wss wrel wa weq cv wbr wral refrelcoss3
      wi idinxpss anbi1i mpbir ) DAEZFZUBGZHIUBJZUBKZLBCMBNCNUBORCUDPBUCPZUFLBC
      AQUEUGUFBCUCUDUBSTUA $.
  $}

  $( The class of cosets by ` R ` is symmetric, see ~ dfsymrel3 .  (Contributed
     by Peter Mazsa, 28-Mar-2019.)  (Revised by Peter Mazsa, 17-Sep-2021.) $)
  symrelcoss3 $p |- ( A. x A. y ( x ,~ R y -> y ,~ R x ) /\ Rel ,~ R ) $=
    ( cv ccoss wbr wi wal wrel wb brcosscnvcoss el2v biimpi gen2 relcoss pm3.2i
    cvv ) ADZBDZCEZFZSRTFZGZBHAHTIUCABUAUBUAUBJABRSCQQKLMNCOP $.

  ${
    $d R x y $.
    $( The class of cosets by ` R ` is symmetric, see ~ dfsymrel2 .
       (Contributed by Peter Mazsa, 27-Dec-2018.) $)
    symrelcoss2 $p |- ( `' ,~ R C_ ,~ R /\ Rel ,~ R ) $=
      ( vx vy ccoss ccnv wss wrel wa cv wbr wal symrelcoss3 cnvsym anbi1i mpbir
      wi ) ADZEQFZQGZHBIZCIZQJUATQJPCKBKZSHBCALRUBSBCQMNO $.
  $}

  $( Equivalent expressions for the class of cosets by ` R ` to be a subset of
     the identity class.  (Contributed by Peter Mazsa, 27-Jul-2021.) $)
  cossssid $p |- ( ,~ R C_ _I <->
                   ,~ R C_ ( _I i^i ( dom ,~ R X. ran ,~ R ) ) ) $=
    ( ccoss cid wss cdm crn cxp wceq iss2 wrel refrelcoss2 simpli eqss mpbiran2
    cin bitri ) ABZCDQCQEQFGOZHZQRDZQISTRQDZUAQJAKLQRMNP $.

  ${
    $d R u x y $.
    $( Equivalent expressions for the class of cosets by ` R ` to be a subset
       of the identity class.  (Contributed by Peter Mazsa, 10-Mar-2019.) $)
    cossssid2 $p |- ( ,~ R C_ _I <->
                      A. x A. y ( E. u ( u R x /\ u R y ) -> x = y ) ) $=
      ( ccoss cid wss weq copab cv wbr wa wex wi df-id sseq2i df-coss ssopab2bw
      wal sseq1i 3bitri ) DEZFGUBABHZABIZGCJZAJDKUEBJDKLCMZABIZUDGUFUCNBSASFUDU
      BABOPUBUGUDABCDQTUFUCABRUA $.
  $}

  ${
    $d R u x y $.
    $( Equivalent expressions for the class of cosets by ` R ` to be a subset
       of the identity class.  (Contributed by Peter Mazsa, 10-Mar-2019.) $)
    cossssid3 $p |- ( ,~ R C_ _I <->
                      A. u A. x A. y ( ( u R x /\ u R y ) -> x = y ) ) $=
      ( ccoss cid wss cv wbr wa wex weq wal cossssid2 19.23v albii alcom bitr3i
      wi 3bitri ) DEFGCHZAHDIUABHDIJZCKABLZSZBMZAMUBUCSZBMZCMZAMUGAMCMABCDNUEUH
      AUEUFCMZBMUHUIUDBUBUCCOPUFBCQRPUGACQT $.
  $}

  ${
    $d R u x y $.
    $( Equivalent expressions for the class of cosets by ` R ` to be a subset
       of the identity class.  (Contributed by Peter Mazsa, 31-Aug-2021.) $)
    cossssid4 $p |- ( ,~ R C_ _I <-> A. u E* x u R x ) $=
      ( vy ccoss cid wss cv wbr wa weq wal wmo cossssid3 breq2 mo4 albii bitr4i
      wi ) CEFGBHZAHZCIZTDHZCIZJADKSDLALZBLUBAMZBLADBCNUFUEBUBUDADUAUCTCOPQR $.
  $}

  ${
    $d R u x y $.
    $( Equivalent expressions for the class of cosets by ` R ` to be a subset
       of the identity class.  (Contributed by Peter Mazsa, 5-Sep-2021.) $)
    cossssid5 $p |- ( ,~ R C_ _I <->
                      A. x e. ran R A. y e. ran R
                        ( x = y \/ ( [ x ] `' R i^i [ y ] `' R ) = (/) ) ) $=
      ( vu ccoss cid wss cv wbr wmo wal wceq ccnv cec cin c0 crn wral cossssid4
      wo ineccnvmo2 bitr4i ) CEFGDHAHZCIAJDKUCBHZLUCCMZNUDUENOPLTBCQZRAUFRADCSA
      BDCUAUB $.
  $}

  ${
    $d A x $.  $d B x $.  $d R x $.  $d V x $.  $d W x $.
    $( ` A ` and ` B ` are cosets by converse ` R ` : a binary relation.
       (Contributed by Peter Mazsa, 23-Jan-2019.) $)
    brcosscnv $p |- ( ( A e. V /\ B e. W ) ->
                      ( A ,~ `' R B <-> E. x ( A R x /\ B R x ) ) ) $=
      ( wcel wa ccnv ccoss wbr cv wex brcoss cvv brcnvg el2v1 bi2anan9 exbidv
      wb bitrd ) BEGZCFGZHZBCDIZJKALZBUEKZUFCUEKZHZAMBUFDKZCUFDKZHZAMABCUEEFNUD
      UIULAUBUGUJUCUHUKUBUGUJTAUFBOEDPQUCUHUKTAUFCOFDPQRSUA $.
  $}

  ${
    $d A x $.  $d B x $.  $d R x $.  $d V x $.  $d W x $.
    $( ` A ` and ` B ` are cosets by converse ` R ` : a binary relation.
       (Contributed by Peter Mazsa, 12-Mar-2019.) $)
    brcosscnv2 $p |- ( ( A e. V /\ B e. W ) ->
       ( A ,~ `' R B <-> ( [ A ] R i^i [ B ] R ) =/= (/) ) ) $=
      ( vx wcel wa ccnv ccoss wbr cv wex cec cin c0 wne brcosscnv ecinn0 bitr4d
      ) ADGBEGHABCIJKAFLZCKBUACKHFMACNBCNOPQFABCDERFABCDEST $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d R x y $.  $d S x y $.  $d V x y $.
    $d W x y $.
    $( ` A ` and ` B ` are cosets by the converse range Cartesian product: a
       binary relation.  (Contributed by Peter Mazsa, 19-Apr-2020.)  (Revised
       by Peter Mazsa, 21-Sep-2021.) $)
    br1cosscnvxrn $p |- ( ( A e. V /\ B e. W ) ->
       ( A ,~ `' ( R |X. S ) B <-> ( A ,~ `' R B /\ A ,~ `' S B ) ) ) $=
      ( vx vy wcel wa cec cin c0 wne cv wbr wex ccnv ccoss copab cxrn ineqan12d
      ecxrn inopab eqtrdi opabbii neeq1d opabn0 exdistrv bitri bitrdi brcosscnv
      an4 brcosscnv2 anbi12d 3bitr4d ) AEIZBFIZJZACDUAZKZBUTKZLZMNZAGOZCPZBVECP
      ZJZGQZAHOZDPZBVJDPZJZHQZJZABUTRSPABCRSPZABDRSPZJUSVDVHVMJZGHTZMNZVOUSVCVS
      MUSVCVFVKJZVGVLJZJZGHTZVSUSVCWAGHTZWBGHTZLWDUQURVAWEVBWFGHACDEUCGHBCDFUCU
      BWAWBGHUDUEWCVRGHVFVKVGVLUMUFUEUGVTVRHQGQVOVRGHUHVHVMGHUIUJUKABUTEFUNUSVP
      VIVQVNGABCEFULHABDEFULUOUP $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( Cosets by the converse range Cartesian product.  (Contributed by Peter
       Mazsa, 19-Apr-2020.)  (Revised by Peter Mazsa, 21-Sep-2021.) $)
    1cosscnvxrn $p |- ,~ `' ( A |X. B ) = ( ,~ `' A i^i ,~ `' B ) $=
      ( vx vy cv cxrn ccnv ccoss wbr copab cin wa wb br1cosscnvxrn wrel relcoss
      cvv wceq dfrel4v mpbi el2v opabbii inopab eqtr4i ineq12i 3eqtr4i ) CEZDEZ
      ABFGZHZIZCDJZUGUHAGZHZIZCDJZUGUHBGZHZIZCDJZKZUJUNURKULUOUSLZCDJVAUKVBCDUK
      VBMCDUGUHABQQNUAUBUOUSCDUCUDUJOUJULRUIPCDUJSTUNUPURUTUNOUNUPRUMPCDUNSTURO
      URUTRUQPCDURSTUEUF $.
  $}

  ${
    $d R u v x $.
    $( Equivalent expressions for the class of cosets by the converse of ` R `
       to be a subset of the identity class.  (Contributed by Peter Mazsa,
       28-Jul-2021.) $)
    cosscnvssid3 $p |- ( ,~ `' R C_ _I <->
                         A. u A. v A. x ( ( u R x /\ v R x ) -> u = v ) ) $=
      ( ccnv ccoss cid wss cv wbr wa weq wi wal cossssid3 alrot3 wb brcnvg el2v
      cvv anbi12i imbi1i 3albii 3bitri ) DEZFGHAIZCIZUEJZUFBIZUEJZKZCBLZMZBNCNA
      NUMANBNCNUGUFDJZUIUFDJZKZULMZANBNCNCBAUEOUMACBPUMUQCBAUKUPULUHUNUJUOUHUNQ
      ACUFUGTTDRSUJUOQABUFUITTDRSUAUBUCUD $.
  $}

  ${
    $d R u x $.
    $( Equivalent expressions for the class of cosets by the converse of ` R `
       to be a subset of the identity class.  (Contributed by Peter Mazsa,
       31-Aug-2021.) $)
    cosscnvssid4 $p |- ( ,~ `' R C_ _I <-> A. x E* u u R x ) $=
      ( ccnv ccoss cid wss cv wbr wmo wal cossssid4 cvv brcnvg el2v mobii albii
      wb bitri ) CDZEFGAHZBHZTIZBJZAKUBUACIZBJZAKBATLUDUFAUCUEBUCUERABUAUBMMCNO
      PQS $.
  $}

  ${
    $d R u v x $.
    $( Equivalent expressions for the class of cosets by the converse of the
       relation ` R ` to be a subset of the identity class.  (Contributed by
       Peter Mazsa, 5-Sep-2021.) $)
    cosscnvssid5 $p |- ( ( ,~ `' R C_ _I /\ Rel R ) <->
       ( A. u e. dom R A. v e. dom R
           ( u = v \/ ( [ u ] R i^i [ v ] R ) = (/) ) /\
         Rel R ) ) $=
      ( vx ccnv ccoss cid wss wrel wa cv wbr wmo wal wceq cec cin c0 wo wral
      cdm cosscnvssid4 anbi1i inecmo3 bitr4i ) CEFGHZCIZJBKZDKCLBMDNZUGJUHAKZOU
      HCPUJCPQROSACUAZTBUKTUGJUFUIUGDBCUBUCDABCUDUE $.
  $}

  ${
    $d x y z $.
    $( Cosets by the empty set are the empty set.  (Contributed by Peter Mazsa,
       22-Oct-2019.) $)
    coss0 $p |- ,~ (/) = (/) $=
      ( vy vx vz c0 ccoss cv cec wcel wa wex copab dfcoss2 eleq2i anbi12i exbii
      ec0 19.9v bitri opabbii cvv cpr wss wne prnzg elv ss0b nemtbir prssg el2v
      wb mtbir opabf 3eqtri ) DEAFZBFZDGZHZCFZUPHZIZBJZACKUNDHZURDHZIZACKDACBDL
      VAVDACVAVDBJVDUTVDBUQVBUSVCUPDUNUOPZMUPDURVEMNOVDBQRSVDACVDUNURUAZDUBZVGV
      FDVFDUCAUNURTUDUEVFUFUGVDVGUJACUNURDTTUHUIUKULUM $.
  $}

  ${
    $d x y z $.
    $( Cosets by the identity relation are the identity relation.  (Contributed
       by Peter Mazsa, 16-Jan-2019.) $)
    cossid $p |- ,~ _I = _I $=
      ( vy vz vx weq copab cv cid wbr wa wex ccoss equvinv wb cvv ideqg anbi12i
      elv exbii bitr4i opabbii df-id df-coss 3eqtr4ri ) ABDZABECFZAFZGHZUEBFZGH
      ZIZCJZABEGGKUDUKABUDCADZCBDZIZCJUKABCLUJUNCUGULUIUMUGULMAUEUFNOQUIUMMBUEU
      HNOQPRSTABUAABCGUBUC $.
  $}

  $( Cosets by the converse identity relation are the identity relation.
     (Contributed by Peter Mazsa, 27-Sep-2021.) $)
  cosscnvid $p |- ,~ `' _I = _I $=
    ( cid ccnv ccoss cnvi cosseqi cossid eqtri ) ABZCACAHADEFG $.

  ${
    $d R u x $.  $d R u z $.  $d u x y $.  $d y z $.
    $( Sufficient condition for the transitivity of cosets by ` R ` .
       (Contributed by Peter Mazsa, 26-Dec-2018.) $)
    trcoss $p |- ( A. y E* u u R y ->
       A. x A. y A. z ( ( x ,~ R y /\ y ,~ R z ) -> x ,~ R z ) ) $=
      ( cv wbr wmo wal ccoss wa wi wex moantr cvv brcoss el2v anbi12i alrimiv
      wb 3imtr4g alimi ) DFZBFZEGZDHZBIAFZUDEJZGZUDCFZUHGZKZUGUJUHGZLZCIZBIAUFU
      OBUFUNCUFUCUGEGZUEKDMZUEUCUJEGZKDMZKUPURKDMZULUMUPUEURDNUIUQUKUSUIUQTABDU
      GUDEOOPQUKUSTBCDUDUJEOOPQRUMUTTACDUGUJEOOPQUASUBS $.
  $}

  $( Two ways of saying that the coset of ` A ` and the coset of ` C ` have the
     common element ` B ` .  (Contributed by Peter Mazsa, 15-Oct-2021.) $)
  eleccossin $p |- ( ( B e. V /\ C e. W ) ->
      ( B e. ( [ A ] ,~ R i^i [ C ] ,~ R ) <-> ( A ,~ R B /\ B ,~ R C ) ) ) $=
    ( wcel wa ccoss cec cin wbr elin wrel relcoss relelec ax-mp anbi12i bitri
    wb brcosscnvcoss anbi2d bitr4id ) BEGCFGHZBADIZJZCUEJZKGZABUELZCBUELZHZUIBC
    UELZHUHBUFGZBUGGZHUKBUFUGMUMUIUNUJUENZUMUITDOZBAUEPQUOUNUJTUPBCUEPQRSUDULUJ
    UIBCDEFUAUBUC $.

  ${
    $d R y $.  $d x y $.  $d y z $.
    $( Equivalent expressions for the transitivity of cosets by ` R ` .
       (Contributed by Peter Mazsa, 4-Jul-2020.)  (Revised by Peter Mazsa,
       16-Oct-2021.) $)
    trcoss2 $p |-
       ( A. x A. y A. z ( ( x ,~ R y /\ y ,~ R z ) -> x ,~ R z ) <->
         A. x A. z
           ( ( [ x ] ,~ R i^i [ z ] ,~ R ) =/= (/) ->
             ( [ x ] `' R i^i [ z ] `' R ) =/= (/) ) ) $=
      ( cv ccoss wbr wa wi wal cec cin c0 wne ccnv alcom albii wb cvv el2v wcel
      wex 19.23v eleccossin bicomi brcoss3 imbi12i imbi1i 3bitr4i 2albii bitri
      n0 ) AEZBEZDFZGUNCEZUOGHZUMUPUOGZIZCJBJZAJUSBJZCJZAJUMUOKUPUOKLZMNZUMDOZK
      UPVEKLMNZIZCJAJUTVBAUSBCPQVAVGACUNVCUAZVFIZBJVHBUBZVFIVAVGVHVFBUCUSVIBUQV
      HURVFVHUQVHUQRBCUMUNUPDSSUDTUEURVFRACUMUPDSSUFTUGQVDVJVFBVCULUHUIUJUK $.
  $}

  $( Cosets of sets are elements of the relations class.  Implies
     ` |- ( R e. Rels -> ,~ R e. Rels ) ` .  (Contributed by Peter Mazsa,
     25-Aug-2021.) $)
  cosselrels $p |- ( A e. V -> ,~ A e. Rels ) $=
    ( wcel ccoss cvv crels cossex wrel relcoss elrelsrel mpbiri syl ) ABCADZECZ
    MFCZABGNOMHAIMEJKL $.

  $( The converse of a set is an element of the class of relations.
     (Contributed by Peter Mazsa, 18-Aug-2019.) $)
  cnvelrels $p |- ( A e. V -> `' A e. Rels ) $=
    ( wcel ccnv crels wrel relcnv cvv wb cnvexg elrelsrel syl mpbiri ) ABCZADZE
    CZOFZAGNOHCPQIABJOHKLM $.

  $( Cosets of converse sets are elements of the relations class.  (Contributed
     by Peter Mazsa, 31-Aug-2021.) $)
  cosscnvelrels $p |- ( A e. V -> ,~ `' A e. Rels ) $=
    ( wcel ccnv crels ccoss cnvelrels cosselrels syl ) ABCADZECJFECABGJEHI $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Subset relations
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y $.
    $( Define the subsets class or the class of subset relations.  Similar to
       definitions of epsilon relation ( ~ df-eprel ) and identity relation
       ( ~ df-id ) classes.  Subset relation class and Scott Fenton's subset
       class ~ df-sset are the same: ` _S = SSet ` (compare ~ dfssr2 with
       ~ df-sset ), the only reason we do not use ~ dfssr2 as the base
       definition of the subsets class is the way we defined the epsilon
       relation and the identity relation classes.

       The binary relation on the class of subsets and the subclass
       relationship ( ~ df-ss ) are the same, that is,
       ` ( A _S B <-> A C_ B ) ` when ` B ` is a set, see ~ brssr .  Yet in
       general we use the subclass relation ` A C_ B ` both for classes and for
       sets, see the comment of ~ df-ss .  The only exception (aside from
       directly investigating the class ` _S ` e.g. in ~ relssr or in
       ~ extssr ) is when we have a specific purpose with its usage, like in
       case of ~ df-refs versus ~ df-cnvrefs , where we need ` _S ` to define
       the class of reflexive sets in order to be able to define the class of
       converse reflexive sets with the help of the converse of ` _S ` .

       The subsets class ` _S ` has another place in set.mm as well: if we
       define extensional relation based on the common property in ~ extid ,
       ~ extep and ~ extssr , then "extrelssr" " |- ExtRel ` _S ` " is a
       theorem along with "extrelep" " |- ExtRel ` _E ` " and "extrelid" " |-
       ExtRel ` _I ` " .  (Contributed by Peter Mazsa, 25-Jul-2019.) $)
    df-ssr $a |- _S = { <. x , y >. | x C_ y } $.
  $}

  ${
    $d x y z $.
    $( Alternate definition of the subset relation.  (Contributed by Peter
       Mazsa, 9-Aug-2021.) $)
    dfssr2 $p |- _S = ( ( _V X. _V ) \ ran ( _E |X. ( _V \ _E ) ) ) $=
      ( vz vx vy cv cep wbr cvv cdif wa wex wn copab wss cxp cxrn crn cssr wcel
      epel brvdif xchbinx anbi12i exbii notbii bitr4i opabbii difeq2i vvdifopab
      dfss6 rnxrn eqtri df-ssr 3eqtr4ri ) ADZBDZEFZUNCDZGEHZFZIZAJZKZBCLZUOUQMZ
      BCLGGNZEUROPZHZQVBVDBCVBUNUORZUNUQRZKZIZAJZKVDVAVLUTVKAUPVHUSVJBUNSUSUNUQ
      EFVIUNUQETCUNSUAUBUCUDAUOUQUIUEUFVGVEVABCLZHVCVFVMVEBCAEURUJUGVABCUHUKBCU
      LUM $.
  $}

  ${
    $d x y $.
    $( The subset relation is a relation.  (Contributed by Peter Mazsa,
       1-Aug-2019.) $)
    relssr $p |- Rel _S $=
      ( vx vy cv wss cssr df-ssr relopabiv ) ACBCDABEABFG $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( The subset relation and subclass relationship ( ~ df-ss ) are the same,
       that is, ` ( A _S B <-> A C_ B ) ` when ` B ` is a set.  (Contributed by
       Peter Mazsa, 31-Jul-2019.) $)
    brssr $p |- ( B e. V -> ( A _S B <-> A C_ B ) ) $=
      ( vx vy wcel wbr wss cvv wa relssr brrelex1i adantl simpl jca ssexg simpr
      cssr ancoms cv sseq1 sseq2 df-ssr brabg pm5.21nd ) BCFZABRGZABHZAIFZUFJZU
      FUGJUIUFUGUIUFABRKLMUFUGNOUHUFUJUHUFJUIUFABCPUHUFQOSDTZETZHAULHUHDEABICRU
      KAULUAULBAUBDEUCUDUE $.
  $}

  $( Any set is a subset of itself.  (Contributed by Peter Mazsa,
     1-Aug-2019.) $)
  brssrid $p |- ( A e. V -> A _S A ) $=
    ( wcel cssr wbr wss ssid brssr mpbiri ) ABCAADEAAFAGAABHI $.

  $( Two ways of expressing set existence.  (Contributed by Peter Mazsa,
     1-Aug-2019.) $)
  issetssr $p |- ( A e. _V <-> A _S A ) $=
    ( cvv wcel cssr wbr brssrid relssr brrelex1i impbii ) ABCAADEABFAADGHI $.

  $( Restricted subset binary relation.  (Contributed by Peter Mazsa,
     25-Nov-2019.) $)
  brssrres $p |- ( C e. V ->
                   ( B ( _S |` A ) C <-> ( B e. A /\ B C_ C ) ) ) $=
    ( wcel cssr cres wbr wa wss brres brssr anbi2d bitrd ) CDEZBCFAGHBAEZBCFHZI
    PBCJZIABCFDKOQRPBCDLMN $.

  $( Restricted converse subset binary relation.  (Contributed by Peter Mazsa,
     25-Nov-2019.) $)
  br1cnvssrres $p |- ( B e. V ->
                       ( B `' ( _S |` A ) C <-> ( C e. A /\ C C_ B ) ) ) $=
    ( cssr cres ccnv wbr wcel wss wa relres relbrcnv brssrres bitrid ) BCEAFZGH
    CBPHBDICAICBJKBCPEALMACBDNO $.

  $( The converse of a subset relation swaps arguments.  (Contributed by Peter
     Mazsa, 1-Aug-2019.) $)
  brcnvssr $p |- ( A e. V -> ( A `' _S B <-> B C_ A ) ) $=
    ( cssr ccnv wbr wcel wss relssr relbrcnv brssr bitrid ) ABDEFBADFACGBAHABDI
    JBACKL $.

  $( Any set is a converse subset of itself.  (Contributed by Peter Mazsa,
     9-Jun-2021.) $)
  brcnvssrid $p |- ( A e. V -> A `' _S A ) $=
    ( wcel cssr ccnv wbr wss ssid brcnvssr mpbiri ) ABCAADEFAAGAHAABIJ $.

  ${
    $d A u $.  $d B u $.  $d C u $.  $d D u $.  $d E u $.  $d R u $.  $d V u $.
    $d W u $.  $d X u $.  $d Y u $.
    $( ` <. B , C >. ` and ` <. D , E >. ` are cosets by range Cartesian
       product with restricted converse subsets class: a binary relation.
       (Contributed by Peter Mazsa, 9-Jun-2021.) $)
    br1cossxrncnvssrres $p |-
        ( ( ( B e. V /\ C e. W ) /\ ( D e. X /\ E e. Y ) ) ->
          ( <. B , C >. ,~ ( R |X. ( `' _S |` A ) ) <. D , E >. <->
            E. u e. A ( ( C C_ u /\ u R B ) /\ ( E C_ u /\ u R D ) ) ) ) $=
      ( wcel wa cop wbr wrex wss wb cvv brcnvssr cssr ccnv cv br1cossxrnres elv
      cres cxrn ccoss anbi1i anbi12i rexbii bitrdi ) CHLDILMEJLGKLMMCDNEGNFUAUB
      ZBUFUGUHOAUCZDUMOZUNCFOZMZUNGUMOZUNEFOZMZMZABPDUNQZUPMZGUNQZUSMZMZABPABCD
      EFUMGHIJKUDVAVFABUQVCUTVEUOVBUPUOVBRAUNDSTUEUIURVDUSURVDRAUNGSTUEUIUJUKUL
      $.
  $}

  ${
    $d A x $.  $d B x $.  $d V x $.  $d W x $.
    $( Property of subset relation, see also ~ extid , ~ extep and the comment
       of ~ df-ssr .  (Contributed by Peter Mazsa, 10-Jul-2019.) $)
    extssr $p |- ( ( A e. V /\ B e. W ) ->
                   ( [ A ] `' _S = [ B ] `' _S <-> A = B ) ) $=
      ( vx wcel wa cv cssr wbr wb wal wss ccnv cec brssr bi2bian9 albidv relssr
      wceq wrel releccnveq mp2an ssext 3bitr4g ) ACFZBDFZGZEHZAIJZUIBIJZKZELZUI
      AMZUIBMZKZELAINZOBUQOTZABTUHULUPEUFUJUNUGUKUOUIACPUIBDPQRIUAZUSURUMKSSEAB
      IIUBUCEABUDUE $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Reflexivity
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define the class of all reflexive sets.  It is used only by ~ df-refrels .
     We use subset relation ` _S ` ( ~ df-ssr ) here to be able to define
     converse reflexivity ( ~ df-cnvrefs ), see also the comment of ~ df-ssr .
     The elements of this class are not necessarily relations (versus
     ~ df-refrels ).

     Note the similarity of Definitions ~ df-refs , ~ df-syms and ~ df-trs ,
     cf. comments of ~ dfrefrels2 .  (Contributed by Peter Mazsa,
     19-Jul-2019.) $)
  df-refs $a |- Refs =
       { x | ( _I i^i ( dom x X. ran x ) ) _S ( x i^i ( dom x X. ran x ) ) } $.

  $( Define the class of reflexive relations.  This is practically ~ dfrefrels2
     (which reveals that ` RefRels ` can not include proper classes like ` _I `
     as is elements, see comments of ~ dfrefrels2 ).

     Another alternative definition is ~ dfrefrels3 .  The element of this
     class and the reflexive relation predicate ( ~ df-refrel ) are the same,
     that is, ` ( R e. RefRels <-> RefRel R ) ` when ` A ` is a set, see
     ~ elrefrelsrel .

     This definition is similar to the definitions of the classes of symmetric
     ( ~ df-symrels ) and transitive ( ~ df-trrels ) relations.  (Contributed
     by Peter Mazsa, 7-Jul-2019.) $)
  df-refrels $a |- RefRels = ( Refs i^i Rels ) $.

  $( Define the reflexive relation predicate.  (Read: ` R ` is a reflexive
     relation.)  This is a surprising definition, see the comment of
     ~ dfrefrel3 .  Alternate definitions are ~ dfrefrel2 and ~ dfrefrel3 .
     For sets, being an element of the class of reflexive relations
     ( ~ df-refrels ) is equivalent to satisfying the reflexive relation
     predicate, that is ` ( R e. RefRels <-> RefRel R ) ` when ` R ` is a set,
     see ~ elrefrelsrel .  (Contributed by Peter Mazsa, 16-Jul-2021.) $)
  df-refrel $a |- ( RefRel R <->
      ( ( _I i^i ( dom R X. ran R ) ) C_ ( R i^i ( dom R X. ran R ) ) /\
        Rel R ) ) $.

  $( Alternate definition of the class of reflexive relations.  This is a 0-ary
     class constant, which is recommended for definitions (see the 1.
     Guideline at ~ https://us.metamath.org/ileuni/mathbox.html ).  Proper
     classes (like ` _I ` , see ~ iprc ) are not elements of this (or any)
     class: if a class is an element of another class, it is not a proper class
     but a set, see ~ elex .  So if we use 0-ary constant classes as our main
     definitions, they are valid only for sets, not for proper classes.  For
     proper classes we use predicate-type definitions like ~ df-refrel .  See
     also the comment of ~ df-rels .

     Note that while elementhood in the class of relations cancels restriction
     of ` r ` in ~ dfrefrels2 , it keeps restriction of ` _I ` : this is why
     the very similar definitions ~ df-refs , ~ df-syms and ~ df-trs diverge
     when we switch from (general) sets to relations in ~ dfrefrels2 ,
     ~ dfsymrels2 and ~ dftrrels2 .  (Contributed by Peter Mazsa,
     20-Jul-2019.) $)
  dfrefrels2 $p |- RefRels =
                   { r e. Rels | ( _I i^i ( dom r X. ran r ) ) C_ r } $=
    ( cid cdm crn cxp cin cssr wbr crefrels crefs crels df-refrels df-refs wcel
    cv wss cvv wb inex1g elv brssr ax-mp elrels6 biimpi sseq2d bitrid abeqinbi
    wceq ) BAOZCUIDEZFZUIUJFZGHZUKUIPZAIJKLAMUMUKULPZUIKNZUNULQNZUMUORUQAUIUJQS
    TUKULQUAUBUPULUIUKUPULUIUHZUPURRAUIQUCTUDUEUFUG $.

  ${
    $d r x y $.
    $( Alternate definition of the class of reflexive relations.  (Contributed
       by Peter Mazsa, 8-Jul-2019.) $)
    dfrefrels3 $p |- RefRels =
        { r e. Rels | A. x e. dom r A. y e. ran r ( x = y -> x r y ) } $=
      ( cid cv cdm crn cxp cin wss weq wbr wi wral crefrels dfrefrels2 idinxpss
      crels rabbieq ) DCEZFZTGZHITJABKAEBETLMBUBNAUANCROCPABUAUBTQS $.
  $}

  $( Alternate definition of the reflexive relation predicate.  (Contributed by
     Peter Mazsa, 25-Jul-2021.) $)
  dfrefrel2 $p |- ( RefRel R <->
                    ( ( _I i^i ( dom R X. ran R ) ) C_ R /\ Rel R ) ) $=
    ( wrefrel cid cdm crn cxp cin wrel wa df-refrel wceq dfrel6 biimpi pm5.32ri
    wss sseq2d bitri ) ABCADAEFZGZARGZOZAHZISAOZUBIAJUBUAUCUBTASUBTAKALMPNQ $.

  ${
    $d R x y $.
    $( Alternate definition of the reflexive relation predicate.  A relation is
       reflexive iff: for all elements on its domain and range, if an element
       of its domain is the same as an element of its range, then there is the
       relation between them.

       Note that this is definitely not the definition we are accustomed to,
       like e.g. ~ idref / ~ idrefALT or ~ df-reflexive
       ` |- ( R Reflexive A <-> ( R C_ ( A X. A ) /\ A. x e. A x R x ) ) ` .
       It turns out that the not-surprising definition which contains
       ` A. x e. dom r x r x ` needs symmetry as well, see ~ refsymrels3 .
       Only when this symmetry condition holds, like in case of equivalence
       relations, see ~ dfeqvrels3 , can we write the traditional form
       ` A. x e. dom r x r x ` for reflexive relations.  For the special case
       with square Cartesian product when the two forms are equivalent see
       ~ idinxpssinxp4 where
       ` |- ( A. x e. A A. y e. A ( x = y -> x R y ) <-> A. x e. A x R x ) ` .
       See also similar definition of the converse reflexive relations class
       ~ dfcnvrefrel3 .  (Contributed by Peter Mazsa, 8-Jul-2019.) $)
    dfrefrel3 $p |- ( RefRel R <->
        ( A. x e. dom R A. y e. ran R ( x = y -> x R y ) /\ Rel R ) ) $=
      ( wrefrel cid cdm crn cxp cin wss wrel wa weq wbr wral dfrefrel2 idinxpss
      cv wi anbi1i bitri ) CDECFZCGZHICJZCKZLABMARBRCNSBUCOAUBOZUELCPUDUFUEABUB
      UCCQTUA $.
  $}

  ${
    $d R x $.
    $( Alternate definition of the reflexive relation predicate.  (Contributed
       by Peter Mazsa, 12-Dec-2023.) $)
    dfrefrel5 $p |- ( RefRel R <->
        ( A. x e. ( dom R i^i ran R ) x R x /\ Rel R ) ) $=
      ( wrefrel cid cdm crn cxp cin wss wrel cv wbr wral dfrefrel2 ref5 bianbi
      ) BCDBEZBFZGHBIBJAKZSBLAQRHMBNAQRBOP $.
  $}

  ${
    $d R r $.
    $( Element of the class of reflexive relations.  (Contributed by Peter
       Mazsa, 23-Jul-2019.) $)
    elrefrels2 $p |- ( R e. RefRels <->
        ( ( _I i^i ( dom R X. ran R ) ) C_ R /\ R e. Rels ) ) $=
      ( vr cid cdm crn cxp cin crels crefrels dfrefrels2 wceq dmeq rneq xpeq12d
      cv wss ineq2d id sseq12d rabeqel ) CBOZDZUAEZFZGZUAPCADZAEZFZGZAPBHIABJUA
      AKZUEUIUAAUJUDUHCUJUBUFUCUGUAALUAAMNQUJRST $.
  $}

  ${
    $d R r x y $.
    $( Element of the class of reflexive relations.  (Contributed by Peter
       Mazsa, 23-Jul-2019.) $)
    elrefrels3 $p |- ( R e. RefRels <->
        ( A. x e. dom R A. y e. ran R ( x = y -> x R y ) /\ R e. Rels ) ) $=
      ( vr cv wceq wbr wi crn wral cdm crels crefrels dfrefrels3 dmeq rneq breq
      imbi2d raleqbidv rabeqel ) AEZBEZFZUAUBDEZGZHZBUDIZJZAUDKZJUCUAUBCGZHZBCI
      ZJZACKZJDLMCABDNUDCFZUHUMAUIUNUDCOUOUFUKBUGULUDCPUOUEUJUCUAUBUDCQRSST $.
  $}

  $( For sets, being an element of the class of reflexive relations
     ( ~ df-refrels ) is equivalent to satisfying the reflexive relation
     predicate.  (Contributed by Peter Mazsa, 25-Jul-2021.) $)
  elrefrelsrel $p |- ( R e. V -> ( R e. RefRels <-> RefRel R ) ) $=
    ( wcel cid cdm crn cxp cin wss crels wrel crefrels wrefrel elrelsrel anbi2d
    wa elrefrels2 dfrefrel2 3bitr4g ) ABCZDAEAFGHAIZAJCZPUAAKZPALCAMTUBUCUAABNO
    AQARS $.

  $( Equality theorem for reflexive relation.  (Contributed by Peter Mazsa,
     15-Apr-2019.)  (Revised by Peter Mazsa, 23-Sep-2021.) $)
  refreleq $p |- ( R = S -> ( RefRel R <-> RefRel S ) ) $=
    ( wceq cid cdm crn cxp cin wrel wa wrefrel dmeq rneq xpeq12d ineq2d sseq12d
    wss id releq dfrefrel2 anbi12d 3bitr4g ) ABCZDAEZAFZGZHZAQZAIZJDBEZBFZGZHZB
    QZBIZJAKBKUCUHUNUIUOUCUGUMABUCUFULDUCUDUJUEUKABLABMNOUCRPABSUAATBTUB $.

  $( Identity relation is reflexive.  (Contributed by Peter Mazsa,
     25-Jul-2021.) $)
  refrelid $p |- RefRel _I $=
    ( cid wrefrel cdm crn cxp cin wss wrel ssid reli df-refrel mpbir2an ) ABAAC
    ADEFZMGAHMIJAKL $.

  $( The class of cosets by ` R ` is reflexive.  (Contributed by Peter Mazsa,
     4-Jul-2020.) $)
  refrelcoss $p |- RefRel ,~ R $=
    ( ccoss wrefrel cid cdm crn cxp cin wss wrel wa refrelcoss2 dfrefrel2 mpbir
    ) ABZCDOEOFGHOIOJKALOMN $.

  ${
    $d A x $.  $d R x $.  $d V x $.
    $( Any class ' R ' restricted to the singleton of the set ' A ' (see
       ~ ressn2 ) is reflexive.  (Contributed by Peter Mazsa, 12-Jun-2024.) $)
    refrelressn $p |- ( A e. V -> RefRel ( R |` { A } ) ) $=
      ( vx wcel cv csn cres wbr cdm crn cin wral wrel refressn relres dfrefrel5
      wrefrel sylanblrc ) ACEDFZTBAGZHZIDUBJUBKLMUBNUBRDABCOBUAPDUBQS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Converse reflexivity
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define the class of all converse reflexive sets, see the comment of
     ~ df-ssr .  It is used only by ~ df-cnvrefrels .  (Contributed by Peter
     Mazsa, 22-Jul-2019.) $)
  df-cnvrefs $a |- CnvRefs =
    { x | ( _I i^i ( dom x X. ran x ) ) `' _S ( x i^i ( dom x X. ran x ) ) } $.

  $( Define the class of converse reflexive relations.  This is practically
     ~ dfcnvrefrels2 (which uses the traditional subclass relation ` C_ ` ) :
     we use converse subset relation ( ~ brcnvssr ) here to ensure the
     comparability to the definitions of the classes of all reflexive
     ( ~ df-ref ), symmetric ( ~ df-syms ) and transitive ( ~ df-trs ) sets.

     We use this concept to define functions ( ~ df-funsALTV , ~ df-funALTV )
     and disjoints ( ~ df-disjs , ~ df-disjALTV ).

     For sets, being an element of the class of converse reflexive relations is
     equivalent to satisfying the converse reflexive relation predicate, see
     ~ elcnvrefrelsrel .  Alternate definitions are ~ dfcnvrefrels2 and
     ~ dfcnvrefrels3 .  (Contributed by Peter Mazsa, 7-Jul-2019.) $)
  df-cnvrefrels $a |- CnvRefRels = ( CnvRefs i^i Rels ) $.

  $( Define the converse reflexive relation predicate (read: ` R ` is a
     converse reflexive relation), see also the comment of ~ dfcnvrefrel3 .
     Alternate definitions are ~ dfcnvrefrel2 and ~ dfcnvrefrel3 .
     (Contributed by Peter Mazsa, 16-Jul-2021.) $)
  df-cnvrefrel $a |- ( CnvRefRel R <->
      ( ( R i^i ( dom R X. ran R ) ) C_ ( _I i^i ( dom R X. ran R ) ) /\
        Rel R ) ) $.

  $( Alternate definition of the class of converse reflexive relations.  See
     the comment of ~ dfrefrels2 .  (Contributed by Peter Mazsa,
     21-Jul-2021.) $)
  dfcnvrefrels2 $p |- CnvRefRels =
                      { r e. Rels | r C_ ( _I i^i ( dom r X. ran r ) ) } $=
    ( cid cv cdm crn cxp cin cssr ccnv ccnvrefrels ccnvrefs crels df-cnvrefrels
    wbr wss df-cnvrefs wcel cvv wb elv dmexg rnexg xpex inex2g brcnvssr elrels6
    mp2b wceq biimpi sseq1d bitrid abeqinbi ) BACZDZUMEZFZGZUMUPGZHINZUMUQOZAJK
    LMAPUSURUQOZUMLQZUTUPRQUQRQUSVASUNUOUNRQAUMRUATUORQAUMRUBTUCUPBRUDUQURRUEUG
    VBURUMUQVBURUMUHZVBVCSAUMRUFTUIUJUKUL $.

  ${
    $d r x y $.
    $( Alternate definition of the class of converse reflexive relations.
       (Contributed by Peter Mazsa, 22-Jul-2019.) $)
    dfcnvrefrels3 $p |- CnvRefRels =
        { r e. Rels | A. x e. dom r A. y e. ran r ( x r y -> x = y ) } $=
      ( cid cv cdm crn cxp cin cssr ccnv wbr wceq wi wral crels ccnvrefrels cvv
      wcel elv ccnvrefs df-cnvrefrels df-cnvrefs abeqin wss wb dmexg rnexg xpex
      inex2g brcnvssr mp2b inxpssidinxp bitri rabbieq ) DCEZFZUPGZHZIZUPUSIZJKL
      ZAEZBEZUPLVCVDMNBUROAUQOZCPQVBCQUAPUBCUCUDVBVAUTUEZVEUSRSUTRSVBVFUFUQURUQ
      RSCUPRUGTURRSCUPRUHTUIUSDRUJUTVARUKULABUQURUPUMUNUO $.
  $}

  $( Alternate definition of the converse reflexive relation predicate.
     (Contributed by Peter Mazsa, 24-Jul-2019.) $)
  dfcnvrefrel2 $p |- ( CnvRefRel R <->
      ( R C_ ( _I i^i ( dom R X. ran R ) ) /\ Rel R ) ) $=
    ( wcnvrefrel cdm crn cxp cin cid wss wrel df-cnvrefrel dfrel6 biimpi sseq1d
    wa wceq pm5.32ri bitri ) ABAACADEZFZGRFZHZAIZNATHZUBNAJUBUAUCUBSATUBSAOAKLM
    PQ $.

  ${
    $d R x y $.
    $( Alternate definition of the converse reflexive relation predicate.  A
       relation is converse reflexive iff: for all elements on its domain and
       range, if for an element of its domain and for an element of its range
       there is the relation between them, then the two elements are the same,
       cf. the comment of ~ dfrefrel3 .  (Contributed by Peter Mazsa,
       25-Jul-2021.) $)
    dfcnvrefrel3 $p |- ( CnvRefRel R <->
        ( A. x e. dom R A. y e. ran R ( x R y -> x = y ) /\ Rel R ) ) $=
      ( wcnvrefrel cdm crn cxp cin cid wss wrel wa cv wbr weq wral df-cnvrefrel
      wi inxpssidinxp anbi1i bitri ) CDCCEZCFZGZHIUDHJZCKZLAMBMCNABORBUCPAUBPZU
      FLCQUEUGUFABUBUCCSTUA $.
  $}

  $( Alternate definition of the converse reflexive relation predicate.
     (Contributed by Peter Mazsa, 25-May-2024.) $)
  dfcnvrefrel4 $p |- ( CnvRefRel R <-> ( R C_ _I /\ Rel R ) ) $=
    ( wcnvrefrel cdm crn cxp cin cid wss wrel df-cnvrefrel cnvref4 bianim ) ABA
    ACADEZFGMFHAIAGHAJAGKL $.

  ${
    $d R x y $.
    $( Alternate definition of the converse reflexive relation predicate.
       (Contributed by Peter Mazsa, 25-May-2024.) $)
    dfcnvrefrel5 $p |- ( CnvRefRel R <->
                         ( A. x A. y ( x R y -> x = y ) /\ Rel R ) ) $=
      ( wcnvrefrel cid wss wrel cv wbr wceq wi wal dfcnvrefrel4 cnvref5 bianim
      ) CDCEFCGAHZBHZCIPQJKBLALCMABCNO $.
  $}

  ${
    $d R r $.
    $( Element of the class of converse reflexive relations.  (Contributed by
       Peter Mazsa, 25-Jul-2019.) $)
    elcnvrefrels2 $p |- ( R e. CnvRefRels <->
        ( R C_ ( _I i^i ( dom R X. ran R ) ) /\ R e. Rels ) ) $=
      ( vr cv cid cdm crn cxp cin wss crels ccnvrefrels dfcnvrefrels2 wceq dmeq
      id rneq xpeq12d ineq2d sseq12d rabeqel ) BCZDUAEZUAFZGZHZIADAEZAFZGZHZIBJ
      KABLUAAMZUAAUEUIUJOUJUDUHDUJUBUFUCUGUAANUAAPQRST $.
  $}

  ${
    $d R r x y $.
    $( Element of the class of converse reflexive relations.  (Contributed by
       Peter Mazsa, 30-Aug-2021.) $)
    elcnvrefrels3 $p |- ( R e. CnvRefRels <->
        ( A. x e. dom R A. y e. ran R ( x R y -> x = y ) /\ R e. Rels ) ) $=
      ( vr cv wbr wceq wi crn wral cdm ccnvrefrels dfcnvrefrels3 dmeq rneq breq
      crels imbi1d raleqbidv rabeqel ) AEZBEZDEZFZUAUBGZHZBUCIZJZAUCKZJUAUBCFZU
      EHZBCIZJZACKZJDQLCABDMUCCGZUHUMAUIUNUCCNUOUFUKBUGULUCCOUOUDUJUEUAUBUCCPRS
      ST $.
  $}

  $( For sets, being an element of the class of converse reflexive relations
     ( ~ df-cnvrefrels ) is equivalent to satisfying the converse reflexive
     relation predicate.  (Contributed by Peter Mazsa, 25-Jul-2021.) $)
  elcnvrefrelsrel $p |- ( R e. V -> ( R e. CnvRefRels <-> CnvRefRel R ) ) $=
    ( wcel cid cdm crn cxp cin crels wa ccnvrefrels wcnvrefrel elrelsrel anbi2d
    wss wrel elcnvrefrels2 dfcnvrefrel2 3bitr4g ) ABCZADAEAFGHOZAICZJUAAPZJAKCA
    LTUBUCUAABMNAQARS $.

  $( Necessary and sufficient condition for a coset relation to be a converse
     reflexive relation.  (Contributed by Peter Mazsa, 27-Jul-2021.) $)
  cnvrefrelcoss2 $p |- ( CnvRefRel ,~ R <-> ,~ R C_ _I ) $=
    ( wcnvrefrel cid cdm crn cxp cin wss relcoss dfcnvrefrel2 mpbiran2 cossssid
    ccoss wrel bitr4i ) AMZBZPCPDPEFGHZPCHQRPNAIPJKALO $.

  $( Necessary and sufficient condition for a coset relation to be an element
     of the converse reflexive relation class.  (Contributed by Peter Mazsa,
     25-Aug-2021.) $)
  cosselcnvrefrels2 $p |- ( ,~ R e. CnvRefRels <->
                            ( ,~ R C_ _I /\ ,~ R e. Rels ) ) $=
    ( ccoss ccnvrefrels cid cdm crn cxp cin wss crels wa elcnvrefrels2 cossssid
    wcel anbi1i bitr4i ) ABZCNQDQEQFGHIZQJNZKQDIZSKQLTRSAMOP $.

  ${
    $d R u x y $.
    $( Necessary and sufficient condition for a coset relation to be an element
       of the converse reflexive relation class.  (Contributed by Peter Mazsa,
       30-Aug-2021.) $)
    cosselcnvrefrels3 $p |- ( ,~ R e. CnvRefRels <->
        ( A. u A. x A. y ( ( u R x /\ u R y ) -> x = y ) /\
          ,~ R e. Rels ) ) $=
      ( ccoss ccnvrefrels wcel cid wss crels wa cv wbr wi wal cosselcnvrefrels2
      wceq cossssid3 anbi1i bitri ) DEZFGUAHIZUAJGZKCLZALZDMUDBLZDMKUEUFQNBOAOC
      OZUCKDPUBUGUCABCDRST $.
  $}

  ${
    $d R u x $.
    $( Necessary and sufficient condition for a coset relation to be an element
       of the converse reflexive relation class.  (Contributed by Peter Mazsa,
       31-Aug-2021.) $)
    cosselcnvrefrels4 $p |- ( ,~ R e. CnvRefRels <->
                              ( A. u E* x u R x /\ ,~ R e. Rels ) ) $=
      ( ccoss ccnvrefrels wcel cid wss crels wa wbr cosselcnvrefrels2 cossssid4
      cv wmo wal anbi1i bitri ) CDZEFSGHZSIFZJBNANCKAOBPZUAJCLTUBUAABCMQR $.
  $}

  ${
    $d R x y $.
    $( Necessary and sufficient condition for a coset relation to be an element
       of the converse reflexive relation class.  (Contributed by Peter Mazsa,
       5-Sep-2021.) $)
    cosselcnvrefrels5 $p |- ( ,~ R e. CnvRefRels <->
        ( A. x e. ran R A. y e. ran R
          ( x = y \/ ( [ x ] `' R i^i [ y ] `' R ) = (/) ) /\
          ,~ R e. Rels ) ) $=
      ( ccoss ccnvrefrels wcel cid wss crels wa cv wceq ccnv cec cin c0 wo wral
      crn cosselcnvrefrels2 cossssid5 anbi1i bitri ) CDZEFUDGHZUDIFZJAKZBKZLUGC
      MZNUHUINOPLQBCSZRAUJRZUFJCTUEUKUFABCUAUBUC $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Symmetry
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define the class of all symmetric sets.  It is used only by ~ df-symrels .

     Note the similarity of Definitions ~ df-refs , ~ df-syms and ~ df-trs ,
     cf. the comment of ~ dfrefrels2 .  (Contributed by Peter Mazsa,
     19-Jul-2019.) $)
  df-syms $a |- Syms =
    { x | `' ( x i^i ( dom x X. ran x ) ) _S ( x i^i ( dom x X. ran x ) ) } $.

  $( Define the class of symmetric relations.  For sets, being an element of
     the class of symmetric relations is equivalent to satisfying the symmetric
     relation predicate, see ~ elsymrelsrel .  Alternate definitions are
     ~ dfsymrels2 , ~ dfsymrels3 , ~ dfsymrels4 and ~ dfsymrels5 .

     This definition is similar to the definitions of the classes of reflexive
     ( ~ df-refrels ) and transitive ( ~ df-trrels ) relations.  (Contributed
     by Peter Mazsa, 7-Jul-2019.) $)
  df-symrels $a |- SymRels = ( Syms i^i Rels ) $.

  $( Define the symmetric relation predicate.  (Read: ` R ` is a symmetric
     relation.)  For sets, being an element of the class of symmetric relations
     ( ~ df-symrels ) is equivalent to satisfying the symmetric relation
     predicate, see ~ elsymrelsrel .  Alternate definitions are ~ dfsymrel2 and
     ~ dfsymrel3 .  (Contributed by Peter Mazsa, 16-Jul-2021.) $)
  df-symrel $a |- ( SymRel R <->
      ( `' ( R i^i ( dom R X. ran R ) ) C_ ( R i^i ( dom R X. ran R ) ) /\
        Rel R ) ) $.

  $( Alternate definition of the class of symmetric relations.  Cf. the comment
     of ~ dfrefrels2 .  (Contributed by Peter Mazsa, 20-Jul-2019.) $)
  dfsymrels2 $p |- SymRels = { r e. Rels | `' r C_ r } $=
    ( cdm crn cxp cin ccnv cssr wbr wss csymrels csyms crels df-symrels df-syms
    cv wcel cvv wb inex1g elv brssr wceq elrels6 biimpi cnveqd sseq12d abeqinbi
    ax-mp bitrid ) AOZUJBUJCDZEZFZULGHZUJFZUJIZAJKLMANUNUMULIZUJLPZUPULQPZUNUQR
    USAUJUKQSTUMULQUAUHURUMUOULUJURULUJURULUJUBZURUTRAUJQUCTUDZUEVAUFUIUG $.

  ${
    $d r x y $.
    $( Alternate definition of the class of symmetric relations.  (Contributed
       by Peter Mazsa, 22-Jul-2021.) $)
    dfsymrels3 $p |- SymRels =
                     { r e. Rels | A. x A. y ( x r y -> y r x ) } $=
      ( cv ccnv wss wbr wi wal crels csymrels dfsymrels2 cnvsym rabbieq ) CDZEO
      FADZBDZOGQPOGHBIAICJKCLABOMN $.
  $}

  ${
    $d R x y $.
    $( Two ways of saying a relation is symmetric.  (Contributed by Peter
       Mazsa, 22-Aug-2021.) $)
    elrelscnveq3 $p |- ( R e. Rels ->
                         ( R = `' R <-> A. x A. y ( x R y -> y R x ) ) ) $=
      ( ccnv wceq wss wa crels wcel cv wbr wi wal eqss cnvsym biimpi a1d adantl
      com12 wrel elrelsrelim dfrel2 sylib cnvss sseq1 syl5ibcom syl5com biimpri
      sylbir jca2 impbid bitrid ) CCDZECUMFZUMCFZGZCHIZAJZBJZCKUSURCKLBMAMZCUMN
      UQUPUTUPUQUTUOUQUTLUNUOUTUQUOUTABCOZPQRSUQUTUNUOUQUMDZCEZUTUNUQCTVCCUACUB
      UCUTUOVCUNLVAUOVBUMFVCUNUMCUDVBCUMUEUFUIUGUOUTVAUHUJUKUL $.
  $}

  ${
    $d R x y $.
    $( Two ways of saying a relation is symmetric.  (Contributed by Peter
       Mazsa, 22-Aug-2021.) $)
    elrelscnveq $p |- ( R e. Rels -> ( `' R C_ R <-> `' R = R ) ) $=
      ( vx vy crels wcel ccnv wceq wss cv wbr wi wal elrelscnveq3 bitr4di eqcom
      cnvsym bitr3di ) ADEZAAFZGZSAHZSAGRTBIZCIZAJUCUBAJKCLBLUABCAMBCAPNASOQ $.
  $}

  ${
    $d R x y $.
    $( Two ways of saying a relation is symmetric.  (Contributed by Peter
       Mazsa, 22-Aug-2021.) $)
    elrelscnveq2 $p |- ( R e. Rels ->
                         ( `' R = R <-> A. x A. y ( x R y <-> y R x ) ) ) $=
      ( crels wcel ccnv wss wa cv wbr wal wceq cnvsym a1i elrelsrelim relbrcnvg
      wi wb wrel syl dfrel2 sylib bitr3di imbi12d 2albidv bitrd anbi12d 2albiim
      sseq1d eqss 3bitr4g ) CDEZCFZCGZCUMGZHAIZBIZCJZUQUPCJZQBKAKZUSURQZBKAKZHU
      MCLURUSRBKAKULUNUTUOVBUNUTRULABCMNULUOUPUQUMJZUQUPUMJZQZBKAKZVBULUMFZUMGU
      OVFULVGCUMULCSZVGCLCOZCUAUBUIABUMMUCULVEVAABULVCUSVDURULVHVCUSRVIUPUQCPTU
      LVHVDURRVIUQUPCPTUDUEUFUGUMCUJURUSABUHUK $.
  $}

  ${
    $d R x y $.
    $( Two ways of saying a relation is symmetric.  (Contributed by Peter
       Mazsa, 22-Aug-2021.) $)
    elrelscnveq4 $p |- ( R e. Rels ->
                         ( `' R C_ R <-> A. x A. y ( x R y <-> y R x ) ) ) $=
      ( crels wcel ccnv wss wceq cv wbr wb wal elrelscnveq elrelscnveq2 bitrd )
      CDECFZCGPCHAIZBIZCJRQCJKBLALCMABCNO $.
  $}

  $( Alternate definition of the class of symmetric relations.  (Contributed by
     Peter Mazsa, 20-Jul-2019.) $)
  dfsymrels4 $p |- SymRels = { r e. Rels | `' r = r } $=
    ( cv ccnv wss wceq crels csymrels dfsymrels2 elrelscnveq rabimbieq ) ABZCZK
    DLKEAFGAHKIJ $.

  ${
    $d r x y $.
    $( Alternate definition of the class of symmetric relations.  (Contributed
       by Peter Mazsa, 22-Jul-2021.) $)
    dfsymrels5 $p |- SymRels =
                     { r e. Rels | A. x A. y ( x r y <-> y r x ) } $=
      ( cv ccnv wceq wbr wal crels csymrels dfsymrels4 elrelscnveq2 rabimbieq
      wb ) CDZEOFADZBDZOGQPOGNBHAHCIJCKABOLM $.
  $}

  $( Alternate definition of the symmetric relation predicate.  (Contributed by
     Peter Mazsa, 19-Apr-2019.)  (Revised by Peter Mazsa, 17-Aug-2021.) $)
  dfsymrel2 $p |- ( SymRel R <-> ( `' R C_ R /\ Rel R ) ) $=
    ( wsymrel cdm crn cxp cin ccnv wss wrel df-symrel wceq dfrel6 biimpi cnveqd
    wa sseq12d pm5.32ri bitri ) ABAACADEFZGZSHZAIZOAGZAHZUBOAJUBUAUDUBTUCSAUBSA
    UBSAKALMZNUEPQR $.

  ${
    $d R x y $.
    $( Alternate definition of the symmetric relation predicate.  (Contributed
       by Peter Mazsa, 21-Apr-2019.)  (Revised by Peter Mazsa, 17-Aug-2021.) $)
    dfsymrel3 $p |- ( SymRel R <->
                      ( A. x A. y ( x R y -> y R x ) /\ Rel R ) ) $=
      ( wsymrel ccnv wss wrel wa cv wbr wi wal dfsymrel2 cnvsym anbi1i bitri )
      CDCECFZCGZHAIZBIZCJTSCJKBLALZRHCMQUARABCNOP $.
  $}

  $( Alternate definition of the symmetric relation predicate.  (Contributed by
     Peter Mazsa, 17-Aug-2021.) $)
  dfsymrel4 $p |- ( SymRel R <-> ( `' R = R /\ Rel R ) ) $=
    ( wsymrel ccnv wss wrel wa wceq dfsymrel2 relcnveq pm5.32ri bitri ) ABACZAD
    ZAEZFLAGZNFAHNMOAIJK $.

  ${
    $d R x y $.
    $( Alternate definition of the symmetric relation predicate.  (Contributed
       by Peter Mazsa, 17-Aug-2021.) $)
    dfsymrel5 $p |- ( SymRel R <->
                      ( A. x A. y ( x R y <-> y R x ) /\ Rel R ) ) $=
      ( wsymrel ccnv wss wrel wa cv wbr wal dfsymrel2 relcnveq4 pm5.32ri bitri
      wb ) CDCECFZCGZHAIZBIZCJTSCJPBKAKZRHCLRQUAABCMNO $.
  $}

  ${
    $d R r $.
    $( Element of the class of symmetric relations.  (Contributed by Peter
       Mazsa, 17-Aug-2021.) $)
    elsymrels2 $p |- ( R e. SymRels <-> ( `' R C_ R /\ R e. Rels ) ) $=
      ( vr cv ccnv wss crels csymrels dfsymrels2 wceq cnveq id sseq12d rabeqel
      ) BCZDZNEADZAEBFGABHNAIZOPNANAJQKLM $.
  $}

  ${
    $d R r x y $.
    $( Element of the class of symmetric relations.  (Contributed by Peter
       Mazsa, 17-Aug-2021.) $)
    elsymrels3 $p |- ( R e. SymRels <->
                       ( A. x A. y ( x R y -> y R x ) /\ R e. Rels ) ) $=
      ( vr cv wbr wi wal crels csymrels dfsymrels3 wceq imbi12d 2albidv rabeqel
      breq ) AEZBEZDEZFZRQSFZGZBHAHQRCFZRQCFZGZBHAHDIJCABDKSCLZUBUEABUFTUCUAUDQ
      RSCPRQSCPMNO $.
  $}

  ${
    $d R r $.
    $( Element of the class of symmetric relations.  (Contributed by Peter
       Mazsa, 17-Aug-2021.) $)
    elsymrels4 $p |- ( R e. SymRels <-> ( `' R = R /\ R e. Rels ) ) $=
      ( vr cv ccnv wceq crels csymrels dfsymrels4 cnveq id eqeq12d rabeqel ) BC
      ZDZMEADZAEBFGABHMAEZNOMAMAIPJKL $.
  $}

  ${
    $d R r x y $.
    $( Element of the class of symmetric relations.  (Contributed by Peter
       Mazsa, 17-Aug-2021.) $)
    elsymrels5 $p |- ( R e. SymRels <->
                       ( A. x A. y ( x R y <-> y R x ) /\ R e. Rels ) ) $=
      ( vr cv wbr wb wal crels csymrels dfsymrels5 wceq bibi12d 2albidv rabeqel
      breq ) AEZBEZDEZFZRQSFZGZBHAHQRCFZRQCFZGZBHAHDIJCABDKSCLZUBUEABUFTUCUAUDQ
      RSCPRQSCPMNO $.
  $}

  $( For sets, being an element of the class of symmetric relations
     ( ~ df-symrels ) is equivalent to satisfying the symmetric relation
     predicate.  (Contributed by Peter Mazsa, 17-Aug-2021.) $)
  elsymrelsrel $p |- ( R e. V -> ( R e. SymRels <-> SymRel R ) ) $=
    ( wcel ccnv wss crels wa wrel wsymrel elrelsrel anbi2d elsymrels2 dfsymrel2
    csymrels 3bitr4g ) ABCZADAEZAFCZGQAHZGANCAIPRSQABJKALAMO $.

  $( Equality theorem for symmetric relation.  (Contributed by Peter Mazsa,
     15-Apr-2019.)  (Revised by Peter Mazsa, 23-Sep-2021.) $)
  symreleq $p |- ( R = S -> ( SymRel R <-> SymRel S ) ) $=
    ( wceq ccnv wss wa wsymrel cnveq id sseq12d releq anbi12d dfsymrel2 3bitr4g
    wrel ) ABCZADZAEZAOZFBDZBEZBOZFAGBGPRUASUBPQTABABHPIJABKLAMBMN $.

  $( Symmetric relation implies that the domain and the range are equal.
     (Contributed by Peter Mazsa, 29-Dec-2021.) $)
  symrelim $p |- ( SymRel R -> dom R = ran R ) $=
    ( wsymrel cdm ccnv crn rncnv wceq wrel dfsymrel4 simplbi rneqd eqtr3id ) AB
    ZACADZEAEAFMNAMNAGAHAIJKL $.

  $( The class of cosets by ` R ` is symmetric.  (Contributed by Peter Mazsa,
     20-Dec-2021.) $)
  symrelcoss $p |- SymRel ,~ R $=
    ( ccoss wsymrel ccnv wss wrel wa symrelcoss2 dfsymrel2 mpbir ) ABZCKDKEKFGA
    HKIJ $.

  $( The identity relation is symmetric.  (Contributed by AV, 19-Jun-2022.) $)
  idsymrel $p |- SymRel _I $=
    ( cid wsymrel ccnv wceq wrel cnvi reli dfsymrel4 mpbir2an ) ABACADAEFGAHI
    $.

  $( The membership (epsilon) relation is not symmetric.  (Contributed by AV,
     18-Jun-2022.) $)
  epnsymrel $p |- -. SymRel _E $=
    ( cep wsymrel ccnv wceq wrel wa epnsym neii intnanr dfsymrel4 mtbir ) ABACZ
    ADZAEZFMNLAGHIAJK $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Reflexivity and symmetry
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Symmetry is a sufficient condition for the equivalence of two versions of
     the reflexive relation, see also ~ symrefref3 .  (Contributed by Peter
     Mazsa, 19-Jul-2018.) $)
  symrefref2 $p |- ( `' R C_ R ->
      ( ( _I i^i ( dom R X. ran R ) ) C_ R <-> ( _I |` dom R ) C_ R ) ) $=
    ( ccnv wss cid cdm crn cxp cres wceq rnss rncnv sseq1i biimpi idreseqidinxp
    cin 3syl sseq1d ) ABZACZDAEZAFZGOZDTHZASRFZUACZTUACZUBUCIRAJUEUFUDTUAAKLMTU
    ANPQ $.

  ${
    $d R x y $.
    $( Symmetry is a sufficient condition for the equivalence of two versions
       of the reflexive relation, see also ~ symrefref2 .  (Contributed by
       Peter Mazsa, 23-Aug-2021.)  (Proof modification is discouraged.) $)
    symrefref3 $p |- ( A. x A. y ( x R y -> y R x ) ->
        ( A. x e. dom R A. y e. ran R ( x = y -> x R y ) <->
          A. x e. dom R x R x ) ) $=
      ( ccnv wss cid cdm crn cxp cin cres wb cv wbr wi wal wceq wral symrefref2
      cnvsym idinxpss idrefALT bibi12i 3imtr3i ) CDCEFCGZCHZIJCEZFUEKCEZLAMZBMZ
      CNZUJUICNOBPAPUIUJQUKOBUFRAUERZUIUICNAUERZLCSABCTUGULUHUMABUEUFCUAAUECUBU
      CUD $.
  $}

  $( Elements of the class of reflexive relations which are elements of the
     class of symmetric relations as well (like the elements of the class of
     equivalence relations ~ dfeqvrels2 ) can use the restricted version for
     their reflexive part (see below), not just the
     ` ( _I i^i ( dom r X. ran r ) ) C_ r ` version of ~ dfrefrels2 , cf. the
     comment of ~ dfrefrels2 .  (Contributed by Peter Mazsa, 20-Jul-2019.) $)
  refsymrels2 $p |- ( RefRels i^i SymRels ) =
      { r e. Rels | ( ( _I |` dom r ) C_ r /\ `' r C_ r ) } $=
    ( crefrels csymrels cin cid cdm crn cxp wss crels crab ccnv cres dfrefrels2
    cv wa dfsymrels2 ineq12i inrab symrefref2 pm5.32ri rabbii 3eqtri ) BCDEAOZF
    ZUDGHDUDIZAJKZUDLUDIZAJKZDUFUHPZAJKEUEMUDIZUHPZAJKBUGCUIANAQRUFUHAJSUJULAJU
    HUFUKUDTUAUBUC $.

  ${
    $d r x y $.
    $( Elements of the class of reflexive relations which are elements of the
       class of symmetric relations as well (like the elements of the class of
       equivalence relations ~ dfeqvrels3 ) can use the ` A. x e. dom r x r x `
       version for their reflexive part, not just the
       ` A. x e. dom r A. y e. ran r ( x = y -> x r y ) ` version of
       ~ dfrefrels3 , cf. the comment of ~ dfrefrel3 .  (Contributed by Peter
       Mazsa, 22-Jul-2019.)  (Proof modification is discouraged.) $)
    refsymrels3 $p |- ( RefRels i^i SymRels ) =
     { r e. Rels | ( A. x e. dom r x r x /\ A. x A. y ( x r y -> y r x ) ) } $=
      ( cid cv cdm cres wss ccnv wa wbr wral wi wal crels crefrels csymrels cin
      refsymrels2 idrefALT cnvsym anbi12i rabbieq ) DCEZFZGUDHZUDIUDHZJAEZUHUDK
      AUELZUHBEZUDKUJUHUDKMBNANZJCOPQRCSUFUIUGUKAUEUDTABUDUAUBUC $.
  $}

  $( A relation which is reflexive and symmetric (like an equivalence relation)
     can use the restricted version for their reflexive part (see below), not
     just the ` ( _I i^i ( dom R X. ran R ) ) C_ R ` version of ~ dfrefrel2 ,
     cf. the comment of ~ dfrefrels2 .  (Contributed by Peter Mazsa,
     23-Aug-2021.) $)
  refsymrel2 $p |- ( ( RefRel R /\ SymRel R ) <->
      ( ( ( _I |` dom R ) C_ R /\ `' R C_ R ) /\ Rel R ) ) $=
    ( wrefrel wsymrel wa cid cdm crn cxp cin ccnv wrel cres dfrefrel2 dfsymrel2
    wss w3a anbi12i anandi3r 3anan32 3bitr2i symrefref2 pm5.32ri anbi1i bitri )
    ABZACZDZEAFZAGHIAOZAJAOZDZAKZDZEUHLAOZUJDZULDUGUIULDZUJULDZDUIULUJPUMUEUPUF
    UQAMANQUIULUJRUIULUJSTUKUOULUJUIUNAUAUBUCUD $.

  ${
    $d R x y $.
    $( A relation which is reflexive and symmetric (like an equivalence
       relation) can use the ` A. x e. dom R x R x ` version for its reflexive
       part, not just the ` A. x e. dom R A. y e. ran R ( x = y -> x R y ) `
       version of ~ dfrefrel3 , cf. the comment of ~ dfrefrel3 .  (Contributed
       by Peter Mazsa, 23-Aug-2021.) $)
    refsymrel3 $p |- ( ( RefRel R /\ SymRel R ) <->
        ( ( A. x e. dom R x R x /\ A. x A. y ( x R y -> y R x ) ) /\
          Rel R ) ) $=
      ( wrefrel wsymrel wa weq cv wbr crn wral cdm wal wrel dfrefrel3 dfsymrel3
      wi w3a anbi12i anandi3r 3anan32 3bitr2i symrefref3 pm5.32ri anbi1i bitri
      ) CDZCEZFZABGAHZBHZCIZQBCJKACLZKZULUKUJCIQBMAMZFZCNZFZUJUJCIAUMKZUOFZUQFU
      IUNUQFZUOUQFZFUNUQUORURUGVAUHVBABCOABCPSUNUQUOTUNUQUOUAUBUPUTUQUOUNUSABCU
      CUDUEUF $.
  $}

  ${
    $d R r $.
    $( Elements of the class of reflexive relations which are elements of the
       class of symmetric relations as well (like the elements of the class of
       equivalence relations ~ dfeqvrels2 ) can use the restricted version for
       their reflexive part (see below), not just the
       ` ( _I i^i ( dom R X. ran R ) ) C_ R ` version of ~ dfrefrels2 , cf. the
       comment of ~ dfrefrels2 .  (Contributed by Peter Mazsa, 22-Jul-2019.) $)
    elrefsymrels2 $p |- ( R e. ( RefRels i^i SymRels ) <->
        ( ( ( _I |` dom R ) C_ R /\ `' R C_ R ) /\ R e. Rels ) ) $=
      ( vr cid cv cdm cres wss ccnv wa crels crefrels csymrels refsymrels2 wceq
      cin dmeq reseq2d id sseq12d cnveq anbi12d rabeqel ) CBDZEZFZUCGZUCHZUCGZI
      CAEZFZAGZAHZAGZIBJKLOABMUCANZUFUKUHUMUNUEUJUCAUNUDUICUCAPQUNRZSUNUGULUCAU
      CATUOSUAUB $.
  $}

  ${
    $d R x y $.
    $( Elements of the class of reflexive relations which are elements of the
       class of symmetric relations as well (like the elements of the class of
       equivalence relations ~ dfeqvrels3 ) can use the ` A. x e. dom R x R x `
       version for their reflexive part, not just the
       ` A. x e. dom R A. y e. ran R ( x = y -> x R y ) ` version of
       ~ dfrefrels3 , cf. the comment of ~ dfrefrel3 .  (Contributed by Peter
       Mazsa, 22-Jul-2019.)  (Proof modification is discouraged.) $)
    elrefsymrels3 $p |- ( R e. ( RefRels i^i SymRels ) <->
        ( ( A. x e. dom R x R x /\ A. x A. y ( x R y -> y R x ) ) /\
          R e. Rels ) ) $=
      ( crefrels csymrels cin wcel cid cdm cres wss ccnv wa crels cv wbr wi wal
      wral elrefsymrels2 idrefALT cnvsym anbi12i anbi1i bitri ) CDEFGHCIZJCKZCL
      CKZMZCNGZMAOZUKCPAUFSZUKBOZCPUMUKCPQBRARZMZUJMCTUIUOUJUGULUHUNAUFCUAABCUB
      UCUDUE $.
  $}

  $( For sets, being an element of the class of reflexive and symmetric
     relations is equivalent to satisfying the reflexive and symmetric relation
     predicates.  (Contributed by Peter Mazsa, 23-Aug-2021.) $)
  elrefsymrelsrel $p |- ( R e. V ->
      ( R e. ( RefRels i^i SymRels ) <-> ( RefRel R /\ SymRel R ) ) ) $=
    ( crefrels csymrels cin wcel wrefrel wsymrel elin elrefrelsrel elsymrelsrel
    wa anbi12d bitrid ) ACDEFACFZADFZLABFZAGZAHZLACDIQORPSABJABKMN $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Transitivity
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define the class of all transitive sets (versus the transitive class
     defined in ~ df-tr ).  It is used only by ~ df-trrels .

     Note the similarity of the definitions of ~ df-refs , ~ df-syms and
     ~ df-trs .  (Contributed by Peter Mazsa, 17-Jul-2021.) $)
  df-trs $a |- Trs = { x |
      ( ( x i^i ( dom x X. ran x ) ) o. ( x i^i ( dom x X. ran x ) ) ) _S
        ( x i^i ( dom x X. ran x ) ) } $.

  $( Define the class of transitive relations.  For sets, being an element of
     the class of transitive relations is equivalent to satisfying the
     transitive relation predicate, see ~ eltrrelsrel .  Alternate definitions
     are ~ dftrrels2 and ~ dftrrels3 .

     This definition is similar to the definitions of the classes of reflexive
     ( ~ df-refrels ) and symmetric ( ~ df-symrels ) relations.  (Contributed
     by Peter Mazsa, 7-Jul-2019.) $)
  df-trrels $a |- TrRels = ( Trs i^i Rels ) $.

  $( Define the transitive relation predicate.  (Read: ` R ` is a transitive
     relation.)  For sets, being an element of the class of transitive
     relations ( ~ df-trrels ) is equivalent to satisfying the transitive
     relation predicate, see ~ eltrrelsrel .  Alternate definitions are
     ~ dftrrel2 and ~ dftrrel3 .  (Contributed by Peter Mazsa, 17-Jul-2021.) $)
  df-trrel $a |- ( TrRel R <->
      ( ( ( R i^i ( dom R X. ran R ) ) o. ( R i^i ( dom R X. ran R ) ) ) C_
          ( R i^i ( dom R X. ran R ) ) /\ Rel R ) ) $.

  $( Alternate definition of the class of transitive relations.

     I'd prefer to define the class of transitive relations by using the
     definition of composition by [Suppes] p. 63. df-coSUP
     ` ( A o. B ) = { <. x , y >. | E. u ( x A u /\ u B y ) } ` as opposed to
     the present definition of composition ~ df-co
     ` ( A o. B ) = { <. x , y >. | E. u ( x B u /\ u A y ) } ` because the
     Suppes definition keeps the order of ` A ` , ` B ` , ` C ` , ` R ` ,
     ` S ` , ` T ` by default in trsinxpSUP ` ( ( ( R i^i ( A X. B ) ) o. ( S `
     ` i^i ( B X. C ) ) ) C_ ( T i^i ( A X. C ) ) <-> A. x e. A A. y e. B A. `
     ` z e. C ( ( x R y /\ y S z ) -> x T z ) ) ` while the present definition
     of composition disarranges them: trsinxp
     ` ( ( ( S i^i ( B X. C ) ) o. ( R i^i ( A X. B ) ) ) C_ ( T i^i ( A X. C `
     ` ) ) <-> A. x e. A A. y e. B A. z e. C ( ( x R y /\ y S z ) -> x T z ) `
     ` ) ` .  This is not mission critical to me, the implication of the Suppes
     definition is just more aesthetic, at least in the above case.

     If we swap to the Suppes definition of class composition, I would define
     the present class of all transitive sets as df-trsSUP and I would consider
     to switch the definition of the class of cosets by ` R ` from the present
     ~ df-coss to a df-cossSUP. But perhaps there is a mathematical reason to
     keep the present definition of composition.  (Contributed by Peter Mazsa,
     21-Jul-2021.) $)
  dftrrels2 $p |- TrRels = { r e. Rels | ( r o. r ) C_ r } $=
    ( cv cdm crn cxp cin ccom cssr wbr ctrrels ctrs crels df-trrels df-trs wcel
    wss cvv wb inex1g elv brssr elrels6 biimpi coeq12d sseq12d bitrid abeqinbi
    ax-mp wceq ) ABZUJCUJDEZFZULGZULHIZUJUJGZUJPZAJKLMANUNUMULPZUJLOZUPULQOZUNU
    QRUSAUJUKQSTUMULQUAUHURUMUOULUJURULUJULUJURULUJUIZURUTRAUJQUBTUCZVAUDVAUEUF
    UG $.

  ${
    $d r x y z $.
    $( Alternate definition of the class of transitive relations.  (Contributed
       by Peter Mazsa, 22-Jul-2021.) $)
    dftrrels3 $p |- TrRels =
        { r e. Rels | A. x A. y A. z ( ( x r y /\ y r z ) -> x r z ) } $=
      ( cv ccom wss wbr wa wi wal crels ctrrels dftrrels2 cotr rabbieq ) DEZQFQ
      GAEZBEZQHSCEZQHIRTQHJCKBKAKDLMDNABCQOP $.
  $}

  $( Alternate definition of the transitive relation predicate.  (Contributed
     by Peter Mazsa, 22-Aug-2021.) $)
  dftrrel2 $p |- ( TrRel R <-> ( ( R o. R ) C_ R /\ Rel R ) ) $=
    ( wtrrel cdm crn cxp cin ccom wss wrel df-trrel wceq dfrel6 coeq12d sseq12d
    wa biimpi pm5.32ri bitri ) ABAACADEFZSGZSHZAIZOAAGZAHZUBOAJUBUAUDUBTUCSAUBS
    ASAUBSAKALPZUEMUENQR $.

  ${
    $d R x y z $.
    $( Alternate definition of the transitive relation predicate.  (Contributed
       by Peter Mazsa, 22-Aug-2021.) $)
    dftrrel3 $p |- ( TrRel R <->
        ( A. x A. y A. z ( ( x R y /\ y R z ) -> x R z ) /\ Rel R ) ) $=
      ( wtrrel ccom wss wrel wa cv wbr wi wal dftrrel2 cotr anbi1i bitri ) DEDD
      FDGZDHZIAJZBJZDKUACJZDKITUBDKLCMBMAMZSIDNRUCSABCDOPQ $.
  $}

  ${
    $d R r $.
    $( Element of the class of transitive relations.  (Contributed by Peter
       Mazsa, 22-Aug-2021.) $)
    eltrrels2 $p |- ( R e. TrRels <-> ( ( R o. R ) C_ R /\ R e. Rels ) ) $=
      ( vr cv ccom wss crels ctrrels dftrrels2 wceq coideq id sseq12d rabeqel )
      BCZNDZNEAADZAEBFGABHNAIZOPNANAJQKLM $.
  $}

  ${
    $d R r x y z $.
    $( Element of the class of transitive relations.  (Contributed by Peter
       Mazsa, 22-Aug-2021.) $)
    eltrrels3 $p |- ( R e. TrRels <->
        ( A. x A. y A. z ( ( x R y /\ y R z ) -> x R z ) /\ R e. Rels ) ) $=
      ( vr cv wbr wa wi wal ctrrels dftrrels3 wceq breq anbi12d imbi12d 2albidv
      crels albidv rabeqel ) AFZBFZEFZGZUBCFZUCGZHZUAUEUCGZIZCJBJZAJUAUBDGZUBUE
      DGZHZUAUEDGZIZCJBJZAJERKDABCELUCDMZUJUPAUQUIUOBCUQUGUMUHUNUQUDUKUFULUAUBU
      CDNUBUEUCDNOUAUEUCDNPQST $.
  $}

  $( For sets, being an element of the class of transitive relations is
     equivalent to satisfying the transitive relation predicate.  (Contributed
     by Peter Mazsa, 22-Aug-2021.) $)
  eltrrelsrel $p |- ( R e. V -> ( R e. TrRels <-> TrRel R ) ) $=
    ( wcel ccom wss crels wa ctrrels wtrrel elrelsrel anbi2d eltrrels2 dftrrel2
    wrel 3bitr4g ) ABCZAADAEZAFCZGQANZGAHCAIPRSQABJKALAMO $.

  $( Equality theorem for the transitive relation predicate.  (Contributed by
     Peter Mazsa, 15-Apr-2019.)  (Revised by Peter Mazsa, 23-Sep-2021.) $)
  trreleq $p |- ( R = S -> ( TrRel R <-> TrRel S ) ) $=
    ( wceq ccom wrel wa wtrrel coideq id sseq12d releq anbi12d dftrrel2 3bitr4g
    wss ) ABCZAADZAOZAEZFBBDZBOZBEZFAGBGPRUASUBPQTABABHPIJABKLAMBMN $.

  ${
    $d A x y z $.  $d R x y z $.
    $( Any class ' R ' restricted to the singleton of the class ' A ' (see
       ~ ressn2 ) is transitive.  (Contributed by Peter Mazsa, 17-Jun-2024.) $)
    trrelressn $p |- TrRel ( R |` { A } ) $=
      ( vx vy vz csn cres wtrrel cv wbr wa wi wal wrel relres dftrrel3 mpbir2an
      trressn ) BAFZGZHCIZDIZTJUBEIZTJKUAUCTJLEMDMCMTNCDEABRBSOCDETPQ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Equivalence relations
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define the class of equivalence relations.  For sets, being an element of
     the class of equivalence relations is equivalent to satisfying the
     equivalence relation predicate, see ~ eleqvrelsrel .  Alternate
     definitions are ~ dfeqvrels2 and ~ dfeqvrels3 .  (Contributed by Peter
     Mazsa, 7-Nov-2018.) $)
  df-eqvrels $a |- EqvRels = ( ( RefRels i^i SymRels ) i^i TrRels ) $.

  $( Define the equivalence relation predicate.  (Read: ` R ` is an equivalence
     relation.)  For sets, being an element of the class of equivalence
     relations ( ~ df-eqvrels ) is equivalent to satisfying the equivalence
     relation predicate, see ~ eleqvrelsrel .  Alternate definitions are
     ~ dfeqvrel2 and ~ dfeqvrel3 .  (Contributed by Peter Mazsa,
     17-Apr-2019.) $)
  df-eqvrel $a |- ( EqvRel R <-> ( RefRel R /\ SymRel R /\ TrRel R ) ) $.

  $( Define the coelement equivalence relations class, the class of sets with
     coelement equivalence relations.  For sets, being an element of the class
     of coelement equivalence relations is equivalent to satisfying the
     coelement equivalence relation predicate, see ~ elcoeleqvrelsrel .
     Alternate definition is ~ dfcoeleqvrels .  (Contributed by Peter Mazsa,
     28-Nov-2022.) $)
  df-coeleqvrels $a |- CoElEqvRels = { a | ,~ ( `' _E |` a ) e. EqvRels } $.

  $( Define the coelement equivalence relation predicate.  (Read: the coelement
     equivalence relation on ` A ` .)  Alternate definition is ~ dfcoeleqvrel .
     For sets, being an element of the class of coelement equivalence relations
     is equivalent to satisfying the coelement equivalence relation predicate,
     see ~ elcoeleqvrelsrel .  (Contributed by Peter Mazsa, 11-Dec-2021.) $)
  df-coeleqvrel $a |- ( CoElEqvRel A <-> EqvRel ,~ ( `' _E |` A ) ) $.

  $( Alternate definition of the class of equivalence relations.  (Contributed
     by Peter Mazsa, 2-Dec-2019.) $)
  dfeqvrels2 $p |- EqvRels = { r e. Rels |
      ( ( _I |` dom r ) C_ r /\ `' r C_ r /\ ( r o. r ) C_ r ) } $=
    ( ceqvrels cid cv cdm cres wss ccnv wa ccom crels w3a crefrels csymrels cin
    crab ctrrels df-eqvrels refsymrels2 dftrrels2 ineq12i 3eqtri df-3an rabbii
    inrab eqtr4i ) BCADZEFUGGZUGHUGGZIZUGUGJUGGZIZAKPZUHUIUKLZAKPBMNOZQOUJAKPZU
    KAKPZOUMRUOUPQUQASATUAUJUKAKUEUBUNULAKUHUIUKUCUDUF $.

  ${
    $d r x y z $.
    $( Alternate definition of the class of equivalence relations.
       (Contributed by Peter Mazsa, 2-Dec-2019.) $)
    dfeqvrels3 $p |- EqvRels = { r e. Rels |
        ( A. x e. dom r x r x /\
          A. x A. y ( x r y -> y r x ) /\
          A. x A. y A. z ( ( x r y /\ y r z ) -> x r z ) ) } $=
      ( cid cv cdm cres wss ccnv ccom w3a wbr wral wi crels ceqvrels dfeqvrels2
      wal wa idrefALT cnvsym cotr 3anbi123i rabbieq ) EDFZGZHUFIZUFJUFIZUFUFKUF
      IZLAFZUKUFMAUGNZUKBFZUFMZUMUKUFMOBSASZUNUMCFZUFMTUKUPUFMOCSBSASZLDPQDRUHU
      LUIUOUJUQAUGUFUAABUFUBABCUFUCUDUE $.
  $}

  $( Alternate definition of the equivalence relation predicate.  (Contributed
     by Peter Mazsa, 22-Apr-2019.) $)
  dfeqvrel2 $p |- ( EqvRel R <->
      ( ( ( _I |` dom R ) C_ R /\ `' R C_ R /\ ( R o. R ) C_ R ) /\
          Rel R ) ) $=
    ( weqvrel wrefrel wsymrel wtrrel w3a cid cdm cres ccnv ccom wrel refsymrel2
    wss wa df-eqvrel dftrrel2 anbi12i df-3an anbi1i 3anan32 anandi3r 3bitr2i
    3bitr4i bitri ) ABACZADZAEZFZGAHIANZAJANZAAKANZFZALZOZAPUFUGOZUHOUJUKOZUNOZ
    ULUNOZOZUIUOUPURUHUSAMAQRUFUGUHSUOUQULOZUNOUQUNULFUTUMVAUNUJUKULSTUQUNULUAU
    QUNULUBUCUDUE $.

  ${
    $d R x y z $.
    $( Alternate definition of the equivalence relation predicate.
       (Contributed by Peter Mazsa, 22-Apr-2019.) $)
    dfeqvrel3 $p |- ( EqvRel R <->
        ( ( A. x e. dom R x R x /\
            A. x A. y ( x R y -> y R x ) /\
            A. x A. y A. z ( ( x R y /\ y R z ) -> x R z ) ) /\
          Rel R ) ) $=
      ( weqvrel wrefrel wsymrel wtrrel w3a cv wbr cdm wral wi wa wrel df-eqvrel
      wal refsymrel3 df-3an dftrrel3 anbi12i 3anan32 anandi3r 3bitr2i 3bitr4i
      anbi1i bitri ) DEDFZDGZDHZIZAJZUMDKADLMZUMBJZDKZUOUMDKNBRARZUPUOCJZDKOUMU
      RDKNCRBRARZIZDPZOZDQUIUJOZUKOUNUQOZVAOZUSVAOZOZULVBVCVEUKVFABDSABCDUAUBUI
      UJUKTVBVDUSOZVAOVDVAUSIVGUTVHVAUNUQUSTUGVDVAUSUCVDVAUSUDUEUFUH $.
  $}

  ${
    $d R r $.
    $( Element of the class of equivalence relations.  (Contributed by Peter
       Mazsa, 24-Aug-2021.) $)
    eleqvrels2 $p |- ( R e. EqvRels <->
        ( ( ( _I |` dom R ) C_ R /\ `' R C_ R /\ ( R o. R ) C_ R ) /\
            R e. Rels ) ) $=
      ( vr cid cv cdm cres wss ccnv ccom crels ceqvrels dfeqvrels2 wceq reseq2d
      w3a dmeq id sseq12d cnveq coideq 3anbi123d rabeqel ) CBDZEZFZUCGZUCHZUCGZ
      UCUCIZUCGZOCAEZFZAGZAHZAGZAAIZAGZOBJKABLUCAMZUFUMUHUOUJUQURUEULUCAURUDUKC
      UCAPNURQZRURUGUNUCAUCASUSRURUIUPUCAUCATUSRUAUB $.
  $}

  ${
    $d R r x y z $.
    $( Element of the class of equivalence relations.  (Contributed by Peter
       Mazsa, 24-Aug-2021.) $)
    eleqvrels3 $p |- ( R e. EqvRels <->
        ( ( A. x e. dom R x R x /\
            A. x A. y ( x R y -> y R x ) /\
            A. x A. y A. z ( ( x R y /\ y R z ) -> x R z ) ) /\
          R e. Rels ) ) $=
      ( vr cv wbr cdm wral wi wal wa w3a crels ceqvrels dfeqvrels3 wceq imbi12d
      breq 2albidv dmeq raleqbidv anbi12d albidv 3anbi123d rabeqel ) AFZUGEFZGZ
      AUHHZIZUGBFZUHGZULUGUHGZJZBKAKZUMULCFZUHGZLZUGUQUHGZJZCKBKZAKZMUGUGDGZADH
      ZIZUGULDGZULUGDGZJZBKAKZVGULUQDGZLZUGUQDGZJZCKBKZAKZMENODABCEPUHDQZUKVFUP
      VJVCVPVQUIVDAUJVEUHDUAUGUGUHDSUBVQUOVIABVQUMVGUNVHUGULUHDSZULUGUHDSRTVQVB
      VOAVQVAVNBCVQUSVLUTVMVQUMVGURVKVRULUQUHDSUCUGUQUHDSRTUDUEUF $.
  $}

  $( For sets, being an element of the class of equivalence relations is
     equivalent to satisfying the equivalence relation predicate.  (Contributed
     by Peter Mazsa, 24-Aug-2021.) $)
  eleqvrelsrel $p |- ( R e. V -> ( R e. EqvRels <-> EqvRel R ) ) $=
    ( wcel cid cdm cres wss ccnv ccom w3a crels wrel ceqvrels weqvrel elrelsrel
    wa anbi2d eleqvrels2 dfeqvrel2 3bitr4g ) ABCZDAEFAGAHAGAAIAGJZAKCZPUBALZPAM
    CANUAUCUDUBABOQARAST $.

  ${
    $d A a $.
    $( Elementhood in the coelement equivalence relations class.  (Contributed
       by Peter Mazsa, 24-Jul-2023.) $)
    elcoeleqvrels $p |- ( A e. V ->
        ( A e. CoElEqvRels <-> ,~ ( `' _E |` A ) e. EqvRels ) ) $=
      ( va cep ccnv cv cres ccoss ceqvrels wcel ccoeleqvrels wceq reseq2 eleq1d
      cosseqd df-coeleqvrels elab2g ) DEZCFZGZHZIJRAGZHZIJCAKBSALZUAUCIUDTUBSAR
      MONCPQ $.
  $}

  $( For sets, being an element of the class of coelement equivalence relations
     is equivalent to satisfying the coelement equivalence relation predicate.
     (Contributed by Peter Mazsa, 24-Jul-2023.) $)
  elcoeleqvrelsrel $p |- ( A e. V ->
                           ( A e. CoElEqvRels <-> CoElEqvRel A ) ) $=
    ( wcel ccoeleqvrels cep ccnv weqvrel wcoeleqvrel ceqvrels elcoeleqvrels cvv
    cres ccoss wb 1cosscnvepresex eleqvrelsrel syl bitrd df-coeleqvrel bitr4di
    ) ABCZADCZEFALMZGZAHUAUBUCICZUDABJUAUCKCUEUDNABOUCKPQRAST $.

  $( An equivalence relation is a relation.  (Contributed by Peter Mazsa,
     2-Jun-2019.) $)
  eqvrelrel $p |- ( EqvRel R -> Rel R ) $=
    ( weqvrel cid cdm cres wss ccnv ccom w3a wrel dfeqvrel2 simprbi ) ABCADEAFA
    GAFAAHAFIAJAKL $.

  $( An equivalence relation is reflexive.  (Contributed by Peter Mazsa,
     29-Dec-2021.) $)
  eqvrelrefrel $p |- ( EqvRel R -> RefRel R ) $=
    ( weqvrel wrefrel wsymrel wtrrel df-eqvrel simp1bi ) ABACADAEAFG $.

  $( An equivalence relation is symmetric.  (Contributed by Peter Mazsa,
     29-Dec-2021.) $)
  eqvrelsymrel $p |- ( EqvRel R -> SymRel R ) $=
    ( weqvrel wrefrel wsymrel wtrrel df-eqvrel simp2bi ) ABACADAEAFG $.

  $( An equivalence relation is transitive.  (Contributed by Peter Mazsa,
     29-Dec-2021.) $)
  eqvreltrrel $p |- ( EqvRel R -> TrRel R ) $=
    ( weqvrel wrefrel wsymrel wtrrel df-eqvrel simp3bi ) ABACADAEAFG $.

  $( Equivalence relation implies that the domain and the range are equal.
     (Contributed by Peter Mazsa, 29-Dec-2021.) $)
  eqvrelim $p |- ( EqvRel R -> dom R = ran R ) $=
    ( weqvrel wsymrel cdm crn wceq eqvrelsymrel symrelim syl ) ABACADAEFAGAHI
    $.

  $( Equality theorem for equivalence relation.  (Contributed by Peter Mazsa,
     19-Apr-2020.)  (Revised by Peter Mazsa, 23-Sep-2021.) $)
  eqvreleq $p |- ( R = S -> ( EqvRel R <-> EqvRel S ) ) $=
    ( wceq wrefrel wsymrel wtrrel weqvrel refreleq symreleq 3anbi123d df-eqvrel
    w3a trreleq 3bitr4g ) ABCZADZAEZAFZLBDZBEZBFZLAGBGOPSQTRUAABHABIABMJAKBKN
    $.

  ${
    eqvreleqi.1 $e |- R = S $.
    $( Equality theorem for equivalence relation, inference version.
       (Contributed by Peter Mazsa, 23-Sep-2021.) $)
    eqvreleqi $p |- ( EqvRel R <-> EqvRel S ) $=
      ( wceq weqvrel wb eqvreleq ax-mp ) ABDAEBEFCABGH $.
  $}

  ${
    eqvreleqd.1 $e |- ( ph -> R = S ) $.
    $( Equality theorem for equivalence relation, deduction version.
       (Contributed by Peter Mazsa, 23-Sep-2021.) $)
    eqvreleqd $p |- ( ph -> ( EqvRel R <-> EqvRel S ) ) $=
      ( wceq weqvrel wb eqvreleq syl ) ABCEBFCFGDBCHI $.
  $}

  ${
    eqvrelsym.1 $e |- ( ph -> EqvRel R ) $.
    eqvrelsym.2 $e |- ( ph -> A R B ) $.
    $( An equivalence relation is symmetric.  (Contributed by NM, 4-Jun-1995.)
       (Revised by Mario Carneiro, 12-Aug-2015.)  (Revised by Peter Mazsa,
       2-Jun-2019.) $)
    eqvrelsym $p |- ( ph -> B R A ) $=
      ( ccnv wbr weqvrel wrel eqvrelrel relbrcnvg 3syl wsymrel wss eqvrelsymrel
      wb mpbird dfsymrel2 simplbi ssbrd mpd ) ACBDGZHZCBDHAUDBCDHZFADIZDJZUDUEQ
      EDKCBDLMRAUCDCBAUFDNZUCDOZEDPUHUIUGDSTMUAUB $.
  $}

  ${
    eqvrelsymb.1 $e |- ( ph -> EqvRel R ) $.
    $( An equivalence relation is symmetric.  (Contributed by NM, 30-Jul-1995.)
       (Revised by Mario Carneiro, 12-Aug-2015.)  (Revised and distinct
       variable conditions removed by Peter Mazsa, 2-Jun-2019.) $)
    eqvrelsymb $p |- ( ph -> ( A R B <-> B R A ) ) $=
      ( wbr wa weqvrel adantr simpr eqvrelsym impbida ) ABCDFZCBDFZAMGBCDADHZME
      IAMJKANGCBDAONEIANJKL $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.  $d R x $.
    eqvreltr.1 $e |- ( ph -> EqvRel R ) $.
    $( An equivalence relation is transitive.  (Contributed by NM, 4-Jun-1995.)
       (Revised by Mario Carneiro, 12-Aug-2015.)  (Revised by Peter Mazsa,
       2-Jun-2019.) $)
    eqvreltr $p |- ( ph -> ( ( A R B /\ B R C ) -> A R C ) ) $=
      ( vx wbr wa ccom cv wex cvv wrel wcel syl simpr brrelex1 syl2an wss breq2
      weqvrel eqvrelrel wceq breq1 anbi12d spcedv simpl brrelex2 syl2anc mpbird
      wb brcog ex cid cdm cres ccnv w3a dfeqvrel2 simplbi simp3d ssbrd syld ) A
      BCEHZCDEHZIZBDEEJZHZBDEHAVGVIAVGIZVIBGKZEHZVKDEHZIZGLZVJVNVGGMCAENZVFCMOV
      GAEUBZVPFEUCPZVEVFQZCDERSAVGQVKCUDVLVEVMVFVKCBEUAVKCDEUEUFUGVJBMOZDMOZVIV
      OULAVPVEVTVGVRVEVFUHBCERSAVPVFWAVGVRVSCDEUISGBDEEMMUMUJUKUNAVHEBDAVQVHETZ
      FVQUOEUPUQETZEURETZWBVQWCWDWBUSVPEUTVAVBPVCVD $.
  $}

  ${
    eqvreltrd.1 $e |- ( ph -> EqvRel R ) $.
    eqvreltrd.2 $e |- ( ph -> A R B ) $.
    eqvreltrd.3 $e |- ( ph -> B R C ) $.
    $( A transitivity relation for equivalences.  (Contributed by Mario
       Carneiro, 9-Jul-2014.)  (Revised by Peter Mazsa, 2-Jun-2019.) $)
    eqvreltrd $p |- ( ph -> A R C ) $=
      ( wbr eqvreltr mp2and ) ABCEICDEIBDEIGHABCDEFJK $.
  $}

  ${
    eqvreltr4d.1 $e |- ( ph -> EqvRel R ) $.
    eqvreltr4d.2 $e |- ( ph -> A R B ) $.
    eqvreltr4d.3 $e |- ( ph -> C R B ) $.
    $( A transitivity relation for equivalences.  (Contributed by Mario
       Carneiro, 9-Jul-2014.)  (Revised by Peter Mazsa, 2-Jun-2019.) $)
    eqvreltr4d $p |- ( ph -> A R C ) $=
      ( eqvrelsym eqvreltrd ) ABCDEFGADCEFHIJ $.
  $}

  ${
    $d A x $.  $d R x $.  $d ph x $.
    eqvrelref.1 $e |- ( ph -> EqvRel R ) $.
    eqvrelref.2 $e |- ( ph -> A e. dom R ) $.
    $( An equivalence relation is reflexive on its field.  Compare Theorem 3M
       of [Enderton] p. 56.  (Contributed by Mario Carneiro, 6-May-2013.)
       (Revised by Mario Carneiro, 12-Aug-2015.)  (Revised by Peter Mazsa,
       2-Jun-2019.) $)
    eqvrelref $p |- ( ph -> A R A ) $=
      ( vx cv wbr cdm wcel wex weqvrel wrel wb eqvrelrel releldmb 3syl mpbid wa
      adantr simpr eqvreltr4d exlimddv ) ABFGZCHZBBCHFABCIJZUEFKZEACLZCMUFUGNDC
      OFBCPQRAUESBUDBCAUHUEDTAUEUAZUIUBUC $.
  $}

  ${
    $d A x $.  $d B x $.  $d R x $.  $d ph x $.
    eqvrelth.1 $e |- ( ph -> EqvRel R ) $.
    eqvrelth.2 $e |- ( ph -> A e. dom R ) $.
    $( Basic property of equivalence relations.  Theorem 73 of [Suppes] p. 82.
       (Contributed by NM, 23-Jul-1995.)  (Revised by Mario Carneiro,
       6-Jul-2015.)  (Revised by Peter Mazsa, 2-Jun-2019.) $)
    eqvrelth $p |- ( ph -> ( A R B <-> [ A ] R = [ B ] R ) ) $=
      ( vx wbr cec wa wcel eqvreltr impl impbida cvv wb adantr sylancr elecALTV
      elecg wceq cv eqvrelsymb biimpa syldanl cdm vex wrel weqvrel syl brrelex2
      eqvrelrel sylan 3bitr4d eqrdv eqvrelref syl2anc mpbird simpr dmec2d mpbid
      eleqtrd eqvrelsym ) ABCDHZBDIZCDIZUAZAVDJZGVEVFVHBGUBZDHZCVIDHZVIVEKZVIVF
      KZVHVJVKAVDCBDHZVJVKAVDVNABCDEUCUDAVNVJVKACBVIDELMUEAVDVKVJABCVIDELMNVHVI
      OKZBDUFZKZVLVJPGUGZAVQVDFQVIBDOVPTRVHVOCOKZVMVKPVRADUHZVDVSADUIZVTEDULUJB
      CDUKUMVICDOOTRUNUOAVGJZCBDAWAVGEQWBBVFKZVNWBBVEVFWBBVEKZBBDHZAWEVGABDEFUP
      QWBVQVQWDWEPAVQVGFQZWFBBDVPVPSUQURAVGUSZVBWBCVPKZVQWCVNPWBVQWHWFWBBCDWGUT
      VAWFCBDVPVPSUQVAVCN $.
  $}

  ${
    eqvrelcl.1 $e |- ( ph -> EqvRel R ) $.
    eqvrelcl.2 $e |- ( ph -> A R B ) $.
    $( Elementhood in the field of an equivalence relation.  (Contributed by
       Mario Carneiro, 12-Aug-2015.)  (Revised by Peter Mazsa, 2-Jun-2019.) $)
    eqvrelcl $p |- ( ph -> A e. dom R ) $=
      ( wrel wbr cdm wcel weqvrel eqvrelrel syl releldm syl2anc ) ADGZBCDHBDIJA
      DKPEDLMFBCDNO $.
  $}

  ${
    eqvrelthi.1 $e |- ( ph -> EqvRel R ) $.
    eqvrelthi.2 $e |- ( ph -> A R B ) $.
    $( Basic property of equivalence relations.  Part of Lemma 3N of [Enderton]
       p. 57.  (Contributed by NM, 30-Jul-1995.)  (Revised by Mario Carneiro,
       9-Jul-2014.)  (Revised by Peter Mazsa, 2-Jun-2019.) $)
    eqvrelthi $p |- ( ph -> [ A ] R = [ B ] R ) $=
      ( wbr cec wceq eqvrelcl eqvrelth mpbid ) ABCDGBDHCDHIFABCDEABCDEFJKL $.
  $}

  ${
    $d A x $.  $d B x $.  $d R x $.
    $( Equivalence classes do not overlap.  In other words, two equivalence
       classes are either equal or disjoint.  Theorem 74 of [Suppes] p. 83.
       (Contributed by NM, 15-Jun-2004.)  (Revised by Mario Carneiro,
       9-Jul-2014.)  (Revised by Peter Mazsa, 2-Jun-2019.) $)
    eqvreldisj $p |- ( EqvRel R ->
        ( [ A ] R = [ B ] R \/ ( [ A ] R i^i [ B ] R ) = (/) ) ) $=
      ( vx weqvrel cec cin c0 wceq wn wcel wbr adantl cvv wb ecexr syl elecALTV
      sylancl mpbid cv wex wa simpl elinel1 vex elinel2 eqvreltr4d eqvrelthi ex
      neq0 exlimdv biimtrid orrd orcomd ) CEZACFZBCFZGZHIZUQURIZUPUTVAUTJDUAZUS
      KZDUBUPVADUSUKUPVCVADUPVCVAUPVCUCZABCUPVCUDZVDAVBBCVEVDVBUQKZAVBCLZVCVFUP
      VBUQURUEMZVDANKZVBNKZVFVGOVDVFVIVHVBACPQDUFZAVBCNNRSTVDVBURKZBVBCLZVCVLUP
      VBUQURUGMZVDBNKZVJVLVMOVDVLVOVNVBBCPQVKBVBCNNRSTUHUIUJULUMUNUO $.
  $}

  ${
    $d A x y $.  $d B x $.  $d C x y $.  $d R x y $.  $d ph x y $.
    qsdisjALTV.1 $e |- ( ph -> EqvRel R ) $.
    qsdisjALTV.2 $e |- ( ph -> B e. ( A /. R ) ) $.
    qsdisjALTV.3 $e |- ( ph -> C e. ( A /. R ) ) $.
    $( Elements of a quotient set do not overlap.  (Contributed by Rodolfo
       Medina, 12-Oct-2010.)  (Revised by Mario Carneiro, 11-Jul-2014.)
       (Revised by Peter Mazsa, 3-Jun-2019.) $)
    qsdisjALTV $p |- ( ph -> ( B = C \/ ( B i^i C ) = (/) ) ) $=
      ( vx vy wcel wceq cin c0 wo cv cec eqeq1d orbi12d wa cqs eqid eqeq1 ineq1
      eqeq2 ineq2 weqvrel ad2antrr eqvreldisj syl ectocld mpidan mpdan ) ACBEUA
      ZKCDLZCDMZNLZOZGIPZEQZDLZUTDMZNLZOZURAICBEUNUNUBZUTCLZVAUOVCUQUTCDUCVFVBU
      PNUTCDUDRSAUSBKZDUNKVDHUTJPZEQZLZUTVIMZNLZOZVDAVGTZJDBEUNVEVIDLZVJVAVLVCV
      IDUTUEVOVKVBNVIDUTUFRSVNVHBKZTEUGZVMAVQVGVPFUHUSVHEUIUJUKULUKUM $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.  $d R x $.
    $( If an element of a quotient set contains a given element, it is equal to
       the equivalence class of the element.  (Contributed by Mario Carneiro,
       12-Aug-2015.)  (Revised by Peter Mazsa, 28-Dec-2019.) $)
    eqvrelqsel $p |- ( ( EqvRel R /\ B e. ( A /. R ) /\ C e. B ) ->
                       B = [ C ] R ) $=
      ( vx weqvrel cqs wcel cec wceq cv wi eqid eleq2 eqeq1 imbi12d wbr wa cvv
      wb elecALTV el2v1 ibi simpll simpr eqvrelthi ex syl5 ectocld 3impia ) DFZ
      BADGZHCBHZBCDIZJZCEKZDIZHZUQUNJZLUMUOLUKEBADULULMUQBJURUMUSUOUQBCNUQBUNOP
      URUPCDQZUKUPAHZRZUSURUTURURUTTEUPCDSUQUAUBUCVBUTUSVBUTRUPCDUKVAUTUDVBUTUE
      UFUGUHUIUJ $.
  $}

  $( Two ways to express equivalent cosets.  (Contributed by Peter Mazsa,
     4-Jul-2020.)  (Revised by Peter Mazsa, 20-Dec-2021.) $)
  eqvrelcoss $p |- ( EqvRel ,~ R <-> TrRel ,~ R ) $=
    ( weqvrel wrefrel wsymrel wtrrel w3a df-eqvrel refrelcoss symrelcoss bitr4i
    ccoss triantru3 ) AKZBMCZMDZMEZFPMGNOPAHAILJ $.

  ${
    $d R x y z $.
    $( Two ways to express equivalent cosets.  (Contributed by Peter Mazsa,
       28-Apr-2019.) $)
    eqvrelcoss3 $p |- ( EqvRel ,~ R <->
        A. x A. y A. z ( ( x ,~ R y /\ y ,~ R z ) -> x ,~ R z ) ) $=
      ( cv ccoss wbr cdm wral wi wal wrel weqvrel relcoss biantru refrelcosslem
      wa w3a symrelcoss3 simpli triantru3 dfeqvrel3 3bitr4ri ) AEZUDDFZGAUEHIZU
      DBEZUEGZUGUDUEGJBKAKZUHUGCEZUEGQUDUJUEGJCKBKAKZRZULUELZQUKUEMUMULDNOUFUIU
      KADPUIUMABDSTUAABCUEUBUC $.
  $}

  ${
    $d R x y z $.
    $( Two ways to express equivalent cosets.  (Contributed by Peter Mazsa,
       3-May-2019.) $)
    eqvrelcoss2 $p |- ( EqvRel ,~ R <-> ,~ ,~ R C_ ,~ R ) $=
      ( vx vy vz ccoss weqvrel cv wbr wa wi wal wss eqvrelcoss3 cocossss bitr4i
      ) AEZFBGZCGZPHRDGZPHIQSPHJDKCKBKPEPLBCDAMBCDAPNO $.
  $}

  ${
    $d R x y z $.
    $( Two ways to express equivalent cosets.  (Contributed by Peter Mazsa,
       3-May-2019.)  (Revised by Peter Mazsa, 30-Sep-2021.) $)
    eqvrelcoss4 $p |- ( EqvRel ,~ R <->
        A. x A. z ( ( [ x ] ,~ R i^i [ z ] ,~ R ) =/= (/) ->
                    ( [ x ] `' R i^i [ z ] `' R ) =/= (/) ) ) $=
      ( vy ccoss weqvrel cv wbr wa wi wal cec cin c0 wne ccnv eqvrelcoss3 bitri
      trcoss2 ) CEZFAGZDGZTHUBBGZTHIUAUCTHJBKDKAKUATLUCTLMNOUACPZLUCUDLMNOJBKAK
      ADBCQADBCSR $.
  $}

  $( Alternate definition of the coelement equivalence relations class.  Other
     alternate definitions should be based on ~ eqvrelcoss2 , ~ eqvrelcoss3 and
     ~ eqvrelcoss4 when needed.  (Contributed by Peter Mazsa, 28-Nov-2022.) $)
  dfcoeleqvrels $p |- CoElEqvRels = { a | ~ a e. EqvRels } $=
    ( ccoeleqvrels cep ccnv cv cres ccoss ceqvrels wcel df-coeleqvrels df-coels
    cab ccoels eleq1i abbii eqtr4i ) BCDAEZFGZHIZALQMZHIZALAJUASATRHQKNOP $.

  $( Alternate definition of the coelement equivalence relation predicate: a
     coelement equivalence relation is an equivalence relation on coelements.
     Other alternate definitions should be based on ~ eqvrelcoss2 ,
     ~ eqvrelcoss3 and ~ eqvrelcoss4 when needed.  (Contributed by Peter Mazsa,
     28-Nov-2022.) $)
  dfcoeleqvrel $p |- ( CoElEqvRel A <-> EqvRel ~ A ) $=
    ( wcoeleqvrel cep ccnv cres weqvrel ccoels df-coeleqvrel df-coels eqvreleqi
    ccoss bitr4i ) ABCDAEKZFAGZFAHNMAIJL $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Redundancy
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z $.
    $( Define the class of all redundant sets ` x ` with respect to ` y ` in
       ` z ` .  For sets, binary relation on the class of all redundant sets
       ( ~ brredunds ) is equivalent to satisfying the redundancy predicate
       ( ~ df-redund ).  (Contributed by Peter Mazsa, 23-Oct-2022.) $)
    df-redunds $a |- Redunds =
                     `' { <. <. y , z >. , x >. |
                          ( x C_ y /\ ( x i^i z ) = ( y i^i z ) ) } $.
  $}

  $( Define the redundancy predicate.  Read: ` A ` is redundant with respect to
     ` B ` in ` C ` .  For sets, binary relation on the class of all redundant
     sets ( ~ brredunds ) is equivalent to satisfying the redundancy predicate.
     (Contributed by Peter Mazsa, 23-Oct-2022.) $)
  df-redund $a |- ( A Redund <. B , C >. <->
                 ( A C_ B /\ ( A i^i C ) = ( B i^i C ) ) ) $.

  $( Define the redundancy operator for propositions, cf. ~ df-redund .
     (Contributed by Peter Mazsa, 23-Oct-2022.) $)
  df-redundp $a |- ( redund ( ph , ps , ch ) <->
                     ( ( ph -> ps ) /\ ( ( ph /\ ch ) <-> ( ps /\ ch ) ) ) ) $.

  ${
    $d A x y z $.  $d B x y z $.  $d C x y z $.
    $( Binary relation on the class of all redundant sets.  (Contributed by
       Peter Mazsa, 25-Oct-2022.) $)
    brredunds $p |- ( ( A e. V /\ B e. W /\ C e. X ) ->
                      ( A Redunds <. B , C >. <->
                        ( A C_ B /\ ( A i^i C ) = ( B i^i C ) ) ) ) $=
      ( vx vy vz cv wss cin wceq wa credunds w3a wb sseq12 3adant3 ineq12
      3adant2 3adant1 eqeq12d anbi12d df-redunds brcnvrabga ) GJZHJZKZUGIJZLZUH
      UJLZMZNABKZACLZBCLZMZNGHIABCODEFUGAMZUHBMZUJCMZPZUIUNUMUQURUSUIUNQUTUGAUH
      BRSVAUKUOULUPURUTUKUOMUSUGAUJCTUAUSUTULUPMURUHBUJCTUBUCUDGHIUEUF $.
  $}

  $( For sets, binary relation on the class of all redundant sets
     ( ~ brredunds ) is equivalent to satisfying the redundancy predicate
     ( ~ df-redund ).  (Contributed by Peter Mazsa, 25-Oct-2022.) $)
  brredundsredund $p |- ( ( A e. V /\ B e. W /\ C e. X ) ->
      ( A Redunds <. B , C >. <-> A Redund <. B , C >. ) ) $=
    ( wcel w3a cop credunds wbr wss wceq wa wredund brredunds df-redund bitr4di
    cin ) ADGBEGCFGHABCIJKABLACSBCSMNABCOABCDEFPABCQR $.

  ${
    redundss3.1 $e |- D C_ C $.
    $( Implication of redundancy predicate.  (Contributed by Peter Mazsa,
       26-Oct-2022.) $)
    redundss3 $p |- ( A Redund <. B , C >. -> A Redund <. B , D >. ) $=
      ( wss cin wceq wa wredund ineq1 dfss mpbi incom eqtri ineq2i inass eqtr4i
      3eqtr4g df-redund anim2i 3imtr4i ) ABFZACGZBCGZHZIUCADGZBDGZHZIABCJABDJUF
      UIUCUFUDDGZUEDGZUGUHUDUEDKUGACDGZGUJDULADDCGZULDCFDUMHEDCLMDCNOZPACDQRUHB
      ULGUKDULBUNPBCDQRSUAABCTABDTUB $.
  $}

  ${
    redundeq1.1 $e |- A = D $.
    $( Equivalence of redundancy predicates.  (Contributed by Peter Mazsa,
       26-Oct-2022.) $)
    redundeq1 $p |- ( A Redund <. B , C >. <-> D Redund <. B , C >. ) $=
      ( wss cin wceq wa wredund sseq1i ineq1i eqeq1i anbi12i df-redund 3bitr4i
      ) ABFZACGZBCGZHZIDBFZDCGZSHZIABCJDBCJQUATUCADBEKRUBSADCELMNABCODBCOP $.
  $}

  ${
    redundpim3.1 $e |- ( th -> ch ) $.
    $( Implication of redundancy of proposition.  (Contributed by Peter Mazsa,
       26-Oct-2022.) $)
    redundpim3 $p |- ( redund ( ph , ps , ch ) -> redund ( ph , ps , th ) ) $=
      ( wi wa wredundp anbi1 pm4.71ri bianass 3bitr4g anim2i df-redundp 3imtr4i
      wb ) ABFZACGZBCGZPZGQADGZBDGZPZGABCHABDHTUCQTRDGSDGUAUBRSDIDCDADCEJZKDCDB
      UDKLMABCNABDNO $.
  $}

  ${
    redundpbi1.1 $e |- ( ph <-> th ) $.
    $( Equivalence of redundancy of propositions.  (Contributed by Peter Mazsa,
       25-Oct-2022.) $)
    redundpbi1 $p |- ( redund ( ph , ps , ch ) <-> redund ( th , ps , ch ) ) $=
      ( wi wa wb wredundp imbi1i anbi1i bibi1i anbi12i df-redundp 3bitr4i ) ABF
      ZACGZBCGZHZGDBFZDCGZRHZGABCIDBCIPTSUBADBEJQUARADCEKLMABCNDBCNO $.
  $}

  $( The naive version of the class of reflexive relations is redundant with
     respect to the class of reflexive relations (see ~ dfrefrels2 ) if the
     relations are symmetric as well.  (Contributed by Peter Mazsa,
     26-Oct-2022.) $)
  refrelsredund4 $p |- { r e. Rels | ( _I |` dom r ) C_ r } Redund
                                     <. RefRels , ( RefRels i^i SymRels ) >. $=
    ( cid cv cdm cres wss crels crab crefrels csymrels cin wredund wceq crn cxp
    wi inxpssres sstr2 in32 inass ssrabi dfrefrels2 sseqtrri ccnv wa dfsymrels2
    ax-mp ineq2i refsymrels2 3eqtr4i ineq1i 3eqtr3ri 3eqtri df-redund mpbir2an
    inrab ) BACZDZEZUQFZAGHZIIJKZLVAIFVAVBKZIVBKZMVABURUQNZOKZUQFZAGHIUTVGAGVFU
    SFUTVGPURVEBQVFUSUQRUGUAAUBUCVCVBIKZIIKJKVDVAJKZIKVAIKJKVHVCVAJISVIVBIVAUQU
    DUQFZAGHZKUTVJUEAGHVIVBUTVJAGUPJVKVAAUFUHAUIUJUKVAIJTULIJISIIJTUMVAIVBUNUO
    $.

  $( The naive version of the class of reflexive relations is redundant with
     respect to the class of reflexive relations (see ~ dfrefrels2 ) in the
     class of equivalence relations.  (Contributed by Peter Mazsa,
     26-Oct-2022.) $)
  refrelsredund2 $p |-
      { r e. Rels | ( _I |` dom r ) C_ r } Redund <. RefRels , EqvRels >. $=
    ( cid cdm cres wss crels crab crefrels csymrels cin ceqvrels refrelsredund4
    cv wredund ctrrels df-eqvrels inss1 eqsstri redundss3 ax-mp ) BAMZCDUAEAFGZ
    HHIJZNUBHKNALUBHUCKKUCOJUCPUCOQRST $.

  ${
    $d r x $.
    $( The naive version of the class of reflexive relations
       ` { r e. Rels | A. x e. dom r x r x } ` is redundant with respect to the
       class of reflexive relations (see ~ dfrefrels3 ) in the class of
       equivalence relations.  (Contributed by Peter Mazsa, 26-Oct-2022.) $)
    refrelsredund3 $p |-
       { r e. Rels | A. x e. dom r x r x } Redund <. RefRels , EqvRels >. $=
      ( cid cv cdm cres wss crels crab crefrels ceqvrels wredund refrelsredund2
      wbr wral idrefALT rabbii redundeq1 mpbi ) CBDZEZFTGZBHIZJKLADZUDTNAUAOZBH
      IZJKLBMUCJKUFUBUEBHAUATPQRS $.
  $}

  $( The naive version of the definition of reflexive relation is redundant
     with respect to reflexive relation (see ~ dfrefrel2 ) if the relation is
     symmetric as well.  (Contributed by Peter Mazsa, 26-Oct-2022.) $)
  refrelredund4 $p |- redund ( ( ( _I |` dom R ) C_ R /\ Rel R ) ,
                               RefRel R ,
                               ( RefRel R /\ SymRel R ) ) $=
    ( cid cdm cres wss wrel wa wrefrel wsymrel wredundp wi wb crn cxp inxpssres
    cin sstr2 ax-mp anim1i anbi2i dfrefrel2 sylibr an12 ccnv anandir refsymrel2
    dfsymrel2 3bitr4i bitr4i df-redundp mpbir2an ) BACZDZAEZAFZGZAHZUQAIZGZJUPU
    QKUPUSGZUQUSGZLUPBULAMZNPZAEZUOGUQUNVDUOVCUMEUNVDKULVBBOVCUMAQRSAUAUBUTUQUP
    URGZGVAUPUQURUCUSVEUQUNAUDAEZGUOGUPVFUOGZGUSVEUNVFUOUEAUFURVGUPAUGTUHTUIUPU
    QUSUJUK $.

  $( The naive version of the definition of reflexive relation is redundant
     with respect to reflexive relation (see ~ dfrefrel2 ) in equivalence
     relation.  (Contributed by Peter Mazsa, 25-Oct-2022.) $)
  refrelredund2 $p |-
      redund ( ( ( _I |` dom R ) C_ R /\ Rel R ) , RefRel R , EqvRel R ) $=
    ( cid cdm cres wss wa wrefrel wsymrel wredundp weqvrel refrelredund4 wtrrel
    wrel w3a df-eqvrel 3simpa sylbi redundpim3 ax-mp ) BACDAEAMFZAGZUAAHZFZITUA
    AJZIAKTUAUCUDUDUAUBALZNUCAOUAUBUEPQRS $.

  ${
    $d R x $.
    $( The naive version of the definition of reflexive relation
       ` ( A. x e. dom R x R x /\ Rel R ) ` is redundant with respect to
       reflexive relation (see ~ dfrefrel3 ) in equivalence relation.
       (Contributed by Peter Mazsa, 25-Oct-2022.) $)
    refrelredund3 $p |-
        redund ( ( A. x e. dom R x R x /\ Rel R ) , RefRel R , EqvRel R ) $=
      ( cid cdm cres wss wrel wa wrefrel weqvrel wredundp cv wral refrelredund2
      wbr idrefALT anbi1i redundpbi1 mpbi ) CBDZEBFZBGZHZBIZBJZKALZUFBOATMZUBHZ
      UDUEKBNUCUDUEUHUAUGUBATBPQRS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Domain quotients
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y $.
    $( Define the class of domain quotients.  Domain quotients are pairs of
       sets, typically a relation and a set, where the quotient (see ~ df-qs )
       of the relation on its domain is equal to the set.  See comments of
       ~ df-ers for the motivation for this definition.  (Contributed by Peter
       Mazsa, 16-Apr-2019.) $)
    df-dmqss $a |- DomainQss = { <. x , y >. | ( dom x /. x ) = y } $.
  $}

  $( Define the domain quotient predicate.  (Read: the domain quotient of ` R `
     is ` A ` .)  If ` A ` and ` R ` are sets, the domain quotient binary
     relation and the domain quotient predicate are the same, see ~ brdmqssqs .
     (Contributed by Peter Mazsa, 9-Aug-2021.) $)
  df-dmqs $a |- ( R DomainQs A <-> ( dom R /. R ) = A ) $.

  $( Equality theorem for domain quotient.  (Contributed by Peter Mazsa,
     17-Apr-2019.) $)
  dmqseq $p |- ( R = S -> ( dom R /. R ) = ( dom S /. S ) ) $=
    ( cdm wceq cqs dmeq qseq12 mpancom ) ACZBCZDABDIAEJBEDABFIJABGH $.

  ${
    dmqseqi.1 $e |- R = S $.
    $( Equality theorem for domain quotient, inference version.  (Contributed
       by Peter Mazsa, 26-Sep-2021.) $)
    dmqseqi $p |- ( dom R /. R ) = ( dom S /. S ) $=
      ( wceq cdm cqs dmqseq ax-mp ) ABDAEAFBEBFDCABGH $.
  $}

  ${
    dmqseqd.1 $e |- ( ph -> R = S ) $.
    $( Equality theorem for domain quotient set, deduction version.
       (Contributed by Peter Mazsa, 23-Apr-2021.) $)
    dmqseqd $p |- ( ph -> ( dom R /. R ) = ( dom S /. S ) ) $=
      ( wceq cdm cqs dmqseq syl ) ABCEBFBGCFCGEDBCHI $.
  $}

  $( Equality theorem for domain quotient.  (Contributed by Peter Mazsa,
     17-Apr-2019.) $)
  dmqseqeq1 $p |- ( R = S ->
                    ( ( dom R /. R ) = A <-> ( dom S /. S ) = A ) ) $=
    ( wceq cdm cqs dmqseq eqeq1d ) BCDBEBFCECFABCGH $.

  ${
    dmqseqeq1i.1 $e |- R = S $.
    $( Equality theorem for domain quotient, inference version.  (Contributed
       by Peter Mazsa, 26-Sep-2021.) $)
    dmqseqeq1i $p |- ( ( dom R /. R ) = A <-> ( dom S /. S ) = A ) $=
      ( wceq cdm cqs wb dmqseqeq1 ax-mp ) BCEBFBGAECFCGAEHDABCIJ $.
  $}

  ${
    dmqseqeq1d.1 $e |- ( ph -> R = S ) $.
    $( Equality theorem for domain quotient set, deduction version.
       (Contributed by Peter Mazsa, 26-Sep-2021.) $)
    dmqseqeq1d $p |- ( ph ->
                       ( ( dom R /. R ) = A <-> ( dom S /. S ) = A ) ) $=
      ( wceq cdm cqs wb dmqseqeq1 syl ) ACDFCGCHBFDGDHBFIEBCDJK $.
  $}

  ${
    $d A x y $.  $d R x y $.
    $( The domain quotient binary relation.  (Contributed by Peter Mazsa,
       17-Apr-2019.) $)
    brdmqss $p |- ( ( A e. V /\ R e. W ) ->
                    ( R DomainQss A <-> ( dom R /. R ) = A ) ) $=
      ( vx vy wcel cdmqss wbr cdm cqs wb cv dmqseq id eqeqan12d df-dmqss brabga
      wceq ancoms ) BDGACGBAHIBJBKZASZLEMZJUCKZFMZSUBEFBAHDCUCBSUEASZUDUAUEAUCB
      NUFOPEFQRT $.
  $}

  $( If ` A ` and ` R ` are sets, the domain quotient binary relation and the
     domain quotient predicate are the same.  (Contributed by Peter Mazsa,
     14-Aug-2021.) $)
  brdmqssqs $p |- ( ( A e. V /\ R e. W ) ->
                    ( R DomainQss A <-> R DomainQs A ) ) $=
    ( wcel wa cdmqss wbr cdm cqs wceq wdmqs brdmqss df-dmqs bitr4di ) ACEBDEFBA
    GHBIBJAKABLABCDMABNO $.

  $( The empty set is not an element of a domain quotient.  (Contributed by
     Peter Mazsa, 2-Mar-2018.) $)
  n0eldmqs $p |- -. (/) e. ( dom R /. R ) $=
    ( c0 cdm cqs wcel wn wss ssid n0elqs mpbir ) BACZADEFKKGKHKAIJ $.

  ${
    $d A u $.  $d B u v $.  $d R u v $.
    $( The quotient set equal to a class.

       This theorem is used when a class ` A ` is identified with a quotient
       ` ( dom R /. R ) ` .  In such a situation, every element ` u e. A ` is
       an ` R `-coset ` [ v ] R ` for some ` v e. dom R ` , but there is no
       requirement that the "witness" ` v ` be equal to its own block
       ` [ v ] R ` . ` A ` is a set of blocks (equivalence classes), not a set
       of raw witnesses.  In particular, when ` ( dom R /. R ) = A ` is read
       together with a partition hypothesis ` R Part A ` (defined as
       ~ dfpart2 ), ` A ` is being treated as the set of blocks ` [ v ] R ` ;
       it does not assert any fixed-point condition ` v = [ v ] R ` such as
       would arise from the mistaken reading ` u e. A <-> u = [ u ] R ` .  Cf.
       ~ dmqsblocks .  (Contributed by Peter Mazsa, 19-Oct-2018.) $)
    qseq $p |- ( ( B /. R ) = A <->
                 A. u ( u e. A <-> E. v e. B u = [ v ] R ) ) $=
      ( cqs wceq cv cec wrex cab wcel wb wal df-qs eqeq2i eqcom eqabb 3bitr3i )
      CDEFZGCBHZAHEIGADJZBKZGTCGUACLUBMBNTUCCABDEOPCTQUBBCRS $.
  $}

  $( The empty set is not an element of a domain quotient.  (Contributed by
     Peter Mazsa, 3-Nov-2018.) $)
  n0eldmqseq $p |- ( ( dom R /. R ) = A -> -. (/) e. A ) $=
    ( cdm cqs wceq c0 wcel n0eldmqs eleq2 mtbii ) BCBDZAEFKGFAGBHKAFIJ $.

  $( Implication of that the empty set is not an element of a class.
     (Contributed by Peter Mazsa, 30-Dec-2024.) $)
  n0elim $p |- ( -. (/) e. A ->
                 ( dom ( `' _E |` A ) /. ( `' _E |` A ) ) = A ) $=
    ( c0 wcel cep ccnv cres cdm cqs wceq n0el2 biimpi qseq1d qsresid qsid eqtri
    wn eqtrdi ) BACPZDEZAFZGZTHATHZARUAATRUAAIAJKLUBASHAASMANOQ $.

  $( Two ways of expressing that the empty set is not an element of a class.
     (Contributed by Peter Mazsa, 27-May-2021.) $)
  n0el3 $p |- ( -. (/) e. A <->
                ( dom ( `' _E |` A ) /. ( `' _E |` A ) ) = A ) $=
    ( c0 wcel wn cep ccnv cres cdm cqs wceq n0elim n0eldmqseq impbii ) BACDEFAG
    ZHNIAJAKANLM $.

  $( The domain quotient binary relation of the restricted converse epsilon
     relation is equivalent to the negated elementhood of the empty set in the
     restriction.  (Contributed by Peter Mazsa, 14-Aug-2021.) $)
  cnvepresdmqss $p |- ( A e. V ->
                        ( ( `' _E |` A ) DomainQss A <-> -. (/) e. A ) ) $=
    ( wcel cep ccnv cres cdmqss wbr cdm cqs wceq c0 wn cnvepresex brdmqss mpdan
    cvv wb n0el3 bitr4di ) ABCZDEAFZAGHZUBIUBJAKZLACMUAUBQCUCUDRABNAUBBQOPAST
    $.

  $( The domain quotient predicate for the restricted converse epsilon relation
     is equivalent to the negated elementhood of the empty set in the
     restriction.  (Contributed by Peter Mazsa, 14-Aug-2021.) $)
  cnvepresdmqs $p |- ( ( `' _E |` A ) DomainQs A <-> -. (/) e. A ) $=
    ( cep ccnv cres wdmqs cdm cqs wceq c0 wcel wn df-dmqs n0el3 bitr4i ) ABCADZ
    EOFOGAHIAJKAOLAMN $.

  $( The range of a relation is equal to the union of the domain quotient.
     (Contributed by Peter Mazsa, 13-Oct-2018.) $)
  unidmqs $p |- ( R e. V -> ( Rel R -> U. ( dom R /. R ) = ran R ) ) $=
    ( wcel wrel cdm cqs cuni crn wceq cres cvv rnresequniqs syl resdm sylan9req
    resexg rneqd ex ) ABCZADZAEZAFGZAHZISTUBAUAJZHZUCSUDKCUEUBIAUABPUAAKLMTUDAA
    NQOR $.

  $( The union of the domain quotient of a relation is equal to the class ` A `
     if and only if the range is equal to it as well.  (Contributed by Peter
     Mazsa, 21-Apr-2019.)  (Revised by Peter Mazsa, 28-Dec-2021.) $)
  unidmqseq $p |- ( R e. V ->
                    ( Rel R ->
                      ( U. ( dom R /. R ) = A <-> ran R = A ) ) ) $=
    ( wcel wrel cdm cqs cuni wceq crn wb wa unidmqs imp eqeq1d ex ) BCDZBEZBFBG
    HZAIBJZAIKQRLSTAQRSTIBCMNOP $.

  $( If the domain quotient of a relation is equal to the class ` A ` , then
     the range of the relation is the union of the class.  (Contributed by
     Peter Mazsa, 29-Dec-2021.) $)
  dmqseqim $p |- ( R e. V ->
                   ( Rel R ->
                     ( ( dom R /. R ) = A -> ran R = U. A ) ) ) $=
    ( wcel wrel cdm cqs wceq crn cuni wi wa unieq wb unidmqseq imp imbitrid ex
    ) BCDZBEZBFBGZAHZBIAJZHZKUBUAJUCHZSTLUDUAAMSTUEUDNUCBCOPQR $.

  $( Lemma for ~ erimeq2 .  (Contributed by Peter Mazsa, 29-Dec-2021.) $)
  dmqseqim2 $p |- ( R e. V -> ( Rel R ->
      ( ( dom R /. R ) = A -> ( B e. ran R <-> B e. U. A ) ) ) ) $=
    ( wcel wrel cdm cqs wceq crn cuni wb dmqseqim eleq2 syl8 ) CDECFCGCHAICJZAK
    ZIBPEBQELACDMPQBNO $.

  ${
    $d A u x $.  $d R u x $.
    $( Elementhood in the domain quotient of a relation.  (Contributed by Peter
       Mazsa, 24-Apr-2021.) $)
    releldmqs $p |- ( A e. V ->
                      ( Rel R ->
                        ( A e. ( dom R /. R ) <->
                          E. u e. dom R E. x e. [ u ] R A = [ u ] R ) ) ) $=
      ( wcel wrel cdm cqs cv cec wceq wrex wb cres resdm dmqseqd eleq2d adantl
      wa eldmqsres2 adantr bitr3d ex ) CEFZDGZCDHZDIZFZCBJDKZLAUJMBUGMZNUEUFTCD
      UGOZHULIZFZUIUKUFUNUINUEUFUMUHCUFULDDPQRSUEUNUKNUFABUGCDEUAUBUCUD $.
  $}

  ${
    $d A u x $.  $d B u x $.  $d R u x $.
    $( Elementhood in the domain quotient of the class of cosets by a
       restriction.  (Contributed by Peter Mazsa, 4-May-2019.) $)
    eldmqs1cossres $p |- ( B e. V ->
        ( B e. ( dom ,~ ( R |` A ) /. ,~ ( R |` A ) ) <->
          E. u e. A E. x e. [ u ] R B = [ x ] ,~ ( R |` A ) ) ) $=
      ( wcel cres ccoss cdm cqs cv cec wrex wceq wa wex df-rex exbii bitri cvv
      elqsg wb eldm1cossres2 elv anbi1i bitrdi rexbii rexcom4 r19.41v bitr4di )
      DFGZDECHIZJZUMKGZALZBLEMZGZBCNZDUPUMMOZPZAQZUTAUQNZBCNZULUOUTAUNNZVBAUNDU
      MFUBVEUPUNGZUTPZAQVBUTAUNRVGVAAVFUSUTVFUSUCABCUPEUAUDUEUFSTUGVDURUTPZAQZB
      CNZVBVCVIBCUTAUQRUHVJVHBCNZAQVBVHBACUIVKVAAURUTBCUJSTTUK $.
  $}

  ${
    $d A u x $.  $d R u x $.
    $( Elementhood in the domain quotient of the class of cosets by a relation.
       (Contributed by Peter Mazsa, 23-Apr-2021.) $)
    releldmqscoss $p |- ( A e. V ->
                          ( Rel R ->
                            ( A e. ( dom ,~ R /. ,~ R ) <->
          E. u e. dom R E. x e. [ u ] R A = [ x ] ,~ R ) ) ) $=
      ( wcel wrel ccoss cdm cqs cv wceq wrex wb wa eldmqs1cossres adantr adantl
      cec cres resdm cosseqd dmqseqd eleq2d eceq2d eqeq2d 2rexbidv 3bitr3d ex )
      CEFZDGZCDHZIULJZFZCAKZULSZLZABKDSZMBDIZMZNUJUKOCDUSTZHZIVBJZFZCUOVBSZLZAU
      RMBUSMZUNUTUJVDVGNUKABUSCDEPQUKVDUNNUJUKVCUMCUKVBULUKVADDUAUBZUCUDRUKVGUT
      NUJUKVFUQBAUSURUKVEUPCUKVBULUOVHUEUFUGRUHUI $.
  $}

  $( Two ways to express the equality of the domain quotient of the coelements
     on the class ` A ` with the class ` A ` .  (Contributed by Peter Mazsa,
     26-Sep-2021.) $)
  dmqscoelseq $p |- ( ( dom ~ A /. ~ A ) = A <-> ( U. A /. ~ A ) = A ) $=
    ( ccoels cdm cqs cuni dmcoels qseq1i eqeq1i ) ABZCZIDAEZIDAJKIAFGH $.

  $( Two ways to express the equality of the domain quotient of the coelements
     on the class ` A ` with the class ` A ` .  (Contributed by Peter Mazsa,
     26-Sep-2021.) $)
  dmqs1cosscnvepreseq $p |-
      ( ( dom ,~ ( `' _E |` A ) /. ,~ ( `' _E |` A ) ) = A <->
        ( U. A /. ~ A ) = A ) $=
    ( cep ccnv cres ccoss cdm cqs ccoels df-coels dmqseqeq1i dmqscoelseq bitr3i
    wceq cuni ) BCADEZFOGAMAHZFPGAMANPGAMAPOAIJAKL $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Equivalence relations on domain quotients
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define the class of equivalence relations on domain quotients (or: domain
     quotients restricted to equivalence relations).

     The present definition of equivalence relation in set.mm ~ df-er "is not
     standard", "somewhat cryptic", has no constant 0-ary class and does not
     follow the traditional transparent reflexive-symmetric-transitive relation
     way of definition of equivalence.  Definitions ~ df-eqvrels ,
     ~ dfeqvrels2 , ~ dfeqvrels3 and ~ df-eqvrel , ~ dfeqvrel2 , ~ dfeqvrel3
     are fully transparent in this regard.  However, they lack the domain
     component ( ` dom R = A ` ) of the present ~ df-er .  While we acknowledge
     the need of a domain component, the present ~ df-er definition does not
     utilize the results revealed by the new theorems in the
     Partition-Equivalence Theorem part below (like ~ pets and ~ pet ).  From
     those theorems follows that the natural domain of equivalence relations is

     not ` R Domain A ` (i.e. ` dom R = A ` see ~ brdomaing ),

     but ` R DomainQss A ` (i.e. ` ( dom R /. R ) = A ` , see ~ brdmqss ), see
     ~ erimeq vs. ~ prter3 .

     While I'm sure we need both equivalence relation ~ df-eqvrels and
     equivalence relation on domain quotient ~ df-ers , I'm not sure whether we
     need a third equivalence relation concept with the present ` dom R = A `
     component as well: this needs further investigation.  As a default I
     suppose that these two concepts ~ df-eqvrels and ~ df-ers are enough and
     named the predicate version of the one on domain quotient as the alternate
     version ~ df-erALTV of the present ~ df-er .  (Contributed by Peter Mazsa,
     26-Jun-2021.) $)
  df-ers $a |- Ers = ( DomainQss |` EqvRels ) $.

  $( Equivalence relation with natural domain predicate, see also the comment
     of ~ df-ers .  Alternate definition is ~ dferALTV2 .  Binary equivalence
     relation with natural domain and the equivalence relation with natural
     domain predicate are the same when ` A ` and ` R ` are sets, see
     ~ brerser .  (Contributed by Peter Mazsa, 12-Aug-2021.) $)
  df-erALTV $a |- ( R ErALTV A <-> ( EqvRel R /\ R DomainQs A ) ) $.

  $( Define the class of comember equivalence relations on their domain
     quotients.  (Contributed by Peter Mazsa, 28-Nov-2022.)  (Revised by Peter
     Mazsa, 24-Jul-2023.) $)
  df-comembers $a |- CoMembErs = { a | ,~ ( `' _E |` a ) Ers a } $.

  $( Define the comember equivalence relation on the class ` A ` (or, the
     restricted coelement equivalence relation on its domain quotient ` A ` .)
     Alternate definitions are ~ dfcomember2 and ~ dfcomember3 .

     Later on, in an application of set theory I make a distinction between the
     default elementhood concept and a special membership concept: membership
     equivalence relation will be an integral part of that membership concept.
     (Contributed by Peter Mazsa, 26-Jun-2021.)  (Revised by Peter Mazsa,
     28-Nov-2022.) $)
  df-comember $a |- ( CoMembEr A <-> ,~ ( `' _E |` A ) ErALTV A ) $.

  $( Binary equivalence relation with natural domain, see the comment of
     ~ df-ers .  (Contributed by Peter Mazsa, 23-Jul-2021.) $)
  brers $p |- ( A e. V ->
                ( R Ers A <-> ( R e. EqvRels /\ R DomainQss A ) ) ) $=
    ( ceqvrels cers cdmqss df-ers eqres ) BADEFCGH $.

  $( Equivalence relation with natural domain predicate, see the comment of
     ~ df-ers .  (Contributed by Peter Mazsa, 26-Jun-2021.)  (Revised by Peter
     Mazsa, 30-Aug-2021.) $)
  dferALTV2 $p |- ( R ErALTV A <-> ( EqvRel R /\ ( dom R /. R ) = A ) ) $=
    ( werALTV weqvrel wdmqs wa cdm cqs wceq df-erALTV df-dmqs anbi2i bitri ) AB
    CBDZABEZFNBGBHAIZFABJOPNABKLM $.

  $( Equality theorem for equivalence relation on domain quotient.
     (Contributed by Peter Mazsa, 25-Sep-2021.) $)
  erALTVeq1 $p |- ( R = S -> ( R ErALTV A <-> S ErALTV A ) ) $=
    ( wceq weqvrel cdm cqs werALTV eqvreleq dmqseqeq1 anbi12d dferALTV2 3bitr4g
    wa ) BCDZBEZBFBGADZNCEZCFCGADZNABHACHOPRQSBCIABCJKABLACLM $.

  ${
    erALTVeq1i.1 $e |- R = S $.
    $( Equality theorem for equivalence relation on domain quotient, inference
       version.  (Contributed by Peter Mazsa, 25-Sep-2021.) $)
    erALTVeq1i $p |- ( R ErALTV A <-> S ErALTV A ) $=
      ( wceq werALTV wb erALTVeq1 ax-mp ) BCEABFACFGDABCHI $.
  $}

  ${
    erALTVeq1d.1 $e |- ( ph -> R = S ) $.
    $( Equality theorem for equivalence relation on domain quotient, deduction
       version.  (Contributed by Peter Mazsa, 25-Sep-2021.) $)
    erALTVeq1d $p |- ( ph -> ( R ErALTV A <-> S ErALTV A ) ) $=
      ( wceq werALTV wb erALTVeq1 syl ) ACDFBCGBDGHEBCDIJ $.
  $}

  $( Alternate definition of the comember equivalence relation.  (Contributed
     by Peter Mazsa, 28-Nov-2022.) $)
  dfcomember $p |- ( CoMembEr A <-> ~ A ErALTV A ) $=
    ( wcomember ccnv cres werALTV ccoels df-comember df-coels erALTVeq1i bitr4i
    cep ccoss ) ABAKCADLZEAAFZEAGANMAHIJ $.

  $( Alternate definition of the comember equivalence relation.  (Contributed
     by Peter Mazsa, 25-Sep-2021.) $)
  dfcomember2 $p |- ( CoMembEr A <->
                      ( EqvRel ~ A /\ ( dom ~ A /. ~ A ) = A ) ) $=
    ( wcomember ccoels werALTV weqvrel cdm cqs wceq dfcomember dferALTV2 bitri
    wa ) ABAACZDMEMFMGAHLAIAMJK $.

  $( Alternate definition of the comember equivalence relation.  (Contributed
     by Peter Mazsa, 26-Sep-2021.)  (Revised by Peter Mazsa, 17-Jul-2023.) $)
  dfcomember3 $p |- ( CoMembEr A <->
                      ( CoElEqvRel A /\ ( U. A /. ~ A ) = A ) ) $=
    ( wcomember ccoels weqvrel cdm wceq wa wcoeleqvrel dfcomember2 dfcoeleqvrel
    cqs cuni bicomi dmqscoelseq anbi12i bitri ) ABACZDZQEQKAFZGAHZALQKAFZGAIRTS
    UATRAJMANOP $.

  $( Two ways to express comember equivalence relation on its domain quotient.
     (Contributed by Peter Mazsa, 26-Sep-2021.)  (Revised by Peter Mazsa,
     17-Jul-2023.) $)
  eqvreldmqs $p |- ( ( EqvRel ,~ ( `' _E |` A ) /\
                       ( dom ,~ ( `' _E |` A ) /. ,~ ( `' _E |` A ) ) = A ) <->
                     ( CoElEqvRel A /\ ( U. A /. ~ A ) = A ) ) $=
    ( cep ccnv cres ccoss weqvrel wcoeleqvrel cdm cqs wceq ccoels df-coeleqvrel
    cuni bicomi dmqs1cosscnvepreseq anbi12i ) BCADEZFZAGZQHQIAJAMAKIAJSRALNAOP
    $.

  $( Two ways to express comember equivalence relation on its domain quotient.
     (Contributed by Peter Mazsa, 30-Dec-2024.) $)
  eqvreldmqs2 $p |- ( ( EqvRel ,~ ( `' _E |` A ) /\
                       ( dom ,~ ( `' _E |` A ) /. ,~ ( `' _E |` A ) ) = A ) <->
                     ( EqvRel ~ A /\ ( U. A /. ~ A ) = A ) ) $=
    ( cep ccnv cres ccoss weqvrel ccoels cdm cqs wceq df-coels eqvreleqi bicomi
    cuni dmqs1cosscnvepreseq anbi12i ) BCADEZFZAGZFZQHQIAJANSIAJTRSQAKLMAOP $.

  $( Binary equivalence relation with natural domain and the equivalence
     relation with natural domain predicate are the same when ` A ` and ` R `
     are sets.  (Contributed by Peter Mazsa, 25-Aug-2021.) $)
  brerser $p |- ( ( A e. V /\ R e. W ) -> ( R Ers A <-> R ErALTV A ) ) $=
    ( wcel wa cers ceqvrels cdmqss werALTV wb brers adantr weqvrel eleqvrelsrel
    wbr wdmqs adantl brdmqssqs anbi12d df-erALTV bitr4di bitrd ) ACEZBDEZFZBAGP
    ZBHEZBAIPZFZABJZUDUGUJKUEABCLMUFUJBNZABQZFUKUFUHULUIUMUEUHULKUDBDORABCDSTAB
    UAUBUC $.

  ${
    $d A u x y $.  $d R u x y $.  $d V x y $.
    $( Equivalence relation on its natural domain implies that the class of
       coelements on the domain is equal to the relation (this is ~ prter3 in a
       more convenient form , see also ~ erimeq ).  (Contributed by Rodolfo
       Medina, 19-Oct-2010.)  (Proof shortened by Mario Carneiro, 12-Aug-2015.)
       (Revised by Peter Mazsa, 29-Dec-2021.) $)
    erimeq2 $p |- ( R e. V ->
                  ( ( EqvRel R /\ ( dom R /. R ) = A ) -> ~ A = R ) ) $=
      ( vx vy vu wcel wceq wa wrel ad2antrl cv wbr wrex wb simpll eleq2d bitrdi
      cvv el2v weqvrel cdm cqs ccoels relcoels a1i eqvrelrel brcoels cec simprl
      simplr eleqtrrd simprr eqvrelqsel syl3anc elecALTV anassrs pm5.32da simpr
      rexbidva adantl eqvrelcl adantll cuni eqvrelim dmqseqim2 syl5 imp32 bitrd
      crn wi eluni2 adantr mpbid pm4.71rd r19.41v bitr4di bitr4d bitrid eqbrrdv
      ex ) BCGZBUAZBUBZBUCZAHZIZAUDZBHWBWGIZDEWHBWHJWIAUEUFWCBJZWBWFBUGZKDLZELZ
      WHMZWLFLZGZWMWOGZIZFANZWIWLWMBMZWNWSODEFAWLWMSSUHTWIWSWPWTIZFANZWTWGWSXBO
      WBWGWRXAFAWGWOAGZIWPWQWTWGXCWPWQWTOWGXCWPIZIZWQWMWLBUIZGZWTXEWOXFWMXEWCWO
      WEGWPWOXFHWCWFXDPXEWOAWEWGXCWPUJWCWFXDUKULWGXCWPUMWDWOWLBUNUOQXGWTODEWLWM
      BSSUPTRUQURUTVAWIWTWPFANZWTIXBWIWTXHWIWTXHWIWTIWLWDGZXHWGWTXIWBWGWTIWLWMB
      WCWFWTPWGWTUSVBVCWIXIXHOWTWIXIWLAVDGZXHWIXIWLBVJZGZXJWIWDXKWLWCWDXKHWBWFB
      VEKQWBWCWFXLXJOZWCWJWBWFXMVKWKAWLBCVFVGVHVIFWLAVLRVMVNWAVOWPWTFAVPVQVRVSV
      TWA $.
  $}

  $( Equivalence relation on its natural domain implies that the class of
     coelements on the domain is equal to the relation (this is the most
     convenient form of ~ prter3 and ~ erimeq2 ).  (Contributed by Peter Mazsa,
     7-Oct-2021.)  (Revised by Peter Mazsa, 29-Dec-2021.) $)
  erimeq $p |- ( R e. V -> ( R ErALTV A -> ~ A = R ) ) $=
    ( werALTV weqvrel cdm cqs wceq wa wcel ccoels dferALTV2 erimeq2 biimtrid )
    ABDBEBFBGAHIBCJAKBHABLABCMN $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Functions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define the class of all function sets (but not necessarily function
     relations, cf. ~ df-funsALTV ).  It is used only by ~ df-funsALTV .
     (Contributed by Peter Mazsa, 17-Jul-2021.) $)
  df-funss $a |- Funss = { x | ,~ x e. CnvRefRels } $.

  $( Define the function relations class, i.e., the class of functions.
     Alternate definitions are ~ dffunsALTV , ... , ~ dffunsALTV5 .
     (Contributed by Peter Mazsa, 17-Jul-2021.) $)
  df-funsALTV $a |- FunsALTV = ( Funss i^i Rels ) $.

  $( Define the function relation predicate, i.e., the function predicate.
     This definition of the function predicate (based on a more general,
     converse reflexive, relation) and the original definition of function in
     set.mm ~ df-fun , are always the same, that is
     ` ( FunALTV F <-> Fun F ) ` , see ~ funALTVfun .

     The element of the class of functions and the function predicate are the
     same, that is ` ( F e. FunsALTV <-> FunALTV F ) ` when ` F ` is a set, see
     ~ elfunsALTVfunALTV .  Alternate definitions are ~ dffunALTV2 , ... ,
     ~ dffunALTV5 .  (Contributed by Peter Mazsa, 17-Jul-2021.) $)
  df-funALTV $a |- ( FunALTV F <-> ( CnvRefRel ,~ F /\ Rel F ) ) $.

  $( Alternate definition of the class of functions.  (Contributed by Peter
     Mazsa, 18-Jul-2021.) $)
  dffunsALTV $p |- FunsALTV = { f e. Rels | ,~ f e. CnvRefRels } $=
    ( ccoss ccnvrefrels wcel cfunsALTV cfunss crels df-funsALTV df-funss abeqin
    cv ) AKBCDAEFGHAIJ $.

  $( Alternate definition of the class of functions.  (Contributed by Peter
     Mazsa, 30-Aug-2021.) $)
  dffunsALTV2 $p |- FunsALTV = { f e. Rels | ,~ f C_ _I } $=
    ( cv ccoss ccnvrefrels cid wss crels cfunsALTV dffunsALTV cosselcnvrefrels2
    wcel wa cosselrels biantrud bitr4id rabimbieq ) ABZCZDKZREFZAGHAIQGKZSTRGKZ
    LTQJUAUBTQGMNOP $.

  ${
    $d f u x y $.
    $( Alternate definition of the class of functions.  For the ` X ` axis and
       the ` Y ` axis you can convert the right side to ` { f e. Rels | A. ` x1
       ` A. ` y1 ` A. ` y2 ` ( ( ` x1 ` f ` y1 ` /\ ` x1 ` f ` y2 ` ) -> ` y1
       ` = ` y2 ` ) } ` .  (Contributed by Peter Mazsa, 30-Aug-2021.) $)
    dffunsALTV3 $p |- FunsALTV =
        { f e. Rels | A. u A. x A. y ( ( u f x /\ u f y ) -> x = y ) } $=
      ( cv ccoss ccnvrefrels wcel wbr wa wceq wi wal crels cfunsALTV dffunsALTV
      cosselcnvrefrels3 cosselrels biantrud bitr4id rabimbieq ) DEZFZGHZCEZAEZU
      BIUEBEZUBIJUFUGKLBMAMCMZDNODPUBNHZUDUHUCNHZJUHABCUBQUIUJUHUBNRSTUA $.
  $}

  ${
    $d f u x $.
    $( Alternate definition of the class of functions.  For the ` X ` axis and
       the ` Y ` axis you can convert the right side to
       ` { f e. Rels | A. x1 E* y1 x1 f y1 } ` .  (Contributed by Peter Mazsa,
       31-Aug-2021.) $)
    dffunsALTV4 $p |- FunsALTV = { f e. Rels | A. u E* x u f x } $=
      ( cv ccoss ccnvrefrels wcel wbr wmo wal crels cfunsALTV cosselcnvrefrels4
      dffunsALTV wa cosselrels biantrud bitr4id rabimbieq ) CDZEZFGZBDADTHAIBJZ
      CKLCNTKGZUBUCUAKGZOUCABTMUDUEUCTKPQRS $.
  $}

  ${
    $d f u x y $.
    $( Alternate definition of the class of functions.  (Contributed by Peter
       Mazsa, 31-Aug-2021.) $)
    dffunsALTV5 $p |- FunsALTV = { f e. Rels | A. x e. ran f A. y e. ran f
                       ( x = y \/ ( [ x ] `' f i^i [ y ] `' f ) = (/) ) } $=
      ( vu cfunsALTV cv wbr wmo wal crels crab wceq ccnv cec cin c0 wo crn wral
      dffunsALTV4 ineccnvmo2 rabbii eqtr4i ) EDFAFZCFZGAHDIZCJKUDBFZLUDUEMZNUGU
      HNOPLQBUERZSAUISZCJKADCTUJUFCJABDUEUAUBUC $.
  $}

  $( Alternate definition of the function relation predicate, cf.
     ~ dfdisjALTV2 .  (Contributed by Peter Mazsa, 8-Feb-2018.) $)
  dffunALTV2 $p |- ( FunALTV F <-> ( ,~ F C_ _I /\ Rel F ) ) $=
    ( wfunALTV ccoss wcnvrefrel wrel wa cid wss df-funALTV cnvrefrelcoss2 bitri
    anbi1i ) ABACZDZAEZFMGHZOFAINPOAJLK $.

  ${
    $d F u x y $.
    $( Alternate definition of the function relation predicate, cf.
       ~ dfdisjALTV3 .  Reproduction of ~ dffun2 .  For the ` X ` axis and the
       ` Y ` axis you can convert the right side to ` ( A. ` x1 ` A. ` y1
       ` A. ` y2 ` ( ( ` x1 ` f ` y1 ` /\ ` x1 ` f ` y2 ` ) -> ` y1 ` = ` y2
       ` ) /\ Rel F ) ` .  (Contributed by NM, 29-Dec-1996.) $)
    dffunALTV3 $p |- ( FunALTV F <->
        ( A. u A. x A. y ( ( u F x /\ u F y ) -> x = y ) /\ Rel F ) ) $=
      ( wfunALTV ccoss cid wss wa cv wbr weq wi wal dffunALTV2 cossssid3 anbi1i
      wrel bitri ) DEDFGHZDRZICJZAJDKUBBJDKIABLMBNANCNZUAIDOTUCUAABCDPQS $.
  $}

  ${
    $d F u x $.
    $( Alternate definition of the function relation predicate, cf.
       ~ dfdisjALTV4 .  This is ~ dffun6 .  For the ` X ` axis and the ` Y `
       axis you can convert the right side to
       ` ( A. x1 E* y1 x1 F y1 /\ Rel F ) ` .  (Contributed by NM,
       9-Mar-1995.) $)
    dffunALTV4 $p |- ( FunALTV F <-> ( A. u E* x u F x /\ Rel F ) ) $=
      ( wfunALTV ccoss cid wss wrel wa cv wbr dffunALTV2 cossssid4 anbi1i bitri
      wmo wal ) CDCEFGZCHZIBJAJCKAPBQZSICLRTSABCMNO $.
  $}

  ${
    $d F x y $.
    $( Alternate definition of the function relation predicate, cf.
       ~ dfdisjALTV5 .  (Contributed by Peter Mazsa, 5-Sep-2021.) $)
    dffunALTV5 $p |- ( FunALTV F <->
       ( A. x e. ran F A. y e. ran F
           ( x = y \/ ( [ x ] `' F i^i [ y ] `' F ) = (/) ) /\
         Rel F ) ) $=
      ( wfunALTV ccoss cid wss wrel wa cv wceq ccnv cec cin crn wral dffunALTV2
      c0 wo cossssid5 anbi1i bitri ) CDCEFGZCHZIAJZBJZKUECLZMUFUGMNRKSBCOZPAUHP
      ZUDICQUCUIUDABCTUAUB $.
  $}

  ${
    $d F x $.
    $( Elementhood in the class of functions.  (Contributed by Peter Mazsa,
       24-Jul-2021.) $)
    elfunsALTV $p |- ( F e. FunsALTV <->
                      ( ,~ F e. CnvRefRels /\ F e. Rels ) ) $=
      ( vx ccoss ccnvrefrels wcel crels cfunsALTV dffunsALTV wceq cosseq eleq1d
      cv rabeqel ) BLZCZDEACZDEBFGABHNAIOPDNAJKM $.
  $}

  $( Elementhood in the class of functions.  (Contributed by Peter Mazsa,
     31-Aug-2021.) $)
  elfunsALTV2 $p |- ( F e. FunsALTV <-> ( ,~ F C_ _I /\ F e. Rels ) ) $=
    ( cfunsALTV ccoss ccnvrefrels crels wa cid wss elfunsALTV cosselcnvrefrels2
    wcel cosselrels biantrud bitr4id pm5.32ri bitri ) ABKACZDKZAEKZFQGHZSFAISRT
    SRTQEKZFTAJSUATAELMNOP $.

  ${
    $d F u x y $.
    $( Elementhood in the class of functions.  (Contributed by Peter Mazsa,
       31-Aug-2021.) $)
    elfunsALTV3 $p |- ( F e. FunsALTV <->
        ( A. u A. x A. y ( ( u F x /\ u F y ) -> x = y ) /\ F e. Rels ) ) $=
      ( cfunsALTV wcel ccoss ccnvrefrels crels wa cv wbr wceq wi wal elfunsALTV
      cosselcnvrefrels3 cosselrels biantrud bitr4id pm5.32ri bitri ) DEFDGZHFZD
      IFZJCKZAKZDLUFBKZDLJUGUHMNBOAOCOZUEJDPUEUDUIUEUDUIUCIFZJUIABCDQUEUJUIDIRS
      TUAUB $.
  $}

  ${
    $d F u x $.
    $( Elementhood in the class of functions.  (Contributed by Peter Mazsa,
       31-Aug-2021.) $)
    elfunsALTV4 $p |- ( F e. FunsALTV <-> ( A. u E* x u F x /\ F e. Rels ) ) $=
      ( cfunsALTV wcel ccoss ccnvrefrels crels wa wbr wmo wal cosselcnvrefrels4
      cv elfunsALTV cosselrels biantrud bitr4id pm5.32ri bitri ) CDECFZGEZCHEZI
      BNANCJAKBLZUCICOUCUBUDUCUBUDUAHEZIUDABCMUCUEUDCHPQRST $.
  $}

  ${
    $d F x y $.
    $( Elementhood in the class of functions.  (Contributed by Peter Mazsa,
       5-Sep-2021.) $)
    elfunsALTV5 $p |- ( F e. FunsALTV <->
       ( A. x e. ran F A. y e. ran F
           ( x = y \/ ( [ x ] `' F i^i [ y ] `' F ) = (/) ) /\
         F e. Rels ) ) $=
      ( cfunsALTV wcel ccoss ccnvrefrels crels wa cv wceq ccnv cec cin crn wral
      c0 wo elfunsALTV cosselcnvrefrels5 cosselrels biantrud bitr4id pm5.32ri
      bitri ) CDECFZGEZCHEZIAJZBJZKUICLZMUJUKMNQKRBCOZPAULPZUHICSUHUGUMUHUGUMUF
      HEZIUMABCTUHUNUMCHUAUBUCUDUE $.
  $}

  $( The element of the class of functions and the function predicate are the
     same when ` F ` is a set.  (Contributed by Peter Mazsa, 26-Jul-2021.) $)
  elfunsALTVfunALTV $p |- ( F e. V -> ( F e. FunsALTV <-> FunALTV F ) ) $=
    ( wcel ccoss ccnvrefrels crels wa wcnvrefrel wrel cfunsALTV wfunALTV cvv wb
    cossex elcnvrefrelsrel syl elrelsrel anbi12d elfunsALTV df-funALTV 3bitr4g
    ) ABCZADZECZAFCZGUCHZAIZGAJCAKUBUDUFUEUGUBUCLCUDUFMABNUCLOPABQRASATUA $.

  $( Our definition of the function predicate ~ df-funALTV (based on a more
     general, converse reflexive, relation) and the original definition of
     function in set.mm ~ df-fun , are always the same and interchangeable.
     (Contributed by Peter Mazsa, 27-Jul-2021.) $)
  funALTVfun $p |- ( FunALTV F <-> Fun F ) $=
    ( wcnvrefrel wrel wa ccnv ccom cid wss wfunALTV wfun cnvrefrelcoss2 dfcoss3
    ccoss sseq1i bitri anbi2ci df-funALTV df-fun 3bitr4i ) AMZBZACZDUBAAEFZGHZD
    AIAJUAUDUBUATGHUDAKTUCGALNOPAQARS $.

  $( Subclass theorem for function.  (Contributed by NM, 16-Aug-1994.)  (Proof
     shortened by Mario Carneiro, 24-Jun-2014.)  (Revised by Peter Mazsa,
     22-Sep-2021.) $)
  funALTVss $p |- ( A C_ B -> ( FunALTV B -> FunALTV A ) ) $=
    ( wss ccoss cid wrel wa wfunALTV wi cossss sstr2 anim12d dffunALTV2 3imtr4g
    syl relss ) ABCZBDZECZBFZGADZECZAFZGBHAHQSUBTUCQUARCSUBIABJUAREKOABPLBMAMN
    $.

  $( Equality theorem for function predicate.  (Contributed by NM,
     16-Aug-1994.) $)
  funALTVeq $p |- ( A = B -> ( FunALTV A <-> FunALTV B ) ) $=
    ( wceq wfunALTV wss wi eqimss2 funALTVss syl eqimss impbid ) ABCZADZBDZLBAE
    MNFBAGBAHILABENMFABJABHIK $.

  ${
    funALTVeqi.1 $e |- A = B $.
    $( Equality inference for the function predicate.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    funALTVeqi $p |- ( FunALTV A <-> FunALTV B ) $=
      ( wceq wfunALTV wb funALTVeq ax-mp ) ABDAEBEFCABGH $.
  $}

  ${
    funALTVeqd.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for the function predicate.  (Contributed by NM,
       23-Feb-2013.) $)
    funALTVeqd $p |- ( ph -> ( FunALTV A <-> FunALTV B ) ) $=
      ( wceq wfunALTV wb funALTVeq syl ) ABCEBFCFGDBCHI $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Disjoints vs. converse functions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define the class of all disjoint sets (but not necessarily disjoint
     relations, cf. ~ df-disjs ).  It is used only by ~ df-disjs .
     (Contributed by Peter Mazsa, 17-Jul-2021.) $)
  df-disjss $a |- Disjss = { x | ,~ `' x e. CnvRefRels } $.

  $( Define the disjoint relations class, i.e., the class of disjoints.  We
     need ` Disjs ` for the definition of Parts and Part for the
     Partition-Equivalence Theorems: this need for Parts as disjoint relations
     on their domain quotients is the reason why we must define ` Disjs `
     instead of simply using converse functions (cf. ~ dfdisjALTV ).

     The element of the class of disjoints and the disjoint predicate are the
     same, that is ` ( R e. Disjs <-> Disj R ) ` when ` R ` is a set, see
     ~ eldisjsdisj .  Alternate definitions are ~ dfdisjs , ... , ~ dfdisjs5 .
     (Contributed by Peter Mazsa, 17-Jul-2021.) $)
  df-disjs $a |- Disjs = ( Disjss i^i Rels ) $.

  $( Define the disjoint relation predicate, i.e., the disjoint predicate.  A
     disjoint relation is a converse function of the relation by ~ dfdisjALTV ,
     see the comment of ~ df-disjs why we need disjoint relations instead of
     converse functions anyway.

     The element of the class of disjoints and the disjoint predicate are the
     same, that is ` ( R e. Disjs <-> Disj R ) ` when ` R ` is a set, see
     ~ eldisjsdisj .  Alternate definitions are ~ dfdisjALTV , ... ,
     ~ dfdisjALTV5 .  (Contributed by Peter Mazsa, 17-Jul-2021.) $)
  df-disjALTV $a |- ( Disj R <-> ( CnvRefRel ,~ `' R /\ Rel R ) ) $.

  $( Define the disjoint element relations class, i.e., the disjoint elements
     class.  The element of the disjoint elements class and the disjoint
     elementhood predicate are the same, that is
     ` ( A e. ElDisjs <-> ElDisj A ) ` when ` A ` is a set, see
     ~ eleldisjseldisj .  (Contributed by Peter Mazsa, 28-Nov-2022.) $)
  df-eldisjs $a |- ElDisjs = { a | ( `' _E |` a ) e. Disjs } $.

  $( Define the disjoint element relation predicate, i.e., the disjoint
     elementhood predicate.  Read: the elements of ` A ` are disjoint.  The
     element of the disjoint elements class and the disjoint elementhood
     predicate are the same, that is ` ( A e. ElDisjs <-> ElDisj A ) ` when
     ` A ` is a set, see ~ eleldisjseldisj .

     As of now, disjoint elementhood is defined as "partition" in set.mm :
     compare ~ df-prt with ~ dfeldisj5 .  See also the comments of
     ~ dfmembpart2 and of ~ df-parts .  (Contributed by Peter Mazsa,
     17-Jul-2021.) $)
  df-eldisj $a |- ( ElDisj A <-> Disj ( `' _E |` A ) ) $.

  $( Alternate definition of the class of disjoints.  (Contributed by Peter
     Mazsa, 18-Jul-2021.) $)
  dfdisjs $p |- Disjs = { r e. Rels | ,~ `' r e. CnvRefRels } $=
    ( cv ccnv ccoss ccnvrefrels cdisjs cdisjss crels df-disjs df-disjss abeqin
    wcel ) ABCDELAFGHIAJK $.

  $( Alternate definition of the class of disjoints.  (Contributed by Peter
     Mazsa, 5-Sep-2021.) $)
  dfdisjs2 $p |- Disjs = { r e. Rels | ,~ `' r C_ _I } $=
    ( cv ccnv ccoss ccnvrefrels wcel cid crels cdisjs dfdisjs cosselcnvrefrels2
    wss wa cosscnvelrels biantrud bitr4id rabimbieq ) ABZCZDZEFZTGLZAHIAJRHFZUA
    UBTHFZMUBSKUCUDUBRHNOPQ $.

  ${
    $d r u v x $.
    $( Alternate definition of the class of disjoints.  (Contributed by Peter
       Mazsa, 5-Sep-2021.) $)
    dfdisjs3 $p |- Disjs =
        { r e. Rels | A. u A. v A. x ( ( u r x /\ v r x ) -> u = v ) } $=
      ( cv ccnv ccoss cid wss wbr wa wceq wi crels cdisjs dfdisjs2 cosscnvssid3
      wal rabbieq ) DEZFGHICEZAEZTJBEZUBTJKUAUCLMARBRCRDNODPABCTQS $.
  $}

  ${
    $d r u x $.
    $( Alternate definition of the class of disjoints.  (Contributed by Peter
       Mazsa, 5-Sep-2021.) $)
    dfdisjs4 $p |- Disjs = { r e. Rels | A. x E* u u r x } $=
      ( cv ccoss cid wss wbr wmo wal crels cdisjs dfdisjs2 cosscnvssid4 rabbieq
      ccnv ) CDZPEFGBDADQHBIAJCKLCMABQNO $.
  $}

  ${
    $d r u v $.
    $( Alternate definition of the class of disjoints.  (Contributed by Peter
       Mazsa, 5-Sep-2021.) $)
    dfdisjs5 $p |- Disjs = { r e. Rels | A. u e. dom r A. v e. dom r
                             ( u = v \/ ( [ u ] r i^i [ v ] r ) = (/) ) } $=
      ( cv ccnv ccoss cid wss wceq cec cin c0 wo cdm wral crels cdisjs biantrud
      wb wa dfdisjs2 wcel cosscnvssid5 elrelsrelim bibi12d mpbiri rabimbieq
      wrel ) CDZEFGHZBDZADZIUKUIJULUIJKLIMAUINZOBUMOZCPQCUAUIPUBZUJUNSUJUIUHZTZ
      UNUPTZSABUIUCUOUJUQUNURUOUPUJUIUDZRUOUPUNUSRUEUFUG $.
  $}

  $( Alternate definition of the disjoint relation predicate.  A disjoint
     relation is a converse function of the relation, see the comment of
     ~ df-disjs why we need disjoint relations instead of converse functions
     anyway.  (Contributed by Peter Mazsa, 27-Jul-2021.) $)
  dfdisjALTV $p |- ( Disj R <-> ( FunALTV `' R /\ Rel R ) ) $=
    ( wdisjALTV ccnv ccoss wcnvrefrel wa wfunALTV df-disjALTV relcnv df-funALTV
    wrel mpbiran2 anbi1i bitr4i ) ABACZDEZAKZFOGZQFAHRPQRPOKAIOJLMN $.

  $( Alternate definition of the disjoint relation predicate, cf.
     ~ dffunALTV2 .  (Contributed by Peter Mazsa, 27-Jul-2021.) $)
  dfdisjALTV2 $p |- ( Disj R <-> ( ,~ `' R C_ _I /\ Rel R ) ) $=
    ( wdisjALTV ccnv ccoss wcnvrefrel wrel wa df-disjALTV cnvrefrelcoss2 anbi1i
    cid wss bitri ) ABACZDZEZAFZGOKLZQGAHPRQNIJM $.

  ${
    $d R u v x $.
    $( Alternate definition of the disjoint relation predicate, cf.
       ~ dffunALTV3 .  (Contributed by Peter Mazsa, 28-Jul-2021.) $)
    dfdisjALTV3 $p |- ( Disj R <->
       ( A. u A. v A. x ( ( u R x /\ v R x ) -> u = v ) /\ Rel R ) ) $=
      ( wdisjALTV ccnv ccoss cid wss wrel wa cv wbr wi dfdisjALTV2 cosscnvssid3
      weq wal anbi1i bitri ) DEDFGHIZDJZKCLALZDMBLUCDMKCBQNARBRCRZUBKDOUAUDUBAB
      CDPST $.
  $}

  ${
    $d R u x $.
    $( Alternate definition of the disjoint relation predicate, cf.
       ~ dffunALTV4 .  (Contributed by Peter Mazsa, 5-Sep-2021.) $)
    dfdisjALTV4 $p |- ( Disj R <-> ( A. x E* u u R x /\ Rel R ) ) $=
      ( wdisjALTV ccnv ccoss cid wss wa cv wbr wmo wal dfdisjALTV2 cosscnvssid4
      wrel anbi1i bitri ) CDCEFGHZCPZIBJAJCKBLAMZTICNSUATABCOQR $.
  $}

  ${
    $d R u v $.
    $( Alternate definition of the disjoint relation predicate, cf.
       ~ dffunALTV5 .  (Contributed by Peter Mazsa, 5-Sep-2021.) $)
    dfdisjALTV5 $p |- ( Disj R <->
        ( A. u e. dom R A. v e. dom R
             ( u = v \/ ( [ u ] R i^i [ v ] R ) = (/) ) /\
          Rel R ) ) $=
      ( wdisjALTV ccnv ccoss cid wss wrel wa cv wceq cec cin c0 cdm dfdisjALTV2
      wo wral cosscnvssid5 bitri ) CDCEFGHCIZJBKZAKZLUCCMUDCMNOLRACPZSBUESUBJCQ
      ABCTUA $.
  $}

  ${
    $d R u v $.
    $( Alternate definition of the disjoint relation predicate. ` Disj R `
       means: different domain generators have disjoint cosets (unless the
       generators are equal), plus ` Rel R ` for relation-typedness.  This is
       the characterization that makes canonicity/uniqueness arguments modular.
       It is the starting point for the entire " ` Disj ` ` <-> ` unique
       representative per block" pipeline that feeds into ` Disjs ` , see
       ~ dfdisjs7 .  (Contributed by Peter Mazsa, 3-Feb-2026.) $)
    dfdisjALTV5a $p |- ( Disj R <->
        ( A. u e. dom R A. v e. dom R
             ( ( [ u ] R i^i [ v ] R ) =/= (/) -> u = v ) /\
          Rel R ) ) $=
      ( wdisjALTV cv wceq cec cin c0 wo cdm wral wrel wi dfdisjALTV5 orcom neor
      wne bitri 2ralbii bianbi ) CDBEZAEZFZUBCGUCCGHZIFZJZACKZLBUHLCMUEIRUDNZAU
      HLBUHLABCOUGUIBAUHUHUGUFUDJUIUDUFPUDUEIQSTUA $.
  $}

  ${
    $d R u v $.
    $( ` Disj ` implies coset-equality injectivity (domain-wise).  Extracts the
       practical consequence of ` Disj ` : the map ` u |-> [ u ] R ` is
       injective on ` dom R ` .  This is exactly the "canonicity" property used
       repeatedly when turning ` E* ` into ` E! ` and when reasoning about
       uniqueness of representatives.  (Contributed by Peter Mazsa,
       3-Feb-2026.) $)
    disjimeceqim $p |- ( Disj R ->
        A. u e. dom R A. v e. dom R ( [ u ] R = [ v ] R -> u = v ) ) $=
      ( wdisjALTV cv cec wceq cin c0 wne wi wral wcel ecdmn0 biimpi ineq2 inidm
      cdm eqtr3di wa neeq1d syl5ibrcom rgen rgenw ralcom mpbi wrel dfdisjALTV5a
      simplbi r19.26-2 pm3.33 2ralimi sylbir sylancr ) CDZBEZCFZAEZCFZGZUQUSHZI
      JZKZACRZLBVDLZVBUPURGZKZAVDLBVDLZUTVFKZAVDLBVDLZVCBVDLZAVDLVEVKAVDVCBVDUP
      VDMZVBUTUQIJZVLVMUPCNOUTVAUQIUTUQUQHVAUQUQUSUQPUQQSUAUBUCUDVCABVDVDUEUFUO
      VHCUGABCUHUIVEVHTVCVGTZAVDLBVDLVJVCVGBAVDVDUJVNVIBAVDVDUTVBVFUKULUMUN $.
  $}

  ${
    $d A u v $.  $d B u v $.  $d R u v $.
    $( ` Disj ` implies injectivity (pairwise form).  The same content as
       ~ disjimeceqim but packaged for direct use with explicit hypotheses
       ` ( A e. dom R /\ B e. dom R ) ` .  (Contributed by Peter Mazsa,
       16-Feb-2026.) $)
    disjimeceqim2 $p |- ( Disj R ->
       ( ( A e. dom R /\ B e. dom R ) -> ( [ A ] R = [ B ] R -> A = B ) ) ) $=
      ( vu vv wdisjALTV cdm wcel wa cec wceq wi cv simprl simprr eleq1 bi2anan9
      eceq1 imbi12d wral eqeqan12d eqeq12 disjimeceqim rsp2 syl vtocl2d pm2.43d
      adantr ex ) CFZACGZHZBUKHZIZACJZBCJZKZABKZLZUJUNUNUSLZUJUNIDMZUKHZEMZUKHZ
      IZVACJZVCCJZKZVAVCKZLZLZUTDEABUKUKUJULUMNUJULUMOVAAKZVCBKZIZVEUNVJUSVLVBU
      LVMVDUMVAAUKPVCBUKPQVNVHUQVIURVLVMVFUOVGUPVAACRVCBCRUAVAAVCBUBSSUJVKUNUJV
      JEUKTDUKTVKEDCUCVJDEUKUKUDUEUHUFUIUG $.
  $}

  ${
    $d R u v $.
    $( ` Disj ` gives biconditional injectivity (domain-wise).  Strengthens
       injectivity to an iff.  (Contributed by Peter Mazsa, 3-Feb-2026.) $)
    disjimeceqbi $p |- ( Disj R ->
        A. u e. dom R A. v e. dom R ( [ u ] R = [ v ] R <-> u = v ) ) $=
      ( wdisjALTV cv cec wceq wi cdm wral wb disjimeceqim eceq1 rgen2w 2ralbiim
      sylanblrc ) CDBEZCFAEZCFGZQRGZHACIZJBUAJTSHZAUAJBUAJSTKAUAJBUAJABCLUBBAUA
      UAQRCMNSTBAUAUAOP $.
  $}

  $( Injectivity of the block constructor under disjointness. ~ suc11reg
     analogue: under disjointness, equal blocks force equal generators (on
     ` dom R ` ).  (Contributed by Peter Mazsa, 16-Feb-2026.) $)
  disjimeceqbi2 $p |- ( Disj R ->
      ( ( A e. dom R /\ B e. dom R ) -> ( [ A ] R = [ B ] R <-> A = B ) ) ) $=
    ( wdisjALTV cdm wcel wa cec wceq disjimeceqim2 wi eceq1 2a1i impbidd ) CDZA
    CEZFBPFGZACHBCHIZABIZABCJSRKOQABCLMN $.

  ${
    $d R u v $.  $d t u v $.
    $( Under ` Disj ` , every block has a unique generator ( ` E* ` form).  If
       ` t ` is a block in the quotient sense, then there is a uniquely
       determined ` u ` in ` dom R ` such that ` t = [ u ] R ` .  This is the
       existence+uniqueness engine behind ` Disjs ` and ` QMap `
       characterizations: it is the "representative theorem" from which the
       ` E! ` forms are obtained.  (Contributed by Peter Mazsa, 5-Feb-2026.) $)
    disjimrmoeqec $p |- ( Disj R -> E* u e. dom R t = [ u ] R ) $=
      ( vv wdisjALTV cv cec wceq wa wi cdm wral wrmo disjimeceqim eqtr2 2ralimi
      imim1i syl eceq1 eqeq2d rmo4 sylibr ) CEZBFZAFZCGZHZUDDFZCGZHZIZUEUHHZJZD
      CKZLAUNLZUGAUNMUCUFUIHZULJZDUNLAUNLUODACNUQUMADUNUNUKUPULUDUFUIOQPRUGUJAD
      UNULUFUIUDUEUHCSTUAUB $.
  $}

  ${
    $d R t u $.
    $( Disjointness implies unique-generation of quotient blocks.  Converts
       existence-quotient comprehension (see ~ df-qs ) into a
       uniqueness-comprehension under disjointness; rewrites ` ( dom R /. R ) `
       carriers as exactly the class of blocks with a unique representative.
       This is the "unique generator per block" content in a carrier-normal
       form.  (Contributed by Peter Mazsa, 5-Feb-2026.) $)
    disjimdmqseq $p |- ( Disj R ->
        ( dom R /. R ) = { t | E! u e. dom R t = [ u ] R } ) $=
      ( wdisjALTV cv cec wceq cdm wreu wcel wrmo wa disjimrmoeqec biantrud wrex
      cqs wb cvv elqsg elv anbi1i reu5 bitr4i bitrdi eqabdv ) CDZBEZAECFGZACHZI
      ZBUICPZUFUGUKJZULUHAUIKZLZUJUFUMULABCMNUNUHAUIOZUMLUJULUOUMULUOQBAUIUGCRS
      TUAUHAUIUBUCUDUE $.
  $}

  $( Alternate definition of the disjoint elementhood predicate.  (Contributed
     by Peter Mazsa, 19-Sep-2021.) $)
  dfeldisj2 $p |- ( ElDisj A <-> ,~ `' ( `' _E |` A ) C_ _I ) $=
    ( weldisj cep ccnv cres wdisjALTV cid wss df-eldisj wrel relres dfdisjALTV2
    ccoss mpbiran2 bitri ) ABCDZAEZFZQDMGHZAIRSQJPAKQLNO $.

  ${
    $d A u v x $.
    $( Alternate definition of the disjoint elementhood predicate.
       (Contributed by Peter Mazsa, 19-Sep-2021.) $)
    dfeldisj3 $p |- ( ElDisj A <->
                      A. u e. A A. v e. A A. x e. ( u i^i v ) u = v ) $=
      ( weldisj cv wcel cin w3a weq wi wal wral wbr wa wb cvv brcnvepres bitr4i
      el2v cep ccnv wdisjALTV df-eldisj relres dfdisjALTV3 mpbiran2 an4 anbi12i
      cres wrel elin anbi2i 3bitr4i df-3an imbi1i 3albii 3bitri r3al ) DEZCFZDG
      ZBFZDGZAFZVAVCHZGZIZCBJZKZALBLCLZVIAVFMBDMCDMUTUAUBZDUJZUCZVAVEVMNZVCVEVM
      NZOZVIKZALBLCLZVKDUDVNVSVMUKVLDUEABCVMUFUGVRVJCBAVQVHVIVQVBVDOZVGOZVHVBVE
      VAGZOZVDVEVCGZOZOVTWBWDOZOVQWAVBWBVDWDUHVOWCVPWEVOWCPCADVAVEQQRTVPWEPBADV
      CVEQQRTUIVGWFVTVEVAVCULUMUNVBVDVGUOSUPUQURVICBADDVFUSS $.
  $}

  ${
    $d A u x $.
    $( Alternate definition of the disjoint elementhood predicate.
       (Contributed by Peter Mazsa, 19-Sep-2021.) $)
    dfeldisj4 $p |- ( ElDisj A <-> A. x E* u e. A x e. u ) $=
      ( weldisj cep ccnv cres wdisjALTV cv wbr wmo wal wcel wrmo df-eldisj wrel
      relres dfdisjALTV4 mpbiran2 cvv wa wb brcnvepres el2v mobii df-rmo bitr4i
      albii 3bitri ) CDEFZCGZHZBIZAIZUKJZBKZALZUNUMMZBCNZALCOULUQUKPUJCQABUKRSU
      PUSAUPUMCMURUAZBKUSUOUTBUOUTUBBACUMUNTTUCUDUEURBCUFUGUHUI $.
  $}

  ${
    $d A u v x $.
    $( Alternate definition of the disjoint elementhood predicate.
       (Contributed by Peter Mazsa, 19-Sep-2021.) $)
    dfeldisj5 $p |- ( ElDisj A <->
        A. u e. A A. v e. A ( u = v \/ ( u i^i v ) = (/) ) ) $=
      ( vx weldisj wrmo wal cv wceq cin c0 wral cep cec biantru cvv eccnvep elv
      wo wa wel dfeldisj4 ccnv wbr inecmo2 relcnv 3bitr4i ineq12i eqeq1i orbi2i
      wrel 2ralbii wb brcnvep rmobii albii 3bitr3i bitr4i ) CEDBUAZBCFZDGZBHZAH
      ZIZVBVCJZKIZSZACLBCLZDBCUBVDVBMUCZNZVCVINZJZKIZSZACLBCLZVBDHZVIUDZBCFZDGZ
      VHVAVOVIUKZTVSVTTVOVSDABCVIUEVTVOMUFZOVTVSWAOUGVNVGBACCVMVFVDVLVEKVJVBVKV
      CVJVBIBVBPQRVKVCIAVCPQRUHUIUJULVRUTDVQUSBCVQUSUMBVBVPPUNRUOUPUQUR $.
  $}

  ${
    $d A u v $.
    $( Alternate definition of the disjoint elementhood predicate.  Members of
       ` A ` are pairwise disjoint: if two members overlap, they are equal.
       (Contributed by Peter Mazsa, 19-Sep-2021.) $)
    dfeldisj5a $p |- ( ElDisj A <->
        A. u e. A A. v e. A ( ( u i^i v ) =/= (/) -> u = v ) ) $=
      ( weldisj cv wceq cin c0 wo wral wne dfeldisj5 orcom neor bitri 2ralbii
      wi ) CDBEZAEZFZRSGZHFZIZACJBCJUAHKTQZACJBCJABCLUCUDBACCUCUBTIUDTUBMTUAHNO
      PO $.
  $}

  ${
    $d A u v $.  $d B u v $.  $d C u v $.
    $( ` ElDisj ` elimination (two chosen elements).  Standard specialization
       lemma: from ` ElDisj A ` infer the disjointness condition for two
       specific elements.  (Contributed by Peter Mazsa, 6-Feb-2026.) $)
    eldisjim3 $p |- ( ElDisj A -> ( ( B e. A /\ C e. A ) ->
                      ( ( B i^i C ) =/= (/) -> B = C ) ) ) $=
      ( vu vv weldisj wcel wa cin c0 wne wceq wi simp1 simp2 eleq1 imbi12d wral
      w3a cv bi2anan9 ineq12 neeq1d eqeq12 dfeldisj5a rsp2 sylbi vtocl2d 3expia
      3ad2ant3 pm2.43b ) AFZBAGZCAGZHZBCIZJKZBCLZMZUMUNULUOUSMZUMUNULSDTZAGZETZ
      AGZHZVAVCIZJKZVAVCLZMZMZUTDEBCAAUMUNULNUMUNULOVABLZVCCLZHZVEUOVIUSVKVBUMV
      LVDUNVABAPVCCAPUAVMVGUQVHURVMVFUPJVABVCCUBUCVABVCCUDQQULUMVJUNULVIEARDARV
      JEDAUEVIDEAAUFUGUJUHUIUK $.
  $}

  $( ElDisj of quotient implies coset-disjointness (domain form).  Converts
     element-disjointness of the quotient carrier into a usable "cosets don't
     overlap unless equal" rule.  (Contributed by Peter Mazsa, 10-Feb-2026.) $)
  eldisjdmqsim2 $p |- ( ( ElDisj ( dom R /. R ) /\ R e. Rels ) ->
                          ( ( u e. dom R /\ v e. dom R ) ->
                            ( ( [ u ] R i^i [ v ] R ) =/= (/) ->
                              [ u ] R = [ v ] R ) ) ) $=
    ( crels wcel cdm cqs weldisj cv wa cec cin c0 wne wceq wi eldisjim3 anbi12d
    eceldmqs imbi1d imbitrid impcom ) CDEZCFZCGZHZBIZUDEZAIZUDEZJZUGCKZUICKZLMN
    ULUMOPZPZUFULUEEZUMUEEZJZUNPUCUOUEULUMQUCURUKUNUCUPUHUQUJUGCDSUICDSRTUAUB
    $.

  ${
    $d R x $.  $d u x $.  $d v x $.
    $( Shared output implies equal cosets (under ` ElDisj ` of quotient): if
       ` u ` and ` v ` both relate to the same ` x ` , then their cosets
       intersect, hence must coincide under quotient ` ElDisj ` .  (Contributed
       by Peter Mazsa, 10-Feb-2026.) $)
    eldisjdmqsim $p |- ( ( ElDisj ( dom R /. R ) /\ R e. Rels ) ->
                        ( ( u R x /\ v R x ) -> [ u ] R = [ v ] R ) ) $=
      ( crels wcel wa cv wbr cec wb cvv elecALTV el2v wi wex 19.8a eldmg sylibr
      elv cdm cqs weldisj cin c0 wceq elin anbi12i bitr2i ne0i anim12i eceldmqs
      wne sylbi anbi12d imbitrrid adantl eldisjim3 adantr syld mpdi ) DUAZDUBZU
      CZDEFZGZCHZAHZDIZBHZVHDIZGZVGDJZVJDJZUDZUEUMZVMVNUFZVLVHVOFZVPVRVHVMFZVHV
      NFZGVLVHVMVNUGVSVIVTVKVSVIKCAVGVHDLLMNVTVKKBAVJVHDLLMNUHUIVOVHUJUNVFVLVMV
      CFZVNVCFZGZVPVQOZVEVLWCOVDVLWCVEVGVBFZVJVBFZGVIWEVKWFVIVIAPZWEVIAQWEWGKCA
      VGDLRTSVKVKAPZWFVKAQWFWHKBAVJDLRTSUKVEWAWEWBWFVGDEULVJDEULUOUPUQVDWCWDOVE
      VCVMVNURUSUTVA $.
  $}

  ${
    $d A x $.  $d B x $.  $d V x $.
    $( Disjointness of successor enforces element-carrier separation:  If ` B `
       is the successor of ` A ` and ` B ` is element-disjoint as a family,
       then no element of ` A ` can itself be a member of ` A ` (equivalently,
       every ` x e. A ` has empty intersection with the carrier ` A ` ).
       Provides a clean bridge between "disjoint family at the next grade" and
       "no block contains a block of the same family" at the previous grade:
       ` MembPart ` alone does not enforce this, see ~ dfmembpart2 (it gives
       disjoint blocks and excludes the empty block, but does not prevent
       ` u e. m ` from also being a member of the carrier ` m ` ).  This lemma
       is used to justify when grade-stability (via successor-shift) supplies
       the extra separation axioms needed in roof/root-style carrier reasoning.
       (Contributed by Peter Mazsa, 18-Feb-2026.) $)
    suceldisj $p |- ( ( A e. V /\ ElDisj B /\ suc A = B ) ->
                      A. x e. A ( x i^i A ) = (/) ) $=
      ( wcel weldisj csuc wceq w3a cv cin c0 wa wne wn elirr eleq1 wss 3ad2ant3
      wi mtbiri con2i adantl sssucid sseq2 mpbii sseld sucidg 3ad2ant1 wb eleq2
      mpbid jctird eldisjim3 3ad2ant2 syld imp mtod nne sylib ralrimiva ) BDEZC
      FZBGZCHZIZAJZBKZLHZABVFVGBEZMZVHLNZOVIVKVLVGBHZVJVMOVFVMVJVMVJBBEBPVGBBQU
      AUBUCVFVJVLVMTZVFVJVGCEZBCEZMZVNVFVJVOVPVFBCVGVEVBBCRZVCVEBVDRVRBUDVDCBUE
      UFSUGVFBVDEZVPVBVCVSVEBDUHUIVEVBVSVPUJVCVDCBUKSULUMVCVBVQVNTVECVGBUNUOUPU
      QURVHLUSUTVA $.
  $}

  ${
    $d R r $.
    $( Elementhood in the class of disjoints.  (Contributed by Peter Mazsa,
       24-Jul-2021.) $)
    eldisjs $p |- ( R e. Disjs <->
                    ( ,~ `' R e. CnvRefRels /\ R e. Rels ) ) $=
      ( vr ccnv ccoss ccnvrefrels wcel crels cdisjs dfdisjs wceq cosseqd eleq1d
      cv cnveq rabeqel ) BMZCZDZEFACZDZEFBGHABIPAJZRTEUAQSPANKLO $.
  $}

  $( Elementhood in the class of disjoints.  (Contributed by Peter Mazsa,
     5-Sep-2021.) $)
  eldisjs2 $p |- ( R e. Disjs <-> ( ,~ `' R C_ _I /\ R e. Rels ) ) $=
    ( cdisjs wcel ccnv ccoss ccnvrefrels crels wa cid eldisjs cosselcnvrefrels2
    wss cosscnvelrels biantrud bitr4id pm5.32ri bitri ) ABCADZEZFCZAGCZHSILZUAH
    AJUATUBUATUBSGCZHUBRKUAUCUBAGMNOPQ $.

  ${
    $d R u v x $.
    $( Elementhood in the class of disjoints.  (Contributed by Peter Mazsa,
       5-Sep-2021.) $)
    eldisjs3 $p |- ( R e. Disjs <->
        ( A. u A. v A. x ( ( u R x /\ v R x ) -> u = v ) /\ R e. Rels ) ) $=
      ( cdisjs wcel ccnv ccoss cid wss crels wa cv wbr wceq wi wal cosscnvssid3
      eldisjs2 anbi1i bitri ) DEFDGHIJZDKFZLCMZAMZDNBMZUEDNLUDUFOPAQBQCQZUCLDSU
      BUGUCABCDRTUA $.
  $}

  ${
    $d R u x $.
    $( Elementhood in the class of disjoints.  (Contributed by Peter Mazsa,
       5-Sep-2021.) $)
    eldisjs4 $p |- ( R e. Disjs <-> ( A. x E* u u R x /\ R e. Rels ) ) $=
      ( cdisjs wcel ccoss cid wss crels wa cv wbr wmo wal eldisjs2 cosscnvssid4
      ccnv anbi1i bitri ) CDECQFGHZCIEZJBKAKCLBMANZUAJCOTUBUAABCPRS $.
  $}

  ${
    $d R u v $.
    $( Elementhood in the class of disjoints.  (Contributed by Peter Mazsa,
       5-Sep-2021.) $)
    eldisjs5 $p |- ( R e. V -> ( R e. Disjs <->
       ( A. u e. dom R A. v e. dom R
           ( u = v \/ ( [ u ] R i^i [ v ] R ) = (/) ) /\
         R e. Rels ) ) ) $=
      ( cdisjs wcel ccnv ccoss cid wss crels wa cv wceq cec cin c0 wral anbi2d
      wb wo cdm eldisjs2 wrel cosscnvssid5 elrelsrel bibi12d mpbiri bitrid ) CE
      FCGHIJZCKFZLZCDFZBMZAMZNUNCOUOCOPQNUAACUBZRBUPRZUKLZCUCUMULURTUJCUDZLZUQU
      SLZTABCUEUMULUTURVAUMUKUSUJCDUFZSUMUKUSUQVBSUGUHUI $.
  $}

  $( The element of the class of disjoint relations and the disjoint relation
     predicate are the same, that is ` ( R e. Disjs <-> Disj R ) ` when ` R `
     is a set.  (Contributed by Peter Mazsa, 25-Jul-2021.) $)
  eldisjsdisj $p |- ( R e. V -> ( R e. Disjs <-> Disj R ) ) $=
    ( wcel ccnv ccoss ccnvrefrels crels wa wcnvrefrel wrel cdisjs wdisjALTV cvv
    wb cosscnvex elcnvrefrelsrel syl elrelsrel anbi12d eldisjs df-disjALTV
    3bitr4g ) ABCZADEZFCZAGCZHUDIZAJZHAKCALUCUEUGUFUHUCUDMCUEUGNABOUDMPQABRSATA
    UAUB $.

  $( When ` R ` is a set (e.g., when it is an element of the class of relations
     ~ df-rels ), the quotient map element of the class of disjoint relations
     and the disjoint relation predicate for quotient maps are the same.
     (Contributed by Peter Mazsa, 12-Feb-2026.) $)
  qmapeldisjs $p |- ( R e. V -> ( QMap R e. Disjs <-> Disj QMap R ) ) $=
    ( wcel cqmap cvv cdisjs wdisjALTV wb qmapex eldisjsdisj syl ) ABCADZECLFCLG
    HABILEJK $.

  ${
    $d R t u $.  $d V t u $.
    $( Disjointness of ` QMap ` equals ` E* ` -generation.  Pairs with
       ~ disjqmap and ~ raldmqseu to move between ` E* ` and ` E! ` depending
       on context.  (Contributed by Peter Mazsa, 12-Feb-2026.) $)
    disjqmap2 $p |- ( R e. V ->
                      ( Disj QMap R <-> A. u E* t e. dom R u = [ t ] R ) ) $=
      ( wdisjALTV ccnv wfun wcel cv cec wceq cdm wrmo wal wfunALTV wrel relqmap
      cqmap cvv nfcv dfdisjALTV mpbiran2 funALTVfun bitri nfv df-qmap wi resexg
      cres elecex syl imp funcnvmpt bitrid ) CRZEZUOFZGZCDHZAIBIZCJZKBCLZMANUPU
      QOZURUPVCUOPCQUOUAUBUQUCUDUSBAVBVAUOSUSBUEBVBTBUOTBCUFUSUTVBHZVASHZUSCVBU
      ISHVDVEUGCVBDUHVBUTCSUJUKULUMUN $.
  $}

  ${
    $d R t u $.  $d V t u $.
    $( Disjointness of ` QMap ` equals unique generation of the quotient
       carrier.  The cleaned, carrier-respecting version of ~ disjqmap2 .  This
       is the statement "each equivalence class has a unique representative"
       for the general coset carrier ` ( dom R /. R ) ` .  (Contributed by
       Peter Mazsa, 12-Feb-2026.) $)
    disjqmap $p |- ( R e. V -> ( Disj QMap R <->
                    A. u e. ( dom R /. R ) E! t e. dom R u = [ t ] R ) ) $=
      ( wcel cqmap wdisjALTV cec wceq cdm wrmo wal wreu cqs disjqmap2 raldmqseu
      cv wral bitr4d ) CDECFGAQBQCHIZBCJZKALTBUAMAUACNRABCDOABCDPS $.
  $}

  ${
    $d A a $.
    $( Elementhood in the disjoint elements class.  (Contributed by Peter
       Mazsa, 23-Jul-2023.) $)
    eleldisjs $p |- ( A e. V ->
                      ( A e. ElDisjs <-> ( `' _E |` A ) e. Disjs ) ) $=
      ( cep ccnv cres cdisjs wcel celdisjs wceq reseq2 eleq1d df-eldisjs elab2g
      va cv ) CDZNOZEZFGPAEZFGNAHBQAIRSFQAPJKNLM $.
  $}

  $( The element of the disjoint elements class and the disjoint elementhood
     predicate are the same, that is ` ( A e. ElDisjs <-> ElDisj A ) ` when
     ` A ` is a set.  (Contributed by Peter Mazsa, 23-Jul-2023.) $)
  eleldisjseldisj $p |- ( A e. V -> ( A e. ElDisjs <-> ElDisj A ) ) $=
    ( wcel celdisjs cep ccnv cres wdisjALTV weldisj cdisjs eleldisjs cnvepresex
    cvv wb eldisjsdisj syl bitrd df-eldisj bitr4di ) ABCZADCZEFAGZHZAITUAUBJCZU
    CABKTUBMCUDUCNABLUBMOPQARS $.

  $( Disjoint relation is a relation.  (Contributed by Peter Mazsa,
     15-Sep-2021.) $)
  disjrel $p |- ( Disj R -> Rel R ) $=
    ( wdisjALTV ccnv ccoss wcnvrefrel wrel df-disjALTV simprbi ) ABACDEAFAGH $.

  $( Subclass theorem for disjoints.  (Contributed by Peter Mazsa,
     28-Oct-2020.)  (Revised by Peter Mazsa, 22-Sep-2021.) $)
  disjss $p |- ( A C_ B -> ( Disj B -> Disj A ) ) $=
    ( wss ccnv wfunALTV wrel wa wdisjALTV wi cnvss funALTVss anim12d dfdisjALTV
    syl relss 3imtr4g ) ABCZBDZEZBFZGADZEZAFZGBHAHQSUBTUCQUARCSUBIABJUARKNABOLB
    MAMP $.

  ${
    disjssi.1 $e |- A C_ B $.
    $( Subclass theorem for disjoints, inference version.  (Contributed by
       Peter Mazsa, 28-Sep-2021.) $)
    disjssi $p |- ( Disj B -> Disj A ) $=
      ( wss wdisjALTV wi disjss ax-mp ) ABDBEAEFCABGH $.
  $}

  ${
    disjssd.1 $e |- ( ph -> A C_ B ) $.
    $( Subclass theorem for disjoints, deduction version.  (Contributed by
       Peter Mazsa, 28-Sep-2021.) $)
    disjssd $p |- ( ph -> ( Disj B -> Disj A ) ) $=
      ( wss wdisjALTV wi disjss syl ) ABCECFBFGDBCHI $.
  $}

  $( Equality theorem for disjoints.  (Contributed by Peter Mazsa,
     22-Sep-2021.) $)
  disjeq $p |- ( A = B -> ( Disj A <-> Disj B ) ) $=
    ( wceq wdisjALTV eqimss2 disjssd eqimss impbid ) ABCZADBDIBABAEFIABABGFH $.

  ${
    disjeqi.1 $e |- A = B $.
    $( Equality theorem for disjoints, inference version.  (Contributed by
       Peter Mazsa, 22-Sep-2021.) $)
    disjeqi $p |- ( Disj A <-> Disj B ) $=
      ( wceq wdisjALTV wb disjeq ax-mp ) ABDAEBEFCABGH $.
  $}

  ${
    disjeqd.1 $e |- ( ph -> A = B ) $.
    $( Equality theorem for disjoints, deduction version.  (Contributed by
       Peter Mazsa, 22-Sep-2021.) $)
    disjeqd $p |- ( ph -> ( Disj A <-> Disj B ) ) $=
      ( wceq wdisjALTV wb disjeq syl ) ABCEBFCFGDBCHI $.
  $}

  $( Lemma for the equality theorem for partition ~ parteq1 .  (Contributed by
     Peter Mazsa, 5-Oct-2021.) $)
  disjdmqseqeq1 $p |- ( R = S ->
                        ( ( Disj R /\ ( dom R /. R ) = A ) <->
                          ( Disj S /\ ( dom S /. S ) = A ) ) ) $=
    ( wceq wdisjALTV cdm cqs disjeq dmqseqeq1 anbi12d ) BCDBECEBFBGADCFCGADBCHA
    BCIJ $.

  $( Subclass theorem for disjoint elementhood.  (Contributed by Peter Mazsa,
     23-Sep-2021.) $)
  eldisjss $p |- ( A C_ B -> ( ElDisj B -> ElDisj A ) ) $=
    ( wss cep ccnv cres wdisjALTV weldisj ssres2 disjssd df-eldisj 3imtr4g ) AB
    CZDEZBFZGNAFZGBHAHMPOABNIJBKAKL $.

  ${
    eldisjssi.1 $e |- A C_ B $.
    $( Subclass theorem for disjoint elementhood, inference version.
       (Contributed by Peter Mazsa, 28-Sep-2021.) $)
    eldisjssi $p |- ( ElDisj B -> ElDisj A ) $=
      ( wss weldisj wi eldisjss ax-mp ) ABDBEAEFCABGH $.
  $}

  ${
    eldisjssd.1 $e |- ( ph -> A C_ B ) $.
    $( Subclass theorem for disjoint elementhood, deduction version.
       (Contributed by Peter Mazsa, 28-Sep-2021.) $)
    eldisjssd $p |- ( ph -> ( ElDisj B -> ElDisj A ) ) $=
      ( wss weldisj wi eldisjss syl ) ABCECFBFGDBCHI $.
  $}

  $( Equality theorem for disjoint elementhood.  (Contributed by Peter Mazsa,
     23-Sep-2021.) $)
  eldisjeq $p |- ( A = B -> ( ElDisj A <-> ElDisj B ) ) $=
    ( wceq cep ccnv cres wdisjALTV weldisj reseq2 disjeqd df-eldisj 3bitr4g ) A
    BCZDEZAFZGNBFZGAHBHMOPABNIJAKBKL $.

  ${
    eldisjeqi.1 $e |- A = B $.
    $( Equality theorem for disjoint elementhood, inference version.
       (Contributed by Peter Mazsa, 23-Sep-2021.) $)
    eldisjeqi $p |- ( ElDisj A <-> ElDisj B ) $=
      ( wceq weldisj wb eldisjeq ax-mp ) ABDAEBEFCABGH $.
  $}

  ${
    eldisjeqd.1 $e |- ( ph -> A = B ) $.
    $( Equality theorem for disjoint elementhood, deduction version.
       (Contributed by Peter Mazsa, 23-Sep-2021.) $)
    eldisjeqd $p |- ( ph -> ( ElDisj A <-> ElDisj B ) ) $=
      ( wceq weldisj wb eldisjeq syl ) ABCEBFCFGDBCHI $.
  $}

  ${
    $d A u v x $.  $d R u v x $.
    $( Disjoint restriction.  (Contributed by Peter Mazsa, 25-Aug-2023.) $)
    disjres $p |- ( Rel R ->
        ( Disj ( R |` A ) <->
          A. u e. A A. v e. A ( u = v \/ ( [ u ] R i^i [ v ] R ) = (/) ) ) ) $=
      ( vx wrel cres wdisjALTV cv wbr wrmo wal wceq cec cin c0 wral wmo relres
      wo dfdisjALTV4 mpbiran2 wcel wa wb cvv brres elv mobii df-rmo albii bitri
      bitr4i id inecmo bitr4id ) DFDCGZHZBIZEIZDJZBCKZELZUSAIZMZUSDNVDDNOPMTACQ
      BCQURUSUTUQJZBRZELZVCURVHUQFDCSEBUQUAUBVGVBEVGUSCUCVAUDZBRVBVFVIBVFVIUEEC
      USUTDUFUGUHUIVABCUJUMUKULBAECUSVDDVEUNUOUP $.
  $}

  $( Two forms of disjoint elements when the empty set is not an element of the
     class.  (Contributed by Peter Mazsa, 31-Dec-2024.) $)
  eldisjn0elb $p |- ( ( ElDisj A /\ -. (/) e. A ) <->
                      ( Disj ( `' _E |` A ) /\
                        ( dom ( `' _E |` A ) /. ( `' _E |` A ) ) = A ) ) $=
    ( weldisj cep ccnv cres wdisjALTV c0 wcel wn cdm cqs wceq df-eldisj anbi12i
    n0el3 ) ABCDAEZFGAHIPJPKALAMAON $.

  $( Two ways of saying that a range Cartesian product is disjoint.
     (Contributed by Peter Mazsa, 17-Jun-2020.)  (Revised by Peter Mazsa,
     21-Sep-2021.) $)
  disjxrn $p |- ( Disj ( R |X. S ) <-> ( ,~ `' R i^i ,~ `' S ) C_ _I ) $=
    ( cxrn wdisjALTV ccnv ccoss cid wss cin wrel xrnrel dfdisjALTV2 1cosscnvxrn
    mpbiran2 sseq1i bitri ) ABCZDZQEFZGHZAEFBEFIZGHRTQJABKQLNSUAGABMOP $.

  ${
    $d A u v $.  $d R u v $.  $d S u v $.
    $( Disjoint range Cartesian product.  (Contributed by Peter Mazsa,
       25-Aug-2023.) $)
    disjxrnres5 $p |- ( Disj ( R |X. ( S |` A ) ) <->
         A. u e. A A. v e. A
           ( u = v \/ ( [ u ] ( R |X. S ) i^i [ v ] ( R |X. S ) ) = (/) ) ) $=
      ( cres cxrn wdisjALTV cv wceq cec cin c0 wral xrnres2 disjeqi wrel xrnrel
      wo wb disjres ax-mp bitr3i ) DECFGZHDEGZCFZHZBIZAIZJUHUEKUIUEKLMJSACNBCNZ
      UFUDCDEOPUEQUGUJTDERABCUEUAUBUC $.
  $}

  $( Disjointness condition for range Cartesian product.  (Contributed by Peter
     Mazsa, 12-Jul-2020.)  (Revised by Peter Mazsa, 22-Sep-2021.) $)
  disjorimxrn $p |- ( ( Disj R \/ Disj S ) -> Disj ( R |X. S ) ) $=
    ( wdisjALTV wo ccnv ccoss cin cid wss cxrn wrel dfdisjALTV2 simplbi orim12i
    inss syl disjxrn sylibr ) ACZBCZDZAEFZBEFZGHIZABJCUAUBHIZUCHIZDUDSUETUFSUEA
    KALMTUFBKBLMNUBUCHOPABQR $.

  $( Disjointness condition for range Cartesian product.  (Contributed by Peter
     Mazsa, 15-Dec-2020.)  (Revised by Peter Mazsa, 22-Sep-2021.) $)
  disjimxrn $p |- ( Disj S -> Disj ( R |X. S ) ) $=
    ( wdisjALTV cxrn disjorimxrn olcs ) ACBCABDCABEF $.

  $( Disjointness condition for restriction.  (Contributed by Peter Mazsa,
     27-Sep-2021.) $)
  disjimres $p |- ( Disj R -> Disj ( R |` A ) ) $=
    ( cres resss disjssi ) BACBBADE $.

  $( Disjointness condition for intersection.  (Contributed by Peter Mazsa,
     11-Jun-2021.)  (Revised by Peter Mazsa, 28-Sep-2021.) $)
  disjimin $p |- ( Disj S -> Disj ( R i^i S ) ) $=
    ( cin inss2 disjssi ) ABCBABDE $.

  $( Disjointness condition for intersection with restriction.  (Contributed by
     Peter Mazsa, 27-Sep-2021.) $)
  disjiminres $p |- ( Disj S -> Disj ( R i^i ( S |` A ) ) ) $=
    ( wdisjALTV cres cin disjimres disjimin syl ) CDCAEZDBJFDACGBJHI $.

  $( Disjointness condition for range Cartesian product with restriction.
     (Contributed by Peter Mazsa, 27-Sep-2021.) $)
  disjimxrnres $p |- ( Disj S -> Disj ( R |X. ( S |` A ) ) ) $=
    ( wdisjALTV cres cxrn disjimres disjimxrn syl ) CDCAEZDBJFDACGBJHI $.

  ${
    $d u x $.
    $( The null class is disjoint.  (Contributed by Peter Mazsa,
       27-Sep-2021.) $)
    disjALTV0 $p |- Disj (/) $=
      ( vu vx c0 wdisjALTV cv wbr wmo wal wrel wex wn br0 nex nexmo ax-gen rel0
      ax-mp dfdisjALTV4 mpbir2an ) CDAEZBEZCFZAGZBHCIUCBUBAJKUCUBATUALMUBANQOPB
      ACRS $.
  $}

  $( The class of identity relations is disjoint.  (Contributed by Peter Mazsa,
     20-Jun-2021.) $)
  disjALTVid $p |- Disj _I $=
    ( cid wdisjALTV ccnv ccoss wrel cosscnvid eqimssi reli dfdisjALTV2 mpbir2an
    wss ) ABACDZAKAELAFGHAIJ $.

  $( The class of identity relations restricted is disjoint.  (Contributed by
     Peter Mazsa, 28-Jun-2020.)  (Revised by Peter Mazsa, 27-Sep-2021.) $)
  disjALTVidres $p |- Disj ( _I |` A ) $=
    ( cid wdisjALTV cres disjALTVid disjimres ax-mp ) BCBADCEABFG $.

  $( The intersection with restricted identity relation is disjoint.
     (Contributed by Peter Mazsa, 31-Dec-2021.) $)
  disjALTVinidres $p |- Disj ( R i^i ( _I |` A ) ) $=
    ( cid wdisjALTV cres cin disjALTVid disjiminres ax-mp ) CDBCAEFDGABCHI $.

  $( The class of range Cartesian product with restricted identity relation is
     disjoint.  (Contributed by Peter Mazsa, 25-Jun-2020.)  (Revised by Peter
     Mazsa, 27-Sep-2021.) $)
  disjALTVxrnidres $p |- Disj ( R |X. ( _I |` A ) ) $=
    ( cid wdisjALTV cres cxrn disjALTVid disjimxrnres ax-mp ) CDBCAEFDGABCHI $.

  ${
    $d A u v $.  $d R u v $.  $d V u $.
    $( Disjoint range Cartesian product, special case.  (Contributed by Peter
       Mazsa, 25-Aug-2023.) $)
    disjsuc $p |- ( A e. V ->
       ( Disj ( R |X. ( `' _E |` suc A ) ) <->
         ( Disj ( R |X. ( `' _E |` A ) ) /\
           A. u e. A
             ( ( u i^i A ) = (/) \/
               ( [ u ] R i^i [ A ] R ) = (/) ) ) ) ) $=
      ( vv wcel cv wceq cep ccnv cxrn cec c0 wo wral cres wdisjALTV disjxrnres5
      cin wa csn cun csuc disjsuc2 df-suc reseq2i xrneq2i disjeqi bitri 3bitr4g
      anbi1i ) BDFAGZEGZHULCIJZKZLUMUOLSMHNZEBBUAUBZOAUQOZUPEBOABOZULBSMHULCLBC
      LSMHNABOZTCUNBUCZPZKZQZCUNBPKQZUTTEABCDUDVDCUNUQPZKZQURVCVGVBVFCVAUQUNBUE
      UFUGUHEAUQCUNRUIVEUSUTEABCUNRUKUJ $.
  $}

  $( Injectivity of coset map from ` QMap ` being disjoint (implication form):
     under the ` Disjs ` condition on ` QMap R ` , the coset assignment is
     injective on ` dom R ` .  (Contributed by Peter Mazsa, 16-Feb-2026.) $)
  qmapeldisjsim $p |-
       ( ( R e. V /\ QMap R e. Disjs /\ ( A e. dom R /\ B e. dom R ) ) ->
         ( [ A ] R = [ B ] R -> A = B ) ) $=
    ( wcel cqmap cdisjs cdm wa cec wceq wdisjALTV qmapeldisjs eleq2d csn ecqmap
    wi imbi1d cvv impexp disjimeceqim2 dmqmap anbi12d imbi1i eqeqan12d wb ecexg
    pm5.32i sneqbg syl sylan9bbr pm5.74i bitri 3bitr3i pm5.74ri imbitrid sylbid
    3imp ) CDEZCFZGEZACHZEZBVBEZIZACJZBCJZKZABKZQZUSVAUTLZVEVJQZCDMVKAUTHZEZBVM
    EZIZAUTJZBUTJZKZVIQZQZUSVLABUTUAUSWAVLUSVPIZVTQZUSVEIZVJQZUSWAQUSVLQWCWDVTQ
    WEWBWDVTUSVPVEUSVNVCVOVDUSVMVBACDUBZNUSVMVBBWFNUCUHUDWDVTVJVEVTVFOZVGOZKZVI
    QUSVJVEVSWIVIVCVDVQWGVRWHACPBCPUERUSWIVHVIUSVFSEWIVHUFADCUGVFVGSUIUJRUKULUM
    USVPVTTUSVEVJTUNUOUPUQUR $.

  $( Injectivity of coset map from QMap being disjoint (biconditional form).
     Convenience version of ~ qmapeldisjsim .  (Contributed by Peter Mazsa,
     16-Feb-2026.) $)
  qmapeldisjsbi $p |-
       ( ( R e. V /\ QMap R e. Disjs /\ ( A e. dom R /\ B e. dom R ) ) ->
         ( [ A ] R = [ B ] R <-> A = B ) ) $=
    ( wcel cqmap cdisjs cdm wa w3a cec wceq qmapeldisjsim eceq1 impbid1 ) CDECF
    GEACHZEBPEIJACKBCKLABLABCDMABCNO $.

  $( Element-disjointness of the quotient carrier forces coset disjointness.
     Supplies the "cosets don't overlap unless equal" direction, but expressed
     via ` ran QMap R ` (the quotient carrier) and ` ElDisjs ` .  This is the
     structural reason ` Disjs ` needs a "carrier disjointness" level distinct
     from the "unique representatives" level.  (Contributed by Peter Mazsa,
     16-Feb-2026.) $)
  rnqmapeleldisjsim $p |-
      ( ( R e. V /\ ran QMap R e. ElDisjs /\ ( A e. dom R /\ B e. dom R ) ) ->
        ( ( [ A ] R i^i [ B ] R ) =/= (/) -> [ A ] R = [ B ] R ) ) $=
    ( wcel cqmap crn celdisjs cdm wa cec cin c0 wne wi cqs weldisj cvv eceldmqs
    wceq rnqmap eleq1i wb dmqsex eleldisjseldisj syl eldisjim3 anbi12d imbitrid
    bitrid imbi1d sylbid 3imp ) CDEZCFGZHEZACIZEZBUQEZJZACKZBCKZLMNVAVBTOZUNUPU
    QCPZQZUTVCOZUPVDHEZUNVEUOVDHCUAUBUNVDREVGVEUCCDUDVDRUEUFUJVEVAVDEZVBVDEZJZV
    COUNVFVDVAVBUGUNVJUTVCUNVHURVIUSACDSBCDSUHUKUIULUM $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Antisymmetry
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define the antisymmetric relation predicate.  (Read: ` R ` is an
     antisymmetric relation.)  (Contributed by Peter Mazsa, 24-Jun-2024.) $)
  df-antisymrel $a |- ( AntisymRel R <->
                        ( CnvRefRel ( R i^i `' R ) /\ Rel R ) ) $.

  $( Alternate definition of the antisymmetric relation predicate.
     (Contributed by Peter Mazsa, 24-Jun-2024.) $)
  dfantisymrel4 $p |- ( AntisymRel R <->
                        ( ( R i^i `' R ) C_ _I /\ Rel R ) ) $=
    ( wantisymrel ccnv cin wcnvrefrel cid wss df-antisymrel relcnv relin2 ax-mp
    wrel dfcnvrefrel4 mpbiran2 bianbi ) ABAACZDZEZALQFGZAHRSQLZPLTAIAPJKQMNO $.

  ${
    $d R x y $.
    $( Alternate definition of the antisymmetric relation predicate.
       (Contributed by Peter Mazsa, 24-Jun-2024.) $)
    dfantisymrel5 $p |- ( AntisymRel R <->
        ( A. x A. y ( ( x R y /\ y R x ) -> x = y ) /\ Rel R ) ) $=
      ( wantisymrel ccnv cin wcnvrefrel wrel cv wa wceq wi df-antisymrel relcnv
      wbr wal relin2 ax-mp dfcnvrefrel5 cvv mpbiran2 brcnvin el2v imbi1i 2albii
      wb bitri bianbi ) CDCCEZFZGZCHAIZBIZCOUMULCOJZULUMKZLZBPAPZCMUKULUMUJOZUO
      LZBPAPZUQUKUTUJHZUIHVACNCUIQRABUJSUAUSUPABURUNUOURUNUFABULUMCCTTUBUCUDUEU
      GUH $.
  $}

  ${
    $d A x y $.  $d R x y $.
    $( (Contributed by Peter Mazsa, 25-Jun-2024.) $)
    antisymrelres $p |- ( AntisymRel ( R |` A ) <->
        A. x e. A A. y e. A ( ( x R y /\ y R x ) -> x = y ) ) $=
      ( cres wantisymrel cv wbr wa wceq wi wal wcel wral wrel relres wb cvv elv
      brres dfantisymrel5 mpbiran2 anbi12i bitri imbi1i 2albii r2alan 3bitri
      an4 ) DCEZFZAGZBGZUJHZUMULUJHZIZULUMJZKZBLALZULCMZUMCMZIULUMDHZUMULDHZIZI
      ZUQKZBLALVDUQKBCNACNUKUSUJODCPABUJUAUBURVFABUPVEUQUPUTVBIZVAVCIZIVEUNVGUO
      VHUNVGQBCULUMDRTSUOVHQACUMULDRTSUCUTVBVAVCUIUDUEUFVDUQABCCUGUH $.
  $}

  ${
    $d A x y $.  $d R x y $.
    $( (Contributed by Peter Mazsa, 29-Jun-2024.) $)
    antisymrelressn $p |- AntisymRel ( R |` { A } ) $=
      ( vx vy csn cres wantisymrel cv wbr wa wceq wi antisymressn dfantisymrel5
      wal wrel relres mpbir2an ) BAEZFZGCHZDHZTIUBUATIJUAUBKLDOCOTPCDABMBSQCDTN
      R $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Partitions: disjoints on domain quotients
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define the class of all partitions, cf. the comment of ~ df-disjs .
     Partitions are disjoints on domain quotients (or: domain quotients
     restricted to disjoints).

     This is a more general meaning of partition than we we are familiar with:
     the conventional meaning of partition (e.g. partition ` A ` of ` X ` ,
     [Halmos] p. 28:  "A partition of ` X ` is a disjoint collection ` A ` of
     non-empty subsets of ` X ` whose union is ` X ` ", or Definition 35,
     [Suppes] p. 83., cf. ~ https://oeis.org/A000110 ) is what we call
     membership partition here, cf. ~ dfmembpart2 .

     The binary partitions relation and the partition predicate are the same,
     that is, ` ( R Parts A <-> R Part A ) ` if ` A ` and ` R ` are sets, cf.
     ~ brpartspart .  (Contributed by Peter Mazsa, 26-Jun-2021.) $)
  df-parts $a |- Parts = ( DomainQss |` Disjs ) $.

  $( Define the partition predicate (read: ` A ` is a partition by ` R ` ).
     Alternative definition is ~ dfpart2 .  The binary partition and the
     partition predicate are the same if ` A ` and ` R ` are sets, cf.
     ~ brpartspart .  (Contributed by Peter Mazsa, 12-Aug-2021.) $)
  df-part $a |- ( R Part A <-> ( Disj R /\ R DomainQs A ) ) $.

  $( Define the class of member partition relations on their domain quotients.
     (Contributed by Peter Mazsa, 26-Jun-2021.) $)
  df-membparts $a |- MembParts = { a | ( `' _E |` a ) Parts a } $.

  $( Define the member partition predicate, or the disjoint restricted element
     relation on its domain quotient predicate.  (Read: ` A ` is a member
     partition.)  A alternative definition is ~ dfmembpart2 .

     Member partition is the conventional meaning of partition (see the notes
     of ~ df-parts and ~ dfmembpart2 ), we generalize the concept in ~ df-parts
     and ~ df-part .

     Member partition and comember equivalence are the same by ~ mpet .
     (Contributed by Peter Mazsa, 26-Jun-2021.) $)
  df-membpart $a |- ( MembPart A <-> ( `' _E |` A ) Part A ) $.

  $( Alternate definition of the partition predicate.  (Contributed by Peter
     Mazsa, 5-Sep-2021.) $)
  dfpart2 $p |- ( R Part A <-> ( Disj R /\ ( dom R /. R ) = A ) ) $=
    ( wpart wdisjALTV wdmqs wa cdm cqs wceq df-part df-dmqs anbi2i bitri ) ABCB
    DZABEZFNBGBHAIZFABJOPNABKLM $.

  $( Alternate definition of the conventional membership case of partition.
     Partition ` A ` of ` X ` , [Halmos] p. 28:  "A partition of ` X ` is a
     disjoint collection ` A ` of non-empty subsets of ` X ` whose union is
     ` X ` ", or Definition 35, [Suppes] p. 83., cf. https://oeis.org/A000110 .
     (Contributed by Peter Mazsa, 14-Aug-2021.) $)
  dfmembpart2 $p |- ( MembPart A <-> ( ElDisj A /\ -. (/) e. A ) ) $=
    ( wmembpart cep ccnv cres wpart wdisjALTV wdmqs wa weldisj wcel df-membpart
    c0 wn df-part df-eldisj bicomi cnvepresdmqs anbi12i 3bitri ) ABACDAEZFUAGZA
    UAHZIAJZMAKNZIALAUAOUBUDUCUEUDUBAPQARST $.

  $( Binary partitions relation.  (Contributed by Peter Mazsa, 23-Jul-2021.) $)
  brparts $p |- ( A e. V ->
                  ( R Parts A <-> ( R e. Disjs /\ R DomainQss A ) ) ) $=
    ( cdisjs cparts cdmqss df-parts eqres ) BADEFCGH $.

  $( Binary partitions relation.  (Contributed by Peter Mazsa, 30-Dec-2021.) $)
  brparts2 $p |- ( ( A e. V /\ R e. W ) ->
      ( R Parts A <-> ( R e. Disjs /\ ( dom R /. R ) = A ) ) ) $=
    ( wcel wa cparts wbr cdisjs cdmqss cdm cqs wb brparts adantr brdmqss anbi2d
    wceq bitrd ) ACEZBDEZFZBAGHZBIEZBAJHZFZUDBKBLARZFTUCUFMUAABCNOUBUEUGUDABCDP
    QS $.

  $( Binary partition and the partition predicate are the same if ` A ` and
     ` R ` are sets.  (Contributed by Peter Mazsa, 5-Sep-2021.) $)
  brpartspart $p |- ( ( A e. V /\ R e. W ) -> ( R Parts A <-> R Part A ) ) $=
    ( wcel wa cdisjs cdmqss wbr wdisjALTV wdmqs cparts wpart eldisjsdisj adantl
    wb brdmqssqs anbi12d brparts adantr df-part a1i 3bitr4d ) ACEZBDEZFZBGEZBAH
    IZFZBJZABKZFZBALIZABMZUFUGUJUHUKUEUGUJPUDBDNOABCDQRUDUMUIPUEABCSTUNULPUFABU
    AUBUC $.

  $( Equality theorem for partition.  (Contributed by Peter Mazsa,
     5-Oct-2021.) $)
  parteq1 $p |- ( R = S -> ( R Part A <-> S Part A ) ) $=
    ( wceq wdisjALTV cdm cqs wa wpart disjdmqseqeq1 dfpart2 3bitr4g ) BCDBEBFBG
    ADHCECFCGADHABIACIABCJABKACKL $.

  $( Equality theorem for partition.  (Contributed by Peter Mazsa,
     25-Jul-2024.) $)
  parteq2 $p |- ( A = B -> ( R Part A <-> R Part B ) ) $=
    ( wceq wdisjALTV cdm cqs wa wpart eqeq2 anbi2d dfpart2 3bitr4g ) ABDZCEZCFC
    GZADZHOPBDZHACIBCINQROABPJKACLBCLM $.

  $( Equality theorem for partition.  (Contributed by Peter Mazsa,
     25-Jul-2024.) $)
  parteq12 $p |- ( ( R = S /\ A = B ) -> ( R Part A <-> S Part B ) ) $=
    ( wceq wpart parteq1 parteq2 sylan9bb ) CDEACFADFABEBDFACDGABDHI $.

  ${
    parteq1i.1 $e |- R = S $.
    $( Equality theorem for partition, inference version.  (Contributed by
       Peter Mazsa, 5-Oct-2021.) $)
    parteq1i $p |- ( R Part A <-> S Part A ) $=
      ( wceq wpart wb parteq1 ax-mp ) BCEABFACFGDABCHI $.
  $}

  ${
    parteq1d.1 $e |- ( ph -> R = S ) $.
    $( Equality theorem for partition, deduction version.  (Contributed by
       Peter Mazsa, 5-Oct-2021.) $)
    parteq1d $p |- ( ph -> ( R Part A <-> S Part A ) ) $=
      ( wceq wpart wb parteq1 syl ) ACDFBCGBDGHEBCDIJ $.
  $}

  $( Property of the partition.  (Contributed by Peter Mazsa, 24-Jul-2024.) $)
  partsuc2 $p |- ( ( ( R |` ( A u. { A } ) ) \ ( R |` { A } ) ) Part
                     ( ( A u. { A } ) \ { A } ) <->
                   ( R |` A ) Part A ) $=
    ( csn cun cres cdif wceq wpart wb ressucdifsn2 sucdifsn2 parteq12 mp2an ) B
    AACZDZEBNEFZBAEZGONFZAGRPHAQHIABJAKRAPQLM $.

  $( Property of the partition.  (Contributed by Peter Mazsa, 20-Sep-2024.) $)
  partsuc $p |-
      ( ( ( R |` suc A ) \ ( R |` { A } ) ) Part ( suc A \ { A } ) <->
        ( R |` A ) Part A ) $=
    ( csuc cres csn cdif wceq wpart wb ressucdifsn sucdifsn parteq12 mp2an ) BA
    CZDBAEZDFZBADZGNOFZAGRPHAQHIABJAKRAPQLM $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Partition-Equivalence Theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d R u x y z $.
    $( The "Divide et Aequivalere" Theorem: every disjoint relation generates
       equivalent cosets by the relation: generalization of the former
       ~ prter1 , cf. ~ eldisjim .  (Contributed by Peter Mazsa, 3-May-2019.)
       (Revised by Peter Mazsa, 17-Sep-2021.) $)
    disjim $p |- ( Disj R -> EqvRel ,~ R ) $=
      ( vx vy vz vu wdisjALTV cv ccoss wbr wal weqvrel wrel dfdisjALTV4 simplbi
      wa wi wmo trcoss syl eqvrelcoss3 sylibr ) AFZBGZCGZAHZIUDDGZUEIOUCUFUEIPD
      JCJBJZUEKUBEGUDAIEQCJZUGUBUHALCEAMNBCDEARSBCDATUA $.
  $}

  ${
    disjimi.1 $e |- Disj R $.
    $( Every disjoint relation generates equivalent cosets by the relation,
       inference version.  (Contributed by Peter Mazsa, 30-Sep-2021.) $)
    disjimi $p |- EqvRel ,~ R $=
      ( wdisjALTV ccoss weqvrel disjim ax-mp ) ACADEBAFG $.
  $}

  ${
    detlem.1 $e |- Disj R $.
    $( If a relation is disjoint, then it is equivalent to the equivalent
       cosets of the relation, inference version.  (Contributed by Peter Mazsa,
       30-Sep-2021.) $)
    detlem $p |- ( Disj R <-> EqvRel ,~ R ) $=
      ( wdisjALTV ccoss weqvrel disjim a1i impbii ) ACZADEZAFIJBGH $.
  $}

  $( If the elements of ` A ` are disjoint, then it has equivalent coelements
     (former ~ prter1 ).  Special case of ~ disjim .  (Contributed by Rodolfo
     Medina, 13-Oct-2010.)  (Revised by Mario Carneiro, 12-Aug-2015) (Revised
     by Peter Mazsa, 8-Feb-2018.)  ( Revised by Peter Mazsa, 23-Sep-2021.) $)
  eldisjim $p |- ( ElDisj A -> CoElEqvRel A ) $=
    ( cep ccnv wdisjALTV ccoss weqvrel weldisj wcoeleqvrel disjim df-coeleqvrel
    cres df-eldisj 3imtr4i ) BCAKZDNEFAGAHNIALAJM $.

  $( Alternate form of ~ eldisjim .  (Contributed by Peter Mazsa,
     30-Dec-2024.) $)
  eldisjim2 $p |- ( ElDisj A -> EqvRel ~ A ) $=
    ( cep ccnv wdisjALTV ccoss weqvrel weldisj ccoels disjim df-eldisj df-coels
    cres eqvreleqi 3imtr4i ) BCALZDOEZFAGAHZFOIAJQPAKMN $.

  $( The null class is an equivalence relation.  (Contributed by Peter Mazsa,
     31-Dec-2021.) $)
  eqvrel0 $p |- EqvRel (/) $=
    ( c0 ccoss weqvrel disjALTV0 disjimi coss0 eqvreleqi mpbi ) ABZCACADEIAFGH
    $.

  $( The cosets by the null class are in equivalence relation if and only if
     the null class is disjoint (which it is, see ~ disjALTV0 ).  (Contributed
     by Peter Mazsa, 31-Dec-2021.) $)
  det0 $p |- ( Disj (/) <-> EqvRel ,~ (/) ) $=
    ( c0 disjALTV0 detlem ) ABC $.

  $( The cosets by the null class are in equivalence relation.  (Contributed by
     Peter Mazsa, 31-Dec-2024.) $)
  eqvrelcoss0 $p |- EqvRel ,~ (/) $=
    ( c0 disjALTV0 disjimi ) ABC $.

  $( The identity relation is an equivalence relation.  (Contributed by Peter
     Mazsa, 15-Apr-2019.)  (Revised by Peter Mazsa, 31-Dec-2021.) $)
  eqvrelid $p |- EqvRel _I $=
    ( cid ccoss weqvrel disjALTVid disjimi cossid eqvreleqi mpbi ) ABZCACADEIAF
    GH $.

  $( The cosets by a restricted identity relation is an equivalence relation.
     (Contributed by Peter Mazsa, 31-Dec-2021.) $)
  eqvrel1cossidres $p |- EqvRel ,~ ( _I |` A ) $=
    ( cid cres disjALTVidres disjimi ) BACADE $.

  $( The cosets by an intersection with a restricted identity relation are in
     equivalence relation.  (Contributed by Peter Mazsa, 31-Dec-2021.) $)
  eqvrel1cossinidres $p |- EqvRel ,~ ( R i^i ( _I |` A ) ) $=
    ( cid cres cin disjALTVinidres disjimi ) BCADEABFG $.

  $( The cosets by a range Cartesian product with a restricted identity
     relation are in equivalence relation.  (Contributed by Peter Mazsa,
     31-Dec-2021.) $)
  eqvrel1cossxrnidres $p |- EqvRel ,~ ( R |X. ( _I |` A ) ) $=
    ( cid cres cxrn disjALTVxrnidres disjimi ) BCADEABFG $.

  $( The cosets by the identity relation are in equivalence relation if and
     only if the identity relation is disjoint.  (Contributed by Peter Mazsa,
     31-Dec-2021.) $)
  detid $p |- ( Disj _I <-> EqvRel ,~ _I ) $=
    ( cid disjALTVid detlem ) ABC $.

  $( The cosets by the identity class are in equivalence relation.
     (Contributed by Peter Mazsa, 31-Dec-2024.) $)
  eqvrelcossid $p |- EqvRel ,~ _I $=
    ( cid disjALTVid disjimi ) ABC $.

  $( The cosets by the restricted identity relation are in equivalence relation
     if and only if the restricted identity relation is disjoint.  (Contributed
     by Peter Mazsa, 31-Dec-2021.) $)
  detidres $p |- ( Disj ( _I |` A ) <-> EqvRel ,~ ( _I |` A ) ) $=
    ( cid cres disjALTVidres detlem ) BACADE $.

  $( The cosets by the intersection with the restricted identity relation are
     in equivalence relation if and only if the intersection with the
     restricted identity relation is disjoint.  (Contributed by Peter Mazsa,
     31-Dec-2021.) $)
  detinidres $p |- ( Disj ( R i^i ( _I |` A ) ) <->
                     EqvRel ,~ ( R i^i ( _I |` A ) ) ) $=
    ( cid cres cin disjALTVinidres detlem ) BCADEABFG $.

  $( The cosets by the range Cartesian product with the restricted identity
     relation are in equivalence relation if and only if the range Cartesian
     product with the restricted identity relation is disjoint.  (Contributed
     by Peter Mazsa, 31-Dec-2021.) $)
  detxrnidres $p |- ( Disj ( R |X. ( _I |` A ) ) <->
                      EqvRel ,~ ( R |X. ( _I |` A ) ) ) $=
    ( cid cres cxrn disjALTVxrnidres detlem ) BCADEABFG $.

  ${
    $d R x y $.
    $( Lemma for ~ disjdmqseq , ~ partim2 and ~ petlem via ~ disjlem17 ,
       (general version of the former ~ prtlem14 ).  (Contributed by Peter
       Mazsa, 10-Sep-2021.) $)
    disjlem14 $p |- ( Disj R ->
                      ( ( x e. dom R /\ y e. dom R ) ->
                        ( ( A e. [ x ] R /\ A e. [ y ] R ) ->
                          [ x ] R = [ y ] R ) ) ) $=
      ( wdisjALTV cv cdm wcel wa wceq cec cin c0 wo wi wral dfdisjALTV5 simplbi
      wrel rsp2 syl eceq1 a1d elin nel02 pm2.21d biimtrrid jaoi syl6 ) DEZAFZDG
      ZHBFZULHIZUKUMJZUKDKZUMDKZLZMJZNZCUPHCUQHIZUPUQJZOZUJUTBULPAULPZUNUTOUJVD
      DSBADQRUTABULULTUAUOVCUSUOVBVAUKUMDUBUCVACURHZUSVBCUPUQUDUSVEVBURCUEUFUGU
      HUI $.
  $}

  ${
    $d A y $.  $d B y $.  $d R x y $.
    $( Lemma for ~ disjdmqseq , ~ partim2 and ~ petlem via ~ disjlem18 ,
       (general version of the former ~ prtlem17 ).  (Contributed by Peter
       Mazsa, 10-Sep-2021.) $)
    disjlem17 $p |- ( Disj R ->
                      ( ( x e. dom R /\ A e. [ x ] R ) ->
                        ( E. y e. dom R ( A e. [ y ] R /\ B e. [ y ] R ) ->
                          B e. [ x ] R ) ) ) $=
      ( wdisjALTV cv cdm wcel cec wa wrex wi df-rex an32 wceq disjlem14 biimprd
      wex eleq2 syl8 exp4a impd biimtrrid expd imp5a imp4b exlimdv biimtrid ex
      ) EFZAGZEHZIZCULEJZIZKZCBGZEJZIZDUSIZKZBUMLZDUOIZMVCURUMIZVBKZBSUKUQKZVDV
      BBUMNVGVFVDBUKUQVEVBVDUKUQVEUTVAVDUKUQVEUTVAVDMZMZUQVEKUNVEKZUPKUKVIUNVEU
      POUKVJUPVIUKVJUPUTVHUKVJUPUTKUOUSPZVHABCEQVKVDVAUOUSDTRUAUBUCUDUEUFUGUHUI
      UJ $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d R x y $.  $d V x y $.  $d W x y $.
    $( Lemma for ~ disjdmqseq , ~ partim2 and ~ petlem via ~ disjlem19 ,
       (general version of the former ~ prtlem18 ).  (Contributed by Peter
       Mazsa, 16-Sep-2021.) $)
    disjlem18 $p |- ( ( A e. V /\ B e. W ) ->
                      ( Disj R ->
                        ( ( x e. dom R /\ A e. [ x ] R ) ->
                          ( B e. [ x ] R <-> A ,~ R B ) ) ) ) $=
      ( vy wcel wa wdisjALTV cv cec wb wi wrex adantl relbrcoss impel sylibrd
      ex cdm ccoss wbr rspe expr wrel disjrel adantr disjlem17 imbi1d impbidd )
      BEHCFHIZDJZAKZDUAZHZBUNDLZHZIZCUQHZBCDUBUCZMNULUMIZUSUTVAVBUSUTVANVBUSIUT
      URUTIZAUOOZVAUSUTVDNVBUPURUTVDVCAUOUDUEPVBVAVDMZUSULDUFZVEUMABCDEFQDUGZRU
      HSTVBUSBGKDLZHCVHHIGUOOZUTNZVAUTNUMUSVJNULAGBCDUIPVBVAVIUTULVFVAVIMUMGBCD
      EFQVGRUJSUKT $.
  $}

  ${
    $d A x z $.  $d R x z $.  $d V x z $.
    $( Lemma for ~ disjdmqseq , ~ partim2 and ~ petlem via ~ disjdmqs ,
       (general version of the former ~ prtlem19 ).  (Contributed by Peter
       Mazsa, 16-Sep-2021.) $)
    disjlem19 $p |- ( A e. V ->
                      ( Disj R ->
                        ( ( x e. dom R /\ A e. [ x ] R ) ->
                          [ x ] R = [ A ] ,~ R ) ) ) $=
      ( vz wcel wdisjALTV cv cdm cec wa ccoss wceq wbr wb wi cvv disjlem18 elvd
      imp31 elecALTV ad2antrr bitr4d eqrdv exp31 ) BDFZCGZAHZCIFBUHCJZFKZUIBCLZ
      JZMUFUGKUJKZEUIULUMEHZUIFZBUNUKNZUNULFZUFUGUJUOUPOZUFUGUJURPPEABUNCDQRSTU
      FUQUPOZUGUJUFUSEBUNUKDQUASUBUCUDUE $.
  $}

  ${
    $d R u v x $.
    $( Lemma for ~ disjdmqseq via ~ disjdmqs .  (Contributed by Peter Mazsa,
       16-Sep-2021.) $)
    disjdmqsss $p |- ( Disj R -> ( dom R /. R ) C_ ( dom ,~ R /. ,~ R ) ) $=
      ( vv vx vu wdisjALTV cdm cqs cv wcel cec wceq wrex wa wb cvv elv syl wral
      wi reximi ccoss wrel disjrel releldmqs disjlem19 ralrimivv 2r19.29 sylbid
      ex eqtr ancoms syl6 releldmqscoss sylibrd ssrdv ) AEZBAFZAGZAUAZFUSGZUPBH
      ZURIZVACHZUSJZKZCDHZAJZLZDUQLZVAUTIZUPVBVGVDKZVAVGKZMZCVGLZDUQLZVIUPVBVLC
      VGLDUQLZVOUPAUBZVBVPNZAUCZVQVRSBCDVAAOUDPQUPVKCVGRDUQRZVPVOSUPVKDCUQVGUPV
      FUQIVCVGIMVKSSCDVCAOUEPUFVTVPVOVKVLDCUQVGUGUIQUHVNVHDUQVMVECVGVLVKVEVAVGV
      DUJUKTTULUPVQVJVINZVSVQWASBCDVAAOUMPQUNUO $.
  $}

  ${
    $d R u v x $.
    $( Lemma for ~ disjdmqseq via ~ disjdmqs .  (Contributed by Peter Mazsa,
       16-Sep-2021.) $)
    disjdmqscossss $p |- ( Disj R ->
                           ( dom ,~ R /. ,~ R ) C_ ( dom R /. R ) ) $=
      ( vv vu vx cv cdm cqs wcel cab cec wceq wrex cvv elv syl wral reximi syl6
      wa wi wdisjALTV wrel wb disjrel releldmqscoss disjlem19 ralrimivv 2r19.29
      ccoss sylbid eqtr3 wex df-rex 19.41v bitri simprbi eqcom imbitrdi ss2abdv
      ex rexbii abid1 df-qs 3sstr4g ) AUAZBEZAUIZFVGGZHZBIVFCEZAJZKZCAFZLZBIVHV
      MAGVEVIVNBVEVIVKVFKZCVMLZVNVEVIVODVKLZCVMLZVPVEVIVKDEZVGJZKZVFVTKZSZDVKLZ
      CVMLZVRVEVIWBDVKLCVMLZWEVEAUBZVIWFUCZAUDWGWHTBDCVFAMUENOVEWADVKPCVMPZWFWE
      TVEWACDVMVKVEVJVMHVSVKHZSWATTDCVSAMUFNUGWIWFWEWAWBCDVMVKUHUTOUJWDVQCVMWCV
      ODVKVKVFVTUKQQRVQVOCVMVQWJDULZVOVQWJVOSDULWKVOSVODVKUMWJVODUNUOUPQRVOVLCV
      MVKVFUQVAURUSBVHVBCBVMAVCVD $.
  $}

  $( If a relation is disjoint, its domain quotient is equal to the domain
     quotient of the cosets by it.  Lemma for ~ partim2 and ~ petlem via
     ~ disjdmqseq .  (Contributed by Peter Mazsa, 16-Sep-2021.) $)
  disjdmqs $p |- ( Disj R -> ( dom R /. R ) = ( dom ,~ R /. ,~ R ) ) $=
    ( wdisjALTV cdm cqs ccoss disjdmqsss disjdmqscossss eqssd ) ABACADAEZCIDAFA
    GH $.

  $( If a relation is disjoint, its domain quotient is equal to a class if and
     only if the domain quotient of the cosets by it is equal to the class.
     General version of ~ eldisjn0el (which is the closest theorem to the
     former ~ prter2 ).  Lemma for ~ partim2 and ~ petlem .  (Contributed by
     Peter Mazsa, 16-Sep-2021.) $)
  disjdmqseq $p |- ( Disj R ->
      ( ( dom R /. R ) = A <-> ( dom ,~ R /. ,~ R ) = A ) ) $=
    ( wdisjALTV cdm cqs ccoss disjdmqs eqeq1d ) BCBDBEBFZDIEABGH $.

  $( Special case of ~ disjdmqseq (perhaps this is the closest theorem to the
     former ~ prter2 ).  (Contributed by Peter Mazsa, 26-Sep-2021.) $)
  eldisjn0el $p |- ( ElDisj A ->
                     ( -. (/) e. A <-> ( U. A /. ~ A ) = A ) ) $=
    ( cep ccnv cres wdisjALTV cdm cqs wceq ccoss wb weldisj c0 wcel cuni ccoels
    wn disjdmqseq df-eldisj n0el3 dmqs1cosscnvepreseq bicomi bibi12i 3imtr4i )
    BCADZEUDFUDGAHZUDIZFUFGAHZJAKLAMPZANAOGAHZJAUDQARUHUEUIUGASUGUIATUAUBUC $.

  $( Disjoint relation on its natural domain implies an equivalence relation on
     the cosets of the relation, on its natural domain, cf. ~ partim .  Lemma
     for ~ petlem .  (Contributed by Peter Mazsa, 17-Sep-2021.) $)
  partim2 $p |- ( ( Disj R /\ ( dom R /. R ) = A ) ->
                  ( EqvRel ,~ R /\ ( dom ,~ R /. ,~ R ) = A ) ) $=
    ( wdisjALTV cdm cqs wceq ccoss weqvrel disjim adantr disjdmqseq biimpa jca
    wa ) BCZBDBEAFZNBGZHZQDQEAFZORPBIJOPSABKLM $.

  $( Partition implies equivalence relation by the cosets of the relation on
     its natural domain, cf. ~ partim2 .  (Contributed by Peter Mazsa,
     17-Sep-2021.) $)
  partim $p |- ( R Part A -> ,~ R ErALTV A ) $=
    ( wdisjALTV cdm cqs wceq wa ccoss weqvrel werALTV partim2 dfpart2 dferALTV2
    wpart 3imtr4i ) BCBDBEAFGBHZIPDPEAFGABNAPJABKABLAPMO $.

  $( Partition implies that the class of coelements on the natural domain is
     equal to the class of cosets of the relation, cf. ~ erimeq .  (Contributed
     by Peter Mazsa, 25-Dec-2024.) $)
  partimeq $p |- ( R e. V -> ( R Part A -> ~ A = ,~ R ) ) $=
    ( wcel ccoss cvv wpart werALTV ccoels wceq cossex partim erimeq syl2im ) BC
    DBEZFDABGAOHAIOJBCKABLAOFMN $.

  ${
    $d A u $.  $d B u $.  $d V u $.
    $( Special case of ~ disjlem19 (together with ~ membpartlem19 , this is
       former ~ prtlem19 ).  (Contributed by Peter Mazsa, 21-Oct-2021.) $)
    eldisjlem19 $p |- ( B e. V ->
                          ( ElDisj A ->
                            ( ( u e. dom ( `' _E |` A ) /\ B e. u ) ->
                              u = [ B ] ~ A ) ) ) $=
      ( wcel weldisj cv cep ccnv cres cdm wa ccoels cec wceq wi ccoss wdisjALTV
      df-eldisj disjlem19 biimtrid expdimp wb eccnvepres3 eleq2d eqeq1d imbi12d
      imp adantl mpbid df-coels eceq2i eqeq2i imbitrrdi expimpd ex ) CDEZBFZAGZ
      HIBJZKEZCUSEZLUSCBMZNZOZPUQURLZVAVBVEVFVALZVBUSCUTQZNZOZVEVGCUSUTNZEZVKVI
      OZPZVBVJPZVFVAVLVMUQURVAVLLVMPZURUTRUQVPBSACUTDTUAUHUBVAVNVOUCVFVAVLVBVMV
      JVAVKUSCBUSUDZUEVAVKUSVIVQUFUGUIUJVDVIUSVCVHCBUKULUMUNUOUP $.
  $}

  ${
    $d A u $.  $d B u $.  $d V u $.
    $( Together with ~ disjlem19 , this is former ~ prtlem19 .  (Contributed by
       Rodolfo Medina, 15-Oct-2010.)  (Revised by Mario Carneiro, 12-Aug-2015.)
       (Revised by Peter Mazsa, 21-Oct-2021.) $)
    membpartlem19 $p |- ( B e. V ->
                          ( MembPart A ->
                            ( ( u e. A /\ B e. u ) ->
                              u = [ B ] ~ A ) ) ) $=
      ( wcel wmembpart cv wa ccoels cec wceq wi weldisj c0 dfmembpart2 cep ccnv
      wn cres cdm n0el2 biimpi ad2antll eleq2d eldisjlem19 adantrd expd sylbird
      imp sylan2b impd ex ) CDEZBFZAGZBEZCUOEZHUOCBIJKZLUMUNHUPUQURUNUMBMZNBERZ
      HZUPUQURLZLBOUMVAHZUPUOPQBSTZEZVBVCVDBUOUTVDBKZUMUSUTVFBUAUBUCUDVCVEUQURU
      MVAVEUQHURLZUMUSVGUTABCDUEUFUIUGUHUJUKUL $.
  $}

  ${
    petlem.1 $e |- ( ( EqvRel ,~ R /\ ( dom ,~ R /. ,~ R ) = A ) ->
                     Disj R ) $.
    $( If you can prove that the equivalence of cosets on their natural domain
       implies disjointness (e.g. ~ eqvrelqseqdisj5 ), or converse function
       (cf. ~ dfdisjALTV ), then disjointness, and equivalence of cosets, both
       on their natural domain, are equivalent.  Lemma for the Partition
       Equivalence Theorem ~ pet2 .  (Contributed by Peter Mazsa,
       18-Sep-2021.) $)
    petlem $p |- ( ( Disj R /\ ( dom R /. R ) = A ) <->
                   ( EqvRel ,~ R /\ ( dom ,~ R /. ,~ R ) = A ) ) $=
      ( wdisjALTV cdm wceq wa ccoss weqvrel partim2 disjdmqseq pm5.32i sylanbrc
      cqs simpr impbii ) BDZBEBNAFZGZBHZIZTETNAFZGZABJUCQUBSCUAUBOQRUBABKLMP $.
  $}

  ${
    petlemi.1 $e |- Disj R $.
    $( If you can prove disjointness (e.g. ~ disjALTV0 , ~ disjALTVid ,
       ~ disjALTVidres , ~ disjALTVxrnidres , search for theorems containing
       the ' |- Disj ' string), or the same with converse function (cf.
       ~ dfdisjALTV ), then disjointness, and equivalence of cosets, both on
       their natural domain, are equivalent.  (Contributed by Peter Mazsa,
       18-Sep-2021.) $)
    petlemi $p |- ( ( Disj R /\ ( dom R /. R ) = A ) <->
                    ( EqvRel ,~ R /\ ( dom ,~ R /. ,~ R ) = A ) ) $=
      ( wdisjALTV ccoss weqvrel cdm cqs wceq wa a1i petlem ) ABBDBEZFMGMHAIJCKL
      $.
  $}

  $( Class ` A ` is a partition by the null class if and only if the cosets by
     the null class are in equivalence relation on it.  (Contributed by Peter
     Mazsa, 31-Dec-2021.) $)
  pet02 $p |- ( ( Disj (/) /\ ( dom (/) /. (/) ) = A ) <->
                ( EqvRel ,~ (/) /\ ( dom ,~ (/) /. ,~ (/) ) = A ) ) $=
    ( c0 disjALTV0 petlemi ) ABCD $.

  $( Class ` A ` is a partition by the null class if and only if the cosets by
     the null class are in equivalence relation on it.  (Contributed by Peter
     Mazsa, 31-Dec-2021.) $)
  pet0 $p |- ( (/) Part A <-> ,~ (/) ErALTV A ) $=
    ( c0 wdisjALTV cdm wceq ccoss weqvrel wpart werALTV pet02 dfpart2 dferALTV2
    cqs wa 3bitr4i ) BCBDBMAENBFZGPDPMAENABHAPIAJABKAPLO $.

  $( Class ` A ` is a partition by the identity class if and only if the cosets
     by the identity class are in equivalence relation on it.  (Contributed by
     Peter Mazsa, 31-Dec-2021.) $)
  petid2 $p |- ( ( Disj _I /\ ( dom _I /. _I ) = A ) <->
                 ( EqvRel ,~ _I /\ ( dom ,~ _I /. ,~ _I ) = A ) ) $=
    ( cid disjALTVid petlemi ) ABCD $.

  $( A class is a partition by the identity class if and only if the cosets by
     the identity class are in equivalence relation on it.  (Contributed by
     Peter Mazsa, 31-Dec-2021.) $)
  petid $p |- ( _I Part A <-> ,~ _I ErALTV A ) $=
    ( cid wdisjALTV cdm cqs wceq ccoss weqvrel werALTV petid2 dfpart2 dferALTV2
    wa wpart 3bitr4i ) BCBDBEAFMBGZHPDPEAFMABNAPIAJABKAPLO $.

  $( Class ` A ` is a partition by the identity class restricted to it if and
     only if the cosets by the restricted identity class are in equivalence
     relation on it.  (Contributed by Peter Mazsa, 31-Dec-2021.) $)
  petidres2 $p |- ( ( Disj ( _I |` A ) /\
                      ( dom ( _I |` A ) /. ( _I |` A ) ) = A ) <->
                    ( EqvRel ,~ ( _I |` A ) /\
                      ( dom ,~ ( _I |` A ) /. ,~ ( _I |` A ) ) = A ) ) $=
    ( cid cres disjALTVidres petlemi ) ABACADE $.

  $( A class is a partition by identity class restricted to it if and only if
     the cosets by the restricted identity class are in equivalence relation on
     it, cf. ~ eqvrel1cossidres .  (Contributed by Peter Mazsa,
     31-Dec-2021.) $)
  petidres $p |- ( ( _I |` A ) Part A <-> ,~ ( _I |` A ) ErALTV A ) $=
    ( cid cres wdisjALTV cdm wceq ccoss weqvrel wpart werALTV petidres2 dfpart2
    cqs wa dferALTV2 3bitr4i ) BACZDQEQMAFNQGZHRERMAFNAQIARJAKAQLAROP $.

  $( Class ` A ` is a partition by an intersection with the identity class
     restricted to it if and only if the cosets by the intersection are in
     equivalence relation on it.  (Contributed by Peter Mazsa, 31-Dec-2021.) $)
  petinidres2 $p |- ( ( Disj ( R i^i ( _I |` A ) ) /\
                        ( dom ( R i^i ( _I |` A ) ) /.
                          ( R i^i ( _I |` A ) ) ) = A ) <->
                      ( EqvRel ,~ ( R i^i ( _I |` A ) ) /\
                        ( dom ,~ ( R i^i ( _I |` A ) ) /.
                          ,~ ( R i^i ( _I |` A ) ) ) = A ) ) $=
    ( cid cres cin disjALTVinidres petlemi ) ABCADEABFG $.

  $( A class is a partition by an intersection with the identity class
     restricted to it if and only if the cosets by the intersection are in
     equivalence relation on it.  Cf. ~ br1cossinidres , ~ disjALTVinidres and
     ~ eqvrel1cossinidres .  (Contributed by Peter Mazsa, 31-Dec-2021.) $)
  petinidres $p |- ( ( R i^i ( _I |` A ) ) Part A <->
                     ,~ ( R i^i ( _I |` A ) ) ErALTV A ) $=
    ( cid cres cin wdisjALTV cdm cqs wa ccoss weqvrel wpart werALTV petinidres2
    wceq dfpart2 dferALTV2 3bitr4i ) BCADEZFSGSHAOISJZKTGTHAOIASLATMABNASPATQR
    $.

  $( Class ` A ` is a partition by a range Cartesian product with the identity
     class restricted to it if and only if the cosets by the range Cartesian
     product are in equivalence relation on it.  (Contributed by Peter Mazsa,
     31-Dec-2021.) $)
  petxrnidres2 $p |- ( ( Disj ( R |X. ( _I |` A ) ) /\
                         ( dom ( R |X. ( _I |` A ) ) /.
                          ( R |X. ( _I |` A ) ) ) = A ) <->
                       ( EqvRel ,~ ( R |X. ( _I |` A ) ) /\
                         ( dom ,~ ( R |X. ( _I |` A ) ) /.
                           ,~ ( R |X. ( _I |` A ) ) ) = A ) ) $=
    ( cid cres cxrn disjALTVxrnidres petlemi ) ABCADEABFG $.

  $( A class is a partition by a range Cartesian product with the identity
     class restricted to it if and only if the cosets by the range Cartesian
     product are in equivalence relation on it.  Cf. ~ br1cossxrnidres ,
     ~ disjALTVxrnidres and ~ eqvrel1cossxrnidres .  (Contributed by Peter
     Mazsa, 31-Dec-2021.) $)
  petxrnidres $p |- ( ( R |X. ( _I |` A ) ) Part A <->
                      ,~ ( R |X. ( _I |` A ) ) ErALTV A ) $=
    ( cid cres cxrn wdisjALTV cdm wceq ccoss weqvrel wpart werALTV petxrnidres2
    cqs wa dfpart2 dferALTV2 3bitr4i ) BCADEZFSGSNAHOSIZJTGTNAHOASKATLABMASPATQ
    R $.

  ${
    $d A y $.  $d R x y $.
    $( The elements of the quotient set of an equivalence relation are disjoint
       (cf. ~ eqvreldisj2 , ~ eqvreldisj3 ).  (Contributed by Mario Carneiro,
       10-Dec-2016.)  (Revised by Peter Mazsa, 3-Dec-2024.) $)
    eqvreldisj1 $p |- ( EqvRel R ->
                        A. x e. ( A /. R ) A. y e. ( A /. R )
                          ( x = y \/ ( x i^i y ) = (/) ) ) $=
      ( weqvrel cv wceq cin c0 wo cqs simpl simprl simprr qsdisjALTV ralrimivva
      wcel wa ) DEZAFZBFZGTUAHIGJABCDKZUBSTUBQZUAUBQZRZRCTUADSUELSUCUDMSUCUDNOP
      $.
  $}

  ${
    $d A x y $.  $d R x y $.
    $( The elements of the quotient set of an equivalence relation are disjoint
       (cf. ~ eqvreldisj3 ).  (Contributed by Mario Carneiro, 10-Dec-2016.)
       (Revised by Peter Mazsa, 19-Sep-2021.) $)
    eqvreldisj2 $p |- ( EqvRel R -> ElDisj ( A /. R ) ) $=
      ( vx vy weqvrel cv wceq cin cqs wral weldisj eqvreldisj1 dfeldisj5 sylibr
      c0 wo ) BECFZDFZGQRHOGPDABIZJCSJSKCDABLDCSMN $.
  $}

  $( The elements of the quotient set of an equivalence relation are disjoint
     (cf. ~ qsdisj2 ).  (Contributed by Mario Carneiro, 10-Dec-2016.)  (Revised
     by Peter Mazsa, 20-Jun-2019.)  (Revised by Peter Mazsa, 19-Sep-2021.) $)
  eqvreldisj3 $p |- ( EqvRel R -> Disj ( `' _E |` ( A /. R ) ) ) $=
    ( weqvrel cqs weldisj cep ccnv cres wdisjALTV eqvreldisj2 df-eldisj sylib )
    BCABDZEFGMHIABJMKL $.

  $( Intersection with the converse epsilon relation restricted to the quotient
     set of an equivalence relation is disjoint.  (Contributed by Peter Mazsa,
     30-May-2020.)  (Revised by Peter Mazsa, 31-Dec-2021.) $)
  eqvreldisj4 $p |- ( EqvRel R -> Disj ( S i^i ( `' _E |` ( B /. R ) ) ) ) $=
    ( weqvrel cep ccnv cqs cres wdisjALTV cin eqvreldisj3 disjimin syl ) BDEFAB
    GHZICNJIABKCNLM $.

  $( Range Cartesian product with converse epsilon relation restricted to the
     quotient set of an equivalence relation is disjoint.  (Contributed by
     Peter Mazsa, 30-May-2020.)  (Revised by Peter Mazsa, 22-Sep-2021.) $)
  eqvreldisj5 $p |- ( EqvRel R -> Disj ( S |X. ( `' _E |` ( B /. R ) ) ) ) $=
    ( weqvrel cep ccnv cqs cres wdisjALTV cxrn eqvreldisj3 disjimxrn syl ) BDEF
    ABGHZICNJIABKCNLM $.

  $( Implication of ~ eqvreldisj2 , lemma for The Main Theorem of Equivalences
     ~ mainer .  (Contributed by Peter Mazsa, 23-Sep-2021.) $)
  eqvrelqseqdisj2 $p |- ( ( EqvRel R /\ ( B /. R ) = A ) -> ElDisj A ) $=
    ( weqvrel cqs wceq wa weldisj eqvreldisj2 adantr wb eldisjeq adantl mpbid )
    CDZBCEZAFZGPHZAHZORQBCIJQRSKOPALMN $.

  $( ` Disj ` implies element-disjoint quotient carrier.  Supplies the
     carrier-disjointness half of the ` Disjs ` pattern: under ` Disj R ` , the
     coset family is element-disjoint.  (Contributed by Peter Mazsa,
     5-Feb-2026.) $)
  disjimeldisjdmqs $p |- ( Disj R -> ElDisj ( dom R /. R ) ) $=
    ( wdisjALTV weqvrel cdm wceq weldisj disjim disjdmqs eqcomd eqvrelqseqdisj2
    ccoss cqs syl2anc ) ABZAKZCODZOLZADALZERFAGNRQAHIRPOJM $.

  $( An element of the class of disjoint relations is disjoint.  (Contributed
     by Peter Mazsa, 11-Feb-2026.) $)
  eldisjsim1 $p |- ( R e. Disjs -> Disj R ) $=
    ( cdisjs wcel wdisjALTV eldisjsdisj ibi ) ABCADABEF $.

  $( An element of the class of disjoint relations is an element of the class
     of relations.  (Contributed by Peter Mazsa, 11-Feb-2026.) $)
  eldisjsim2 $p |- ( R e. Disjs -> R e. Rels ) $=
    ( crels wcel cdisjss cin cdisjs elinel2 df-disjs eleq2s ) ABCADBEFADBGHI $.

  $( The class of disjoint relations is a subclass of the class of relations.
     (Contributed by Peter Mazsa, 11-Feb-2026.) $)
  disjsssrels $p |- Disjs C_ Rels $=
    ( vr cdisjs crels cv eldisjsim2 ssriv ) ABCADEF $.

  $( ` Disjs ` implies element-disjoint quotient carrier.  Exports the
     carrier-disjointness property in the ` ElDisjs ` packaging.  (Contributed
     by Peter Mazsa, 11-Feb-2026.) $)
  eldisjsim3 $p |- ( R e. Disjs -> ( dom R /. R ) e. ElDisjs ) $=
    ( cdisjs cdm cqs celdisjs wi wdisjALTV weldisj disjimeldisjdmqs eldisjsdisj
    wcel cvv wb dmqsex eleldisjseldisj syl imbi12d mpbiri pm2.43i ) ABKZACADZEK
    ZTTUBFAGZUAHZFAITTUCUBUDABJTUALKUBUDMABNUALOPQRS $.

  $( ` Disjs ` implies element-disjoint range of ` QMap ` .  Same as
     ~ eldisjsim3 but expressed using the block-map range ` ran QMap R ` (often
     the more modular expression).  (Contributed by Peter Mazsa,
     15-Feb-2026.) $)
  eldisjsim4 $p |- ( R e. Disjs -> ran QMap R e. ElDisjs ) $=
    ( cdisjs wcel cqmap crn cdm cqs celdisjs rnqmap eldisjsim3 eqeltrid ) ABCAD
    EAFAGHAIAJK $.

  ${
    $d R t u $.
    $( ` Disjs ` is closed under ` QMap ` .  If a relation is
       "disjoint-structured" ( ` Disjs ` ), then its canonical block map is
       also "disjoint-structured".  This is the second "structure level" in
       ` Disjs ` : it expresses that the property is stable under passing to
       the canonical block map, a theme that mirrors Pet-grade stability at a
       different axis.  (Contributed by Peter Mazsa, 15-Feb-2026.) $)
    eldisjsim5 $p |- ( R e. Disjs -> QMap R e. Disjs ) $=
      ( vu vt cdisjs wcel cqmap wdisjALTV cec wceq cdm eldisjsim1 disjimrmoeqec
      cv wrmo wal syl alrimiv disjqmap2 mpbird qmapeldisjs ) ADEZAFZDEUBGZUAUCB
      MCMAHICAJNZBOUAUDBUAAGUDAKCBALPQBCADRSADTS $.
  $}

  ${
    $d R u v $.
    $( Elementhood in the class of disjoints.  A relation ` R ` is in ` Disjs `
       iff:

       it is relation-typed, and

       its quotient-map ` QMap R ` is itself disjoint, and

       its quotient-carrier ` ran QMap R = ( dom R /. R ) ` lies in ` ElDisjs `
       (element-disjoint carriers).

       This is the central "stability-by-decomposition" theorem for ` Disjs ` :
       it explains why ` Disjs ` is internally well-behaved without adding an
       external stability clause.  It is the exact template that ` PetParts `
       imitates: for ~ pet , the analogue of "map layer" is the disjointness of
       the lifted span, the analogue of "carrier layer" is the block-lift
       fixpoint ( ` BlockLiftFix ` ), and then adds external grade stability
       ( ` SucMap ShiftStable ` ) which ` Disjs ` does not need.  (Contributed
       by Peter Mazsa, 16-Feb-2026.) $)
    eldisjs6 $p |- ( R e. Disjs <->
        ( R e. Rels /\ ( ran QMap R e. ElDisjs /\ QMap R e. Disjs ) ) ) $=
      ( vu vv cdisjs wcel crels cqmap celdisjs eldisjsim2 eldisjsim4 eldisjsim5
      crn wa jca32 cv cec cin wceq wi wral rnqmapeleldisjsim qmapeldisjsim syld
      wne cdm w3a 3adant2r 3adant2l 3expia ralrimivv wdisjALTV wrel elrelsrelim
      c0 dfdisjALTV5a simplbi2com syl eldisjsdisj sylibrd adantr mpd impbii ) A
      DEZAFEZAGZLHEZVEDEZMZMZVCVDVFVGAIAJAKNVIBOZAPZCOZAPZQUNUDZVJVLRZSZCAUEZTB
      VQTZVCVIVPBCVQVQVDVHVJVQEVLVQEMZVPVDVHVSUFVNVKVMRZVOVDVFVSVNVTSVGVJVLAFUA
      UGVDVGVSVTVOSVFVJVLAFUBUHUCUIUJVDVRVCSVHVDVRAUKZVCVDAULZVRWASAUMWAVRWBCBA
      UOUPUQAFURUSUTVAVB $.
  $}

  ${
    $d R t u $.  $d R u x $.
    $( Elementhood in the class of disjoints. ` R e. Disjs ` iff:

       ` R e. Rels ` , and

       every ` x ` belongs to at most one block ` u ` in the quotient-carrier
       ` ( dom R /. R ) ` (element-disjointness at the carrier), and

       every block ` u ` in the quotient-carrier has a unique representative
       ` t e. dom R ` such that ` u = [ t ] R ` .

       Provides the "fully expanded" quantifier characterization of the same
       decomposition as ~ eldisjs6 , but without explicitly mentioning
       ` QMap ` .  This is the "E*/E!"" view that is closest in spirit to
       ~ suc11reg -style injectivity and to the "unique generator per block"
       narrative.  It is also the right contrast-point to older one-line
       criteria like ~ dfdisjs4 (the "u R x" style), because it makes the
       carrier and representation discipline explicit and type-safe.
       (Contributed by Peter Mazsa, 16-Feb-2026.) $)
    eldisjs7 $p |- ( R e. Disjs <-> ( R e. Rels /\
        ( A. x E* u e. ( dom R /. R ) x e. u /\
          A. u e. ( dom R /. R ) E! t e. dom R u = [ t ] R ) ) ) $=
      ( cdisjs wcel crels cqmap crn celdisjs wa cv cdm cqs wrmo wal cec weldisj
      cvv bitri wceq wreu wral eldisjs6 wb rnexg eleldisjseldisj 3syl eldisjeqi
      qmapex rnqmap dfeldisj4 bitrdi qmapeldisjs disjqmap bitrd anbi12d pm5.32i
      wdisjALTV ) DEFDGFZDHZIZJFZVAEFZKZKUTALBLZFBDMZDNZOAPZVFCLDQUACVGUBBVHUCZ
      KZKDUDUTVEVKUTVCVIVDVJUTVCVBRZVIUTVASFVBSFVCVLUEDGUJVASUFVBSUGUHVLVHRVIVB
      VHDUKUIABVHULTUMUTVDVAUSVJDGUNBCDGUOUPUQURT $.
  $}

  $( Alternate definition of the class of disjoints (via quotient-map
     stability). ` Disjs ` is the class of relations ` r ` whose quotient-map
     ` QMap r ` is again disjoint and whose induced quotient-carrier is
     element-disjoint.  This is the definitional "stability-by-decomposition"
     packaging of disjointness: it builds ` Disjs ` from two internal layers
     (i) a carrier-layer constraint and (ii) a map-layer closure constraint.
     This is deliberately different from "u R x" style definitions: it makes
     the carrier of blocks and the uniqueness-of-representatives discipline
     first-class and reusable (via ` QMap ` ) rather than implicit.
     (Contributed by Peter Mazsa, 16-Feb-2026.) $)
  dfdisjs6 $p |- Disjs =
      { r e. Rels | ( ran QMap r e. ElDisjs /\ QMap r e. Disjs ) } $=
    ( cv cqmap crn celdisjs wcel cdisjs wa crels eldisjs6 eqrabi ) ABZCZDEFMGFH
    AGILJK $.

  ${
    $d r t u $.  $d r u x $.
    $( Alternate definition of the class of disjoints (via carrier disjointness
       + unique representatives).  Ideology-free normal form of ~ dfdisjs6 :
       "blocks cover their elements" ( ` E* ` ) and "each block has a unique
       generator" ( ` E! ` ), expressed entirely at the quotient-carrier level.
       Same class as ~ dfdisjs6 , but presented in fully expanded ` E* ` /
       ` E! ` form over the quotient-carrier ` ( dom r /. r ) ` .  Makes
       explicit (a) element-disjointness of the quotient-carrier and (b) unique
       representative existence for each block.  These are exactly the two
       conditions that rule out type-confusions (blocks vs witnesses) and
       ensure canonical decomposition.  This is the form that best supports
       analogy arguments with ~ df-petparts and with successor-style uniqueness
       patterns.  (Contributed by Peter Mazsa, 16-Feb-2026.) $)
    dfdisjs7 $p |- Disjs = { r e. Rels |
        ( A. x E* u e. ( dom r /. r ) x e. u /\
          A. u e. ( dom r /. r ) E! t e. dom r u = [ t ] r ) } $=
      ( cv wcel cdm cqs wrmo wal wceq wreu wral wa cdisjs crels eldisjs7 eqrabi
      cec ) AEBEZFBDEZGZUAHZIAJTCEUASKCUBLBUCMNDOPABCUAQR $.
  $}

  $( Implication of ~ eqvrelqseqdisj2 and ~ n0eldmqseq , see comment of
     ~ fences .  (Contributed by Peter Mazsa, 30-Dec-2024.) $)
  fences3 $p |- ( ( EqvRel R /\ ( dom R /. R ) = A ) ->
                  ( ElDisj A /\ -. (/) e. A ) ) $=
    ( weqvrel cdm cqs wceq wa weldisj c0 wcel eqvrelqseqdisj2 n0eldmqseq adantl
    wn jca ) BCZBDZBEAFZGAHIAJNZAQBKRSPABLMO $.

  $( Implication of ~ eqvreldisj3 , lemma for the Member Partition Equivalence
     Theorem ~ mpet3 .  (Contributed by Peter Mazsa, 27-Oct-2020.)  (Revised by
     Peter Mazsa, 24-Sep-2021.) $)
  eqvrelqseqdisj3 $p |- ( ( EqvRel R /\ ( B /. R ) = A ) ->
                          Disj ( `' _E |` A ) ) $=
    ( weqvrel cqs wceq wa cep ccnv cres wdisjALTV eqvreldisj3 adantr wb disjeqd
    reseq2 adantl mpbid ) CDZBCEZAFZGHIZTJZKZUBAJZKZSUDUABCLMUAUDUFNSUAUCUETAUB
    POQR $.

  $( Lemma for ~ petincnvepres2 .  (Contributed by Peter Mazsa,
     31-Dec-2021.) $)
  eqvrelqseqdisj4 $p |- ( ( EqvRel R /\ ( B /. R ) = A ) ->
                          Disj ( S i^i ( `' _E |` A ) ) ) $=
    ( weqvrel cqs wceq cep ccnv cres wdisjALTV cin eqvrelqseqdisj3 disjimin syl
    wa ) CEBCFAGPHIAJZKDQLKABCMDQNO $.

  $( Lemma for the Partition-Equivalence Theorem ~ pet2 .  (Contributed by
     Peter Mazsa, 15-Jul-2020.)  (Revised by Peter Mazsa, 22-Sep-2021.) $)
  eqvrelqseqdisj5 $p |- ( ( EqvRel R /\ ( B /. R ) = A ) ->
                          Disj ( S |X. ( `' _E |` A ) ) ) $=
    ( weqvrel cqs wceq wa cep ccnv cres wdisjALTV eqvrelqseqdisj3 disjimxrn syl
    cxrn ) CEBCFAGHIJAKZLDQPLABCMDQNO $.

  $( The Main Theorem of Equivalences: every equivalence relation implies
     equivalent comembers.  (Contributed by Peter Mazsa, 26-Sep-2021.) $)
  mainer $p |- ( R ErALTV A -> CoMembEr A ) $=
    ( weqvrel cdm cqs wceq wa wcoeleqvrel cuni ccoels werALTV wcomember weldisj
    eqvrelqseqdisj2 eldisjim syl c0 wcel wn n0eldmqseq adantl wb eldisjn0el jca
    mpbid dferALTV2 dfcomember3 3imtr4i ) BCZBDZBEAFZGZAHZAIAJEAFZGABKALULUMUNU
    LAMZUMAUJBNZAOPULQARSZUNUKUQUIABTUAULUOUQUNUBUPAUCPUEUDABUFAUGUH $.

  $( Partition with general ` R ` (in addition to the member partition cf.
     ~ mpet and ~ mpet2 ) implies equivalent comembers.  (Contributed by Peter
     Mazsa, 23-Sep-2021.)  (Revised by Peter Mazsa, 22-Dec-2024.) $)
  partimcomember $p |- ( R Part A -> CoMembEr A ) $=
    ( wpart ccoss werALTV wcomember partim mainer syl ) ABCABDZEAFABGAJHI $.

  $( Member Partition-Equivalence Theorem.  Together with ~ mpet ~ mpet2 ,
     mostly in its conventional ~ cpet and ~ cpet2 form, this is what we used
     to think of as the partition equivalence theorem (but cf. ~ pet2 with
     general ` R ` ).  (Contributed by Peter Mazsa, 4-May-2018.)  (Revised by
     Peter Mazsa, 26-Sep-2021.) $)
  mpet3 $p |- ( ( ElDisj A /\ -. (/) e. A ) <->
                ( CoElEqvRel A /\ ( U. A /. ~ A ) = A ) ) $=
    ( weldisj c0 wcel wn cep ccnv cres wdisjALTV cdm cqs wceq ccoss wcoeleqvrel
    wa weqvrel cuni ccoels eldisjn0elb eqvrelqseqdisj3 petlem eqvreldmqs 3bitri
    ) ABCADEOFGAHZIUDJUDKALOUDMZPUEJZUEKALOANAQARKALOASAUDAUFUETUAAUBUC $.

  $( The conventional form of the Member Partition-Equivalence Theorem.  In the
     conventional case there is no (general) disjoint and no (general)
     partition concept: mathematicians have called disjoint or partition what
     we call element disjoint or member partition, see also ~ cpet .  Together
     with ~ cpet , ~ mpet ~ mpet2 , this is what we used to think of as the
     partition equivalence theorem (but cf. ~ pet2 with general ` R ` ).
     (Contributed by Peter Mazsa, 30-Dec-2024.) $)
  cpet2 $p |- ( ( ElDisj A /\ -. (/) e. A ) <->
                ( EqvRel ~ A /\ ( U. A /. ~ A ) = A ) ) $=
    ( weldisj c0 wcel wn wa cep ccnv cres wdisjALTV cdm cqs wceq weqvrel ccoels
    ccoss cuni eldisjn0elb eqvrelqseqdisj3 petlem eqvreldmqs2 3bitri ) ABCADEFG
    HAIZJUCKUCLAMFUCPZNUDKZUDLAMFAOZNAQUFLAMFARAUCAUEUDSTAUAUB $.

  $( The conventional form of Member Partition-Equivalence Theorem.  In the
     conventional case there is no (general) disjoint and no (general)
     partition concept: mathematicians have been calling disjoint or partition
     what we call element disjoint or member partition, see also ~ cpet2 .  Cf.
     ~ mpet , ~ mpet2 and ~ mpet3 for unconventional forms of Member
     Partition-Equivalence Theorem.  Cf. ~ pet and ~ pet2 for
     Partition-Equivalence Theorem with general ` R ` .  (Contributed by Peter
     Mazsa, 31-Dec-2024.) $)
  cpet $p |- ( MembPart A <->
               ( EqvRel ~ A /\ ( U. A /. ~ A ) = A ) ) $=
    ( wmembpart weldisj c0 wcel wn wa ccoels weqvrel cuni cqs dfmembpart2 cpet2
    wceq bitri ) ABACDAEFGAHZIAJPKANGALAMO $.

  $( Member Partition-Equivalence Theorem in almost its shortest possible form,
     cf. the 0-ary version ~ mpets .  Member partition and comember equivalence
     relation are the same (or: each element of ` A ` have equivalent comembers
     if and only if ` A ` is a member partition).  Together with ~ mpet2 ,
     ~ mpet3 , and with the conventional ~ cpet and ~ cpet2 , this is what we
     used to think of as the partition equivalence theorem (but cf. ~ pet2 with
     general ` R ` ).  (Contributed by Peter Mazsa, 24-Sep-2021.) $)
  mpet $p |- ( MembPart A <-> CoMembEr A ) $=
    ( weldisj c0 wcel wn wcoeleqvrel cuni ccoels wceq wmembpart wcomember mpet3
    wa cqs dfmembpart2 dfcomember3 3bitr4i ) ABCADEMAFAGAHNAIMAJAKALAOAPQ $.

  $( Member Partition-Equivalence Theorem in a shorter form.  Together with
     ~ mpet ~ mpet3 , mostly in its conventional ~ cpet and ~ cpet2 form, this
     is what we used to think of as the partition equivalence theorem (but cf.
     ~ pet2 with general ` R ` ).  (Contributed by Peter Mazsa,
     24-Sep-2021.) $)
  mpet2 $p |- ( ( `' _E |` A ) Part A <-> ,~ ( `' _E |` A ) ErALTV A ) $=
    ( wmembpart wcomember ccnv cres wpart ccoss werALTV df-membpart df-comember
    cep mpet 3bitr3i ) ABACAKDAEZFANGHALAIAJM $.

  $( Member Partition-Equivalence Theorem with binary relations, cf. ~ mpet2 .
     (Contributed by Peter Mazsa, 24-Sep-2021.) $)
  mpets2 $p |- ( A e. V ->
                 ( ( `' _E |` A ) Parts A <-> ,~ ( `' _E |` A ) Ers A ) ) $=
    ( wcel cep ccnv cres cparts wbr ccoss wb wpart werALTV mpet2 cvv cnvepresex
    cers brpartspart mpdan 1cosscnvepresex brerser bibi12d mpbiri ) ABCZDEAFZAG
    HZUDIZAPHZJAUDKZAUFLZJAMUCUEUHUGUIUCUDNCUEUHJABOAUDBNQRUCUFNCUGUIJABSAUFBNT
    RUAUB $.

  $( Member Partition-Equivalence Theorem in its shortest possible form: it
     shows that member partitions and comember equivalence relations are
     literally the same.  Cf. ~ pet , the Partition-Equivalence Theorem, with
     general ` R ` .  (Contributed by Peter Mazsa, 31-Dec-2024.) $)
  mpets $p |- MembParts = CoMembErs $=
    ( va cep ccnv cv cres cparts wbr ccoss cers cmembparts ccomembers wb mpets2
    cab cvv elv abbii df-membparts df-comembers 3eqtr4i ) BCADZEZUAFGZANUBHUAIG
    ZANJKUCUDAUCUDLAUAOMPQARAST $.

  $( Partition with general ` R ` also imply member partition.  (Contributed by
     Peter Mazsa, 23-Sep-2021.)  (Revised by Peter Mazsa, 22-Dec-2024.) $)
  mainpart $p |- ( R Part A -> MembPart A ) $=
    ( wpart wcomember wmembpart partimcomember mpet sylibr ) ABCADAEABFAGH $.

  $( The Theorem of Fences by Equivalences: all conceivable equivalence
     relations (besides the comember equivalence relation cf. ~ mpet ) generate
     a partition of the members.  (Contributed by Peter Mazsa, 26-Sep-2021.) $)
  fences $p |- ( R ErALTV A -> MembPart A ) $=
    ( werALTV wcomember wmembpart mainer mpet sylibr ) ABCADAEABFAGH $.

  $( The Theorem of Fences by Equivalences: all conceivable equivalence
     relations (besides the comember equivalence relation cf. ~ mpet3 )
     generate a partition of the members, it alo means that
     ` ( R ErALTV A -> ElDisj A ) ` and that
     ` ( R ErALTV A -> -. (/) e. A ) ` .  (Contributed by Peter Mazsa,
     15-Oct-2021.) $)
  fences2 $p |- ( R ErALTV A -> ( ElDisj A /\ -. (/) e. A ) ) $=
    ( werALTV wmembpart weldisj c0 wcel wn wa fences dfmembpart2 sylib ) ABCADA
    EFAGHIABJAKL $.

  $( The Main Theorem of Equivalences: every equivalence relation implies
     equivalent comembers.  (Contributed by Peter Mazsa, 15-Oct-2021.) $)
  mainer2 $p |- ( R ErALTV A -> ( CoElEqvRel A /\ -. (/) e. A ) ) $=
    ( werALTV weldisj c0 wcel wn wa wcoeleqvrel fences2 eldisjim anim1i syl ) A
    BCADZEAFGZHAIZOHABJNPOAKLM $.

  $( Every equivalence relation implies equivalent coelements.  (Contributed by
     Peter Mazsa, 20-Oct-2021.) $)
  mainerim $p |- ( R ErALTV A -> CoElEqvRel A ) $=
    ( werALTV wcoeleqvrel c0 wcel wn mainer2 simpld ) ABCADEAFGABHI $.

  $( A partition-equivalence theorem with intersection and general ` R ` .
     (Contributed by Peter Mazsa, 31-Dec-2021.) $)
  petincnvepres2 $p |- ( ( Disj ( R i^i ( `' _E |` A ) ) /\
                           ( dom ( R i^i ( `' _E |` A ) ) /.
                             ( R i^i ( `' _E |` A ) ) ) = A ) <->
                         ( EqvRel ,~ ( R i^i ( `' _E |` A ) ) /\
                           ( dom ,~ ( R i^i ( `' _E |` A ) ) /.
                             ,~ ( R i^i ( `' _E |` A ) ) ) = A ) ) $=
    ( cep ccnv cres cin ccoss cdm eqvrelqseqdisj4 petlem ) ABCDAEFZAKGZHLBIJ $.

  $( The shortest form of a partition-equivalence theorem with intersection and
     general ` R ` .  Cf. ~ br1cossincnvepres .  Cf. ~ pet .  (Contributed by
     Peter Mazsa, 23-Sep-2021.) $)
  petincnvepres $p |- ( ( R i^i ( `' _E |` A ) ) Part A <->
                        ,~ ( R i^i ( `' _E |` A ) ) ErALTV A ) $=
    ( cep ccnv cres cin wdisjALTV cdm cqs wa ccoss weqvrel wpart petincnvepres2
    wceq werALTV dfpart2 dferALTV2 3bitr4i ) BCDAEFZGTHTIAOJTKZLUAHUAIAOJATMAUA
    PABNATQAUARS $.

  $( Partition-Equivalence Theorem, with general ` R ` .  This theorem
     (together with ~ pet and ~ pets ) is the main result of my investigation
     into set theory, see the comment of ~ pet .  (Contributed by Peter Mazsa,
     24-May-2021.)  (Revised by Peter Mazsa, 23-Sep-2021.) $)
  pet2 $p |- ( ( Disj ( R |X. ( `' _E |` A ) ) /\
                 ( dom ( R |X. ( `' _E |` A ) ) /.
                   ( R |X. ( `' _E |` A ) ) ) = A ) <->
               ( EqvRel ,~ ( R |X. ( `' _E |` A ) ) /\
                 ( dom ,~ ( R |X. ( `' _E |` A ) ) /.
                   ,~ ( R |X. ( `' _E |` A ) ) ) = A ) ) $=
    ( cep ccnv cres cxrn ccoss cdm eqvrelqseqdisj5 petlem ) ABCDAEFZAKGZHLBIJ
    $.

  $( Partition-Equivalence Theorem with general ` R ` while preserving the
     restricted converse epsilon relation of ~ mpet2 (as opposed to
     ~ petincnvepres ).  A class is a partition by a range Cartesian product
     with general ` R ` and the restricted converse element class if and only
     if the cosets by the range Cartesian product are in an equivalence
     relation on it.  Cf. ~ br1cossxrncnvepres .

     This theorem (together with ~ pets and ~ pet2 ) is the main result of my
     investigation into set theory.  It is no more general than the
     conventional Member Partition-Equivalence Theorem ~ mpet , ~ mpet2 and
     ~ mpet3 (because you cannot set ` R ` in this theorem in such a way that
     you get ~ mpet2 ), i.e., it is not the hypothetical General
     Partition-Equivalence Theorem gpet ` |- ( R Part A <-> ,~ R ErALTV A ) ` ,
     but this one has a general part that ~ mpet2 lacks: ` R ` , which is
     sufficient for my future application of set theory, for my purpose outside
     of set theory.  (Contributed by Peter Mazsa, 23-Sep-2021.) $)
  pet $p |- ( ( R |X. ( `' _E |` A ) ) Part A <->
              ,~ ( R |X. ( `' _E |` A ) ) ErALTV A ) $=
    ( cep ccnv cres cxrn wdisjALTV cdm wceq wa ccoss weqvrel wpart werALTV pet2
    cqs dfpart2 dferALTV2 3bitr4i ) BCDAEFZGTHTPAIJTKZLUAHUAPAIJATMAUANABOATQAU
    ARS $.

  $( Partition-Equivalence Theorem with general ` R ` , with binary relations.
     This theorem (together with ~ pet and ~ pet2 ) is the main result of my
     investigation into set theory, cf. the comment of ~ pet .  (Contributed by
     Peter Mazsa, 23-Sep-2021.) $)
  pets $p |- ( ( A e. V /\ R e. W ) ->
               ( ( R |X. ( `' _E |` A ) ) Parts A <->
                 ,~ ( R |X. ( `' _E |` A ) ) Ers A ) ) $=
    ( wcel wa cep ccnv cres cxrn cparts wbr ccoss cers wb wpart werALTV pet cvv
    syldan xrncnvepresex brpartspart 1cossxrncnvepresex brerser bibi12d mpbiri
    ) ACEZBDEZFZBGHAIJZAKLZUJMZANLZOAUJPZAULQZOABRUIUKUNUMUOUGUHUJSEUKUNOABCDUA
    AUJCSUBTUGUHULSEUMUOOABCDUCAULCSUDTUEUF $.

  ${
    $d A b c u v $.  $d R b c u v $.
    $( If the ~ pet span ` ( R |X. ( ``' _E |`` A ) ) ` partitions ` A ` , then
       every block ` u e. A ` is of the form ` [ v ] ` for some ` v ` that not
       only lies in the domain but also has at least one internal element ` c `
       and at least one ` R ` -target ` b ` (cf. also the comments of ~ qseq ).
       It makes explicit that ~ pet gives active representatives for each
       block, without ever forcing ` v = u ` .  (Contributed by Peter Mazsa,
       23-Nov-2025.) $)
    dmqsblocks $p |- ( ( dom ( R |X. ( `' _E |` A ) ) /.
                          ( R |X. ( `' _E |` A ) ) ) =
                        A ->
        A. u e. A E. v e. dom ( R |X. ( `' _E |` A ) ) E. b E. c
         ( u = [ v ] ( R |X. ( `' _E |` A ) ) /\ c e. v /\ v R b ) ) $=
      ( cep ccnv cres wceq cv wrex wral wcel w3a wex wb sylbi wa syl cxrn eqab2
      cdm cqs cec wbr wal qseq rexanid cvv eldmxrncnvepres2 elv 3simpc exdistrv
      excom bitr3i anim1ci 3anass 2exbii 19.42vv sylbbr reximi sylbir ralimi
      sylib ) DGHCIUAZUCZVFUDCJZBKZAKZVFUEJZAVGLZBCMZVKFKVJNZVJEKDUFZOZFPEPZAVG
      LZBCMVHVICNVLQBUGVMABCVGVFUHVLBCUBRVLVRBCVLVJVGNZVKSZAVGLVRVKAVGUIVTVQAVG
      VTVKVNVOSZFPEPZSZVQVSWBVKVSVNFPZVOEPZSZWBVSVJCNZWDWEOZWFVSWHQAFECVJDUJUKU
      LWGWDWEUMRWFWAEPFPWBVNVOFEUNWAFEUOUPVEUQVQVKWASZFPEPWCVPWIEFVKVNVOURUSVKW
      AEFUTVATVBVCVDT $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Type-safe Partition-Equivalence: PetParts, PetErs, Pet2Parts, Pet2Ers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d n r $.
    $( Define the class of partition-side general partition-equivalence spans.

       ` <. r , n >. e. PetParts ` means:

       (1) ` r ` is a set-relation ( ` r e. Rels ` ), and

       (2) ` n ` is a membership block-carrier ( ` n e. MembParts ` ), and

       (3) the block-lift span ` ( r |X. ( ``' _E |`` n ) ) ` is a generalized
       partition on its natural quotient-carrier ` n ` (i.e.
       ` ( r |X. ( ``' _E |`` n ) ) Parts n ` ).

       This is the horizontal feasibility base object on the partition side,
       expressed in the type-safe ` Parts ` language.

       The explicit typing ` ( r e. Rels /\ n e. MembParts ) ` is included at
       the definition level so later modular refinements can treat typedness as
       a first-class component (e.g. intersecting a typedness module with
       disjointness and equilibrium modules) without repeatedly restating it.
       In particular, it lets decompositions such as ~ dfpetparts2 be written
       as clean intersections whose first conjunct is exactly the typedness
       module ` ( Rels X. MembParts ) ` .  (Contributed by Peter Mazsa,
       19-Feb-2026.)  (Revised by Peter Mazsa, 25-Feb-2026.) $)
    df-petparts $a |- PetParts = { <. r , n >. |
  ( ( r e. Rels /\ n e. MembParts ) /\ ( r |X. ( `' _E |` n ) ) Parts n ) } $.
  $}

  ${
    $d n r $.
    $( Define the class of equivalence-side general partition-equivalence
       spans.

       ` <. r , n >. e. PetErs ` means:

       (1) ` r ` is a set-relation ( ` r e. Rels ` ), and

       (2) ` n ` is a carrier recognized on the equivalence side of membership
       ( ` n e. CoMembErs ` ), and

       (3) the coset relation of the lifted span,
       ` ,~ ( r |X. ( ``' _E |`` n ) ) ` , is an equivalence relation on its
       natural quotient with carrier ` n ` (i.e.
       ` ,~ ( r |X. ( ``' _E |`` n ) ) Ers n ` ).

       This packages the equivalence-view of the same lifted construction that
       underlies ` PetParts ` .  It is designed to be parallel to ` PetParts `
       so later proofs can freely choose the partition side ( ` Parts ` ) or
       the equivalence side ( ` Ers ` ) without rebuilding the bridge each
       time; the identification is provided by ~ petseq (using ~ typesafepets
       and ~ mpets ).  The explicit typing ` ( r e. Rels /\ n e. CoMembErs ) `
       is included for the same reason as in ~ df-petparts : to make typedness
       a reusable module.  (Contributed by Peter Mazsa, 19-Feb-2026.)  (Revised
       by Peter Mazsa, 25-Feb-2026.) $)
    df-peters $a |- PetErs = { <. r , n >. | ( ( r e. Rels /\ n e. CoMembErs )
                               /\ ,~ ( r |X. ( `' _E |` n ) ) Ers n ) } $.
  $}

  $( Define the class of grade- and blocklift-stable partition-side general
     partition-equivalence spans.  It consists of those
     ` <. r , n >. e. PetParts ` such that ` <. r , n >. ` remains in
     ` PetParts ` after shifting one grade along ` SucMap ` (via
     ` ShiftStable ` ).  Concretely: ` <. r , n >. e. PetParts ` and there
     exists a predecessor ` m ` with ` suc m = n ` such that
     ` <. r , m >. e. PetParts ` (encoded by ` SucMap o. PetParts ` inside
     ` ShiftStable ` ).  I.e., it introduces the external (tower/grade)
     stability axis.  This is the "4th level" for ~ pet (see ~ dfpet2parts2 ):
     beyond (i) carrier membership partition, (ii) disjointness, and (iii)
     semantic equilibrium, we require (iv) stability under a canonical grade
     shift. ` PetParts ` already enforces disjointness and the quotient-carrier
     equation for the lifted span (hence semantic equilibrium via
     ~ dfpetparts2 ). ` Pet2Parts ` adds the external grade (tower) stability
     axis via ~ df-shiftstable with ` SucMap ` .  This (iv) is why we need
     explicit second-level ` Pet2Parts ` , while ` Disjs ` typically does not:
     ` Disjs ` already packages its own internal two-step consistency (carrier
     + map) by ~ dfdisjs6 / ~ dfdisjs7 , whereas ~ pet has an additional grade
     axis that must be imposed separately.  (Contributed by Peter Mazsa,
     19-Feb-2026.) $)
  df-pet2parts $a |- Pet2Parts = ( SucMap ShiftStable PetParts ) $.

  $( Define the class of grade- and blocklift-stable equivalence-side general
     partition-equivalence spans.  The equivalence-side analogue of
     ` Pet2Parts ` : stability of ` PetErs ` under one-step grade shift along
     ` SucMap ` .  Ensures that the equivalence-side formulation supports the
     same tower/grade infrastructure as the partition-side formulation.
     ` SucMap ShiftStable ` is the grade axis and does not change the
     equivalence-vs-partition viewpoint (reinforced by ~ pets2eq ).
     (Contributed by Peter Mazsa, 19-Feb-2026.) $)
  df-pet2ers $a |- Pet2Ers = ( SucMap ShiftStable PetErs ) $.

  ${
    $d n r $.
    $( Alternate definition of ` PetParts ` as typedness + disjoint-span +
       block-lift equilibrium.

       This theorem is the key modularization step.  It decomposes ` PetParts `
       into the intersection of three orthogonal modules:

       (T) typedness: ` <. r , n >. e. ( Rels X. MembParts ) ` ,

       (D) disjoint-span: ` ( r |X. ( ``' _E |`` n ) ) e. Disjs ` ,

       (E) semantic equilibrium: ` <. r , n >. e. BlockLiftFix ` , i.e. the
       carrier ` n ` is a fixpoint of the induced block-generation operator.

       Conceptually, (D) provides the disjointness/quotient discipline for the
       lifted span, while (E) prevents hidden carrier drift (refinement or
       coarsening of what counts as a block) by enforcing the fixpoint
       equation.  The point of this theorem is that these constraints can be
       imposed and reused independently by later constructions, while their
       intersection recovers the intended ` Parts `-based notion.

       This mirrors the internal packaging of ` Disjs ` (see ~ dfdisjs6 /
       ~ dfdisjs7 ): for disjoint relations, the "map layer + carrier layer"
       decomposition is internal via ` QMap ` and ` ElDisjs ` ; for
       ` PetParts ` , the carrier ` n ` is an external parameter, so the
       additional carrier stability must be factored explicitly as
       ` BlockLiftFix ` .  (Contributed by Peter Mazsa, 20-Feb-2026.)  (Revised
       by Peter Mazsa, 25-Feb-2026.) $)
    dfpetparts2 $p |- PetParts = ( ( ( Rels X. MembParts ) i^i
    { <. r , n >. | ( r |X. ( `' _E |` n ) ) e. Disjs } ) i^i BlockLiftFix ) $=
      ( crels cmembparts cxp cv cep ccnv cres cxrn copab cin wcel cblockliftfix
      cpetparts wa inopab ineq2i cvv 3eqtr4ri cparts wbr cdisjs df-blockliftfix
      cdm cqs wceq xrncnvepresex el2v brparts2 el2v1 ax-mp opabbii df-xp ineq1i
      wb df-petparts inass 3eqtr4i ) CDEZBFZGHAFZIJZVBUAUBZBAKZLZUTVCUCMZBAKZNL
      ZLOUTVHLNLVEVIUTVHVCUEVCUFVBUGZBAKZLVGVJPZBAKVIVEVGVJBAQNVKVHBAUDRVDVLBAV
      CSMZVDVLUPZVMABVBVASSUHUIVMVNAVBVCSSUJUKULUMTRVACMVBDMPZBAKZVELVOVDPBAKVF
      OVOVDBAQUTVPVEBACDUNUOABUQTUTVHNURUS $.
  $}

  ${
    $d n r $.
    $( Grade stability applied to the decomposed ` PetParts ` modules.

       ` Pet2Parts ` is obtained by applying the grade-stability operator
       ` SucMap ShiftStable ` (see ~ df-shiftstable ) to the modular
       intersection from ~ dfpetparts2 .  This makes the two orthogonal
       stability axes explicit:

       (E) semantic stability / equilibrium: ` BlockLiftFix ` ,

       (G) grade stability: ` SucMap ShiftStable ` ,

       assembled on top of typedness and disjoint-span base modules.

       This is the principled "extra level" that does not arise for ` Disjs ` :
       disjoint relations already bundle their internal map/carrier consistency
       via ` QMap ` and ` ElDisjs ` (see ~ dfdisjs6 / ~ dfdisjs7 ), while the
       present construction has an additional external grading axis imposed by
       the canonical successor map ` SucMap ` .  (Contributed by Peter Mazsa,
       20-Feb-2026.)  (Revised by Peter Mazsa, 25-Feb-2026.) $)
    dfpet2parts2 $p |- Pet2Parts =
        ( SucMap ShiftStable
          ( ( ( Rels X. MembParts ) i^i
              { <. r , n >. | ( r |X. ( `' _E |` n ) ) e. Disjs } ) i^i
            BlockLiftFix ) ) $=
      ( cpet2parts csucmap cpetparts cshiftstable crels cmembparts cxp cep ccnv
      cv cres cxrn cdisjs wcel copab cin cblockliftfix wceq df-pet2parts ax-mp
      dfpetparts2 shiftstableeq2 eqtri ) CDEFZDGHIBLJKALMNOPBAQRSRZFZUAEUGTUFUH
      TABUCDEUGUDUBUE $.
  $}

  ${
    $d n r $.
    $( Alternate definition of ` PetErs ` in fully modular form.

       This expands the ` Ers n ` predicate into:

       (i) a typedness module ` ( Rels X. CoMembErs ) ` ,

       (ii) an equivalence module for the coset relation
       ` ,~ ( r |X. ( ``' _E |`` n ) ) e. EqvRels ` ,

       (iii) the corresponding quotient-carrier (domain quotient) equation
       ` dom ,~ ( ... ) /. ,~ ( ... ) = n ` .

       This is the equivalence-side counterpart of the modular decomposition
       ~ dfpetparts2 on the partition side.  (Contributed by Peter Mazsa,
       25-Feb-2026.) $)
    dfpeters2 $p |- PetErs = ( ( ( Rels X. CoMembErs ) i^i
        { <. r , n >. | ,~ ( r |X. ( `' _E |` n ) ) e. EqvRels } ) i^i
        { <. r , n >. |
          ( dom ,~ ( r |X. ( `' _E |` n ) ) /. ,~ ( r |X. ( `' _E |` n ) ) ) =
            n } ) $=
      ( crels ccomembers cxp cv cep ccnv cres cxrn wbr copab wcel cpeters wa wb
      cin cvv elv inopab ccoss cers ceqvrels cdm wceq cdmqss 1cossxrncnvepresex
      cqs brers el2v brdmqss mpan2 anbi2i bitri opabbii eqtr4i ineq2i df-peters
      df-xp ineq1i 3eqtr4ri inass 3eqtr4i ) CDEZBFZGHAFZIJUAZVFUBKZBALZQZVDVGUC
      MZBALZVGUDVGUHVFUEZBALZQZQNVDVLQVNQVIVOVDVIVKVMOZBALVOVHVPBAVHVKVGVFUFKZO
      ZVPVHVRPAVFVGRUISVQVMVKVQVMPZAVFRMVGRMZVSVTABVFVERRUGUJVFVGRRUKULSUMUNUOV
      KVMBATUPUQVECMVFDMOZBALZVIQWAVHOBALVJNWAVHBATVDWBVIBACDUSUTABURVAVDVLVNVB
      VC $.
  $}

  $( Type-safe ~ pets scheme.  On a membership block-carrier
     ` A e. MembParts ` , the lifted span ` ( R |X. ( ``' _E |`` A ) ) ` yields
     a generalized partition of ` A ` iff its coset relation yields an
     equivalence relation on the same carrier ` A ` .  This is the type-safe
     replacement for the earlier broad ~ pets : it explicitly restricts to
     carriers where ` A ` is already known to be a block-family (by
     ` MembParts ` ).  That removes the standard type-safety objection ("are
     you equating a quotient-carrier of blocks with raw witnesses?") by
     construction.  It is the key bridge used to identify the partition-side
     and equivalence-side pet classes ( ~ petseq ), in complete parallel with
     the membership bridge ~ mpets .  This theorem is intentionally not the
     definition of ` PetParts ` ; it is the bridge used by ~ petseq after
     typedness is enforced by the "Pet*" definitions.  (Contributed by Peter
     Mazsa, 19-Feb-2026.) $)
  typesafepets $p |- ( ( A e. MembParts /\ R e. V ) ->
                       ( ( R |X. ( `' _E |` A ) ) Parts A <->
                         ,~ ( R |X. ( `' _E |` A ) ) Ers A ) ) $=
    ( cmembparts pets ) ABDCE $.

  ${
    $d n r $.
    $( Generalized partition-equivalence identification.

       The partition-side scheme ` PetParts ` and the equivalence-side scheme
       ` PetErs ` define the same class of spans (pairs ` <. r , n >. ` ).

       This plays the same organizational role for lifted spans that ~ mpets
       plays for carriers: ~ mpets identifies ` MembParts ` with ` CoMembErs `
       at the membership-carrier level, while ~ petseq identifies the
       corresponding span-level predicates built from ` Parts ` and ` Ers ` .

       Unlike the earlier broad ~ pets , the bridge used here is the type-safe
       span theorem ~ typesafepets , which restricts to membership
       block-carriers.  Since typedness ( ` r e. Rels ` and the appropriate
       carrier condition) is now built directly into ` PetParts ` and
       ` PetErs ` , this theorem can be used downstream without repeatedly
       re-establishing basic typing premises.  (Contributed by Peter Mazsa,
       19-Feb-2026.) $)
    petseq $p |- PetParts = PetErs $=
      ( vr vn cv crels wcel cmembparts cep ccnv cres cxrn cparts wbr ccomembers
      wa copab ccoss cers cpetparts cpeters wb typesafepets elvd adantl pm5.32i
      cvv mpets eleq2i anbi2i bianbi opabbii df-petparts df-peters 3eqtr4i ) AC
      ZDEZBCZFEZNZUNGHUPIJZUPKLZNZABOUOUPMEZNZUSPUPQLZNZABORSVAVEABVAURVDVCURUT
      VDUQUTVDTZUOUQVFAUPUNUEUAUBUCUDUQVBUOFMUPUFUGUHUIUJBAUKBAULUM $.
  $}

  $( Grade-stable generalized partition-equivalence identification.  After
     applying the same grade-stability operator ( ` SucMap ShiftStable ` ) to
     both sides, the grade-stable pet classes still coincide.  Confirms that
     the grade/tower infrastructure is orthogonal to the
     partition-vs-equivalence viewpoint: stability is preserved under the
     ` PetParts = PetErs ` identification.  This is the level at which we can
     freely work on whichever side is more convenient ( ` Parts ` for block
     discipline, ` Ers ` for equivalence reasoning), without changing the
     stable notion of "pet".  (Contributed by Peter Mazsa, 19-Feb-2026.) $)
  pets2eq $p |- Pet2Parts = Pet2Ers $=
    ( csucmap cpetparts cshiftstable cpeters cpet2parts cpet2ers shiftstableeq2
    wceq petseq ax-mp df-pet2parts df-pet2ers 3eqtr4i ) ABCZADCZEFBDHNOHIABDGJK
    LM $.

$( (End of Peter Mazsa's mathbox.) $)
