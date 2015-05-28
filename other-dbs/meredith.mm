$( -*-text-*-
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Pre-logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)
  $( Declare the primitive constant symbols for propositional calculus. $)
  $c ( $.  $( Left parenthesis $)
  $c ) $.  $( Right parenthesis $)
  $c -> $. $( Right arrow (read:  "implies") $)
  $c -. $. $( Right handle (read:  "not") $)
  $c wff $. $( Well-formed formula symbol (read:  "the following symbol
               sequence is a wff") $)
  $c |- $. $( Turnstile (read:  "the following symbol sequence is provable" or
              'a proof exists for") $)

  $( wff variable sequence:  ph ps ch th ta et ze si rh mu la ka $)
  $( Introduce some variable names we will use to represent well-formed
     formulas (wff's). $)
  $v ph $.  $( Greek phi $)
  $v ps $.  $( Greek psi $)
  $v ch $.  $( Greek chi $)
  $v th $.  $( Greek theta $)
  $v ta $.  $( Greek tau $)
  $v et $.  $( Greek eta $)
  $v ze $.  $( Greek zeta $)
  $v si $.  $( Greek sigma $)
  $v rh $.  $( Greek rho $)
  $v mu $.  $( Greek mu $)
  $v la $.  $( Greek lambda $)
  $v ka $.  $( Greek kappa $)

  $( Specify some variables that we will use to represent wff's.
     The fact that a variable represents a wff is relevant only to a theorem
     referring to that variable, so we may use $f hypotheses.  The symbol
     ` wff ` specifies that the variable that follows it represents a wff. $)
  $( Let variable ` ph ` be a wff. $)
  wph $f wff ph $.
  $( Let variable ` ps ` be a wff. $)
  wps $f wff ps $.
  $( Let variable ` ch ` be a wff. $)
  wch $f wff ch $.
  $( Let variable ` th ` be a wff. $)
  wth $f wff th $.
  $( Let variable ` ta ` be a wff. $)
  wta $f wff ta $.
  $( Let variable ` et ` be a wff. $)
  wet $f wff et $.
  $( Let variable ` ze ` be a wff. $)
  wze $f wff ze $.
  $( Let variable ` si ` be a wff. $)
  wsi $f wff si $.
  $( Let variable ` rh ` be a wff. $)
  wrh $f wff rh $.
  $( Let variable ` mu ` be a wff. $)
  wmu $f wff mu $.
  $( Let variable ` la ` be a wff. $)
  wla $f wff la $.
  $( Let variable ` ka ` be a wff. $)
  wka $f wff ka $.


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Propositional calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Recursively define primitive wffs for propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( If ` ph ` is a wff, so is ` -. ph ` or "not ` ph ` ."  Part of the
     recursive definition of a wff (well-formed formula).  In classical logic
     (which is our logic), a wff is interpreted as either true or false.
     So if ` ph ` is true, then ` -. ph ` is false; if ` ph ` is false, then
     ` -. ph ` is true.  Traditionally, Greek letters are used to represent
     wffs, and we follow this convention.  In propositional calculus, we define
     only wffs built up from other wffs, i.e. there is no starting or "atomic"
     wff.  Later, in predicate calculus, we will extend the basic wff
     definition by including atomic wffs ( ~ weq and ~ wel ). $)
  wn $a wff -. ph $.

  $( If ` ph ` and ` ps ` are wff's, so is ` ( ph -> ps ) ` or " ` ph ` implies
     ` ps ` ."  Part of the recursive definition of a wff.  The resulting wff
     is (interpreted as) false when ` ph ` is true and ` ps ` is false; it is
     true otherwise.  (Think of the truth table for an OR gate with input
     ` ph ` connected through an inverter.)  The left-hand wff is called the
     antecedent, and the right-hand wff is called the consequent.  In the case
     of ` ( ph -> ( ps -> ch ) ) ` , the middle ` ps ` may be informally called
     either an antecedent or part of the consequent depending on context. $)
  wi $a wff ( ph -> ps ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The axioms of propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ax-meredith $a |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) ->
     ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $.

  ${
    $( Minor premise for modus ponens. $)
    min $e |- ph $.
    $( Major premise for modus ponens. $)
    maj $e |- ( ph -> ps ) $.
    $( Rule of Modus Ponens.  The postulated inference rule of propositional
       calculus.  See e.g. Rule 1 of [Hamilton] p. 73.  The rule says, "if
       ` ph ` is true, and ` ph ` implies ` ps ` , then ` ps ` must also be
       true."  This rule is sometimes called "detachment," since it detaches
       the minor premise from the major premise.

       Note:  In some web page displays such as the Statement List, the symbols
       "&" and "=>" informally indicate the relationship between the hypotheses
       and the assertion (conclusion), abbreviating the English words "and" and
       "implies."  They are not part of the formal language. $)
    ax-mp $a |- ps $.
  $}


  ax1 $p |- ( ph -> ( ps -> ph ) ) $=
    ( wch wi wn ax-meredith ax-mp ) CCDZCEZIDDCDCDHHDDZABADZDZCCCCCFAADZKDZLDZJ
    LDZKCDZAEZRDZDZADMDZOARDSEZRDDZSDTDZUASRQEDZEUBEDZDUEDADUCDUDRRUEUBAFSUFAQU
    CFGARSATFGKCAAMFGLRJEDZEBEDZDUGDADNDOPDAKUGBAFLUHAJNFGGG $.
    $( [?] $) $( [13-Jan-2011] $)

  id $p |- ( ph -> ph ) $=
    ( wps wi wn ax-meredith ax-mp ) BBCZBDZHCCBCBCGGCCZAACZBBBBBEZIIJCZKJJCZLCZ
    ILCZJBCZADZIDZCZCZACJCZNAQCSDZQCCZSCTCZUASQPDCZDUBDCZCUECACUCCUDQRUEUBAESUF
    APUCEFAQSATEFJBAIJEFLBCZJDZRCZCZJCMCZNOCJUHCUIDZUHCCZUICUJCZUKUIUHUGDCZDULD
    CZCUOCJCUMCUNUHRUOULJEUIUPJUGUMEFJUHUIJUJEFLBJIMEFFFF $.
    $( [?] $) $( [13-Jan-2011] $)

  $( D D a D a D a D D a D a D a a D a D a D a a D a D a D D a D a D a a D a D a D a a $)
  luk-3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wch wn wi ax-meredith ax-mp ) BDZADZEZBEZIBEZEZALEZBCEZIDZPEZEZIEJEZMICEC
    DZHDEECEZREZSQQEZREZUBQCEZPDZODZEZEZPEQEZUDPUFEUHDZUFEEZUHEUIEZUJUHUFUEDEZD
    UKDEZEUNEPEULEUMUFUGUNUKPFUHUOPUEULFGPUFUHPUIFGQCPOQFGRCEZQDZUADZEZEZQEUCEZ
    UDUBEQUQEUSDZUQEEZUSEUTEZVAUSUQUPDEZDVBDEZEVEEQEVCEVDUQURVEVBQFUSVFQUPVCFGQ
    UQUSQUTFGRCQUAUCFGGICCHRFGBCIIJFGLCEZJEZBEKEZMNEOJDZVJEZEZJEVHEZVIJCETVGDEE
    CEZVLEZVMVKVKEZVLEZVOVKCEZVJDZUGEZEZVJEVKEZVQVJVSEVTDZVSEEZVTEWAEZWBVTVSVRD
    EZDWCDEZEWFEVJEWDEWEVSUGWFWCVJFVTWGVJVRWDFGVJVSVTVJWAFGVKCVJOVKFGVLCEZVKDZV
    NDZEZEZVKEVPEZVQVOEVKWIEWKDZWIEEZWKEWLEZWMWKWIWHDEZDWNDEZEWQEVKEWOEWPWIWJWQ
    WNVKFWKWRVKWHWOFGVKWIWKVKWLFGVLCVKVNVPFGGJCCVGVLFGBCJJVHFGLCBAKFGG $.
    $( [?] $) $( [10-May-2012] $)
