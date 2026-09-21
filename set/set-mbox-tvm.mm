$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Thomas van Maaren
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  ${
    $d ch x w $.  $d ta x $.  $d x y z $.  $d A w x $.  $d ph w y z $.
    findcard4.1 $e |- ( x = y -> ( ph <-> ch ) ) $.
    findcard4.2 $e |- ( x = A -> ( ph <-> ta ) ) $.
    findcard4.3 $e |- ( y e. Fin -> ( A. x ( ( # ` x ) < ( # ` y ) -> ph ) ->
      ch ) ) $.
    $( Schema for strong induction on the cardinality of a finite set.  The
       inductive hypothesis is that the result is true on any set with less
       elements.  The result is then proven to be true for all finite sets.
       (Contributed by Thomas van Maaren, 14-Aug-2026.) $)
    findcard4 $p |- ( A e. Fin -> ta ) $=
      ( vw cfn wcel wceq wi wal ccrd cfv wa wb cvv vz com ficardom nnfi syl weq
      cv fveq2 adantl simpl eqeq12d imbi12d cbvaldvaw eqeq2 imbi1d albidv eleq1
      wpss cen wbr vex cardid enfi ax-mp bitr3di biimpd psseq2 bicomd sp imim1i
      axi5r ax-5 eqcom pm2.04 biimtrid alimi 3syl biimtrdi alimdv ax-11 a1i wnf
      nfvd alrimiv fvexd w3a ceqsalt syl3anc 3syld chash clt cn0 cxnn0 hashxnn0
      psseq1 cle elv hashcl hashxrcl xrltle mp2an xnn0lenn0nn0 mp3an3an hashclb
      sylibr csdm hashsdom cardsdom el2v bitr4di expimpd mpcom ex cardon onordi
      cxr word ordelpss imbitrdi imim1d syld imp syl2and com12 findcard3 ax-gen
      id mpbid ) FKLZDUGZFMZANZDOZCYIFPQZKLZYJPQZYNMZANZDOZYMYIYNUBLYOFUCYNUDUE
      YPJUGZMZANZDOZEUGZPQZUAUGZMZBNZEOZYSJUAYNJUAUFZUUBUUHDEUUJDEUFZRZUUAUUGAB
      UULYPUUEYTUUFUUKYPUUEMUUJYJUUDPUHUIUUJUUKUJUKUUKABSUUJGUIULUMYTYNMZUUBYRD
      UUMUUAYQAYTYNYPUNUOUPUUFKLZYTUUFURZUUCNZJOZUUIUUNUUQRZUUHEUUGUURBUUGUUNUU
      DKLZUUQYPUUEURZANZDOZBUUGUUNUUSUUGUUEKLZUUNUUSUUEUUFKUQUUEUUDUSUTUVCUUSSU
      UDEVAVBUUEUUDVCVDVEVFUUGUUQYTYPMZYTUUEURZANZNZDOZJOZUVGJOZDOZUVBUUGUUPUVH
      JUUGUUPUVEUUCNZUVHUUGUUOUVEUUCUUGUVEUUOUUEUUFYTVGVHUOUVLUVEDOZUUCNUVMUUBN
      ZDOUVHUVMUVEUUCUVEDVIVJUVEUUBDVKUVNUVGDUVNUVEUUBNZUVGUVEUVMUUBUVEDVLVJUVD
      UUAUVOUVFYTYPVMUVEUUAAVNVOUEVPVQVRVSUVIUVKNUUGUVGJDVTWAUUGUVJUVADUUGUVAJW
      BZUVDUVFUVASNZJOZYPTLZUVJUVANUUGUVAJWCUUGUVQJUVQUUGUVDUVEUUTAYTYPUUEWOUOW
      AWDUUGYJPWEUVPUVRUVSWFUVJUVAUVFUVAJYPTWGVFWHVSWIUUSUVBRBNUUGUUSUVBBUUSUVB
      YJWJQZUUDWJQZWKUTZANZDOBUUSUVAUWCDUUSUWBUUTAUUSUWBYPUUELZUUTUUSUWBUWDYJKL
      ZUUSUWBRZUWDUWFUVTWLLZUWEUVTWMLZUUSUWAWLLUWBUVTUWAWPUTZUWGUWHDYJTWNWQUUDW
      RUVTXPLZUWAXPLZUWBUWINUWJDYJTWSWQUWKEUUDTWSWQUVTUWAWTXAUVTUWAXBXCUWEUWGSD
      YJTXDWQXEUWEUUSUWBUWDUWEUUSRZUWBUWDUWLUWBYJUUDXFUTZUWDYJUUDXGUWDUWMSDEYJU
      UDTTXHXIXJVFXKXLXMYPXQUUEXQUWDUUTSYPYJXNXOUUEUUDXNXOYPUUEXRXAXSXTVSIYAYBW
      AYCYDWDXMYEYRYLDYKYQAYJFPUHVJVPVQYICDWBYKACSNZDOZYIYMCSYICDWCUWOYIUWNDHYF
      WAYIYGACDFKWGWHYH $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The language of Propositional Calculus.
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Sentences of propositional calculus are encoded as sequences of nonnegative
  integers. Variables are encoded as ` ( propvar `` n ) ` where ` n ` is a
  natural number. The negation of a sentence of propositional calculus ` x ` is
  encoded as ` ( prop-. `` x ) ` . Two sentences of propositional calculus
  ` x ` and ` y ` can be combined using the implication ` prop-> ` . To avoid
  the necessity of brackets, this is done in an RPN-format. We can thus encode
  the sentence " ` x ` implies ` y ` " as ` ( x prop-> y ) ` .

$)

  $c propvar $.
  $c prop-. $.
  $c prop-> $.
  $( A variable in a sentence of propositional calculus. $)
  cpropvar $a class propvar $.
  $( The negation of a sentence of propositional calculus. $)
  cpropneg $a class prop-. $.
  $( The implication between two sentences of propositional calculus. $)
  cpropimp $a class prop-> $.

  $( Variables in sentences of propositional calculus are encoded by appending
     a zero after the number of the variable.  (Contributed by Thomas van
     Maaren, 21-Aug-2026.) $)
  df-propvar $a |- propvar = ( n e. NN |-> ( <" n "> ++ <" 0 "> ) ) $.

  $( The negation of a sentence of propositional calculus is encoded by
     appending a one after the sentence.  (Contributed by Thomas van Maaren,
     21-Aug-2026.) $)
  df-propneg $a |- prop-. = ( x e. _V |-> ( x ++ <" 1 "> ) ) $.

  ${
    $d x y $.
    $( The implication between two sentences of propositional calculus is
       encoded by concatenating the two sentences and appending a two at the
       end.  (Contributed by Thomas van Maaren, 21-Aug-2026.) $)
    df-propimp $a |- prop-> = ( x e. _V , y e. _V |-> ( ( x ++ y ) ++ <" 2 "> )
      ) $.
  $}

  $c PROP $.
  $( The language of Propositional Calculus. $)
  cprop $a class PROP $.

  ${
    $d n w x y z $.
    $( Define the language of propositional calculus.  This definition is
       noncircular.  For a more usable and intuitive, but circular, definition
       see ~ dfprop .  (Contributed by Thomas van Maaren, 21-Aug-2026.) $)
    df-prop $a |- PROP = setrecs ( ( y e. _V |->
      { x | ( E. z e. y ( x = ( prop-. ` z ) \/ E. w e. y x = ( w prop-> z ) )
      \/ E. n e. NN x = ( propvar ` n ) ) } ) ) $.
  $}

  ${
    $d A w $.  $d w x y $.  $d A x z $.  $d x z $.  $d n x y $.
    dfproplem.a $e |- A e. _V $.
    $( Given a set A, the set of all variables encoded as natural numbers,
       negations of elements in A, and implications between elements of A forms
       a set.  This lemma is used when using ~ fvmptd on the defining function
       of ` PROP ` .  (Contributed by Thomas van Maaren, 21-Aug-2026.) $)
    dfproplem $p |- { x | ( E. z e. A ( x = ( prop-. ` z ) \/
      E. w e. A x = ( w prop-> z ) ) \/ E. n e. NN x = ( propvar ` n ) ) } e.
      _V $=
      ( cv cfv csn ciun cun cn wceq wrex wo cab iunsn eqtri snex iunex cpropneg
      cpropimp co cpropvar cvv wcel df-iun df-sn uneq12i unab eqabri abbii unex
      rexbii nnex eqeltrri ) BDBGZUAHZIZCDCGUQUBUCZIZJZKZJZELEGUDHZIZJZKZAGZURM
      ZVIUTMCDNZOZBDNZVIVEMELNZOAPZUEVHVMAPZVNAPZKVOVDVPVGVQVDVIVCUFZBDNZAPVPBA
      DVCUGVSVMAVRVLBDVLAVCVCVJAPZVKAPZKVLAPUSVTVBWAAURUHCADUTQUIVJVKAUJRUKUNUL
      REALVEQUIVMVNAUJRVDVGBDVCFUSVBURSCDVAFUTSTUMTELVFUOVESTUMUP $.
  $}

  ${
    $d n w x y z $.
    $( Variables encoded as natural numbers are sentences of propositional
       calculus.  (Contributed by Thomas van Maaren, 21-Aug-2026.) $)
    varprop $p |- ( n e. NN -> ( propvar ` n ) e. PROP ) $=
      ( vy vx vz vw cv cn wcel c0 cvv cfv wceq wrex wo cpropvar cab cprop ax-mp
      0ex a1i cpropneg cpropimp co cmpt df-prop wss 0ss setrec1 wi wa rspe olcd
      wal ex alrimiv wb fvex elab6g sylibr orbi2d rexeqbi1dv orbi1d abbidv eqid
      rexeq dfproplem fvmpt eleqtrrdi sseldd ) AFZGHZIBJCFZDFZUAKLZVLEFVMUBUCLZ
      EBFZMZNZDVPMZVLVJOKZLZAGMZNZCPZUDZKZQVTVKIQWECBDEAUEIJHZVKSTIQUFVKQUGTUHV
      KVTVNVOEIMZNZDIMZWBNZCPZWFVKWAWKUIZCUMZVTWLHZVKWMCVKWAWKVKWAUJWBWJWAAGUKU
      LUNUOVTJHWOWNUPVJOUQWKCVTJURRUSWGWFWLLSBIWDWLJWEVPILZWCWKCWPVSWJWBVRWIDVP
      IWPVQWHVNVOEVPIVEUTVAVBVCWEVDCDEIASVFVGRVHVI $.
  $}

  ${
    $d w x y z u n $.
    $( The negation of a sentence of propositional calculus is a sentence of
       propositional calculus.  (Contributed by Thomas van Maaren,
       21-Aug-2026.) $)
    negprop $p |- ( x e. PROP -> ( prop-. ` x ) e. PROP ) $=
      ( vy vu vz vw vn cv cprop wcel csn cvv cpropneg cfv wceq wrex wo wa ax-mp
      cab wex cpropimp co cpropvar cn cmpt df-prop snexg snssi setrec1 wi velsn
      wal weq anbi1i exbii fveq2 eqeq2d bitri bilanri df-rex biimpri orc reximi
      equsexvw orcd 3syl ex alrimiv elab6g sylibr vsnex rexeq orbi2d rexeqbi1dv
      wb fvex orbi1d abbidv eqid dfproplem fvmpt eleqtrrdi sseldd ) AGZHIZWDJZB
      KCGZDGZLMZNZWGEGWHUAUBNZEBGZOZPZDWLOZWGFGUCMNFUDOZPZCSZUEZMZHWDLMZWEWFHWS
      CBDEFUFWDHUGWDHUHUIWEXAWJWKEWFOZPZDWFOZWPPZCSZWTWEWGXANZXEUJZCULZXAXFIZWE
      XHCWEXGXEWEXGQWHWFIZWJQZDTZWJDWFOZXEXMXGWEXMDAUMZWJQZDTXGXLXPDXKXOWJDWDUK
      UNUOWJXGDAXOWIXAWGWHWDLUPUQVDURUSXNXMWJDWFUTVAXNXDWPWJXCDWFWJXBVBVCVEVFVG
      VHXAKIXJXIVOWDLVPXECXAKVIRVJWFKIWTXFNAVKZBWFWRXFKWSWLWFNZWQXECXRWOXDWPWNX
      CDWLWFXRWMXBWJWKEWLWFVLVMVNVQVRWSVSCDEWFFXQVTWARWBWC $.
  $}

  ${
    $d w u v y z n t $.  $d w u v x z n t $.
    $( The implication between two sentences of propositional calculus is a
       sentence of propositional calculus.  (Contributed by Thomas van Maaren,
       21-Aug-2026.) $)
    impprop $p |- ( ( x e. PROP /\ y e. PROP ) -> ( x prop-> y ) e. PROP ) $=
      ( vw vz vv vu vn cv cprop wcel wa cvv wceq cpropimp wo wex weq vex sylibr
      wrex cpr cpropneg cfv co cpropvar cab cmpt df-prop prex a1i prssi setrec1
      cn wi wal w3a oveq2 eqeq2d oveq1 ceqsex2v 3anass exbii 19.42v bitri sylib
      bilanri olc elpr orc anim1i eximi df-rex olcd anim12i syl orcd ex alrimiv
      wb ovex elab6g ax-mp rexeq orbi2d rexeqbi1dv orbi1d abbidv eqid dfproplem
      fvmpt eleqtrrdi sseldd ) AHZIJBHZIJKZWMWNUAZCLDHZEHZUBUCMZWQFHZWRNUDZMZFC
      HZTZOZEXCTZWQGHUEUCMGUMTZOZDUFZUGZUCZIWMWNNUDZWOWPIXJDCEFGUHWPLJZWOWMWNUI
      ZUJWMWNIUKULWOXLWSXBFWPTZOZEWPTZXGOZDUFZXKWOWQXLMZXRUNZDUOZXLXSJZWOYADWOX
      TXRWOXTKZXQXGYDWRWPJZXPKZEPZXQYDEBQZFAQZXBKZFPZKZEPZYGYDYHYIXBUPZFPZEPZYM
      YPXTWOXBWQWTWNNUDZMXTEFWNWMBRARYHXAYQWQWRWNWTNUQURYIYQXLWQWTWMWNNUSURUTVF
      YOYLEYOYHYJKZFPYLYNYRFYHYIXBVAVBYHYJFVCVDVBVEYLYFEYHYEYKXPYHEAQZYHOYEYHYS
      VGWRWMWNERVHSYKXOWSYKWTWPJZXBKZFPXOYJUUAFYIYTXBYIYIFBQZOYTYIUUBVIWTWMWNFR
      VHSVJVKXBFWPVLSVMVNVKVOXPEWPVLSVPVQVRXLLJYCYBVSWMWNNVTXRDXLLWAWBSXMXKXSMX
      NCWPXIXSLXJXCWPMZXHXRDUUCXFXQXGXEXPEXCWPUUCXDXOWSXBFXCWPWCWDWEWFWGXJWHDEF
      WPGXNWIWJWBWKWL $.
  $}

  ${
    $d n x y $.  $d w x y z $.
    $( The set of variables encoded as a natural number, negations of sentences
       of propositional calculus, and implications between sentences of
       propositional calculus is a subset of ` PROP ` .  (Contributed by Thomas
       van Maaren, 21-Aug-2026.) $)
    dfprop1 $p |- { x | ( E. z e. PROP ( x = ( prop-. ` z ) \/
      E. w e. PROP x = ( w prop-> z ) ) \/ E. n e. NN x = ( propvar ` n ) ) }
      C_ PROP $=
      ( cv cpropneg cfv wceq cprop wrex wo cn wa simpr adantr eqeltrd wex simpl
      wcel rexlimiva cpropimp co cpropvar negprop df-rex anbi2i impprop syl2an2
      19.42v bitr4i simprr exlimiv sylbi jaodan varprop jaoi abssi ) AEZBEZFGZH
      ZURCEZUSUAUBZHZCIJZKZBIJZURDEZUCGZHZDLJZKAIVGURISZVKVFVLBIUSISZVAVLVEVMVA
      MURUTIVMVANVMUTISVABUDOPVMVEMZVMVBISZVDMZMZCQZVLVNVMVPCQZMVRVEVSVMVDCIUEU
      FVMVPCUIUJVQVLCVQURVCIVMVOVDUKVPVOVMVMVCISVOVDRVMVPRCBUGUHPULUMUNTVJVLDLV
      HLSZVJMURVIIVTVJNVTVIISVJDUOOPTUPUQ $.
  $}

  ${
    $d a n x y $.  $d a w x y z $.  $d n z w $.
    $( Every sentence of propositional calculus is either a variable encoded as
       a natural number, a negation of a sentence of propositional calculus, or
       an implication between two sentences of propositional calculus.
       (Contributed by Thomas van Maaren, 21-Aug-2026.) $)
    dfprop2 $p |- PROP C_ { x | ( E. z e. PROP ( x = ( prop-. ` z ) \/
      E. w e. PROP x = ( w prop-> z ) ) \/ E. n e. NN x = ( propvar ` n ) ) }
      $=
      ( vy va cprop cv cpropneg cfv wceq cpropimp wrex wo cab wss ssrexv orim1d
      wtru cvv co cpropvar cn df-prop wi wal dfprop1 sstr2 mpi weq rexeq orbi2d
      cmpt rexeqbi1dv orbi1d abbidv eqid vex dfproplem fvmpt elv orim2d reximdv
      syld ss2abdv eqsstrid syl ax-gen a1i setrec2v mptru ) GAHZBHZIJKZVLCHVMLU
      AKZCGMZNZBGMZVLDHUBJKDUCMZNZAOZPSGWAETVNVOCEHZMZNZBWBMZVSNZAOZUMZFAEBCDUD
      FHZWAPZWIWHJZWAPZUEZFUFSWMFWJWIGPZWLWJWAGPWNABCDUGWIWAGUHUIWNWKVNVOCWIMZN
      ZBWIMZVSNZAOZWAWKWSKFEWIWGWSTWHEFUJZWFWRAWTWEWQVSWDWPBWBWIWTWCWOVNVOCWBWI
      UKULUNUOUPWHUQABCWIDFURUSUTVAWNWRVTAWNWRWPBGMZVSNVTWNWQXAVSWPBWIGQRWNXAVR
      VSWNWPVQBGWNWOVPVNVOCWIGQVBVCRVDVEVFVGVHVIVJVK $.
  $}

  ${
    $d n w x z $.
    $( The set of sentences of propositional calculus is equal to the set of
       sentences that are either a variable encoded as a natural number, a
       negation of a sentence propositional calculus, or an implication between
       two sentences of propositional calculus.  (Contributed by Thomas van
       Maaren, 21-Aug-2026.) $)
    dfprop $p |- PROP = { x | ( E. z e. PROP ( x = ( prop-. ` z ) \/
      E. w e. PROP x = ( w prop-> z ) ) \/ E. n e. NN x = ( propvar ` n ) ) }
      $=
      ( cprop cv cpropneg cfv wceq cpropimp co wrex wo cpropvar dfprop2 dfprop1
      cn cab eqssi ) EAFZBFZGHITCFUAJKICELMBELTDFNHIDQLMARABCDOABCDPS $.
  $}


$( (End of Thomas van Maaren's mathbox.) $)
