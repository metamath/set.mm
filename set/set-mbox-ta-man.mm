$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Topological Manifolds
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Found this and was curious about how manifolds would be expressed in set.mm:
  ~
  https://mathoverflow.net/questions/336367/real-manifolds-in-a-theorem-prover

  This chapter proposes to define first manifold topologies, which characterize
  topological manifolds, and then to extend the structure with presentations,
  i.e., equivalence classes of atlases for a given topological space.  We
  suggest to use the extensible structures to define the "topological space"
  aspect of topological manifolds, and then extend it with
  charts/presentations.

$)

  $c ManTop $.

  $( The class of n-manifold topologies. $)
  cmntop $a class ManTop $.

  ${
    $d n j $.
    $( Define the class of ` N ` -manifold topologies, as second countable
       Hausdorff topologies locally homeomorphic to a ball of the Euclidean
       space of dimension ` N ` .  (Contributed by Thierry Arnoux,
       22-Dec-2019.) $)
    df-mntop $a |- ManTop = { <. n , j >. |
      ( n e. NN0 /\ ( j e. 2ndc /\ j e. Haus
        /\ j e. Locally [ ( TopOpen ` ( EEhil ` n ) ) ] ~= ) ) } $.

    $( Manifold is a relation.  (Contributed by Thierry Arnoux,
       28-Dec-2019.) $)
    relmntop $p |- Rel ManTop $=
      ( vn vj cv cn0 wcel c2ndc cha cehl cfv ctopn chmph cec clly w3a wa cmntop
      df-mntop relopabiv ) ACZDEBCZFETGETSHIJIKLMENOABPBAQR $.
  $}

  ${
    $d J j n u x y $.  $d N j n u x y $.
    $( Property of being a manifold.  (Contributed by Thierry Arnoux,
       28-Dec-2019.) $)
    ismntoplly $p |- ( ( N e. NN0 /\ J e. V ) ->
      ( N ManTop J <-> ( J e. 2ndc /\ J e. Haus /\ J e. Locally
      [ ( TopOpen ` ( EEhil ` N ) ) ] ~= ) ) ) $=
      ( vn vj cn0 wcel wa cmntop c2ndc cha cehl cfv ctopn chmph cec clly eleq1d
      w3a wceq wbr simpl simpr 2fveq3 eceq1d llyeq syl adantr eleq12d 3anbi123d
      cv anbi12d df-mntop brabga mpbirand ) BFGZACGZHBAIUAUPAJGZAKGZABLMNMZOPZQ
      ZGZSZUPUQUBDUKZFGZEUKZJGZVGKGZVGVELMNMZOPZQZGZSZHUPVDHDEBAIFCVEBTZVGATZHZ
      VFUPVNVDVQVEBFVOVPUBRVQVHURVIUSVMVCVQVGAJVOVPUCZRVQVGAKVRRVQVGAVLVBVRVOVL
      VBTZVPVOVKVATVSVOVJUTOVEBNLUDUEVKVAUFUGUHUIUJULEDUMUNUO $.

    $( Property of being a manifold.  (Contributed by Thierry Arnoux,
       5-Jan-2020.) $)
    ismntop $p |- ( ( N e. NN0 /\ J e. V ) -> ( N ManTop J <-> ( J e. 2ndc
      /\ J e. Haus /\ A. x e. J A. y e. x E. u e. ( J i^i ~P x ) ( y e. u /\
        ( J |`t u ) ~= ( TopOpen ` ( EEhil ` N ) ) ) ) ) ) $=
      ( wcel wa wbr cfv chmph w3a cv wrex wral wb ctop a1i anbi2d 3anass cmntop
      cn0 c2ndc cha cehl ctopn cec clly crest cpw cin ismntoplly haustop adantl
      co biantrurd wer wrel hmpher errel relelec mp2b hmphsymb rexbidv 2ralbidv
      bitr2i islly 3bitr4rd pm5.32da 3bitr4g adantr bitrd ) EUBGZDFGZHEDUAIDUCG
      ZDUDGZDEUEJUFJZKUGZUHGZLZVOVPBMCMZGZDWAUIUOZVQKIZHZCDAMZUJUKZNZBWFOADOZLZ
      DEFULVMVTWJPVNVMVOVPVSHZHVOVPWIHZHVTWJVMWKWLVOVMVPVSWIVMVPHZWBWCVRGZHZCWG
      NZBWFOADOZDQGZWQHZWIVSWMWRWQVPWRVMDUMUNUPWMWHWPABDWFWMWEWOCWGWMWDWNWBWDWN
      PWMWNVQWCKIZWDQKUQKURWNWTPUSQKUTWCVQKVAVBVQWCVCVFRSVDVEVSWSPWMABCVRDVGRVH
      VISVOVPVSTVOVPWITVJVKVL $.
  $}

$(
  @( The real line is a manifold of dimension 1.  (Contributed by Thierry
     Arnoux, 4-Jan-2020.) @)
    remntop @p |- ( TopOpen ` RRfld ) e. ( ManTop " { 1 } ) @=
      ? @.

  @{
    circmntop.f @e |- F = ( x e. RR |-> ( exp ` ( _i x. x ) ) ) @.
    circmntop.c @e |- C = ( `' abs " { 1 } ) @.
    circmntop.w @e |- W = ( ( F "s RRfld ) |`s C ) @.
    @( The unit circle is a manifold of dimension 1.  (Contributed by Thierry
       Arnoux, 4-Jan-2020.) @)
    circmntop @p |- ( TopOpen ` W ) e. ( ManTop " { 1 } ) @=
      ? @.
  @}
$)

