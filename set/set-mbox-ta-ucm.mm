$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Uniform Stuctures and Spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Hausdorff uniform completion
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c HCmp $. $( The Hausdorff uniform completion relation. $)

  $( Extend class notation with the Hausdorff uniform completion relation. $)
  chcmp $a class HCmp $.

  ${
    $d u w $.
    $( Nota: despite uniqueness, this definition will not yield a function,
       since only three components of the structure are fixed. ( Base o. HCmp )
       shall be a function, though. $)
    $( Definition of the Hausdorff completion.  In this definition, a structure
       ` w ` is a Hausdorff completion of a uniform structure ` u ` if ` w ` is
       a complete uniform space, in which ` u ` is dense, and which admits the
       same uniform structure.  Theorem 3 of [BourbakiTop1] p.  II.21. states
       the existence and uniqueness of such a completion.  (Contributed by
       Thierry Arnoux, 5-Mar-2018.) $)
    df-hcmp $a |- HCmp = { <. u , w >. | ( ( u e. U. ran UnifOn /\ w e. CUnifSp
      ) /\ ( ( UnifSt ` w ) |`t dom U. u ) = u
        /\ ( ( cls ` ( TopOpen ` w ) ) ` dom U. u ) = ( Base ` w ) ) } $.
  $}
