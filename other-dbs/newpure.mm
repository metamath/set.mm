$[ prop.mm $]

$c A. var $.

$v x y z w $.

vx $f var x $.
vy $f var y $.
vz $f var z $.
vw $f var w $.

wal $a wff A. x ph $.

ax-5 $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.

ax-6 $a |- ( -. A. x -> A. x -. A. x ph ) $.

${
   ax-gen.1 $e |- ph $.

   ax-gen $a |- A. x ph $.
$}

${
   mpg.1 $e |- ( A. x ph -> ps ) $.
   mpg.2 $e |- ph $.

   mpg $p |- ps $= $.
$}

${
   19.20i.1 $e |- ( ph -> ps ) $.

   19.20i $p |- ( A. x ph -> A. x ps ) $= $.
$}

hba1 $p |- ( A. x ph -> A. x A. x ph ) $= $.
