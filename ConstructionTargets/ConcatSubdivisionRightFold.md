# ConcatSubdivisionRightFold

This target defines the literal right-block object and arrow families inside a
concatenated subdivision. `rightBlockArrow` uses the actual concatenated
mapped piece and explicit endpoint `eqToHom` transports.

`rightBlockArrow_eq_conjugate` compares each such arrow with the corresponding
arrow of `T`. `rightBlockComposeFin_eq` applies the generic dependent-fold
conjugation theorem, leaving exactly the midpoint and final point transports.

The remaining theorem is the prefix/suffix join: identify this restricted fold
with the last `T.n + 1` arrows of the full concatenated fold. Its induction
must retain the midpoint transport while repeatedly applying
`composeFin_dropLast_two`. No full evaluation equality is claimed here.
