# Maps out of the cyclic integer module

`IntegerCyclic.lean` packages the coordinate-free fact that a nonzero map from
the free rank-one integer module into a torsion-free integer module is a
monomorphism.  It also provides an isomorphism-invariant form for consumers
whose source and target are only identified with these standard modules.

The module was extracted for `t00J02`, where the target is `Fin 4 → ℤ`.  Keeping
torsion-freeness as the interface makes the result useful without fixing a
basis or a finite rank.
