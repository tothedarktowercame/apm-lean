# ComposeFinFrontTailAbsorption

`composeFin_front_tail_absorbed` consumes the exact output of
`composeFin_front_tail_reindex` and reassociates its two object transports into
the neighboring prefix and suffix arrows. The theorem retains every
`eqToIso`; it does not simplify a dependent endpoint before its type is
aligned. `absorb_conjugated_middle` records the underlying categorical law.

The remaining arbitrary-split theorem is an induction on the length of the
first block. At each successor step this absorption theorem supplies the typed
tail recursion; the induction must then normalize the chosen split index and
apply the left/right mapped-piece formulas. The concatSubdivision segment-fold
and evaluation equalities are not claimed here.
