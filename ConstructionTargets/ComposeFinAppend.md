# ComposeFinAppend

`dependentArrow_conjugation` transports a dependent categorical arrow across
an equality of its indices while displaying both endpoint `eqToHom`s.

`composeFin_front_tail_reindex` uses `composeFin_reindex_of_index_eq` to
compare the two tail chains indexed by `i.succ.castSucc` and
`i.castSucc.succ`. It retains the outer endpoint transports and never rewrites
a dependent arrow family directly.

The arbitrary split after `S.n + 1` remains. The precise next step is to absorb
the two outer transports from the tail comparison into the first and final
arrows during the front-recursion induction, then apply the banked left/right
mapped-piece formulas. No concatenated evaluation or quotient composition law
is claimed here.
