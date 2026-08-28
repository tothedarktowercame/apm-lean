# TwiceSpiralFundamentalGroupPushout

The pinned Mathlib contains the fundamental groupoid, induced maps, homotopy
transport, products, and the algebraic indexed group pushout
`Monoid.PushoutI`.  It does not contain a Seifert--van Kampen theorem for an
open cover or a quotient gluing.

This target records the concrete algebraic diagram that such a theorem must
produce.  The common group is `Multiplicative (ℤ × ℤ)` and the two piece maps
are

* `(a,b) ↦ b`, and
* `(a,b) ↦ 2*a + d*b`.

`TwiceSpiralPushout d` is Mathlib's genuine group pushout of this diagram.
`pushoutToZModTwo` is its canonical map to `Multiplicative (ZMod 2)`;
`branches_comp_boundary` proves the cocone equation,
`right_generator_sq` derives the order-two relation from the pushout relation,
and `pushoutToZModTwo_surjective` proves that the canonical map is onto.

The reverse map `zmodTwoToPushout` is the `ZMod.lift` of the right pushout
generator; `rightGeneratorAddHom_two` supplies its order-two premise.  The
pushout relation at `(0,n)` gives `left_branch_eq_right_branch`, identifying
the left generator `n` with the right generator `d*n`.  The indexed-pushout
universal property proves one composite is the identity, while integer
representatives of `ZMod 2` prove the other.  Thus
`pushoutToZModTwo_injective` and the explicit equivalence
`twiceSpiralPushoutMulEquivZModTwo` require no presentation theorem.

No fundamental group, van Kampen theorem, presentation, or desired frozen
equivalence is assumed.  The remaining seam is a topological theorem that the
fundamental groupoid sends the actual path-connected open cover (or collared
quotient gluing) to this group pushout, including basepoint-change transports
identifying the piece maps with `leftBoundaryHom` and `rightBoundaryHom d`.
