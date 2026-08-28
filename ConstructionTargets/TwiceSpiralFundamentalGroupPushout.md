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

No fundamental group, van Kampen theorem, presentation, or desired frozen
equivalence is assumed.  The remaining algebraic step is injectivity of
`pushoutToZModTwo`, obtainable by constructing the reverse map with
`ZMod.lift` and proving the two generator equations.  After that, the first
absent topological interface is a theorem that the fundamental groupoid sends
the actual path-connected open cover (or the collared quotient gluing) to this
group pushout, including basepoint-change transports.
