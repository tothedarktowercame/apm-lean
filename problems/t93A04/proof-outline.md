# Proof Outline: t93A04

The compiled helper
`apm_t93a04_isSmoothLinePreimage_preimage_iff` reduces the custom conclusion
for the actual inverse image to the transversality condition alone.

`apm_t93a04_range_sup_span_eq_top_of_projection_surjective` compiles the
linear-algebra step: a derivative whose composition with projection along
`v` is surjective has range which, together with `span {v}`, is all of `ℝ³`.

`apm_t93a04_lineDirection_ne_zero` supplies a concrete line direction, and
the main theorem now closes the entire empty-domain branch because its
transversality obligation is vacuous.

Fix a nonzero direction in `ℝ³` and project along it to `ℝ²`.  A regular
value of the composite projection with `f` determines an affine fiber line.
Surjectivity of the composite derivative is equivalent to the range of
`mfderiv f` together with the line direction spanning `ℝ³`.

## Remaining boundary

For nonempty domains, Mathlib supplies Sard-type results for finite-dimensional
normed vector spaces but not arbitrary second-countable manifolds. Closure needs a
countable chart cover, chartwise Sard, compatibility of criticality with chart
derivatives, and countable-union nullity.

The countable null-set avoidance has now been compiled in sibling `t92J07`;
the shared missing input is still chartwise manifold-Sard nullity itself.
