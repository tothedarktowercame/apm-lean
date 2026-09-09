# Small-chain comparison in degree zero

For `R : Type` with `[CommRing R]`, a topological space `X : Type` and
an arbitrary index type `α : Type`, let `U : α → Set X` be an open cover.
All these types are universe zero. No connectedness or nonemptiness is
assumed. The small chains and their actual inclusion are those constructed
in `CoefficientSmallPath`, with coefficient object `ModuleCat.of R R`.

`component_mono` proves degreewise monicity of the inclusion from injectivity
of the small-simplex subtype map. `liftZero` assigns every singular vertex
its small-simplex generator, since the sets cover the space; `liftZero_inc`
proves this is a right inverse to the degree-zero inclusion.

`edge_lift` treats a singular one-simplex as a path and applies the reviewed
finite small-path construction to lift its boundary. `liftOne` assembles
the chosen lifts by the coproduct universal property. `liftOne_boundary`
states that inclusion followed by the absolute differential recovers the
original boundary. This is a boundary-lifting map, not a subdivision chain
operator in every degree.

`exists_boundary` extracts a one-chain bounding a null H0 cycle using the
actual homology cokernel and module exactness. Applying `liftOne` and the
degree-zero monomorphism shows that every small cycle vanishing in absolute
H0 already bounds in the small complex. Thus `h0_injective` holds. The
zero-chain lift gives surjectivity, and `h0_isIso` proves invertibility.

`h0Iso` uses the inverse of this proved isomorphism. `h0Iso_hom` identifies
its forward map exactly with `HomologicalComplex.homologyMap` of the actual
small-chain inclusion in degree zero. `inverse_left` states inverse then
forward is identity, and `inverse_right` states forward then inverse is
identity. No H0 comparison or path-component classification is assumed.

The rational and integer examples use the overlapping real-line cover
`(-∞,1)` and `(0,∞)`. `empty_cover` uses the empty space with empty index
type, showing the statement needs no hidden inhabitance hypothesis.

The source exactly promotes `/tmp/CoefficientSmallH0.lean`, SHA256
`605f1bc748910d477aa9f2ef4272f007a02b518aac32fb806ebbb63dc27e2312`.
Validation includes fixture and canonical compilation, the focused build,
eight standard-only printed axiom audits including all three examples,
and placeholder and scope checks.

Positive-degree small-chain comparison, relative excision including degree
zero and potentially nonclosed excision, sphere suspension and rational S2
H1/H2 remain downstream. No frozen consumer closure is claimed.
