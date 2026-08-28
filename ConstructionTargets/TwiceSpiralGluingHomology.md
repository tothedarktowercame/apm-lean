# TwiceSpiralGluingHomology

This target begins the production Mayer--Vietoris calculation for
`SolidTorusGluingOpenCover.Gluing h`.

Degree zero is complete.  Explicit witnesses make both cover pieces and their
intersection nonempty; their supplied homotopy equivalences transport the
known H0 coordinates for the solid torus and boundary torus.  The production
open-cover H0 theorem therefore yields both additive-group and `ModuleCat ℤ`
isomorphisms with `ℤ`.

In degree one, the target constructs the exact coordinate isomorphisms from
the production intersection and piece homology objects to `ℤ²`, using the H1
coordinates determined by the supplied π1 coordinates.  It also defines
`productionH1CoordinateArrow`, the actual production intersection arrow
conjugated by those isomorphisms.

`productionH1ArrowComparisonStatement` now records the literal equality only
with the three coordinate-normalization premises it needs: the two boundary
inclusions must be second-coordinate maps in the supplied bases, and
`h_*(1,0)=(1,2)`.  Arbitrary choices of the four coordinate equivalences do
not satisfy that statement (for example, negating a solid-torus coordinate
negates the corresponding component).

The continuous-map squares are transported through singular homology by
`intersection_left_homology_square` and
`intersection_right_homology_square`.  The banked singular-homology
representation comparisons now identify each projection of
`productionIntersectionArrow` with the corresponding public
`singularHomologyFunctor.map`; the declarations
`productionIntersectionArrow_fst_functor` and
`productionIntersectionArrow_snd_functor` expose those identities directly.
Their postcomposed versions feed the two staged coordinate formulas
`productionH1CoordinateArrow_fst` and
`productionH1CoordinateArrow_snd`.

`productionH1ArrowComparison` proves the conditional statement.  Its proof
uses all three normalization hypotheses through
`actual_signed_H1_pair_formula`: `hinc₁` and `hinc₂` identify the two
boundary inclusions with second-coordinate projection, while `h10` fixes the
first column of the gluing map.  The right projection uses the fully
left-associated negation lemma to transport the Mayer--Vietoris sign; the two
projections are then reassembled through the canonical biproduct-to-product
isomorphism.

Accordingly this target does not claim H1, H2, H3, or higher-degree homology
of the glued space.  The next residual is categorical rather than
representational: transport monicity and the explicit cokernel of
`twiceSpiralSignedArrow` through this comparison and the adjacent production
Mayer--Vietoris exact segments to derive the H2 and H1 conclusions.  No such
exactness consequence or desired homology-table entry is assumed here.
