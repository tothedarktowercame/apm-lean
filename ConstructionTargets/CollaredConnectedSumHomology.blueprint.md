# Collared connected-sum homology

## Implemented split (2026-10-21)

`connectedSum_homology` is now a sorry-free assembly.  Every admitted theorem
below is independent: whenever a later mathematical stage needs an earlier
conclusion, that conclusion is an explicit hypothesis.

* `BallCollar.largeInterior_isOpen` (B2, **LIBRARY**, 250--500 lines):
  invariance of domain for the restricted radius-two embedding.  Mathlib has
  `IsOpenMap`/manifold chart machinery but no located invariance-of-domain
  theorem.  There is no t00A01 proof: its `HasBallCollar` assumes openness.
  For t93A03's `Circle × sphere` summands, openness can instead be proved from
  its concrete product charts, but not from its present abstract embedding
  data alone.  Truth checks: ordinary disks in dimensions 2 and 4 have open
  interior images; dimension zero is intentionally outside B11 (`2 ≤ n`).
* `BallCollar.punctured_pathConnected` (B3, 80--140 lines), template
  `apm_t00A01_punctured_pathConnected` and its auxiliary proof at line 578.
  Generalization replaces path detours in `S²` by path connectedness of
  `S^(n-1)`, valid for `n ≥ 2`.  For punctured `S²`, `T²`, `S⁴`, and
  `S² × S²`, the complement remains path connected.
* B4 is split into two independent **LIBRARY** leaves:
  `BallCollar.punctured_topHomology_zero` (180--350 lines) says `H_n` of the
  puncture vanishes, while `BallCollar.boundary_homology_zero` (250--550
  lines) says the actual inclusion-induced map
  `H_(n-1)(Sphere n) ⟶ H_(n-1)(Punctured c)` is zero.  Template: the localization chain under
  `apm_t00A01_punctured_isHomologyBall_aux_localization`.  Its `H₃` and local
  degree-three generator must become degree `n`; the integral sign is
  irrelevant to vanishing.  For punctured closed surfaces the boundary circle
  bounds the remaining surface, and in dimension four the same relative
  fundamental-class argument kills `H₄`.
* `BallCollar.punctured_homology` (B5, 120--200 lines once B4 exists), template
  `apm_t00A01_punctured_isHomologyBall` plus `_aux_cover`, `_aux_mv`, and
  `_aux_mid_connecting`.  Sphere homology changes from `S²` to `S^(n-1)`.
  In dimension two the boundary circle is zero in puncture `H₁` because it is
  the boundary of the complementary fundamental chain, so `H₁` is preserved;
  in dimension four it preserves the two middle `ℤ` classes of `S² × S²`.
* `BallCollar.punctured_fundamentalGroup_three` (B6, 120--180 lines), template
  `apm_t00A01_punctured_fundamentalGroup` and auxiliaries beginning near line
  845.  This is deliberately dimension three: it uses simple connectivity of
  `S²` and does not generalize to `n = 2`.  The supplied sphere point makes the
  basepoint change explicit.
* `BallCollar.connectedSum_standardCover` (B7, 150--250 lines), template
  `apm_t00A01_collared_standardCover` and its `_aux_*` declarations.  Its
  `HasStandardCover` conclusion includes open `U,V`, their union equation,
  homotopy equivalences `U ≃ₕ P₁`, `V ≃ₕ P₂`, and
  `U ∩ V ≃ₕ Sphere n`; it is not satisfiable merely by `U = V = univ`.
  The equivalences are also compatible with the inclusions: transported
  through them, `U ∩ V ⊆ U` and `U ∩ V ⊆ V` are homotopic to
  `c₁.boundaryMap` and `c₂.boundaryMap`.  B9b (degree `n-1`) and B10 need
  this, because their `boundaryHomologyMap = 0` hypotheses must reach the
  Mayer--Vietoris map out of `H (U ∩ V)`; with unrelated equivalences they
  could not (review fix, 2026-10-21).
  Radial formulas are dimension-independent.  It works for both surface and four-manifold
  connected sums, including `S² # S²` and `S⁴ # S⁴`.
* B8 is **not a leaf**.  `ConstructionTargets.IntegralOpenCoverMayerVietoris.HZ`
  and this module's `H` unfold to the same Mathlib singular-homology functor;
  no production/Mathlib comparison is necessary.
* B9 is split into three independent leaves:
  `connectedSum_mayerVietoris_zero` (40--80 lines),
  `connectedSum_mayerVietoris_middle` (100--170 lines), and
  `connectedSum_mayerVietoris_above` (50--100 lines).  Each consumes only the
  relevant parts of the two puncture tables plus the genuine standard cover.
  The middle leaf additionally receives both boundary-map vanishing equations;
  these are essential at `k = n-1`.  Templates:
  `apm_t00A01_bridge_connectedSum_isHomology3Sphere` for assembly and
  `apm_t00A01_punctured_isHomologyBall_aux_mv` for exactness.  In dimension
  two it gives the expected direct sum on `H₁`; in dimension four it gives
  rank four for `(S²×S²)#(S²×S²)` in degree two and no extra degree three.
* `connectedSum_topConnecting_iso` (B10, **LIBRARY**, 150--300 lines): consumes
  the two puncture top vanishings, both boundary-map vanishing equations, and
  the genuine standard cover, and identifies the sole top
  class.  Template: `_aux_mid_connecting` and the final bridge assembly.
  The orientation sign changes the chosen generator only.  It gives one `ℤ`
  for `S²#S²`, `T²#T²`, `S⁴#S⁴`, and four-dimensional oriented examples.

B11 calls B2 twice, B3 twice, both B4 leaves twice, B5 twice, B7, B9, and B10.  B6 is an
independent t93A03 consumer and therefore is intentionally not used by the
homology assembly.  There are no admitted definitions and no placeholder
propositions.

The closed-annulus counterexample now fails B4b: for a radius-three closed
ball punctured by the unit ball, the boundary inclusion
`S^(n-1) → {1 ≤ ‖x‖ ≤ 3}` is a homotopy equivalence, so its map on
`H_(n-1)` is not zero.  It also cannot substitute the trivial `U = V = univ`
cover for B7, because the required overlap equivalence and two piece
equivalences would force incompatible homotopy types.  For `n = 2`, B4b is
exactly the fact that the boundary circle bounds the complementary surface;
for `n = 4`, it removes the possible extra quotient in degree three, while
the degree-two direct sum (for example rank four for two `S² × S²` summands)
is unaffected.

## Sources and scope

This blueprint follows:

* `~/notes/closer/audits/t98A02-collared.edn`, steps
  `closedManifold_homology_localToGlobal`,
  `t98A02_productionHomology_bridge`,
  `t98A02_collaredBallComplement_homology`,
  `t98A02_collaredConnectedSum_mayerVietoris`, and
  `connectedSum_topConnecting`;
* `holes/labs/blueprints/t98A02/Blueprint.lean`, whose sole library
  obligation is `t98A02_collaredConnectedSum_homology`;
* `holes/labs/blueprints/t00A01/Blueprint.lean`, revision 2, specifically
  `apm_t00A01_punctured_pathConnected`,
  `apm_t00A01_punctured_fundamentalGroup`,
  `apm_t00A01_punctured_isHomologyBall`, and
  `apm_t00A01_collared_standardCover`.

The foundation is restricted to the integral singular homology and puncture
facts those two consumers use. It does not develop a theory of arbitrary wild
balls. The radius-two extension in t98A02 and `HasBallCollar` in t00A01 are
the collar data.

The implementation builds on
`ConstructionTargets.ProductionOpenCoverMayerVietoris`,
`ConstructionTargets.SphereHomology`,
`ConstructionTargets.SingularHomologyHomotopy`,
`ConstructionTargets.TopologicalSumSingularHomology`, and Mathlib's
`AlgebraicTopology.singularHomologyFunctor`, `HomologicalComplex.homologyMap`,
`ContinuousMap.HomotopyEquiv`, `FundamentalGroup`, and manifold invariance of
domain API. All homology objects below mean
`((singularHomologyFunctor (ModuleCat ℤ) k).obj (ModuleCat.of ℤ ℤ)).obj
(TopCat.of X)`.

## Representations

For `n : ℕ`, write `E n := EuclideanSpace ℝ (Fin n)`, `D n r` for the
closed ball of radius `r`, and `S n` for the unit sphere in `E n` (thus
topologically `S^(n-1)`). `BallCollar n M` contains maps
`φ : D n 1 → M` and `ψ : D n 2 → M`, embeddings of both, and the
equation `ψ ∘ unitToLarge = φ`. Openness of the image of the radius-two
interior is a derived field, not an extra t98A02 hypothesis.

`Punctured c` is the subtype complement of `φ '' Metric.ball 0 1`.
`ConnectedSum c₁ c₂` is the quotient of `Punctured c₁ ⊕ Punctured c₂`
by the equivalence relation generated by equal unit-sphere parameters. The
consumer quotients use the same oriented relation. B12 and B13 construct the
explicit quotient homeomorphisms; no definitional equality is assumed.

### B1. Collar package and radial regions
lean: `BallCollar`, `Punctured`, `boundaryMap`, `ConnectedSum`, and the radial
open subsets at radii `1/2`, `1`, `3/2`, and `2`.
uses: Mathlib metric balls, subtypes, quotient topology
status: planned

Prove injectivity and continuity of every restriction, identify the unit
sphere with the boundary of the deleted ball, and record the radial homotopies
that retract an annulus onto that sphere. `IsEmbedding φ` is used for the
boundary map and its image equations; `ψ ∘ unitToLarge = φ` is used to
rewrite every inner-collar point in the consumer coordinates.

### B2. The large collar has open interior image
lean: `BallCollar.largeInterior_isOpen`
uses: B1, manifold invariance of domain
status: planned

For an `n`-manifold modelled on `E n`, restrict the embedding `ψ : D n 2 → M`
to `Metric.ball 0 2`. The source is an open `n`-manifold, so invariance of
domain makes the restricted map open. Its range is exactly
`ψ '' {x | dist x.1 0 < 2}`. This is the openness already present in the
t00A01 collar hypothesis and the fact that must be derived for t98A02.

### B3. A collared puncture is path connected
lean: `BallCollar.punctured_pathConnected`
uses: B1, B2
status: planned

Assume `M` is path connected and a boundaryless connected `n`-manifold with
`2 ≤ n`. Modify any path whose endpoints lie outside the deleted open ball:
inside each collar component, radially project the path segment to the unit
sphere, leaving it fixed outside the radius-`3/2` collar. The pasting lemma
gives a path in `Punctured c`. Compactness is not used here.

### B4. Local orientation from top integral homology
lean: `closedManifold_topClass_localGenerator`
uses: B1, B2, relative singular homology and excision
status: planned

Let `M` be compact, path connected, and an `n`-manifold, and assume
`Nonempty (H n M ≅ ℤ)`. The map from absolute top homology to the local
group at a point in the inner ball sends a choice of generator to a generator.
Prove this by transporting the local group through the collar chart, using
excision to the Euclidean ball, and propagating the sign along paths. Compactness
is used for the closed-manifold fundamental class; path connectedness makes
the local sign system constant; the top-homology isomorphism selects a
nonzero global class.

### B5. Homology of a collared puncture
lean: `BallCollar.punctured_homology`
uses: B2, B3, B4, sphere homology, open-cover Mayer--Vietoris
status: planned

For compact path-connected `M`, `2 ≤ n`, `H n M ≅ ℤ`, and `H k M = 0`
for `n < k`, prove
`H 0 (Punctured c) ≅ ℤ`, `H k (Punctured c) ≅ H k M` for
`0 < k < n`, and `H k (Punctured c) = 0` for `n ≤ k`. Cover `M` by the
large collar interior and the complement of the closed radius-`1/2` ball.
Their overlap retracts radially to `S n`; use B4 to prove that the top
connecting morphism is an isomorphism. Exactness then gives every stated
degree. The assumed high-degree vanishing is used only above `n`.

### B6. Fundamental group of a three-dimensional puncture
lean: `BallCollar.punctured_fundamentalGroup_three`
uses: B1, B2, B3, van Kampen, simple connectedness of `S²`
status: planned

For `n = 3`, apply van Kampen to the cover used in B5. The collar ball is
simply connected and the overlap retracts to `S²`; hence inclusion of the
punctured piece induces an isomorphism on fundamental groups. Include the
change of basepoint from the boundary point to the supplied `m : M`.

### B7. Standard open cover of the quotient
lean: `BallCollar.connectedSum_standardCover`
uses: B1, B2
status: planned

Thicken each punctured summand across half of the other outer collar. Prove
the two saturated subsets of the quotient are open, cover the quotient,
retract to the respective punctured summands, and have intersection
homotopy-equivalent to `S n`, compatibly: the overlap inclusions,
transported through the equivalences, are homotopic to the collar boundary
maps. All quotient descents are proved from the
generating boundary equation before continuity is invoked.

### B8. Production/Mathlib homology comparison
lean: `productionHomologyIso`
uses: production singular-chain comparison
status: planned

Construct a natural isomorphism between the integral production homology
objects used by `ProductionOpenCoverMayerVietoris` and `H k X` above. Prove
naturality for both inclusions and the connecting morphism. This is the only
representation conversion used in B9--B11.

### B9. Connected-sum Mayer--Vietoris sequence
lean: `connectedSum_mayerVietoris`
uses: B7, B8, production open-cover Mayer--Vietoris
status: planned

Transport the production exact sequence for the B7 cover to `H`. Under the
three homotopy equivalences, its terms are `H k (S n)`,
`H k (Punctured c₁) ⊕ H k (Punctured c₂)`, and
`H k (ConnectedSum c₁ c₂)`. Record these identifications and exactness in
each degree without yet simplifying the terms.

### B10. The top connecting map
lean: `connectedSum_topConnecting_iso`
uses: B4, B5, B9
status: planned

Orient the two boundary maps oppositely according to the quotient relation.
The boundary sphere maps to zero in each punctured top-minus-one group because
it is the boundary of the selected local fundamental chain. Exactness and B4
then show `H n (ConnectedSum c₁ c₂) → H (n-1) (S n)` is an isomorphism.
The sign affects only the chosen isomorphism, not its existence.

### B11. Final generic homology theorem
lean: `ConstructionTargets.CollaredConnectedSumHomology.connectedSum_homology`
uses: B3, B5, B9, B10
status: planned

Intended Lean type (the names `E`, `I`, `H`, and `ConnectedSum` are the
declarations fixed in B1):

```
theorem connectedSum_homology
    (n : ℕ) (hn : 2 ≤ n)
    (X₁ X₂ : Type)
    [TopologicalSpace X₁] [T2Space X₁] [CompactSpace X₁]
    [PathConnectedSpace X₁] [ChartedSpace (E n) X₁]
    [IsManifold (I n) (⊤ : ℕ∞) X₁]
    [TopologicalSpace X₂] [T2Space X₂] [CompactSpace X₂]
    [PathConnectedSpace X₂] [ChartedSpace (E n) X₂]
    [IsManifold (I n) (⊤ : ℕ∞) X₂]
    (c₁ : BallCollar n X₁) (c₂ : BallCollar n X₂)
    (htop₁ : Nonempty (H n X₁ ≅ ModuleCat.of ℤ ℤ))
    (htop₂ : Nonempty (H n X₂ ≅ ModuleCat.of ℤ ℤ))
    (habove₁ : ∀ k, n < k → IsZero (H k X₁))
    (habove₂ : ∀ k, n < k → IsZero (H k X₂)) :
    let Y := ConnectedSum c₁ c₂
    Nonempty (H 0 Y ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ k, 0 < k → k < n →
      Nonempty (H k Y ≅ ModuleCat.of ℤ ((H k X₁) × (H k X₂)))) ∧
    Nonempty (H n Y ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ k, n < k → IsZero (H k Y))
```

H₀ uses B3. Degrees strictly between zero and `n` follow from B5, B9, and
the vanishing of sphere homology there. Degree `n-1` also uses the zero
boundary maps from B10. Degree `n` is B10, and higher degrees use B5, B9,
and the supplied high-degree hypotheses.

### B12. Exact t98A02 adapter
lean: `t98A02_collaredConnectedSum_homology` (consumer theorem)
uses: B1, B2, B11
status: planned

Instantiate `n = 4`, build each `BallCollar` from `φᵢ,ψᵢ`, and use B2 for
the missing openness field. Construct the quotient homeomorphism from the
generic relation to `T98A02ConnectedSum φ₁ φ₂`, oriented from the
generic quotient to the frozen quotient, and transport B11. The hypotheses
`H₄ ≅ ℤ` feed B4/B11 and the hypotheses `5 ≤ k` feed B11's `4 < k`.
This yields the frozen theorem in `holes/labs/blueprints/t98A02/Blueprint.lean`
verbatim.

### B13. Exact t00A01 adapters
lean: the four `apm_t00A01_*` library theorems named in Sources
uses: B3, B5, B6, B7
status: planned

Instantiate `n = 3`. `HasBallCollar` supplies B2's openness directly. B3 gives
`punctured_pathConnected`; B6 gives `punctured_fundamentalGroup`; B5, together
with the homology-three-sphere hypotheses, gives `punctured_isHomologyBall`;
B7 and the explicit quotient homeomorphism give `collared_standardCover`.
The compact, Hausdorff, second-countable, charted, manifold, and boundaryless
hypotheses are used by B3--B6. The homology-sphere hypothesis is unused by
B3 and B6 except where their frozen consumer signatures mandate it; it is
used essentially by B5.
