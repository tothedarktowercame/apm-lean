# Blueprint for t98A04

## Triage and repair

Verdict: **unfaithful as registered; repaired**.

The point-set sphere, fibers, corrected section type `S² → S³`, and no-section
conclusion in `Main.lean` are faithful.  The defect is the definition of
`apm_t98a04_IsSubmersion`: it existentially chooses the source
`ChartedSpace`.  Thus it does not say that the displayed Hopf map is a
submersion for the ordinary smooth structure on the sphere fixed in the
problem.  This is exactly the defect recorded by
`holes/labs/statement-registry/triage-3.md`.

`RevisedMain.lean` makes the smallest repair recommended there.  It replaces
the ad-hoc subtype by Mathlib's
`Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1`, supplies the elementary
real-finrank fact `4 = 3 + 1`, and consequently uses Mathlib's fixed
`EuclideanSpace.instChartedSpaceSphere`.  The source atlas is removed from the
existential submersion predicate.  The target atlas remains existential,
because Mathlib has no installed smooth atlas for this projectivization.  No
mathematical hypothesis or conclusion from `problem.md` was dropped.

There is no short logical counterexample to compile in `Refute.lean`: the old
claim is under-specified rather than contradicted by a concrete input.  Its
witness may select an arbitrary source atlas, so even proving it would not
answer the sentence “Show that π is a submersion” for the standard `S³`.

Degenerate checks:

* The repaired sphere is nonempty (for example `(1,0)`) and excludes zero;
  `apm_t98a04_sphere_ne_zero` is compiled.
* The base point `[1:0]` is represented by a nonzero vector.
* Scalar normalization has no zero-norm branch because every source vector
  has norm one.
* A hypothetical section cannot evade the obstruction by an empty domain:
  `CP¹` contains `[1:0]`.

The topology worklists contain no dedicated `t98A04` producer.  Their nearest
Hopf entries concern the different invariant-surface problem `t95J06` and do
not prove any contract below.  The solve loop's recorded exact residual agrees
that the missing items are the smooth atlas/submersion, normalized fibers, and
global no-section obstruction.

## Reused compiled facts

`apm_t98a04_sphere_ne_zero` proves that a unit-sphere point is nonzero.
`apm_t98a04_continuous_hopf` factors the map through the coinduced quotient
topology and is sorry-free.  The blueprint imports the sorry-free
`ConstructionTargets.ComplexProjectiveChartTargets`, whose affine-coordinate
definitions and proved inverse/source facts are the closest existing start for
the target atlas.

## Split of the two remaining LIBRARY lemmas

The three fibre lemmas are now proved and are not queue items.  The two former
300-line bridges have been replaced by seven seat-sized leaves.  Every leaf is
a top-level theorem whose entire body is `sorry`; the old bridge names are
sorry-free assemblies.

| Queue order | Leaf | Work and named tools | Estimate | Inputs | LIBRARY |
|---:|---|---|---:|---|---|
| 1 | `apm_t98a04_no_section_aux_homology_factor` | Apply rational singular homology to `hopf ∘ i = id`; use `Functor.map_comp`, `Functor.map_id`, `IsZero.eq_of_src`, and `IsZero.iff_id_eq_zero`. | 25–45 | nonzero base H₂; zero total H₂ | no |
| 2 | `apm_t98a04_no_section_aux_s3_h2_zero` | Restrict the canonical real-linear isometry `ℂ² ≃ₗᵢ[ℝ] ℝ⁴` to spheres and transport sphere homology vanishing from `SphereHomology.sphereModuleHomology_isZero_of_ne_zero_top` (with coefficient change to `ℚ`). | 50–90 | definitions | no |
| 3 | `apm_t98a04_no_section_aux_cp1_h2_nonzero` | Identify the file's `WithLp` quotient with `ProjectiveSpaceTopology.Space ℂ 1`, use `RP3Homology.cpU_homology_aux_CP1_hequiv_S2` from `CP2RationalHomology.lean`, and transport `CoefficientSphereEndpoints.rationalS2H2`. | 80–120 | definitions | no |
| 4 | `apm_t98a04_submersion_aux_affine_atlas` | Construct the two exact ratio charts using `affineSource_isOpen`, quotient descent, and the explicit `[1:w]`/`[w:1]` inverses recorded by `apm_t98a04_IsStandardAffineAtlas`. | 100–140 | coordinate definitions | no |
| 5 | `apm_t98a04_submersion_aux_affine_isManifold` | Check the two chart transitions; the only nonidentity overlap is complex inversion. Use `contDiffOn_inv₀`, real/complex coordinate smoothness, and the compatible-atlas manifold constructor. | 50–90 | affine atlas witness | no |
| 6 | `apm_t98a04_submersion_aux_hopf_smooth` | In each target chart the Hopf map is a homogeneous-coordinate quotient. Combine Mathlib's standard sphere charts with smooth division on the patch where the denominator is nonzero. | 90–130 | affine atlas; manifold compatibility | no |
| 7 | `apm_t98a04_submersion_aux_mfderiv_surjective` | Differentiate the ratio formula. Use Mathlib's `range_mfderiv_coe_sphere` and `mfderiv_coe_sphere_injective`; the two real directions in the unused complex coordinate map onto the target. | 120–150 | affine atlas; manifold compatibility; Hopf smoothness | no |

No leaf is estimated above 150 lines, so no unresolved LIBRARY item remains.
The CP¹ route is cheaper than rebuilding its homology: the existing CP² file
already constructs a homotopy equivalence from its literal `CP 1` to the
repository's standard two-sphere.  The only new identification is the
real-linear isometry between this file's `WithLp` homogeneous vectors and the
plain `Fin 2 → ℂ` carrier used there.

## Assemblies and dependency layers

* **Layer 1 (parallel):** `..._s3_h2_zero`, `..._cp1_h2_nonzero`, and
  `..._affine_atlas`.
* **Layer 2 (parallel):** `..._homology_factor` (takes both homology facts as
  explicit hypotheses) and `..._affine_isManifold` (takes the atlas witness).
* **Layer 3:** `..._hopf_smooth` (takes atlas and manifold facts).
* **Layer 4:** `..._mfderiv_surjective` (also takes smoothness explicitly).
* **Layer 5:** sorry-free `apm_t98a04_no_section_bridge` and
  `apm_t98a04_submersion_bridge` assemblies.
* **Layer 6:** the pre-existing `apm_t98a04` assembly.

Witnesses are passed forward explicitly: no leaf re-obtains an existential
atlas from a sibling.  The atlas predicate fixes the actual ratio coordinates
and inverse maps, rather than permitting an unrelated charted space.

## C1–C10 review record

* **`..._homology_factor`:** C1 functorial factorisation is valid for the exact
  concrete maps; C2 the two homology hypotheses do not state the no-section
  conclusion; C3 only the categorical contradiction remains; C4 composition
  closes from `hopf (i p)=p`; C5 the maps are the consumer's `hopf` and section;
  C6–C7 rational coefficients and degree 2 preserve the source conclusion;
  C8 an empty base is excluded indirectly by nonzero H₂; C9 strictly weaker
  than the old bridge because it requires computed homology facts; C10 matches.
* **`..._s3_h2_zero`:** C1 checked against `H₂(S³)=0`; C2 computes rather than
  assumes vanishing; C3 one carrier/isometry transport; C4–C5 returns exactly
  the H₂ object consumed by the factor leaf; C6 rational coefficients are
  allowed; C7 `S3` is Mathlib's fixed metric sphere; C8 `(1,0)` is a point and
  zero is excluded; C9 not the no-section ancestor; C10 matches.
* **`..._cp1_h2_nonzero`:** C1 follows from `CP¹≃S²` and checked repository
  endpoints; C2 no chosen nonzero class is supplied; C3 only carrier and
  homotopy transport; C4–C5 its exact H₂ object feeds the factor leaf; C6
  rational coefficients are allowed; C7 uses the coinduced topology already
  fixed in the registered statement; C8 `[1:0]` prevents emptiness; C9 does
  not restate no-section; C10 matches.
* **`..._affine_atlas`:** C1 both coordinate patches cover because a nonzero
  representative has a nonzero coordinate; C2 the predicate fixes sources,
  coordinates and inverses; C3 only point-set chart construction; C4 the two
  charts cover all cases; C5 exact maps used downstream are recorded; C6 no
  source condition is added; C7 chart model is real dimension two; C8 at
  `(1,0)` chart zero is defined and equals zero; C9 not the old submersion
  theorem; C10 matches.
* **`..._affine_isManifold`:** C1 transitions are identity or `w↦w⁻¹` away
  from zero; C2 receives only the fixed atlas data; C3 compatibility only;
  C4 two-by-two overlaps exhaust the atlas; C5 returns the exact instance
  consumed later; C6–C7 smoothness order is `⊤ : ℕ∞`; C8 empty overlap is
  harmless and inversion excludes zero; C9 not the ancestor; C10 matches.
* **`..._hopf_smooth`:** C1 ratio maps are smooth on nonzero-denominator
  patches; C2 smoothness is not assumed; C3 does not include derivative rank;
  C4 the two target patches cover; C5 it uses the fixed atlas and exact Hopf
  map; C6–C7 source is Mathlib's standard sphere atlas and order is analytic
  `⊤`; C8 at `(1,0)` the formula is `z₁/z₀`; C9 only one conjunct of the old
  bridge; C10 matches.
* **`..._mfderiv_surjective`:** C1 at `(1,0)`, tangent vectors `(0,1)` and
  `(0,I)` map to the two real basis directions, and the symmetric chart covers
  `(0,1)`; C2 surjectivity is computed, not passed in; C3 only the rank
  calculation remains; C4 every point has a nonzero coordinate; C5 the
  derivative is that of the registered Hopf map under the fixed atlases; C6
  no stronger hypothesis than the constructed smooth structure is added; C7
  `range_mfderiv_coe_sphere` identifies the actual manifold tangent carrier;
  C8 radial and phase directions are distinguished, including coordinate-axis
  points; C9 it is the derivative conjunct rather than the full ancestor; C10
  matches.

## Compilation, registry and axioms

The skeleton is compiled through the required lock and 12G systemd scope.
The expected seven `sorry` warnings are exactly the seven leaves above.  The
bridge assemblies and main assembly contain no direct `sorry`.

```text
errors: 0
sorry warnings: 7
'apm_t98a04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`python3 scripts/statement-registry.py check t98A04` reports:

```text
1 registered statements match, 0 do not
```
