# t95J02 reroute: use a separating ambient map, not fiber classification

## Exact stall in the old route

The old route first tried to construct
`circleB_homeo : euclideanUnitSphere 2 ≃ₜ t95J02CircleB`.  Its forward map is
the period-one parametrization `y ↦ [(0,y)]`.  The attempted inverse was
described as the restriction of

```
[(x,y)] ↦ (cos (2πy), sin (2πy) * cos (πx)).
```

The loop stopped while trying to prove the inverse law by classifying equality
of vertical representatives in `Relation.EqvGen t95J02KleinRel`: from
`[(0,y)] = [(0,y')]`, derive `y-y' ∈ ℤ`.  No normal-form/classification lemma
for this custom `EqvGen` quotient was available.  Consequently the sphere-to-B
homeomorphism was not built, so the reflection homotopy and the H1 kernel
witness never became typeable.  The other two sorries were untouched.

There is also a small correction to the prose of the old route: the displayed
formula does **not** land in the unit circle on all of the Klein bottle (for
example `x=1/2, y=1/4` gives `(0,0)`).  It lands in `ℝ²`; only its restriction
to `CircleB` lands in the unit circle.

## New route

The displayed formula avoids the missing classification when used at the
right codomain.  Descend it as a continuous map `sep : KleinBottle → ℝ × ℝ`.
Its restriction to B is the standard trigonometric coordinate of a vertical
representative.  Thus it is a continuous inverse to the period-one
parametrization, and the inverse laws can be proved after destructing the
*existing witness* in the definition of `CircleB`; no converse theorem about
`EqvGen` is needed.

Ordered implementation steps:

1. **Separating map (about 45 lines; supplies the replacement for the stalled
   fiber-classification step).** Define
   `sepRaw (x,y) = (cos (2*pi*y), sin (2*pi*y) * cos (pi*x))`.  Prove directly
   that it is unchanged by `vertical` and `glide`, extend through
   `Relation.EqvGen.rec`, and descend with `Quotient.lift`.  Prove continuity
   with `Continuous.quotient_lift`.  This part was compiled in the probe below.

2. **CircleB homeomorphism without normal forms (about 70--100 lines; supplies
   the geometric input to `apm_t95J02_bridge_vertical_H1_kernel`).** It is
   cleanest to define the period-one parametrization first from `AddCircle 1`
   by quotient lifting `y ↦ ⟨[(0,y)], y, rfl⟩`, then conjugate it by
   `AddCircle.homeomorphCircle`/the banked
   `circleHomeomorphSphereOne` to get a map from `euclideanUnitSphere 2`.
   Define the inverse on `z : CircleB` by applying `sep z.1`; after
   `rcases z.2 with ⟨y, rfl⟩`, its norm-one proof is `sin_sq_add_cos_sq`,
   and both inverse laws reduce to the standard AddCircle/circle homeomorphism
   simp lemmas.  In particular, do **not** prove that equal vertical quotient
   representatives differ by an integer: `sep` supplies the required
   coordinate before either inverse law is considered.

3. **Glide homotopy (about 35--55 lines; remaining geometric part of the first
   sorry).** With the same standard parametrization `beta : S¹ ⟶ B ⟶ K`,
   use `(t,u) ↦ [(t, y(u))]`.  At `t=0` it is `beta`; at `t=1`, the glide
   identity gives `[(1,y)] = [(0,-y)]`, hence `beta ∘ reflectionMap`.
   Build this first on `AddCircle 1`, where the quotient lift removes any
   choice of angle, and transport across the standard circle/sphere
   homeomorphism.  Continuity follows from the quotient/coinduced API already
   used for the positive retraction.

4. **Fill `apm_t95J02_bridge_vertical_H1_kernel` (about 25--40 lines).** Let
   `g := (CoefficientFirstReflection.topIso ℤ 0).inv 1` and let `gamma` be
   the image of `2 • g` under the homeomorphism into B.  It is nonzero because
   `topIso` sends it to `2 : ℤ`.  Apply
   `SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic` to step 3,
   `Functor.map_comp`, and
   `CoefficientFirstReflection.all_reflections_negative ℤ 1 (by decide)`.
   The equation `beta_* = beta_* ∘ (-id)` gives `beta_*(2g)=0`.

5. **Fill `apm_t95J02_bridge_retraction_injective` (about 8--15 lines).** From
   `⟨r, i ≫ r = 𝟙⟩`, map the equality through the singular-homology
   functor, rewrite with `Functor.map_comp`, and use the resulting left inverse
   of `H₁(i)` to prove `Function.Injective` by applying `H₁(r)` to an
   equality.  This step is independent of the custom quotient.

6. **Fill the final sorry (about 6--10 lines).** Obtain the nonzero kernel
   witness from step 4 and injectivity from step 5; injectivity turns its zero
   image into `gamma = 0`, contradicting `gamma ≠ 0`.  Reuse the already closed
   positive conjunct verbatim.

## Compiled probe

File: `/tmp/reroute-t95J02/Probe.lean`

Command:

```
cd /home/joe/code/apm-lean && lake env lean /tmp/reroute-t95J02/Probe.lean
```

Result: exit 0.  The probe recreates the concrete quotient, proves both
generator invariances by trigonometric simplification, extends them through
`Relation.EqvGen.rec`, defines the quotient lift `KF : K → ℝ × ℝ`, and proves
its continuity using `Continuous.quotient_lift`.  This compiles the new route's
riskiest and genuinely new step: the ambient separating map that removes the
need for vertical-fiber normal forms.

## Confidence

**Medium-high (0.8).** The precise replacement for the prior blocker compiles,
and the inverse laws now reduce to witnesses already stored in the subtype
rather than an absent quotient classification.  The remaining uncertainty is
API-level work in transporting the explicit AddCircle homotopy to the banked
Euclidean-sphere reflection theorem; the mathematics and all quotient
well-definedness needed for that transport are explicit, and the bank already
contains both the circle/sphere homeomorphism and the reflection action.
