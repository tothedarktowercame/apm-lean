# t95J02 closure blueprint

This closure foundation follows the `t95J02` closer audit, steps
`t95J02CircleB_homeo`, `t95J02_beta_homotopic_beta_reflection`,
`apm_t95J02_bridge_vertical_H1_kernel`, and
`apm_t95J02_bridge_retraction_injective`.  It closes the three remaining
placeholders in `problems/t95J02/lean/Main.lean` without changing the
registered theorem `apm_t95j02`.

The representation is the frozen quotient
`Quotient (Relation.EqvGen.setoid t95J02KleinRel)` with its coinduced
topology.  The blueprint uses the existing quotient identities
`t95J02QuotientPoint_vertical`, `t95J02QuotientPoint_glide`, and
`t95J02QuotientPoint_glide_vertical_inverse`; Mathlib's quotient universal
property, compact-to-Hausdorff homeomorphism criterion, and functor laws; and
the banked `CoefficientFirstReflection.integral_circle`,
`CoefficientFirstReflection.topIso`, and
`SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic`.

### B1. Separating coordinate respects the generators

lean: `t95J02Closure.separatingRaw` : `ℝ × ℝ → EuclideanSpace ℝ (Fin 2)` and
`t95J02Closure.separatingRaw_generator` :
`t95J02KleinRel p q → separatingRaw p = separatingRaw q`.

uses: real continuity and trigonometric periodicity lemmas

status: proved

Set
`separatingRaw (x,y) = ![Real.cos (2 * π * y),
Real.sin (2 * π * y) * Real.cos (π * x)]`.
It is continuous.  For the vertical generator, add `2π` to the trigonometric
argument.  For the glide generator `(x,y) ↦ (x+1,-y)`, cosine is even while
both sine factors change sign, so their product is unchanged.  Prove both
coordinates separately with `Fin.isValue` extensionality and the standard
`sin_add_int_mul_two_pi`, `cos_add_int_mul_two_pi`, `sin_neg`, `cos_neg`, and
`cos_add_pi` identities.

### B2. Descend the separating coordinate

lean: `t95J02Closure.separatingMap` :
`C(t95J02KleinBottleType, EuclideanSpace ℝ (Fin 2))`.

uses: B1, `Relation.EqvGen.rec`, `Continuous.quotient_lift`

status: proved

Extend B1 from generators through reflexivity, symmetry, and transitivity of
`Relation.EqvGen`.  Use `Quotient.lift separatingRaw` for the function.  Its
continuity follows from continuity of B1's raw map and the coinduced quotient
topology, exactly as in the already compiled `t95J02RetractionA` descent.

### B3. The vertical real parametrization

lean: `t95J02Closure.verticalParam` : `C(ℝ, t95J02CircleB)` with
`verticalParam y = ⟨t95J02QuotientPoint (0,y), ⟨y,rfl⟩⟩`, and
`t95J02Closure.verticalParam_add_int` :
`∀ (y : ℝ) (n : ℤ), verticalParam (y+n) = verticalParam y`.

uses: `t95J02QuotientPoint_vertical`, continuity of the quotient map

status: proved

Continuity is the quotient map composed with `y ↦ (0,y)`, followed by the
subtype constructor.  Prove integer periodicity first for natural numbers by
induction using the vertical identity, then for negative integers by symmetry
and cancellation.

### B4. Classify fibers on the vertical core

lean: `t95J02Closure.verticalParam_eq_iff` :
`verticalParam y = verticalParam y' ↔ ∃ n : ℤ, y' = y + n`.

uses: B2, B3, `Real.cos_eq_cos`, `Real.sin_eq_sin`

status: proved

The reverse implication is B3.  For the forward implication, apply B2 to the
subtype equality.  At representatives `(0,y)` and `(0,y')`, B1's second
coordinate simplifies because `cos 0 = 1`; hence both cosine and sine of
`2πy` and `2πy'` agree.  Combine the two trigonometric equalities to exclude
the reflected branch and obtain `2πy' = 2πy + 2πn`; cancel the nonzero factor
`2π`.  This proof uses no unproved classification of the full Klein
equivalence relation.

### B5. Homeomorphism from the standard circle to CircleB

lean: `t95J02Closure.t95J02CircleB_homeo` :
`euclideanUnitSphere 2 ≃ₜ t95J02CircleB`.

uses: B2, B3, B4,
`CircleHomology.circleHomeomorphSphereOne`,
`AddCircle.homeomorphCircle (T := 1) one_ne_zero`,
`isQuotientMap_quotient_mk'`, and `Continuous.homeoOfEquivCompactToT2`

status: proved

Use B3's integer-periodic map to descend from `ℝ` to `AddCircle 1` by
`Function.Periodic.lift`, with continuity obtained from
`isQuotientMap_quotient_mk'`.  Transport the domain along
`AddCircle.homeomorphCircle one_ne_zero`; its formula is
`y ↦ (cos 2πy, sin 2πy)`.  B4 proves injectivity, while every element of
`CircleB` has a witness `y`, giving surjectivity.
For the inverse, restrict B2 to `CircleB`; its value there is exactly
`(cos 2πy, sin 2πy)` and lies on `euclideanUnitSphere 2`.  Thus the inverse is
continuous without requiring the ambient Klein quotient to be Hausdorff.
Transport between Mathlib's complex `Circle` and the Euclidean sphere with
`circleHomeomorphSphereOne`.  Alternatively, after the continuous bijection
is obtained, use compactness of the sphere and the Hausdorff topology inherited
by `CircleB` through the separating inverse.

### B6. Reflection homotopy of the vertical inclusion

lean: `t95J02Closure.t95J02_beta_homotopic_beta_reflection` :
for `β := t95J02InclusionB.comp t95J02CircleB_homeo.toContinuousMap`,
`ContinuousMap.Homotopic β
  (β.comp (CoefficientCoordinateReflections.reflectionMap (1 : Fin 2)))`.

uses: B3, B4, B5, `t95J02QuotientPoint_glide`,
`AddCircle.homeomorphCircle (T := 1) one_ne_zero`,
`isQuotientMap_quotient_mk'`, `IsQuotientMap.lift`

status: proved

Choose a real lift `y` of a point on the source circle only inside the
periodic quotient construction used in B5.  Define the homotopy by
`H(t,u) = t95J02QuotientPoint (t,y)`.  Changing `y` by an integer does not
change the quotient point by the vertical identity, so the formula descends
continuously.  At `t=0` it is `β`.  At `t=1`, the glide equality identifies
`[(1,y)]` with `[(0,-y)]`, which is the second-coordinate reflection of the
Euclidean circle under B5's cosine/sine coordinate: it fixes `cos (2πy)` and
negates `sin (2πy)`, hence is `reflectionMap (1 : Fin 2)`.

Implemented: `verticalSweepHomotopy` performs this descent and proves the two
endpoints on `AddCircle 1`; `sphereToAddCircle_reflection` identifies additive
negation with coordinate-1 reflection, and the final theorem transports the
homotopy through B5.

### B7. Nonzero vertical class killed in the Klein bottle

lean: `t95J02Closure.apm_t95J02_bridge_vertical_H1_kernel` :
`∃ gamma : apm_t95J02_H1 t95J02CircleB, gamma ≠ 0 ∧
 apm_t95J02_H1Map t95J02InclusionB gamma = 0`.

uses: B5, B6, `CoefficientFirstReflection.topIso`,
`CoefficientFirstReflection.integral_circle`,
`CoefficientCoordinateReflections.reflectionMap`,
`SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic`,
Mathlib `Functor.map_comp`

status: planned

Let `g` be the inverse image of `1 : ℤ` under the integral H1 isomorphism of
the Euclidean circle and let `gamma` be the image of `2 • g` under the H1
isomorphism induced by B5.  It is nonzero because its integer coordinate is
`2`.  B6 and homotopy invariance give
`H₁(β) = H₁(CoefficientCoordinateReflections.reflectionMap (1 : Fin 2)) ≫
H₁(β)`.  Instantiate
`CoefficientFirstReflection.integral_circle` at coordinate `1`; it replaces
the first factor by `-𝟙`, so `H₁(β)(g) = H₁(β)(-g)`.  By additivity this is
`H₁(β)(g) = -H₁(β)(g)`, hence `H₁(β)(2 • g)=0`.
Rewrite `β` as B5 followed by `t95J02InclusionB` and cancel the B5
isomorphism to obtain the required equation.

### B8. Retractions induce injective H1 maps

lean: `t95J02Closure.apm_t95J02_bridge_retraction_injective` :
`HasT95J02Retraction t95J02InclusionB →
 Function.Injective (apm_t95J02_H1Map t95J02InclusionB)`.

uses: Mathlib `Functor.map_comp`, `Functor.map_id`

status: planned

Unpack a retraction `r` and the equality
`t95J02InclusionB ≫ r = 𝟙 _`.  Apply the singular-homology functor to this
equality and rewrite by the functor laws.  If the inclusion maps `x` and `y`
to the same class, apply `H₁(r)` and simplify both sides with the mapped
retraction equation.

### B9. Frozen theorem closure

lean: `apm_t95j02` in `problems/t95J02/lean/Main.lean`, with its registered
type unchanged and no `sorry`.

uses: B7, B8, the existing `t95J02RetractionA` and
`t95J02RetractionA_comp_inclusion`

status: planned

The positive conjunct is the existing explicit retraction.  For the negative
conjunct, assume a retraction onto `CircleB`, obtain the nonzero `gamma` from
B7, and apply injectivity from B8 to the equality between its zero image and
the image of zero.  This forces `gamma = 0`, contradicting B7.
