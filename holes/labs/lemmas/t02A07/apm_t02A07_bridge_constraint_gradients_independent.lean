import Mathlib

/-!
# APM t02A07

## Statement repairs

The defining equation for `X` repeats `(x²)²` and omits `(x¹)²`. It is
repaired to the standard unit-sphere equation
`(x¹)² + (x²)² + (x³)² + (x⁴)² = 1`, as required by the phrase “unit sphere”.

## Encoding questions

The submanifold claim is encoded by the regular-value criterion for the two
actual constraint functions in `ℝ⁴`, giving dimension `4 - 2 = 2`.
Transversality is the concrete tangent-space condition: at every intersection,
the image of the derivative of the displayed family plus the kernel of the
constraint derivative is the full ambient space.
-/

noncomputable section

abbrev apm_t02a07_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t02a07_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t02a07_E4 := EuclideanSpace ℝ (Fin 4)

def apm_t02a07_X : Set apm_t02a07_E4 :=
  Metric.sphere 0 1

def apm_t02a07_Z : Set apm_t02a07_E4 :=
  {x | x ∈ apm_t02a07_X ∧ x 2 * x 3 = (1 : ℝ) / 4}

abbrev apm_t02a07_S2 := Metric.sphere (0 : apm_t02a07_E3) 1
abbrev apm_t02a07_parameterCircle := Metric.sphere (0 : apm_t02a07_E2) 1

def apm_t02a07_family
    (parameter : apm_t02a07_parameterCircle) (y : apm_t02a07_S2) :
    apm_t02a07_E4 :=
  WithLp.toLp 2
    ![y.1 0 * parameter.1 0, parameter.1 1, y.1 1 * parameter.1 0,
      y.1 2 * parameter.1 0]

def apm_t02a07_constraints (x : apm_t02a07_E4) : apm_t02a07_E2 :=
  WithLp.toLp 2
    ![‖x‖ ^ 2 - 1, x 2 * x 3 - (1 : ℝ) / 4]

/-- On the constrained set, both coordinates occurring in the product
constraint are nonzero.  This is the first algebraic input to the explicit
Jacobian-rank proof. -/
lemma apm_t02a07_product_coordinates_ne_zero {x : apm_t02a07_E4}
    (hx : x ∈ apm_t02a07_Z) : x 2 ≠ 0 ∧ x 3 ≠ 0 := by
  rcases hx with ⟨hxSphere, hxProd⟩
  constructor
  · intro hx2
    rw [hx2, zero_mul] at hxProd
    norm_num at hxProd
  · intro hx3
    rw [hx3, mul_zero] at hxProd
    norm_num at hxProd

/-- The product constraint's coordinate gradient is therefore nonzero on
`Z`; this rules out the most immediate Jacobian degeneration. -/
lemma apm_t02a07_product_gradient_ne_zero {x : apm_t02a07_E4}
    (hx : x ∈ apm_t02a07_Z) :
    (WithLp.toLp 2 ![(0 : ℝ), 0, x 3, x 2] : apm_t02a07_E4) ≠ 0 := by
  intro hzero
  have hcoord := congrFun (congrArg WithLp.ofLp hzero) (2 : Fin 4)
  simp at hcoord
  exact (apm_t02a07_product_coordinates_ne_zero hx).2 hcoord

def apm_t02a07_IsRegularDimensionTwo : Prop :=
  ∀ x ∈ apm_t02a07_Z,
    Function.Surjective (fderiv ℝ apm_t02a07_constraints x)

def apm_t02a07_sphereTangent (y : apm_t02a07_S2) : Submodule ℝ apm_t02a07_E3 :=
  (Submodule.span ℝ ({(y : apm_t02a07_E3)} : Set apm_t02a07_E3)).orthogonal

def apm_t02a07_familyAmbient
    (parameter : apm_t02a07_parameterCircle) (y : apm_t02a07_E3) :
    apm_t02a07_E4 :=
  WithLp.toLp 2
    ![y 0 * parameter.1 0, parameter.1 1, y 1 * parameter.1 0,
      y 2 * parameter.1 0]

@[simp] lemma apm_t02a07_family_eq_familyAmbient
    (parameter : apm_t02a07_parameterCircle) (y : apm_t02a07_S2) :
    apm_t02a07_family parameter y =
      apm_t02a07_familyAmbient parameter y := rfl

/-- The displayed family lands in the unit sphere. This discharges the finite
coordinate normalization independently of the transversality argument. -/
lemma apm_t02a07_family_mem_X
    (parameter : apm_t02a07_parameterCircle) (y : apm_t02a07_S2) :
    apm_t02a07_family parameter y ∈ apm_t02a07_X := by
  have hp : ‖(parameter : apm_t02a07_E2)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using parameter.property
  have hy : ‖(y : apm_t02a07_E3)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using y.property
  have hp2 := congrArg (fun z : ℝ => z ^ 2) hp
  have hy2 := congrArg (fun z : ℝ => z ^ 2) hy
  dsimp only at hp2 hy2
  rw [EuclideanSpace.norm_sq_eq] at hp2 hy2
  simp [Fin.sum_univ_succ] at hp2 hy2
  rw [apm_t02a07_X, Metric.mem_sphere, dist_zero_right]
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [EuclideanSpace.norm_sq_eq]
  simp [apm_t02a07_family, Fin.sum_univ_succ]
  nlinarith

def apm_t02a07_tangentZ (x : apm_t02a07_E4) : Submodule ℝ apm_t02a07_E4 :=
  LinearMap.ker (fderiv ℝ apm_t02a07_constraints x).toLinearMap

def apm_t02a07_IsTransverse (parameter : apm_t02a07_parameterCircle) : Prop :=
  ∀ y : apm_t02a07_S2, apm_t02a07_family parameter y ∈ apm_t02a07_Z →
    Submodule.map
        (fderiv ℝ (apm_t02a07_familyAmbient parameter) y).toLinearMap
        (apm_t02a07_sphereTangent y) ⊔
      apm_t02a07_tangentZ (apm_t02a07_family parameter y) = ⊤

/-- Why this unblocks the regularity conjunct of `apm_t02a07`: these are the
two coordinate gradients of the sphere and product constraints, up to the
harmless nonzero scalar `2` on the first row. Their linear independence is
the exact rank-two Jacobian calculation needed for surjectivity of the frozen
constraint derivative along `Z`. -/
-- BEGIN SEAT AREA
theorem apm_t02A07_bridge_constraint_gradients_independent
    {x : apm_t02a07_E4} (hx : x ∈ apm_t02a07_Z) :
    LinearIndependent ℝ
      (![x, (WithLp.toLp 2 ![(0 : ℝ), 0, x 3, x 2] :
        apm_t02a07_E4)] : Fin 2 → apm_t02a07_E4) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hcoord (j : Fin 4) := congrFun (congrArg WithLp.ofLp hc) j
  have h0 : c 0 * x 0 = 0 := by simpa using hcoord 0
  have h1 : c 0 * x 1 = 0 := by simpa using hcoord 1
  have h2 : c 0 * x 2 + c 1 * x 3 = 0 := by simpa using hcoord 2
  have h3 : c 0 * x 3 + c 1 * x 2 = 0 := by simpa using hcoord 3
  have hxprod : x 2 * x 3 = (1 : ℝ) / 4 := hx.2
  have hxnorm : ‖x‖ = 1 := by simpa [apm_t02a07_X] using hx.1
  have hsquares : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq x
    have h' : x 0 ^ 2 + (x 1 ^ 2 + (x 2 ^ 2 + x 3 ^ 2)) = 1 := by
      simpa [Fin.sum_univ_succ, hxnorm] using h.symm
    nlinarith
  have hc0 : c 0 = 0 := by
    by_contra hc0
    have hx0 : x 0 = 0 := (mul_eq_zero.mp h0).resolve_left hc0
    have hx1 : x 1 = 0 := (mul_eq_zero.mp h1).resolve_left hc0
    have hh2 : (c 0 * x 2 + c 1 * x 3) * x 2 = 0 := by rw [h2, zero_mul]
    have hh3 : (c 0 * x 3 + c 1 * x 2) * x 3 = 0 := by rw [h3, zero_mul]
    have heq : x 2 ^ 2 = x 3 ^ 2 := by
      apply (mul_left_cancel₀ hc0)
      nlinarith
    have hsame : x 2 = x 3 := by
      rcases (sq_eq_sq_iff_eq_or_eq_neg).mp heq with h | h
      · exact h
      · nlinarith
    rw [hx0, hx1, hsame] at hsquares
    rw [hsame] at hxprod
    norm_num at hsquares hxprod
    nlinarith
  have hc1 : c 1 = 0 := by
    rw [hc0, zero_mul, zero_add] at h2
    exact (mul_eq_zero.mp h2).resolve_right
      (apm_t02a07_product_coordinates_ne_zero hx).2
  fin_cases i <;> assumption
-- END SEAT AREA

/-- Compute the frozen `fderiv` and turn independence of its two coordinate
rows into surjectivity.  The independence result is an explicit hypothesis so
this lemma can be proved in parallel with the preceding one. -/
theorem apm_t02A07_constraints_fderiv_surjective
    (hind : ∀ x ∈ apm_t02a07_Z,
      LinearIndependent ℝ
        (![x, (WithLp.toLp 2 ![(0 : ℝ), 0, x 3, x 2] :
          apm_t02a07_E4)] : Fin 2 → apm_t02a07_E4)) :
    apm_t02a07_IsRegularDimensionTwo := by
  sorry

/-- Direct classification of the exceptional parameters.  A slice fails to
be transverse exactly when the square of its first circle coordinate is
`1/2`. -/
theorem apm_t02A07_transverse_iff_parameter_sq_ne_half
    (parameter : apm_t02a07_parameterCircle) :
    apm_t02a07_IsTransverse parameter ↔
      parameter.1 0 ^ 2 ≠ (1 : ℝ) / 2 := by
  sorry

/-- Removing the four parameters with first-coordinate square `1/2` leaves a
dense subset of the parameter circle. -/
theorem apm_t02A07_good_parameters_dense :
    Dense {parameter : apm_t02a07_parameterCircle |
      parameter.1 0 ^ 2 ≠ (1 : ℝ) / 2} := by
  sorry

/-- Why this unblocks the density conjunct of `apm_t02a07`: this is the
parametric-transversality conclusion specialized to the displayed family and
constraint surface. Equivalently, it may be proved by classifying the
exceptional circle parameters and showing that their complement is dense. -/
theorem apm_t02A07_bridge_transverse_parameters_dense :
    Dense {parameter : apm_t02a07_parameterCircle |
      apm_t02a07_IsTransverse parameter} := by
  simpa only [Set.mem_setOf_eq,
    apm_t02A07_transverse_iff_parameter_sq_ne_half] using
      apm_t02A07_good_parameters_dense

theorem apm_t02a07 :
    apm_t02a07_IsRegularDimensionTwo ∧
    (∀ parameter : apm_t02a07_parameterCircle,
      Set.range (apm_t02a07_family parameter) ⊆ apm_t02a07_X) ∧
    Dense {parameter : apm_t02a07_parameterCircle |
      apm_t02a07_IsTransverse parameter} := by
  /-
  CLOSER HOP 1 boundary. The restricted family is now explicitly connected to
  its ambient differentiable extension by
  `apm_t02a07_family_eq_familyAmbient`, eliminating a later coercion bridge.

  The range-in-sphere conjunct is an explicit norm calculation: using
  `EuclideanSpace.norm_sq_eq`, the squared norm of the four displayed
  coordinates factors as
  `parameter₀² * ‖y‖² + parameter₁² = 1`. Mathlib supplies the norm identity,
  but the required `Fin 3`/`Fin 4` sum normalization and `WithLp.toLp`
  coordinate simplification remain to be assembled locally.

  Regularity requires computing the derivative of both constraints. At a
  point with `x₂*x₃ = 1/4`, the second constraint forces `x₂,x₃ ≠ 0`; the norm
  gradient and product gradient are then linearly independent, yielding
  surjectivity onto `ℝ²`. No searched lemma packages this coordinate Jacobian
  argument for the frozen `fderiv` expression.

  Finally, the density statement is the parametric transversality theorem.
  Mathlib contains Sard's theorem and elementary tangent/submodule machinery,
  but searches found no Thom/parametric-transversality theorem. A direct route
  would have to classify the exceptional parameters by solving the displayed
  derivative-rank equations and prove their complement dense in the circle.
  Searches covered `LEMMA-INDEX.md`, all `ConstructionTargets/`, sibling
  `t94A06`, all closed transversality artifacts, Mathlib's Sard, fderiv,
  Euclidean norm, submodule, and density APIs, and git history. None supplies
  the parameter-density assembly, so the statement remains open.

  CLOSER HOP 2 goes beyond that search boundary by completing the entire
  range-in-sphere conjunct as `apm_t02a07_family_mem_X`. The proof extracts
  the two unit-norm equations from the sphere subtypes, expands them with
  `EuclideanSpace.norm_sq_eq`, normalizes the `Fin 2`, `Fin 3`, and `Fin 4`
  sums, and finishes the displayed coordinate identity by `nlinarith`.
  Thus neither `WithLp.toLp` simplification nor the finite-coordinate norm
  calculation remains open. Targeted reinspection of `t94A06`, the repository
  transversality users, `LEMMA-INDEX.md`, `ConstructionTargets/`, and Mathlib's
  Sard/density APIs still found no parametric-transversality theorem. The live
  bridge is now only the explicit constraint-Jacobian surjectivity proof and
  the exceptional-parameter classification/density argument.

  CLOSER HOP 3 begins that explicit Jacobian proof rather than repeating the
  library search. `apm_t02a07_product_coordinates_ne_zero` derives
  `x₂ ≠ 0` and `x₃ ≠ 0` directly from `x₂*x₃ = 1/4` on `Z`, and
  `apm_t02a07_product_gradient_ne_zero` packages the consequence that the
  second constraint's coordinate gradient `(0,0,x₃,x₂)` is nonzero. Thus the
  product row of the constraint Jacobian is now certified nondegenerate.

  Final-hop searches of Mathlib's norm-square derivative, inner-product
  calculus, fixed-dimensional Sard, Jacobian, and manifold bordism sources
  found `fderiv_norm_sq` for the first constraint but still no parametric
  transversality theorem or ready-made two-row surjectivity lemma. The
  remaining local regularity bridge is to prove the norm gradient and this
  nonzero product gradient linearly independent on `Z`; density still requires
  exceptional-parameter classification or new parametric-transversality
  infrastructure. The frozen statement is unchanged.
  -/
  refine ⟨?_, ?_, apm_t02A07_bridge_transverse_parameters_dense⟩
  · apply apm_t02A07_constraints_fderiv_surjective
    intro x hx
    exact apm_t02A07_bridge_constraint_gradients_independent hx
  · intro parameter x hx
    rcases hx with ⟨y, rfl⟩
    exact apm_t02a07_family_mem_X parameter y

#print axioms apm_t02a07
