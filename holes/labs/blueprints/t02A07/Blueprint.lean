import Mathlib

/-!
# APM t02A07

## Statement repairs

The defining equation for `X` repeats `(x²)²` and omits `(x¹)²`. It is
repaired to the standard unit-sphere equation
`(x¹)² + (x²)² + (x³)² + (x⁴)² = 1`, as required by the phrase “unit sphere”.

Revised 2026-10-13 (outside grade, batch 2): transversality in `X` compares the sum of the
two tangent images with `T_xX = xᗮ`, not with all of `ℝ⁴` (both summands lie in `T_xX`, so `= ⊤`
was never satisfiable and the density claim was false). Part (a) now also states `dim Z = 2`
as `finrank (tangentZ x) = 2` at every point of `Z`.

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

/-- Tangent space of the unit sphere `X` at `x`: the orthogonal complement of `x`. -/
def apm_t02a07_tangentX (x : apm_t02a07_E4) : Submodule ℝ apm_t02a07_E4 :=
  (Submodule.span ℝ ({x} : Set apm_t02a07_E4)).orthogonal

def apm_t02a07_IsTransverse (parameter : apm_t02a07_parameterCircle) : Prop :=
  ∀ y : apm_t02a07_S2, apm_t02a07_family parameter y ∈ apm_t02a07_Z →
    Submodule.map
        (fderiv ℝ (apm_t02a07_familyAmbient parameter) y).toLinearMap
        (apm_t02a07_sphereTangent y) ⊔
      apm_t02a07_tangentZ (apm_t02a07_family parameter y) =
        apm_t02a07_tangentX (apm_t02a07_family parameter y)

/-- Why this unblocks the regularity conjunct of `apm_t02a07`: these are the
two coordinate gradients of the sphere and product constraints, up to the
harmless nonzero scalar `2` on the first row. Their linear independence is
the exact rank-two Jacobian calculation needed for surjectivity of the frozen
constraint derivative along `Z`. -/
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

/-- Compute the frozen `fderiv` and turn independence of its two coordinate
rows into surjectivity.  The independence result is an explicit hypothesis so
this lemma can be proved in parallel with the preceding one. -/
lemma apm_t02A07_constraints_fderiv_surjective_aux_formula
    (x v : apm_t02a07_E4) :
    fderiv ℝ apm_t02a07_constraints x v =
      WithLp.toLp 2 ![2 * inner ℝ x v, x 3 * v 2 + x 2 * v 3] := by
  let qfun : apm_t02a07_E4 → (Fin 2 → ℝ) := fun z j ↦
    if j = 0 then ‖z‖ ^ 2 - 1 else z 2 * z 3 - (1 : ℝ) / 4
  have hq : DifferentiableAt ℝ qfun x := by
    apply differentiableAt_pi.mpr
    intro j
    fin_cases j
    · simpa [qfun] using
        (hasStrictFDerivAt_norm_sq x).differentiableAt.sub
          (differentiableAt_const (c := (1 : ℝ)))
    · simp [qfun]
      fun_prop
  have hconstraints : apm_t02a07_constraints = WithLp.toLp 2 ∘ qfun := by
    funext z
    apply WithLp.ofLp_injective
    funext j
    fin_cases j <;> simp [apm_t02a07_constraints, qfun]
  have hc := (PiLp.hasFDerivAt_toLp (p := 2) (𝕜 := ℝ) (qfun x)).comp x
    hq.hasFDerivAt
  rw [hconstraints, hc.fderiv]
  apply congrArg (WithLp.toLp 2)
  have hcoord : ∀ j : Fin 2, DifferentiableAt ℝ (fun z ↦ qfun z j) x := by
    intro j
    fin_cases j
    · simpa [qfun] using
        (hasStrictFDerivAt_norm_sq x).differentiableAt.sub
          (differentiableAt_const (c := (1 : ℝ)))
    · simp [qfun]
      fun_prop
  rw [fderiv_pi hcoord]
  funext j
  fin_cases j
  · change (fderiv ℝ (fun z ↦ qfun z 0) x) v = 2 * inner ℝ x v
    simp only [qfun, if_pos]
    have hd := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub
      (hasFDerivAt_const (x := x) (1 : ℝ))
    have he := congrArg (fun L : apm_t02a07_E4 →L[ℝ] ℝ ↦ L v) hd.fderiv
    simpa using he
  · have h2 : DifferentiableAt ℝ (fun z : apm_t02a07_E4 ↦ z 2) x := by fun_prop
    have h3 : DifferentiableAt ℝ (fun z : apm_t02a07_E4 ↦ z 3) x := by fun_prop
    change (fderiv ℝ (fun z ↦ qfun z 1) x) v = x 3 * v 2 + x 2 * v 3
    simp only [qfun, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    have hd := (h2.hasFDerivAt.mul h3.hasFDerivAt).sub
      (hasFDerivAt_const (x := x) ((1 : ℝ) / 4))
    have he := congrArg (fun L : apm_t02a07_E4 →L[ℝ] ℝ ↦ L v) hd.fderiv
    have he2 := congrArg (fun L : apm_t02a07_E4 →L[ℝ] ℝ ↦ L v)
      (PiLp.hasFDerivAt_apply (p := 2) (𝕜 := ℝ) x (2 : Fin 4)).fderiv
    have he3 := congrArg (fun L : apm_t02a07_E4 →L[ℝ] ℝ ↦ L v)
      (PiLp.hasFDerivAt_apply (p := 2) (𝕜 := ℝ) x (3 : Fin 4)).fderiv
    simpa [add_comm, he2, he3] using he

lemma apm_t02A07_constraints_fderiv_surjective_aux_rank_aux_formula
    (x v : apm_t02a07_E4) :
    fderiv ℝ apm_t02a07_constraints x v =
      WithLp.toLp 2 ![2 * inner ℝ x v, x 3 * v 2 + x 2 * v 3] := by
  unfold apm_t02a07_constraints
  let g : apm_t02a07_E4 → (Fin 2 → ℝ) := fun z =>
    ![‖z‖ ^ 2 - 1, z 2 * z 3 - (1 : ℝ) / 4]
  have hg : DifferentiableAt ℝ g x := by
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i
    · exact ((hasFDerivAt_id x).norm_sq.sub_const _).differentiableAt
    · dsimp [g]
      fun_prop
  have hc := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (g x)).comp x hg.hasFDerivAt
  have hgv : fderiv ℝ g x v =
      ![2 * inner ℝ x v, x 3 * v 2 + x 2 * v 3] := by
    have hj (j : Fin 4) : fderiv ℝ (fun z : apm_t02a07_E4 => z j) x v = v j := by
      let P : apm_t02a07_E4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) j
      have h := P.hasFDerivAt (x := x)
      exact congrArg (fun q : apm_t02a07_E4 →L[ℝ] ℝ => q v) h.fderiv
    rw [fderiv_pi]
    · ext i
      fin_cases i
      · dsimp [g]
        rw [fderiv_sub_const, fderiv_norm_sq_apply]
        simp
      · dsimp [g]
        rw [fderiv_sub_const, fderiv_fun_mul]
        · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
          rw [hj, hj]
          ring
        all_goals fun_prop
    · intro i
      fin_cases i
      · exact ((hasFDerivAt_id x).norm_sq.sub_const _).differentiableAt
      · dsimp [g]
        fun_prop
  change fderiv ℝ (WithLp.toLp 2 ∘ g) x v = _
  rw [hc.fderiv]
  change WithLp.toLp 2 (fderiv ℝ g x v) = _
  rw [hgv]

lemma apm_t02A07_constraints_fderiv_surjective_aux_rank
    (x : apm_t02a07_E4)
    (hind : LinearIndependent ℝ
      (![x, (WithLp.toLp 2 ![(0 : ℝ), 0, x 3, x 2] :
        apm_t02a07_E4)] : Fin 2 → apm_t02a07_E4)) :
    Function.Surjective (fderiv ℝ apm_t02a07_constraints x) := by
  let A := fderiv ℝ apm_t02a07_constraints x
  let w : apm_t02a07_E4 := WithLp.toLp 2 ![(0 : ℝ), 0, x 3, x 2]
  have hadj (c : apm_t02a07_E2) :
      A.adjoint c = (2 * c 0) • x + (c 1) • w := by
    apply ext_inner_right ℝ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left]
    rw [apm_t02A07_constraints_fderiv_surjective_aux_rank_aux_formula]
    simp [w, PiLp.inner_apply, Fin.sum_univ_succ, real_inner_eq_re_inner,
      RCLike.inner_apply]
    ring
  have hi : Function.Injective A.adjoint := by
    intro c d hcd
    have hc : A.adjoint (c - d) = 0 := by
      simp [hcd]
    rw [hadj] at hc
    have hs : ∑ i : Fin 2, (![2 * (c - d) 0, (c - d) 1] i) • (![x, w] i) = 0 := by
      simpa [Fin.sum_univ_succ] using hc
    have hz := (Fintype.linearIndependent_iff.mp (by simpa [w] using hind)) _ hs
    rw [← sub_eq_zero]
    apply PiLp.ext
    intro i
    fin_cases i
    · have := hz 0
      simp at this
      simpa using this
    · simpa using hz 1
  have hr := LinearMap.finrank_range_adjoint A.toLinearMap
  have hra : Module.finrank ℝ A.adjoint.range = Module.finrank ℝ apm_t02a07_E2 :=
    LinearMap.finrank_range_of_inj hi
  have hA : Module.finrank ℝ A.toLinearMap.range = Module.finrank ℝ apm_t02a07_E2 := by
    exact hr.symm.trans hra
  exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hA)

theorem apm_t02A07_constraints_fderiv_surjective
    (hind : ∀ x ∈ apm_t02a07_Z,
      LinearIndependent ℝ
        (![x, (WithLp.toLp 2 ![(0 : ℝ), 0, x 3, x 2] :
          apm_t02a07_E4)] : Fin 2 → apm_t02a07_E4)) :
    apm_t02a07_IsRegularDimensionTwo := by
  intro x hx
  exact apm_t02A07_constraints_fderiv_surjective_aux_rank x (hind x hx)

/-- Direct classification of the exceptional parameters.  A slice fails to
be transverse exactly when the square of its first circle coordinate is
`1/2`. -/
lemma apm_t02A07_transverse_iff_parameter_sq_ne_half_aux_level
    (parameter : apm_t02a07_parameterCircle) (y : apm_t02a07_S2)
    (hy : apm_t02a07_family parameter y ∈ apm_t02a07_Z) :
    parameter.1 0 ^ 2 * y.1 1 * y.1 2 = (1 : ℝ) / 4 := by
  have h := hy.2
  simp [apm_t02a07_family] at h
  nlinarith

lemma apm_t02A07_transverse_iff_parameter_sq_ne_half_aux_sphere
    (y : apm_t02a07_S2) :
    y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 = 1 := by
  have hy : ‖(y : apm_t02a07_E3)‖ = 1 := by simpa using y.2
  have h := EuclideanSpace.real_norm_sq_eq (y : apm_t02a07_E3)
  have h' : y.1 0 ^ 2 + (y.1 1 ^ 2 + y.1 2 ^ 2) = 1 := by
    simpa [Fin.sum_univ_succ, hy] using h.symm
  nlinarith

lemma apm_t02A07_transverse_iff_parameter_sq_ne_half_aux_fderiv
    (parameter : apm_t02a07_parameterCircle) (y v : apm_t02a07_E3) :
    fderiv ℝ (apm_t02a07_familyAmbient parameter) y v =
      (WithLp.toLp 2
        ![v 0 * parameter.1 0, 0, v 1 * parameter.1 0,
          v 2 * parameter.1 0] : apm_t02a07_E4) := by
  let L₀ : apm_t02a07_E3 →ₗ[ℝ] apm_t02a07_E4 :=
    { toFun := fun z => WithLp.toLp 2
        ![z 0 * parameter.1 0, 0, z 1 * parameter.1 0,
          z 2 * parameter.1 0]
      map_add' := by
        intro a b
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [add_mul]
      map_smul' := by
        intro c z
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [mul_assoc] }
  let L : apm_t02a07_E3 →L[ℝ] apm_t02a07_E4 :=
    LinearMap.toContinuousLinearMap L₀
  let c : apm_t02a07_E4 := WithLp.toLp 2
    ![(0 : ℝ), parameter.1 1, 0, 0]
  have heq : apm_t02a07_familyAmbient parameter = fun z => L z + c := by
    funext z
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [apm_t02a07_familyAmbient, L, L₀, c]
  rw [heq, ((L.hasFDerivAt.add_const c).fderiv)]
  rfl

lemma apm_t02A07_transverse_iff_parameter_sq_ne_half_aux_submodule
    (parameter : apm_t02a07_parameterCircle)
    (hderiv : ∀ (y v : apm_t02a07_E3),
      fderiv ℝ (apm_t02a07_familyAmbient parameter) y v =
        (WithLp.toLp 2
          ![v 0 * parameter.1 0, 0, v 1 * parameter.1 0,
            v 2 * parameter.1 0] : apm_t02a07_E4)) :
    apm_t02a07_IsTransverse parameter ↔
      parameter.1 0 ^ 2 ≠ (1 : ℝ) / 2 := by
  sorry

theorem apm_t02A07_transverse_iff_parameter_sq_ne_half
    (parameter : apm_t02a07_parameterCircle) :
    apm_t02a07_IsTransverse parameter ↔
      parameter.1 0 ^ 2 ≠ (1 : ℝ) / 2 := by
  exact apm_t02A07_transverse_iff_parameter_sq_ne_half_aux_submodule parameter
    (apm_t02A07_transverse_iff_parameter_sq_ne_half_aux_fderiv parameter)

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

/-- `dim Z = 2`: at a point of `Z` the constraint derivative `ℝ⁴ → ℝ²` is surjective (the
regularity lemmas), so its kernel has dimension `4 − 2 = 2` (rank–nullity). -/
theorem apm_t02a07_tangentZ_finrank :
    ∀ x ∈ apm_t02a07_Z, Module.finrank ℝ (apm_t02a07_tangentZ x) = 2 := by
  intro x hx
  let L := (fderiv ℝ apm_t02a07_constraints x).toLinearMap
  have hsurj : Function.Surjective L :=
    apm_t02A07_constraints_fderiv_surjective_aux_rank x
      (apm_t02A07_bridge_constraint_gradients_independent hx)
  have hrange : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim := L.finrank_range_add_finrank_ker
  rw [hrange, finrank_top] at hdim
  change Module.finrank ℝ (LinearMap.ker
    (fderiv ℝ apm_t02a07_constraints x).toLinearMap) = 2
  change Module.finrank ℝ (LinearMap.ker L) = 2
  simp only [finrank_euclideanSpace_fin] at hdim
  omega

theorem apm_t02a07 :
    apm_t02a07_IsRegularDimensionTwo ∧
    (∀ x ∈ apm_t02a07_Z, Module.finrank ℝ (apm_t02a07_tangentZ x) = 2) ∧
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
  refine ⟨?_, apm_t02a07_tangentZ_finrank, ?_, apm_t02A07_bridge_transverse_parameters_dense⟩
  · apply apm_t02A07_constraints_fderiv_surjective
    intro x hx
    exact apm_t02A07_bridge_constraint_gradients_independent hx
  · intro parameter x hx
    rcases hx with ⟨y, rfl⟩
    exact apm_t02a07_family_mem_X parameter y

#print axioms apm_t02a07
