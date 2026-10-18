import Mathlib

set_option maxHeartbeats 200000

/-!
# APM m02J02

## Statement repairs

None.  "Basis" is read as a linearly independent family whose finite linear
span is dense in the `H¹` graph norm.  This is a reading, and a weak one: no
orthogonality is asserted, and no unique convergent expansion (Schauder basis).
In (a) the sines are in fact `H¹`-orthogonal, so they are an orthogonal basis.
In (b) and (c) the Hermite functions are not `H¹`-orthogonal and, in their
natural order, not a Schauder basis of `H¹(ℝ)`.  The revised informal solution
(7de364a86) reads "basis" as an orthonormal basis and obtains one by applying
Gram–Schmidt in `H¹` to these families.  That step, which needs only the linear
independence and density proved here, is not stated in this file.

## Encoding notes

Because Mathlib has no packaged Sobolev-space type, `H¹₀(Ω)` is encoded
directly as value/weak-derivative pairs that are graph-norm limits of smooth
compactly supported functions.  Thus the central Sobolev object is retained,
including its distributional derivative and closure definition.
-/

open Filter MeasureTheory Polynomial Set
open scoped BigOperators ContDiff ENNReal

def apm_m02j02_IsWeakDerivativeOn (s : Set ℝ) (u du : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ s →
      ∫ x, u x * deriv φ x ∂(volume.restrict s) =
        -∫ x, du x * φ x ∂(volume.restrict s)

def apm_m02j02_InH10 (s : Set ℝ) (u du : ℝ → ℝ) : Prop :=
  MemLp u 2 (volume.restrict s) ∧ MemLp du 2 (volume.restrict s) ∧
  apm_m02j02_IsWeakDerivativeOn s u du ∧
  ∀ ε : ℝ, 0 < ε → ∃ φ : ℝ → ℝ,
    ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ s ∧
    eLpNorm (u - φ) 2 (volume.restrict s) +
      eLpNorm (du - deriv φ) 2 (volume.restrict s) < ENNReal.ofReal ε

def apm_m02j02_IsH10Basis
    (s : Set ℝ) (e de : ℕ → ℝ → ℝ) : Prop :=
  (∀ n : ℕ, apm_m02j02_InH10 s (e n) (de n)) ∧
  LinearIndependent ℝ (fun n ↦ (e n, de n)) ∧
  ∀ u du : ℝ → ℝ, apm_m02j02_InH10 s u du →
    ∀ ε : ℝ, 0 < ε → ∃ c : ℕ →₀ ℝ,
      eLpNorm (u - c.sum fun n a ↦ a • e n) 2 (volume.restrict s) +
        eLpNorm (du - c.sum fun n a ↦ a • de n) 2 (volume.restrict s) <
          ENNReal.ofReal ε

noncomputable def apm_m02j02_sine (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin ((n + 1 : ℝ) * Real.pi * x)

noncomputable def apm_m02j02_sineDeriv (n : ℕ) (x : ℝ) : ℝ :=
  (n + 1 : ℝ) * Real.pi * Real.cos ((n + 1 : ℝ) * Real.pi * x)

noncomputable def apm_m02j02_hermiteFunction (n : ℕ) (x : ℝ) : ℝ :=
  Polynomial.eval x ((Polynomial.hermite n).map (Int.castRingHom ℝ)) *
    Real.exp (-(x ^ 2) / 4)

noncomputable def apm_m02j02_hermiteFunctionDeriv (n : ℕ) (x : ℝ) : ℝ :=
  deriv (apm_m02j02_hermiteFunction n) x

lemma apm_m02j02_hasDerivAt_sine (n : ℕ) (x : ℝ) :
    HasDerivAt (apm_m02j02_sine n) (apm_m02j02_sineDeriv n x) x := by
  convert (((hasDerivAt_id x).const_mul ((n + 1 : ℝ) * Real.pi)).sin) using 1 <;>
    simp [apm_m02j02_sineDeriv, id_eq] <;> ring

lemma apm_m02j02_deriv_sine (n : ℕ) (x : ℝ) :
    deriv (apm_m02j02_sine n) x = apm_m02j02_sineDeriv n x :=
  (apm_m02j02_hasDerivAt_sine n x).deriv

lemma apm_m02j02_sine_zero (n : ℕ) : apm_m02j02_sine n 0 = 0 := by
  simp [apm_m02j02_sine]

lemma apm_m02j02_sine_one (n : ℕ) : apm_m02j02_sine n 1 = 0 := by
  simp [apm_m02j02_sine, add_mul]

/-- Each interval basis function is smooth on the ambient real line. -/
lemma apm_m02j02_sine_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (apm_m02j02_sine n) := by
  unfold apm_m02j02_sine
  fun_prop

lemma apm_m02j02_sineDeriv_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (apm_m02j02_sineDeriv n) := by
  unfold apm_m02j02_sineDeriv
  fun_prop

lemma apm_m02j02_sine_memLp_two_Ioo (n : ℕ) :
    MemLp (apm_m02j02_sine n) 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  apply MemLp.of_bound
    (apm_m02j02_sine_contDiff n).continuous.aestronglyMeasurable 1
  filter_upwards with x
  simpa [Real.norm_eq_abs, apm_m02j02_sine] using
    Real.abs_sin_le_one ((n + 1 : ℝ) * Real.pi * x)

lemma apm_m02j02_sineDeriv_memLp_two_Ioo (n : ℕ) :
    MemLp (apm_m02j02_sineDeriv n) 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  apply MemLp.of_bound
    (apm_m02j02_sineDeriv_contDiff n).continuous.aestronglyMeasurable
      |(n + 1 : ℝ) * Real.pi|
  filter_upwards with x
  rw [Real.norm_eq_abs, apm_m02j02_sineDeriv, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- The Hermite-Gaussian functions occurring in both unbounded-domain
families are smooth. -/
lemma apm_m02j02_hermiteFunction_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (apm_m02j02_hermiteFunction n) := by
  let p : ℝ[X] := (Polynomial.hermite n).map (Int.castRingHom ℝ)
  have hp : ContDiff ℝ ∞ (fun x : ℝ => Polynomial.eval x p) := by
    simpa [Polynomial.aeval_def] using Polynomial.contDiff_aeval p ∞
  unfold apm_m02j02_hermiteFunction
  exact hp.mul (by fun_prop)

lemma apm_m02j02_hermiteFunction_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (apm_m02j02_hermiteFunction n)
      (apm_m02j02_hermiteFunctionDeriv n x) x := by
  simpa [apm_m02j02_hermiteFunctionDeriv] using
    ((apm_m02j02_hermiteFunction_contDiff n).differentiable
      (by simp)).differentiableAt.hasDerivAt

lemma apm_m02j02_deriv_hermiteFunction (n : ℕ) (x : ℝ) :
    deriv (apm_m02j02_hermiteFunction n) x =
      apm_m02j02_hermiteFunctionDeriv n x :=
  (apm_m02j02_hermiteFunction_hasDerivAt n x).deriv

/-- Every odd Hermite–Gaussian has the required zero trace at the finite
endpoint of the half-line. -/
lemma apm_m02j02_hermiteFunction_odd_zero (n : ℕ) :
    apm_m02j02_hermiteFunction (2 * n + 1) 0 = 0 := by
  have hodd : Odd ((2 * n + 1) + 0) := by simpa using odd_two_mul_add_one n
  have hc := Polynomial.coeff_hermite_of_odd_add hodd
  unfold apm_m02j02_hermiteFunction
  rw [mul_eq_zero]
  left
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map, hc]
  exact map_zero _

private noncomputable def apm_m02j02_hermiteSequenceReal :
    Polynomial.Sequence ℝ where
  elems' n := (Polynomial.hermite n).map (Int.castRingHom ℝ)
  degree_eq' n := by
    rw [Polynomial.degree_map_eq_of_injective Int.cast_injective]
    exact Polynomial.degree_hermite n

/-- The real Hermite polynomials span the entire polynomial ring.  This is
the algebraic half of Hermite completeness: after applying
`apm_m02j02_weightedEval`, their finite sums are exactly all polynomials
times the fixed Gaussian. -/
lemma apm_m02j02_hermiteReal_span :
    Submodule.span ℝ (Set.range (fun n : ℕ ↦
      (Polynomial.hermite n).map (Int.castRingHom ℝ))) = ⊤ := by
  apply Polynomial.Sequence.span apm_m02j02_hermiteSequenceReal
  intro n
  change IsUnit (((Polynomial.hermite n).map
    (Int.castRingHom ℝ)).leadingCoeff)
  rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero]
  · simp [Polynomial.leadingCoeff_hermite]
  · simp [Polynomial.leadingCoeff_hermite]

private noncomputable def apm_m02j02_weightedEval :
    ℝ[X] →ₗ[ℝ] (ℝ → ℝ) where
  toFun p x := Polynomial.eval x p * Real.exp (-(x ^ 2) / 4)
  map_add' p q := by
    funext x
    simp [add_mul]
  map_smul' a p := by
    funext x
    simp [mul_assoc]

/-- Finite linear combinations of the frozen Hermite functions are exactly
the polynomial-times-Gaussian functions.  Consequently the remaining
Hermite completeness step is purely the analytic density of the range on the
right, rather than a further polynomial-algebra problem. -/
lemma apm_m02j02_span_hermiteFunction_eq_weightedEval_range :
    Submodule.span ℝ (Set.range apm_m02j02_hermiteFunction) =
      LinearMap.range apm_m02j02_weightedEval := by
  rw [LinearMap.range_eq_map, ← apm_m02j02_hermiteReal_span,
    Submodule.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨(Polynomial.hermite n).map (Int.castRingHom ℝ), ⟨n, rfl⟩, ?_⟩
    rfl
  · rintro ⟨p, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩

/-- Differentiating a polynomial times the frozen Gaussian stays in the same
range.  The polynomial is transformed by `p ↦ p' - (X / 2) p`. -/
lemma apm_m02j02_weightedEval_hasDerivAt (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (apm_m02j02_weightedEval p)
      (apm_m02j02_weightedEval
        (p.derivative - Polynomial.C (1 / 2 : ℝ) * Polynomial.X * p) x) x := by
  have hg : HasDerivAt (fun z : ℝ ↦ -(z ^ 2) / 4) (-x / 2) x := by
    convert ((hasDerivAt_id x).pow 2).neg.div_const 4 using 1 <;>
      simp [id_eq] <;> ring
  have he : HasDerivAt (fun z : ℝ ↦ Real.exp (-(z ^ 2) / 4))
      ((-x / 2) * Real.exp (-(x ^ 2) / 4)) x := by
    convert (Real.hasDerivAt_exp _).comp x hg using 1 <;> ring
  have hp := (Polynomial.hasDerivAt p x).mul he
  convert hp using 1 <;>
    simp [apm_m02j02_weightedEval, Polynomial.eval_sub,
      Polynomial.eval_mul] <;> ring

lemma apm_m02j02_deriv_weightedEval (p : ℝ[X]) (x : ℝ) :
    deriv (apm_m02j02_weightedEval p) x =
      apm_m02j02_weightedEval
        (p.derivative - Polynomial.C (1 / 2 : ℝ) * Polynomial.X * p) x :=
  (apm_m02j02_weightedEval_hasDerivAt p x).deriv

/-- Every polynomial-times-Gaussian function is a finite Hermite linear
combination, stated as membership in the exact span used above. -/
lemma apm_m02j02_weightedEval_mem_hermite_span (p : ℝ[X]) :
    apm_m02j02_weightedEval p ∈
      Submodule.span ℝ (Set.range apm_m02j02_hermiteFunction) := by
  rw [apm_m02j02_span_hermiteFunction_eq_weightedEval_range]
  exact LinearMap.mem_range_self apm_m02j02_weightedEval p

/-- The derivative of every polynomial-times-Gaussian function is likewise a
finite Hermite linear combination. -/
lemma apm_m02j02_deriv_weightedEval_mem_hermite_span (p : ℝ[X]) :
    (fun x ↦ deriv (apm_m02j02_weightedEval p) x) ∈
      Submodule.span ℝ (Set.range apm_m02j02_hermiteFunction) := by
  rw [show (fun x ↦ deriv (apm_m02j02_weightedEval p) x) =
      apm_m02j02_weightedEval
        (p.derivative - Polynomial.C (1 / 2 : ℝ) * Polynomial.X * p) by
    funext x
    exact apm_m02j02_deriv_weightedEval p x]
  exact apm_m02j02_weightedEval_mem_hermite_span _

/-- Differentiating a finite Hermite expansion preserves its coefficients and
replaces each mode by the frozen derivative mode. -/
lemma apm_m02j02_deriv_hermite_finsupp_sum (c : ℕ →₀ ℝ) :
    (fun x ↦ deriv (c.sum fun n a ↦ a • apm_m02j02_hermiteFunction n) x) =
      c.sum fun n a ↦ a • apm_m02j02_hermiteFunctionDeriv n := by
  funext x
  rw [Finsupp.sum, Finsupp.sum]
  rw [show (∑ n ∈ c.support, c n • apm_m02j02_hermiteFunction n) =
      (fun y ↦ ∑ n ∈ c.support, c n * apm_m02j02_hermiteFunction n y) by
    funext y
    simp]
  rw [show (∑ n ∈ c.support, c n • apm_m02j02_hermiteFunctionDeriv n) =
      (fun y ↦ ∑ n ∈ c.support, c n * apm_m02j02_hermiteFunctionDeriv n y) by
    funext y
    simp]
  change deriv (fun y ↦ ∑ n ∈ c.support,
      c n * apm_m02j02_hermiteFunction n y) x =
    ∑ n ∈ c.support, c n * apm_m02j02_hermiteFunctionDeriv n x
  have h := HasDerivAt.fun_sum (u := c.support)
    (A := fun n ↦ c n • apm_m02j02_hermiteFunction n)
    (A' := fun n ↦ c n * apm_m02j02_hermiteFunctionDeriv n x)
    (fun n _ ↦ (apm_m02j02_hermiteFunction_hasDerivAt n x).const_mul (c n))
  exact h.deriv

/-- A polynomial-times-Gaussian function and its derivative are represented
by one finite coefficient family in the frozen Hermite value/derivative pair
family. -/
lemma apm_m02j02_exists_hermite_coefficients_weightedEval (p : ℝ[X]) :
    ∃ c : ℕ →₀ ℝ,
      apm_m02j02_weightedEval p =
          (c.sum fun n a ↦ a • apm_m02j02_hermiteFunction n) ∧
        (fun x ↦ deriv (apm_m02j02_weightedEval p) x) =
          c.sum fun n a ↦ a • apm_m02j02_hermiteFunctionDeriv n := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (apm_m02j02_weightedEval_mem_hermite_span p)
  refine ⟨c, hc.symm, ?_⟩
  rw [← hc, apm_m02j02_deriv_hermite_finsupp_sum]

private lemma apm_m02j02_weightedEval_injective :
    Function.Injective apm_m02j02_weightedEval := by
  intro p q hpq
  apply Polynomial.funext
  intro x
  have hx := congrFun hpq x
  dsimp [apm_m02j02_weightedEval] at hx
  exact mul_right_cancel₀ (Real.exp_ne_zero (-(x ^ 2) / 4)) hx

lemma apm_m02j02_hermiteFunction_linearIndependent :
    LinearIndependent ℝ apm_m02j02_hermiteFunction := by
  have hp : LinearIndependent ℝ
      (apm_m02j02_hermiteSequenceReal : ℕ → ℝ[X]) :=
    Polynomial.Sequence.linearIndependent apm_m02j02_hermiteSequenceReal
  have hm := hp.map' apm_m02j02_weightedEval
    (LinearMap.ker_eq_bot.mpr apm_m02j02_weightedEval_injective)
  simpa [Function.comp_def, apm_m02j02_hermiteSequenceReal,
    apm_m02j02_weightedEval, apm_m02j02_hermiteFunction] using hm

lemma apm_m02j02_hermitePair_linearIndependent :
    LinearIndependent ℝ (fun n ↦
      (apm_m02j02_hermiteFunction n, apm_m02j02_hermiteFunctionDeriv n)) := by
  apply LinearIndependent.of_comp (LinearMap.fst ℝ (ℝ → ℝ) (ℝ → ℝ))
  simpa [Function.comp_def] using apm_m02j02_hermiteFunction_linearIndependent

lemma apm_m02j02_oddHermitePair_linearIndependent :
    LinearIndependent ℝ (fun n ↦
      (apm_m02j02_hermiteFunction (2 * n + 1),
        apm_m02j02_hermiteFunctionDeriv (2 * n + 1))) := by
  exact apm_m02j02_hermitePair_linearIndependent.comp
    (fun n ↦ 2 * n + 1) (by
      intro a b h
      exact Nat.mul_left_cancel (by norm_num) (Nat.add_right_cancel h))

private lemma apm_m02j02_integrable_pow_gaussian (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ ↦ x ^ n * Real.exp (-b * x ^ 2)) volume := by
  have hn : (-1 : ℝ) < (n : ℝ) :=
    lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)
  have h := integrable_rpow_mul_exp_neg_mul_sq hb hn
  have hm : AEStronglyMeasurable
      (fun x : ℝ ↦ x ^ n * Real.exp (-b * x ^ 2)) volume := by fun_prop
  apply (integrable_norm_iff hm).mp
  apply h.norm.congr
  filter_upwards with x
  rw [Real.rpow_natCast]

private lemma apm_m02j02_integrable_polynomial_gaussian
    (p : ℝ[X]) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ ↦ p.eval x * Real.exp (-b * x ^ 2)) volume := by
  rw [show (fun x : ℝ ↦ p.eval x * Real.exp (-b * x ^ 2)) =
      fun x ↦ ∑ n ∈ Finset.range (p.natDegree + 1),
        p.coeff n * (x ^ n * Real.exp (-b * x ^ 2)) by
    funext x
    rw [Polynomial.eval_eq_sum_range]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    ring]
  exact integrable_finset_sum _ fun n _ ↦
    (apm_m02j02_integrable_pow_gaussian n hb).const_mul (p.coeff n)

private lemma apm_m02j02_polynomial_gaussian_memLp_two (p : ℝ[X]) :
    MemLp (fun x : ℝ ↦ p.eval x * Real.exp (-(x ^ 2) / 4)) 2 volume := by
  have hm : AEStronglyMeasurable
      (fun x : ℝ ↦ p.eval x * Real.exp (-(x ^ 2) / 4)) volume := by fun_prop
  rw [memLp_two_iff_integrable_sq hm]
  have h := apm_m02j02_integrable_polynomial_gaussian (p ^ 2)
    (show 0 < (1 / 2 : ℝ) by norm_num)
  apply h.congr
  filter_upwards with x
  simp only [Polynomial.eval_pow, mul_pow]
  congr 1
  conv_rhs => rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Every element of the polynomial-times-Gaussian approximation class is in
whole-line `L²`. -/
lemma apm_m02j02_weightedEval_memLp_two (p : ℝ[X]) :
    MemLp (apm_m02j02_weightedEval p) 2 volume := by
  simpa [apm_m02j02_weightedEval] using
    apm_m02j02_polynomial_gaussian_memLp_two p

/-- The actual derivative of every polynomial-times-Gaussian approximant is
also in whole-line `L²`. -/
lemma apm_m02j02_deriv_weightedEval_memLp_two (p : ℝ[X]) :
    MemLp (fun x ↦ deriv (apm_m02j02_weightedEval p) x) 2 volume := by
  apply (memLp_congr_ae (Filter.Eventually.of_forall fun x ↦
    apm_m02j02_deriv_weightedEval p x)).mpr
  exact apm_m02j02_weightedEval_memLp_two
    (p.derivative - Polynomial.C (1 / 2 : ℝ) * Polynomial.X * p)

/-- On every centered compact interval, polynomial-times-Gaussian functions
uniformly approximate any continuous function. -/
lemma apm_m02j02_exists_weightedEval_near_on_Icc (φ : ℝ → ℝ)
    (hφ : Continuous φ) (R ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Set.Icc (-R) R,
      |apm_m02j02_weightedEval p x - φ x| < ε := by
  have hg : Continuous (fun x : ℝ ↦ φ x * Real.exp (x ^ 2 / 4)) := by
    fun_prop
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn
    (-R) R (fun x : ℝ ↦ φ x * Real.exp (x ^ 2 / 4))
    hg.continuousOn ε hε
  refine ⟨p, fun x hx ↦ ?_⟩
  have hraw := hp x hx
  have hexp_nonneg : 0 ≤ Real.exp (-(x ^ 2) / 4) := Real.exp_pos _ |>.le
  have hexp_le_one : Real.exp (-(x ^ 2) / 4) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    linarith
  have hid : φ x * Real.exp (x ^ 2 / 4) * Real.exp (-(x ^ 2) / 4) = φ x := by
    have heprod : Real.exp (x ^ 2 / 4) * Real.exp (-(x ^ 2) / 4) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    rw [mul_assoc, heprod, mul_one]
  have hfactor : apm_m02j02_weightedEval p x - φ x =
      (p.eval x - φ x * Real.exp (x ^ 2 / 4)) *
        Real.exp (-(x ^ 2) / 4) := by
    dsimp [apm_m02j02_weightedEval]
    calc
      p.eval x * Real.exp (-(x ^ 2) / 4) - φ x =
          p.eval x * Real.exp (-(x ^ 2) / 4) -
            (φ x * Real.exp (x ^ 2 / 4)) * Real.exp (-(x ^ 2) / 4) := by rw [hid]
      _ = (p.eval x - φ x * Real.exp (x ^ 2 / 4)) *
            Real.exp (-(x ^ 2) / 4) := by ring
  rw [hfactor, abs_mul, abs_of_nonneg hexp_nonneg]
  exact lt_of_le_of_lt
    (mul_le_of_le_one_right (abs_nonneg _) hexp_le_one) hraw

/-- The derivative of the Gaussian-unweighted target can itself be uniformly
approximated by a polynomial on every centered compact interval.  Integrating
this polynomial is the remaining step in the direct `C¹` approximation. -/
lemma apm_m02j02_exists_polynomial_near_unweighted_deriv_on_Icc
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (R ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℝ[X], ∀ x ∈ Set.Icc (-R) R,
      |q.eval x - deriv (fun y : ℝ ↦ φ y * Real.exp (y ^ 2 / 4)) x| < ε := by
  have hg : ContDiff ℝ ∞ (fun y : ℝ ↦ φ y * Real.exp (y ^ 2 / 4)) := by
    fun_prop
  exact exists_polynomial_near_of_continuousOn (-R) R
    (deriv (fun y : ℝ ↦ φ y * Real.exp (y ^ 2 / 4)))
    (hg.continuous_deriv (by simp)).continuousOn ε hε

/-- Over `ℝ`, every polynomial has a polynomial primitive. -/
lemma apm_m02j02_exists_polynomial_derivative_eq (q : ℝ[X]) :
    ∃ p : ℝ[X], p.derivative = q := by
  let p : ℝ[X] := ∑ n ∈ q.support,
    Polynomial.C (q.coeff n / (n + 1 : ℝ)) * Polynomial.X ^ (n + 1)
  refine ⟨p, ?_⟩
  change (∑ n ∈ q.support,
    Polynomial.C (q.coeff n / (n + 1 : ℝ)) * Polynomial.X ^ (n + 1)).derivative = q
  rw [Polynomial.derivative_sum]
  simp only [Polynomial.derivative_sum, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.derivative_X_pow_succ]
  calc
    (∑ n ∈ q.support,
        C (q.coeff n / (↑n + 1)) * (C (↑n + 1) * X ^ n)) =
        ∑ n ∈ q.support, C (q.coeff n) * X ^ n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← mul_assoc, ← Polynomial.C_mul]
      congr 1
      field_simp
    _ = q := q.as_sum_support_C_mul_X_pow.symm

/-- A polynomial primitive can be normalized to take any prescribed value at
an anchor point. -/
lemma apm_m02j02_exists_polynomial_derivative_eq_eval_eq
    (q : ℝ[X]) (a b : ℝ) :
    ∃ p : ℝ[X], p.derivative = q ∧ p.eval a = b := by
  obtain ⟨p, hp⟩ := apm_m02j02_exists_polynomial_derivative_eq q
  refine ⟨p + Polynomial.C (b - p.eval a), ?_, ?_⟩
  · simp [hp]
  · simp

/-- An anchored derivative error bound integrates to a value error bound on
an interval. -/
lemma apm_m02j02_abs_sub_le_of_deriv_sub_le_of_eq_left
    (f g : ℝ → ℝ) (a b δ : ℝ) (hab : a ≤ b)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hleft : f a = g a)
    (hderiv : ∀ x ∈ Set.Icc a b, |deriv f x - deriv g x| ≤ δ) :
    ∀ x ∈ Set.Icc a b, |f x - g x| ≤ δ * |x - a| := by
  intro x hx
  have hdiff : ∀ y ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun z ↦ f z - g z) y := by
    intro y hy
    exact (hf y).sub (hg y)
  have hbound : ∀ y ∈ Set.Icc a b,
      ‖deriv (fun z ↦ f z - g z) y‖ ≤ δ := by
    intro y hy
    have heq : deriv (fun z ↦ f z - g z) y =
        deriv f y - deriv g y :=
      ((hf y).hasDerivAt.sub (hg y).hasDerivAt).deriv
    rw [heq]
    simpa [Real.norm_eq_abs] using hderiv y hy
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (convex_Icc a b) (left_mem_Icc.mpr hab) hx
  have hzero : f a - g a = 0 := sub_eq_zero.mpr hleft
  rw [hzero, sub_zero] at hmv
  simpa [Real.norm_eq_abs] using hmv

/-- Uniform approximation of the derivative of the Gaussian-unweighted
target can be integrated, with an anchored constant, to simultaneous `C¹`
approximation on a centered compact interval. -/
lemma apm_m02j02_exists_polynomial_near_unweighted_C1_on_Icc
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (R ε : ℝ)
    (hR : 0 < R) (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Set.Icc (-R) R,
      |p.eval x - φ x * Real.exp (x ^ 2 / 4)| < ε * (2 * R + 1) ∧
      |p.derivative.eval x -
        deriv (fun y : ℝ ↦ φ y * Real.exp (y ^ 2 / 4)) x| < ε := by
  let g : ℝ → ℝ := fun y ↦ φ y * Real.exp (y ^ 2 / 4)
  have hg : ContDiff ℝ ∞ g := by
    dsimp [g]
    fun_prop
  obtain ⟨q, hq⟩ :=
    apm_m02j02_exists_polynomial_near_unweighted_deriv_on_Icc φ hφ R ε hε
  obtain ⟨p, hpderiv, hpanchor⟩ :=
    apm_m02j02_exists_polynomial_derivative_eq_eval_eq q (-R) (g (-R))
  refine ⟨p, ?_⟩
  intro x hx
  have hp_diff : Differentiable ℝ (fun y : ℝ ↦ p.eval y) :=
    fun y ↦ (p.hasDerivAt y).differentiableAt
  have hg_diff : Differentiable ℝ g := hg.differentiable (by simp)
  have hderiv_le : ∀ y ∈ Set.Icc (-R) R,
      |deriv (fun z : ℝ ↦ p.eval z) y - deriv g y| ≤ ε := by
    intro y hy
    rw [(p.hasDerivAt y).deriv, hpderiv]
    exact (hq y hy).le
  have hvalue := apm_m02j02_abs_sub_le_of_deriv_sub_le_of_eq_left
    (fun y : ℝ ↦ p.eval y) g (-R) R ε (by linarith)
    hp_diff hg_diff hpanchor hderiv_le x hx
  have hxbound : |x - (-R)| ≤ 2 * R := by
    rw [abs_of_nonneg (by linarith [hx.1])]
    linarith [hx.2]
  constructor
  · dsimp [g] at hvalue ⊢
    calc
      |p.eval x - φ x * Real.exp (x ^ 2 / 4)| ≤ ε * |x - -R| := hvalue
      _ ≤ ε * (2 * R) := mul_le_mul_of_nonneg_left hxbound hε.le
      _ < ε * (2 * R + 1) := by nlinarith
  · rw [hpderiv]
    exact hq x hx

/-- Multiplication by the frozen Gaussian turns transformed value error into
the actual weighted-polynomial value error. -/
lemma apm_m02j02_weightedEval_sub_eq_unweighted_sub_mul
    (φ : ℝ → ℝ) (p : ℝ[X]) (x : ℝ) :
    apm_m02j02_weightedEval p x - φ x =
      (p.eval x - φ x * Real.exp (x ^ 2 / 4)) *
        Real.exp (-(x ^ 2) / 4) := by
  have hexp : Real.exp (x ^ 2 / 4) * Real.exp (-(x ^ 2) / 4) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  simp only [apm_m02j02_weightedEval, LinearMap.coe_mk,
    AddHom.coe_mk]
  calc
    p.eval x * Real.exp (-(x ^ 2) / 4) - φ x =
        p.eval x * Real.exp (-(x ^ 2) / 4) -
          (φ x * Real.exp (x ^ 2 / 4)) * Real.exp (-(x ^ 2) / 4) := by
            rw [mul_assoc, hexp, mul_one]
    _ = (p.eval x - φ x * Real.exp (x ^ 2 / 4)) *
          Real.exp (-(x ^ 2) / 4) := by ring

/-- The derivative error after multiplying back by the Gaussian is exactly
the transformed derivative error minus `x/2` times the transformed value
error, with the common Gaussian factor. -/
lemma apm_m02j02_deriv_weightedEval_sub_eq_unweighted_errors_mul
    (φ : ℝ → ℝ) (p : ℝ[X]) (x : ℝ)
    (hφ : DifferentiableAt ℝ φ x) :
    deriv (apm_m02j02_weightedEval p) x - deriv φ x =
      ((p.derivative.eval x -
          deriv (fun y : ℝ ↦ φ y * Real.exp (y ^ 2 / 4)) x) -
        (x / 2) * (p.eval x - φ x * Real.exp (x ^ 2 / 4))) *
          Real.exp (-(x ^ 2) / 4) := by
  have hpos : HasDerivAt (fun y : ℝ ↦ Real.exp (y ^ 2 / 4))
      ((x / 2) * Real.exp (x ^ 2 / 4)) x := by
    convert (((hasDerivAt_id x).pow 2).div_const 4).exp using 1 <;>
      simp [id_eq] <;> ring
  have hg := hφ.hasDerivAt.mul hpos
  have hgderiv : deriv (fun y : ℝ ↦ φ y * Real.exp (y ^ 2 / 4)) x =
      deriv φ x * Real.exp (x ^ 2 / 4) +
        φ x * ((x / 2) * Real.exp (x ^ 2 / 4)) := by
    exact hg.deriv
  have hexp : Real.exp (x ^ 2 / 4) * Real.exp (-(x ^ 2) / 4) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hexp_rev : Real.exp (-(x ^ 2) / 4) * Real.exp (x ^ 2 / 4) = 1 := by
    rw [mul_comm]
    exact hexp
  have hnorm : Real.exp (x ^ 2 * (-1 / 4)) *
      Real.exp (x ^ 2 * (1 / 4)) = 1 := by
    convert hexp_rev using 1 <;> ring
  rw [apm_m02j02_deriv_weightedEval, hgderiv]
  simp only [apm_m02j02_weightedEval, LinearMap.coe_mk, AddHom.coe_mk,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  field_simp
  ring_nf
  linear_combination (2 * deriv φ x) * hnorm

/-- Uniform transformed `C¹` errors on `[-R,R]` give uniform errors after
multiplication by the frozen Gaussian. -/
lemma apm_m02j02_weightedEval_errors_lt_of_unweighted_errors_lt
    (φ : ℝ → ℝ) (p : ℝ[X]) (x R A B : ℝ)
    (hφ : DifferentiableAt ℝ φ x) (hR : 0 ≤ R)
    (hx : x ∈ Set.Icc (-R) R)
    (hval : |p.eval x - φ x * Real.exp (x ^ 2 / 4)| < A)
    (hder : |p.derivative.eval x -
      deriv (fun y : ℝ ↦ φ y * Real.exp (y ^ 2 / 4)) x| < B) :
    |apm_m02j02_weightedEval p x - φ x| < A ∧
      |deriv (apm_m02j02_weightedEval p) x - deriv φ x| <
        B + (R / 2) * A := by
  have hexp_nonneg : 0 ≤ Real.exp (-(x ^ 2) / 4) := (Real.exp_pos _).le
  have hexp_le : Real.exp (-(x ^ 2) / 4) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    linarith
  have hxabs : |x| ≤ R := (abs_le.mpr hx)
  constructor
  · rw [apm_m02j02_weightedEval_sub_eq_unweighted_sub_mul, abs_mul,
      abs_of_nonneg hexp_nonneg]
    exact lt_of_le_of_lt
      (mul_le_of_le_one_right (abs_nonneg _) hexp_le) hval
  · rw [apm_m02j02_deriv_weightedEval_sub_eq_unweighted_errors_mul φ p x hφ,
      abs_mul, abs_of_nonneg hexp_nonneg]
    apply lt_of_le_of_lt (mul_le_of_le_one_right (abs_nonneg _) hexp_le)
    calc
      |(p.derivative.eval x -
          deriv (fun y : ℝ ↦ φ y * Real.exp (y ^ 2 / 4)) x) -
        (x / 2) * (p.eval x - φ x * Real.exp (x ^ 2 / 4))| ≤
          |p.derivative.eval x -
            deriv (fun y : ℝ ↦ φ y * Real.exp (y ^ 2 / 4)) x| +
          |(x / 2) * (p.eval x - φ x * Real.exp (x ^ 2 / 4))| :=
            abs_sub _ _
      _ < B + (R / 2) * A := by
        have hcross : |(x / 2) *
            (p.eval x - φ x * Real.exp (x ^ 2 / 4))| ≤ (R / 2) * A := by
          rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          exact mul_le_mul (div_le_div_of_nonneg_right hxabs (by norm_num))
            hval.le (abs_nonneg _) (by positivity)
        exact add_lt_add_of_lt_of_le hder hcross

/-- A uniform real-valued bound on a measurable set gives the corresponding
explicit restricted `L²` bound. -/
lemma apm_m02j02_eLpNorm_two_restrict_le_of_abs_le
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (f : ℝ → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ s, |f x| ≤ C) :
    eLpNorm f 2 (μ.restrict s) ≤
      ENNReal.ofReal C * (μ s) ^ (1 / 2 : ℝ) := by
  calc
    eLpNorm f 2 (μ.restrict s) ≤
        eLpNorm (fun _ : ℝ ↦ C) 2 (μ.restrict s) := by
      apply eLpNorm_mono_ae
      filter_upwards [ae_restrict_mem hs] with x hx
      simpa [Real.norm_eq_abs, abs_of_nonneg hC0] using hC x hx
    _ = ENNReal.ofReal C * (μ s) ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_const']
      · rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg hC0]
        simp [hs]
      · norm_num
      · norm_num

/-- Uniform transformed errors on a centered interval give explicit
restricted `L²` bounds for both the weighted value and its derivative. -/
lemma apm_m02j02_weightedEval_restrict_Icc_eLpNorm_bounds
    (φ : ℝ → ℝ) (p : ℝ[X]) (R A B : ℝ)
    (hφ : Differentiable ℝ φ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hval : ∀ x ∈ Set.Icc (-R) R,
      |p.eval x - φ x * Real.exp (x ^ 2 / 4)| ≤ A)
    (hder : ∀ x ∈ Set.Icc (-R) R,
      |p.derivative.eval x -
        deriv (fun y : ℝ ↦ φ y * Real.exp (y ^ 2 / 4)) x| ≤ B) :
    eLpNorm (φ - apm_m02j02_weightedEval p) 2
        (volume.restrict (Set.Icc (-R) R)) ≤
      ENNReal.ofReal A * (ENNReal.ofReal (R + R)) ^ (1 / 2 : ℝ) ∧
    eLpNorm ((deriv φ) -
        (fun x ↦ deriv (apm_m02j02_weightedEval p) x)) 2
        (volume.restrict (Set.Icc (-R) R)) ≤
      ENNReal.ofReal (B + (R / 2) * A) *
        (ENNReal.ofReal (R + R)) ^ (1 / 2 : ℝ) := by
  have hactual : ∀ x ∈ Set.Icc (-R) R,
      |apm_m02j02_weightedEval p x - φ x| ≤ A ∧
      |deriv (apm_m02j02_weightedEval p) x - deriv φ x| ≤
        B + (R / 2) * A := by
    intro x hx
    -- Use the exact error identities directly to retain the non-strict
    -- constants `A` and `B`.
    have hexp_nonneg : 0 ≤ Real.exp (-(x ^ 2) / 4) := (Real.exp_pos _).le
    have hexp_le : Real.exp (-(x ^ 2) / 4) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
      linarith
    have hxabs : |x| ≤ R := abs_le.mpr hx
    constructor
    · rw [apm_m02j02_weightedEval_sub_eq_unweighted_sub_mul, abs_mul,
        abs_of_nonneg hexp_nonneg]
      exact (mul_le_of_le_one_right (abs_nonneg _) hexp_le).trans (hval x hx)
    · rw [apm_m02j02_deriv_weightedEval_sub_eq_unweighted_errors_mul φ p x
        (hφ x), abs_mul, abs_of_nonneg hexp_nonneg]
      apply (mul_le_of_le_one_right (abs_nonneg _) hexp_le).trans
      calc
        |(p.derivative.eval x -
            deriv (fun y : ℝ ↦ φ y * Real.exp (y ^ 2 / 4)) x) -
          (x / 2) * (p.eval x - φ x * Real.exp (x ^ 2 / 4))| ≤
            |p.derivative.eval x -
              deriv (fun y : ℝ ↦ φ y * Real.exp (y ^ 2 / 4)) x| +
            |(x / 2) * (p.eval x - φ x * Real.exp (x ^ 2 / 4))| := abs_sub _ _
        _ ≤ B + (R / 2) * A := by
          apply add_le_add (hder x hx)
          rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          exact mul_le_mul (div_le_div_of_nonneg_right hxabs (by norm_num))
            (hval x hx) (abs_nonneg _) (by positivity)
  constructor
  · have h := apm_m02j02_eLpNorm_two_restrict_le_of_abs_le
      (μ := volume) measurableSet_Icc (φ - apm_m02j02_weightedEval p) A hA
      (fun x hx ↦ by simpa [Pi.sub_apply, abs_sub_comm] using (hactual x hx).1)
    simpa [Real.volume_Icc] using h
  · have hC : 0 ≤ B + (R / 2) * A := by positivity
    have h := apm_m02j02_eLpNorm_two_restrict_le_of_abs_le
      (μ := volume) measurableSet_Icc
      ((deriv φ) - (fun x ↦ deriv (apm_m02j02_weightedEval p) x))
      (B + (R / 2) * A) hC
      (fun x hx ↦ by simpa [Pi.sub_apply, abs_sub_comm] using (hactual x hx).2)
    simpa [Real.volume_Icc] using h

lemma apm_m02j02_hermiteFunction_memLp_two (n : ℕ) :
    MemLp (apm_m02j02_hermiteFunction n) 2 volume := by
  simpa [apm_m02j02_hermiteFunction] using
    apm_m02j02_polynomial_gaussian_memLp_two
      ((Polynomial.hermite n).map (Int.castRingHom ℝ))

private noncomputable def apm_m02j02_hermiteDerivPolynomial (n : ℕ) : ℝ[X] :=
  let p := (Polynomial.hermite n).map (Int.castRingHom ℝ)
  p.derivative - Polynomial.C (1 / 2) * Polynomial.X * p

private lemma apm_m02j02_hermiteFunctionDeriv_eq (n : ℕ) (x : ℝ) :
    apm_m02j02_hermiteFunctionDeriv n x =
      (apm_m02j02_hermiteDerivPolynomial n).eval x *
        Real.exp (-(x ^ 2) / 4) := by
  let p : ℝ[X] := (Polynomial.hermite n).map (Int.castRingHom ℝ)
  have hg : HasDerivAt (fun z : ℝ ↦ -(z ^ 2) / 4) (-x / 2) x := by
    convert ((hasDerivAt_id x).pow 2).neg.div_const 4 using 1 <;>
      simp [id_eq] <;> ring
  have he : HasDerivAt (fun z : ℝ ↦ Real.exp (-(z ^ 2) / 4))
      ((-x / 2) * Real.exp (-(x ^ 2) / 4)) x := by
    convert (Real.hasDerivAt_exp _).comp x hg using 1 <;> ring
  have hp := (Polynomial.hasDerivAt p x).mul he
  rw [apm_m02j02_hermiteFunctionDeriv]
  change deriv (fun z : ℝ ↦ p.eval z * Real.exp (-(z ^ 2) / 4)) x = _
  have hd : deriv (fun z : ℝ ↦ p.eval z * Real.exp (-(z ^ 2) / 4)) x =
      p.derivative.eval x * Real.exp (-(x ^ 2) / 4) +
        p.eval x * ((-x / 2) * Real.exp (-(x ^ 2) / 4)) := by
    simpa only [Pi.mul_apply] using hp.deriv
  rw [hd]
  simp only [apm_m02j02_hermiteDerivPolynomial, p, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  ring

lemma apm_m02j02_hermiteFunctionDeriv_memLp_two (n : ℕ) :
    MemLp (apm_m02j02_hermiteFunctionDeriv n) 2 volume := by
  apply (memLp_congr_ae (Filter.Eventually.of_forall fun x ↦
    apm_m02j02_hermiteFunctionDeriv_eq n x)).mpr
  exact apm_m02j02_polynomial_gaussian_memLp_two
    (apm_m02j02_hermiteDerivPolynomial n)

lemma apm_m02j02_oddHermite_memLp_two_Ioi (n : ℕ) :
    MemLp (apm_m02j02_hermiteFunction (2 * n + 1)) 2
      (volume.restrict (Ioi (0 : ℝ))) :=
  (apm_m02j02_hermiteFunction_memLp_two (2 * n + 1)).mono_measure
    (Measure.restrict_le_self)

lemma apm_m02j02_oddHermiteDeriv_memLp_two_Ioi (n : ℕ) :
    MemLp (apm_m02j02_hermiteFunctionDeriv (2 * n + 1)) 2
      (volume.restrict (Ioi (0 : ℝ))) :=
  (apm_m02j02_hermiteFunctionDeriv_memLp_two (2 * n + 1)).mono_measure
    (Measure.restrict_le_self)

private lemma apm_m02j02_hermiteFunctionDeriv_continuous (n : ℕ) :
    Continuous (apm_m02j02_hermiteFunctionDeriv n) := by
  simpa [apm_m02j02_hermiteFunctionDeriv] using
    (apm_m02j02_hermiteFunction_contDiff n).continuous_deriv (by simp)

private lemma apm_m02j02_integrable_continuous_mul_compact
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (f * g) volume := by
  exact (hf.mul hg).integrable_of_hasCompactSupport hgc.mul_left

lemma apm_m02j02_hermiteFunction_weakDerivative_univ (n : ℕ) :
    apm_m02j02_IsWeakDerivativeOn Set.univ
      (apm_m02j02_hermiteFunction n)
      (apm_m02j02_hermiteFunctionDeriv n) := by
  intro φ hφ hφc _
  simp only [Measure.restrict_univ]
  have hfcont : Continuous (apm_m02j02_hermiteFunction n) :=
    (apm_m02j02_hermiteFunction_contDiff n).continuous
  have hdfcont : Continuous (apm_m02j02_hermiteFunctionDeriv n) :=
    apm_m02j02_hermiteFunctionDeriv_continuous n
  have hφdcont : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have hi1 : Integrable
      (apm_m02j02_hermiteFunction n * deriv φ) volume :=
    apm_m02j02_integrable_continuous_mul_compact _ _ hfcont hφdcont hφc.deriv
  have hi2 : Integrable
      (apm_m02j02_hermiteFunctionDeriv n * φ) volume :=
    apm_m02j02_integrable_continuous_mul_compact _ _ hdfcont hφ.continuous hφc
  have hi0 : Integrable
      (apm_m02j02_hermiteFunction n * φ) volume :=
    apm_m02j02_integrable_continuous_mul_compact _ _ hfcont hφ.continuous hφc
  exact MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ ↦ apm_m02j02_hermiteFunction_hasDerivAt n x)
    (fun x _ ↦ (hφ.differentiable (by simp) x).hasDerivAt)
    hi1 hi2 hi0

lemma apm_m02j02_oddHermite_weakDerivative_Ioi (n : ℕ) :
    apm_m02j02_IsWeakDerivativeOn (Ioi (0 : ℝ))
      (apm_m02j02_hermiteFunction (2 * n + 1))
      (apm_m02j02_hermiteFunctionDeriv (2 * n + 1)) := by
  intro φ hφ hφc _
  let f := apm_m02j02_hermiteFunction (2 * n + 1)
  let df := apm_m02j02_hermiteFunctionDeriv (2 * n + 1)
  have hfcont : Continuous f :=
    (apm_m02j02_hermiteFunction_contDiff (2 * n + 1)).continuous
  have hdfcont : Continuous df :=
    apm_m02j02_hermiteFunctionDeriv_continuous (2 * n + 1)
  have hφdcont : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have hi1 : IntegrableOn (f * deriv φ) (Ioi 0) volume :=
    (apm_m02j02_integrable_continuous_mul_compact _ _ hfcont hφdcont
      hφc.deriv).integrableOn
  have hi2 : IntegrableOn (df * φ) (Ioi 0) volume :=
    (apm_m02j02_integrable_continuous_mul_compact _ _ hdfcont hφ.continuous
      hφc).integrableOn
  have hzero : Tendsto (f * φ) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    have hprod := (hfcont.tendsto 0).mul (hφ.continuous.tendsto 0)
    simpa [f, apm_m02j02_hermiteFunction_odd_zero n] using
      hprod.mono_left inf_le_left
  have hinfty : Tendsto (f * φ) atTop (nhds 0) := by
    rw [hasCompactSupport_iff_eventuallyEq,
      Filter.coclosedCompact_eq_cocompact] at hφc
    have heq : (f * φ) =ᶠ[atTop] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [hφc.filter_mono atTop_le_cocompact] with x hx
      simp [Pi.mul_apply, hx]
    exact tendsto_const_nhds.congr' heq.symm
  simpa [f, df] using
    (MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
      (u := f) (v := φ) (u' := df) (v' := deriv φ)
      (fun x _ ↦ apm_m02j02_hermiteFunction_hasDerivAt (2 * n + 1) x)
      (fun x _ ↦ (hφ.differentiable (by simp) x).hasDerivAt)
      hi1 hi2 hzero hinfty)

lemma apm_m02j02_sine_weakDerivative_Ioo (n : ℕ) :
    apm_m02j02_IsWeakDerivativeOn (Ioo (0 : ℝ) 1)
      (apm_m02j02_sine n) (apm_m02j02_sineDeriv n) := by
  intro φ hφ _ _
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (u := apm_m02j02_sine n) (v := φ)
    (u' := apm_m02j02_sineDeriv n) (v' := deriv φ)
    (fun x _ ↦ apm_m02j02_hasDerivAt_sine n x)
    (fun x _ ↦ (hφ.differentiable (by simp) x).hasDerivAt)
    ((apm_m02j02_sineDeriv_contDiff n).continuous.intervalIntegrable 0 1)
    ((hφ.continuous_deriv (by simp)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at h
  simpa [apm_m02j02_sine_zero n, apm_m02j02_sine_one n] using h

private lemma apm_m02j02_integral_cos_nat_mul_pi (k : ℕ) (hk : k ≠ 0) :
    (∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x)) = 0 := by
  let c : ℝ := (k : ℝ) * Real.pi
  have hc : c ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hk) Real.pi_ne_zero
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => Real.sin (c * x) / c)
    (f' := fun x : ℝ => Real.cos (c * x))
    (a := (0 : ℝ)) (b := 1)
    (fun x _ => by
      convert ((Real.hasDerivAt_sin (c * x)).comp x
        ((hasDerivAt_id x).const_mul c)).div_const c using 1 <;>
        field_simp)
    ((show Continuous (fun x : ℝ => Real.cos (c * x)) by fun_prop).intervalIntegrable 0 1)
  simpa [c, Real.sin_nat_mul_pi] using h

private lemma apm_m02j02_sine_orthogonal {n m : ℕ} (hnm : n ≠ m) :
    (∫ x in (0 : ℝ)..1, apm_m02j02_sine n x * apm_m02j02_sine m x) = 0 := by
  wlog hlt : n < m generalizing n m
  · have hmn : m < n := lt_of_le_of_ne (Nat.le_of_not_gt hlt) hnm.symm
    rw [show (∫ x in (0 : ℝ)..1, apm_m02j02_sine n x * apm_m02j02_sine m x) =
        ∫ x in (0 : ℝ)..1, apm_m02j02_sine m x * apm_m02j02_sine n x by
      apply intervalIntegral.integral_congr
      intro x _
      ring]
    exact this hnm.symm hmn
  have hd : m - n ≠ 0 := by omega
  have hs : m + n + 2 ≠ 0 := by omega
  have hdiff := apm_m02j02_integral_cos_nat_mul_pi (m - n) hd
  have hsum := apm_m02j02_integral_cos_nat_mul_pi (m + n + 2) hs
  have hprod : ∀ x : ℝ,
      2 * (apm_m02j02_sine n x * apm_m02j02_sine m x) =
        Real.cos (((m - n : ℕ) : ℝ) * Real.pi * x) -
          Real.cos (((m + n + 2 : ℕ) : ℝ) * Real.pi * x) := by
    intro x
    rw [apm_m02j02_sine, apm_m02j02_sine]
    calc
      2 * (Real.sin ((n + 1 : ℝ) * Real.pi * x) *
          Real.sin ((m + 1 : ℝ) * Real.pi * x)) =
          2 * Real.sin ((m + 1 : ℝ) * Real.pi * x) *
            Real.sin ((n + 1 : ℝ) * Real.pi * x) := by ring
      _ = Real.cos (((m + 1 : ℝ) * Real.pi * x) -
            ((n + 1 : ℝ) * Real.pi * x)) -
          Real.cos (((m + 1 : ℝ) * Real.pi * x) +
            ((n + 1 : ℝ) * Real.pi * x)) :=
        Real.two_mul_sin_mul_sin _ _
      _ = _ := by
        rw [Nat.cast_sub (Nat.le_of_lt hlt)]
        push_cast
        congr 2 <;> ring
  have hi : IntervalIntegrable
      (fun x : ℝ => apm_m02j02_sine n x * apm_m02j02_sine m x) volume 0 1 :=
    ((apm_m02j02_sine_contDiff n).continuous.mul
      (apm_m02j02_sine_contDiff m).continuous).intervalIntegrable 0 1
  calc
    (∫ x in (0 : ℝ)..1, apm_m02j02_sine n x * apm_m02j02_sine m x) =
        (2 * (∫ x in (0 : ℝ)..1,
          apm_m02j02_sine n x * apm_m02j02_sine m x)) / 2 := by ring
    _ = (∫ x in (0 : ℝ)..1,
          (2 * (apm_m02j02_sine n x * apm_m02j02_sine m x))) / 2 := by
        rw [intervalIntegral.integral_const_mul]
    _ = 0 := by
      rw [intervalIntegral.integral_congr (fun x _ => hprod x),
        intervalIntegral.integral_sub]
      · rw [hdiff, hsum]
        norm_num
      · exact (show Continuous (fun x : ℝ =>
            Real.cos (((m - n : ℕ) : ℝ) * Real.pi * x)) by fun_prop).intervalIntegrable 0 1
      · exact (show Continuous (fun x : ℝ =>
            Real.cos (((m + n + 2 : ℕ) : ℝ) * Real.pi * x)) by fun_prop).intervalIntegrable 0 1

private lemma apm_m02j02_sine_norm_sq (n : ℕ) :
    (∫ x in (0 : ℝ)..1, apm_m02j02_sine n x * apm_m02j02_sine n x) = 1 / 2 := by
  have hk : 2 * (n + 1) ≠ 0 := by omega
  have hcos := apm_m02j02_integral_cos_nat_mul_pi (2 * (n + 1)) hk
  have hcos' : (∫ x in (0 : ℝ)..1,
      Real.cos (2 * (n + 1 : ℝ) * Real.pi * x)) = 0 := by
    convert hcos using 1 <;> push_cast <;> ring
  have hpoint : ∀ x : ℝ,
      2 * (apm_m02j02_sine n x * apm_m02j02_sine n x) =
        1 - Real.cos (((2 * (n + 1) : ℕ) : ℝ) * Real.pi * x) := by
    intro x
    rw [apm_m02j02_sine]
    have h := Real.two_mul_sin_mul_sin
      ((n + 1 : ℝ) * Real.pi * x) ((n + 1 : ℝ) * Real.pi * x)
    rw [sub_self, Real.cos_zero] at h
    calc
      2 * (Real.sin ((n + 1 : ℝ) * Real.pi * x) *
          Real.sin ((n + 1 : ℝ) * Real.pi * x)) =
          1 - Real.cos (((n + 1 : ℝ) * Real.pi * x) +
            ((n + 1 : ℝ) * Real.pi * x)) := by simpa [mul_assoc] using h
      _ = _ := by push_cast; congr 2 <;> ring
  have hi : IntervalIntegrable
      (fun x : ℝ => apm_m02j02_sine n x * apm_m02j02_sine n x) volume 0 1 :=
    ((apm_m02j02_sine_contDiff n).continuous.mul
      (apm_m02j02_sine_contDiff n).continuous).intervalIntegrable 0 1
  have htwo : 2 * (∫ x in (0 : ℝ)..1,
      apm_m02j02_sine n x * apm_m02j02_sine n x) = 1 := by
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_congr (fun x _ => hpoint x),
      intervalIntegral.integral_sub]
    · simp [hcos']
    · exact intervalIntegrable_const
    · exact (show Continuous (fun x : ℝ =>
          Real.cos (((2 * (n + 1) : ℕ) : ℝ) * Real.pi * x)) by
            fun_prop).intervalIntegrable 0 1
  linarith

lemma apm_m02j02_sine_linearIndependent :
    LinearIndependent ℝ apm_m02j02_sine := by
  rw [linearIndependent_iff']
  intro s g h i hi
  have hpoint : ∀ x : ℝ, (∑ j ∈ s, g j * apm_m02j02_sine j x) = 0 := by
    intro x
    simpa [Pi.smul_apply] using congrFun h x
  have hint : (∫ x in (0 : ℝ)..1,
      (∑ j ∈ s, g j * apm_m02j02_sine j x) * apm_m02j02_sine i x) = 0 := by
    rw [intervalIntegral.integral_congr (fun x _ => by rw [hpoint x, zero_mul])]
    simp
  simp_rw [Finset.sum_mul] at hint
  rw [intervalIntegral.integral_finset_sum] at hint
  · have hcollapse : (∑ j ∈ s, ∫ x in (0 : ℝ)..1,
          (g j * apm_m02j02_sine j x) * apm_m02j02_sine i x) = g i / 2 := by
      rw [Finset.sum_eq_single i]
      · rw [show (∫ x in (0 : ℝ)..1,
            (g i * apm_m02j02_sine i x) * apm_m02j02_sine i x) =
            ∫ x in (0 : ℝ)..1,
              g i * (apm_m02j02_sine i x * apm_m02j02_sine i x) by
              apply intervalIntegral.integral_congr
              intro x _
              ring]
        rw [intervalIntegral.integral_const_mul]
        rw [apm_m02j02_sine_norm_sq]
        ring
      · intro j hj hji
        rw [show (∫ x in (0 : ℝ)..1,
            (g j * apm_m02j02_sine j x) * apm_m02j02_sine i x) =
            ∫ x in (0 : ℝ)..1,
              g j * (apm_m02j02_sine j x * apm_m02j02_sine i x) by
              apply intervalIntegral.integral_congr
              intro x _
              ring]
        rw [intervalIntegral.integral_const_mul]
        rw [apm_m02j02_sine_orthogonal hji]
        simp
      · exact fun hni => (hni hi).elim
    rw [hcollapse] at hint
    linarith
  · intro j hj
    exact (((apm_m02j02_sine_contDiff j).continuous.const_mul (g j)).mul
      (apm_m02j02_sine_contDiff i).continuous).intervalIntegrable 0 1

lemma apm_m02j02_sinePair_linearIndependent :
    LinearIndependent ℝ (fun n ↦
      (apm_m02j02_sine n, apm_m02j02_sineDeriv n)) := by
  apply LinearIndependent.of_comp (LinearMap.fst ℝ (ℝ → ℝ) (ℝ → ℝ))
  simpa [Function.comp_def] using apm_m02j02_sine_linearIndependent

lemma apm_m02j02_sine_inH10_of_approx (n : ℕ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ φ : ℝ → ℝ,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo (0 : ℝ) 1 ∧
      eLpNorm (apm_m02j02_sine n - φ) 2 (volume.restrict (Ioo (0 : ℝ) 1)) +
        eLpNorm (apm_m02j02_sineDeriv n - deriv φ) 2
          (volume.restrict (Ioo (0 : ℝ) 1)) < ENNReal.ofReal ε) :
    apm_m02j02_InH10 (Ioo (0 : ℝ) 1)
      (apm_m02j02_sine n) (apm_m02j02_sineDeriv n) := by
  exact ⟨apm_m02j02_sine_memLp_two_Ioo n,
    apm_m02j02_sineDeriv_memLp_two_Ioo n,
    apm_m02j02_sine_weakDerivative_Ioo n, happrox⟩

lemma apm_m02j02_oddHermite_inH10_of_approx (n : ℕ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ φ : ℝ → ℝ,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioi (0 : ℝ) ∧
      eLpNorm (apm_m02j02_hermiteFunction (2 * n + 1) - φ) 2
          (volume.restrict (Ioi (0 : ℝ))) +
        eLpNorm (apm_m02j02_hermiteFunctionDeriv (2 * n + 1) - deriv φ) 2
          (volume.restrict (Ioi (0 : ℝ))) < ENNReal.ofReal ε) :
    apm_m02j02_InH10 (Ioi (0 : ℝ))
      (apm_m02j02_hermiteFunction (2 * n + 1))
      (apm_m02j02_hermiteFunctionDeriv (2 * n + 1)) := by
  exact ⟨apm_m02j02_oddHermite_memLp_two_Ioi n,
    apm_m02j02_oddHermiteDeriv_memLp_two_Ioi n,
    apm_m02j02_oddHermite_weakDerivative_Ioi n, happrox⟩

lemma apm_m02j02_hermite_inH10_of_approx (n : ℕ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ φ : ℝ → ℝ,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ (Set.univ : Set ℝ) ∧
      eLpNorm (apm_m02j02_hermiteFunction n - φ) 2 volume +
        eLpNorm (apm_m02j02_hermiteFunctionDeriv n - deriv φ) 2 volume <
          ENNReal.ofReal ε) :
    apm_m02j02_InH10 Set.univ
      (apm_m02j02_hermiteFunction n) (apm_m02j02_hermiteFunctionDeriv n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Measure.restrict_univ] using
      apm_m02j02_hermiteFunction_memLp_two n
  · simpa only [Measure.restrict_univ] using
      apm_m02j02_hermiteFunctionDeriv_memLp_two n
  · simpa only [Measure.restrict_univ] using
      apm_m02j02_hermiteFunction_weakDerivative_univ n
  · simpa only [Measure.restrict_univ] using happrox

lemma apm_m02j02_sine_basis_of_approx_density
    (happrox : ∀ n ε, 0 < ε → ∃ φ : ℝ → ℝ,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo (0 : ℝ) 1 ∧
      eLpNorm (apm_m02j02_sine n - φ) 2 (volume.restrict (Ioo (0 : ℝ) 1)) +
        eLpNorm (apm_m02j02_sineDeriv n - deriv φ) 2
          (volume.restrict (Ioo (0 : ℝ) 1)) < ENNReal.ofReal ε)
    (hdense : ∀ u du : ℝ → ℝ, apm_m02j02_InH10 (Ioo (0 : ℝ) 1) u du →
      ∀ ε : ℝ, 0 < ε → ∃ c : ℕ →₀ ℝ,
        eLpNorm (u - c.sum fun n a ↦ a • apm_m02j02_sine n) 2
            (volume.restrict (Ioo (0 : ℝ) 1)) +
          eLpNorm (du - c.sum fun n a ↦ a • apm_m02j02_sineDeriv n) 2
            (volume.restrict (Ioo (0 : ℝ) 1)) < ENNReal.ofReal ε) :
    apm_m02j02_IsH10Basis (Ioo (0 : ℝ) 1)
      apm_m02j02_sine apm_m02j02_sineDeriv := by
  exact ⟨fun n => apm_m02j02_sine_inH10_of_approx n (happrox n),
    apm_m02j02_sinePair_linearIndependent, hdense⟩

lemma apm_m02j02_oddHermite_basis_of_approx_density
    (hmem : ∀ n, apm_m02j02_InH10 (Ioi (0 : ℝ))
      (apm_m02j02_hermiteFunction (2 * n + 1))
      (apm_m02j02_hermiteFunctionDeriv (2 * n + 1)))
    (hdense : ∀ u du : ℝ → ℝ, apm_m02j02_InH10 (Ioi (0 : ℝ)) u du →
      ∀ ε : ℝ, 0 < ε → ∃ c : ℕ →₀ ℝ,
        eLpNorm (u - c.sum fun n a ↦ a • apm_m02j02_hermiteFunction (2*n+1)) 2
            (volume.restrict (Ioi (0 : ℝ))) +
          eLpNorm (du - c.sum fun n a ↦ a •
            apm_m02j02_hermiteFunctionDeriv (2*n+1)) 2
            (volume.restrict (Ioi (0 : ℝ))) < ENNReal.ofReal ε) :
    apm_m02j02_IsH10Basis (Ioi (0 : ℝ))
      (fun n ↦ apm_m02j02_hermiteFunction (2 * n + 1))
      (fun n ↦ apm_m02j02_hermiteFunctionDeriv (2 * n + 1)) := by
  exact ⟨hmem, apm_m02j02_oddHermitePair_linearIndependent, hdense⟩

lemma apm_m02j02_hermite_basis_of_approx_density
    (hmem : ∀ n, apm_m02j02_InH10 Set.univ
      (apm_m02j02_hermiteFunction n) (apm_m02j02_hermiteFunctionDeriv n))
    (hdense : ∀ u du : ℝ → ℝ, apm_m02j02_InH10 Set.univ u du →
      ∀ ε : ℝ, 0 < ε → ∃ c : ℕ →₀ ℝ,
        eLpNorm (u - c.sum fun n a ↦ a • apm_m02j02_hermiteFunction n) 2
            (volume.restrict Set.univ) +
          eLpNorm (du - c.sum fun n a ↦ a • apm_m02j02_hermiteFunctionDeriv n) 2
            (volume.restrict Set.univ) < ENNReal.ofReal ε) :
    apm_m02j02_IsH10Basis Set.univ
      apm_m02j02_hermiteFunction apm_m02j02_hermiteFunctionDeriv := by
  exact ⟨hmem, apm_m02j02_hermitePair_linearIndependent, hdense⟩

/-- A concrete nonzero smooth test function exists in the interval test space
used by the frozen graph-norm closure. -/
lemma apm_m02j02_exists_interval_testFunction :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ Ioo (0 : ℝ) 1 ∧ φ (1 / 2 : ℝ) = 1 := by
  have hmem : Ioo (0 : ℝ) 1 ∈ nhds (1 / 2 : ℝ) := by
    exact Ioo_mem_nhds (by norm_num) (by norm_num)
  obtain ⟨φ, hsub, hcomp, hsmooth, -, hone⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hmem
  exact ⟨φ, hsmooth, hcomp, hsub, hone⟩

/-- A concrete nonzero smooth test function exists in the half-line test
space used by the odd-Hermite closure. -/
lemma apm_m02j02_exists_halfline_testFunction :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ Ioi (0 : ℝ) ∧ φ 1 = 1 := by
  have hmem : Ioi (0 : ℝ) ∈ nhds (1 : ℝ) := by
    exact Ioi_mem_nhds (by norm_num)
  obtain ⟨φ, hsub, hcomp, hsmooth, -, hone⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hmem
  exact ⟨φ, hsmooth, hcomp, hsub, hone⟩

lemma apm_m02j02_exists_zero_near_zero_of_tsupport_subset_Ioi
    {f : ℝ → ℝ} (hsub : tsupport f ⊆ Ioi (0 : ℝ)) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, |x| < r → f x = 0 := by
  have hz : (0 : ℝ) ∉ tsupport f := by
    intro hz
    have hz' : (0 : ℝ) < 0 := hsub hz
    exact (lt_irrefl 0 hz')
  have hnhds : (tsupport f)ᶜ ∈ nhds (0 : ℝ) :=
    isOpen_compl_iff.2 isClosed_closure |>.mem_nhds hz
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 hnhds
  refine ⟨r, hr, fun x hx => ?_⟩
  have hxball : x ∈ Metric.ball (0 : ℝ) r := by
    simpa [Real.dist_eq] using hx
  have hxt : x ∉ tsupport f := hrsub hxball
  exact not_ne_iff.mp (fun hne => hxt (subset_closure hne))

lemma apm_m02j02_oddExtension_contDiff
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x : ℝ => f x - f (-x)) := by
  exact hf.sub (hf.comp (by fun_prop))

lemma apm_m02j02_oddExtension_hasCompactSupport
    {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun x : ℝ => f x - f (-x)) := by
  exact hf.sub (hf.comp_homeomorph (Homeomorph.neg ℝ))

lemma apm_m02j02_oddExtension_neg (f : ℝ → ℝ) (x : ℝ) :
    (f (-x) - f (-(-x))) = -(f x - f (-x)) := by
  simp

lemma apm_m02j02_oddExtension_eq_of_pos
    {f : ℝ → ℝ} (hsub : tsupport f ⊆ Ioi (0 : ℝ))
    {x : ℝ} (hx : 0 < x) :
    f x - f (-x) = f x := by
  have hneg : f (-x) = 0 := by
    by_contra hn
    have hmem : -x ∈ tsupport f := subset_closure hn
    have hpos : 0 < -x := hsub hmem
    linarith
  rw [hneg, sub_zero]

lemma apm_m02j02_oddExtension_tsupport_subset_Ioo
    {f : ℝ → ℝ} (hsub : tsupport f ⊆ Ioo (0 : ℝ) 1) :
    tsupport (fun x : ℝ => f x - f (-x)) ⊆ Ioo (-1 : ℝ) 1 := by
  let S : Set ℝ := tsupport f ∪ (fun x : ℝ => -x) ⁻¹' tsupport f
  have hclosed : IsClosed S := isClosed_closure.union
    (isClosed_closure.preimage (by fun_prop))
  have hsupp : Function.support (fun x : ℝ => f x - f (-x)) ⊆ S := by
    intro x hx
    by_cases hfx : f x = 0
    · have hfn : f (-x) ≠ 0 := by
        intro hzero
        exact hx (by simp [hfx, hzero])
      exact Or.inr (subset_closure hfn)
    · exact Or.inl (subset_closure hfx)
  have hts : tsupport (fun x : ℝ => f x - f (-x)) ⊆ S :=
    closure_minimal hsupp hclosed
  intro x hx
  rcases hts hx with hx | hx
  · have h := hsub hx
    exact ⟨lt_trans (by norm_num) h.1, h.2⟩
  · have hx' : -x ∈ tsupport f := hx
    have h := hsub hx'
    constructor <;> linarith [h.1, h.2]

lemma apm_m02j02_deriv_oddExtension
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝ) :
    deriv (fun y : ℝ => f y - f (-y)) x = deriv f x + deriv f (-x) := by
  have hout : HasDerivAt f (deriv f (-x)) (-x) :=
    (hf.differentiable (by simp) (-x)).hasDerivAt
  have hin : HasDerivAt (fun y : ℝ => -y) (-1) x :=
    (hasDerivAt_id x).neg
  have hneg : HasDerivAt (fun y : ℝ => f (-y)) (-deriv f (-x)) x := by
    simpa only [Function.comp_apply, mul_neg, mul_one] using hout.comp x hin
  exact ((hf.differentiable (by simp) x).hasDerivAt.sub hneg).deriv.trans (by ring)

lemma apm_m02j02_deriv_oddExtension_even
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝ) :
    deriv (fun y : ℝ => f y - f (-y)) (-x) =
      deriv (fun y : ℝ => f y - f (-y)) x := by
  rw [apm_m02j02_deriv_oddExtension hf,
    apm_m02j02_deriv_oddExtension hf]
  simp only [neg_neg]
  exact add_comm _ _

lemma apm_m02j02_fourierCoeffOn_deriv_eq_mul
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hsub : tsupport f ⊆ Ioo (-1 : ℝ) 1) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
        (fun x : ℝ => ((deriv f x : ℝ) : ℂ)) n =
      (Real.pi * Complex.I * n) *
        fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
          (fun x : ℝ => (f x : ℂ)) n := by
  have hfm : f (-1) = 0 := by
    by_contra hne
    have hm := hsub (subset_closure hne)
    exact (lt_irrefl (-1 : ℝ)) hm.1
  have hfp : f 1 = 0 := by
    by_contra hne
    have hp := hsub (subset_closure hne)
    exact (lt_irrefl (1 : ℝ)) hp.2
  have hhas : ∀ x : ℝ, x ∈ uIcc (-1 : ℝ) 1 →
      HasDerivAt (fun y : ℝ => (f y : ℂ)) ((deriv f x : ℝ) : ℂ) x := by
    intro x hx
    exact ((hf.differentiable (by simp) x).hasDerivAt).ofReal_comp
  have hint : IntervalIntegrable (fun x : ℝ => ((deriv f x : ℝ) : ℂ)) volume (-1) 1 :=
    (Complex.continuous_ofReal.comp (hf.continuous_deriv (by simp))).intervalIntegrable _ _
  have h := fourierCoeffOn_of_hasDerivAt
    (by norm_num : (-1 : ℝ) < 1) hn hhas hint
  simp [hfm, hfp] at h
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp [hπ, hI, hn'] at h
  have hi : Complex.I ^ 2 = (-1 : ℂ) := Complex.I_sq
  linear_combination (-Complex.I / 2 : ℂ) * h +
    fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
      (fun x : ℝ => ((deriv f x : ℝ) : ℂ)) n * hi

lemma apm_m02j02_fourierCoeffOn_deriv_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hsub : tsupport f ⊆ Ioo (-1 : ℝ) 1) :
    fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
      (fun x : ℝ => ((deriv f x : ℝ) : ℂ)) 0 = 0 := by
  let FC : ℝ → ℂ := fun x => (f x : ℂ)
  have hfm : FC (-1) = 0 := by
    change (f (-1) : ℂ) = 0
    congr 1
    by_contra hne
    exact (lt_irrefl (-1 : ℝ)) (hsub (subset_closure hne)).1
  have hfp : FC 1 = 0 := by
    change (f 1 : ℂ) = 0
    congr 1
    by_contra hne
    exact (lt_irrefl (1 : ℝ)) (hsub (subset_closure hne)).2
  have hderiv (x : ℝ) : deriv FC x = ((deriv f x : ℝ) : ℂ) := by
    exact ((hf.differentiable (by simp) x).hasDerivAt.ofReal_comp).deriv
  have hint : IntervalIntegrable (deriv FC) volume (-1) 1 :=
    ((Complex.continuous_ofReal.comp (hf.continuous_deriv (by simp))).congr
      (fun x => (hderiv x).symm)).intervalIntegrable _ _
  have hfund := intervalIntegral.integral_deriv_eq_sub
    (f := FC) (a := (-1 : ℝ)) (b := 1)
    (fun x hx => ((hf.differentiable (by simp) x).hasDerivAt.ofReal_comp).differentiableAt)
    hint
  rw [hfm, hfp, sub_self] at hfund
  have hcast : (∫ x in (-1 : ℝ)..1, ((deriv f x : ℝ) : ℂ)) = 0 := by
    calc
      (∫ x in (-1 : ℝ)..1, ((deriv f x : ℝ) : ℂ)) =
          ∫ x in (-1 : ℝ)..1, deriv FC x :=
        intervalIntegral.integral_congr (fun x _ => (hderiv x).symm)
      _ = 0 := hfund
  rw [fourierCoeffOn_eq_integral]
  simp only [neg_zero, fourier_zero, one_smul]
  rw [hcast]
  simp

lemma apm_m02j02_fourierCoeffOn_deriv_eq_mul_all
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hsub : tsupport f ⊆ Ioo (-1 : ℝ) 1) (n : ℤ) :
    fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
        (fun x : ℝ => ((deriv f x : ℝ) : ℂ)) n =
      (Real.pi * Complex.I * n) *
        fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
          (fun x : ℝ => (f x : ℂ)) n := by
  by_cases hn : n = 0
  · subst n
    rw [apm_m02j02_fourierCoeffOn_deriv_zero hf hsub]
    simp
  · exact apm_m02j02_fourierCoeffOn_deriv_eq_mul hf hsub n hn

lemma apm_m02j02_fourier_two_neg (n : ℤ) (x : ℝ) :
    @fourier (2 : ℝ) n ((-x : ℝ) : AddCircle (2 : ℝ)) =
      @fourier (2 : ℝ) (-n) (x : AddCircle (2 : ℝ)) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  congr 1
  push_cast
  ring

lemma apm_m02j02_fourierCoeffOn_neg_eq_neg_of_odd
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hodd : ∀ x : ℝ, f (-x) = -f x) (n : ℤ) :
    fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
        (fun x : ℝ => (f x : ℂ)) (-n) =
      -fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
        (fun x : ℝ => (f x : ℂ)) n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [neg_neg]
  have href := intervalIntegral.integral_comp_neg
    (f := fun x : ℝ =>
      (@fourier (2 : ℝ) (-n) (x : AddCircle (2 : ℝ))) * (f x : ℂ))
    (a := (-1 : ℝ)) (b := 1)
  simp only [neg_neg] at href
  have hpoint : (fun x : ℝ =>
      (@fourier (2 : ℝ) (-n) ((-x : ℝ) : AddCircle (2 : ℝ))) * (f (-x) : ℂ)) =
      fun x : ℝ => -((@fourier (2 : ℝ) n (x : AddCircle (2 : ℝ))) * (f x : ℂ)) := by
    funext x
    rw [apm_m02j02_fourier_two_neg, hodd]
    push_cast
    ring
  rw [hpoint, intervalIntegral.integral_neg] at href
  norm_num at href
  let A : ℂ := ∫ x in (-1 : ℝ)..1,
    (@fourier (2 : ℝ) n (x : AddCircle (2 : ℝ))) * (f x : ℂ)
  let B : ℂ := ∫ x in (-1 : ℝ)..1,
    (@fourier (2 : ℝ) (-n) (x : AddCircle (2 : ℝ))) * (f x : ℂ)
  have hrefAB : -A = B := by
    simpa [A, B, fourier_coe_apply] using href
  have htwo : (1 / ((1 : ℝ) - (-1 : ℝ)) : ℝ) = 1 / 2 := by norm_num
  rw [htwo]
  simp only [smul_eq_mul]
  norm_num
  have href' := neg_eq_iff_eq_neg.mp href
  rw [href']
  simp

lemma apm_m02j02_fourierCoeffOn_zero_eq_zero_of_odd
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hodd : ∀ x : ℝ, f (-x) = -f x) :
    fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
        (fun x : ℝ => (f x : ℂ)) 0 = 0 := by
  have h := apm_m02j02_fourierCoeffOn_neg_eq_neg_of_odd hf hodd 0
  simp only [neg_zero] at h
  linear_combination (1 / 2 : ℂ) * h

lemma apm_m02j02_intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    (∫ x in a..b, starRingEnd ℂ (f x)) =
      starRingEnd ℂ (∫ x in a..b, f x) := by
  unfold intervalIntegral
  rw [map_sub]
  exact congrArg₂ (· - ·)
    (@integral_conj ℝ _ (volume.restrict (Ioc a b)) ℂ _ f)
    (@integral_conj ℝ _ (volume.restrict (Ioc b a)) ℂ _ f)

local instance apm_m02j02_fact_two_pos_early : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
local instance apm_m02j02_fact_two_expr_pos : Fact (0 < (1 - (-1 : ℝ))) := ⟨by norm_num⟩

lemma apm_m02j02_star_liftIoc_real {T : ℝ} [Fact (0 < T)]
    (a : ℝ) (f : ℝ → ℝ) (x : AddCircle T) :
    (starRingEnd ℂ) (AddCircle.liftIoc T a
      (fun y : ℝ => (f y : ℂ)) x) =
      AddCircle.liftIoc T a (fun y : ℝ => (f y : ℂ)) x := by
  calc
    (starRingEnd ℂ) (AddCircle.liftIoc T a
        (fun y : ℝ => (f y : ℂ)) x) =
      AddCircle.liftIoc T a
        ((starRingEnd ℂ) ∘ fun y : ℝ => (f y : ℂ)) x :=
      (AddCircle.liftIoc_comp_apply).symm
    _ = AddCircle.liftIoc T a (fun y : ℝ => (f y : ℂ)) x := by
      congr 1
      funext y
      simp

lemma apm_m02j02_conj_fourierCoeffOn_real (f : ℝ → ℝ) (n : ℤ) :
    starRingEnd ℂ
        (fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
          (fun x : ℝ => (f x : ℂ)) n) =
      fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
        (fun x : ℝ => (f x : ℂ)) (-n) := by
  letI : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
  unfold fourierCoeffOn fourierCoeff
  change (starRingEnd ℂ) (∫ t : AddCircle (1 - (-1 : ℝ)),
      (@fourier (1 - (-1 : ℝ)) (-n) t) •
        AddCircle.liftIoc (1 - (-1 : ℝ)) (-1) (fun x : ℝ => (f x : ℂ)) t
        ∂AddCircle.haarAddCircle) = _
  calc
    _ = ∫ t : AddCircle (1 - (-1 : ℝ)), (starRingEnd ℂ)
          ((@fourier (1 - (-1 : ℝ)) (-n) t) •
            AddCircle.liftIoc (1 - (-1 : ℝ)) (-1) (fun x : ℝ => (f x : ℂ)) t)
          ∂AddCircle.haarAddCircle := (@integral_conj _ _ _ ℂ _ _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [smul_eq_mul, map_mul, fourier_neg]
      rw [apm_m02j02_star_liftIoc_real]
      simp

lemma apm_m02j02_fourierCoeffOn_odd_is_pure_imaginary
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hodd : ∀ x : ℝ, f (-x) = -f x) (n : ℤ) :
    (fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
      (fun x : ℝ => (f x : ℂ)) n).re = 0 := by
  have hreal := apm_m02j02_conj_fourierCoeffOn_real f n
  have hoddCoeff := apm_m02j02_fourierCoeffOn_neg_eq_neg_of_odd hf hodd n
  rw [hoddCoeff] at hreal
  have hre := congrArg Complex.re hreal
  simp only [Complex.neg_re, Complex.conj_re] at hre
  linarith

lemma apm_m02j02_fourierCoeffOn_odd_eq_im_mul_I
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hodd : ∀ x : ℝ, f (-x) = -f x) (n : ℤ) :
    fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
        (fun x : ℝ => (f x : ℂ)) n =
      ((fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
        (fun x : ℝ => (f x : ℂ)) n).im : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [apm_m02j02_fourierCoeffOn_odd_is_pure_imaginary hf hodd n]
  · simp

lemma apm_m02j02_odd_fourier_pair_eq_sine
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hodd : ∀ x : ℝ, f (-x) = -f x) (n : ℤ) (x : ℝ) :
    fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
          (fun y : ℝ => (f y : ℂ)) n *
        (@fourier (2 : ℝ) n (x : AddCircle (2 : ℝ))) +
      fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
          (fun y : ℝ => (f y : ℂ)) (-n) *
        (@fourier (2 : ℝ) (-n) (x : AddCircle (2 : ℝ))) =
      ((-2 * (fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
          (fun y : ℝ => (f y : ℂ)) n).im *
        Real.sin (Real.pi * (n : ℝ) * x) : ℝ) : ℂ) := by
  rw [apm_m02j02_fourierCoeffOn_neg_eq_neg_of_odd hf hodd n]
  rw [apm_m02j02_fourierCoeffOn_odd_eq_im_mul_I hf hodd n]
  rw [fourier_coe_apply, fourier_coe_apply]
  have hp :
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) / 2 =
        ((Real.pi * (n : ℝ) * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hn :
      -(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)) / 2 =
        ((-(Real.pi * (n : ℝ) * x) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  norm_num
  rw [hp, hn, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma apm_m02j02_HasSum_tendsto_symmetricIcc
    {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    {f : ℤ → E} {a : E} (h : HasSum f a) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, f n)
      atTop (nhds a) := by
  rw [← SummationFilter.hasSum_symmetricIcc_iff]
  rw [HasSum] at h ⊢
  exact h.mono_left SummationFilter.LeAtTop.le_atTop

local instance apm_m02j02_fact_two_pos : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩

lemma apm_m02j02_tendsto_fourier_series_symmetricIcc
    (U : Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ)))) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        fourierCoeff U n • fourierLp 2 n)
      atTop (nhds U) := by
  exact apm_m02j02_HasSum_tendsto_symmetricIcc
    (hasSum_fourier_series_L2 U)

set_option maxHeartbeats 800000 in
lemma apm_m02j02_exists_common_symmetric_fourier_truncation
    (U V : Lp ℂ 2
      (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ N : ℕ,
      edist (∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          fourierCoeff U n • fourierLp 2 n) U < ε ∧
        edist (∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          fourierCoeff V n • fourierLp 2 n) V < ε := by
  obtain ⟨Nu, hNu⟩ := EMetric.tendsto_atTop.mp
    (apm_m02j02_tendsto_fourier_series_symmetricIcc U) ε hε
  obtain ⟨Nv, hNv⟩ := EMetric.tendsto_atTop.mp
    (apm_m02j02_tendsto_fourier_series_symmetricIcc V) ε hε
  exact ⟨max Nu Nv,
    hNu _ (le_max_left _ _), hNv _ (le_max_right _ _)⟩

lemma apm_m02j02_fourierCoeff_toLp_eq_representative
    (f : AddCircle (2 : ℝ) → ℂ) (h : MemLp f 2 AddCircle.haarAddCircle)
    (n : ℤ) : fourierCoeff (h.toLp f) n = fourierCoeff f n := by
  unfold fourierCoeff
  apply integral_congr_ae
  filter_upwards [h.coeFn_toLp] with x hx
  rw [hx]

lemma apm_m02j02_fourierCoeff_liftIoc_two_eq_on
    (f : ℝ → ℂ) (n : ℤ) (hab : (-1 : ℝ) < 1) :
    fourierCoeff (AddCircle.liftIoc 2 (-1) f) n =
      fourierCoeffOn hab f n := by
  rw [fourierCoeff_eq_intervalIntegral _ _ (-1)]
  rw [fourierCoeffOn_eq_integral f n hab]
  norm_num
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ (-1 : ℝ) := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with x hne hx
  change (starRingEnd ℂ)
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) / 2)) *
      AddCircle.liftIoc 2 (-1) f (x : AddCircle (2 : ℝ)) =
    (starRingEnd ℂ)
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) / 2)) * f x
  rw [AddCircle.liftIoc_coe_apply]
  rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  exact ⟨hx.1, by linarith [hx.2]⟩

lemma apm_m02j02_fourierCoeff_toLp_liftIoc_eq_on
    (f : ℝ → ℂ)
    (h : MemLp (AddCircle.liftIoc 2 (-1) f) 2
      (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))))
    (n : ℤ) (hab : (-1 : ℝ) < 1) :
    fourierCoeff (h.toLp (AddCircle.liftIoc 2 (-1) f)) n =
      fourierCoeffOn hab f n := by
  rw [apm_m02j02_fourierCoeff_toLp_eq_representative]
  exact apm_m02j02_fourierCoeff_liftIoc_two_eq_on f n hab

lemma apm_m02j02_fourierCoeff_toLp_liftIoc_deriv_eq_mul
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hsub : tsupport f ⊆ Ioo (-1 : ℝ) 1)
    (hF : MemLp (AddCircle.liftIoc 2 (-1) (fun x : ℝ => (f x : ℂ))) 2
      (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))))
    (hD : MemLp (AddCircle.liftIoc 2 (-1)
        (fun x : ℝ => ((deriv f x : ℝ) : ℂ))) 2
      (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))))
    (n : ℤ) :
    fourierCoeff (hD.toLp (AddCircle.liftIoc 2 (-1)
        (fun x : ℝ => ((deriv f x : ℝ) : ℂ)))) n =
      (Real.pi * Complex.I * n) *
        fourierCoeff (hF.toLp (AddCircle.liftIoc 2 (-1)
          (fun x : ℝ => (f x : ℂ)))) n := by
  let hab : (-1 : ℝ) < 1 := by norm_num
  rw [apm_m02j02_fourierCoeff_toLp_liftIoc_eq_on _ _ _ hab,
    apm_m02j02_fourierCoeff_toLp_liftIoc_eq_on _ _ _ hab]
  exact apm_m02j02_fourierCoeffOn_deriv_eq_mul_all hf hsub n

lemma apm_m02j02_eLpNorm_liftIoc_two_volume
    (f : ℝ → ℂ) :
    eLpNorm (AddCircle.liftIoc 2 (-1) f) 2
        (volume : Measure (AddCircle (2 : ℝ))) =
      eLpNorm f 2 (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  congr 1
  calc
    (∫⁻ x : AddCircle (2 : ℝ), ‖AddCircle.liftIoc 2 (-1) f x‖ₑ ^
        (2 : ℝ≥0∞).toReal) =
      ∫⁻ x : ℝ in Ioc (-1) (-1 + 2),
        ‖AddCircle.liftIoc 2 (-1) f (x : AddCircle (2 : ℝ))‖ₑ ^
          (2 : ℝ≥0∞).toReal := by
        simpa only using (AddCircle.lintegral_preimage 2 (-1)
          (fun z : AddCircle (2 : ℝ) =>
            ‖AddCircle.liftIoc 2 (-1) f z‖ₑ ^ (2 : ℝ≥0∞).toReal)).symm
    _ = _ := by
      norm_num
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro x hx
      dsimp only
      change ‖AddCircle.liftIoc 2 (-1) f (x : AddCircle (2 : ℝ))‖ₑ ^ (2 : ℕ) =
        ‖f x‖ₑ ^ (2 : ℕ)
      rw [AddCircle.liftIoc_coe_apply]
      exact ⟨hx.1, by linarith [hx.2]⟩

lemma apm_m02j02_eLpNorm_Ioc_eq_sqrtTwo_mul_liftIoc
    (f : ℝ → ℂ) :
    eLpNorm f 2 (volume.restrict (Ioc (-1 : ℝ) 1)) =
      (ENNReal.ofReal 2) ^ (1 / 2 : ℝ) *
        eLpNorm (AddCircle.liftIoc 2 (-1) f) 2
          (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))) := by
  rw [← apm_m02j02_eLpNorm_liftIoc_two_volume]
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num)]
  norm_num

lemma apm_m02j02_eLpNorm_restrict_Ioo_le_sqrtTwo_mul_liftIoc
    (f : ℝ → ℂ) :
    eLpNorm f 2 (volume.restrict (Ioo (0 : ℝ) 1)) ≤
      (ENNReal.ofReal 2) ^ (1 / 2 : ℝ) *
        eLpNorm (AddCircle.liftIoc 2 (-1) f) 2
          (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))) := by
  calc
    _ ≤ eLpNorm f 2 (volume.restrict (Ioc (-1 : ℝ) 1)) :=
      eLpNorm_mono_measure f (Measure.restrict_mono_set volume (by
        intro x hx
        exact ⟨by linarith [hx.1], hx.2.le⟩))
    _ = _ := apm_m02j02_eLpNorm_Ioc_eq_sqrtTwo_mul_liftIoc f

lemma apm_m02j02_sum_symmetricIcc_eq_zero_add_pairs
    {E : Type*} [AddCommMonoid E] (g : ℤ → E) (N : ℕ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N, g n =
      g 0 + ∑ k ∈ Finset.range N,
        (g ((k + 1 : ℕ) : ℤ) + g (-((k + 1 : ℕ) : ℤ))) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show (-(N.succ : ℤ)) = -((N : ℤ) + 1) by omega]
      rw [show (N.succ : ℤ) = (N : ℤ) + 1 by omega]
      rw [Finset.Icc_succ_succ]
      rw [Finset.sum_union]
      · rw [Finset.sum_insert (by
            simp only [Finset.mem_singleton]
            exact ne_of_lt (by omega : -((N : ℤ) + 1) < (N : ℤ) + 1))]
        · rw [Finset.sum_singleton, ih, Finset.sum_range_succ]
          simp only [Nat.cast_add, Nat.cast_one]
          rw [add_comm (g (-((N : ℤ) + 1))) (g ((N : ℤ) + 1))]
          exact add_assoc _ _ _
      · rw [Finset.disjoint_left]
        intro a ha hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · simp only [Finset.mem_Icc] at ha
          omega
        · simp only [Finset.mem_Icc] at ha
          omega

lemma apm_m02j02_sum_symmetricIcc_eq_sum_range_pairs
    {E : Type*} [AddCommMonoid E] (g : ℤ → E) (h : ℕ → E)
    (hg0 : g 0 = 0)
    (hpair : ∀ k : ℕ,
      g ((k + 1 : ℕ) : ℤ) + g (-((k + 1 : ℕ) : ℤ)) = h k)
    (N : ℕ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N, g n =
      ∑ k ∈ Finset.range N, h k := by
  rw [apm_m02j02_sum_symmetricIcc_eq_zero_add_pairs, hg0, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  exact hpair k

lemma apm_m02j02_odd_fourier_symmetric_sum_eq_sine_sum
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hodd : ∀ x : ℝ, f (-x) = -f x) (N : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
            (fun y : ℝ => (f y : ℂ)) n *
          (@fourier (2 : ℝ) n (x : AddCircle (2 : ℝ))) =
      ∑ k ∈ Finset.range N,
        (((-2 * (fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
            (fun y : ℝ => (f y : ℂ)) ((k + 1 : ℕ) : ℤ)).im : ℝ) : ℂ) *
          (Real.sin ((k + 1 : ℝ) * Real.pi * x) : ℂ)) := by
  apply apm_m02j02_sum_symmetricIcc_eq_sum_range_pairs
  · rw [apm_m02j02_fourierCoeffOn_zero_eq_zero_of_odd hf hodd]
    simp
  · intro k
    rw [apm_m02j02_odd_fourier_pair_eq_sine hf hodd]
    push_cast
    congr 2
    ring

lemma apm_m02j02_exists_sine_finsupp_for_fourier_coefficients
    (f : ℝ → ℝ) (N : ℕ) :
    ∃ c : ℕ →₀ ℝ,
      c.sum (fun k a => a • apm_m02j02_sine k) =
        (fun x => ∑ k ∈ Finset.range N,
          (-2 * (fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
            (fun y : ℝ => (f y : ℂ)) ((k + 1 : ℕ) : ℤ)).im) *
              Real.sin ((k + 1 : ℝ) * Real.pi * x)) ∧
      c.sum (fun k a => a • apm_m02j02_sineDeriv k) =
        (fun x => ∑ k ∈ Finset.range N,
          (-2 * (fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
            (fun y : ℝ => (f y : ℂ)) ((k + 1 : ℕ) : ℤ)).im) *
              ((k + 1 : ℝ) * Real.pi) *
                Real.cos ((k + 1 : ℝ) * Real.pi * x)) := by
  let a : ℕ → ℝ := fun k =>
    -2 * (fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
      (fun y : ℝ => (f y : ℂ)) ((k + 1 : ℕ) : ℤ)).im
  let c : ℕ →₀ ℝ := Finsupp.onFinset (Finset.range N)
    (fun k => if k < N then a k else 0) (by
      intro k hk
      simp only [Finset.mem_range]
      by_contra hkn
      simp [hkn] at hk)
  refine ⟨c, ?_, ?_⟩
  · funext x
    rw [Finsupp.sum_of_support_subset c Finsupp.support_onFinset_subset
      (fun k a => a • apm_m02j02_sine k) (by simp)]
    simp_rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    have hkl : k < N := Finset.mem_range.mp hk
    simp [c, a, hkl, apm_m02j02_sine]
  · funext x
    rw [Finsupp.sum_of_support_subset c Finsupp.support_onFinset_subset
      (fun k a => a • apm_m02j02_sineDeriv k) (by simp)]
    simp_rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    have hkl : k < N := Finset.mem_range.mp hk
    simp [c, a, hkl, apm_m02j02_sineDeriv]
    ring

lemma apm_m02j02_oddExtension_complex_memLp_pair
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    let F : ℝ → ℝ := fun x => φ x - φ (-x)
    MemLp (fun x : ℝ => (F x : ℂ)) 2 (volume.restrict (Ioc (-1 : ℝ) 1)) ∧
      MemLp (fun x : ℝ => ((deriv F x : ℝ) : ℂ)) 2
        (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  let F : ℝ → ℝ := fun x => φ x - φ (-x)
  have hF : ContDiff ℝ ∞ F := apm_m02j02_oddExtension_contDiff hφ
  have hFc : HasCompactSupport F := apm_m02j02_oddExtension_hasCompactSupport hφc
  have hFLp : MemLp F 2 volume := hF.continuous.memLp_of_hasCompactSupport hFc
  have hdFLp : MemLp (deriv F) 2 volume :=
    (contDiff_infty_iff_deriv.mp hF).2.continuous.memLp_of_hasCompactSupport hFc.deriv
  exact ⟨(hFLp.restrict (Ioc (-1 : ℝ) 1)).ofReal,
    (hdFLp.restrict (Ioc (-1 : ℝ) 1)).ofReal⟩

lemma apm_m02j02_oddExtension_liftIoc_memLp_pair
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    let F : ℝ → ℝ := fun x => φ x - φ (-x)
    let FC : ℝ → ℂ := fun x => (F x : ℂ)
    let DC : ℝ → ℂ := fun x => ((deriv F x : ℝ) : ℂ)
    MemLp (AddCircle.liftIoc 2 (-1) FC) 2
        (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))) ∧
      MemLp (AddCircle.liftIoc 2 (-1) DC) 2
        (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))) := by
  let F : ℝ → ℝ := fun x => φ x - φ (-x)
  let FC : ℝ → ℂ := fun x => (F x : ℂ)
  let DC : ℝ → ℂ := fun x => ((deriv F x : ℝ) : ℂ)
  letI : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨hFC, hDC⟩ := apm_m02j02_oddExtension_complex_memLp_pair hφ hφc
  have hFC' : MemLp FC 2 (volume.restrict (Ioc (-1 : ℝ) (-1 + 2))) := by
    convert hFC using 1 <;> ring_nf
  have hDC' : MemLp DC 2 (volume.restrict (Ioc (-1 : ℝ) (-1 + 2))) := by
    convert hDC using 1 <;> ring_nf
  exact ⟨hFC'.memLp_liftIoc.haarAddCircle, hDC'.memLp_liftIoc.haarAddCircle⟩

/-- Every fixed smooth bump has a global derivative bound. Under affine
rescaling this supplies the quantitative `1 / δ` estimate needed by endpoint
and expanding-support cutoff arguments. -/
lemma apm_m02j02_contDiffBump_deriv_bounded (c : ℝ) (b : ContDiffBump c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |deriv b x| ≤ C := by
  have hcont : Continuous (deriv (b : ℝ → ℝ)) := by
    simpa using (b.contDiff (n := (⊤ : ℕ∞))).continuous_deriv (by simp)
  have hcomp : HasCompactSupport (deriv (b : ℝ → ℝ)) := b.hasCompactSupport.deriv
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcomp
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hx : |deriv b x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC x
  exact hx.trans (le_max_left _ _)

/-- The derivative of Mathlib's smooth transition is confined to its transition
interval.  This is the compactness fact needed to obtain a uniform derivative
bound before affine rescaling near an endpoint. -/
lemma apm_m02j02_smoothTransition_deriv_hasCompactSupport :
    HasCompactSupport (deriv Real.smoothTransition) := by
  apply HasCompactSupport.intro (K := Icc (0 : ℝ) 1) isCompact_Icc
  intro x hx
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · have heq : Real.smoothTransition =ᶠ[nhds x] (fun _ : ℝ => 0) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [heq.deriv_eq]
    simp
  · have heq : Real.smoothTransition =ᶠ[nhds x] (fun _ : ℝ => 1) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [heq.deriv_eq]
    simp

lemma apm_m02j02_smoothTransition_deriv_eq_zero_of_not_mem_Icc
    {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition x = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · have heq : Real.smoothTransition =ᶠ[nhds x] (fun _ : ℝ => 0) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [heq.deriv_eq]
    simp
  · have heq : Real.smoothTransition =ᶠ[nhds x] (fun _ : ℝ => 1) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [heq.deriv_eq]
    simp

lemma apm_m02j02_smoothTransition_deriv_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (@Real.smoothTransition.contDiff (⊤ : ℕ∞)).continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support
    apm_m02j02_smoothTransition_deriv_hasCompactSupport
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hx : |deriv Real.smoothTransition x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC x
  exact hx.trans (le_max_left _ _)

/-- Affine rescaling of the smooth transition. -/
lemma apm_m02j02_deriv_smoothTransition_affine
    {a δ x : ℝ} (hδ : δ ≠ 0) :
    deriv (fun y : ℝ => Real.smoothTransition ((y - a) / δ)) x =
      deriv Real.smoothTransition ((x - a) / δ) / δ := by
  have hs : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((x - a) / δ)) ((x - a) / δ) :=
    ((@Real.smoothTransition.contDiff (⊤ : ℕ∞)).differentiable (by simp)
      ((x - a) / δ)).hasDerivAt
  have ha : HasDerivAt (fun y : ℝ => (y - a) / δ) (1 / δ) x := by
    convert ((hasDerivAt_id x).sub_const a).div_const δ using 1 <;> field_simp
  convert (hs.comp x ha).deriv using 1 <;> field_simp

lemma apm_m02j02_smoothTransition_affine_deriv_bound
    {C a δ : ℝ} (hC : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C)
    (hδ : 0 < δ) (x : ℝ) :
    |deriv (fun y : ℝ => Real.smoothTransition ((y - a) / δ)) x| ≤ C / δ := by
  rw [apm_m02j02_deriv_smoothTransition_affine hδ.ne', abs_div,
    abs_of_pos hδ]
  exact div_le_div_of_nonneg_right (hC ((x - a) / δ)) hδ.le

lemma apm_m02j02_deriv_smoothTransition_affine_eq_zero
    {a δ x : ℝ} (hδ : 0 < δ) (hx : x ∉ Icc a (a + δ)) :
    deriv (fun y : ℝ => Real.smoothTransition ((y - a) / δ)) x = 0 := by
  rw [apm_m02j02_deriv_smoothTransition_affine hδ.ne']
  have hout : (x - a) / δ ∉ Icc (0 : ℝ) 1 := by
    contrapose! hx
    constructor
    · have hh := (div_nonneg_iff.mp hx.1)
      rcases hh with hh | hh
      · exact le_of_sub_nonneg hh.1
      · exact False.elim ((not_le_of_gt hδ) hh.2)
    · have hsub : x - a ≤ δ := (div_le_one hδ).1 hx.2
      linarith
  rw [apm_m02j02_smoothTransition_deriv_eq_zero_of_not_mem_Icc hout,
    zero_div]

lemma apm_m02j02_deriv_smoothTransition_affine_hasCompactSupport
    {a δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport
      (deriv (fun y : ℝ => Real.smoothTransition ((y - a) / δ))) := by
  apply HasCompactSupport.intro (K := Icc a (a + δ)) isCompact_Icc
  intro x hx
  exact apm_m02j02_deriv_smoothTransition_affine_eq_zero hδ hx

lemma apm_m02j02_smoothTransition_affine_zero
    {a δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ a) :
    Real.smoothTransition ((x - a) / δ) = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hx) hδ.le

lemma apm_m02j02_smoothTransition_affine_one
    {a δ x : ℝ} (hδ : 0 < δ) (hx : a + δ ≤ x) :
    Real.smoothTransition ((x - a) / δ) = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ hδ).2 (by linarith)

lemma apm_m02j02_tsupport_smoothTransition_affine_subset_Ici
    {a δ : ℝ} (hδ : 0 < δ) :
    tsupport (fun x : ℝ => Real.smoothTransition ((x - a) / δ)) ⊆ Ici a := by
  apply closure_minimal
  · intro x hx
    by_contra hxa
    have hxlt : x < a := lt_of_not_ge hxa
    exact hx (apm_m02j02_smoothTransition_affine_zero hδ hxlt.le)
  · exact isClosed_Ici

/-- Multiplying a compactly supported smooth function by a shifted transition
produces a compactly supported smooth function whose topological support lies
strictly in the positive half-line when the shift is positive. -/
lemma apm_m02j02_smoothTransition_affine_mul_regular
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ContDiff ℝ ∞
        (fun x : ℝ => Real.smoothTransition ((x - a) / δ) * f x) ∧
      HasCompactSupport
        (fun x : ℝ => Real.smoothTransition ((x - a) / δ) * f x) ∧
      tsupport (fun x : ℝ => Real.smoothTransition ((x - a) / δ) * f x) ⊆
        Ioi (0 : ℝ) := by
  refine ⟨(@Real.smoothTransition.contDiff (⊤ : ℕ∞)).comp
      (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ => (x - a) / δ)) |>.mul hf,
    hfc.mul_left, ?_⟩
  exact tsupport_mul_subset_left.trans
    ((apm_m02j02_tsupport_smoothTransition_affine_subset_Ici hδ).trans
      (fun _ hx => ha.trans_le hx))

lemma apm_m02j02_deriv_smoothTransition_affine_mul
    {a δ x : ℝ} (hδ : δ ≠ 0) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    deriv (fun y : ℝ => Real.smoothTransition ((y - a) / δ) * f y) x =
      (deriv Real.smoothTransition ((x - a) / δ) / δ) * f x +
        Real.smoothTransition ((x - a) / δ) * deriv f x := by
  have hs : HasDerivAt
      (fun y : ℝ => Real.smoothTransition ((y - a) / δ))
      (deriv Real.smoothTransition ((x - a) / δ) / δ) x := by
    exact (apm_m02j02_deriv_smoothTransition_affine hδ) ▸
      (((@Real.smoothTransition.contDiff (⊤ : ℕ∞)).comp
        (by fun_prop : ContDiff ℝ ∞ (fun y : ℝ => (y - a) / δ))).differentiable
          (by simp) x).hasDerivAt
  exact (hs.mul ((hf.differentiable (by simp) x).hasDerivAt)).deriv

lemma apm_m02j02_innerCutoff_memLp_pair
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hfLp : MemLp f 2 volume)
    (hdfLp : MemLp (deriv f) 2 volume) {a δ : ℝ} (hδ : 0 < δ) :
    MemLp (fun x : ℝ => Real.smoothTransition ((x - a) / δ) * f x) 2 volume ∧
      MemLp (deriv (fun x : ℝ =>
        Real.smoothTransition ((x - a) / δ) * f x)) 2 volume := by
  let q : ℝ → ℝ := fun x => Real.smoothTransition ((x - a) / δ)
  have hq : ContDiff ℝ ∞ q :=
    (@Real.smoothTransition.contDiff (⊤ : ℕ∞)).comp (by fun_prop)
  have hqbound (x : ℝ) : |q x| ≤ 1 := by
    dsimp only [q]
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hqf : MemLp (fun x : ℝ => q x * f x) 2 volume := by
    apply hfLp.of_le (hq.continuous.mul hf.continuous).aestronglyMeasurable
    filter_upwards [] with x
    change |q x * f x| ≤ |f x|
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg (f x)) (hqbound x)
  refine ⟨hqf, ?_⟩
  have hcross : MemLp (fun x : ℝ => deriv q x * f x) 2 volume := by
    apply Continuous.memLp_of_hasCompactSupport
    · exact (hq.continuous_deriv (by simp)).mul hf.continuous
    · exact (apm_m02j02_deriv_smoothTransition_affine_hasCompactSupport hδ).mul_right
  have hqdf : MemLp (fun x : ℝ => q x * deriv f x) 2 volume := by
    apply hdfLp.of_le
      (hq.continuous.mul (hf.continuous_deriv (by simp))).aestronglyMeasurable
    filter_upwards [] with x
    change |q x * deriv f x| ≤ |deriv f x|
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg (deriv f x)) (hqbound x)
  have hsum : MemLp
      ((fun x : ℝ => deriv q x * f x) + (fun x : ℝ => q x * deriv f x))
      2 volume := hcross.add hqdf
  apply hsum.congr_norm
    ((hq.mul hf).continuous_deriv (by simp)).aestronglyMeasurable
  filter_upwards [] with x
  congr 1
  symm
  simpa only [Pi.add_apply, q,
    apm_m02j02_deriv_smoothTransition_affine hδ.ne'] using
      apm_m02j02_deriv_smoothTransition_affine_mul
        (a := a) (x := x) hδ.ne' (hf.of_le (by simp))

/-- A smooth function vanishing at the origin grows at most linearly on the
unit interval.  This is the estimate that cancels the `1 / δ` created by a
rescaled endpoint cutoff. -/
lemma apm_m02j02_exists_linear_bound_Icc_of_contDiff_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ K * |x| := by
  have hdcont : Continuous (fun x : ℝ => ‖deriv f x‖) :=
    (hf.continuous_deriv (by simp)).norm
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.bddAbove_image hdcont.continuousOn
  let K : ℝ := max K₀ 0
  have hK : ∀ x ∈ Icc (0 : ℝ) 1, ‖deriv f x‖ ≤ K := by
    intro x hx
    exact (hK₀ (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  refine ⟨K, le_max_right _ _, fun x hx => ?_⟩
  have hmv := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun y _ => hf.differentiable (by simp) y) hK (left_mem_Icc.2 zero_le_one) hx
  rw [hf0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  exact hmv

lemma apm_m02j02_exists_abs_bound_Icc_of_continuous
    {f : ℝ → ℝ} (hf : Continuous f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ B := by
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.bddAbove_image hf.norm.continuousOn
  refine ⟨max B₀ 0, le_max_right _ _, fun x hx => ?_⟩
  have hxB : ‖f x‖ ≤ B₀ := hB₀ (mem_image_of_mem _ hx)
  simpa only [Real.norm_eq_abs] using hxB.trans (le_max_left _ _)

lemma apm_m02j02_exists_oddHermite_and_deriv_abs_bound_Icc (n : ℕ) :
    ∃ B D : ℝ, 0 ≤ B ∧ 0 ≤ D ∧
      (∀ x ∈ Icc (0 : ℝ) 1,
        |apm_m02j02_hermiteFunction (2 * n + 1) x| ≤ B) ∧
      (∀ x ∈ Icc (0 : ℝ) 1,
        |apm_m02j02_hermiteFunctionDeriv (2 * n + 1) x| ≤ D) := by
  obtain ⟨B, hB0, hB⟩ := apm_m02j02_exists_abs_bound_Icc_of_continuous
    (apm_m02j02_hermiteFunction_contDiff (2 * n + 1)).continuous
  obtain ⟨D, hD0, hD⟩ := apm_m02j02_exists_abs_bound_Icc_of_continuous
    (apm_m02j02_hermiteFunctionDeriv_continuous (2 * n + 1))
  exact ⟨B, D, hB0, hD0, hB, hD⟩

lemma apm_m02j02_exists_sine_and_deriv_abs_bound_Icc (n : ℕ) :
    ∃ B D : ℝ, 0 ≤ B ∧ 0 ≤ D ∧
      (∀ x ∈ Icc (0 : ℝ) 1, |apm_m02j02_sine n x| ≤ B) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, |apm_m02j02_sineDeriv n x| ≤ D) := by
  obtain ⟨B, hB0, hB⟩ := apm_m02j02_exists_abs_bound_Icc_of_continuous
    (apm_m02j02_sine_contDiff n).continuous
  obtain ⟨D, hD0, hD⟩ := apm_m02j02_exists_abs_bound_Icc_of_continuous
    (apm_m02j02_sineDeriv_contDiff n).continuous
  exact ⟨B, D, hB0, hD0, hB, hD⟩

lemma apm_m02j02_exists_sine_linear_bound_Icc (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      |apm_m02j02_sine n x| ≤ K * |x| := by
  apply apm_m02j02_exists_linear_bound_Icc_of_contDiff_zero
    ((apm_m02j02_sine_contDiff n).of_le (by simp))
  exact apm_m02j02_sine_zero n

/-- A pointwise bound together with interval support gives the corresponding
explicit `L²` bound.  This is used for every term created by the shrinking
endpoint cutoff. -/
lemma apm_m02j02_eLpNorm_two_le_indicator_Icc
    {f : ℝ → ℝ} {a b C : ℝ} (hC : 0 ≤ C)
    (hsupp : ∀ x : ℝ, x ∉ Icc a b → f x = 0)
    (hbound : ∀ x ∈ Icc a b, |f x| ≤ C) :
    eLpNorm f 2 volume ≤
      ENNReal.ofReal C * (volume (Icc a b) : ℝ≥0∞) ^
        (1 / (2 : ℝ≥0∞).toReal) := by
  calc
    eLpNorm f 2 volume ≤
        eLpNorm ((Icc a b).indicator (fun _ : ℝ => C)) 2 volume := by
      apply eLpNorm_mono
      intro x
      by_cases hx : x ∈ Icc a b
      · simp only [Set.indicator_of_mem hx, Real.norm_eq_abs,
          abs_of_nonneg hC]
        exact hbound x hx
      · rw [hsupp x hx]
        simp [hx]
    _ = _ := by
      rw [eLpNorm_indicator_const measurableSet_Icc (by norm_num) (by simp)]
      simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC]

lemma apm_m02j02_eLpNorm_two_restrict_Ioi_le_indicator_Icc
    {f : ℝ → ℝ} {b C : ℝ} (hC : 0 ≤ C)
    (hsupp : ∀ x ∈ Ioi (0 : ℝ), x ∉ Icc (0 : ℝ) b → f x = 0)
    (hbound : ∀ x ∈ Icc (0 : ℝ) b, |f x| ≤ C) :
    eLpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) ≤
      ENNReal.ofReal C * (volume (Icc (0 : ℝ) b) : ℝ≥0∞) ^
        (1 / (2 : ℝ≥0∞).toReal) := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioi]
  apply apm_m02j02_eLpNorm_two_le_indicator_Icc hC
  · intro x hx
    by_cases hxp : x ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hxp, hsupp x hxp hx]
    · simp [hxp]
  · intro x hx
    by_cases hxp : x ∈ Ioi (0 : ℝ)
    · simpa [hxp] using hbound x hx
    · simp [hxp, hC]

/-- The derivative cross term in the inner cutoff is uniformly bounded and
supported on an interval of length `δ`. -/
lemma apm_m02j02_innerCutoff_cross_eLpNorm_le
    {f : ℝ → ℝ} {C K δ : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C)
    (hK0 : 0 ≤ K)
    (hK : ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ K * |x|)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    eLpNorm (fun x : ℝ =>
      deriv (fun y : ℝ => Real.smoothTransition ((y - δ) / δ)) x * f x)
        2 volume ≤
      ENNReal.ofReal (2 * C * K) *
        (volume (Icc δ (2 * δ)) : ℝ≥0∞) ^
          (1 / (2 : ℝ≥0∞).toReal) := by
  apply apm_m02j02_eLpNorm_two_le_indicator_Icc
    (mul_nonneg (mul_nonneg (by norm_num) hC0) hK0)
  · intro x hx
    rw [apm_m02j02_deriv_smoothTransition_affine_eq_zero hδ (by
      simpa [two_mul] using hx), zero_mul]
  · intro x hx
    have hx01 : x ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact hδ.le.trans hx.1
      · nlinarith [hx.2]
    have hdx := apm_m02j02_smoothTransition_affine_deriv_bound
      (a := δ) hC hδ x
    have hfx := hK x hx01
    rw [abs_mul]
    calc
      |deriv (fun y : ℝ => Real.smoothTransition ((y - δ) / δ)) x| * |f x| ≤
          (C / δ) * (K * |x|) :=
        mul_le_mul hdx hfx (abs_nonneg _) (div_nonneg hC0 hδ.le)
      _ ≤ (C / δ) * (K * (2 * δ)) := by
        gcongr
        rw [abs_of_nonneg (hδ.le.trans hx.1)]
        exact hx.2
      _ = 2 * C * K := by field_simp

lemma apm_m02j02_innerCutoff_cross_eLpNorm_le_sqrt
    {f : ℝ → ℝ} {C K δ : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C)
    (hK0 : 0 ≤ K)
    (hK : ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ K * |x|)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    eLpNorm (fun x : ℝ =>
      deriv (fun y : ℝ => Real.smoothTransition ((y - δ) / δ)) x * f x)
        2 volume ≤
      ENNReal.ofReal (2 * C * K) * (ENNReal.ofReal δ) ^ (1 / 2 : ℝ) := by
  have hsub : 2 * δ - δ = δ := by ring
  simpa [Real.volume_Icc, ENNReal.toReal_ofNat, hsub] using
    apm_m02j02_innerCutoff_cross_eLpNorm_le hC0 hC hK0 hK hδ hδhalf

/-- The ordinary error made by the inner cutoff is supported in `(0,2δ)`
and inherits any local pointwise bound for the function being cut off. -/
lemma apm_m02j02_innerCutoff_value_eLpNorm_le
    {f : ℝ → ℝ} {B δ : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ B)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    eLpNorm (f - fun x : ℝ =>
      Real.smoothTransition ((x - δ) / δ) * f x) 2
        (volume.restrict (Ioi (0 : ℝ))) ≤
      ENNReal.ofReal B * (ENNReal.ofReal (2 * δ)) ^ (1 / 2 : ℝ) := by
  have hmain := apm_m02j02_eLpNorm_two_restrict_Ioi_le_indicator_Icc
    (f := f - fun x : ℝ =>
      Real.smoothTransition ((x - δ) / δ) * f x)
    hB0 (b := 2 * δ) (C := B)
  have hsupp : ∀ x ∈ Ioi (0 : ℝ), x ∉ Icc (0 : ℝ) (2 * δ) →
      (f - fun y : ℝ => Real.smoothTransition ((y - δ) / δ) * f y) x = 0 := by
    intro x hxp hx
    have hxgt : 2 * δ < x := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · change 0 < x at hxp
        linarith
      · exact hx
    rw [Pi.sub_apply,
      apm_m02j02_smoothTransition_affine_one hδ (by linarith)]
    ring
  have hbound : ∀ x ∈ Icc (0 : ℝ) (2 * δ),
      |(f - fun y : ℝ => Real.smoothTransition ((y - δ) / δ) * f y) x| ≤ B := by
    intro x hx
    have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, by nlinarith [hx.2]⟩
    have hs0 := Real.smoothTransition.nonneg ((x - δ) / δ)
    have hs1 := Real.smoothTransition.le_one ((x - δ) / δ)
    rw [Pi.sub_apply, show f x - Real.smoothTransition ((x - δ) / δ) * f x =
      (1 - Real.smoothTransition ((x - δ) / δ)) * f x by ring,
      abs_mul, abs_of_nonneg (sub_nonneg.2 hs1)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (by linarith)).trans (hB x hx01)
  calc
    _ ≤ ENNReal.ofReal B * (volume (Icc (0 : ℝ) (2 * δ)) : ℝ≥0∞) ^
        (1 / (2 : ℝ≥0∞).toReal) := hmain hsupp hbound
    _ = _ := by simp [Real.volume_Icc, ENNReal.toReal_ofNat]

lemma apm_m02j02_innerCutoff_deriv_eLpNorm_le
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {C K D δ : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C)
    (hK0 : 0 ≤ K)
    (hK : ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ K * |x|)
    (hD0 : 0 ≤ D)
    (hD : ∀ x ∈ Icc (0 : ℝ) 1, |deriv f x| ≤ D)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    eLpNorm (deriv f - deriv (fun x : ℝ =>
      Real.smoothTransition ((x - δ) / δ) * f x)) 2
        (volume.restrict (Ioi (0 : ℝ))) ≤
      ENNReal.ofReal D * (ENNReal.ofReal (2 * δ)) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (2 * C * K) * (ENNReal.ofReal δ) ^ (1 / 2 : ℝ) := by
  let q : ℝ → ℝ := fun x => Real.smoothTransition ((x - δ) / δ)
  have hq : ContDiff ℝ ∞ q :=
    (@Real.smoothTransition.contDiff (⊤ : ℕ∞)).comp (by fun_prop)
  have heq : deriv f - deriv (fun x : ℝ => q x * f x) =
      (deriv f - fun x : ℝ => q x * deriv f x) +
        -(fun x : ℝ => deriv q x * f x) := by
    funext x
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
    rw [show deriv (fun y : ℝ => q y * f y) x =
        deriv q x * f x + q x * deriv f x by
      simpa only [q, apm_m02j02_deriv_smoothTransition_affine hδ.ne'] using
        (apm_m02j02_deriv_smoothTransition_affine_mul
          (a := δ) (x := x) hδ.ne' (hf.of_le (by simp)))]
    ring
  change eLpNorm (deriv f - deriv (fun x : ℝ => q x * f x)) 2
      (volume.restrict (Ioi (0 : ℝ))) ≤ _
  rw [heq]
  calc
    eLpNorm ((deriv f - fun x : ℝ => q x * deriv f x) +
        -(fun x : ℝ => deriv q x * f x)) 2
        (volume.restrict (Ioi (0 : ℝ))) ≤
      eLpNorm (deriv f - fun x : ℝ => q x * deriv f x) 2
          (volume.restrict (Ioi (0 : ℝ))) +
        eLpNorm (-(fun x : ℝ => deriv q x * f x)) 2
          (volume.restrict (Ioi (0 : ℝ))) := by
      apply eLpNorm_add_le
      · exact ((hf.continuous_deriv (by simp)).sub
          (hq.continuous.mul (hf.continuous_deriv (by simp)))).aestronglyMeasurable
      · exact (((hq.continuous_deriv (by simp)).mul hf.continuous).neg).aestronglyMeasurable
      · norm_num
    _ ≤ _ := by
      rw [eLpNorm_neg]
      exact add_le_add
        (apm_m02j02_innerCutoff_value_eLpNorm_le hD0 hD hδ hδhalf)
        ((eLpNorm_mono_measure (fun x : ℝ => deriv q x * f x)
          Measure.restrict_le_self).trans
            (by
              change eLpNorm (fun x : ℝ =>
                deriv (fun y : ℝ => Real.smoothTransition ((y - δ) / δ)) x * f x)
                  2 volume ≤ _
              exact apm_m02j02_innerCutoff_cross_eLpNorm_le_sqrt
                hC0 hC hK0 hK hδ hδhalf))

lemma apm_m02j02_innerCutoff_graph_eLpNorm_le
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {B C K D δ : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ B)
    (hC0 : 0 ≤ C)
    (hC : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C)
    (hK0 : 0 ≤ K)
    (hK : ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ K * |x|)
    (hD0 : 0 ≤ D)
    (hD : ∀ x ∈ Icc (0 : ℝ) 1, |deriv f x| ≤ D)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    eLpNorm (f - fun x : ℝ =>
      Real.smoothTransition ((x - δ) / δ) * f x) 2
        (volume.restrict (Ioi (0 : ℝ))) +
      eLpNorm (deriv f - deriv (fun x : ℝ =>
        Real.smoothTransition ((x - δ) / δ) * f x)) 2
          (volume.restrict (Ioi (0 : ℝ))) ≤
      ENNReal.ofReal B * (ENNReal.ofReal (2 * δ)) ^ (1 / 2 : ℝ) +
        (ENNReal.ofReal D * (ENNReal.ofReal (2 * δ)) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (2 * C * K) *
            (ENNReal.ofReal δ) ^ (1 / 2 : ℝ)) := by
  exact add_le_add
    (apm_m02j02_innerCutoff_value_eLpNorm_le hB0 hB hδ hδhalf)
    (apm_m02j02_innerCutoff_deriv_eLpNorm_le hf hC0 hC hK0 hK hD0 hD
      hδ hδhalf)

lemma apm_m02j02_innerCutoff_bound_tendsto_zero (B C K D : ℝ) :
    Tendsto (fun δ : ℝ =>
      ENNReal.ofReal B * (ENNReal.ofReal (2 * δ)) ^ (1 / 2 : ℝ) +
        (ENNReal.ofReal D * (ENNReal.ofReal (2 * δ)) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (2 * C * K) *
            (ENNReal.ofReal δ) ^ (1 / 2 : ℝ)))
      (nhds 0) (nhds 0) := by
  have hδ : Tendsto (fun δ : ℝ => ENNReal.ofReal δ) (nhds 0) (nhds 0) :=
    by simpa using (ENNReal.tendsto_ofReal
      (tendsto_id : Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0)))
  have h2real : Tendsto (fun δ : ℝ => 2 * δ) (nhds 0) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul tendsto_id :
      Tendsto (fun δ : ℝ => 2 * δ) (nhds 0) (nhds (2 * 0)))
  have h2 : Tendsto (fun δ : ℝ => ENNReal.ofReal (2 * δ))
      (nhds 0) (nhds 0) := by simpa using ENNReal.tendsto_ofReal h2real
  have hs : Tendsto (fun δ : ℝ =>
      (ENNReal.ofReal δ) ^ (1 / 2 : ℝ)) (nhds 0) (nhds 0) := by
    convert (ENNReal.continuous_rpow_const.tendsto 0).comp hδ using 1 <;>
      norm_num
  have h2s : Tendsto (fun δ : ℝ =>
      (ENNReal.ofReal (2 * δ)) ^ (1 / 2 : ℝ)) (nhds 0) (nhds 0) := by
    convert (ENNReal.continuous_rpow_const.tendsto 0).comp h2 using 1 <;>
      norm_num
  have hB : Tendsto (fun δ : ℝ => ENNReal.ofReal B *
      (ENNReal.ofReal (2 * δ)) ^ (1 / 2 : ℝ)) (nhds 0) (nhds 0) :=
    by simpa only [Function.comp_apply, mul_zero] using
      ((ENNReal.continuous_const_mul (a := ENNReal.ofReal B)
        ENNReal.ofReal_ne_top).tendsto 0).comp h2s
  have hD : Tendsto (fun δ : ℝ => ENNReal.ofReal D *
      (ENNReal.ofReal (2 * δ)) ^ (1 / 2 : ℝ)) (nhds 0) (nhds 0) :=
    by simpa only [Function.comp_apply, mul_zero] using
      ((ENNReal.continuous_const_mul (a := ENNReal.ofReal D)
        ENNReal.ofReal_ne_top).tendsto 0).comp h2s
  have hCK : Tendsto (fun δ : ℝ => ENNReal.ofReal (2 * C * K) *
      (ENNReal.ofReal δ) ^ (1 / 2 : ℝ)) (nhds 0) (nhds 0) :=
    by simpa only [Function.comp_apply, mul_zero] using
      ((ENNReal.continuous_const_mul (a := ENNReal.ofReal (2 * C * K))
        ENNReal.ofReal_ne_top).tendsto 0).comp hs
  simpa using hB.add (hD.add hCK)

lemma apm_m02j02_exists_small_innerCutoff_scale
    (B C K D ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧
      ENNReal.ofReal B * (ENNReal.ofReal (2 * δ)) ^ (1 / 2 : ℝ) +
        (ENNReal.ofReal D * (ENNReal.ofReal (2 * δ)) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (2 * C * K) *
            (ENNReal.ofReal δ) ^ (1 / 2 : ℝ)) < ENNReal.ofReal ε := by
  let F : ℝ → ℝ≥0∞ := fun δ =>
    ENNReal.ofReal B * (ENNReal.ofReal (2 * δ)) ^ (1 / 2 : ℝ) +
      (ENNReal.ofReal D * (ENNReal.ofReal (2 * δ)) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (2 * C * K) *
          (ENNReal.ofReal δ) ^ (1 / 2 : ℝ))
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  have hev : {x : ℝ | F x < ENNReal.ofReal ε} ∈ nhds 0 :=
    (apm_m02j02_innerCutoff_bound_tendsto_zero B C K D)
      (Iio_mem_nhds hpos)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 hev
  let δ : ℝ := min (r / 2) (1 / 4)
  have hδ : 0 < δ := lt_min (half_pos hr) (by norm_num)
  have hδquarter : δ ≤ 1 / 4 := min_le_right _ _
  have hδr : δ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hmem : δ ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδ]
    exact hδr
  refine ⟨δ, hδ, hδquarter, ?_⟩
  exact hrsub hmem

lemma apm_m02j02_exists_centered_cutoff :
    ∃ b : ContDiffBump (0 : ℝ), b.rIn = 1 ∧ b.rOut = 2 ∧ b 0 = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  refine ⟨b, rfl, rfl, ?_⟩
  apply b.one_of_mem_closedBall
  simp [b]

lemma apm_m02j02_deriv_bump_rescale (c : ℝ) (b : ContDiffBump c)
    {δ x : ℝ} (hδ : δ ≠ 0) :
    deriv (fun y : ℝ => b (y / δ)) x = deriv b (x / δ) / δ := by
  have hb : HasDerivAt (b : ℝ → ℝ) (deriv b (x / δ)) (x / δ) :=
    ((b.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp)
      (x / δ)).hasDerivAt
  have hs : HasDerivAt (fun y : ℝ => y / δ) (1 / δ) x := by
    convert (hasDerivAt_id x).div_const δ using 1 <;> field_simp
  convert (hb.comp x hs).deriv using 1 <;> field_simp

lemma apm_m02j02_bump_rescale_deriv_bound (c : ℝ) (b : ContDiffBump c)
    {C δ : ℝ} (hC : ∀ x : ℝ, |deriv b x| ≤ C)
    (hδ : 0 < δ) (x : ℝ) :
    |deriv (fun y : ℝ => b (y / δ)) x| ≤ C / δ := by
  rw [apm_m02j02_deriv_bump_rescale c b hδ.ne', abs_div, abs_of_pos hδ]
  exact div_le_div_of_nonneg_right (hC (x / δ)) hδ.le

lemma apm_m02j02_deriv_bump_affine (c : ℝ) (b : ContDiffBump c)
    {a δ x : ℝ} (hδ : δ ≠ 0) :
    deriv (fun y : ℝ => b ((y - a) / δ)) x =
      deriv b ((x - a) / δ) / δ := by
  have hb : HasDerivAt (b : ℝ → ℝ) (deriv b ((x - a) / δ)) ((x - a) / δ) :=
    ((b.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp)
      ((x - a) / δ)).hasDerivAt
  have hs : HasDerivAt (fun y : ℝ => (y - a) / δ) (1 / δ) x := by
    convert ((hasDerivAt_id x).sub_const a).div_const δ using 1 <;> field_simp
  convert (hb.comp x hs).deriv using 1 <;> field_simp

lemma apm_m02j02_bump_affine_deriv_bound (c : ℝ) (b : ContDiffBump c)
    {C a δ : ℝ} (hC : ∀ x : ℝ, |deriv b x| ≤ C)
    (hδ : 0 < δ) (x : ℝ) :
    |deriv (fun y : ℝ => b ((y - a) / δ)) x| ≤ C / δ := by
  rw [apm_m02j02_deriv_bump_affine c b hδ.ne', abs_div, abs_of_pos hδ]
  exact div_le_div_of_nonneg_right (hC ((x - a) / δ)) hδ.le

lemma apm_m02j02_bump_rescale_eq_one (b : ContDiffBump (0 : ℝ))
    {R x : ℝ} (hR : 0 < R) (hx : |x| ≤ R * b.rIn) :
    b (x / R) = 1 := by
  apply b.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hR]
  exact (div_le_iff₀ hR).2 (by simpa [mul_comm] using hx)

lemma apm_m02j02_bump_rescale_eq_zero (b : ContDiffBump (0 : ℝ))
    {R x : ℝ} (hR : 0 < R) (hx : R * b.rOut ≤ |x|) :
    b (x / R) = 0 := by
  apply b.zero_of_le_dist
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hR]
  exact (le_div_iff₀ hR).2 (by simpa [mul_comm] using hx)

lemma apm_m02j02_bump_rescale_hasCompactSupport (b : ContDiffBump (0 : ℝ))
    {R : ℝ} (hR : R ≠ 0) : HasCompactSupport (fun x : ℝ => b (x / R)) := by
  have h := b.hasCompactSupport.comp_homeomorph
    (Homeomorph.mulLeft₀ (R⁻¹) (inv_ne_zero hR))
  simpa [Homeomorph.coe_mulLeft₀, div_eq_inv_mul, mul_comm] using h

lemma apm_m02j02_bump_rescale_mul_regular (b : ContDiffBump (0 : ℝ))
    {R : ℝ} (hR : R ≠ 0) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x : ℝ => b (x / R) * f x) ∧
      HasCompactSupport (fun x : ℝ => b (x / R) * f x) := by
  constructor
  · exact ((b.contDiff (n := (⊤ : ℕ∞))).comp
      (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ => x / R))).mul hf
  · exact (apm_m02j02_bump_rescale_hasCompactSupport b hR).mul_right

lemma apm_m02j02_deriv_bump_rescale_mul (b : ContDiffBump (0 : ℝ))
    {R x : ℝ} (hR : R ≠ 0) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    deriv (fun y : ℝ => b (y / R) * f y) x =
      (deriv b (x / R) / R) * f x + b (x / R) * deriv f x := by
  have hb : HasDerivAt (fun y : ℝ => b (y / R)) (deriv b (x / R) / R) x := by
    exact (show deriv (fun y : ℝ => b (y / R)) x = deriv b (x / R) / R from
      apm_m02j02_deriv_bump_rescale 0 b hR) ▸
        (((b.contDiff (n := (⊤ : ℕ∞))).comp
          (by fun_prop : ContDiff ℝ ∞ (fun y : ℝ => y / R))).differentiable
            (by simp) x).hasDerivAt
  have hfx : HasDerivAt f (deriv f x) x :=
    (hf.differentiable (by simp) x).hasDerivAt
  exact (hb.mul hfx).deriv

lemma apm_m02j02_exists_Lp_tail_bound {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ R : ℝ, 0 < R ∧
      eLpNorm ((Metric.closedBall (0 : ℝ) R)ᶜ.indicator f) 2 volume ≤ ε := by
  obtain ⟨g, hgcomp, hfg, -, -⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (p := (2 : ℝ≥0∞)) (by simp) hε
  obtain ⟨R, hR, hgzero⟩ := hgcomp.exists_pos_le_norm
  refine ⟨R, hR, (eLpNorm_mono fun x => ?_).trans hfg⟩
  by_cases hx : x ∈ Metric.closedBall (0 : ℝ) R
  · simp [hx]
  · have hxR : R ≤ ‖x‖ := by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx
      exact le_of_not_ge hx
    simp [hx, hgzero x hxR, Real.norm_eq_abs]

lemma apm_m02j02_bump_rescale_value_error_le (b : ContDiffBump (0 : ℝ))
    {R : ℝ} (hR : 0 < R) (f : ℝ → ℝ) :
    eLpNorm (f - fun x : ℝ => b (x / R) * f x) 2 volume ≤
      eLpNorm ((Metric.closedBall (0 : ℝ) (R * b.rIn))ᶜ.indicator f) 2 volume := by
  apply eLpNorm_mono
  intro x
  by_cases hx : x ∈ Metric.closedBall (0 : ℝ) (R * b.rIn)
  · have hone : b (x / R) = 1 := by
      apply apm_m02j02_bump_rescale_eq_one b hR
      simpa [Metric.mem_closedBall, Real.dist_eq] using hx
    simp [hx, hone]
  · have hb0 : 0 ≤ b (x / R) := b.nonneg
    have hb1 : b (x / R) ≤ 1 := b.le_one
    simp only [Pi.sub_apply, Set.indicator_of_mem (Set.mem_compl hx), Real.norm_eq_abs]
    rw [show f x - b (x / R) * f x = (1 - b (x / R)) * f x by ring,
      abs_mul]
    have habs : |1 - b (x / R)| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hb1)]
      linarith
    simpa using mul_le_mul_of_nonneg_right habs (abs_nonneg (f x))

lemma apm_m02j02_bump_rescale_cross_eLpNorm_le (b : ContDiffBump (0 : ℝ))
    {C R : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x : ℝ, |deriv b x| ≤ C)
    (hR : 0 < R) (f : ℝ → ℝ) :
    eLpNorm (fun x : ℝ => (deriv b (x / R) / R) * f x) 2 volume ≤
      ENNReal.ofReal (C / R) * eLpNorm f 2 volume := by
  calc
    eLpNorm (fun x : ℝ => (deriv b (x / R) / R) * f x) 2 volume ≤
        eLpNorm (fun x : ℝ => (C / R) * f x) 2 volume := by
      apply eLpNorm_mono
      intro x
      simp only [Real.norm_eq_abs, abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg (f x))
      rw [abs_div, abs_of_pos hR, abs_of_nonneg (div_nonneg hC0 hR.le)]
      exact div_le_div_of_nonneg_right (hC (x / R)) hR.le
    _ = ENNReal.ofReal (C / R) * eLpNorm f 2 volume := by
      simpa [Pi.smul_apply, smul_eq_mul, Real.enorm_eq_ofReal_abs,
        abs_of_nonneg (div_nonneg hC0 hR.le)] using
          eLpNorm_const_smul (C / R) f (2 : ℝ≥0∞) volume

lemma apm_m02j02_bump_rescale_deriv_error_le (b : ContDiffBump (0 : ℝ))
    {C R : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x : ℝ, |deriv b x| ≤ C)
    (hR : 0 < R) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    eLpNorm (deriv f - deriv (fun x : ℝ => b (x / R) * f x)) 2 volume ≤
      eLpNorm ((Metric.closedBall (0 : ℝ) (R * b.rIn))ᶜ.indicator (deriv f))
          2 volume +
        ENNReal.ofReal (C / R) * eLpNorm f 2 volume := by
  have heq : (deriv f - deriv (fun x : ℝ => b (x / R) * f x)) =
      (deriv f - fun x : ℝ => b (x / R) * deriv f x) +
        -(fun x : ℝ => (deriv b (x / R) / R) * f x) := by
    funext x
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
    rw [apm_m02j02_deriv_bump_rescale_mul b hR.ne' (hf.of_le (by norm_num))]
    ring
  rw [heq]
  calc
    eLpNorm ((deriv f - fun x : ℝ => b (x / R) * deriv f x) +
        -(fun x : ℝ => (deriv b (x / R) / R) * f x)) 2 volume ≤
        eLpNorm (deriv f - fun x : ℝ => b (x / R) * deriv f x) 2 volume +
          eLpNorm (-(fun x : ℝ => (deriv b (x / R) / R) * f x)) 2 volume := by
      apply eLpNorm_add_le
      · exact ((hf.continuous_deriv (by simp)).aestronglyMeasurable.sub
          (((b.contDiff (n := (⊤ : ℕ∞))).continuous.comp
            (by fun_prop)).aestronglyMeasurable.mul
              (hf.continuous_deriv (by simp)).aestronglyMeasurable))
      · have hdb : Continuous (deriv (b : ℝ → ℝ)) :=
          (b.contDiff (n := (⊤ : ℕ∞))).continuous_deriv (by simp)
        have hxR : Continuous (fun x : ℝ => x / R) := by fun_prop
        exact (((hdb.comp hxR).div_const R).mul hf.continuous).neg.aestronglyMeasurable
      · norm_num
    _ ≤ _ := by
      rw [eLpNorm_neg]
      exact add_le_add
        (apm_m02j02_bump_rescale_value_error_le b hR (deriv f))
        (apm_m02j02_bump_rescale_cross_eLpNorm_le b hC0 hC hR f)

lemma apm_m02j02_ofReal_div_mul_tendsto_zero {C K : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) :
    Tendsto (fun R : ℝ => ENNReal.ofReal (C / R) * ENNReal.ofReal K)
      atTop (nhds 0) := by
  have hreal : Tendsto (fun R : ℝ => C / R) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_id :
      Tendsto (fun R : ℝ => C / R) atTop (nhds 0))
  have hprod : Tendsto (fun R : ℝ => (C / R) * K) atTop (nhds 0) := by
    simpa using hreal.mul_const K
  convert ENNReal.tendsto_ofReal hprod using 1
  · funext R
    rw [ENNReal.ofReal_mul' hK]
  · simp

lemma apm_m02j02_cutoff_cross_tendsto_zero {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) {C : ℝ} (hC : 0 ≤ C) :
    Tendsto (fun R : ℝ => ENNReal.ofReal (C / R) * eLpNorm f 2 volume)
      atTop (nhds 0) := by
  have hfinite : eLpNorm f 2 volume ≠ (∞ : ℝ≥0∞) := ne_of_lt hf.eLpNorm_lt_top
  have hrepr : ENNReal.ofReal (eLpNorm f 2 volume).toReal = eLpNorm f 2 volume :=
    ENNReal.ofReal_toReal hfinite
  rw [← hrepr]
  exact apm_m02j02_ofReal_div_mul_tendsto_zero hC ENNReal.toReal_nonneg

lemma apm_m02j02_cutoff_cross_eventually_lt_ofReal {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ENNReal.ofReal (C / R) * eLpNorm f 2 volume < ENNReal.ofReal ε := by
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  have hev : ∀ᶠ R : ℝ in atTop,
      ENNReal.ofReal (C / R) * eLpNorm f 2 volume < ENNReal.ofReal ε :=
    (apm_m02j02_cutoff_cross_tendsto_zero hf hC)
      (Iio_mem_nhds hpos)
  exact (eventually_atTop.1 hev)

lemma apm_m02j02_eLpNorm_restrict_Ioi_le (f : ℝ → ℝ) (p : ℝ≥0∞) :
    eLpNorm f p (volume.restrict (Ioi (0 : ℝ))) ≤ eLpNorm f p volume := by
  exact eLpNorm_mono_measure f Measure.restrict_le_self

lemma apm_m02j02_graphNorm_restrict_Ioi_le (f g : ℝ → ℝ) :
    eLpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) +
        eLpNorm g 2 (volume.restrict (Ioi (0 : ℝ))) ≤
      eLpNorm f 2 volume + eLpNorm g 2 volume := by
  exact add_le_add (apm_m02j02_eLpNorm_restrict_Ioi_le f 2)
    (apm_m02j02_eLpNorm_restrict_Ioi_le g 2)

lemma apm_m02j02_eLpNorm_comp_one_sub
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f
      (volume.restrict (Iio (1 : ℝ)))) (p : ℝ≥0∞) :
    eLpNorm (fun x : ℝ => f (1 - x)) p
        (volume.restrict (Ioi (0 : ℝ))) =
      eLpNorm f p (volume.restrict (Iio (1 : ℝ))) := by
  have hpre : (fun x : ℝ => 1 - x) ⁻¹' Iio (1 : ℝ) = Ioi (0 : ℝ) := by
    ext x
    simp
  have hmp : MeasurePreserving (fun x : ℝ => 1 - x)
      (volume.restrict (Ioi (0 : ℝ)))
      (volume.restrict (Iio (1 : ℝ))) := by
    simpa only [hpre] using
      ((volume : Measure ℝ).measurePreserving_sub_left (1 : ℝ)).restrict_preimage_emb
        (Homeomorph.subLeft (1 : ℝ)).measurableEmbedding (Iio (1 : ℝ))
  exact eLpNorm_comp_measurePreserving hf hmp

lemma apm_m02j02_deriv_comp_one_sub
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝ) :
    deriv (fun y : ℝ => f (1 - y)) x = -deriv f (1 - x) := by
  have hout : HasDerivAt f (deriv f (1 - x)) (1 - x) :=
    (hf.differentiable (by simp) (1 - x)).hasDerivAt
  have hin : HasDerivAt (fun y : ℝ => 1 - y) (-1) x :=
    (hasDerivAt_id x).const_sub 1
  simpa only [Function.comp_apply, mul_neg, mul_one] using
    (hout.comp x hin).deriv

lemma apm_m02j02_graphNorm_sub_triangle_Ioi
    (f df g dg h dh : ℝ → ℝ)
    (hf : Continuous f) (hdf : Continuous df)
    (hg : Continuous g) (hdg : Continuous dg)
    (hh : Continuous h) (hdh : Continuous dh) :
    eLpNorm (f - h) 2 (volume.restrict (Ioi (0 : ℝ))) +
        eLpNorm (df - dh) 2 (volume.restrict (Ioi (0 : ℝ))) ≤
      (eLpNorm (f - g) 2 (volume.restrict (Ioi (0 : ℝ))) +
        eLpNorm (df - dg) 2 (volume.restrict (Ioi (0 : ℝ)))) +
      (eLpNorm (g - h) 2 (volume.restrict (Ioi (0 : ℝ))) +
        eLpNorm (dg - dh) 2 (volume.restrict (Ioi (0 : ℝ)))) := by
  have hv : eLpNorm (f - h) 2 (volume.restrict (Ioi (0 : ℝ))) ≤
      eLpNorm (f - g) 2 (volume.restrict (Ioi (0 : ℝ))) +
        eLpNorm (g - h) 2 (volume.restrict (Ioi (0 : ℝ))) := by
    rw [show f - h = (f - g) + (g - h) by funext x; simp]
    apply eLpNorm_add_le
    · exact (hf.sub hg).aestronglyMeasurable
    · exact (hg.sub hh).aestronglyMeasurable
    · norm_num
  have hd : eLpNorm (df - dh) 2 (volume.restrict (Ioi (0 : ℝ))) ≤
      eLpNorm (df - dg) 2 (volume.restrict (Ioi (0 : ℝ))) +
        eLpNorm (dg - dh) 2 (volume.restrict (Ioi (0 : ℝ))) := by
    rw [show df - dh = (df - dg) + (dg - dh) by funext x; simp]
    apply eLpNorm_add_le
    · exact (hdf.sub hdg).aestronglyMeasurable
    · exact (hdg.sub hdh).aestronglyMeasurable
    · norm_num
  calc
    _ ≤ (eLpNorm (f - g) 2 (volume.restrict (Ioi (0 : ℝ))) +
          eLpNorm (g - h) 2 (volume.restrict (Ioi (0 : ℝ)))) +
        (eLpNorm (df - dg) 2 (volume.restrict (Ioi (0 : ℝ))) +
          eLpNorm (dg - dh) 2 (volume.restrict (Ioi (0 : ℝ)))) := add_le_add hv hd
    _ = _ := by
      simp only [add_assoc]
      congr 1
      exact add_left_comm _ _ _

lemma apm_m02j02_Lp_tail_eventually_lt_ofReal {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      eLpNorm ((Metric.closedBall (0 : ℝ) R)ᶜ.indicator f) 2 volume <
        ENNReal.ofReal ε := by
  have hhalf : ENNReal.ofReal (ε / 2) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hε]
  obtain ⟨R₀, hR₀, htail⟩ := apm_m02j02_exists_Lp_tail_bound hf hhalf
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  have hmono :
      eLpNorm ((Metric.closedBall (0 : ℝ) R)ᶜ.indicator f) 2 volume ≤
        eLpNorm ((Metric.closedBall (0 : ℝ) R₀)ᶜ.indicator f) 2 volume := by
    apply eLpNorm_mono_ae'
    filter_upwards with x
    by_cases hx : x ∈ (Metric.closedBall (0 : ℝ) R)ᶜ
    · have hxsmall : x ∈ (Metric.closedBall (0 : ℝ) R₀)ᶜ := by
        simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, Set.mem_compl_iff,
          not_le] at hx ⊢
        exact lt_of_le_of_lt hR hx
      simp [hx, hxsmall]
    · simp [hx]
  exact hmono.trans_lt (htail.trans_lt (by
    rw [ENNReal.ofReal_lt_ofReal_iff hε]
    linarith))

lemma apm_m02j02_exists_common_cutoff_radius {f df : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hdf : MemLp df 2 volume)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧
      eLpNorm ((Metric.closedBall (0 : ℝ) R)ᶜ.indicator f) 2 volume <
        ENNReal.ofReal ε ∧
      eLpNorm ((Metric.closedBall (0 : ℝ) R)ᶜ.indicator df) 2 volume <
        ENNReal.ofReal ε ∧
      ENNReal.ofReal (C / R) * eLpNorm f 2 volume < ENNReal.ofReal ε := by
  obtain ⟨Rf, hRfpos, hRf⟩ := apm_m02j02_Lp_tail_eventually_lt_ofReal hf hε
  obtain ⟨Rd, hRdpos, hRd⟩ := apm_m02j02_Lp_tail_eventually_lt_ofReal hdf hε
  obtain ⟨Rc, hRc⟩ := apm_m02j02_cutoff_cross_eventually_lt_ofReal hf hC hε
  let R : ℝ := max (max Rf Rd) (max Rc 1)
  have hfR : Rf ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hdR : Rd ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  have hcR : Rc ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one
    (le_trans (le_max_right Rc 1) (le_max_right _ _))
  exact ⟨R, hRpos, hRf R hfR, hRd R hdR, hRc R hcR⟩

lemma apm_m02j02_exists_compact_graph_approx
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfLp : MemLp f 2 volume) (hdfLp : MemLp (deriv f) 2 volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ tsupport f ∧
      eLpNorm (f - φ) 2 volume +
        eLpNorm (deriv f - deriv φ) 2 volume < ENNReal.ofReal ε := by
  obtain ⟨b, hbIn, -, -⟩ := apm_m02j02_exists_centered_cutoff
  obtain ⟨C, hC0, hC⟩ := apm_m02j02_contDiffBump_deriv_bounded 0 b
  obtain ⟨R, hR, hval, hderiv, hcross⟩ :=
    apm_m02j02_exists_common_cutoff_radius hfLp hdfLp hC0
      (show 0 < ε / 4 by positivity)
  let φ : ℝ → ℝ := fun x => b (x / R) * f x
  refine ⟨φ, (apm_m02j02_bump_rescale_mul_regular b hR.ne' hf).1,
    (apm_m02j02_bump_rescale_mul_regular b hR.ne' hf).2,
    tsupport_mul_subset_right, ?_⟩
  have hv := apm_m02j02_bump_rescale_value_error_le b hR f
  have hd := apm_m02j02_bump_rescale_deriv_error_le b hC0 hC hR hf
  rw [hbIn, mul_one] at hv hd
  calc
    eLpNorm (f - φ) 2 volume + eLpNorm (deriv f - deriv φ) 2 volume ≤
      eLpNorm ((Metric.closedBall (0 : ℝ) R)ᶜ.indicator f) 2 volume +
        (eLpNorm ((Metric.closedBall (0 : ℝ) R)ᶜ.indicator (deriv f)) 2 volume +
          ENNReal.ofReal (C / R) * eLpNorm f 2 volume) := add_le_add hv hd
    _ < ENNReal.ofReal (ε / 4) +
        (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) :=
      ENNReal.add_lt_add hval (ENNReal.add_lt_add hderiv hcross)
    _ < ENNReal.ofReal ε := by
      have hq : 0 ≤ ε / 4 := by positivity
      rw [← ENNReal.ofReal_add hq hq,
        ← ENNReal.ofReal_add hq (add_nonneg hq hq),
        ENNReal.ofReal_lt_ofReal_iff hε]
      linarith

lemma apm_m02j02_hermite_inH10 (n : ℕ) :
    apm_m02j02_InH10 Set.univ
      (apm_m02j02_hermiteFunction n) (apm_m02j02_hermiteFunctionDeriv n) := by
  apply apm_m02j02_hermite_inH10_of_approx n
  intro ε hε
  obtain ⟨b, hbIn, -, -⟩ := apm_m02j02_exists_centered_cutoff
  obtain ⟨C, hC0, hC⟩ := apm_m02j02_contDiffBump_deriv_bounded 0 b
  obtain ⟨R, hR, hval, hderiv, hcross⟩ :=
    apm_m02j02_exists_common_cutoff_radius
      (apm_m02j02_hermiteFunction_memLp_two n)
      (apm_m02j02_hermiteFunctionDeriv_memLp_two n) hC0 (show 0 < ε / 4 by positivity)
  let φ : ℝ → ℝ := fun x => b (x / R) * apm_m02j02_hermiteFunction n x
  refine ⟨φ, (apm_m02j02_bump_rescale_mul_regular b hR.ne'
    (apm_m02j02_hermiteFunction_contDiff n)).1,
    (apm_m02j02_bump_rescale_mul_regular b hR.ne'
      (apm_m02j02_hermiteFunction_contDiff n)).2, Set.subset_univ _, ?_⟩
  have hv := apm_m02j02_bump_rescale_value_error_le b hR
    (apm_m02j02_hermiteFunction n)
  have hd := apm_m02j02_bump_rescale_deriv_error_le b hC0 hC hR
    (apm_m02j02_hermiteFunction_contDiff n)
  rw [hbIn, mul_one] at hv hd
  calc
    eLpNorm (apm_m02j02_hermiteFunction n - φ) 2 volume +
        eLpNorm (apm_m02j02_hermiteFunctionDeriv n - deriv φ) 2 volume ≤
      eLpNorm ((Metric.closedBall (0 : ℝ) R)ᶜ.indicator
          (apm_m02j02_hermiteFunction n)) 2 volume +
        (eLpNorm ((Metric.closedBall (0 : ℝ) R)ᶜ.indicator
            (apm_m02j02_hermiteFunctionDeriv n)) 2 volume +
          ENNReal.ofReal (C / R) *
            eLpNorm (apm_m02j02_hermiteFunction n) 2 volume) :=
      add_le_add hv hd
    _ < ENNReal.ofReal (ε / 4) +
        (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) :=
      ENNReal.add_lt_add hval (ENNReal.add_lt_add hderiv hcross)
    _ < ENNReal.ofReal ε := by
      have hq : 0 ≤ ε / 4 := by positivity
      rw [← ENNReal.ofReal_add hq hq,
        ← ENNReal.ofReal_add hq (add_nonneg hq hq),
        ENNReal.ofReal_lt_ofReal_iff hε]
      linarith

lemma apm_m02j02_continuous_finsupp_sum (e : ℕ → ℝ → ℝ)
    (he : ∀ n, Continuous (e n)) (c : ℕ →₀ ℝ) :
    Continuous (c.sum fun n a ↦ a • e n) := by
  rw [Finsupp.sum]
  rw [show (∑ n ∈ c.support, c n • e n) =
      (fun x => ∑ n ∈ c.support, c n • e n x) by
        funext x
        simp]
  apply continuous_finset_sum
  intro n hn
  exact (he n).const_smul (c n)

lemma apm_m02j02_density_of_testFunction_density
    (s : Set ℝ) (e de : ℕ → ℝ → ℝ)
    (he : ∀ n, Continuous (e n)) (hde : ∀ n, Continuous (de n))
    (htest : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ s → ∀ ε : ℝ, 0 < ε → ∃ c : ℕ →₀ ℝ,
        eLpNorm (φ - c.sum fun n a ↦ a • e n) 2 (volume.restrict s) +
          eLpNorm (deriv φ - c.sum fun n a ↦ a • de n) 2
            (volume.restrict s) < ENNReal.ofReal ε) :
    ∀ u du : ℝ → ℝ, apm_m02j02_InH10 s u du →
      ∀ ε : ℝ, 0 < ε → ∃ c : ℕ →₀ ℝ,
        eLpNorm (u - c.sum fun n a ↦ a • e n) 2 (volume.restrict s) +
          eLpNorm (du - c.sum fun n a ↦ a • de n) 2
            (volume.restrict s) < ENNReal.ofReal ε := by
  intro u du hu ε hε
  obtain ⟨φ, hφsmooth, hφcomp, hφsub, hφerr⟩ :=
    hu.2.2.2 (ε / 2) (by positivity)
  obtain ⟨c, hc⟩ := htest φ hφsmooth hφcomp hφsub (ε / 2) (by positivity)
  let E : ℝ → ℝ := c.sum fun n a ↦ a • e n
  let D : ℝ → ℝ := c.sum fun n a ↦ a • de n
  have hE : Continuous E := apm_m02j02_continuous_finsupp_sum e he c
  have hD : Continuous D := apm_m02j02_continuous_finsupp_sum de hde c
  have hφd : Continuous (deriv φ) :=
    hφsmooth.continuous_deriv (by simp)
  have huval : eLpNorm (u - E) 2 (volume.restrict s) ≤
      eLpNorm (u - φ) 2 (volume.restrict s) +
        eLpNorm (φ - E) 2 (volume.restrict s) := by
    have h := eLpNorm_add_le
      (hu.1.aestronglyMeasurable.sub hφsmooth.continuous.aestronglyMeasurable)
      (hφsmooth.continuous.aestronglyMeasurable.sub hE.aestronglyMeasurable)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hfun : u - E = (u - φ) + (φ - E) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [hfun]
    exact h
  have huderiv : eLpNorm (du - D) 2 (volume.restrict s) ≤
      eLpNorm (du - deriv φ) 2 (volume.restrict s) +
        eLpNorm (deriv φ - D) 2 (volume.restrict s) := by
    have h := eLpNorm_add_le
      (hu.2.1.aestronglyMeasurable.sub hφd.aestronglyMeasurable)
      (hφd.aestronglyMeasurable.sub hD.aestronglyMeasurable)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hfun : du - D = (du - deriv φ) + (deriv φ - D) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [hfun]
    exact h
  refine ⟨c, ?_⟩
  change eLpNorm (u - E) 2 (volume.restrict s) +
    eLpNorm (du - D) 2 (volume.restrict s) < ENNReal.ofReal ε
  calc
    _ ≤ (eLpNorm (u - φ) 2 (volume.restrict s) +
          eLpNorm (φ - E) 2 (volume.restrict s)) +
        (eLpNorm (du - deriv φ) 2 (volume.restrict s) +
          eLpNorm (deriv φ - D) 2 (volume.restrict s)) := add_le_add huval huderiv
    _ = (eLpNorm (u - φ) 2 (volume.restrict s) +
          eLpNorm (du - deriv φ) 2 (volume.restrict s)) +
        (eLpNorm (φ - E) 2 (volume.restrict s) +
          eLpNorm (deriv φ - D) 2 (volume.restrict s)) := by
      rw [add_assoc,
        add_left_comm (eLpNorm (φ - E) 2 (volume.restrict s))
          (eLpNorm (du - deriv φ) 2 (volume.restrict s)),
        ← add_assoc]
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      ENNReal.add_lt_add hφerr hc
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

lemma apm_m02j02_oddHermite_continuous (n : ℕ) :
    Continuous (apm_m02j02_hermiteFunction (2 * n + 1)) :=
  (apm_m02j02_hermiteFunction_contDiff (2 * n + 1)).continuous

lemma apm_m02j02_oddHermiteDeriv_continuous (n : ℕ) :
    Continuous (apm_m02j02_hermiteFunctionDeriv (2 * n + 1)) :=
  apm_m02j02_hermiteFunctionDeriv_continuous (2 * n + 1)

lemma apm_m02j02_hermiteReal_succ (n : ℕ) :
    (Polynomial.hermite (n + 1)).map (Int.castRingHom ℝ) =
      Polynomial.X * (Polynomial.hermite n).map (Int.castRingHom ℝ) -
        ((Polynomial.hermite n).map (Int.castRingHom ℝ)).derivative := by
  rw [Polynomial.hermite_succ, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.derivative_map]

lemma apm_m02j02_derivative_hermite_succ (n : ℕ) :
    (Polynomial.hermite (n + 1)).derivative =
      Polynomial.C (n + 1 : ℤ) * Polynomial.hermite n := by
  induction n with
  | zero =>
      rw [Polynomial.hermite_one, Polynomial.derivative_X]
      norm_num
  | succ n ih =>
      rw [Polynomial.hermite_succ, Polynomial.derivative_sub,
        Polynomial.derivative_mul, Polynomial.derivative_X, ih,
        Polynomial.hermite_succ n]
      push_cast
      simp only [Polynomial.derivative_mul, Polynomial.derivative_C, mul_zero,
        add_zero]
      norm_num [← Polynomial.C_add]
      ring

lemma apm_m02j02_hermiteFunctionDeriv_recurrence (n : ℕ) (x : ℝ) :
    apm_m02j02_hermiteFunctionDeriv n x =
      (x / 2) * apm_m02j02_hermiteFunction n x -
        apm_m02j02_hermiteFunction (n + 1) x := by
  let p : ℝ[X] := (Polynomial.hermite n).map (Int.castRingHom ℝ)
  let q : ℝ[X] := (Polynomial.hermite (n + 1)).map (Int.castRingHom ℝ)
  have hp : HasDerivAt (fun y : ℝ => Polynomial.eval y p)
      (Polynomial.eval x p.derivative) x := p.hasDerivAt x
  have hexponent : HasDerivAt (fun y : ℝ => -(y ^ 2) / 4) (-x / 2) x := by
    convert ((hasDerivAt_id x).pow 2).neg.div_const 4 using 1 <;>
      simp [id_eq] <;> ring
  have hprod := hp.mul hexponent.exp
  have hrec : Polynomial.eval x q = x * Polynomial.eval x p -
      Polynomial.eval x p.derivative := by
    simpa [p, q] using
      congrArg (Polynomial.eval x) (apm_m02j02_hermiteReal_succ n)
  rw [← apm_m02j02_deriv_hermiteFunction]
  rw [show deriv (apm_m02j02_hermiteFunction n) x =
      Polynomial.eval x p.derivative * Real.exp (-(x ^ 2) / 4) +
        Polynomial.eval x p * (Real.exp (-(x ^ 2) / 4) * (-x / 2)) by
    exact hprod.deriv]
  change _ = (x / 2) * (Polynomial.eval x p * Real.exp (-(x ^ 2) / 4)) -
    Polynomial.eval x q * Real.exp (-(x ^ 2) / 4)
  rw [hrec]
  ring

lemma apm_m02j02_hermiteFunctionDeriv_succ_recurrence (n : ℕ) (x : ℝ) :
    apm_m02j02_hermiteFunctionDeriv (n + 1) x =
      (n + 1 : ℝ) * apm_m02j02_hermiteFunction n x -
        (x / 2) * apm_m02j02_hermiteFunction (n + 1) x := by
  let p : ℝ[X] := (Polynomial.hermite (n + 1)).map (Int.castRingHom ℝ)
  let q : ℝ[X] := (Polynomial.hermite n).map (Int.castRingHom ℝ)
  have hp : HasDerivAt (fun y : ℝ => Polynomial.eval y p)
      (Polynomial.eval x p.derivative) x := p.hasDerivAt x
  have hexponent : HasDerivAt (fun y : ℝ => -(y ^ 2) / 4) (-x / 2) x := by
    convert ((hasDerivAt_id x).pow 2).neg.div_const 4 using 1 <;>
      simp [id_eq] <;> ring
  have hprod := hp.mul hexponent.exp
  have hpoly : p.derivative = Polynomial.C (n + 1 : ℝ) * q := by
    simpa [p, q, Polynomial.derivative_map] using
      congrArg (Polynomial.map (Int.castRingHom ℝ))
        (apm_m02j02_derivative_hermite_succ n)
  rw [← apm_m02j02_deriv_hermiteFunction]
  rw [show deriv (apm_m02j02_hermiteFunction (n + 1)) x =
      Polynomial.eval x p.derivative * Real.exp (-(x ^ 2) / 4) +
        Polynomial.eval x p * (Real.exp (-(x ^ 2) / 4) * (-x / 2)) by
    exact hprod.deriv]
  rw [hpoly]
  change _ = (n + 1 : ℝ) *
      (Polynomial.eval x q * Real.exp (-(x ^ 2) / 4)) -
    (x / 2) * (Polynomial.eval x p * Real.exp (-(x ^ 2) / 4))
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

/-- Symmetric adjacent-mode form of the derivative recurrence, avoiding the
coordinate multiplier. -/
lemma apm_m02j02_two_mul_hermiteFunctionDeriv_succ (n : ℕ) (x : ℝ) :
    2 * apm_m02j02_hermiteFunctionDeriv (n + 1) x =
      (n + 1 : ℝ) * apm_m02j02_hermiteFunction n x -
        apm_m02j02_hermiteFunction (n + 2) x := by
  have h₁ := apm_m02j02_hermiteFunctionDeriv_succ_recurrence n x
  have h₂ := apm_m02j02_hermiteFunctionDeriv_recurrence (n + 1) x
  rw [show n + 1 + 1 = n + 2 by omega] at h₂
  linarith

/-- Boundary case of the symmetric derivative recurrence. -/
lemma apm_m02j02_two_mul_hermiteFunctionDeriv_zero (x : ℝ) :
    2 * apm_m02j02_hermiteFunctionDeriv 0 x =
      -apm_m02j02_hermiteFunction 1 x := by
  have h := apm_m02j02_hermiteFunctionDeriv_recurrence 0 x
  have h₁ : apm_m02j02_hermiteFunction 1 x =
      x * apm_m02j02_hermiteFunction 0 x := by
    simp [apm_m02j02_hermiteFunction, Polynomial.hermite_zero]
  rw [h₁] at h
  linarith

lemma apm_m02j02_mul_hermiteFunction_succ (n : ℕ) (x : ℝ) :
    x * apm_m02j02_hermiteFunction (n + 1) x =
      apm_m02j02_hermiteFunction (n + 2) x +
        (n + 1 : ℝ) * apm_m02j02_hermiteFunction n x := by
  have hraise := apm_m02j02_hermiteFunctionDeriv_recurrence (n + 1) x
  have hlower := apm_m02j02_hermiteFunctionDeriv_succ_recurrence n x
  linarith

lemma apm_m02j02_hermiteFunctionDeriv_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (apm_m02j02_hermiteFunctionDeriv n)
      ((x ^ 2 / 4 - (n : ℝ) - 1 / 2) *
        apm_m02j02_hermiteFunction n x) x := by
  rw [show apm_m02j02_hermiteFunctionDeriv n = fun y : ℝ =>
      (y / 2) * apm_m02j02_hermiteFunction n y -
        apm_m02j02_hermiteFunction (n + 1) y by
    funext y
    exact apm_m02j02_hermiteFunctionDeriv_recurrence n y]
  have h := ((hasDerivAt_id x).div_const 2).mul
      (apm_m02j02_hermiteFunction_hasDerivAt n x) |>.sub
        (apm_m02j02_hermiteFunction_hasDerivAt (n + 1) x)
  convert h using 1
  rw [apm_m02j02_hermiteFunctionDeriv_recurrence n x,
    apm_m02j02_hermiteFunctionDeriv_succ_recurrence n x]
  simp only [id_eq, add_comm n 1]
  ring

lemma apm_m02j02_secondDeriv_hermiteFunction (n : ℕ) (x : ℝ) :
    deriv (apm_m02j02_hermiteFunctionDeriv n) x =
      (x ^ 2 / 4 - (n : ℝ) - 1 / 2) *
        apm_m02j02_hermiteFunction n x :=
  (apm_m02j02_hermiteFunctionDeriv_hasDerivAt n x).deriv

lemma apm_m02j02_secondDeriv_hermiteFunction_memLp_two (n : ℕ) :
    MemLp (fun x : ℝ => deriv (apm_m02j02_hermiteFunctionDeriv n) x)
      2 volume := by
  let p : ℝ[X] := (Polynomial.hermite n).map (Int.castRingHom ℝ)
  let q : ℝ[X] :=
    (Polynomial.C (1 / 4) * Polynomial.X ^ 2 -
      Polynomial.C ((n : ℝ) + 1 / 2)) * p
  apply (memLp_congr_ae (Filter.Eventually.of_forall fun x =>
    show deriv (apm_m02j02_hermiteFunctionDeriv n) x =
      Polynomial.eval x q * Real.exp (-(x ^ 2) / 4) by
      rw [apm_m02j02_secondDeriv_hermiteFunction]
      simp only [apm_m02j02_hermiteFunction, q, p, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
      ring)).mpr
  exact apm_m02j02_polynomial_gaussian_memLp_two q

lemma apm_m02j02_integral_hermite_mul_secondDeriv (m n : ℕ) :
    (∫ x : ℝ, apm_m02j02_hermiteFunction m x *
      deriv (apm_m02j02_hermiteFunctionDeriv n) x) =
      -∫ x : ℝ, apm_m02j02_hermiteFunctionDeriv m x *
        apm_m02j02_hermiteFunctionDeriv n x := by
  apply MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
  · intro x _
    exact apm_m02j02_hermiteFunction_hasDerivAt m x
  · intro x _
    rw [apm_m02j02_secondDeriv_hermiteFunction]
    exact apm_m02j02_hermiteFunctionDeriv_hasDerivAt n x
  · exact (apm_m02j02_hermiteFunction_memLp_two m).integrable_mul
      (apm_m02j02_secondDeriv_hermiteFunction_memLp_two n)
  · exact (apm_m02j02_hermiteFunctionDeriv_memLp_two m).integrable_mul
      (apm_m02j02_hermiteFunctionDeriv_memLp_two n)
  · exact (apm_m02j02_hermiteFunction_memLp_two m).integrable_mul
      (apm_m02j02_hermiteFunctionDeriv_memLp_two n)

/-- For a smooth compactly supported test function, the Hermite oscillator
can be transferred across the whole-line integral by two integrations by
parts. -/
lemma apm_m02j02_integral_test_mul_secondDeriv_hermite
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (n : ℕ) :
    (∫ x : ℝ, φ x * deriv (apm_m02j02_hermiteFunctionDeriv n) x) =
      ∫ x : ℝ, deriv (deriv φ) x * apm_m02j02_hermiteFunction n x := by
  have hφd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hφdc : HasCompactSupport (deriv φ) := hφc.deriv
  have hφddc : HasCompactSupport (deriv (deriv φ)) := hφdc.deriv
  have hnsecond : Continuous
      (fun x : ℝ ↦ deriv (apm_m02j02_hermiteFunctionDeriv n) x) := by
    rw [show (fun x : ℝ ↦ deriv (apm_m02j02_hermiteFunctionDeriv n) x) =
        fun x ↦ (x ^ 2 / 4 - (n : ℝ) - 1 / 2) *
          apm_m02j02_hermiteFunction n x by
      funext x
      exact apm_m02j02_secondDeriv_hermiteFunction n x]
    apply Continuous.mul
    · fun_prop
    · exact (apm_m02j02_hermiteFunction_contDiff n).continuous
  have hfirst :
      (∫ x : ℝ, φ x * deriv (apm_m02j02_hermiteFunctionDeriv n) x) =
        -∫ x : ℝ, deriv φ x * apm_m02j02_hermiteFunctionDeriv n x := by
    apply MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    · intro x _
      exact (hφ.differentiable (by simp) x).hasDerivAt
    · intro x _
      rw [apm_m02j02_secondDeriv_hermiteFunction]
      exact apm_m02j02_hermiteFunctionDeriv_hasDerivAt n x
    · simpa [mul_comm] using apm_m02j02_integrable_continuous_mul_compact _ _
        hnsecond hφ.continuous hφc
    · simpa [mul_comm] using apm_m02j02_integrable_continuous_mul_compact _ _
        (apm_m02j02_hermiteFunctionDeriv_continuous n)
        hφd.continuous hφdc
    · simpa [mul_comm] using apm_m02j02_integrable_continuous_mul_compact _ _
        (apm_m02j02_hermiteFunctionDeriv_continuous n)
        hφ.continuous hφc
  have hsecond :
      (∫ x : ℝ, apm_m02j02_hermiteFunction n x * deriv (deriv φ) x) =
        -∫ x : ℝ, apm_m02j02_hermiteFunctionDeriv n x * deriv φ x := by
    apply MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    · intro x _
      exact apm_m02j02_hermiteFunction_hasDerivAt n x
    · intro x _
      exact (hφd.differentiable (by simp) x).hasDerivAt
    · exact apm_m02j02_integrable_continuous_mul_compact _ _
        (apm_m02j02_hermiteFunction_contDiff n).continuous
        (contDiff_infty_iff_deriv.mp hφd).2.continuous hφddc
    · exact apm_m02j02_integrable_continuous_mul_compact _ _
        (apm_m02j02_hermiteFunctionDeriv_continuous n)
        hφd.continuous hφdc
    · exact apm_m02j02_integrable_continuous_mul_compact _ _
        (apm_m02j02_hermiteFunction_contDiff n).continuous
        hφd.continuous hφdc
  rw [hfirst]
  have hcomm : (∫ x : ℝ,
      deriv φ x * apm_m02j02_hermiteFunctionDeriv n x) =
      ∫ x : ℝ, apm_m02j02_hermiteFunctionDeriv n x * deriv φ x := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  calc
    -∫ x : ℝ, deriv φ x * apm_m02j02_hermiteFunctionDeriv n x =
        -∫ x : ℝ, apm_m02j02_hermiteFunctionDeriv n x * deriv φ x := by
          rw [hcomm]
    _ = ∫ x : ℝ, apm_m02j02_hermiteFunction n x * deriv (deriv φ) x :=
      hsecond.symm
    _ = ∫ x : ℝ, deriv (deriv φ) x * apm_m02j02_hermiteFunction n x := by
      apply integral_congr_ae
      filter_upwards with x
      ring

/-- The harmonic-oscillator eigenvalue can be transferred from a Hermite mode
to a smooth compactly supported test function. -/
lemma apm_m02j02_integral_test_oscillator_mul_hermite
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (n : ℕ) :
    (∫ x : ℝ, (-deriv (deriv φ) x + (x ^ 2 / 4) * φ x) *
        apm_m02j02_hermiteFunction n x) =
      ((n : ℝ) + 1 / 2) *
        ∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x := by
  have hφd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hφdd : Continuous (deriv (deriv φ)) := hφd.continuous_deriv (by simp)
  have hφddc : HasCompactSupport (deriv (deriv φ)) := hφc.deriv.deriv
  have hncont : Continuous (apm_m02j02_hermiteFunction n) :=
    (apm_m02j02_hermiteFunction_contDiff n).continuous
  have hiSecond : Integrable
      (fun x : ℝ ↦ deriv (deriv φ) x * apm_m02j02_hermiteFunction n x) volume :=
    by
      simpa [Pi.mul_apply, mul_comm] using
        apm_m02j02_integrable_continuous_mul_compact _ _ hncont hφdd hφddc
  have hiPotential : Integrable
      (fun x : ℝ ↦ (x ^ 2 / 4) * φ x * apm_m02j02_hermiteFunction n x) volume := by
    have hi := apm_m02j02_integrable_continuous_mul_compact
      (fun x : ℝ ↦ (x ^ 2 / 4) * apm_m02j02_hermiteFunction n x) φ
      (by fun_prop) hφ.continuous hφc
    apply hi.congr
    filter_upwards with x
    simp only [Pi.mul_apply]
    ring
  have hiBase : Integrable
      (fun x : ℝ ↦ φ x * apm_m02j02_hermiteFunction n x) volume :=
    by
      simpa [Pi.mul_apply, mul_comm] using
        apm_m02j02_integrable_continuous_mul_compact _ _ hncont hφ.continuous hφc
  have hparts := apm_m02j02_integral_test_mul_secondDeriv_hermite φ hφ hφc n
  have hosc :
      (∫ x : ℝ, deriv (deriv φ) x * apm_m02j02_hermiteFunction n x) =
        (∫ x : ℝ, (x ^ 2 / 4) * φ x * apm_m02j02_hermiteFunction n x) -
          ((n : ℝ) + 1 / 2) *
            ∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x := by
    rw [← hparts]
    calc
      (∫ x : ℝ, φ x * deriv (apm_m02j02_hermiteFunctionDeriv n) x) =
          ∫ x : ℝ, ((x ^ 2 / 4) * φ x *
            apm_m02j02_hermiteFunction n x -
            (((n : ℝ) + 1 / 2) *
              (φ x * apm_m02j02_hermiteFunction n x))) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [apm_m02j02_secondDeriv_hermiteFunction]
        ring
      _ = (∫ x : ℝ, (x ^ 2 / 4) * φ x *
            apm_m02j02_hermiteFunction n x) -
          ∫ x : ℝ, ((n : ℝ) + 1 / 2) *
            (φ x * apm_m02j02_hermiteFunction n x) :=
        integral_sub hiPotential (hiBase.const_mul _)
      _ = (∫ x : ℝ, (x ^ 2 / 4) * φ x *
            apm_m02j02_hermiteFunction n x) -
          ((n : ℝ) + 1 / 2) *
            ∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x := by
        rw [integral_const_mul]
  calc
    (∫ x : ℝ, (-deriv (deriv φ) x + (x ^ 2 / 4) * φ x) *
        apm_m02j02_hermiteFunction n x) =
        ∫ x : ℝ, (-(deriv (deriv φ) x *
          apm_m02j02_hermiteFunction n x)) +
          ((x ^ 2 / 4) * φ x * apm_m02j02_hermiteFunction n x) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = (∫ x : ℝ, -(deriv (deriv φ) x *
          apm_m02j02_hermiteFunction n x)) +
          ∫ x : ℝ, (x ^ 2 / 4) * φ x *
            apm_m02j02_hermiteFunction n x :=
      integral_add hiSecond.neg hiPotential
    _ =
        -(∫ x : ℝ, deriv (deriv φ) x *
          apm_m02j02_hermiteFunction n x) +
          ∫ x : ℝ, (x ^ 2 / 4) * φ x *
            apm_m02j02_hermiteFunction n x := by
      rw [integral_neg]
    _ = ((n : ℝ) + 1 / 2) *
        ∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x := by
      rw [hosc]
      ring

/-- The test-function oscillator expression remains smooth and compactly
supported, so the coefficient-transfer identity can be iterated. -/
lemma apm_m02j02_test_oscillator_regular
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ContDiff ℝ ∞
        (fun x : ℝ ↦ -deriv (deriv φ) x + (x ^ 2 / 4) * φ x) ∧
      HasCompactSupport
        (fun x : ℝ ↦ -deriv (deriv φ) x + (x ^ 2 / 4) * φ x) := by
  have hφd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hφdd : ContDiff ℝ ∞ (deriv (deriv φ)) :=
    (contDiff_infty_iff_deriv.mp hφd).2
  constructor
  · exact hφdd.neg.add ((by fun_prop : ContDiff ℝ ∞ (fun x : ℝ ↦ x ^ 2 / 4)).mul hφ)
  · exact hφc.deriv.deriv.neg.add hφc.mul_left

/-- Iterating the oscillator transfers an arbitrary power of every Hermite
eigenvalue onto one smooth compactly supported test function. -/
lemma apm_m02j02_exists_test_oscillator_iterate
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (k : ℕ) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      ∀ n : ℕ,
        (∫ x : ℝ, ψ x * apm_m02j02_hermiteFunction n x) =
          (((n : ℝ) + 1 / 2) ^ k) *
            ∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x := by
  induction k with
  | zero =>
      refine ⟨φ, hφ, hφc, ?_⟩
      intro n
      simp
  | succ k ih =>
      obtain ⟨ψ, hψ, hψc, hcoeff⟩ := ih
      let χ : ℝ → ℝ := fun x ↦
        -deriv (deriv ψ) x + (x ^ 2 / 4) * ψ x
      have hχ := apm_m02j02_test_oscillator_regular ψ hψ hψc
      refine ⟨χ, hχ.1, hχ.2, ?_⟩
      intro n
      have htransfer :=
        apm_m02j02_integral_test_oscillator_mul_hermite ψ hψ hψc n
      change (∫ x : ℝ, χ x * apm_m02j02_hermiteFunction n x) = _
      rw [show (∫ x : ℝ, χ x * apm_m02j02_hermiteFunction n x) =
          ((n : ℝ) + 1 / 2) *
            ∫ x : ℝ, ψ x * apm_m02j02_hermiteFunction n x by
        simpa [χ] using htransfer,
        hcoeff n, pow_succ]
      ring

/-- Whole-line real `L²` Cauchy--Schwarz in the integral form used for
Hermite coefficients. -/
lemma apm_m02j02_abs_integral_mul_le_sq_integrals
    (f g : ℝ → ℝ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    |∫ x : ℝ, f x * g x| ≤
      (∫ x : ℝ, |f x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫ x : ℝ, |g x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) volume := by
    norm_num
    exact hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) volume := by
    norm_num
    exact hg
  calc
    |∫ x : ℝ, f x * g x| ≤ ∫ x : ℝ, |f x * g x| :=
      abs_integral_le_integral_abs
    _ = ∫ x : ℝ, ‖f x‖ * ‖g x‖ := by
      apply integral_congr_ae
      filter_upwards with x
      simp [Real.norm_eq_abs, abs_mul]
    _ ≤ (∫ x : ℝ, ‖f x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫ x : ℝ, ‖g x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      simpa using integral_mul_norm_le_Lp_mul_Lq
        Real.HolderConjugate.two_two hf' hg'
    _ = (∫ x : ℝ, |f x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫ x : ℝ, |g x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      simp [Real.norm_eq_abs]

/-- A continuous compactly supported real function belongs to whole-line
`L²`.  This is the specialization used for every oscillator iterate. -/
lemma apm_m02j02_memLp_two_of_contDiff_compact
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    MemLp f 2 volume :=
  hf.continuous.memLp_of_hasCompactSupport hfc

/-- Oscillator iteration and Cauchy--Schwarz give an arbitrary polynomial
decay estimate for the unnormalised Hermite coefficients of a test function. -/
lemma apm_m02j02_exists_hermite_coefficient_power_bound
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (k : ℕ) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      ∀ n : ℕ,
        (((n : ℝ) + 1 / 2) ^ k) *
            |∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x| ≤
          (∫ x : ℝ, |ψ x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
            (∫ x : ℝ, |apm_m02j02_hermiteFunction n x| ^ (2 : ℝ)) ^
              (1 / 2 : ℝ) := by
  obtain ⟨ψ, hψ, hψc, hcoeff⟩ :=
    apm_m02j02_exists_test_oscillator_iterate φ hφ hφc k
  refine ⟨ψ, hψ, hψc, fun n => ?_⟩
  have hCS := apm_m02j02_abs_integral_mul_le_sq_integrals ψ
    (apm_m02j02_hermiteFunction n)
    (apm_m02j02_memLp_two_of_contDiff_compact ψ hψ hψc)
    (apm_m02j02_hermiteFunction_memLp_two n)
  rw [hcoeff n, abs_mul, abs_of_nonneg (by positivity)] at hCS
  exact hCS

lemma apm_m02j02_hermite_orthogonal {m n : ℕ} (hmn : m ≠ n) :
    (∫ x : ℝ, apm_m02j02_hermiteFunction m x *
      apm_m02j02_hermiteFunction n x) = 0 := by
  let hm := apm_m02j02_hermiteFunction m
  let hn := apm_m02j02_hermiteFunction n
  let dm := apm_m02j02_hermiteFunctionDeriv m
  let dn := apm_m02j02_hermiteFunctionDeriv n
  let ddm := fun x : ℝ => deriv dm x
  let ddn := fun x : ℝ => deriv dn x
  have hibp_mn : (∫ x : ℝ, hm x * ddn x) = -∫ x : ℝ, dm x * dn x := by
    simpa [hm, hn, dm, dn, ddm, ddn] using
      apm_m02j02_integral_hermite_mul_secondDeriv m n
  have hibp_nm : (∫ x : ℝ, hn x * ddm x) = -∫ x : ℝ, dn x * dm x := by
    simpa [hm, hn, dm, dn, ddm, ddn] using
      apm_m02j02_integral_hermite_mul_secondDeriv n m
  have hderiv_integrals : (∫ x : ℝ, dm x * dn x) = ∫ x : ℝ, dn x * dm x := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  have hselfadjoint : (∫ x : ℝ, hm x * ddn x) = ∫ x : ℝ, hn x * ddm x := by
    rw [hibp_mn, hibp_nm, hderiv_integrals]
  have hi_left : Integrable (fun x : ℝ => hm x * ddn x) volume :=
    (apm_m02j02_hermiteFunction_memLp_two m).integrable_mul
      (apm_m02j02_secondDeriv_hermiteFunction_memLp_two n)
  have hi_right : Integrable (fun x : ℝ => hn x * ddm x) volume :=
    (apm_m02j02_hermiteFunction_memLp_two n).integrable_mul
      (apm_m02j02_secondDeriv_hermiteFunction_memLp_two m)
  have hzero : (∫ x : ℝ, hm x * ddn x - hn x * ddm x) = 0 := by
    rw [MeasureTheory.integral_sub hi_left hi_right, hselfadjoint, sub_self]
  have hfactor : (∫ x : ℝ, ((m : ℝ) - (n : ℝ)) * (hm x * hn x)) = 0 := by
    rw [← hzero]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    dsimp [hm, hn, dm, dn, ddm, ddn]
    rw [apm_m02j02_secondDeriv_hermiteFunction,
      apm_m02j02_secondDeriv_hermiteFunction]
    ring
  rw [MeasureTheory.integral_const_mul] at hfactor
  rcases mul_eq_zero.mp hfactor with hcast | hinner
  · exfalso
    apply hmn
    exact_mod_cast sub_eq_zero.mp hcast
  · simpa [hm, hn] using hinner

lemma apm_m02j02_integral_hermite_succ_mul_deriv (n : ℕ) :
    (∫ x : ℝ, apm_m02j02_hermiteFunction (n + 1) x *
      apm_m02j02_hermiteFunctionDeriv n x) =
      -∫ x : ℝ, apm_m02j02_hermiteFunctionDeriv (n + 1) x *
        apm_m02j02_hermiteFunction n x := by
  apply MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
  · intro x _
    exact apm_m02j02_hermiteFunction_hasDerivAt (n + 1) x
  · intro x _
    exact apm_m02j02_hermiteFunction_hasDerivAt n x
  · exact (apm_m02j02_hermiteFunction_memLp_two (n + 1)).integrable_mul
      (apm_m02j02_hermiteFunctionDeriv_memLp_two n)
  · exact (apm_m02j02_hermiteFunctionDeriv_memLp_two (n + 1)).integrable_mul
      (apm_m02j02_hermiteFunction_memLp_two n)
  · exact (apm_m02j02_hermiteFunction_memLp_two (n + 1)).integrable_mul
      (apm_m02j02_hermiteFunction_memLp_two n)

lemma apm_m02j02_hermite_norm_sq_succ (n : ℕ) :
    (∫ x : ℝ, apm_m02j02_hermiteFunction (n + 1) x ^ 2) =
      (n + 1 : ℝ) * ∫ x : ℝ, apm_m02j02_hermiteFunction n x ^ 2 := by
  let A := apm_m02j02_hermiteFunction (n + 1)
  let B := apm_m02j02_hermiteFunction n
  let dA := apm_m02j02_hermiteFunctionDeriv (n + 1)
  let dB := apm_m02j02_hermiteFunctionDeriv n
  have hiA : Integrable (fun x : ℝ => A x ^ 2) volume := by
    simpa [pow_two] using
      (apm_m02j02_hermiteFunction_memLp_two (n + 1)).integrable_mul
        (apm_m02j02_hermiteFunction_memLp_two (n + 1))
  have hiB : Integrable (fun x : ℝ => (n + 1 : ℝ) * B x ^ 2) volume := by
    apply Integrable.const_mul
    simpa [pow_two] using
      (apm_m02j02_hermiteFunction_memLp_two n).integrable_mul
        (apm_m02j02_hermiteFunction_memLp_two n)
  have hiAdB : Integrable (fun x : ℝ => A x * dB x) volume :=
    (apm_m02j02_hermiteFunction_memLp_two (n + 1)).integrable_mul
      (apm_m02j02_hermiteFunctionDeriv_memLp_two n)
  have hidAB : Integrable (fun x : ℝ => dA x * B x) volume :=
    (apm_m02j02_hermiteFunctionDeriv_memLp_two (n + 1)).integrable_mul
      (apm_m02j02_hermiteFunction_memLp_two n)
  have hibp : (∫ x : ℝ, A x * dB x) = -∫ x : ℝ, dA x * B x := by
    simpa [A, B, dA, dB] using apm_m02j02_integral_hermite_succ_mul_deriv n
  have hpoint : ∀ x : ℝ,
      A x ^ 2 - (n + 1 : ℝ) * B x ^ 2 = -(A x * dB x + dA x * B x) := by
    intro x
    dsimp [A, B, dA, dB]
    rw [apm_m02j02_hermiteFunctionDeriv_recurrence n x,
      apm_m02j02_hermiteFunctionDeriv_succ_recurrence n x]
    ring
  have hzero : (∫ x : ℝ, A x ^ 2 - (n + 1 : ℝ) * B x ^ 2) = 0 := by
    calc
      _ = ∫ x : ℝ, -(A x * dB x + dA x * B x) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        exact hpoint x
      _ = -((∫ x : ℝ, A x * dB x) + ∫ x : ℝ, dA x * B x) := by
        rw [MeasureTheory.integral_neg, MeasureTheory.integral_add hiAdB hidAB]
      _ = 0 := by rw [hibp]; ring
  rw [MeasureTheory.integral_sub hiA hiB,
    MeasureTheory.integral_const_mul] at hzero
  simpa [A, B] using sub_eq_zero.mp hzero

lemma apm_m02j02_hermite_norm_sq_zero :
    (∫ x : ℝ, apm_m02j02_hermiteFunction 0 x ^ 2) =
      Real.sqrt (Real.pi / (1 / 2 : ℝ)) := by
  rw [show (fun x : ℝ => apm_m02j02_hermiteFunction 0 x ^ 2) =
      fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2) by
    funext x
    simp [apm_m02j02_hermiteFunction, Polynomial.hermite_zero, pow_two,
      ← Real.exp_add]
    congr 1
    ring]
  exact integral_gaussian (1 / 2)

lemma apm_m02j02_hermite_norm_sq (n : ℕ) :
    (∫ x : ℝ, apm_m02j02_hermiteFunction n x ^ 2) =
      (n.factorial : ℝ) * Real.sqrt (Real.pi / (1 / 2 : ℝ)) := by
  induction n with
  | zero =>
      simpa using apm_m02j02_hermite_norm_sq_zero
  | succ n ih =>
      rw [apm_m02j02_hermite_norm_sq_succ, ih, Nat.factorial_succ]
      push_cast
      ring

lemma apm_m02j02_hermite_norm_sq_pos (n : ℕ) :
    0 < ∫ x : ℝ, apm_m02j02_hermiteFunction n x ^ 2 := by
  rw [apm_m02j02_hermite_norm_sq]
  positivity

lemma apm_m02j02_integral_abs_hermite_rpow_two (n : ℕ) :
    (∫ x : ℝ, |apm_m02j02_hermiteFunction n x| ^ (2 : ℝ)) =
      ((n.factorial : ℝ) * Real.sqrt (Real.pi / (1 / 2 : ℝ))) := by
  rw [show (fun x : ℝ =>
      |apm_m02j02_hermiteFunction n x| ^ (2 : ℝ)) =
      fun x => apm_m02j02_hermiteFunction n x ^ 2 by
    funext x
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, sq_abs]]
  exact apm_m02j02_hermite_norm_sq n

lemma apm_m02j02_integral_abs_hermite_rpow_two_half (n : ℕ) :
    (∫ x : ℝ, |apm_m02j02_hermiteFunction n x| ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) =
      Real.sqrt ((n.factorial : ℝ) *
        Real.sqrt (Real.pi / (1 / 2 : ℝ))) := by
  rw [apm_m02j02_integral_abs_hermite_rpow_two]
  exact (Real.sqrt_eq_rpow _).symm

/-- The coefficient decay estimate with the Hermite norm evaluated
explicitly. -/
lemma apm_m02j02_exists_hermite_coefficient_power_bound_explicit
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (k : ℕ) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      ∀ n : ℕ,
        (((n : ℝ) + 1 / 2) ^ k) *
            |∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x| ≤
          (∫ x : ℝ, |ψ x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
            Real.sqrt ((n.factorial : ℝ) *
              Real.sqrt (Real.pi / (1 / 2 : ℝ))) := by
  obtain ⟨ψ, hψ, hψc, hb⟩ :=
    apm_m02j02_exists_hermite_coefficient_power_bound φ hφ hφc k
  refine ⟨ψ, hψ, hψc, fun n => ?_⟩
  simpa only [apm_m02j02_integral_abs_hermite_rpow_two_half] using hb n

/-- After normalizing each Hermite mode, the oscillator estimate has a
constant right-hand side independent of the mode index. -/
lemma apm_m02j02_exists_normalized_hermite_coefficient_power_bound
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ,
      (((n : ℝ) + 1 / 2) ^ k) *
          |(∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
            Real.sqrt ((n.factorial : ℝ) *
              Real.sqrt (Real.pi / (1 / 2 : ℝ)))| ≤ A := by
  obtain ⟨ψ, hψ, hψc, hb⟩ :=
    apm_m02j02_exists_hermite_coefficient_power_bound_explicit φ hφ hφc k
  let A : ℝ := (∫ x : ℝ, |ψ x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  have hA : 0 ≤ A := Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _
  refine ⟨A, hA, fun n => ?_⟩
  let S : ℝ := Real.sqrt ((n.factorial : ℝ) *
    Real.sqrt (Real.pi / (1 / 2 : ℝ)))
  have hS : 0 < S := by
    dsimp [S]
    rw [Real.sqrt_pos]
    positivity
  have hn := hb n
  change (((n : ℝ) + 1 / 2) ^ k) *
      |(∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) / S| ≤ A
  calc
    (((n : ℝ) + 1 / 2) ^ k) *
        |(∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) / S| =
      ((((n : ℝ) + 1 / 2) ^ k) *
        |∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x|) / S := by
          rw [abs_div, abs_of_pos hS]
          ring
    _ ≤ (A * S) / S := div_le_div_of_nonneg_right hn hS.le
    _ = A := by field_simp

/-- Arbitrarily rapid polynomial decay of the normalized Hermite
coefficients implies absolute summability after any fixed polynomial weight. -/
lemma apm_m02j02_summable_weighted_normalized_hermite_coefficients
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (q : ℕ) :
    Summable (fun n : ℕ =>
      (((n : ℝ) + 1 / 2) ^ q) *
        |(∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
          Real.sqrt ((n.factorial : ℝ) *
            Real.sqrt (Real.pi / (1 / 2 : ℝ)))|) := by
  obtain ⟨A, hA, hbound⟩ :=
    apm_m02j02_exists_normalized_hermite_coefficient_power_bound
      φ hφ hφc (q + 2)
  have hs : Summable (fun n : ℕ => A / |(n : ℝ) + 1 / 2| ^ (2 : ℝ)) := by
    simpa [div_eq_mul_inv] using
      ((Real.summable_one_div_nat_add_rpow (1 / 2) 2).2 (by norm_num)).mul_left A
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ => A / |(n : ℝ) + 1 / 2| ^ (2 : ℝ))
    (g := fun n : ℕ =>
      (((n : ℝ) + 1 / 2) ^ q) *
        |(∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
          Real.sqrt ((n.factorial : ℝ) *
            Real.sqrt (Real.pi / (1 / 2 : ℝ)))|) ?_ ?_ hs
  · intro n
    positivity
  · intro n
    have hnpos : 0 < (n : ℝ) + 1 / 2 := by positivity
    have hb := hbound n
    have hpow : 0 < ((n : ℝ) + 1 / 2) ^ 2 := pow_pos hnpos _
    calc
      (((n : ℝ) + 1 / 2) ^ q) *
          |(∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
            Real.sqrt ((n.factorial : ℝ) *
              Real.sqrt (Real.pi / (1 / 2 : ℝ)))| =
        ((((n : ℝ) + 1 / 2) ^ (q + 2)) *
          |(∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
            Real.sqrt ((n.factorial : ℝ) *
              Real.sqrt (Real.pi / (1 / 2 : ℝ)))|) /
            (((n : ℝ) + 1 / 2) ^ 2) := by
              rw [pow_add]
              field_simp
      _ ≤ A / (((n : ℝ) + 1 / 2) ^ 2) :=
        div_le_div_of_nonneg_right hb hpow.le
      _ = A / |(n : ℝ) + 1 / 2| ^ (2 : ℝ) := by
        rw [abs_of_pos hnpos, show (2 : ℝ) = (2 : ℕ) by norm_num,
          Real.rpow_natCast]

/-- The normalized Hermite coefficients of a test function are square
summable. -/
lemma apm_m02j02_summable_sq_normalized_hermite_coefficients
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Summable (fun n : ℕ =>
      ((∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
        Real.sqrt ((n.factorial : ℝ) *
          Real.sqrt (Real.pi / (1 / 2 : ℝ)))) ^ 2) := by
  have h := apm_m02j02_summable_weighted_normalized_hermite_coefficients
    φ hφ hφc 0
  simp only [pow_zero, one_mul] at h
  obtain ⟨A, hA, hbound⟩ :=
    apm_m02j02_exists_normalized_hermite_coefficient_power_bound
      φ hφ hφc 0
  simp only [pow_zero, one_mul] at hbound
  apply Summable.of_nonneg_of_le
    (f := fun n : ℕ => A *
      |(∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
        Real.sqrt ((n.factorial : ℝ) *
          Real.sqrt (Real.pi / (1 / 2 : ℝ)))|)
  · intro n
    positivity
  · intro n
    rw [← sq_abs, pow_two]
    exact mul_le_mul_of_nonneg_right (hbound n) (abs_nonneg _)
  · exact h.mul_left A

/-- Polynomially weighted squares of the normalized Hermite coefficients are
summable; in particular the linear weight required by the derivative
recurrences is summable. -/
lemma apm_m02j02_summable_weighted_sq_normalized_hermite_coefficients
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (q : ℕ) :
    Summable (fun n : ℕ =>
      (((n : ℝ) + 1 / 2) ^ q) *
        ((∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
          Real.sqrt ((n.factorial : ℝ) *
            Real.sqrt (Real.pi / (1 / 2 : ℝ)))) ^ 2) := by
  have h := apm_m02j02_summable_weighted_normalized_hermite_coefficients
    φ hφ hφc q
  obtain ⟨A, hA, hbound⟩ :=
    apm_m02j02_exists_normalized_hermite_coefficient_power_bound
      φ hφ hφc 0
  simp only [pow_zero, one_mul] at hbound
  apply Summable.of_nonneg_of_le
    (f := fun n : ℕ => A *
      ((((n : ℝ) + 1 / 2) ^ q) *
        |(∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
          Real.sqrt ((n.factorial : ℝ) *
            Real.sqrt (Real.pi / (1 / 2 : ℝ)))|))
  · intro n
    positivity
  · intro n
    rw [← sq_abs, pow_two]
    calc
      ((n : ℝ) + 1 / 2) ^ q *
          (|((∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
            Real.sqrt ((n.factorial : ℝ) *
              Real.sqrt (Real.pi / (1 / 2 : ℝ))))| *
           |((∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
            Real.sqrt ((n.factorial : ℝ) *
              Real.sqrt (Real.pi / (1 / 2 : ℝ))))|) =
        |((∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
            Real.sqrt ((n.factorial : ℝ) *
              Real.sqrt (Real.pi / (1 / 2 : ℝ))))| *
          (((n : ℝ) + 1 / 2) ^ q *
           |((∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
            Real.sqrt ((n.factorial : ℝ) *
              Real.sqrt (Real.pi / (1 / 2 : ℝ))))|) := by ring
      _ ≤ A * ((((n : ℝ) + 1 / 2) ^ q) *
          |(∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
            Real.sqrt ((n.factorial : ℝ) *
              Real.sqrt (Real.pi / (1 / 2 : ℝ)))|) :=
        mul_le_mul_of_nonneg_right (hbound n) (by positivity)
  · exact h.mul_left A

/-- The partial sums of normalized Hermite coefficient squares form a Cauchy
sequence. -/
lemma apm_m02j02_cauchySeq_sum_range_sq_normalized_hermite_coefficients
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    CauchySeq (fun N : ℕ => ∑ n ∈ Finset.range N,
      ((∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
        Real.sqrt ((n.factorial : ℝ) *
          Real.sqrt (Real.pi / (1 / 2 : ℝ)))) ^ 2) :=
  (apm_m02j02_summable_sq_normalized_hermite_coefficients φ hφ hφc).hasSum
    |>.tendsto_sum_nat.cauchySeq

/-- The forward-shifted weighted coefficient squares arising from the lower
part of the derivative recurrence are summable. -/
lemma apm_m02j02_summable_succ_mul_succ_sq_normalized_coefficients
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Summable (fun n : ℕ => (n + 1 : ℝ) *
      ((∫ x : ℝ, φ x * apm_m02j02_hermiteFunction (n + 1) x) /
        Real.sqrt (((n + 1).factorial : ℝ) *
          Real.sqrt (Real.pi / (1 / 2 : ℝ)))) ^ 2) := by
  let c : ℕ → ℝ := fun n =>
    (∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
      Real.sqrt ((n.factorial : ℝ) *
        Real.sqrt (Real.pi / (1 / 2 : ℝ)))
  have h := apm_m02j02_summable_weighted_sq_normalized_hermite_coefficients
    φ hφ hφc 1
  have h' : Summable (fun n : ℕ => ((n : ℝ) + 1 / 2) * (c n) ^ 2) := by
    simpa only [pow_one, c] using h
  have hs : Summable (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) + 1 / 2) * (c (n + 1)) ^ 2) := by
    exact (summable_nat_add_iff 1).2 h'
  apply Summable.of_nonneg_of_le
    (f := fun n : ℕ => (((n + 1 : ℕ) : ℝ) + 1 / 2) * (c (n + 1)) ^ 2)
  · intro n
    positivity
  · intro n
    change (n + 1 : ℝ) * (c (n + 1)) ^ 2 ≤
      (((n + 1 : ℕ) : ℝ) + 1 / 2) * (c (n + 1)) ^ 2
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    push_cast
    linarith
  · simpa [c] using hs

/-- The unshifted weighted coefficient squares controlling the upper part of
the derivative recurrence are summable. -/
lemma apm_m02j02_summable_succ_mul_sq_normalized_coefficients
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Summable (fun n : ℕ => (n + 1 : ℝ) *
      ((∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
        Real.sqrt ((n.factorial : ℝ) *
          Real.sqrt (Real.pi / (1 / 2 : ℝ)))) ^ 2) := by
  let c : ℕ → ℝ := fun n =>
    (∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
      Real.sqrt ((n.factorial : ℝ) *
        Real.sqrt (Real.pi / (1 / 2 : ℝ)))
  have h := apm_m02j02_summable_weighted_sq_normalized_hermite_coefficients
    φ hφ hφc 1
  have h' : Summable (fun n : ℕ => ((n : ℝ) + 1 / 2) * (c n) ^ 2) := by
    simpa only [pow_one, c] using h
  apply Summable.of_nonneg_of_le
    (f := fun n : ℕ => 2 * (((n : ℝ) + 1 / 2) * (c n) ^ 2))
  · intro n
    positivity
  · intro n
    change (n + 1 : ℝ) * (c n) ^ 2 ≤
      2 * (((n : ℝ) + 1 / 2) * (c n) ^ 2)
    have hn : (0 : ℝ) ≤ n := by positivity
    nlinarith [sq_nonneg (c n)]
  · exact h'.mul_left 2

/-- The linear weight matching the coarse normalized derivative-mode bound is
absolutely summable against the normalized Hermite coefficients. -/
lemma apm_m02j02_summable_two_mul_add_one_mul_abs_normalized_coefficients
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Summable (fun n : ℕ => (2 * (n : ℝ) + 1) *
      |(∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
        Real.sqrt ((n.factorial : ℝ) *
          Real.sqrt (Real.pi / (1 / 2 : ℝ)))|) := by
  have h := apm_m02j02_summable_weighted_normalized_hermite_coefficients
    φ hφ hφc 1
  have h' : Summable (fun n : ℕ => ((n : ℝ) + 1 / 2) *
      |(∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
        Real.sqrt ((n.factorial : ℝ) *
          Real.sqrt (Real.pi / (1 / 2 : ℝ)))|) := by
    simpa only [pow_one] using h
  convert h'.mul_left 2 using 1
  funext n
  ring

/-- A difference of two square-summable real sequences is square-summable,
with the elementary `2u²+2v²` majorant used by the derivative reindexing. -/
lemma apm_m02j02_summable_sq_sub_of_summable_sq
    (u v : ℕ → ℝ) (hu : Summable (fun n => (u n) ^ 2))
    (hv : Summable (fun n => (v n) ^ 2)) :
    Summable (fun n => (u n - v n) ^ 2) := by
  apply Summable.of_nonneg_of_le
    (f := fun n => 2 * (u n) ^ 2 + 2 * (v n) ^ 2)
  · intro n
    positivity
  · intro n
    nlinarith [sq_nonneg (u n + v n)]
  · exact (hu.mul_left 2).add (hv.mul_left 2)

lemma apm_m02j02_hermite_gram (m n : ℕ) :
    (∫ x : ℝ, apm_m02j02_hermiteFunction m x *
      apm_m02j02_hermiteFunction n x) =
      if m = n then
        (n.factorial : ℝ) * Real.sqrt (Real.pi / (1 / 2 : ℝ))
      else 0 := by
  by_cases hmn : m = n
  · subst m
    simp only [if_pos rfl, ← pow_two]
    exact apm_m02j02_hermite_norm_sq n
  · rw [if_neg hmn]
    exact apm_m02j02_hermite_orthogonal hmn

lemma apm_m02j02_hermite_self_inner_ne_zero (n : ℕ) :
    (∫ x : ℝ, apm_m02j02_hermiteFunction n x *
      apm_m02j02_hermiteFunction n x) ≠ 0 := by
  rw [apm_m02j02_hermite_gram n n, if_pos rfl]
  positivity

lemma apm_m02j02_hermite_normalized_gram (m n : ℕ) :
    (∫ x : ℝ,
      (apm_m02j02_hermiteFunction m x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2)) *
      (apm_m02j02_hermiteFunction n x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))) =
      if m = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl]
    let I : ℝ := ∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2
    have hI : 0 < I := by
      simpa [I] using apm_m02j02_hermite_norm_sq_pos n
    have hsqrt : Real.sqrt I ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hI)
    have hsquare : Real.sqrt I * Real.sqrt I = I := by
      simpa [pow_two] using Real.sq_sqrt hI.le
    rw [show (fun x : ℝ =>
        (apm_m02j02_hermiteFunction n x / Real.sqrt I) *
          (apm_m02j02_hermiteFunction n x / Real.sqrt I)) =
        fun x : ℝ => (Real.sqrt I)⁻¹ * (Real.sqrt I)⁻¹ *
          (apm_m02j02_hermiteFunction n x ^ 2) by
      funext x
      field_simp]
    rw [MeasureTheory.integral_const_mul]
    change (Real.sqrt I)⁻¹ * (Real.sqrt I)⁻¹ * I = 1
    calc
      (Real.sqrt I)⁻¹ * (Real.sqrt I)⁻¹ * I =
          (Real.sqrt I)⁻¹ * (Real.sqrt I)⁻¹ *
            (Real.sqrt I * Real.sqrt I) := by rw [hsquare]
      _ = ((Real.sqrt I)⁻¹ * Real.sqrt I) *
            ((Real.sqrt I)⁻¹ * Real.sqrt I) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hsqrt]; norm_num
  · rw [if_neg hmn]
    rw [show (fun x : ℝ =>
        (apm_m02j02_hermiteFunction m x /
          Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2)) *
        (apm_m02j02_hermiteFunction n x /
          Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))) =
        fun x : ℝ =>
          (Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2))⁻¹ *
          (Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))⁻¹ *
          (apm_m02j02_hermiteFunction m x *
            apm_m02j02_hermiteFunction n x) by
      funext x
      ring]
    rw [MeasureTheory.integral_const_mul,
      apm_m02j02_hermite_orthogonal hmn]
    simp

/-- Derivative of a normalized positive-index Hermite mode as a combination
of its two adjacent normalized modes, with normalization ratios left exact. -/
lemma apm_m02j02_two_mul_normalized_hermiteDeriv_succ (n : ℕ) (x : ℝ) :
    2 * (apm_m02j02_hermiteFunctionDeriv (n + 1) x /
      Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction (n + 1) y ^ 2)) =
      ((n + 1 : ℝ) *
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2) /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction (n + 1) y ^ 2)) *
          (apm_m02j02_hermiteFunction n x /
            Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)) -
      (Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction (n + 2) y ^ 2) /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction (n + 1) y ^ 2)) *
          (apm_m02j02_hermiteFunction (n + 2) x /
            Real.sqrt (∫ y : ℝ,
              apm_m02j02_hermiteFunction (n + 2) y ^ 2)) := by
  have hn : Real.sqrt (∫ y : ℝ,
      apm_m02j02_hermiteFunction n y ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (apm_m02j02_hermite_norm_sq_pos n))
  have hn1 : Real.sqrt (∫ y : ℝ,
      apm_m02j02_hermiteFunction (n + 1) y ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (apm_m02j02_hermite_norm_sq_pos (n + 1)))
  have hn2 : Real.sqrt (∫ y : ℝ,
      apm_m02j02_hermiteFunction (n + 2) y ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (apm_m02j02_hermite_norm_sq_pos (n + 2)))
  field_simp [hn, hn1, hn2]
  rw [apm_m02j02_two_mul_hermiteFunctionDeriv_succ n x]

/-- Squared lower-mode coefficient in the normalized derivative recurrence. -/
lemma apm_m02j02_sq_normalized_hermiteDeriv_lower_ratio (n : ℕ) :
    (((n + 1 : ℝ) *
      Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2) /
      Real.sqrt (∫ y : ℝ,
        apm_m02j02_hermiteFunction (n + 1) y ^ 2)) ^ 2) = n + 1 := by
  let I : ℝ := ∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2
  have hI : 0 < I := by
    simpa [I] using apm_m02j02_hermite_norm_sq_pos n
  have hsucc : (∫ y : ℝ,
      apm_m02j02_hermiteFunction (n + 1) y ^ 2) = (n + 1 : ℝ) * I := by
    simpa [I] using apm_m02j02_hermite_norm_sq_succ n
  have hn1 : 0 < (n + 1 : ℝ) := by positivity
  rw [hsucc]
  have hsI : (Real.sqrt I) ^ 2 = I := Real.sq_sqrt hI.le
  have hsprod : (Real.sqrt ((n + 1 : ℝ) * I)) ^ 2 =
      (n + 1 : ℝ) * I := Real.sq_sqrt (mul_nonneg hn1.le hI.le)
  have hsprod0 : Real.sqrt ((n + 1 : ℝ) * I) ≠ 0 := by positivity
  field_simp [hsprod0]
  nlinarith

/-- Squared upper-mode coefficient in the normalized derivative recurrence. -/
lemma apm_m02j02_sq_normalized_hermiteDeriv_upper_ratio (n : ℕ) :
    ((Real.sqrt (∫ y : ℝ,
        apm_m02j02_hermiteFunction (n + 2) y ^ 2) /
      Real.sqrt (∫ y : ℝ,
        apm_m02j02_hermiteFunction (n + 1) y ^ 2)) ^ 2) = n + 2 := by
  let I : ℝ := ∫ y : ℝ, apm_m02j02_hermiteFunction (n + 1) y ^ 2
  have hI : 0 < I := by
    simpa [I] using apm_m02j02_hermite_norm_sq_pos (n + 1)
  have hsucc : (∫ y : ℝ,
      apm_m02j02_hermiteFunction (n + 2) y ^ 2) = (n + 2 : ℝ) * I := by
    have h := apm_m02j02_hermite_norm_sq_succ (n + 1)
    rw [show n + 1 + 1 = n + 2 by omega] at h
    push_cast at h
    change (∫ y : ℝ, apm_m02j02_hermiteFunction (n + 2) y ^ 2) =
      ((n : ℝ) + 1 + 1) * I at h
    linarith
  have hn2 : 0 < (n + 2 : ℝ) := by positivity
  rw [hsucc]
  have hsI : (Real.sqrt I) ^ 2 = I := Real.sq_sqrt hI.le
  have hsprod : (Real.sqrt ((n + 2 : ℝ) * I)) ^ 2 =
      (n + 2 : ℝ) * I := Real.sq_sqrt (mul_nonneg hn2.le hI.le)
  have hsI0 : Real.sqrt I ≠ 0 := by positivity
  change (Real.sqrt ((n + 2 : ℝ) * I) / Real.sqrt I) ^ 2 = n + 2
  field_simp [hsI0]
  nlinarith

/-- Successive normalized Hermite norms have squared ratio `n+1`. -/
lemma apm_m02j02_sq_hermite_norm_succ_ratio (n : ℕ) :
    ((Real.sqrt (∫ y : ℝ,
        apm_m02j02_hermiteFunction (n + 1) y ^ 2) /
      Real.sqrt (∫ y : ℝ,
        apm_m02j02_hermiteFunction n y ^ 2)) ^ 2) = n + 1 := by
  let I : ℝ := ∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2
  have hI : 0 < I := by
    simpa [I] using apm_m02j02_hermite_norm_sq_pos n
  rw [apm_m02j02_hermite_norm_sq_succ]
  change (Real.sqrt ((n + 1 : ℝ) * I) / Real.sqrt I) ^ 2 = n + 1
  have hsI : (Real.sqrt I) ^ 2 = I := Real.sq_sqrt hI.le
  have hsprod : (Real.sqrt ((n + 1 : ℝ) * I)) ^ 2 =
      (n + 1 : ℝ) * I := Real.sq_sqrt (by positivity)
  have hsI0 : Real.sqrt I ≠ 0 := by positivity
  field_simp [hsI0]
  nlinarith

/-- Normalized boundary derivative mode. -/
lemma apm_m02j02_two_mul_normalized_hermiteDeriv_zero (x : ℝ) :
    2 * (apm_m02j02_hermiteFunctionDeriv 0 x /
      Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction 0 y ^ 2)) =
      -(Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction 1 y ^ 2) /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction 0 y ^ 2)) *
        (apm_m02j02_hermiteFunction 1 x /
          Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction 1 y ^ 2)) := by
  have h0 : Real.sqrt (∫ y : ℝ,
      apm_m02j02_hermiteFunction 0 y ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (apm_m02j02_hermite_norm_sq_pos 0))
  have h1 : Real.sqrt (∫ y : ℝ,
      apm_m02j02_hermiteFunction 1 y ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (apm_m02j02_hermite_norm_sq_pos 1))
  field_simp [h0, h1]
  rw [apm_m02j02_two_mul_hermiteFunctionDeriv_zero]

/-- The lower adjacent-mode coefficients in the derivative of the normalized
Hermite projection are square-summable. -/
lemma apm_m02j02_summable_sq_normalized_hermiteDeriv_lower_coefficients
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Summable (fun n : ℕ =>
      ((((n + 1 : ℝ) *
          Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2) /
          Real.sqrt (∫ y : ℝ,
            apm_m02j02_hermiteFunction (n + 1) y ^ 2)) *
        ((∫ x : ℝ, φ x * apm_m02j02_hermiteFunction (n + 1) x) /
          Real.sqrt (((n + 1).factorial : ℝ) *
            Real.sqrt (Real.pi / (1 / 2 : ℝ))))) ^ 2)) := by
  have h := apm_m02j02_summable_succ_mul_succ_sq_normalized_coefficients
    φ hφ hφc
  convert h using 1
  funext n
  rw [mul_pow, apm_m02j02_sq_normalized_hermiteDeriv_lower_ratio]

/-- The upper adjacent-mode coefficients in the derivative of the normalized
Hermite projection are square-summable, including the mode-zero boundary. -/
lemma apm_m02j02_summable_sq_normalized_hermiteDeriv_upper_coefficients
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Summable (fun n : ℕ =>
      (((Real.sqrt (∫ y : ℝ,
            apm_m02j02_hermiteFunction (n + 1) y ^ 2) /
          Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)) *
        ((∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
          Real.sqrt ((n.factorial : ℝ) *
            Real.sqrt (Real.pi / (1 / 2 : ℝ))))) ^ 2)) := by
  have h := apm_m02j02_summable_succ_mul_sq_normalized_coefficients
    φ hφ hφc
  convert h using 1
  funext n
  rw [mul_pow, apm_m02j02_sq_hermite_norm_succ_ratio]

/-- After shifting the upper adjacent contribution to its output-mode index,
and inserting its absent mode-zero coefficient, its squares remain summable. -/
lemma apm_m02j02_summable_sq_normalized_hermiteDeriv_shifted_upper_coefficients
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Summable (fun k : ℕ =>
      (match k with
      | 0 => 0
      | n + 1 =>
          (Real.sqrt (∫ y : ℝ,
              apm_m02j02_hermiteFunction (n + 1) y ^ 2) /
            Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)) *
          ((∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
            Real.sqrt ((n.factorial : ℝ) *
              Real.sqrt (Real.pi / (1 / 2 : ℝ))))) ^ 2) := by
  let u : ℕ → ℝ := fun n =>
    ((Real.sqrt (∫ y : ℝ,
          apm_m02j02_hermiteFunction (n + 1) y ^ 2) /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)) *
      ((∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
        Real.sqrt ((n.factorial : ℝ) *
          Real.sqrt (Real.pi / (1 / 2 : ℝ))))) ^ 2
  have hu : Summable u := by
    simpa only [u] using
      apm_m02j02_summable_sq_normalized_hermiteDeriv_upper_coefficients
        φ hφ hφc
  apply (summable_nat_add_iff 1).1
  simpa [u] using hu

/-- The reindexed coefficients of twice the derivative projection are
square-summable.  The remaining finite-sum argument only has to identify
these coefficients pointwise. -/
lemma apm_m02j02_summable_sq_normalized_hermiteDeriv_output_coefficients
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Summable (fun k : ℕ =>
      (((((k + 1 : ℝ) *
            Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction k y ^ 2) /
            Real.sqrt (∫ y : ℝ,
              apm_m02j02_hermiteFunction (k + 1) y ^ 2)) *
          ((∫ x : ℝ, φ x * apm_m02j02_hermiteFunction (k + 1) x) /
            Real.sqrt (((k + 1).factorial : ℝ) *
              Real.sqrt (Real.pi / (1 / 2 : ℝ))))) -
        (match k with
        | 0 => 0
        | n + 1 =>
            (Real.sqrt (∫ y : ℝ,
                apm_m02j02_hermiteFunction (n + 1) y ^ 2) /
              Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)) *
            ((∫ x : ℝ, φ x * apm_m02j02_hermiteFunction n x) /
              Real.sqrt ((n.factorial : ℝ) *
                Real.sqrt (Real.pi / (1 / 2 : ℝ)))))) ^ 2)) := by
  apply apm_m02j02_summable_sq_sub_of_summable_sq
  · exact apm_m02j02_summable_sq_normalized_hermiteDeriv_lower_coefficients
      φ hφ hφc
  · exact
      apm_m02j02_summable_sq_normalized_hermiteDeriv_shifted_upper_coefficients
        φ hφ hφc

/-- Differentiation of a finite normalized Hermite projection is termwise. -/
lemma apm_m02j02_deriv_sum_range_normalized_hermite
    (a : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => ∑ n ∈ Finset.range N,
      a n * (apm_m02j02_hermiteFunction n y /
        Real.sqrt (∫ z : ℝ, apm_m02j02_hermiteFunction n z ^ 2))) x =
      ∑ n ∈ Finset.range N,
        a n * (apm_m02j02_hermiteFunctionDeriv n x /
          Real.sqrt (∫ z : ℝ, apm_m02j02_hermiteFunction n z ^ 2)) := by
  have h := HasDerivAt.fun_sum (u := Finset.range N)
    (A := fun n => fun y : ℝ =>
      a n * (apm_m02j02_hermiteFunction n y /
        Real.sqrt (∫ z : ℝ, apm_m02j02_hermiteFunction n z ^ 2)))
    (A' := fun n =>
      a n * (apm_m02j02_hermiteFunctionDeriv n x /
        Real.sqrt (∫ z : ℝ, apm_m02j02_hermiteFunction n z ^ 2)))
    (fun n _ => by
      convert (apm_m02j02_hermiteFunction_hasDerivAt n x).const_mul
        (a n / Real.sqrt
          (∫ z : ℝ, apm_m02j02_hermiteFunction n z ^ 2)) using 1 <;>
        field_simp)
  exact h.deriv

/-- Every finite normalized Hermite value projection belongs to `L²`. -/
lemma apm_m02j02_memLp_sum_range_normalized_hermite
    (a : ℕ → ℝ) (N : ℕ) :
    MemLp (fun x : ℝ => ∑ n ∈ Finset.range N,
      a n * (apm_m02j02_hermiteFunction n x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)))
      2 volume := by
  apply memLp_finset_sum
  intro n hn
  convert (apm_m02j02_hermiteFunction_memLp_two n).const_mul
    (a n / Real.sqrt (∫ y : ℝ,
      apm_m02j02_hermiteFunction n y ^ 2)) using 1
  ext x
  simp [div_eq_mul_inv]
  ring

/-- Every finite normalized Hermite derivative projection belongs to `L²`. -/
lemma apm_m02j02_memLp_sum_range_normalized_hermiteDeriv
    (a : ℕ → ℝ) (N : ℕ) :
    MemLp (fun x : ℝ => ∑ n ∈ Finset.range N,
      a n * (apm_m02j02_hermiteFunctionDeriv n x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)))
      2 volume := by
  apply memLp_finset_sum
  intro n hn
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    (apm_m02j02_hermiteFunctionDeriv_memLp_two n).const_mul
      (a n * (Real.sqrt (∫ y : ℝ,
        apm_m02j02_hermiteFunction n y ^ 2))⁻¹)

/-- The concrete normalized Hermite value projection as an element of `Lp`. -/
noncomputable def apm_m02j02_normalizedHermiteCoefficient
    (φ : ℝ → ℝ) (n : ℕ) : ℝ :=
  (∫ y : ℝ, φ y * apm_m02j02_hermiteFunction n y) /
    Real.sqrt ((n.factorial : ℝ) *
      Real.sqrt (Real.pi / (1 / 2 : ℝ)))

lemma apm_m02j02_normalizedHermiteCoefficient_apply
    (φ : ℝ → ℝ) (n : ℕ) :
    apm_m02j02_normalizedHermiteCoefficient φ n =
      (∫ y : ℝ, φ y * apm_m02j02_hermiteFunction n y) /
        Real.sqrt ((n.factorial : ℝ) *
          Real.sqrt (Real.pi / (1 / 2 : ℝ))) := rfl

noncomputable def apm_m02j02_normalizedHermiteProjection
    (a : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    a n * (apm_m02j02_hermiteFunction n x /
      Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))

noncomputable def apm_m02j02_normalizedHermiteDerivProjection
    (a : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    a n * (apm_m02j02_hermiteFunctionDeriv n x /
      Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))

noncomputable def apm_m02j02_normalizedHermiteProjectionLp
    (a : ℕ → ℝ) (N : ℕ) : Lp ℝ 2 (volume : Measure ℝ) :=
  (apm_m02j02_memLp_sum_range_normalized_hermite a N).toLp
    (apm_m02j02_normalizedHermiteProjection a N)

noncomputable def apm_m02j02_normalizedHermiteProjectionSequence
    (φ : ℝ → ℝ) (N : ℕ) : Lp ℝ 2 (volume : Measure ℝ) :=
  apm_m02j02_normalizedHermiteProjectionLp
    (apm_m02j02_normalizedHermiteCoefficient φ) N

/-- Parseval's identity for a finite linear combination of the normalized
Hermite functions. -/
lemma apm_m02j02_integral_sq_finset_normalized_hermite
    (s : Finset ℕ) (a : ℕ → ℝ) :
    (∫ x : ℝ,
      (∑ n ∈ s, a n *
        (apm_m02j02_hermiteFunction n x /
          Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))) ^ 2) =
      ∑ n ∈ s, (a n) ^ 2 := by
  let e : ℕ → ℝ → ℝ := fun n x =>
    apm_m02j02_hermiteFunction n x /
      Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)
  have he (m n : ℕ) : Integrable (fun x : ℝ => e m x * e n x) volume := by
    dsimp [e]
    convert ((apm_m02j02_hermiteFunction_memLp_two m).integrable_mul
      (apm_m02j02_hermiteFunction_memLp_two n)).div_const
        (Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2) *
          Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)) using 1
    ext x
    dsimp
    ring
  rw [show (fun x : ℝ =>
      (∑ n ∈ s, a n * e n x) ^ 2) =
      fun x : ℝ => ∑ m ∈ s, ∑ n ∈ s,
        (a m * a n) * (e m x * e n x) by
    funext x
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    ring]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [MeasureTheory.integral_finset_sum]
    · simp [e, MeasureTheory.integral_const_mul,
        apm_m02j02_hermite_normalized_gram, hm]
      <;> ring
    · intro n hn
      exact (he m n).const_mul _
  · intro m hm
    exact integrable_finset_sum _ fun n hn => (he m n).const_mul _

/-- Pairing a finite normalized Hermite sum with one normalized mode extracts
its coefficient. -/
lemma apm_m02j02_integral_finset_normalized_hermite_mul_mode
    (s : Finset ℕ) (a : ℕ → ℝ) (m : ℕ) :
    (∫ x : ℝ, (∑ n ∈ s, a n *
      (apm_m02j02_hermiteFunction n x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))) *
      (apm_m02j02_hermiteFunction m x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2))) =
      if m ∈ s then a m else 0 := by
  let e : ℕ → ℝ → ℝ := fun n x =>
    apm_m02j02_hermiteFunction n x /
      Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)
  have he (n : ℕ) : Integrable (fun x : ℝ => e n x * e m x) volume := by
    dsimp [e]
    convert ((apm_m02j02_hermiteFunction_memLp_two n).integrable_mul
      (apm_m02j02_hermiteFunction_memLp_two m)).div_const
        (Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2) *
          Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2)) using 1
    ext x
    dsimp
    ring
  rw [show (fun x : ℝ => (∑ n ∈ s, a n * e n x) * e m x) =
      fun x : ℝ => ∑ n ∈ s, a n * (e n x * e m x) by
    funext x
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    ring]
  rw [MeasureTheory.integral_finset_sum]
  · simp [e, MeasureTheory.integral_const_mul,
      apm_m02j02_hermite_normalized_gram]
  · intro n hn
    exact (he n).const_mul _

/-- Every sufficiently late range projection has the prescribed coefficient
against a fixed normalized mode. -/
lemma apm_m02j02_integral_range_normalized_hermite_mul_mode
    (a : ℕ → ℝ) (m N : ℕ) (hmN : m < N) :
    (∫ x : ℝ, (∑ n ∈ Finset.range N, a n *
      (apm_m02j02_hermiteFunction n x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))) *
      (apm_m02j02_hermiteFunction m x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2))) = a m := by
  rw [apm_m02j02_integral_finset_normalized_hermite_mul_mode,
    if_pos (Finset.mem_range.2 hmN)]

lemma apm_m02j02_normalized_hermite_memLp_two (m : ℕ) :
    MemLp (fun x : ℝ =>
      apm_m02j02_hermiteFunction m x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2))
      2 volume := by
  simpa only [div_eq_mul_inv, mul_comm] using
    (apm_m02j02_hermiteFunction_memLp_two m).const_mul
      (Real.sqrt (∫ y : ℝ,
        apm_m02j02_hermiteFunction m y ^ 2))⁻¹

lemma apm_m02j02_real_inner_eq_mul (x y : ℝ) : inner ℝ x y = x * y := by
  calc
    inner ℝ x y = inner ℝ (x • (1 : ℝ)) (y • (1 : ℝ)) := by simp
    _ = x * y * inner ℝ (1 : ℝ) 1 := by
      rw [inner_smul_left, inner_smul_right]
      simp
    _ = x * y := by rw [real_inner_self_eq_norm_sq]; norm_num

/-- The Hilbert-space pairing of a finite normalized Hermite projection with
one normalized mode is the same coefficient extracted by the integral Gram
identity. -/
lemma apm_m02j02_inner_toLp_range_normalized_hermite_mode
    (a : ℕ → ℝ) (m N : ℕ) (hmN : m < N) :
    let f : ℝ → ℝ := fun x => ∑ n ∈ Finset.range N,
      a n * (apm_m02j02_hermiteFunction n x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))
    let e : ℝ → ℝ := fun x =>
      apm_m02j02_hermiteFunction m x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2)
    let hf : MemLp f 2 volume :=
      apm_m02j02_memLp_sum_range_normalized_hermite a N
    let he : MemLp e 2 volume :=
      apm_m02j02_normalized_hermite_memLp_two m
    inner ℝ (hf.toLp f) (he.toLp e) = a m := by
  dsimp only
  rw [L2.inner_def]
  rw [integral_congr_ae]
  · exact apm_m02j02_integral_range_normalized_hermite_mul_mode a m N hmN
  · filter_upwards
      [(apm_m02j02_memLp_sum_range_normalized_hermite a N).coeFn_toLp,
       (apm_m02j02_normalized_hermite_memLp_two m).coeFn_toLp]
      with x hfx hex
    rw [hfx, hex]
    rw [apm_m02j02_real_inner_eq_mul]

/-- The concrete `Lp` projection definition is nontrivial. -/
lemma apm_m02j02_normalizedHermiteProjectionLp_nonzero :
    apm_m02j02_normalizedHermiteProjectionLp (fun _ => 1) 1 ≠ 0 := by
  intro hz
  have hpair :=
    apm_m02j02_inner_toLp_range_normalized_hermite_mode
      (fun _ => (1 : ℝ)) 0 1 (by omega)
  change inner ℝ
    (apm_m02j02_normalizedHermiteProjectionLp (fun _ => 1) 1)
    ((apm_m02j02_normalized_hermite_memLp_two 0).toLp
      (fun x : ℝ => apm_m02j02_hermiteFunction 0 x /
        Real.sqrt (∫ y : ℝ,
          apm_m02j02_hermiteFunction 0 y ^ 2))) = 1 at hpair
  rw [hz, inner_zero_left] at hpair
  norm_num at hpair

lemma apm_m02j02_normalizedHermiteProjection_nonzero :
    apm_m02j02_normalizedHermiteProjection (fun _ => 1) 1 ≠ 0 := by
  intro hz
  have h0 := congrFun hz 0
  simp [apm_m02j02_normalizedHermiteProjection,
    apm_m02j02_hermiteFunction] at h0
  have hp := apm_m02j02_hermite_norm_sq_pos 0
  simp [apm_m02j02_hermiteFunction] at hp
  have hs := Real.sqrt_pos.2 hp
  rw [h0] at hs
  exact (lt_irrefl 0 hs)

lemma apm_m02j02_normalizedHermiteDerivProjection_nonzero :
    apm_m02j02_normalizedHermiteDerivProjection (fun _ => 1) 1 ≠ 0 := by
  intro hz
  have h1 := congrFun hz 1
  simp [apm_m02j02_normalizedHermiteDerivProjection] at h1
  have hs : Real.sqrt
      (∫ y : ℝ, apm_m02j02_hermiteFunction 0 y ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (apm_m02j02_hermite_norm_sq_pos 0))
  have hd : apm_m02j02_hermiteFunctionDeriv 0 1 = 0 := by
    exact h1.resolve_right hs
  have hr := apm_m02j02_two_mul_hermiteFunctionDeriv_zero 1
  rw [hd] at hr
  have hp : 0 < apm_m02j02_hermiteFunction 1 1 := by
    simp [apm_m02j02_hermiteFunction]
    positivity
  linarith

lemma apm_m02j02_normalizedHermiteProjection_memLp
    (a : ℕ → ℝ) (N : ℕ) :
    MemLp (apm_m02j02_normalizedHermiteProjection a N) 2 volume := by
  simpa only [apm_m02j02_normalizedHermiteProjection] using
    apm_m02j02_memLp_sum_range_normalized_hermite a N

lemma apm_m02j02_normalizedHermiteDerivProjection_memLp
    (a : ℕ → ℝ) (N : ℕ) :
    MemLp (apm_m02j02_normalizedHermiteDerivProjection a N) 2 volume := by
  simpa only [apm_m02j02_normalizedHermiteDerivProjection] using
    apm_m02j02_memLp_sum_range_normalized_hermiteDeriv a N

noncomputable def apm_m02j02_normalizedHermiteDerivProjectionLp
    (a : ℕ → ℝ) (N : ℕ) : Lp ℝ 2 (volume : Measure ℝ) :=
  (apm_m02j02_normalizedHermiteDerivProjection_memLp a N).toLp
    (apm_m02j02_normalizedHermiteDerivProjection a N)

noncomputable def apm_m02j02_normalizedHermiteDerivProjectionSequence
    (φ : ℝ → ℝ) (N : ℕ) : Lp ℝ 2 (volume : Measure ℝ) :=
  apm_m02j02_normalizedHermiteDerivProjectionLp
    (apm_m02j02_normalizedHermiteCoefficient φ) N

lemma apm_m02j02_normalizedHermiteDerivProjection_continuous
    (a : ℕ → ℝ) (N : ℕ) :
    Continuous (apm_m02j02_normalizedHermiteDerivProjection a N) := by
  apply continuous_finset_sum
  intro n hn
  exact continuous_const.mul
    ((apm_m02j02_hermiteFunctionDeriv_continuous n).div_const _)

/-- The concrete derivative projection in `Lp` is nontrivial. -/
lemma apm_m02j02_normalizedHermiteDerivProjectionLp_nonzero :
    apm_m02j02_normalizedHermiteDerivProjectionLp (fun _ => 1) 1 ≠ 0 := by
  intro hz
  have hzero : MemLp (0 : ℝ → ℝ) 2 volume := MemLp.zero
  have hz' :
      apm_m02j02_normalizedHermiteDerivProjectionLp (fun _ => 1) 1 =
        hzero.toLp (0 : ℝ → ℝ) := by simpa using hz
  have hae :
      apm_m02j02_normalizedHermiteDerivProjection (fun _ => 1) 1 =ᵐ[volume]
        (0 : ℝ → ℝ) := by
    exact (MemLp.toLp_eq_toLp_iff
      (apm_m02j02_normalizedHermiteDerivProjection_memLp (fun _ => 1) 1)
      hzero).mp hz'
  have heq : apm_m02j02_normalizedHermiteDerivProjection (fun _ => 1) 1 =
      (0 : ℝ → ℝ) :=
    MeasureTheory.Measure.eq_of_ae_eq hae
      (apm_m02j02_normalizedHermiteDerivProjection_continuous (fun _ => 1) 1)
      continuous_zero
  exact apm_m02j02_normalizedHermiteDerivProjection_nonzero heq

lemma apm_m02j02_edist_normalizedHermiteDerivProjectionLp
    (a : ℕ → ℝ) (M N : ℕ) :
    edist (apm_m02j02_normalizedHermiteDerivProjectionLp a N)
        (apm_m02j02_normalizedHermiteDerivProjectionLp a M) =
      eLpNorm (apm_m02j02_normalizedHermiteDerivProjection a N -
        apm_m02j02_normalizedHermiteDerivProjection a M) 2 volume := by
  change
    edist
      ((apm_m02j02_normalizedHermiteDerivProjection_memLp a N).toLp
        (apm_m02j02_normalizedHermiteDerivProjection a N))
      ((apm_m02j02_normalizedHermiteDerivProjection_memLp a M).toLp
        (apm_m02j02_normalizedHermiteDerivProjection a M)) = _
  rw [Lp.edist_toLp_toLp]

/-- The normalized coefficient abbreviation is nontrivial. -/
lemma apm_m02j02_normalizedHermiteCoefficient_nonzero :
    apm_m02j02_normalizedHermiteCoefficient
      (apm_m02j02_hermiteFunction 0) 0 ≠ 0 := by
  rw [apm_m02j02_normalizedHermiteCoefficient]
  apply div_ne_zero
  · rw [show (fun y : ℝ => apm_m02j02_hermiteFunction 0 y *
        apm_m02j02_hermiteFunction 0 y) =
        fun y : ℝ => apm_m02j02_hermiteFunction 0 y ^ 2 by
      funext y
      ring]
    exact ne_of_gt (apm_m02j02_hermite_norm_sq_pos 0)
  · apply ne_of_gt
    apply Real.sqrt_pos.2
    simpa [apm_m02j02_hermite_norm_sq] using
      apm_m02j02_hermite_norm_sq_pos 0

lemma apm_m02j02_normalizedHermiteProjectionSequence_nonzero :
    apm_m02j02_normalizedHermiteProjectionSequence
      (apm_m02j02_hermiteFunction 0) 1 ≠ 0 := by
  intro hz
  have hpair := apm_m02j02_inner_toLp_range_normalized_hermite_mode
    (apm_m02j02_normalizedHermiteCoefficient
      (apm_m02j02_hermiteFunction 0)) 0 1 (by omega)
  change inner ℝ
    (apm_m02j02_normalizedHermiteProjectionSequence
      (apm_m02j02_hermiteFunction 0) 1)
    ((apm_m02j02_normalized_hermite_memLp_two 0).toLp
      (fun x : ℝ => apm_m02j02_hermiteFunction 0 x /
        Real.sqrt (∫ y : ℝ,
          apm_m02j02_hermiteFunction 0 y ^ 2))) =
      apm_m02j02_normalizedHermiteCoefficient
        (apm_m02j02_hermiteFunction 0) 0 at hpair
  rw [hz, inner_zero_left] at hpair
  exact apm_m02j02_normalizedHermiteCoefficient_nonzero hpair.symm

/-- Distance between two concrete `Lp` projections is the real value of the
`eLpNorm` of their representative difference. -/
lemma apm_m02j02_dist_normalizedHermiteProjectionLp
    (a : ℕ → ℝ) (M N : ℕ) :
    dist (apm_m02j02_normalizedHermiteProjectionLp a N)
        (apm_m02j02_normalizedHermiteProjectionLp a M) =
      (eLpNorm (apm_m02j02_normalizedHermiteProjection a N -
        apm_m02j02_normalizedHermiteProjection a M) 2 volume).toReal := by
  rw [Lp.dist_edist]
  change
    (edist
      ((apm_m02j02_memLp_sum_range_normalized_hermite a N).toLp
        (apm_m02j02_normalizedHermiteProjection a N))
      ((apm_m02j02_memLp_sum_range_normalized_hermite a M).toLp
        (apm_m02j02_normalizedHermiteProjection a M))).toReal = _
  rw [Lp.edist_toLp_toLp]

/-- Extended distance between two concrete normalized Hermite projections is
the `eLpNorm` of the difference of their representatives. -/
lemma apm_m02j02_edist_normalizedHermiteProjectionLp
    (a : ℕ → ℝ) (M N : ℕ) :
    edist (apm_m02j02_normalizedHermiteProjectionLp a N)
        (apm_m02j02_normalizedHermiteProjectionLp a M) =
      eLpNorm (apm_m02j02_normalizedHermiteProjection a N -
        apm_m02j02_normalizedHermiteProjection a M) 2 volume := by
  change
    edist
      ((apm_m02j02_memLp_sum_range_normalized_hermite a N).toLp
        (apm_m02j02_normalizedHermiteProjection a N))
      ((apm_m02j02_memLp_sum_range_normalized_hermite a M).toLp
        (apm_m02j02_normalizedHermiteProjection a M)) = _
  rw [Lp.edist_toLp_toLp]

/-- The exact `L²` square of a difference of two nested finite normalized
Hermite sums is the corresponding coefficient-square tail. -/
lemma apm_m02j02_integral_sq_sub_range_normalized_hermite
    (a : ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    (∫ x : ℝ,
      ((∑ n ∈ Finset.range N, a n *
          (apm_m02j02_hermiteFunction n x /
            Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))) -
        (∑ n ∈ Finset.range M, a n *
          (apm_m02j02_hermiteFunction n x /
            Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)))) ^ 2) =
      ∑ n ∈ Finset.Ico M N, (a n) ^ 2 := by
  rw [show (fun x : ℝ =>
      ((∑ n ∈ Finset.range N, a n *
          (apm_m02j02_hermiteFunction n x /
            Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))) -
        (∑ n ∈ Finset.range M, a n *
          (apm_m02j02_hermiteFunction n x /
            Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)))) ^ 2) =
      fun x : ℝ =>
        (∑ n ∈ Finset.Ico M N, a n *
          (apm_m02j02_hermiteFunction n x /
            Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))) ^ 2 by
    funext x
    rw [Finset.sum_Ico_eq_sub _ hMN]]
  exact apm_m02j02_integral_sq_finset_normalized_hermite
    (Finset.Ico M N) a

/-- For a real-valued `L²` function, the extended `L²` seminorm is the
`ENNReal` lift of the square root of its square integral. -/
lemma apm_m02j02_eLpNorm_two_eq_ofReal_sqrt_integral_sq
    {μ : Measure ℝ} (f : ℝ → ℝ) (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ x : ℝ, f x ^ 2 ∂μ)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  norm_num
  congr 1
  rw [Real.sqrt_eq_rpow]

/-- Every normalized Hermite mode has extended `L²` norm one. -/
lemma apm_m02j02_eLpNorm_normalized_hermite (n : ℕ) :
    eLpNorm (fun x : ℝ => apm_m02j02_hermiteFunction n x /
      Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))
      2 volume = 1 := by
  have hn : Real.sqrt (∫ y : ℝ,
      apm_m02j02_hermiteFunction n y ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (apm_m02j02_hermite_norm_sq_pos n))
  have hm : MemLp (fun x : ℝ => apm_m02j02_hermiteFunction n x /
      Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))
      2 volume := by
    convert (apm_m02j02_hermiteFunction_memLp_two n).const_mul
      (Real.sqrt (∫ y : ℝ,
        apm_m02j02_hermiteFunction n y ^ 2))⁻¹ using 1
    ext x
    simp only [div_eq_mul_inv, Pi.smul_apply, smul_eq_mul]
    ring
  rw [apm_m02j02_eLpNorm_two_eq_ofReal_sqrt_integral_sq _ hm]
  have hg := apm_m02j02_hermite_normalized_gram n n
  simp only [if_pos rfl] at hg
  have hi : (∫ x : ℝ,
      (apm_m02j02_hermiteFunction n x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)) ^ 2) = 1 := by
    simpa [pow_two] using hg
  rw [hi]
  norm_num

/-- The `L²` norm of a scalar multiple of a normalized Hermite mode is the
absolute value of the scalar. -/
lemma apm_m02j02_eLpNorm_mul_normalized_hermite (c : ℝ) (n : ℕ) :
    eLpNorm (fun x : ℝ => c *
      (apm_m02j02_hermiteFunction n x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)))
      2 volume = ENNReal.ofReal |c| := by
  rw [show (fun x : ℝ => c *
      (apm_m02j02_hermiteFunction n x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))) =
      c • (fun x : ℝ => apm_m02j02_hermiteFunction n x /
        Real.sqrt (∫ y : ℝ,
          apm_m02j02_hermiteFunction n y ^ 2)) by rfl,
    eLpNorm_const_smul, apm_m02j02_eLpNorm_normalized_hermite]
  rw [mul_one, ← ofReal_norm_eq_enorm]
  simp

/-- Triangle bound for a two-mode normalized Hermite combination. -/
lemma apm_m02j02_eLpNorm_sub_mul_normalized_hermite_le
    (c d : ℝ) (m n : ℕ) :
    eLpNorm (fun x : ℝ =>
      c * (apm_m02j02_hermiteFunction m x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2)) -
      d * (apm_m02j02_hermiteFunction n x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)))
      2 volume ≤ ENNReal.ofReal |c| + ENNReal.ofReal |d| := by
  let f : ℝ → ℝ := fun x =>
    c * (apm_m02j02_hermiteFunction m x /
      Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2))
  let g : ℝ → ℝ := fun x =>
    d * (apm_m02j02_hermiteFunction n x /
      Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))
  have hf : AEStronglyMeasurable f volume := by
    apply Continuous.aestronglyMeasurable
    simpa [f, div_eq_mul_inv, mul_assoc] using
      ((apm_m02j02_hermiteFunction_contDiff m).continuous.const_mul c |>.div_const
        (Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2)))
  have hg : AEStronglyMeasurable g volume := by
    apply Continuous.aestronglyMeasurable
    simpa [g, div_eq_mul_inv, mul_assoc] using
      ((apm_m02j02_hermiteFunction_contDiff n).continuous.const_mul d |>.div_const
        (Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)))
  change eLpNorm (f - g) 2 volume ≤ _
  calc
    eLpNorm (f - g) 2 volume ≤ eLpNorm f 2 volume + eLpNorm g 2 volume := by
      simpa only [sub_eq_add_neg, eLpNorm_neg] using
        eLpNorm_add_le hf hg.neg (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ = _ := by
      rw [show eLpNorm f 2 volume = ENNReal.ofReal |c| by
        exact apm_m02j02_eLpNorm_mul_normalized_hermite c m,
        show eLpNorm g 2 volume = ENNReal.ofReal |d| by
          exact apm_m02j02_eLpNorm_mul_normalized_hermite d n]

/-- The positive-index normalized derivative recurrence as an `L²` norm
bound, retaining its exact two normalization ratios. -/
lemma apm_m02j02_eLpNorm_two_mul_normalized_hermiteDeriv_succ_le (n : ℕ) :
    eLpNorm (fun x : ℝ => 2 *
      (apm_m02j02_hermiteFunctionDeriv (n + 1) x /
        Real.sqrt (∫ y : ℝ,
          apm_m02j02_hermiteFunction (n + 1) y ^ 2))) 2 volume ≤
      ENNReal.ofReal |(n + 1 : ℝ) *
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2) /
        Real.sqrt (∫ y : ℝ,
          apm_m02j02_hermiteFunction (n + 1) y ^ 2)| +
      ENNReal.ofReal |Real.sqrt (∫ y : ℝ,
          apm_m02j02_hermiteFunction (n + 2) y ^ 2) /
        Real.sqrt (∫ y : ℝ,
          apm_m02j02_hermiteFunction (n + 1) y ^ 2)| := by
  rw [show (fun x : ℝ => 2 *
      (apm_m02j02_hermiteFunctionDeriv (n + 1) x /
        Real.sqrt (∫ y : ℝ,
          apm_m02j02_hermiteFunction (n + 1) y ^ 2))) =
      fun x : ℝ =>
        ((n + 1 : ℝ) *
          Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2) /
          Real.sqrt (∫ y : ℝ,
            apm_m02j02_hermiteFunction (n + 1) y ^ 2)) *
            (apm_m02j02_hermiteFunction n x /
              Real.sqrt (∫ y : ℝ,
                apm_m02j02_hermiteFunction n y ^ 2)) -
        (Real.sqrt (∫ y : ℝ,
            apm_m02j02_hermiteFunction (n + 2) y ^ 2) /
          Real.sqrt (∫ y : ℝ,
            apm_m02j02_hermiteFunction (n + 1) y ^ 2)) *
            (apm_m02j02_hermiteFunction (n + 2) x /
              Real.sqrt (∫ y : ℝ,
                apm_m02j02_hermiteFunction (n + 2) y ^ 2)) by
    funext x
    exact apm_m02j02_two_mul_normalized_hermiteDeriv_succ n x]
  exact apm_m02j02_eLpNorm_sub_mul_normalized_hermite_le _ _ n (n + 2)

/-- Coarse linear bound for the lower normalization ratio. -/
lemma apm_m02j02_abs_normalized_hermiteDeriv_lower_ratio_le (n : ℕ) :
    |(n + 1 : ℝ) *
      Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2) /
      Real.sqrt (∫ y : ℝ,
        apm_m02j02_hermiteFunction (n + 1) y ^ 2)| ≤ n + 1 := by
  let r : ℝ := (n + 1 : ℝ) *
    Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2) /
    Real.sqrt (∫ y : ℝ,
      apm_m02j02_hermiteFunction (n + 1) y ^ 2)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hrsq : r ^ 2 = n + 1 := by
    simpa [r] using apm_m02j02_sq_normalized_hermiteDeriv_lower_ratio n
  rw [abs_of_nonneg hr0]
  have hn : (1 : ℝ) ≤ n + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  nlinarith [sq_nonneg (r - 1)]

/-- Coarse linear bound for the upper normalization ratio. -/
lemma apm_m02j02_abs_normalized_hermiteDeriv_upper_ratio_le (n : ℕ) :
    |Real.sqrt (∫ y : ℝ,
        apm_m02j02_hermiteFunction (n + 2) y ^ 2) /
      Real.sqrt (∫ y : ℝ,
        apm_m02j02_hermiteFunction (n + 1) y ^ 2)| ≤ n + 2 := by
  let r : ℝ := Real.sqrt (∫ y : ℝ,
      apm_m02j02_hermiteFunction (n + 2) y ^ 2) /
    Real.sqrt (∫ y : ℝ,
      apm_m02j02_hermiteFunction (n + 1) y ^ 2)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hrsq : r ^ 2 = n + 2 := by
    simpa [r] using apm_m02j02_sq_normalized_hermiteDeriv_upper_ratio n
  rw [abs_of_nonneg hr0]
  have hn : (1 : ℝ) ≤ n + 2 := by
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  nlinarith [sq_nonneg (r - 1)]

/-- A linear `L²` bound for twice every positive-index normalized Hermite
derivative. -/
lemma apm_m02j02_eLpNorm_two_mul_normalized_hermiteDeriv_succ_linear_le
    (n : ℕ) :
    eLpNorm (fun x : ℝ => 2 *
      (apm_m02j02_hermiteFunctionDeriv (n + 1) x /
        Real.sqrt (∫ y : ℝ,
          apm_m02j02_hermiteFunction (n + 1) y ^ 2))) 2 volume ≤
      ENNReal.ofReal (2 * (n : ℝ) + 3) := by
  calc
    _ ≤ ENNReal.ofReal |(n + 1 : ℝ) *
          Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2) /
          Real.sqrt (∫ y : ℝ,
            apm_m02j02_hermiteFunction (n + 1) y ^ 2)| +
        ENNReal.ofReal |Real.sqrt (∫ y : ℝ,
            apm_m02j02_hermiteFunction (n + 2) y ^ 2) /
          Real.sqrt (∫ y : ℝ,
            apm_m02j02_hermiteFunction (n + 1) y ^ 2)| :=
      apm_m02j02_eLpNorm_two_mul_normalized_hermiteDeriv_succ_le n
    _ ≤ ENNReal.ofReal (n + 1 : ℝ) + ENNReal.ofReal (n + 2 : ℝ) := by
      gcongr
      · exact apm_m02j02_abs_normalized_hermiteDeriv_lower_ratio_le n
      · exact apm_m02j02_abs_normalized_hermiteDeriv_upper_ratio_le n
    _ = ENNReal.ofReal (2 * (n : ℝ) + 3) := by
      rw [← ENNReal.ofReal_add (by
          have : (0 : ℝ) ≤ n := by positivity
          linarith : 0 ≤ (n + 1 : ℝ)) (by
          have : (0 : ℝ) ≤ n := by positivity
          linarith : 0 ≤ (n + 2 : ℝ))]
      congr 1
      ring

/-- Boundary-mode counterpart of the linear normalized derivative bound. -/
lemma apm_m02j02_eLpNorm_two_mul_normalized_hermiteDeriv_zero_le :
    eLpNorm (fun x : ℝ => 2 *
      (apm_m02j02_hermiteFunctionDeriv 0 x /
        Real.sqrt (∫ y : ℝ,
          apm_m02j02_hermiteFunction 0 y ^ 2))) 2 volume ≤ 1 := by
  let r : ℝ := Real.sqrt (∫ y : ℝ,
      apm_m02j02_hermiteFunction 1 y ^ 2) /
    Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction 0 y ^ 2)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hrsq : r ^ 2 = 1 := by
    simpa [r] using apm_m02j02_sq_hermite_norm_succ_ratio 0
  have hr : r = 1 := by nlinarith
  rw [show (fun x : ℝ => 2 *
      (apm_m02j02_hermiteFunctionDeriv 0 x /
        Real.sqrt (∫ y : ℝ,
          apm_m02j02_hermiteFunction 0 y ^ 2))) =
      fun x : ℝ => (-r) *
        (apm_m02j02_hermiteFunction 1 x /
          Real.sqrt (∫ y : ℝ,
            apm_m02j02_hermiteFunction 1 y ^ 2)) by
    funext x
    rw [apm_m02j02_two_mul_normalized_hermiteDeriv_zero]]
  rw [apm_m02j02_eLpNorm_mul_normalized_hermite, hr]
  norm_num

/-- Uniform linear bound for twice every normalized Hermite derivative. -/
lemma apm_m02j02_eLpNorm_two_mul_normalized_hermiteDeriv_linear_le (n : ℕ) :
    eLpNorm (fun x : ℝ => 2 *
      (apm_m02j02_hermiteFunctionDeriv n x /
        Real.sqrt (∫ y : ℝ,
          apm_m02j02_hermiteFunction n y ^ 2))) 2 volume ≤
      ENNReal.ofReal (2 * (n : ℝ) + 1) := by
  cases n with
  | zero =>
      simpa using apm_m02j02_eLpNorm_two_mul_normalized_hermiteDeriv_zero_le
  | succ n =>
      convert
        apm_m02j02_eLpNorm_two_mul_normalized_hermiteDeriv_succ_linear_le n
        using 1 <;> push_cast <;> ring

/-- Finite-tail estimate used for derivative projections. -/
lemma apm_m02j02_eLpNorm_two_mul_finset_sum_le
    (a : ℕ → ℝ) (d : ℕ → ℝ → ℝ) (s : Finset ℕ)
    (hd : ∀ n, AEStronglyMeasurable (d n) volume)
    (hmode : ∀ n,
      eLpNorm (fun x : ℝ => 2 * d n x) 2 volume ≤
        ENNReal.ofReal (2 * (n : ℝ) + 1)) :
    eLpNorm (fun x : ℝ => 2 * ∑ n ∈ s, a n * d n x) 2 volume ≤
      ∑ n ∈ s, ENNReal.ofReal (|a n| * (2 * (n : ℝ) + 1)) := by
  rw [show (fun x : ℝ => 2 * ∑ n ∈ s, a n * d n x) =
      ∑ n ∈ s, fun x : ℝ => a n * (2 * d n x) by
    funext x
    simp only [Finset.mul_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro n hn
    ring]
  calc
    eLpNorm (∑ n ∈ s, fun x : ℝ => a n * (2 * d n x)) 2 volume ≤
        ∑ n ∈ s, eLpNorm (fun x : ℝ => a n * (2 * d n x)) 2 volume := by
      apply eLpNorm_sum_le
      · intro n hn
        convert (hd n).const_smul (2 * a n) using 1
        ext x
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      · norm_num
    _ ≤ ∑ n ∈ s, ENNReal.ofReal (|a n| * (2 * (n : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [show (fun x : ℝ => a n * (2 * d n x)) =
          a n • (fun x : ℝ => 2 * d n x) by rfl,
        eLpNorm_const_smul]
      calc
        ‖a n‖ₑ * eLpNorm (fun x : ℝ => 2 * d n x) 2 volume ≤
            ‖a n‖ₑ * ENNReal.ofReal (2 * (n : ℝ) + 1) :=
          mul_le_mul_left' (hmode n) _
        _ = ENNReal.ofReal (|a n| * (2 * (n : ℝ) + 1)) := by
          rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul]
          · simp
          · positivity

/-- `eLpNorm` form of the exact normalized Hermite projection-tail identity. -/
lemma apm_m02j02_eLpNorm_sub_range_normalized_hermite
    (a : ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    eLpNorm (fun x : ℝ =>
      (∑ n ∈ Finset.range N, a n *
          (apm_m02j02_hermiteFunction n x /
            Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))) -
        (∑ n ∈ Finset.range M, a n *
          (apm_m02j02_hermiteFunction n x /
            Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))))
      2 volume =
        ENNReal.ofReal (Real.sqrt (∑ n ∈ Finset.Ico M N, (a n) ^ 2)) := by
  have hsum (K : ℕ) : MemLp (fun x : ℝ =>
      ∑ n ∈ Finset.range K, a n *
        (apm_m02j02_hermiteFunction n x /
          Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))) 2 volume := by
    apply memLp_finset_sum
    intro n hn
    convert (apm_m02j02_hermiteFunction_memLp_two n).const_mul
      (a n / Real.sqrt (∫ y : ℝ,
        apm_m02j02_hermiteFunction n y ^ 2)) using 1
    ext x
    simp [div_eq_mul_inv]
    ring
  have htail : MemLp (fun x : ℝ =>
      (∑ n ∈ Finset.range N, a n *
          (apm_m02j02_hermiteFunction n x /
            Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))) -
        (∑ n ∈ Finset.range M, a n *
          (apm_m02j02_hermiteFunction n x /
            Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))))
      2 volume := by
    simpa only [Pi.sub_apply] using (hsum N).sub (hsum M)
  rw [apm_m02j02_eLpNorm_two_eq_ofReal_sqrt_integral_sq _ htail,
    apm_m02j02_integral_sq_sub_range_normalized_hermite a hMN]

/-- Every square-summable coefficient sequence gives an `eLpNorm`-Cauchy
sequence of finite normalized Hermite sums. -/
lemma apm_m02j02_normalized_hermite_sums_eLpNorm_cauchy_of_summable_sq
    (a : ℕ → ℝ) (ha : Summable (fun n => (a n) ^ 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ M N : ℕ, K ≤ M → M ≤ N →
      eLpNorm (fun x : ℝ =>
        (∑ n ∈ Finset.range N, a n *
          (apm_m02j02_hermiteFunction n x /
            Real.sqrt (∫ y : ℝ,
              apm_m02j02_hermiteFunction n y ^ 2))) -
        (∑ n ∈ Finset.range M, a n *
          (apm_m02j02_hermiteFunction n x /
            Real.sqrt (∫ y : ℝ,
              apm_m02j02_hermiteFunction n y ^ 2))))
        2 volume < ENNReal.ofReal ε := by
  have hc : CauchySeq (fun N : ℕ => ∑ n ∈ Finset.range N, (a n) ^ 2) :=
    ha.hasSum.tendsto_sum_nat.cauchySeq
  obtain ⟨K, hK⟩ := (Metric.cauchySeq_iff.1 hc)
    (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨K, fun M N hKM hMN => ?_⟩
  have hd : dist (∑ n ∈ Finset.range M, (a n) ^ 2)
      (∑ n ∈ Finset.range N, (a n) ^ 2) < ε ^ 2 :=
    hK M hKM N (hKM.trans hMN)
  rw [Real.dist_eq, abs_lt] at hd
  have htail : ∑ n ∈ Finset.Ico M N, (a n) ^ 2 < ε ^ 2 := by
    rw [Finset.sum_Ico_eq_sub _ hMN]
    linarith [hd.1]
  have htail_nonneg : 0 ≤ ∑ n ∈ Finset.Ico M N, (a n) ^ 2 := by
    positivity
  have hsqrt : Real.sqrt (∑ n ∈ Finset.Ico M N, (a n) ^ 2) < ε := by
    nlinarith [Real.sq_sqrt htail_nonneg, Real.sqrt_nonneg
      (∑ n ∈ Finset.Ico M N, (a n) ^ 2)]
  rw [apm_m02j02_eLpNorm_sub_range_normalized_hermite a hMN]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hsqrt

/-- Exact homogeneity for the factor two used in the normalized derivative
recurrence. -/
lemma apm_m02j02_eLpNorm_two_mul (f : ℝ → ℝ) (μ : Measure ℝ) :
    eLpNorm (fun x => 2 * f x) 2 μ = 2 * eLpNorm f 2 μ := by
  rw [show (fun x => 2 * f x) = (2 : ℝ) • f by rfl,
    eLpNorm_const_smul]
  congr 1
  rw [← ofReal_norm_eq_enorm]
  norm_num

/-- Late nested normalized Hermite projections of a test function are
arbitrarily close in the extended `L²` seminorm. -/
lemma apm_m02j02_normalized_hermite_projections_eLpNorm_cauchy
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ M N : ℕ, K ≤ M → M ≤ N →
      eLpNorm (fun x : ℝ =>
        (∑ n ∈ Finset.range N,
          ((∫ y : ℝ, φ y * apm_m02j02_hermiteFunction n y) /
            Real.sqrt ((n.factorial : ℝ) *
              Real.sqrt (Real.pi / (1 / 2 : ℝ)))) *
            (apm_m02j02_hermiteFunction n x /
              Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))) -
        (∑ n ∈ Finset.range M,
          ((∫ y : ℝ, φ y * apm_m02j02_hermiteFunction n y) /
            Real.sqrt ((n.factorial : ℝ) *
              Real.sqrt (Real.pi / (1 / 2 : ℝ)))) *
            (apm_m02j02_hermiteFunction n x /
              Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))))
        2 volume < ENNReal.ofReal ε := by
  let a : ℕ → ℝ := fun n =>
    (∫ y : ℝ, φ y * apm_m02j02_hermiteFunction n y) /
      Real.sqrt ((n.factorial : ℝ) *
        Real.sqrt (Real.pi / (1 / 2 : ℝ)))
  have hc := apm_m02j02_cauchySeq_sum_range_sq_normalized_hermite_coefficients
    φ hφ hφc
  obtain ⟨K, hK⟩ := (Metric.cauchySeq_iff.1 hc) (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨K, fun M N hKM hMN => ?_⟩
  have hd : dist (∑ n ∈ Finset.range M, (a n) ^ 2)
      (∑ n ∈ Finset.range N, (a n) ^ 2) < ε ^ 2 := by
    simpa [a] using hK M hKM N (hKM.trans hMN)
  rw [Real.dist_eq, abs_lt] at hd
  have htail : ∑ n ∈ Finset.Ico M N, (a n) ^ 2 < ε ^ 2 := by
    rw [Finset.sum_Ico_eq_sub _ hMN]
    linarith [hd.1]
  have htail_nonneg : 0 ≤ ∑ n ∈ Finset.Ico M N, (a n) ^ 2 := by positivity
  have hsqrt : Real.sqrt (∑ n ∈ Finset.Ico M N, (a n) ^ 2) < ε := by
    nlinarith [Real.sq_sqrt htail_nonneg, Real.sqrt_nonneg
      (∑ n ∈ Finset.Ico M N, (a n) ^ 2)]
  change eLpNorm (fun x : ℝ =>
      (∑ n ∈ Finset.range N, a n *
        (apm_m02j02_hermiteFunction n x /
          Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))) -
      (∑ n ∈ Finset.range M, a n *
        (apm_m02j02_hermiteFunction n x /
          Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2))))
      2 volume < ENNReal.ofReal ε
  rw [apm_m02j02_eLpNorm_sub_range_normalized_hermite a hMN]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hsqrt

/-- Late normalized Hermite derivative projections are Cauchy in the
extended `L²` seminorm. -/
lemma apm_m02j02_normalized_hermite_deriv_projections_eLpNorm_cauchy
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ M N : ℕ, K ≤ M → M ≤ N →
      eLpNorm (fun x : ℝ =>
        (∑ n ∈ Finset.range N,
          ((∫ y : ℝ, φ y * apm_m02j02_hermiteFunction n y) /
            Real.sqrt ((n.factorial : ℝ) *
              Real.sqrt (Real.pi / (1 / 2 : ℝ)))) *
            (apm_m02j02_hermiteFunctionDeriv n x /
              Real.sqrt (∫ y : ℝ,
                apm_m02j02_hermiteFunction n y ^ 2))) -
        (∑ n ∈ Finset.range M,
          ((∫ y : ℝ, φ y * apm_m02j02_hermiteFunction n y) /
            Real.sqrt ((n.factorial : ℝ) *
              Real.sqrt (Real.pi / (1 / 2 : ℝ)))) *
            (apm_m02j02_hermiteFunctionDeriv n x /
              Real.sqrt (∫ y : ℝ,
                apm_m02j02_hermiteFunction n y ^ 2))))
        2 volume < ENNReal.ofReal ε := by
  let a : ℕ → ℝ := fun n =>
    (∫ y : ℝ, φ y * apm_m02j02_hermiteFunction n y) /
      Real.sqrt ((n.factorial : ℝ) *
        Real.sqrt (Real.pi / (1 / 2 : ℝ)))
  let b : ℕ → ℝ := fun n => (2 * (n : ℝ) + 1) * |a n|
  have hb : Summable b := by
    simpa only [a, b] using
      apm_m02j02_summable_two_mul_add_one_mul_abs_normalized_coefficients
        φ hφ hφc
  have hc : CauchySeq (fun N : ℕ => ∑ n ∈ Finset.range N, b n) :=
    hb.hasSum.tendsto_sum_nat.cauchySeq
  obtain ⟨K, hK⟩ := (Metric.cauchySeq_iff.1 hc) ε hε
  refine ⟨K, fun M N hKM hMN => ?_⟩
  have hd : dist (∑ n ∈ Finset.range M, b n)
      (∑ n ∈ Finset.range N, b n) < ε :=
    hK M hKM N (hKM.trans hMN)
  rw [Real.dist_eq, abs_lt] at hd
  have htail : ∑ n ∈ Finset.Ico M N, b n < ε := by
    rw [Finset.sum_Ico_eq_sub _ hMN]
    linarith [hd.1]
  let d : ℕ → ℝ → ℝ := fun n x =>
    apm_m02j02_hermiteFunctionDeriv n x /
      Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)
  have hdmeas : ∀ n, AEStronglyMeasurable (d n) volume := by
    intro n
    convert (apm_m02j02_hermiteFunctionDeriv_memLp_two n).aestronglyMeasurable.const_mul
      (Real.sqrt (∫ y : ℝ,
        apm_m02j02_hermiteFunction n y ^ 2))⁻¹ using 1
    ext x
    simp [d, div_eq_mul_inv, mul_comm]
  have hmaj := apm_m02j02_eLpNorm_two_mul_finset_sum_le
    a d (Finset.Ico M N) hdmeas
    (fun n => by simpa [d] using
      apm_m02j02_eLpNorm_two_mul_normalized_hermiteDeriv_linear_le n)
  have hmaj' : eLpNorm (fun x : ℝ =>
      2 * ∑ n ∈ Finset.Ico M N, a n * d n x) 2 volume ≤
      ENNReal.ofReal (∑ n ∈ Finset.Ico M N, b n) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun n hn => by
      dsimp [b]
      positivity)]
    simpa [b, mul_comm] using hmaj
  have h2lt : eLpNorm (fun x : ℝ =>
      2 * ∑ n ∈ Finset.Ico M N, a n * d n x) 2 volume <
      ENNReal.ofReal ε :=
    hmaj'.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).2 htail)
  rw [apm_m02j02_eLpNorm_two_mul] at h2lt
  change eLpNorm (fun x : ℝ =>
      (∑ n ∈ Finset.range N, a n * d n x) -
      (∑ n ∈ Finset.range M, a n * d n x)) 2 volume < ENNReal.ofReal ε
  rw [show (fun x : ℝ =>
      (∑ n ∈ Finset.range N, a n * d n x) -
      (∑ n ∈ Finset.range M, a n * d n x)) =
      fun x : ℝ => ∑ n ∈ Finset.Ico M N, a n * d n x by
    funext x
    rw [Finset.sum_Ico_eq_sub _ hMN]]
  have hle : eLpNorm (fun x : ℝ =>
      ∑ n ∈ Finset.Ico M N, a n * d n x) 2 volume ≤
      2 * eLpNorm (fun x : ℝ =>
        ∑ n ∈ Finset.Ico M N, a n * d n x) 2 volume := by
    have h := mul_le_mul_right'
      (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
      (eLpNorm (fun x : ℝ =>
        ∑ n ∈ Finset.Ico M N, a n * d n x) 2 volume)
    simpa using h
  exact hle.trans_lt h2lt

lemma apm_m02j02_normalizedHermiteDerivProjection_eLpNorm_cauchy
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ M N : ℕ, K ≤ M → M ≤ N →
      eLpNorm
        (apm_m02j02_normalizedHermiteDerivProjection
            (apm_m02j02_normalizedHermiteCoefficient φ) N -
          apm_m02j02_normalizedHermiteDerivProjection
            (apm_m02j02_normalizedHermiteCoefficient φ) M)
        2 volume < ENNReal.ofReal ε := by
  simpa only [apm_m02j02_normalizedHermiteCoefficient_apply,
    apm_m02j02_normalizedHermiteDerivProjection] using
      apm_m02j02_normalized_hermite_deriv_projections_eLpNorm_cauchy
        φ hφ hφc hε

lemma apm_m02j02_normalizedHermiteDerivProjectionSequence_edist_tail
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
      edist (apm_m02j02_normalizedHermiteDerivProjectionSequence φ N)
        (apm_m02j02_normalizedHermiteDerivProjectionSequence φ K) < ε := by
  by_cases htop : ε = ⊤
  · refine ⟨0, fun N hN => ?_⟩
    rw [htop]
    exact lt_top_iff_ne_top.mpr (edist_ne_top _ _)
  · have hto : 0 < ε.toReal :=
      ENNReal.toReal_pos (ne_of_gt hε) htop
    have hhalf : 0 < ε.toReal / 2 := by positivity
    obtain ⟨K, hK⟩ :=
      apm_m02j02_normalizedHermiteDerivProjection_eLpNorm_cauchy
        φ hφ hφc hhalf
    refine ⟨K, fun N hKN => ?_⟩
    change edist
      (apm_m02j02_normalizedHermiteDerivProjectionLp
        (apm_m02j02_normalizedHermiteCoefficient φ) N)
      (apm_m02j02_normalizedHermiteDerivProjectionLp
        (apm_m02j02_normalizedHermiteCoefficient φ) K) < ε
    rw [apm_m02j02_edist_normalizedHermiteDerivProjectionLp]
    refine (hK K N (le_refl K) hKN).trans ?_
    rw [ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hhalf) htop]
    linarith

lemma apm_m02j02_normalizedHermiteDerivProjectionSequence_cauchy
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    CauchySeq (apm_m02j02_normalizedHermiteDerivProjectionSequence φ) := by
  apply EMetric.cauchySeq_iff'.2
  intro ε hε
  exact apm_m02j02_normalizedHermiteDerivProjectionSequence_edist_tail
    φ hφ hφc hε

lemma apm_m02j02_exists_normalizedHermiteDerivProjectionSequence_limit
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∃ v : Lp ℝ 2 (volume : Measure ℝ),
      Tendsto (apm_m02j02_normalizedHermiteDerivProjectionSequence φ)
        atTop (nhds v) := by
  exact cauchySeq_tendsto_of_complete
    (apm_m02j02_normalizedHermiteDerivProjectionSequence_cauchy φ hφ hφc)

/-- Compact restatement of the normalized value-projection tail estimate. -/
lemma apm_m02j02_normalizedHermiteProjection_eLpNorm_cauchy
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ M N : ℕ, K ≤ M → M ≤ N →
      eLpNorm
        (apm_m02j02_normalizedHermiteProjection
            (apm_m02j02_normalizedHermiteCoefficient φ) N -
          apm_m02j02_normalizedHermiteProjection
            (apm_m02j02_normalizedHermiteCoefficient φ) M)
        2 volume < ENNReal.ofReal ε := by
  simpa only [apm_m02j02_normalizedHermiteCoefficient_apply,
    apm_m02j02_normalizedHermiteProjection] using
      apm_m02j02_normalized_hermite_projections_eLpNorm_cauchy
        φ hφ hφc hε

/-- The value projection sequence satisfies the extended-metric tail
criterion, stated without passing through real-valued distance. -/
lemma apm_m02j02_normalizedHermiteProjectionSequence_edist_tail
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
      edist (apm_m02j02_normalizedHermiteProjectionSequence φ N)
        (apm_m02j02_normalizedHermiteProjectionSequence φ K) < ε := by
  by_cases htop : ε = ⊤
  · obtain ⟨K, hK⟩ :=
      apm_m02j02_normalizedHermiteProjection_eLpNorm_cauchy
        φ hφ hφc (show (0 : ℝ) < 1 by norm_num)
    refine ⟨K, fun N hKN => ?_⟩
    rw [htop]
    exact lt_top_iff_ne_top.mpr (edist_ne_top _ _)
  · have hto : 0 < ε.toReal :=
      ENNReal.toReal_pos (ne_of_gt hε) htop
    have hhalf : 0 < ε.toReal / 2 := by positivity
    obtain ⟨K, hK⟩ :=
      apm_m02j02_normalizedHermiteProjection_eLpNorm_cauchy
        φ hφ hφc hhalf
    refine ⟨K, fun N hKN => ?_⟩
    change edist
      (apm_m02j02_normalizedHermiteProjectionLp
        (apm_m02j02_normalizedHermiteCoefficient φ) N)
      (apm_m02j02_normalizedHermiteProjectionLp
        (apm_m02j02_normalizedHermiteCoefficient φ) K) < ε
    rw [apm_m02j02_edist_normalizedHermiteProjectionLp]
    refine (hK K N (le_refl K) hKN).trans ?_
    rw [ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hhalf) htop]
    linarith

lemma apm_m02j02_normalizedHermiteProjectionSequence_cauchy
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    CauchySeq (apm_m02j02_normalizedHermiteProjectionSequence φ) := by
  apply EMetric.cauchySeq_iff'.2
  intro ε hε
  exact apm_m02j02_normalizedHermiteProjectionSequence_edist_tail
    φ hφ hφc hε

lemma apm_m02j02_exists_normalizedHermiteProjectionSequence_limit
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∃ u : Lp ℝ 2 (volume : Measure ℝ),
      Tendsto (apm_m02j02_normalizedHermiteProjectionSequence φ)
        atTop (nhds u) := by
  exact cauchySeq_tendsto_of_complete
    (apm_m02j02_normalizedHermiteProjectionSequence_cauchy φ hφ hφc)

lemma apm_m02j02_inner_testFunction_normalizedHermite_mode
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (m : ℕ) :
    let e : ℝ → ℝ := fun x =>
      apm_m02j02_hermiteFunction m x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2)
    let hφLp : MemLp φ 2 volume :=
      apm_m02j02_memLp_two_of_contDiff_compact φ hφ hφc
    let he : MemLp e 2 volume := apm_m02j02_normalized_hermite_memLp_two m
    inner ℝ (hφLp.toLp φ) (he.toLp e) =
      apm_m02j02_normalizedHermiteCoefficient φ m := by
  dsimp only
  rw [L2.inner_def]
  rw [integral_congr_ae]
  · change (∫ x : ℝ, φ x *
        (apm_m02j02_hermiteFunction m x /
          Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2))) = _
    rw [show (fun x : ℝ => φ x *
        (apm_m02j02_hermiteFunction m x /
          Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2))) =
        fun x : ℝ => (φ x * apm_m02j02_hermiteFunction m x) /
          Real.sqrt (∫ y : ℝ,
            apm_m02j02_hermiteFunction m y ^ 2) by
      funext x
      ring]
    rw [MeasureTheory.integral_div, apm_m02j02_hermite_norm_sq]
    rfl
  · filter_upwards
      [(apm_m02j02_memLp_two_of_contDiff_compact φ hφ hφc).coeFn_toLp,
       (apm_m02j02_normalized_hermite_memLp_two m).coeFn_toLp]
      with x hφx hex
    rw [hφx, hex, apm_m02j02_real_inner_eq_mul]

/-- Every fixed normalized Hermite coefficient passes to the `Lp` limit of
the finite value projections. -/
lemma apm_m02j02_inner_normalizedHermiteProjectionSequence_limit
    (φ : ℝ → ℝ) (u : Lp ℝ 2 (volume : Measure ℝ))
    (hu : Tendsto (apm_m02j02_normalizedHermiteProjectionSequence φ)
      atTop (nhds u)) (m : ℕ) :
    let e : ℝ → ℝ := fun x =>
      apm_m02j02_hermiteFunction m x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2)
    let he : MemLp e 2 volume := apm_m02j02_normalized_hermite_memLp_two m
    inner ℝ u (he.toLp e) = apm_m02j02_normalizedHermiteCoefficient φ m := by
  dsimp only
  let e : ℝ → ℝ := fun x =>
    apm_m02j02_hermiteFunction m x /
      Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2)
  let em : Lp ℝ 2 (volume : Measure ℝ) :=
    (apm_m02j02_normalized_hermite_memLp_two m).toLp e
  have hlim : Tendsto
      (fun N => inner ℝ
        (apm_m02j02_normalizedHermiteProjectionSequence φ N) em)
      atTop (nhds (inner ℝ u em)) :=
    hu.inner tendsto_const_nhds
  have hevent : ∀ᶠ N : ℕ in atTop,
      inner ℝ (apm_m02j02_normalizedHermiteProjectionSequence φ N) em =
        apm_m02j02_normalizedHermiteCoefficient φ m := by
    filter_upwards [eventually_ge_atTop (m + 1)] with N hN
    have hp := apm_m02j02_inner_toLp_range_normalized_hermite_mode
      (apm_m02j02_normalizedHermiteCoefficient φ) m N (by omega)
    change inner ℝ
      (apm_m02j02_normalizedHermiteProjectionSequence φ N) em =
        apm_m02j02_normalizedHermiteCoefficient φ m
    exact hp
  have hconst : Tendsto
      (fun N => inner ℝ
        (apm_m02j02_normalizedHermiteProjectionSequence φ N) em)
      atTop (nhds (apm_m02j02_normalizedHermiteCoefficient φ m)) :=
    tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hevent)
  exact tendsto_nhds_unique hlim hconst

lemma apm_m02j02_projection_limit_residual_orthogonal
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (u : Lp ℝ 2 (volume : Measure ℝ))
    (hu : Tendsto (apm_m02j02_normalizedHermiteProjectionSequence φ)
      atTop (nhds u)) (m : ℕ) :
    let e : ℝ → ℝ := fun x =>
      apm_m02j02_hermiteFunction m x /
        Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction m y ^ 2)
    let hφLp : MemLp φ 2 volume :=
      apm_m02j02_memLp_two_of_contDiff_compact φ hφ hφc
    let he : MemLp e 2 volume := apm_m02j02_normalized_hermite_memLp_two m
    inner ℝ (hφLp.toLp φ - u) (he.toLp e) = 0 := by
  dsimp only
  rw [inner_sub_left,
    apm_m02j02_inner_testFunction_normalizedHermite_mode φ hφ hφc m,
    apm_m02j02_inner_normalizedHermiteProjectionSequence_limit φ u hu m,
    sub_self]

/-- Orthogonality to a normalized Hermite mode is equivalent, in the needed
direction, to orthogonality to the original unnormalized mode. -/
lemma apm_m02j02_inner_hermite_eq_zero_of_inner_normalized_eq_zero
    (f : Lp ℝ 2 (volume : Measure ℝ)) (n : ℕ)
    (horth :
      let e : ℝ → ℝ := fun x =>
        apm_m02j02_hermiteFunction n x /
          Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)
      let he : MemLp e 2 volume := apm_m02j02_normalized_hermite_memLp_two n
      inner ℝ f (he.toLp e) = 0) :
    inner ℝ f
      ((apm_m02j02_hermiteFunction_memLp_two n).toLp
        (apm_m02j02_hermiteFunction n)) = 0 := by
  let s : ℝ := Real.sqrt
    (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)
  let e : ℝ → ℝ := fun x => apm_m02j02_hermiteFunction n x / s
  have hs : s ≠ 0 := ne_of_gt (Real.sqrt_pos.2
    (apm_m02j02_hermite_norm_sq_pos n))
  have hfun : (fun x : ℝ => s * e x) = apm_m02j02_hermiteFunction n := by
    funext x
    dsimp [e]
    field_simp
  have hLp :
      (apm_m02j02_hermiteFunction_memLp_two n).toLp
          (apm_m02j02_hermiteFunction n) =
        s • (apm_m02j02_normalized_hermite_memLp_two n).toLp e := by
    calc
      _ = ((apm_m02j02_normalized_hermite_memLp_two n).const_smul s).toLp
          (s • e) := by
        apply MemLp.toLp_congr
        filter_upwards with x
        exact congrFun hfun x |>.symm
      _ = _ := MemLp.toLp_const_smul s
        (apm_m02j02_normalized_hermite_memLp_two n)
  rw [hLp, inner_smul_right]
  change s * inner ℝ f
      ((apm_m02j02_normalized_hermite_memLp_two n).toLp e) = 0
  rw [show inner ℝ f
      ((apm_m02j02_normalized_hermite_memLp_two n).toLp e) = 0 by
    simpa only [e, s] using horth]
  simp

/-- Orthogonality to every Hermite function is preserved by an arbitrary
finite `Finsupp` linear combination in `Lp`. -/
lemma apm_m02j02_inner_finsupp_hermite_eq_zero
    (f : Lp ℝ 2 (volume : Measure ℝ))
    (horth : ∀ n : ℕ,
      inner ℝ f ((apm_m02j02_hermiteFunction_memLp_two n).toLp
        (apm_m02j02_hermiteFunction n)) = 0)
    (c : ℕ →₀ ℝ) :
    inner ℝ f (c.sum fun n a => a •
      (apm_m02j02_hermiteFunction_memLp_two n).toLp
        (apm_m02j02_hermiteFunction n)) = 0 := by
  classical
  change inner ℝ f (∑ n ∈ c.support, c n •
    (apm_m02j02_hermiteFunction_memLp_two n).toLp
      (apm_m02j02_hermiteFunction n)) = 0
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro n hn
  rw [inner_smul_right, horth]
  simp

lemma apm_m02j02_finsupp_hermite_memLp (c : ℕ →₀ ℝ) :
    MemLp (c.sum fun n a => a • apm_m02j02_hermiteFunction n) 2 volume := by
  classical
  change MemLp (∑ n ∈ c.support,
    c n • apm_m02j02_hermiteFunction n) 2 volume
  convert memLp_finset_sum c.support (fun n hn =>
    (apm_m02j02_hermiteFunction_memLp_two n).const_smul (c n)) using 1
  ext x
  simp only [Finset.sum_apply]

lemma apm_m02j02_Lp_coeFn_finset_sum
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F : ι → Lp ℝ 2 (volume : Measure ℝ)) :
    ((∑ i ∈ s, F i : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) =ᵐ[volume]
      fun x => ∑ i ∈ s, (F i : ℝ → ℝ) x := by
  induction s using Finset.induction_on with
  | empty => simpa using (Lp.coeFn_zero ℝ 2 volume)
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j), ih] with x hadd htail
      rw [hadd]
      simp only [Pi.add_apply, htail, Finset.sum_insert hi]

/-- Packaging a pointwise finite Hermite sum in `Lp` agrees with taking the
same finite sum of the individually packaged Hermite modes. -/
lemma apm_m02j02_toLp_finsupp_hermite (c : ℕ →₀ ℝ) :
    (apm_m02j02_finsupp_hermite_memLp c).toLp
        (c.sum fun n a => a • apm_m02j02_hermiteFunction n) =
      c.sum fun n a => a •
        (apm_m02j02_hermiteFunction_memLp_two n).toLp
          (apm_m02j02_hermiteFunction n) := by
  classical
  apply Lp.ext
  have hterms : ∀ᵐ x : ℝ ∂volume, ∀ n ∈ c.support,
      ((c n • (apm_m02j02_hermiteFunction_memLp_two n).toLp
        (apm_m02j02_hermiteFunction n) : Lp ℝ 2 volume) : ℝ → ℝ) x =
          c n * apm_m02j02_hermiteFunction n x := by
    rw [Finset.eventually_all]
    intro n hn
    filter_upwards [Lp.coeFn_smul (c n)
      ((apm_m02j02_hermiteFunction_memLp_two n).toLp
        (apm_m02j02_hermiteFunction n)),
      (apm_m02j02_hermiteFunction_memLp_two n).coeFn_toLp] with x hs hx
    rw [hs]
    simp only [Pi.smul_apply, smul_eq_mul, hx]
  have hsum := apm_m02j02_Lp_coeFn_finset_sum c.support
    (fun n => c n • (apm_m02j02_hermiteFunction_memLp_two n).toLp
      (apm_m02j02_hermiteFunction n))
  filter_upwards [(apm_m02j02_finsupp_hermite_memLp c).coeFn_toLp,
    hsum, hterms] with x hx hsumx htermsx
  rw [hx]
  simp only [Finsupp.sum]
  rw [hsumx]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n hn
  exact (htermsx n hn).symm

lemma apm_m02j02_inner_weightedEval_eq_zero_of_hermite
    (f : Lp ℝ 2 (volume : Measure ℝ))
    (horth : ∀ n : ℕ,
      inner ℝ f ((apm_m02j02_hermiteFunction_memLp_two n).toLp
        (apm_m02j02_hermiteFunction n)) = 0)
    (p : ℝ[X]) :
    inner ℝ f ((apm_m02j02_weightedEval_memLp_two p).toLp
      (apm_m02j02_weightedEval p)) = 0 := by
  obtain ⟨c, hc, hcderiv⟩ :=
    apm_m02j02_exists_hermite_coefficients_weightedEval p
  have hLp :
      (apm_m02j02_weightedEval_memLp_two p).toLp
          (apm_m02j02_weightedEval p) =
        (apm_m02j02_finsupp_hermite_memLp c).toLp
          (c.sum fun n a => a • apm_m02j02_hermiteFunction n) := by
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (fun x => congrFun hc x)
  rw [hLp, apm_m02j02_toLp_finsupp_hermite]
  exact apm_m02j02_inner_finsupp_hermite_eq_zero f horth c

lemma apm_m02j02_integral_weightedEval_eq_zero_of_hermite
    (f : Lp ℝ 2 (volume : Measure ℝ))
    (horth : ∀ n : ℕ,
      inner ℝ f ((apm_m02j02_hermiteFunction_memLp_two n).toLp
        (apm_m02j02_hermiteFunction n)) = 0)
    (p : ℝ[X]) :
    (∫ x : ℝ, f x * apm_m02j02_weightedEval p x) = 0 := by
  have h := apm_m02j02_inner_weightedEval_eq_zero_of_hermite f horth p
  rw [L2.inner_def] at h
  calc
    (∫ x : ℝ, f x * apm_m02j02_weightedEval p x) =
        ∫ x : ℝ, inner ℝ (f x)
          (((apm_m02j02_weightedEval_memLp_two p).toLp
            (apm_m02j02_weightedEval p)) x) := by
      apply integral_congr_ae
      filter_upwards [(apm_m02j02_weightedEval_memLp_two p).coeFn_toLp]
        with x hx
      rw [hx, apm_m02j02_real_inner_eq_mul]
    _ = 0 := h

/-- An `L²` representative becomes integrable after multiplication by the
Gaussian appearing in the Hermite functions. -/
lemma apm_m02j02_integrable_Lp_mul_gaussian
    (f : Lp ℝ 2 (volume : Measure ℝ)) :
    Integrable (fun x : ℝ => f x * Real.exp (-(x ^ 2) / 4)) volume := by
  have h := (MeasureTheory.Lp.memLp f).integrable_mul
    (apm_m02j02_hermiteFunction_memLp_two 0)
  convert h using 1
  ext x
  simp [apm_m02j02_hermiteFunction, Polynomial.hermite_zero]

lemma apm_m02j02_gaussian_weighted_moment_eq_zero
    (f : Lp ℝ 2 (volume : Measure ℝ))
    (horth : ∀ n : ℕ,
      inner ℝ f ((apm_m02j02_hermiteFunction_memLp_two n).toLp
        (apm_m02j02_hermiteFunction n)) = 0)
    (n : ℕ) :
    (∫ x : ℝ, x ^ n * (f x * Real.exp (-(x ^ 2) / 4))) = 0 := by
  have h := apm_m02j02_integral_weightedEval_eq_zero_of_hermite
    f horth (Polynomial.X ^ n)
  simpa [apm_m02j02_weightedEval, mul_assoc, mul_left_comm, mul_comm] using h

lemma apm_m02j02_integrable_gaussian_weighted_moment
    (f : Lp ℝ 2 (volume : Measure ℝ)) (n : ℕ) :
    Integrable (fun x : ℝ =>
      x ^ n * (f x * Real.exp (-(x ^ 2) / 4))) volume := by
  have h := (MeasureTheory.Lp.memLp f).integrable_mul
    (apm_m02j02_weightedEval_memLp_two (Polynomial.X ^ n))
  convert h using 1
  ext x
  simp [apm_m02j02_weightedEval]
  ring

lemma apm_m02j02_exp_abs_mul_gaussian_majorant (t x : ℝ) :
    Real.exp (|t| * |x| - x ^ 2 / 4) ≤
      Real.exp (2 * t ^ 2) * Real.exp (-x ^ 2 / 8) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := sq_nonneg (|x| - 4 * |t|)
  have ht : |t| ^ 2 = t ^ 2 := sq_abs t
  have hx : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith

lemma apm_m02j02_integrable_exp_abs_mul_gaussian (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (|t| * |x| - x ^ 2 / 4)) volume := by
  have hg : Integrable (fun x : ℝ => Real.exp (-x ^ 2 / 8)) volume := by
    convert integrable_exp_neg_mul_sq (by norm_num : 0 < (1 / 8 : ℝ)) using 1
    ext x
    congr 2
    ring
  apply Integrable.mono' (hg.const_mul (Real.exp (2 * t ^ 2)))
  · fun_prop
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact apm_m02j02_exp_abs_mul_gaussian_majorant t x

lemma apm_m02j02_memLp_two_exp_abs_mul_gaussian (t : ℝ) :
    MemLp (fun x : ℝ => Real.exp (|t| * |x| - x ^ 2 / 4)) 2 volume := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have h := apm_m02j02_integrable_exp_abs_mul_gaussian (2 * t)
  apply Integrable.mono' h
  · fun_prop
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two,
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [abs_mul]
    norm_num
    nlinarith [sq_nonneg x]

lemma apm_m02j02_integrable_exp_mul_abs_gaussianWeighted
    (f : Lp ℝ 2 (volume : Measure ℝ)) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (|t| * |x|) *
      |f x * Real.exp (-(x ^ 2) / 4)|) volume := by
  have h := (MeasureTheory.Lp.memLp f).integrable_mul
    (apm_m02j02_memLp_two_exp_abs_mul_gaussian t)
  have hn := h.norm
  convert hn using 1
  ext x
  rw [Real.norm_eq_abs]
  simp only [Pi.mul_apply, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (|t| * |x|) * (|f x| * Real.exp (-x ^ 2 / 4)) =
        |f x| * (Real.exp (|t| * |x|) * Real.exp (-x ^ 2 / 4)) := by ring
    _ = |f x| * Real.exp (|t| * |x| - x ^ 2 / 4) := by
      rw [← Real.exp_add]
      congr 2 <;> ring

lemma apm_m02j02_integral_complex_gaussian_weighted_moment_eq_zero
    (f : Lp ℝ 2 (volume : Measure ℝ))
    (horth : ∀ n : ℕ,
      inner ℝ f ((apm_m02j02_hermiteFunction_memLp_two n).toLp
        (apm_m02j02_hermiteFunction n)) = 0)
    (n : ℕ) :
    (∫ x : ℝ, ((x ^ n *
      (f x * Real.exp (-(x ^ 2) / 4)) : ℝ) : ℂ)) = 0 := by
  have hi := integral_ofReal
    (f := fun x : ℝ => x ^ n *
      (f x * Real.exp (-(x ^ 2) / 4))) (𝕜 := ℂ) (μ := volume)
  exact hi.trans (by
    rw [apm_m02j02_gaussian_weighted_moment_eq_zero f horth n]
    norm_num)

lemma apm_m02j02_hasSum_integral_complex_exp_gaussianWeighted
    (f : Lp ℝ 2 (volume : Measure ℝ)) (z : ℂ) :
    HasSum
      (fun n : ℕ => ∫ x : ℝ,
        ((z * (x : ℂ)) ^ n / n.factorial) *
          ((f x * Real.exp (-(x ^ 2) / 4) : ℝ) : ℂ))
      (∫ x : ℝ, Complex.exp (z * (x : ℂ)) *
        ((f x * Real.exp (-(x ^ 2) / 4) : ℝ) : ℂ)) := by
  let h : ℝ → ℝ := fun x => f x * Real.exp (-(x ^ 2) / 4)
  let F : ℕ → ℝ → ℂ := fun n x =>
    ((z * (x : ℂ)) ^ n / n.factorial) * (h x : ℂ)
  let b : ℕ → ℝ → ℝ := fun n x =>
    ((‖z‖ * |x|) ^ n / n.factorial) * |h x|
  apply MeasureTheory.hasSum_integral_of_dominated_convergence b
  · intro n
    fun_prop
  · intro n
    filter_upwards [] with x
    dsimp [F, b]
    rw [norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_real,
      Complex.norm_natCast, Real.norm_eq_abs]
    rw [Complex.norm_real, Real.norm_eq_abs]
  · filter_upwards [] with x
    exact ((NormedSpace.expSeries_div_hasSum_exp
      (‖z‖ * |x| : ℝ)).mul_right |h x|).summable
  · have hi := apm_m02j02_integrable_exp_mul_abs_gaussianWeighted f ‖z‖
    convert hi using 1
    ext x
    dsimp [b, h]
    have hs := NormedSpace.expSeries_div_hasSum_exp
      (‖z‖ * |x| : ℝ)
    rw [← Real.exp_eq_exp_ℝ] at hs
    calc
      (∑' n : ℕ, (‖z‖ * |x|) ^ n / n.factorial *
          |f x * Real.exp (-x ^ 2 / 4)|) =
          (∑' n : ℕ, (‖z‖ * |x|) ^ n / n.factorial) *
            |f x * Real.exp (-x ^ 2 / 4)| := tsum_mul_right
      _ = Real.exp (‖z‖ * |x|) *
            |f x * Real.exp (-x ^ 2 / 4)| := by rw [hs.tsum_eq]
      _ = _ := by simp
  · filter_upwards [] with x
    simpa [F, h, Complex.exp_eq_exp_ℂ] using
      ((NormedSpace.expSeries_div_hasSum_exp (z * (x : ℂ))).mul_right
        ((h x : ℝ) : ℂ))

lemma apm_m02j02_integral_complex_exp_gaussianWeighted_eq_zero
    (f : Lp ℝ 2 (volume : Measure ℝ))
    (horth : ∀ n : ℕ,
      inner ℝ f ((apm_m02j02_hermiteFunction_memLp_two n).toLp
        (apm_m02j02_hermiteFunction n)) = 0)
    (z : ℂ) :
    (∫ x : ℝ, Complex.exp (z * (x : ℂ)) *
      ((f x * Real.exp (-(x ^ 2) / 4) : ℝ) : ℂ)) = 0 := by
  have hs := apm_m02j02_hasSum_integral_complex_exp_gaussianWeighted f z
  have hterm : ∀ n : ℕ, (∫ x : ℝ,
      ((z * (x : ℂ)) ^ n / n.factorial) *
        ((f x * Real.exp (-(x ^ 2) / 4) : ℝ) : ℂ)) = 0 := by
    intro n
    have hm := apm_m02j02_integral_complex_gaussian_weighted_moment_eq_zero
      f horth n
    calc
      _ = ∫ x : ℝ, (z ^ n / n.factorial) *
          ((x ^ n * (f x * Real.exp (-(x ^ 2) / 4)) : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [] with x
        push_cast
        ring
      _ = (z ^ n / n.factorial) *
          (∫ x : ℝ, ((x ^ n *
            (f x * Real.exp (-(x ^ 2) / 4)) : ℝ) : ℂ)) := by
        exact MeasureTheory.integral_const_mul (μ := volume)
          (z ^ n / n.factorial)
          (fun x : ℝ => ((x ^ n *
            (f x * Real.exp (-(x ^ 2) / 4)) : ℝ) : ℂ))
      _ = 0 := by rw [hm, mul_zero]
  have hs0 : HasSum
      (fun n : ℕ => ∫ x : ℝ,
        ((z * (x : ℂ)) ^ n / n.factorial) *
          ((f x * Real.exp (-(x ^ 2) / 4) : ℝ) : ℂ)) 0 := by
    simpa only [hterm] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  exact hs.unique hs0

lemma apm_m02j02_integrable_gaussianWeighted_posPart
    (f : Lp ℝ 2 (volume : Measure ℝ)) :
    Integrable (fun x : ℝ =>
      max (f x * Real.exp (-(x ^ 2) / 4)) 0) volume := by
  apply Integrable.mono' (apm_m02j02_integrable_Lp_mul_gaussian f).norm
  · fun_prop
  · filter_upwards [] with x
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)

lemma apm_m02j02_integrable_gaussianWeighted_negPart
    (f : Lp ℝ 2 (volume : Measure ℝ)) :
    Integrable (fun x : ℝ =>
      max (-(f x * Real.exp (-(x ^ 2) / 4))) 0) volume := by
  apply Integrable.mono' (apm_m02j02_integrable_Lp_mul_gaussian f).norm
  · fun_prop
  · filter_upwards [] with x
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)

lemma apm_m02j02_integral_char_posPart_eq_negPart
    (f : Lp ℝ 2 (volume : Measure ℝ))
    (horth : ∀ n : ℕ,
      inner ℝ f ((apm_m02j02_hermiteFunction_memLp_two n).toLp
        (apm_m02j02_hermiteFunction n)) = 0)
    (t : ℝ) :
    (∫ x : ℝ, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
      (max (f x * Real.exp (-(x ^ 2) / 4)) 0 : ℝ)) =
    ∫ x : ℝ, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
      (max (-(f x * Real.exp (-(x ^ 2) / 4))) 0 : ℝ) := by
  let hp : ℝ → ℂ := fun x => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
    (max (f x * Real.exp (-(x ^ 2) / 4)) 0 : ℝ)
  let hn : ℝ → ℂ := fun x => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
    (max (-(f x * Real.exp (-(x ^ 2) / 4))) 0 : ℝ)
  have hip : Integrable hp volume := by
    apply Integrable.mono'
      (apm_m02j02_integrable_gaussianWeighted_posPart f)
    · fun_prop
    · filter_upwards [] with x
      dsimp [hp]
      rw [norm_mul, Complex.norm_exp]
      rw [show (((t : ℂ) * (x : ℂ) * Complex.I).re) = 0 by simp]
      simp only [Real.exp_zero, one_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (le_max_right _ _)]
  have hin : Integrable hn volume := by
    apply Integrable.mono'
      (apm_m02j02_integrable_gaussianWeighted_negPart f)
    · fun_prop
    · filter_upwards [] with x
      dsimp [hn]
      rw [norm_mul, Complex.norm_exp]
      rw [show (((t : ℂ) * (x : ℂ) * Complex.I).re) = 0 by simp]
      simp only [Real.exp_zero, one_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (le_max_right _ _)]
  have hz := apm_m02j02_integral_complex_exp_gaussianWeighted_eq_zero
    f horth ((t : ℂ) * Complex.I)
  have hz' : (∫ x : ℝ,
      Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
        ((f x * Real.exp (-(x ^ 2) / 4) : ℝ) : ℂ)) = 0 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hz
  have hsplit : (∫ x : ℝ,
      Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
        ((f x * Real.exp (-(x ^ 2) / 4) : ℝ) : ℂ)) =
      ∫ x : ℝ, hp x - hn x := by
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [hp, hn]
    rw [mul_assoc]
    congr 1
    push_cast
    by_cases hx : 0 ≤ f x * Real.exp (-(x ^ 2) / 4)
    · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    · have hx' : f x * Real.exp (-(x ^ 2) / 4) ≤ 0 := le_of_not_ge hx
      simp [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
  rw [hsplit, MeasureTheory.integral_sub hip hin] at hz'
  exact sub_eq_zero.mp hz'

lemma apm_m02j02_integral_char_withDensity_posPart
    (f : Lp ℝ 2 (volume : Measure ℝ)) (t : ℝ) :
    (∫ x : ℝ, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)
      ∂volume.withDensity (fun x : ℝ => ENNReal.ofReal
        (max (f x * Real.exp (-(x ^ 2) / 4)) 0))) =
    ∫ x : ℝ, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
      (max (f x * Real.exp (-(x ^ 2) / 4)) 0 : ℝ) := by
  have hp := apm_m02j02_integrable_gaussianWeighted_posPart f
  calc
    _ = ∫ x : ℝ, (ENNReal.ofReal
          (max (f x * Real.exp (-(x ^ 2) / 4)) 0)).toReal •
        Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) :=
      integral_withDensity_eq_integral_toReal_smul₀
        hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [ENNReal.toReal_ofReal (le_max_right _ _)]
      simp [smul_eq_mul, mul_comm]

lemma apm_m02j02_integral_char_withDensity_negPart
    (f : Lp ℝ 2 (volume : Measure ℝ)) (t : ℝ) :
    (∫ x : ℝ, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)
      ∂volume.withDensity (fun x : ℝ => ENNReal.ofReal
        (max (-(f x * Real.exp (-(x ^ 2) / 4))) 0))) =
    ∫ x : ℝ, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
      (max (-(f x * Real.exp (-(x ^ 2) / 4))) 0 : ℝ) := by
  have hn := apm_m02j02_integrable_gaussianWeighted_negPart f
  calc
    _ = ∫ x : ℝ, (ENNReal.ofReal
          (max (-(f x * Real.exp (-(x ^ 2) / 4))) 0)).toReal •
        Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) :=
      integral_withDensity_eq_integral_toReal_smul₀
        hn.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [ENNReal.toReal_ofReal (le_max_right _ _)]
      simp [smul_eq_mul, mul_comm]

lemma apm_m02j02_charFun_gaussianWeighted_posPart_eq_negPart
    (f : Lp ℝ 2 (volume : Measure ℝ))
    (horth : ∀ n : ℕ,
      inner ℝ f ((apm_m02j02_hermiteFunction_memLp_two n).toLp
        (apm_m02j02_hermiteFunction n)) = 0) :
    MeasureTheory.charFun
        (volume.withDensity (fun x : ℝ => ENNReal.ofReal
          (max (f x * Real.exp (-(x ^ 2) / 4)) 0))) =
      MeasureTheory.charFun
        (volume.withDensity (fun x : ℝ => ENNReal.ofReal
          (max (-(f x * Real.exp (-(x ^ 2) / 4))) 0))) := by
  funext t
  rw [MeasureTheory.charFun_apply_real, MeasureTheory.charFun_apply_real]
  rw [apm_m02j02_integral_char_withDensity_posPart,
    apm_m02j02_integral_char_withDensity_negPart]
  exact apm_m02j02_integral_char_posPart_eq_negPart f horth t

lemma apm_m02j02_gaussianWeighted_pos_withDensity_eq_neg
    (f : Lp ℝ 2 (volume : Measure ℝ))
    (horth : ∀ n : ℕ,
      inner ℝ f ((apm_m02j02_hermiteFunction_memLp_two n).toLp
        (apm_m02j02_hermiteFunction n)) = 0) :
    volume.withDensity (fun x : ℝ => ENNReal.ofReal
      (max (f x * Real.exp (-(x ^ 2) / 4)) 0)) =
    volume.withDensity (fun x : ℝ => ENNReal.ofReal
      (max (-(f x * Real.exp (-(x ^ 2) / 4))) 0)) := by
  let p : ℝ → ℝ := fun x => max (f x * Real.exp (-(x ^ 2) / 4)) 0
  let n : ℝ → ℝ := fun x => max (-(f x * Real.exp (-(x ^ 2) / 4))) 0
  have hp : Integrable p volume :=
    apm_m02j02_integrable_gaussianWeighted_posPart f
  have hn : Integrable n volume :=
    apm_m02j02_integrable_gaussianWeighted_negPart f
  letI : IsFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (p x)) :=
    MeasureTheory.isFiniteMeasure_withDensity_ofReal hp.hasFiniteIntegral
  letI : IsFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (n x)) :=
    MeasureTheory.isFiniteMeasure_withDensity_ofReal hn.hasFiniteIntegral
  change volume.withDensity (fun x => ENNReal.ofReal (p x)) =
    volume.withDensity (fun x => ENNReal.ofReal (n x))
  apply MeasureTheory.Measure.ext_of_charFun
  simpa only [p, n] using
    apm_m02j02_charFun_gaussianWeighted_posPart_eq_negPart f horth

lemma apm_m02j02_gaussianWeighted_ae_eq_zero_of_hermite
    (f : Lp ℝ 2 (volume : Measure ℝ))
    (horth : ∀ n : ℕ,
      inner ℝ f ((apm_m02j02_hermiteFunction_memLp_two n).toLp
        (apm_m02j02_hermiteFunction n)) = 0) :
    (fun x : ℝ => f x * Real.exp (-(x ^ 2) / 4)) =ᵐ[volume] 0 := by
  let p : ℝ → ℝ := fun x => max (f x * Real.exp (-(x ^ 2) / 4)) 0
  let n : ℝ → ℝ := fun x => max (-(f x * Real.exp (-(x ^ 2) / 4))) 0
  have hp := apm_m02j02_integrable_gaussianWeighted_posPart f
  have hn := apm_m02j02_integrable_gaussianWeighted_negPart f
  have hm := apm_m02j02_gaussianWeighted_pos_withDensity_eq_neg f horth
  have hae : (fun x => ENNReal.ofReal (p x)) =ᵐ[volume]
      (fun x => ENNReal.ofReal (n x)) :=
    (MeasureTheory.withDensity_eq_iff_of_sigmaFinite
      hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      hn.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mp (by
        simpa only [p, n] using hm)
  filter_upwards [hae] with x hx
  have hpn : p x = n x :=
    (ENNReal.ofReal_eq_ofReal_iff (by dsimp [p]; exact le_max_right _ _)
      (by dsimp [n]; exact le_max_right _ _)).mp hx
  dsimp [p, n] at hpn ⊢
  by_cases h : 0 ≤ f x * Real.exp (-(x ^ 2) / 4)
  · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)] at hpn
    rw [hpn, zero_mul]
  · have h' : f x * Real.exp (-(x ^ 2) / 4) ≤ 0 := le_of_not_ge h
    simp [max_eq_right h', max_eq_left (neg_nonneg.mpr h')] at hpn
    rw [hpn, zero_mul]

lemma apm_m02j02_hermite_orthogonal_complement_eq_zero
    (f : Lp ℝ 2 (volume : Measure ℝ))
    (horth : ∀ n : ℕ,
      inner ℝ f ((apm_m02j02_hermiteFunction_memLp_two n).toLp
        (apm_m02j02_hermiteFunction n)) = 0) :
    f = 0 := by
  have hw := apm_m02j02_gaussianWeighted_ae_eq_zero_of_hermite f horth
  apply Lp.ext
  filter_upwards [hw] with x hx
  have he : Real.exp (-(x ^ 2) / 4) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hf : f x = 0 := (mul_eq_zero.mp hx).resolve_right he
  simpa [hf]

lemma apm_m02j02_normalizedHermiteProjectionSequence_limit_eq_testFunction
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (u : Lp ℝ 2 (volume : Measure ℝ))
    (hu : Tendsto (apm_m02j02_normalizedHermiteProjectionSequence φ)
      atTop (nhds u)) :
    u = (apm_m02j02_memLp_two_of_contDiff_compact φ hφ hφc).toLp φ := by
  let φLp : Lp ℝ 2 (volume : Measure ℝ) :=
    (apm_m02j02_memLp_two_of_contDiff_compact φ hφ hφc).toLp φ
  have horth : ∀ n : ℕ, inner ℝ (φLp - u)
      ((apm_m02j02_hermiteFunction_memLp_two n).toLp
        (apm_m02j02_hermiteFunction n)) = 0 := by
    intro n
    apply apm_m02j02_inner_hermite_eq_zero_of_inner_normalized_eq_zero
    exact apm_m02j02_projection_limit_residual_orthogonal
      φ hφ hφc u hu n
  have hz := apm_m02j02_hermite_orthogonal_complement_eq_zero (φLp - u) horth
  exact sub_eq_zero.mp hz |>.symm

lemma apm_m02j02_integral_normalizedHermiteProjection_mul_modeDeriv
    (a : ℕ → ℝ) (N m : ℕ) :
    (∫ x : ℝ, apm_m02j02_normalizedHermiteProjection a N x *
      apm_m02j02_hermiteFunctionDeriv m x) =
    -∫ x : ℝ, apm_m02j02_normalizedHermiteDerivProjection a N x *
      apm_m02j02_hermiteFunction m x := by
  apply MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
  · intro x _
    unfold apm_m02j02_normalizedHermiteProjection
    have h := HasDerivAt.fun_sum (u := Finset.range N)
      (A := fun n => fun y : ℝ =>
        a n * (apm_m02j02_hermiteFunction n y /
          Real.sqrt (∫ z : ℝ, apm_m02j02_hermiteFunction n z ^ 2)))
      (A' := fun n =>
        a n * (apm_m02j02_hermiteFunctionDeriv n x /
          Real.sqrt (∫ z : ℝ, apm_m02j02_hermiteFunction n z ^ 2)))
      (fun n _ => by
        convert (apm_m02j02_hermiteFunction_hasDerivAt n x).const_mul
          (a n / Real.sqrt
            (∫ z : ℝ, apm_m02j02_hermiteFunction n z ^ 2)) using 1 <;>
          field_simp)
    simpa only [apm_m02j02_normalizedHermiteDerivProjection] using h
  · intro x _
    exact apm_m02j02_hermiteFunction_hasDerivAt m x
  · exact (apm_m02j02_normalizedHermiteProjection_memLp a N).integrable_mul
      (apm_m02j02_hermiteFunctionDeriv_memLp_two m)
  · exact (apm_m02j02_normalizedHermiteDerivProjection_memLp a N).integrable_mul
      (apm_m02j02_hermiteFunction_memLp_two m)
  · exact (apm_m02j02_normalizedHermiteProjection_memLp a N).integrable_mul
      (apm_m02j02_hermiteFunction_memLp_two m)

lemma apm_m02j02_inner_normalizedHermiteProjection_modeDeriv
    (a : ℕ → ℝ) (N m : ℕ) :
    inner ℝ (apm_m02j02_normalizedHermiteProjectionLp a N)
      ((apm_m02j02_hermiteFunctionDeriv_memLp_two m).toLp
        (apm_m02j02_hermiteFunctionDeriv m)) =
    -inner ℝ (apm_m02j02_normalizedHermiteDerivProjectionLp a N)
      ((apm_m02j02_hermiteFunction_memLp_two m).toLp
        (apm_m02j02_hermiteFunction m)) := by
  rw [L2.inner_def, L2.inner_def]
  have hv : (∫ x : ℝ, inner ℝ
      (apm_m02j02_normalizedHermiteProjectionLp a N x)
      (((apm_m02j02_hermiteFunctionDeriv_memLp_two m).toLp
        (apm_m02j02_hermiteFunctionDeriv m)) x)) =
      ∫ x : ℝ, apm_m02j02_normalizedHermiteProjection a N x *
        apm_m02j02_hermiteFunctionDeriv m x := by
    apply integral_congr_ae
    filter_upwards
      [(apm_m02j02_normalizedHermiteProjection_memLp a N).coeFn_toLp,
       (apm_m02j02_hermiteFunctionDeriv_memLp_two m).coeFn_toLp]
      with x hx hdx
    simp only [apm_m02j02_normalizedHermiteProjectionLp]
    rw [hx, hdx, apm_m02j02_real_inner_eq_mul]
  have hd : (∫ x : ℝ, inner ℝ
      (apm_m02j02_normalizedHermiteDerivProjectionLp a N x)
      (((apm_m02j02_hermiteFunction_memLp_two m).toLp
        (apm_m02j02_hermiteFunction m)) x)) =
      ∫ x : ℝ, apm_m02j02_normalizedHermiteDerivProjection a N x *
        apm_m02j02_hermiteFunction m x := by
    apply integral_congr_ae
    filter_upwards
      [(apm_m02j02_normalizedHermiteDerivProjection_memLp a N).coeFn_toLp,
       (apm_m02j02_hermiteFunction_memLp_two m).coeFn_toLp]
      with x hx hmx
    simp only [apm_m02j02_normalizedHermiteDerivProjectionLp]
    rw [hx, hmx, apm_m02j02_real_inner_eq_mul]
  rw [hv, hd]
  exact apm_m02j02_integral_normalizedHermiteProjection_mul_modeDeriv a N m

lemma apm_m02j02_inner_testFunctionDeriv_hermite_mode
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (m : ℕ) :
    let hφLp : MemLp φ 2 volume :=
      apm_m02j02_memLp_two_of_contDiff_compact φ hφ hφc
    let hφd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
    let hφdLp : MemLp (deriv φ) 2 volume :=
      apm_m02j02_memLp_two_of_contDiff_compact (deriv φ) hφd hφc.deriv
    inner ℝ (hφdLp.toLp (deriv φ))
      ((apm_m02j02_hermiteFunction_memLp_two m).toLp
        (apm_m02j02_hermiteFunction m)) =
    -inner ℝ (hφLp.toLp φ)
      ((apm_m02j02_hermiteFunctionDeriv_memLp_two m).toLp
        (apm_m02j02_hermiteFunctionDeriv m)) := by
  dsimp only
  rw [L2.inner_def, L2.inner_def]
  have hleft : (∫ x : ℝ, inner ℝ
      (((apm_m02j02_memLp_two_of_contDiff_compact (deriv φ)
        (contDiff_infty_iff_deriv.mp hφ).2 hφc.deriv).toLp (deriv φ)) x)
      (((apm_m02j02_hermiteFunction_memLp_two m).toLp
        (apm_m02j02_hermiteFunction m)) x)) =
      ∫ x : ℝ, deriv φ x * apm_m02j02_hermiteFunction m x := by
    apply integral_congr_ae
    filter_upwards
      [(apm_m02j02_memLp_two_of_contDiff_compact (deriv φ)
        (contDiff_infty_iff_deriv.mp hφ).2 hφc.deriv).coeFn_toLp,
       (apm_m02j02_hermiteFunction_memLp_two m).coeFn_toLp]
      with x hx hmx
    rw [hx, hmx, apm_m02j02_real_inner_eq_mul]
  have hright : (∫ x : ℝ, inner ℝ
      (((apm_m02j02_memLp_two_of_contDiff_compact φ hφ hφc).toLp φ) x)
      (((apm_m02j02_hermiteFunctionDeriv_memLp_two m).toLp
        (apm_m02j02_hermiteFunctionDeriv m)) x)) =
      ∫ x : ℝ, φ x * apm_m02j02_hermiteFunctionDeriv m x := by
    apply integral_congr_ae
    filter_upwards
      [(apm_m02j02_memLp_two_of_contDiff_compact φ hφ hφc).coeFn_toLp,
       (apm_m02j02_hermiteFunctionDeriv_memLp_two m).coeFn_toLp]
      with x hx hdx
    rw [hx, hdx, apm_m02j02_real_inner_eq_mul]
  rw [hleft, hright]
  have hibp : (∫ x : ℝ, φ x * apm_m02j02_hermiteFunctionDeriv m x) =
      -∫ x : ℝ, deriv φ x * apm_m02j02_hermiteFunction m x := by
    apply MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    · intro x _
      exact (hφ.differentiable (by simp) x).hasDerivAt
    · intro x _
      exact apm_m02j02_hermiteFunction_hasDerivAt m x
    · exact (apm_m02j02_memLp_two_of_contDiff_compact φ hφ hφc).integrable_mul
        (apm_m02j02_hermiteFunctionDeriv_memLp_two m)
    · exact (apm_m02j02_memLp_two_of_contDiff_compact (deriv φ)
        (contDiff_infty_iff_deriv.mp hφ).2 hφc.deriv).integrable_mul
        (apm_m02j02_hermiteFunction_memLp_two m)
    · exact (apm_m02j02_memLp_two_of_contDiff_compact φ hφ hφc).integrable_mul
        (apm_m02j02_hermiteFunction_memLp_two m)
  linarith

lemma apm_m02j02_normalizedHermiteDerivProjectionSequence_limit_eq_deriv
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (u v : Lp ℝ 2 (volume : Measure ℝ))
    (hu : Tendsto (apm_m02j02_normalizedHermiteProjectionSequence φ)
      atTop (nhds u))
    (hv : Tendsto (apm_m02j02_normalizedHermiteDerivProjectionSequence φ)
      atTop (nhds v)) :
    v = (apm_m02j02_memLp_two_of_contDiff_compact (deriv φ)
      (contDiff_infty_iff_deriv.mp hφ).2 hφc.deriv).toLp (deriv φ) := by
  let φLp : Lp ℝ 2 (volume : Measure ℝ) :=
    (apm_m02j02_memLp_two_of_contDiff_compact φ hφ hφc).toLp φ
  let dφLp : Lp ℝ 2 (volume : Measure ℝ) :=
    (apm_m02j02_memLp_two_of_contDiff_compact (deriv φ)
      (contDiff_infty_iff_deriv.mp hφ).2 hφc.deriv).toLp (deriv φ)
  have hu_eq : u = φLp :=
    apm_m02j02_normalizedHermiteProjectionSequence_limit_eq_testFunction
      φ hφ hφc u hu
  have horth : ∀ m : ℕ, inner ℝ (v - dφLp)
      ((apm_m02j02_hermiteFunction_memLp_two m).toLp
        (apm_m02j02_hermiteFunction m)) = 0 := by
    intro m
    let hm : Lp ℝ 2 (volume : Measure ℝ) :=
      (apm_m02j02_hermiteFunction_memLp_two m).toLp
        (apm_m02j02_hermiteFunction m)
    let hdm : Lp ℝ 2 (volume : Measure ℝ) :=
      (apm_m02j02_hermiteFunctionDeriv_memLp_two m).toLp
        (apm_m02j02_hermiteFunctionDeriv m)
    have hlu : Tendsto
        (fun N => inner ℝ
          (apm_m02j02_normalizedHermiteProjectionSequence φ N) hdm)
        atTop (nhds (inner ℝ u hdm)) := hu.inner tendsto_const_nhds
    have hlv : Tendsto
        (fun N => -inner ℝ
          (apm_m02j02_normalizedHermiteDerivProjectionSequence φ N) hm)
        atTop (nhds (-inner ℝ v hm)) :=
      (hv.inner tendsto_const_nhds).neg
    have heq : (fun N => inner ℝ
          (apm_m02j02_normalizedHermiteProjectionSequence φ N) hdm) =
        (fun N => -inner ℝ
          (apm_m02j02_normalizedHermiteDerivProjectionSequence φ N) hm) := by
      funext N
      simpa only [apm_m02j02_normalizedHermiteProjectionSequence,
        apm_m02j02_normalizedHermiteDerivProjectionSequence, hm, hdm] using
        apm_m02j02_inner_normalizedHermiteProjection_modeDeriv
          (apm_m02j02_normalizedHermiteCoefficient φ) N m
    have hlim : inner ℝ u hdm = -inner ℝ v hm :=
      tendsto_nhds_unique hlu (heq ▸ hlv)
    have htest := apm_m02j02_inner_testFunctionDeriv_hermite_mode
      φ hφ hφc m
    change inner ℝ (v - dφLp) hm = 0
    rw [inner_sub_left]
    change inner ℝ v hm - inner ℝ dφLp hm = 0
    change inner ℝ dφLp hm = -inner ℝ φLp hdm at htest
    rw [hu_eq] at hlim
    linarith
  have hz := apm_m02j02_hermite_orthogonal_complement_eq_zero (v - dφLp) horth
  exact sub_eq_zero.mp hz

lemma apm_m02j02_edist_projectionSequence_testFunction
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (N : ℕ) :
    edist (apm_m02j02_normalizedHermiteProjectionSequence φ N)
      ((apm_m02j02_memLp_two_of_contDiff_compact φ hφ hφc).toLp φ) =
    eLpNorm (apm_m02j02_normalizedHermiteProjection
      (apm_m02j02_normalizedHermiteCoefficient φ) N - φ) 2 volume := by
  change edist
    ((apm_m02j02_normalizedHermiteProjection_memLp
      (apm_m02j02_normalizedHermiteCoefficient φ) N).toLp
        (apm_m02j02_normalizedHermiteProjection
          (apm_m02j02_normalizedHermiteCoefficient φ) N))
    ((apm_m02j02_memLp_two_of_contDiff_compact φ hφ hφc).toLp φ) = _
  rw [Lp.edist_toLp_toLp]

lemma apm_m02j02_edist_derivProjectionSequence_testFunctionDeriv
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (N : ℕ) :
    edist (apm_m02j02_normalizedHermiteDerivProjectionSequence φ N)
      ((apm_m02j02_memLp_two_of_contDiff_compact (deriv φ)
        (contDiff_infty_iff_deriv.mp hφ).2 hφc.deriv).toLp (deriv φ)) =
    eLpNorm (apm_m02j02_normalizedHermiteDerivProjection
      (apm_m02j02_normalizedHermiteCoefficient φ) N - deriv φ) 2 volume := by
  change edist
    ((apm_m02j02_normalizedHermiteDerivProjection_memLp
      (apm_m02j02_normalizedHermiteCoefficient φ) N).toLp
        (apm_m02j02_normalizedHermiteDerivProjection
          (apm_m02j02_normalizedHermiteCoefficient φ) N))
    ((apm_m02j02_memLp_two_of_contDiff_compact (deriv φ)
      (contDiff_infty_iff_deriv.mp hφ).2 hφc.deriv).toLp (deriv φ)) = _
  rw [Lp.edist_toLp_toLp]

lemma apm_m02j02_exists_normalizedHermiteProjection_graph_close
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ,
      eLpNorm (φ - apm_m02j02_normalizedHermiteProjection
        (apm_m02j02_normalizedHermiteCoefficient φ) N) 2 volume +
      eLpNorm (deriv φ - apm_m02j02_normalizedHermiteDerivProjection
        (apm_m02j02_normalizedHermiteCoefficient φ) N) 2 volume <
        ENNReal.ofReal ε := by
  obtain ⟨u, hu⟩ :=
    apm_m02j02_exists_normalizedHermiteProjectionSequence_limit φ hφ hφc
  obtain ⟨v, hv⟩ :=
    apm_m02j02_exists_normalizedHermiteDerivProjectionSequence_limit φ hφ hφc
  have hueq := apm_m02j02_normalizedHermiteProjectionSequence_limit_eq_testFunction
    φ hφ hφc u hu
  have hveq :=
    apm_m02j02_normalizedHermiteDerivProjectionSequence_limit_eq_deriv
      φ hφ hφc u v hu hv
  rw [hueq] at hu
  rw [hveq] at hv
  obtain ⟨Nu, hNu⟩ := EMetric.tendsto_atTop.mp hu
    (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (half_pos hε))
  obtain ⟨Nv, hNv⟩ := EMetric.tendsto_atTop.mp hv
    (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (half_pos hε))
  let N := max Nu Nv
  refine ⟨N, ?_⟩
  have hval := hNu N (le_max_left _ _)
  have hder := hNv N (le_max_right _ _)
  rw [apm_m02j02_edist_projectionSequence_testFunction φ hφ hφc N] at hval
  rw [apm_m02j02_edist_derivProjectionSequence_testFunctionDeriv
    φ hφ hφc N] at hder
  rw [eLpNorm_sub_comm] at hval hder
  calc
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      ENNReal.add_lt_add hval hder
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
      congr 1
      ring

lemma apm_m02j02_exists_weightedEval_eq_normalizedHermiteProjection
    (a : ℕ → ℝ) (N : ℕ) :
    ∃ p : ℝ[X],
      apm_m02j02_weightedEval p =
        apm_m02j02_normalizedHermiteProjection a N ∧
      (fun x => deriv (apm_m02j02_weightedEval p) x) =
        apm_m02j02_normalizedHermiteDerivProjection a N := by
  have hmem : apm_m02j02_normalizedHermiteProjection a N ∈
      Submodule.span ℝ (Set.range apm_m02j02_hermiteFunction) := by
    rw [show apm_m02j02_normalizedHermiteProjection a N =
        ∑ n ∈ Finset.range N,
          (a n / Real.sqrt (∫ y : ℝ,
            apm_m02j02_hermiteFunction n y ^ 2)) •
              apm_m02j02_hermiteFunction n by
      funext x
      simp only [apm_m02j02_normalizedHermiteProjection,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro n hn
      ring]
    apply Submodule.sum_mem
    intro n hn
    apply Submodule.smul_mem
    exact Submodule.subset_span (Set.mem_range_self n)
  rw [apm_m02j02_span_hermiteFunction_eq_weightedEval_range] at hmem
  obtain ⟨p, hp⟩ := hmem
  refine ⟨p, hp, ?_⟩
  funext x
  rw [hp]
  exact apm_m02j02_deriv_sum_range_normalized_hermite a N x

lemma apm_m02j02_hermiteFunction_neg (n : ℕ) (x : ℝ) :
    apm_m02j02_hermiteFunction n (-x) =
      (-1 : ℝ) ^ n * apm_m02j02_hermiteFunction n x := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [apm_m02j02_hermiteFunction, Polynomial.hermite_zero]
  | one =>
      simp [apm_m02j02_hermiteFunction, Polynomial.hermite_one]
  | more n hn hn1 =>
      have hneg := apm_m02j02_mul_hermiteFunction_succ n (-x)
      have hpos := apm_m02j02_mul_hermiteFunction_succ n x
      rw [hn, hn1] at hneg
      rw [show (-1 : ℝ) ^ (n + 2) = (-1 : ℝ) ^ n by
        rw [pow_add]
        norm_num]
      rw [show (-1 : ℝ) ^ (n + 1) = -((-1 : ℝ) ^ n) by
        rw [pow_succ]
        ring] at hneg
      linear_combination (-1 : ℝ) ^ n * hpos - hneg

lemma apm_m02j02_oddHermite_neg (n : ℕ) (x : ℝ) :
    apm_m02j02_hermiteFunction (2 * n + 1) (-x) =
      -apm_m02j02_hermiteFunction (2 * n + 1) x := by
  rw [apm_m02j02_hermiteFunction_neg]
  rw [show (-1 : ℝ) ^ (2 * n + 1) = -1 by
    rw [pow_add, pow_mul]
    norm_num]
  ring

lemma apm_m02j02_exists_oddHermite_linear_bound_Icc (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      |apm_m02j02_hermiteFunction (2 * n + 1) x| ≤ K * |x| := by
  apply apm_m02j02_exists_linear_bound_Icc_of_contDiff_zero
    ((apm_m02j02_hermiteFunction_contDiff (2 * n + 1)).of_le (by simp))
  have hodd := apm_m02j02_oddHermite_neg n 0
  simp only [neg_zero] at hodd
  linarith

lemma apm_m02j02_exists_oddHermite_innerCutoff_graph_close
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧
      eLpNorm (apm_m02j02_hermiteFunction (2 * n + 1) - fun x : ℝ =>
        Real.smoothTransition ((x - δ) / δ) *
          apm_m02j02_hermiteFunction (2 * n + 1) x) 2
          (volume.restrict (Ioi (0 : ℝ))) +
        eLpNorm (apm_m02j02_hermiteFunctionDeriv (2 * n + 1) -
          deriv (fun x : ℝ => Real.smoothTransition ((x - δ) / δ) *
            apm_m02j02_hermiteFunction (2 * n + 1) x)) 2
          (volume.restrict (Ioi (0 : ℝ))) < ENNReal.ofReal ε := by
  obtain ⟨B, D, hB0, hD0, hB, hD⟩ :=
    apm_m02j02_exists_oddHermite_and_deriv_abs_bound_Icc n
  obtain ⟨C, hC0, hC⟩ := apm_m02j02_smoothTransition_deriv_bounded
  obtain ⟨K, hK0, hK⟩ := apm_m02j02_exists_oddHermite_linear_bound_Icc n
  obtain ⟨δ, hδ, hδhalf, hsmall⟩ :=
    apm_m02j02_exists_small_innerCutoff_scale B C K D ε hε
  refine ⟨δ, hδ, hδhalf, ?_⟩
  have hδtwo : δ ≤ 1 / 2 := hδhalf.trans (by norm_num)
  exact (apm_m02j02_innerCutoff_graph_eLpNorm_le
    (apm_m02j02_hermiteFunction_contDiff (2 * n + 1))
    hB0 hB hC0 hC hK0 hK hD0 hD hδ hδtwo).trans_lt hsmall

lemma apm_m02j02_exists_sine_leftCutoff_graph_close
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧
      eLpNorm (apm_m02j02_sine n - fun x : ℝ =>
        Real.smoothTransition ((x - δ) / δ) * apm_m02j02_sine n x) 2
          (volume.restrict (Ioi (0 : ℝ))) +
        eLpNorm (apm_m02j02_sineDeriv n -
          deriv (fun x : ℝ => Real.smoothTransition ((x - δ) / δ) *
            apm_m02j02_sine n x)) 2
          (volume.restrict (Ioi (0 : ℝ))) < ENNReal.ofReal ε := by
  obtain ⟨B, D, hB0, hD0, hB, hD⟩ :=
    apm_m02j02_exists_sine_and_deriv_abs_bound_Icc n
  obtain ⟨C, hC0, hC⟩ := apm_m02j02_smoothTransition_deriv_bounded
  obtain ⟨K, hK0, hK⟩ := apm_m02j02_exists_sine_linear_bound_Icc n
  obtain ⟨δ, hδ, hδhalf, hsmall⟩ :=
    apm_m02j02_exists_small_innerCutoff_scale B C K D ε hε
  refine ⟨δ, hδ, hδhalf, ?_⟩
  have hδtwo : δ ≤ 1 / 2 := hδhalf.trans (by norm_num)
  have hb := (apm_m02j02_innerCutoff_graph_eLpNorm_le
    (apm_m02j02_sine_contDiff n) hB0 hB hC0 hC hK0 hK hD0
    (by simpa [apm_m02j02_deriv_sine] using hD) hδ hδtwo).trans_lt hsmall
  rw [show deriv (apm_m02j02_sine n) = apm_m02j02_sineDeriv n by
    funext x
    exact apm_m02j02_deriv_sine n x] at hb
  exact hb

lemma apm_m02j02_exists_reflectedSine_leftCutoff_graph_close
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧
      let f : ℝ → ℝ := fun x => apm_m02j02_sine n (1 - x)
      eLpNorm (f - fun x : ℝ =>
        Real.smoothTransition ((x - δ) / δ) * f x) 2
          (volume.restrict (Ioi (0 : ℝ))) +
        eLpNorm (deriv f - deriv (fun x : ℝ =>
          Real.smoothTransition ((x - δ) / δ) * f x)) 2
          (volume.restrict (Ioi (0 : ℝ))) < ENNReal.ofReal ε := by
  let f : ℝ → ℝ := fun x => apm_m02j02_sine n (1 - x)
  have hf : ContDiff ℝ ∞ f := (apm_m02j02_sine_contDiff n).comp (by fun_prop)
  have hf0 : f 0 = 0 := by simp [f, apm_m02j02_sine_one]
  obtain ⟨B, hB0, hB⟩ := apm_m02j02_exists_abs_bound_Icc_of_continuous
    hf.continuous
  obtain ⟨D, hD0, hD⟩ := apm_m02j02_exists_abs_bound_Icc_of_continuous
    (hf.continuous_deriv (by simp))
  obtain ⟨C, hC0, hC⟩ := apm_m02j02_smoothTransition_deriv_bounded
  obtain ⟨K, hK0, hK⟩ :=
    apm_m02j02_exists_linear_bound_Icc_of_contDiff_zero
      (hf.of_le (by simp)) hf0
  obtain ⟨δ, hδ, hδhalf, hsmall⟩ :=
    apm_m02j02_exists_small_innerCutoff_scale B C K D ε hε
  refine ⟨δ, hδ, hδhalf, ?_⟩
  have hδtwo : δ ≤ 1 / 2 := hδhalf.trans (by norm_num)
  dsimp only
  exact (apm_m02j02_innerCutoff_graph_eLpNorm_le hf hB0 hB hC0 hC
    hK0 hK hD0 hD hδ hδtwo).trans_lt hsmall

lemma apm_m02j02_exists_sine_rightCutoff_graph_close
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧
      eLpNorm (apm_m02j02_sine n - fun x : ℝ =>
        Real.smoothTransition (((1 - x) - δ) / δ) * apm_m02j02_sine n x) 2
          (volume.restrict (Iio (1 : ℝ))) +
        eLpNorm (apm_m02j02_sineDeriv n -
          deriv (fun x : ℝ => Real.smoothTransition (((1 - x) - δ) / δ) *
            apm_m02j02_sine n x)) 2
          (volume.restrict (Iio (1 : ℝ))) < ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hδhalf, hleft⟩ :=
    apm_m02j02_exists_reflectedSine_leftCutoff_graph_close n hε
  let f : ℝ → ℝ := apm_m02j02_sine n
  let r : ℝ → ℝ := fun x => f (1 - x)
  let g : ℝ → ℝ := fun x =>
    Real.smoothTransition ((x - δ) / δ) * r x
  let h : ℝ → ℝ := fun x =>
    Real.smoothTransition (((1 - x) - δ) / δ) * f x
  have hf : ContDiff ℝ ∞ f := apm_m02j02_sine_contDiff n
  have hg : ContDiff ℝ ∞ g :=
    (@Real.smoothTransition.contDiff (⊤ : ℕ∞)).comp (by fun_prop) |>.mul
      (hf.comp (by fun_prop))
  have hh : ContDiff ℝ ∞ h :=
    (@Real.smoothTransition.contDiff (⊤ : ℕ∞)).comp (by fun_prop) |>.mul hf
  have hgcomp : g = fun x : ℝ => h (1 - x) := by
    funext x
    simp only [g, h, r, f]
    congr 2 <;> ring
  have hvfun : (fun x : ℝ => f (1 - x) - h (1 - x)) = r - g := by
    funext x
    simp only [Pi.sub_apply, r, hgcomp]
  have hdfun : (fun x : ℝ => deriv f (1 - x) - deriv h (1 - x)) =
      -(deriv r - deriv g) := by
    funext x
    simp only [Pi.sub_apply, Pi.neg_apply]
    have hr := apm_m02j02_deriv_comp_one_sub (hf.of_le (by simp)) x
    have hh' := apm_m02j02_deriv_comp_one_sub (hh.of_le (by simp)) x
    rw [hgcomp]
    dsimp only [r]
    rw [hr, hh']
    ring
  have hv := apm_m02j02_eLpNorm_comp_one_sub
    ((hf.continuous.sub hh.continuous).aestronglyMeasurable) 2
  have hd := apm_m02j02_eLpNorm_comp_one_sub
    (((hf.continuous_deriv (by simp)).sub
      (hh.continuous_deriv (by simp))).aestronglyMeasurable) 2
  rw [hvfun] at hv
  rw [hdfun, eLpNorm_neg] at hd
  change eLpNorm (r - g) 2 (volume.restrict (Ioi (0 : ℝ))) =
    eLpNorm (f - h) 2 (volume.restrict (Iio (1 : ℝ))) at hv
  change eLpNorm (deriv r - deriv g) 2 (volume.restrict (Ioi (0 : ℝ))) =
    eLpNorm (deriv f - deriv h) 2 (volume.restrict (Iio (1 : ℝ))) at hd
  refine ⟨δ, hδ, hδhalf, ?_⟩
  have hfd : deriv f = apm_m02j02_sineDeriv n := by
    funext x
    exact apm_m02j02_deriv_sine n x
  rw [← hfd]
  change eLpNorm (f - h) 2 (volume.restrict (Iio (1 : ℝ))) +
      eLpNorm (deriv f - deriv h) 2 (volume.restrict (Iio (1 : ℝ))) < _
  rw [← hv, ← hd]
  simpa only [f, r, g, apm_m02j02_deriv_sine] using hleft

lemma apm_m02j02_sine_inH10 (n : ℕ) :
    apm_m02j02_InH10 (Ioo (0 : ℝ) 1)
      (apm_m02j02_sine n) (apm_m02j02_sineDeriv n) := by
  apply apm_m02j02_sine_inH10_of_approx n
  intro ε hε
  obtain ⟨δ, hδ, hδq, hleft⟩ :=
    apm_m02j02_exists_sine_leftCutoff_graph_close n
      (show 0 < ε / 2 by positivity)
  obtain ⟨η, hη, hηq, hright⟩ :=
    apm_m02j02_exists_sine_rightCutoff_graph_close n
      (show 0 < ε / 2 by positivity)
  let f : ℝ → ℝ := apm_m02j02_sine n
  let l : ℝ → ℝ := fun x => Real.smoothTransition ((x - δ) / δ) * f x
  let r : ℝ → ℝ := fun x => Real.smoothTransition (((1 - x) - η) / η) * f x
  let φ : ℝ → ℝ := l + r - f
  have hf : ContDiff ℝ ∞ f := apm_m02j02_sine_contDiff n
  have hl : ContDiff ℝ ∞ l :=
    (@Real.smoothTransition.contDiff (⊤ : ℕ∞)).comp (by fun_prop) |>.mul hf
  have hr : ContDiff ℝ ∞ r :=
    (@Real.smoothTransition.contDiff (⊤ : ℕ∞)).comp (by fun_prop) |>.mul hf
  have hφ : ContDiff ℝ ∞ φ := hl.add hr |>.sub hf
  have hφzero : ∀ x : ℝ, x ∉ Icc δ (1 - η) → φ x = 0 := by
    intro x hx
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · have hL : Real.smoothTransition ((x - δ) / δ) = 0 :=
        apm_m02j02_smoothTransition_affine_zero hδ (le_of_lt hx)
      have hR : Real.smoothTransition (((1 - x) - η) / η) = 1 := by
        apply apm_m02j02_smoothTransition_affine_one hη
        have h2η : 2 * η ≤ 1 / 2 := by linarith
        linarith
      simp [φ, l, r, hL, hR]
    · have hR : Real.smoothTransition (((1 - x) - η) / η) = 0 :=
        apm_m02j02_smoothTransition_affine_zero hη (by linarith)
      have hL : Real.smoothTransition ((x - δ) / δ) = 1 := by
        apply apm_m02j02_smoothTransition_affine_one hδ
        have h2δ : 2 * δ ≤ 1 / 2 := by linarith
        linarith
      simp [φ, l, r, hL, hR]
  have hφcomp : HasCompactSupport φ :=
    HasCompactSupport.intro (K := Icc δ (1 - η)) isCompact_Icc hφzero
  have hφsub : tsupport φ ⊆ Ioo (0 : ℝ) 1 := by
    have hcl : tsupport φ ⊆ Icc δ (1 - η) := by
      apply closure_minimal
      · intro x hx
        by_contra hnot
        exact hx (hφzero x hnot)
      · exact isClosed_Icc
    intro x hx
    have hx' := hcl hx
    exact ⟨hδ.trans_le hx'.1, hx'.2.trans_lt (sub_lt_self 1 hη)⟩
  refine ⟨φ, hφ, hφcomp, hφsub, ?_⟩
  have hdf : deriv f = apm_m02j02_sineDeriv n := by
    funext x
    exact apm_m02j02_deriv_sine n x
  have hdφ : deriv φ = deriv l + deriv r - deriv f := by
    funext x
    change deriv ((l + r) - f) x = _
    exact (((hl.differentiable (by simp) x).hasDerivAt.add
      (hr.differentiable (by simp) x).hasDerivAt).sub
        (hf.differentiable (by simp) x).hasDerivAt).deriv
  have hvfun : f - φ = (f - l) + (f - r) := by
    funext x
    simp [φ]
    ring
  have hdfun : deriv f - deriv φ =
      (deriv f - deriv l) + (deriv f - deriv r) := by
    rw [hdφ]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [← hdf]
  change eLpNorm (f - φ) 2 (volume.restrict (Ioo (0 : ℝ) 1)) +
      eLpNorm (deriv f - deriv φ) 2 (volume.restrict (Ioo (0 : ℝ) 1)) < _
  rw [hvfun, hdfun]
  have hv := eLpNorm_add_le (μ := volume.restrict (Ioo (0 : ℝ) 1))
    ((hf.continuous.sub hl.continuous).aestronglyMeasurable)
    ((hf.continuous.sub hr.continuous).aestronglyMeasurable)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hdv := eLpNorm_add_le (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (((hf.continuous_deriv (by simp)).sub
      (hl.continuous_deriv (by simp))).aestronglyMeasurable)
    (((hf.continuous_deriv (by simp)).sub
      (hr.continuous_deriv (by simp))).aestronglyMeasurable)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hleft' : eLpNorm (f - l) 2 (volume.restrict (Ioo (0 : ℝ) 1)) +
      eLpNorm (deriv f - deriv l) 2 (volume.restrict (Ioo (0 : ℝ) 1)) <
        ENNReal.ofReal (ε / 2) := by
    have hs : Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun _ hx => hx.1
    exact (add_le_add
      (eLpNorm_mono_measure _ (Measure.restrict_mono hs le_rfl))
      (eLpNorm_mono_measure _ (Measure.restrict_mono hs le_rfl))).trans_lt
        (by simpa only [f, l, hdf] using hleft)
  have hright' : eLpNorm (f - r) 2 (volume.restrict (Ioo (0 : ℝ) 1)) +
      eLpNorm (deriv f - deriv r) 2 (volume.restrict (Ioo (0 : ℝ) 1)) <
        ENNReal.ofReal (ε / 2) := by
    have hs : Ioo (0 : ℝ) 1 ⊆ Iio (1 : ℝ) := fun _ hx => hx.2
    exact (add_le_add
      (eLpNorm_mono_measure _ (Measure.restrict_mono hs le_rfl))
      (eLpNorm_mono_measure _ (Measure.restrict_mono hs le_rfl))).trans_lt
        (by simpa only [f, r, hdf] using hright)
  calc
    _ ≤ (eLpNorm (f - l) 2 (volume.restrict (Ioo (0 : ℝ) 1)) +
          eLpNorm (f - r) 2 (volume.restrict (Ioo (0 : ℝ) 1))) +
        (eLpNorm (deriv f - deriv l) 2 (volume.restrict (Ioo (0 : ℝ) 1)) +
          eLpNorm (deriv f - deriv r) 2 (volume.restrict (Ioo (0 : ℝ) 1))) :=
      add_le_add hv hdv
    _ = (eLpNorm (f - l) 2 (volume.restrict (Ioo (0 : ℝ) 1)) +
          eLpNorm (deriv f - deriv l) 2 (volume.restrict (Ioo (0 : ℝ) 1))) +
        (eLpNorm (f - r) 2 (volume.restrict (Ioo (0 : ℝ) 1)) +
          eLpNorm (deriv f - deriv r) 2 (volume.restrict (Ioo (0 : ℝ) 1))) := by
      simp only [add_assoc]
      congr 1
      exact add_left_comm _ _ _
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      ENNReal.add_lt_add hleft' hright'
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ ε / 2) (by positivity : 0 ≤ ε / 2)]
      congr
      ring

lemma apm_m02j02_oddHermite_inH10 (n : ℕ) :
    apm_m02j02_InH10 (Ioi (0 : ℝ))
      (apm_m02j02_hermiteFunction (2 * n + 1))
      (apm_m02j02_hermiteFunctionDeriv (2 * n + 1)) := by
  apply apm_m02j02_oddHermite_inH10_of_approx n
  intro ε hε
  obtain ⟨δ, hδ, -, hinner⟩ :=
    apm_m02j02_exists_oddHermite_innerCutoff_graph_close n
      (show 0 < ε / 2 by positivity)
  let f : ℝ → ℝ := apm_m02j02_hermiteFunction (2 * n + 1)
  let g : ℝ → ℝ := fun x => Real.smoothTransition ((x - δ) / δ) * f x
  have hf : ContDiff ℝ ∞ f := apm_m02j02_hermiteFunction_contDiff _
  have hg : ContDiff ℝ ∞ g :=
    (@Real.smoothTransition.contDiff (⊤ : ℕ∞)).comp (by fun_prop) |>.mul hf
  obtain ⟨hgLp, hdgLp⟩ := apm_m02j02_innerCutoff_memLp_pair hf
    (apm_m02j02_hermiteFunction_memLp_two _) 
    (apm_m02j02_hermiteFunctionDeriv_memLp_two _) hδ
  obtain ⟨φ, hφsmooth, hφcomp, hφsub, houter⟩ :=
    apm_m02j02_exists_compact_graph_approx hg hgLp hdgLp
      (show 0 < ε / 2 by positivity)
  have hgsub : tsupport g ⊆ Ioi (0 : ℝ) := by
    exact tsupport_mul_subset_left.trans
      ((apm_m02j02_tsupport_smoothTransition_affine_subset_Ici hδ).trans
        (fun _ hx => hδ.trans_le hx))
  refine ⟨φ, hφsmooth, hφcomp, hφsub.trans hgsub, ?_⟩
  have htri := apm_m02j02_graphNorm_sub_triangle_Ioi
    f (deriv f) g (deriv g) φ (deriv φ)
    hf.continuous (hf.continuous_deriv (by simp)) hg.continuous
    (hg.continuous_deriv (by simp)) hφsmooth.continuous
    (hφsmooth.continuous_deriv (by simp))
  change eLpNorm (f - φ) 2 (volume.restrict (Ioi (0 : ℝ))) +
      eLpNorm (deriv f - deriv φ) 2 (volume.restrict (Ioi (0 : ℝ))) < _
  calc
    _ ≤ (eLpNorm (f - g) 2 (volume.restrict (Ioi (0 : ℝ))) +
          eLpNorm (deriv f - deriv g) 2 (volume.restrict (Ioi (0 : ℝ)))) +
        (eLpNorm (g - φ) 2 (volume.restrict (Ioi (0 : ℝ))) +
          eLpNorm (deriv g - deriv φ) 2 (volume.restrict (Ioi (0 : ℝ)))) := htri
    _ ≤ (eLpNorm (f - g) 2 (volume.restrict (Ioi (0 : ℝ))) +
          eLpNorm (deriv f - deriv g) 2 (volume.restrict (Ioi (0 : ℝ)))) +
        (eLpNorm (g - φ) 2 volume + eLpNorm (deriv g - deriv φ) 2 volume) :=
      add_le_add le_rfl (apm_m02j02_graphNorm_restrict_Ioi_le (g - φ)
        (deriv g - deriv φ))
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      ENNReal.add_lt_add hinner houter
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ ε / 2) (by positivity : 0 ≤ ε / 2)]
      congr
      linarith

lemma apm_m02j02_oddHermiteDeriv_neg (n : ℕ) (x : ℝ) :
    apm_m02j02_hermiteFunctionDeriv (2 * n + 1) (-x) =
      apm_m02j02_hermiteFunctionDeriv (2 * n + 1) x := by
  rw [apm_m02j02_hermiteFunctionDeriv_recurrence,
    apm_m02j02_hermiteFunctionDeriv_recurrence,
    apm_m02j02_oddHermite_neg,
    apm_m02j02_hermiteFunction_neg]
  rw [show (-1 : ℝ) ^ (2 * n + 1 + 1) = 1 by
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul]
    norm_num]
  ring

lemma apm_m02j02_integral_eq_two_mul_Ioi_of_even
    {f : ℝ → ℝ} (hf : Integrable f volume)
    (heven : ∀ x : ℝ, f (-x) = f x) :
    (∫ x : ℝ, f x) = 2 * ∫ x : ℝ in Ioi 0, f x := by
  have hreflect : (∫ x : ℝ in Iic 0, f x) = ∫ x : ℝ in Ioi 0, f x := by
    calc
      _ = ∫ x : ℝ in Ioi 0, f (-x) := by
        simpa using (integral_comp_neg_Ioi (c := (0 : ℝ)) f).symm
      _ = _ := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x _
        exact heven x
  have hsplit := MeasureTheory.integral_add_compl
    (s := Ioi (0 : ℝ)) measurableSet_Ioi hf
  rw [compl_Ioi, hreflect] at hsplit
  linarith

lemma apm_m02j02_integral_eq_zero_of_odd
    {f : ℝ → ℝ} (hf : Integrable f volume)
    (hodd : ∀ x : ℝ, f (-x) = -f x) :
    (∫ x : ℝ, f x) = 0 := by
  have hreflect : (∫ x : ℝ in Iic 0, f x) = -∫ x : ℝ in Ioi 0, f x := by
    calc
      _ = ∫ x : ℝ in Ioi 0, f (-x) := by
        simpa using (integral_comp_neg_Ioi (c := (0 : ℝ)) f).symm
      _ = ∫ x : ℝ in Ioi 0, -f x := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x _
        exact hodd x
      _ = _ := by rw [MeasureTheory.integral_neg]
  have hsplit := MeasureTheory.integral_add_compl
    (s := Ioi (0 : ℝ)) measurableSet_Ioi hf
  rw [compl_Ioi, hreflect] at hsplit
  linarith

lemma apm_m02j02_evenHermite_neg (n : ℕ) (x : ℝ) :
    apm_m02j02_hermiteFunction (2 * n) (-x) =
      apm_m02j02_hermiteFunction (2 * n) x := by
  rw [apm_m02j02_hermiteFunction_neg]
  rw [pow_mul]
  norm_num

lemma apm_m02j02_integral_odd_mul_evenHermite_eq_zero
    {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hodd : ∀ x : ℝ, f (-x) = -f x) (n : ℕ) :
    (∫ x : ℝ, f x * apm_m02j02_hermiteFunction (2 * n) x) = 0 := by
  apply apm_m02j02_integral_eq_zero_of_odd
    (hf.integrable_mul (apm_m02j02_hermiteFunction_memLp_two (2 * n)))
  intro x
  simp only [Pi.mul_apply]
  rw [hodd, apm_m02j02_evenHermite_neg]
  ring

lemma apm_m02j02_normalizedHermiteCoefficient_even_eq_zero_of_odd
    {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hodd : ∀ x : ℝ, f (-x) = -f x) (n : ℕ) :
    apm_m02j02_normalizedHermiteCoefficient f (2 * n) = 0 := by
  rw [apm_m02j02_normalizedHermiteCoefficient,
    apm_m02j02_integral_odd_mul_evenHermite_eq_zero hf hodd n, zero_div]

lemma apm_m02j02_exists_oddHermite_coefficients_projection
    {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hodd : ∀ x : ℝ, f (-x) = -f x) (N : ℕ) :
    ∃ c : ℕ →₀ ℝ,
      apm_m02j02_normalizedHermiteProjection
          (apm_m02j02_normalizedHermiteCoefficient f) N =
        (c.sum fun n a ↦ a • apm_m02j02_hermiteFunction (2 * n + 1)) ∧
      apm_m02j02_normalizedHermiteDerivProjection
          (apm_m02j02_normalizedHermiteCoefficient f) N =
        (c.sum fun n a ↦ a • apm_m02j02_hermiteFunctionDeriv (2 * n + 1)) := by
  have hmem : apm_m02j02_normalizedHermiteProjection
        (apm_m02j02_normalizedHermiteCoefficient f) N ∈
      Submodule.span ℝ
        (Set.range (fun n ↦ apm_m02j02_hermiteFunction (2 * n + 1))) := by
    rw [show apm_m02j02_normalizedHermiteProjection
          (apm_m02j02_normalizedHermiteCoefficient f) N =
        ∑ n ∈ Finset.range N,
          (apm_m02j02_normalizedHermiteCoefficient f n /
            Real.sqrt (∫ y : ℝ, apm_m02j02_hermiteFunction n y ^ 2)) •
              apm_m02j02_hermiteFunction n by
      funext x
      simp only [apm_m02j02_normalizedHermiteProjection,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro n hn
      ring]
    apply Submodule.sum_mem
    intro n hn
    by_cases he : Even n
    · obtain ⟨j, rfl⟩ := he
      have hz := apm_m02j02_normalizedHermiteCoefficient_even_eq_zero_of_odd hf hodd j
      simp only [two_mul] at hz
      rw [hz]
      simp
    · obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.mp he
      rw [hj]
      simp only [two_mul]
      apply Submodule.smul_mem
      exact Submodule.subset_span (Set.mem_range_self j)
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
  refine ⟨c, hc.symm, ?_⟩
  have hdc : (fun x => deriv
      (c.sum fun n a ↦ a • apm_m02j02_hermiteFunction (2 * n + 1)) x) =
      c.sum fun n a ↦ a • apm_m02j02_hermiteFunctionDeriv (2 * n + 1) := by
    funext x
    rw [Finsupp.sum, Finsupp.sum]
    rw [show (∑ n ∈ c.support,
          c n • apm_m02j02_hermiteFunction (2 * n + 1)) =
        (fun y ↦ ∑ n ∈ c.support,
          c n * apm_m02j02_hermiteFunction (2 * n + 1) y) by
      funext y
      simp]
    rw [show (∑ n ∈ c.support,
          c n • apm_m02j02_hermiteFunctionDeriv (2 * n + 1)) =
        (fun y ↦ ∑ n ∈ c.support,
          c n * apm_m02j02_hermiteFunctionDeriv (2 * n + 1) y) by
      funext y
      simp]
    exact HasDerivAt.deriv (HasDerivAt.fun_sum (u := c.support)
      (A := fun n ↦ c n • apm_m02j02_hermiteFunction (2 * n + 1))
      (A' := fun n ↦ c n * apm_m02j02_hermiteFunctionDeriv (2 * n + 1) x)
      (fun n _ ↦ (apm_m02j02_hermiteFunction_hasDerivAt (2 * n + 1) x).const_mul
        (c n)))
  rw [← hdc, hc]
  funext x
  exact (apm_m02j02_deriv_sum_range_normalized_hermite
    (apm_m02j02_normalizedHermiteCoefficient f) N x).symm

lemma apm_m02j02_oddHermite_gram_Ioi (m n : ℕ) :
    (∫ x : ℝ in Ioi 0,
      apm_m02j02_hermiteFunction (2 * m + 1) x *
        apm_m02j02_hermiteFunction (2 * n + 1) x) =
      (if m = n then
        (((2 * n + 1).factorial : ℝ) *
          Real.sqrt (Real.pi / (1 / 2 : ℝ))) / 2
       else 0) := by
  let f := fun x : ℝ =>
    apm_m02j02_hermiteFunction (2 * m + 1) x *
      apm_m02j02_hermiteFunction (2 * n + 1) x
  have hf : Integrable f volume :=
    (apm_m02j02_hermiteFunction_memLp_two (2 * m + 1)).integrable_mul
      (apm_m02j02_hermiteFunction_memLp_two (2 * n + 1))
  have heven : ∀ x : ℝ, f (-x) = f x := by
    intro x
    simp only [f, apm_m02j02_oddHermite_neg]
    ring
  have hhalf := apm_m02j02_integral_eq_two_mul_Ioi_of_even hf heven
  have hfull : (∫ x : ℝ, f x) =
      if m = n then
        ((2 * n + 1).factorial : ℝ) *
          Real.sqrt (Real.pi / (1 / 2 : ℝ))
      else 0 := by
    dsimp [f]
    rw [apm_m02j02_hermite_gram]
    by_cases hmn : m = n
    · subst m
      simp
    · rw [if_neg hmn, if_neg (by omega)]
  rw [hfull] at hhalf
  by_cases hmn : m = n
  · subst m
    dsimp [f] at hhalf
    simp at hhalf ⊢
    linarith
  · simp only [if_neg hmn] at hhalf ⊢
    dsimp [f] at hhalf
    linarith

/-- Simultaneous graph-norm approximation by one polynomial times the frozen
Gaussian gives the exact finite Hermite-pair approximation required by the
basis predicate.  All coefficient matching is discharged here. -/
lemma apm_m02j02_hermite_pair_approx_of_weightedEval_approx
    (μ : Measure ℝ) (φ : ℝ → ℝ) (ε : ℝ)
    (happrox : ∃ p : ℝ[X],
      eLpNorm (φ - apm_m02j02_weightedEval p) 2 μ +
        eLpNorm ((deriv φ) -
          (fun x ↦ deriv (apm_m02j02_weightedEval p) x)) 2 μ <
            ENNReal.ofReal ε) :
    ∃ c : ℕ →₀ ℝ,
      eLpNorm (φ - c.sum fun n a ↦ a • apm_m02j02_hermiteFunction n) 2 μ +
        eLpNorm ((deriv φ) -
          c.sum fun n a ↦ a • apm_m02j02_hermiteFunctionDeriv n) 2 μ <
            ENNReal.ofReal ε := by
  obtain ⟨p, hp⟩ := happrox
  obtain ⟨c, hcval, hcderiv⟩ :=
    apm_m02j02_exists_hermite_coefficients_weightedEval p
  refine ⟨c, ?_⟩
  rw [← hcval, ← hcderiv]
  exact hp

lemma apm_m02j02_fourierLp_finset_sum_ae
    (a : ℤ → ℂ) (s : Finset ℤ) :
    (↑↑(∑ n ∈ s, a n • (@fourierLp (2 : ℝ) _ 2 _ n)) :
        AddCircle (2 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      (fun x ↦ ∑ n ∈ s, a n * (@fourier (2 : ℝ) n x)) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using
      (Lp.coeFn_zero ℂ 2
        (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))))
  | @insert n s hn ih =>
      simp only [Finset.sum_insert hn]
      filter_upwards [ih, coeFn_fourierLp 2 n,
        Lp.coeFn_smul (a n) (@fourierLp (2 : ℝ) _ 2 _ n),
        Lp.coeFn_add (a n • (@fourierLp (2 : ℝ) _ 2 _ n))
          (∑ i ∈ s, a i • (@fourierLp (2 : ℝ) _ 2 _ i))]
          with x hs hx hsm hadd
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hsm hadd ⊢
      rw [hadd, hsm, hx, hs]

lemma apm_m02j02_fourierPolynomial_memLp_toLp
    (a : ℤ → ℂ) (s : Finset ℤ) :
    ∃ h : MemLp (fun x : AddCircle (2 : ℝ) ↦
        ∑ n ∈ s, a n * (@fourier (2 : ℝ) n x)) 2
          AddCircle.haarAddCircle,
      h.toLp (fun x : AddCircle (2 : ℝ) ↦
        ∑ n ∈ s, a n * (@fourier (2 : ℝ) n x)) =
        ∑ n ∈ s, a n • (@fourierLp (2 : ℝ) _ 2 _ n) := by
  let U : Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))) :=
    ∑ n ∈ s, a n • (@fourierLp (2 : ℝ) _ 2 _ n)
  have hae : (↑↑U : AddCircle (2 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      (fun x ↦ ∑ n ∈ s, a n * (@fourier (2 : ℝ) n x)) := by
    exact apm_m02j02_fourierLp_finset_sum_ae a s
  have hp : MemLp (fun x : AddCircle (2 : ℝ) ↦
      ∑ n ∈ s, a n * (@fourier (2 : ℝ) n x)) 2
        AddCircle.haarAddCircle :=
    (memLp_congr_ae hae).mp (Lp.memLp U)
  refine ⟨hp, ?_⟩
  calc
    hp.toLp _ = (Lp.memLp U).toLp (↑↑U) :=
      MemLp.toLp_congr hp (Lp.memLp U) hae.symm
    _ = U := Lp.toLp_coeFn U (Lp.memLp U)

lemma apm_m02j02_edist_fourierLp_sum_eq_eLpNorm
    (a : ℤ → ℂ) (s : Finset ℤ) (f : AddCircle (2 : ℝ) → ℂ)
    (hf : MemLp f 2 AddCircle.haarAddCircle) :
    edist (∑ n ∈ s, a n • (@fourierLp (2 : ℝ) _ 2 _ n))
        (hf.toLp f) =
      eLpNorm ((fun x : AddCircle (2 : ℝ) ↦
        ∑ n ∈ s, a n * (@fourier (2 : ℝ) n x)) - f) 2
          AddCircle.haarAddCircle := by
  obtain ⟨hp, hto⟩ := apm_m02j02_fourierPolynomial_memLp_toLp a s
  rw [← hto]
  exact Lp.edist_toLp_toLp _ _ hp hf

lemma apm_m02j02_exists_common_symmetric_fourier_eLpNorm
    (f g : AddCircle (2 : ℝ) → ℂ)
    (hf : MemLp f 2 AddCircle.haarAddCircle)
    (hg : MemLp g 2 AddCircle.haarAddCircle)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ N : ℕ,
      eLpNorm ((fun x : AddCircle (2 : ℝ) ↦
          ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
            fourierCoeff (hf.toLp f) n * (@fourier (2 : ℝ) n x)) - f)
          2 AddCircle.haarAddCircle < ε ∧
      eLpNorm ((fun x : AddCircle (2 : ℝ) ↦
          ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
            fourierCoeff (hg.toLp g) n * (@fourier (2 : ℝ) n x)) - g)
          2 AddCircle.haarAddCircle < ε := by
  obtain ⟨N, hNf, hNg⟩ :=
    apm_m02j02_exists_common_symmetric_fourier_truncation
      (hf.toLp f) (hg.toLp g) ε hε
  refine ⟨N, ?_, ?_⟩
  · rw [← apm_m02j02_edist_fourierLp_sum_eq_eLpNorm
      (fun n ↦ fourierCoeff (hf.toLp f) n)
      (Finset.Icc (-(N : ℤ)) N) f hf]
    exact hNf
  · rw [← apm_m02j02_edist_fourierLp_sum_eq_eLpNorm
      (fun n ↦ fourierCoeff (hg.toLp g) n)
      (Finset.Icc (-(N : ℤ)) N) g hg]
    exact hNg

lemma apm_m02j02_exists_oddExtension_symmetric_fourier_eLpNorm
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    let F : ℝ → ℝ := fun x ↦ φ x - φ (-x)
    let FC : ℝ → ℂ := fun x ↦ (F x : ℂ)
    let DC : ℝ → ℂ := fun x ↦ ((deriv F x : ℝ) : ℂ)
    ∃ (hFC : MemLp (AddCircle.liftIoc 2 (-1) FC) 2
          (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))))
      (hDC : MemLp (AddCircle.liftIoc 2 (-1) DC) 2
          (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))))
      (N : ℕ),
      eLpNorm ((fun x : AddCircle (2 : ℝ) ↦
          ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
            fourierCoeff (hFC.toLp (AddCircle.liftIoc 2 (-1) FC)) n *
              (@fourier (2 : ℝ) n x)) - AddCircle.liftIoc 2 (-1) FC)
          2 AddCircle.haarAddCircle < ε ∧
      eLpNorm ((fun x : AddCircle (2 : ℝ) ↦
          ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
            fourierCoeff (hDC.toLp (AddCircle.liftIoc 2 (-1) DC)) n *
              (@fourier (2 : ℝ) n x)) - AddCircle.liftIoc 2 (-1) DC)
          2 AddCircle.haarAddCircle < ε := by
  dsimp only
  obtain ⟨hFC, hDC⟩ := apm_m02j02_oddExtension_liftIoc_memLp_pair hφ hφc
  obtain ⟨N, hN⟩ := apm_m02j02_exists_common_symmetric_fourier_eLpNorm
    _ _ hFC hDC ε hε
  exact ⟨hFC, hDC, N, hN⟩

lemma apm_m02j02_exists_sine_finsupp_eq_lifted_fourier_sum
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hodd : ∀ x : ℝ, f (-x) = -f x)
    (hFC : MemLp (AddCircle.liftIoc 2 (-1) (fun x : ℝ ↦ (f x : ℂ))) 2
      (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))))
    (N : ℕ) :
    ∃ c : ℕ →₀ ℝ,
      ∀ x : ℝ,
        ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
            fourierCoeff
                (hFC.toLp (AddCircle.liftIoc 2 (-1)
                  (fun y : ℝ ↦ (f y : ℂ)))) n *
              (@fourier (2 : ℝ) n (x : AddCircle (2 : ℝ))) =
          ((c.sum (fun k a ↦ a • apm_m02j02_sine k) x : ℝ) : ℂ) := by
  obtain ⟨c, hc, _⟩ :=
    apm_m02j02_exists_sine_finsupp_for_fourier_coefficients f N
  refine ⟨c, fun x ↦ ?_⟩
  calc
    _ = ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
              (fun y : ℝ ↦ (f y : ℂ)) n *
            (@fourier (2 : ℝ) n (x : AddCircle (2 : ℝ))) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [apm_m02j02_fourierCoeff_toLp_liftIoc_eq_on]
    _ = ∑ k ∈ Finset.range N,
          (((-2 * (fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
            (fun y : ℝ ↦ (f y : ℂ)) ((k + 1 : ℕ) : ℤ)).im : ℝ) : ℂ) *
              (Real.sin ((k + 1 : ℝ) * Real.pi * x) : ℂ)) :=
        apm_m02j02_odd_fourier_symmetric_sum_eq_sine_sum hf hodd N x
    _ = ((c.sum (fun k a ↦ a • apm_m02j02_sine k) x : ℝ) : ℂ) := by
        rw [hc]
        push_cast
        rfl

lemma apm_m02j02_odd_fourier_deriv_pair_eq_sineDeriv
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hodd : ∀ x : ℝ, f (-x) = -f x) (n : ℤ) (x : ℝ) :
    ((Real.pi : ℂ) * Complex.I * n) *
          fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
            (fun y : ℝ ↦ (f y : ℂ)) n *
          (@fourier (2 : ℝ) n (x : AddCircle (2 : ℝ))) +
      ((Real.pi : ℂ) * Complex.I * (-n)) *
          fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
            (fun y : ℝ ↦ (f y : ℂ)) (-n) *
          (@fourier (2 : ℝ) (-n) (x : AddCircle (2 : ℝ))) =
      ((-2 * (fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
          (fun y : ℝ ↦ (f y : ℂ)) n).im *
        (Real.pi * (n : ℝ)) * Real.cos (Real.pi * (n : ℝ) * x) : ℝ) : ℂ) := by
  rw [apm_m02j02_fourierCoeffOn_neg_eq_neg_of_odd hf hodd n]
  rw [apm_m02j02_fourierCoeffOn_odd_eq_im_mul_I hf hodd n]
  rw [fourier_coe_apply, fourier_coe_apply]
  have hp :
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) / 2 =
        ((Real.pi * (n : ℝ) * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hn :
      -(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)) / 2 =
        ((-(Real.pi * (n : ℝ) * x) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  norm_num
  rw [hp, hn, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma apm_m02j02_odd_fourier_deriv_symmetric_sum_eq_sineDeriv_sum
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hodd : ∀ x : ℝ, f (-x) = -f x) (N : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        (((Real.pi : ℂ) * Complex.I * n) *
          fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
            (fun y : ℝ ↦ (f y : ℂ)) n) *
          (@fourier (2 : ℝ) n (x : AddCircle (2 : ℝ))) =
      ∑ k ∈ Finset.range N,
        (((-2 * (fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
          (fun y : ℝ ↦ (f y : ℂ)) ((k + 1 : ℕ) : ℤ)).im : ℝ) : ℂ) *
          ((((k + 1 : ℝ) * Real.pi) *
            Real.cos ((k + 1 : ℝ) * Real.pi * x) : ℝ) : ℂ)) := by
  apply apm_m02j02_sum_symmetricIcc_eq_sum_range_pairs
  · simp
  · intro k
    have h := apm_m02j02_odd_fourier_deriv_pair_eq_sineDeriv hf hodd
      ((k + 1 : ℕ) : ℤ) x
    convert h using 1 <;> push_cast <;> ring

lemma apm_m02j02_exists_sine_finsupp_eq_lifted_fourier_sum_pair
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hsub : tsupport f ⊆ Ioo (-1 : ℝ) 1)
    (hodd : ∀ x : ℝ, f (-x) = -f x)
    (hFC : MemLp (AddCircle.liftIoc 2 (-1) (fun x : ℝ ↦ (f x : ℂ))) 2
      (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))))
    (hDC : MemLp (AddCircle.liftIoc 2 (-1)
        (fun x : ℝ ↦ ((deriv f x : ℝ) : ℂ))) 2
      (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))))
    (N : ℕ) :
    ∃ c : ℕ →₀ ℝ,
      (∀ x : ℝ,
        ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
            fourierCoeff (hFC.toLp (AddCircle.liftIoc 2 (-1)
              (fun y : ℝ ↦ (f y : ℂ)))) n *
              (@fourier (2 : ℝ) n (x : AddCircle (2 : ℝ))) =
          ((c.sum (fun k a ↦ a • apm_m02j02_sine k) x : ℝ) : ℂ)) ∧
      (∀ x : ℝ,
        ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
            fourierCoeff (hDC.toLp (AddCircle.liftIoc 2 (-1)
              (fun y : ℝ ↦ ((deriv f y : ℝ) : ℂ)))) n *
              (@fourier (2 : ℝ) n (x : AddCircle (2 : ℝ))) =
          ((c.sum (fun k a ↦ a • apm_m02j02_sineDeriv k) x : ℝ) : ℂ)) := by
  obtain ⟨c, hcval, hcderiv⟩ :=
    apm_m02j02_exists_sine_finsupp_for_fourier_coefficients f N
  refine ⟨c, ?_, ?_⟩
  · intro x
    calc
      _ = ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
            (fun y : ℝ ↦ (f y : ℂ)) n *
              (@fourier (2 : ℝ) n (x : AddCircle (2 : ℝ))) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [apm_m02j02_fourierCoeff_toLp_liftIoc_eq_on]
      _ = _ := by
        rw [apm_m02j02_odd_fourier_symmetric_sum_eq_sine_sum hf hodd N x]
        rw [hcval]
        push_cast
        rfl
  · intro x
    calc
      _ = ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          (((Real.pi : ℂ) * Complex.I * n) *
            fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
              (fun y : ℝ ↦ (f y : ℂ)) n) *
              (@fourier (2 : ℝ) n (x : AddCircle (2 : ℝ))) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [apm_m02j02_fourierCoeff_toLp_liftIoc_deriv_eq_mul
              hf hsub hFC hDC]
            rw [apm_m02j02_fourierCoeff_toLp_liftIoc_eq_on]
      _ = _ := by
        rw [apm_m02j02_odd_fourier_deriv_symmetric_sum_eq_sineDeriv_sum
          hf hodd N x]
        rw [hcderiv]
        push_cast
        apply Finset.sum_congr rfl
        intro k hk
        ring

lemma apm_m02j02_deriv_eq_zero_at_neg_of_tsupport_subset_Ioi
    {f : ℝ → ℝ} (hsub : tsupport f ⊆ Ioi (0 : ℝ))
    {x : ℝ} (hx : 0 < x) : deriv f (-x) = 0 := by
  have hnmem : -x ∉ tsupport f := by
    intro hmem
    have := hsub hmem
    simp only [Set.mem_Ioi] at this
    linarith
  have hopen : IsOpen ((tsupport f)ᶜ) := isClosed_closure.isOpen_compl
  have hpoint : -x ∈ (tsupport f)ᶜ := hnmem
  have hevset : Filter.Eventually (fun y ↦ y ∈ (tsupport f)ᶜ) (nhds (-x)) :=
    hopen.mem_nhds hpoint
  have hev : f =ᶠ[nhds (-x)] (fun _ : ℝ ↦ 0) := by
    filter_upwards [hevset] with y hy
    have hzero : f y = 0 := by
      by_contra hne
      exact hy (subset_closure hne)
    exact hzero
  simpa using hev.deriv_eq

lemma apm_m02j02_deriv_oddExtension_eq_of_pos
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hsub : tsupport f ⊆ Ioi (0 : ℝ))
    {x : ℝ} (hx : 0 < x) :
    deriv (fun y : ℝ ↦ f y - f (-y)) x = deriv f x := by
  rw [apm_m02j02_deriv_oddExtension hf,
    apm_m02j02_deriv_eq_zero_at_neg_of_tsupport_subset_Ioi hsub hx, add_zero]

lemma apm_m02j02_eLpNorm_complexification_eq
    (u : ℝ → ℝ) (p : ℝ≥0∞) (μ : Measure ℝ) :
    eLpNorm (fun x ↦ (u x : ℂ)) p μ = eLpNorm u p μ := by
  apply eLpNorm_congr_norm_ae
  filter_upwards with x
  simp

lemma apm_m02j02_eLpNorm_complex_sub_eq
    (u v : ℝ → ℝ) (p : ℝ≥0∞) (μ : Measure ℝ) :
    eLpNorm (fun x ↦ (u x : ℂ) - (v x : ℂ)) p μ =
      eLpNorm (u - v) p μ := by
  rw [← apm_m02j02_eLpNorm_complexification_eq (u - v) p μ]
  apply eLpNorm_congr_ae
  filter_upwards with x
  simp

lemma apm_m02j02_eLpNorm_complex_sub_rev_eq
    (u v : ℝ → ℝ) (p : ℝ≥0∞) (μ : Measure ℝ) :
    eLpNorm (fun x ↦ (v x : ℂ) - (u x : ℂ)) p μ =
      eLpNorm (u - v) p μ := by
  apply eLpNorm_congr_norm_ae
  filter_upwards with x
  rw [show (v x : ℂ) - (u x : ℂ) = ((v x - u x : ℝ) : ℂ) by
    push_cast; rfl]
  simp only [Complex.norm_real, Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm]

lemma apm_m02j02_eLpNorm_oddExtension_sub_eq_on_Ioo
    {f E : ℝ → ℝ} (hsub : tsupport f ⊆ Ioi (0 : ℝ)) :
    eLpNorm (f - E) 2 (volume.restrict (Ioo (0 : ℝ) 1)) =
      eLpNorm (fun x ↦ (E x : ℂ) - ((f x - f (-x) : ℝ) : ℂ)) 2
        (volume.restrict (Ioo (0 : ℝ) 1)) := by
  apply eLpNorm_congr_norm_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [apm_m02j02_oddExtension_eq_of_pos hsub hx.1]
  simp only [Pi.sub_apply]
  rw [show (E x : ℂ) - (f x : ℂ) = ((E x - f x : ℝ) : ℂ) by
    push_cast; rfl]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]

lemma apm_m02j02_eLpNorm_derivOddExtension_sub_eq_on_Ioo
    {f E : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hsub : tsupport f ⊆ Ioi (0 : ℝ)) :
    eLpNorm (deriv f - E) 2 (volume.restrict (Ioo (0 : ℝ) 1)) =
      eLpNorm (fun x ↦ (E x : ℂ) -
        ((deriv (fun y : ℝ ↦ f y - f (-y)) x : ℝ) : ℂ)) 2
          (volume.restrict (Ioo (0 : ℝ) 1)) := by
  apply eLpNorm_congr_norm_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [apm_m02j02_deriv_oddExtension_eq_of_pos hf hsub hx.1]
  simp only [Pi.sub_apply]
  change ‖deriv f x - E x‖ = ‖(E x : ℂ) - ((deriv f x : ℝ) : ℂ)‖
  calc
    ‖deriv f x - E x‖ = |deriv f x - E x| := Real.norm_eq_abs _
    _ = |E x - deriv f x| := abs_sub_comm _ _
    _ = ‖((E x - deriv f x : ℝ) : ℂ)‖ := (Complex.norm_real _).symm
    _ = ‖(E x : ℂ) - ((deriv f x : ℝ) : ℂ)‖ := by push_cast; rfl

lemma apm_m02j02_sine_basis_of_testFunction_density
    (htest : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (0 : ℝ) 1 → ∀ ε : ℝ, 0 < ε → ∃ c : ℕ →₀ ℝ,
        eLpNorm (φ - c.sum fun n a ↦ a • apm_m02j02_sine n) 2
            (volume.restrict (Ioo (0 : ℝ) 1)) +
          eLpNorm (deriv φ - c.sum fun n a ↦ a • apm_m02j02_sineDeriv n) 2
            (volume.restrict (Ioo (0 : ℝ) 1)) < ENNReal.ofReal ε) :
    apm_m02j02_IsH10Basis (Ioo (0 : ℝ) 1)
      apm_m02j02_sine apm_m02j02_sineDeriv := by
  refine ⟨apm_m02j02_sine_inH10,
    apm_m02j02_sinePair_linearIndependent, ?_⟩
  exact apm_m02j02_density_of_testFunction_density
    (Ioo (0 : ℝ) 1) apm_m02j02_sine apm_m02j02_sineDeriv
    (fun n ↦ (apm_m02j02_sine_contDiff n).continuous)
    (fun n ↦ (apm_m02j02_sineDeriv_contDiff n).continuous) htest

lemma apm_m02j02_two_error_budget
    (K ε A B : ℝ≥0∞) (hK0 : K ≠ 0) (hKtop : K ≠ ⊤)
    (hA : A < (ε / 2) / K) (hB : B < (ε / 2) / K) :
    K * A + K * B < ε := by
  have hc : (ε / 2) / K * K = ε / 2 := ENNReal.div_mul_cancel hK0 hKtop
  have ha : K * A < ε / 2 := by
    rw [mul_comm]
    exact (ENNReal.mul_lt_mul_left hK0 hKtop hA).trans_le hc.le
  have hb : K * B < ε / 2 := by
    rw [mul_comm]
    exact (ENNReal.mul_lt_mul_left hK0 hKtop hB).trans_le hc.le
  calc
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add ha hb
    _ = ε := by
      rw [← ENNReal.add_div, show ε + ε = 2 * ε by ring,
        ENNReal.div_eq_inv_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

lemma apm_m02j02_liftIoc_two_eq_of_coe_eq
    {E : Type*} (P : ℝ → E) (Q : AddCircle (2 : ℝ) → E)
    (h : ∀ x : ℝ, Q (x : AddCircle (2 : ℝ)) = P x) :
    AddCircle.liftIoc 2 (-1) P = Q := by
  funext q
  let r : Ioc (-1 : ℝ) (-1 + 2) := AddCircle.equivIoc 2 (-1) q
  have hq : ((r.1 : ℝ) : AddCircle (2 : ℝ)) = q := by
    exact (AddCircle.equivIoc 2 (-1)).symm_apply_apply q
  rw [← hq, AddCircle.liftIoc_coe_apply r.2, h]

lemma apm_m02j02_eLpNorm_restrict_Ioo_le_circle_of_coe_eq
    (P : ℝ → ℂ) (Q : AddCircle (2 : ℝ) → ℂ)
    (h : ∀ x : ℝ, Q (x : AddCircle (2 : ℝ)) = P x) :
    eLpNorm P 2 (volume.restrict (Ioo (0 : ℝ) 1)) ≤
      (ENNReal.ofReal 2) ^ (1 / 2 : ℝ) *
        eLpNorm Q 2 AddCircle.haarAddCircle := by
  rw [← apm_m02j02_liftIoc_two_eq_of_coe_eq P Q h]
  exact apm_m02j02_eLpNorm_restrict_Ioo_le_sqrtTwo_mul_liftIoc P

lemma apm_m02j02_eLpNorm_restrict_Ioo_le_circle_of_eq_on_Ioo
    (P : ℝ → ℂ) (Q : AddCircle (2 : ℝ) → ℂ)
    (h : ∀ x ∈ Ioo (0 : ℝ) 1, Q (x : AddCircle (2 : ℝ)) = P x) :
    eLpNorm P 2 (volume.restrict (Ioo (0 : ℝ) 1)) ≤
      (ENNReal.ofReal 2) ^ (1 / 2 : ℝ) *
        eLpNorm Q 2 AddCircle.haarAddCircle := by
  let R : ℝ → ℂ := fun x ↦ Q (x : AddCircle (2 : ℝ))
  have hPR : eLpNorm P 2 (volume.restrict (Ioo (0 : ℝ) 1)) =
      eLpNorm R 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (h x hx).symm
  rw [hPR]
  exact apm_m02j02_eLpNorm_restrict_Ioo_le_circle_of_coe_eq R Q (fun _ ↦ rfl)

lemma apm_m02j02_value_error_le_circle_fourier_error
    {φ : ℝ → ℝ} (hφsub : tsupport φ ⊆ Ioi (0 : ℝ))
    (F : ℝ → ℝ) (hF : ∀ x, F x = φ x - φ (-x))
    (hFC : MemLp (AddCircle.liftIoc 2 (-1) (fun x : ℝ ↦ (F x : ℂ))) 2
      (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))))
    (N : ℕ) (E : ℝ → ℝ)
    (hpoly : ∀ x : ℝ,
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          fourierCoeff (hFC.toLp (AddCircle.liftIoc 2 (-1)
            (fun y : ℝ ↦ (F y : ℂ)))) n *
            (@fourier (2 : ℝ) n (x : AddCircle (2 : ℝ))) = (E x : ℂ)) :
    eLpNorm (φ - E) 2 (volume.restrict (Ioo (0 : ℝ) 1)) ≤
      (ENNReal.ofReal 2) ^ (1 / 2 : ℝ) *
        eLpNorm ((fun q : AddCircle (2 : ℝ) ↦
          ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
            fourierCoeff (hFC.toLp (AddCircle.liftIoc 2 (-1)
              (fun y : ℝ ↦ (F y : ℂ)))) n * (@fourier (2 : ℝ) n q)) -
          AddCircle.liftIoc 2 (-1) (fun y : ℝ ↦ (F y : ℂ))) 2
            AddCircle.haarAddCircle := by
  let P : ℝ → ℂ := fun x ↦ (E x : ℂ) - (F x : ℂ)
  let Q : AddCircle (2 : ℝ) → ℂ :=
    (fun q ↦ ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
      fourierCoeff (hFC.toLp (AddCircle.liftIoc 2 (-1)
        (fun y : ℝ ↦ (F y : ℂ)))) n * (@fourier (2 : ℝ) n q)) -
      AddCircle.liftIoc 2 (-1) (fun y : ℝ ↦ (F y : ℂ))
  have hPQ : ∀ x ∈ Ioo (0 : ℝ) 1, Q (x : AddCircle (2 : ℝ)) = P x := by
    intro x hx
    dsimp [Q, P]
    have hs := hpoly x
    change (∑ n ∈ Finset.Icc (-(N : ℤ)) N,
      fourierCoeff (hFC.toLp (AddCircle.liftIoc 2 (-1)
        (fun y : ℝ ↦ (F y : ℂ)))) n *
        (@fourier (2 : ℝ) n (x : AddCircle (2 : ℝ)))) -
      AddCircle.liftIoc 2 (-1) (fun y : ℝ ↦ (F y : ℂ))
        (x : AddCircle (2 : ℝ)) = (E x : ℂ) - (F x : ℂ)
    rw [hs, AddCircle.liftIoc_coe_apply]
    constructor <;> linarith [hx.1, hx.2]
  have hle := apm_m02j02_eLpNorm_restrict_Ioo_le_circle_of_eq_on_Ioo P Q hPQ
  have hPfun : P = fun x ↦ (E x : ℂ) - ((φ x - φ (-x) : ℝ) : ℂ) := by
    funext x
    simp only [P, hF x]
  rw [hPfun, ← apm_m02j02_eLpNorm_oddExtension_sub_eq_on_Ioo hφsub] at hle
  exact hle

lemma apm_m02j02_deriv_error_le_circle_fourier_error
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφsub : tsupport φ ⊆ Ioi (0 : ℝ))
    (F : ℝ → ℝ) (hF : ∀ x, F x = φ x - φ (-x))
    (hDC : MemLp (AddCircle.liftIoc 2 (-1)
        (fun x : ℝ ↦ ((deriv F x : ℝ) : ℂ))) 2
      (AddCircle.haarAddCircle : Measure (AddCircle (2 : ℝ))))
    (N : ℕ) (D : ℝ → ℝ)
    (hpoly : ∀ x : ℝ,
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          fourierCoeff (hDC.toLp (AddCircle.liftIoc 2 (-1)
            (fun y : ℝ ↦ ((deriv F y : ℝ) : ℂ)))) n *
            (@fourier (2 : ℝ) n (x : AddCircle (2 : ℝ))) = (D x : ℂ)) :
    eLpNorm (deriv φ - D) 2 (volume.restrict (Ioo (0 : ℝ) 1)) ≤
      (ENNReal.ofReal 2) ^ (1 / 2 : ℝ) *
        eLpNorm ((fun q : AddCircle (2 : ℝ) ↦
          ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
            fourierCoeff (hDC.toLp (AddCircle.liftIoc 2 (-1)
              (fun y : ℝ ↦ ((deriv F y : ℝ) : ℂ)))) n *
              (@fourier (2 : ℝ) n q)) -
          AddCircle.liftIoc 2 (-1)
            (fun y : ℝ ↦ ((deriv F y : ℝ) : ℂ))) 2
            AddCircle.haarAddCircle := by
  let P : ℝ → ℂ := fun x ↦ (D x : ℂ) - ((deriv F x : ℝ) : ℂ)
  let Q : AddCircle (2 : ℝ) → ℂ :=
    (fun q ↦ ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
      fourierCoeff (hDC.toLp (AddCircle.liftIoc 2 (-1)
        (fun y : ℝ ↦ ((deriv F y : ℝ) : ℂ)))) n *
        (@fourier (2 : ℝ) n q)) -
      AddCircle.liftIoc 2 (-1) (fun y : ℝ ↦ ((deriv F y : ℝ) : ℂ))
  have hPQ : ∀ x ∈ Ioo (0 : ℝ) 1, Q (x : AddCircle (2 : ℝ)) = P x := by
    intro x hx
    dsimp [Q, P]
    have hs := hpoly x
    change (∑ n ∈ Finset.Icc (-(N : ℤ)) N,
      fourierCoeff (hDC.toLp (AddCircle.liftIoc 2 (-1)
        (fun y : ℝ ↦ ((deriv F y : ℝ) : ℂ)))) n *
        (@fourier (2 : ℝ) n (x : AddCircle (2 : ℝ)))) -
      AddCircle.liftIoc 2 (-1) (fun y : ℝ ↦ ((deriv F y : ℝ) : ℂ))
        (x : AddCircle (2 : ℝ)) = (D x : ℂ) - ((deriv F x : ℝ) : ℂ)
    rw [hs, AddCircle.liftIoc_coe_apply]
    constructor <;> linarith [hx.1, hx.2]
  have hle := apm_m02j02_eLpNorm_restrict_Ioo_le_circle_of_eq_on_Ioo P Q hPQ
  have hFeq : F = fun y : ℝ ↦ φ y - φ (-y) := funext hF
  have hPfun : P = fun x ↦ (D x : ℂ) -
      ((deriv (fun y : ℝ ↦ φ y - φ (-y)) x : ℝ) : ℂ) := by
    funext x
    simp only [P, hFeq]
  rw [hPfun, ← apm_m02j02_eLpNorm_derivOddExtension_sub_eq_on_Ioo
    hφ hφsub] at hle
  exact hle

lemma apm_m02j02_sine_testFunction_graph_dense
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφsub : tsupport φ ⊆ Ioo (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ →₀ ℝ,
      eLpNorm (φ - c.sum fun n a ↦ a • apm_m02j02_sine n) 2
          (volume.restrict (Ioo (0 : ℝ) 1)) +
        eLpNorm (deriv φ - c.sum fun n a ↦ a • apm_m02j02_sineDeriv n) 2
          (volume.restrict (Ioo (0 : ℝ) 1)) < ENNReal.ofReal ε := by
  let F : ℝ → ℝ := fun x ↦ φ x - φ (-x)
  let K : ℝ≥0∞ := (ENNReal.ofReal 2) ^ (1 / 2 : ℝ)
  let δ : ℝ≥0∞ := (ENNReal.ofReal ε / 2) / K
  have hK0 : K ≠ 0 := by simp [K]
  have hKtop : K ≠ ⊤ := by simp [K]
  have hδ : 0 < δ := by
    dsimp [δ]
    rw [ENNReal.div_pos_iff]
    constructor
    · rw [ENNReal.div_ne_zero]
      exact ⟨ne_of_gt (ENNReal.ofReal_pos.mpr hε), by norm_num⟩
    · exact hKtop
  obtain ⟨hFC, hDC, N, hNv, hNd⟩ :=
    apm_m02j02_exists_oddExtension_symmetric_fourier_eLpNorm hφ hφc δ hδ
  have hFsmooth : ContDiff ℝ ∞ F := apm_m02j02_oddExtension_contDiff hφ
  have hFsub : tsupport F ⊆ Ioo (-1 : ℝ) 1 :=
    apm_m02j02_oddExtension_tsupport_subset_Ioo hφsub
  have hFodd : ∀ x : ℝ, F (-x) = -F x := by
    intro x
    simp [F, apm_m02j02_oddExtension_neg]
  obtain ⟨c, hcval, hcderiv⟩ :=
    apm_m02j02_exists_sine_finsupp_eq_lifted_fourier_sum_pair
      hFsmooth hFsub hFodd hFC hDC N
  let E : ℝ → ℝ := c.sum fun n a ↦ a • apm_m02j02_sine n
  let D : ℝ → ℝ := c.sum fun n a ↦ a • apm_m02j02_sineDeriv n
  have hφIoi : tsupport φ ⊆ Ioi (0 : ℝ) := fun x hx ↦ (hφsub hx).1
  have hv := apm_m02j02_value_error_le_circle_fourier_error
    hφIoi F (fun _ ↦ rfl) hFC N E hcval
  have hd := apm_m02j02_deriv_error_le_circle_fourier_error
    (hφ.of_le (by simp)) hφIoi F (fun _ ↦ rfl) hDC N D hcderiv
  refine ⟨c, ?_⟩
  change eLpNorm (φ - E) 2 (volume.restrict (Ioo (0 : ℝ) 1)) +
      eLpNorm (deriv φ - D) 2 (volume.restrict (Ioo (0 : ℝ) 1)) <
        ENNReal.ofReal ε
  apply lt_of_le_of_lt (add_le_add hv hd)
  exact apm_m02j02_two_error_budget K (ENNReal.ofReal ε) _ _ hK0 hKtop hNv hNd

/-- Why this unblocks `apm_m02j02`: this is the exact Fourier-sine
completeness theorem in the custom weak-derivative and compactly-supported
graph-norm closure encoding used by the frozen statement. -/
theorem apm_m02J02_bridge_1 :
    apm_m02j02_IsH10Basis (Ioo (0 : ℝ) 1)
      apm_m02j02_sine apm_m02j02_sineDeriv := by
  exact apm_m02j02_sine_basis_of_testFunction_density
    apm_m02j02_sine_testFunction_graph_dense

/-- Why this unblocks `apm_m02j02`: this packages half-line `H¹₀`
membership, linear independence, and graph-norm density of the odd
Hermite--Gaussian family in the exact frozen predicate. -/
theorem apm_m02J02_bridge_2 :
    apm_m02j02_IsH10Basis (Ioi (0 : ℝ))
      (fun n ↦ apm_m02j02_hermiteFunction (2 * n + 1))
      (fun n ↦ apm_m02j02_hermiteFunctionDeriv (2 * n + 1)) := by
  apply apm_m02j02_oddHermite_basis_of_approx_density
    apm_m02j02_oddHermite_inH10
  apply apm_m02j02_density_of_testFunction_density (Ioi (0 : ℝ))
    (fun n ↦ apm_m02j02_hermiteFunction (2 * n + 1))
    (fun n ↦ apm_m02j02_hermiteFunctionDeriv (2 * n + 1))
    (fun n => (apm_m02j02_hermiteFunction_contDiff _).continuous)
    (fun n => apm_m02j02_hermiteFunctionDeriv_continuous _)
  intro φ hφsmooth hφcomp hφsub ε hε
  let ψ : ℝ → ℝ := fun x => φ x - φ (-x)
  have hψsmooth : ContDiff ℝ ∞ ψ :=
    apm_m02j02_oddExtension_contDiff hφsmooth
  have hψcomp : HasCompactSupport ψ :=
    apm_m02j02_oddExtension_hasCompactSupport hφcomp
  have hψodd : ∀ x : ℝ, ψ (-x) = -ψ x := by
    intro x
    exact apm_m02j02_oddExtension_neg φ x
  have hψeq : ∀ x : ℝ, 0 < x → ψ x = φ x := by
    intro x hx
    exact apm_m02j02_oddExtension_eq_of_pos hφsub hx
  have hdψeq : ∀ x : ℝ, 0 < x → deriv ψ x = deriv φ x := by
    intro x hx
    have heq : ψ =ᶠ[nhds x] φ := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact hψeq y hy
    exact heq.deriv_eq
  obtain ⟨N, hN⟩ :=
    apm_m02j02_exists_normalizedHermiteProjection_graph_close
      ψ hψsmooth hψcomp ε hε
  have hψLp : MemLp ψ 2 volume :=
    apm_m02j02_memLp_two_of_contDiff_compact ψ hψsmooth hψcomp
  obtain ⟨c, hcval, hcderiv⟩ :=
    apm_m02j02_exists_oddHermite_coefficients_projection hψLp hψodd N
  refine ⟨c, ?_⟩
  rw [← hcval, ← hcderiv]
  have hv : eLpNorm
      (φ - apm_m02j02_normalizedHermiteProjection
        (apm_m02j02_normalizedHermiteCoefficient ψ) N) 2
        (volume.restrict (Ioi (0 : ℝ))) =
      eLpNorm
      (ψ - apm_m02j02_normalizedHermiteProjection
        (apm_m02j02_normalizedHermiteCoefficient ψ) N) 2
        (volume.restrict (Ioi (0 : ℝ))) := by
    apply MeasureTheory.eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [Pi.sub_apply]
    rw [hψeq x hx]
  have hd : eLpNorm
      (deriv φ - apm_m02j02_normalizedHermiteDerivProjection
        (apm_m02j02_normalizedHermiteCoefficient ψ) N) 2
        (volume.restrict (Ioi (0 : ℝ))) =
      eLpNorm
      (deriv ψ - apm_m02j02_normalizedHermiteDerivProjection
        (apm_m02j02_normalizedHermiteCoefficient ψ) N) 2
        (volume.restrict (Ioi (0 : ℝ))) := by
    apply MeasureTheory.eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [Pi.sub_apply]
    rw [hdψeq x hx]
  rw [hv, hd]
  exact (apm_m02j02_graphNorm_restrict_Ioi_le
    (ψ - apm_m02j02_normalizedHermiteProjection
      (apm_m02j02_normalizedHermiteCoefficient ψ) N)
    (deriv ψ - apm_m02j02_normalizedHermiteDerivProjection
      (apm_m02j02_normalizedHermiteCoefficient ψ) N)).trans_lt hN

/-- Why this unblocks `apm_m02j02`: this packages whole-line `H¹`
membership, linear independence, and graph-norm density of the full
Hermite--Gaussian family in the exact frozen predicate. -/
theorem apm_m02J02_bridge_3 :
    apm_m02j02_IsH10Basis (Set.univ : Set ℝ)
      apm_m02j02_hermiteFunction apm_m02j02_hermiteFunctionDeriv := by
  apply apm_m02j02_hermite_basis_of_approx_density apm_m02j02_hermite_inH10
  apply apm_m02j02_density_of_testFunction_density Set.univ
    apm_m02j02_hermiteFunction apm_m02j02_hermiteFunctionDeriv
    (fun n => (apm_m02j02_hermiteFunction_contDiff n).continuous)
    apm_m02j02_hermiteFunctionDeriv_continuous
  intro φ hφsmooth hφcomp hφsub ε hε
  apply apm_m02j02_hermite_pair_approx_of_weightedEval_approx
  obtain ⟨N, hN⟩ :=
    apm_m02j02_exists_normalizedHermiteProjection_graph_close
      φ hφsmooth hφcomp ε hε
  obtain ⟨p, hp, hpd⟩ :=
    apm_m02j02_exists_weightedEval_eq_normalizedHermiteProjection
      (apm_m02j02_normalizedHermiteCoefficient φ) N
  refine ⟨p, ?_⟩
  rw [hpd, hp, Measure.restrict_univ]
  exact hN

theorem apm_m02j02 :
    apm_m02j02_IsH10Basis (Ioo (0 : ℝ) 1)
        apm_m02j02_sine apm_m02j02_sineDeriv ∧
    apm_m02j02_IsH10Basis (Ioi (0 : ℝ))
        (fun n ↦ apm_m02j02_hermiteFunction (2 * n + 1))
        (fun n ↦ apm_m02j02_hermiteFunctionDeriv (2 * n + 1)) ∧
    apm_m02j02_IsH10Basis (Set.univ : Set ℝ)
        apm_m02j02_hermiteFunction apm_m02j02_hermiteFunctionDeriv := by
  /-
  Boundary (closer hop 1): the definition expands
  `H¹₀` into weak-derivative and graph-norm approximation clauses, so proving
  the three basis assertions requires, in particular, graph-norm density of
  sine series and of the full/odd Hermite families, plus compactly supported
  smooth approximation of every displayed Hermite function.

  This hop closes the elementary differential and boundary-value layer for the
  interval family: `apm_m02j02_hasDerivAt_sine` and
  `apm_m02j02_deriv_sine` identify the frozen derivative exactly, while
  `apm_m02j02_sine_zero` and `apm_m02j02_sine_one` prove the two Dirichlet
  endpoint values.

  Searches of Mathlib and compiled problem artifacts found polynomial identities
  for `Polynomial.hermite` (and local uses in `a96A04`) and general eLp/Sobolev
  inequalities, but no Hermite completeness theorem, Fourier-sine density
  theorem, or packaged Sobolev space whose basis result could discharge these
  exact `eLpNorm` approximation goals. Searches also covered
  `LEMMA-INDEX.md`, all solved artifacts, `ConstructionTargets/`, Mathlib's
  Hermite Gaussian file and Sobolev inequality source, and git history. Sibling
  `a96A04` uses Hermite polynomials only for finite Gaussian derivative
  formulas, and `m95A02` provides no reusable Fourier density theorem.
  Establishing the three spectral completeness theorems remains open.

  Closer hop 2 closes the ambient smoothness layer for every displayed
  family. `apm_m02j02_sine_contDiff` and
  `apm_m02j02_sineDeriv_contDiff` prove global smoothness of the interval
  functions and their frozen derivatives. For the unbounded families,
  `apm_m02j02_hermiteFunction_contDiff` combines
  `Polynomial.contDiff_aeval` with smoothness of the Gaussian factor, and
  `apm_m02j02_hermiteFunction_hasDerivAt` certifies the frozen derivative at
  every point. This removes ordinary differentiability/regularity from the
  remaining obligations. Renewed searches of orthonormal-basis, Schwartz,
  Fourier-sine, and Hermite sources still found no completeness theorem that
  transports to the custom value/derivative-pair graph norm. Membership via
  compactly supported approximation, linear independence, and the three
  density clauses therefore remain open.

  Closer hop 3 proves the remaining elementary identities needed before the
  half-line membership argument: `apm_m02j02_deriv_hermiteFunction` rewrites
  the actual derivative to the frozen derivative family, and
  `apm_m02j02_hermiteFunction_odd_zero` uses
  `Polynomial.coeff_hermite_of_odd_add` to prove that every selected odd
  Hermite–Gaussian has zero trace at the half-line endpoint. A further search
  found Gaussian integrability primitives and polynomial/exponential decay,
  but no theorem converting those facts into the frozen weak-derivative plus
  compactly-supported graph-norm approximation predicate. The three spectral
  density results and linear independence of the function/derivative pairs
  remain substantial and were not completed in this final hop.
  -/
  exact ⟨apm_m02J02_bridge_1, apm_m02J02_bridge_2, apm_m02J02_bridge_3⟩
