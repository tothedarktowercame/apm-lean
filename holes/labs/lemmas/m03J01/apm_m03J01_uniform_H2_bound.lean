import Mathlib

/-!
# APM m03J01

## Statement repairs

The final item prints `U ∈ H²(U)`; this is repaired to `u ∈ H²(Ω)`, as
required by both the boundary-value problem and its requested conclusion.

## Encoding questions

Mathlib currently has no packaged `H₀¹(Ω)` type. It is encoded here by its
standard definition: `L²` functions with `L²` weak gradient that are limits of
smooth functions compactly supported in `Ω`. The `H²` conclusion is encoded by
an `L²` weak Hessian, and uniqueness is consequently stated up to a.e. equality.
-/

open Filter MeasureTheory Set

abbrev apm_m03J01_E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The `i`th coordinate vector in Euclidean `ℝⁿ`. -/
noncomputable def apm_m03J01_basis (n : ℕ) (i : Fin n) : apm_m03J01_E n :=
  EuclideanSpace.single i 1

/-- The classical gradient used for smooth approximants. -/
noncomputable def apm_m03J01_gradient (n : ℕ)
    (u : apm_m03J01_E n → ℝ) (x : apm_m03J01_E n) : apm_m03J01_E n :=
  ∑ i : Fin n,
    fderiv ℝ u x (apm_m03J01_basis n i) • apm_m03J01_basis n i

/-- Smooth functions compactly supported in the domain. -/
def apm_m03J01_testFunction (n : ℕ) (Ω : Set (apm_m03J01_E n))
    (φ : apm_m03J01_E n → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧ Function.support φ ⊆ Ω

/-- Dimension zero is the genuine exception to the preceding collapse: on the
one-point Euclidean space the constant-one function is analytic and compactly
supported, hence is a nonzero test function for the whole space. -/
lemma apm_m03J01_testFunction_zero_dim_nonzero :
    apm_m03J01_testFunction 0 univ
        (fun _ : apm_m03J01_E 0 ↦ (1 : ℝ)) ∧
      (fun _ : apm_m03J01_E 0 ↦ (1 : ℝ)) ≠ 0 := by
  constructor
  · refine ⟨contDiff_const, ?_, by simp⟩
    apply HasCompactSupport.intro (K := {0}) isCompact_singleton
    intro x hx
    exact (hx (by rw [Subsingleton.elim x 0]; simp)).elim
  · intro h
    have := congrFun h 0
    norm_num at this

lemma apm_m03J01_gradient_continuous {n : ℕ}
    {φ : apm_m03J01_E n → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    Continuous (apm_m03J01_gradient n φ) := by
  unfold apm_m03J01_gradient
  apply continuous_finset_sum
  intro i hi
  exact ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const

lemma apm_m03J01_gradient_add {n : ℕ} {φ ψ : apm_m03J01_E n → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) :
    apm_m03J01_gradient n (φ + ψ) =
      apm_m03J01_gradient n φ + apm_m03J01_gradient n ψ := by
  have hφdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hψdiff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  funext x
  simp only [apm_m03J01_gradient, fderiv_add (hφdiff x) (hψdiff x),
    ContinuousLinearMap.add_apply, add_smul, Finset.sum_add_distrib, Pi.add_apply]

lemma apm_m03J01_gradient_smul {n : ℕ} (c : ℝ)
    (φ : apm_m03J01_E n → ℝ) :
    apm_m03J01_gradient n (c • φ) = c • apm_m03J01_gradient n φ := by
  funext x
  simp only [apm_m03J01_gradient, fderiv_const_smul_field c, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum]

lemma apm_m03J01_testFunction_zero (n : ℕ) (Ω : Set (apm_m03J01_E n)) :
    apm_m03J01_testFunction n Ω (0 : apm_m03J01_E n → ℝ) := by
  exact ⟨contDiff_zero_fun, HasCompactSupport.zero, by simp⟩

lemma apm_m03J01_testFunction_add {n : ℕ} {Ω : Set (apm_m03J01_E n)}
    {φ ψ : apm_m03J01_E n → ℝ}
    (hφ : apm_m03J01_testFunction n Ω φ)
    (hψ : apm_m03J01_testFunction n Ω ψ) :
    apm_m03J01_testFunction n Ω (φ + ψ) := by
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, ?_⟩
  intro x hx
  by_contra hxΩ
  have hφx : φ x = 0 := by
    by_contra hne
    exact hxΩ (hφ.2.2 hne)
  have hψx : ψ x = 0 := by
    by_contra hne
    exact hxΩ (hψ.2.2 hne)
  exact hx (by simp [hφx, hψx])

lemma apm_m03J01_testFunction_smul {n : ℕ} {Ω : Set (apm_m03J01_E n)}
    (c : ℝ) {φ : apm_m03J01_E n → ℝ}
    (hφ : apm_m03J01_testFunction n Ω φ) :
    apm_m03J01_testFunction n Ω (c • φ) := by
  refine ⟨hφ.1.const_smul c, hφ.2.1.smul_left, ?_⟩
  intro x hx
  by_contra hxΩ
  have hφx : φ x = 0 := by
    by_contra hne
    exact hxΩ (hφ.2.2 hne)
  exact hx (by simp [hφx])

lemma apm_m03J01_gradient_hasCompactSupport {n : ℕ}
    {φ : apm_m03J01_E n → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (apm_m03J01_gradient n φ) := by
  unfold apm_m03J01_gradient
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using
      (HasCompactSupport.zero : HasCompactSupport (0 : apm_m03J01_E n → apm_m03J01_E n))
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (hφ.fderiv_apply ℝ (apm_m03J01_basis n i)).smul_right.add ih

lemma apm_m03J01_testFunction_val_memLp {n : ℕ} {Ω : Set (apm_m03J01_E n)}
    {φ : apm_m03J01_E n → ℝ} (hφ : apm_m03J01_testFunction n Ω φ) :
    MemLp φ 2 volume :=
  hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1

lemma apm_m03J01_testFunction_grad_memLp {n : ℕ} {Ω : Set (apm_m03J01_E n)}
    {φ : apm_m03J01_E n → ℝ} (hφ : apm_m03J01_testFunction n Ω φ) :
    MemLp (apm_m03J01_gradient n φ) 2 volume :=
  (apm_m03J01_gradient_continuous hφ.1).memLp_of_hasCompactSupport
    (apm_m03J01_gradient_hasCompactSupport hφ.2.1)

/-- An explicit representative of an element of `H₀¹(Ω)`. -/
structure apm_m03J01_H01 (n : ℕ) (Ω : Set (apm_m03J01_E n)) where
  val : apm_m03J01_E n → ℝ
  grad : apm_m03J01_E n → apm_m03J01_E n
  val_memLp : MemLp val 2 volume
  grad_memLp : MemLp grad 2 volume
  approximable : ∃ φ : ℕ → apm_m03J01_E n → ℝ,
    (∀ k, apm_m03J01_testFunction n Ω (φ k)) ∧
    Tendsto (fun k ↦ eLpNorm (fun x ↦ φ k x - val x) 2 volume) atTop (nhds 0) ∧
    Tendsto (fun k ↦ eLpNorm
      (fun x ↦ apm_m03J01_gradient n (φ k) x - grad x) 2 volume) atTop (nhds 0)

/-- The zero value/gradient pair is represented by the constant zero test
sequence. This is the first closure datum needed for the eventual quotient
Hilbert space. -/
noncomputable def apm_m03J01_zeroH01 (n : ℕ) (Ω : Set (apm_m03J01_E n)) :
    apm_m03J01_H01 n Ω where
  val := 0
  grad := 0
  val_memLp := by simp
  grad_memLp := by simp
  approximable := by
    refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩
    · intro k
      refine ⟨contDiff_const, ?_, ?_⟩
      · exact HasCompactSupport.zero
      · simp
    · simp
    · simp [apm_m03J01_gradient]

/-- The custom approximation condition is closed under addition. The result
is stated existentially so that no unquotiented representative operation is
made part of the public data model. -/
lemma apm_m03J01_H01_add_exists {n : ℕ} {Ω : Set (apm_m03J01_E n)}
    (u v : apm_m03J01_H01 n Ω) :
    ∃ w : apm_m03J01_H01 n Ω,
      w.val = u.val + v.val ∧ w.grad = u.grad + v.grad := by
  rcases u.approximable with ⟨φ, hφtest, hφval, hφgrad⟩
  rcases v.approximable with ⟨ψ, hψtest, hψval, hψgrad⟩
  let θ : ℕ → apm_m03J01_E n → ℝ := fun k x => φ k x + ψ k x
  have hgradient_continuous {f : apm_m03J01_E n → ℝ}
      (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) : Continuous (apm_m03J01_gradient n f) := by
    unfold apm_m03J01_gradient
    apply continuous_finset_sum
    intro i hi
    exact ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const
  have hgradient_add (k : ℕ) :
      apm_m03J01_gradient n (θ k) =
        apm_m03J01_gradient n (φ k) + apm_m03J01_gradient n (ψ k) := by
    have hφdiff : Differentiable ℝ (φ k) := (hφtest k).1.differentiable (by simp)
    have hψdiff : Differentiable ℝ (ψ k) := (hψtest k).1.differentiable (by simp)
    funext x
    simp only [θ, apm_m03J01_gradient, fderiv_fun_add (hφdiff x) (hψdiff x),
      ContinuousLinearMap.add_apply, add_smul, Finset.sum_add_distrib, Pi.add_apply]
  have hθtest (k : ℕ) : apm_m03J01_testFunction n Ω (θ k) := by
    refine ⟨(hφtest k).1.add (hψtest k).1, (hφtest k).2.1.add (hψtest k).2.1, ?_⟩
    intro x hx
    by_contra hxΩ
    have hφx : φ k x = 0 := by
      by_contra hne
      exact hxΩ ((hφtest k).2.2 hne)
    have hψx : ψ k x = 0 := by
      by_contra hne
      exact hxΩ ((hψtest k).2.2 hne)
    exact hx (by simp [θ, hφx, hψx])
  have tendsto_zero_of_le {a b : ℕ → ENNReal}
      (hab : ∀ k, a k ≤ b k) (hb : Tendsto b atTop (nhds 0)) :
      Tendsto a atTop (nhds 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro c hc
      exact (not_lt_of_ge bot_le hc).elim
    · intro c hc
      filter_upwards [(tendsto_order.1 hb).2 c hc] with k hk
      exact lt_of_le_of_lt (hab k) hk
  have hval_bound (k : ℕ) :
      eLpNorm (fun x => θ k x - (u.val x + v.val x)) 2 volume ≤
        eLpNorm (fun x => φ k x - u.val x) 2 volume +
          eLpNorm (fun x => ψ k x - v.val x) 2 volume := by
    have heq :
        (fun x => θ k x - (u.val x + v.val x)) =
          (fun x => φ k x - u.val x) + (fun x => ψ k x - v.val x) := by
      funext x
      simp only [θ, Pi.add_apply]
      ring
    rw [heq]
    exact eLpNorm_add_le
      ((hφtest k).1.continuous.aestronglyMeasurable.sub u.val_memLp.aestronglyMeasurable)
      ((hψtest k).1.continuous.aestronglyMeasurable.sub v.val_memLp.aestronglyMeasurable)
      (by norm_num : (1 : ENNReal) ≤ 2)
  have hgrad_bound (k : ℕ) :
      eLpNorm
          (fun x => apm_m03J01_gradient n (θ k) x - (u.grad x + v.grad x))
          2 volume ≤
        eLpNorm (fun x => apm_m03J01_gradient n (φ k) x - u.grad x) 2 volume +
          eLpNorm (fun x => apm_m03J01_gradient n (ψ k) x - v.grad x) 2 volume := by
    have heq :
        (fun x => apm_m03J01_gradient n (θ k) x - (u.grad x + v.grad x)) =
          (fun x => apm_m03J01_gradient n (φ k) x - u.grad x) +
            (fun x => apm_m03J01_gradient n (ψ k) x - v.grad x) := by
      funext x
      rw [hgradient_add]
      simp only [Pi.add_apply]
      abel
    rw [heq]
    exact eLpNorm_add_le
      ((hgradient_continuous (hφtest k).1).aestronglyMeasurable.sub
        u.grad_memLp.aestronglyMeasurable)
      ((hgradient_continuous (hψtest k).1).aestronglyMeasurable.sub
        v.grad_memLp.aestronglyMeasurable)
      (by norm_num : (1 : ENNReal) ≤ 2)
  have hval_tendsto :
      Tendsto
        (fun k => eLpNorm (fun x => φ k x - u.val x) 2 volume +
          eLpNorm (fun x => ψ k x - v.val x) 2 volume)
        atTop (nhds 0) := by
    simpa only [add_zero] using hφval.add hψval
  have hgrad_tendsto :
      Tendsto
        (fun k => eLpNorm (fun x => apm_m03J01_gradient n (φ k) x - u.grad x) 2 volume +
          eLpNorm (fun x => apm_m03J01_gradient n (ψ k) x - v.grad x) 2 volume)
        atTop (nhds 0) := by
    simpa only [add_zero] using hφgrad.add hψgrad
  refine ⟨{
    val := u.val + v.val
    grad := u.grad + v.grad
    val_memLp := u.val_memLp.add v.val_memLp
    grad_memLp := u.grad_memLp.add v.grad_memLp
    approximable := ⟨θ, hθtest,
      tendsto_zero_of_le hval_bound hval_tendsto,
      tendsto_zero_of_le hgrad_bound hgrad_tendsto⟩ }, rfl, rfl⟩

/-- The custom approximation condition is closed under real scalar
multiplication, again without choosing a canonical raw representative. -/
lemma apm_m03J01_H01_smul_exists {n : ℕ} {Ω : Set (apm_m03J01_E n)}
    (c : ℝ) (u : apm_m03J01_H01 n Ω) :
    ∃ w : apm_m03J01_H01 n Ω,
      w.val = c • u.val ∧ w.grad = c • u.grad := by
  rcases u.approximable with ⟨φ, hφtest, hφval, hφgrad⟩
  let θ : ℕ → apm_m03J01_E n → ℝ := fun k => c • φ k
  have hgradient_smul (k : ℕ) :
      apm_m03J01_gradient n (θ k) = c • apm_m03J01_gradient n (φ k) := by
    funext x
    simp only [θ, apm_m03J01_gradient, fderiv_const_smul_field c,
      Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_smul,
      Finset.smul_sum]
  have hθtest (k : ℕ) : apm_m03J01_testFunction n Ω (θ k) := by
    refine ⟨(hφtest k).1.const_smul c, (hφtest k).2.1.smul_left, ?_⟩
    intro x hx
    by_contra hxΩ
    have hφx : φ k x = 0 := by
      by_contra hne
      exact hxΩ ((hφtest k).2.2 hne)
    exact hx (by simp [θ, hφx])
  have hval_eq (k : ℕ) :
      eLpNorm (fun x => θ k x - (c • u.val) x) 2 volume =
        ‖c‖ₑ * eLpNorm (fun x => φ k x - u.val x) 2 volume := by
    have heq :
        (fun x => θ k x - (c • u.val) x) = c • (fun x => φ k x - u.val x) := by
      funext x
      simp only [θ, Pi.smul_apply, smul_eq_mul, mul_sub]
    rw [heq, eLpNorm_const_smul]
  have hgrad_eq (k : ℕ) :
      eLpNorm
          (fun x => apm_m03J01_gradient n (θ k) x - (c • u.grad) x)
          2 volume =
        ‖c‖ₑ *
          eLpNorm (fun x => apm_m03J01_gradient n (φ k) x - u.grad x) 2 volume := by
    have heq :
        (fun x => apm_m03J01_gradient n (θ k) x - (c • u.grad) x) =
          c • (fun x => apm_m03J01_gradient n (φ k) x - u.grad x) := by
      funext x
      rw [hgradient_smul]
      simp only [Pi.smul_apply]
      module
    rw [heq, eLpNorm_const_smul]
  have hval_tendsto :
      Tendsto
        (fun k => ‖c‖ₑ * eLpNorm (fun x => φ k x - u.val x) 2 volume)
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hφval (Or.inr (by simp))
  have hgrad_tendsto :
      Tendsto
        (fun k => ‖c‖ₑ *
          eLpNorm (fun x => apm_m03J01_gradient n (φ k) x - u.grad x) 2 volume)
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hφgrad (Or.inr (by simp))
  refine ⟨{
    val := c • u.val
    grad := c • u.grad
    val_memLp := u.val_memLp.const_smul c
    grad_memLp := u.grad_memLp.const_smul c
    approximable := ⟨θ, hθtest,
      hval_tendsto.congr' (Eventually.of_forall fun k => (hval_eq k).symm),
      hgrad_tendsto.congr' (Eventually.of_forall fun k => (hgrad_eq k).symm)⟩ }, rfl, rfl⟩

/-- Weak formulation of `-Δu + u = F` with zero Dirichlet boundary data. -/
def apm_m03J01_weakSolution {n : ℕ} {Ω : Set (apm_m03J01_E n)}
    (F : apm_m03J01_E n → ℝ) (u : apm_m03J01_H01 n Ω) : Prop :=
  ∀ v : apm_m03J01_H01 n Ω,
    ∫ x, (inner ℝ (u.grad x) (v.grad x) + u.val x * v.val x) ∂volume =
      ∫ x, F x * v.val x ∂volume

lemma apm_m03J01_weakSolution_zero_iff {n : ℕ} {Ω : Set (apm_m03J01_E n)}
    (F : apm_m03J01_E n → ℝ) :
    apm_m03J01_weakSolution F (apm_m03J01_zeroH01 n Ω) ↔
      ∀ v : apm_m03J01_H01 n Ω, ∫ x, F x * v.val x ∂volume = 0 := by
  simp only [apm_m03J01_weakSolution, apm_m03J01_zeroH01, Pi.zero_apply,
    inner_zero_left, zero_mul, zero_add, integral_zero]
  constructor
  · intro h v
    exact (h v).symm
  · intro h v
    exact (h v).symm

/-- Weak solutions are unique as `L²` values. This argument only uses the
energy equation: two solutions may be tested against each other, and the
resulting identities make the squared energy distance vanish. -/
lemma apm_m03J01_weakSolution_unique_ae {n : ℕ}
    {Ω : Set (apm_m03J01_E n)} (F : apm_m03J01_E n → ℝ)
    (u v : apm_m03J01_H01 n Ω)
    (hu : apm_m03J01_weakSolution F u)
    (hv : apm_m03J01_weakSolution F v) :
    u.val =ᵐ[volume] v.val := by
  let toEnergy : apm_m03J01_H01 n Ω →
      WithLp 2 (Lp (apm_m03J01_E n) 2 volume × Lp ℝ 2 volume) :=
    fun w => WithLp.toLp 2 (w.grad_memLp.toLp w.grad, w.val_memLp.toLp w.val)
  have henergy (a b : apm_m03J01_H01 n Ω) :
      inner ℝ (toEnergy a) (toEnergy b) =
        ∫ x, (inner ℝ (a.grad x) (b.grad x) + a.val x * b.val x) ∂volume := by
    change
      inner ℝ (a.grad_memLp.toLp a.grad) (b.grad_memLp.toLp b.grad) +
          inner ℝ (a.val_memLp.toLp a.val) (b.val_memLp.toLp b.val) = _
    rw [L2.inner_def, L2.inner_def,
      ← integral_add (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
    apply integral_congr_ae
    have hreal (r s : ℝ) : inner ℝ r s = r * s := by
      calc
        inner ℝ r s = inner ℝ (r • (1 : ℝ)) (s • (1 : ℝ)) := by simp
        _ = r * s * inner ℝ (1 : ℝ) 1 := by
          rw [real_inner_smul_left, real_inner_smul_right]
          ring
        _ = r * s := by rw [real_inner_self_eq_norm_sq]; norm_num
    filter_upwards [a.grad_memLp.coeFn_toLp, b.grad_memLp.coeFn_toLp,
      a.val_memLp.coeFn_toLp, b.val_memLp.coeFn_toLp]
      with x hagrad hbgrad haval hbval
    simp only [hagrad, hbgrad, haval, hbval, hreal]
  have h_self_cross :
      inner ℝ (toEnergy u) (toEnergy u) =
        inner ℝ (toEnergy v) (toEnergy u) := by
    calc
      inner ℝ (toEnergy u) (toEnergy u) =
          ∫ x, (inner ℝ (u.grad x) (u.grad x) + u.val x * u.val x) ∂volume :=
        henergy u u
      _ = ∫ x, F x * u.val x ∂volume := hu u
      _ = ∫ x, (inner ℝ (v.grad x) (u.grad x) + v.val x * u.val x) ∂volume :=
        (hv u).symm
      _ = inner ℝ (toEnergy v) (toEnergy u) := (henergy v u).symm
  have h_cross_self :
      inner ℝ (toEnergy u) (toEnergy v) =
        inner ℝ (toEnergy v) (toEnergy v) := by
    calc
      inner ℝ (toEnergy u) (toEnergy v) =
          ∫ x, (inner ℝ (u.grad x) (v.grad x) + u.val x * v.val x) ∂volume :=
        henergy u v
      _ = ∫ x, F x * v.val x ∂volume := hu v
      _ = ∫ x, (inner ℝ (v.grad x) (v.grad x) + v.val x * v.val x) ∂volume :=
        (hv v).symm
      _ = inner ℝ (toEnergy v) (toEnergy v) := (henergy v v).symm
  have hdiff :
      inner ℝ (toEnergy u - toEnergy v) (toEnergy u - toEnergy v) = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      h_self_cross, h_cross_self]
    ring
  have hpair : toEnergy u = toEnergy v := by
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hdiff)
  have hval := congrArg (fun w => (WithLp.ofLp w).2) hpair
  change u.val_memLp.toLp u.val = v.val_memLp.toLp v.val at hval
  exact (MemLp.toLp_eq_toLp_iff u.val_memLp v.val_memLp).mp hval

set_option maxHeartbeats 800000 in
lemma apm_m03J01_weakSolution_exists {n : ℕ} {Ω : Set (apm_m03J01_E n)}
    (F : apm_m03J01_E n → ℝ) (hF : MemLp F 2 volume) :
    ∃ u : apm_m03J01_H01 n Ω, apm_m03J01_weakSolution F u := by
  classical
  let Energy := WithLp 2
    (Lp (apm_m03J01_E n) 2 (volume : Measure (apm_m03J01_E n)) ×
      Lp ℝ 2 (volume : Measure (apm_m03J01_E n)))
  let Test := {φ : apm_m03J01_E n → ℝ // apm_m03J01_testFunction n Ω φ}
  let embed : Test → Energy := fun φ => WithLp.toLp 2
    ((apm_m03J01_testFunction_grad_memLp φ.2).toLp (apm_m03J01_gradient n φ),
      (apm_m03J01_testFunction_val_memLp φ.2).toLp φ)
  let pre : Submodule ℝ Energy := {
    carrier := Set.range embed
    zero_mem' := by
      refine ⟨⟨0, apm_m03J01_testFunction_zero n Ω⟩, ?_⟩
      apply (WithLp.prodContinuousLinearEquiv 2 ℝ
        (Lp (apm_m03J01_E n) 2 (volume : Measure (apm_m03J01_E n)))
        (Lp ℝ 2 (volume : Measure (apm_m03J01_E n)))).injective
      change
        ((apm_m03J01_testFunction_grad_memLp
              (apm_m03J01_testFunction_zero n Ω)).toLp
            (apm_m03J01_gradient n (0 : apm_m03J01_E n → ℝ)),
          (apm_m03J01_testFunction_val_memLp
              (apm_m03J01_testFunction_zero n Ω)).toLp 0) = (0, 0)
      apply Prod.ext
      · have hgradzero :
            apm_m03J01_gradient n (0 : apm_m03J01_E n → ℝ) = 0 := by
          funext x
          simp [apm_m03J01_gradient]
        change
          (apm_m03J01_testFunction_grad_memLp
              (apm_m03J01_testFunction_zero n Ω)).toLp
              (apm_m03J01_gradient n (0 : apm_m03J01_E n → ℝ)) = 0
        have hzeroMem :
            MemLp (0 : apm_m03J01_E n → apm_m03J01_E n) 2 volume := by
          simp
        calc
          _ = hzeroMem.toLp 0 := by
            apply MemLp.toLp_congr
            exact Eventually.of_forall fun x => congrFun hgradzero x
          _ = 0 := MemLp.toLp_zero hzeroMem
      · exact MemLp.toLp_zero
          (apm_m03J01_testFunction_val_memLp
            (apm_m03J01_testFunction_zero n Ω))
    add_mem' := by
      rintro x y ⟨φ, rfl⟩ ⟨ψ, rfl⟩
      refine ⟨⟨φ.1 + ψ.1, apm_m03J01_testFunction_add φ.2 ψ.2⟩, ?_⟩
      apply (WithLp.prodContinuousLinearEquiv 2 ℝ
        (Lp (apm_m03J01_E n) 2 (volume : Measure (apm_m03J01_E n)))
        (Lp ℝ 2 (volume : Measure (apm_m03J01_E n)))).injective
      change
        ((apm_m03J01_testFunction_grad_memLp
              (apm_m03J01_testFunction_add φ.2 ψ.2)).toLp
            (apm_m03J01_gradient n (φ.1 + ψ.1)),
          (apm_m03J01_testFunction_val_memLp
              (apm_m03J01_testFunction_add φ.2 ψ.2)).toLp (φ.1 + ψ.1)) =
        ((apm_m03J01_testFunction_grad_memLp φ.2).toLp
              (apm_m03J01_gradient n φ) +
            (apm_m03J01_testFunction_grad_memLp ψ.2).toLp
              (apm_m03J01_gradient n ψ),
          (apm_m03J01_testFunction_val_memLp φ.2).toLp φ +
            (apm_m03J01_testFunction_val_memLp ψ.2).toLp ψ)
      apply Prod.ext
      · change
          (apm_m03J01_testFunction_grad_memLp
              (apm_m03J01_testFunction_add φ.2 ψ.2)).toLp
              (apm_m03J01_gradient n (φ.1 + ψ.1)) =
            (apm_m03J01_testFunction_grad_memLp φ.2).toLp
                (apm_m03J01_gradient n φ) +
              (apm_m03J01_testFunction_grad_memLp ψ.2).toLp
                (apm_m03J01_gradient n ψ)
        calc
          _ = ((apm_m03J01_testFunction_grad_memLp φ.2).add
                (apm_m03J01_testFunction_grad_memLp ψ.2)).toLp
              (apm_m03J01_gradient n φ + apm_m03J01_gradient n ψ) := by
            apply MemLp.toLp_congr
            exact Eventually.of_forall fun x =>
              congrFun (apm_m03J01_gradient_add φ.2.1 ψ.2.1) x
          _ = _ := MemLp.toLp_add _ _
      · exact MemLp.toLp_add _ _
    smul_mem' := by
      rintro c x ⟨φ, rfl⟩
      refine ⟨⟨c • φ.1, apm_m03J01_testFunction_smul c φ.2⟩, ?_⟩
      apply (WithLp.prodContinuousLinearEquiv 2 ℝ
        (Lp (apm_m03J01_E n) 2 (volume : Measure (apm_m03J01_E n)))
        (Lp ℝ 2 (volume : Measure (apm_m03J01_E n)))).injective
      change
        ((apm_m03J01_testFunction_grad_memLp
              (apm_m03J01_testFunction_smul c φ.2)).toLp
            (apm_m03J01_gradient n (c • φ.1)),
          (apm_m03J01_testFunction_val_memLp
              (apm_m03J01_testFunction_smul c φ.2)).toLp (c • φ.1)) =
        (c • (apm_m03J01_testFunction_grad_memLp φ.2).toLp
            (apm_m03J01_gradient n φ),
          c • (apm_m03J01_testFunction_val_memLp φ.2).toLp φ)
      apply Prod.ext
      · change
          (apm_m03J01_testFunction_grad_memLp
              (apm_m03J01_testFunction_smul c φ.2)).toLp
              (apm_m03J01_gradient n (c • φ.1)) =
            c • (apm_m03J01_testFunction_grad_memLp φ.2).toLp
              (apm_m03J01_gradient n φ)
        calc
          _ = ((apm_m03J01_testFunction_grad_memLp φ.2).const_smul c).toLp
              (c • apm_m03J01_gradient n φ) := by
            apply MemLp.toLp_congr
            exact Eventually.of_forall fun x =>
              congrFun (apm_m03J01_gradient_smul c φ.1) x
          _ = _ := MemLp.toLp_const_smul c _
      · exact MemLp.toLp_const_smul c _ }
  let HC : ClosedSubmodule ℝ Energy := pre.closure
  let H : Submodule ℝ Energy := HC.toSubmodule
  haveI : H.HasOrthogonalProjection := by
    change HC.toSubmodule.HasOrthogonalProjection
    infer_instance
  let energyOf : apm_m03J01_H01 n Ω → Energy := fun v => WithLp.toLp 2
    (v.grad_memLp.toLp v.grad, v.val_memLp.toLp v.val)
  have energyOf_mem (v : apm_m03J01_H01 n Ω) : energyOf v ∈ H := by
    rcases v.approximable with ⟨φ, hφtest, hφval, hφgrad⟩
    let φsub : ℕ → Test := fun k => ⟨φ k, hφtest k⟩
    have hgradLp :
        Tendsto
          (fun k => (apm_m03J01_testFunction_grad_memLp (hφtest k)).toLp
            (apm_m03J01_gradient n (φ k))) atTop
          (nhds (v.grad_memLp.toLp v.grad)) := by
      refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun k => apm_m03J01_gradient n (φ k))
        (fun k => apm_m03J01_testFunction_grad_memLp (hφtest k))
        v.grad v.grad_memLp).2 ?_
      simpa only [Pi.sub_apply] using hφgrad
    have hvalLp :
        Tendsto
          (fun k => (apm_m03J01_testFunction_val_memLp (hφtest k)).toLp (φ k))
          atTop (nhds (v.val_memLp.toLp v.val)) := by
      refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        φ (fun k => apm_m03J01_testFunction_val_memLp (hφtest k))
        v.val v.val_memLp).2 ?_
      simpa only [Pi.sub_apply] using hφval
    have hprod := hgradLp.prodMk_nhds hvalLp
    have henergy :
        Tendsto (fun k => embed (φsub k)) atTop (nhds (energyOf v)) := by
      simpa only [embed, φsub, energyOf,
        WithLp.prodContinuousLinearEquiv_symm_apply] using
        ((WithLp.prodContinuousLinearEquiv 2 ℝ
          (Lp (apm_m03J01_E n) 2 (volume : Measure (apm_m03J01_E n)))
          (Lp ℝ 2 (volume : Measure (apm_m03J01_E n)))).symm.continuous.continuousAt.tendsto.comp
            hprod)
    change energyOf v ∈ closure (pre : Set Energy)
    apply mem_closure_of_tendsto henergy
    exact Eventually.of_forall fun k => ⟨φsub k, rfl⟩
  have realize (q : H) :
      ∃ u : apm_m03J01_H01 n Ω, energyOf u = (q : Energy) := by
    have hqmem : (q : Energy) ∈ closure (pre : Set Energy) := q.property
    obtain ⟨s, hs, hslim⟩ := mem_closure_iff_seq_limit.mp hqmem
    have hsrange (k : ℕ) : s k ∈ Set.range embed := by
      have hk := hs k
      change s k ∈ Set.range embed at hk
      exact hk
    choose φ hφ using hsrange
    have hembedlim :
        Tendsto (fun k => embed (φ k)) atTop (nhds (q : Energy)) := by
      apply hslim.congr'
      exact Eventually.of_forall fun k => (hφ k).symm
    let qgrad : Lp (apm_m03J01_E n) 2 volume := (q : Energy).fst
    let qval : Lp ℝ 2 (volume : Measure (apm_m03J01_E n)) := (q : Energy).snd
    have hgradLp :
        Tendsto
          (fun k => (apm_m03J01_testFunction_grad_memLp (φ k).2).toLp
            (apm_m03J01_gradient n (φ k))) atTop (nhds qgrad) := by
      simpa only [embed, qgrad, WithLp.toLp_fst] using
        ((WithLp.fstL 2 ℝ
          (Lp (apm_m03J01_E n) 2 (volume : Measure (apm_m03J01_E n)))
          (Lp ℝ 2 (volume : Measure (apm_m03J01_E n)))).continuous.continuousAt.tendsto.comp
            hembedlim)
    have hvalLp :
        Tendsto
          (fun k => (apm_m03J01_testFunction_val_memLp (φ k).2).toLp (φ k))
          atTop (nhds qval) := by
      simpa only [embed, qval, WithLp.toLp_snd] using
        ((WithLp.sndL 2 ℝ
          (Lp (apm_m03J01_E n) 2 (volume : Measure (apm_m03J01_E n)))
          (Lp ℝ 2 (volume : Measure (apm_m03J01_E n)))).continuous.continuousAt.tendsto.comp
            hembedlim)
    have hgradEdist :
        Tendsto
          (fun k => edist
            ((apm_m03J01_testFunction_grad_memLp (φ k).2).toLp
              (apm_m03J01_gradient n (φ k))) qgrad)
          atTop (nhds 0) := by
      simpa using hgradLp.edist
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => qgrad) atTop (nhds qgrad))
    have hvalEdist :
        Tendsto
          (fun k => edist
            ((apm_m03J01_testFunction_val_memLp (φ k).2).toLp (φ k)) qval)
          atTop (nhds 0) := by
      simpa using hvalLp.edist
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => qval) atTop (nhds qval))
    have hgradNorm :
        Tendsto
          (fun k => eLpNorm
            (fun x => apm_m03J01_gradient n (φ k) x - qgrad x) 2 volume)
          atTop (nhds 0) := by
      apply hgradEdist.congr'
      exact Eventually.of_forall fun k => by
        calc
          edist
              ((apm_m03J01_testFunction_grad_memLp (φ k).2).toLp
                (apm_m03J01_gradient n (φ k))) qgrad =
              edist
                ((apm_m03J01_testFunction_grad_memLp (φ k).2).toLp
                  (apm_m03J01_gradient n (φ k)))
                ((Lp.memLp qgrad).toLp qgrad) := by
                  rw [Lp.toLp_coeFn]
          _ = eLpNorm
              (fun x => apm_m03J01_gradient n (φ k) x - qgrad x) 2 volume := by
                simpa only [Pi.sub_apply] using
                  Lp.edist_toLp_toLp
                    (apm_m03J01_gradient n (φ k)) qgrad
                    (apm_m03J01_testFunction_grad_memLp (φ k).2) (Lp.memLp qgrad)
    have hvalNorm :
        Tendsto (fun k => eLpNorm (fun x => (φ k : apm_m03J01_E n → ℝ) x - qval x)
          2 volume) atTop (nhds 0) := by
      apply hvalEdist.congr'
      exact Eventually.of_forall fun k => by
        calc
          edist ((apm_m03J01_testFunction_val_memLp (φ k).2).toLp (φ k)) qval =
              edist ((apm_m03J01_testFunction_val_memLp (φ k).2).toLp (φ k))
                ((Lp.memLp qval).toLp qval) := by
                  rw [Lp.toLp_coeFn]
          _ = eLpNorm (fun x => (φ k : apm_m03J01_E n → ℝ) x - qval x)
              2 volume := by
                simpa only [Pi.sub_apply] using
                  Lp.edist_toLp_toLp (φ k : apm_m03J01_E n → ℝ) qval
                    (apm_m03J01_testFunction_val_memLp (φ k).2) (Lp.memLp qval)
    let u : apm_m03J01_H01 n Ω := {
      val := qval
      grad := qgrad
      val_memLp := Lp.memLp qval
      grad_memLp := Lp.memLp qgrad
      approximable := ⟨fun k => φ k, fun k => (φ k).2, hvalNorm, hgradNorm⟩ }
    refine ⟨u, ?_⟩
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ
      (Lp (apm_m03J01_E n) 2 (volume : Measure (apm_m03J01_E n)))
      (Lp ℝ 2 (volume : Measure (apm_m03J01_E n)))).injective
    change ((Lp.memLp qgrad).toLp qgrad, (Lp.memLp qval).toLp qval) =
      (qgrad, qval)
    exact Prod.ext (Lp.toLp_coeFn qgrad (Lp.memLp qgrad))
      (Lp.toLp_coeFn qval (Lp.memLp qval))
  have energy_inner (a b : apm_m03J01_H01 n Ω) :
      inner ℝ (energyOf a) (energyOf b) =
        ∫ x, (inner ℝ (a.grad x) (b.grad x) + a.val x * b.val x) ∂volume := by
    change
      inner ℝ (a.grad_memLp.toLp a.grad) (b.grad_memLp.toLp b.grad) +
          inner ℝ (a.val_memLp.toLp a.val) (b.val_memLp.toLp b.val) = _
    rw [L2.inner_def, L2.inner_def,
      ← integral_add (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
    apply integral_congr_ae
    have hreal (r s : ℝ) : inner ℝ r s = r * s := by
      calc
        inner ℝ r s = inner ℝ (r • (1 : ℝ)) (s • (1 : ℝ)) := by simp
        _ = r * s * inner ℝ (1 : ℝ) 1 := by
          rw [real_inner_smul_left, real_inner_smul_right]
          ring
        _ = r * s := by rw [real_inner_self_eq_norm_sq]; norm_num
    filter_upwards [a.grad_memLp.coeFn_toLp, b.grad_memLp.coeFn_toLp,
      a.val_memLp.coeFn_toLp, b.val_memLp.coeFn_toLp]
      with x hagrad hbgrad haval hbval
    simp only [hagrad, hbgrad, haval, hbval, hreal]
  let fEnergy : Energy := WithLp.toLp 2
    (0, hF.toLp F)
  have forcing_inner (v : apm_m03J01_H01 n Ω) :
      inner ℝ fEnergy (energyOf v) = ∫ x, F x * v.val x ∂volume := by
    change inner ℝ (0 : Lp (apm_m03J01_E n) 2 volume)
        (v.grad_memLp.toLp v.grad) +
        inner ℝ (hF.toLp F) (v.val_memLp.toLp v.val) = _
    simp only [inner_zero_left, zero_add]
    rw [L2.inner_def]
    apply integral_congr_ae
    have hreal (r s : ℝ) : inner ℝ r s = r * s := by
      calc
        inner ℝ r s = inner ℝ (r • (1 : ℝ)) (s • (1 : ℝ)) := by simp
        _ = r * s * inner ℝ (1 : ℝ) 1 := by
          rw [real_inner_smul_left, real_inner_smul_right]
          ring
        _ = r * s := by rw [real_inner_self_eq_norm_sq]; norm_num
    filter_upwards [hF.coeFn_toLp, v.val_memLp.coeFn_toLp]
      with x hFx hvx
    simp only [hFx, hvx, hreal]
  let q : H := H.orthogonalProjection fEnergy
  obtain ⟨u, huEnergy⟩ := realize q
  refine ⟨u, ?_⟩
  intro v
  let vH : H := ⟨energyOf v, energyOf_mem v⟩
  have hprojection : inner ℝ q vH = inner ℝ fEnergy (energyOf v) := by
    exact H.inner_orthogonalProjection_eq_of_mem_right vH fEnergy
  have hambient :
      inner ℝ (energyOf u) (energyOf v) =
        inner ℝ fEnergy (energyOf v) := by
    calc
      inner ℝ (energyOf u) (energyOf v) = inner ℝ q vH := by
        rw [huEnergy]
        rfl
      _ = inner ℝ fEnergy (energyOf v) := hprojection
  calc
    ∫ x, (inner ℝ (u.grad x) (v.grad x) + u.val x * v.val x) ∂volume =
        inner ℝ (energyOf u) (energyOf v) := (energy_inner u v).symm
    _ = inner ℝ fEnergy (energyOf v) := hambient
    _ = ∫ x, F x * v.val x ∂volume := forcing_inner v

/-- `H` is the weak Hessian of the weak gradient `g`. -/
def apm_m03J01_weakHessian {n : ℕ}
    (g : apm_m03J01_E n → apm_m03J01_E n)
    (H : apm_m03J01_E n → Fin n → Fin n → ℝ) : Prop :=
  MemLp H 2 volume ∧
  ∀ (i j : Fin n) (φ : apm_m03J01_E n → ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    ∫ x, g x i * fderiv ℝ φ x (apm_m03J01_basis n j) ∂volume =
      -∫ x, H x i j * φ x ∂volume

/-- The explicit `H²` size of a representative and a weak Hessian. -/
noncomputable def apm_m03J01_H2size {n : ℕ} {Ω : Set (apm_m03J01_E n)}
    (u : apm_m03J01_H01 n Ω)
    (H : apm_m03J01_E n → Fin n → Fin n → ℝ) : ENNReal :=
  eLpNorm u.val 2 volume + eLpNorm u.grad 2 volume + eLpNorm H 2 volume

/-- The zero representative has the zero weak Hessian. This is the origin
needed by a future closed weak-Hessian graph construction. -/
lemma apm_m03J01_zero_weakHessian (n : ℕ) (Ω : Set (apm_m03J01_E n)) :
    apm_m03J01_weakHessian (apm_m03J01_zeroH01 n Ω).grad
      (0 : apm_m03J01_E n → Fin n → Fin n → ℝ) := by
  constructor
  · simp
  · intro i j φ hφ hφc
    simp [apm_m03J01_zeroH01]

lemma apm_m03J01_zero_H2size (n : ℕ) (Ω : Set (apm_m03J01_E n)) :
    apm_m03J01_H2size (apm_m03J01_zeroH01 n Ω)
      (0 : apm_m03J01_E n → Fin n → Fin n → ℝ) = 0 := by
  simp [apm_m03J01_H2size, apm_m03J01_zeroH01]

/-- Every weak Hessian admitted by the graph has finite displayed `H²` size.
This isolates the finiteness bookkeeping needed when the closed-graph bound is
eventually converted into an `ENNReal` estimate. -/
lemma apm_m03J01_H2size_lt_top {n : ℕ} {Ω : Set (apm_m03J01_E n)}
    (u : apm_m03J01_H01 n Ω)
    (H : apm_m03J01_E n → Fin n → Fin n → ℝ)
    (hH : apm_m03J01_weakHessian u.grad H) :
    apm_m03J01_H2size u H < ⊤ := by
  unfold apm_m03J01_H2size
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
    ⟨u.val_memLp.eLpNorm_lt_top, u.grad_memLp.eLpNorm_lt_top⟩,
    hH.1.eLpNorm_lt_top⟩

/-- The weak-Hessian relation is closed under simultaneous negation.  This is
one of the graph operations required by the eventual closed-operator space. -/
lemma apm_m03J01_weakHessian_neg {n : ℕ}
    {g : apm_m03J01_E n → apm_m03J01_E n}
    {H : apm_m03J01_E n → Fin n → Fin n → ℝ}
    (hH : apm_m03J01_weakHessian g H) :
    apm_m03J01_weakHessian (-g) (-H) := by
  constructor
  · exact hH.1.neg
  · intro i j φ hφ hφc
    change (∫ x, -(g x i) * fderiv ℝ φ x (apm_m03J01_basis n j) ∂volume) =
      -∫ x, -(H x i j) * φ x ∂volume
    simpa only [neg_mul, integral_neg, neg_neg] using
      congrArg Neg.neg (hH.2 i j φ hφ hφc)

/-- An a.e.-zero weak gradient has the zero weak Hessian. This is the
positive-dimensional Hessian witness used after the frozen analytic test-space
collapse. -/
lemma apm_m03J01_zero_weakHessian_of_grad_ae_eq_zero {n : ℕ}
    {g : apm_m03J01_E n → apm_m03J01_E n}
    (hg : g =ᵐ[volume] 0) :
    apm_m03J01_weakHessian g
      (0 : apm_m03J01_E n → Fin n → Fin n → ℝ) := by
  constructor
  · simp
  · intro i j φ hφ hφcompact
    have hzero :
        (fun x ↦ g x i * fderiv ℝ φ x (apm_m03J01_basis n j)) =ᵐ[volume]
          (0 : apm_m03J01_E n → ℝ) := by
      filter_upwards [hg] with x hx
      simp [hx]
    rw [integral_congr_ae hzero]
    simp

/-- In dimension zero the weak-Hessian equations have no coordinate indices,
so the zero Hessian is available for every gradient. -/
lemma apm_m03J01_zero_dim_zero_weakHessian
    (g : apm_m03J01_E 0 → apm_m03J01_E 0) :
    apm_m03J01_weakHessian g
      (0 : apm_m03J01_E 0 → Fin 0 → Fin 0 → ℝ) := by
  constructor
  · simp
  · intro i
    exact Fin.elim0 i

/-- Every vector-valued function into zero-dimensional Euclidean space is
pointwise zero. -/
lemma apm_m03J01_H01_zero_dim_grad_eq_zero {Ω : Set (apm_m03J01_E 0)}
    (u : apm_m03J01_H01 0 Ω) :
    u.grad = 0 := by
  funext x
  exact Subsingleton.elim _ _

/-- In dimension zero the weak equation is just the `L²` Riesz identity for
the value component, and testing with the solution gives its norm bound. -/
lemma apm_m03J01_zero_dim_eLpNorm_val_le {Ω : Set (apm_m03J01_E 0)}
    (F : apm_m03J01_E 0 → ℝ) (hF : MemLp F 2 volume)
    (u : apm_m03J01_H01 0 Ω) (hu : apm_m03J01_weakSolution F u) :
    eLpNorm u.val 2 volume ≤ eLpNorm F 2 volume := by
  have hgrad := apm_m03J01_H01_zero_dim_grad_eq_zero u
  have hweak :
      ∫ x, u.val x * u.val x ∂volume = ∫ x, F x * u.val x ∂volume := by
    simpa [hgrad] using hu u
  have hreal (r s : ℝ) : inner ℝ r s = r * s := by
    calc
      inner ℝ r s = inner ℝ (r • (1 : ℝ)) (s • (1 : ℝ)) := by simp
      _ = r * s * inner ℝ (1 : ℝ) 1 := by
        rw [real_inner_smul_left, real_inner_smul_right]
        ring
      _ = r * s := by rw [real_inner_self_eq_norm_sq]; norm_num
  have hinner :
      inner ℝ (u.val_memLp.toLp u.val) (u.val_memLp.toLp u.val) =
        inner ℝ (hF.toLp F) (u.val_memLp.toLp u.val) := by
    rw [L2.inner_def, L2.inner_def]
    calc
      ∫ x, inner ℝ ((u.val_memLp.toLp u.val) x)
            ((u.val_memLp.toLp u.val) x) ∂volume =
          ∫ x, u.val x * u.val x ∂volume := by
        apply integral_congr_ae
        filter_upwards [u.val_memLp.coeFn_toLp] with x hx
        simp only [hx, hreal]
      _ = ∫ x, F x * u.val x ∂volume := hweak
      _ = ∫ x, inner ℝ ((hF.toLp F) x)
            ((u.val_memLp.toLp u.val) x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [hF.coeFn_toLp, u.val_memLp.coeFn_toLp] with x hFx hux
        simp only [hFx, hux, hreal]
  have hnorm : ‖u.val_memLp.toLp u.val‖ ≤ ‖hF.toLp F‖ := by
    by_cases hzero : u.val_memLp.toLp u.val = 0
    · simp [hzero]
    · have hmul :
          ‖u.val_memLp.toLp u.val‖ * ‖u.val_memLp.toLp u.val‖ ≤
            ‖hF.toLp F‖ * ‖u.val_memLp.toLp u.val‖ := by
        calc
          ‖u.val_memLp.toLp u.val‖ * ‖u.val_memLp.toLp u.val‖ =
              inner ℝ (u.val_memLp.toLp u.val) (u.val_memLp.toLp u.val) :=
            (real_inner_self_eq_norm_mul_norm _).symm
          _ = inner ℝ (hF.toLp F) (u.val_memLp.toLp u.val) := hinner
          _ ≤ ‖hF.toLp F‖ * ‖u.val_memLp.toLp u.val‖ := real_inner_le_norm _ _
      exact le_of_mul_le_mul_right hmul (norm_pos_iff.mpr hzero)
  have henorm : ‖u.val_memLp.toLp u.val‖ₑ ≤ ‖hF.toLp F‖ₑ :=
    enorm_le_iff_norm_le.mpr hnorm
  simpa only [Lp.enorm_toLp u.val_memLp, Lp.enorm_toLp hF] using henorm

/-- The continuous Fréchet--Riesz solution operator used in the theorem's
abstract Hilbert-space clause. -/
noncomputable def apm_m03J01_riesz
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] : (V →L[ℝ] ℝ) →L[ℝ] V :=
  (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma apm_m03J01_inner_riesz
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (f : V →L[ℝ] ℝ) (v : V) :
    inner ℝ (apm_m03J01_riesz V f) v = f v := by
  exact InnerProductSpace.toDual_symm_apply

lemma apm_m03J01_abstract_variational :
    ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [CompleteSpace V],
      ∃ T : (V →L[ℝ] ℝ) →L[ℝ] V, ∀ f : V →L[ℝ] ℝ,
        (∃ C : ℝ, ∀ v : V, C ≤ (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v) ∧
        (∀ v : V,
          (2 : ℝ)⁻¹ * ‖T f‖ ^ 2 - f (T f) ≤
            (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v) ∧
        (∀ u : V,
          (∀ v : V, (2 : ℝ)⁻¹ * ‖u‖ ^ 2 - f u ≤
            (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v) → u = T f) ∧
        (∀ v : V, inner ℝ (T f) v = f v) := by
  intro V _ _ _
  let T := apm_m03J01_riesz V
  refine ⟨T, ?_⟩
  intro f
  have hinner (v : V) : inner ℝ (T f) v = f v :=
    apm_m03J01_inner_riesz f v
  have henergy (v : V) :
      (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v =
        (2 : ℝ)⁻¹ * ‖v - T f‖ ^ 2 - (2 : ℝ)⁻¹ * ‖T f‖ ^ 2 := by
    rw [← hinner v, norm_sub_sq_real, real_inner_comm]
    ring
  refine ⟨?_, ?_, ?_, hinner⟩
  · refine ⟨-(2 : ℝ)⁻¹ * ‖T f‖ ^ 2, ?_⟩
    intro v
    rw [henergy]
    nlinarith [sq_nonneg ‖v - T f‖]
  · intro v
    rw [henergy, henergy]
    simp
  · intro u hu
    have hle := hu (T f)
    rw [henergy, henergy] at hle
    have hs : 0 ≤ ‖u - T f‖ ^ 2 := sq_nonneg _
    have hz : ‖u - T f‖ = 0 := by
      simp only [sub_self, norm_zero] at hle
      nlinarith [norm_nonneg (u - T f)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- The closure definition of `H₀¹` makes the weak gradient independent of
the chosen representative of the value function. -/
lemma apm_m03J01_gradient_unique_of_val_ae {n : ℕ}
    {Ω : Set (apm_m03J01_E n)} (u v : apm_m03J01_H01 n Ω)
    (hval : u.val =ᵐ[volume] v.val) :
    u.grad =ᵐ[volume] v.grad := by
  sorry

/-- Distributional first derivatives are unique in `L²`. -/
lemma apm_m03J01_weakHessian_unique_ae {n : ℕ}
    {g : apm_m03J01_E n → apm_m03J01_E n}
    {H K : apm_m03J01_E n → Fin n → Fin n → ℝ}
    (hH : apm_m03J01_weakHessian g H)
    (hK : apm_m03J01_weakHessian g K) :
    H =ᵐ[volume] K := by
  sorry

/-- Qualitative `H²` regularity upgrades to a uniform estimate by applying
the closed graph theorem to the solution/weak-Hessian graph. -/
-- BEGIN SEAT AREA
lemma apm_m03J01_uniform_H2_bound
    (n : ℕ) (Ω : Set (apm_m03J01_E n))
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hΩnonempty : Ω.Nonempty)
    (hregular : ∀ (F : apm_m03J01_E n → ℝ) (hF : MemLp F 2 volume)
      (u : apm_m03J01_H01 n Ω), apm_m03J01_weakSolution F u →
        ∃ H, apm_m03J01_weakHessian u.grad H) :
    ∃ C : ENNReal, C < ⊤ ∧
      ∀ (F : apm_m03J01_E n → ℝ) (hF : MemLp F 2 volume)
        (u : apm_m03J01_H01 n Ω), apm_m03J01_weakSolution F u →
          ∃ H, apm_m03J01_weakHessian u.grad H ∧
            apm_m03J01_H2size u H ≤ C * eLpNorm F 2 volume := by
  sorry
-- END SEAT AREA

set_option linter.unusedVariables false in
theorem apm_m03j01 :
    (∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [CompleteSpace V],
      ∃ T : (V →L[ℝ] ℝ) →L[ℝ] V, ∀ f : V →L[ℝ] ℝ,
        (∃ C : ℝ, ∀ v : V, C ≤ (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v) ∧
        (∀ v : V,
          (2 : ℝ)⁻¹ * ‖T f‖ ^ 2 - f (T f) ≤
            (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v) ∧
        (∀ u : V,
          (∀ v : V, (2 : ℝ)⁻¹ * ‖u‖ ^ 2 - f u ≤
            (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v) → u = T f) ∧
        (∀ v : V, inner ℝ (T f) v = f v)) ∧
    (∀ (n : ℕ) (Ω : Set (apm_m03J01_E n)),
      IsOpen Ω → Bornology.IsBounded Ω → Ω.Nonempty →
      ∀ F : apm_m03J01_E n → ℝ, MemLp F 2 volume →
        ∃ u : apm_m03J01_H01 n Ω,
          apm_m03J01_weakSolution F u ∧
          ∀ v : apm_m03J01_H01 n Ω,
            apm_m03J01_weakSolution F v → u.val =ᵐ[volume] v.val) ∧
    (∀ (n : ℕ) (Ω : Set (apm_m03J01_E n)),
      IsOpen Ω → Bornology.IsBounded Ω → Ω.Nonempty →
      (∀ (F : apm_m03J01_E n → ℝ) (hF : MemLp F 2 volume)
        (u : apm_m03J01_H01 n Ω), apm_m03J01_weakSolution F u →
          ∃ H, apm_m03J01_weakHessian u.grad H) →
      ∃ C : ENNReal, C < ⊤ ∧
        ∀ (F : apm_m03J01_E n → ℝ) (hF : MemLp F 2 volume)
          (u : apm_m03J01_H01 n Ω), apm_m03J01_weakSolution F u →
            ∃ H, apm_m03J01_weakHessian u.grad H ∧
              apm_m03J01_H2size u H ≤ C * eLpNorm F 2 volume) := by
  refine ⟨apm_m03J01_abstract_variational, ?_, ?_⟩
  · intro n Ω hΩopen hΩbounded hΩnonempty F hF
    obtain ⟨u, hu⟩ := apm_m03J01_weakSolution_exists F hF
    exact ⟨u, hu, fun v hv => apm_m03J01_weakSolution_unique_ae F u v hu hv⟩
  · intro n Ω hΩopen hΩbounded hΩnonempty hregular
    exact apm_m03J01_uniform_H2_bound n Ω hΩopen hΩbounded hΩnonempty hregular

#print axioms apm_m03j01
