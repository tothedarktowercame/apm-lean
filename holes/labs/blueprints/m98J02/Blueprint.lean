import Mathlib
import Mathlib.MeasureTheory.Measure.OpenPos
import ConstructionTargets.TestFunctionTranslation

/-!
# APM m98J02

## Statement repairs

Part (d) assumes only `f ∈ C²(ℝ²)`, but the convolution construction in
parts (b)--(c) requires one factor to have compact support. Following the
informal solution, `f` is minimally assumed compactly supported. This is also
the hypothesis under which the convolution is defined here.  The printed
regularity conclusion is false for an arbitrary fundamental distribution of
this non-hypoelliptic operator.  Following the informal solution's explicit
function-level convolution argument, `w₀` is additionally required to be the
regular distribution represented by a locally integrable function.

The garbled operator typography is read, as in the supplied solution, as
`T = 2 ∂²/∂x² - ∂/∂y + 3 ∂²/(∂x∂y)`.

The former first conjunct merely unfolded `apm_m98J02_hasCompactSupport`.
Since the definition above already supplies part (a), that tautology is
replaced by the substantive closure of compactly supported distributions
under addition.

Revised 2026-10-13: in `apm_m98J02_isConvolution` the cutoff `χ` must equal one
on an open neighbourhood of `K`, not merely at the points of `K`. With the pointwise
condition, a distribution of positive order (for example `δ₀'`, with `K = {0}`) sees
the derivatives of `χ` at `K`, so the defining pairing depended on the cutoff and
the definition did not determine the convolution (found by a lemma seat, round 2).

## Encoding questions

Mathlib currently provides `Distribution` but not the general convolution of
a compactly supported distribution with an arbitrary distribution, nor
general distributional partial derivatives. Consequently these are encoded
by their defining test-function identities. `apm_m98J02_isConvolution` uses a
test-function cutoff equal to one on an open neighbourhood of a compact support of
the first factor;
`apm_m98J02_solvesT` uses the formal adjoint
`2∂ₓ² + ∂ᵧ + 3∂ₓ∂ᵧ` on test functions. No function-level surrogate
replaces the distributions.
-/

open MeasureTheory Set TopologicalSpace
open scoped Distributions ContDiff BoundedContinuousFunction

noncomputable section

abbrev apm_m98J02_E := EuclideanSpace ℝ (Fin 2)

abbrev apm_m98J02_Test :=
  TestFunction (⊤ : Opens apm_m98J02_E) ℝ ⊤

abbrev apm_m98J02_Dist :=
  Distribution (⊤ : Opens apm_m98J02_E) ℝ ⊤

/-- A distribution vanishes on every test function supported off one compact set. -/
def apm_m98J02_hasCompactSupport (u : apm_m98J02_Dist) : Prop :=
  ∃ K : Set apm_m98J02_E, IsCompact K ∧
    ∀ φ : apm_m98J02_Test, Disjoint (tsupport (φ : apm_m98J02_E → ℝ)) K → u φ = 0

/-- The defining pairing for convolution when the first factor has compact support.

The cutoff `χ` lets the compactly supported distribution `u` act on the
generally non-compact smooth function `x ↦ v (y ↦ φ (x + y))`. -/
def apm_m98J02_isConvolution
    (u v w : apm_m98J02_Dist) : Prop :=
  ∀ φ : apm_m98J02_Test,
    ∃ (K : Set apm_m98J02_E) (χ Ψ : apm_m98J02_Test),
      IsCompact K ∧
      (∀ η : apm_m98J02_Test,
        Disjoint (tsupport (η : apm_m98J02_E → ℝ)) K → u η = 0) ∧
      (∃ U : Set apm_m98J02_E, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U, χ x = 1) ∧
      (∀ x : apm_m98J02_E,
        ∃ τ : apm_m98J02_Test,
          (∀ y : apm_m98J02_E, τ y = φ (x + y)) ∧ Ψ x = χ x * v τ) ∧
      w φ = u Ψ

/-- Directional partial derivative in one of the two coordinate directions. -/
def apm_m98J02_partial (i : Fin 2) (f : apm_m98J02_E → ℝ)
    (x : apm_m98J02_E) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The formal adjoint of `2∂ₓ² - ∂ᵧ + 3∂ₓ∂ᵧ`. -/
def apm_m98J02_formalAdjoint (f : apm_m98J02_E → ℝ)
    (x : apm_m98J02_E) : ℝ :=
  2 * apm_m98J02_partial 0 (apm_m98J02_partial 0 f) x +
    apm_m98J02_partial 1 f x +
    3 * apm_m98J02_partial 0 (apm_m98J02_partial 1 f) x

/-- Distributional equation `T w = r`, expressed against test functions. -/
def apm_m98J02_solvesT
    (w : apm_m98J02_Dist) (r : apm_m98J02_Test → ℝ) : Prop :=
  ∀ φ : apm_m98J02_Test,
    ∃ ψ : apm_m98J02_Test,
      (∀ x : apm_m98J02_E,
        ψ x = apm_m98J02_formalAdjoint (φ : apm_m98J02_E → ℝ) x) ∧
      w ψ = r φ

/-- A distribution is the regular distribution induced by a function. -/
def apm_m98J02_representsFunction
    (u : apm_m98J02_Dist) (f : apm_m98J02_E → ℝ) : Prop :=
  ∀ φ : apm_m98J02_Test, u φ = ∫ x, f x * φ x

/-- Compactly supported distributions are closed under addition directly from
the support definition. -/
lemma apm_m98J02_hasCompactSupport_add
    (u v : apm_m98J02_Dist)
    (hu : apm_m98J02_hasCompactSupport u)
    (hv : apm_m98J02_hasCompactSupport v) :
    apm_m98J02_hasCompactSupport (u + v) := by
  obtain ⟨Ku, hKuc, hKu⟩ := hu
  obtain ⟨Kv, hKvc, hKv⟩ := hv
  refine ⟨Ku ∪ Kv, hKuc.union hKvc, ?_⟩
  intro φ hdis
  have hd := disjoint_union_right.mp hdis
  simp [hKu φ hd.1, hKv φ hd.2]

@[simp] lemma apm_m98J02_hasCompactSupport_zero :
    apm_m98J02_hasCompactSupport (0 : apm_m98J02_Dist) := by
  refine ⟨∅, isCompact_empty, ?_⟩
  simp

lemma apm_m98J02_hasCompactSupport_neg
    (u : apm_m98J02_Dist) (hu : apm_m98J02_hasCompactSupport u) :
    apm_m98J02_hasCompactSupport (-u) := by
  obtain ⟨K, hKc, hK⟩ := hu
  refine ⟨K, hKc, ?_⟩
  intro φ hdis
  simp [hK φ hdis]

lemma apm_m98J02_hasCompactSupport_sub
    (u v : apm_m98J02_Dist)
    (hu : apm_m98J02_hasCompactSupport u)
    (hv : apm_m98J02_hasCompactSupport v) :
    apm_m98J02_hasCompactSupport (u - v) := by
  rw [sub_eq_add_neg]
  exact apm_m98J02_hasCompactSupport_add u (-v) hu
    (apm_m98J02_hasCompactSupport_neg v hv)

lemma apm_m98J02_hasCompactSupport_smul
    (c : ℝ) (u : apm_m98J02_Dist)
    (hu : apm_m98J02_hasCompactSupport u) :
    apm_m98J02_hasCompactSupport (c • u) := by
  obtain ⟨K, hKc, hK⟩ := hu
  refine ⟨K, hKc, ?_⟩
  intro φ hdis
  simp [hK φ hdis]

/-- Adding a homogeneous solution preserves the encoded inhomogeneous
distributional equation. -/
lemma apm_m98J02_solvesT_add_homogeneous
    (w z : apm_m98J02_Dist) (r : apm_m98J02_Test → ℝ)
    (hw : apm_m98J02_solvesT w r)
    (hz : apm_m98J02_solvesT z (fun _ ↦ 0)) :
    apm_m98J02_solvesT (w + z) r := by
  intro φ
  obtain ⟨ψ, hψ, hwψ⟩ := hw φ
  obtain ⟨η, hη, hzη⟩ := hz φ
  have hηψ : η = ψ := by
    ext x
    rw [hη x, hψ x]
  subst η
  refine ⟨ψ, hψ, ?_⟩
  simp [hwψ, hzη]

/-- Translation of a test function by a fixed vector.  This is the test
function required pointwise in the definition of distributional convolution. -/
def apm_m98J02_translateTest (x : apm_m98J02_E)
    (φ : apm_m98J02_Test) : apm_m98J02_Test where
  toFun := fun y ↦ φ (x + y)
  contDiff' := φ.contDiff.comp (contDiff_const.add contDiff_id)
  hasCompactSupport' :=
    φ.hasCompactSupport.comp_homeomorph (Homeomorph.addLeft x)
  tsupport_subset' := by simp

@[simp] lemma apm_m98J02_translateTest_apply
    (x y : apm_m98J02_E) (φ : apm_m98J02_Test) :
    apm_m98J02_translateTest x φ y = φ (x + y) := rfl

/-- Why this unblocks the cutoff step in `apm_m98j02`: every compact subset
of the Euclidean plane admits a compactly supported smooth function that is
identically one on an open neighbourhood of that subset. -/
theorem apm_m98J02_bridge_1
    (K : Set apm_m98J02_E) (hK : IsCompact K) :
    ∃ χ : apm_m98J02_Test, ∃ U : Set apm_m98J02_E, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U, χ x = 1 := by
  rcases (Metric.isBounded_iff_subset_ball (0 : apm_m98J02_E)).mp hK.isBounded with
    ⟨r, hr⟩
  let b : ContDiffBump (0 : apm_m98J02_E) :=
    ⟨|r| + 1, |r| + 2, by positivity, by linarith⟩
  let χ : apm_m98J02_Test := TestFunction.mk b b.contDiff
    b.hasCompactSupport (by simp)
  refine ⟨χ, Metric.ball 0 (|r| + 1), Metric.isOpen_ball,
    hr.trans (Metric.ball_subset_ball (by linarith [le_abs_self r])), ?_⟩
  intro x hx
  change b x = 1
  exact b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)

noncomputable def apm_m98J02_integralAgainstBCF
    (q : apm_m98J02_E → ℝ) (hq : Continuous q)
    (hqc : HasCompactSupport q) :
    (apm_m98J02_E →ᵇ ℝ) →L[ℝ] ℝ := by
  let L : (apm_m98J02_E →ᵇ ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun φ => ∫ x, q x * φ x
      map_add' := by
        intro φ ψ
        rw [← integral_add]
        · congr 1
          funext x
          simp [mul_add]
        · exact (hq.mul φ.continuous).integrable_of_hasCompactSupport
            hqc.mul_right
        · exact (hq.mul ψ.continuous).integrable_of_hasCompactSupport
            hqc.mul_right
      map_smul' := by
        intro c φ
        simp only [RingHom.id_apply, smul_eq_mul,
          BoundedContinuousFunction.smul_apply]
        rw [← integral_const_mul]
        congr 1
        funext x
        ring }
  exact L.mkContinuous (∫ x, |q x|) (by
    intro φ
    have hqi : Integrable (fun x => |q x|) :=
      hq.abs.integrable_of_hasCompactSupport hqc.abs
    calc
      _ ≤ ∫ x, |q x| * ‖φ‖ :=
        MeasureTheory.norm_integral_le_of_norm_le
          (hqi.mul_const ‖φ‖) (Filter.Eventually.of_forall (fun x => by
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul_of_nonneg_left
              (by simpa [Real.norm_eq_abs] using φ.norm_coe_le_norm x)
              (abs_nonneg _)))
      _ = (∫ x, |q x|) * ‖φ‖ := integral_mul_const _ _)

lemma apm_m98J02_integralAgainstBCF_apply
    (q : apm_m98J02_E → ℝ) (hq : Continuous q)
    (hqc : HasCompactSupport q) (φ : apm_m98J02_E →ᵇ ℝ) :
    apm_m98J02_integralAgainstBCF q hq hqc φ = ∫ x, q x * φ x := rfl

noncomputable def apm_m98J02_regularDistribution
    (q : apm_m98J02_E → ℝ) (hq : Continuous q)
    (hqc : HasCompactSupport q) : apm_m98J02_Dist :=
  TestFunction.mkCLM ℝ (fun φ => ∫ x, q x * φ x)
    (by
      intro φ ψ
      change (∫ x, q x * (φ x + ψ x)) =
        (∫ x, q x * φ x) + ∫ x, q x * ψ x
      rw [← integral_add]
      · congr 1
        funext x; ring
      · exact (hq.mul φ.contDiff.continuous).integrable_of_hasCompactSupport
          hqc.mul_right
      · exact (hq.mul ψ.contDiff.continuous).integrable_of_hasCompactSupport
          hqc.mul_right)
    (by
      intro c φ
      change (∫ x, q x * (c * φ x)) = c * ∫ x, q x * φ x
      rw [← integral_const_mul]
      congr 1
      funext x
      change q x * (c * φ x) = c * (q x * φ x)
      ring)
    (by
      intro K hK
      exact (apm_m98J02_integralAgainstBCF q hq hqc).continuous.comp
        (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ).continuous)

lemma apm_m98J02_regularDistribution_apply
    (q : apm_m98J02_E → ℝ) (hq : Continuous q)
    (hqc : HasCompactSupport q) (φ : apm_m98J02_Test) :
    apm_m98J02_regularDistribution q hq hqc φ = ∫ x, q x * φ x := by
  apply TestFunction.mkCLM_apply

lemma apm_m98J02_regularDistribution_represents
    (q : apm_m98J02_E → ℝ) (hq : Continuous q)
    (hqc : HasCompactSupport q) :
    apm_m98J02_representsFunction
      (apm_m98J02_regularDistribution q hq hqc) q := by
  intro φ
  exact apm_m98J02_regularDistribution_apply q hq hqc φ

lemma apm_m98J02_regularDistribution_hasCompactSupport
    (q : apm_m98J02_E → ℝ) (hq : Continuous q)
    (hqc : HasCompactSupport q) :
    apm_m98J02_hasCompactSupport
      (apm_m98J02_regularDistribution q hq hqc) := by
  refine ⟨tsupport q, hqc, ?_⟩
  intro φ hdis
  rw [apm_m98J02_regularDistribution_apply]
  apply integral_eq_zero_of_ae
  filter_upwards with x
  by_cases hqx : q x = 0
  · simp [hqx]
  · have hxq : x ∈ tsupport q := subset_tsupport q hqx
    have hφx : φ x = 0 := by
      by_contra hne
      have hxφ : x ∈ tsupport (φ : apm_m98J02_E → ℝ) :=
        subset_tsupport _ hne
      exact Set.disjoint_left.1 hdis hxφ hxq
    simp [hφx]

noncomputable def apm_m98J02_setIntegralBCF
    (K : Compacts apm_m98J02_E) :
    (apm_m98J02_E →ᵇ ℝ) →L[ℝ] ℝ := by
  let L : (apm_m98J02_E →ᵇ ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun φ => ∫ x in (K : Set apm_m98J02_E), φ x
      map_add' := by
        intro φ ψ
        rw [← integral_add]
        · rfl
        · exact φ.continuous.continuousOn.integrableOn_compact K.isCompact
        · exact ψ.continuous.continuousOn.integrableOn_compact K.isCompact
      map_smul' := by
        intro c φ
        simp only [RingHom.id_apply, smul_eq_mul,
          BoundedContinuousFunction.smul_apply]
        exact integral_const_mul c _ }
  exact L.mkContinuous (volume.real (K : Set apm_m98J02_E)) (by
    intro φ
    simpa [mul_comm] using MeasureTheory.norm_setIntegral_le_of_norm_le_const
      K.isCompact.measure_lt_top (fun x hx => φ.norm_coe_le_norm x))

lemma apm_m98J02_setIntegralBCF_apply
    (K : Compacts apm_m98J02_E) (φ : apm_m98J02_E →ᵇ ℝ) :
    apm_m98J02_setIntegralBCF K φ =
      ∫ x in (K : Set apm_m98J02_E), φ x := rfl

noncomputable def apm_m98J02_constantDistribution : apm_m98J02_Dist :=
  TestFunction.mkCLM ℝ (fun φ => ∫ x, φ x)
    (by
      intro φ ψ
      rw [← integral_add]
      · rfl
      · exact φ.contDiff.continuous.integrable_of_hasCompactSupport
          φ.hasCompactSupport
      · exact ψ.contDiff.continuous.integrable_of_hasCompactSupport
          ψ.hasCompactSupport)
    (by
      intro c φ
      change (∫ x, c * φ x) = c * ∫ x, φ x
      exact integral_const_mul c _)
    (by
      intro K hK
      have heq : (fun φ : 𝓓_{K}(apm_m98J02_E, ℝ) => ∫ x, φ x) =
          fun φ => apm_m98J02_setIntegralBCF K
            (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ φ) := by
        funext φ
        rw [apm_m98J02_setIntegralBCF_apply]
        have hind : (K : Set apm_m98J02_E).indicator (fun x => φ x) =
            fun x => φ x := by
          funext x
          by_cases hx : x ∈ (K : Set apm_m98J02_E)
          · simp [hx]
          · simp [hx, φ.zero_on_compl hx]
        rw [← hind, integral_indicator K.isCompact.measurableSet]
        apply integral_congr_ae
        filter_upwards with x
        rfl
      change Continuous (fun φ : 𝓓_{K}(apm_m98J02_E, ℝ) => ∫ x, φ x)
      rw [heq]
      exact (apm_m98J02_setIntegralBCF K).continuous.comp
        (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ).continuous)

lemma apm_m98J02_constantDistribution_apply (φ : apm_m98J02_Test) :
    apm_m98J02_constantDistribution φ = ∫ x, φ x := by
  apply TestFunction.mkCLM_apply

lemma apm_m98J02_constantDistribution_ne_zero :
    apm_m98J02_constantDistribution ≠ 0 := by
  let b : ContDiffBump (0 : apm_m98J02_E) :=
    ⟨1, 2, by norm_num, by norm_num⟩
  let φ : apm_m98J02_Test := TestFunction.mk b b.contDiff
    b.hasCompactSupport (by simp)
  intro hzero
  have happ := congrArg (fun T : apm_m98J02_Dist => T φ) hzero
  change apm_m98J02_constantDistribution φ = (0 : apm_m98J02_Dist) φ at happ
  rw [apm_m98J02_constantDistribution_apply] at happ
  have hint : 0 < ∫ x : apm_m98J02_E, b x := by
    apply (integral_pos_iff_support_of_nonneg (fun x => b.nonneg' x)
      (b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport)).2
    rw [b.support_eq]
    exact Metric.measure_ball_pos volume (0 : apm_m98J02_E) (by norm_num)
  change (∫ x : apm_m98J02_E, b x) = 0 at happ
  linarith

/-- A coordinate derivative of a test function, bundled again as a test
function.  Compact support is preserved because the Fréchet derivative of a
function vanishing near infinity also vanishes there. -/
noncomputable def apm_m98J02_partialTest (i : Fin 2)
    (φ : apm_m98J02_Test) : apm_m98J02_Test :=
  TestFunction.mk (apm_m98J02_partial i φ)
    (by
      exact (contDiff_infty_iff_fderiv.mp φ.contDiff).2.clm_apply
        contDiff_const)
    (φ.hasCompactSupport.fderiv_apply ℝ (EuclideanSpace.single i 1))
    (by simp)

@[simp] lemma apm_m98J02_partialTest_apply (i : Fin 2)
    (φ : apm_m98J02_Test) (x : apm_m98J02_E) :
    apm_m98J02_partialTest i φ x = apm_m98J02_partial i φ x := rfl

lemma apm_m98J02_partialTest_coe (i : Fin 2)
    (φ : apm_m98J02_Test) :
    (apm_m98J02_partialTest i φ : apm_m98J02_E → ℝ) =
      apm_m98J02_partial i φ := rfl

/-- The formal adjoint expression occurring in the frozen statement really
is a test function. -/
noncomputable def apm_m98J02_formalAdjointTest
    (φ : apm_m98J02_Test) : apm_m98J02_Test :=
  2 • apm_m98J02_partialTest 0 (apm_m98J02_partialTest 0 φ) +
    apm_m98J02_partialTest 1 φ +
    3 • apm_m98J02_partialTest 0 (apm_m98J02_partialTest 1 φ)

@[simp] lemma apm_m98J02_formalAdjointTest_apply
    (φ : apm_m98J02_Test) (x : apm_m98J02_E) :
    apm_m98J02_formalAdjointTest φ x =
      apm_m98J02_formalAdjoint (φ : apm_m98J02_E → ℝ) x := by
  simp [apm_m98J02_formalAdjointTest, apm_m98J02_formalAdjoint,
    apm_m98J02_partialTest_coe]

/-- Shared cutoff-independence fact for a compactly supported distribution. -/
noncomputable def apm_m98J02_cutoff_independence_aux_mul
    (f g : apm_m98J02_Test) : apm_m98J02_Test :=
  TestFunction.mk (fun x ↦ f x * g x) (f.contDiff.mul g.contDiff)
    f.hasCompactSupport.mul_right (by simp)

@[simp] lemma apm_m98J02_cutoff_independence_aux_mul_apply
    (f g : apm_m98J02_Test) (x : apm_m98J02_E) :
    apm_m98J02_cutoff_independence_aux_mul f g x = f x * g x := rfl

theorem apm_m98J02_cutoff_independence
    (u : apm_m98J02_Dist) (F : apm_m98J02_E → ℝ)
    (K₁ K₂ : Set apm_m98J02_E) (χ₁ χ₂ Ψ₁ Ψ₂ : apm_m98J02_Test)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hu₁ : ∀ η : apm_m98J02_Test,
      Disjoint (tsupport (η : apm_m98J02_E → ℝ)) K₁ → u η = 0)
    (hu₂ : ∀ η : apm_m98J02_Test,
      Disjoint (tsupport (η : apm_m98J02_E → ℝ)) K₂ → u η = 0)
    (hχ₁ : (∃ U : Set apm_m98J02_E, IsOpen U ∧ K₁ ⊆ U ∧ ∀ x ∈ U, χ₁ x = 1))
    (hχ₂ : (∃ U : Set apm_m98J02_E, IsOpen U ∧ K₂ ⊆ U ∧ ∀ x ∈ U, χ₂ x = 1))
    (hΨ₁ : ∀ x, Ψ₁ x = χ₁ x * F x)
    (hΨ₂ : ∀ x, Ψ₂ x = χ₂ x * F x) :
    u Ψ₁ = u Ψ₂ := by
  obtain ⟨U₁, hU₁, hK₁U, hχ₁U⟩ := hχ₁
  obtain ⟨U₂, hU₂, hK₂U, hχ₂U⟩ := hχ₂
  let η₁ : apm_m98J02_Test :=
    Ψ₁ - apm_m98J02_cutoff_independence_aux_mul χ₂ Ψ₁
  let η₂ : apm_m98J02_Test :=
    apm_m98J02_cutoff_independence_aux_mul χ₁ Ψ₂ - Ψ₂
  have hd₁ : Disjoint (tsupport (η₁ : apm_m98J02_E → ℝ)) K₂ := by
    rw [Set.disjoint_left]
    intro a ha haK
    have haU := hK₂U haK
    rw [tsupport] at ha
    obtain ⟨b, hbU, hb⟩ := mem_closure_iff.mp ha U₂ hU₂ haU
    exact hb (by simp [η₁, hχ₂U b hbU])
  have hd₂ : Disjoint (tsupport (η₂ : apm_m98J02_E → ℝ)) K₁ := by
    rw [Set.disjoint_left]
    intro a ha haK
    have haU := hK₁U haK
    rw [tsupport] at ha
    obtain ⟨b, hbU, hb⟩ := mem_closure_iff.mp ha U₁ hU₁ haU
    exact hb (by simp [η₂, hχ₁U b hbU])
  have hsum : Ψ₁ - Ψ₂ = η₁ + η₂ := by
    ext a
    change Ψ₁ a - Ψ₂ a =
      (Ψ₁ a - χ₂ a * Ψ₁ a) + (χ₁ a * Ψ₂ a - Ψ₂ a)
    rw [hΨ₁ a, hΨ₂ a]
    ring
  have hz : u (Ψ₁ - Ψ₂) = 0 := by
    rw [hsum]
    simp [hu₂ η₁ hd₁, hu₁ η₂ hd₂]
  exact sub_eq_zero.mp (by simpa using hz)

lemma apm_m98J02_translated_pairing_calculus_aux_partial_translate
    (i : Fin 2) (φ : apm_m98J02_Test) (y x : apm_m98J02_E) :
    apm_m98J02_partial i (fun z : apm_m98J02_E => φ (z + y)) x =
      apm_m98J02_partial i φ (x + y) := by
  unfold apm_m98J02_partial
  have hφ : DifferentiableAt ℝ (φ : apm_m98J02_E → ℝ) (x + y) :=
    (φ.contDiff.differentiable (by simp)).differentiableAt
  have hadd : HasFDerivAt (fun z : apm_m98J02_E => z + y)
      (1 : apm_m98J02_E →L[ℝ] apm_m98J02_E) x :=
    hasFDerivAt_id x |>.add_const y
  have hc : HasFDerivAt (fun z : apm_m98J02_E => φ (z + y))
      ((fderiv ℝ (φ : apm_m98J02_E → ℝ) (x + y)).comp
        (1 : apm_m98J02_E →L[ℝ] apm_m98J02_E)) x := by
    simpa only [Function.comp_apply] using hφ.hasFDerivAt.comp x hadd
  rw [hc.fderiv]
  simp

lemma apm_m98J02_translated_pairing_calculus_aux_partial_translateTest
    (i : Fin 2) (φ : apm_m98J02_Test) (y x : apm_m98J02_E) :
    apm_m98J02_partial i
        (fun z : apm_m98J02_E => apm_m98J02_translateTest z φ y) x =
      apm_m98J02_translateTest x (apm_m98J02_partialTest i φ) y := by
  exact apm_m98J02_translated_pairing_calculus_aux_partial_translate i φ y x

/-! ### Split of `apm_m98J02_translated_pairing_calculus` (claude-14, 2026-10-13, after a partial
round-2 attempt that banked the two helpers above). (a) and (b) are facts about translation in the
test-function (LF) topology, via one fixed compact support stage near each `x`; (c) is the
calculus for a continuous linear `v`, given (a) and (b) as hypotheses. All three run in parallel.
m98A04 needs the same two facts on `ℝⁿ` (its `translateReflectStageLocal` lemmas). -/

lemma apm_m98J02_translateTest_continuous_aux_local_support
    (ψ : apm_m98J02_Test) (x₀ : apm_m98J02_E) :
    ∃ K : Set apm_m98J02_E, IsCompact K ∧
      ∃ U ∈ nhds x₀, ∀ x ∈ U,
        tsupport (apm_m98J02_translateTest x ψ : apm_m98J02_E → ℝ) ⊆ K := by
  let B : Set apm_m98J02_E := Metric.closedBall x₀ 1
  let S : Set apm_m98J02_E := tsupport (ψ : apm_m98J02_E → ℝ)
  let K : Set apm_m98J02_E :=
    (fun p : apm_m98J02_E × apm_m98J02_E => p.2 - p.1) '' (B ×ˢ S)
  have hK : IsCompact K := by
    have hB : IsCompact B := by
      dsimp [B]
      exact isCompact_closedBall x₀ 1
    have hS : IsCompact S := ψ.hasCompactSupport
    exact (hB.prod hS).image (by fun_prop)
  refine ⟨K, hK, Metric.ball x₀ 1, Metric.ball_mem_nhds x₀ zero_lt_one, ?_⟩
  intro x hx y hy
  have hxB : x ∈ B := Metric.ball_subset_closedBall hx
  have hsupport : x + y ∈ S := by
    have he := tsupport_comp_eq_preimage (ψ : apm_m98J02_E → ℝ)
      (Homeomorph.addLeft x)
    have hy' : y ∈ tsupport ((ψ : apm_m98J02_E → ℝ) ∘ Homeomorph.addLeft x) := by
      exact hy
    rw [he] at hy'
    exact hy'
  refine ⟨(x, x + y), ⟨hxB, hsupport⟩, ?_⟩
  simp

/-- (a) Translation is continuous into the test-function space. -/
theorem apm_m98J02_translateTest_continuous (ψ : apm_m98J02_Test) :
    Continuous (fun x : apm_m98J02_E ↦ apm_m98J02_translateTest x ψ) := by
  exact ConstructionTargets.TestFunctionTranslation.tftTranslate_continuous ψ

lemma apm_m98J02_translateTest_difference_quotient_aux_pointwise
    (ψ : apm_m98J02_Test) (i : Fin 2) (x y : apm_m98J02_E) :
    Filter.Tendsto (fun h : ℝ ↦ h⁻¹ *
        (apm_m98J02_translateTest (x + h • EuclideanSpace.single i 1) ψ y -
          apm_m98J02_translateTest x ψ y))
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
      (nhds (apm_m98J02_translateTest x (apm_m98J02_partialTest i ψ) y)) := by
  let e : apm_m98J02_E := EuclideanSpace.single i 1
  let F : ℝ → ℝ := fun h ↦ ψ (x + h • e + y)
  have hψ : DifferentiableAt ℝ (ψ : apm_m98J02_E → ℝ) (x + y) :=
    (ψ.contDiff.differentiable (by simp)).differentiableAt
  have hline : HasDerivAt (fun h : ℝ ↦ x + h • e + y)
      ((1 : ℝ) • e) 0 := by
    simpa [add_comm] using
      (((hasDerivAt_id (𝕜 := ℝ) (x := 0)).smul_const e).const_add x |>.add_const y)
  have hF : HasDerivAt F (apm_m98J02_partial i ψ (x + y)) 0 := by
    have hψ0 : DifferentiableAt ℝ (ψ : apm_m98J02_E → ℝ)
        (x + (0 : ℝ) • e + y) := by
      simpa using hψ
    have hc := hψ0.hasFDerivAt.comp 0 hline.hasFDerivAt
    simpa [F, e, apm_m98J02_partial] using hc.hasDerivAt
  simpa [F, e, apm_m98J02_translateTest_apply,
    apm_m98J02_partialTest_apply, apm_m98J02_partial, div_eq_inv_mul,
    mul_comm] using hF.tendsto_slope_zero

/-- (b) Difference quotients of translation converge in the test-function space. -/
lemma apm_m98J02_translateTest_difference_quotient_aux_fixed_stage
    (ψ : apm_m98J02_Test) (i : Fin 2) (x : apm_m98J02_E) :
    ∃ K : Compacts apm_m98J02_E,
      (∀ h : ℝ, |h| ≤ 1 →
        Function.support (apm_m98J02_translateTest
          (x + h • EuclideanSpace.single i 1) ψ : apm_m98J02_E → ℝ) ⊆ K) ∧
      Function.support (apm_m98J02_translateTest x
        (apm_m98J02_partialTest i ψ) : apm_m98J02_E → ℝ) ⊆ K := by
  refine ⟨ConstructionTargets.TestFunctionTranslation.tftTranslationCompact ψ x,
    fun h hh => ?_, ?_⟩
  · have hx : x + h • EuclideanSpace.single i 1 ∈ Metric.closedBall x 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs]
      exact hh
    exact (subset_tsupport _).trans
      (ConstructionTargets.TestFunctionTranslation.tft_local_fixed_support ψ x _ hx)
  · exact ConstructionTargets.TestFunctionTranslation.tft_directional_translate_function_support
      ψ x x _ (Metric.mem_closedBall_self zero_le_one)

lemma apm_m98J02_translateTest_difference_quotient_aux_stage_convergence
    (ψ : apm_m98J02_Test) (i : Fin 2) (x : apm_m98J02_E) :
    Filter.Tendsto (fun h : ℝ ↦ h⁻¹ •
        (apm_m98J02_translateTest (x + h • EuclideanSpace.single i 1) ψ -
          apm_m98J02_translateTest x ψ))
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
      (nhds (apm_m98J02_translateTest x (apm_m98J02_partialTest i ψ))) := by
  exact ConstructionTargets.TestFunctionTranslation.tftTranslate_difference_quotient ψ x
    (EuclideanSpace.single i 1)

theorem apm_m98J02_translateTest_difference_quotient (ψ : apm_m98J02_Test) (i : Fin 2)
    (x : apm_m98J02_E) :
    Filter.Tendsto (fun h : ℝ ↦ h⁻¹ • (apm_m98J02_translateTest (x + h • EuclideanSpace.single i 1) ψ - apm_m98J02_translateTest x ψ))
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) (nhds (apm_m98J02_translateTest x (apm_m98J02_partialTest i ψ))) := by
  exact apm_m98J02_translateTest_difference_quotient_aux_stage_convergence ψ i x

/-- (c) Calculus of `x ↦ v (τₓ φ)` from (a), (b): partials by continuity of `v`, then continuous
partials in `ℝ²` give `C¹`, and once more give `C²`. -/
lemma apm_m98J02_translated_pairing_calculus_of_facts_aux_slope
    (hdq : ∀ (ψ : apm_m98J02_Test) (i : Fin 2) (x : apm_m98J02_E),
      Filter.Tendsto (fun h : ℝ ↦ h⁻¹ • (apm_m98J02_translateTest
        (x + h • EuclideanSpace.single i 1) ψ - apm_m98J02_translateTest x ψ))
        (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
        (nhds (apm_m98J02_translateTest x (apm_m98J02_partialTest i ψ))))
    (v : apm_m98J02_Dist) (ψ : apm_m98J02_Test) (i : Fin 2)
    (x : apm_m98J02_E) :
    Filter.Tendsto (fun h : ℝ ↦ h⁻¹ *
        (v (apm_m98J02_translateTest (x + h • EuclideanSpace.single i 1) ψ) -
          v (apm_m98J02_translateTest x ψ)))
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
      (nhds (v (apm_m98J02_translateTest x (apm_m98J02_partialTest i ψ)))) := by
  have hv := v.continuous.continuousAt.tendsto.comp (hdq ψ i x)
  change Filter.Tendsto (fun h : ℝ => v (h⁻¹ •
      (apm_m98J02_translateTest (x + h • EuclideanSpace.single i 1) ψ -
        apm_m98J02_translateTest x ψ))) _ _ at hv
  simpa only [map_sub, map_smul, smul_eq_mul] using hv

lemma apm_m98J02_translated_pairing_calculus_of_facts_aux_continuous
    (hcont : ∀ ψ : apm_m98J02_Test,
      Continuous (fun x : apm_m98J02_E ↦ apm_m98J02_translateTest x ψ))
    (v : apm_m98J02_Dist) (ψ : apm_m98J02_Test) :
    Continuous (fun x : apm_m98J02_E => v (apm_m98J02_translateTest x ψ)) := by
  exact v.continuous.comp (hcont ψ)

/-- Continuous partial derivatives (as one-sided-free coordinate slope limits)
give a Fréchet derivative: the classical C¹ criterion on `ℝ²`. -/
lemma apm_m98J02_translated_pairing_calculus_of_facts_aux_hasFDerivAt_aux_line_zero
    (F : apm_m98J02_E → ℝ) (G : Fin 2 → apm_m98J02_E → ℝ)
    (hF : ∀ i x, Filter.Tendsto
      (fun h : ℝ ↦ h⁻¹ * (F (x + h • EuclideanSpace.single i 1) - F x))
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) (nhds (G i x)))
    (i : Fin 2) (z : apm_m98J02_E) :
    HasDerivAt (fun t : ℝ => F (z + t • EuclideanSpace.single i 1)) (G i z) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simpa [smul_eq_mul] using hF i z

lemma apm_m98J02_translated_pairing_calculus_of_facts_aux_hasFDerivAt_aux_line
    (F : apm_m98J02_E → ℝ) (G : Fin 2 → apm_m98J02_E → ℝ)
    (hF : ∀ i x, Filter.Tendsto
      (fun h : ℝ ↦ h⁻¹ * (F (x + h • EuclideanSpace.single i 1) - F x))
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) (nhds (G i x)))
    (i : Fin 2) (z : apm_m98J02_E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (z + s • EuclideanSpace.single i 1))
      (G i (z + t • EuclideanSpace.single i 1)) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  convert hF i (z + t • EuclideanSpace.single i 1) using 1
  funext s
  congr 3
  module

lemma apm_m98J02_translated_pairing_calculus_of_facts_aux_hasFDerivAt_aux_segment
    (F : apm_m98J02_E → ℝ) (G : Fin 2 → apm_m98J02_E → ℝ)
    (hF : ∀ i x, Filter.Tendsto
      (fun h : ℝ ↦ h⁻¹ * (F (x + h • EuclideanSpace.single i 1) - F x))
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) (nhds (G i x)))
    (i : Fin 2) (p : apm_m98J02_E) (c ε t : ℝ)
    (hε : ∀ s : ℝ, |s| ≤ |t| → |G i (p + s • EuclideanSpace.single i 1) - c| ≤ ε) :
    |F (p + t • EuclideanSpace.single i 1) - F p - c * t| ≤ ε * |t| := by
  have hd : ∀ s ∈ Set.Icc (-|t|) |t|, HasDerivWithinAt
      (fun s : ℝ => F (p + s • EuclideanSpace.single i 1) - c * s)
      (G i (p + s • EuclideanSpace.single i 1) - c) (Set.Icc (-|t|) |t|) s := by
    intro s _
    have := (apm_m98J02_translated_pairing_calculus_of_facts_aux_hasFDerivAt_aux_line F G hF i p s).sub ((hasDerivAt_id s).const_mul c)
    simpa using this.hasDerivWithinAt
  have hb : ∀ s ∈ Set.Icc (-|t|) |t|,
      ‖G i (p + s • EuclideanSpace.single i 1) - c‖ ≤ ε := by
    intro s hs
    rw [Real.norm_eq_abs]
    exact hε s (abs_le.2 hs)
  have key := (convex_Icc (-|t|) |t|).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (x := 0) (y := t) (by constructor <;> simp) (by constructor <;> [exact neg_abs_le t; exact le_abs_self t])
  simp only [Real.norm_eq_abs, sub_zero, zero_smul, add_zero, mul_zero] at key
  convert key using 2
  ring

lemma apm_m98J02_translated_pairing_calculus_of_facts_aux_hasFDerivAt
    (F : apm_m98J02_E → ℝ) (G : Fin 2 → apm_m98J02_E → ℝ)
    (hG : ∀ i, Continuous (G i))
    (hF : ∀ i x, Filter.Tendsto (fun h : ℝ ↦ h⁻¹ * (F (x + h • EuclideanSpace.single i 1) - F x))
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) (nhds (G i x)))
    (x : apm_m98J02_E) :
    HasFDerivAt F (∑ i, G i x • (EuclideanSpace.proj i : apm_m98J02_E →L[ℝ] ℝ)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ0, hδ0, H0⟩ := Metric.continuousAt_iff.1 (hG 0).continuousAt (ε / 2) (by positivity)
  obtain ⟨δ1, hδ1, H1⟩ := Metric.continuousAt_iff.1 (hG 1).continuousAt (ε / 2) (by positivity)
  have hball : ∀ i y, dist y x < min δ0 δ1 → |G i y - G i x| ≤ ε / 2 := by
    intro i y hy
    rw [← Real.dist_eq]
    fin_cases i
    · exact (H0 (lt_of_lt_of_le hy (min_le_left _ _))).le
    · exact (H1 (lt_of_lt_of_le hy (min_le_right _ _))).le
  filter_upwards [Metric.ball_mem_nhds (0 : apm_m98J02_E) (lt_min hδ0 hδ1)] with h hh
  rw [Metric.mem_ball, dist_zero_right] at hh
  have hsq : ‖h‖ ^ 2 = h 0 ^ 2 + h 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  have hnorm2 : ∀ a b : ℝ, ‖a • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
      b • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
    intro a b
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [sq_abs]
  have hle : ∀ a b : ℝ, |a| ≤ |h 0| → |b| ≤ |h 1| →
      ‖a • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        b • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)‖ ≤ ‖h‖ := by
    intro a b ha hb
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hnorm2, hsq]
    have := sq_le_sq.2 ha
    have := sq_le_sq.2 hb
    linarith
  have hdec : h = h 0 • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
      h 1 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
    ext j; fin_cases j <;> simp
  have e0 := apm_m98J02_translated_pairing_calculus_of_facts_aux_hasFDerivAt_aux_segment F G hF 0 x (G 0 x) (ε / 2) (h 0) (fun s hs => by
    apply hball
    rw [dist_eq_norm, add_sub_cancel_left]
    refine lt_of_le_of_lt ?_ hh
    simpa using hle s 0 hs (by simp))
  have e1 := apm_m98J02_translated_pairing_calculus_of_facts_aux_hasFDerivAt_aux_segment F G hF 1 (x + h 0 • EuclideanSpace.single 0 1) (G 1 x) (ε / 2) (h 1)
    (fun s hs => by
      apply hball
      rw [dist_eq_norm, add_assoc, add_sub_cancel_left]
      exact lt_of_le_of_lt (hle (h 0) s le_rfl hs) hh)
  have happ : (∑ i, G i x • (EuclideanSpace.proj i : apm_m98J02_E →L[ℝ] ℝ)) h =
      G 0 x * h 0 + G 1 x * h 1 := by
    simp [Fin.sum_univ_two]
  rw [happ, Real.norm_eq_abs]
  have hx : x + h = x + h 0 • EuclideanSpace.single 0 1 + h 1 • EuclideanSpace.single 1 1 := by
    conv_lhs => rw [hdec]
    abel
  rw [hx]
  have h0le : |h 0| ≤ ‖h‖ := by simpa using PiLp.norm_apply_le h 0
  have h1le : |h 1| ≤ ‖h‖ := by simpa using PiLp.norm_apply_le h 1
  calc |F (x + h 0 • EuclideanSpace.single 0 1 + h 1 • EuclideanSpace.single 1 1) - F x -
        (G 0 x * h 0 + G 1 x * h 1)|
      = |(F (x + h 0 • EuclideanSpace.single 0 1 + h 1 • EuclideanSpace.single 1 1) -
          F (x + h 0 • EuclideanSpace.single 0 1) - G 1 x * h 1) +
        (F (x + h 0 • EuclideanSpace.single 0 1) - F x - G 0 x * h 0)| := by ring_nf
    _ ≤ ε / 2 * |h 1| + ε / 2 * |h 0| := (abs_add_le _ _).trans (add_le_add e1 e0)
    _ ≤ ε * ‖h‖ := by nlinarith

lemma apm_m98J02_translated_pairing_calculus_of_facts_aux_hasFDerivAt_pairing
    (hcont : ∀ ψ : apm_m98J02_Test,
      Continuous (fun x : apm_m98J02_E ↦ apm_m98J02_translateTest x ψ))
    (hdq : ∀ (ψ : apm_m98J02_Test) (i : Fin 2) (x : apm_m98J02_E),
      Filter.Tendsto (fun h : ℝ ↦ h⁻¹ • (apm_m98J02_translateTest
        (x + h • EuclideanSpace.single i 1) ψ - apm_m98J02_translateTest x ψ))
        (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
        (nhds (apm_m98J02_translateTest x (apm_m98J02_partialTest i ψ))))
    (v : apm_m98J02_Dist) (ψ : apm_m98J02_Test) (x : apm_m98J02_E) :
    HasFDerivAt (fun z : apm_m98J02_E => v (apm_m98J02_translateTest z ψ))
      (∑ i, v (apm_m98J02_translateTest x (apm_m98J02_partialTest i ψ)) •
        (EuclideanSpace.proj i : apm_m98J02_E →L[ℝ] ℝ)) x :=
  apm_m98J02_translated_pairing_calculus_of_facts_aux_hasFDerivAt _
    (fun i z => v (apm_m98J02_translateTest z (apm_m98J02_partialTest i ψ)))
    (fun i => apm_m98J02_translated_pairing_calculus_of_facts_aux_continuous hcont v _)
    (fun i z => apm_m98J02_translated_pairing_calculus_of_facts_aux_slope hdq v ψ i z) x

lemma apm_m98J02_translated_pairing_calculus_of_facts_aux_contDiff_one
    (hcont : ∀ ψ : apm_m98J02_Test,
      Continuous (fun x : apm_m98J02_E ↦ apm_m98J02_translateTest x ψ))
    (hdq : ∀ (ψ : apm_m98J02_Test) (i : Fin 2) (x : apm_m98J02_E),
      Filter.Tendsto (fun h : ℝ ↦ h⁻¹ • (apm_m98J02_translateTest
        (x + h • EuclideanSpace.single i 1) ψ - apm_m98J02_translateTest x ψ))
        (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
        (nhds (apm_m98J02_translateTest x (apm_m98J02_partialTest i ψ))))
    (v : apm_m98J02_Dist) (ψ : apm_m98J02_Test) :
    ContDiff ℝ 1 (fun z : apm_m98J02_E => v (apm_m98J02_translateTest z ψ)) := by
  rw [show (1 : WithTop ℕ∞) = ((0 : ℕ) : WithTop ℕ∞) + 1 by norm_num, contDiff_succ_iff_hasFDerivAt]
  refine ⟨fun x => ∑ i, v (apm_m98J02_translateTest x (apm_m98J02_partialTest i ψ)) •
      (EuclideanSpace.proj i : apm_m98J02_E →L[ℝ] ℝ), ?_,
    fun x => apm_m98J02_translated_pairing_calculus_of_facts_aux_hasFDerivAt_pairing hcont hdq v ψ x⟩
  rw [Nat.cast_zero]
  refine contDiff_zero.2 (continuous_finset_sum _ fun i _ => ?_)
  exact (apm_m98J02_translated_pairing_calculus_of_facts_aux_continuous hcont v _).smul continuous_const

lemma apm_m98J02_translated_pairing_calculus_of_facts_aux_partial
    (hcont : ∀ ψ : apm_m98J02_Test,
      Continuous (fun x : apm_m98J02_E ↦ apm_m98J02_translateTest x ψ))
    (hdq : ∀ (ψ : apm_m98J02_Test) (i : Fin 2) (x : apm_m98J02_E),
      Filter.Tendsto (fun h : ℝ ↦ h⁻¹ • (apm_m98J02_translateTest
        (x + h • EuclideanSpace.single i 1) ψ - apm_m98J02_translateTest x ψ))
        (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
        (nhds (apm_m98J02_translateTest x (apm_m98J02_partialTest i ψ))))
    (v : apm_m98J02_Dist) (ψ : apm_m98J02_Test) (i : Fin 2) :
    apm_m98J02_partial i (fun z : apm_m98J02_E => v (apm_m98J02_translateTest z ψ)) =
      fun x => v (apm_m98J02_translateTest x (apm_m98J02_partialTest i ψ)) := by
  funext x
  unfold apm_m98J02_partial
  rw [(apm_m98J02_translated_pairing_calculus_of_facts_aux_hasFDerivAt_pairing hcont hdq v ψ x).fderiv]
  fin_cases i <;> simp [Fin.sum_univ_two]

theorem apm_m98J02_translated_pairing_calculus_of_facts
    (hcont : ∀ ψ : apm_m98J02_Test, Continuous (fun x : apm_m98J02_E ↦ apm_m98J02_translateTest x ψ))
    (hdq : ∀ (ψ : apm_m98J02_Test) (i : Fin 2) (x : apm_m98J02_E),
      Filter.Tendsto (fun h : ℝ ↦ h⁻¹ • (apm_m98J02_translateTest (x + h • EuclideanSpace.single i 1) ψ - apm_m98J02_translateTest x ψ))
        (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) (nhds (apm_m98J02_translateTest x (apm_m98J02_partialTest i ψ))))
    (v : apm_m98J02_Dist) (φ : apm_m98J02_Test) :
    ContDiff ℝ 2 (fun x : apm_m98J02_E =>
      v (apm_m98J02_translateTest x φ)) ∧
    (∀ i x,
      apm_m98J02_partial i
          (fun z : apm_m98J02_E => v (apm_m98J02_translateTest z φ)) x =
        v (apm_m98J02_translateTest x (apm_m98J02_partialTest i φ))) ∧
    (∀ i j x,
      apm_m98J02_partial i
          (apm_m98J02_partial j
            (fun z : apm_m98J02_E => v (apm_m98J02_translateTest z φ))) x =
        v (apm_m98J02_translateTest x
          (apm_m98J02_partialTest i (apm_m98J02_partialTest j φ)))) := by
  refine ⟨?_, fun i x => by rw [apm_m98J02_translated_pairing_calculus_of_facts_aux_partial hcont hdq], fun i j x => by
    rw [apm_m98J02_translated_pairing_calculus_of_facts_aux_partial hcont hdq, apm_m98J02_translated_pairing_calculus_of_facts_aux_partial hcont hdq]⟩
  rw [show (2 : WithTop ℕ∞) = ((1 : ℕ) : WithTop ℕ∞) + 1 by norm_num, contDiff_succ_iff_hasFDerivAt]
  refine ⟨fun x => ∑ i, v (apm_m98J02_translateTest x (apm_m98J02_partialTest i φ)) •
      (EuclideanSpace.proj i : apm_m98J02_E →L[ℝ] ℝ), ?_,
    fun x => apm_m98J02_translated_pairing_calculus_of_facts_aux_hasFDerivAt_pairing hcont hdq v φ x⟩
  rw [Nat.cast_one]
  refine ContDiff.sum fun i _ => ?_
  exact (apm_m98J02_translated_pairing_calculus_of_facts_aux_contDiff_one hcont hdq v _).smul contDiff_const

/-- Shared translation calculus needed by construction, differentiation of
convolution, and the PDE identity. -/
theorem apm_m98J02_translated_pairing_calculus
    (v : apm_m98J02_Dist) (φ : apm_m98J02_Test) :
    ContDiff ℝ 2 (fun x : apm_m98J02_E =>
      v (apm_m98J02_translateTest x φ)) ∧
    (∀ i x,
      apm_m98J02_partial i
          (fun z : apm_m98J02_E => v (apm_m98J02_translateTest z φ)) x =
        v (apm_m98J02_translateTest x (apm_m98J02_partialTest i φ))) ∧
    (∀ i j x,
      apm_m98J02_partial i
          (apm_m98J02_partial j
            (fun z : apm_m98J02_E => v (apm_m98J02_translateTest z φ))) x =
        v (apm_m98J02_translateTest x
          (apm_m98J02_partialTest i (apm_m98J02_partialTest j φ)))) := by
  exact apm_m98J02_translated_pairing_calculus_of_facts
    apm_m98J02_translateTest_continuous apm_m98J02_translateTest_difference_quotient v φ

/-- The cutoff-based predicate defines at most one distribution.  This rules
out choosing a smoother witness when the fixed fundamental solution is bad. -/
theorem apm_m98J02_isConvolution_unique
    (u v w₁ w₂ : apm_m98J02_Dist)
    (h₁ : apm_m98J02_isConvolution u v w₁)
    (h₂ : apm_m98J02_isConvolution u v w₂) :
    w₁ = w₂ := by
  ext φ
  obtain ⟨K₁, χ₁, Ψ₁, hK₁, hu₁, hχ₁, hΨ₁, hw₁⟩ := h₁ φ
  obtain ⟨K₂, χ₂, Ψ₂, hK₂, hu₂, hχ₂, hΨ₂, hw₂⟩ := h₂ φ
  rw [hw₁, hw₂]
  apply apm_m98J02_cutoff_independence u
    (fun x => v (apm_m98J02_translateTest x φ)) K₁ K₂ χ₁ χ₂ Ψ₁ Ψ₂
    hK₁ hK₂ hu₁ hu₂ hχ₁ hχ₂
  · intro x
    obtain ⟨τ, hτ, hx⟩ := hΨ₁ x
    rw [hx]
    congr 1
    apply congrArg v
    ext y
    exact hτ y
  · intro x
    obtain ⟨τ, hτ, hx⟩ := hΨ₂ x
    rw [hx]
    congr 1
    apply congrArg v
    ext y
    exact hτ y

/-- Why this unblocks the convolution step in `apm_m98j02`: this packages the
iterated pairing
`φ ↦ u (x ↦ χ x * v (y ↦ φ (x + y)))` as a continuous linear functional on
the LF space of test functions.  The conclusion records all cutoff and
translation identities needed by the concrete convolution definition. -/
theorem apm_m98J02_bridge_2
    (u v : apm_m98J02_Dist) (K : Set apm_m98J02_E)
    (hK : IsCompact K)
    (huK : ∀ η : apm_m98J02_Test,
      Disjoint (tsupport (η : apm_m98J02_E → ℝ)) K → u η = 0) :
    ∃ w : apm_m98J02_Dist, apm_m98J02_isConvolution u v w := by
  sorry

theorem apm_m98J02_regular_convolution_is_C2
    (f k : apm_m98J02_E → ℝ) (w₀ w : apm_m98J02_Dist)
    (hf : ContDiff ℝ 2 f) (hfc : IsCompact (tsupport f))
    (hk : LocallyIntegrable k)
    (hw₀rep : apm_m98J02_representsFunction w₀ k)
    (hconv : apm_m98J02_isConvolution
      (apm_m98J02_regularDistribution f hf.continuous hfc) w₀ w) :
    ∃ g : apm_m98J02_E → ℝ,
      apm_m98J02_representsFunction w g ∧ ContDiff ℝ 2 g := by
  sorry

theorem apm_m98J02_convolution_solves_fundamental
    (f : apm_m98J02_E → ℝ) (w₀ w : apm_m98J02_Dist)
    (hf : ContDiff ℝ 2 f) (hfc : IsCompact (tsupport f))
    (hw₀ : apm_m98J02_solvesT w₀ (fun φ ↦ φ 0))
    (hconv : apm_m98J02_isConvolution
      (apm_m98J02_regularDistribution f hf.continuous hfc) w₀ w) :
    apm_m98J02_solvesT w (fun φ ↦ ∫ x, f x * φ x) := by
  sorry

theorem apm_m98J02_constantDistribution_homogeneous :
    apm_m98J02_solvesT apm_m98J02_constantDistribution (fun _ ↦ 0) := by
  sorry

theorem apm_m98j02 :
    (∀ u v : apm_m98J02_Dist,
      apm_m98J02_hasCompactSupport u →
      apm_m98J02_hasCompactSupport v →
      apm_m98J02_hasCompactSupport (u + v)) ∧
    (∀ u v : apm_m98J02_Dist,
      apm_m98J02_hasCompactSupport u →
        ∃ w : apm_m98J02_Dist, apm_m98J02_isConvolution u v w) ∧
    ∀ (f k : apm_m98J02_E → ℝ) (w₀ : apm_m98J02_Dist),
      ContDiff ℝ 2 f → IsCompact (tsupport f) →
      LocallyIntegrable k → apm_m98J02_representsFunction w₀ k →
      apm_m98J02_solvesT w₀ (fun φ ↦ φ 0) →
      ∃ (u w w' : apm_m98J02_Dist) (g : apm_m98J02_E → ℝ),
        apm_m98J02_representsFunction u f ∧
        apm_m98J02_hasCompactSupport u ∧
        apm_m98J02_isConvolution u w₀ w ∧
        apm_m98J02_representsFunction w g ∧
        ContDiff ℝ 2 g ∧
        apm_m98J02_solvesT w (fun φ ↦ ∫ x, f x * φ x) ∧
        w' ≠ w ∧
        apm_m98J02_solvesT w' (fun φ ↦ ∫ x, f x * φ x) := by
  refine ⟨?_, ?_⟩
  · intro u v hu hv
    exact apm_m98J02_hasCompactSupport_add u v hu hv
  · constructor
    · intro u v hu
      obtain ⟨K, hK, huK⟩ := hu
      exact apm_m98J02_bridge_2 u v K hK huK
    · intro f k w₀ hf hfc hk hw₀rep hw₀
      let u := apm_m98J02_regularDistribution f hf.continuous hfc
      have huRep : apm_m98J02_representsFunction u f :=
        apm_m98J02_regularDistribution_represents f hf.continuous hfc
      have huComp : apm_m98J02_hasCompactSupport u :=
        apm_m98J02_regularDistribution_hasCompactSupport f hf.continuous hfc
      obtain ⟨K, hK, huK⟩ := huComp
      obtain ⟨w, hconv⟩ := apm_m98J02_bridge_2 u w₀ K hK huK
      obtain ⟨g, hwRep, hg⟩ :=
        apm_m98J02_regular_convolution_is_C2 f k w₀ w hf hfc hk hw₀rep hconv
      have hwSolve :=
        apm_m98J02_convolution_solves_fundamental f w₀ w hf hfc hw₀ hconv
      let w' := w + apm_m98J02_constantDistribution
      have hw'ne : w' ≠ w := by
        intro heq
        have hc : apm_m98J02_constantDistribution = 0 := by
          apply add_left_cancel (a := w)
          simpa [w'] using heq
        exact apm_m98J02_constantDistribution_ne_zero hc
      have hw'Solve : apm_m98J02_solvesT w'
          (fun φ ↦ ∫ x, f x * φ x) :=
        apm_m98J02_solvesT_add_homogeneous w
          apm_m98J02_constantDistribution _ hwSolve
          apm_m98J02_constantDistribution_homogeneous
      exact ⟨u, w, w', g, huRep,
        apm_m98J02_regularDistribution_hasCompactSupport f hf.continuous hfc,
        hconv, hwRep, hg,
        hwSolve, hw'ne, hw'Solve⟩

#print axioms apm_m98j02
