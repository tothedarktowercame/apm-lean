import Mathlib

/-!
# APM m02J01

## Statement repairs

The spelling `primative` in the source is read as `primitive`; no mathematical
change is made.

## Encoding notes

The statement uses Mathlib's genuine LF-topological test-function and
distribution spaces.  Distributional differentiation is exposed by its
defining action on the pointwise derivative of every bundled test function.
-/

open MeasureTheory Set TopologicalSpace
open scoped Distributions ContDiff

def apm_m02j01_IsDistributionalDerivative
    (v u : Distribution (⊤ : Opens ℝ) ℝ ⊤) : Prop :=
  ∀ φ dφ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
    (∀ x : ℝ, dφ x = deriv (φ : ℝ → ℝ) x) → u φ = -v dφ

/-- The derivative of a test function has total integral zero. This is the
function-level necessity direction of part (a). -/
lemma apm_m02j01_integral_deriv_testFunction_eq_zero
    (ψ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    ∫ x : ℝ, deriv (ψ : ℝ → ℝ) x = 0 := by
  have hdiff : ContDiff ℝ 1 (ψ : ℝ → ℝ) := ψ.contDiff.of_le (by simp)
  have hcompact : HasCompactSupport (ψ : ℝ → ℝ) := ψ.hasCompactSupport
  have hint : Integrable (deriv (ψ : ℝ → ℝ)) :=
    hdiff.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport hcompact.deriv
  rw [← integral_add_compl measurableSet_Iic hint, compl_Iic]
  rw [hcompact.integral_Iic_deriv_eq hdiff 0,
    hcompact.integral_Ioi_deriv_eq hdiff 0]
  ring

lemma apm_m02j01_integral_eq_zero_of_eq_deriv
    (φ ψ : TestFunction (⊤ : Opens ℝ) ℝ ⊤)
    (h : ∀ x : ℝ, φ x = deriv (ψ : ℝ → ℝ) x) :
    ∫ x : ℝ, φ x = 0 := by
  calc
    ∫ x : ℝ, φ x = ∫ x : ℝ, deriv (ψ : ℝ → ℝ) x :=
      integral_congr_ae (Filter.Eventually.of_forall h)
    _ = 0 := apm_m02j01_integral_deriv_testFunction_eq_zero ψ

/-- The ordinary interval-integral primitive of a test function is smooth and
has the original function as its derivative. -/
lemma apm_m02j01_primitive_smooth
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    let P : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, φ t
    ContDiff ℝ ∞ P ∧ ∀ x : ℝ, deriv P x = φ x := by
  let P : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, φ t
  have hderiv (x : ℝ) : HasDerivAt P (φ x) x := by
    exact intervalIntegral.integral_hasDerivAt_right
      (φ.contDiff.continuous.intervalIntegrable 0 x)
      (φ.contDiff.continuous.stronglyMeasurableAtFilter volume (nhds x))
      φ.contDiff.continuous.continuousAt
  have hderiv_eq : deriv P = (φ : ℝ → ℝ) := by
    funext x
    exact (hderiv x).deriv
  refine ⟨(contDiff_infty_iff_deriv.mpr ⟨?_, ?_⟩), fun x => congrFun hderiv_eq x⟩
  · exact fun x => (hderiv x).differentiableAt
  · rw [hderiv_eq]
    exact φ.contDiff

/-- The same smoothness calculation with an arbitrary base point. -/
lemma apm_m02j01_primitive_smooth_base
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) (a : ℝ) :
    let P : ℝ → ℝ := fun x => ∫ t in a..x, φ t
    ContDiff ℝ ∞ P ∧ ∀ x : ℝ, deriv P x = φ x := by
  let P : ℝ → ℝ := fun x => ∫ t in a..x, φ t
  have hderiv (x : ℝ) : HasDerivAt P (φ x) x := by
    exact intervalIntegral.integral_hasDerivAt_right
      (φ.contDiff.continuous.intervalIntegrable a x)
      (φ.contDiff.continuous.stronglyMeasurableAtFilter volume (nhds x))
      φ.contDiff.continuous.continuousAt
  have hderiv_eq : deriv P = (φ : ℝ → ℝ) := by
    funext x
    exact (hderiv x).deriv
  refine ⟨(contDiff_infty_iff_deriv.mpr ⟨?_, ?_⟩), fun x => congrFun hderiv_eq x⟩
  · exact fun x => (hderiv x).differentiableAt
  · rw [hderiv_eq]
    exact φ.contDiff

/-- With an explicit support interval and zero total integral, the primitive
based at its left endpoint is supported in the corresponding closed interval. -/
lemma apm_m02j01_primitive_support
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) (a b : ℝ)
    (hsupp : Function.support (φ : ℝ → ℝ) ⊆ Ioc a b)
    (hzero : ∫ x : ℝ, φ x = 0) :
    Function.support (fun x => ∫ t in a..x, φ t) ⊆ Icc a b := by
  intro x hx
  by_contra hxab
  rw [mem_Icc, not_and_or] at hxab
  rcases hxab with hxa | hxb
  · have hpoint : Set.EqOn (φ : ℝ → ℝ) 0 (uIcc a x) := by
      intro t ht
      have hta : t ≤ a := by
        rw [uIcc_comm, uIcc_of_le (le_of_not_ge hxa)] at ht
        exact ht.2
      by_contra hφt
      have ht_support : t ∈ Function.support (φ : ℝ → ℝ) := hφt
      exact (not_lt_of_ge hta) (hsupp ht_support).1
    have hint : (∫ t in a..x, φ t) = 0 := by
      rw [intervalIntegral.integral_congr hpoint]
      simp
    exact hx hint
  · have hsupp' : Function.support (φ : ℝ → ℝ) ⊆ Ioc a x := by
      intro t ht
      exact ⟨(hsupp ht).1, (hsupp ht).2.trans (le_of_not_ge hxb)⟩
    have hint : (∫ t in a..x, φ t) = 0 := by
      rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp', hzero]
    exact hx hint

/-- Consequently the endpoint-based primitive has compact support. -/
lemma apm_m02j01_primitive_hasCompactSupport
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) (a b : ℝ)
    (hsupp : Function.support (φ : ℝ → ℝ) ⊆ Ioc a b)
    (hzero : ∫ x : ℝ, φ x = 0) :
    HasCompactSupport (fun x => ∫ t in a..x, φ t) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (apm_m02j01_primitive_support φ a b hsupp hzero)

/-- A zero-integral test function is the derivative of a bundled test
function.  This completes both directions of the function-level assertion. -/
lemma apm_m02j01_exists_testFunction_primitive
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤)
    (hzero : ∫ x : ℝ, φ x = 0) :
    ∃ ψ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
      ∀ x : ℝ, φ x = deriv (ψ : ℝ → ℝ) x := by
  have hc : IsCompact (tsupport (φ : ℝ → ℝ)) := φ.hasCompactSupport
  obtain ⟨a, b, hab⟩ :=
    bddBelow_bddAbove_iff_subset_Icc.mp ⟨hc.bddBelow, hc.bddAbove⟩
  let A : ℝ := a - 1
  let P : ℝ → ℝ := fun x => ∫ t in A..x, φ t
  have hsupp : Function.support (φ : ℝ → ℝ) ⊆ Ioc A b := by
    intro x hx
    have hxab : x ∈ Icc a b := hab (subset_closure hx)
    exact ⟨by dsimp [A]; linarith [hxab.1], hxab.2⟩
  have hsmooth : ContDiff ℝ ∞ P ∧ ∀ x : ℝ, deriv P x = φ x :=
    apm_m02j01_primitive_smooth_base φ A
  have hcompact : HasCompactSupport P :=
    apm_m02j01_primitive_hasCompactSupport φ A b hsupp hzero
  let ψ : TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
    TestFunction.mk P hsmooth.1 hcompact (by simp)
  refine ⟨ψ, fun x => ?_⟩
  exact (hsmooth.2 x).symm

/-- Integration on a fixed-support stage, realized through `L¹` for the
restricted finite measure. -/
noncomputable def apm_m02j01_integralSupportedInCLM (K : Compacts ℝ) :
    ContDiffMapSupportedIn ℝ ℝ ⊤ K →L[ℝ] ℝ := by
  letI : Fact (volume (K : Set ℝ) < (⊤ : ENNReal)) := ⟨K.isCompact.measure_lt_top⟩
  exact L1.integralCLM ∘L
    BoundedContinuousFunction.toLp 1 (volume.restrict (K : Set ℝ)) ℝ ∘L
      ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ

lemma apm_m02j01_integralSupportedInCLM_apply (K : Compacts ℝ)
    (φ : ContDiffMapSupportedIn ℝ ℝ ⊤ K) :
    apm_m02j01_integralSupportedInCLM K φ = ∫ x : ℝ, φ x := by
  letI : Fact (volume (K : Set ℝ) < (⊤ : ENNReal)) := ⟨K.isCompact.measure_lt_top⟩
  rw [apm_m02j01_integralSupportedInCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ← L1.integral_eq, L1.integral_eq_integral]
  rw [integral_congr_ae (BoundedContinuousFunction.coeFn_toLp 1
    (volume.restrict (K : Set ℝ)) ℝ _)]
  change (∫ x in (K : Set ℝ), φ x) = ∫ x : ℝ, φ x
  exact setIntegral_eq_integral_of_ae_compl_eq_zero <|
    Filter.Eventually.of_forall fun x hx => by
      by_contra hne
      exact hx (φ.tsupport_subset (subset_closure hne))

/-- The total integral is a continuous linear functional for the LF topology
on test functions. -/
noncomputable def apm_m02j01_integralCLM :
    TestFunction (⊤ : Opens ℝ) ℝ ⊤ →L[ℝ] ℝ :=
  TestFunction.limitCLM ℝ (fun φ => ∫ x : ℝ, φ x)
    (fun K _ => apm_m02j01_integralSupportedInCLM K)
    (fun K _ φ => (apm_m02j01_integralSupportedInCLM_apply K φ).symm)

@[simp] lemma apm_m02j01_integralCLM_apply
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    apm_m02j01_integralCLM φ = ∫ x : ℝ, φ x := rfl

/-- A fixed unit-mass test function, used to split an arbitrary test function
into its zero-mass part and a one-dimensional complement. -/
noncomputable def apm_m02j01_unitMassTestFunction :
    TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
  let f : ContDiffBump (0 : ℝ) := default
  TestFunction.mk (f.normed volume) f.contDiff_normed
    f.hasCompactSupport_normed (by simp)

lemma apm_m02j01_integral_unitMassTestFunction :
    ∫ x : ℝ, apm_m02j01_unitMassTestFunction x = 1 := by
  let f : ContDiffBump (0 : ℝ) := default
  exact f.integral_normed (μ := volume)

/-- Continuous projection onto the codimension-one subspace of test functions
with total integral zero. -/
noncomputable def apm_m02j01_zeroMassProjection :
    TestFunction (⊤ : Opens ℝ) ℝ ⊤ →L[ℝ]
      TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
  ContinuousLinearMap.id ℝ _ -
    apm_m02j01_integralCLM.smulRight apm_m02j01_unitMassTestFunction

@[simp] lemma apm_m02j01_zeroMassProjection_apply
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    apm_m02j01_zeroMassProjection φ =
      φ - (∫ x : ℝ, φ x) • apm_m02j01_unitMassTestFunction := by
  rfl

lemma apm_m02j01_integral_zeroMassProjection
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    ∫ x : ℝ, apm_m02j01_zeroMassProjection φ x = 0 := by
  rw [apm_m02j01_zeroMassProjection_apply]
  have hφint : Integrable (φ : ℝ → ℝ) :=
    φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hρint : Integrable (apm_m02j01_unitMassTestFunction : ℝ → ℝ) :=
    apm_m02j01_unitMassTestFunction.contDiff.continuous.integrable_of_hasCompactSupport
      apm_m02j01_unitMassTestFunction.hasCompactSupport
  rw [show ((φ - (∫ x : ℝ, φ x) • apm_m02j01_unitMassTestFunction :
      TestFunction (⊤ : Opens ℝ) ℝ ⊤) : ℝ → ℝ) =
        fun x => φ x - (∫ y : ℝ, φ y) * apm_m02j01_unitMassTestFunction x by rfl]
  rw [integral_sub hφint (hρint.const_mul _), integral_const_mul,
    apm_m02j01_integral_unitMassTestFunction]
  ring

/-- The canonical primitive which vanishes on the left tail. -/
noncomputable def apm_m02j01_leftTailPrimitive
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) : ℝ → ℝ :=
  fun x => ∫ t in Iic x, φ t

lemma apm_m02j01_leftTailPrimitive_eq_interval
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) (a b : ℝ)
    (hsupp : Function.support (φ : ℝ → ℝ) ⊆ Ioc a b) (x : ℝ) :
    apm_m02j01_leftTailPrimitive φ x = ∫ t in a..x, φ t := by
  have hint : Integrable (φ : ℝ → ℝ) :=
    φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have ha : ∫ t in Iic a, φ t = 0 := by
    exact setIntegral_eq_zero_of_forall_eq_zero fun t hta => by
      by_contra hφ
      exact (not_lt_of_ge hta) (hsupp hφ).1
  have hsub :
      (∫ t in Iic x, φ t) - ∫ t in Iic a, φ t = ∫ t in a..x, φ t :=
    intervalIntegral.integral_Iic_sub_Iic (a := a) (b := x)
      hint.integrableOn hint.integrableOn
  rw [ha, sub_zero] at hsub
  exact hsub

/-- For zero total mass, the canonical left-tail primitive is itself a test
function and differentiates to the original test function. -/
lemma apm_m02j01_exists_leftTailPrimitive_testFunction
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤)
    (hzero : ∫ x : ℝ, φ x = 0) :
    ∃ ψ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
      (ψ : ℝ → ℝ) = apm_m02j01_leftTailPrimitive φ ∧
      ∀ x : ℝ, deriv (ψ : ℝ → ℝ) x = φ x := by
  have hc : IsCompact (tsupport (φ : ℝ → ℝ)) := φ.hasCompactSupport
  obtain ⟨a, b, hab⟩ :=
    bddBelow_bddAbove_iff_subset_Icc.mp ⟨hc.bddBelow, hc.bddAbove⟩
  let A : ℝ := a - 1
  let P : ℝ → ℝ := fun x => ∫ t in A..x, φ t
  have hsupp : Function.support (φ : ℝ → ℝ) ⊆ Ioc A b := by
    intro x hx
    have hxab : x ∈ Icc a b := hab (subset_closure hx)
    exact ⟨by dsimp [A]; linarith [hxab.1], hxab.2⟩
  have heq : apm_m02j01_leftTailPrimitive φ = P := by
    funext x
    exact apm_m02j01_leftTailPrimitive_eq_interval φ A b hsupp x
  have hsmoothP : ContDiff ℝ ∞ P ∧ ∀ x : ℝ, deriv P x = φ x :=
    apm_m02j01_primitive_smooth_base φ A
  have hcompactP : HasCompactSupport P :=
    apm_m02j01_primitive_hasCompactSupport φ A b hsupp hzero
  have hsmooth : ContDiff ℝ ∞ (apm_m02j01_leftTailPrimitive φ) := by
    rw [heq]
    exact hsmoothP.1
  have hcompact : HasCompactSupport (apm_m02j01_leftTailPrimitive φ) := by
    rw [heq]
    exact hcompactP
  let ψ : TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
    TestFunction.mk (apm_m02j01_leftTailPrimitive φ) hsmooth hcompact (by simp)
  refine ⟨ψ, rfl, fun x => ?_⟩
  change deriv (apm_m02j01_leftTailPrimitive φ) x = φ x
  rw [heq]
  exact hsmoothP.2 x

/-- The bundled canonical primitive on a zero-mass input. -/
noncomputable def apm_m02j01_leftTailPrimitiveTestFunction
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤)
    (hzero : ∫ x : ℝ, φ x = 0) : TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
  Classical.choose (apm_m02j01_exists_leftTailPrimitive_testFunction φ hzero)

@[simp] lemma apm_m02j01_leftTailPrimitiveTestFunction_coe
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤)
    (hzero : ∫ x : ℝ, φ x = 0) :
    (apm_m02j01_leftTailPrimitiveTestFunction φ hzero : ℝ → ℝ) =
      apm_m02j01_leftTailPrimitive φ :=
  (Classical.choose_spec
    (apm_m02j01_exists_leftTailPrimitive_testFunction φ hzero)).1

lemma apm_m02j01_deriv_leftTailPrimitiveTestFunction
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤)
    (hzero : ∫ x : ℝ, φ x = 0) (x : ℝ) :
    deriv (apm_m02j01_leftTailPrimitiveTestFunction φ hzero : ℝ → ℝ) x = φ x :=
  (Classical.choose_spec
    (apm_m02j01_exists_leftTailPrimitive_testFunction φ hzero)).2 x

/-- The normalized primitive on arbitrary test functions: first project away
the mass, then take the canonical left-tail primitive. -/
noncomputable def apm_m02j01_normalizedPrimitive
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
  apm_m02j01_leftTailPrimitiveTestFunction
    (apm_m02j01_zeroMassProjection φ)
    (apm_m02j01_integral_zeroMassProjection φ)

@[simp] lemma apm_m02j01_normalizedPrimitive_coe
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    (apm_m02j01_normalizedPrimitive φ : ℝ → ℝ) =
      apm_m02j01_leftTailPrimitive (apm_m02j01_zeroMassProjection φ) :=
  apm_m02j01_leftTailPrimitiveTestFunction_coe _ _

lemma apm_m02j01_deriv_normalizedPrimitive
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) (x : ℝ) :
    deriv (apm_m02j01_normalizedPrimitive φ : ℝ → ℝ) x =
      apm_m02j01_zeroMassProjection φ x :=
  apm_m02j01_deriv_leftTailPrimitiveTestFunction _ _ x

lemma apm_m02j01_normalizedPrimitive_add
    (φ ψ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    apm_m02j01_normalizedPrimitive (φ + ψ) =
      apm_m02j01_normalizedPrimitive φ + apm_m02j01_normalizedPrimitive ψ := by
  ext x
  simp only [apm_m02j01_normalizedPrimitive_coe,
    apm_m02j01_leftTailPrimitive, TestFunction.coe_add, Pi.add_apply]
  rw [map_add]
  change (∫ t in Iic x, (apm_m02j01_zeroMassProjection φ) t +
    (apm_m02j01_zeroMassProjection ψ) t) = _
  rw [integral_add]
  · exact (apm_m02j01_zeroMassProjection φ).contDiff.continuous
      |>.integrable_of_hasCompactSupport
        (apm_m02j01_zeroMassProjection φ).hasCompactSupport |>.integrableOn
  · exact (apm_m02j01_zeroMassProjection ψ).contDiff.continuous
      |>.integrable_of_hasCompactSupport
        (apm_m02j01_zeroMassProjection ψ).hasCompactSupport |>.integrableOn

lemma apm_m02j01_normalizedPrimitive_smul (c : ℝ)
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    apm_m02j01_normalizedPrimitive (c • φ) =
      c • apm_m02j01_normalizedPrimitive φ := by
  ext x
  simp only [apm_m02j01_normalizedPrimitive_coe,
    apm_m02j01_leftTailPrimitive, TestFunction.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [map_smul]
  change (∫ t in Iic x, c * (apm_m02j01_zeroMassProjection φ) t) = _
  rw [integral_const_mul]

/-- The normalized primitive as an algebraic linear map. Its continuity is the
remaining LF-topological obligation. -/
noncomputable def apm_m02j01_normalizedPrimitiveLM :
    TestFunction (⊤ : Opens ℝ) ℝ ⊤ →ₗ[ℝ]
      TestFunction (⊤ : Opens ℝ) ℝ ⊤ where
  toFun := apm_m02j01_normalizedPrimitive
  map_add' := apm_m02j01_normalizedPrimitive_add
  map_smul' := apm_m02j01_normalizedPrimitive_smul

@[simp] lemma apm_m02j01_normalizedPrimitiveLM_apply
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    apm_m02j01_normalizedPrimitiveLM φ = apm_m02j01_normalizedPrimitive φ := rfl

lemma apm_m02j01_exists_supportBounds (K : Compacts ℝ) :
    ∃ p : ℝ × ℝ,
      (K : Set ℝ) ∪ tsupport (apm_m02j01_unitMassTestFunction : ℝ → ℝ) ⊆
        Icc p.1 p.2 := by
  have hc : IsCompact ((K : Set ℝ) ∪
      tsupport (apm_m02j01_unitMassTestFunction : ℝ → ℝ)) :=
    K.isCompact.union apm_m02j01_unitMassTestFunction.hasCompactSupport
  obtain ⟨a, b, hab⟩ :=
    bddBelow_bddAbove_iff_subset_Icc.mp ⟨hc.bddBelow, hc.bddAbove⟩
  exact ⟨(a, b), hab⟩

/-- Bounds, depending only on an input support stage, which contain both that
stage and the fixed normalizing bump. -/
noncomputable def apm_m02j01_supportBounds (K : Compacts ℝ) : ℝ × ℝ :=
  Classical.choose (apm_m02j01_exists_supportBounds K)

lemma apm_m02j01_supportBounds_spec (K : Compacts ℝ) :
    (K : Set ℝ) ∪ tsupport (apm_m02j01_unitMassTestFunction : ℝ → ℝ) ⊆
      Icc (apm_m02j01_supportBounds K).1 (apm_m02j01_supportBounds K).2 :=
  Classical.choose_spec (apm_m02j01_exists_supportBounds K)

/-- A compact stage containing every normalized primitive of an input from
the stage `K`. The left endpoint is enlarged by one to make support inclusion
strict where the endpoint primitive lemma requires it. -/
noncomputable def apm_m02j01_primitiveSupportCompact (K : Compacts ℝ) : Compacts ℝ :=
  ⟨Icc ((apm_m02j01_supportBounds K).1 - 1)
      (apm_m02j01_supportBounds K).2, isCompact_Icc⟩

lemma apm_m02j01_zeroMassProjection_support_stage (K : Compacts ℝ)
    (φ : ContDiffMapSupportedIn ℝ ℝ ⊤ K) :
    Function.support
        (apm_m02j01_zeroMassProjection
          (TestFunction.ofSupportedIn (by simp) φ) : ℝ → ℝ) ⊆
      Ioc ((apm_m02j01_supportBounds K).1 - 1)
        (apm_m02j01_supportBounds K).2 := by
  let f : TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
    TestFunction.ofSupportedIn (by simp) φ
  have htf : tsupport (f : ℝ → ℝ) ⊆ (K : Set ℝ) := by
    intro x hx
    exact φ.tsupport_subset hx
  intro x hx
  change f x - (∫ y : ℝ, f y) * apm_m02j01_unitMassTestFunction x ≠ 0 at hx
  have hor : f x ≠ 0 ∨ apm_m02j01_unitMassTestFunction x ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h.1, h.2] at hx
  have hxI := apm_m02j01_supportBounds_spec K
    (hor.elim (fun h => Or.inl (htf (subset_closure h)))
      (fun h => Or.inr (subset_closure h)))
  exact ⟨by linarith [hxI.1], hxI.2⟩

lemma apm_m02j01_normalizedPrimitive_support_stage (K : Compacts ℝ)
    (φ : ContDiffMapSupportedIn ℝ ℝ ⊤ K) :
    Function.support
        (apm_m02j01_normalizedPrimitive
          (TestFunction.ofSupportedIn (by simp) φ) : ℝ → ℝ) ⊆
      (apm_m02j01_primitiveSupportCompact K : Set ℝ) := by
  let f : TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
    TestFunction.ofSupportedIn (by simp) φ
  let q := apm_m02j01_zeroMassProjection f
  let A := (apm_m02j01_supportBounds K).1 - 1
  let b := (apm_m02j01_supportBounds K).2
  have hq : Function.support (q : ℝ → ℝ) ⊆ Ioc A b :=
    apm_m02j01_zeroMassProjection_support_stage K φ
  have hzero : ∫ x : ℝ, q x = 0 := apm_m02j01_integral_zeroMassProjection f
  have hleft : apm_m02j01_leftTailPrimitive q = fun x => ∫ t in A..x, q t := by
    funext x
    exact apm_m02j01_leftTailPrimitive_eq_interval q A b hq x
  rw [show (apm_m02j01_normalizedPrimitive f : ℝ → ℝ) =
    apm_m02j01_leftTailPrimitive q by
      exact apm_m02j01_normalizedPrimitive_coe f, hleft]
  exact apm_m02j01_primitive_support q A b hq hzero

/-- Fixed-stage factor of the normalized primitive. This packages the exact
source and target Fréchet spaces needed for the remaining seminorm proof. -/
noncomputable def apm_m02j01_normalizedPrimitiveSupportedInLM (K : Compacts ℝ) :
    ContDiffMapSupportedIn ℝ ℝ ⊤ K →ₗ[ℝ]
      ContDiffMapSupportedIn ℝ ℝ ⊤ (apm_m02j01_primitiveSupportCompact K) where
  toFun φ := ContDiffMapSupportedIn.of_support_subset
    (apm_m02j01_normalizedPrimitive
      (TestFunction.ofSupportedIn (by simp) φ)).contDiff
    (apm_m02j01_normalizedPrimitive_support_stage K φ)
  map_add' φ ψ := by
    ext x
    exact congrFun (congrArg (fun f : TestFunction (⊤ : Opens ℝ) ℝ ⊤ =>
      (f : ℝ → ℝ)) (apm_m02j01_normalizedPrimitive_add
        (TestFunction.ofSupportedIn (by simp) φ)
        (TestFunction.ofSupportedIn (by simp) ψ))) x
  map_smul' c φ := by
    ext x
    exact congrFun (congrArg (fun f : TestFunction (⊤ : Opens ℝ) ℝ ⊤ =>
      (f : ℝ → ℝ)) (apm_m02j01_normalizedPrimitive_smul c
        (TestFunction.ofSupportedIn (by simp) φ))) x

@[simp] lemma apm_m02j01_normalizedPrimitiveSupportedInLM_apply_coe
    (K : Compacts ℝ) (φ : ContDiffMapSupportedIn ℝ ℝ ⊤ K) :
    (apm_m02j01_normalizedPrimitiveSupportedInLM K φ : ℝ → ℝ) =
      apm_m02j01_normalizedPrimitive (TestFunction.ofSupportedIn (by simp) φ) := rfl

/-- The cumulative integral is uniformly bounded by the `L¹` norm. This is
the order-zero estimate underlying continuity of the primitive. -/
lemma apm_m02j01_abs_leftTailPrimitive_le_integral_abs
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) (x : ℝ) :
    |apm_m02j01_leftTailPrimitive φ x| ≤ ∫ t : ℝ, |φ t| := by
  have hint : Integrable (fun t : ℝ => |φ t|) :=
    (φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).abs
  calc
    |apm_m02j01_leftTailPrimitive φ x| =
        ‖∫ t in Iic x, φ t‖ := by rfl
    _ ≤ ∫ t in Iic x, ‖φ t‖ := norm_integral_le_integral_norm _
    _ = ∫ t in Iic x, |φ t| := by rfl
    _ ≤ ∫ t : ℝ, |φ t| := setIntegral_le_integral hint
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)

/-- On a fixed support stage, the `L¹` norm is controlled by its zeroth
defining seminorm. -/
lemma apm_m02j01_integral_abs_le_stageSeminorm (K : Compacts ℝ)
    (φ : ContDiffMapSupportedIn ℝ ℝ ⊤ K) :
    ∫ x : ℝ, |φ x| ≤
      N[ℝ]_{K, 0} φ * volume.real (K : Set ℝ) := by
  have hsupport : ∫ x : ℝ, |φ x| = ∫ x in (K : Set ℝ), |φ x| := by
    symm
    exact setIntegral_eq_integral_of_ae_compl_eq_zero <|
      Filter.Eventually.of_forall fun x hx => by
        rw [abs_eq_zero]
        by_contra hne
        exact hx (φ.tsupport_subset (subset_closure hne))
  rw [hsupport]
  letI : Fact (volume (K : Set ℝ) < (⊤ : ENNReal)) := ⟨K.isCompact.measure_lt_top⟩
  have hbound := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (K : Set ℝ))
    (f := fun x : ℝ => |φ x|)
    (C := N[ℝ]_{K, 0} φ)
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_abs] using
        (ContDiffMapSupportedIn.norm_apply_le_seminorm ℝ (f := φ) (x := x)))
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at hbound
  simpa [Measure.restrict_apply_univ] using hbound

lemma apm_m02j01_abs_integral_le_stageSeminorm (K : Compacts ℝ)
    (φ : ContDiffMapSupportedIn ℝ ℝ ⊤ K) :
    |∫ x : ℝ, φ x| ≤
      N[ℝ]_{K, 0} φ * volume.real (K : Set ℝ) :=
  (abs_integral_le_integral_abs).trans
    (apm_m02j01_integral_abs_le_stageSeminorm K φ)

lemma apm_m02j01_integral_abs_unitMassTestFunction :
    ∫ x : ℝ, |apm_m02j01_unitMassTestFunction x| = 1 := by
  have hnonneg : ∀ x : ℝ, 0 ≤ apm_m02j01_unitMassTestFunction x := by
    intro x
    let f : ContDiffBump (0 : ℝ) := default
    exact f.nonneg_normed x
  rw [show (fun x : ℝ => |apm_m02j01_unitMassTestFunction x|) =
    apm_m02j01_unitMassTestFunction by
      funext x
      exact abs_of_nonneg (hnonneg x)]
  exact apm_m02j01_integral_unitMassTestFunction

/-- The zero-mass projection has a fixed-stage `L¹` bound using only the
zeroth source seminorm. -/
lemma apm_m02j01_integral_abs_zeroMassProjection_stage (K : Compacts ℝ)
    (φ : ContDiffMapSupportedIn ℝ ℝ ⊤ K) :
    let f : TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
      TestFunction.ofSupportedIn (by simp) φ
    ∫ x : ℝ, |apm_m02j01_zeroMassProjection f x| ≤
      2 * N[ℝ]_{K, 0} φ * volume.real (K : Set ℝ) := by
  let f : TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
    TestFunction.ofSupportedIn (by simp) φ
  have hfint : Integrable (f : ℝ → ℝ) :=
    f.contDiff.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hρint : Integrable (apm_m02j01_unitMassTestFunction : ℝ → ℝ) :=
    apm_m02j01_unitMassTestFunction.contDiff.continuous.integrable_of_hasCompactSupport
      apm_m02j01_unitMassTestFunction.hasCompactSupport
  have hqint : Integrable
      (apm_m02j01_zeroMassProjection f : ℝ → ℝ) :=
    (apm_m02j01_zeroMassProjection f).contDiff.continuous
      |>.integrable_of_hasCompactSupport
        (apm_m02j01_zeroMassProjection f).hasCompactSupport
  have hmono :
      (∫ x : ℝ, |apm_m02j01_zeroMassProjection f x|) ≤
        ∫ x : ℝ, |f x| + |∫ y : ℝ, f y| *
          |apm_m02j01_unitMassTestFunction x| := by
    apply integral_mono hqint.abs (hfint.abs.add (hρint.abs.const_mul _))
    intro x
    rw [apm_m02j01_zeroMassProjection_apply]
    change |f x - (∫ y : ℝ, f y) * apm_m02j01_unitMassTestFunction x| ≤ _
    calc
      _ ≤ |f x| + |(∫ y : ℝ, f y) * apm_m02j01_unitMassTestFunction x| :=
        abs_sub _ _
      _ = _ := by rw [abs_mul]; rfl
  rw [integral_add hfint.abs (hρint.abs.const_mul _), integral_const_mul,
    apm_m02j01_integral_abs_unitMassTestFunction, mul_one] at hmono
  have habs := apm_m02j01_integral_abs_le_stageSeminorm K φ
  change (∫ x : ℝ, |f x|) ≤ _ at habs
  have hmass := apm_m02j01_abs_integral_le_stageSeminorm K φ
  change |∫ x : ℝ, f x| ≤ _ at hmass
  have hN : 0 ≤ N[ℝ]_{K, 0} φ := apply_nonneg _ _
  nlinarith

lemma apm_m02j01_abs_normalizedPrimitive_stage (K : Compacts ℝ)
    (φ : ContDiffMapSupportedIn ℝ ℝ ⊤ K) (x : ℝ) :
    let f : TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
      TestFunction.ofSupportedIn (by simp) φ
    |apm_m02j01_normalizedPrimitive f x| ≤
      2 * N[ℝ]_{K, 0} φ * volume.real (K : Set ℝ) := by
  let f : TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
    TestFunction.ofSupportedIn (by simp) φ
  dsimp only
  rw [show (apm_m02j01_normalizedPrimitive f : ℝ → ℝ) =
    apm_m02j01_leftTailPrimitive (apm_m02j01_zeroMassProjection f) by
      exact apm_m02j01_normalizedPrimitive_coe f]
  exact (apm_m02j01_abs_leftTailPrimitive_le_integral_abs
    (apm_m02j01_zeroMassProjection f) x).trans
      (apm_m02j01_integral_abs_zeroMassProjection_stage K φ)

/-- Zeroth target seminorm estimate for the fixed-stage primitive map. -/
lemma apm_m02j01_normalizedPrimitiveSupportedInLM_seminorm_zero (K : Compacts ℝ)
    (φ : ContDiffMapSupportedIn ℝ ℝ ⊤ K) :
    N[ℝ]_{apm_m02j01_primitiveSupportCompact K, 0}
        (apm_m02j01_normalizedPrimitiveSupportedInLM K φ) ≤
      2 * volume.real (K : Set ℝ) * N[ℝ]_{K, 0} φ := by
  rw [ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (by positivity)]
  intro x _
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  have h := apm_m02j01_abs_normalizedPrimitive_stage K φ x
  rw [apm_m02j01_normalizedPrimitiveSupportedInLM_apply_coe]
  nlinarith

/-- Every positive-order derivative of the primitive is exactly the preceding
derivative of the zero-mass projection, expressed at the norm level matching
the defining Fréchet seminorms. -/
lemma apm_m02j01_norm_iteratedFDeriv_normalizedPrimitive_succ
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) (i : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ (i + 1)
        (apm_m02j01_normalizedPrimitive φ : ℝ → ℝ) x‖ =
      ‖iteratedFDeriv ℝ i
        (apm_m02j01_zeroMassProjection φ : ℝ → ℝ) x‖ := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_succ']
  have hderiv : deriv (apm_m02j01_normalizedPrimitive φ : ℝ → ℝ) =
      (apm_m02j01_zeroMassProjection φ : ℝ → ℝ) := by
    funext y
    exact apm_m02j01_deriv_normalizedPrimitive φ y
  rw [hderiv, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]

lemma apm_m02j01_norm_iteratedFDeriv_normalizedPrimitiveSupportedInLM_succ
    (K : Compacts ℝ) (φ : ContDiffMapSupportedIn ℝ ℝ ⊤ K)
    (i : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ (i + 1)
        (apm_m02j01_normalizedPrimitiveSupportedInLM K φ : ℝ → ℝ) x‖ =
      ‖iteratedFDeriv ℝ i
        (apm_m02j01_zeroMassProjection
          (TestFunction.ofSupportedIn (by simp) φ) : ℝ → ℝ) x‖ := by
  rw [apm_m02j01_normalizedPrimitiveSupportedInLM_apply_coe]
  exact apm_m02j01_norm_iteratedFDeriv_normalizedPrimitive_succ _ i x

/-- The normalizing bump, bundled in the fixed target support stage. -/
noncomputable def apm_m02j01_unitMassSupportedIn (K : Compacts ℝ) :
    ContDiffMapSupportedIn ℝ ℝ ⊤ (apm_m02j01_primitiveSupportCompact K) :=
  ContDiffMapSupportedIn.of_support_subset
    apm_m02j01_unitMassTestFunction.contDiff <| by
      intro x hx
      have hI := apm_m02j01_supportBounds_spec K
        (Or.inr (subset_closure hx))
      exact ⟨by linarith [hI.1], hI.2⟩

@[simp] lemma apm_m02j01_unitMassSupportedIn_coe (K : Compacts ℝ) :
    (apm_m02j01_unitMassSupportedIn K : ℝ → ℝ) =
      apm_m02j01_unitMassTestFunction := rfl

/-- Pointwise positive-order estimate for the projected input. -/
lemma apm_m02j01_norm_iteratedFDeriv_zeroMassProjection_stage
    (K : Compacts ℝ) (φ : ContDiffMapSupportedIn ℝ ℝ ⊤ K)
    (i : ℕ) (x : ℝ) :
    let f : TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
      TestFunction.ofSupportedIn (by simp) φ
    ‖iteratedFDeriv ℝ i
        (apm_m02j01_zeroMassProjection f : ℝ → ℝ) x‖ ≤
      N[ℝ]_{K, i} φ +
        (N[ℝ]_{K, 0} φ * volume.real (K : Set ℝ)) *
          N[ℝ]_{apm_m02j01_primitiveSupportCompact K, i}
            (apm_m02j01_unitMassSupportedIn K) := by
  let f : TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
    TestFunction.ofSupportedIn (by simp) φ
  dsimp only
  rw [apm_m02j01_zeroMassProjection_apply]
  change ‖iteratedFDeriv ℝ i
    ((f : ℝ → ℝ) - fun y => (∫ z : ℝ, f z) •
      apm_m02j01_unitMassTestFunction y) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply
    (f.contDiff.of_le (by exact_mod_cast le_top)).contDiffAt
    ((apm_m02j01_unitMassTestFunction.contDiff.of_le
      (by exact_mod_cast le_top)).const_smul _).contDiffAt,
    iteratedFDeriv_const_smul_apply'
      (apm_m02j01_unitMassTestFunction.contDiff.of_le
        (by exact_mod_cast le_top)).contDiffAt]
  calc
    ‖iteratedFDeriv ℝ i (f : ℝ → ℝ) x -
        (∫ z : ℝ, f z) • iteratedFDeriv ℝ i
          (apm_m02j01_unitMassTestFunction : ℝ → ℝ) x‖
        ≤ ‖iteratedFDeriv ℝ i (f : ℝ → ℝ) x‖ +
          ‖(∫ z : ℝ, f z) • iteratedFDeriv ℝ i
            (apm_m02j01_unitMassTestFunction : ℝ → ℝ) x‖ := norm_sub_le _ _
    _ ≤ N[ℝ]_{K, i} φ + |∫ z : ℝ, f z| *
          N[ℝ]_{apm_m02j01_primitiveSupportCompact K, i}
            (apm_m02j01_unitMassSupportedIn K) := by
      gcongr
      · exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top
          ℝ (f := φ)
      · rw [norm_smul, Real.norm_eq_abs]
        gcongr
        exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top
          ℝ (f := apm_m02j01_unitMassSupportedIn K)
    _ ≤ _ := by
      gcongr
      have hmass := apm_m02j01_abs_integral_le_stageSeminorm K φ
      change |∫ z : ℝ, f z| ≤ _ at hmass
      exact hmass

/-- Positive-order target seminorm estimate for the fixed-stage primitive. -/
lemma apm_m02j01_normalizedPrimitiveSupportedInLM_seminorm_succ
    (K : Compacts ℝ) (φ : ContDiffMapSupportedIn ℝ ℝ ⊤ K) (i : ℕ) :
    N[ℝ]_{apm_m02j01_primitiveSupportCompact K, i + 1}
        (apm_m02j01_normalizedPrimitiveSupportedInLM K φ) ≤
      N[ℝ]_{K, i} φ +
        (N[ℝ]_{K, 0} φ * volume.real (K : Set ℝ)) *
          N[ℝ]_{apm_m02j01_primitiveSupportCompact K, i}
            (apm_m02j01_unitMassSupportedIn K) := by
  rw [ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (by positivity)]
  intro x _
  rw [apm_m02j01_norm_iteratedFDeriv_normalizedPrimitiveSupportedInLM_succ]
  exact apm_m02j01_norm_iteratedFDeriv_zeroMassProjection_stage K φ i x

lemma apm_m02j01_continuous_normalizedPrimitiveSupportedInLM (K : Compacts ℝ) :
    Continuous (apm_m02j01_normalizedPrimitiveSupportedInLM K) := by
  apply WithSeminorms.continuous_of_isBounded
    (ContDiffMapSupportedIn.withSeminorms' ℝ ℝ ℝ ⊤ K)
    (ContDiffMapSupportedIn.withSeminorms ℝ ℝ ℝ ⊤
      (apm_m02j01_primitiveSupportCompact K))
  apply Seminorm.IsBounded.of_real
  intro j
  cases j with
  | zero =>
      refine ⟨{0}, 2 * volume.real (K : Set ℝ), fun φ => ?_⟩
      have h := apm_m02j01_normalizedPrimitiveSupportedInLM_seminorm_zero K φ
      have h0 : N[ℝ]_{K, 0} φ ≤
          (ContDiffMapSupportedIn.supSeminorm ℝ ℝ ℝ ⊤ K 0) φ := by
        exact Seminorm.le_def.mp (Finset.le_sup
          (f := fun k => N[ℝ]_{K, k}) (Finset.mem_Iic.mpr le_rfl)) φ
      simp only [Finset.sup_singleton]
      calc
        _ ≤ 2 * volume.real (K : Set ℝ) * N[ℝ]_{K, 0} φ := h
        _ ≤ 2 * volume.real (K : Set ℝ) *
            (ContDiffMapSupportedIn.supSeminorm ℝ ℝ ℝ ⊤ K 0) φ := by
          gcongr
  | succ i =>
      let R := N[ℝ]_{apm_m02j01_primitiveSupportCompact K, i}
        (apm_m02j01_unitMassSupportedIn K)
      refine ⟨{i}, 1 + volume.real (K : Set ℝ) * R, fun φ => ?_⟩
      have h := apm_m02j01_normalizedPrimitiveSupportedInLM_seminorm_succ K φ i
      have hi : N[ℝ]_{K, i} φ ≤
          (ContDiffMapSupportedIn.supSeminorm ℝ ℝ ℝ ⊤ K i) φ := by
        exact Seminorm.le_def.mp (Finset.le_sup
          (f := fun k => N[ℝ]_{K, k}) (Finset.mem_Iic.mpr le_rfl)) φ
      have h0 : N[ℝ]_{K, 0} φ ≤
          (ContDiffMapSupportedIn.supSeminorm ℝ ℝ ℝ ⊤ K i) φ := by
        exact Seminorm.le_def.mp (Finset.le_sup
          (f := fun k => N[ℝ]_{K, k}) (Finset.mem_Iic.mpr (Nat.zero_le i))) φ
      have hS : 0 ≤ (ContDiffMapSupportedIn.supSeminorm ℝ ℝ ℝ ⊤ K i) φ :=
        apply_nonneg _ _
      have hM : 0 ≤ volume.real (K : Set ℝ) := measureReal_nonneg
      have hR : 0 ≤ R := apply_nonneg _ _
      dsimp [R] at h hR ⊢
      simp only [Finset.sup_singleton]
      calc
        _ ≤ N[ℝ]_{K, i} φ +
            (N[ℝ]_{K, 0} φ * volume.real (K : Set ℝ)) *
              N[ℝ]_{apm_m02j01_primitiveSupportCompact K, i}
                (apm_m02j01_unitMassSupportedIn K) := h
        _ ≤ (ContDiffMapSupportedIn.supSeminorm ℝ ℝ ℝ ⊤ K i) φ +
            ((ContDiffMapSupportedIn.supSeminorm ℝ ℝ ℝ ⊤ K i) φ *
              volume.real (K : Set ℝ)) *
                N[ℝ]_{apm_m02j01_primitiveSupportCompact K, i}
                  (apm_m02j01_unitMassSupportedIn K) := by gcongr
        _ = (1 + volume.real (K : Set ℝ) *
              N[ℝ]_{apm_m02j01_primitiveSupportCompact K, i}
                (apm_m02j01_unitMassSupportedIn K)) *
              (ContDiffMapSupportedIn.supSeminorm ℝ ℝ ℝ ⊤ K i) φ := by ring

noncomputable def apm_m02j01_normalizedPrimitiveSupportedInCLM (K : Compacts ℝ) :
    ContDiffMapSupportedIn ℝ ℝ ⊤ K →L[ℝ]
      ContDiffMapSupportedIn ℝ ℝ ⊤ (apm_m02j01_primitiveSupportCompact K) where
  toLinearMap := apm_m02j01_normalizedPrimitiveSupportedInLM K
  cont := apm_m02j01_continuous_normalizedPrimitiveSupportedInLM K

/-- The continuous normalized primitive operator on the LF test-function
space. -/
noncomputable def apm_m02j01_normalizedPrimitiveCLM :
    TestFunction (⊤ : Opens ℝ) ℝ ⊤ →L[ℝ]
      TestFunction (⊤ : Opens ℝ) ℝ ⊤ where
  toLinearMap := apm_m02j01_normalizedPrimitiveLM
  cont := by
    change Continuous (apm_m02j01_normalizedPrimitiveLM :
      TestFunction (⊤ : Opens ℝ) ℝ ⊤ → TestFunction (⊤ : Opens ℝ) ℝ ⊤)
    rw [TestFunction.continuous_iff_continuous_comp
      apm_m02j01_normalizedPrimitiveLM]
    intro K K_sub
    have hL : (apm_m02j01_primitiveSupportCompact K : Set ℝ) ⊆
        (⊤ : Opens ℝ) := fun _ _ => trivial
    have hcont : Continuous
        (TestFunction.ofSupportedInCLM ℝ hL ∘L
          apm_m02j01_normalizedPrimitiveSupportedInCLM K) :=
      (TestFunction.ofSupportedInCLM ℝ hL ∘L
        apm_m02j01_normalizedPrimitiveSupportedInCLM K).continuous
    exact hcont.congr fun φ => by
      ext x
      rfl

@[simp] lemma apm_m02j01_normalizedPrimitiveCLM_apply
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    apm_m02j01_normalizedPrimitiveCLM φ = apm_m02j01_normalizedPrimitive φ := rfl

theorem apm_m02j01 :
    (∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
      (∫ x : ℝ, φ x) = 0 ↔
        ∃ ψ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
          ∀ x : ℝ, φ x = deriv (ψ : ℝ → ℝ) x) ∧
    (∀ u : Distribution (⊤ : Opens ℝ) ℝ ⊤,
      ∃ v : Distribution (⊤ : Opens ℝ) ℝ ⊤,
        apm_m02j01_IsDistributionalDerivative v u) ∧
    (∀ u v₁ v₂ : Distribution (⊤ : Opens ℝ) ℝ ⊤,
      apm_m02j01_IsDistributionalDerivative v₁ u →
      apm_m02j01_IsDistributionalDerivative v₂ u →
      ∃ c : ℝ, ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
        (v₁ - v₂) φ = c * ∫ x : ℝ, φ x) := by
  constructor
  · intro φ
    constructor
    · exact apm_m02j01_exists_testFunction_primitive φ
    · rintro ⟨ψ, hψ⟩
      exact apm_m02j01_integral_eq_zero_of_eq_deriv φ ψ hψ
  · constructor
    · intro u
      let v : Distribution (⊤ : Opens ℝ) ℝ ⊤ :=
        -(u.comp apm_m02j01_normalizedPrimitiveCLM)
      refine ⟨v, fun φ dφ hdφ => ?_⟩
      have hdint : ∫ x : ℝ, dφ x = 0 :=
        apm_m02j01_integral_eq_zero_of_eq_deriv dφ φ hdφ
      have hproj : apm_m02j01_zeroMassProjection dφ = dφ := by
        ext x
        simp [apm_m02j01_zeroMassProjection_apply, hdint]
      have hprimitive : apm_m02j01_normalizedPrimitiveCLM dφ = φ := by
        ext x
        rw [apm_m02j01_normalizedPrimitiveCLM_apply]
        rw [show (apm_m02j01_normalizedPrimitive dφ : ℝ → ℝ) =
          apm_m02j01_leftTailPrimitive
            (apm_m02j01_zeroMassProjection dφ) by
              exact apm_m02j01_normalizedPrimitive_coe dφ]
        rw [hproj]
        change (∫ t in Iic x, dφ t) = φ x
        rw [show (dφ : ℝ → ℝ) = deriv (φ : ℝ → ℝ) by
          funext y; exact hdφ y]
        exact φ.hasCompactSupport.integral_Iic_deriv_eq
          (φ.contDiff.of_le (by norm_num)) x
      change u φ = -(-u (apm_m02j01_normalizedPrimitiveCLM dφ))
      rw [hprimitive]
      ring
    · intro u v₁ v₂ hv₁ hv₂
      let ρ := apm_m02j01_unitMassTestFunction
      refine ⟨(v₁ - v₂) ρ, fun φ => ?_⟩
      let q : TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
        φ - (∫ x : ℝ, φ x) • ρ
      have hqzero : ∫ x : ℝ, q x = 0 := by
        have hφint : Integrable (φ : ℝ → ℝ) :=
          φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
        have hρint : Integrable (ρ : ℝ → ℝ) :=
          ρ.contDiff.continuous.integrable_of_hasCompactSupport ρ.hasCompactSupport
        rw [show (q : ℝ → ℝ) = fun x => φ x - (∫ y : ℝ, φ y) * ρ x by rfl]
        rw [integral_sub hφint (hρint.const_mul _)]
        rw [integral_const_mul, show (∫ x : ℝ, ρ x) = 1 by
          exact apm_m02j01_integral_unitMassTestFunction]
        ring
      obtain ⟨ψ, hψ⟩ := apm_m02j01_exists_testFunction_primitive q hqzero
      have hv₁q : v₁ q = -u ψ := by
        linarith [hv₁ ψ q hψ]
      have hv₂q : v₂ q = -u ψ := by
        linarith [hv₂ ψ q hψ]
      have hdiffq : (v₁ - v₂) q = 0 := by
        simp [hv₁q, hv₂q]
      have hdecomp : φ = q + (∫ x : ℝ, φ x) • ρ := by
        simp [q]
      calc
        (v₁ - v₂) φ = (v₁ - v₂) (q + (∫ x : ℝ, φ x) • ρ) :=
          congrArg (v₁ - v₂) hdecomp
        _ = (∫ x : ℝ, φ x) • (v₁ - v₂) ρ := by
          rw [map_add, map_smul, hdiffq, zero_add]
        _ = (v₁ - v₂) ρ * ∫ x : ℝ, φ x := by
          change (∫ x : ℝ, φ x) * (v₁ - v₂) ρ = _
          ring
  /-
  SKIPPED (test-function LF-topology API boundary). The mathematical proof
  needs a continuous linear primitive operator on the codimension-one space of
  compactly supported smooth functions with integral zero. Searches of
  Mathlib's `TestFunction` and `Distribution` APIs found the endpoint identity
  `HasCompactSupport.integral_Ioi_deriv_eq`, but no bundled primitive operator
  that preserves compact support and is continuous for the test-function
  LF topology, nor a theorem that distributional differentiation on `ℝ` is
  surjective with constants as its kernel.

  Closer hop 1 compiles the necessity direction of part (a).
  `apm_m02j01_integral_deriv_testFunction_eq_zero` splits the whole-line
  integral at zero and combines `HasCompactSupport.integral_Iic_deriv_eq` with
  `HasCompactSupport.integral_Ioi_deriv_eq`; the endpoint values cancel.
  `apm_m02j01_integral_eq_zero_of_eq_deriv` then transports this result across
  the pointwise derivative identity. Thus every test-function derivative now
  formally has total integral zero.

  Closer hop 2 now compiles the reverse FTC/smoothness component as
  `apm_m02j01_primitive_smooth`: the explicit interval-integral primitive is
  globally `C∞` and its derivative is pointwise equal to the original test
  function. This uses `intervalIntegral.integral_hasDerivAt_right` and
  `contDiff_infty_iff_deriv`, neither of which was exploited by hop 1.

  The remaining function-level step is to use compact support and the
  zero-total-integral hypothesis to show this primitive vanishes on both
  tails, then bundle it as a `TestFunction`. Parts (b) and (c) further require
  bundling that
  construction as a continuous linear map before it can be transposed to a
  `Distribution`; this bridge is not supplied by the abstract distribution
  derivative API. Renewed searches of `LEMMA-INDEX.md`, closed artifacts,
  `ConstructionTargets/`, `TestFunction`, and `Distribution` sources found no
  compiled sibling route or reusable LF-continuity theorem, and the
  frozen statement remains unchanged.

  CLOSER HOP 3: the tail-vanishing and compact-support layer is now compiled.
  `apm_m02j01_primitive_support` shows that if `support φ ⊆ Ioc a b` and the
  total integral is zero, then the endpoint-based primitive
  `x ↦ ∫ t in a..x, φ t` has support contained in `Icc a b`. On the left tail
  this follows by interval-integral congruence with zero; on the right tail,
  `intervalIntegral.integral_eq_integral_of_support_subset` identifies the
  primitive with the zero total integral. The wrapper
  `apm_m02j01_primitive_hasCompactSupport` turns this into genuine
  `HasCompactSupport`.

  Thus the remaining function-level work is only extracting explicit real
  bounds from `φ.hasCompactSupport` and invoking the `TestFunction` bundling
  constructor together with smoothness (the FTC proof readily generalizes
  from basepoint zero to `a`). Parts (b) and (c) still require LF-continuity of
  that primitive operator and its transpose; renewed TestFunction and
  Distribution searches found no packaged operator. The statement remains
  unchanged.

  HOP 4 isolates the LF-topological gap as the following precise contract
  (recorded here rather than introduced as another declaration with `sorry`):

  ```lean
  theorem apm_m02j01_normalizedPrimitiveCLM_exists :
      ∃ (ρ : TestFunction (⊤ : Opens ℝ) ℝ ⊤)
        (P : TestFunction (⊤ : Opens ℝ) ℝ ⊤ →L[ℝ]
          TestFunction (⊤ : Opens ℝ) ℝ ⊤),
        (∫ x : ℝ, ρ x) = 1 ∧
        ∀ (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) (x : ℝ),
          deriv (P φ : ℝ → ℝ) x =
            φ x - (∫ t : ℝ, φ t) * ρ x
  ```

  This statement is true by choosing a fixed unit-integral bump `ρ` and
  applying the endpoint primitive to `φ - (∫ φ) • ρ`; the substantive missing
  assertion is precisely continuity for Mathlib's LF topology. For a
  derivative test function the integral term vanishes, so transposing `P`
  constructs a primitive of every distribution. For uniqueness, the displayed
  identity decomposes every test function into a derivative plus its integral
  times `ρ`, forcing any distribution annihilating derivatives to be a scalar
  multiple of integration.
  -/
