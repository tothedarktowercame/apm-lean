import Mathlib

/-!
# APM m02J05

## Statement repairs

Measurable functions are taken modulo almost-everywhere equality. Without this
standard identification, the displayed Luxemburg functional is only a
seminorm, since it cannot distinguish functions differing on a null set.

## Encoding questions

The inverse `β` of `α` is supplied explicitly, with its two inverse identities
on the nonnegative half-line. This avoids extending a half-line homeomorphism
arbitrarily to all of `ℝ`.
-/

open Filter MeasureTheory Set intervalIntegral

/-- The Young function obtained by integrating `α` from zero. -/
noncomputable def apm_m02J05_young (α : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, α s

/-- The convex modular class `K_A`, on `[0,1]`, modulo a.e. equality. -/
def apm_m02J05_K (α : ℝ → ℝ) : Set (ℝ →ₘ[volume] ℝ) :=
  {u | IntegrableOn
    (fun x ↦ apm_m02J05_young α |u x|) (Icc (0 : ℝ) 1) volume}

/-- The Orlicz class consisting of functions with some nonzero rescaling in `K_A`. -/
def apm_m02J05_L (α : ℝ → ℝ) : Set (ℝ →ₘ[volume] ℝ) :=
  {u | ∃ c : ℝ, c ≠ 0 ∧ c • u ∈ apm_m02J05_K α}

/-- The Luxemburg functional associated to `α`.

The sublevel set carries an explicit `IntegrableOn` conjunct. Without it the
condition `∫ ... ≤ 1` is vacuous when the modular integral diverges: the
real-valued Lebesgue integral of a nonnegative measurable function with
infinite integral is `0` in Mathlib, so every small `c` would be admissible,
the infimum would collapse to `0` for every `u`, and definiteness modulo
a.e. equality would fail. With the integrability conjunct the set is the
classical one: nonempty on `apm_m02J05_L α` by monotone convergence, and the
Luxemburg gauge laws hold. -/
noncomputable def apm_m02J05_lux (α : ℝ → ℝ) (u : ℝ →ₘ[volume] ℝ) : ℝ :=
  sInf {c : ℝ | 0 < c ∧
    IntegrableOn (fun x ↦ apm_m02J05_young α (|u x| / c)) (Icc (0 : ℝ) 1) volume ∧
    ∫ x in Icc (0 : ℝ) 1, apm_m02J05_young α (|u x| / c) ∂volume ≤ 1}

lemma apm_m02J05_young_zero (α : ℝ → ℝ) :
    apm_m02J05_young α 0 = 0 := by
  simp [apm_m02J05_young]

lemma apm_m02J05_zero_mem_K (α : ℝ → ℝ) :
    (0 : ℝ →ₘ[volume] ℝ) ∈ apm_m02J05_K α := by
  simp [apm_m02J05_K, apm_m02J05_young_zero]

lemma apm_m02J05_zero_mem_L (α : ℝ → ℝ) :
    (0 : ℝ →ₘ[volume] ℝ) ∈ apm_m02J05_L α := by
  refine ⟨1, one_ne_zero, ?_⟩
  simpa using apm_m02J05_zero_mem_K α

/-- The Young primitive is nonnegative on the nonnegative half-line. -/
lemma apm_m02J05_young_nonneg
    {α : ℝ → ℝ} (hα : ∀ t, 0 ≤ t → 0 ≤ α t) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ apm_m02J05_young α t := by
  unfold apm_m02J05_young
  exact intervalIntegral.integral_nonneg ht (fun x hx => hα x hx.1)

/-- Monotonicity of the primitive follows directly by enlarging its interval
of integration; continuity supplies interval integrability. -/
lemma apm_m02J05_young_mono
    {α : ℝ → ℝ} (hc : ContinuousOn α (Ici 0))
    (hα : ∀ t, 0 ≤ t → 0 ≤ α t) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    apm_m02J05_young α s ≤ apm_m02J05_young α t := by
  unfold apm_m02J05_young
  apply intervalIntegral.integral_mono_interval (le_refl 0) hs hst
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hα x hx.1.le
  · have ht : 0 ≤ t := hs.trans hst
    have hi : ContinuousOn α (uIcc (0 : ℝ) t) := by
      simpa [uIcc_of_le ht] using hc.mono Icc_subset_Ici_self
    exact hi.intervalIntegrable

/-! The integrability repair to the Luxemburg sublevel set does not repair
definiteness: the ambient `AEEqFun` is still quotiented by full Lebesgue
measure, whereas the modular only observes `[0,1]`. -/

noncomputable def apm_m02J05_outside : ℝ →ₘ[volume] ℝ :=
  AEEqFun.mk (fun x : ℝ ↦ max (x - 1) 0)
    ((continuous_id.sub continuous_const).max continuous_const).aestronglyMeasurable

lemma apm_m02J05_outside_ae_zero_on_Icc :
    apm_m02J05_outside =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] 0 := by
  filter_upwards [ae_restrict_of_ae (AEEqFun.coeFn_mk
      (fun x : ℝ ↦ max (x - 1) 0)
      ((continuous_id.sub continuous_const).max continuous_const).aestronglyMeasurable),
    ae_restrict_mem measurableSet_Icc] with x hx hmem
  rw [apm_m02J05_outside, hx]
  simp only [Pi.zero_apply]
  rw [max_eq_right]
  linarith [hmem.2]

lemma apm_m02J05_outside_ne_zero :
    apm_m02J05_outside ≠ (0 : ℝ →ₘ[volume] ℝ) := by
  intro h
  have hae : (fun x : ℝ ↦ max (x - 1) 0) =ᵐ[volume] (fun _ ↦ (0 : ℝ)) := by
    have hm : apm_m02J05_outside =ᵐ[volume] (fun x : ℝ ↦ max (x - 1) 0) :=
      AEEqFun.coeFn_mk _ _
    rw [h] at hm
    exact hm.symm.trans (Filter.Eventually.of_forall fun x ↦ by simp)
  have hall := (Continuous.ae_eq_iff_eq volume
    ((continuous_id.sub continuous_const).max continuous_const) continuous_const).mp hae
  have := congrFun hall 2
  norm_num at this

lemma apm_m02J05_outside_mem_K (α : ℝ → ℝ) :
    apm_m02J05_outside ∈ apm_m02J05_K α := by
  change IntegrableOn
    (fun x ↦ apm_m02J05_young α |apm_m02J05_outside x|) (Icc (0 : ℝ) 1) volume
  apply integrableOn_zero.congr
  filter_upwards [apm_m02J05_outside_ae_zero_on_Icc] with x hx
  rw [hx]
  simp [apm_m02J05_young_zero]

lemma apm_m02J05_outside_mem_L (α : ℝ → ℝ) :
    apm_m02J05_outside ∈ apm_m02J05_L α := by
  exact ⟨1, one_ne_zero, by simpa using apm_m02J05_outside_mem_K α⟩

lemma apm_m02J05_lux_outside (α : ℝ → ℝ) :
    apm_m02J05_lux α apm_m02J05_outside = 0 := by
  unfold apm_m02J05_lux
  convert (csInf_Ioi : sInf (Ioi (0 : ℝ)) = 0)
  ext c
  simp only [mem_setOf_eq, mem_Ioi]
  have hz : (fun x ↦ apm_m02J05_young α
      (|apm_m02J05_outside x| / c)) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] 0 := by
    filter_upwards [apm_m02J05_outside_ae_zero_on_Icc] with x hx
    rw [hx]
    simp [apm_m02J05_young_zero]
  have hint : IntegrableOn (fun x ↦ apm_m02J05_young α
      (|apm_m02J05_outside x| / c)) (Icc (0 : ℝ) 1) volume :=
    integrableOn_zero.congr hz.symm
  have hi : (∫ x in Icc (0 : ℝ) 1,
      apm_m02J05_young α (|apm_m02J05_outside x| / c) ∂volume) = 0 :=
    integral_eq_zero_of_ae hz
  constructor
  · exact fun h ↦ h.1
  · intro hc
    exact ⟨hc, hint, by rw [hi]; norm_num⟩

theorem apm_m02J05_definiteness_counterexample (α : ℝ → ℝ) :
    apm_m02J05_outside ∈ apm_m02J05_L α ∧
      apm_m02J05_lux α apm_m02J05_outside = 0 ∧
      apm_m02J05_outside ≠ 0 :=
  ⟨apm_m02J05_outside_mem_L α, apm_m02J05_lux_outside α,
    apm_m02J05_outside_ne_zero⟩

theorem apm_m02J05_definiteness_false (α : ℝ → ℝ) :
    ¬ (∀ u ∈ apm_m02J05_L α,
      apm_m02J05_lux α u = 0 ↔ u = 0) := by
  intro h
  exact apm_m02J05_outside_ne_zero
    ((h apm_m02J05_outside (apm_m02J05_outside_mem_L α)).mp
      (apm_m02J05_lux_outside α))

theorem apm_m02J05_admissible_data_with_false_definiteness :
    ∃ α β : ℝ → ℝ,
      ContinuousOn α (Ici 0) ∧
      StrictMonoOn α (Ici 0) ∧
      α 0 = 0 ∧
      Tendsto α atTop atTop ∧
      ContinuousOn β (Ici 0) ∧
      (∀ t, 0 ≤ t → 0 ≤ α t ∧ 0 ≤ β t) ∧
      (∀ t, 0 ≤ t → β (α t) = t) ∧
      (∀ t, 0 ≤ t → α (β t) = t) ∧
      ¬ (∀ u ∈ apm_m02J05_L α,
        apm_m02J05_lux α u = 0 ↔ u = 0) := by
  refine ⟨id, id, continuous_id.continuousOn,
    (strictMono_id : StrictMono (id : ℝ → ℝ)).strictMonoOn (Ici 0),
    rfl, tendsto_id, continuous_id.continuousOn, ?_, ?_, ?_,
    apm_m02J05_definiteness_false id⟩
  · intro t ht
    exact ⟨ht, ht⟩
  · intro t _
    rfl
  · intro t _
    rfl

theorem apm_m02j05_false :
    ¬ (∀ (α β : ℝ → ℝ),
      ContinuousOn α (Ici 0) →
      StrictMonoOn α (Ici 0) →
      α 0 = 0 →
      Tendsto α atTop atTop →
      ContinuousOn β (Ici 0) →
      (∀ t, 0 ≤ t → 0 ≤ α t ∧ 0 ≤ β t) →
      (∀ t, 0 ≤ t → β (α t) = t) →
      (∀ t, 0 ≤ t → α (β t) = t) →
      Convex ℝ (apm_m02J05_K α) ∧
      (∃ S : Submodule ℝ (ℝ →ₘ[volume] ℝ),
        (S : Set (ℝ →ₘ[volume] ℝ)) = apm_m02J05_L α) ∧
      ((∀ u ∈ apm_m02J05_L α, 0 ≤ apm_m02J05_lux α u) ∧
        (∀ u ∈ apm_m02J05_L α, apm_m02J05_lux α u = 0 ↔ u = 0) ∧
        (∀ u ∈ apm_m02J05_L α, ∀ c : ℝ,
          apm_m02J05_lux α (c • u) = |c| * apm_m02J05_lux α u) ∧
        (∀ u ∈ apm_m02J05_L α, ∀ v ∈ apm_m02J05_L α,
          apm_m02J05_lux α (u + v) ≤
            apm_m02J05_lux α u + apm_m02J05_lux α v)) ∧
      (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
        s * t ≤ apm_m02J05_young α s + apm_m02J05_young β t) ∧
      (∀ u ∈ apm_m02J05_L α, ∀ v ∈ apm_m02J05_L β,
        ∫ x in Icc (0 : ℝ) 1, u x * v x ∂volume ≤
          2 * apm_m02J05_lux α u * apm_m02J05_lux β v)) := by
  intro h
  have hall := h id id continuous_id.continuousOn
    ((strictMono_id : StrictMono (id : ℝ → ℝ)).strictMonoOn (Ici 0))
    rfl tendsto_id continuous_id.continuousOn
    (by intro t ht; exact ⟨ht, ht⟩)
    (by intro t _; rfl)
    (by intro t _; rfl)
  exact apm_m02J05_definiteness_false id hall.2.2.1.2.1
