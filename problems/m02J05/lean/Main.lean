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

/-- The Luxemburg functional associated to `α`. -/
noncomputable def apm_m02J05_lux (α : ℝ → ℝ) (u : ℝ →ₘ[volume] ℝ) : ℝ :=
  sInf {c : ℝ | 0 < c ∧
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

/-- Why this unblocks `apm_m02j05`: this packages the missing convexity of
the modular class and closure of its rescalable hull under the vector-space
operations on `AEEqFun`. These are the two structural conjuncts preceding the
Luxemburg functional laws. -/
theorem apm_m02J05_bridge_convex_and_submodule
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t) :
    Convex ℝ (apm_m02J05_K α) ∧
      ∃ S : Submodule ℝ (ℝ →ₘ[volume] ℝ),
        (S : Set (ℝ →ₘ[volume] ℝ)) = apm_m02J05_L α := by
  sorry

/-- Why this unblocks `apm_m02j05`: this is the complete `sInf` theory for
the Luxemburg gauge on the rescalable modular class: nonnegativity,
definiteness modulo a.e. equality, absolute homogeneity, and the triangle
inequality. -/
theorem apm_m02J05_bridge_luxemburg_laws
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t) :
    (∀ u ∈ apm_m02J05_L α, 0 ≤ apm_m02J05_lux α u) ∧
      (∀ u ∈ apm_m02J05_L α, apm_m02J05_lux α u = 0 ↔ u = 0) ∧
      (∀ u ∈ apm_m02J05_L α, ∀ c : ℝ,
        apm_m02J05_lux α (c • u) = |c| * apm_m02J05_lux α u) ∧
      ∀ u ∈ apm_m02J05_L α, ∀ v ∈ apm_m02J05_L α,
        apm_m02J05_lux α (u + v) ≤
          apm_m02J05_lux α u + apm_m02J05_lux α v := by
  sorry

/-- Why this unblocks `apm_m02j05`: this packages the complementary integral
identity for inverse functions into pointwise Young's inequality and the
resulting normalized Orlicz--Hölder estimate. It supplies the final two
conjuncts of the frozen theorem. -/
theorem apm_m02J05_bridge_complementary_young_holder
    (α β : ℝ → ℝ)
    (hαc : ContinuousOn α (Ici 0))
    (hαmono : StrictMonoOn α (Ici 0))
    (hαzero : α 0 = 0)
    (hαinfty : Tendsto α atTop atTop)
    (hβc : ContinuousOn β (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t ∧ 0 ≤ β t)
    (hβα : ∀ t, 0 ≤ t → β (α t) = t)
    (hαβ : ∀ t, 0 ≤ t → α (β t) = t) :
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      s * t ≤ apm_m02J05_young α s + apm_m02J05_young β t) ∧
      ∀ u ∈ apm_m02J05_L α, ∀ v ∈ apm_m02J05_L β,
        ∫ x in Icc (0 : ℝ) 1, u x * v x ∂volume ≤
          2 * apm_m02J05_lux α u * apm_m02J05_lux β v := by
  sorry

theorem apm_m02j05 :
    ∀ (α β : ℝ → ℝ),
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
          2 * apm_m02J05_lux α u * apm_m02J05_lux β v) := by
  /-
  CLOSER HOP 1 (partial). The zero-value infrastructure is now compiled:
  `apm_m02J05_young_zero`, `apm_m02J05_zero_mem_K`, and
  `apm_m02J05_zero_mem_L` establish the base cases required by convexity and
  the proposed submodule structure.

  Searches of Mathlib and compiled
  siblings found no packaged Young-function, complementary-function, Orlicz
  space, or Luxemburg-norm API. The available theorems named
  `young_inequality` concern Hölder-conjugate powers, not the general inverse
  pair `α`, `β` used here.

  Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, Mathlib, prior
  solved problems, and git history found no stronger general-purpose bridge.
  A proof must therefore build the remaining theory in this file: convexity and
  monotonicity of the interval-integral primitive from `StrictMonoOn α`,
  stability and common rescaling of `AEEqFun`s, nonemptiness and attainment of
  the `sInf` modular sublevel set (dominated convergence plus Fatou),
  definiteness modulo a.e. equality, homogeneity and the triangle inequality,
  and finally the complementary-integral Young identity followed by the
  normalized integral estimate. No solved sibling supplies that combined
  bridge, so no sibling code was reused and the frozen statement was left
  unchanged.

  Closer hop 3 starts the missing primitive theory directly.
  `apm_m02J05_young_nonneg` proves nonnegativity of the interval-integral
  Young function, and `apm_m02J05_young_mono` proves its monotonicity on the
  nonnegative half-line using `intervalIntegral.integral_mono_interval` and
  continuity for interval integrability. Searches additionally inspected
  Mathlib's convex-integral and Fenchel/Young inequalities; the latter remain
  specialized to power conjugates and do not apply to the supplied inverse
  pair. The remaining bridge is still broad: upgrade primitive monotonicity
  to convexity, build the rescaling submodule on `AEEqFun`, establish the
  `sInf` attainment/definiteness/homogeneity/triangle theory, and prove the
  complementary integral identity. This final hop did not complete that
  self-contained Orlicz development.
  -/
  sorry
