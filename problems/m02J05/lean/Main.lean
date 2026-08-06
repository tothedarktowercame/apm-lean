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
  SKIPPED (Orlicz/Luxemburg library boundary). Searches of Mathlib and compiled
  siblings found no packaged Young-function, complementary-function, Orlicz
  space, or Luxemburg-norm API. The available theorems named
  `young_inequality` concern Hölder-conjugate powers, not the general inverse
  pair `α`, `β` used here.

  A proof must therefore build the complete theory in this file: convexity and
  monotonicity of the interval-integral primitive from `StrictMonoOn α`,
  stability and common rescaling of `AEEqFun`s, nonemptiness and attainment of
  the `sInf` modular sublevel set (dominated convergence plus Fatou),
  definiteness modulo a.e. equality, homogeneity and the triangle inequality,
  and finally the complementary-integral Young identity followed by the
  normalized integral estimate. No solved sibling supplies that combined
  bridge, so no sibling code was reused and the frozen statement was left
  unchanged.
  -/
  sorry
