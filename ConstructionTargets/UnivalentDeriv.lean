import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Derivative of a univalent holomorphic function

The target is the standard fact that a holomorphic function which is injective
on an open set has nonvanishing derivative there.

The local analytic-order reduction is recorded below.  The remaining
construction is the local-degree step: an analytic germ of order at least two
is not locally injective.
-/

open Set
open scoped Topology

noncomputable section

namespace ConstructionTargets.UnivalentDeriv

/-- If a complex analytic function has zero derivative at `z`, then
`g - g z` vanishes to order at least two at `z`. -/
lemma two_le_analyticOrderAt_sub_self
    {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z)
    (hderiv : deriv g z = 0) :
    (2 : ℕ) ≤ analyticOrderAt (fun w => g w - g z) z := by
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hg.fun_sub analyticAt_const)]
  intro i hi
  interval_cases i
  · simp
  · simpa using hderiv

/-- Injectivity on an open neighborhood rules out the infinite-order
(`eventually constant`) case for the centered germ. -/
lemma analyticOrderAt_sub_self_ne_top_of_injOn
    {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hinj : InjOn g U) {z : ℂ} (hz : z ∈ U) :
    analyticOrderAt (fun w => g w - g z) z ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hzero := htop
  have hzero' : ∀ᶠ w in 𝓝[≠] z, g w - g z = 0 :=
    hzero.filter_mono nhdsWithin_le_nhds
  have hmem0 : ∀ᶠ w in 𝓝 z, w ∈ U := hU.mem_nhds hz
  have hmem : ∀ᶠ w in 𝓝[≠] z, w ∈ U :=
    hmem0.filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ w in 𝓝[≠] z, w ≠ z := self_mem_nhdsWithin
  obtain ⟨w, hwzero, hwmem, hwne⟩ := (hzero'.and (hmem.and hne)).exists
  exact hwne (hinj hwmem hz (sub_eq_zero.mp hwzero))

/-- At a hypothetical critical point of a holomorphic injection, the centered
germ has a finite local normal form of degree at least two. -/
lemma exists_local_normal_form_of_deriv_eq_zero
    {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (hinj : InjOn g U)
    {z : ℂ} (hz : z ∈ U) (hderiv : deriv g z = 0) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ F : ℂ → ℂ,
      AnalyticAt ℂ F z ∧ F z ≠ 0 ∧
        (fun w => g w - g z) =ᶠ[𝓝 z] fun w => (w - z) ^ n * F w := by
  have hg' : AnalyticAt ℂ (fun w => g w - g z) z :=
    (hg.analyticAt (hU.mem_nhds hz)).fun_sub analyticAt_const
  have hfinite :=
    analyticOrderAt_sub_self_ne_top_of_injOn hU hinj hz
  let n := analyticOrderNatAt (fun w => g w - g z) z
  have hn : 2 ≤ n := by
    have horder :=
      two_le_analyticOrderAt_sub_self (hg.analyticAt (hU.mem_nhds hz)) hderiv
    rw [← Nat.cast_analyticOrderNatAt hfinite] at horder
    exact_mod_cast horder
  obtain ⟨F, hFa, hFne, hform⟩ := hg'.analyticOrderAt_ne_top.mp hfinite
  exact ⟨n, hn, F, hFa, hFne, by simpa [n] using hform⟩

/-- A holomorphic function injective on an open set has nonzero derivative at
every point of that set. -/
theorem deriv_ne_zero_of_injOn
    {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (hinj : InjOn g U)
    {z : ℂ} (hz : z ∈ U) :
    deriv g z ≠ 0 := by
  intro hderiv
  obtain ⟨n, hn, F, hFa, hFne, hform⟩ :=
    exists_local_normal_form_of_deriv_eq_zero hU hg hinj hz hderiv
  -- It remains to take a local analytic `n`th root of the nonzero factor
  -- `F`, reducing `g - g z` to a nonzero constant times `φ ^ n`, where
  -- `φ` maps every neighborhood of `z` onto a neighborhood of `0`.
  -- Since `2 ≤ n`, two small values differing by a nontrivial `n`th root
  -- of unity have equal `n`th powers; pulling them back contradicts `hinj`.
  sorry

end ConstructionTargets.UnivalentDeriv
