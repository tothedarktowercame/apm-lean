import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Derivative of a univalent holomorphic function

The target is the standard fact that a holomorphic function which is injective
on an open set has nonvanishing derivative there.

The local analytic-order reduction is recorded below.  The remaining
construction is the local-degree step: an analytic germ of order at least two
is not locally injective.
-/

open Set Filter
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
  have hn0 : n ≠ 0 := by omega
  let Q : ℂ → ℂ := fun w => F w / F z
  let R : ℂ → ℂ := fun w => Q w ^ ((n : ℂ)⁻¹)
  have hQa : AnalyticAt ℂ Q z := by simpa [Q] using hFa.div_const
  have hQz : Q z = 1 := by simp [Q, hFne]
  have hRa : AnalyticAt ℂ R z := by
    apply hQa.cpow analyticAt_const
    simp [hQz]
  have hRz : R z = 1 := by simp [R, hQz]
  have hFroot : ∀ w, F w = F z * R w ^ n := by
    intro w
    have hp := Complex.cpow_nat_inv_pow (Q w) hn0
    rw [show R w ^ n = Q w from hp]
    exact (mul_div_cancel₀ (F w) hFne).symm
  let φ : ℂ → ℂ := fun w => (w - z) * R w
  have hφa : AnalyticAt ℂ φ z :=
    (analyticAt_id.sub analyticAt_const).mul hRa
  have hφz : φ z = 0 := by simp [φ]
  have hφderiv : HasDerivAt φ 1 z := by
    dsimp [φ]
    convert ((hasDerivAt_id z).sub_const z).mul hRa.differentiableAt.hasDerivAt using 1
    simp [hRz]
  have hφs : HasStrictDerivAt φ 1 z := by
    simpa [hφderiv.deriv] using hφa.hasStrictDerivAt
  let e : ℂ ≃L[ℂ] ℂ :=
    ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 1 one_ne_zero)
  have hφsf : HasStrictFDerivAt φ (e : ℂ →L[ℂ] ℂ) z := by
    simpa [e] using hφs.hasStrictFDerivAt_equiv one_ne_zero
  let inv : ℂ → ℂ := hφsf.localInverse φ e z
  have hinv0 : inv 0 = z := by
    simpa [inv, hφz] using hφsf.localInverse_apply_image
  have hinv_tendsto : Tendsto inv (𝓝 0) (𝓝 z) := by
    simpa [inv, hφz] using hφsf.localInverse_tendsto
  have hright : ∀ᶠ v in 𝓝 0, φ (inv v) = v := by
    simpa [inv, hφz] using hφsf.eventually_right_inverse
  have hgood : ∀ᶠ v in 𝓝 0,
      inv v ∈ U ∧
      g (inv v) - g z = (inv v - z) ^ n * F (inv v) ∧
      φ (inv v) = v := by
    filter_upwards [hinv_tendsto.eventually (hU.mem_nhds hz),
      hinv_tendsto.eventually hform, hright] with v hvU hvform hvright
    exact ⟨hvU, hvform, hvright⟩
  let ω : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
  have hωroot : IsPrimitiveRoot ω n := by
    simpa [ω] using Complex.isPrimitiveRoot_exp n hn0
  have hωpow : ω ^ n = 1 := hωroot.pow_eq_one
  have hωne : ω ≠ 1 := hωroot.ne_one hn
  have hmul_tendsto : Tendsto (fun a : ℂ => ω * a) (𝓝 0) (𝓝 0) := by
    simpa using
      ((continuous_const : Continuous fun _ : ℂ => ω).mul continuous_id).tendsto 0
  have hgoodω : ∀ᶠ a in 𝓝 0, inv (ω * a) ∈ U ∧
      g (inv (ω * a)) - g z = (inv (ω * a) - z) ^ n * F (inv (ω * a)) ∧
      φ (inv (ω * a)) = ω * a :=
    hmul_tendsto.eventually hgood
  obtain ⟨a, ha, haω, ha0⟩ : ∃ a : ℂ,
      (inv a ∈ U ∧ g (inv a) - g z = (inv a - z) ^ n * F (inv a) ∧ φ (inv a) = a) ∧
      (inv (ω * a) ∈ U ∧
        g (inv (ω * a)) - g z = (inv (ω * a) - z) ^ n * F (inv (ω * a)) ∧
        φ (inv (ω * a)) = ω * a) ∧ a ≠ 0 := by
    have h : ∀ᶠ a in 𝓝[≠] (0 : ℂ),
        (inv a ∈ U ∧
          g (inv a) - g z = (inv a - z) ^ n * F (inv a) ∧ φ (inv a) = a) ∧
        (inv (ω * a) ∈ U ∧
          g (inv (ω * a)) - g z = (inv (ω * a) - z) ^ n * F (inv (ω * a)) ∧
          φ (inv (ω * a)) = ω * a) :=
      (hgood.and hgoodω).filter_mono nhdsWithin_le_nhds
    obtain ⟨a, ha, ha0⟩ := (h.and self_mem_nhdsWithin).exists
    exact ⟨a, ha.1, ha.2, ha0⟩
  have hφfactor (w : ℂ) : (w - z) ^ n * F w = F z * φ w ^ n := by
    rw [hFroot]
    simp only [φ, mul_pow]
    ring
  have hga : g (inv a) - g z = F z * a ^ n := by
    rw [ha.2.1, hφfactor, ha.2.2]
  have hgaω : g (inv (ω * a)) - g z = F z * a ^ n := by
    rw [haω.2.1, hφfactor, haω.2.2, mul_pow, hωpow, one_mul]
  have hinv_ne : inv a ≠ inv (ω * a) := by
    intro heq
    have hav : a = ω * a :=
      ha.2.2.symm.trans ((congrArg φ heq).trans haω.2.2)
    apply hωne
    apply mul_right_cancel₀ ha0
    simpa using hav.symm
  apply hinv_ne
  apply hinj ha.1 haω.1
  exact sub_left_inj.mp (hga.trans hgaω.symm)

end ConstructionTargets.UnivalentDeriv
