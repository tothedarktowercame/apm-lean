import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.Convex

/-!
# APM a94A10: f real iff z real implies f' never vanishes on ℝ

## Problem (from `a94A10.tex`)

Suppose `f` is an entire function with the property that `f(z)` is real if and
only if `z` is real. Verify that `f'(z) = 0` cannot be true for any real `z`.

## Statement repair notes

1. The proposed `RealIffReal` definition is correct: `f z` is real iff `z` is
   real, expressed as `(f z).im = 0 ↔ z.im = 0`.

2. The informal proof's helper lemmas used `iteratedDeriv` which is less natural
   than `analyticOrderAt` from `Mathlib.Analysis.Analytic.Order`. We use the
   latter, which gives the local factorization
   `f(z) - f(z₀) = (z - z₀)^n · g(z)` with `g(z₀) ≠ 0` directly.

3. The local Rouché argument only applies directly when the critical point (and
   hence its image) is real, whereas the boundary lemma below allows arbitrary
   `x₀`.  At that generality the appropriate route is global: the nonvanishing
   of `im ∘ f` makes `f` map the upper half-plane wholly into one open
   half-plane; the classification of entire Pick functions then makes `f`
   affine.  The connectedness/sign part of that route is formalized below.

## Proof strategy

By contradiction: assume `f'(x₀) = 0` for real `x₀`. Then `g := f - f(x₀)`
vanishes to order `n ≥ 2` at `x₀` (by the order theory for analytic functions).
The local factorization `g(z) = (z-x₀)^n · h(z)` with `h(x₀) ≠ 0` means `f`
is locally `n`-to-`1` at `x₀`. Since `n ≥ 2`, the `n` branches include non-real
directions that map to real values (the `n`-th roots of a real number include
non-real `n`-th roots when `n ≥ 2`). This gives a non-real `z` with `f(z) ∈ ℝ`,
contradicting the hypothesis.
-/

set_option linter.unusedVariables false in
noncomputable section

open Complex Set Filter Topology

namespace ApmCanaries.A94A10

/-- The "f(z) real iff z real" hypothesis. -/
def RealIffReal (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, (f z).im = 0 ↔ z.im = 0

/-- f is non-constant (a constant function maps non-real z to real values,
    violating "f(z) real ⟹ z real"). -/
lemma nonconstant_of_realIffReal
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hreal : RealIffReal f) :
    ∃ z₁ z₂ : ℂ, f z₁ ≠ f z₂ := by
  by_contra h
  push_neg at h
  have hconst : f I = f 0 := h I 0
  have h0_real : (f 0).im = 0 := (hreal 0).mpr (by simp)
  have hI_real : (f I).im = 0 := by rw [hconst]; exact h0_real
  have hI_im : I.im = 0 := (hreal I).mp hI_real
  simp at hI_im

/-- On the upper half-plane, the imaginary parts of any two values of `f`
have the same strict sign.  This is the connectedness step behind the global
Pick/Nevanlinna route: `RealIffReal` keeps the continuous function `im ∘ f`
away from zero there. -/
lemma im_image_mul_pos_of_im_pos
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hreal : RealIffReal f)
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    0 < (f z).im * (f w).im := by
  have hz_ne : (f z).im ≠ 0 := by
    intro h
    exact hz.ne' ((hreal z).mp h)
  have hw_ne : (f w).im ≠ 0 := by
    intro h
    exact hw.ne' ((hreal w).mp h)
  have hpre : IsPreconnected {u : ℂ | 0 < u.im} :=
    (convex_halfSpace_im_gt 0).isPreconnected
  have hcont : ContinuousOn (fun u : ℂ => (f u).im) {u : ℂ | 0 < u.im} :=
    (Complex.continuous_im.comp hf.continuous).continuousOn
  rcases lt_or_gt_of_ne hz_ne with hz_neg | hz_pos
  · rcases lt_or_gt_of_ne hw_ne with hw_neg | hw_pos
    · exact mul_pos_of_neg_of_neg hz_neg hw_neg
    · have hzero : (0 : ℝ) ∈ Set.Icc ((f z).im) ((f w).im) :=
        ⟨hz_neg.le, hw_pos.le⟩
      obtain ⟨u, hu, hu0⟩ := hpre.intermediate_value hz hw hcont hzero
      exact False.elim ((ne_of_gt hu) ((hreal u).mp hu0))
  · rcases lt_or_gt_of_ne hw_ne with hw_neg | hw_pos
    · have hzero : (0 : ℝ) ∈ Set.Icc ((f w).im) ((f z).im) :=
        ⟨hw_neg.le, hz_pos.le⟩
      obtain ⟨u, hu, hu0⟩ := hpre.intermediate_value hw hz hcont hzero
      exact False.elim ((ne_of_gt hu) ((hreal u).mp hu0))
    · exact mul_pos hz_pos hw_pos

/-- Consequently, `f` maps the whole upper half-plane into one of the two
open half-planes. -/
lemma maps_upper_halfPlane_one_side
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hreal : RealIffReal f) :
    (∀ z : ℂ, 0 < z.im → 0 < (f z).im) ∨
      (∀ z : ℂ, 0 < z.im → (f z).im < 0) := by
  have hI : 0 < (I : ℂ).im := by simp
  have hfI_ne : (f I).im ≠ 0 := by
    intro h
    exact hI.ne' ((hreal I).mp h)
  rcases lt_or_gt_of_ne hfI_ne with hfI_neg | hfI_pos
  · right
    intro z hz
    have hmul := im_image_mul_pos_of_im_pos f hf hreal hz hI
    nlinarith
  · left
    intro z hz
    have hmul := im_image_mul_pos_of_im_pos f hf hreal hz hI
    nlinarith

/-- If `f` is entire and `f'(x₀) = 0` for real `x₀`, then `f - f(x₀)` has
    order ≥ 2 at `x₀`. -/
lemma order_ge_two_of_deriv_zero
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (x₀ : ℝ) (hcrit : deriv f (↑x₀) = 0) :
    2 ≤ analyticOrderAt (fun z => f z - f (↑x₀)) (↑x₀) := by
  have ha : AnalyticAt ℂ f (↑x₀) := hf.analyticAt (↑x₀)
  have had : AnalyticAt ℂ (deriv f) (↑x₀) := by
    have ha' : AnalyticOnNhd ℂ f Set.univ := fun x _ => hf.analyticAt x
    exact ha'.deriv (↑x₀) (by trivial)
  have key : analyticOrderAt (deriv f) (↑x₀) + 1 =
      analyticOrderAt (fun z => f z - f (↑x₀)) (↑x₀) :=
    ha.analyticOrderAt_deriv_add_one
  have h0 : analyticOrderAt (deriv f) (↑x₀) ≠ 0 := by
    rw [had.analyticOrderAt_ne_zero]
    exact hcrit
  rw [← key]
  have h1 : (1 : ℕ∞) ≤ analyticOrderAt (deriv f) (↑x₀) :=
    ENat.one_le_iff_ne_zero.mpr h0
  rw [show (2 : ℕ∞) = (1 : ℕ∞) + 1 from rfl]
  gcongr

/-- Helper: extracting the natural number order and factorization. -/
lemma exists_factorization_of_order_ge_two
    (f : ℂ → ℂ) (x₀ : ℂ) (hf : Differentiable ℂ f)
    (hord : 2 ≤ analyticOrderAt (fun z => f z - f x₀) x₀)
    (hne : analyticOrderAt (fun z => f z - f x₀) x₀ ≠ ⊤) :
    ∃ (n : ℕ) (g : ℂ → ℂ),
      2 ≤ n ∧ AnalyticAt ℂ g x₀ ∧ g x₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 x₀, f z - f x₀ = (z - x₀)^n * g z := by
  -- f is analytic, so f - f x₀ is analytic (as a function)
  have ha : AnalyticAt ℂ f x₀ := hf.analyticAt x₀
  have hasub : AnalyticAt ℂ (fun z => f z - f x₀) x₀ := by
    fun_prop
  set n := analyticOrderNatAt (fun z => f z - f x₀) x₀
  have hn_cast : (n : ℕ∞) = analyticOrderAt (fun z => f z - f x₀) x₀ :=
    Nat.cast_analyticOrderNatAt hne
  have hn : 2 ≤ n := by
    have h2 : (2 : ℕ∞) ≤ (n : ℕ∞) := hn_cast ▸ hord
    exact mod_cast h2
  obtain ⟨g, hg, hg_ne, hg_eq⟩ :=
    (hasub.analyticOrderAt_eq_natCast (n := n)).mp (hn_cast.symm)
  refine ⟨n, g, hn, hg, hg_ne, ?_⟩
  filter_upwards [hg_eq] with z hz
  -- hz : f z - f x₀ = (z - x₀)^n • g z  (for E = ℂ, smul = mul)
  rw [smul_eq_mul] at hz
  exact hz

/-- **Core boundary lemma (SORRY).** Given the factorization
    `f(z) - f(x₀) = (z - x₀)^n · g(z)` with `n ≥ 2`, `g(x₀) ≠ 0`, `f` entire
    with the real-iff-real property, find a non-real `z` near `x₀` with
    `f(z) ∈ ℝ`.

    For a real `x₀`, the following local argument applies. Since `f` maps ℝ to
    ℝ, `f|_ℝ` is real-analytic with
    real Taylor coefficients, so `g(x₀) ∈ ℝ`. For small `r > 0`, consider
    `φ(α) = Im(f(x₀ + r·e^{iα}))`. Then `φ(0) = 0` (since `x₀ + r ∈ ℝ`).
    Locally `f(x₀ + r·e^{iα}) ≈ f(x₀) + g(x₀)·r^n·e^{inα}`, so
    `φ(α) ≈ g(x₀)·r^n·sin(nα)`. Since `n ≥ 2`, `sin(n·π/n) = sin(π) = 0`,
    and by the intermediate value theorem there exists `α` near `π/n` with
    `φ(α) = 0` exactly. The corresponding `z = x₀ + r·e^{iα}` is non-real
    (since `π/n ∈ (0, π/2]` for `n ≥ 2`), yet `f(z) ∈ ℝ`. Contradiction.

    **What was tried:**
    (a) Direct IVT argument on `φ(α)` — requires controlling the error between
        `φ(α)` and its leading-order approximation `g(x₀)·r^n·sin(nα)`.
    (b) Open mapping theorem + one-sided coverage of `f|_ℝ` — requires showing
        `f|_ℝ` covers only one side of `f(x₀)` near a critical point.
    (c) Rouché's theorem — not in Mathlib.
    For arbitrary `x₀`, however, its local image need not meet the real axis,
    so these local arguments do not prove the stated lemma.  The valid general
    route uses `maps_upper_halfPlane_one_side` and the theorem that an entire
    holomorphic self-map of a half-plane is affine (the entire Pick-function
    classification).  That classification is not currently packaged in
    Mathlib. -/
lemma exists_nonreal_preimage_of_real
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hreal : RealIffReal f)
    (x₀ : ℂ) (n : ℕ) (hn : 2 ≤ n)
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g x₀) (hg_ne : g x₀ ≠ 0)
    (hg_eq : ∀ᶠ z in 𝓝 x₀, f z - f x₀ = (z - x₀)^n * g z) :
    ∃ z : ℂ, z.im ≠ 0 ∧ (f z).im = 0 := by
  -- SORRY: requires the classification of entire Pick functions
  sorry

/-- **Main theorem.** If `f` is entire and `f(z)` is real iff `z` is real,
    then `f'(x) ≠ 0` for all real `x`.

    **SORRY BOUNDARY:** The proof requires showing that the local `n`-to-1
    structure at a critical point of order `n ≥ 2` produces non-real preimages
    of real values. This needs Rouché's theorem or the argument principle,
    neither of which is in Mathlib as of 2026. We prove all the setup lemmas
    and identify the exact sorry boundary in `exists_nonreal_preimage_of_real`.
-/
theorem deriv_ne_zero_on_reals
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hreal : RealIffReal f) :
    ∀ x : ℝ, deriv f (↑x) ≠ 0 := by
  intro x₀ hcrit
  -- f is non-constant
  have hnc := nonconstant_of_realIffReal f hf hreal
  -- Order of f - f(x₀) at x₀ is ≥ 2
  have hord := order_ge_two_of_deriv_zero f hf x₀ hcrit
  -- f(x₀) is real
  have hfx0_real : (f (↑x₀)).im = 0 := (hreal (↑x₀)).mpr (by simp)
  -- Order ≠ ⊤ (otherwise f is constant near x₀, hence globally constant)
  have hord_ne_top : analyticOrderAt (fun z => f z - f (↑x₀)) (↑x₀) ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hconst : ∀ᶠ z in 𝓝 (↑x₀), f z = f (↑x₀) := by
      filter_upwards [htop] with z hz using sub_eq_zero.mp hz
    have hglobal : ∀ z : ℂ, f z = f (↑x₀) := by
      intro z
      have hao : AnalyticOnNhd ℂ f Set.univ := fun w _ => hf.analyticAt w
      have hao2 : AnalyticOnNhd ℂ (fun (_ : ℂ) => f (↑x₀)) Set.univ :=
        fun _ _ => by exact analyticAt_const
      have hev : (f : ℂ → ℂ) =ᶠ[𝓝 (↑x₀)] fun _ => f (↑x₀) := hconst
      have := hao.eqOn_of_preconnected_of_eventuallyEq hao2
        isPreconnected_univ (Set.mem_univ (↑x₀)) hev
      exact this (Set.mem_univ z)
    obtain ⟨z₁, z₂, hne⟩ := hnc
    exact hne (by rw [hglobal z₁, hglobal z₂])
  -- Get the factorization
  obtain ⟨n, g, hn, hg, hg_ne, hg_eq⟩ :=
    exists_factorization_of_order_ge_two f (↑x₀) hf hord hord_ne_top
  -- KEY BOUNDARY: find non-real z near x₀ with f(z) ∈ ℝ
  obtain ⟨z, hz_nonreal, hfz_real⟩ :=
    exists_nonreal_preimage_of_real f hf hreal (↑x₀) n hn g hg hg_ne hg_eq
  -- Contradiction with hreal
  exact absurd ((hreal z).mp hfz_real) hz_nonreal

end ApmCanaries.A94A10
