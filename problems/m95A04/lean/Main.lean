import Mathlib

/-!
# APM m95A04: distributions and first-order Sobolev completeness

## Statement repairs

* The typographical `bet` is read as `but`, `equiped` as `equipped`, and the
  norm's `u`/`Du` as the bound variable `w`/`Dw`.
* The printed Sobolev claim omits the standard exponent range. We state it for
  `1 ≤ p < ∞`, where the displayed expression is a norm and `Lᵖ` is Banach.

## Encoding questions

Mathlib provides test functions and distributions but no bundled `W¹ᐟᵖ`
space. The latter is therefore encoded honestly as a normed space equipped
with value and weak-derivative maps onto the exact closed distributional
derivative graph in `Lᵖ × Lᵖ`; its norm is pinned to the displayed p-sum norm.
No part is replaced by pointwise differentiability.
-/

noncomputable section

open MeasureTheory Set
open scoped Distributions SchwartzMap

abbrev apm_m95A04_Ω : TopologicalSpace.Opens ℝ := ⊤
abbrev apm_m95A04_Test := 𝓓(apm_m95A04_Ω, ℝ)
abbrev apm_m95A04_Dist := 𝓓'(apm_m95A04_Ω, ℝ)
abbrev apm_m95A04_I := Set.Icc (0 : ℝ) 1
abbrev apm_m95A04_LpI (p : ENNReal) : Type :=
  Lp ℝ p (volume : Measure apm_m95A04_I)

/-- The weak derivative relation on `[0,1]`, tested against smooth functions
supported in the open interval. -/
def apm_m95A04_weakDeriv {p : ENNReal}
    (w v : apm_m95A04_LpI p) : Prop :=
  ∀ φ : 𝓢(ℝ, ℝ), Function.support φ ⊆ Set.Ioo 0 1 →
    (∫ x : apm_m95A04_I, v x * φ x.1) =
      -(∫ x : apm_m95A04_I,
          w x * SchwartzMap.derivCLM ℝ ℝ φ x.1)

/-- Differentiation is injective on test functions: the only compactly
supported constant smooth function on `ℝ` is zero. -/
lemma apm_m95A04_Dtest_injective
    (Dtest : apm_m95A04_Test →ₗ[ℝ] apm_m95A04_Test)
    (hDtest : ∀ (φ : apm_m95A04_Test) (x : ℝ),
      Dtest φ x = deriv φ x) :
    Function.Injective Dtest := by
  intro φ ψ hφψ
  apply TestFunction.toTestFunctionClass.coe_injective'
  funext x
  let h : apm_m95A04_Test := φ - ψ
  have hderiv : ∀ y : ℝ, deriv h y = 0 := by
    intro y
    rw [← hDtest]
    change Dtest (φ - ψ) y = 0
    rw [map_sub, hφψ, sub_self]
    rfl
  have hconst : ∀ y : ℝ, h x = h y :=
    is_const_of_deriv_eq_zero
      (h.contDiff.differentiable (by simp)) hderiv x
  have hbdd : BddAbove (tsupport (h : ℝ → ℝ)) :=
    h.hasCompactSupport.isBounded.bddAbove
  obtain ⟨b, hb⟩ := hbdd
  have hnot : b + 1 ∉ tsupport (h : ℝ → ℝ) := by
    intro hmem
    have := hb hmem
    linarith
  have hz : h (b + 1) = 0 := by
    rw [← Function.notMem_support]
    exact fun hm => hnot (subset_closure hm)
  have hxzero : h x = 0 := (hconst (b + 1)).trans hz
  exact sub_eq_zero.mp hxzero

/-- Regular distributions remember locally integrable functions up to almost
everywhere equality.  The forward direction is the fundamental lemma for
smooth compactly supported test functions. -/
lemma apm_m95A04_regular_iff_ae
    (regular : (ℝ → ℝ) → apm_m95A04_Dist)
    (hregular : ∀ (f : ℝ → ℝ), LocallyIntegrable f volume →
      ∀ φ : apm_m95A04_Test,
        regular f φ = ∫ x : ℝ, f x * φ x)
    (f g : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) :
    regular f = regular g ↔ f =ᵐ[volume] g := by
  constructor
  · intro hfg
    apply ae_eq_of_integral_contDiff_smul_eq hf hg
    intro q hqdiff hqcompact
    let φ : apm_m95A04_Test := TestFunction.mk q hqdiff hqcompact (by simp)
    have heval := DFunLike.congr_fun hfg φ
    rw [hregular f hf, hregular g hg] at heval
    simpa [φ, mul_comm] using heval
  · intro hfg
    ext φ
    rw [hregular f hf, hregular g hg]
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]

/-- The integral of the derivative of a test function on the real line
vanishes. This is the endpoint calculation needed to put the regular
distribution associated to the constant function in the kernel of
distributional differentiation. -/
lemma apm_m95A04_integral_deriv_testFunction_eq_zero
    (φ : apm_m95A04_Test) :
    ∫ x : ℝ, deriv (φ : ℝ → ℝ) x = 0 := by
  have hdiff : ContDiff ℝ 1 (φ : ℝ → ℝ) := φ.contDiff.of_le (by simp)
  have hcompact : HasCompactSupport (φ : ℝ → ℝ) := φ.hasCompactSupport
  have hint : Integrable (deriv (φ : ℝ → ℝ)) :=
    hdiff.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport hcompact.deriv
  rw [← integral_add_compl measurableSet_Iic hint, compl_Iic]
  rw [hcompact.integral_Iic_deriv_eq hdiff 0,
    hcompact.integral_Ioi_deriv_eq hdiff 0]
  ring

theorem apm_m95a04
    (regular : (ℝ → ℝ) → apm_m95A04_Dist)
    (hregular : ∀ (f : ℝ → ℝ), LocallyIntegrable f volume →
      ∀ φ : apm_m95A04_Test,
        regular f φ = ∫ x : ℝ, f x * φ x)
    (Dtest : apm_m95A04_Test →ₗ[ℝ] apm_m95A04_Test)
    (hDtest : ∀ (φ : apm_m95A04_Test) (x : ℝ),
      Dtest φ x = deriv φ x)
    (Ddist : apm_m95A04_Dist →ₗ[ℝ] apm_m95A04_Dist)
    (hDdist : ∀ (T : apm_m95A04_Dist) (φ : apm_m95A04_Test),
      Ddist T φ = -T (Dtest φ))
    (absDist signDist δ : apm_m95A04_Dist)
    (habs : ∀ φ : apm_m95A04_Test,
      absDist φ = ∫ x : ℝ, |x| * φ x)
    (hsign : ∀ φ : apm_m95A04_Test,
      signDist φ = ∫ x : ℝ, (SignType.sign x : ℝ) * φ x)
    (hδ : ∀ φ : apm_m95A04_Test, δ φ = φ 0)
    (causal : ℝ → apm_m95A04_Dist)
    (hcausal : ∀ (lam : ℝ) (φ : apm_m95A04_Test),
      causal lam φ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-lam * x) * φ x)
    (p : ENNReal) [Fact (1 ≤ p)] (hp_top : p ≠ ⊤)
    (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W]
    (wVal wDeriv : W →L[ℝ] apm_m95A04_LpI p)
    (hW_graph : ∀ w : W, apm_m95A04_weakDeriv (wVal w) (wDeriv w))
    (hW_exact : ∀ u v : apm_m95A04_LpI p,
      apm_m95A04_weakDeriv u v →
        ∃! w : W, wVal w = u ∧ wDeriv w = v)
    (hW_norm : ∀ w : W,
      ‖w‖ = Real.rpow (‖wVal w‖ ^ p.toReal + ‖wDeriv w‖ ^ p.toReal)
        (1 / p.toReal)) :
    (∀ f g : ℝ → ℝ,
      LocallyIntegrable f volume → LocallyIntegrable g volume →
      (regular f = regular g ↔ f =ᵐ[volume] g)) ∧
    Ddist absDist = signDist ∧
    Ddist signDist = (2 : ℝ) • δ ∧
    Function.Injective Dtest ∧
    ¬ Function.Injective Ddist ∧
    (∀ lam : ℝ, Ddist (causal lam) + lam • causal lam = δ) ∧
    Nonempty (CompleteSpace W) := by
  refine ⟨fun f g hf hg => apm_m95A04_regular_iff_ae regular hregular f g hf hg, ?_⟩
  /-
  Boundary (closer hop 3): two of the six bridges are now proved locally.
  `apm_m95A04_regular_iff_ae` uses Mathlib's
  `ae_eq_of_integral_contDiff_smul_eq` and constructs arbitrary test functions
  with `TestFunction.mk`; `apm_m95A04_Dtest_injective` proves the fourth
  conjunct using `is_const_of_deriv_eq_zero` and compact support.

  The remaining conjunction still requires the explicit integration-by-parts
  calculations `D |x| = sign`, `D sign = 2 δ`, and
  `(D + λ) causal = δ`.  Searches of `Analysis/Distribution` found the
  fundamental lemma and test-function derivative CLMs, but no general
  distribution theorem packaging these nonsmooth boundary-term calculations.
  Noninjectivity of the abstract `Ddist` can then use the regular distribution
  of the constant function, but depends on the same integral-of-a-derivative
  boundary lemma.  Finally, `Lp.instCompleteSpace` and `CompleteSpace.prod`
  give completeness of the ambient product (as illustrated by sibling
  `a96J05`), but transferring it to `W` requires proving that the custom
  weak-derivative graph is closed and building a norm-compatible equivalence;
  no searched sibling or construction target supplies that bridge.

  Hop 4 reduces the missing analytic content to these exact propositions:

    `∀ φ : apm_m95A04_Test,
      -(∫ x : ℝ, |x| * deriv (φ : ℝ → ℝ) x) =
        ∫ x : ℝ, (SignType.sign x : ℝ) * φ x`,

    `∀ φ : apm_m95A04_Test,
      -(∫ x : ℝ, (SignType.sign x : ℝ) * deriv (φ : ℝ → ℝ) x) =
        2 * φ 0`,

    `∀ (lam : ℝ) (φ : apm_m95A04_Test),
      -(∫ x in Set.Ioi (0 : ℝ),
          Real.exp (-lam * x) * deriv (φ : ℝ → ℝ) x) +
        lam * (∫ x in Set.Ioi (0 : ℝ), Real.exp (-lam * x) * φ x) = φ 0`.

  The exact remaining functional-analytic statement is
  `Nonempty (CompleteSpace W)` under `Fact (1 ≤ p)`, `p ≠ ⊤`, `hW_graph`,
  `hW_exact`, and `hW_norm` above. It amounts to closedness of
  `apm_m95A04_weakDeriv` in `Lp × Lp`, followed by transport of completeness
  across the norm-preserving graph equivalence. The locally proved
  `apm_m95A04_integral_deriv_testFunction_eq_zero` closes the independent
  total-derivative endpoint calculation but does not imply these four
  statements.
  -/
  sorry
