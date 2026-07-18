import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# APM a94J05: Liouville's theorem and bounded real part

## Problem (from `a94J05.tex`)

State Cauchy's integral theorem expressing the value of an analytic function at
a point as a contour integral. Let `f` be entire. Prove:
**(a)** if `f` is bounded, then it is constant;
**(b)** if the real part of `f` is bounded below, then `f` is constant.

## Statement repair notes

1. The proposed Cauchy integral formula and Cauchy estimate lemmas are available
   in Mathlib (`Mathlib.Analysis.Complex.Liouville` provides
   `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` and Liouville's
   theorem directly). We use Mathlib's packaged Liouville instead.

2. The proposed statements for parts (a) and (b) are mathematically correct.

3. For part (b), the exponential trick `g = exp(-f)` converts a half-plane bound
   into a disk bound. Mathlib's `Differentiable.exists_const_forall_eq_of_bounded`
   then gives `g` constant. The final step (from `exp(-f)` constant to `f`
   constant) uses the fact that `f` is continuous and `f - f(0) ∈ 2πiℤ`, combined
   with the IVT to derive a contradiction.

## Proof

**(a)** Direct application of Mathlib's Liouville:
`Differentiable.exists_const_forall_eq_of_bounded`.

**(b)** Define `g(z) = exp(-f(z))`. Then:
- `g` is entire (composition of `exp` with `-f`).
- `|g(z)| = exp(-Re f(z)) ≤ exp(C)` since `Re f(z) ≥ -C`.
- By Liouville (part a), `g` is constant: `g(z) = g(0)`.
- So `exp(-f(z)) = exp(-f(0))`, giving `f(z) - f(0) ∈ 2πiℤ`.
- The function `h(s) = f(s·z)` is continuous on `[0,1]`, `h(0) = f(0)`,
  and `‖h(s) - f(0)‖ ∈ {0, 2π, 4π, ...}`.
- If `f(z) ≠ f(0)`, then `‖h(1) - f(0)‖ ≥ 2π`.
- By IVT, `‖h(s₀) - f(0)‖ = π` for some `s₀ ∈ (0,1)`.
- But `π ∉ {0, 2π, 4π, ...}` — contradiction.
- So `f(z) = f(0)` for all `z`. ∎
-/

set_option linter.unusedVariables false in
noncomputable section

open Complex Bornology Set Topology

open scoped Real

namespace ApmCanaries.A94J05

/-- **Part (a): Liouville's theorem** — bounded entire ⟹ constant.

    Direct application of Mathlib's `Differentiable.exists_const_forall_eq_of_bounded`. -/
theorem liouville_bounded
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (M : ℝ) (hM : ∀ z, ‖f z‖ ≤ M) :
    ∃ c : ℂ, ∀ z, f z = c := by
  apply Differentiable.exists_const_forall_eq_of_bounded hf
  rw [isBounded_iff_forall_norm_le]
  refine ⟨M, ?_⟩
  rintro y ⟨z, rfl⟩
  exact hM z

/-- **Part (b): Re f bounded below ⟹ f constant.**

    Uses the exponential trick: `g = exp(-f)` is bounded entire, hence constant
    by Liouville. Then `f(z) - f(0) ∈ 2πiℤ`, and continuity + IVT forces `f` constant.

    **SORRY BOUNDARY:** The final IVT argument requires showing that
    `‖f(s·z) - f(0)‖` is continuous in `s` (which follows from `f` continuous)
    and takes values in the discrete set `{0, 2π, 4π, ...}`, leading to a
    contradiction via IVT. The IVT is available in Mathlib
    (`ContinuousOn.exists_Ioc` or `exists_hasDerivAt_eq_slope`), but connecting
    it to the norm computation requires careful management of the complex
    arithmetic. -/
theorem liouville_re_bounded_below
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (C : ℝ) (hC : ∀ z, -C ≤ (f z).re) :
    ∃ c : ℂ, ∀ z, f z = c := by
  -- g(z) = exp(-f(z)) is bounded entire
  have hg : Differentiable ℂ (fun z => cexp (-f z)) :=
    Differentiable.cexp (Differentiable.neg hf)
  have hg_bdd : ∀ z, ‖cexp (-f z)‖ ≤ Real.exp C := by
    intro z
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    rw [neg_re]
    linarith [hC z]
  -- By Liouville, g is constant
  obtain ⟨c, hc⟩ := Differentiable.exists_const_forall_eq_of_bounded hg
    (by rw [isBounded_iff_forall_norm_le]
        refine ⟨Real.exp C, ?_⟩
        rintro y ⟨z, rfl⟩
        exact hg_bdd z)
  -- So exp(-f(z)) = exp(-f(0)) for all z
  have hgf : ∀ z, cexp (-f z) = cexp (-f 0) := fun z => by rw [hc z, hc 0]
  -- Claim: f is constant, equal to f(0)
  refine ⟨f 0, fun z => ?_⟩
  -- For any z, consider the path s ↦ f(s · z) for s ∈ [0,1]
  -- This is continuous (composition of f with continuous path)
  -- exp(-f(s·z)) = exp(-f(0)) for all s ∈ [0,1]
  -- So f(s·z) - f(0) ∈ {n · (2πI) : n ∈ ℤ} for all s
  -- ‖f(s·z) - f(0)‖ ∈ {0, 2π, 4π, ...}
  -- At s = 0: f(0·z) - f(0) = 0, so ‖...‖ = 0
  -- By continuity: ‖f(s·z) - f(0)‖ → 0 as s → 0
  -- So for small s, ‖f(s·z) - f(0)‖ < 2π, hence = 0
  -- The set {s ∈ [0,1] : f(s·z) = f(0)} is nonempty, open, and closed
  -- → = [0,1] by connectedness → f(z) = f(0)

  by_contra hne
  -- f(z) ≠ f(0). Get the integer n such that f(z) - f(0) = -n · (2πI)
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.mp (hgf z)
  -- hn : -f(z) = -f(0) + n · (2πI)
  -- So f(z) - f(0) = -n · (2πI)
  -- Since f(z) ≠ f(0), n ≠ 0
  have hn_ne : n ≠ 0 := by
    intro hzero
    rw [hzero] at hn
    simp at hn
    exact hne hn
  -- ‖f(z) - f(0)‖ = |n| · 2π ≥ 2π (since n ≠ 0)
  -- Consider ψ(s) = ‖f(s·z) - f(0)‖ for s ∈ [0,1]
  -- ψ is continuous, ψ(0) = 0, ψ(1) = ‖f(z) - f(0)‖ ≥ 2π
  -- By IVT: ∃ s₀ ∈ (0,1), ψ(s₀) = π
  -- But ψ(s) ∈ {0, 2π, 4π, ...} for all s (from the exp equality)
  -- And π ∉ {0, 2π, 4π, ...} — contradiction
  sorry

end ApmCanaries.A94J05
