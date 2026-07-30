import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# APM a01A05: Nearly-orthogonal sequences and Gram-Schmidt

**Problem.** Let `{fₙ}` be a sequence in a real Hilbert space `H` with
`‖fₙ‖ = 1` for all `n`, and `|⟨fₙ, fₘ⟩| ≤ 2⁻ᵐ` for all `n < m`.
Let `{eₙ}` be a Gram-Schmidt orthonormalization of `{fₙ}`.

(a) Show that `‖fₘ - eₘ‖ ≤ 2⁻ᵐ`.
(b) For any `g ∈ H`, show that `⟨g, fₘ⟩ → 0` as `m → ∞`.

In the original problem, `H = L²(ℝ)` with `⟨f,g⟩ = ∫ fg dx`.

**Statement repair note.**

The informal-solution file `apm-a01A05.md` was harvested with the **wrong
content**: it contains the proof for a01A04 (unit ball volumes), not a01A05
(Gram-Schmidt / nearly-orthogonal sequences). This file implements the correct
problem from `a01A05.tex`.
-/

set_option linter.unusedVariables false in
noncomputable section

open Filter

namespace ApmCanaries.A01A05

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A sequence of unit vectors with nearly-orthogonal inner products. -/
structure NearOrthogonalSeq (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] where
  /-- The sequence of unit vectors -/
  f : ℕ → H
  /-- Each fₙ has norm 1 -/
  norm_one : ∀ n, ‖f n‖ = 1
  /-- Inner products decay: |⟨fₙ, fₘ⟩| ≤ 2⁻ᵐ for n < m -/
  inner_bound : ∀ n m, n < m → |inner ℝ (f n) (f m)| ≤ (2 : ℝ) ^ (-(m : ℝ))

/-! ## Part (b): ⟨g, fₘ⟩ → 0 for any g ∈ H -/

/-- Part (b): For any `g ∈ H`, the inner products `⟨g, fₘ⟩ → 0`.

    **SORRY BOUNDARY:** The proof uses Bessel's inequality to show
    `⟨g, eₘ⟩ → 0` for the Gram-Schmidt orthonormalization, then transfers
    via part (a). This requires connecting the Gram-Schmidt orthonormalization
    with Bessel's inequality and the near-orthogonality hypothesis.
-/
theorem inner_tendsto_zero [CompleteSpace H]
    (seq : NearOrthogonalSeq H) (g : H) :
    Tendsto (fun m => inner ℝ g (seq.f m)) atTop (nhds 0) := by
  sorry

/-! ## Part (a): ‖fₘ - eₘ‖ ≤ 2⁻ᵐ -/

/-- Part (a): The Gram-Schmidt orthonormalization `{eₙ}` satisfies
    `‖fₘ - eₘ‖ ≤ 2⁻ᵐ`.

    **SORRY BOUNDARY:** Requires computing the Gram-Schmidt projection
    explicitly and bounding it using the near-orthogonality condition.
    Mathlib's `gramSchmidtNormed` provides the orthonormalization but the
    specific error bound requires the near-orthogonality condition.
-/
-- STATEMENT REPAIR 2026-07-30 (Joe-authorised). See faithfulness-ledger #7.
-- This is the one CLASS-C row: the ORIGINAL EXAM asks to "Show that
-- |f_m - e_m| ≤ 2⁻ᵐ", and that is false — Gram–Schmidt error ACCUMULATES over
-- all preceding vectors, so a per-PAIR hypothesis cannot yield the same bound on
-- the accumulated error. Knife-edge witness in ℓ²: f₀ = e₀,
-- f₁ = ½e₀ + (√3/2)e₁ saturates the hypothesis exactly (⟨f₀,f₁⟩ = ½ = 2⁻¹) yet
-- ‖f₁ - e₁‖ = √(2-√3) ≈ 0.5176 > 0.5. Margin ≈ 0.018; it still fails under
-- 1-indexing (≈ 0.252 vs 0.25). The deciding inequality was machine-checked.
--
-- Repaired to the O(2⁻ᵐ) reading, which is the evident intent and is
-- conservative: a uniform constant absorbs the accumulation. NOTE FOR REVIEW —
-- unlike the class-A repairs in the other files, this one is NOT dictated by an
-- informal solution (a01A05 has none); the choice of `∃ C` is ground control's
-- reading of the exam's intent and should be sanity-checked.
theorem gramSchmidt_approximation [CompleteSpace H]
    (seq : NearOrthogonalSeq H) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      ‖seq.f m - InnerProductSpace.gramSchmidtNormed ℝ seq.f m‖
        ≤ C * (2 : ℝ) ^ (-(m : ℝ)) := by
  sorry

end ApmCanaries.A01A05
