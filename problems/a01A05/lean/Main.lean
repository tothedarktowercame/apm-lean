import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# APM a01A05 — nearly orthogonal sequences and Gram–Schmidt

## Statement repairs

Part (a) is false as printed. Already for two unit vectors with inner product
`1/2`, normalized Gram–Schmidt can move the second vector by
`sqrt (2 - sqrt 3) > 1/2`. More generally, the pairwise bounds do not control
the accumulated Gram–Schmidt error by `2⁻ᵐ`. Accordingly, part (a) is stated
as the negation of the claimed universal estimate rather than silently
omitted. Part (b), which is valid, is preserved.

The harvested `informal-solution.md` contains material for a01A04 rather than
this problem, so the TeX source and the mathematical correction above are used.

## Encoding questions

None. Mathlib's actual normalized Gram–Schmidt construction is used.
-/

open Filter

noncomputable section

structure apm_a01A05_NearOrthogonalSeq (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  f : ℕ → H
  norm_one : ∀ n, ‖f n‖ = 1
  inner_bound : ∀ n m, n < m →
    |inner ℝ (f n) (f m)| ≤ (2 : ℝ) ^ (-(m : ℝ))

theorem apm_a01a05 :
    (¬ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      (seq : apm_a01A05_NearOrthogonalSeq H) (m : ℕ),
      ‖seq.f m - InnerProductSpace.gramSchmidtNormed ℝ seq.f m‖ ≤
        (2 : ℝ) ^ (-(m : ℝ))) ∧
    (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [CompleteSpace H] (seq : apm_a01A05_NearOrthogonalSeq H) (g : H),
      Tendsto (fun m ↦ inner ℝ g (seq.f m)) atTop (nhds 0)) := by
  sorry
