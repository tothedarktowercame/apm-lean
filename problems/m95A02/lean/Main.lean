import Mathlib

/-! # APM m95A02: the periodic Sobolev space `H¹`

## Statement repairs

None.

## Encoding note

Mathlib does not bundle periodic `W^{1,2}`.  We use its exact weighted-Fourier
realization: an element of `m95A02H = ℓ²(ℤ, ℂ)` stores the coefficient in the
normalized basis `exp (inx) / √(2π(n²+1))`.  Consequently its `ℓ²` inner product
is precisely the Sobolev inner product printed in the question.
-/

open Filter Set

noncomputable section

abbrev m95A02H := lp (fun _ : ℤ => ℂ) 2

def m95A02BasisFunction (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) /
    (Real.sqrt (2 * Real.pi * ((n : ℝ) ^ 2 + 1)) : ℂ)

def m95A02Value (f : m95A02H) (x : ℝ) : ℂ :=
  ∑' n : ℤ, f n * m95A02BasisFunction n x

def m95A02MaxDist (f g : m95A02H) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ Icc (0 : ℝ) (2 * Real.pi),
    r = dist (m95A02Value f x) (m95A02Value g x)}

theorem apm_m95a02 :
    (∃ b : HilbertBasis ℤ ℂ m95A02H,
      ∀ n : ℤ, b n = lp.single 2 n 1 ∧
        ∀ x : ℝ, m95A02Value (b n) x = m95A02BasisFunction n x) ∧
    (∀ (f : m95A02H) (x y : ℝ),
      dist (m95A02Value f x) (m95A02Value f y) ≤
        |x - y| ^ (1 / 2 : ℝ) * ‖f‖) ∧
    (∀ (f : ℕ → m95A02H) (g : m95A02H),
      Tendsto (fun n => toWeakSpace ℂ m95A02H (f n)) atTop
        (nhds (toWeakSpace ℂ m95A02H g)) →
      Tendsto (fun n => m95A02MaxDist (f n) g) atTop (nhds 0)) := by
  sorry
