import Mathlib

/-!
# APM a97A01 — weak convergence of the Rademacher functions

## Statement repairs

The source says `f_n(t) = 1` on both the odd and even dyadic intervals. This
would make the sequence constant almost everywhere and the claimed limit
false. Following the supplied solution, the value on even intervals is
repaired to `-1`; these are the Rademacher functions.

## Encoding questions

None. `f ∈ L∞([0,1])` is represented by `MemLp f ∞` for Lebesgue measure
restricted to `Icc 0 1`, so representatives and almost-everywhere behavior
are retained explicitly.
-/

open Filter MeasureTheory Set

noncomputable section

def apm_a97A01_measure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The source's dyadic sign function, including its specified endpoint
value. -/
def apm_a97A01_rademacher (n : ℕ) (t : ℝ) : ℝ := by
  classical
  exact if n = 1 then 1
    else if t = 1 then -1
    else if ∃ k : ℕ,
        1 ≤ k ∧ k ≤ 2 ^ n ∧ Odd k ∧
        t ∈ Set.Ico (((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ))
          ((k : ℝ) / (2 ^ n : ℕ))
      then 1 else -1

theorem apm_a97a01
    (f : ℝ → ℝ) (hf : MemLp f ⊤ apm_a97A01_measure) :
    Tendsto
      (fun n : ℕ ↦ ∫ t,
        f t * apm_a97A01_rademacher n t ∂apm_a97A01_measure)
      atTop (nhds 0) := by
  sorry
