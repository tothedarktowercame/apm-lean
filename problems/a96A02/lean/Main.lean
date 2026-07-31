/-
! # APM a96A02: Hölder-1/2 continuous but not absolutely continuous piecewise linear function

f is piecewise linear on [0,1] with f(0)=0, f(1/n)=0, f(midpoint_n)=1/n.
(a) |f(x)-f(y)| ≤ A|x-y|^{1/2} (Hölder-1/2).
(b) f is not absolutely continuous.

## Proof strategy

(a) Within spike n: slope = 2(n+1), height = 1/n.
    |f(x)-f(y)|² ≤ height · slope · |x-y| = (1/n)(2(n+1))|x-y| ≤ 4|x-y|.
(b) Intervals [1/(n+1), m_n] for n=N,...,2N: total length → 0, total oscillation ≥ log(2)/2.

## Theory boundaries

- The piecewise linear function with infinitely many spikes is hard to define
  in Lean (requires careful case analysis or an inductive definition).
- Hölder continuity (`HolderOnWith`) IS in Mathlib but the spike function
  definition is the main obstacle.

## Statement repair

The generated `spikeFunction` had a sorry in its def. We define it as an
opaque function for the purpose of stating the theorem, with a precise
specification of its values. The key arithmetical lemmas are provable.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set Real

open scoped ENNReal

noncomputable section

/-- The piecewise linear spike function.

f(0) = 0, f(1/n) = 0 for n ≥ 1, f(midpoint_n) = 1/n.
Piecewise linear between these points.

This function has infinitely many triangular spikes of height 1/n
on intervals [1/(n+1), 1/n], creating a Hölder-1/2 continuous but
not absolutely continuous function on [0,1].

We define it opaquely since the full piecewise-linear construction
with infinitely many pieces is technically involved. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): remove the constant-zero
-- placeholder; the repaired theorems require the exact triangular-spike
-- specification below.
opaque spikeFunction : ℝ → ℝ

/-- The midpoint of the interval `[1/(n+1), 1/n]`. -/
def spikeMidpoint (n : ℕ) : ℝ :=
  1 / (2 * (n : ℝ)) + 1 / (2 * ((n : ℝ) + 1))

/-- Exact specification of the triangular spikes from the informal problem.

On spike `n`, the function rises linearly from zero to height `1/n` and then
falls linearly back to zero.  Keeping this as a hypothesis makes the currently
opaque construction explicit without pretending that the constant-zero
placeholder was the intended function. -/
structure SpikeFunctionSpec (f : ℝ → ℝ) : Prop where
  at_zero : f 0 = 0
  on_left (n : ℕ) (hn : 0 < n) (x : ℝ)
      (hx : x ∈ Icc (1 / ((n : ℝ) + 1)) (spikeMidpoint n)) :
      f x = 2 * ((n : ℝ) + 1) * (x - 1 / ((n : ℝ) + 1))
  on_right (n : ℕ) (hn : 0 < n) (x : ℝ)
      (hx : x ∈ Icc (spikeMidpoint n) (1 / (n : ℝ))) :
      f x = 2 * ((n : ℝ) + 1) * (1 / (n : ℝ) - x)

/-- Within spike n: height × slope = (1/n) · 2(n+1) ≤ 4 for n ≥ 1.

This is the key bound: height × slope ≤ 4 ensures |f(x)-f(y)|² ≤ 4|x-y|
within a single spike, giving the Hölder-1/2 bound with constant A = 2.

Proof: (1/n) · 2(n+1) = 2(1 + 1/n) ≤ 2(1 + 1) = 4 for n ≥ 1. -/
lemma spike_height_slope_bound (n : ℕ) (hn : 0 < n) :
    (1 / (↑n : ℝ)) * (2 * (↑n + 1)) ≤ 4 := by
  -- For n ≥ 1: (1/n)·2(n+1) = 2 + 2/n ≤ 2 + 2 = 4.
  -- This is trivial arithmetic but requires division manipulation.
  sorry

/-- The base of spike n: |1/n - 1/(n+1)| = 1/(n(n+1)). -/
lemma spike_base_length (n : ℕ) (hn : 0 < n) :
    1 / ↑n - 1 / (↑n + 1 : ℝ) = 1 / (↑n * (↑n + 1)) := by
  field_simp
  ring
/-- Hölder-1/2 bound: |f(x)-f(y)| ≤ 2|x-y|^{1/2}.

**Blocker:** Requires the full spike function definition and the
within-spike bound |f(x)-f(y)|² ≤ 4|x-y|, plus the cross-spike
argument using f = 0 at junction points. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): require the exact
-- triangular-spike specification so this is no longer a theorem about a
-- constant-zero placeholder.
theorem spikeFunction_holderWith :
    SpikeFunctionSpec spikeFunction →
    ∃ A : ℝ, 0 < A ∧ ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      |spikeFunction x - spikeFunction y| ≤ A * |x - y| ^ ((1:ℝ) / 2) := by
  sorry

/-- Not absolutely continuous on [0,1].

**Blocker:** Requires constructing the AC-violating collection of intervals. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): require the exact
-- triangular-spike specification so the non-AC conclusion concerns the
-- intended function rather than the false constant-zero model.
theorem spikeFunction_not_absolutelyContinuous :
    SpikeFunctionSpec spikeFunction →
    ∃ ε > 0, ∀ δ > 0, ∃ (n : ℕ) (a b : Fin n → ℝ),
      (∀ i, a i ∈ Icc 0 1) ∧ (∀ i, b i ∈ Icc 0 1) ∧
      (∀ i, a i ≤ b i) ∧
      (∀ i j, i < j → b i ≤ a j) ∧
      ∑ i, (b i - a i) < δ ∧
      ε ≤ ∑ i, |spikeFunction (b i) - spikeFunction (a i)| := by
  sorry

end
