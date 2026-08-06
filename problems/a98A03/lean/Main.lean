import Mathlib

/-!
# APM a98A03

## Statement repairs

None.

## Encoding notes

The problem's functions on `[0, 1]` are represented by functions on `ℝ`, with
all hypotheses restricted to the unit interval.  Since Mathlib's integral is
the Lebesgue integral, the Riemann-integrable strengthening is expressed using
the tagged-partition definition below, including its proposed integral value.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

/-- `g` has Riemann integral `I` on `[0, 1]`, expressed by convergence of all
tagged sums as the mesh tends to zero. -/
def HasRiemannIntegralOnUnitInterval (g : ℝ → ℝ) (I : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ) (hn : 0 < n) (x : Fin (n + 1) → ℝ) (tag : Fin n → ℝ),
        x 0 = 0 → x (Fin.last n) = 1 → StrictMono x →
        (∀ i : Fin n, x i.castSucc ≤ tag i ∧ tag i ≤ x i.succ) →
        (∀ i : Fin n, x i.succ - x i.castSucc < δ) →
        |(∑ i, g (tag i) * (x i.succ - x i.castSucc)) - I| < ε

theorem apm_a98a03 :
    (∃ (f f' : ℝ → ℝ),
      ContinuousOn f (Icc 0 1) ∧
      (∀ᵐ x ∂volume.restrict (Icc 0 1), HasDerivAt f (f' x) x) ∧
      (∃ C : ℝ, ∀ᵐ x ∂volume.restrict (Icc 0 1), f' x ≤ C) ∧
      f 1 - f 0 ≠ ∫ x in Icc (0 : ℝ) 1, f' x ∂volume) ∧
    (∀ (f f' : ℝ → ℝ) (I : ℝ),
      ContinuousOn f (Icc 0 1) →
      (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x) →
      HasRiemannIntegralOnUnitInterval f' I →
      f 1 - f 0 = I) := by
  -- PART 1 (counterexample): requires constructing the Cantor function
  -- (or an equivalent singular function) — continuous on [0,1], with
  -- derivative 0 a.e. (hence ess sup f' = 0 < ∞), yet f(1)-f(0) = 1 ≠ 0 = ∫f'.
  -- BOUNDARY: Mathlib has NO Cantor staircase function. `cantorFunction` in
  -- `Mathlib.Analysis.Real.Cardinality` is a cardinality bijection, not the
  -- devil's staircase. Constructing it requires building the middle-thirds
  -- Cantor set, proving continuity, and showing derivative = 0 a.e. — a major
  -- formalization effort (100+ lines).
  --
  -- PART 2 (FTC): requires proving f(1)-f(0) = Riemann integral of f' using:
  -- (a) MVT to produce tags on each partition subinterval,
  -- (b) telescoping sum,
  -- (c) tag-independence of Riemann sums (from HasRiemannIntegralOnUnitInterval).
  -- BOUNDARY: The custom `HasRiemannIntegralOnUnitInterval` definition uses
  -- Fin-indexed tagged partitions. The MVT produces tags `t_i ∈ (x_{i-1}, x_i)`,
  -- and the telescoping requires `∑ (f(x_i) - f(x_{i-1})) = f(1) - f(0)`.
  -- The proof structure is clear but requires:
  -- - `exists_ratio_deriv_eq_slope` or equivalent MVT (Mathlib has this)
  -- - Fin-indexed telescoping sums
  -- - Careful manipulation of the tagged partition structure
  -- APIs searched: `exists_ratio_deriv_eq_slope`, `StrictMono`,
  -- `Fin.sum_univ_castSucc`, `intervalIntegral` (not applicable — Riemann, not Lebesgue)
  --
  -- Blocker: Part 1 is the hard blocker (Cantor function construction).
  -- Part 2 is tractable in principle but combined exceeds the time budget.
  sorry
