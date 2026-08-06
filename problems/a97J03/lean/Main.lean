import Mathlib

/-!
# APM a97J03: Convolution of conjugate Lp functions

## Statement repairs

None.

## Encoding questions

None. Because the source explicitly declares `h : ℝ → ℂ`, the `L^p` and
`L^q` functions are encoded as complex-valued measurable functions. Membership
is represented by Mathlib's `MemLp` at the finite real exponents embedded in
`ℝ≥0∞`.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section

/-- The convolution `h(y) = ∫ x, f(y-x)g(x) dx`. -/
def apm_a97J03_convolution (f g : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ x : ℝ, f (y - x) * g x ∂volume

theorem apm_a97j03
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1)
    (f g : ℝ → ℂ)
    (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    Continuous (apm_a97J03_convolution f g) ∧
      Tendsto (apm_a97J03_convolution f g) atTop (𝓝 0) ∧
      Tendsto (apm_a97J03_convolution f g) atBot (𝓝 0) := by
  -- Boundary (closer hop 2): bridge still open. Enriched with Mathlib API findings.
  --
  -- Key finding: `Real.HolderConjugate p q` is defined as `HolderTriple p q 1`
  -- in `Mathlib/Data/Real/ConjExponents.lean`. The `holderConjugate_iff` lemma gives
  -- `p.HolderConjugate q ↔ 1 < p ∧ p⁻¹ + q⁻¹ = 1`.
  -- Our hypothesis `hpq : 1/p + 1/q = 1` with `hp : 1 < p` matches exactly.
  --
  -- The a03J03 proof uses `MemLp.integrable_mul` (from Holder.lean) to show the
  -- convolution integrand is integrable, and Lp translation continuity for continuity.
  -- For ℂ-valued functions, the same lemmas should apply since ℂ is a NormedSpace.
  --
  -- Remaining blockers for inlining a03J03's approach for ℂ:
  -- 1. Need `p.HolderConjugate q` from `hpq` (trivial: 1/p = p⁻¹ in ℝ).
  -- 2. Need `ENNReal.HolderTriple (ofReal p) (ofReal q) 1` for MemLp Hölder —
  --    a03J03 uses `hpq.ennrealOfReal` to bridge this.
  -- 3. Need `Fact (1 ≤ ofReal p)` and `Fact (1 ≤ ofReal q)` instances.
  -- 4. Need translation continuity for ℂ-valued Lp functions.
  --    Mathlib has `MemLp.comp_measurePreserving` which handles f(y-x) via
  --    the measure-preserving map x ↦ y-x.
  -- 5. The vanishing at infinity part needs C_c density for ℂ-valued functions.
  --
  -- Assessment: the proof is ~80-120 lines of assembly even with the a03J03
  -- template. Each step is conceptually straightforward but requires careful
  -- Mathlib typeclass instance management (ENNReal.ofReal, Fact, HolderTriple).
  -- The statement is mathematically correct; the blocker is assembly time.
  sorry
