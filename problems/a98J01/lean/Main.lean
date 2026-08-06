import Mathlib

open MeasureTheory Set

noncomputable section

/-!
# APM a98J01

## Statement repairs

None.

## Encoding notes

The interval function is represented by a globally measurable real function and
then restricted to `[a,b]`. Continuity of its restriction to the large compact set
is expressed by `ContinuousOn f K`, i.e. continuity in the subspace topology on `K`.
-/

theorem apm_a98j01
    {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : Measurable f) :
    ∀ ε : ℝ, 0 < ε →
      ∃ K : Set ℝ,
        K ⊆ Icc a b ∧
        IsCompact K ∧
        volume (Icc a b \ K) < ENNReal.ofReal ε ∧
        ContinuousOn f K := by
  -- LUSIN'S THEOREM: measurable functions are "almost" continuous.
  --
  -- Strategy (from informal solution):
  -- 1. Approximate f by simple functions s_n → f pointwise
  --    (Mathlib: `SimpleFunc.approxOn` + `tendsto_approxOn`)
  -- 2. Each simple function is continuous off a small compact set
  --    (requires inner regularity + disjoint compact separation)
  -- 3. Egorov: s_n → f uniformly on a large compact set
  --    (Mathlib: `tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist`)
  -- 4. Intersect good sets; uniform limit of continuous = continuous
  --    (Mathlib: `TendstoUniformlyOn.continuousOn_of_continuousOn` or similar)
  --
  -- Mathlib ingredients verified available:
  -- - `InnerRegularCompactLTTop volume` on ℝ: ✓ (compact approximation of measurable sets)
  -- - `OuterRegular volume` on ℝ: ✓
  -- - Egorov: `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist`: ✓
  -- - `SimpleFunc.approxOn` + `tendsto_approxOn`: ✓ (pointwise approximation)
  --
  -- BOUNDARY: The assembly requires:
  -- (a) Constructing simple function sequence converging to f on [a,b]
  --     with measurable edist (for Egorov applicability)
  -- (b) For each simple function, proving continuity on a compact subset
  --     (Step 1 of informal proof: disjoint compact level sets at positive
  --     distance → locally constant → continuous)
  -- (c) Budgeting measure: ε/2^n across infinitely many steps
  -- (d) Intersecting countably many compact sets (remaining compact)
  -- (e) Uniform limit continuity on the intersection
  --
  -- Blocker: Steps (b) and (c) require ~50-80 lines of careful measure-theoretic
  -- formalization, combining inner regularity with compact separation in ℝ.
  -- The overall proof is a multi-page argument that exceeds the pass-1 budget.
  --
  -- APIs searched: `InnerRegularCompactLTTop`, `OuterRegular`, `tendstoUniformlyOn_of_ae_tendsto`,
  -- `SimpleFunc.approxOn`, `tendsto_approxOn`, `MeasurableSet.exists_lt_isCompact_of_ne_top`
  sorry
