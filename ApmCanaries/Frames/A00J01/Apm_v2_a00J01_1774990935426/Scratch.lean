import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Order.Filter.AtTopBot.Field

open NNReal ENNReal Filter Topology

-- For NNReal: t^y is jointly continuous (NNReal.continuous_rpow)
-- So for fixed t > 0: y ↦ t^y is continuous
-- Hence t^{1/p} → t^0 = 1 as 1/p → 0

-- Step 1: 1/p → 0 as p → ∞
lemma inv_tendsto : Tendsto (fun p : ℝ => 1 / p) atTop (nhds 0) :=
  by simpa [one_div] using
    (tendsto_inv_atTop_zero : Tendsto (fun p : ℝ => p⁻¹) atTop (𝓝 0))

-- Actually, let's try the NNReal route directly
-- NNReal.rpow is jointly continuous → tendsto in exponent for fixed base
-- Mathlib exposes the real-valued route we need directly, so we stop here.
