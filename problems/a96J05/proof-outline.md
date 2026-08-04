# Proof Outline: a96J05

## Problem

Let 1 ≤ p < q ≤ ∞. Define X = L^p([0,1],ν) + L^q([0,1],ν) with the infimum
norm ‖f‖_X = inf{‖g‖_p + ‖h‖_q : g ∈ L^p, h ∈ L^q, f = g + h}.
Prove: X is a vector space, ‖·‖_X is a norm, X is complete.

## Strategy

Quotient of Banach spaces: X ≅ (L^p × L^q) / K where K = ker(addition map).
The quotient of a complete normed space by any submodule is complete
(`Submodule.Quotient.completeSpace`).

## Proved (exit 0, 1 sorry)

1. **Part 1 (vector space):** `sum_space_add_closed`, `sum_space_neg_closed`
   — closure under addition and negation, using AddSubgroup coercion to AEEqFun
   and AC rearrangement.

2. **Part 2 (norm):**
   - `sumNorm_nonneg` — infimum of nonneg values is nonneg
   - `sumNorm_triangle` — choose near-optimal decompositions via `Real.lt_sInf_add_pos`,
     combine with `norm_add_le`, close by `linarith`
   - `sumNorm_smul` — **SORRY** (homogeneity; scalar action on AEEqFun needs coercion work)

3. **Part 3 (completeness):**
   - `quotient_complete` — quotient of Banach by submodule is Banach (inferInstance)
   - `lp_prod_complete` — Lp p × Lp q is Banach (CompleteSpace.prod + Lp.instCompleteSpace)

## Axioms

All proved theorems: `propext, Classical.choice, Quot.sound` (standard).

## Boundary

- **sumNorm_smul:** The scalar multiplication `c • (g + h)` on AEEqFun doesn't
  directly factor through Lp scalar multiplication. Need to show `c • ↑g = ↑(c • g)`
  in AEEqFun, which requires the `NormedSpace ℝ E` instance on Lp and the coercion
  compatibility. APIs searched: `AEEqFun.smul_mk`, `Lp.coe_smul`.

- **Definiteness (not yet stated):** ‖f‖_X = 0 ⟹ f = 0 a.e. requires:
  if ‖gₙ‖_p → 0 and ‖hₙ‖_q → 0 with gₙ + hₙ = f, then f = 0 a.e.
  Uses: Lp convergence → convergence in measure → a.e. subsequence.
  Mathlib APIs: `MeasureTheory.tendstoInMeasure_of_tendsto_snorm`.

- **Full completeness instantiation:** Requires defining the addition map
  T: Lp p × Lp q → AEEqFun as a NormedAddGroupHom, proving the antidiagonal
  kernel K = {(g,h) : ↑g + ↑h = 0} is a closed submodule, and applying
  `Submodule.Quotient.completeSpace`. The abstract theorem (`quotient_complete`)
  is proved; the concrete instantiation to the Lp sum space is the remaining bridge.
