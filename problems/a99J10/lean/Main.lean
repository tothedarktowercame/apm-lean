import Mathlib

/-!
# APM a99J10 — boundary uniqueness under square-root growth

## Statement repairs

The displayed bound `|f(x + iy)| ≤ |y|⁻¹ᐟ²` is singular when `y = 0`.
It is therefore imposed when `y ≠ 0`, which is the minimal domain restriction
needed to express the source's intended blow-up bound without assigning it a
spurious finite value on the real diameter.

## Encoding notes

The radial limit is expressed as `r → 1⁻` for every angle in `[0, 2π]`.
-/

open Set Filter
open scoped Topology
open Metric

theorem apm_a99j10 (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, z.im ≠ 0 →
      ‖f z‖ ≤ Real.rpow |z.im| (-(1 : ℝ) / 2))
    (hradial : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      Tendsto
        (fun r : ℝ => f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (𝓝[<] (1 : ℝ)) (𝓝 0)) :
    ∀ z ∈ ball (0 : ℂ) 1, f z = 0 := by
  -- SKIPPED: boundary uniqueness under square-root growth |f(z)| ≤ |y|^{-1/2}.
  -- Requires: maximum principle / Phragmén-Lindelöf with singular growth bound
  -- + vanishing radial limits → f≡0. The |y|^{-1/2} bound controls blow-up near
  -- real axis; vanishing on all boundary directions + growth control forces f=0.
  -- Blocker: Mathlib has maximum modulus (`Complex.norm_le_of_forall_mem_frontier_norm_le`)
  -- but not Phragmén-Lindelöf type results with singular bounds on unbounded growth.
  -- APIs: `DifferentiableOn`, `Tendsto`, `Complex.norm_le_of_forall_mem_frontier_norm_le`
  sorry
