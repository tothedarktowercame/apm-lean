# Proof Outline: a01A07

## Problem

Let `{fₙ}` be analytic on a region `Ω ⊆ ℂ`, `F` continuous on `Ω`, with
`∫_D |fₙ - F| dA → 0` for every disk `D ⊂ Ω`. Show that `F` is analytic and
`fₙ → F`, `fₙ' → F'` uniformly on compact subsets.

## Proof sketch

**Step 1 (uniform convergence on compacts).** The mean value property for
analytic functions gives `|g(z₀)| ≤ (1/πr²) ∫_{D(z₀,r)} |g| dA`. Applied to
`g = fₙ - fₘ`, this shows `sup_K |fₙ - fₘ| ≤ (1/πr²) ∫_{D_K} |fₙ-fₘ| dA → 0`,
so `{fₙ}` is uniformly Cauchy on each compact `K`.

**Step 2 (F is analytic).** By Morera's theorem: `∮_Δ F = lim ∮_Δ fₙ = 0`
for every triangle `Δ ⊂ Ω`.

**Step 3 (fₙ' → F' uniformly on compacts).** Cauchy derivative estimate:
`|fₙ'(z) - F'(z)| ≤ (1/ρ) sup_{|w-z|=ρ} |fₙ(w) - F(w)| → 0`.

## Lean formalization status

**Classification: partial** (5 sorries, 0 errors)

### Statement repairs

1. Added `MeasureSpace ℂ` instance via `volume.map Complex.equivRealProd.symm`
   (Mathlib has no direct `MeasureSpace ℂ` instance)
2. Fixed imports (`Bochner.Basic`, `Haar.OfBasis`, `Prod`)
3. Used default `volume` from the instance (no explicit `∂volume`)
4. Added `noncomputable` to the instance

### Sorries (5)

1. `norm_le_area_integral_div_area` — mean value property for analytic
   functions. Mathlib has circle-integral Cauchy formulas but not a direct
   area-integral mean value property.
2. `tendstoUniformlyOn_of_L1_on_disks` — Step 1: requires the mean value
   property + compact-to-boundary distance + Cauchy criterion.
3. `differentiableOn_of_L1_limit` — Step 2: Morera's theorem via triangle
   contour integrals.
4. `deriv_norm_le_sup_div_radius` — Cauchy derivative estimate from the
   Cauchy integral formula for derivatives.
5. `tendstoUniformlyOn_deriv_of_L1` — Step 3: depends on Steps 1+2 and
   the Cauchy estimate.

### Blockers

All sorries are at genuine Mathlib API boundaries:
- No area-integral mean value property for holomorphic functions in Mathlib
- No packaged Morera theorem (`∮_Δ = 0 ⟹ analytic`)
- The compact-distance-to-boundary argument needs plumbing through
  `Metric.infDist_pos_of_isCompact` + `IsOpen`
- Cauchy derivative estimates exist via circle integrals but require
  careful `circleIntegral` API assembly

## Files

- Lean attempt: `lean/Main.lean`
