import Mathlib

/-!
# APM a97J08

## Statement repairs

None.

## Encoding questions

Mathlib has no single bundled type for a rectifiable Jordan curve. The source's
condition is encoded without weakening as continuity and bounded variation on
`[0,1]`, equality of the endpoints, and injectivity on `[0,1)`. The interior is
the union of the bounded connected components of the complement of the curve.
Zero counts use the positive part of the meromorphic divisor, hence count
multiplicity rather than merely distinct zero locations.
-/

open Filter Metric Set
open scoped Topology

noncomputable section

/-- The image `Γ` of a parametrized closed curve. -/
def apm_a97j08_curveImage (γ : ℝ → ℂ) : Set ℂ :=
  γ '' Icc (0 : ℝ) 1

/-- The bounded side of a Jordan curve: the bounded connected components of
its complement. -/
def apm_a97j08_curveInterior (γ : ℝ → ℂ) : Set ℂ :=
  {z | z ∉ apm_a97j08_curveImage γ ∧
    Bornology.IsBounded
      (connectedComponentIn (apm_a97j08_curveImage γ)ᶜ z)}

/-- The number of zeros in `U`, counted with multiplicity by the positive
part of the divisor. -/
def apm_a97j08_zeroCount (f : ℂ → ℂ) (U : Set ℂ) : ℤ :=
  ∑ᶠ z : ℂ, max (MeromorphicOn.divisor f U z) 0

/-! ## Blocker analysis

This is the Hurwitz/Rouché theorem: zeros are stable under locally uniform
convergence. The proof requires:

1. **Weierstrass convergence theorem**: g is analytic (limit of analytic f_n).
   - Mathlib has `TendstoLocallyUniformlyOn` but no pre-packaged theorem that
     the locally uniform limit of holomorphic functions is holomorphic.

2. **Jordan curve theorem**: the interior of a Jordan curve is well-defined.
   - Mathlib has NO Jordan curve theorem. `apm_a97j08_curveInterior` is defined
     via `connectedComponentIn` and `Bornology.IsBounded`, but there is no
     theorem that a simple closed curve bounds a unique bounded region.

3. **Rouché's theorem / argument principle**: zero-counting via contour integrals.
   - Mathlib (v4.29.0-rc8) has NO Rouché's theorem, NO argument principle
     (`(1/2πi)∮ f'/f dz = number of zeros`), NO winding number.
   - Available: `Complex.circleIntegral_sub_inv_smul` (Cauchy integral formula),
     `MeromorphicOn.divisor` (divisor function), `MeromorphicOn.extract_zeros_poles`
   - But no theorem connecting contour integrals to zero counts.

4. **Homotopy invariance of zero count**: integer-valued continuous function is
   eventually constant — the key mechanism behind Rouché.

The statement is TRUE as stated. The blocker is a fundamental Mathlib
infrastructure gap: the entire argument-principle / Rouché / Hurwitz pipeline
is absent. This is the same gap that blocks a94A09. -/

theorem apm_a97j08 (D : Set ℂ) (γ : ℝ → ℂ) (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hD_open : IsOpen D)
    (hD_simplyConnected : IsSimplyConnected D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγ_closed : γ 0 = γ 1)
    (hγ_simple : Set.InjOn γ (Ico (0 : ℝ) 1))
    (hγ_rectifiable : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hγD : apm_a97j08_curveImage γ ⊆ D)
    (hF_analytic : ∀ n, DifferentiableOn ℂ (F n) D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D)
    (hg_ne : ∀ z ∈ apm_a97j08_curveImage γ, g z ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N,
      apm_a97j08_zeroCount (F n) (apm_a97j08_curveInterior γ) =
        apm_a97j08_zeroCount g (apm_a97j08_curveInterior γ) := by
  -- SKIPPED: Hurwitz/Rouché theorem — zeros stable under locally uniform convergence.
  -- Requires: Weierstrass convergence theorem, Jordan curve theorem, Rouché's theorem /
  -- argument principle — ALL absent from Mathlib. Same infrastructure gap as a94A09.
  -- The file documents the full blocker analysis including which Mathlib APIs exist
  -- (circleIntegral, MeromorphicOn.divisor) but are insufficient (no contour-to-zero-count).
  -- -- (Memory: e-codexpilot-prove-Hurwitz-zero-persistence-through-quantitative-open-mapping)
  -- --    confirms Hurwitz zero persistence is the core; (Memory: e-codexpilot-straight-line-rouche-homotopy-stays-nonzero-on-boundary)
  -- --    confirms the Rouché boundary condition approach.
  sorry
