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
  sorry
