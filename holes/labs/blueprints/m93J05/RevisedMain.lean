import Mathlib

open MeasureTheory Filter

/-!
# APM m93J05 — Fourier truncation and its variational functional

## Statement repairs

1. The source asks for the “cokernel” to be described.  For a projection this
   is canonically represented by its complementary (high-frequency) subspace;
   the statement records that direct-sum decomposition rather than the source
   note's incorrect description of the cokernel as functions with nonzero low
   modes.
2. Variations in the Euler equation are restricted to `Lᵖ` directions.  Without
   `MemLp h (ENNReal.ofReal p) μ`, the path immediately leaves the functional's
   domain and `ENNReal.toReal` turns an infinite norm into the junk value zero,
   so the asserted derivative can fail to exist.

## Encoding note

Functions are represented by measurable representatives on `[0,1]`; all
`L^p` assertions and pairings use Lebesgue measure restricted to that interval.
-/

noncomputable def apm_m93j05_cosCoeff (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  2 * ∫ θ in Set.Icc (0 : ℝ) 1, f θ * Real.cos (j * 2 * Real.pi * θ)

noncomputable def apm_m93j05_sinCoeff (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  2 * ∫ θ in Set.Icc (0 : ℝ) 1, f θ * Real.sin (j * 2 * Real.pi * θ)

noncomputable def apm_m93j05_trunc (N : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  (∫ x in Set.Icc (0 : ℝ) 1, f x) +
    ∑ j ∈ Finset.Icc 1 N,
      (apm_m93j05_cosCoeff f j * Real.cos (j * 2 * Real.pi * θ) +
       apm_m93j05_sinCoeff f j * Real.sin (j * 2 * Real.pi * θ))

noncomputable def apm_m93j05_J (N : ℕ) (p : ℝ) (g f : ℝ → ℝ) : ℝ :=
  Real.rpow (eLpNorm (fun x => f x - apm_m93j05_trunc N f x)
      (ENNReal.ofReal p) (volume.restrict (Set.Icc 0 1))).toReal p +
    (eLpNorm (apm_m93j05_trunc N f) 2
      (volume.restrict (Set.Icc 0 1))).toReal ^ 2 +
    ∫ x in Set.Icc (0 : ℝ) 1, f x * g x

theorem apm_m93j05 :
    ∀ (N : ℕ) (p q : ℝ), 1 < p → 1 < q → 1 / p + 1 / q = 1 →
    let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
    let Φ := apm_m93j05_trunc N
    (∀ f g, MemLp f (ENNReal.ofReal p) μ → MemLp g (ENNReal.ofReal q) μ →
      ∫ x, Φ f x * g x ∂μ = ∫ x, f x * Φ g x ∂μ) ∧
    (∀ f, Φ f = 0 ↔
      (∫ x in Set.Icc (0 : ℝ) 1, f x = 0 ∧
       ∀ j ∈ Finset.Icc 1 N,
         apm_m93j05_cosCoeff f j = 0 ∧ apm_m93j05_sinCoeff f j = 0)) ∧
    (∀ f, ∃ u v, f = u + v ∧ Φ u = u ∧ Φ v = 0) ∧
    (∀ g, MemLp g (ENNReal.ofReal q) μ →
      (∀ (f : ℝ → ℝ) (s : ℕ → ℝ → ℝ),
        MemLp f (ENNReal.ofReal p) μ →
        (∀ n, MemLp (s n) (ENNReal.ofReal p) μ) →
        (∀ h, MemLp h (ENNReal.ofReal q) μ →
          Tendsto (fun n => ∫ x, s n x * h x ∂μ) atTop
            (nhds (∫ x, f x * h x ∂μ))) →
        ∀ r, (∀ᶠ n in atTop, r ≤ apm_m93j05_J N p g (s n)) →
          r ≤ apm_m93j05_J N p g f) ∧
      (∃ f₀, MemLp f₀ (ENNReal.ofReal p) μ ∧
        ∀ f, MemLp f (ENNReal.ofReal p) μ →
          apm_m93j05_J N p g f₀ ≤ apm_m93j05_J N p g f) ∧
      (∀ f₀, MemLp f₀ (ENNReal.ofReal p) μ →
        (∀ f, MemLp f (ENNReal.ofReal p) μ →
          apm_m93j05_J N p g f₀ ≤ apm_m93j05_J N p g f) →
        ∀ h, MemLp h (ENNReal.ofReal p) μ →
          HasDerivAt
            (fun t : ℝ => apm_m93j05_J N p g (f₀ + t • h)) 0 0)) := by
  sorry
