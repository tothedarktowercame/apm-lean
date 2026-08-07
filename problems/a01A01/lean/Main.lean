import Mathlib

open Filter MeasureTheory Set

noncomputable section

/-!
# APM a01A01

## Statement repairs

None.

## Encoding notes

The condition `∀ M N, ∃ k ≥ N, M ≤ f k x` is the cofinal quantified
characterization of `limsup (fun k ↦ f k x) = +∞`. The higher-dimensional
domain is the genuine Euclidean space `EuclideanSpace ℝ (Fin d)` with its
Lebesgue measure.
-/

theorem apm_a01a01 :
    (∃ f : ℕ → ℝ → ℝ,
      (∀ k, IntegrableOn (f k) (Icc (0 : ℝ) 1) volume) ∧
      (∀ k x, x ∈ Icc (0 : ℝ) 1 → 0 ≤ f k x) ∧
      (∀ x, x ∈ Icc (0 : ℝ) 1 →
        ∀ M : ℝ, ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ M ≤ f k x) ∧
      Tendsto (fun k ↦ ∫ x in Icc (0 : ℝ) 1, f k x ∂volume)
        atTop (nhds 0)) ∧
    (∀ d : ℕ, 0 < d →
      ∃ f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ k, Integrable (f k) volume) ∧
        (∀ k x, 0 ≤ f k x) ∧
        (∀ x, ∀ M : ℝ, ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ M ≤ f k x) ∧
        Tendsto (fun k ↦ ∫ x, f k x ∂volume) atTop (nhds 0)) := by
  /-
  CLOSER HOP 1 boundary: the bridge remains open after sustained research.

  `LEMMA-INDEX.md` contains nearby spike lemmas (`a01J01`, `a96A02`) but
  none sweeps every point while its integrals vanish. Git history contains an
  ungated orphan at `2e3057d` with substantial 1D typewriter helpers
  (`twStage`, `typewriter1d`, integral and cofinality arguments), but that file
  still ends in this same theorem-level `sorry`; it also places
  `twStage_tendsto_atTop` before its dependency `twStage_sq_gt`, so it is not a
  compiled reusable artifact. Importing it would additionally alter the
  frozen theorem presentation through an auxiliary predicate.

  For the Euclidean clause, Mathlib supplies
  `EuclideanSpace.volume_preserving_measurableEquiv_toLp`, `volume_pi_pi`,
  `Real.volume_Icc_pi`, and indicator-integrability machinery. The missing
  assembly is an explicit enumeration of all cells in the expanding cubes
  `[-m,m]^d`, with proof that (1) every point lies in one enumerated cell at
  arbitrarily large stages, (2) the global sequence index is cofinal, and
  (3) height times cell volume tends to zero. No closed sibling,
  `ConstructionTargets/` module, or `YoungL2.lean` lemma packages this
  enumeration and its volume calculation. The statement appears sound, but
  completing both clauses requires a sizeable new combinatorial development.
  -/
  sorry
