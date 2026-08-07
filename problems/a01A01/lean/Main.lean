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

/-- Stage number for the diagonal enumeration of pairs of naturals. -/
def apm_a01A01_stage (k : ℕ) : ℕ :=
  (Nat.unpair k).1 + (Nat.unpair k).2 + 1

/-- Position inside a diagonally enumerated stage. -/
def apm_a01A01_position (k : ℕ) : ℕ :=
  (Nat.unpair k).2

lemma apm_a01A01_position_lt_stage (k : ℕ) :
    apm_a01A01_position k < apm_a01A01_stage k := by
  show (Nat.unpair k).2 < (Nat.unpair k).1 + (Nat.unpair k).2 + 1
  omega

lemma apm_a01A01_index_lt_stage_sq (k : ℕ) (_hk : 1 ≤ k) :
    k < apm_a01A01_stage k ^ 2 := by
  have key : ∀ a b : ℕ,
      Nat.pair a b <
        ((Nat.unpair (Nat.pair a b)).1 + (Nat.unpair (Nat.pair a b)).2 + 1) ^ 2 := by
    intro a b
    rw [Nat.unpair_pair]
    unfold Nat.pair
    split_ifs <;> nlinarith [sq_nonneg a, sq_nonneg b]
  have h := key (Nat.unpair k).1 (Nat.unpair k).2
  rwa [Nat.pair_unpair] at h

lemma apm_a01A01_stage_tendsto_atTop :
    Tendsto apm_a01A01_stage atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro n₀
  refine ⟨max (n₀ ^ 2) 1, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_of_max_le_right hk
  have hsq : k < apm_a01A01_stage k ^ 2 :=
    apm_a01A01_index_lt_stage_sq k hk1
  have hk_ge : n₀ ^ 2 ≤ k := (le_max_left _ _).trans hk
  nlinarith [sq_nonneg (apm_a01A01_stage k), sq_nonneg n₀]

/-- The one-dimensional typewriter cell attached to a global index. -/
def apm_a01A01_typewriter1d (k : ℕ) : ℝ → ℝ := fun x =>
  Real.sqrt (apm_a01A01_stage k) *
    Set.indicator
      (Icc ((apm_a01A01_position k : ℝ) / apm_a01A01_stage k)
        (((apm_a01A01_position k + 1 : ℕ) : ℝ) / apm_a01A01_stage k))
      (fun _ => (1 : ℝ)) x

lemma apm_a01A01_typewriter1d_nonneg (k : ℕ) (x : ℝ) :
    0 ≤ apm_a01A01_typewriter1d k x := by
  unfold apm_a01A01_typewriter1d
  rw [Set.indicator_apply]
  split_ifs
  · exact mul_nonneg (Real.sqrt_nonneg _) zero_le_one
  · simp

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

  Closer hop 2 salvages and repairs the reusable combinatorial core from the
  ungated historical attempt: `apm_a01A01_stage`,
  `apm_a01A01_position`, `apm_a01A01_index_lt_stage_sq`, and
  `apm_a01A01_stage_tendsto_atTop` now compile above, as does the nonnegative
  1D cell `apm_a01A01_typewriter1d`. This closes the global-index cofinality
  component. Remaining work is the exact integral computation and pointwise
  cell-selection proof in 1D, followed by the finite-product cube analogue.
  -/
  sorry
