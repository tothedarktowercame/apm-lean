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

lemma apm_a01A01_typewriter1d_integrableOn (k : ℕ) :
    IntegrableOn (apm_a01A01_typewriter1d k) (Icc (0 : ℝ) 1) volume := by
  let C := Icc ((apm_a01A01_position k : ℝ) / apm_a01A01_stage k)
    (((apm_a01A01_position k + 1 : ℕ) : ℝ) / apm_a01A01_stage k)
  have hC : MeasurableSet C := measurableSet_Icc
  have hCfin : volume C ≠ ⊤ := measure_Icc_lt_top.ne
  have hi : Integrable (C.indicator
      (fun _ : ℝ => Real.sqrt (apm_a01A01_stage k))) volume :=
    (integrableOn_const hCfin).integrable_indicator hC
  apply hi.integrableOn.congr_fun _ measurableSet_Icc
  intro x _
  unfold apm_a01A01_typewriter1d
  dsimp [C]
  rw [Set.indicator_apply, Set.indicator_apply]
  split_ifs <;> ring

lemma apm_a01A01_integral_typewriter1d (k : ℕ) :
    ∫ x in Icc (0 : ℝ) 1, apm_a01A01_typewriter1d k x ∂volume =
      Real.sqrt (apm_a01A01_stage k) / apm_a01A01_stage k := by
  have hn : 0 < apm_a01A01_stage k := by
    unfold apm_a01A01_stage
    omega
  have hn' : (0 : ℝ) < apm_a01A01_stage k := by exact_mod_cast hn
  have hj := apm_a01A01_position_lt_stage k
  have hj0 : (0 : ℝ) ≤ (apm_a01A01_position k : ℝ) / apm_a01A01_stage k :=
    div_nonneg (by positivity) hn'.le
  have hj1 : (((apm_a01A01_position k + 1 : ℕ) : ℝ) /
      apm_a01A01_stage k) ≤ 1 :=
    (div_le_one hn').mpr (by exact_mod_cast hj)
  unfold apm_a01A01_typewriter1d
  rw [show (fun x : ℝ => Real.sqrt (apm_a01A01_stage k) *
      (Icc ((apm_a01A01_position k : ℝ) / apm_a01A01_stage k)
        (((apm_a01A01_position k + 1 : ℕ) : ℝ) /
          apm_a01A01_stage k)).indicator (fun _ => 1) x) =
      (Icc ((apm_a01A01_position k : ℝ) / apm_a01A01_stage k)
        (((apm_a01A01_position k + 1 : ℕ) : ℝ) /
          apm_a01A01_stage k)).indicator
        (fun _ => Real.sqrt (apm_a01A01_stage k)) by
      funext x
      rw [Set.indicator_apply, Set.indicator_apply]
      split_ifs <;> ring]
  rw [setIntegral_indicator measurableSet_Icc]
  have hsub : Icc (0 : ℝ) 1 ∩
      Icc ((apm_a01A01_position k : ℝ) / apm_a01A01_stage k)
        (((apm_a01A01_position k + 1 : ℕ) : ℝ) /
          apm_a01A01_stage k) =
      Icc ((apm_a01A01_position k : ℝ) / apm_a01A01_stage k)
        (((apm_a01A01_position k + 1 : ℕ) : ℝ) /
          apm_a01A01_stage k) := by
    apply Set.inter_eq_right.mpr
    rintro x ⟨hx1, hx2⟩
    exact ⟨hj0.trans hx1, hx2.trans hj1⟩
  rw [hsub, setIntegral_const, Measure.real, Real.volume_Icc]
  have hdiff : 0 ≤
      (((apm_a01A01_position k + 1 : ℕ) : ℝ) / apm_a01A01_stage k) -
        ((apm_a01A01_position k : ℝ) / apm_a01A01_stage k) := by
    rw [show ((apm_a01A01_position k + 1 : ℕ) : ℝ) =
      (apm_a01A01_position k : ℝ) + 1 by exact_mod_cast rfl,
      div_sub_div_same]
    exact div_nonneg (by norm_num) hn'.le
  rw [ENNReal.toReal_ofReal hdiff, smul_eq_mul]
  rw [show ((apm_a01A01_position k + 1 : ℕ) : ℝ) =
    (apm_a01A01_position k : ℝ) + 1 by exact_mod_cast rfl]
  field_simp
  ring

lemma apm_a01A01_integral_typewriter1d_tendsto :
    Tendsto (fun k => ∫ x in Icc (0 : ℝ) 1,
      apm_a01A01_typewriter1d k x ∂volume) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun k => Real.sqrt (apm_a01A01_stage k)) atTop atTop := by
    have hcast : Tendsto (fun k => (apm_a01A01_stage k : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto Nat.cast atTop atTop).comp
        apm_a01A01_stage_tendsto_atTop
    exact Real.tendsto_sqrt_atTop.comp hcast
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_inv_atTop_zero.comp hsqrt)
  · intro k
    change 0 ≤ ∫ x in Icc (0 : ℝ) 1, apm_a01A01_typewriter1d k x ∂volume
    rw [apm_a01A01_integral_typewriter1d]
    positivity
  · intro k
    change (∫ x in Icc (0 : ℝ) 1, apm_a01A01_typewriter1d k x ∂volume) ≤
      (Real.sqrt (apm_a01A01_stage k))⁻¹
    rw [apm_a01A01_integral_typewriter1d]
    have hkpos : (0 : ℝ) < apm_a01A01_stage k := by
      unfold apm_a01A01_stage
      positivity
    have hsq : Real.sqrt (apm_a01A01_stage k) *
        Real.sqrt (apm_a01A01_stage k) = apm_a01A01_stage k :=
      Real.mul_self_sqrt hkpos.le
    have hspos : 0 < Real.sqrt (apm_a01A01_stage k) := Real.sqrt_pos.mpr hkpos
    apply le_of_eq
    field_simp [hspos.ne', hkpos.ne']
    simpa [pow_two] using hsq

lemma apm_a01A01_add_le_pair (a b : ℕ) : a + b ≤ Nat.pair a b := by
  unfold Nat.pair
  split_ifs <;> nlinarith [sq_nonneg a, sq_nonneg b]

lemma apm_a01A01_typewriter1d_cofinal
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (M : ℝ) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ M ≤ apm_a01A01_typewriter1d k x := by
  obtain ⟨s, hs⟩ := exists_nat_ge (max ((max M 0) ^ 2) (N + 1 : ℝ))
  have hsNreal : (N + 1 : ℝ) ≤ s := (le_max_right _ _).trans hs
  have hsN : N + 1 ≤ s := by exact_mod_cast hsNreal
  have hspos : 0 < s := by omega
  have hsposR : (0 : ℝ) < s := by exact_mod_cast hspos
  let j : ℕ := if x = 1 then s - 1 else ⌊(s : ℝ) * x⌋₊
  have hjlt : j < s := by
    dsimp [j]
    split_ifs with hxeq
    · omega
    · apply (Nat.floor_lt (mul_nonneg hsposR.le hx.1)).mpr
      have hxlt : x < 1 := hx.2.lt_of_ne hxeq
      nlinarith
  let k := Nat.pair (s - 1 - j) j
  have hstage : apm_a01A01_stage k = s := by
    simp [k, apm_a01A01_stage]
    omega
  have hpos : apm_a01A01_position k = j := by
    simp [k, apm_a01A01_position]
  refine ⟨k, ?_, ?_⟩
  · have hsum : s - 1 - j + j = s - 1 := by omega
    have hpair := apm_a01A01_add_le_pair (s - 1 - j) j
    dsimp [k]
    omega
  · have hcell : x ∈ Icc ((j : ℝ) / s) (((j + 1 : ℕ) : ℝ) / s) := by
      constructor
      · rw [div_le_iff₀ hsposR]
        dsimp [j]
        split_ifs with hxeq
        · subst x
          norm_num
        · simpa [mul_comm] using Nat.floor_le (mul_nonneg hsposR.le hx.1)
      · rw [le_div_iff₀ hsposR]
        dsimp [j]
        split_ifs with hxeq
        · subst x
          norm_num [Nat.sub_add_cancel hspos]
        · simpa [Nat.cast_add_one, mul_comm] using
            (Nat.lt_floor_add_one ((s : ℝ) * x)).le
    have hM : M ≤ Real.sqrt s := by
      have hsq : (max M 0) ^ 2 ≤ (s : ℝ) := (le_max_left _ _).trans hs
      have hm0 : 0 ≤ max M 0 := le_max_right _ _
      exact le_trans (le_max_left _ _) ((Real.le_sqrt hm0 hsposR.le).2 hsq)
    unfold apm_a01A01_typewriter1d
    rw [hstage, hpos, Set.indicator_of_mem hcell, mul_one]
    exact hM

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
  constructor
  · refine ⟨apm_a01A01_typewriter1d, ?_, ?_, ?_,
      apm_a01A01_integral_typewriter1d_tendsto⟩
    · exact apm_a01A01_typewriter1d_integrableOn
    · intro k x _
      exact apm_a01A01_typewriter1d_nonneg k x
    · exact apm_a01A01_typewriter1d_cofinal
  ·
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

  This frame closes the entire one-dimensional conjunct.  In addition to the
  earlier exact integral calculation, `apm_a01A01_add_le_pair` controls the
  global index of a chosen diagonal cell,
  `apm_a01A01_typewriter1d_cofinal` selects that cell using `Nat.floor`, and
  `apm_a01A01_typewriter1d_integrableOn` supplies Bochner integrability.

  The sole remaining obligation is now the Euclidean conjunct.  The same
  construction needs, for each positive `d`, finite grids covering expanding
  cubes, a single natural-number scheduler whose grid scale tends to infinity
  along *every* global index, and a cell-volume estimate with height times
  volume tending to zero.  A direct diagonal scheduler has only `stage` cells,
  whereas a `d`-cube grid needs a `d`th-power number of cells; using it without
  a slower expanding radius is therefore invalid.  Searches of the repo index,
  construction modules, the orphan history, and Mathlib's Euclidean-volume
  equivalences found the measure pieces but no such scheduler.  The Zulip
  archive contained no `typewriter` construction.  No axiom, opaque
  declaration, or `native_decide` was introduced, and the frozen statement is
  unchanged.
  -/
    sorry
