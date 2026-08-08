import Mathlib

/-!
# APM a99J05 — small L¹ norm versus almost-everywhere convergence

## Statement repairs

None. Sequences are indexed by `ℕ`; this is the standard Lean reindexing of
the source's sequence beginning at one.

## Encoding questions

None. The functions, restricted Lebesgue measure on `[0,1]`, L¹ norms, and
almost-everywhere pointwise convergence are all represented directly.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

def apm_a99J05_measure : Measure ℝ := volume.restrict (Set.Icc 0 1)

def apm_a99J05_l1Norm (f : ℝ → ℝ) : ℝ :=
  ∫ x, ‖f x‖ ∂apm_a99J05_measure

lemma apm_a99J05_summable_l1Norm_of_geometric_bound
    (f : ℕ → ℝ → ℝ)
    (hbound : ∀ n, apm_a99J05_l1Norm (f n) ≤ (2 : ℝ)⁻¹ ^ n) :
    Summable (fun n ↦ apm_a99J05_l1Norm (f n)) := by
  apply Summable.of_nonneg_of_le
  · intro n
    exact integral_nonneg (fun x ↦ norm_nonneg (f n x))
  · exact hbound
  · exact summable_geometric_of_norm_lt_one (by norm_num : ‖(2 : ℝ)⁻¹‖ < 1)

/-- Tonelli extraction for the second half: summability of the `L¹` norms
forces pointwise convergence to zero almost everywhere. -/
lemma apm_a99J05_ae_tendsto_zero_of_summable_l1Norm
    (f : ℕ → ℝ → ℝ)
    (hint : ∀ n, Integrable (f n) apm_a99J05_measure)
    (hsum : Summable (fun n ↦ apm_a99J05_l1Norm (f n))) :
    ∀ᵐ x ∂apm_a99J05_measure,
      Tendsto (fun n ↦ f n x) atTop (𝓝 0) := by
  have hmeas : ∀ n, AEMeasurable (fun x ↦ ‖f n x‖ₑ) apm_a99J05_measure :=
    fun n ↦ (hint n).aestronglyMeasurable.enorm
  have htsum : (∑' n, ∫⁻ x, ‖f n x‖ₑ ∂apm_a99J05_measure) ≠ ∞ := by
    rw [show (∑' n, ∫⁻ x, ‖f n x‖ₑ ∂apm_a99J05_measure) =
        ∑' n, ENNReal.ofReal (apm_a99J05_l1Norm (f n)) by
      apply tsum_congr
      intro n
      unfold apm_a99J05_l1Norm
      exact (ofReal_integral_norm_eq_lintegral_enorm (hint n)).symm]
    exact hsum.tsum_ofReal_ne_top
  rw [← lintegral_tsum hmeas] at htsum
  have hae : ∀ᵐ x ∂apm_a99J05_measure, (∑' n, ‖f n x‖ₑ) ≠ ∞ :=
    (ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) htsum).mono
      (fun _ hx ↦ hx.ne)
  filter_upwards [hae] with x hx
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have henorm := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx
  have hreal := (ENNReal.tendsto_toReal_zero_iff
    (fun n ↦ enorm_ne_top)).2 henorm
  simpa using hreal


/-- Cofinal unboundedness, used to rule out pointwise convergence. -/
def apm_a99J05_LimsupInfinite (u : ℕ → ℝ) : Prop :=
  ∀ M : ℝ, ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ M ≤ u k


/-- Stage number for the diagonal enumeration of pairs of naturals. -/
def apm_a99J05_stage (k : ℕ) : ℕ :=
  (Nat.unpair k).1 + (Nat.unpair k).2 + 1

/-- Position inside a diagonally enumerated stage. -/
def apm_a99J05_position (k : ℕ) : ℕ :=
  (Nat.unpair k).2

lemma apm_a99J05_position_lt_stage (k : ℕ) :
    apm_a99J05_position k < apm_a99J05_stage k := by
  show (Nat.unpair k).2 < (Nat.unpair k).1 + (Nat.unpair k).2 + 1
  omega

lemma apm_a99J05_index_lt_stage_sq (k : ℕ) (_hk : 1 ≤ k) :
    k < apm_a99J05_stage k ^ 2 := by
  have key : ∀ a b : ℕ,
      Nat.pair a b <
        ((Nat.unpair (Nat.pair a b)).1 + (Nat.unpair (Nat.pair a b)).2 + 1) ^ 2 := by
    intro a b
    rw [Nat.unpair_pair]
    unfold Nat.pair
    split_ifs <;> nlinarith [sq_nonneg a, sq_nonneg b]
  have h := key (Nat.unpair k).1 (Nat.unpair k).2
  rwa [Nat.pair_unpair] at h

lemma apm_a99J05_stage_tendsto_atTop :
    Tendsto apm_a99J05_stage atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro n₀
  refine ⟨max (n₀ ^ 2) 1, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_of_max_le_right hk
  have hsq : k < apm_a99J05_stage k ^ 2 :=
    apm_a99J05_index_lt_stage_sq k hk1
  have hk_ge : n₀ ^ 2 ≤ k := (le_max_left _ _).trans hk
  nlinarith [sq_nonneg (apm_a99J05_stage k), sq_nonneg n₀]

/-- The one-dimensional typewriter cell attached to a global index. -/
def apm_a99J05_typewriter1d (k : ℕ) : ℝ → ℝ := fun x =>
  Real.sqrt (apm_a99J05_stage k) *
    Set.indicator
      (Icc ((apm_a99J05_position k : ℝ) / apm_a99J05_stage k)
        (((apm_a99J05_position k + 1 : ℕ) : ℝ) / apm_a99J05_stage k))
      (fun _ => (1 : ℝ)) x

lemma apm_a99J05_typewriter1d_nonneg (k : ℕ) (x : ℝ) :
    0 ≤ apm_a99J05_typewriter1d k x := by
  unfold apm_a99J05_typewriter1d
  rw [Set.indicator_apply]
  split_ifs
  · exact mul_nonneg (Real.sqrt_nonneg _) zero_le_one
  · simp

lemma apm_a99J05_integral_typewriter1d (k : ℕ) :
    ∫ x in Icc (0 : ℝ) 1, apm_a99J05_typewriter1d k x ∂volume =
      Real.sqrt (apm_a99J05_stage k) / apm_a99J05_stage k := by
  have hn : 0 < apm_a99J05_stage k := by
    unfold apm_a99J05_stage
    omega
  have hn' : (0 : ℝ) < apm_a99J05_stage k := by exact_mod_cast hn
  have hj := apm_a99J05_position_lt_stage k
  have hj0 : (0 : ℝ) ≤ (apm_a99J05_position k : ℝ) / apm_a99J05_stage k :=
    div_nonneg (by positivity) hn'.le
  have hj1 : (((apm_a99J05_position k + 1 : ℕ) : ℝ) /
      apm_a99J05_stage k) ≤ 1 :=
    (div_le_one hn').mpr (by exact_mod_cast hj)
  unfold apm_a99J05_typewriter1d
  rw [show (fun x : ℝ => Real.sqrt (apm_a99J05_stage k) *
      (Icc ((apm_a99J05_position k : ℝ) / apm_a99J05_stage k)
        (((apm_a99J05_position k + 1 : ℕ) : ℝ) /
          apm_a99J05_stage k)).indicator (fun _ => 1) x) =
      (Icc ((apm_a99J05_position k : ℝ) / apm_a99J05_stage k)
        (((apm_a99J05_position k + 1 : ℕ) : ℝ) /
          apm_a99J05_stage k)).indicator
        (fun _ => Real.sqrt (apm_a99J05_stage k)) by
      funext x
      rw [Set.indicator_apply, Set.indicator_apply]
      split_ifs <;> ring]
  rw [setIntegral_indicator measurableSet_Icc]
  have hsub : Icc (0 : ℝ) 1 ∩
      Icc ((apm_a99J05_position k : ℝ) / apm_a99J05_stage k)
        (((apm_a99J05_position k + 1 : ℕ) : ℝ) /
          apm_a99J05_stage k) =
      Icc ((apm_a99J05_position k : ℝ) / apm_a99J05_stage k)
        (((apm_a99J05_position k + 1 : ℕ) : ℝ) /
          apm_a99J05_stage k) := by
    apply Set.inter_eq_right.mpr
    rintro x ⟨hx1, hx2⟩
    exact ⟨hj0.trans hx1, hx2.trans hj1⟩
  rw [hsub, setIntegral_const, Measure.real, Real.volume_Icc]
  have hdiff : 0 ≤
      (((apm_a99J05_position k + 1 : ℕ) : ℝ) / apm_a99J05_stage k) -
        ((apm_a99J05_position k : ℝ) / apm_a99J05_stage k) := by
    rw [show ((apm_a99J05_position k + 1 : ℕ) : ℝ) =
      (apm_a99J05_position k : ℝ) + 1 by exact_mod_cast rfl,
      div_sub_div_same]
    exact div_nonneg (by norm_num) hn'.le
  rw [ENNReal.toReal_ofReal hdiff, smul_eq_mul]
  rw [show ((apm_a99J05_position k + 1 : ℕ) : ℝ) =
    (apm_a99J05_position k : ℝ) + 1 by exact_mod_cast rfl]
  field_simp
  ring

lemma apm_a99J05_integral_typewriter1d_tendsto :
    Tendsto (fun k => ∫ x in Icc (0 : ℝ) 1,
      apm_a99J05_typewriter1d k x ∂volume) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun k => Real.sqrt (apm_a99J05_stage k)) atTop atTop := by
    have hcast : Tendsto (fun k => (apm_a99J05_stage k : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto Nat.cast atTop atTop).comp
        apm_a99J05_stage_tendsto_atTop
    exact Real.tendsto_sqrt_atTop.comp hcast
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_inv_atTop_zero.comp hsqrt)
  · intro k
    change 0 ≤ ∫ x in Icc (0 : ℝ) 1, apm_a99J05_typewriter1d k x ∂volume
    rw [apm_a99J05_integral_typewriter1d]
    positivity
  · intro k
    change (∫ x in Icc (0 : ℝ) 1, apm_a99J05_typewriter1d k x ∂volume) ≤
      (Real.sqrt (apm_a99J05_stage k))⁻¹
    rw [apm_a99J05_integral_typewriter1d]
    have hkpos : (0 : ℝ) < apm_a99J05_stage k := by
      unfold apm_a99J05_stage
      positivity
    have hsq : Real.sqrt (apm_a99J05_stage k) *
        Real.sqrt (apm_a99J05_stage k) = apm_a99J05_stage k :=
      Real.mul_self_sqrt hkpos.le
    have hspos : 0 < Real.sqrt (apm_a99J05_stage k) := Real.sqrt_pos.mpr hkpos
    apply le_of_eq
    field_simp [hspos.ne', hkpos.ne']
    simpa [pow_two] using hsq

/-- Integrability of each typewriter function. -/
lemma apm_a99J05_typewriter1d_integrable (k : ℕ) :
    IntegrableOn (apm_a99J05_typewriter1d k) (Icc (0 : ℝ) 1) volume := by
  -- apm_a99J05_typewriter1d k is nonneg, measurable, and bounded by √n on [0,1] which has measure 1
  have hsm : AEStronglyMeasurable (apm_a99J05_typewriter1d k) (volume.restrict (Icc (0 : ℝ) 1)) := by
    unfold apm_a99J05_typewriter1d apm_a99J05_stage apm_a99J05_position
    exact (StronglyMeasurable.const_mul
      (StronglyMeasurable.indicator stronglyMeasurable_const measurableSet_Icc) _).aestronglyMeasurable
  have hc : Integrable (fun _ : ℝ => Real.sqrt (apm_a99J05_stage k))
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    integrableOn_const (by simp [Real.volume_Icc])
  apply hc.mono' hsm
  filter_upwards [] with x
  unfold apm_a99J05_typewriter1d
  rw [Set.indicator_apply]
  split_ifs <;> simp [abs_of_nonneg (Real.sqrt_nonneg _)]

/- CLOSER HOP 3 NOTE.

The stage, position, cofinality, exact cell integral, vanishing-integral, and
restricted-measure integrability lemmas above are adapted from the compiled
one-dimensional core in sibling `a01A01`. An older orphaned branch also
contained a proposed floor-based point-selection proof. Porting that proof
exposed nontrivial snapshot gaps: its nonlinear lower bound for `Nat.pair`
was not discharged by the current arithmetic tactics, and its uses of the
old minimum/floor and ordered-field division APIs no longer elaborate.
Thus the remaining bridge is precisely a current-snapshot proof that every
`x ∈ Icc 0 1` belongs to arbitrarily late diagonal cells. The resulting
cofinal unbounded subsequence suffices to refute convergence. No axiom or
opaque declaration is introduced.
-/
theorem apm_a99j05 :
    (∃ f : ℕ → ℝ → ℝ,
      (∀ n, Integrable (f n) apm_a99J05_measure) ∧
      Tendsto (fun n ↦ apm_a99J05_l1Norm (f n)) atTop (𝓝 0) ∧
      ¬(∀ᵐ x ∂apm_a99J05_measure,
        ∃ a : ℝ, Tendsto (fun n ↦ f n x) atTop (𝓝 a))) ∧
    (∀ f : ℕ → ℝ → ℝ,
      (∀ n, Integrable (f n) apm_a99J05_measure) →
      (∀ n, apm_a99J05_l1Norm (f n) ≤ (2 : ℝ)⁻¹ ^ n) →
      ∀ᵐ x ∂apm_a99J05_measure,
        Tendsto (fun n ↦ f n x) atTop (𝓝 0)) := by
  constructor
  · /- CLOSER HOP 2 BOUNDARY.

    This hop closes the complete second conjunct.  The new helper
    `apm_a99J05_ae_tendsto_zero_of_summable_l1Norm` extracts the Tonelli
    argument from Mathlib's `integral_tsum`: it converts the summable real
    integrals to a finite ENNReal `tsum`, uses `lintegral_tsum` and
    `ae_lt_top'`, and then applies
    `ENNReal.tendsto_atTop_zero_of_tsum_ne_top`.  The geometric-bound helper
    supplies its summability premise below.

    The sole remaining bridge is the first conjunct's typewriter sequence.
    Renewed `LEMMA-INDEX.md` inspection found substantial compiled helpers in
    solved/partial sibling `a01A01`: its stage, position, cell integral, and
    vanishing-integral lemmas are precisely reusable mathematical ingredients.
    However, that module's main theorem remains partial and it still lacks the
    cofinal pointwise cell-selection lemma needed to prove that the sequence
    has no pointwise limit.  `ConstructionTargets`, the broader solved corpus,
    Borel--Cantelli sources, and git history contain no closed substitute.
    Thus importing or copying those helpers alone cannot honestly close this
    existential.  The frozen statement is unchanged.
    -/
    sorry
  · intro f hint hbound
    exact apm_a99J05_ae_tendsto_zero_of_summable_l1Norm f hint
      (apm_a99J05_summable_l1Norm_of_geometric_bound f hbound)

#print axioms apm_a99j05
