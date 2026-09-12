import Mathlib
import Mathlib.Topology.Bases

open MeasureTheory
open scoped BoundedContinuousFunction
noncomputable section

/-!
# APM m93J07 — a Banach-space and `Lᵖ` example zoo

## Statement repairs

None.  The two impossible requests are represented as nonexistence claims.

## Encoding note

Banach spaces are bundled below so separability and surjectivity of the
canonical map into the continuous bidual can be stated without assuming the
very properties whose examples the problem asks us to distinguish.
-/

structure apm_m93j07_Banach where
  carrier : Type
  normedAddCommGroup : NormedAddCommGroup carrier
  normedSpace : NormedSpace ℝ carrier
  completeSpace : CompleteSpace carrier

attribute [instance] apm_m93j07_Banach.normedAddCommGroup
  apm_m93j07_Banach.normedSpace apm_m93j07_Banach.completeSpace

def apm_m93j07_Reflexive (X : apm_m93j07_Banach) : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X.carrier)

def apm_m93j07_Separable (X : apm_m93j07_Banach) : Prop :=
  Nonempty (TopologicalSpace.SeparableSpace X.carrier)

def apm_m93j07_DualSeparable (X : apm_m93j07_Banach) : Prop :=
  Nonempty (TopologicalSpace.SeparableSpace (StrongDual ℝ X.carrier))

/-- The local power used for the `L² \ L⁴` examples has an integrable square. -/
lemma apm_m93J07_local_power_two_integrable :
    IntegrableOn (fun x : ℝ => x ^ (-2 / 3 : ℝ)) (Set.Ioo 0 1) volume := by
  exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by norm_num)

/-- The fourth power of the same local singularity is not integrable. -/
lemma apm_m93J07_local_power_four_not_integrable :
    ¬ IntegrableOn (fun x : ℝ => x ^ (-4 / 3 : ℝ)) (Set.Ioo 0 1) volume := by
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
  norm_num

/-- At infinity the fourth power is integrable. -/
lemma apm_m93J07_tail_power_four_integrable :
    IntegrableOn (fun x : ℝ => x ^ (-4 / 3 : ℝ)) (Set.Ioi 1) volume := by
  exact (integrableOn_Ioi_rpow_iff zero_lt_one).2 (by norm_num)

/-- At infinity the square is not integrable. -/
lemma apm_m93J07_tail_power_two_not_integrable :
    ¬ IntegrableOn (fun x : ℝ => x ^ (-2 / 3 : ℝ)) (Set.Ioi 1) volume := by
  rw [integrableOn_Ioi_rpow_iff zero_lt_one]
  norm_num

noncomputable def apm_m93J07_localWitness : ℝ → ℝ :=
  Set.Ioo (0 : ℝ) 1 |>.indicator (fun x ↦ x ^ (-1 / 3 : ℝ))

lemma apm_m93J07_localWitness_aestronglyMeasurable :
    AEStronglyMeasurable apm_m93J07_localWitness volume := by
  rw [apm_m93J07_localWitness, aestronglyMeasurable_indicator_iff measurableSet_Ioo]
  exact (continuousOn_id.rpow_const (fun _ hx ↦ Or.inl hx.1.ne')).aestronglyMeasurable
    measurableSet_Ioo

lemma apm_m93J07_localWitness_memLp_two :
    MemLp apm_m93J07_localWitness 2 volume := by
  rw [memLp_two_iff_integrable_sq apm_m93J07_localWitness_aestronglyMeasurable]
  have hi := apm_m93J07_local_power_two_integrable.integrable_indicator measurableSet_Ioo
  convert hi using 1
  funext x
  by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
  · simp only [apm_m93J07_localWitness, Set.indicator_of_mem hx]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hx.1.le]
    norm_num
  · simp [apm_m93J07_localWitness, Set.indicator, hx]

lemma apm_m93J07_localWitness_not_memLp_four :
    ¬ MemLp apm_m93J07_localWitness 4 volume := by
  intro hf
  apply apm_m93J07_local_power_four_not_integrable
  have hi := hf.integrable_norm_rpow (by norm_num) (by norm_num)
  apply (integrable_indicator_iff measurableSet_Ioo).1
  convert hi using 1
  funext x
  by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
  · simp only [apm_m93J07_localWitness, Set.indicator_of_mem hx,
      Real.norm_rpow_of_nonneg hx.1.le, Real.norm_eq_abs, abs_of_pos hx.1]
    norm_num
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hx.1.le]
    norm_num
  · simp [apm_m93J07_localWitness, Set.indicator, hx]

noncomputable def apm_m93J07_tailWitness : ℝ → ℝ :=
  Set.Ioi (1 : ℝ) |>.indicator (fun x ↦ x ^ (-1 / 3 : ℝ))

lemma apm_m93J07_tailWitness_aestronglyMeasurable :
    AEStronglyMeasurable apm_m93J07_tailWitness volume := by
  rw [apm_m93J07_tailWitness, aestronglyMeasurable_indicator_iff measurableSet_Ioi]
  exact (continuousOn_id.rpow_const (fun _ hx ↦ Or.inl (zero_lt_one.trans hx).ne')).aestronglyMeasurable
    measurableSet_Ioi

lemma apm_m93J07_tailWitness_memLp_four :
    MemLp apm_m93J07_tailWitness 4 volume := by
  apply (integrable_norm_rpow_iff apm_m93J07_tailWitness_aestronglyMeasurable
    (by norm_num) (by norm_num)).1
  norm_num
  have hi := apm_m93J07_tail_power_four_integrable.integrable_indicator measurableSet_Ioi
  convert hi using 1
  funext x
  by_cases hx : x ∈ Set.Ioi (1 : ℝ)
  · have hxpos : 0 < x := zero_lt_one.trans hx
    simp only [apm_m93J07_tailWitness, Set.indicator_of_mem hx]
    rw [abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hxpos.le]
    norm_num
  · simp [apm_m93J07_tailWitness, Set.indicator, hx]

lemma apm_m93J07_tailWitness_not_memLp_two :
    ¬ MemLp apm_m93J07_tailWitness 2 volume := by
  intro hf
  apply apm_m93J07_tail_power_two_not_integrable
  rw [memLp_two_iff_integrable_sq apm_m93J07_tailWitness_aestronglyMeasurable] at hf
  apply (integrable_indicator_iff measurableSet_Ioi).1
  convert hf using 1
  funext x
  by_cases hx : x ∈ Set.Ioi (1 : ℝ)
  · have hxpos : 0 < x := zero_lt_one.trans hx
    simp only [apm_m93J07_tailWitness, Set.indicator_of_mem hx]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hxpos.le]
    norm_num
  · simp [apm_m93J07_tailWitness, Set.indicator, hx]

lemma apm_m93J07_localWitness_memLp_two_restrict :
    MemLp apm_m93J07_localWitness 2 (volume.restrict (Set.Icc 0 1)) :=
  apm_m93J07_localWitness_memLp_two.restrict _

lemma apm_m93J07_localWitness_not_memLp_four_restrict :
    ¬ MemLp apm_m93J07_localWitness 4 (volume.restrict (Set.Icc 0 1)) := by
  intro hf
  apply apm_m93J07_localWitness_not_memLp_four
  have hi : MemLp ((Set.Icc (0 : ℝ) 1).indicator apm_m93J07_localWitness) 4 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc).2 hf
  rw [show (Set.Icc (0 : ℝ) 1).indicator apm_m93J07_localWitness =
      apm_m93J07_localWitness by
    funext x
    by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
    · simp [apm_m93J07_localWitness, hx, hx.1.le, hx.2.le]
    · simp [apm_m93J07_localWitness, hx]] at hi
  exact hi

def apm_m93J07_discreteReal := ℝ

instance : TopologicalSpace apm_m93J07_discreteReal := ⊥
instance : DiscreteTopology apm_m93J07_discreteReal := ⟨rfl⟩
noncomputable local instance : DecidableEq apm_m93J07_discreteReal := Classical.decEq _

noncomputable def apm_m93J07_spike (i : apm_m93J07_discreteReal) :
    apm_m93J07_discreteReal →ᵇ ℝ :=
  BoundedContinuousFunction.indicator {i} (isClopen_discrete _)

lemma apm_m93J07_spike_dist (i j : apm_m93J07_discreteReal) (h : i ≠ j) :
    1 ≤ dist (apm_m93J07_spike i) (apm_m93J07_spike j) := by
  rw [dist_eq_norm]
  calc
    1 = ‖(apm_m93J07_spike i - apm_m93J07_spike j) i‖ := by
      simp [apm_m93J07_spike, h]
    _ ≤ ‖apm_m93J07_spike i - apm_m93J07_spike j‖ :=
      BoundedContinuousFunction.norm_coe_le_norm _ _

lemma apm_m93J07_boundedFunctions_not_separable :
    ¬ Nonempty (TopologicalSpace.SeparableSpace
      (apm_m93J07_discreteReal →ᵇ ℝ)) := by
  rintro ⟨hsep⟩
  letI := hsep
  have hc : Countable apm_m93J07_discreteReal :=
    Pairwise.countable_of_isOpen_disjoint
      (s := fun i ↦ Metric.ball (apm_m93J07_spike i) (1 / 3 : ℝ))
      (fun i j hij ↦ Metric.ball_disjoint_ball (by
        norm_num
        exact (by norm_num : (2 / 3 : ℝ) ≤ 1).trans
          (apm_m93J07_spike_dist i j hij)))
      (fun _ ↦ Metric.isOpen_ball)
      (fun i ↦ ⟨apm_m93J07_spike i, Metric.mem_ball_self (by norm_num)⟩)
  exact Cardinal.not_countable_real (Set.countable_univ_iff.mpr hc)

noncomputable def apm_m93J07_nonseparableBanach : apm_m93j07_Banach where
  carrier := apm_m93J07_discreteReal →ᵇ ℝ
  normedAddCommGroup := inferInstance
  normedSpace := inferInstance
  completeSpace := inferInstance

lemma apm_m93J07_hilbert_reflexive (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E) := by
  intro g
  let h : StrongDual ℝ E :=
    { toFun := fun x ↦ g (InnerProductSpace.toDual ℝ E x)
      map_add' := by simp
      map_smul' := by simp
      cont := g.continuous.comp (InnerProductSpace.toDual ℝ E).continuous }
  obtain ⟨x, hx⟩ := (InnerProductSpace.toDual ℝ E).surjective h
  refine ⟨x, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  obtain ⟨y, rfl⟩ := (InnerProductSpace.toDual ℝ E).surjective f
  change InnerProductSpace.toDual ℝ E y x = g (InnerProductSpace.toDual ℝ E y)
  have heval := DFunLike.congr_fun hx y
  change InnerProductSpace.toDual ℝ E x y = g (InnerProductSpace.toDual ℝ E y) at heval
  rw [← heval, InnerProductSpace.toDual_apply_apply,
    InnerProductSpace.toDual_apply_apply]
  exact real_inner_comm _ _

abbrev apm_m93J07_nonseparableHilbert :=
  lp (fun _ : apm_m93J07_discreteReal ↦ ℝ) 2

lemma apm_m93J07_l2_single_dist (i j : apm_m93J07_discreteReal) (h : i ≠ j) :
    1 ≤ dist (lp.single 2 i (1 : ℝ) : apm_m93J07_nonseparableHilbert)
      (lp.single 2 j (1 : ℝ)) := by
  classical
  rw [dist_eq_norm]
  let f : lp (fun _ : apm_m93J07_discreteReal ↦ ℝ) 2 :=
    lp.single 2 i 1 - lp.single 2 j 1
  change 1 ≤ ‖f‖
  calc
    1 = ‖f i‖ := by
      change 1 = |(lp.single 2 i (1 : ℝ) : apm_m93J07_nonseparableHilbert) i -
        (lp.single 2 j (1 : ℝ) : apm_m93J07_nonseparableHilbert) i|
      rw [lp.single_apply_self, lp.single_apply_ne 2 j 1 h]
      norm_num
    _ ≤ ‖f‖ :=
      lp.norm_apply_le_norm (E := fun _ : apm_m93J07_discreteReal ↦ ℝ)
        (p := 2) (by norm_num) f i

lemma apm_m93J07_l2_not_separable :
    ¬ Nonempty (TopologicalSpace.SeparableSpace apm_m93J07_nonseparableHilbert) := by
  classical
  rintro ⟨hsep⟩
  letI := hsep
  have hc : Countable apm_m93J07_discreteReal :=
    Pairwise.countable_of_isOpen_disjoint
      (s := fun i ↦ Metric.ball
        (lp.single 2 i (1 : ℝ) : apm_m93J07_nonseparableHilbert) (1 / 3 : ℝ))
      (fun i j hij ↦ Metric.ball_disjoint_ball (by
        norm_num
        exact (by norm_num : (2 / 3 : ℝ) ≤ 1).trans
          (apm_m93J07_l2_single_dist i j hij)))
      (fun _ ↦ Metric.isOpen_ball)
      (fun i ↦ ⟨lp.single 2 i (1 : ℝ), Metric.mem_ball_self (by norm_num)⟩)
  exact Cardinal.not_countable_real (Set.countable_univ_iff.mpr hc)

noncomputable def apm_m93J07_nonseparableReflexiveBanach : apm_m93j07_Banach where
  carrier := apm_m93J07_nonseparableHilbert
  normedAddCommGroup := inferInstance
  normedSpace := inferInstance
  completeSpace := inferInstance

abbrev apm_m93J07_l1 := lp (fun _ : ℕ ↦ ℝ) 1

lemma apm_m93J07_l1_separable :
    Nonempty (TopologicalSpace.SeparableSpace apm_m93J07_l1) := by
  let s : Set apm_m93J07_l1 :=
    ⋃ i : ℕ, Set.range (lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ ℝ) 1 i)
  have hs : TopologicalSpace.IsSeparable s := by
    apply TopologicalSpace.IsSeparable.iUnion
    intro i
    exact TopologicalSpace.isSeparable_range
      (lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ ℝ) 1 i).continuous
  have hd : (Submodule.span ℝ s).topologicalClosure = ⊤ := by
    apply eq_top_iff.mpr
    intro f _
    apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num) f)
    filter_upwards [] with t
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.subset_span
    apply Set.mem_iUnion_of_mem i
    exact ⟨f i, rfl⟩
  have hu : TopologicalSpace.IsSeparable (Set.univ : Set apm_m93J07_l1) := by
    have hdset : closure (Submodule.span ℝ s : Set apm_m93J07_l1) = Set.univ := by
      simpa using congrArg (fun U : Submodule ℝ apm_m93J07_l1 ↦
        (U : Set apm_m93J07_l1)) hd
    rw [← hdset]
    exact hs.span.closure
  exact ⟨TopologicalSpace.isSeparable_univ_iff.mp hu⟩

noncomputable def apm_m93J07_l1Banach : apm_m93j07_Banach where
  carrier := apm_m93J07_l1
  normedAddCommGroup := inferInstance
  normedSpace := inferInstance
  completeSpace := inferInstance

lemma apm_m93J07_l1_summable_norm (f : apm_m93J07_l1) : Summable (fun n ↦ ‖f n‖) := by
  simpa using (lp.memℓp f).summable (by norm_num : 0 < ENNReal.toReal (1 : ENNReal))

lemma apm_m93J07_subset_summable (A : Set ℕ) (f : apm_m93J07_l1) :
    Summable (A.indicator fun n ↦ f n) := by
  apply Summable.of_norm
  exact ((apm_m93J07_l1_summable_norm f).of_norm.indicator A).norm

noncomputable def apm_m93J07_subsetFunctional (A : Set ℕ) :
    StrongDual ℝ apm_m93J07_l1 := by
  classical
  exact LinearMap.mkContinuous
    { toFun := fun f ↦ ∑' n, A.indicator (fun n ↦ f n) n
      map_add' := fun f g ↦ by
        rw [← (apm_m93J07_subset_summable A f).tsum_add
          (apm_m93J07_subset_summable A g)]
        congr 1
        funext n
        by_cases hn : n ∈ A
        · simp only [Set.indicator_of_mem hn]
          rfl
        · simp [Set.indicator, hn]
      map_smul' := fun c f ↦ by
        change (∑' n, A.indicator (fun n ↦ (c • f) n) n) =
          c * ∑' n, A.indicator (fun n ↦ f n) n
        rw [← tsum_mul_left]
        congr 1
        funext n
        by_cases hn : n ∈ A
        · simp only [Set.indicator_of_mem hn]
          rfl
        · simp [Set.indicator, hn] }
    1 (fun f ↦ by
      rw [one_mul]
      calc
        ‖∑' n, A.indicator (fun n ↦ f n) n‖ ≤
            ∑' n, ‖A.indicator (fun n ↦ f n) n‖ :=
          norm_tsum_le_tsum_norm (apm_m93J07_subset_summable A f).norm
        _ ≤ ∑' n, ‖f n‖ := by
          apply (apm_m93J07_subset_summable A f).norm.tsum_le_tsum
          · intro n
            by_cases hn : n ∈ A <;> simp [Set.indicator, hn]
          · exact apm_m93J07_l1_summable_norm f
        _ = ‖f‖ := by
          have h := lp.norm_rpow_eq_tsum (p := (1 : ENNReal))
            (E := fun _ : ℕ ↦ ℝ)
            (by norm_num : 0 < ENNReal.toReal (1 : ENNReal)) f
          norm_num at h
          exact h.symm)

lemma apm_m93J07_subsetFunctional_single (A : Set ℕ) (i : ℕ) :
    apm_m93J07_subsetFunctional A (lp.single 1 i (1 : ℝ)) =
      A.indicator (fun _ ↦ (1 : ℝ)) i := by
  classical
  change (∑' n, A.indicator (fun n ↦
    (lp.single 1 i (1 : ℝ) : apm_m93J07_l1) n) n) = A.indicator (fun _ ↦ (1 : ℝ)) i
  rw [tsum_eq_single i]
  · simp [Set.indicator, lp.single_apply]
  · intro n hni
    simp [Set.indicator, lp.single_apply, hni]

lemma apm_m93J07_coordinateFunctional_apply (f : apm_m93J07_l1) (i : ℕ) :
    apm_m93J07_subsetFunctional {i} f = f i := by
  classical
  change (∑' n, ({i} : Set ℕ).indicator (fun n ↦ f n) n) = f i
  rw [tsum_eq_single i]
  · simp
  · intro n hni
    simp [Set.indicator, hni]

lemma apm_m93J07_subsetFunctional_dist (A B : Set ℕ) (h : A ≠ B) :
    1 ≤ dist (apm_m93J07_subsetFunctional A) (apm_m93J07_subsetFunctional B) := by
  classical
  have h' : ¬ ∀ i, (i ∈ A ↔ i ∈ B) := by simpa [Set.ext_iff] using h
  push_neg at h'
  obtain ⟨i, hi⟩ := h'
  rw [dist_eq_norm]
  have hb := ContinuousLinearMap.le_opNorm
    (apm_m93J07_subsetFunctional A - apm_m93J07_subsetFunctional B)
    (lp.single 1 i (1 : ℝ) : apm_m93J07_l1)
  rw [lp.norm_single (by norm_num)] at hb
  norm_num at hb
  have hv : |apm_m93J07_subsetFunctional A (lp.single 1 i (1 : ℝ) : apm_m93J07_l1) -
      apm_m93J07_subsetFunctional B (lp.single 1 i (1 : ℝ) : apm_m93J07_l1)| = 1 := by
    rw [apm_m93J07_subsetFunctional_single, apm_m93J07_subsetFunctional_single]
    by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;>
      simp [Set.indicator, hA, hB] at hi ⊢
  rw [hv] at hb
  exact hb

lemma apm_m93J07_l1_dual_not_separable :
    ¬ Nonempty (TopologicalSpace.SeparableSpace (StrongDual ℝ apm_m93J07_l1)) := by
  rintro ⟨hsep⟩
  letI := hsep
  have hc : Countable (Set ℕ) := Pairwise.countable_of_isOpen_disjoint
    (s := fun A ↦ Metric.ball (apm_m93J07_subsetFunctional A) (1 / 3 : ℝ))
    (fun A B hAB ↦ Metric.ball_disjoint_ball (by
      norm_num
      exact (by norm_num : (2 / 3 : ℝ) ≤ 1).trans
        (apm_m93J07_subsetFunctional_dist A B hAB)))
    (fun _ ↦ Metric.isOpen_ball)
    (fun A ↦ ⟨apm_m93J07_subsetFunctional A, Metric.mem_ball_self (by norm_num)⟩)
  have hcu : (Set.univ : Set (Set ℕ)).Countable := Set.countable_univ_iff.mpr hc
  obtain ⟨e, he⟩ := hcu.exists_surjective ⟨∅, Set.mem_univ _⟩
  let D : Set ℕ := {n | n ∉ (e n : Set ℕ)}
  obtain ⟨k, hk⟩ := he ⟨D, Set.mem_univ D⟩
  have hk' : (e k : Set ℕ) = D := congrArg Subtype.val hk
  have hdiag : k ∈ D ↔ k ∉ (e k : Set ℕ) := by rfl
  rw [hk'] at hdiag
  tauto
def apm_m93J07_coordinateFunctionals : Set (StrongDual ℝ apm_m93J07_l1) :=
  Set.range (fun i : ℕ ↦ apm_m93J07_subsetFunctional {i})

lemma apm_m93J07_span_eventually_zero (z : StrongDual ℝ apm_m93J07_l1)
    (hz : z ∈ Submodule.span ℝ apm_m93J07_coordinateFunctionals) :
    ∃ F : Finset ℕ, ∀ i ∉ F, z (lp.single 1 i (1 : ℝ)) = 0 := by
  refine Submodule.span_induction
    (p := fun z _ ↦ ∃ F : Finset ℕ, ∀ i ∉ F, z (lp.single 1 i (1 : ℝ)) = 0)
    ?_ ?_ ?_ ?_ hz
  · rintro z ⟨j, rfl⟩
    refine ⟨{j}, ?_⟩
    intro i hi
    have hij : i ≠ j := by simpa using hi
    rw [apm_m93J07_subsetFunctional_single]
    simp [Set.indicator, hij]
  · exact ⟨∅, by simp⟩
  · rintro x y hxmem hymem ⟨Fx, hx⟩ ⟨Fy, hy⟩
    refine ⟨Fx ∪ Fy, ?_⟩
    intro i hi
    simp only [Finset.mem_union, not_or] at hi
    rw [ContinuousLinearMap.add_apply, hx i hi.1, hy i hi.2, add_zero]
  · rintro c x hxmem ⟨F, hx⟩
    refine ⟨F, ?_⟩
    intro i hi
    rw [ContinuousLinearMap.smul_apply, hx i hi, smul_zero]

lemma apm_m93J07_allOne_span_dist (z : StrongDual ℝ apm_m93J07_l1)
    (hz : z ∈ Submodule.span ℝ apm_m93J07_coordinateFunctionals) :
    1 ≤ dist (apm_m93J07_subsetFunctional Set.univ) z := by
  obtain ⟨F, hF⟩ := apm_m93J07_span_eventually_zero z hz
  obtain ⟨i, hi⟩ : ∃ i : ℕ, i ∉ F := by
    by_cases hEmpty : F = ∅
    · exact ⟨0, by simp [hEmpty]⟩
    · let i := F.max' (Finset.nonempty_iff_ne_empty.mpr hEmpty) + 1
      refine ⟨i, ?_⟩
      intro him
      have := F.le_max' i him
      omega
  rw [dist_eq_norm]
  have hb := ContinuousLinearMap.le_opNorm
    (apm_m93J07_subsetFunctional Set.univ - z)
    (lp.single 1 i (1 : ℝ) : apm_m93J07_l1)
  rw [lp.norm_single (by norm_num)] at hb
  norm_num at hb
  rw [apm_m93J07_subsetFunctional_single, hF i hi] at hb
  simp [Set.indicator] at hb
  exact hb

noncomputable def apm_m93J07_closedCoordinateSpan : Submodule ℝ (StrongDual ℝ apm_m93J07_l1) :=
  (Submodule.span ℝ apm_m93J07_coordinateFunctionals).topologicalClosure

lemma apm_m93J07_allOne_not_mem_closedCoordinateSpan :
    apm_m93J07_subsetFunctional Set.univ ∉ apm_m93J07_closedCoordinateSpan := by
  let C : Set (StrongDual ℝ apm_m93J07_l1) :=
    {z | 1 ≤ dist (apm_m93J07_subsetFunctional Set.univ) z}
  have hCclosed : IsClosed C := by
    exact isClosed_Ici.preimage (continuous_const.dist continuous_id)
  have hspanC : (Submodule.span ℝ apm_m93J07_coordinateFunctionals :
      Set (StrongDual ℝ apm_m93J07_l1)) ⊆ C := by
    intro z hz
    exact apm_m93J07_allOne_span_dist z hz
  have hclosureC : closure (Submodule.span ℝ apm_m93J07_coordinateFunctionals :
      Set (StrongDual ℝ apm_m93J07_l1)) ⊆ C := closure_minimal hspanC hCclosed
  intro hall
  have hmem : apm_m93J07_subsetFunctional Set.univ ∈ C :=
    hclosureC hall
  simp [C] at hmem
  norm_num at hmem

instance apm_m93J07_closedCoordinateSpan_isClosed :
    IsClosed (apm_m93J07_closedCoordinateSpan :
      Set (StrongDual ℝ apm_m93J07_l1)) :=
  Submodule.isClosed_topologicalClosure _

noncomputable def apm_m93J07_coordinateQuotientMap :
    StrongDual ℝ apm_m93J07_l1 →L[ℝ]
      (StrongDual ℝ apm_m93J07_l1 ⧸ apm_m93J07_closedCoordinateSpan) where
  toLinearMap := apm_m93J07_closedCoordinateSpan.mkQ
  cont := apm_m93J07_closedCoordinateSpan.toAddSubgroup.normedMk.continuous

lemma apm_m93J07_exists_bidual_separator :
    ∃ G : StrongDual ℝ (StrongDual ℝ apm_m93J07_l1),
      (∀ z ∈ apm_m93J07_closedCoordinateSpan, G z = 0) ∧
      G (apm_m93J07_subsetFunctional Set.univ) ≠ 0 := by
  let u : StrongDual ℝ apm_m93J07_l1 := apm_m93J07_subsetFunctional Set.univ
  let q : StrongDual ℝ apm_m93J07_l1 ⧸ apm_m93J07_closedCoordinateSpan :=
    Submodule.Quotient.mk u
  letI : IsClosed (apm_m93J07_closedCoordinateSpan.toAddSubgroup :
      Set (StrongDual ℝ apm_m93J07_l1)) :=
    apm_m93J07_closedCoordinateSpan_isClosed
  have hnq : ‖q‖ ≠ 0 := by
    intro h
    have hu : u ∈ apm_m93J07_closedCoordinateSpan :=
      (QuotientAddGroup.norm_mk_eq_zero
        (S := apm_m93J07_closedCoordinateSpan.toAddSubgroup) (m := u)).mp h
    exact apm_m93J07_allOne_not_mem_closedCoordinateSpan hu
  obtain ⟨g, _, hgq⟩ := exists_dual_vector ℝ q hnq
  refine ⟨g.comp apm_m93J07_coordinateQuotientMap, ?_, ?_⟩
  · intro z hz
    change g (Submodule.Quotient.mk z) = 0
    rw [(Submodule.Quotient.mk_eq_zero apm_m93J07_closedCoordinateSpan).2 hz, map_zero]
  · change g q ≠ 0
    rw [hgq]
    exact hnq

lemma apm_m93J07_l1_not_reflexive :
    ¬ Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ apm_m93J07_l1) := by
  obtain ⟨G, hGzero, hGone⟩ := apm_m93J07_exists_bidual_separator
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj G
  have hxi (i : ℕ) : x i = 0 := by
    have hcoord : apm_m93J07_subsetFunctional {i} ∈
        apm_m93J07_closedCoordinateSpan := by
      exact subset_closure (Submodule.subset_span ⟨i, rfl⟩)
    have hz := hGzero (apm_m93J07_subsetFunctional {i}) hcoord
    rw [← hx, NormedSpace.dual_def, apm_m93J07_coordinateFunctional_apply] at hz
    exact hz
  have hxzero : x = 0 := by
    apply lp.ext
    funext i
    simpa using hxi i
  apply hGone
  rw [← hx, NormedSpace.dual_def, hxzero]
  simp

noncomputable def apm_m93J07_restrictRightDual (A B : Type)
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] :
    StrongDual ℝ (A × B) →L[ℝ] StrongDual ℝ B :=
  (ContinuousLinearMap.compL ℝ B (A × B) ℝ).flip
    (ContinuousLinearMap.inr ℝ A B)

lemma apm_m93J07_product_reflexive_right (A B : Type)
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (h : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ (A × B))) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ B) := by
  intro G
  let Gprod : StrongDual ℝ (StrongDual ℝ (A × B)) :=
    G.comp (apm_m93J07_restrictRightDual A B)
  obtain ⟨p, hp⟩ := h Gprod
  refine ⟨p.2, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  have hev := DFunLike.congr_fun hp
    (f.comp (ContinuousLinearMap.snd ℝ A B))
  simpa [Gprod, apm_m93J07_restrictRightDual, NormedSpace.dual_def] using hev

abbrev apm_m93J07_nonseparableNonreflexive :=
  apm_m93J07_nonseparableHilbert × apm_m93J07_l1

lemma apm_m93J07_product_single_dist
    (i j : apm_m93J07_discreteReal) (h : i ≠ j) :
    1 ≤ dist
      ((lp.single 2 i (1 : ℝ), 0) : apm_m93J07_nonseparableNonreflexive)
      ((lp.single 2 j (1 : ℝ), 0) : apm_m93J07_nonseparableNonreflexive) := by
  simpa using apm_m93J07_l2_single_dist i j h

lemma apm_m93J07_nonseparableNonreflexive_not_separable :
    ¬ Nonempty (TopologicalSpace.SeparableSpace
      apm_m93J07_nonseparableNonreflexive) := by
  classical
  rintro ⟨hsep⟩
  letI := hsep
  have hc : Countable apm_m93J07_discreteReal :=
    Pairwise.countable_of_isOpen_disjoint
      (s := fun i ↦ Metric.ball
        ((lp.single 2 i (1 : ℝ), 0) : apm_m93J07_nonseparableNonreflexive)
        (1 / 3 : ℝ))
      (fun i j hij ↦ Metric.ball_disjoint_ball (by
        norm_num
        exact (by norm_num : (2 / 3 : ℝ) ≤ 1).trans
          (apm_m93J07_l2_single_dist i j hij)))
      (fun _ ↦ Metric.isOpen_ball)
      (fun i ↦ ⟨_, Metric.mem_ball_self (by norm_num)⟩)
  exact Cardinal.not_countable_real (Set.countable_univ_iff.mpr hc)

lemma apm_m93J07_nonseparableNonreflexive_not_reflexive :
    ¬ Function.Surjective
      (NormedSpace.inclusionInDoubleDual ℝ apm_m93J07_nonseparableNonreflexive) := by
  intro h
  exact apm_m93J07_l1_not_reflexive
    (apm_m93J07_product_reflexive_right
      apm_m93J07_nonseparableHilbert apm_m93J07_l1 h)

noncomputable def apm_m93J07_nonseparableNonreflexiveBanach : apm_m93j07_Banach where
  carrier := apm_m93J07_nonseparableNonreflexive
  normedAddCommGroup := inferInstance
  normedSpace := inferInstance
  completeSpace := inferInstance

lemma apm_m93J07_exists_annihilator {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : Submodule ℝ E) [IsClosed (S : Set E)]
    (x : E) (hx : x ∉ S) :
    ∃ g : StrongDual ℝ E, (∀ z ∈ S, g z = 0) ∧ g x ≠ 0 := by
  letI : IsClosed (S.toAddSubgroup : Set E) := ‹IsClosed (S : Set E)›
  let q : E ⧸ S := Submodule.Quotient.mk x
  have hnq : ‖q‖ ≠ 0 := by
    intro h
    apply hx
    exact (QuotientAddGroup.norm_mk_eq_zero
      (S := S.toAddSubgroup) (m := x)).mp h
  obtain ⟨g, _, hgq⟩ := exists_dual_vector ℝ q hnq
  let Q : E →L[ℝ] E ⧸ S :=
    { toLinearMap := S.mkQ
      cont := S.toAddSubgroup.normedMk.continuous }
  refine ⟨g.comp Q, ?_, ?_⟩
  · intro z hz
    change g (Submodule.Quotient.mk z) = 0
    rw [(Submodule.Quotient.mk_eq_zero S).2 hz, map_zero]
  · change g q ≠ 0
    rw [hgq]
    exact hnq

lemma apm_m93J07_dual_separable_implies_separable {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hdual : Nonempty (TopologicalSpace.SeparableSpace (StrongDual ℝ E))) :
    Nonempty (TopologicalSpace.SeparableSpace E) := by
  letI := hdual.some
  let f : ℕ → StrongDual ℝ E := TopologicalSpace.denseSeq _
  let x : ℕ → E := fun n ↦
    if h : (1 / 2 : ℝ) < ‖f n‖ then
      Classical.choose ((f n).exists_lt_apply_of_lt_opNorm
        (show ‖f n‖ / 2 < ‖f n‖ by linarith))
    else 0
  have hxnorm (n : ℕ) (h : (1 / 2 : ℝ) < ‖f n‖) : ‖x n‖ < 1 := by
    simp only [x, dif_pos h]
    exact (Classical.choose_spec ((f n).exists_lt_apply_of_lt_opNorm
      (show ‖f n‖ / 2 < ‖f n‖ by linarith))).1
  have hxeval (n : ℕ) (h : (1 / 2 : ℝ) < ‖f n‖) :
      ‖f n‖ / 2 < ‖f n (x n)‖ := by
    simp only [x, dif_pos h]
    exact (Classical.choose_spec ((f n).exists_lt_apply_of_lt_opNorm
      (show ‖f n‖ / 2 < ‖f n‖ by linarith))).2
  let W : Submodule ℝ E := (Submodule.span ℝ (Set.range x)).topologicalClosure
  have hW : W = ⊤ := by
    by_contra hne
    have hex : ∃ y : E, y ∉ W := by
      by_contra h
      push_neg at h
      exact hne (eq_top_iff.mpr fun y _ ↦ h y)
    obtain ⟨y, hy⟩ := hex
    letI : IsClosed (W : Set E) := Submodule.isClosed_topologicalClosure _
    obtain ⟨g0, hg0W, hg0y⟩ := apm_m93J07_exists_annihilator W y hy
    have hg0 : ‖g0‖ ≠ 0 := by
      intro h
      exact hg0y ((norm_eq_zero.mp h) ▸ rfl)
    let g : StrongDual ℝ E := ‖g0‖⁻¹ • g0
    have hgW : ∀ z ∈ W, g z = 0 := by
      intro z hz
      simp [g, hg0W z hz]
    have hgnorm : ‖g‖ = 1 := by
      simp [g, norm_smul, hg0]
    obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq
      (StrongDual ℝ E)).exists_dist_lt g (by norm_num : (0 : ℝ) < 1 / 4)
    have hdiff : ‖f n - g‖ < 1 / 4 := by
      simpa [f, dist_eq_norm, norm_sub_rev] using hn
    have hfn : (3 / 4 : ℝ) < ‖f n‖ := by
      have ht := norm_sub_norm_le g (f n)
      rw [hgnorm, norm_sub_rev] at ht
      linarith
    have hhalf : (1 / 2 : ℝ) < ‖f n‖ := by linarith
    have hxW : x n ∈ W := subset_closure (Submodule.subset_span ⟨n, rfl⟩)
    have heq : f n (x n) = (f n - g) (x n) := by
      simp [hgW (x n) hxW]
    have hupper := ContinuousLinearMap.le_opNorm (f n - g) (x n)
    rw [← heq] at hupper
    have hlower := hxeval n hhalf
    have hxn := hxnorm n hhalf
    have hnonneg : 0 ≤ ‖f n - g‖ := norm_nonneg _
    nlinarith
  have hs : TopologicalSpace.IsSeparable
      (closure (Submodule.span ℝ (Set.range x) : Set E)) :=
    (Set.countable_range x).isSeparable.span.closure
  have hset : closure (Submodule.span ℝ (Set.range x) : Set E) = Set.univ := by
    change (W : Set E) = Set.univ
    rw [hW]
    rfl
  have hu : TopologicalSpace.IsSeparable (Set.univ : Set E) := by
    rw [← hset]
    exact hs
  exact ⟨TopologicalSpace.isSeparable_univ_iff.mp hu⟩

noncomputable def apm_m93J07_mu : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)
abbrev apm_m93J07_H := Lp ℝ 2 apm_m93J07_mu

instance apm_m93J07_mu_isFinite : IsFiniteMeasure apm_m93J07_mu :=
  ⟨by simp [apm_m93J07_mu]⟩

lemma apm_m93J07_id_memLp_top : MemLp (fun x : ℝ ↦ x) ⊤ apm_m93J07_mu := by
  apply memLp_top_of_bound continuous_id.aestronglyMeasurable 1
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simp only [id_eq, Real.norm_eq_abs]
  rw [abs_of_nonneg hx.1]
  exact hx.2

noncomputable def apm_m93J07_multiplier : Lp ℝ ⊤ apm_m93J07_mu :=
  apm_m93J07_id_memLp_top.toLp (fun x ↦ x)

noncomputable def apm_m93J07_mulLinear : apm_m93J07_H →ₗ[ℝ] apm_m93J07_H where
  toFun f := apm_m93J07_multiplier • f
  map_add' f g := Lp.add_smul _ _ _
  map_smul' c f := by
    rw [RingHom.id_apply]
    exact (Lp.smul_comm (p := ⊤) (q := 2) (r := 2)
      c apm_m93J07_multiplier f).symm

noncomputable def apm_m93J07_mulCLM : apm_m93J07_H →L[ℝ] apm_m93J07_H :=
  apm_m93J07_mulLinear.mkContinuous ‖apm_m93J07_multiplier‖ (fun f ↦
    Lp.norm_smul_le apm_m93J07_multiplier f)

lemma apm_m93J07_mulCLM_injective : Function.Injective apm_m93J07_mulCLM := by
  apply LinearMap.ker_eq_bot.mp
  rw [eq_bot_iff]
  intro f hf
  apply Lp.ext
  have he := Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
    apm_m93J07_multiplier f
  change apm_m93J07_multiplier • f = 0 at hf
  rw [hf] at he
  filter_upwards [he, apm_m93J07_id_memLp_top.coeFn_toLp,
    (volume.ae_ne 0).filter_mono (ae_mono Measure.restrict_le_self),
    Lp.coeFn_zero ℝ 2 apm_m93J07_mu] with x hprod hmult hx hzero
  change apm_m93J07_multiplier x = x at hmult
  have hprod' : x * f x = (0 : ℝ) := by
    calc
      x * f x = apm_m93J07_multiplier x * f x := by rw [hmult]
      _ = (0 : apm_m93J07_H) x := hprod.symm
      _ = 0 := hzero
  rw [hzero]
  exact (mul_eq_zero.mp hprod').resolve_left hx

lemma apm_m93J07_mulLinear_symmetric :
    LinearMap.IsSymmetric apm_m93J07_mulLinear := by
  intro f g
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
      apm_m93J07_multiplier f,
    Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
      apm_m93J07_multiplier g] with x hf hg
  change inner ℝ ((apm_m93J07_multiplier • f) x) (g x) =
    inner ℝ (f x) ((apm_m93J07_multiplier • g) x)
  rw [hf, hg]
  change inner ℝ (apm_m93J07_multiplier x • f x) (g x) =
    inner ℝ (f x) (apm_m93J07_multiplier x • g x)
  rw [real_inner_smul_left, real_inner_smul_right]

lemma apm_m93J07_mulCLM_denseRange : DenseRange apm_m93J07_mulCLM := by
  have hker : LinearMap.ker apm_m93J07_mulLinear = ⊥ :=
    LinearMap.ker_eq_bot.mpr apm_m93J07_mulCLM_injective
  have hortho : (LinearMap.range apm_m93J07_mulLinear)ᗮ = ⊥ := by
    rw [apm_m93J07_mulLinear_symmetric.orthogonal_range, hker]
  let K := (LinearMap.range apm_m93J07_mulLinear).topologicalClosure
  have hKorth : Kᗮ = ⊥ := by
    change ((LinearMap.range apm_m93J07_mulLinear).topologicalClosure)ᗮ = ⊥
    rw [Submodule.orthogonal_closure, hortho]
  have hK : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hKorth
  rw [denseRange_iff_closure_range]
  have hset := congrArg (fun S : Submodule ℝ apm_m93J07_H ↦ (S : Set apm_m93J07_H)) hK
  simpa [K] using hset

lemma apm_m93J07_inv_not_memLp_two :
    ¬ MemLp (fun x : ℝ ↦ x⁻¹) 2 apm_m93J07_mu := by
  intro h
  have hi : Integrable (fun x : ℝ ↦ (x⁻¹) ^ 2) apm_m93J07_mu :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mp h
  have hi' : IntegrableOn (fun x : ℝ ↦ (x⁻¹) ^ 2) (Set.Ioo 0 1) volume :=
    hi.mono_measure (Measure.restrict_mono (by
      intro x hx
      exact ⟨hx.1.le, hx.2.le⟩) le_rfl)
  have hp : IntegrableOn (fun x : ℝ ↦ x ^ (-2 : ℝ)) (Set.Ioo 0 1) volume := by
    apply hi'.congr_fun _ measurableSet_Ioo
    intro x hx
    dsimp only
    rw [← Real.rpow_neg_one x, ← Real.rpow_natCast,
      ← Real.rpow_mul hx.1.le]
    norm_num
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one] at hp
  norm_num at hp

lemma apm_m93J07_mulCLM_not_surjective :
    ¬ Function.Surjective apm_m93J07_mulCLM := by
  intro hsurj
  let one : apm_m93J07_H := Lp.const 2 apm_m93J07_mu (1 : ℝ)
  obtain ⟨f, hf⟩ := hsurj one
  have he := Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
    apm_m93J07_multiplier f
  change apm_m93J07_multiplier • f = one at hf
  rw [hf] at he
  have hinv : (fun x : ℝ ↦ x⁻¹) =ᵐ[apm_m93J07_mu] fun x ↦ f x := by
    filter_upwards [he, apm_m93J07_id_memLp_top.coeFn_toLp,
      Lp.coeFn_const (α := ℝ) (p := 2) (μ := apm_m93J07_mu) (c := (1 : ℝ)),
      (volume.ae_ne 0).filter_mono (ae_mono Measure.restrict_le_self)] with
      x hprod hmult hone hx
    change apm_m93J07_multiplier x = x at hmult
    have hone' : one x = 1 := by simpa using hone
    have hxf : x * f x = 1 := by
      calc
        x * f x = apm_m93J07_multiplier x * f x := by rw [hmult]
        _ = one x := hprod.symm
        _ = 1 := hone'
    calc
      x⁻¹ = x⁻¹ * (x * f x) := by rw [hxf, mul_one]
      _ = f x := by field_simp
  apply apm_m93J07_inv_not_memLp_two
  exact (Lp.memLp f).ae_eq hinv.symm

theorem apm_m93j07 :
    (∃ X : apm_m93j07_Banach, ¬ apm_m93j07_Separable X) ∧
    (∃ X : apm_m93j07_Banach,
      apm_m93j07_Separable X ∧ ¬ apm_m93j07_Reflexive X) ∧
    (∃ X : apm_m93j07_Banach,
      ¬ apm_m93j07_Separable X ∧ apm_m93j07_Reflexive X) ∧
    (∃ X : apm_m93j07_Banach,
      ¬ apm_m93j07_Separable X ∧ ¬ apm_m93j07_Reflexive X) ∧
    (∃ X : apm_m93j07_Banach,
      apm_m93j07_Separable X ∧ ¬ apm_m93j07_DualSeparable X) ∧
    (¬ ∃ X : apm_m93j07_Banach,
      ¬ apm_m93j07_Separable X ∧ apm_m93j07_DualSeparable X) ∧
    (let H := Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1));
      (∃ Φ : H →ₗ[ℝ] H, DenseRange Φ ∧ ¬ Function.Surjective Φ) ∧
      (∃ Φ : H →L[ℝ] H, DenseRange Φ ∧ ¬ Function.Surjective Φ)) ∧
    (∃ f : ℝ → ℝ, MemLp f 2 volume ∧ ¬ MemLp f 4 volume) ∧
    (∃ f : ℝ → ℝ, MemLp f 4 volume ∧ ¬ MemLp f 2 volume) ∧
    (∃ f : ℝ → ℝ,
      MemLp f 2 (volume.restrict (Set.Icc 0 1)) ∧
      ¬ MemLp f 4 (volume.restrict (Set.Icc 0 1))) ∧
    (¬ ∃ f : ℝ → ℝ,
      MemLp f 4 (volume.restrict (Set.Icc 0 1)) ∧
      ¬ MemLp f 2 (volume.restrict (Set.Icc 0 1))) := by
  have hfiniteLp : ¬ ∃ f : ℝ → ℝ,
      MemLp f 4 (volume.restrict (Set.Icc 0 1)) ∧
      ¬ MemLp f 2 (volume.restrict (Set.Icc 0 1)) := by
    rintro ⟨f, hf4, hf2⟩
    exact hf2 (hf4.mono_exponent (by norm_num))
  have hdualForcesSeparable : ¬ ∃ X : apm_m93j07_Banach,
      ¬ apm_m93j07_Separable X ∧ apm_m93j07_DualSeparable X := by
    rintro ⟨X, hnot, hdual⟩
    exact hnot (apm_m93J07_dual_separable_implies_separable hdual)
  have hoperators :
      (let H := Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1));
        (∃ Φ : H →ₗ[ℝ] H, DenseRange Φ ∧ ¬ Function.Surjective Φ) ∧
        (∃ Φ : H →L[ℝ] H, DenseRange Φ ∧ ¬ Function.Surjective Φ)) := by
    dsimp only
    refine ⟨⟨apm_m93J07_mulLinear, ?_, ?_⟩,
      ⟨apm_m93J07_mulCLM, ?_, ?_⟩⟩
    · simpa [apm_m93J07_mu] using apm_m93J07_mulCLM_denseRange
    · simpa [apm_m93J07_mu] using apm_m93J07_mulCLM_not_surjective
    · simpa [apm_m93J07_mu] using apm_m93J07_mulCLM_denseRange
    · simpa [apm_m93J07_mu] using apm_m93J07_mulCLM_not_surjective
  /-
  Boundary: the remaining ten clauses require bundling concrete Banach
  spaces with separability/reflexivity proofs, including a nonseparable
  Hilbert space and the theorem that separability of `StrongDual ℝ X`
  forces separability of `X`. They also require a concrete bounded operator
  on the restricted-measure `Lp` space with dense proper range, plus three
  explicit power-singularity/tail functions with exact `MemLp` and
  non-`MemLp` calculations.

  I searched the `MemLp` comparison API and used
  `MemLp.mono_exponent` above to prove the finite-measure impossibility.
  I did not find compiled sibling constructions covering the bundled
  separability/reflexivity examples or the required `Lp` multiplication
  operator and power-integrability calculations within this pass.

  Closer hop 1 found the relevant improper-integral APIs and compiled the four
  scalar power tests above: local exponents `-2/3` and `-4/3`, and tail
  exponents `-4/3` and `-2/3`, have exactly the required integrability behavior.
  The sibling `a01A06` demonstrates the local `Ioo` conversion but is itself
  partial, so only its proof pattern—not its theorem—was reused. The remaining
  `Lᵖ` work is now the measurable-indicator and `MemLp` conversion around these
  facts. Searches still found no packaged theorem that dual separability forces
  primal separability, nor a ready dense-proper multiplication operator on the
  frozen restricted `Lp` type; the Banach-space bundle conjuncts therefore
  remain the dominant blocker.

  Closer hop 2 completes that local conversion.  The explicit indicator
  `apm_m93J07_localWitness` is strongly measurable, belongs to `L²(volume)`,
  and does not belong to `L⁴(volume)`, by
  `memLp_two_iff_integrable_sq`, `MemLp.integrable_norm_rpow`, and the four
  scalar tests above.  Searches of the strong-dual, weak-dual, separability,
  dense-range, and `Lp` operator sources still found no packaged proof that a
  separable strong dual forces primal separability and no ready dense proper
  endomorphism of the exact restricted `Lp` type.  Those Banach-space and
  operator clauses remain the principal open bridge; the tail and restricted
  `MemLp` witnesses can now follow the same compiled indicator pattern.

  Closer hop 3 removes the already-proved global `L² \ L⁴` clause from the
  aggregate assumption: the final theorem now supplies it directly with
  `apm_m93J07_localWitness_memLp_two` and
  `apm_m93J07_localWitness_not_memLp_four`. The sole `sorry` is correspondingly
  narrowed to the six Banach-space assertions, the dense proper operator pair,
  the tail `L⁴ \ L²` witness, and the restricted-measure `L² \ L⁴` witness.
  Further searches of `MemLp` restriction/indicator lemmas and the separability
  and operator APIs found no packaged closure of the dominant Banach-space
  bridge.
  -/
  exact ⟨⟨apm_m93J07_nonseparableBanach,
      apm_m93J07_boundedFunctions_not_separable⟩,
    ⟨apm_m93J07_l1Banach, apm_m93J07_l1_separable,
      apm_m93J07_l1_not_reflexive⟩,
    ⟨apm_m93J07_nonseparableReflexiveBanach,
      apm_m93J07_l2_not_separable,
      apm_m93J07_hilbert_reflexive apm_m93J07_nonseparableHilbert⟩,
    ⟨apm_m93J07_nonseparableNonreflexiveBanach,
      apm_m93J07_nonseparableNonreflexive_not_separable,
      apm_m93J07_nonseparableNonreflexive_not_reflexive⟩,
    ⟨apm_m93J07_l1Banach, apm_m93J07_l1_separable,
      apm_m93J07_l1_dual_not_separable⟩,
    hdualForcesSeparable, hoperators,
    ⟨apm_m93J07_localWitness, apm_m93J07_localWitness_memLp_two,
      apm_m93J07_localWitness_not_memLp_four⟩,
    ⟨apm_m93J07_tailWitness, apm_m93J07_tailWitness_memLp_four,
      apm_m93J07_tailWitness_not_memLp_two⟩,
    ⟨apm_m93J07_localWitness, apm_m93J07_localWitness_memLp_two_restrict,
      apm_m93J07_localWitness_not_memLp_four_restrict⟩,
    hfiniteLp⟩
