import ConstructionTargets.PlaneArcFiniteSmallTranslations

/- Simultaneous plane translations can be chosen inside prescribed open
neighborhoods of compact arc images. Translations may move endpoints. -/
noncomputable section
open Set
open scoped ContDiff

namespace PlaneArcContainedSmallTranslations

open PlaneArcSmallTranslation CompactTransverseArcIntersections

theorem finite_positive_lower_bound {ι : Type} [Fintype ι]
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ e : ℝ, 0 < e ∧ ∀ i, e ≤ d i := by
  classical
  have aux : ∀ s : Finset ι, (∀ i ∈ s, 0 < d i) →
      ∃ e : ℝ, 0 < e ∧ ∀ i ∈ s, e ≤ d i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨1, zero_lt_one, by simp⟩
    | @insert a s ha ih =>
      intro hs
      obtain ⟨e, he, hle⟩ := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
      refine ⟨min e (d a), lt_min he (hs a (Finset.mem_insert_self a s)), ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hle i hi)
  obtain ⟨e, he, hle⟩ := aux Finset.univ (fun i _ => hd i)
  exact ⟨e, he, fun i => hle i (Finset.mem_univ i)⟩

theorem image_margin {ι : Type} [Fintype ι]
    (K W : ι → Set Plane)
    (hK : ∀ i, IsCompact (K i))
    (hW : ∀ i, IsOpen (W i))
    (hsub : ∀ i, K i ⊆ W i) :
    ∃ e : ℝ, 0 < e ∧ ∀ i,
      Metric.thickening e (K i) ⊆ W i := by
  let witness (i : ι) :=
    (hK i).exists_thickening_subset_open (hW i) (hsub i)
  let d (i : ι) : ℝ := Classical.choose (witness i)
  have hd (i : ι) : 0 < d i := (Classical.choose_spec (witness i)).1
  have hthick (i : ι) : Metric.thickening (d i)
      (K i) ⊆ W i := (Classical.choose_spec (witness i)).2
  obtain ⟨e, he, hle⟩ := finite_positive_lower_bound d hd
  refine ⟨e, he, fun i => ?_⟩
  intro x hx
  apply hthick i
  rw [Metric.mem_thickening_iff] at hx ⊢
  obtain ⟨z, hz, hxz⟩ := hx
  exact ⟨z, hz, hxz.trans_le (hle i)⟩

theorem translated_isEmbedding (a : C(Icc (0 : ℝ) 1, Plane))
    (ha : Topology.IsEmbedding a) (v : Plane) :
    Topology.IsEmbedding (fun t => a t + v) := by
  exact (Homeomorph.addRight v).isEmbedding.comp ha

theorem contained_family {ι : Type} [Finite ι]
    (a : ι → ℝ → Plane) (U : ι → Set ℝ) (W : ι → Set Plane)
    (hU : ∀ i, IsOpen (U i)) (hIU : ∀ i, Icc (0 : ℝ) 1 ⊆ U i)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) (U i))
    (hemb : ∀ i, Topology.IsEmbedding (fun t : Icc (0 : ℝ) 1 => a i t))
    (hW : ∀ i, IsOpen (W i))
    (hsub : ∀ i, a i '' Icc (0 : ℝ) 1 ⊆ W i)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ v : ι → Plane, (∀ i, ‖v i‖ < ε) ∧
      (∀ i, Topology.IsEmbedding (fun t : Icc (0 : ℝ) 1 => a i t + v i)) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) 1 → a i t + v i ∈ W i) ∧
      ∀ i j, i ≠ j →
        (Coincidences (fun t => a i t + v i) (fun t => a j t + v j)).Finite := by
  classical
  letI := Fintype.ofFinite ι
  have hcont (i : ι) : ContinuousOn (a i) (Icc (0 : ℝ) 1) :=
    (ha i).continuousOn.mono (hIU i)
  obtain ⟨e, he, heW⟩ := image_margin
    (fun i => a i '' Icc (0 : ℝ) 1) W
    (fun i => isCompact_Icc.image_of_continuousOn (hcont i)) hW hsub
  obtain ⟨v, hv, hfinite⟩ := finite_family a U hU hIU ha (min ε e) (lt_min hε he)
  refine ⟨v, fun i => (hv i).trans_le (min_le_left _ _),
    fun i => translated_isEmbedding
      ⟨fun t => a i t, (hcont i).restrict⟩ (hemb i) (v i), ?_, hfinite⟩
  intro i t ht
  apply heW i
  rw [Metric.mem_thickening_iff]
  refine ⟨a i t, ⟨t, ht, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  simpa using (hv i).trans_le (min_le_right ε e)

#print axioms finite_positive_lower_bound
#print axioms image_margin
#print axioms translated_isEmbedding
#print axioms contained_family

end PlaneArcContainedSmallTranslations
