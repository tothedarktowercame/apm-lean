import ConstructionTargets.PlaneArcSmallTranslation
/- Finite families of plane curves admit simultaneous arbitrarily small translations
with finite parameter coincidences. Open extensions include endpoint coincidences.
Translations may move endpoints; no chart containment, coverage preservation,
compatible faces or triangulation is asserted. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace PlaneSmallRegularValue
theorem exists_small_common_regular {ι : Type} [Finite ι]
    (f : ι → Plane → Plane) (U : ι → Set Plane) (hU : ∀ i, IsOpen (U i))
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i)) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : Plane, ‖v‖ < ε ∧ ∀ i z, z ∈ U i → f i z = v → Function.Surjective (fderiv ℝ (f i) z) := by
  let W (i : ι) : Set Model := coordinates ⁻¹' U i
  have hW (i : ι) : IsOpen (W i) := (hU i).preimage coordinates.continuous
  have hg (i : ι) : ContDiffOn ℝ ∞ (conjugate (f i)) (W i) :=
    coordinates.symm.contDiff.contDiffOn.comp
      ((hf i).comp coordinates.contDiff.contDiffOn (fun _ hz => hz)) (fun _ _ => mem_univ _)
  let C (i : ι) := conjugate (f i) '' (W i ∩ {z | ¬ Function.Surjective (fderiv ℝ (conjugate (f i)) z)})
  have hC (i : ι) : volume (C i) = 0 := SardGenuineSmoothEuclideanProbe.open_domain_critical_image_null
    volume (conjugate (f i)) (W i) (W i) (hW i) Set.Subset.rfl (hg i)
  have hUnion : volume (⋃ i, C i) = 0 := measure_iUnion_null hC
  let B : Set Model := coordinates ⁻¹' Metric.ball 0 ε
  have hB : IsOpen B := Metric.isOpen_ball.preimage coordinates.continuous
  have hBne : B.Nonempty := ⟨0, by simpa [B] using hε⟩
  have hpos : 0 < volume B := hB.measure_pos volume hBne
  have hnot : ¬ B ⊆ ⋃ i, C i := by
    intro h
    have hle : volume B ≤ volume (⋃ i, C i) := measure_mono h
    rw [hUnion] at hle
    exact (ne_of_gt hpos) (le_antisymm hle bot_le)
  obtain ⟨v,hvB,hvC⟩ := Set.not_subset.mp hnot
  refine ⟨coordinates v, ?_, ?_⟩
  · simpa only [B, mem_preimage, Metric.mem_ball, dist_zero_right] using hvB
  · intro i z hz he
    have hzW : coordinates.symm z ∈ W i := by simpa [W] using hz
    have hs : Function.Surjective (fderiv ℝ (conjugate (f i)) (coordinates.symm z)) := by
      by_contra hn
      apply hvC
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      refine ⟨coordinates.symm z, ⟨hzW,hn⟩, ?_⟩
      simp [conjugate,he]
    have hd : DifferentiableAt ℝ (f i) (coordinates (coordinates.symm z)) := by
      simpa using ((hf i).contDiffAt ((hU i).mem_nhds hz)).differentiableAt (by simp)
    simpa using surjective_of_conjugate (f i) (coordinates.symm z) hd hs

#print axioms exists_small_common_regular
end PlaneSmallRegularValue

namespace PlaneArcSmallTranslation
open CompactTransverseArcIntersections
theorem finite_against_family {ι : Type} [Finite ι]
    (a : ι → ℝ → Plane) (b : ℝ → Plane) (U : ι → Set ℝ) (V : Set ℝ)
    (hU : ∀ i, IsOpen (U i)) (hV : IsOpen V)
    (hIU : ∀ i, Icc (0 : ℝ) 1 ⊆ U i) (hIV : Icc (0 : ℝ) 1 ⊆ V)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) (U i)) (hb : ContDiffOn ℝ ∞ b V)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ v : Plane, ‖v‖ < ε ∧
      ∀ i, {p : Plane | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ a i p.1 = b p.2 + v}.Finite := by
  have hd (i : ι) : ContDiffOn ℝ ∞ (difference (a i) b) (U i ×ˢ V) :=
    ((ha i).comp contDiff_fst.contDiffOn (fun _ h => h.1)).sub
      (hb.comp contDiff_snd.contDiffOn (fun _ h => h.2))
  obtain ⟨v,hv,hreg⟩ := PlaneSmallRegularValue.exists_small_common_regular
    (fun i => difference (a i) b) (fun i => U i ×ˢ V) (fun i => (hU i).prod hV) hd ε hε
  refine ⟨v,hv,?_⟩
  intro i
  have hc := compact_fiber_finite (difference (a i) b)
    (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) v (isCompact_Icc.prod isCompact_Icc)
    (fun p hp => ((hd i).contDiffAt (((hU i).prod hV).mem_nhds ⟨hIU i hp.1,hIV hp.2⟩)).of_le (by simp))
    (fun p hp he => ?_)
  · convert hc using 1
    ext p
    simp only [mem_setOf_eq, mem_inter_iff, mem_prod, mem_preimage, mem_singleton_iff,
      difference, sub_eq_iff_eq_add, and_assoc]
    rw [add_comm]
  · have hs := hreg i p ⟨hIU i hp.1,hIV hp.2⟩ he
    let L := fderiv ℝ (difference (a i) b) p
    exact ⟨ContinuousLinearEquiv.ofBijective L
      (LinearMap.ker_eq_bot.mpr (LinearMap.injective_iff_surjective.mpr hs))
      (LinearMap.range_eq_top.mpr hs), rfl⟩

#print axioms finite_against_family
end PlaneArcSmallTranslation
namespace PlaneArcSmallTranslation
open CompactTransverseArcIntersections

def Coincidences (a b : ℝ → Plane) : Set Plane :=
  {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ a p.1 = b p.2}

theorem finite_swap (a b : ℝ → Plane) (h : (Coincidences a b).Finite) :
    (Coincidences b a).Finite := by
  apply (h.image Prod.swap).subset
  intro p hp
  exact ⟨p.swap, ⟨hp.2.1, hp.1, hp.2.2.symm⟩, rfl⟩

theorem finite_family_finset {ι : Type} (s : Finset ι)
    (a : ι → ℝ → Plane) (U : ι → Set ℝ)
    (hU : ∀ i, IsOpen (U i)) (hIU : ∀ i, Icc (0 : ℝ) 1 ⊆ U i)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) (U i)) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : ι → Plane, (∀ i ∈ s, ‖v i‖ < ε) ∧
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        (Coincidences (fun t => a i t + v i) (fun t => a j t + v j)).Finite := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | @insert k s hks ih =>
    obtain ⟨v, hv, hp⟩ := ih
    obtain ⟨w, hw, hf⟩ := finite_against_family
      (fun i : {i // i ∈ s} => fun t => a i.val t + v i.val) (a k)
      (fun i => U i.val) (U k) (fun i => hU i.val) (hU k)
      (fun i => hIU i.val) (hIU k) (fun i => (ha i.val).add contDiffOn_const)
      (ha k) ε hε
    refine ⟨Function.update v k w, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa using hw
      · have hik : i ≠ k := by intro he; subst i; exact hks hi
        simpa [Function.update_of_ne hik] using hv i hi
    · intro i hi j hj hij
      by_cases hik : i = k
      · subst i
        have hjk : j ≠ k := Ne.symm hij
        have hjs : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hjk
        have h := finite_swap (fun t => a j t + v j) (fun t => a k t + w) (hf ⟨j,hjs⟩)
        simpa [Function.update_of_ne hjk] using h
      · have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hik
        by_cases hjk : j = k
        · subst j
          simpa [Function.update_of_ne hik, Coincidences] using hf ⟨i,his⟩
        · have hjs : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hjk
          simpa [Function.update_of_ne hik, Function.update_of_ne hjk] using hp i his j hjs hij

theorem finite_family {ι : Type} [Finite ι]
    (a : ι → ℝ → Plane) (U : ι → Set ℝ)
    (hU : ∀ i, IsOpen (U i)) (hIU : ∀ i, Icc (0 : ℝ) 1 ⊆ U i)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) (U i)) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : ι → Plane, (∀ i, ‖v i‖ < ε) ∧
      ∀ i j, i ≠ j →
        (Coincidences (fun t => a i t + v i) (fun t => a j t + v j)).Finite := by
  classical
  letI := Fintype.ofFinite ι
  simpa using finite_family_finset Finset.univ a U hU hIU ha ε hε

#print axioms finite_swap
#print axioms finite_family_finset
#print axioms finite_family
end PlaneArcSmallTranslation
