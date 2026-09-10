import ConstructionTargets.SardGenuineSmoothEuclidean
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import ConstructionTargets.CompactTransverseArcIntersections
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace PlaneSmallRegularValue
abbrev Plane := ℝ × ℝ
abbrev Model := EuclideanSpace ℝ (Fin 2)
def coordinates : Model ≃L[ℝ] Plane := ContinuousLinearEquiv.ofFinrankEq (by simp)
def conjugate (f : Plane → Plane) : Model → Model := fun z => coordinates.symm (f (coordinates z))
theorem conjugate_derivative (f : Plane → Plane) (z : Model)
    (hf : DifferentiableAt ℝ f (coordinates z)) :
    HasFDerivAt (conjugate f)
      (coordinates.symm.toContinuousLinearMap.comp
        ((fderiv ℝ f (coordinates z)).comp coordinates.toContinuousLinearMap)) z :=
  coordinates.symm.hasFDerivAt.comp z (hf.hasFDerivAt.comp z coordinates.hasFDerivAt)

theorem surjective_of_conjugate (f : Plane → Plane) (z : Model)
    (hf : DifferentiableAt ℝ f (coordinates z))
    (hs : Function.Surjective (fderiv ℝ (conjugate f) z)) :
    Function.Surjective (fderiv ℝ f (coordinates z)) := by
  rw [(conjugate_derivative f z hf).fderiv] at hs
  intro w
  obtain ⟨v,hv⟩ := hs (coordinates.symm w)
  exact ⟨coordinates v, coordinates.symm.injective hv⟩

theorem exists_small_regular (f : Plane → Plane) (U : Set Plane) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : Plane, ‖v‖ < ε ∧ ∀ z ∈ U, f z = v → Function.Surjective (fderiv ℝ f z) := by
  let W : Set Model := coordinates ⁻¹' U
  have hW : IsOpen W := hU.preimage coordinates.continuous
  have hg : ContDiffOn ℝ ∞ (conjugate f) W :=
    coordinates.symm.contDiff.contDiffOn.comp
      (hf.comp coordinates.contDiff.contDiffOn (fun _ hz => hz)) (fun _ _ => mem_univ _)
  let C := conjugate f '' (W ∩ {z | ¬ Function.Surjective (fderiv ℝ (conjugate f) z)})
  have hC : volume C = 0 := SardGenuineSmoothEuclideanProbe.open_domain_critical_image_null
    volume (conjugate f) W W hW Set.Subset.rfl hg
  let B : Set Model := coordinates ⁻¹' Metric.ball 0 ε
  have hB : IsOpen B := Metric.isOpen_ball.preimage coordinates.continuous
  have hBne : B.Nonempty := ⟨0, by simpa [B] using hε⟩
  have hpos : 0 < volume B := hB.measure_pos volume hBne
  have hnot : ¬ B ⊆ C := by
    intro h
    have hle : volume B ≤ volume C := measure_mono h
    rw [hC] at hle
    exact (ne_of_gt hpos) (le_antisymm hle bot_le)
  obtain ⟨v,hvB,hvC⟩ := Set.not_subset.mp hnot
  refine ⟨coordinates v, ?_, ?_⟩
  · simpa only [B, mem_preimage, Metric.mem_ball, dist_zero_right] using hvB
  · intro z hz he
    have hzW : coordinates.symm z ∈ W := by simpa [W] using hz
    have hs : Function.Surjective (fderiv ℝ (conjugate f) (coordinates.symm z)) := by
      by_contra hn
      apply hvC
      refine ⟨coordinates.symm z, ⟨hzW,hn⟩, ?_⟩
      simp [conjugate,he]
    have hd : DifferentiableAt ℝ f (coordinates (coordinates.symm z)) := by
      simpa using (hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    simpa using surjective_of_conjugate f (coordinates.symm z) hd hs
#print axioms conjugate_derivative
#print axioms surjective_of_conjugate
#print axioms exists_small_regular
end PlaneSmallRegularValue

namespace PlaneArcSmallTranslation
open CompactTransverseArcIntersections
open scoped ContDiff
noncomputable section

theorem translation_difference (a b : ℝ → Plane) (v p : Plane) :
    difference a (fun t => b t + v) p = difference a b p - v := by
  simp only [difference]; abel

theorem translated_derivative (a b : ℝ → Plane) (v p : Plane)
    (ha : DifferentiableAt ℝ a p.1) (hb : DifferentiableAt ℝ b p.2) :
    HasFDerivAt (difference a (fun t => b t + v))
      ((fderiv ℝ a p.1).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) -
       (fderiv ℝ b p.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
  have h := (difference_derivative a b p ha hb).sub_const v
  have he : difference a (fun t => b t + v) = fun q => difference a b q - v :=
    funext (translation_difference a b v)
  rw [he]
  exact h

theorem finite_translated (a b : ℝ → Plane) (U V : Set ℝ)
    (hU : IsOpen U) (hV : IsOpen V)
    (hIU : Icc (0 : ℝ) 1 ⊆ U) (hIV : Icc (0 : ℝ) 1 ⊆ V)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ v : Plane, ‖v‖ < ε ∧
      {p : Plane | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ a p.1 = b p.2 + v}.Finite := by
  have hd : ContDiffOn ℝ ∞ (difference a b) (U ×ˢ V) :=
    (ha.comp contDiff_fst.contDiffOn (fun _ h => h.1)).sub
      (hb.comp contDiff_snd.contDiffOn (fun _ h => h.2))
  obtain ⟨v,hv,hreg⟩ := PlaneSmallRegularValue.exists_small_regular
    (difference a b) (U ×ˢ V) (hU.prod hV) hd ε hε
  refine ⟨v,hv,?_⟩
  have hc := compact_fiber_finite (difference a b)
    (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) v (isCompact_Icc.prod isCompact_Icc)
    (fun p hp => (hd.contDiffAt ((hU.prod hV).mem_nhds ⟨hIU hp.1,hIV hp.2⟩)).of_le (by simp))
    (fun p hp he => ?_)
  · convert hc using 1
    ext p
    simp only [mem_setOf_eq, mem_inter_iff, mem_prod, mem_preimage, mem_singleton_iff,
      difference, sub_eq_iff_eq_add, and_assoc]
    rw [add_comm]
  · have hs := hreg p ⟨hIU hp.1,hIV hp.2⟩ he
    let L := fderiv ℝ (difference a b) p
    exact ⟨ContinuousLinearEquiv.ofBijective L
      (LinearMap.ker_eq_bot.mpr (LinearMap.injective_iff_surjective.mpr hs))
      (LinearMap.range_eq_top.mpr hs), rfl⟩
#print axioms translated_derivative
#print axioms translation_difference
#print axioms finite_translated
end
end PlaneArcSmallTranslation
