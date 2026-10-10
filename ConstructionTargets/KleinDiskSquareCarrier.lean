import ConstructionTargets.KleinSurfaceRelNormalForm
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Complex.Convex

namespace KleinDiskSquareCarrier

open Set Metric Bornology
open scoped ComplexConjugate

def centeredSquare : Set ℂ := Set.Icc (-1 : ℝ) 1 ×ℂ Set.Icc (-1 : ℝ) 1

theorem convex_centeredSquare : Convex ℝ centeredSquare := by
  rw [show centeredSquare =
    {z : ℂ | (-1 : ℝ) ≤ z.re} ∩ {z | z.re ≤ 1} ∩
      ({z | (-1 : ℝ) ≤ z.im} ∩ {z | z.im ≤ 1}) by
      ext z
      change ((-1 : ℝ) ≤ z.re ∧ z.re ≤ 1) ∧ (-1 : ℝ) ≤ z.im ∧ z.im ≤ 1 ↔ _
      simp only [mem_inter_iff, mem_setOf_eq]]
  exact ((convex_halfSpace_re_ge (-1)).inter (convex_halfSpace_re_le 1)).inter
    ((convex_halfSpace_im_ge (-1)).inter (convex_halfSpace_im_le 1))

theorem interior_centeredSquare_nonempty : (interior centeredSquare).Nonempty := by
  refine ⟨0, ?_⟩
  rw [centeredSquare, Complex.interior_reProdIm]
  exact ⟨by simpa [interior_Icc], by simpa [interior_Icc]⟩

theorem bounded_centeredSquare : IsBounded centeredSquare := by
  exact Bornology.IsBounded.reProdIm (isBounded_Icc (-1) 1) (isBounded_Icc (-1) 1)

theorem exists_centeredSquare_disk_homeomorph :
    Nonempty (centeredSquare ≃ₜ Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨h, -, hclosure, -⟩ := exists_homeomorph_image_eq
    convex_centeredSquare interior_centeredSquare_nonempty
    (NormedSpace.isVonNBounded_of_isBounded ℝ bounded_centeredSquare)
    (convex_ball (0 : ℂ) 1) (by simp [isOpen_ball.interior_eq])
    (NormedSpace.isVonNBounded_ball ℝ ℂ 1)
  have hsclosed : closure centeredSquare = centeredSquare := by
    rw [centeredSquare, Complex.closure_reProdIm]
    simp
  have hb : closure (Metric.ball (0 : ℂ) 1) = Metric.closedBall 0 1 :=
    closure_ball _ one_ne_zero
  rw [hsclosed, hb] at hclosure
  exact ⟨(Homeomorph.image h centeredSquare).trans (Homeomorph.setCongr hclosure)⟩

#print axioms exists_centeredSquare_disk_homeomorph

end KleinDiskSquareCarrier
