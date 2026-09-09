import ConstructionTargets.SardGenuineSmoothRankUpperResidualZero
import ConstructionTargets.SardProjectedPositiveRankDimensionData

open Set MeasureTheory
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 800000
namespace SardGenuineSmoothPositiveRankSliceNullityProbe
universe u v
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F]

theorem exists_positive_rank_slice_image_null
    (f : E → F) (x : E) (hf : ContDiff ℝ ∞ f)
    (hpos : 0 < Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap))
    (hlt : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) < Module.finrank ℝ F) :
    let L := fderiv ℝ f x
    let R := LinearMap.range L.toLinearMap
    let G := (R.orthogonalProjection.comp L).ker
    ∀ (μ : Measure Rᗮ) [μ.IsAddHaarMeasure],
    (∀ (H : Type u) [NormedAddCommGroup H] [NormedSpace ℝ H]
      [FiniteDimensional ℝ H] [CompleteSpace H],
      Module.finrank ℝ H < Module.finrank ℝ E →
      ∀ (q : H → Rᗮ) (s : Set H),
        (∀ z ∈ s, ContDiffAt ℝ ∞ q z) →
        μ (q '' (s ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0) →
    ∃ e : OpenPartialHomeomorph E (R × G),
      x ∈ e.source ∧ Module.finrank ℝ G < Module.finrank ℝ E ∧ Nontrivial Rᗮ ∧
      (∀ y, (e y).1 = R.orthogonalProjection (f y)) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ r, μ ((fun z : G => Rᗮ.orthogonalProjection (f (e.symm (r,z)))) ''
        {z | (r,z) ∈ e.target ∧
          Module.finrank ℝ (LinearMap.range (fderiv ℝ f (e.symm (r,z))).toLinearMap) ≤ Module.finrank ℝ R}) = 0 := by
  dsimp only
  let L := fderiv ℝ f x
  let R := LinearMap.range L.toLinearMap
  let G := (R.orthogonalProjection.comp L).ker
  intro μ hμ hind
  have hdim : Module.finrank ℝ G < Module.finrank ℝ E :=
    (SardProjectedPositiveRankDimensionDataProbe.projected_positiveRank_dimension_data
      L (Module.finrank ℝ R) rfl hpos).2.2
  have hSpos : 0 < Module.finrank ℝ Rᗮ := by
    have h := R.finrank_add_finrank_orthogonal
    change Module.finrank ℝ R < Module.finrank ℝ F at hlt
    omega
  letI hS : Nontrivial Rᗮ := Module.finrank_pos_iff.mp hSpos
  letI hG : CompleteSpace G := inferInstance
  obtain ⟨e,he,hfirst,hsm,hsi,hreg,hzero⟩ :=
    SardGenuineSmoothRankUpperResidualZeroProbe.exists_rank_upper_residual_zero f x hf
  refine ⟨e,he,hdim,hS,hfirst,hsm,hsi,?_⟩
  intro r
  let q : G → Rᗮ := fun z => Rᗮ.orthogonalProjection (f (e.symm (r,z)))
  let s : Set G := {z | (r,z) ∈ e.target ∧
    Module.finrank ℝ (LinearMap.range (fderiv ℝ f (e.symm (r,z))).toLinearMap) ≤ Module.finrank ℝ R}
  have hc : ∀ z ∈ s, ¬Function.Surjective (fderiv ℝ q z) := by
    intro z hz hsurj
    have hd : fderiv ℝ q z = 0 := (hzero r z hz.1 hz.2).fderiv
    obtain ⟨a,ha⟩ := exists_ne (0 : Rᗮ)
    obtain ⟨b,hb⟩ := hsurj a
    rw [hd] at hb
    exact ha (by simpa using hb.symm)
  have hn := @hind G inferInstance inferInstance inferInstance hG hdim q s
    (fun z hz => hreg r z hz.1)
  have heq : s ∩ {z | ¬Function.Surjective (fderiv ℝ q z)} = s :=
    Set.inter_eq_left.mpr (fun z hz => hc z hz)
  have hn' : μ (q '' (s ∩ {z | ¬Function.Surjective (fderiv ℝ q z)})) = 0 := by
    convert hn using 1
  rw [heq] at hn'
  exact hn'

#print axioms exists_positive_rank_slice_image_null
end SardGenuineSmoothPositiveRankSliceNullityProbe
