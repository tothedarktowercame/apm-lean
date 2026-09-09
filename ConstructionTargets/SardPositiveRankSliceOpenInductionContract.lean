import ConstructionTargets.SardGenuineSmoothRankUpperResidualZero
import ConstructionTargets.SardProjectedPositiveRankDimensionData
import ConstructionTargets.SardGenuineSmoothOpenDomainLocalization

open Set MeasureTheory
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 800000
namespace SardPositiveRankSliceOpenInductionContractProbe
universe u v
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

omit [BorelSpace F] in
theorem exists_positive_rank_slice_image_null
    (f : E → F) (x : E) (hf : ContDiff ℝ ∞ f)
    (hpos : 0 < Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap))
    (hlt : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) < Module.finrank ℝ F) :
    let L := fderiv ℝ f x
    let R := LinearMap.range L.toLinearMap
    let G := (R.orthogonalProjection.comp L).ker
    ∀ (μ : Measure Rᗮ) [μ.IsAddHaarMeasure],
    (∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [FiniteDimensional ℝ H] [CompleteSpace H],
      Module.finrank ℝ H < Module.finrank ℝ E →
      ∀ (q : H → Rᗮ) (U s : Set H),
        IsOpen U → s ⊆ U → ContDiffOn ℝ ∞ q U →
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
  let U : Set G := {z | (r,z) ∈ e.target}
  have hU : IsOpen U := e.open_target.preimage (by fun_prop)
  have hsU : s ⊆ U := fun _ hz => hz.1
  have hq : ContDiffOn ℝ ∞ q U := fun z hz => (hreg r z hz).contDiffWithinAt
  have hn := @hind G inferInstance inferInstance inferInstance hG hdim q U s hU hsU hq
  have heq : s ∩ {z | ¬Function.Surjective (fderiv ℝ q z)} = s :=
    Set.inter_eq_left.mpr (fun z hz => hc z hz)
  have hn' : μ (q '' (s ∩ {z | ¬Function.Surjective (fderiv ℝ q z)})) = 0 := by
    convert hn using 1
  rw [heq] at hn'
  exact hn'

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem open_induction_of_global
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (hglobal : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [FiniteDimensional ℝ H] [CompleteSpace H],
      Module.finrank ℝ H < Module.finrank ℝ E →
      ∀ q : H → F, ContDiff ℝ ∞ q →
        μ (q '' {z | ¬ Function.Surjective (fderiv ℝ q z)}) = 0) :
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [FiniteDimensional ℝ H] [CompleteSpace H],
      Module.finrank ℝ H < Module.finrank ℝ E →
      ∀ (q : H → F) (U s : Set H),
        IsOpen U → s ⊆ U → ContDiffOn ℝ ∞ q U →
        μ (q '' (s ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0 := by
  intro H hN hI hD hC hdim q U s hU hs hq
  exact SardGenuineSmoothOpenDomainLocalizationProbe.local_image_null_of_global
    μ (@hglobal H hN hI hD hC hdim) q U s hU hs hq

theorem exists_positive_rank_slice_image_null_of_global_induction
    (f : E → F) (x : E) (hf : ContDiff ℝ ∞ f)
    (hpos : 0 < Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap))
    (hlt : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) < Module.finrank ℝ F) :
    let L := fderiv ℝ f x
    let R := LinearMap.range L.toLinearMap
    let G := (R.orthogonalProjection.comp L).ker
    ∀ (μ : Measure Rᗮ) [μ.IsAddHaarMeasure],
    (∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [FiniteDimensional ℝ H] [CompleteSpace H],
      Module.finrank ℝ H < Module.finrank ℝ E →
      ∀ q : H → Rᗮ, ContDiff ℝ ∞ q →
        μ (q '' {z | ¬ Function.Surjective (fderiv ℝ q z)}) = 0) →
    ∃ e : OpenPartialHomeomorph E (R × G),
      x ∈ e.source ∧ Module.finrank ℝ G < Module.finrank ℝ E ∧ Nontrivial Rᗮ ∧
      (∀ y, (e y).1 = R.orthogonalProjection (f y)) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ r, μ ((fun z : G => Rᗮ.orthogonalProjection (f (e.symm (r,z)))) ''
        {z | (r,z) ∈ e.target ∧
          Module.finrank ℝ (LinearMap.range (fderiv ℝ f (e.symm (r,z))).toLinearMap) ≤ Module.finrank ℝ R}) = 0 := by
  dsimp only
  intro μ hμ hglobal
  obtain ⟨_, hBS⟩ := SardDerivativeRangeInheritedBorelSpaceProbe.range_orthogonal_inherited_borelSpace (fderiv ℝ f x)
  letI : BorelSpace (LinearMap.range (fderiv ℝ f x).toLinearMap)ᗮ := hBS
  exact exists_positive_rank_slice_image_null f x hf hpos hlt μ
    (@open_induction_of_global E (LinearMap.range (fderiv ℝ f x).toLinearMap)ᗮ
      _ _ _ _ _ _ hBS μ hμ hglobal)

#print axioms open_induction_of_global
#print axioms exists_positive_rank_slice_image_null_of_global_induction
#print axioms exists_positive_rank_slice_image_null
end SardPositiveRankSliceOpenInductionContractProbe
