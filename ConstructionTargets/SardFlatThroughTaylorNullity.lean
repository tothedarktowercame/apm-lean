import ConstructionTargets.SardMultivariableTaylorCoveringNullity
import ConstructionTargets.SardHigherJetLocusDecomposition

open Metric Set MeasureTheory
open scoped ENNReal NNReal

namespace SardFlatThroughTaylorNullityProbe

/-- The multivariable Taylor nullity theorem applies directly to the exact
`flatThrough` locus once its compactness and inherited bound are supplied. -/
theorem flatThrough_image_volume_eq_zero
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (f : E → F) (K : Set E) (k : ℕ)
    (hflatCompact : IsCompact (SardHigherJetLocusDecompositionProbe.flatThrough f K k))
    (z : E) (R : ℝ)
    (hbounded : SardHigherJetLocusDecompositionProbe.flatThrough f K k ⊆ closedBall z R)
    (d : ℕ) (hd : 0 < d)
    (hexp : (k + 1) * Module.finrank ℝ F = Module.finrank ℝ E + d)
    (hf : ContDiff ℝ (k + 1) f)
    (hk0 : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ 0)
    (hkt : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ ⊤)
    (q : ℝ≥0) (hq0 : 0 < q) (hq1 : q < 1) :
    volume (f '' SardHigherJetLocusDecompositionProbe.flatThrough f K k) = 0 := by
  exact smooth_flat_locus_image_volume_eq_zero f
    (SardHigherJetLocusDecompositionProbe.flatThrough f K k)
    hflatCompact z R hbounded k d hd hexp hf
    (fun a ha i hi1 hik => ha.2 i hi1 hik) hk0 hkt q hq0 hq1

#print axioms flatThrough_image_volume_eq_zero
end SardFlatThroughTaylorNullityProbe
