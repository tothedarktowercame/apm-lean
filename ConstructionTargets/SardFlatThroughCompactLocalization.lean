import ConstructionTargets.SardHigherJetLocusDecomposition

open Metric Set

namespace SardFlatThroughCompactLocalizationProbe

/-- On a compact localized source, global smoothness makes the exact
`flatThrough` locus compact and preserves any containing closed-ball bound. -/
theorem flatThrough_isCompact_and_bounded
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (K : Set E) (k : ℕ) (hK : IsCompact K)
    (hf : ContDiff ℝ k f) (z : E) (R : ℝ) (hbounded : K ⊆ closedBall z R) :
    IsCompact (SardHigherJetLocusDecompositionProbe.flatThrough f K k) ∧
      SardHigherJetLocusDecompositionProbe.flatThrough f K k ⊆ closedBall z R := by
  let Z : Set E := {x | ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0}
  have hZ : IsClosed Z := by
    rw [show Z = ⋂ i : ℕ, if 1 ≤ i ∧ i ≤ k
        then {x | iteratedFDeriv ℝ i f x = 0} else Set.univ by
      ext x
      simp [Z]]
    apply isClosed_iInter
    intro i
    split_ifs with hi
    · exact isClosed_eq (hf.continuous_iteratedFDeriv (mod_cast hi.2)) continuous_const
    · exact isClosed_univ
  have heq : SardHigherJetLocusDecompositionProbe.flatThrough f K k = K ∩ Z := by
    ext x
    simp [SardHigherJetLocusDecompositionProbe.flatThrough, Z]
  constructor
  · rw [heq]
    exact hK.inter_right hZ
  · intro x hx
    exact hbounded hx.1

#print axioms flatThrough_isCompact_and_bounded
end SardFlatThroughCompactLocalizationProbe
