import ConstructionTargets.SardFirstDerivativeProjectedChartInverseFormula

open Filter
open scoped Topology
noncomputable section
namespace SardFirstDerivativeProjectedChartExplicitNeighborhoodProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The eventual inverse identities of the projected rank chart may be retained
on one explicit neighborhood of the projected base coordinate. -/
theorem exists_projected_localRankNormalForm_with_explicit_inverse_neighborhood
    (f : E → F) (x : E) (L : E →L[ℝ] F) (hf : HasStrictFDerivAt f L x) :
    let R := LinearMap.range L.toLinearMap
    let A : E →L[ℝ] R := R.orthogonalProjection.comp L
    let G := A.ker
    ∃ e : OpenPartialHomeomorph E (R × G),
      x ∈ e.source ∧
      (e : E → R × G) =
        (fun y => (R.orthogonalProjection (f y), G.orthogonalProjection y)) ∧
      ∃ V : Set (R × G),
        V ∈ 𝓝 (R.orthogonalProjection (f x), G.orthogonalProjection x) ∧
        ∀ p ∈ V,
          R.orthogonalProjection (f (e.symm p)) = p.1 ∧
            G.orthogonalProjection (e.symm p) = p.2 := by
  dsimp only
  obtain ⟨e, hx, he, hinv⟩ :=
    SardFirstDerivativeProjectedChartInverseFormulaProbe.exists_projected_localRankNormalForm_with_inverse_formula
      f x L hf
  refine ⟨e, hx, he, ?_⟩
  exact ⟨_, hinv, fun _ hp => hp⟩

#print axioms exists_projected_localRankNormalForm_with_explicit_inverse_neighborhood

end SardFirstDerivativeProjectedChartExplicitNeighborhoodProbe
