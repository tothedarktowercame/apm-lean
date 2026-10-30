import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.PointWedgePathConnected
import ConstructionTargets.GenericPointWedgeOpenCoverComparison
import ConstructionTargets.GenericPointWedgeOverlapInclusionSquares
import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.CoefficientH0
import ConstructionTargets.RationalLefschetz

/-! Rational homology and Lefschetz-number interfaces for finite point wedges
of the polygon model of the real projective plane. -/

open CategoryTheory CategoryTheory.Limits Set Topology
open scoped ContinuousMap

noncomputable section

namespace ConstructionTargets.ProjectivePlaneWedgeRationalHomology

open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.PointWedgePathConnected
open ConstructionTargets.PointedPuncturedCircleContraction
open ConstructionTargets.StatementSurfaceModels
open ConstructionTargets.RationalLefschetz

/-- The unreduced rational homology of `X` is that of a point. -/
def RationallyPointlike (X : Type) [TopologicalSpace X] : Prop :=
  Nonempty (Homology X 0 ≅ ModuleCat.of ℚ ℚ) ∧
    ∀ k : ℕ, 0 < k → IsZero (Homology X k)

/-- A basepoint has an open neighbourhood contracted to that basepoint. -/
def HasPointedContractibleNeighbourhood
    {X : Type} [TopologicalSpace X] (x : X) : Prop :=
  ∃ U : Set X, ∃ hx : x ∈ U, IsOpen U ∧
    Nonempty (PointedContraction U ⟨x, hx⟩)

/-- L1 (LIBRARY): the polygon `aa` calculation over `ℚ`. -/
theorem realProjectivePlane_rationallyPointlike :
    RationallyPointlike RealProjectivePlane := by
  sorry

/-- L2: the polygon quotient is path connected. -/
theorem realProjectivePlane_pathConnected :
    PathConnectedSpace RealProjectivePlane := by
  sorry

/-- L3: the image of the polygon centre has a small pointed contractible
neighbourhood. -/
-- BEGIN SEAT AREA
theorem surfacePoint_hasPointedContractibleNeighbourhood :
    HasPointedContractibleNeighbourhood (surfacePoint false 1) := by
  sorry
-- END SEAT AREA

/-- L4 (LIBRARY): rational Mayer--Vietoris for a point wedge.  The local
hypotheses rule out wild wedges such as the Hawaiian earring. -/
theorem wedge_rationallyPointlike
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y)
    (hX : RationallyPointlike X) (hY : RationallyPointlike Y)
    (hnX : HasPointedContractibleNeighbourhood x₀)
    (hnY : HasPointedContractibleNeighbourhood y₀) :
    RationallyPointlike (Wedge x₀ y₀) := by
  sorry

/-- L5: pointed contractible neighbourhoods persist at the point of a
binary wedge. -/
theorem wedgePoint_hasPointedContractibleNeighbourhood
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y)
    (hnX : HasPointedContractibleNeighbourhood x₀)
    (hnY : HasPointedContractibleNeighbourhood y₀) :
    HasPointedContractibleNeighbourhood (quotientMap x₀ y₀ (.inl x₀)) := by
  sorry

/-- L6: every endomorphism acts identically on one-dimensional `H₀` of a
path-connected space. -/
theorem induced_zero_eq_id
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (e : Homology X 0 ≅ ModuleCat.of ℚ ℚ) (f : C(X, X)) :
    (induced f 0).hom = LinearMap.id := by
  open ConstructionTargets.CoefficientH0 in
    letI : FiniteDimensional ℚ (Homology X 0) :=
      Module.Finite.equiv e.toLinearEquiv.symm
    let ε : Homology X 0 ⟶ ModuleCat.of ℚ ℚ := h0Augmentation ℚ
    let p : X := Classical.choice inferInstance
    have hsurj : Function.Surjective ε := by
      intro a
      refine ⟨singularVertexH0Class ℚ p a, ?_⟩
      exact congrArg (fun g => g a)
        (singularVertexH0Class_comp_h0Augmentation ℚ p)
    have hdim : Module.finrank ℚ (Homology X 0) =
        Module.finrank ℚ (ModuleCat.of ℚ ℚ) := by
      simpa using e.toLinearEquiv.finrank_eq
    have hinj : Function.Injective ε :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
    letI : Mono ε := (ModuleCat.mono_iff_injective ε).2 hinj
    have hcat : (induced f 0) ≫ ε = (𝟙 _) ≫ ε := by
      rw [Category.id_comp]
      change HomologicalComplex.homologyMap
          (singularPostcomposition ℚ f) 0 ≫ ε = ε
      exact h0Augmentation_naturality ℚ f
    have h := (cancel_mono ε).1 hcat
    exact congrArg (fun g => g.hom) h

/-- A path-connected rational homology point has Lefschetz number one for
every self-map. -/
theorem lefschetzNumber_one_of_rationallyPointlike
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (hX : RationallyPointlike X) :
    ∀ f : C(X, X), HasLefschetzNumber f 1 := by
  intro f
  obtain ⟨e⟩ := hX.1
  letI : FiniteDimensional ℚ (Homology X 0) :=
    Module.Finite.equiv e.toLinearEquiv.symm
  have hfd : ∀ k, FiniteDimensional ℚ (Homology X k) := by
    intro k
    by_cases hk : k = 0
    · subst k
      infer_instance
    · letI : Subsingleton (Homology X k) :=
        ModuleCat.subsingleton_of_isZero (hX.2 k (Nat.pos_of_ne_zero hk))
      exact Module.Finite.of_surjective (0 : ℚ →ₗ[ℚ] Homology X k)
        (fun x ↦ ⟨0, Subsingleton.elim _ _⟩)
  refine ⟨hfd, 0, ?_, ?_⟩
  · intro k hk
    exact ModuleCat.subsingleton_of_isZero (hX.2 k hk)
  · simp only [Nat.zero_add, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, pow_zero, one_mul]
    rw [induced_zero_eq_id e f, LinearMap.trace_id]
    have hrank : Module.finrank ℚ (Homology X 0) = 1 := by
      simpa using e.toLinearEquiv.finrank_eq
    simp [hrank]

/-- The standard twofold projective-plane wedge is rationally pointlike. -/
theorem projectivePlaneWedge_rationallyPointlike :
    RationallyPointlike ProjectivePlaneWedge := by
  exact wedge_rationallyPointlike _ _
    realProjectivePlane_rationallyPointlike
    realProjectivePlane_rationallyPointlike
    surfacePoint_hasPointedContractibleNeighbourhood
    surfacePoint_hasPointedContractibleNeighbourhood

/-- Its wedge point has the same local regularity, allowing iteration. -/
theorem projectivePlaneWedge_pointedNeighbourhood :
    HasPointedContractibleNeighbourhood
      (quotientMap (surfacePoint false 1) (surfacePoint false 1)
        (.inl (surfacePoint false 1))) := by
  exact wedgePoint_hasPointedContractibleNeighbourhood _ _
    surfacePoint_hasPointedContractibleNeighbourhood
    surfacePoint_hasPointedContractibleNeighbourhood

end ConstructionTargets.ProjectivePlaneWedgeRationalHomology
