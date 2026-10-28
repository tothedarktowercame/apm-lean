import ConstructionTargets.GeometricSimplicialSubdivision
import ConstructionTargets.CoefficientSimplicialChainFinsuppRange
import ConstructionTargets.CoefficientSingularSubdivision
import ConstructionTargets.CoefficientBarycentricNaturality
import ConstructionTargets.CoefficientAffineNaturality
import ConstructionTargets.RationalLefschetz

/-! Concrete, staged ordered-face chain blueprint. -/
open Set CategoryTheory
noncomputable section
namespace ConstructionTargets.OrientedSimplicialChains

open SingularSubdivision

abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The genuine degree-`k` basis: faces with `k+1` vertices.  Their canonical
orientation is the increasing order inherited from the ambient lexicographic order. -/
def FaceIndex {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n)) (k : ℕ) :=
  {s : Finset (Euc n) // s ∈ K.faces ∧ s.card = k + 1}

abbrev FaceModule {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n)) (k : ℕ) :=
  FaceIndex K k →₀ ℚ

abbrev FaceModuleCat {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n)) (k : ℕ) :=
  ModuleCat.of ℚ (FaceModule K k)

/-- Generator-level specification of the signed deletion differential. -/
def IsSignedDeletion {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k) : Prop :=
  ∀ k (s : FaceIndex K (k + 1)), ∃ z : FaceModule K k,
    d k (Finsupp.single s 1) = z ∧ ∀ t, z t = ∑ v ∈ s.1,
      if s.1.erase v = t.1 then (-1 : ℚ) ^ ((s.1.sort o.le).idxOf v) else 0

/-- Generator-level specification of canonical affine realization.  It pins
down the map and rules out the arbitrary-comparison defect of the old model. -/
def IsAffineComparison {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (cmp : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k) : Prop :=
  ∀ k (s : FaceIndex K k), ∃ σ : SingularSimplex (TopCat.of K.space) k,
    cmp k (Finsupp.single s 1) = (CoefficientH0.singularGenerator ℚ _ k σ) 1 ∧
    Set.range (continuousMapOfSingularSimplex k σ) =
      (fun x : K.space => (x : Euc n)) ⁻¹' convexHull ℝ (s.1 : Set (Euc n))

/-! Stage 1: raw data and independent obligations. -/

theorem signedDeletion_exists {n : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n)) :
    ∃ d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k,
      IsSignedDeletion o K d := by sorry

theorem signedDeletion_sq_zero {n : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) : ∀ k, d (k + 1) ≫ d k = 0 := by sorry

theorem faceModule_finiteDimensional {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite) :
    ∀ k, FiniteDimensional ℚ (FaceModule K k) := by sorry

theorem faceModule_zero_above {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite) :
    ∃ b, ∀ k, b < k → Subsingleton (FaceModule K k) := by sorry

theorem affineComparison_exists_and_commutes {n : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) :
    ∃ cmp : ∀ k, FaceModuleCat K k ⟶
        (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k,
      IsAffineComparison K cmp ∧ ∀ k,
        cmp (k + 1) ≫ (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 1) k =
          d k ≫ cmp k := by sorry

/-! Stage 2.  `ChainComplex.of` occurs only with the stage-one square-zero
conclusion supplied explicitly, so these declarations acquire no hidden axiom. -/

theorem orderedFace_singular_quasiIso {n : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (cmp : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (hcmp : IsAffineComparison K cmp)
    (hchain : ∀ k, cmp (k + 1) ≫
        (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 1) k =
      d k ≫ cmp k) :
    ∀ k, Function.Bijective
      (HomologicalComplex.homologyMap
        (ChainComplex.ofHom _ _ hdd _ _
          (fun k => (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d_comp_d
            (k + 2) (k + 1) k) cmp hchain) k).hom := by
  sorry

end ConstructionTargets.OrientedSimplicialChains
