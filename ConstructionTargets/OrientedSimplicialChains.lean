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
      IsSignedDeletion o K d := by
  let b : ∀ k, FaceIndex K (k + 1) → FaceModule K k := fun k s =>
    ∑ v : s.1, Finsupp.single
      (⟨s.1.erase v.1,
        K.down_closed s.2.1 (Finset.erase_subset v.1 s.1) (by
          rw [Finset.nonempty_iff_ne_empty]
          intro h
          have hc := Finset.card_erase_of_mem v.2
          rw [h, Finset.card_empty, s.2.2] at hc
          omega),
        by
          rw [Finset.card_erase_of_mem v.2, s.2.2]
          omega⟩ : FaceIndex K k)
      ((-1 : ℚ) ^ ((s.1.sort o.le).idxOf v.1))
  let d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k := fun k =>
    ModuleCat.ofHom (Finsupp.linearCombination ℚ (b k))
  refine ⟨d, ?_⟩
  intro k s
  refine ⟨b k s, ?_, ?_⟩
  · simp [d]
  · intro t
    simp only [b]
    change Finsupp.applyAddHom t _ = _
    rw [map_sum]
    change (∑ v : s.1, Finsupp.single
      (⟨s.1.erase v.1,
        K.down_closed s.2.1 (Finset.erase_subset v.1 s.1) (by
          rw [Finset.nonempty_iff_ne_empty]
          intro h
          have hc := Finset.card_erase_of_mem v.2
          rw [h, Finset.card_empty, s.2.2] at hc
          omega),
        by rw [Finset.card_erase_of_mem v.2, s.2.2]; omega⟩ : FaceIndex K k)
      ((-1 : ℚ) ^ ((s.1.sort o.le).idxOf v.1)) t) = _
    simp_rw [Finsupp.single_apply]
    rw [← Finset.sum_attach s.1]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [Subtype.ext_iff]

theorem signedDeletion_sq_zero_aux_generator {n : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (k : ℕ) (s : FaceIndex K (k + 2)) :
    d k (d (k + 1) (Finsupp.single s 1)) = 0 := by
  sorry

theorem signedDeletion_sq_zero {n : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) : ∀ k, d (k + 1) ≫ d k = 0 := by
  intro k
  ext x t
  change d k (d (k + 1) (Finsupp.single x 1)) t = 0
  rw [signedDeletion_sq_zero_aux_generator o K d hd k x]
  rfl

theorem faceModule_finiteDimensional {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite) :
    ∀ k, FiniteDimensional ℚ (FaceModule K k) := by
  intro k
  letI : Finite K.faces := hK
  letI : Finite (FaceIndex K k) :=
    Finite.of_injective
      (fun s : FaceIndex K k => (⟨s.1, s.2.1⟩ : K.faces))
      (by
        intro s t h
        exact Subtype.ext (congrArg (fun x : K.faces => x.1) h))
  infer_instance

theorem faceModule_zero_above {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite) :
    ∃ b, ∀ k, b < k → Subsingleton (FaceModule K k) := by
  classical
  let F : Finset (Finset (Euc n)) := hK.toFinset
  let U : Finset (Euc n) := F.biUnion id
  refine ⟨U.card, fun k hk => ?_⟩
  have hempty : IsEmpty (FaceIndex K k) :=
    ⟨fun s => by
      have hsF : s.1 ∈ F := by
        simpa [F] using s.2.1
      have hsub : s.1 ⊆ U := by
        intro x hx
        simp only [U, Finset.mem_biUnion]
        exact ⟨s.1, hsF, hx⟩
      have hcard : s.1.card ≤ U.card := Finset.card_le_card hsub
      have heq : s.1.card = k + 1 := s.2.2
      omega⟩
  letI := hempty
  infer_instance

theorem affineComparison_exists_and_commutes {n : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) :
    ∃ cmp : ∀ k, FaceModuleCat K k ⟶
        (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k,
      IsAffineComparison K cmp ∧ ∀ k,
        cmp (k + 1) ≫ (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 1) k =
          d k ≫ cmp k := by
  sorry

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
