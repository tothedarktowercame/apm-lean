import ConstructionTargets.OrientedSimplicialChains
import ConstructionTargets.GeometricSimplicialSubdivision
import ConstructionTargets.LefschetzCompactPolyhedron

/-! Concrete chain maps used in the finite-polyhedron Lefschetz argument. -/
open Set CategoryTheory
open ConstructionTargets.OrientedSimplicialChains
open ConstructionTargets.RationalLefschetz

noncomputable section
namespace ConstructionTargets.SimplicialChainMaps

abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev GSC (n : ℕ) := Geometry.SimplicialComplex ℝ (Euc n)

/-- The parity of the inversions created by applying `h` to the increasing
vertices of `s`.  This definition is meaningful even when `h` has collisions;
the vertex-chain specification uses it only in the injective case. -/
def sortingSign {n m : ℕ} (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    (s : Finset (Euc n)) (h : Euc n → Euc m) : ℚ :=
  (-1 : ℚ) ^ ((Finset.univ.filter fun ij : Fin s.card × Fin s.card =>
    ij.1 < ij.2 ∧
      h ((s.1.sort on.le).getD ij.1 0) > h ((s.1.sort on.le).getD ij.2 0)).card)

/-- Generator formula for the ordered-face map of a simplicial vertex map.
It is zero on a collapsed face and otherwise is the image face with sorting sign. -/
def IsVertexChainMap {n m : ℕ} (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    (K : GSC n) (L : GSC m) (h : Euc n → Euc m)
    (hm : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat L k) : Prop :=
  ∀ k (s : FaceIndex K k),
    if hinj : (s.1.image h).card = k + 1 then
      ∃ t : FaceIndex L k, t.1 = s.1.image h ∧
        hm k (Finsupp.single s 1) = Finsupp.single t (sortingSign on om s.1 h)
    else hm k (Finsupp.single s 1) = 0

/-- A face of `K'` is carried by an old face when all its vertices lie in it. -/
def IsCarriedBy {n : ℕ} (K K' : GSC n) (u : Finset (Euc n)) (s : Finset (Euc n)) : Prop :=
  u ∈ K'.faces ∧ s ∈ K.faces ∧ (u : Set (Euc n)) ⊆ s

/-- Generator-level subdivision formula: coefficients are signed flag simplices,
and every occurring simplex is carried by the source face.  `IsFlagSimplex`
records the strict chain of old faces whose barycenters form `u`. -/
def IsFlagSimplex {n : ℕ} (K K' : GSC n) (s u : Finset (Euc n)) : Prop :=
  ∃ c : Finset (Finset (Euc n)),
    GeometricSimplicialSubdivision.IsStrictFaceChain K c ∧
    (∀ t ∈ c, (t : Set (Euc n)) ⊆ s) ∧ u = c.image GeometricSimplicialSubdivision.barycenter

/-- The vertex introduced at a member of a flag.  The `getD` makes the formula
total off genuine maximal flags; on a flag contributing to a `k`-simplex the
difference is a singleton. -/
def flagNewVertex {n : ℕ} (o : LinearOrder (Euc n))
    (c : Finset (Finset (Euc n))) (t : Finset (Euc n)) : Euc n :=
  ((t \ c.biUnion (fun u => if u ⊂ t then u else ∅)).1.sort o.le).getD 0 0

/-- Closed orientation formula for a flag: order the faces by inclusion and
take the inversion parity of the successive newly introduced old vertices. -/
def flagSign {n : ℕ} (o : LinearOrder (Euc n))
    (c : Finset (Finset (Euc n))) : ℚ :=
  (-1 : ℚ) ^ ((c ×ˢ c).filter fun tu =>
    tu.1 ⊂ tu.2 ∧ flagNewVertex o c tu.1 > flagNewVertex o c tu.2).card

def IsSubdivisionChainMap {n : ℕ} (o : LinearOrder (Euc n)) (K K' : GSC n)
    (sd : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat K' k) : Prop := by
  classical
  exact ∀ k (s : FaceIndex K k), ∃ z : FaceModule K' k,
    sd k (Finsupp.single s 1) = z ∧
    ∀ u, z u = ∑ c ∈ s.1.powerset.powerset,
      if GeometricSimplicialSubdivision.IsStrictFaceChain K c ∧
          u.1 = c.image GeometricSimplicialSubdivision.barycenter then
        flagSign o c else 0

/-- The canonical barycentric step, with all three construction proofs fixed. -/
def barycentricStep {n : ℕ} (K : GSC n) : GSC n :=
  GeometricSimplicialSubdivision.barycentricSubdivision K
    (GeometricSimplicialSubdivision.barycentricFaces_affineIndependent K)
    (GeometricSimplicialSubdivision.barycentricFaces_isLowerSet K)
    (GeometricSimplicialSubdivision.barycentricFaces_inter_subset K)

def homeomorphMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : C(X,Y) := ⟨e, e.continuous⟩

def CarrierAvoidingVertexMap {n : ℕ} (K K' : GSC n) (h : Euc n → Euc n) : Prop :=
  ∀ s ∈ K.faces, ∀ u ∈ K'.faces, (u : Set (Euc n)) ⊆ s →
    Disjoint (u.image h : Set (Euc n)) s

theorem vertexChainMap_exists {n m : ℕ} (on : LinearOrder (Euc n))
    (om : LinearOrder (Euc m)) (K : GSC n) (L : GSC m) (h : Euc n → Euc m)
    (hh : GeometricSimplicialSubdivision.IsSimplicialVertexMap K L h) :
    ∃ hm : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat L k,
      IsVertexChainMap on om K L h hm := by
  sorry

theorem vertexChainMap_commutes {n m : ℕ} (on : LinearOrder (Euc n))
    (om : LinearOrder (Euc m)) (K : GSC n) (L : GSC m) (h : Euc n → Euc m)
    (dK : ∀ k, FaceModuleCat K (k+1) ⟶ FaceModuleCat K k)
    (dL : ∀ k, FaceModuleCat L (k+1) ⟶ FaceModuleCat L k)
    (hm : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat L k)
    (hdK : IsSignedDeletion on K dK) (hdL : IsSignedDeletion om L dL)
    (hhm : IsVertexChainMap on om K L h hm) :
    ∀ k, hm (k+1) ≫ dL k = dK k ≫ hm k := by
  sorry

theorem barycentricSubdivisionChainMap_exists {n : ℕ} (o : LinearOrder (Euc n))
    (K : GSC n) (hi hd hx) :
    ∃ sd : ∀ k, FaceModuleCat K k ⟶
        FaceModuleCat (GeometricSimplicialSubdivision.barycentricSubdivision K hi hd hx) k,
      IsSubdivisionChainMap o K
        (GeometricSimplicialSubdivision.barycentricSubdivision K hi hd hx) sd := by
  sorry

theorem subdivisionChainMap_commutes {n : ℕ} (o : LinearOrder (Euc n))
    (K K' : GSC n) (dK : ∀ k, FaceModuleCat K (k+1) ⟶ FaceModuleCat K k)
    (dK' : ∀ k, FaceModuleCat K' (k+1) ⟶ FaceModuleCat K' k)
    (sd : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat K' k)
    (hdK : IsSignedDeletion o K dK) (hdK' : IsSignedDeletion o K' dK')
    (hsd : IsSubdivisionChainMap o K K' sd) :
    ∀ k, sd (k+1) ≫ dK' k = dK k ≫ sd k := by
  sorry

theorem vertexChainMap_affineComparison_square {n m : ℕ} (on : LinearOrder (Euc n))
    (om : LinearOrder (Euc m)) (K : GSC n) (L : GSC m) (h : Euc n → Euc m)
    (hh : GeometricSimplicialSubdivision.IsSimplicialVertexMap K L h)
    (f : C(K.space, L.space))
    (hf : ∀ s ∈ K.faces, ∀ x : K.space, (x : Euc n) ∈ convexHull ℝ (s : Set _) →
      (f x : Euc m) ∈ convexHull ℝ (s.image h : Set _))
    (hm : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat L k)
    (hhm : IsVertexChainMap on om K L h hm)
    (dK : ∀ k, FaceModuleCat K (k+1) ⟶ FaceModuleCat K k)
    (dL : ∀ k, FaceModuleCat L (k+1) ⟶ FaceModuleCat L k)
    (hddK : ∀ k, dK (k+1) ≫ dK k = 0) (hddL : ∀ k, dL (k+1) ≫ dL k = 0)
    (hmH : ChainComplex.of _ dK hddK ⟶ ChainComplex.of _ dL hddL)
    (hmH_f : ∀ k, hmH.f k = hm k)
    (cmpK : ∀ k, FaceModuleCat K k ⟶ (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (cmpL : ∀ k, FaceModuleCat L k ⟶ (CoefficientH0.SingularChains ℚ (TopCat.of L.space)).X k)
    (hcmpK : IsAffineComparison K cmpK) (hcmpL : IsAffineComparison L cmpL)
    (cmpKH : ChainComplex.of _ dK hddK ⟶
      CoefficientH0.SingularChains ℚ (TopCat.of K.space))
    (cmpLH : ChainComplex.of _ dL hddL ⟶
      CoefficientH0.SingularChains ℚ (TopCat.of L.space))
    (cmpKH_f : ∀ k, cmpKH.f k = cmpK k) (cmpLH_f : ∀ k, cmpLH.f k = cmpL k) :
    ∀ k,
      HomologicalComplex.homologyMap hmH k ≫ HomologicalComplex.homologyMap cmpLH k =
      HomologicalComplex.homologyMap cmpKH k ≫ induced f k := by
  sorry

theorem subdivision_affineComparison_square {n : ℕ} (o : LinearOrder (Euc n))
    (K K' : GSC n) (hspace : K.space = K'.space)
    (sd : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat K' k)
    (hsd : IsSubdivisionChainMap o K K' sd)
    (dK : ∀ k, FaceModuleCat K (k+1) ⟶ FaceModuleCat K k)
    (dK' : ∀ k, FaceModuleCat K' (k+1) ⟶ FaceModuleCat K' k)
    (hddK : ∀ k, dK (k+1) ≫ dK k = 0) (hddK' : ∀ k, dK' (k+1) ≫ dK' k = 0)
    (sdH : ChainComplex.of _ dK hddK ⟶ ChainComplex.of _ dK' hddK')
    (sdH_f : ∀ k, sdH.f k = sd k)
    (cmpK : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (cmpK' : ∀ k, FaceModuleCat K' k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K'.space)).X k)
    (hcmpK : IsAffineComparison K cmpK) (hcmpK' : IsAffineComparison K' cmpK')
    (cmpKH : ChainComplex.of _ dK hddK ⟶
      CoefficientH0.SingularChains ℚ (TopCat.of K.space))
    (cmpK'H : ChainComplex.of _ dK' hddK' ⟶
      CoefficientH0.SingularChains ℚ (TopCat.of K'.space))
    (cmpKH_f : ∀ k, cmpKH.f k = cmpK k) (cmpK'H_f : ∀ k, cmpK'H.f k = cmpK' k) :
    ∀ k,
      HomologicalComplex.homologyMap sdH k ≫ HomologicalComplex.homologyMap cmpK'H k =
      HomologicalComplex.homologyMap cmpKH k ≫
        induced (Homeomorph.setCongr hspace) k := by
  sorry

theorem composite_zero_diagonal {n : ℕ} (o : LinearOrder (Euc n)) (K K' : GSC n)
    (h : Euc n → Euc n) (sd : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat K' k)
    (hm : ∀ k, FaceModuleCat K' k ⟶ FaceModuleCat K k)
    (hsd : IsSubdivisionChainMap o K K' sd)
    (hhm : IsVertexChainMap o o K' K h hm)
    (havoid : CarrierAvoidingVertexMap K K' h) :
    ∀ k (s : FaceIndex K k), (hm k (sd k (Finsupp.single s 1))) s = 0 := by
  sorry

/-- LIBRARY: geometric preparation retaining the fact that the fine complex is
an iterated barycentric subdivision, together with a carrier-avoiding simplicial
approximation homotopic to `g`. -/
theorem exists_fine_iterated_approximation
    {X : Type} [TopologicalSpace X] {n : ℕ} (K : GSC n) (hK : K.faces.Finite)
    (e : X ≃ₜ K.space) (g : C(X,X)) (δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ s ∈ K.faces, ∀ x : X, (e x : Euc n) ∈ convexHull ℝ (s : Set _) →
      ∀ y ∈ convexHull ℝ (s : Set _), δ ≤ dist (e (g x) : Euc n) y) :
    ∃ p m : ℕ, ∃ hL : ((barycentricStep^[p]) K).space = K.space,
      ((barycentricStep^[p]) K).faces.Finite ∧
      ∃ hspace : ((barycentricStep^[m]) ((barycentricStep^[p]) K)).space =
          ((barycentricStep^[p]) K).space,
        ((barycentricStep^[m]) ((barycentricStep^[p]) K)).faces.Finite ∧
      ∃ h : Euc n → Euc n,
        GeometricSimplicialSubdivision.IsSimplicialVertexMap
          ((barycentricStep^[m]) ((barycentricStep^[p]) K)) ((barycentricStep^[p]) K) h ∧
        CarrierAvoidingVertexMap ((barycentricStep^[p]) K)
          ((barycentricStep^[m]) ((barycentricStep^[p]) K)) h ∧
        ∀ v ∈ ((barycentricStep^[m]) ((barycentricStep^[p]) K)).vertices,
          (fun x : ((barycentricStep^[m]) ((barycentricStep^[p]) K)).space =>
            (e.trans (Homeomorph.setCongr hL.symm)) (g ((e.trans
              (Homeomorph.setCongr hL.symm)).symm (Homeomorph.setCongr hspace x)))) ''
              ((Subtype.val : _ → Euc n) ⁻¹'
                GeometricSimplicialSubdivision.openStar
                  ((barycentricStep^[m]) ((barycentricStep^[p]) K)) v) ⊆
            (Subtype.val : ((barycentricStep^[p]) K).space → Euc n) ⁻¹'
              GeometricSimplicialSubdivision.openStar ((barycentricStep^[p]) K) (h v) := by
  sorry

/-- LIBRARY: assemble explicit commuting subdivision and vertex maps, their
comparison squares and quasi-isomorphism into the packaged finite chain model. -/
-- BEGIN SEAT AREA
theorem oriented_model_of_explicit_maps
    {X : Type} [TopologicalSpace X] {n : ℕ} (K K' : GSC n)
    (m : ℕ) (hiter : K' = (barycentricStep^[m]) K)
    (hK : K.faces.Finite) (hK' : K'.faces.Finite) (hspace : K'.space = K.space)
    (e : X ≃ₜ K.space) (g : C(X,X)) (h : Euc n → Euc n)
    (hh : GeometricSimplicialSubdivision.IsSimplicialVertexMap K' K h)
    (havoid : CarrierAvoidingVertexMap K K' h)
    (f : C(K'.space, K.space))
    (hf : ∀ s ∈ K'.faces, ∀ x : K'.space,
      (x : Euc n) ∈ convexHull ℝ (s : Set _) →
      (f x : Euc n) ∈ convexHull ℝ (s.image h : Set _))
    (hhom : ContinuousMap.Homotopic
      ((homeomorphMap e).comp
        (g.comp ((homeomorphMap e.symm).comp
          (homeomorphMap (Homeomorph.setCongr hspace : K'.space ≃ₜ K.space))))) f) :
    ∃ M : LefschetzCompactPolyhedron.FiniteChainEndomorphism,
      (∀ k, M.chainTrace k = 0) ∧ LefschetzCompactPolyhedron.HomologyModels M g := by
  sorry
-- END SEAT AREA

/-- Adapter with exactly the statement consumed by `LefschetzCompactPolyhedron`. -/
theorem exists_carrier_avoiding_oriented_chain_model
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (e : X ≃ₜ K.space) (g : C(X, X))
    (δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ s ∈ K.faces, ∀ x : X,
      (e x : EuclideanSpace ℝ (Fin n)) ∈ convexHull ℝ (s : Set _) →
      ∀ y ∈ convexHull ℝ (s : Set _),
        δ ≤ dist (e (g x) : EuclideanSpace ℝ (Fin n)) y) :
    ∃ M : LefschetzCompactPolyhedron.FiniteChainEndomorphism,
      (∀ k, M.chainTrace k = 0) ∧
        LefschetzCompactPolyhedron.HomologyModels M g := by
  obtain ⟨p, m, hL, hLfin, hspace, hK', h, hh, hav, hstar⟩ :=
    exists_fine_iterated_approximation K hK e g δ hδ hmargin
  let L := (barycentricStep^[p]) K
  let K' := (barycentricStep^[m]) L
  let eL : X ≃ₜ L.space := e.trans (Homeomorph.setCongr hL.symm)
  obtain ⟨f, _hvertex, hf⟩ :=
    GeometricSimplicialSubdivision.exists_inducedContinuousMap K' hK' L h hh
  exact oriented_model_of_explicit_maps L K' m rfl hLfin hK' hspace eL g h hh hav f hf
    (GeometricSimplicialSubdivision.inducedMap_homotopic_of_star_condition
      K' L _ f h hstar hf)
end ConstructionTargets.SimplicialChainMaps

#print axioms ConstructionTargets.SimplicialChainMaps.exists_carrier_avoiding_oriented_chain_model
