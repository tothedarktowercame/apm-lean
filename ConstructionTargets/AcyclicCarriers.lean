import ConstructionTargets.OrientedSimplicialChains
import ConstructionTargets.ProjectivePlaneWedgeRationalHomology
import Mathlib.Analysis.Convex.Contractible

/-!
# Acyclic carriers for ordered simplicial chains

This file isolates the acyclic-carrier input used to compare two affine
realizations of the ordered-face complex.
-/

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.AcyclicCarriers

open ConstructionTargets.OrientedSimplicialChains
open ConstructionTargets.ProjectivePlaneWedgeRationalHomology
open SingularSubdivision

abbrev SingularQChains {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n)) :=
  CoefficientH0.SingularChains ℚ (TopCat.of K.space)

/-- A production singular chain is carried by the convex hull of `s` if it
has a finite generator presentation all of whose simplices land in that hull.
The existential presentation makes this definition independent of a choice of
coordinates for the categorical coproduct defining singular chains. -/
def FaceCarriedChain {n k : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (s : Finset (Euc n)) (z : (SingularQChains K).X k) : Prop :=
  ∃ (m : ℕ) (a : Fin m → ℚ)
      (σ : Fin m → SingularSimplex (TopCat.of K.space) k),
    z = ∑ i, (CoefficientH0.singularGenerator ℚ _ k (σ i)) (a i) ∧
    ∀ i, Set.range (continuousMapOfSingularSimplex k (σ i)) ⊆
      (fun x : K.space => (x : Euc n)) ⁻¹' convexHull ℝ (s : Set (Euc n))

/-- The convex carrier of every (nonempty) face has the rational homology of
a point.  The proof contracts the subtype `convexHull ℝ s` and applies
`rationallyPointlike_of_homotopyEquiv` and `rationallyPointlike_unit`. -/
theorem faceHull_rationallyPointlike {n k : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (s : FaceIndex K k) :
    RationallyPointlike (convexHull ℝ (s.1 : Set (Euc n))) := by
  have hs : (s.1 : Set (Euc n)).Nonempty := by
    rw [Finset.coe_nonempty]
    apply Finset.card_pos.mp
    rw [s.2.2]
    omega
  have hh : (convexHull ℝ (s.1 : Set (Euc n))).Nonempty :=
    convexHull_nonempty_iff.mpr hs
  letI : ContractibleSpace (convexHull ℝ (s.1 : Set (Euc n))) :=
    (convex_convexHull ℝ (s.1 : Set (Euc n))).contractibleSpace hh
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit
    (convexHull ℝ (s.1 : Set (Euc n)))
  exact rationallyPointlike_of_homotopyEquiv e rationallyPointlike_unit

/-- Taking the singular boundary preserves the face carrier.  This is the
generator boundary formula together with the fact that restricting a simplex
to a standard face does not enlarge its range. -/
theorem faceCarriedChain_boundary {n k : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (s : Finset (Euc n))
    (z : (SingularQChains K).X (k + 1)) (hz : FaceCarriedChain K s z) :
    FaceCarriedChain K s ((SingularQChains K).d (k + 1) k z) := by
  classical
  rcases hz with ⟨m, a, σ, rfl, hσ⟩
  let e : (Fin m × Fin (k + 2)) ≃ Fin (Fintype.card (Fin m × Fin (k + 2))) :=
    Fintype.equivFin _
  let τ : Fin (Fintype.card (Fin m × Fin (k + 2))) →
      SingularSimplex (TopCat.of K.space) k := fun j ↦
    (TopCat.toSSet.obj (TopCat.of K.space)).δ (e.symm j).2 (σ (e.symm j).1)
  let b : Fin (Fintype.card (Fin m × Fin (k + 2))) → ℚ := fun j ↦
    ((-1 : ℚ) ^ ((e.symm j).2 : ℕ)) * a (e.symm j).1
  refine ⟨_, b, τ, ?_, ?_⟩
  · simp only [map_sum]
    calc
      _ = ∑ i, (CoefficientH0.singularGenerator ℚ (TopCat.of K.space)
            (k + 1) (σ i) ≫ (SingularQChains K).d (k + 1) k) (a i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rfl
      _ = ∑ i, ∑ j : Fin (k + 2),
            (CoefficientH0.singularGenerator ℚ (TopCat.of K.space) k
              ((TopCat.toSSet.obj (TopCat.of K.space)).δ j (σ i)))
              (((-1 : ℚ) ^ (j : ℕ)) * a i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [CoefficientH0.singularGenerator_boundary]
          simp only [ModuleCat.hom_sum, LinearMap.coe_sum, Finset.sum_apply]
          apply Finset.sum_congr rfl
          intro j hj
          rw [ModuleCat.hom_smul, LinearMap.smul_apply]
          rw [← Int.cast_smul_eq_zsmul ℚ]
          rw [← map_smul]
          simp
    calc
      _ = ∑ p : Fin m × Fin (k + 2),
          (CoefficientH0.singularGenerator ℚ (TopCat.of K.space) k
            ((TopCat.toSSet.obj (TopCat.of K.space)).δ p.2 (σ p.1)))
            (((-1 : ℚ) ^ (p.2 : ℕ)) * a p.1) := by
          rw [Fintype.sum_prod_type]
      _ = _ := by
        simpa [τ, b] using e.sum_comp (fun j ↦
          (CoefficientH0.singularGenerator ℚ (TopCat.of K.space) k (τ j)) (b j))
  · intro j
    let p := e.symm j
    let cσ := continuousMapOfSingularSimplex (k + 1) (σ p.1)
    have hcσ : singularSimplexOfContinuousMap (TopCat.of K.space) (k + 1) cσ =
        σ p.1 :=
      Equiv.symm_apply_apply _ _
    dsimp [τ]
    rw [← hcσ, singularSimplexOfContinuousMap_face]
    simp only [continuousMapOfSingularSimplex_ofContinuousMap]
    rintro x ⟨y, rfl⟩
    exact hσ p.1 ⟨_, rfl⟩

/-- The image of a face generator under an affine comparison is carried by
that face. -/
theorem affineComparison_generator_carried {n k : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (cmp : ∀ j, FaceModuleCat K j ⟶ (SingularQChains K).X j)
    (hcmp : IsAffineComparison K cmp) (s : FaceIndex K k) :
    FaceCarriedChain K s.1 (cmp k (Finsupp.single s 1)) := by
  rcases hcmp k s with ⟨σ, hσ, hrange⟩
  refine ⟨1, fun _ ↦ 1, fun _ ↦ σ, ?_, ?_⟩
  · simpa using hσ
  · intro i
    simpa [hrange]

/-- Carrier monotonicity: a chain carried by a subface is carried by the
containing face.  This is `convexHull_mono`. -/
theorem faceCarriedChain_mono {n k : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (s t : Finset (Euc n)) (hst : t ⊆ s) (z : (SingularQChains K).X k)
    (hz : FaceCarriedChain K t z) : FaceCarriedChain K s z := by
  rcases hz with ⟨m, a, σ, hz, hσ⟩
  refine ⟨m, a, σ, hz, fun i ↦ (hσ i).trans ?_⟩
  exact preimage_mono (convexHull_mono (by simpa using hst))

/-- Positive-degree acyclicity in the concrete carrier form needed by the
induction: a carried cycle bounds a carried chain.  Its proof lifts the finite
presentation to singular chains on the hull subtype, uses positive-degree
rational homology vanishing, and pushes the bounding chain forward. -/
theorem faceCarriedCycle_bounds {n k : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (s : FaceIndex K k)
    (hpoint : RationallyPointlike (convexHull ℝ (s.1 : Set (Euc n))))
    (z : (SingularQChains K).X k) (hz : FaceCarriedChain K s.1 z)
    (hcycle : (SingularQChains K).d k (k - 1) z = 0) (hk : 0 < k) :
    ∃ w : (SingularQChains K).X (k + 1), FaceCarriedChain K s.1 w ∧
      (SingularQChains K).d (k + 1) k w = z := by
  sorry

/-- In degree zero an affine comparison is forced on vertices: a singular
zero-simplex whose range is the singleton hull of a vertex is constant. -/
theorem affineComparison_degreeZero_eq {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (cmp₁ cmp₂ : ∀ k, FaceModuleCat K k ⟶ (SingularQChains K).X k)
    (hcmp₁ : IsAffineComparison K cmp₁) (hcmp₂ : IsAffineComparison K cmp₂) :
    cmp₁ 0 = cmp₂ 0 := by
  sorry

/-- The inductive acyclic-carrier construction.  The filling operation is an
explicit hypothesis so this leaf is independent of its topological proof.
On a basis face in degree `k`, choose a carried preimage of
`cmp₁(s) - cmp₂(s) - H(d s)` and extend linearly. -/
theorem carried_chainHomotopy_exists {n : ℕ}
    (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (cmp₁ cmp₂ : ∀ k, FaceModuleCat K k ⟶ (SingularQChains K).X k)
    (hcmp₁ : IsAffineComparison K cmp₁) (hcmp₂ : IsAffineComparison K cmp₂)
    (hchain₁ : ∀ k, cmp₁ (k + 1) ≫ (SingularQChains K).d (k + 1) k = d k ≫ cmp₁ k)
    (hchain₂ : ∀ k, cmp₂ (k + 1) ≫ (SingularQChains K).d (k + 1) k = d k ≫ cmp₂ k)
    (hzero : cmp₁ 0 = cmp₂ 0)
    (hfill : ∀ (k : ℕ) (s : FaceIndex K k) (z : (SingularQChains K).X k),
      FaceCarriedChain K s.1 z → (SingularQChains K).d k (k - 1) z = 0 →
      0 < k → ∃ w : (SingularQChains K).X (k + 1),
        FaceCarriedChain K s.1 w ∧ (SingularQChains K).d (k + 1) k w = z) :
    Nonempty (Homotopy
      (ChainComplex.ofHom _ _ hdd _ _ (fun j ↦ (SingularQChains K).d_comp_d
        (j + 2) (j + 1) j) cmp₁ hchain₁)
      (ChainComplex.ofHom _ _ hdd _ _ (fun j ↦ (SingularQChains K).d_comp_d
        (j + 2) (j + 1) j) cmp₂ hchain₂)) := by
  sorry

end ConstructionTargets.AcyclicCarriers
