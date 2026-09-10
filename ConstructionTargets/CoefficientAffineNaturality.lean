import ConstructionTargets.CoefficientAffineRealization
noncomputable section
namespace ConstructionTargets.CoefficientAffineNaturality
open CategoryTheory CategoryTheory.Limits Simplicial SingularSubdivision
variable (R : Type) [CommRing R]
def vertexMapDegree {V W : Type} (f : V → W) (n : ℕ) :
    (CoefficientVertexCone.VertexChains R V).X n ⟶ (CoefficientVertexCone.VertexChains R W).X n := by
  change (∐ fun _ : Fin (n + 1) → V ↦ ModuleCat.of R R) ⟶ _
  exact Limits.Sigma.desc fun v => CoefficientVertexCone.vertexGenerator R W n (f ∘ v)

@[simp, reassoc] theorem vertexGenerator_vertexMapDegree {V W : Type}
    (f : V → W) (n : ℕ) (v : Fin (n + 1) → V) :
    CoefficientVertexCone.vertexGenerator R V n v ≫ vertexMapDegree R f n =
      CoefficientVertexCone.vertexGenerator R W n (f ∘ v) := by
  dsimp [CoefficientVertexCone.vertexGenerator, vertexMapDegree]
  exact Limits.Sigma.ι_desc _ v

/-- Mapping vertices commutes with the ordered-vertex differential. -/
theorem vertexMapDegree_comm_d {V W : Type} (f : V → W) (n : ℕ) :
    vertexMapDegree R f (n + 1) ≫ (CoefficientVertexCone.VertexChains R W).d (n + 1) n =
      (CoefficientVertexCone.VertexChains R V).d (n + 1) n ≫ vertexMapDegree R f n := by
  apply Limits.Sigma.hom_ext
  intro v
  change (CoefficientVertexCone.vertexGenerator R V (n + 1) v ≫ vertexMapDegree R f (n + 1)) ≫ _ =
    (CoefficientVertexCone.vertexGenerator R V (n + 1) v ≫ _) ≫ vertexMapDegree R f n
  rw [vertexGenerator_vertexMapDegree R, CoefficientVertexCone.vertexGenerator_boundary R,
    CoefficientVertexCone.vertexGenerator_boundary R, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, vertexGenerator_vertexMapDegree R]
  apply Finset.sum_congr rfl
  intro i _
  congr 2

/-- Vertexwise application as a chain map. -/
def vertexMap {V W : Type} (f : V → W) : CoefficientVertexCone.VertexChains R V ⟶ CoefficientVertexCone.VertexChains R W where
  f := vertexMapDegree R f
  comm' n m h := by
    obtain rfl := h
    exact vertexMapDegree_comm_d R f m

theorem vertexRealization_affine_natural {m : ℕ} {κ : Type} [Fintype κ]
    (u : Fin (m + 1) → stdSimplex ℝ κ) (n : ℕ) :
    CoefficientAffineRealization.vertexRealizationDegree R (ι := Fin (m + 1)) n ≫
        (CoefficientH0.singularPostcomposition R (affineSimplex u)).f n =
      vertexMapDegree R (affineSimplex u) n ≫
        CoefficientAffineRealization.vertexRealizationDegree R (ι := κ) n := by
  apply Limits.Sigma.hom_ext
  intro v
  change (CoefficientVertexCone.vertexGenerator R _ n v ≫ CoefficientAffineRealization.vertexRealizationDegree R n) ≫ _ =
    (CoefficientVertexCone.vertexGenerator R _ n v ≫ vertexMapDegree R (affineSimplex u) n) ≫ _
  rw [CoefficientAffineRealization.vertexGenerator_vertexRealizationDegree R,
    vertexGenerator_vertexMapDegree R, CoefficientAffineRealization.vertexGenerator_vertexRealizationDegree R]
  dsimp [CoefficientAffineRealization.affineGenerator]
  rw [CoefficientH0.singularGenerator_singularPostcomposition R]
  rw [affineSimplex_comp_affineSimplex]
  congr 3


theorem vertexMap_id (V : Type) : vertexMap R (id : V → V) = 𝟙 _ := by
  ext n : 1
  apply Limits.Sigma.hom_ext
  intro v
  change CoefficientVertexCone.vertexGenerator R V n v ≫ vertexMapDegree R id n = _
  simp
  change _ = CoefficientVertexCone.vertexGenerator R V n v ≫ 𝟙 _
  simp

theorem vertexMap_comp {V W Z : Type} (f : V → W) (g : W → Z) :
    vertexMap R (g ∘ f) = vertexMap R f ≫ vertexMap R g := by
  ext n : 1
  apply Limits.Sigma.hom_ext
  intro v
  change CoefficientVertexCone.vertexGenerator R V n v ≫ vertexMapDegree R (g ∘ f) n =
    CoefficientVertexCone.vertexGenerator R V n v ≫ (vertexMapDegree R f n ≫ vertexMapDegree R g n)
  simp [← Category.assoc, Function.comp_assoc]

theorem realization_naturality {m : ℕ} {κ : Type} [Fintype κ]
    (u : Fin (m+1) → stdSimplex ℝ κ) :
    vertexMap R (affineSimplex u) ≫ CoefficientAffineRealization.vertexRealization R =
    CoefficientAffineRealization.vertexRealization R ≫ CoefficientH0.singularPostcomposition R (affineSimplex u) := by
  ext n : 1
  exact (vertexRealization_affine_natural R u n).symm

theorem face_naturality (m : ℕ) (i : Fin (m+2)) :
    vertexMap R (affineSimplex (standardSimplexVertices (m+1) ∘ i.succAbove)) ≫
      CoefficientAffineRealization.vertexRealization R =
    CoefficientAffineRealization.vertexRealization R ≫
      CoefficientH0.singularPostcomposition R (affineSimplex (standardSimplexVertices (m+1) ∘ i.succAbove)) :=
  realization_naturality R _

theorem affine_face_eq (m : ℕ) (i : Fin (m+2)) :
    affineSimplex (standardSimplexVertices (m+1) ∘ i.succAbove) =
      (⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩ :
        C(stdSimplex ℝ (Fin (m+1)), stdSimplex ℝ (Fin (m+2)))) := by
  ext x : 1
  have h := congrFun (affineSimplex_comp_map (standardSimplexVertices (m+1)) i.succAbove) x
  rw [affineSimplex_standardSimplexVertices] at h
  exact h.symm

theorem actual_face_naturality (m : ℕ) (i : Fin (m+2)) :
    vertexMap R (stdSimplex.map i.succAbove : stdSimplex ℝ (Fin (m+1)) → stdSimplex ℝ (Fin (m+2))) ≫
      CoefficientAffineRealization.vertexRealization R =
    CoefficientAffineRealization.vertexRealization R ≫
      CoefficientH0.singularPostcomposition R
        (⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩ :
          C(stdSimplex ℝ (Fin (m+1)), stdSimplex ℝ (Fin (m+2)))) := by
  have h := face_naturality R m i
  rw [affine_face_eq] at h
  exact h

example (i : Fin 2) := actual_face_naturality ℤ 0 i
example (i : Fin 2) := actual_face_naturality ℚ 0 i
#print axioms actual_face_naturality
#print axioms vertexMap
#print axioms vertexMap_id
#print axioms vertexMap_comp
#print axioms realization_naturality
#print axioms face_naturality
end ConstructionTargets.CoefficientAffineNaturality
