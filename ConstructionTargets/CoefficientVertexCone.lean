import ConstructionTargets.CoefficientH0
noncomputable section
namespace ConstructionTargets.CoefficientVertexCone
open CategoryTheory CategoryTheory.Limits Simplicial SingularSubdivision
variable (R : Type) [CommRing R]
abbrev VertexChains (V : Type) : ChainComplex (ModuleCat R) ℕ :=
  ((AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj
    (ModuleCat.of R R)).obj (vertexSSet V)

/-- A basis generator of the formal ordered-vertex chain complex. -/
def vertexGenerator (V : Type) (n : ℕ) (v : Fin (n + 1) → V) :
    ModuleCat.of R R ⟶ (VertexChains R V).X n := by
  change ModuleCat.of R R ⟶ ∐ fun _ : Fin (n + 1) → V ↦ ModuleCat.of R R
  exact Limits.Sigma.ι (fun _ : Fin (n + 1) → V ↦ ModuleCat.of R R) v

/-- Formal vertex generators have the usual alternating boundary. -/
theorem vertexGenerator_boundary (V : Type) (n : ℕ)
    (v : Fin (n + 2) → V) :
    vertexGenerator R V (n + 1) v ≫ (VertexChains R V).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        vertexGenerator R V n (v ∘ i.succAbove) := by
  dsimp [vertexGenerator, VertexChains,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  unfold AlgebraicTopology.AlternatingFaceMapComplex.objD
  calc
    _ = ∑ i : Fin (n + 2), Limits.Sigma.ι
          (fun _ : Fin (n + 2) → V ↦ ModuleCat.of R R) v ≫
        ((-1 : ℤ) ^ (i : ℕ) •
          ((((SimplicialObject.whiskering Type (ModuleCat R)).obj
              (CategoryTheory.Limits.sigmaConst.obj (ModuleCat.of R R))).obj
                (vertexSSet V)).δ i)) := by
      simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte]
        using Preadditive.comp_sum (Finset.univ : Finset (Fin (n + 2)))
          (Limits.Sigma.ι
            (fun _ : Fin (n + 2) → V ↦ ModuleCat.of R R) v)
          (fun i ↦ (-1 : ℤ) ^ (i : ℕ) •
            ((((SimplicialObject.whiskering Type (ModuleCat R)).obj
                (CategoryTheory.Limits.sigmaConst.obj (ModuleCat.of R R))).obj
                  (vertexSSet V)).δ i))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = (-1 : ℤ) ^ (i : ℕ) •
            (Limits.Sigma.ι
              (fun _ : Fin (n + 2) → V ↦ ModuleCat.of R R) v ≫
              ((((SimplicialObject.whiskering Type (ModuleCat R)).obj
                (CategoryTheory.Limits.sigmaConst.obj (ModuleCat.of R R))).obj
                  (vertexSSet V)).δ i)) := by
          exact CategoryTheory.Preadditive.comp_zsmul
            (Limits.Sigma.ι
              (fun _ : Fin (n + 2) → V ↦ ModuleCat.of R R) v)
            (((((SimplicialObject.whiskering Type (ModuleCat R)).obj
              (CategoryTheory.Limits.sigmaConst.obj (ModuleCat.of R R))).obj
                (vertexSSet V)).δ i))
            ((-1 : ℤ) ^ (i : ℕ))
        _ = _ := by
          congr 1
          dsimp [vertexGenerator, SimplicialObject.δ,
            SimplicialObject.whiskering, CategoryTheory.Limits.sigmaConst,
            vertexSSet]
          rw [Limits.Sigma.ι_comp_map']
          congr 1

def vertexCone (V : Type) (b : V) (n : ℕ) :
    (VertexChains R V).X n ⟶ (VertexChains R V).X (n + 1) := by
  change (∐ fun _ : Fin (n + 1) → V ↦ ModuleCat.of R R) ⟶
    (∐ fun _ : Fin (n + 2) → V ↦ ModuleCat.of R R)
  exact Limits.Sigma.desc fun v ↦ vertexGenerator R V (n + 1) (prependVertex b v)

@[simp, reassoc] theorem vertexGenerator_vertexCone (V : Type) (b : V)
    (n : ℕ) (v : Fin (n + 1) → V) :
    vertexGenerator R V n v ≫ vertexCone R V b n =
      vertexGenerator R V (n + 1) (prependVertex b v) := by
  dsimp [vertexGenerator, vertexCone]
  exact Limits.Sigma.ι_desc _ v

/-- Coning is a contraction of the augmented ordered-vertex chain complex in
positive degrees. -/
theorem vertexCone_boundary (V : Type) (b : V) (n : ℕ) :
    vertexCone R V b (n + 1) ≫ (VertexChains R V).d (n + 2) (n + 1) =
      𝟙 ((VertexChains R V).X (n + 1)) -
        (VertexChains R V).d (n + 1) n ≫ vertexCone R V b n := by
  apply Limits.Sigma.hom_ext
  intro v
  change (vertexGenerator R V (n + 1) v ≫ vertexCone R V b (n + 1)) ≫ _ =
    vertexGenerator R V (n + 1) v ≫ _
  rw [vertexGenerator_vertexCone R, vertexGenerator_boundary R]
  rw [Preadditive.comp_sub, Category.comp_id]
  rw [← Category.assoc]
  rw [vertexGenerator_boundary R]
  rw [Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, vertexGenerator_vertexCone R]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul]
  rw [prependVertex_face_zero]
  simp_rw [prependVertex_face_succ]
  rw [sub_eq_add_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (-1 : ℤ) ^ ((i.succ : Fin (n + 3)) : ℕ) =
      -((-1 : ℤ) ^ (i : ℕ)) by
    rw [Fin.val_succ, pow_succ]
    ring]
  simp

/-- Degree-zero coning has the expected augmented boundary `[p]-[b]`. -/
theorem vertexGenerator_cone_zero_boundary (V : Type) (b : V)
    (p : Fin 1 → V) :
    (vertexGenerator R V 0 p ≫ vertexCone R V b 0) ≫
        (VertexChains R V).d 1 0 =
      vertexGenerator R V 0 p -
        vertexGenerator R V 0 (fun _ : Fin 1 ↦ b) := by
  rw [vertexGenerator_vertexCone R, vertexGenerator_boundary R]
  rw [Fin.sum_univ_two]
  rw [prependVertex_face_zero]
  rw [show prependVertex b p ∘
      (1 : Fin 2).succAbove = (fun _ : Fin 1 ↦ b) by
    funext i
    fin_cases i
    rfl]
  simp [sub_eq_add_neg]


example (b : ℝ) :
    vertexCone ℤ ℝ b 1 ≫ (VertexChains ℤ ℝ).d 2 1 =
      𝟙 _ - (VertexChains ℤ ℝ).d 1 0 ≫ vertexCone ℤ ℝ b 0 :=
  vertexCone_boundary ℤ ℝ b 0
example (b : ℝ) :
    vertexCone ℚ ℝ b 1 ≫ (VertexChains ℚ ℝ).d 2 1 =
      𝟙 _ - (VertexChains ℚ ℝ).d 1 0 ≫ vertexCone ℚ ℝ b 0 :=
  vertexCone_boundary ℚ ℝ b 0
#print axioms vertexGenerator_boundary
#print axioms vertexGenerator_vertexCone
#print axioms vertexCone_boundary
#print axioms vertexGenerator_cone_zero_boundary
end ConstructionTargets.CoefficientVertexCone
