import Mathlib

/-!
# Singular-chain subdivision machinery

This file supplies the affine-simplex and coning layer needed before
barycentric subdivision can be defined on Mathlib's categorical singular-chain
complex.  It deliberately stops before subdivision itself.
-/

noncomputable section

namespace ConstructionTargets.SingularSubdivision

open CategoryTheory CategoryTheory.Limits Simplicial


/-- Ordinary integer singular chains. -/
abbrev SingularChains (X : TopCat) : ChainComplex AddCommGrpCat ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).obj X

/-- The affine map of standard simplices determined by an ordered family of
vertices.  Coordinate `j` is the weighted sum of the `j`-coordinates of the
chosen vertices. -/
def affineSimplex {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 1) → stdSimplex ℝ ι) :
    C(stdSimplex ℝ (Fin (m + 1)), stdSimplex ℝ ι) where
  toFun x :=
    ⟨fun j ↦ ∑ i, x i * v i j,
      ⟨fun j ↦ Finset.sum_nonneg fun i _ ↦
          mul_nonneg (stdSimplex.zero_le x i) (stdSimplex.zero_le (v i) j),
        by
          rw [Finset.sum_comm]
          simp_rw [← Finset.mul_sum]
          simp⟩⟩
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro j
    change Continuous fun x : stdSimplex ℝ (Fin (m + 1)) ↦
      ∑ i, x i * v i j
    exact continuous_finset_sum _ fun i _ ↦
      ((continuous_apply i).comp continuous_subtype_val).mul continuous_const

@[simp] theorem affineSimplex_apply {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 1) → stdSimplex ℝ ι)
    (x : stdSimplex ℝ (Fin (m + 1))) (j : ι) :
    affineSimplex v x j = ∑ i, x i * v i j :=
  rfl

/-- Restricting an affine simplex along a vertex reindexing simply reindexes
its ordered vertex family. -/
theorem affineSimplex_comp_map {m k : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 1) → stdSimplex ℝ ι) (f : Fin (k + 1) → Fin (m + 1)) :
    affineSimplex v ∘ ContinuousMap.mk (stdSimplex.map f)
        (stdSimplex.continuous_map f) =
      affineSimplex (v ∘ f) := by
  ext x j
  change ∑ i, (stdSimplex.map f x) i * v i j =
    ∑ i, x i * v (f i) j
  change ∑ i, (FunOnFinite.linearMap ℝ ℝ f x) i * v i j = _
  simp_rw [FunOnFinite.linearMap_apply_apply]
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ y, ∑ i with f i = y, x i * v (f i) j := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise Finset.univ f
      (fun i ↦ x i * v (f i) j)

/-- Singular `n`-simplices in a topological space. -/
abbrev SingularSimplex (X : TopCat) (n : ℕ) :=
  (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)

/-- The canonical copy of `ℤ` indexed by a singular simplex inside the
degree-`n` singular-chain group. -/
def singularGenerator (X : TopCat) (n : ℕ) (σ : SingularSimplex X n) :
    AddCommGrpCat.of ℤ ⟶ (SingularChains X).X n :=
  by
    change AddCommGrpCat.of ℤ ⟶
      ∐ fun _ : SingularSimplex X n ↦ AddCommGrpCat.of ℤ
    exact Limits.Sigma.ι (fun _ : SingularSimplex X n ↦ AddCommGrpCat.of ℤ) σ

/-- A singular simplex represented by a continuous map from the standard
topological simplex. -/
def singularSimplexOfContinuousMap (X : TopCat) (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) : SingularSimplex X n :=
  (TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌)).symm σ

/-- The boundary of a singular-chain generator is the alternating sum of its
faces.  This is the generator-facing form of Mathlib's categorical
`AlternatingFaceMapComplex` differential. -/
theorem singularGenerator_boundary (X : TopCat) (n : ℕ)
    (σ : SingularSimplex X (n + 1)) :
    singularGenerator X (n + 1) σ ≫ (SingularChains X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        singularGenerator X n ((TopCat.toSSet.obj X).δ i σ) := by
  dsimp [singularGenerator, SingularChains,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  unfold AlgebraicTopology.AlternatingFaceMapComplex.objD
  calc
    _ = ∑ i : Fin (n + 2), Limits.Sigma.ι
          (fun _ : SingularSimplex X (n + 1) ↦ AddCommGrpCat.of ℤ) σ ≫
        ((-1 : ℤ) ^ (i : ℕ) •
          ((((SimplicialObject.whiskering Type AddCommGrpCat).obj
              (CategoryTheory.Limits.sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
                (TopCat.toSSet.obj X)).δ i)) := by
      simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte]
        using Preadditive.comp_sum (Finset.univ : Finset (Fin (n + 2)))
          (Limits.Sigma.ι
            (fun _ : SingularSimplex X (n + 1) ↦ AddCommGrpCat.of ℤ) σ)
          (fun i ↦ (-1 : ℤ) ^ (i : ℕ) •
            ((((SimplicialObject.whiskering Type AddCommGrpCat).obj
                (CategoryTheory.Limits.sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
                  (TopCat.toSSet.obj X)).δ i))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = (-1 : ℤ) ^ (i : ℕ) •
            (Limits.Sigma.ι
              (fun _ : SingularSimplex X (n + 1) ↦ AddCommGrpCat.of ℤ) σ ≫
              ((((SimplicialObject.whiskering Type AddCommGrpCat).obj
                (CategoryTheory.Limits.sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
                  (TopCat.toSSet.obj X)).δ i)) := by
          exact CategoryTheory.Preadditive.comp_zsmul
            (Limits.Sigma.ι
              (fun _ : SingularSimplex X (n + 1) ↦ AddCommGrpCat.of ℤ) σ)
            (((((SimplicialObject.whiskering Type AddCommGrpCat).obj
              (CategoryTheory.Limits.sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
                (TopCat.toSSet.obj X)).δ i))
            ((-1 : ℤ) ^ (i : ℕ))
        _ = _ := by
          congr 1
          dsimp [singularGenerator, SimplicialObject.δ,
            SimplicialObject.whiskering, CategoryTheory.Limits.sigmaConst]
          rw [Limits.Sigma.ι_comp_map']
          simp

/-! ## Degree-two Alexander--Whitney faces -/

/-- The front edge `[0,1]` of a singular two-simplex. -/
def alexanderWhitneyFrontEdge (X : TopCat) (s : SingularSimplex X 2) :
    SingularSimplex X 1 :=
  (TopCat.toSSet.obj X).δ (2 : Fin 3) s

/-- The back edge `[1,2]` of a singular two-simplex. -/
def alexanderWhitneyBackEdge (X : TopCat) (s : SingularSimplex X 2) :
    SingularSimplex X 1 :=
  (TopCat.toSSet.obj X).δ (0 : Fin 3) s

/-- Linear extension of the Alexander--Whitney front edge from singular
two-simplices to degree-two singular chains. -/
def alexanderWhitneyFrontEdgeMap (X : TopCat) :
    (SingularChains X).X 2 ⟶ (SingularChains X).X 1 := by
  dsimp [SingularChains, AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  exact Limits.Sigma.desc (fun s =>
    singularGenerator X 1 (alexanderWhitneyFrontEdge X s))

/-- Linear extension of the Alexander--Whitney back edge. -/
def alexanderWhitneyBackEdgeMap (X : TopCat) :
    (SingularChains X).X 2 ⟶ (SingularChains X).X 1 := by
  dsimp [SingularChains, AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  exact Limits.Sigma.desc (fun s =>
    singularGenerator X 1 (alexanderWhitneyBackEdge X s))

@[reassoc]
theorem singularGenerator_alexanderWhitneyFrontEdgeMap
    (X : TopCat) (s : SingularSimplex X 2) :
    singularGenerator X 2 s ≫ alexanderWhitneyFrontEdgeMap X =
      singularGenerator X 1 (alexanderWhitneyFrontEdge X s) := by
  dsimp [singularGenerator, alexanderWhitneyFrontEdgeMap]
  exact Limits.Sigma.ι_desc _ s

@[reassoc]
theorem singularGenerator_alexanderWhitneyBackEdgeMap
    (X : TopCat) (s : SingularSimplex X 2) :
    singularGenerator X 2 s ≫ alexanderWhitneyBackEdgeMap X =
      singularGenerator X 1 (alexanderWhitneyBackEdge X s) := by
  dsimp [singularGenerator, alexanderWhitneyBackEdgeMap]
  exact Limits.Sigma.ι_desc _ s

/-- In degree two the singular boundary is back edge minus the middle edge
plus front edge, the low-dimensional Alexander--Whitney sign convention. -/
theorem singularGenerator_boundary_two (X : TopCat)
    (s : SingularSimplex X 2) :
    singularGenerator X 2 s ≫ (SingularChains X).d 2 1 =
      singularGenerator X 1 (alexanderWhitneyBackEdge X s) -
        singularGenerator X 1 ((TopCat.toSSet.obj X).δ (1 : Fin 3) s) +
      singularGenerator X 1 (alexanderWhitneyFrontEdge X s) := by
  rw [singularGenerator_boundary]
  simp [alexanderWhitneyFrontEdge, alexanderWhitneyBackEdge,
    Fin.sum_univ_succ]
  abel

/-- The singular-chain generator represented by an ordered affine simplex. -/
def affineGenerator {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 1) → stdSimplex ℝ ι) :
    AddCommGrpCat.of ℤ ⟶
      (SingularChains (TopCat.of (stdSimplex ℝ ι))).X m :=
  singularGenerator _ m
    (singularSimplexOfContinuousMap _ m (affineSimplex v))

/-- Taking a simplicial face of an affine singular simplex deletes the
corresponding ordered vertex. -/
theorem singularSimplexOfContinuousMap_affine_face
    {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 2) → stdSimplex ℝ ι) (i : Fin (m + 2)) :
    (TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ ι))).δ i
        (singularSimplexOfContinuousMap _ (m + 1) (affineSimplex v)) =
      singularSimplexOfContinuousMap _ m
        (affineSimplex (v ∘ i.succAbove)) := by
  apply (TopCat.toSSetObjEquiv
    (TopCat.of (stdSimplex ℝ ι)) (Opposite.op ⦋m⦌)).injective
  simp only [singularSimplexOfContinuousMap, Equiv.apply_symm_apply]
  ext x j
  simp [TopCat.toSSetObjEquiv, TopCat.toSSet,
    Presheaf.restrictedULiftYoneda, CategoryTheory.uliftYoneda,
    SimplicialObject.δ, SimplexCategory.toTop, SimplexCategory.toTop₀,
    TopCat.uliftFunctor]
  change affineSimplex v (stdSimplex.map (SimplexCategory.δ i) x) j = _
  have h := congrFun (affineSimplex_comp_map v i.succAbove) x
  exact congrFun (congrArg Subtype.val h) j

/-- Taking a simplicial face of an arbitrary represented singular simplex is
precomposition by the corresponding affine face inclusion. -/
theorem singularSimplexOfContinuousMap_face
    {X : Type} [TopologicalSpace X] {m : ℕ}
    (σ : C(stdSimplex ℝ (Fin (m + 2)), X)) (i : Fin (m + 2)) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i
        (singularSimplexOfContinuousMap _ (m + 1) σ) =
      singularSimplexOfContinuousMap _ m
        (σ.comp (affineSimplex
          (fun j : Fin (m + 1) =>
            ⟨Pi.single (i.succAbove j) 1,
              single_mem_stdSimplex ℝ (i.succAbove j)⟩))) := by
  classical
  apply (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋m⦌)).injective
  simp only [singularSimplexOfContinuousMap, Equiv.apply_symm_apply]
  ext x
  simp [TopCat.toSSetObjEquiv, TopCat.toSSet,
    Presheaf.restrictedULiftYoneda, CategoryTheory.uliftYoneda,
    SimplicialObject.δ, SimplexCategory.toTop, SimplexCategory.toTop₀,
    TopCat.uliftFunctor]
  apply congrArg σ
  ext j
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove x) j =
    ∑ k, x k * (Pi.single (i.succAbove k) (1 : ℝ) : Fin (m + 2) → ℝ) j
  rw [FunOnFinite.linearMap_apply_apply]
  by_cases hj : j = i
  · subst j
    simp [Fin.succAbove_ne]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [Pi.single_apply, Fin.succAbove_right_injective.eq_iff]
    rw [show Finset.filter (fun q : Fin (m + 1) => q = k) Finset.univ = {k} by
      ext q
      simp]
    simp

/-- The affine-generator boundary is the alternating sum obtained by deleting
one ordered vertex. -/
theorem affineGenerator_boundary {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 2) → stdSimplex ℝ ι) :
    affineGenerator v ≫
        (SingularChains (TopCat.of (stdSimplex ℝ ι))).d (m + 1) m =
      ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) •
        affineGenerator (v ∘ i.succAbove) := by
  rw [show affineGenerator v = singularGenerator _ (m + 1)
      (singularSimplexOfContinuousMap _ (m + 1) (affineSimplex v)) from rfl]
  rw [singularGenerator_boundary]
  simp_rw [singularSimplexOfContinuousMap_affine_face]
  rfl

/-- Prepend a cone point to an ordered vertex family.  The cone point is vertex
zero, fixing the orientation convention used by the boundary formula. -/
def coneVertices {m : ℕ} {ι : Type} [Fintype ι]
    (b : stdSimplex ℝ ι) (v : Fin (m + 1) → stdSimplex ℝ ι) :
    Fin (m + 2) → stdSimplex ℝ ι :=
  Fin.cases b v

/-- Cone an affine singular-chain generator from the explicitly first vertex
`b`. -/
def coneGenerator {m : ℕ} {ι : Type} [Fintype ι]
    (b : stdSimplex ℝ ι) (v : Fin (m + 1) → stdSimplex ℝ ι) :
    AddCommGrpCat.of ℤ ⟶
      (SingularChains (TopCat.of (stdSimplex ℝ ι))).X (m + 1) :=
  affineGenerator (coneVertices b v)

@[simp] theorem coneVertices_face_zero {m : ℕ} {ι : Type} [Fintype ι]
    (b : stdSimplex ℝ ι) (v : Fin (m + 1) → stdSimplex ℝ ι) :
    coneVertices b v ∘ (0 : Fin (m + 2)).succAbove = v := by
  funext i
  simp [coneVertices]

@[simp] theorem coneVertices_face_succ {m : ℕ} {ι : Type} [Fintype ι]
    (b : stdSimplex ℝ ι) (v : Fin (m + 2) → stdSimplex ℝ ι)
    (i : Fin (m + 2)) :
    coneVertices b v ∘ i.succ.succAbove =
      coneVertices b (v ∘ i.succAbove) := by
  funext j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp [coneVertices]
  · simp [coneVertices]

/-- The alternating boundary of an ordered affine simplex, written in the
generator API rather than through the internal coproduct presentation. -/
def affineBoundary {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 2) → stdSimplex ℝ ι) :
    AddCommGrpCat.of ℤ ⟶
      (SingularChains (TopCat.of (stdSimplex ℝ ι))).X m :=
  ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) •
    affineGenerator (v ∘ i.succAbove)

/-- The boundary of a cone is its base minus the cone on the boundary.  The
cone vertex is first, so deleting it has positive sign and deleting base
vertex `i` has sign `-(-1)^i`. -/
theorem coneGenerator_boundary {m : ℕ} {ι : Type} [Fintype ι]
    (b : stdSimplex ℝ ι) (v : Fin (m + 2) → stdSimplex ℝ ι) :
    coneGenerator b v ≫
        (SingularChains (TopCat.of (stdSimplex ℝ ι))).d (m + 2) (m + 1) =
      affineGenerator v -
        ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) •
          coneGenerator b (v ∘ i.succAbove) := by
  rw [show coneGenerator b v = singularGenerator _ (m + 2)
      (singularSimplexOfContinuousMap _ (m + 2)
        (affineSimplex (coneVertices b v))) from rfl]
  rw [singularGenerator_boundary]
  simp_rw [singularSimplexOfContinuousMap_affine_face]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul]
  rw [coneVertices_face_zero]
  simp_rw [coneVertices_face_succ]
  change affineGenerator v + _ = affineGenerator v - _
  rw [sub_eq_add_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (-1 : ℤ) ^ ((i.succ : Fin (m + 3)) : ℕ) =
      -((-1 : ℤ) ^ (i : ℕ)) by
    rw [Fin.val_succ, pow_succ]
    ring]
  simp [coneGenerator, affineGenerator]

/-- The production cone operation on a vertex is the oriented edge from the
cone point `b` to that vertex `p`; its boundary visibly is `[p] - [b]`. -/
theorem coneGenerator_vertex_boundary {ι : Type} [Fintype ι]
    (b p : stdSimplex ℝ ι) :
    coneGenerator b (fun _ : Fin 1 ↦ p) ≫
        (SingularChains (TopCat.of (stdSimplex ℝ ι))).d 1 0 =
      affineGenerator (fun _ : Fin 1 ↦ p) -
        affineGenerator (fun _ : Fin 1 ↦ b) := by
  rw [show coneGenerator b (fun _ : Fin 1 ↦ p) =
      singularGenerator _ 1
        (singularSimplexOfContinuousMap _ 1
          (affineSimplex (coneVertices b (fun _ : Fin 1 ↦ p)))) from rfl]
  rw [singularGenerator_boundary]
  simp_rw [singularSimplexOfContinuousMap_affine_face]
  rw [Fin.sum_univ_two]
  rw [coneVertices_face_zero]
  rw [show coneVertices b (fun _ : Fin 1 ↦ p) ∘
      (1 : Fin 2).succAbove = (fun _ : Fin 1 ↦ b) by
    funext i
    fin_cases i
    rfl]
  simp [affineGenerator, sub_eq_add_neg]

#print axioms coneGenerator_boundary
#print axioms coneGenerator_vertex_boundary

/-! ## Formal affine chains and recursive subdivision

The recursion is performed in the free simplicial abelian group on ordered
vertex families. This imports `∂² = 0` from Mathlib's alternating-face-map
complex, avoiding a second hand-written double-face cancellation proof. -/

/-- The simplicial set whose `n`-simplices are ordered `(n+1)`-tuples of
vertices. -/
def vertexSSet (V : Type) : SSet where
  obj n := Fin (n.unop.len + 1) → V
  map f v := v ∘ f.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Free integer chains on ordered vertex families. -/
abbrev VertexChains (V : Type) : ChainComplex AddCommGrpCat ℕ :=
  ((AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).obj (vertexSSet V)

/-- A basis generator of the formal ordered-vertex chain complex. -/
def vertexGenerator (V : Type) (n : ℕ) (v : Fin (n + 1) → V) :
    AddCommGrpCat.of ℤ ⟶ (VertexChains V).X n := by
  change AddCommGrpCat.of ℤ ⟶ ∐ fun _ : Fin (n + 1) → V ↦ AddCommGrpCat.of ℤ
  exact Limits.Sigma.ι (fun _ : Fin (n + 1) → V ↦ AddCommGrpCat.of ℤ) v

/-- Formal vertex generators have the usual alternating boundary. -/
theorem vertexGenerator_boundary (V : Type) (n : ℕ)
    (v : Fin (n + 2) → V) :
    vertexGenerator V (n + 1) v ≫ (VertexChains V).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        vertexGenerator V n (v ∘ i.succAbove) := by
  dsimp [vertexGenerator, VertexChains,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  unfold AlgebraicTopology.AlternatingFaceMapComplex.objD
  calc
    _ = ∑ i : Fin (n + 2), Limits.Sigma.ι
          (fun _ : Fin (n + 2) → V ↦ AddCommGrpCat.of ℤ) v ≫
        ((-1 : ℤ) ^ (i : ℕ) •
          ((((SimplicialObject.whiskering Type AddCommGrpCat).obj
              (CategoryTheory.Limits.sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
                (vertexSSet V)).δ i)) := by
      simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte]
        using Preadditive.comp_sum (Finset.univ : Finset (Fin (n + 2)))
          (Limits.Sigma.ι
            (fun _ : Fin (n + 2) → V ↦ AddCommGrpCat.of ℤ) v)
          (fun i ↦ (-1 : ℤ) ^ (i : ℕ) •
            ((((SimplicialObject.whiskering Type AddCommGrpCat).obj
                (CategoryTheory.Limits.sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
                  (vertexSSet V)).δ i))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = (-1 : ℤ) ^ (i : ℕ) •
            (Limits.Sigma.ι
              (fun _ : Fin (n + 2) → V ↦ AddCommGrpCat.of ℤ) v ≫
              ((((SimplicialObject.whiskering Type AddCommGrpCat).obj
                (CategoryTheory.Limits.sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
                  (vertexSSet V)).δ i)) := by
          exact CategoryTheory.Preadditive.comp_zsmul
            (Limits.Sigma.ι
              (fun _ : Fin (n + 2) → V ↦ AddCommGrpCat.of ℤ) v)
            (((((SimplicialObject.whiskering Type AddCommGrpCat).obj
              (CategoryTheory.Limits.sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
                (vertexSSet V)).δ i))
            ((-1 : ℤ) ^ (i : ℕ))
        _ = _ := by
          congr 1
          dsimp [vertexGenerator, SimplicialObject.δ,
            SimplicialObject.whiskering, CategoryTheory.Limits.sigmaConst,
            vertexSSet]
          rw [Limits.Sigma.ι_comp_map']
          congr 1

/-- The barycentre of an ordered family of vertices. -/
def vertexBarycenter {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 1) → stdSimplex ℝ ι) : stdSimplex ℝ ι :=
  affineSimplex v stdSimplex.barycenter

/-- Prepend a vertex to an arbitrary ordered vertex family. -/
def prependVertex {V : Type} {m : ℕ} (b : V) (v : Fin (m + 1) → V) :
    Fin (m + 2) → V :=
  Fin.cases b v

/-- Linear coning on formal ordered-vertex chains. -/
def vertexCone (V : Type) (b : V) (n : ℕ) :
    (VertexChains V).X n ⟶ (VertexChains V).X (n + 1) := by
  change (∐ fun _ : Fin (n + 1) → V ↦ AddCommGrpCat.of ℤ) ⟶
    (∐ fun _ : Fin (n + 2) → V ↦ AddCommGrpCat.of ℤ)
  exact Limits.Sigma.desc fun v ↦ vertexGenerator V (n + 1) (prependVertex b v)

@[simp, reassoc] theorem vertexGenerator_vertexCone (V : Type) (b : V)
    (n : ℕ) (v : Fin (n + 1) → V) :
    vertexGenerator V n v ≫ vertexCone V b n =
      vertexGenerator V (n + 1) (prependVertex b v) := by
  dsimp [vertexGenerator, vertexCone]
  exact Limits.Sigma.ι_desc _ v

@[simp] theorem prependVertex_face_zero {V : Type} {m : ℕ}
    (b : V) (v : Fin (m + 1) → V) :
    prependVertex b v ∘ (0 : Fin (m + 2)).succAbove = v := by
  funext i
  simp [prependVertex]

@[simp] theorem prependVertex_face_succ {V : Type} {m : ℕ}
    (b : V) (v : Fin (m + 2) → V) (i : Fin (m + 2)) :
    prependVertex b v ∘ i.succ.succAbove =
      prependVertex b (v ∘ i.succAbove) := by
  funext j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp [prependVertex]
  · simp [prependVertex]

/-- Coning is a contraction of the augmented ordered-vertex chain complex in
positive degrees. -/
theorem vertexCone_boundary (V : Type) (b : V) (n : ℕ) :
    vertexCone V b (n + 1) ≫ (VertexChains V).d (n + 2) (n + 1) =
      𝟙 ((VertexChains V).X (n + 1)) -
        (VertexChains V).d (n + 1) n ≫ vertexCone V b n := by
  apply Limits.Sigma.hom_ext
  intro v
  change (vertexGenerator V (n + 1) v ≫ vertexCone V b (n + 1)) ≫ _ =
    vertexGenerator V (n + 1) v ≫ _
  rw [vertexGenerator_vertexCone, vertexGenerator_boundary]
  rw [Preadditive.comp_sub, Category.comp_id]
  rw [← Category.assoc]
  rw [vertexGenerator_boundary]
  rw [Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, vertexGenerator_vertexCone]
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
    (vertexGenerator V 0 p ≫ vertexCone V b 0) ≫
        (VertexChains V).d 1 0 =
      vertexGenerator V 0 p -
        vertexGenerator V 0 (fun _ : Fin 1 ↦ b) := by
  rw [vertexGenerator_vertexCone, vertexGenerator_boundary]
  rw [Fin.sum_univ_two]
  rw [prependVertex_face_zero]
  rw [show prependVertex b p ∘
      (1 : Fin 2).succAbove = (fun _ : Fin 1 ↦ b) by
    funext i
    fin_cases i
    rfl]
  simp [sub_eq_add_neg]

/-- Barycentric subdivision on formal ordered-vertex chains. -/
def vertexSubdivision {ι : Type} [Fintype ι] (n : ℕ) :
    (VertexChains (stdSimplex ℝ ι)).X n ⟶
      (VertexChains (stdSimplex ℝ ι)).X n :=
  match n with
  | 0 => 𝟙 _
  | n + 1 => by
      change (∐ fun _ : Fin (n + 2) → stdSimplex ℝ ι ↦ AddCommGrpCat.of ℤ) ⟶ _
      exact Limits.Sigma.desc fun v ↦
        vertexGenerator _ (n + 1) v ≫
          (VertexChains (stdSimplex ℝ ι)).d (n + 1) n ≫
          vertexSubdivision n ≫ vertexCone _ (vertexBarycenter v) n

@[simp] theorem vertexGenerator_vertexSubdivision_zero
    {ι : Type} [Fintype ι] (v : Fin 1 → stdSimplex ℝ ι) :
    vertexGenerator _ 0 v ≫ vertexSubdivision 0 = vertexGenerator _ 0 v := by
  simp [vertexSubdivision]

@[simp] theorem vertexGenerator_vertexSubdivision_succ
    {ι : Type} [Fintype ι] (n : ℕ)
    (v : Fin (n + 2) → stdSimplex ℝ ι) :
    vertexGenerator _ (n + 1) v ≫ vertexSubdivision (n + 1) =
      vertexGenerator _ (n + 1) v ≫
        (VertexChains (stdSimplex ℝ ι)).d (n + 1) n ≫
        vertexSubdivision n ≫ vertexCone _ (vertexBarycenter v) n := by
  dsimp [vertexSubdivision, vertexGenerator]
  exact Limits.Sigma.ι_desc _ v

/-- Subdivision commutes with the differential. -/
theorem vertexSubdivision_comm_d {ι : Type} [Fintype ι] (n : ℕ) :
    vertexSubdivision (ι := ι) (n + 1) ≫
        (VertexChains (stdSimplex ℝ ι)).d (n + 1) n =
      (VertexChains (stdSimplex ℝ ι)).d (n + 1) n ≫ vertexSubdivision n := by
  induction n with
  | zero =>
      apply Limits.Sigma.hom_ext
      intro v
      change (vertexGenerator (stdSimplex ℝ ι) 1 v ≫ vertexSubdivision 1) ≫
          (VertexChains (stdSimplex ℝ ι)).d 1 0 =
        (vertexGenerator (stdSimplex ℝ ι) 1 v ≫
          (VertexChains (stdSimplex ℝ ι)).d 1 0) ≫ vertexSubdivision 0
      rw [vertexGenerator_vertexSubdivision_succ]
      simp only [vertexSubdivision, Category.assoc, Category.id_comp,
        Category.comp_id]
      rw [← Category.assoc]
      rw [vertexGenerator_boundary]
      rw [Preadditive.sum_comp]
      rw [Fin.sum_univ_two]
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
        neg_smul]
      rw [Preadditive.neg_comp]
      simp only [← Category.assoc]
      rw [vertexGenerator_cone_zero_boundary,
        vertexGenerator_cone_zero_boundary]
      rw [Fin.sum_univ_two]
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
        neg_smul]
      abel
  | succ n ih =>
      apply Limits.Sigma.hom_ext
      intro v
      change (vertexGenerator _ (n + 2) v ≫ vertexSubdivision (n + 2)) ≫ _ =
        (vertexGenerator _ (n + 2) v ≫ _) ≫ vertexSubdivision (n + 1)
      rw [vertexGenerator_vertexSubdivision_succ]
      simp only [Category.assoc]
      have hz : (VertexChains (stdSimplex ℝ ι)).d (n + 2) (n + 1) ≫
          vertexSubdivision (n + 1) ≫
          (VertexChains (stdSimplex ℝ ι)).d (n + 1) n ≫
          vertexCone _ (vertexBarycenter v) n = 0 := by
        rw [← Category.assoc
          (vertexSubdivision (ι := ι) (n + 1))
          ((VertexChains (stdSimplex ℝ ι)).d (n + 1) n)
          (vertexCone _ (vertexBarycenter v) n)]
        rw [ih]
        simp only [← Category.assoc]
        rw [Category.assoc, HomologicalComplex.d_comp_d]
        simp
      have hz' : vertexGenerator (stdSimplex ℝ ι) (n + 1 + 1) v ≫
          (VertexChains (stdSimplex ℝ ι)).d (n + 1 + 1) (n + 1) ≫
          vertexSubdivision (n + 1) ≫
          (VertexChains (stdSimplex ℝ ι)).d (n + 1) n ≫
          vertexCone _ (vertexBarycenter v) n = 0 := by
        rw [hz]
        simp
      rw [vertexCone_boundary]
      simp only [Preadditive.comp_sub, Category.comp_id]
      simpa only [sub_zero] using congrArg
        (fun z ↦
          (vertexGenerator (stdSimplex ℝ ι) (n + 1 + 1) v ≫
            (VertexChains (stdSimplex ℝ ι)).d (n + 1 + 1) (n + 1) ≫
            vertexSubdivision (n + 1)) - z) hz'

/-- Realize a formal ordered-vertex chain as the corresponding affine singular
chain. -/
def vertexRealizationDegree {ι : Type} [Fintype ι] (n : ℕ) :
    (VertexChains (stdSimplex ℝ ι)).X n ⟶
      (SingularChains (TopCat.of (stdSimplex ℝ ι))).X n := by
  change (∐ fun _ : Fin (n + 1) → stdSimplex ℝ ι ↦ AddCommGrpCat.of ℤ) ⟶ _
  exact Limits.Sigma.desc fun v ↦ affineGenerator v

@[simp, reassoc] theorem vertexGenerator_vertexRealizationDegree
    {ι : Type} [Fintype ι] (n : ℕ)
    (v : Fin (n + 1) → stdSimplex ℝ ι) :
    vertexGenerator _ n v ≫ vertexRealizationDegree n = affineGenerator v := by
  dsimp [vertexGenerator, vertexRealizationDegree]
  exact Limits.Sigma.ι_desc _ v

/-- Affine realization is a chain map. -/
def vertexRealization {ι : Type} [Fintype ι] :
    VertexChains (stdSimplex ℝ ι) ⟶
      SingularChains (TopCat.of (stdSimplex ℝ ι)) where
  f := vertexRealizationDegree
  comm' n m h := by
    obtain rfl := h
    apply Limits.Sigma.hom_ext
    intro v
    change (vertexGenerator _ (m + 1) v ≫ vertexRealizationDegree (m + 1)) ≫ _ =
      (vertexGenerator _ (m + 1) v ≫ _) ≫ vertexRealizationDegree m
    rw [vertexGenerator_vertexRealizationDegree, affineGenerator_boundary]
    rw [vertexGenerator_boundary, Preadditive.sum_comp]
    simp_rw [Preadditive.zsmul_comp,
      vertexGenerator_vertexRealizationDegree]

/-- Barycentric subdivision as a chain endomorphism of formal vertex chains. -/
def vertexSubdivisionHom {ι : Type} [Fintype ι] :
    VertexChains (stdSimplex ℝ ι) ⟶ VertexChains (stdSimplex ℝ ι) where
  f := vertexSubdivision
  comm' n m h := by
    obtain rfl := h
    exact vertexSubdivision_comm_d m

/-- The production subdivision of an affine singular generator: recursively
subdivide its ordered vertices, then realize every resulting simplex in the
actual singular-chain complex. -/
def affineSubdivision {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 1) → stdSimplex ℝ ι) :
    AddCommGrpCat.of ℤ ⟶
      (SingularChains (TopCat.of (stdSimplex ℝ ι))).X m :=
  vertexGenerator _ m v ≫ vertexSubdivision m ≫ vertexRealizationDegree m

/-- The production affine subdivision commutes with boundary. -/
theorem affineSubdivision_boundary {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 2) → stdSimplex ℝ ι) :
    affineSubdivision v ≫
        (SingularChains (TopCat.of (stdSimplex ℝ ι))).d (m + 1) m =
      ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) •
        affineSubdivision (v ∘ i.succAbove) := by
  dsimp [affineSubdivision]
  simp only [Category.assoc]
  have hr := (vertexRealization (ι := ι)).comm
    (i := m + 1) (j := m)
  change vertexRealizationDegree (m + 1) ≫
      (SingularChains (TopCat.of (stdSimplex ℝ ι))).d (m + 1) m =
    (VertexChains (stdSimplex ℝ ι)).d (m + 1) m ≫
      vertexRealizationDegree m at hr
  rw [hr]
  rw [← Category.assoc
    (vertexSubdivision (ι := ι) (m + 1))
    ((VertexChains (stdSimplex ℝ ι)).d (m + 1) m)
    (vertexRealizationDegree m)]
  rw [vertexSubdivision_comm_d]
  simp only [← Category.assoc]
  rw [vertexGenerator_boundary, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp]
  simp only [Category.assoc]
  rw [Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp]
  rfl

/-- On an edge, the production subdivision has the same boundary as the
original edge: the terminal vertex minus the initial vertex.  This tests the
property needed by the chain-map construction without imposing a false normal
form on parameterized singular simplices. -/
theorem affineSubdivision_edge_boundary {ι : Type} [Fintype ι]
    (v : Fin 2 → stdSimplex ℝ ι) :
    affineSubdivision v ≫
        (SingularChains (TopCat.of (stdSimplex ℝ ι))).d 1 0 =
      affineGenerator (fun _ : Fin 1 ↦ v 1) -
        affineGenerator (fun _ : Fin 1 ↦ v 0) := by
  rw [affineSubdivision_boundary]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
    neg_smul]
  rw [← sub_eq_add_neg]
  change affineSubdivision (v ∘ (0 : Fin 2).succAbove) -
      affineSubdivision (v ∘ (1 : Fin 2).succAbove) = _
  simp only [affineSubdivision, vertexSubdivision, Category.id_comp,
    vertexGenerator_vertexRealizationDegree]
  rw [show v ∘ (0 : Fin 2).succAbove = (fun _ : Fin 1 ↦ v 1) by
    funext i
    fin_cases i
    rfl]
  rw [show v ∘ (1 : Fin 2).succAbove = (fun _ : Fin 1 ↦ v 0) by
    funext i
    fin_cases i
    rfl]

/-! ## Prism operator -/

/-- The prism operator, recursively coning the remaining homotopy defect from
the barycentre of each generator. -/
def vertexPrism {ι : Type} [Fintype ι] (n : ℕ) :
    (VertexChains (stdSimplex ℝ ι)).X n ⟶
      (VertexChains (stdSimplex ℝ ι)).X (n + 1) :=
  match n with
  | 0 => 0
  | n + 1 => by
      change (∐ fun _ : Fin (n + 2) → stdSimplex ℝ ι ↦ AddCommGrpCat.of ℤ) ⟶ _
      exact Limits.Sigma.desc fun v ↦
        (vertexGenerator _ (n + 1) v ≫
            (vertexSubdivision (n + 1) - 𝟙 _) -
          vertexGenerator _ (n + 1) v ≫
            (VertexChains (stdSimplex ℝ ι)).d (n + 1) n ≫ vertexPrism n) ≫
            vertexCone _ (vertexBarycenter v) (n + 1)
termination_by n

/-- The prism correction in degree `n`: there is no lower differential in
degree zero, and in positive degree it is `∂T`. -/
def vertexPrismCorrection {ι : Type} [Fintype ι] (n : ℕ) :
    (VertexChains (stdSimplex ℝ ι)).X n ⟶
      (VertexChains (stdSimplex ℝ ι)).X n :=
  match n with
  | 0 => 0
  | n + 1 => (VertexChains (stdSimplex ℝ ι)).d (n + 1) n ≫ vertexPrism n

@[simp] theorem vertexPrism_zero {ι : Type} [Fintype ι] :
    vertexPrism (ι := ι) 0 = 0 := by simp [vertexPrism]

@[simp, reassoc] theorem vertexGenerator_vertexPrism_succ
    {ι : Type} [Fintype ι] (n : ℕ)
    (v : Fin (n + 2) → stdSimplex ℝ ι) :
    vertexGenerator _ (n + 1) v ≫ vertexPrism (n + 1) =
      (vertexGenerator _ (n + 1) v ≫
          (vertexSubdivision (n + 1) - 𝟙 _) -
        vertexGenerator _ (n + 1) v ≫ vertexPrismCorrection (n + 1)) ≫
          vertexCone _ (vertexBarycenter v) (n + 1) := by
  rw [show vertexPrismCorrection (ι := ι) (n + 1) =
      (VertexChains (stdSimplex ℝ ι)).d (n + 1) n ≫ vertexPrism n from rfl]
  rw [vertexPrism]
  dsimp [vertexGenerator]
  exact Limits.Sigma.ι_desc _ v

theorem d_comp_vertexPrismCorrection {ι : Type} [Fintype ι] (n : ℕ) :
    (VertexChains (stdSimplex ℝ ι)).d (n + 1) n ≫
      vertexPrismCorrection n = 0 := by
  cases n with
  | zero => simp [vertexPrismCorrection]
  | succ n =>
      rw [show vertexPrismCorrection (ι := ι) (n + 1) =
        (VertexChains (stdSimplex ℝ ι)).d (n + 1) n ≫ vertexPrism n from rfl]
      simp only [← Category.assoc]
      rw [HomologicalComplex.d_comp_d]
      simp

/-- The prism identity `∂T + T∂ = sd - id`. -/
theorem vertexPrism_identity {ι : Type} [Fintype ι] (n : ℕ) :
    vertexPrism (ι := ι) n ≫
        (VertexChains (stdSimplex ℝ ι)).d (n + 1) n +
      vertexPrismCorrection n =
        vertexSubdivision n - 𝟙 ((VertexChains (stdSimplex ℝ ι)).X n) := by
  induction n with
  | zero => simp [vertexPrismCorrection, vertexSubdivision]
  | succ n ih =>
      apply Limits.Sigma.hom_ext
      intro v
      change vertexGenerator _ (n + 1) v ≫
          (vertexPrism (n + 1) ≫ _ + vertexPrismCorrection (n + 1)) =
        vertexGenerator _ (n + 1) v ≫
          (vertexSubdivision (n + 1) - 𝟙 _)
      rw [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id]
      rw [← Category.assoc, vertexGenerator_vertexPrism_succ]
      have hD : (vertexSubdivision (ι := ι) (n + 1) - 𝟙 _) ≫
          (VertexChains (stdSimplex ℝ ι)).d (n + 1) n =
        (VertexChains (stdSimplex ℝ ι)).d (n + 1) n ≫
          (vertexSubdivision n - 𝟙 _) := by
        rw [Preadditive.sub_comp, Preadditive.comp_sub]
        rw [vertexSubdivision_comm_d, Category.id_comp, Category.comp_id]
      have ht : vertexPrism (ι := ι) n ≫
          (VertexChains (stdSimplex ℝ ι)).d (n + 1) n =
        (vertexSubdivision n - 𝟙 _) - vertexPrismCorrection n := by
        rw [eq_sub_iff_add_eq]
        exact ih
      have hz :
          (vertexGenerator _ (n + 1) v ≫
              (vertexSubdivision (n + 1) - 𝟙 _) -
            vertexGenerator _ (n + 1) v ≫
              vertexPrismCorrection (n + 1)) ≫
            (VertexChains (stdSimplex ℝ ι)).d (n + 1) n = 0 := by
        have hdc : vertexGenerator _ (n + 1) v ≫
            (VertexChains (stdSimplex ℝ ι)).d (n + 1) n ≫
            vertexPrismCorrection n = 0 := by
          rw [d_comp_vertexPrismCorrection]
          simp
        rw [Preadditive.sub_comp]
        rw [show vertexPrismCorrection (ι := ι) (n + 1) =
          (VertexChains (stdSimplex ℝ ι)).d (n + 1) n ≫ vertexPrism n from rfl]
        simp only [Category.assoc]
        rw [hD, ht]
        simp only [Preadditive.comp_sub, Category.comp_id]
        rw [hdc]
        simp
      rw [Category.assoc, vertexCone_boundary]
      rw [Preadditive.comp_sub, Category.comp_id]
      rw [← Category.assoc, hz]
      simp

/-- The two vertices of the standard topological edge. -/
def standardEdgeVertices : Fin 2 → stdSimplex ℝ (Fin 2) :=
  fun i => ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩

/-- The prism identity evaluated on the production degree-one generator of the
standard edge.  This checks the homotopy property without imposing a choice of
normal form on the resulting free singular chain. -/
theorem vertexPrism_standardEdge_identity :
    vertexGenerator _ 1 standardEdgeVertices ≫
        (vertexPrism 1 ≫
            (VertexChains (stdSimplex ℝ (Fin 2))).d 2 1 +
          vertexPrismCorrection 1) =
      vertexGenerator _ 1 standardEdgeVertices ≫
        (vertexSubdivision 1 -
          𝟙 ((VertexChains (stdSimplex ℝ (Fin 2))).X 1)) := by
  rw [vertexPrism_identity]

/-! ## Finite support for formal vertex chains

The categorical coproduct used by `VertexChains` deliberately hides its
finite-support representation.  For geometric arguments we retain that
representation explicitly as a `Finsupp`, together with its canonical
realization into the categorical chain group. -/

/-- A genuinely finite formal chain of ordered vertex families. -/
abbrev FiniteVertexChain (V : Type) (n : ℕ) :=
  (Fin (n + 1) → V) →₀ ℤ

/-- Realize a finite formal chain in the categorical coproduct. -/
def FiniteVertexChain.realize {V : Type} {n : ℕ}
    (c : FiniteVertexChain V n) :
    AddCommGrpCat.of ℤ ⟶ (VertexChains V).X n :=
  c.sum fun v z => z • vertexGenerator V n v

@[simp] theorem FiniteVertexChain.realize_single {V : Type} {n : ℕ}
    (v : Fin (n + 1) → V) (z : ℤ) :
    FiniteVertexChain.realize (Finsupp.single v z) =
      z • vertexGenerator V n v := by
  simp [FiniteVertexChain.realize]

@[simp] theorem FiniteVertexChain.realize_zero {V : Type} {n : ℕ} :
    FiniteVertexChain.realize (0 : FiniteVertexChain V n) = 0 := by
  simp [FiniteVertexChain.realize]

@[simp] theorem FiniteVertexChain.realize_add {V : Type} {n : ℕ}
    (c d : FiniteVertexChain V n) :
    FiniteVertexChain.realize (c + d) =
      FiniteVertexChain.realize c + FiniteVertexChain.realize d := by
  classical
  simp [FiniteVertexChain.realize, Finsupp.sum_add_index,
    add_smul]

theorem FiniteVertexChain.realize_finset_sum {V α : Type} {n : ℕ}
    (s : Finset α) (f : α → FiniteVertexChain V n) :
    FiniteVertexChain.realize (∑ a ∈ s, f a) =
      ∑ a ∈ s, FiniteVertexChain.realize (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

@[simp] theorem FiniteVertexChain.realize_zsmul {V : Type} {n : ℕ}
    (z : ℤ) (c : FiniteVertexChain V n) :
    FiniteVertexChain.realize (z • c) =
      z • FiniteVertexChain.realize c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add v k c hvc hk ih =>
      simp only [smul_add, FiniteVertexChain.realize_add,
        Finsupp.smul_single, FiniteVertexChain.realize_single, ih,
        smul_smul]
      simp

@[simp] theorem FiniteVertexChain.realize_neg {V : Type} {n : ℕ}
    (c : FiniteVertexChain V n) :
    FiniteVertexChain.realize (-c) = -FiniteVertexChain.realize c := by
  simpa only [neg_one_zsmul] using FiniteVertexChain.realize_zsmul (-1) c

@[simp] theorem FiniteVertexChain.realize_sub {V : Type} {n : ℕ}
    (c d : FiniteVertexChain V n) :
    FiniteVertexChain.realize (c - d) =
      FiniteVertexChain.realize c - FiniteVertexChain.realize d := by
  simp [sub_eq_add_neg]

/-- Substitute a finite chain for each basis simplex. -/
def FiniteVertexChain.bind {V W : Type} {m n : ℕ}
    (c : FiniteVertexChain V m)
    (f : (Fin (m + 1) → V) → FiniteVertexChain W n) :
    FiniteVertexChain W n :=
  c.sum fun v z => z • f v

@[simp] theorem FiniteVertexChain.bind_single {V W : Type} {m n : ℕ}
    (v : Fin (m + 1) → V) (z : ℤ)
    (f : (Fin (m + 1) → V) → FiniteVertexChain W n) :
    FiniteVertexChain.bind (Finsupp.single v z) f = z • f v := by
  simp [FiniteVertexChain.bind]

@[simp] theorem FiniteVertexChain.bind_add {V W : Type} {m n : ℕ}
    (c d : FiniteVertexChain V m)
    (f : (Fin (m + 1) → V) → FiniteVertexChain W n) :
    FiniteVertexChain.bind (c + d) f =
      FiniteVertexChain.bind c f + FiniteVertexChain.bind d f := by
  classical
  simp [FiniteVertexChain.bind, Finsupp.sum_add_index, add_smul]

theorem FiniteVertexChain.realize_bind {V W : Type} {m n : ℕ}
    (c : FiniteVertexChain V m)
    (f : (Fin (m + 1) → V) → FiniteVertexChain W n)
    (F : (VertexChains V).X m ⟶ (VertexChains W).X n)
    (hF : ∀ v, FiniteVertexChain.realize (f v) =
      vertexGenerator V m v ≫ F) :
    FiniteVertexChain.realize (FiniteVertexChain.bind c f) =
      FiniteVertexChain.realize c ≫ F := by
  classical
  induction c using Finsupp.induction with
  | zero => simp [FiniteVertexChain.bind]
  | single_add v z c hvc hz ih =>
      simp only [FiniteVertexChain.bind_add,
        FiniteVertexChain.bind_single,
        FiniteVertexChain.realize_add, FiniteVertexChain.realize_single,
        FiniteVertexChain.realize_zsmul,
        Preadditive.add_comp, Preadditive.zsmul_comp, hF, ih]

theorem FiniteVertexChain.mem_support_bind {V W : Type} {m n : ℕ}
    {c : FiniteVertexChain V m}
    {f : (Fin (m + 1) → V) → FiniteVertexChain W n}
    {w : Fin (n + 1) → W}
    (hw : w ∈ (FiniteVertexChain.bind c f).support) :
    ∃ v ∈ c.support, w ∈ (f v).support := by
  classical
  change w ∈ (∑ v ∈ c.support, c v • f v).support at hw
  obtain ⟨v, hv, hwv⟩ := Finsupp.mem_support_finset_sum w hw
  refine ⟨v, hv, ?_⟩
  rw [Finsupp.mem_support_iff] at hwv ⊢
  intro hf
  apply hwv
  simp [hf]

/-- Prepending a fixed cone point is injective on ordered vertex families. -/
def prependVertexEmbedding {V : Type} {n : ℕ} (b : V) :
    (Fin (n + 1) → V) ↪ (Fin (n + 2) → V) where
  toFun := prependVertex b
  inj' := by
    intro v w h
    funext i
    have hi := congrFun h i.succ
    simpa [prependVertex] using hi

@[simp] theorem prependVertexEmbedding_apply {V : Type} {n : ℕ}
    (b : V) (v : Fin (n + 1) → V) :
    prependVertexEmbedding b v = prependVertex b v := rfl

/-- Cone every simplex in an explicitly finite chain. -/
def FiniteVertexChain.cone {V : Type} {n : ℕ} (b : V)
    (c : FiniteVertexChain V n) : FiniteVertexChain V (n + 1) :=
  Finsupp.embDomain (prependVertexEmbedding b) c

@[simp] theorem FiniteVertexChain.cone_single {V : Type} {n : ℕ}
    (b : V) (v : Fin (n + 1) → V) (z : ℤ) :
    FiniteVertexChain.cone b (Finsupp.single v z) =
      Finsupp.single (prependVertex b v) z := by
  simp [FiniteVertexChain.cone]

theorem FiniteVertexChain.realize_cone {V : Type} {n : ℕ} (b : V)
    (c : FiniteVertexChain V n) :
    FiniteVertexChain.realize (FiniteVertexChain.cone b c) =
      FiniteVertexChain.realize c ≫ vertexCone V b n := by
  classical
  induction c using Finsupp.induction with
  | zero => simp [FiniteVertexChain.cone]
  | single_add v z c hvc hz ih =>
      change FiniteVertexChain.realize
        (Finsupp.embDomain (prependVertexEmbedding b) c) = _ at ih
      simp only [FiniteVertexChain.cone, Finsupp.embDomain_add,
        FiniteVertexChain.realize_add,
        Finsupp.embDomain_single, FiniteVertexChain.realize_single,
        Preadditive.add_comp,
        Preadditive.zsmul_comp, vertexGenerator_vertexCone]
      rw [ih]
      simp only [prependVertexEmbedding_apply]

/-- The alternating boundary, retaining its finite support. -/
def FiniteVertexChain.boundary {V : Type} {n : ℕ}
    (v : Fin (n + 2) → V) : FiniteVertexChain V n :=
  ∑ i : Fin (n + 2),
    Finsupp.single (v ∘ i.succAbove) ((-1 : ℤ) ^ (i : ℕ))

theorem FiniteVertexChain.realize_boundary {V : Type} {n : ℕ}
    (v : Fin (n + 2) → V) :
    FiniteVertexChain.realize (FiniteVertexChain.boundary v) =
      vertexGenerator V (n + 1) v ≫ (VertexChains V).d (n + 1) n := by
  rw [vertexGenerator_boundary]
  rw [show FiniteVertexChain.boundary v =
      ∑ i ∈ (Finset.univ : Finset (Fin (n + 2))),
        Finsupp.single (v ∘ i.succAbove) ((-1 : ℤ) ^ (i : ℕ)) by
    simp [FiniteVertexChain.boundary]]
  rw [FiniteVertexChain.realize_finset_sum]
  simp

/-- Barycentric subdivision with its finite support exposed. -/
def finiteVertexSubdivision {ι : Type} [Fintype ι] :
    ∀ n : ℕ, (Fin (n + 1) → stdSimplex ℝ ι) →
      FiniteVertexChain (stdSimplex ℝ ι) n :=
  Nat.rec (motive := fun n =>
      (Fin (n + 1) → stdSimplex ℝ ι) →
        FiniteVertexChain (stdSimplex ℝ ι) n)
    (fun v => Finsupp.single v 1)
    (fun _n ih v =>
      FiniteVertexChain.cone (vertexBarycenter v)
        (FiniteVertexChain.bind (FiniteVertexChain.boundary v) ih))

@[simp] theorem finiteVertexSubdivision_zero {ι : Type} [Fintype ι]
    (v : Fin 1 → stdSimplex ℝ ι) :
    finiteVertexSubdivision 0 v = Finsupp.single v 1 := rfl

@[simp] theorem finiteVertexSubdivision_succ {ι : Type} [Fintype ι]
    (n : ℕ) (v : Fin (n + 2) → stdSimplex ℝ ι) :
    finiteVertexSubdivision (n + 1) v =
      FiniteVertexChain.cone (vertexBarycenter v)
        (FiniteVertexChain.bind (FiniteVertexChain.boundary v)
          (finiteVertexSubdivision n)) := rfl

/-- The support API is the actual finite set of simplices with nonzero
coefficient in the recursive subdivision. -/
def finiteVertexSubdivisionSupport {ι : Type} [Fintype ι] (n : ℕ)
    (v : Fin (n + 1) → stdSimplex ℝ ι) :
    Finset (Fin (n + 1) → stdSimplex ℝ ι) :=
  (finiteVertexSubdivision n v).support

/-- A supported subdivided simplex is recursively a cone from the barycentre
over a supported subdivided face.  This is the geometric flag information
hidden by the categorical coproduct. -/
def IsSubdivisionPiece {ι : Type} [Fintype ι] (n : ℕ)
    (v w : Fin (n + 1) → stdSimplex ℝ ι) : Prop := by
  induction n with
  | zero => exact w = v
  | succ n ih =>
      exact ∃ (i : Fin (n + 2))
        (u : Fin (n + 1) → stdSimplex ℝ ι),
        ih (v ∘ i.succAbove) u ∧
          w = prependVertex (vertexBarycenter v) u

theorem finiteVertexSubdivision_support_piece {ι : Type} [Fintype ι]
    (n : ℕ) (v : Fin (n + 1) → stdSimplex ℝ ι)
    {w : Fin (n + 1) → stdSimplex ℝ ι}
    (hw : w ∈ finiteVertexSubdivisionSupport n v) :
    IsSubdivisionPiece n v w := by
  induction n with
  | zero =>
      have : w = v := by
        rw [finiteVertexSubdivisionSupport, Finsupp.mem_support_iff] at hw
        by_contra hne
        apply hw
        simp [finiteVertexSubdivision, hne]
      subst w
      rfl
  | succ n ih =>
      change w ∈ (FiniteVertexChain.cone (vertexBarycenter v)
        (FiniteVertexChain.bind (FiniteVertexChain.boundary v)
          (finiteVertexSubdivision n))).support at hw
      rw [FiniteVertexChain.cone, Finsupp.support_embDomain] at hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hw
      obtain ⟨face, hface, hu'⟩ :=
        FiniteVertexChain.mem_support_bind hu
      obtain ⟨i, -, hi⟩ := Finsupp.mem_support_finset_sum face
        (by simpa [FiniteVertexChain.boundary] using hface)
      have hfaceEq : face = v ∘ i.succAbove := by
        by_contra hne
        rw [Finsupp.mem_support_iff] at hi
        apply hi
        simp [hne]
      subst face
      exact ⟨i, u, ih _ hu', rfl⟩

/-- The barycentre used by subdivision lies in the convex hull of the original
ordered vertices (viewed in the ambient normed vector space). -/
theorem vertexBarycenter_val_mem_convexHull {m : ℕ} {ι : Type}
    [Fintype ι] (v : Fin (m + 1) → stdSimplex ℝ ι) :
    (vertexBarycenter v : ι → ℝ) ∈
      convexHull ℝ (Set.range fun i => (v i : ι → ℝ)) := by
  let t : Finset (Fin (m + 1)) := Finset.univ
  have h := t.centerMass_mem_convexHull
    (s := Set.range fun i => (v i : ι → ℝ))
    (w := fun _ => (1 : ℝ))
    (z := fun i => (v i : ι → ℝ))
    (fun _ _ => zero_le_one)
    (by simp [t]; positivity)
    (fun i _ => Set.mem_range_self i)
  convert h using 1
  ext j
  change (∑ i : Fin (m + 1),
    ((Fintype.card (Fin (m + 1)) : ℕ) : ℝ)⁻¹ * v i j) =
      (t.centerMass (fun _ => (1 : ℝ))
        (fun i => (v i : ι → ℝ))) j
  simp [Finset.centerMass, t, Finset.mul_sum]

theorem IsSubdivisionPiece.vertex_val_mem_convexHull {ι : Type}
    [Fintype ι] {n : ℕ}
    {v w : Fin (n + 1) → stdSimplex ℝ ι}
    (h : IsSubdivisionPiece n v w) (k : Fin (n + 1)) :
    (w k : ι → ℝ) ∈ convexHull ℝ
      (Set.range fun i => (v i : ι → ℝ)) := by
  induction n with
  | zero =>
      subst w
      exact subset_convexHull ℝ _ (Set.mem_range_self k)
  | succ n ih =>
      obtain ⟨i, u, hu, rfl⟩ := h
      refine Fin.cases ?_ (fun j => ?_) k
      · exact vertexBarycenter_val_mem_convexHull v
      · apply convexHull_mono
          (s := Set.range fun j => (v (i.succAbove j) : ι → ℝ))
          (t := Set.range fun j => (v j : ι → ℝ))
        · rintro x ⟨j, rfl⟩
          exact ⟨i.succAbove j, rfl⟩
        · exact ih hu j

theorem vertexBarycenter_sub_vertex {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 1) → stdSimplex ℝ ι) (k : Fin (m + 1)) :
    (vertexBarycenter v : ι → ℝ) - (v k : ι → ℝ) =
      ((m + 1 : ℕ) : ℝ)⁻¹ •
        ∑ i ∈ (Finset.univ.erase k),
          ((v i : ι → ℝ) - (v k : ι → ℝ)) := by
  have hk : k ∈ (Finset.univ : Finset (Fin (m + 1))) := Finset.mem_univ k
  let a : ℝ := ((m + 1 : ℕ) : ℝ)⁻¹
  have ha : a * (m + 1 : ℕ) = 1 := by
    dsimp [a]
    rw [inv_mul_cancel₀]
    positivity
  rw [show (vertexBarycenter v : ι → ℝ) =
      a • ∑ i : Fin (m + 1), (v i : ι → ℝ) by
    apply funext
    intro j
    change affineSimplex v stdSimplex.barycenter j = _
    rw [affineSimplex_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    calc
      (∑ i : Fin (m + 1), stdSimplex.barycenter i * v i j) =
          ∑ i : Fin (m + 1), ((m + 1 : ℕ) : ℝ)⁻¹ * v i j := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        convert (stdSimplex.barycenter_apply (𝕜 := ℝ) i) using 1
        simp
      _ = ((m + 1 : ℕ) : ℝ)⁻¹ * ∑ i, v i j :=
        (Finset.mul_sum _ _ _).symm
      _ = a * ∑ i, v i j := by rfl]
  rw [← Finset.sum_erase_add _ _ hk, smul_add]
  simp only [Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_erase_of_mem hk, Finset.card_univ, Fintype.card_fin,
    Nat.add_sub_cancel]
  change a • (∑ i ∈ Finset.univ.erase k, (v i : ι → ℝ)) +
      a • (v k : ι → ℝ) - (v k : ι → ℝ) =
    a • ((∑ i ∈ Finset.univ.erase k, (v i : ι → ℝ)) -
      m • (v k : ι → ℝ))
  have ha' : a * (m : ℝ) + a = 1 := by
    push_cast at ha
    linarith
  have hcoef : a - 1 = -(a * (m : ℝ)) := by linarith
  rw [← Nat.cast_smul_eq_nsmul ℝ m]
  calc
    a • (∑ i ∈ Finset.univ.erase k, (v i : ι → ℝ)) +
          a • (v k : ι → ℝ) - (v k : ι → ℝ) =
        a • (∑ i ∈ Finset.univ.erase k, (v i : ι → ℝ)) +
          (a - 1) • (v k : ι → ℝ) := by module
    _ = a • (∑ i ∈ Finset.univ.erase k, (v i : ι → ℝ)) +
          (-(a * (m : ℝ))) • (v k : ι → ℝ) := by rw [hcoef]
    _ = a • ((∑ i ∈ Finset.univ.erase k, (v i : ι → ℝ)) -
          (m : ℝ) • (v k : ι → ℝ)) := by module

/-- Diameter of the finite ordered vertex set, measured in the ambient normed
vector space. -/
def vertexDiameter {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 1) → stdSimplex ℝ ι) : ℝ :=
  Metric.diam (Set.range fun i => (v i : ι → ℝ))

/-- Every original vertex lies within `m/(m+1)` times the original diameter of
the barycentre. -/
theorem dist_vertexBarycenter_vertex_le {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 1) → stdSimplex ℝ ι) (k : Fin (m + 1)) :
    dist (vertexBarycenter v : ι → ℝ) (v k : ι → ℝ) ≤
      (m : ℝ) / (m + 1) * vertexDiameter v := by
  let a : ℝ := ((m + 1 : ℕ) : ℝ)⁻¹
  let s : Finset (Fin (m + 1)) := Finset.univ.erase k
  have ha : 0 ≤ a := by positivity
  have hb : Bornology.IsBounded (Set.range fun i => (v i : ι → ℝ)) :=
    Set.Finite.isBounded (Set.finite_range fun i => (v i : ι → ℝ))
  have hi (i : Fin (m + 1)) :
      ‖(v i : ι → ℝ) - (v k : ι → ℝ)‖ ≤ vertexDiameter v := by
    rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem hb (Set.mem_range_self i)
      (Set.mem_range_self k)
  have hsum :
      ∑ i ∈ s, ‖(v i : ι → ℝ) - (v k : ι → ℝ)‖ ≤
        (m : ℝ) * vertexDiameter v := by
    calc
      _ ≤ ∑ _i ∈ s, vertexDiameter v :=
        Finset.sum_le_sum fun i _ => hi i
      _ = _ := by
        simp [s]
  rw [dist_eq_norm, vertexBarycenter_sub_vertex]
  change ‖a • ∑ i ∈ s, ((v i : ι → ℝ) - (v k : ι → ℝ))‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  calc
    a * ‖∑ i ∈ s, ((v i : ι → ℝ) - (v k : ι → ℝ))‖ ≤
        a * ∑ i ∈ s, ‖(v i : ι → ℝ) - (v k : ι → ℝ)‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ a * ((m : ℝ) * vertexDiameter v) := by gcongr
    _ = (m : ℝ) / (m + 1) * vertexDiameter v := by
      dsimp [a]
      rw [div_eq_mul_inv]
      push_cast
      ring

/-- The same barycentre bound holds throughout the convex hull of the vertex
set, because the corresponding closed ball is convex. -/
theorem dist_vertexBarycenter_convexHull_le {m : ℕ} {ι : Type}
    [Fintype ι] (v : Fin (m + 1) → stdSimplex ℝ ι)
    {x : ι → ℝ}
    (hx : x ∈ convexHull ℝ (Set.range fun i => (v i : ι → ℝ))) :
    dist (vertexBarycenter v : ι → ℝ) x ≤
      (m : ℝ) / (m + 1) * vertexDiameter v := by
  let r := (m : ℝ) / (m + 1) * vertexDiameter v
  have hrange : Set.range (fun i => (v i : ι → ℝ)) ⊆
      Metric.closedBall (vertexBarycenter v : ι → ℝ) r := by
    rintro _ ⟨i, rfl⟩
    apply Metric.mem_closedBall.mpr
    rw [dist_comm]
    exact dist_vertexBarycenter_vertex_le v i
  have hhull : convexHull ℝ (Set.range fun i => (v i : ι → ℝ)) ⊆
      Metric.closedBall (vertexBarycenter v : ι → ℝ) r :=
    convexHull_min hrange (convex_closedBall _ _)
  rw [dist_comm]
  exact Metric.mem_closedBall.mp (hhull hx)

theorem vertexDiameter_face_le {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 2) → stdSimplex ℝ ι) (i : Fin (m + 2)) :
    vertexDiameter (v ∘ i.succAbove) ≤ vertexDiameter v := by
  apply Metric.diam_mono
  · rintro _ ⟨j, rfl⟩
    exact ⟨i.succAbove j, rfl⟩
  · exact Set.Finite.isBounded (Set.finite_range fun j => (v j : ι → ℝ))

/-- Quantitative barycentric contraction for every simplex in the recursive
subdivision support. -/
theorem IsSubdivisionPiece.dist_le {ι : Type} [Fintype ι] {n : ℕ}
    {v w : Fin (n + 1) → stdSimplex ℝ ι}
    (h : IsSubdivisionPiece n v w) (p q : Fin (n + 1)) :
    dist (w p : ι → ℝ) (w q : ι → ℝ) ≤
      (n : ℝ) / (n + 1) * vertexDiameter v := by
  induction n with
  | zero =>
      change w = v at h
      subst w
      fin_cases p
      fin_cases q
      simp
  | succ n ih =>
      change ∃ (i : Fin (n + 2))
        (u : Fin (n + 1) → stdSimplex ℝ ι),
        IsSubdivisionPiece n (v ∘ i.succAbove) u ∧
          w = prependVertex (vertexBarycenter v) u at h
      obtain ⟨i, u, hu, rfl⟩ := h
      refine Fin.cases ?_ (fun p' => ?_) p <;>
        refine Fin.cases ?_ (fun q' => ?_) q
      · rw [dist_self]
        exact mul_nonneg (div_nonneg (by positivity) (by positivity))
          Metric.diam_nonneg
      · apply dist_vertexBarycenter_convexHull_le v
        apply convexHull_mono
            (s := Set.range fun j => (v (i.succAbove j) : ι → ℝ))
            (t := Set.range fun j => (v j : ι → ℝ))
        · rintro _ ⟨j, rfl⟩
          exact ⟨i.succAbove j, rfl⟩
        · exact IsSubdivisionPiece.vertex_val_mem_convexHull hu q'
      · rw [dist_comm]
        apply dist_vertexBarycenter_convexHull_le v
        apply convexHull_mono
            (s := Set.range fun j => (v (i.succAbove j) : ι → ℝ))
            (t := Set.range fun j => (v j : ι → ℝ))
        · rintro _ ⟨j, rfl⟩
          exact ⟨i.succAbove j, rfl⟩
        · exact IsSubdivisionPiece.vertex_val_mem_convexHull hu p'
      · calc
          dist (u p' : ι → ℝ) (u q' : ι → ℝ) ≤
              (n : ℝ) / (n + 1) *
                vertexDiameter (v ∘ i.succAbove) := ih hu p' q'
          _ ≤ (n : ℝ) / (n + 1) * vertexDiameter v := by
            exact mul_le_mul_of_nonneg_left (vertexDiameter_face_le v i)
              (div_nonneg (by positivity) (by positivity))
          _ ≤ ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 1) *
              vertexDiameter v := by
            apply mul_le_mul_of_nonneg_right _ Metric.diam_nonneg
            apply (div_le_div_iff₀
              (show 0 < (n : ℝ) + 1 by positivity)
              (show 0 < ((n + 1 : ℕ) : ℝ) + 1 by positivity)).mpr
            push_cast
            nlinarith [show 0 ≤ (n : ℝ) by positivity]

theorem IsSubdivisionPiece.diameter_le {ι : Type} [Fintype ι] {n : ℕ}
    {v w : Fin (n + 1) → stdSimplex ℝ ι}
    (h : IsSubdivisionPiece n v w) :
    vertexDiameter w ≤ (n : ℝ) / (n + 1) * vertexDiameter v := by
  apply Metric.diam_le_of_forall_dist_le_of_nonempty
  · exact ⟨(w 0 : ι → ℝ), Set.mem_range_self 0⟩
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact h.dist_le p q

/-- The explicit `n/(n+1)` diameter contraction for every simplex in the
actual finite support of production barycentric subdivision. -/
theorem finiteVertexSubdivision_diameter_le {ι : Type} [Fintype ι]
    (n : ℕ) (v : Fin (n + 1) → stdSimplex ℝ ι)
    {w : Fin (n + 1) → stdSimplex ℝ ι}
    (hw : w ∈ finiteVertexSubdivisionSupport n v) :
    vertexDiameter w ≤ (n : ℝ) / (n + 1) * vertexDiameter v :=
  (finiteVertexSubdivision_support_piece n v hw).diameter_le

/-- Concrete property check: every supported simplex of the subdivided
standard edge has at most half the original edge's diameter. -/
theorem finiteVertexSubdivision_standardEdge_diameter_le
    {w : Fin 2 → stdSimplex ℝ (Fin 2)}
    (hw : w ∈ finiteVertexSubdivisionSupport 1 standardEdgeVertices) :
    vertexDiameter w ≤ (1 / 2 : ℝ) * vertexDiameter standardEdgeVertices := by
  convert finiteVertexSubdivision_diameter_le 1 standardEdgeVertices hw using 1
  norm_num

/-! ## Iterated subdivision and open-cover smallness -/

/-- Iterate the finite-support subdivision `k` times. -/
def iteratedFiniteVertexSubdivision {ι : Type} [Fintype ι] (n : ℕ) :
    ℕ → (Fin (n + 1) → stdSimplex ℝ ι) →
      FiniteVertexChain (stdSimplex ℝ ι) n :=
  Nat.rec (fun v => Finsupp.single v 1) (fun _ ih v =>
      FiniteVertexChain.bind (ih v)
        (finiteVertexSubdivision n))

/-- The corresponding categorical iterate of production subdivision. -/
def vertexSubdivisionIterate {ι : Type} [Fintype ι] (n : ℕ) :
    ℕ → ((VertexChains (stdSimplex ℝ ι)).X n ⟶
      (VertexChains (stdSimplex ℝ ι)).X n) :=
  Nat.rec (𝟙 _) (fun _ ih => ih ≫ vertexSubdivision n)

def iteratedFiniteVertexSubdivisionSupport {ι : Type} [Fintype ι]
    (n k : ℕ) (v : Fin (n + 1) → stdSimplex ℝ ι) :
    Finset (Fin (n + 1) → stdSimplex ℝ ι) :=
  (iteratedFiniteVertexSubdivision n k v).support

/-- Diameter contraction compounds under iteration. -/
theorem iteratedFiniteVertexSubdivision_diameter_le {ι : Type} [Fintype ι]
    (n k : ℕ) (v : Fin (n + 1) → stdSimplex ℝ ι)
    {w : Fin (n + 1) → stdSimplex ℝ ι}
    (hw : w ∈ iteratedFiniteVertexSubdivisionSupport n k v) :
    vertexDiameter w ≤
      ((n : ℝ) / (n + 1)) ^ k * vertexDiameter v := by
  induction k generalizing w with
  | zero =>
      rw [iteratedFiniteVertexSubdivisionSupport,
        Finsupp.mem_support_iff] at hw
      have hwv : w = v := by
        by_contra hne
        apply hw
        simp [iteratedFiniteVertexSubdivision, hne]
      subst w
      simp
  | succ k ih =>
      change w ∈ (FiniteVertexChain.bind
        (iteratedFiniteVertexSubdivision n k v)
        (finiteVertexSubdivision n)).support at hw
      obtain ⟨u, hu, hwu⟩ := FiniteVertexChain.mem_support_bind hw
      calc
        vertexDiameter w ≤ (n : ℝ) / (n + 1) * vertexDiameter u :=
          finiteVertexSubdivision_diameter_le n u hwu
        _ ≤ (n : ℝ) / (n + 1) *
            (((n : ℝ) / (n + 1)) ^ k * vertexDiameter v) := by
          exact mul_le_mul_of_nonneg_left (ih hu)
            (div_nonneg (by positivity) (by positivity))
        _ = ((n : ℝ) / (n + 1)) ^ (k + 1) * vertexDiameter v := by
          rw [pow_succ]
          ring

/-- Every point of an affine simplex lies in the convex hull of its ordered
vertices. -/
theorem affineSimplex_val_mem_convexHull {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 1) → stdSimplex ℝ ι)
    (x : stdSimplex ℝ (Fin (m + 1))) :
    (affineSimplex v x : ι → ℝ) ∈
      convexHull ℝ (Set.range fun i => (v i : ι → ℝ)) := by
  let t : Finset (Fin (m + 1)) := Finset.univ
  have h := t.centerMass_mem_convexHull
    (s := Set.range fun i => (v i : ι → ℝ))
    (w := fun i => x i)
    (z := fun i => (v i : ι → ℝ))
    (fun i _ => stdSimplex.zero_le x i)
    (by simp [t])
    (fun i _ => Set.mem_range_self i)
  convert h using 1
  ext j
  simp [Finset.centerMass, t, affineSimplex_apply]

/-- The image of an affine simplex stays within one vertex diameter of any
chosen vertex. -/
theorem dist_affineSimplex_vertex_le {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 1) → stdSimplex ℝ ι)
    (x : stdSimplex ℝ (Fin (m + 1))) (i : Fin (m + 1)) :
    dist (affineSimplex v x : ι → ℝ) (v i : ι → ℝ) ≤ vertexDiameter v := by
  have hrange : Set.range (fun j => (v j : ι → ℝ)) ⊆
      Metric.closedBall (v i : ι → ℝ) (vertexDiameter v) := by
    rintro _ ⟨j, rfl⟩
    exact Metric.mem_closedBall.mpr
      (Metric.dist_le_diam_of_mem
        (Set.Finite.isBounded (Set.finite_range fun j => (v j : ι → ℝ)))
        (Set.mem_range_self j) (Set.mem_range_self i))
  have hhull := convexHull_min hrange (convex_closedBall _ _)
  exact Metric.mem_closedBall.mp (hhull (affineSimplex_val_mem_convexHull v x))

/-- After sufficiently many subdivisions, every supported affine simplex is
subordinate to an arbitrary open cover of the target standard simplex. -/
theorem exists_iteratedFiniteVertexSubdivision_subordinate
    {ι α : Type} [Fintype ι] (n : ℕ)
    (v : Fin (n + 1) → stdSimplex ℝ ι)
    (c : α → Set (stdSimplex ℝ ι))
    (hcOpen : ∀ a, IsOpen (c a))
    (hcCover : Set.univ ⊆ ⋃ a, c a) :
    ∃ k, ∀ w ∈ iteratedFiniteVertexSubdivisionSupport n k v,
      ∃ a, Set.range (affineSimplex w) ⊆ c a := by
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric (s := Set.univ) isCompact_univ hcOpen hcCover
  let r : ℝ := (n : ℝ) / (n + 1)
  have hr0 : 0 ≤ r := div_nonneg (by positivity) (by positivity)
  have hr1 : r < 1 := by
    dsimp [r]
    rw [div_lt_one (by positivity)]
    norm_num
  have ht : Filter.Tendsto (fun k : ℕ => r ^ k * vertexDiameter v)
      Filter.atTop (nhds 0) :=
    by simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const
        (vertexDiameter v)
  have hev : ∀ᶠ k : ℕ in Filter.atTop,
      r ^ k * vertexDiameter v < δ := by
    exact (tendsto_order.1 ht).2 δ hδ
  obtain ⟨k, hk⟩ := hev.exists
  refine ⟨k, fun w hw => ?_⟩
  have hdiam : vertexDiameter w < δ :=
    (iteratedFiniteVertexSubdivision_diameter_le n k v hw).trans_lt hk
  obtain ⟨a, ha⟩ := hball (w 0) (Set.mem_univ _)
  refine ⟨a, fun _ hy => ?_⟩
  obtain ⟨x, rfl⟩ := hy
  apply ha
  apply Metric.mem_ball.mpr
  change dist (affineSimplex w x : ι → ℝ) (w 0 : ι → ℝ) < δ
  exact (dist_affineSimplex_vertex_le w x 0).trans_lt hdiam

/-- Subordination holds at every sufficiently large subdivision depth.  This
is the monotone form needed to choose one depth for all simplices in a finite
chain. -/
theorem eventually_iteratedFiniteVertexSubdivision_subordinate
    {ι α : Type} [Fintype ι] (n : ℕ)
    (v : Fin (n + 1) → stdSimplex ℝ ι)
    (c : α → Set (stdSimplex ℝ ι))
    (hcOpen : ∀ a, IsOpen (c a))
    (hcCover : Set.univ ⊆ ⋃ a, c a) :
    ∃ k, ∀ l, k ≤ l → ∀ w ∈ iteratedFiniteVertexSubdivisionSupport n l v,
      ∃ a, Set.range (affineSimplex w) ⊆ c a := by
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric (s := Set.univ) isCompact_univ hcOpen hcCover
  let r : ℝ := (n : ℝ) / (n + 1)
  have hr0 : 0 ≤ r := div_nonneg (by positivity) (by positivity)
  have hr1 : r < 1 := by
    dsimp [r]
    rw [div_lt_one (by positivity)]
    norm_num
  have ht : Filter.Tendsto (fun k : ℕ => r ^ k * vertexDiameter v)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const
      (vertexDiameter v)
  have hev : ∀ᶠ k : ℕ in Filter.atTop,
      r ^ k * vertexDiameter v < δ :=
    (tendsto_order.1 ht).2 δ hδ
  rw [Filter.eventually_atTop] at hev
  obtain ⟨k, hk⟩ := hev
  refine ⟨k, fun l hkl w hw => ?_⟩
  have hdiam : vertexDiameter w < δ :=
    (iteratedFiniteVertexSubdivision_diameter_le n l v hw).trans_lt (hk l hkl)
  obtain ⟨a, ha⟩ := hball (w 0) (Set.mem_univ _)
  refine ⟨a, fun _ hy => ?_⟩
  obtain ⟨x, rfl⟩ := hy
  apply ha
  apply Metric.mem_ball.mpr
  exact (dist_affineSimplex_vertex_le w x 0).trans_lt hdiam

/-- Concrete smallness check: some iterate of the production subdivision of
the standard edge is subordinate to the cover by quarter-radius metric balls. -/
theorem exists_standardEdge_quarterBall_subdivision :
    ∃ k, ∀ w ∈ iteratedFiniteVertexSubdivisionSupport 1 k standardEdgeVertices,
      ∃ p : stdSimplex ℝ (Fin 2),
        Set.range (affineSimplex w) ⊆ Metric.ball p (1 / 4 : ℝ) := by
  apply exists_iteratedFiniteVertexSubdivision_subordinate 1
    standardEdgeVertices (fun p => Metric.ball p (1 / 4 : ℝ))
  · exact fun _ => Metric.isOpen_ball
  · intro p _
    simp only [Set.mem_iUnion]
    exact ⟨p, Metric.mem_ball_self (by norm_num)⟩

/-! ## Transport to arbitrary singular simplices -/

/-- Postcompose every affine simplex in a finite vertex chain with an
arbitrary singular simplex.  `mapDomain` deliberately adds coefficients when
two parameterized simplices become equal after postcomposition. -/
def postcomposeFiniteVertexChain {X ι : Type} [TopologicalSpace X]
    [Fintype ι] {m : ℕ} (σ : C(stdSimplex ℝ ι, X))
    (c : FiniteVertexChain (stdSimplex ℝ ι) m) :
    C(stdSimplex ℝ (Fin (m + 1)), X) →₀ ℤ :=
  Finsupp.mapDomain (fun v => σ.comp (affineSimplex v)) c

/-- Every term surviving postcomposition comes from a genuine source-support
term.  Cancellation may remove terms, but cannot invent one. -/
theorem postcomposeFiniteVertexChain_mem_support {X : Type}
    [TopologicalSpace X] {ι : Type} [Fintype ι] {m : ℕ}
    (σ : C(stdSimplex ℝ ι, X))
    (c : FiniteVertexChain (stdSimplex ℝ ι) m)
    {τ : C(stdSimplex ℝ (Fin (m + 1)), X)}
    (hτ : τ ∈ (postcomposeFiniteVertexChain σ c).support) :
    ∃ v ∈ c.support, σ.comp (affineSimplex v) = τ := by
  classical
  by_contra h
  push_neg at h
  rw [Finsupp.mem_support_iff] at hτ
  apply hτ
  by_cases hr : τ ∈ Set.range (fun v => σ.comp (affineSimplex v))
  · obtain ⟨v, rfl⟩ := hr
    unfold postcomposeFiniteVertexChain
    rw [Finsupp.mapDomain_apply_eq_sum]
    apply Finset.sum_eq_zero
    intro u hu
    simp only [Finset.mem_filter] at hu
    exact False.elim ((h u hu.1) hu.2)
  · unfold postcomposeFiniteVertexChain
    exact Finsupp.mapDomain_notin_range c τ hr

/-- The transported finite support of the `k`-fold subdivision of a singular
simplex. -/
def postcomposedIteratedSubdivision {X : Type} [TopologicalSpace X] (n k : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    C(stdSimplex ℝ (Fin (n + 1)), X) →₀ ℤ :=
  postcomposeFiniteVertexChain σ
    (iteratedFiniteVertexSubdivision n k
      (fun i => ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩))

/-- A cover-small singular simplex remains cover-small term-by-term after
arbitrary iterated subdivision and postcomposition. -/
theorem postcomposedIteratedSubdivision_small {X α : Type}
    [TopologicalSpace X] (n k : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (c : α → Set X)
    {a : α} (hσ : Set.range σ ⊆ c a)
    {τ : C(stdSimplex ℝ (Fin (n + 1)), X)}
    (hτ : τ ∈ (postcomposedIteratedSubdivision n k σ).support) :
    Set.range τ ⊆ c a := by
  obtain ⟨v, -, hv⟩ := postcomposeFiniteVertexChain_mem_support σ _ hτ
  subst τ
  rintro _ ⟨x, rfl⟩
  exact hσ (Set.mem_range_self (affineSimplex v x))

/-- Pulling an open cover back along a singular simplex and subdividing deeply
enough makes every surviving postcomposed simplex subordinate to the original
cover. -/
theorem exists_postcomposedIteratedSubdivision_subordinate
    {X α : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (U : α → Set X)
    (hUOpen : ∀ a, IsOpen (U a)) (hUCover : Set.univ ⊆ ⋃ a, U a) :
    ∃ k, ∀ τ ∈ (postcomposedIteratedSubdivision n k σ).support,
      ∃ a, Set.range τ ⊆ U a := by
  let V : α → Set (stdSimplex ℝ (Fin (n + 1))) := fun a => σ ⁻¹' U a
  have hVOpen : ∀ a, IsOpen (V a) := fun a =>
    (hUOpen a).preimage σ.continuous
  have hVCover : Set.univ ⊆ ⋃ a, V a := by
    intro x _
    have hx := hUCover (Set.mem_univ (σ x))
    simpa only [V, Set.mem_iUnion, Set.mem_preimage] using hx
  obtain ⟨k, hk⟩ := exists_iteratedFiniteVertexSubdivision_subordinate n
    (fun i => ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩) V hVOpen hVCover
  refine ⟨k, fun τ hτ => ?_⟩
  obtain ⟨v, hv, rfl⟩ := postcomposeFiniteVertexChain_mem_support σ _ hτ
  obtain ⟨a, ha⟩ := hk v hv
  refine ⟨a, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact ha (Set.mem_range_self x)

/-- Every singular simplex is subordinate after every sufficiently large
subdivision depth. -/
theorem eventually_postcomposedIteratedSubdivision_subordinate
    {X α : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (U : α → Set X)
    (hUOpen : ∀ a, IsOpen (U a)) (hUCover : Set.univ ⊆ ⋃ a, U a) :
    ∃ k, ∀ l, k ≤ l → ∀ τ ∈ (postcomposedIteratedSubdivision n l σ).support,
      ∃ a, Set.range τ ⊆ U a := by
  let V : α → Set (stdSimplex ℝ (Fin (n + 1))) := fun a => σ ⁻¹' U a
  have hVOpen : ∀ a, IsOpen (V a) := fun a =>
    (hUOpen a).preimage σ.continuous
  have hVCover : Set.univ ⊆ ⋃ a, V a := by
    intro x _
    simpa only [V, Set.mem_iUnion, Set.mem_preimage] using
      hUCover (Set.mem_univ (σ x))
  obtain ⟨k, hk⟩ := eventually_iteratedFiniteVertexSubdivision_subordinate n
    (fun i => ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩) V hVOpen hVCover
  refine ⟨k, fun l hkl τ hτ => ?_⟩
  obtain ⟨v, hv, rfl⟩ := postcomposeFiniteVertexChain_mem_support σ _ hτ
  obtain ⟨a, ha⟩ := hk l hkl v hv
  refine ⟨a, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact ha (Set.mem_range_self x)

/-- A finite family of monotone depth requirements admits one common depth.
This is the finite-max step used to choose a single subdivision exponent for a
finite singular chain. -/
theorem exists_uniform_depth_finset {β : Type} (s : Finset β)
    (P : ℕ → β → Prop)
    (hmono : ∀ {k l b}, k ≤ l → P k b → P l b)
    (h : ∀ b ∈ s, ∃ k, P k b) :
    ∃ k, ∀ b ∈ s, P k b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert b s hb ih =>
      obtain ⟨kb, hkb⟩ := h b (by simp)
      obtain ⟨ks, hks⟩ := ih (fun x hx => h x (by simp [hx]))
      refine ⟨max kb ks, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · exact hmono (le_max_left _ _) hkb
      · exact hmono (le_max_right _ _) (hks x hxs)

/-- Named finite-chain form of uniform subdivision-depth selection. -/
theorem Finsupp.exists_uniform_depth {β M : Type} [Zero M]
    (z : β →₀ M) (P : ℕ → β → Prop)
    (hmono : ∀ {k l b}, k ≤ l → P k b → P l b)
    (h : ∀ b ∈ z.support, ∃ k, P k b) :
    ∃ k, ∀ b ∈ z.support, P k b :=
  exists_uniform_depth_finset z.support P hmono h

/-- Concrete depth-selection check on a two-term finite chain. -/
theorem twoTermChain_uniform_depth {β : Type} [DecidableEq β]
    (b₀ b₁ : β) (P : ℕ → β → Prop)
    (hmono : ∀ {k l b}, k ≤ l → P k b → P l b)
    {k₀ k₁ : ℕ} (h₀ : P k₀ b₀) (h₁ : P k₁ b₁) :
    ∀ b ∈ (Finsupp.single b₀ (1 : ℤ) +
      Finsupp.single b₁ 1).support, P (max k₀ k₁) b := by
  intro b hb
  have hb' : b = b₀ ∨ b = b₁ := by
    have hs := Finsupp.support_add (g₁ := Finsupp.single b₀ (1 : ℤ))
      (g₂ := Finsupp.single b₁ 1) hb
    simpa only [Finsupp.support_single_ne_zero _ one_ne_zero,
      Finset.mem_union, Finset.mem_singleton] using hs
  rcases hb' with rfl | rfl
  · exact hmono (le_max_left _ _) h₀
  · exact hmono (le_max_right _ _) h₁

/-! ## Finite support for the prism correction -/

/-- Finite-support presentation of the production prism recursion. -/
def finiteVertexPrism {ι : Type} [Fintype ι] :
    ∀ n : ℕ, (Fin (n + 1) → stdSimplex ℝ ι) →
      FiniteVertexChain (stdSimplex ℝ ι) (n + 1) :=
  Nat.rec (motive := fun n =>
      (Fin (n + 1) → stdSimplex ℝ ι) →
        FiniteVertexChain (stdSimplex ℝ ι) (n + 1))
    (fun _ => 0)
    (fun n ih v =>
      FiniteVertexChain.cone (vertexBarycenter v)
        (finiteVertexSubdivision (n + 1) v - Finsupp.single v 1 -
          FiniteVertexChain.bind (FiniteVertexChain.boundary v) ih))

@[simp] theorem finiteVertexPrism_zero {ι : Type} [Fintype ι]
    (v : Fin 1 → stdSimplex ℝ ι) : finiteVertexPrism 0 v = 0 := rfl

@[simp] theorem finiteVertexPrism_succ {ι : Type} [Fintype ι]
    (n : ℕ) (v : Fin (n + 2) → stdSimplex ℝ ι) :
    finiteVertexPrism (n + 1) v =
      FiniteVertexChain.cone (vertexBarycenter v)
        (finiteVertexSubdivision (n + 1) v - Finsupp.single v 1 -
          FiniteVertexChain.bind (FiniteVertexChain.boundary v)
            (finiteVertexPrism n)) := rfl

/-- The transported finite support of the production prism on an arbitrary
singular simplex. -/
def postcomposedPrism {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    C(stdSimplex ℝ (Fin (n + 2)), X) →₀ ℤ :=
  postcomposeFiniteVertexChain σ
    (finiteVertexPrism n
      (fun i => ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩))

/-- The production prism correction of a cover-small simplex stays in the
same cover member: every transported prism term factors through the original
simplex. -/
theorem postcomposedPrism_small {X α : Type} [TopologicalSpace X]
    (n : ℕ) (σ : C(stdSimplex ℝ (Fin (n + 1)), X))
    (c : α → Set X) {a : α} (hσ : Set.range σ ⊆ c a)
    {τ : C(stdSimplex ℝ (Fin (n + 2)), X)}
    (hτ : τ ∈ (postcomposedPrism n σ).support) :
    Set.range τ ⊆ c a := by
  obtain ⟨v, -, hv⟩ := postcomposeFiniteVertexChain_mem_support σ _ hτ
  subst τ
  rintro _ ⟨x, rfl⟩
  exact hσ (Set.mem_range_self (affineSimplex v x))

/-- The standard edge as a singular simplex in its ambient coordinate space. -/
def standardEdgeInclusion :
    C(stdSimplex ℝ (Fin 2), Fin 2 → ℝ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Concrete support-transport check: every iterated-subdivision term of the
ambient standard edge still lands in that standard edge. -/
theorem standardEdge_postcomposedSubdivision_small (k : ℕ)
    {τ : C(stdSimplex ℝ (Fin 2), Fin 2 → ℝ)}
    (hτ : τ ∈
      (postcomposedIteratedSubdivision 1 k standardEdgeInclusion).support) :
    Set.range τ ⊆ stdSimplex ℝ (Fin 2) := by
  apply postcomposedIteratedSubdivision_small
    (c := fun _ : Unit => stdSimplex ℝ (Fin 2))
    (a := ()) 1 k standardEdgeInclusion
  · rintro _ ⟨x, rfl⟩
    exact x.2
  · exact hτ

/-- Concrete prism check: every production-prism term on the ambient standard
edge stays inside the standard edge. -/
theorem standardEdge_postcomposedPrism_small
    {τ : C(stdSimplex ℝ (Fin 3), Fin 2 → ℝ)}
    (hτ : τ ∈ (postcomposedPrism 1 standardEdgeInclusion).support) :
    Set.range τ ⊆ stdSimplex ℝ (Fin 2) := by
  apply postcomposedPrism_small 1 standardEdgeInclusion
    (fun _ : Unit => stdSimplex ℝ (Fin 2)) (a := ())
  · rintro _ ⟨x, rfl⟩
    exact x.2
  · exact hτ

/-- The finite-support recursion realizes to the production categorical
subdivision map.  Thus support facts proved through the `Finsupp` API are facts
about `vertexSubdivision`, not a parallel decorative construction. -/
theorem finiteVertexSubdivision_realize {ι : Type} [Fintype ι] (n : ℕ)
    (v : Fin (n + 1) → stdSimplex ℝ ι) :
    FiniteVertexChain.realize (finiteVertexSubdivision n v) =
      vertexGenerator _ n v ≫ vertexSubdivision n := by
  induction n with
  | zero => simp [finiteVertexSubdivision]
  | succ n ih =>
      rw [finiteVertexSubdivision_succ]
      rw [FiniteVertexChain.realize_cone]
      rw [FiniteVertexChain.realize_bind _ _ (vertexSubdivision n) ih]
      rw [FiniteVertexChain.realize_boundary]
      simp only [Category.assoc]
      rw [← vertexGenerator_vertexSubdivision_succ]

/-- Iterated finite support realizes to the corresponding iterate of the
production categorical subdivision map. -/
theorem iteratedFiniteVertexSubdivision_realize {ι : Type} [Fintype ι]
    (n k : ℕ) (v : Fin (n + 1) → stdSimplex ℝ ι) :
    FiniteVertexChain.realize (iteratedFiniteVertexSubdivision n k v) =
      vertexGenerator _ n v ≫ vertexSubdivisionIterate n k := by
  induction k with
  | zero => simp [iteratedFiniteVertexSubdivision, vertexSubdivisionIterate]
  | succ k ih =>
      rw [show iteratedFiniteVertexSubdivision n (k + 1) v =
        FiniteVertexChain.bind (iteratedFiniteVertexSubdivision n k v)
          (finiteVertexSubdivision n) from rfl]
      rw [FiniteVertexChain.realize_bind _ _ (vertexSubdivision n)
        (finiteVertexSubdivision_realize n)]
      rw [ih, Category.assoc]
      congr 1

/-- The finite prism presentation is exactly the production categorical
prism, not a parallel combinatorial homotopy. -/
theorem finiteVertexPrism_realize {ι : Type} [Fintype ι]
    (n : ℕ) (v : Fin (n + 1) → stdSimplex ℝ ι) :
    FiniteVertexChain.realize (finiteVertexPrism n v) =
      vertexGenerator _ n v ≫ vertexPrism n := by
  induction n with
  | zero => simp [finiteVertexPrism]
  | succ n ih =>
      rw [finiteVertexPrism_succ, FiniteVertexChain.realize_cone]
      simp only [FiniteVertexChain.realize_sub,
        finiteVertexSubdivision_realize,
        FiniteVertexChain.realize_single]
      rw [FiniteVertexChain.realize_bind _ _ (vertexPrism n) ih]
      rw [FiniteVertexChain.realize_boundary]
      simp only [Category.assoc]
      symm
      rw [vertexGenerator_vertexPrism_succ]
      simp only [Preadditive.comp_sub, Category.comp_id, one_zsmul]
      rfl

/-! ## Naturality under maps preserving barycentres -/

/-- Apply a function to every vertex of an ordered-vertex chain. -/
def vertexMapDegree {V W : Type} (f : V → W) (n : ℕ) :
    (VertexChains V).X n ⟶ (VertexChains W).X n := by
  change (∐ fun _ : Fin (n + 1) → V ↦ AddCommGrpCat.of ℤ) ⟶ _
  exact Limits.Sigma.desc fun v => vertexGenerator W n (f ∘ v)

@[simp, reassoc] theorem vertexGenerator_vertexMapDegree {V W : Type}
    (f : V → W) (n : ℕ) (v : Fin (n + 1) → V) :
    vertexGenerator V n v ≫ vertexMapDegree f n =
      vertexGenerator W n (f ∘ v) := by
  dsimp [vertexGenerator, vertexMapDegree]
  exact Limits.Sigma.ι_desc _ v

/-- Mapping vertices commutes with the ordered-vertex differential. -/
theorem vertexMapDegree_comm_d {V W : Type} (f : V → W) (n : ℕ) :
    vertexMapDegree f (n + 1) ≫ (VertexChains W).d (n + 1) n =
      (VertexChains V).d (n + 1) n ≫ vertexMapDegree f n := by
  apply Limits.Sigma.hom_ext
  intro v
  change (vertexGenerator V (n + 1) v ≫ vertexMapDegree f (n + 1)) ≫ _ =
    (vertexGenerator V (n + 1) v ≫ _) ≫ vertexMapDegree f n
  rw [vertexGenerator_vertexMapDegree, vertexGenerator_boundary,
    vertexGenerator_boundary, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, vertexGenerator_vertexMapDegree]
  apply Finset.sum_congr rfl
  intro i _
  congr 2

/-- Vertexwise application as a chain map. -/
def vertexMap {V W : Type} (f : V → W) : VertexChains V ⟶ VertexChains W where
  f := vertexMapDegree f
  comm' n m h := by
    obtain rfl := h
    exact vertexMapDegree_comm_d f m

/-- Mapping a cone maps its cone point and its base. -/
theorem vertexMapDegree_cone {V W : Type} (f : V → W) (b : V) (n : ℕ) :
    vertexMapDegree f n ≫ vertexCone W (f b) n =
      vertexCone V b n ≫ vertexMapDegree f (n + 1) := by
  apply Limits.Sigma.hom_ext
  intro v
  change (vertexGenerator V n v ≫ vertexMapDegree f n) ≫ _ =
    (vertexGenerator V n v ≫ vertexCone V b n) ≫ _
  rw [vertexGenerator_vertexMapDegree, vertexGenerator_vertexCone,
    vertexGenerator_vertexCone, vertexGenerator_vertexMapDegree]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- An affine simplex map preserves barycentres of finite vertex families. -/
theorem affineSimplex_vertexBarycenter {m : ℕ} {κ : Type}
    [Fintype κ]
    (u : Fin (m + 1) → stdSimplex ℝ κ)
    {n : ℕ} (v : Fin (n + 1) → stdSimplex ℝ (Fin (m + 1))) :
    affineSimplex u (vertexBarycenter v) =
      vertexBarycenter (fun i => affineSimplex u (v i)) := by
  ext j
  simp only [vertexBarycenter, affineSimplex_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Subdivision is natural under every vertex map which preserves the
barycentres used by its recursion. -/
theorem vertexSubdivision_natural {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : stdSimplex ℝ ι → stdSimplex ℝ κ)
    (hb : ∀ (n : ℕ) (v : Fin (n + 1) → stdSimplex ℝ ι),
      f (vertexBarycenter v) = vertexBarycenter (f ∘ v)) (n : ℕ) :
    vertexSubdivision (ι := ι) n ≫ vertexMapDegree f n =
      vertexMapDegree f n ≫ vertexSubdivision (ι := κ) n := by
  induction n with
  | zero => simp [vertexSubdivision]
  | succ n ih =>
      apply Limits.Sigma.hom_ext
      intro v
      change (vertexGenerator (stdSimplex ℝ ι) (n + 1) v ≫
          vertexSubdivision (n + 1)) ≫ _ =
        (vertexGenerator (stdSimplex ℝ ι) (n + 1) v ≫
          vertexMapDegree f (n + 1)) ≫ _
      rw [vertexGenerator_vertexSubdivision_succ,
        vertexGenerator_vertexMapDegree, vertexGenerator_vertexSubdivision_succ]
      simp only [← Category.assoc]
      rw [Category.assoc]
      rw [← vertexMapDegree_cone]
      simp only [← Category.assoc]
      rw [show
        ((vertexGenerator (stdSimplex ℝ ι) (n + 1) v ≫
            (VertexChains (stdSimplex ℝ ι)).d (n + 1) n) ≫
              vertexSubdivision n) ≫ vertexMapDegree f n =
          ((vertexGenerator (stdSimplex ℝ ι) (n + 1) v ≫
            (VertexChains (stdSimplex ℝ ι)).d (n + 1) n) ≫
              vertexMapDegree f n) ≫ vertexSubdivision n by
            simp only [Category.assoc, ih]]
      rw [show
        (vertexGenerator (stdSimplex ℝ ι) (n + 1) v ≫
            (VertexChains (stdSimplex ℝ ι)).d (n + 1) n) ≫
              vertexMapDegree f n =
          (vertexGenerator (stdSimplex ℝ ι) (n + 1) v ≫
            vertexMapDegree f (n + 1)) ≫
              (VertexChains (stdSimplex ℝ κ)).d (n + 1) n by
            simp only [Category.assoc, vertexMapDegree_comm_d]]
      rw [vertexGenerator_vertexMapDegree]
      rw [hb (n + 1) v]

/-- Affine simplex maps commute with subdivision on ordered-vertex chains. -/
theorem vertexSubdivision_affine_natural {m : ℕ} {κ : Type} [Fintype κ]
    (u : Fin (m + 1) → stdSimplex ℝ κ) (n : ℕ) :
    vertexSubdivision (ι := Fin (m + 1)) n ≫
        vertexMapDegree (affineSimplex u) n =
      vertexMapDegree (affineSimplex u) n ≫
        vertexSubdivision (ι := κ) n := by
  apply vertexSubdivision_natural (ι := Fin (m + 1)) (κ := κ)
  intro q v
  exact affineSimplex_vertexBarycenter u v

/-! ## Naturality of affine realization -/

/-- Composition of affine simplex maps is obtained by mapping the vertices of
the inner simplex through the outer one. -/
theorem affineSimplex_comp_affineSimplex {m n : ℕ} {κ : Type} [Fintype κ]
    (u : Fin (m + 1) → stdSimplex ℝ κ)
    (v : Fin (n + 1) → stdSimplex ℝ (Fin (m + 1))) :
    (affineSimplex u).comp (affineSimplex v) =
      affineSimplex (fun i => affineSimplex u (v i)) := by
  ext x j
  simp only [ContinuousMap.comp_apply, affineSimplex_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- The production singular-chain map induced by postcomposition. -/
def singularPostcomposition {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    SingularChains (TopCat.of X) ⟶ SingularChains (TopCat.of Y) :=
  ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)

/-- The map obtained by applying the simplicial singular-chain functor to
postcomposition of singular simplices is the production postcomposition map. -/
theorem ssetChainMap_eq_singularPostcomposition {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    ((AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map
          (TopCat.toSSet.map (TopCat.ofHom f)) =
      singularPostcomposition f := by
  rfl

/-- Consequently the two presentations induce the same map on integral
singular homology in every degree. -/
theorem ssetHomologyMap_eq_singularPostcomposition {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map
            (TopCat.toSSet.map (TopCat.ofHom f))) n =
      HomologicalComplex.homologyMap (singularPostcomposition f) n := by
  exact congrArg (fun k ↦ HomologicalComplex.homologyMap k n)
    (ssetChainMap_eq_singularPostcomposition f)

/-- The map supplied by Mathlib's integral singular-homology functor is the
homology map of the production postcomposition chain map. -/
theorem singularHomologyFunctor_map_eq_singularPostcomposition {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f) =
      HomologicalComplex.homologyMap (singularPostcomposition f) n := by
  rfl

/-- SSet-chain form of
`singularHomologyFunctor_map_eq_singularPostcomposition`. -/
theorem singularHomologyFunctor_map_eq_ssetHomologyMap {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f) =
      HomologicalComplex.homologyMap
        (((AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map
            (TopCat.toSSet.map (TopCat.ofHom f))) n := by
  rw [singularHomologyFunctor_map_eq_singularPostcomposition,
    ssetHomologyMap_eq_singularPostcomposition]

@[reassoc] theorem singularHomologyFunctor_map_eq_singularPostcomposition_comp
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ)
    {Z : AddCommGrpCat} (g :
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
        (AddCommGrpCat.of ℤ)).obj (TopCat.of Y) ⟶ Z) :
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f) ≫ g =
      HomologicalComplex.homologyMap (singularPostcomposition f) n ≫ g := by
  exact congrArg (fun q ↦ q ≫ g)
    (singularHomologyFunctor_map_eq_singularPostcomposition f n)

@[reassoc] theorem singularPostcomposition_comp {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) :
    singularPostcomposition f ≫ singularPostcomposition g =
      singularPostcomposition (g.comp f) := by
  dsimp [singularPostcomposition]
  rw [← Functor.map_comp]

/-- Postcomposition carries a production generator to the generator of the
composite simplex. -/
theorem singularGenerator_singularPostcomposition {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (τ : C(stdSimplex ℝ (Fin (n + 1)), X)) (f : C(X, Y)) :
    singularGenerator (TopCat.of X) n
        (singularSimplexOfContinuousMap _ n τ) ≫
        (singularPostcomposition f).f n =
      singularGenerator (TopCat.of Y) n
        (singularSimplexOfContinuousMap _ n (f.comp τ)) := by
  dsimp [singularGenerator, singularPostcomposition, SingularChains,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  rw [Limits.Sigma.ι_comp_map']
  congr 1

/-- Postcomposition commutes with the front-edge term on every represented
singular two-simplex. -/
theorem alexanderWhitneyFrontEdge_generator_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (τ : C(stdSimplex ℝ (Fin 3), X)) (f : C(X, Y)) :
    singularGenerator (TopCat.of X) 1
        (alexanderWhitneyFrontEdge _
          (singularSimplexOfContinuousMap _ 2 τ)) ≫
        (singularPostcomposition f).f 1 =
      singularGenerator (TopCat.of Y) 1
        (alexanderWhitneyFrontEdge _
          (singularSimplexOfContinuousMap _ 2 (f.comp τ))) := by
  have hx : alexanderWhitneyFrontEdge (TopCat.of X)
      (singularSimplexOfContinuousMap _ 2 τ) =
      singularSimplexOfContinuousMap _ 1
        (τ.comp (affineSimplex (fun j : Fin 2 =>
          ⟨Pi.single ((2 : Fin 3).succAbove j) 1,
            single_mem_stdSimplex ℝ ((2 : Fin 3).succAbove j)⟩))) :=
    singularSimplexOfContinuousMap_face τ (2 : Fin 3)
  rw [hx, singularGenerator_singularPostcomposition]
  have hy : alexanderWhitneyFrontEdge (TopCat.of Y)
      (singularSimplexOfContinuousMap _ 2 (f.comp τ)) =
      singularSimplexOfContinuousMap _ 1
        ((f.comp τ).comp (affineSimplex (fun j : Fin 2 =>
          ⟨Pi.single ((2 : Fin 3).succAbove j) 1,
            single_mem_stdSimplex ℝ ((2 : Fin 3).succAbove j)⟩))) :=
    singularSimplexOfContinuousMap_face (f.comp τ) (2 : Fin 3)
  rw [hy]
  congr 2

/-- Affine realization commutes with affine postcomposition.  This is the
square connecting ordered-vertex chains to the production singular complex. -/
theorem vertexRealization_affine_natural {m : ℕ} {κ : Type} [Fintype κ]
    (u : Fin (m + 1) → stdSimplex ℝ κ) (n : ℕ) :
    vertexRealizationDegree (ι := Fin (m + 1)) n ≫
        (singularPostcomposition (affineSimplex u)).f n =
      vertexMapDegree (affineSimplex u) n ≫
        vertexRealizationDegree (ι := κ) n := by
  apply Limits.Sigma.hom_ext
  intro v
  change (vertexGenerator _ n v ≫ vertexRealizationDegree n) ≫ _ =
    (vertexGenerator _ n v ≫ vertexMapDegree (affineSimplex u) n) ≫ _
  rw [vertexGenerator_vertexRealizationDegree,
    vertexGenerator_vertexMapDegree, vertexGenerator_vertexRealizationDegree]
  dsimp [affineGenerator]
  rw [singularGenerator_singularPostcomposition]
  rw [affineSimplex_comp_affineSimplex]
  congr 3

/-- The recursive prism is natural under barycentre-preserving vertex maps. -/
theorem vertexPrism_natural {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : stdSimplex ℝ ι → stdSimplex ℝ κ)
    (hb : ∀ (n : ℕ) (v : Fin (n + 1) → stdSimplex ℝ ι),
      f (vertexBarycenter v) = vertexBarycenter (f ∘ v)) (n : ℕ) :
    vertexPrism (ι := ι) n ≫ vertexMapDegree f (n + 1) =
      vertexMapDegree f n ≫ vertexPrism (ι := κ) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      apply Limits.Sigma.hom_ext
      intro v
      change (vertexGenerator _ (n + 1) v ≫ vertexPrism (n + 1)) ≫ _ =
        (vertexGenerator _ (n + 1) v ≫ vertexMapDegree f (n + 1)) ≫ _
      rw [vertexGenerator_vertexPrism_succ,
        vertexGenerator_vertexMapDegree, vertexGenerator_vertexPrism_succ]
      rw [Category.assoc]
      rw [← vertexMapDegree_cone]
      rw [hb (n + 1) v]
      simp only [← Category.assoc]
      congr 1
      have hc : vertexPrismCorrection (ι := ι) (n + 1) ≫
          vertexMapDegree f (n + 1) =
        vertexMapDegree f (n + 1) ≫
          vertexPrismCorrection (ι := κ) (n + 1) := by
        change ((VertexChains _).d (n + 1) n ≫ vertexPrism n) ≫ _ =
          _ ≫ (VertexChains _).d (n + 1) n ≫ vertexPrism n
        simp only [Category.assoc]
        rw [ih, ← Category.assoc, ← vertexMapDegree_comm_d f n]
        rw [Category.assoc]
      simp only [Preadditive.sub_comp, Preadditive.comp_sub,
        Category.comp_id, Category.assoc]
      rw [vertexSubdivision_natural f hb (n + 1), hc,
        ← Category.assoc, vertexGenerator_vertexMapDegree]
      rw [← Category.assoc, vertexGenerator_vertexMapDegree]

/-- Affine simplex maps commute with the recursive prism. -/
theorem vertexPrism_affine_natural {m : ℕ} {κ : Type} [Fintype κ]
    (u : Fin (m + 1) → stdSimplex ℝ κ) (n : ℕ) :
    vertexPrism (ι := Fin (m + 1)) n ≫
        vertexMapDegree (affineSimplex u) (n + 1) =
      vertexMapDegree (affineSimplex u) n ≫ vertexPrism (ι := κ) n := by
  apply vertexPrism_natural (ι := Fin (m + 1)) (κ := κ)
  intro q v
  exact affineSimplex_vertexBarycenter u v

/-! ## Standard-simplex normalization -/

def standardSimplexVertices (n : ℕ) :
    Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)) :=
  fun i => ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩

def faceAffine (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  affineSimplex (fun j => standardSimplexVertices (n + 1) (i.succAbove j))

/-- The affine simplex on the standard basis vertices is the identity. -/
theorem affineSimplex_standardSimplexVertices (n : ℕ) :
    affineSimplex (standardSimplexVertices n) = ContinuousMap.id _ := by
  ext x j
  simp [affineSimplex_apply, standardSimplexVertices, Pi.single_apply]

/-- The affine face inclusion sends each standard basis vertex to the
corresponding undeleted basis vertex. -/
theorem faceAffine_standardSimplexVertices (n : ℕ) (i : Fin (n + 2)) :
    faceAffine n i ∘ standardSimplexVertices n =
      standardSimplexVertices (n + 1) ∘ i.succAbove := by
  funext j
  ext q
  simp only [faceAffine, affineSimplex_apply, standardSimplexVertices,
    Function.comp_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    change (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ) b *
      (Pi.single (i.succAbove b) (1 : ℝ) : Fin (n + 2) → ℝ) q = 0
    rw [Pi.single_eq_of_ne hbj]
    simp
  · simp

/-! ## Production-level assembly -/

/-- Mathlib's chosen coproduct of copies of `ℤ` in `AddCommGrpCat`, transported
through the equivalence with `ModuleCat ℤ`, is the usual direct sum. -/
noncomputable def addCommGrpCoproductIsoDirectSum (ι : Type) [DecidableEq ι] :
    (∐ fun _ : ι => AddCommGrpCat.of ℤ) ≅
      AddCommGrpCat.of (DirectSum ι fun _ => ℤ) :=
  let F := forget₂ (ModuleCat ℤ) AddCommGrpCat
  let ZM := fun _ : ι => ModuleCat.of ℤ ℤ
  (preservesColimitIso F (Discrete.functor ZM)).symm ≪≫
    Functor.mapIso F (ModuleCat.coprodIsoDirectSum ZM)

@[simp] theorem addCommGrpCoproductIsoDirectSum_generator
    {ι : Type} [DecidableEq ι] (i : ι) :
    Limits.Sigma.ι (fun _ : ι => AddCommGrpCat.of ℤ) i ≫
        (addCommGrpCoproductIsoDirectSum ι).hom =
      AddCommGrpCat.ofHom (DirectSum.of (fun _ : ι => ℤ) i) := by
  let F := forget₂ (ModuleCat ℤ) AddCommGrpCat
  let ZM := fun _ : ι => ModuleCat.of ℤ ℤ
  simp only [addCommGrpCoproductIsoDirectSum, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  change colimit.ι ((Discrete.functor ZM) ⋙ F) ⟨i⟩ ≫ _ ≫ _ = _
  slice_lhs 1 2 => rw [ι_preservesColimitIso_inv]
  change (forget₂ (ModuleCat ℤ) AddCommGrpCat).map (Limits.Sigma.ι ZM i) ≫
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
      (ModuleCat.coprodIsoDirectSum ZM).hom = _
  rw [← (forget₂ (ModuleCat ℤ) AddCommGrpCat).map_comp,
    ModuleCat.ι_coprodIsoDirectSum_hom]
  rfl

/-- The finitely-supported coefficient family of a production singular chain. -/
noncomputable def productionChainCoefficients
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (z : (SingularChains (TopCat.of X)).X n) :
    DirectSum (SingularSimplex (TopCat.of X) n) (fun _ => ℤ) := by
  letI := Classical.decEq (SingularSimplex (TopCat.of X) n)
  exact (addCommGrpCoproductIsoDirectSum
    (SingularSimplex (TopCat.of X) n)).hom z

/-- Every production singular chain has finite simplex support, exposed through
the direct-sum model of its categorical coproduct. -/
theorem productionChainCoefficients_finite
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (z : (SingularChains (TopCat.of X)).X n) :
    Set.Finite {σ | productionChainCoefficients n z σ ≠ 0} :=
  DFinsupp.finite_support _

def continuousMapOfSingularSimplex {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : SingularSimplex (TopCat.of X) n) :
    C(stdSimplex ℝ (Fin (n + 1)), X) :=
  TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌) σ

@[simp] theorem continuousMapOfSingularSimplex_ofContinuousMap
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    continuousMapOfSingularSimplex n
      (singularSimplexOfContinuousMap (TopCat.of X) n σ) = σ :=
  (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌)).apply_symm_apply σ

def singularSubdivisionDegree {X : Type} [TopologicalSpace X] (n : ℕ) :
    (SingularChains (TopCat.of X)).X n ⟶ (SingularChains (TopCat.of X)).X n := by
  change (∐ fun _ : SingularSimplex (TopCat.of X) n ↦ AddCommGrpCat.of ℤ) ⟶ _
  exact Limits.Sigma.desc fun σ =>
    vertexGenerator _ n (standardSimplexVertices n) ≫ vertexSubdivision n ≫
      vertexRealizationDegree n ≫
      (singularPostcomposition (continuousMapOfSingularSimplex n σ)).f n

@[simp, reassoc] theorem singularGenerator_singularSubdivisionDegree
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : SingularSimplex (TopCat.of X) n) :
    singularGenerator (TopCat.of X) n σ ≫ singularSubdivisionDegree n =
      vertexGenerator _ n (standardSimplexVertices n) ≫ vertexSubdivision n ≫
        vertexRealizationDegree n ≫
        (singularPostcomposition (continuousMapOfSingularSimplex n σ)).f n := by
  dsimp [singularGenerator, singularSubdivisionDegree]
  exact Limits.Sigma.ι_desc _ σ

def singularPrismDegree {X : Type} [TopologicalSpace X] (n : ℕ) :
    (SingularChains (TopCat.of X)).X n ⟶ (SingularChains (TopCat.of X)).X (n + 1) := by
  change (∐ fun _ : SingularSimplex (TopCat.of X) n ↦ AddCommGrpCat.of ℤ) ⟶ _
  exact Limits.Sigma.desc fun σ =>
    vertexGenerator _ n (standardSimplexVertices n) ≫ vertexPrism n ≫
      vertexRealizationDegree (n + 1) ≫
      (singularPostcomposition (continuousMapOfSingularSimplex n σ)).f (n + 1)

@[simp, reassoc] theorem singularGenerator_singularPrismDegree
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : SingularSimplex (TopCat.of X) n) :
    singularGenerator (TopCat.of X) n σ ≫ singularPrismDegree n =
      vertexGenerator _ n (standardSimplexVertices n) ≫ vertexPrism n ≫
        vertexRealizationDegree (n + 1) ≫
        (singularPostcomposition (continuousMapOfSingularSimplex n σ)).f (n + 1) := by
  dsimp [singularGenerator, singularPrismDegree]
  exact Limits.Sigma.ι_desc _ σ

/-- The four presentations of a single subdivided face give the same
production chain. -/
@[reassoc] theorem subdividedFace_transport {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    vertexGenerator _ n
          (standardSimplexVertices (n + 1) ∘ i.succAbove) ≫
        vertexSubdivision n ≫ vertexRealizationDegree n ≫
        (singularPostcomposition σ).f n =
      vertexGenerator _ n (standardSimplexVertices n) ≫
        vertexSubdivision n ≫ vertexRealizationDegree n ≫
        (singularPostcomposition (σ.comp (faceAffine n i))).f n := by
  rw [← faceAffine_standardSimplexVertices]
  rw [← vertexGenerator_vertexMapDegree]
  unfold faceAffine
  simp only [← Category.assoc]
  rw [show
    (vertexGenerator _ n (standardSimplexVertices n) ≫
        vertexMapDegree (affineSimplex
          (fun j => standardSimplexVertices (n + 1) (i.succAbove j))) n) ≫
        vertexSubdivision n =
      (vertexGenerator _ n (standardSimplexVertices n) ≫
        vertexSubdivision n) ≫
        vertexMapDegree (affineSimplex
          (fun j => standardSimplexVertices (n + 1) (i.succAbove j))) n by
      simp only [Category.assoc, vertexSubdivision_affine_natural]]
  simp only [Category.assoc]
  simp only [← Category.assoc]
  rw [show
    ((vertexGenerator _ n (standardSimplexVertices n) ≫ vertexSubdivision n) ≫
        vertexMapDegree (affineSimplex
          (fun j => standardSimplexVertices (n + 1) (i.succAbove j))) n) ≫
        vertexRealizationDegree n =
      ((vertexGenerator _ n (standardSimplexVertices n) ≫ vertexSubdivision n) ≫
        vertexRealizationDegree n) ≫
        (singularPostcomposition (affineSimplex
          (fun j => standardSimplexVertices (n + 1) (i.succAbove j)))).f n by
      simp only [Category.assoc, vertexRealization_affine_natural]]
  rw [Category.assoc]
  rw [← HomologicalComplex.comp_f, singularPostcomposition_comp]

theorem singularSubdivisionDegree_comm_d {X : Type} [TopologicalSpace X]
    (n : ℕ) :
    singularSubdivisionDegree (X := X) (n + 1) ≫
        (SingularChains (TopCat.of X)).d (n + 1) n =
      (SingularChains (TopCat.of X)).d (n + 1) n ≫
        singularSubdivisionDegree n := by
  apply Limits.Sigma.hom_ext
  intro s
  let σ := continuousMapOfSingularSimplex (n + 1) s
  have hs : singularSimplexOfContinuousMap (TopCat.of X) (n + 1) σ = s :=
    (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n + 1⦌)).symm_apply_apply s
  change (singularGenerator (TopCat.of X) (n + 1) s ≫
      singularSubdivisionDegree (n + 1)) ≫ _ =
    (singularGenerator (TopCat.of X) (n + 1) s ≫ _) ≫
      singularSubdivisionDegree n
  rw [← hs, singularGenerator_singularSubdivisionDegree]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap, Category.assoc]
  rw [(singularPostcomposition σ).comm]
  slice_lhs 3 4 =>
    change (vertexRealization (ι := Fin (n + 1 + 1))).f (n + 1) ≫ _
    rw [(vertexRealization (ι := Fin (n + 1 + 1))).comm]
  slice_lhs 2 3 => rw [vertexSubdivision_comm_d]
  simp only [← Category.assoc]
  rw [vertexGenerator_boundary, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp]
  rw [singularGenerator_boundary, Preadditive.sum_comp]
  simp only [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.zsmul_comp]
  rw [singularSimplexOfContinuousMap_face]
  slice_rhs 1 2 => rw [Preadditive.zsmul_comp]
  rw [singularGenerator_singularSubdivisionDegree]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap,
    Preadditive.zsmul_comp]
  congr 1
  exact subdividedFace_transport n σ i

def singularSubdivision {X : Type} [TopologicalSpace X] :
    SingularChains (TopCat.of X) ⟶ SingularChains (TopCat.of X) where
  f := singularSubdivisionDegree
  comm' i j h := by
    obtain rfl := h
    exact singularSubdivisionDegree_comm_d j

theorem vertexRealization_comp_singularSubdivision
    {ι : Type} [Fintype ι] (n : ℕ) :
    vertexRealizationDegree (ι := ι) n ≫ singularSubdivisionDegree n =
      vertexSubdivision n ≫ vertexRealizationDegree n := by
  classical
  apply Limits.Sigma.hom_ext
  intro v
  change (vertexGenerator _ n v ≫ vertexRealizationDegree n) ≫ _ = _
  rw [vertexGenerator_vertexRealizationDegree]
  dsimp [affineGenerator]
  rw [singularGenerator_singularSubdivisionDegree]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap]
  simp only [← Category.assoc]
  slice_lhs 3 4 => rw [vertexRealization_affine_natural]
  slice_lhs 2 3 => rw [vertexSubdivision_affine_natural]
  simp only [← Category.assoc]
  rw [vertexGenerator_vertexMapDegree]
  have hv : affineSimplex v ∘ standardSimplexVertices n = v := by
    funext i
    change affineSimplex v (standardSimplexVertices n i) = v i
    ext j
    simp only [affineSimplex_apply, standardSimplexVertices]
    change ∑ q, (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) q * v q j = v i j
    simp [Pi.single_apply]
  change (vertexGenerator _ n
      ((fun x => affineSimplex v x) ∘ standardSimplexVertices n) ≫ _) ≫ _ = _
  rw [hv]
  change vertexGenerator _ n v ≫ vertexSubdivision n ≫
    vertexRealizationDegree n = vertexGenerator _ n v ≫
      vertexSubdivision n ≫ vertexRealizationDegree n
  rfl

def singularSubdivisionIterate {X : Type} [TopologicalSpace X] (n : ℕ) :
    ℕ → ((SingularChains (TopCat.of X)).X n ⟶
      (SingularChains (TopCat.of X)).X n) := fun k =>
  Nat.rec (𝟙 _) (fun _ r => r ≫ singularSubdivisionDegree n) k

theorem vertexRealization_comp_singularSubdivisionIterate
    {ι : Type} [Fintype ι] (n k : ℕ) :
    vertexRealizationDegree (ι := ι) n ≫ singularSubdivisionIterate n k =
      vertexSubdivisionIterate n k ≫ vertexRealizationDegree n := by
  induction k with
  | zero => simp [singularSubdivisionIterate, vertexSubdivisionIterate]
  | succ k ih =>
      simp only [singularSubdivisionIterate, vertexSubdivisionIterate,
        ← Category.assoc]
      change (vertexRealizationDegree n ≫ singularSubdivisionIterate n k) ≫ _ = _
      rw [ih]
      simp only [Category.assoc]
      rw [vertexRealization_comp_singularSubdivision]
      rfl

/-! ## Cover-small production chains -/

def coverSubspaceInclusion {X α : Type} [TopologicalSpace X]
    (U : α → Set X) (a : α) : TopCat.of (U a) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The simplicial subset consisting of simplices factoring through one cover
member.  Being a simplicial subcomplex makes face closure structural. -/
def coverSmallSSet {X α : Type} [TopologicalSpace X] (U : α → Set X) :
    (TopCat.toSSet.obj (TopCat.of X)).Subcomplex :=
  ⨆ a, SSet.Subcomplex.range
    (TopCat.toSSet.map (coverSubspaceInclusion U a))

/-- The production subcomplex generated by simplices whose image lies in one
member of `U`. -/
noncomputable def coverSmallChains {X α : Type} [TopologicalSpace X]
    (U : α → Set X) : ChainComplex AddCommGrpCat ℕ :=
  ((AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).obj (coverSmallSSet U : SSet)

/-- Inclusion of cover-small chains into the production singular complex. -/
noncomputable def coverSmallChains.ι {X α : Type} [TopologicalSpace X]
    (U : α → Set X) :
    coverSmallChains U ⟶ SingularChains (TopCat.of X) :=
  ((AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).map (coverSmallSSet U).ι

def liftSimplexToCover {X α : Type} [TopologicalSpace X]
    (U : α → Set X) {n : ℕ}
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (a : α)
    (hσ : Set.range σ ⊆ U a) :
    C(stdSimplex ℝ (Fin (n + 1)), U a) where
  toFun x := ⟨σ x, hσ (Set.mem_range_self x)⟩
  continuous_toFun := continuous_induced_rng.mpr σ.continuous

/-- A simplex subordinate to one cover member has a canonical generator in
the small-chain subcomplex, and its inclusion is the production generator. -/
noncomputable def coverSmallGenerator {X α : Type} [TopologicalSpace X]
    (U : α → Set X) {n : ℕ}
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (a : α)
    (hσ : Set.range σ ⊆ U a) :
    AddCommGrpCat.of ℤ ⟶ (coverSmallChains U).X n := by
  let τ := singularSimplexOfContinuousMap (TopCat.of (U a)) n
    (liftSimplexToCover U σ a hσ)
  let f := TopCat.toSSet.map (coverSubspaceInclusion U a)
  have hmapped : f.app (Opposite.op ⦋n⦌) τ =
      singularSimplexOfContinuousMap (TopCat.of X) n σ := by
    change (TopCat.toSSetObjEquiv (TopCat.of X) _).symm
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U a, X)).comp
        (liftSimplexToCover U σ a hσ)) = _
    congr 1
  have hmem : singularSimplexOfContinuousMap (TopCat.of X) n σ ∈
      (coverSmallSSet U).obj (Opposite.op ⦋n⦌) := by
    rw [← hmapped]
    apply (le_iSup (fun a => SSet.Subcomplex.range
      (TopCat.toSSet.map (coverSubspaceInclusion U a))) a)
    exact ⟨τ, rfl⟩
  change AddCommGrpCat.of ℤ ⟶
    ∐ fun _ : (coverSmallSSet U).obj (Opposite.op ⦋n⦌) => AddCommGrpCat.of ℤ
  let sSmall : (coverSmallSSet U : SSet).obj (Opposite.op ⦋n⦌) :=
    ⟨singularSimplexOfContinuousMap (TopCat.of X) n σ, hmem⟩
  exact Limits.Sigma.ι
    (fun _ : (coverSmallSSet U : SSet).obj (Opposite.op ⦋n⦌) =>
      AddCommGrpCat.of ℤ) sSmall

@[reassoc] theorem coverSmallGenerator_comp_ι
    {X α : Type} [TopologicalSpace X]
    (U : α → Set X) {n : ℕ}
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (a : α)
    (hσ : Set.range σ ⊆ U a) :
    coverSmallGenerator U σ a hσ ≫ (coverSmallChains.ι U).f n =
      singularGenerator (TopCat.of X) n
        (singularSimplexOfContinuousMap (TopCat.of X) n σ) := by
  dsimp [coverSmallGenerator, coverSmallChains.ι, coverSmallChains,
    SingularChains, AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  rw [Limits.Sigma.ι_comp_map']
  rfl

/-- The small-chain generator attached directly to membership in the
subordinate simplicial subset. -/
noncomputable def coverSmallGeneratorOfMem {X α : Type} [TopologicalSpace X]
    (U : α → Set X) {n : ℕ} (s : SingularSimplex (TopCat.of X) n)
    (hs : s ∈ (coverSmallSSet U).obj
      (Opposite.op (SimplexCategory.mk n))) :
    AddCommGrpCat.of ℤ ⟶ (coverSmallChains U).X n := by
  change AddCommGrpCat.of ℤ ⟶
    ∐ fun _ : (coverSmallSSet U).obj
      (Opposite.op (SimplexCategory.mk n)) ↦ AddCommGrpCat.of ℤ
  let t : (coverSmallSSet U).obj
      (Opposite.op (SimplexCategory.mk n)) := ⟨s, hs⟩
  exact Limits.Sigma.ι
    (fun _ : (coverSmallSSet U).obj
      (Opposite.op (SimplexCategory.mk n)) ↦ AddCommGrpCat.of ℤ) t

@[reassoc] theorem coverSmallGeneratorOfMem_comp_ι
    {X α : Type} [TopologicalSpace X]
    (U : α → Set X) {n : ℕ} (s : SingularSimplex (TopCat.of X) n)
    (hs : s ∈ (coverSmallSSet U).obj
      (Opposite.op (SimplexCategory.mk n))) :
    coverSmallGeneratorOfMem U s hs ≫ (coverSmallChains.ι U).f n =
      singularGenerator (TopCat.of X) n s := by
  dsimp [coverSmallGeneratorOfMem, coverSmallChains.ι, coverSmallChains,
    SingularChains, AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  rw [Limits.Sigma.ι_comp_map']
  rfl

/-- Realization of a finitely-supported family indexed by production
simplices. -/
def finiteProductionChainRealize {X : Type} [TopologicalSpace X] (n : ℕ)
    (c : SingularSimplex (TopCat.of X) n →₀ ℤ) :
    AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X n :=
  c.sum fun s z => z • singularGenerator (TopCat.of X) n s

@[simp] theorem finiteProductionChainRealize_single
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (s : SingularSimplex (TopCat.of X) n) (z : ℤ) :
    finiteProductionChainRealize n (Finsupp.single s z) =
      z • singularGenerator (TopCat.of X) n s := by
  classical
  simp [finiteProductionChainRealize]

@[simp] theorem finiteProductionChainRealize_add
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (c d : SingularSimplex (TopCat.of X) n →₀ ℤ) :
    finiteProductionChainRealize n (c + d) =
      finiteProductionChainRealize n c + finiteProductionChainRealize n d := by
  classical
  unfold finiteProductionChainRealize
  apply Finsupp.sum_add_index
  · intro s
    simp
  · intro s _ z₁ z₂
    simp [add_smul]

/-- A finite production chain supported on subordinate simplices factors
through the concrete small-chain complex. -/
theorem finiteProductionChainRealize_factors
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n : ℕ)
    (c : SingularSimplex (TopCat.of X) n →₀ ℤ)
    (hc : ∀ s ∈ c.support,
      s ∈ (coverSmallSSet U).obj
        (Opposite.op (SimplexCategory.mk n))) :
    ∃ q : AddCommGrpCat.of ℤ ⟶ (coverSmallChains U).X n,
      q ≫ (coverSmallChains.ι U).f n = finiteProductionChainRealize n c := by
  classical
  induction c using Finsupp.induction with
  | zero => exact ⟨0, by simp [finiteProductionChainRealize]⟩
  | single_add s z c hsc hz ih =>
      have hs : s ∈ (coverSmallSSet U).obj
          (Opposite.op (SimplexCategory.mk n)) :=
        hc s (by
          have hcs : c s = 0 := by
            simpa only [Finsupp.mem_support_iff, not_not] using hsc
          simp [Finsupp.mem_support_iff, hcs, hz])
      have hc' : ∀ t ∈ c.support,
          t ∈ (coverSmallSSet U).obj
            (Opposite.op (SimplexCategory.mk n)) := by
        intro t ht
        apply hc t
        apply Finsupp.mem_support_iff.mpr
        have hts : t ≠ s := fun h => hsc (h ▸ ht)
        have hct : c t ≠ 0 := Finsupp.mem_support_iff.mp ht
        simp [hts, hct]
      obtain ⟨q, hq⟩ := ih hc'
      refine ⟨z • coverSmallGeneratorOfMem U s hs + q, ?_⟩
      rw [Preadditive.add_comp, Preadditive.zsmul_comp,
        coverSmallGeneratorOfMem_comp_ι, hq]
      rw [← finiteProductionChainRealize_single,
        ← finiteProductionChainRealize_add]

/-- Finite realization followed by the coproduct coordinate isomorphism is
the morphism represented by the same direct-sum coefficient family. -/
theorem finiteProductionChainRealize_comp_coproductIso
    {X : Type} [TopologicalSpace X] (n : ℕ)
    [DecidableEq (SingularSimplex (TopCat.of X) n)]
    (c : DirectSum (SingularSimplex (TopCat.of X) n) (fun _ => ℤ)) :
    finiteProductionChainRealize n (DFinsupp.toFinsupp c) ≫
        (addCommGrpCoproductIsoDirectSum
          (SingularSimplex (TopCat.of X) n)).hom =
      AddCommGrpCat.asHom c := by
  classical
  induction c using DFinsupp.induction with
  | h0 =>
      apply AddCommGrpCat.int_hom_ext
      simp [DFinsupp.toFinsupp_zero, finiteProductionChainRealize,
        AddCommGrpCat.asHom]
      rfl
  | ha s a c hs ha ih =>
      rw [DFinsupp.toFinsupp_add, DFinsupp.toFinsupp_single,
        finiteProductionChainRealize_add, Preadditive.add_comp]
      rw [finiteProductionChainRealize_single]
      dsimp [singularGenerator]
      have hz : (a • Limits.Sigma.ι
          (fun _ : SingularSimplex (TopCat.of X) n ↦ AddCommGrpCat.of ℤ) s) ≫
          (addCommGrpCoproductIsoDirectSum
            (SingularSimplex (TopCat.of X) n)).hom =
          a • (Limits.Sigma.ι
            (fun _ : SingularSimplex (TopCat.of X) n ↦ AddCommGrpCat.of ℤ) s ≫
            (addCommGrpCoproductIsoDirectSum
              (SingularSimplex (TopCat.of X) n)).hom) :=
        Preadditive.zsmul_comp _ _ a
      refine (congrArg (fun f => f +
        finiteProductionChainRealize n (DFinsupp.toFinsupp c) ≫
          (addCommGrpCoproductIsoDirectSum
            (SingularSimplex (TopCat.of X) n)).hom) hz).trans ?_
      have hgen : Limits.Sigma.ι
          (fun _ : SingularSimplex (TopCat.of X) n ↦ AddCommGrpCat.of ℤ) s ≫
          (addCommGrpCoproductIsoDirectSum
            (SingularSimplex (TopCat.of X) n)).hom =
          AddCommGrpCat.ofHom (DirectSum.of
            (fun _ : SingularSimplex (TopCat.of X) n => ℤ) s) :=
        addCommGrpCoproductIsoDirectSum_generator s
      rw [ih]
      apply AddCommGrpCat.int_hom_ext
      rw [hgen]
      simp [AddCommGrpCat.asHom]
      congr 1
      rw [← (DirectSum.of
        (fun _ : SingularSimplex (TopCat.of X) n => ℤ) s).map_zsmul]
      simp
      ext t
      by_cases h : s = t <;> simp [DirectSum.of_apply, h]

/-- The finite-support coefficients of an arbitrary production-chain element. -/
noncomputable def productionChainFinsupp
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (z : (SingularChains (TopCat.of X)).X n) :
    SingularSimplex (TopCat.of X) n →₀ ℤ := by
  letI := Classical.decEq (SingularSimplex (TopCat.of X) n)
  exact DFinsupp.toFinsupp (productionChainCoefficients n z)

/-- Reassembling the finite-support coefficients of an arbitrary production
chain gives that chain back. -/
theorem finiteProductionChainRealize_productionChainFinsupp
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (z : (SingularChains (TopCat.of X)).X n) :
    finiteProductionChainRealize n (productionChainFinsupp n z) =
      AddCommGrpCat.asHom z := by
  classical
  let e := addCommGrpCoproductIsoDirectSum
    (SingularSimplex (TopCat.of X) n)
  apply (cancel_mono e.hom).1
  change finiteProductionChainRealize n
      (DFinsupp.toFinsupp (e.hom z)) ≫ e.hom =
    AddCommGrpCat.asHom z ≫ e.hom
  rw [finiteProductionChainRealize_comp_coproductIso]
  apply AddCommGrpCat.int_hom_ext
  simp [AddCommGrpCat.asHom]
  rfl

/-- Every production-chain element whose finite coefficient support is
subordinate factors through the small-chain inclusion. -/
theorem productionChain_factors_coverSmallChains
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n : ℕ)
    (z : (SingularChains (TopCat.of X)).X n)
    (hz : ∀ s ∈ (productionChainFinsupp n z).support,
      s ∈ (coverSmallSSet U).obj
        (Opposite.op (SimplexCategory.mk n))) :
    ∃ q : AddCommGrpCat.of ℤ ⟶ (coverSmallChains U).X n,
      q ≫ (coverSmallChains.ι U).f n = AddCommGrpCat.asHom z := by
  obtain ⟨q, hq⟩ := finiteProductionChainRealize_factors U n
    (productionChainFinsupp n z) hz
  refine ⟨q, ?_⟩
  rw [hq, finiteProductionChainRealize_productionChainFinsupp]

theorem prismFace_transport {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    vertexGenerator _ n
          (standardSimplexVertices (n + 1) ∘ i.succAbove) ≫
        vertexPrism n ≫ vertexRealizationDegree (n + 1) ≫
        (singularPostcomposition σ).f (n + 1) =
      vertexGenerator _ n (standardSimplexVertices n) ≫
        vertexPrism n ≫ vertexRealizationDegree (n + 1) ≫
        (singularPostcomposition (σ.comp (faceAffine n i))).f (n + 1) := by
  rw [← faceAffine_standardSimplexVertices]
  rw [← vertexGenerator_vertexMapDegree]
  unfold faceAffine
  simp only [← Category.assoc]
  slice_lhs 2 3 => rw [← vertexPrism_affine_natural]
  slice_lhs 3 4 => rw [← vertexRealization_affine_natural]
  slice_lhs 4 5 =>
    rw [← HomologicalComplex.comp_f, singularPostcomposition_comp]
  simp only [Category.assoc]

theorem standardVertexRealization_postcomposition
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    vertexGenerator _ n (standardSimplexVertices n) ≫
        vertexRealizationDegree n ≫ (singularPostcomposition σ).f n =
      singularGenerator (TopCat.of X) n
        (singularSimplexOfContinuousMap (TopCat.of X) n σ) := by
  simp only [← Category.assoc]
  rw [vertexGenerator_vertexRealizationDegree]
  dsimp [affineGenerator]
  rw [singularGenerator_singularPostcomposition]
  rw [affineSimplex_standardSimplexVertices]
  rfl

def singularPrismCorrection {X : Type} [TopologicalSpace X] (n : ℕ) :
    (SingularChains (TopCat.of X)).X n ⟶
      (SingularChains (TopCat.of X)).X n :=
  match n with
  | 0 => 0
  | n + 1 => (SingularChains (TopCat.of X)).d (n + 1) n ≫
      singularPrismDegree n

theorem singularGenerator_prismCorrection_succ
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 2)), X)) :
    singularGenerator (TopCat.of X) (n + 1)
          (singularSimplexOfContinuousMap (TopCat.of X) (n + 1) σ) ≫
        singularPrismCorrection (n + 1) =
      vertexGenerator _ (n + 1) (standardSimplexVertices (n + 1)) ≫
        vertexPrismCorrection (n + 1) ≫ vertexRealizationDegree (n + 1) ≫
        (singularPostcomposition σ).f (n + 1) := by
  change singularGenerator _ _ _ ≫
      ((SingularChains (TopCat.of X)).d (n + 1) n ≫ singularPrismDegree n) = _
  rw [show vertexPrismCorrection (ι := Fin (n + 2)) (n + 1) =
    (VertexChains (stdSimplex ℝ (Fin (n + 2)))).d (n + 1) n ≫
      vertexPrism n from rfl]
  simp only [← Category.assoc]
  rw [singularGenerator_boundary, Preadditive.sum_comp]
  rw [vertexGenerator_boundary, Preadditive.sum_comp]
  rw [Preadditive.sum_comp, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [singularSimplexOfContinuousMap_face]
  rw [singularGenerator_singularPrismDegree]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap]
  exact (prismFace_transport n σ i).symm

theorem singularGenerator_prism_boundary
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    singularGenerator (TopCat.of X) n
          (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫
        singularPrismDegree n ≫
        (SingularChains (TopCat.of X)).d (n + 1) n =
      vertexGenerator _ n (standardSimplexVertices n) ≫ vertexPrism n ≫
        (VertexChains (stdSimplex ℝ (Fin (n + 1)))).d (n + 1) n ≫
        vertexRealizationDegree n ≫ (singularPostcomposition σ).f n := by
  simp only [← Category.assoc]
  rw [singularGenerator_singularPrismDegree]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap, Category.assoc]
  rw [(singularPostcomposition σ).comm]
  slice_lhs 3 4 =>
    change (vertexRealization (ι := Fin (n + 1))).f (n + 1) ≫ _
    rw [(vertexRealization (ι := Fin (n + 1))).comm]
  simp only [vertexRealization, Category.assoc]

theorem singularGenerator_prismCorrection
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    singularGenerator (TopCat.of X) n
          (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫
        singularPrismCorrection n =
      vertexGenerator _ n (standardSimplexVertices n) ≫
        vertexPrismCorrection n ≫ vertexRealizationDegree n ≫
        (singularPostcomposition σ).f n := by
  cases n with
  | zero => simp [singularPrismCorrection, vertexPrismCorrection]
  | succ n => exact singularGenerator_prismCorrection_succ n σ

theorem singularPrism_identity {X : Type} [TopologicalSpace X] (n : ℕ) :
    singularPrismDegree (X := X) n ≫
        (SingularChains (TopCat.of X)).d (n + 1) n +
      singularPrismCorrection n = singularSubdivisionDegree n - 𝟙 _ := by
  apply Limits.Sigma.hom_ext
  intro s
  let σ := continuousMapOfSingularSimplex n s
  have hs : singularSimplexOfContinuousMap (TopCat.of X) n σ = s :=
    (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌)).symm_apply_apply s
  rw [← hs]
  change singularGenerator (TopCat.of X) n
      (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫
        (_ + _) = singularGenerator (TopCat.of X) n
      (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫ (_ - _)
  rw [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id]
  rw [singularGenerator_prism_boundary]
  rw [singularGenerator_prismCorrection]
  rw [singularGenerator_singularSubdivisionDegree]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap]
  rw [← standardVertexRealization_postcomposition]
  have h := vertexPrism_identity (ι := Fin (n + 1)) n
  apply_fun (fun f => vertexGenerator _ n (standardSimplexVertices n) ≫
    f ≫ vertexRealizationDegree n ≫ (singularPostcomposition σ).f n) at h
  simpa only [Preadditive.comp_add, Preadditive.comp_sub,
    Preadditive.add_comp, Preadditive.sub_comp, Category.comp_id,
    Category.id_comp, Category.assoc] using h

theorem productionCycle_homologous_to_subdivision
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (z : AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X (n + 1))
    (hz : z ≫ (SingularChains (TopCat.of X)).d (n + 1) n = 0) :
    ∃ b : AddCommGrpCat.of ℤ ⟶
        (SingularChains (TopCat.of X)).X (n + 2),
      z ≫ singularSubdivisionDegree (n + 1) - z =
        b ≫ (SingularChains (TopCat.of X)).d (n + 2) (n + 1) := by
  refine ⟨z ≫ singularPrismDegree (n + 1), ?_⟩
  have h := singularPrism_identity (X := X) (n + 1)
  rw [show singularPrismCorrection (X := X) (n + 1) =
    (SingularChains (TopCat.of X)).d (n + 1) n ≫
      singularPrismDegree n from rfl] at h
  apply_fun (fun f => z ≫ f) at h
  simp only [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id,
    ← Category.assoc, hz, zero_comp, add_zero] at h
  exact h.symm

/-- Iterated subdivision commutes with the production differential. -/
theorem singularSubdivisionIterate_comm_d
    {X : Type} [TopologicalSpace X] (n k : ℕ) :
    singularSubdivisionIterate (X := X) (n + 1) k ≫
        (SingularChains (TopCat.of X)).d (n + 1) n =
      (SingularChains (TopCat.of X)).d (n + 1) n ≫
        singularSubdivisionIterate n k := by
  induction k with
  | zero => simp [singularSubdivisionIterate]
  | succ k ih =>
      simp only [singularSubdivisionIterate, Category.assoc]
      rw [singularSubdivisionDegree_comm_d]
      change (singularSubdivisionIterate (X := X) (n + 1) k ≫
        (SingularChains (TopCat.of X)).d (n + 1) n) ≫
          singularSubdivisionDegree n = _
      rw [ih]
      rfl

/-- A production cycle is homologous to every iterated subdivision of it. -/
theorem productionCycle_homologous_to_iteratedSubdivision
    {X : Type} [TopologicalSpace X] (n k : ℕ)
    (z : AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X (n + 1))
    (hz : z ≫ (SingularChains (TopCat.of X)).d (n + 1) n = 0) :
    ∃ b : AddCommGrpCat.of ℤ ⟶
        (SingularChains (TopCat.of X)).X (n + 2),
      z ≫ singularSubdivisionIterate (n + 1) k - z =
        b ≫ (SingularChains (TopCat.of X)).d (n + 2) (n + 1) := by
  induction k with
  | zero =>
      refine ⟨0, ?_⟩
      simp [singularSubdivisionIterate]
  | succ k ih =>
      obtain ⟨b, hb⟩ := ih
      have hzk : (z ≫ singularSubdivisionIterate (n + 1) k) ≫
          (SingularChains (TopCat.of X)).d (n + 1) n = 0 := by
        rw [Category.assoc, singularSubdivisionIterate_comm_d,
          ← Category.assoc, hz, zero_comp]
      obtain ⟨c, hc⟩ := productionCycle_homologous_to_subdivision n
        (z ≫ singularSubdivisionIterate (n + 1) k) hzk
      refine ⟨c + b, ?_⟩
      calc
        z ≫ singularSubdivisionIterate (n + 1) (k + 1) - z =
            ((z ≫ singularSubdivisionIterate (n + 1) k) ≫
                singularSubdivisionDegree (n + 1) -
              z ≫ singularSubdivisionIterate (n + 1) k) +
            (z ≫ singularSubdivisionIterate (n + 1) k - z) := by
              simp only [singularSubdivisionIterate, Category.assoc]
              abel
        _ = c ≫ (SingularChains (TopCat.of X)).d (n + 2) (n + 1) +
            b ≫ (SingularChains (TopCat.of X)).d (n + 2) (n + 1) := by
              rw [hc, hb]
        _ = (c + b) ≫
            (SingularChains (TopCat.of X)).d (n + 2) (n + 1) := by
              rw [Preadditive.add_comp]

def finiteSingularChainRealize {X : Type} [TopologicalSpace X] (n : ℕ)
    (c : C(stdSimplex ℝ (Fin (n + 1)), X) →₀ ℤ) :
    AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X n :=
  c.sum fun σ z => z • singularGenerator (TopCat.of X) n
    (singularSimplexOfContinuousMap (TopCat.of X) n σ)

@[simp] theorem finiteSingularChainRealize_single
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (z : ℤ) :
    finiteSingularChainRealize n (Finsupp.single σ z) =
      z • singularGenerator (TopCat.of X) n
        (singularSimplexOfContinuousMap (TopCat.of X) n σ) := by
  classical
  simp [finiteSingularChainRealize]

@[simp] theorem finiteSingularChainRealize_add
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (c d : C(stdSimplex ℝ (Fin (n + 1)), X) →₀ ℤ) :
    finiteSingularChainRealize n (c + d) =
      finiteSingularChainRealize n c + finiteSingularChainRealize n d := by
  classical
  unfold finiteSingularChainRealize
  apply Finsupp.sum_add_index
  · intro a _
    simp
  · intro a _ b₁ b₂
    simp [add_smul]

/-- A represented simplex whose image is contained in one cover member is a
simplex of the cover-small simplicial subset. -/
theorem singularSimplex_mem_coverSmallSSet_of_range_subset
    {X α : Type} [TopologicalSpace X] (U : α → Set X) {n : ℕ}
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (a : α)
    (hσ : Set.range σ ⊆ U a) :
    singularSimplexOfContinuousMap (TopCat.of X) n σ ∈
      (coverSmallSSet U).obj (Opposite.op (SimplexCategory.mk n)) := by
  let τ := singularSimplexOfContinuousMap (TopCat.of (U a)) n
    (liftSimplexToCover U σ a hσ)
  let f := TopCat.toSSet.map (coverSubspaceInclusion U a)
  have hmapped : f.app (Opposite.op ⦋n⦌) τ =
      singularSimplexOfContinuousMap (TopCat.of X) n σ := by
    change (TopCat.toSSetObjEquiv (TopCat.of X) _).symm
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U a, X)).comp
        (liftSimplexToCover U σ a hσ)) = _
    congr 1
  rw [← hmapped]
  apply (le_iSup (fun a => SSet.Subcomplex.range
    (TopCat.toSSet.map (coverSubspaceInclusion U a))) a)
  exact ⟨τ, rfl⟩

/-- Membership in the concrete cover-small simplicial subset exposes an
actual cover member containing the represented simplex. -/
theorem range_subset_of_singularSimplex_mem_coverSmallSSet
    {X α : Type} [TopologicalSpace X] (U : α → Set X) {n : ℕ}
    (s : SingularSimplex (TopCat.of X) n)
    (hs : s ∈ (coverSmallSSet U).obj
      (Opposite.op (SimplexCategory.mk n))) :
    ∃ a, Set.range (continuousMapOfSingularSimplex n s) ⊆ U a := by
  simp only [coverSmallSSet, Subfunctor.iSup_obj, Subfunctor.range_obj,
    Set.mem_iUnion, Set.mem_range] at hs
  obtain ⟨a, t, rfl⟩ := hs
  refine ⟨a, ?_⟩
  rintro _ ⟨x, rfl⟩
  change ((continuousMapOfSingularSimplex n
    ((TopCat.toSSet.map (coverSubspaceInclusion U a)).app
      (Opposite.op (SimplexCategory.mk n)) t)) x) ∈ U a
  change ((continuousMapOfSingularSimplex n t) x : X) ∈ U a
  exact (continuousMapOfSingularSimplex n t x).property

/-- A finite represented chain supported on cover-subordinate simplices
factors through the cover-small complex. -/
theorem finiteSingularChainRealize_factors
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n : ℕ)
    (c : C(stdSimplex ℝ (Fin (n + 1)), X) →₀ ℤ)
    (hc : ∀ σ ∈ c.support, ∃ a, Set.range σ ⊆ U a) :
    ∃ q : AddCommGrpCat.of ℤ ⟶ (coverSmallChains U).X n,
      q ≫ (coverSmallChains.ι U).f n = finiteSingularChainRealize n c := by
  classical
  induction c using Finsupp.induction with
  | zero => exact ⟨0, by simp [finiteSingularChainRealize]⟩
  | single_add σ z c hσc hz ih =>
      obtain ⟨a, ha⟩ := hc σ (by
        have hcσ : c σ = 0 := by
          simpa only [Finsupp.mem_support_iff, not_not] using hσc
        simp [Finsupp.mem_support_iff, hcσ, hz])
      have hc' : ∀ τ ∈ c.support, ∃ a, Set.range τ ⊆ U a := by
        intro τ hτ
        apply hc τ
        apply Finsupp.mem_support_iff.mpr
        have hτσ : τ ≠ σ := fun h => hσc (h ▸ hτ)
        have hct : c τ ≠ 0 := Finsupp.mem_support_iff.mp hτ
        simp [hτσ, hct]
      obtain ⟨q, hq⟩ := ih hc'
      refine ⟨z • coverSmallGenerator U σ a ha + q, ?_⟩
      rw [Preadditive.add_comp, Preadditive.zsmul_comp,
        coverSmallGenerator_comp_ι, hq]
      rw [← finiteSingularChainRealize_single,
        ← finiteSingularChainRealize_add]

theorem postcomposeFiniteVertexChain_realize
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (n : ℕ) (σ : C(stdSimplex ℝ ι, X))
    (c : FiniteVertexChain (stdSimplex ℝ ι) n) :
    finiteSingularChainRealize n (postcomposeFiniteVertexChain σ c) =
      FiniteVertexChain.realize c ≫ vertexRealizationDegree n ≫
        (singularPostcomposition σ).f n := by
  classical
  induction c using Finsupp.induction with
  | zero => simp [postcomposeFiniteVertexChain, finiteSingularChainRealize,
      FiniteVertexChain.realize]
  | single_add v z c hvc hz ih =>
      simp only [postcomposeFiniteVertexChain, Finsupp.mapDomain_add,
        Finsupp.mapDomain_single, finiteSingularChainRealize_add,
        finiteSingularChainRealize_single, FiniteVertexChain.realize_add,
        FiniteVertexChain.realize_single, Preadditive.add_comp]
      congr 1
      simp only [Preadditive.zsmul_comp]
      congr 1
      simp only [← Category.assoc]
      rw [vertexGenerator_vertexRealizationDegree]
      dsimp [affineGenerator]
      rw [singularGenerator_singularPostcomposition]

theorem singularSubdivision_natural {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) :
    (singularPostcomposition f).f n ≫ singularSubdivisionDegree n =
      singularSubdivisionDegree n ≫ (singularPostcomposition f).f n := by
  apply Limits.Sigma.hom_ext
  intro s
  let σ := continuousMapOfSingularSimplex n s
  have hs : singularSimplexOfContinuousMap (TopCat.of X) n σ = s :=
    (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌)).symm_apply_apply s
  rw [← hs]
  change (singularGenerator (TopCat.of X) n
    (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫
      (singularPostcomposition f).f n) ≫ _ = _
  rw [singularGenerator_singularPostcomposition]
  rw [singularGenerator_singularSubdivisionDegree]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap]
  change _ = (singularGenerator (TopCat.of X) n
    (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫
      singularSubdivisionDegree n) ≫ _
  rw [singularGenerator_singularSubdivisionDegree]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap]
  have hcomp := congrArg (fun q => q.f n)
    (singularPostcomposition_comp σ f)
  change (singularPostcomposition σ).f n ≫
    (singularPostcomposition f).f n =
      (singularPostcomposition (f.comp σ)).f n at hcomp
  simp only [Category.assoc]
  rw [hcomp]

theorem singularSubdivisionIterate_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n k : ℕ) :
    (singularPostcomposition f).f n ≫ singularSubdivisionIterate n k =
      singularSubdivisionIterate n k ≫ (singularPostcomposition f).f n := by
  induction k with
  | zero => simp [singularSubdivisionIterate]
  | succ k ih =>
      simp only [singularSubdivisionIterate, Category.assoc]
      change ((singularPostcomposition f).f n ≫
        singularSubdivisionIterate n k) ≫ _ = _
      rw [ih]
      slice_lhs 2 3 => rw [singularSubdivision_natural]
      rfl

theorem singularGenerator_iteratedSubdivision_realize
    {X : Type} [TopologicalSpace X] (n k : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    singularGenerator (TopCat.of X) n
          (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫
        singularSubdivisionIterate n k =
      finiteSingularChainRealize n
        (postcomposedIteratedSubdivision n k σ) := by
  unfold postcomposedIteratedSubdivision
  rw [postcomposeFiniteVertexChain_realize]
  rw [iteratedFiniteVertexSubdivision_realize]
  rw [← standardVertexRealization_postcomposition]
  simp only [Category.assoc]
  rw [singularSubdivisionIterate_natural]
  slice_lhs 2 3 => rw [vertexRealization_comp_singularSubdivisionIterate]
  rfl

/-- The production prism on one represented simplex is exactly the realization
of its finite-support postcomposed prism. -/
theorem singularGenerator_prism_realize
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    singularGenerator (TopCat.of X) n
          (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫
        singularPrismDegree n =
      finiteSingularChainRealize (n + 1) (postcomposedPrism n σ) := by
  unfold postcomposedPrism
  rw [postcomposeFiniteVertexChain_realize]
  rw [finiteVertexPrism_realize]
  rw [singularGenerator_singularPrismDegree]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap]
  rfl

def iteratedSubdivisionRealizationDegree
    {X : Type} [TopologicalSpace X] (n k : ℕ) :
    (SingularChains (TopCat.of X)).X n ⟶
      (SingularChains (TopCat.of X)).X n := by
  change (∐ fun _ : SingularSimplex (TopCat.of X) n =>
    AddCommGrpCat.of ℤ) ⟶ _
  exact Limits.Sigma.desc fun s => finiteSingularChainRealize n
    (postcomposedIteratedSubdivision n k
      (continuousMapOfSingularSimplex n s))

/-- Iterated subdivision on every production chain is exactly the linear
extension of the finite-support postcomposed construction. -/
theorem singularSubdivisionIterate_eq_realization
    {X : Type} [TopologicalSpace X] (n k : ℕ) :
    singularSubdivisionIterate (X := X) n k =
      iteratedSubdivisionRealizationDegree n k := by
  apply Limits.Sigma.hom_ext
  intro s
  let σ := continuousMapOfSingularSimplex n s
  have hs : singularSimplexOfContinuousMap (TopCat.of X) n σ = s :=
    (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌)).symm_apply_apply s
  change singularGenerator (TopCat.of X) n s ≫
      singularSubdivisionIterate n k = _
  rw [← hs, singularGenerator_iteratedSubdivision_realize]
  dsimp [iteratedSubdivisionRealizationDegree, singularGenerator]
  rw [Limits.Sigma.ι_desc]
  simp only [σ, continuousMapOfSingularSimplex_ofContinuousMap]

/-- A finite production chain whose generatorwise `k`-fold subdivisions are
subordinate has a subdivided realization in the cover-small complex. -/
theorem finiteProductionChain_subdivision_factors
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n k : ℕ)
    (c : SingularSimplex (TopCat.of X) n →₀ ℤ)
    (hc : ∀ s ∈ c.support,
      ∀ τ ∈ (postcomposedIteratedSubdivision n k
        (continuousMapOfSingularSimplex n s)).support,
        ∃ a, Set.range τ ⊆ U a) :
    ∃ q : AddCommGrpCat.of ℤ ⟶ (coverSmallChains U).X n,
      q ≫ (coverSmallChains.ι U).f n =
        finiteProductionChainRealize n c ≫ singularSubdivisionIterate n k := by
  classical
  induction c using Finsupp.induction with
  | zero => exact ⟨0, by simp [finiteProductionChainRealize]⟩
  | single_add s z c hsc hz ih =>
      have hs : ∀ τ ∈ (postcomposedIteratedSubdivision n k
          (continuousMapOfSingularSimplex n s)).support,
          ∃ a, Set.range τ ⊆ U a := by
        apply hc s
        have hcs : c s = 0 := by
          simpa only [Finsupp.mem_support_iff, not_not] using hsc
        simp [Finsupp.mem_support_iff, hcs, hz]
      obtain ⟨qs, hqs⟩ := finiteSingularChainRealize_factors U n _ hs
      have hc' : ∀ t ∈ c.support,
          ∀ τ ∈ (postcomposedIteratedSubdivision n k
            (continuousMapOfSingularSimplex n t)).support,
            ∃ a, Set.range τ ⊆ U a := by
        intro t ht
        apply hc t
        apply Finsupp.mem_support_iff.mpr
        have hts : t ≠ s := fun h => hsc (h ▸ ht)
        have hct : c t ≠ 0 := Finsupp.mem_support_iff.mp ht
        simp [hts, hct]
      obtain ⟨q, hq⟩ := ih hc'
      refine ⟨z • qs + q, ?_⟩
      rw [Preadditive.add_comp, Preadditive.zsmul_comp, hqs, hq,
        finiteProductionChainRealize_add, Preadditive.add_comp,
        finiteProductionChainRealize_single, Preadditive.zsmul_comp]
      have hgen := singularGenerator_iteratedSubdivision_realize n k
        (continuousMapOfSingularSimplex n s)
      have hs : singularSimplexOfContinuousMap (TopCat.of X) n
          (continuousMapOfSingularSimplex n s) = s :=
        (TopCat.toSSetObjEquiv (TopCat.of X)
          (Opposite.op (SimplexCategory.mk n))).symm_apply_apply s
      rw [hs] at hgen
      rw [← hgen]

/-- Every finite production chain has a common subdivision depth at which it
factors through the cover-small complex. -/
theorem productionChain_eventually_factors_coverSmallChains
    {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (hUOpen : ∀ a, IsOpen (U a)) (hUCover : Set.univ ⊆ ⋃ a, U a)
    (n : ℕ) (z : (SingularChains (TopCat.of X)).X n) :
    ∃ k, ∃ q : AddCommGrpCat.of ℤ ⟶ (coverSmallChains U).X n,
      q ≫ (coverSmallChains.ι U).f n =
        AddCommGrpCat.asHom z ≫ singularSubdivisionIterate n k := by
  classical
  let c := productionChainFinsupp n z
  let P : ℕ → SingularSimplex (TopCat.of X) n → Prop := fun k s =>
    ∀ l, k ≤ l → ∀ τ ∈ (postcomposedIteratedSubdivision n l
      (continuousMapOfSingularSimplex n s)).support,
      ∃ a, Set.range τ ⊆ U a
  have hP : ∀ s ∈ c.support, ∃ k, P k s := by
    intro s _
    exact eventually_postcomposedIteratedSubdivision_subordinate n
      (continuousMapOfSingularSimplex n s) U hUOpen hUCover
  obtain ⟨k, hk⟩ :=
    ConstructionTargets.SingularSubdivision.Finsupp.exists_uniform_depth c P
    (fun {k l s} hkl hk m hlm => hk m (hkl.trans hlm)) hP
  obtain ⟨q, hq⟩ := finiteProductionChain_subdivision_factors U n k c
    (fun s hs => hk s hs k le_rfl)
  refine ⟨k, q, ?_⟩
  rw [hq, finiteProductionChainRealize_productionChainFinsupp]

/-- Degreewise realization of the finite-support prism on every production
singular chain. -/
def prismRealizationDegree {X : Type} [TopologicalSpace X] (n : ℕ) :
    (SingularChains (TopCat.of X)).X n ⟶
      (SingularChains (TopCat.of X)).X (n + 1) := by
  change (∐ fun _ : SingularSimplex (TopCat.of X) n ↦
    AddCommGrpCat.of ℤ) ⟶ _
  exact Limits.Sigma.desc fun s => finiteSingularChainRealize (n + 1)
    (postcomposedPrism n (continuousMapOfSingularSimplex n s))

/-- The production prism on every chain is the linear extension of the
finite-support postcomposed prism. -/
theorem singularPrismDegree_eq_realization
    {X : Type} [TopologicalSpace X] (n : ℕ) :
    singularPrismDegree (X := X) n = prismRealizationDegree n := by
  apply Limits.Sigma.hom_ext
  intro s
  dsimp [prismRealizationDegree, singularGenerator]
  rw [Limits.Sigma.ι_desc]
  change singularGenerator (TopCat.of X) n s ≫ singularPrismDegree n =
    finiteSingularChainRealize (n + 1)
      (postcomposedPrism n (continuousMapOfSingularSimplex n s))
  rw [← (TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk n))).symm_apply_apply s]
  exact singularGenerator_prism_realize n (continuousMapOfSingularSimplex n s)

/-- The prism of one generator of the cover-small complex, lifted back to that
complex using preservation of its cover member. -/
noncomputable def coverSmallPrismGenerator
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n : ℕ)
    (s : (coverSmallSSet U).obj
      (Opposite.op (SimplexCategory.mk n))) :
    AddCommGrpCat.of ℤ ⟶ (coverSmallChains U).X (n + 1) := by
  let σ := continuousMapOfSingularSimplex n s.1
  let hex := range_subset_of_singularSimplex_mem_coverSmallSSet U s.1 s.2
  let a := Classical.choose hex
  let ha := Classical.choose_spec hex
  have hp : ∀ τ ∈ (postcomposedPrism n σ).support,
      ∃ a, Set.range τ ⊆ U a := by
    intro τ hτ
    exact ⟨a, postcomposedPrism_small n σ U ha hτ⟩
  exact Classical.choose (finiteSingularChainRealize_factors U (n + 1)
    (postcomposedPrism n σ) hp)

@[reassoc] theorem coverSmallPrismGenerator_comp_ι
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n : ℕ)
    (s : (coverSmallSSet U).obj
      (Opposite.op (SimplexCategory.mk n))) :
    coverSmallPrismGenerator U n s ≫ (coverSmallChains.ι U).f (n + 1) =
      singularGenerator (TopCat.of X) n s.1 ≫ singularPrismDegree n := by
  let σ := continuousMapOfSingularSimplex n s.1
  let hex := range_subset_of_singularSimplex_mem_coverSmallSSet U s.1 s.2
  let a := Classical.choose hex
  let ha := Classical.choose_spec hex
  have hp : ∀ τ ∈ (postcomposedPrism n σ).support,
      ∃ a, Set.range τ ⊆ U a := by
    intro τ hτ
    exact ⟨a, postcomposedPrism_small n σ U ha hτ⟩
  rw [show coverSmallPrismGenerator U n s =
      Classical.choose (finiteSingularChainRealize_factors U (n + 1)
        (postcomposedPrism n σ) hp) from rfl]
  rw [Classical.choose_spec (finiteSingularChainRealize_factors U (n + 1)
    (postcomposedPrism n σ) hp)]
  change finiteSingularChainRealize (n + 1) (postcomposedPrism n σ) =
    singularGenerator (TopCat.of X) n s.1 ≫ singularPrismDegree n
  rw [← (TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk n))).symm_apply_apply s.1]
  exact (singularGenerator_prism_realize n σ).symm

/-- The production prism restricts degreewise to the cover-small complex. -/
noncomputable def coverSmallPrismDegree
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n : ℕ) :
    (coverSmallChains U).X n ⟶ (coverSmallChains U).X (n + 1) := by
  change (∐ fun _ : (coverSmallSSet U).obj
    (Opposite.op (SimplexCategory.mk n)) ↦ AddCommGrpCat.of ℤ) ⟶ _
  exact Limits.Sigma.desc (coverSmallPrismGenerator U n)

@[reassoc] theorem coverSmallPrismDegree_comp_ι
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n : ℕ) :
    coverSmallPrismDegree U n ≫ (coverSmallChains.ι U).f (n + 1) =
      (coverSmallChains.ι U).f n ≫ singularPrismDegree n := by
  apply Limits.Sigma.hom_ext
  intro s
  dsimp [coverSmallPrismDegree]
  change (Limits.Sigma.ι (fun _ : (coverSmallSSet U).obj
      (Opposite.op (SimplexCategory.mk n)) ↦ AddCommGrpCat.of ℤ) s ≫
      Limits.Sigma.desc (coverSmallPrismGenerator U n)) ≫
        (coverSmallChains.ι U).f (n + 1) = _
  rw [Limits.Sigma.ι_desc]
  rw [coverSmallPrismGenerator_comp_ι]
  change _ = (coverSmallGeneratorOfMem U s.1 s.2 ≫
    (coverSmallChains.ι U).f n) ≫ singularPrismDegree n
  rw [coverSmallGeneratorOfMem_comp_ι]

instance coverSmallChains_ι_component_mono
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n : ℕ) :
    Mono ((coverSmallChains.ι U).f n) := by
  dsimp [coverSmallChains.ι, coverSmallChains, SingularChains,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  apply Limits.MonoCoprod.mono_map'_of_injective
  exact Subtype.val_injective

/-- The `k`-fold subdivision of one cover-small generator, lifted back into
the cover-small complex. -/
noncomputable def coverSmallSubdivisionGenerator
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n k : ℕ)
    (s : (coverSmallSSet U).obj (Opposite.op (SimplexCategory.mk n))) :
    AddCommGrpCat.of ℤ ⟶ (coverSmallChains U).X n := by
  let σ := continuousMapOfSingularSimplex n s.1
  let hex := range_subset_of_singularSimplex_mem_coverSmallSSet U s.1 s.2
  let a := Classical.choose hex
  let ha := Classical.choose_spec hex
  have hp : ∀ τ ∈ (postcomposedIteratedSubdivision n k σ).support,
      ∃ a, Set.range τ ⊆ U a := by
    intro τ hτ
    exact ⟨a, postcomposedIteratedSubdivision_small n k σ U ha hτ⟩
  exact Classical.choose (finiteSingularChainRealize_factors U n
    (postcomposedIteratedSubdivision n k σ) hp)

@[reassoc] theorem coverSmallSubdivisionGenerator_comp_ι
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n k : ℕ)
    (s : (coverSmallSSet U).obj (Opposite.op (SimplexCategory.mk n))) :
    coverSmallSubdivisionGenerator U n k s ≫ (coverSmallChains.ι U).f n =
      singularGenerator (TopCat.of X) n s.1 ≫ singularSubdivisionIterate n k := by
  let σ := continuousMapOfSingularSimplex n s.1
  let hex := range_subset_of_singularSimplex_mem_coverSmallSSet U s.1 s.2
  let a := Classical.choose hex
  let ha := Classical.choose_spec hex
  have hp : ∀ τ ∈ (postcomposedIteratedSubdivision n k σ).support,
      ∃ a, Set.range τ ⊆ U a := by
    intro τ hτ
    exact ⟨a, postcomposedIteratedSubdivision_small n k σ U ha hτ⟩
  rw [show coverSmallSubdivisionGenerator U n k s =
      Classical.choose (finiteSingularChainRealize_factors U n
        (postcomposedIteratedSubdivision n k σ) hp) from rfl]
  rw [Classical.choose_spec (finiteSingularChainRealize_factors U n
    (postcomposedIteratedSubdivision n k σ) hp)]
  change finiteSingularChainRealize n (postcomposedIteratedSubdivision n k σ) =
    singularGenerator (TopCat.of X) n s.1 ≫ singularSubdivisionIterate n k
  rw [← (TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk n))).symm_apply_apply s.1]
  exact (singularGenerator_iteratedSubdivision_realize n k σ).symm

noncomputable def coverSmallSubdivisionDegree
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n k : ℕ) :
    (coverSmallChains U).X n ⟶ (coverSmallChains U).X n := by
  change (∐ fun _ : (coverSmallSSet U).obj
    (Opposite.op (SimplexCategory.mk n)) ↦ AddCommGrpCat.of ℤ) ⟶ _
  exact Limits.Sigma.desc (coverSmallSubdivisionGenerator U n k)

@[reassoc] theorem coverSmallSubdivisionDegree_comp_ι
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n k : ℕ) :
    coverSmallSubdivisionDegree U n k ≫ (coverSmallChains.ι U).f n =
      (coverSmallChains.ι U).f n ≫ singularSubdivisionIterate n k := by
  apply Limits.Sigma.hom_ext
  intro s
  dsimp [coverSmallSubdivisionDegree]
  change (Limits.Sigma.ι (fun _ : (coverSmallSSet U).obj
      (Opposite.op (SimplexCategory.mk n)) ↦ AddCommGrpCat.of ℤ) s ≫
      Limits.Sigma.desc (coverSmallSubdivisionGenerator U n k)) ≫
        (coverSmallChains.ι U).f n = _
  rw [Limits.Sigma.ι_desc, coverSmallSubdivisionGenerator_comp_ι]
  change _ = (coverSmallGeneratorOfMem U s.1 s.2 ≫
    (coverSmallChains.ι U).f n) ≫ singularSubdivisionIterate n k
  rw [coverSmallGeneratorOfMem_comp_ι]

theorem coverSmallSubdivisionDegree_succ
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n k : ℕ) :
    coverSmallSubdivisionDegree U n (k + 1) =
      coverSmallSubdivisionDegree U n k ≫ coverSmallSubdivisionDegree U n 1 := by
  apply (cancel_mono ((coverSmallChains.ι U).f n)).1
  calc
    coverSmallSubdivisionDegree U n (k + 1) ≫ (coverSmallChains.ι U).f n =
        (coverSmallChains.ι U).f n ≫ singularSubdivisionIterate n (k + 1) :=
      coverSmallSubdivisionDegree_comp_ι U n (k + 1)
    _ = (coverSmallChains.ι U).f n ≫
        (singularSubdivisionIterate n k ≫ singularSubdivisionIterate n 1) := rfl
    _ = ((coverSmallChains.ι U).f n ≫ singularSubdivisionIterate n k) ≫
        singularSubdivisionIterate n 1 := (Category.assoc _ _ _).symm
    _ = (coverSmallSubdivisionDegree U n k ≫ (coverSmallChains.ι U).f n) ≫
        singularSubdivisionIterate n 1 := by rw [coverSmallSubdivisionDegree_comp_ι]
    _ = coverSmallSubdivisionDegree U n k ≫
        ((coverSmallChains.ι U).f n ≫ singularSubdivisionIterate n 1) :=
      Category.assoc _ _ _
    _ = coverSmallSubdivisionDegree U n k ≫
        (coverSmallSubdivisionDegree U n 1 ≫ (coverSmallChains.ι U).f n) := by
      rw [coverSmallSubdivisionDegree_comp_ι]
    _ = (coverSmallSubdivisionDegree U n k ≫ coverSmallSubdivisionDegree U n 1) ≫
        (coverSmallChains.ι U).f n := (Category.assoc _ _ _).symm

theorem coverSmallSubdivisionDegree_comm_d
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n k : ℕ) :
    coverSmallSubdivisionDegree U (n + 1) k ≫
        (coverSmallChains U).d (n + 1) n =
      (coverSmallChains U).d (n + 1) n ≫ coverSmallSubdivisionDegree U n k := by
  apply (cancel_mono ((coverSmallChains.ι U).f n)).1
  calc
    (coverSmallSubdivisionDegree U (n + 1) k ≫
        (coverSmallChains U).d (n + 1) n) ≫ (coverSmallChains.ι U).f n =
      coverSmallSubdivisionDegree U (n + 1) k ≫
        ((coverSmallChains U).d (n + 1) n ≫ (coverSmallChains.ι U).f n) :=
          Category.assoc _ _ _
    _ = coverSmallSubdivisionDegree U (n + 1) k ≫
        ((coverSmallChains.ι U).f (n + 1) ≫
          (SingularChains (TopCat.of X)).d (n + 1) n) := by
          rw [(coverSmallChains.ι U).comm]
    _ = (coverSmallSubdivisionDegree U (n + 1) k ≫
        (coverSmallChains.ι U).f (n + 1)) ≫
          (SingularChains (TopCat.of X)).d (n + 1) n :=
            (Category.assoc _ _ _).symm
    _ = ((coverSmallChains.ι U).f (n + 1) ≫
        singularSubdivisionIterate (n + 1) k) ≫
          (SingularChains (TopCat.of X)).d (n + 1) n := by
            rw [coverSmallSubdivisionDegree_comp_ι]
    _ = ((coverSmallChains.ι U).f (n + 1) ≫
        (SingularChains (TopCat.of X)).d (n + 1) n) ≫
          singularSubdivisionIterate n k := by
            simp only [Category.assoc, singularSubdivisionIterate_comm_d]
    _ = ((coverSmallChains U).d (n + 1) n ≫
        (coverSmallChains.ι U).f n) ≫ singularSubdivisionIterate n k := by
          rw [(coverSmallChains.ι U).comm]
    _ = (coverSmallChains U).d (n + 1) n ≫
        ((coverSmallChains.ι U).f n ≫ singularSubdivisionIterate n k) :=
          Category.assoc _ _ _
    _ = (coverSmallChains U).d (n + 1) n ≫
        (coverSmallSubdivisionDegree U n k ≫ (coverSmallChains.ι U).f n) := by
          rw [coverSmallSubdivisionDegree_comp_ι]
    _ = ((coverSmallChains U).d (n + 1) n ≫ coverSmallSubdivisionDegree U n k) ≫
        (coverSmallChains.ι U).f n := (Category.assoc _ _ _).symm

theorem coverSmallPrism_identity_succ
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n : ℕ) :
    coverSmallPrismDegree U (n + 1) ≫
        (coverSmallChains U).d (n + 2) (n + 1) +
      (coverSmallChains U).d (n + 1) n ≫ coverSmallPrismDegree U n =
        coverSmallSubdivisionDegree U (n + 1) 1 - 𝟙 _ := by
  apply (cancel_mono ((coverSmallChains.ι U).f (n + 1))).1
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Category.id_comp]
  rw [Category.assoc, ← (coverSmallChains.ι U).comm]
  rw [← Category.assoc, coverSmallPrismDegree_comp_ι]
  have hsecond :
      ((coverSmallChains U).d (n + 1) n ≫ coverSmallPrismDegree U n) ≫
          (coverSmallChains.ι U).f (n + 1) =
        (coverSmallChains U).d (n + 1) n ≫
          ((coverSmallChains.ι U).f n ≫ singularPrismDegree n) := by
    rw [Category.assoc, coverSmallPrismDegree_comp_ι]
  rw [hsecond]
  rw [coverSmallSubdivisionDegree_comp_ι]
  have h := singularPrism_identity (X := X) (n + 1)
  apply_fun (fun f => (coverSmallChains.ι U).f (n + 1) ≫ f) at h
  simpa [singularPrismCorrection, singularSubdivisionIterate,
    Preadditive.comp_add, Preadditive.comp_sub, Category.assoc] using h

/-- Within the cover-small complex, a positive-degree cycle is homologous to
each of its chosen iterated subdivisions. -/
theorem coverSmallCycle_homologous_to_iteratedSubdivision
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n k : ℕ)
    (z : AddCommGrpCat.of ℤ ⟶ (coverSmallChains U).X (n + 1))
    (hz : z ≫ (coverSmallChains U).d (n + 1) n = 0) :
    ∃ b : AddCommGrpCat.of ℤ ⟶ (coverSmallChains U).X (n + 2),
      z ≫ coverSmallSubdivisionDegree U (n + 1) k - z =
        b ≫ (coverSmallChains U).d (n + 2) (n + 1) := by
  induction k with
  | zero =>
      refine ⟨0, ?_⟩
      apply (cancel_mono ((coverSmallChains.ι U).f (n + 1))).1
      rw [Preadditive.sub_comp, zero_comp, Category.assoc,
        coverSmallSubdivisionDegree_comp_ι]
      simp [singularSubdivisionIterate]
  | succ k ih =>
      obtain ⟨b, hb⟩ := ih
      have hzk : (z ≫ coverSmallSubdivisionDegree U (n + 1) k) ≫
          (coverSmallChains U).d (n + 1) n = 0 := by
        rw [Category.assoc, coverSmallSubdivisionDegree_comm_d,
          ← Category.assoc, hz, zero_comp]
      refine ⟨(z ≫ coverSmallSubdivisionDegree U (n + 1) k) ≫
          coverSmallPrismDegree U (n + 1) + b, ?_⟩
      have hone := coverSmallPrism_identity_succ U n
      apply_fun (fun f => z ≫ coverSmallSubdivisionDegree U (n + 1) k ≫ f) at hone
      simp only [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id,
        ← Category.assoc, hzk, zero_comp, add_zero] at hone
      rw [coverSmallSubdivisionDegree_succ]
      simp only [Category.assoc, Preadditive.add_comp]
      calc
        z ≫ coverSmallSubdivisionDegree U (n + 1) k ≫
              coverSmallSubdivisionDegree U (n + 1) 1 - z =
            ((z ≫ coverSmallSubdivisionDegree U (n + 1) k) ≫
                coverSmallSubdivisionDegree U (n + 1) 1 -
              z ≫ coverSmallSubdivisionDegree U (n + 1) k) +
            (z ≫ coverSmallSubdivisionDegree U (n + 1) k - z) := by
              simp only [← Category.assoc]
              abel
        _ = ((z ≫ coverSmallSubdivisionDegree U (n + 1) k) ≫
              coverSmallPrismDegree U (n + 1)) ≫
                (coverSmallChains U).d (n + 2) (n + 1) +
            b ≫ (coverSmallChains U).d (n + 2) (n + 1) := by
              rw [← hone, hb]
        _ = (z ≫ coverSmallSubdivisionDegree U (n + 1) k ≫
              coverSmallPrismDegree U (n + 1) + b) ≫
                (coverSmallChains U).d (n + 2) (n + 1) := by
              simp only [Preadditive.add_comp, Category.assoc]
      simp only [Preadditive.add_comp, Category.assoc]

/-! ## Degree-zero small chains -/

/-- Every singular zero-simplex belongs to the small simplicial subset of a
cover: its domain is a singleton, so its image is one point. -/
theorem singularZeroSimplex_mem_coverSmallSSet
    {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (hUCover : Set.univ ⊆ ⋃ a, U a)
    (s : SingularSimplex (TopCat.of X) 0) :
    s ∈ (coverSmallSSet U).obj (Opposite.op (SimplexCategory.mk 0)) := by
  let σ := continuousMapOfSingularSimplex 0 s
  let v : stdSimplex ℝ (Fin 1) := standardSimplexVertices 0 0
  have hv : σ v ∈ ⋃ a, U a := hUCover (Set.mem_univ _)
  simp only [Set.mem_iUnion] at hv
  obtain ⟨a, ha⟩ := hv
  have hrange : Set.range σ ⊆ U a := by
    rintro _ ⟨x, rfl⟩
    letI : Subsingleton (Fin (0 + 1)) := ⟨fun i j => Fin.ext (by omega)⟩
    rw [Subsingleton.elim x v]
    exact ha
  have hm := singularSimplex_mem_coverSmallSSet_of_range_subset U σ a hrange
  simpa [σ] using hm

/-- Barycentric subdivision does not change a zero-chain. -/
theorem singularSubdivisionDegree_zero
    {X : Type} [TopologicalSpace X] :
    singularSubdivisionDegree (X := X) 0 = 𝟙 _ := by
  apply Limits.Sigma.hom_ext
  intro s
  change singularGenerator (TopCat.of X) 0 s ≫ singularSubdivisionDegree 0 =
    singularGenerator (TopCat.of X) 0 s ≫ 𝟙 _
  rw [singularGenerator_singularSubdivisionDegree]
  slice_lhs 1 2 => rw [vertexGenerator_vertexSubdivision_zero]
  rw [Category.assoc]
  rw [standardVertexRealization_postcomposition]
  have hs : singularSimplexOfContinuousMap (TopCat.of X) 0
      (continuousMapOfSingularSimplex 0 s) = s :=
    (TopCat.toSSetObjEquiv (TopCat.of X)
      (Opposite.op ⦋0⦌)).symm_apply_apply s
  rw [hs]
  rw [Category.comp_id]

@[simp] theorem singularSubdivisionIterate_zero
    {X : Type} [TopologicalSpace X] (k : ℕ) :
    singularSubdivisionIterate (X := X) 0 k = 𝟙 _ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show singularSubdivisionIterate (X := X) 0 (k + 1) =
        singularSubdivisionIterate 0 k ≫ singularSubdivisionDegree 0 by rfl]
      rw [ih, singularSubdivisionDegree_zero, Category.comp_id]

#print axioms singularSubdivisionIterate_zero

/-- In degree zero the small-chain inclusion is already an epimorphism on
chain groups; no subdivision is required. -/
theorem coverSmallChains_ι_component_epi_zero
    {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (hUCover : Set.univ ⊆ ⋃ a, U a) :
    Epi ((coverSmallChains.ι U).f 0) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro z
  obtain ⟨q, hq⟩ := productionChain_factors_coverSmallChains U 0 z (by
    intro s hs
    exact singularZeroSimplex_mem_coverSmallSSet U hUCover s)
  refine ⟨q 1, ?_⟩
  have heval := ConcreteCategory.congr_hom hq (1 : ℤ)
  simpa [AddCommGrpCat.asHom] using heval

/-- The small-chain inclusion is surjective on zeroth homology. -/
theorem coverSmall_homologyMap_epi_zero
    {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (hUCover : Set.univ ⊆ ⋃ a, U a) :
    Epi (HomologicalComplex.homologyMap (coverSmallChains.ι U) 0) := by
  letI := coverSmallChains_ι_component_epi_zero U hUCover
  apply HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
  intro j hj
  simpa using hj

/-- In a chain complex indexed by `ℕ`, a degree-zero cycle whose homology class
vanishes is the boundary of an actual degree-one chain.  This is the concrete
elementwise form of the cokernel presentation of zeroth homology. -/
theorem exists_boundary_of_homologyπ_eq_zero_zero
    (K : HomologicalComplex AddCommGrpCat (ComplexShape.down ℕ))
    (x : K.cycles 0) (hx : K.homologyπ 0 x = 0) :
    ∃ b : K.X 1, K.d 1 0 b = K.iCycles 0 x := by
  let S := ShortComplex.mk (K.toCycles 1 0) (K.homologyπ 0)
    (K.toCycles_comp_homologyπ 1 0)
  have hS : S.Exact := S.exact_of_g_is_cokernel
    (K.homologyIsCokernel 1 0 (by simp))
  obtain ⟨b, hb⟩ := (S.ab_exact_iff.mp hS) x hx
  refine ⟨b, ?_⟩
  calc
    K.d 1 0 b = K.iCycles 0 (K.toCycles 1 0 b) := by
      have hi := ConcreteCategory.congr_hom (K.toCycles_i 1 0) b
      simpa only [CategoryTheory.comp_apply] using hi.symm
    _ = K.iCycles 0 x := congrArg (fun y => K.iCycles 0 y) hb

#print axioms exists_boundary_of_homologyπ_eq_zero_zero

/-- The cover-small inclusion is injective on zeroth homology. -/
theorem coverSmall_homologyMap_injective_zero
    {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (hUOpen : ∀ a, IsOpen (U a)) (hUCover : Set.univ ⊆ ⋃ a, U a) :
    Function.Injective
      (HomologicalComplex.homologyMap (coverSmallChains.ι U) 0) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hπ : Function.Surjective ((coverSmallChains U).homologyπ 0) :=
    (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨x, hx⟩ := hπ y
  let xp := HomologicalComplex.cyclesMap (coverSmallChains.ι U) 0 x
  have hxp : (SingularChains (TopCat.of X)).homologyπ 0 xp = 0 := by
    have hnat := HomologicalComplex.homologyπ_naturality
      (coverSmallChains.ι U) 0
    have heval := ConcreteCategory.congr_hom hnat x
    simpa only [CategoryTheory.comp_apply, xp, hx, hy, map_zero] using heval.symm
  obtain ⟨b, hb⟩ := exists_boundary_of_homologyπ_eq_zero_zero
    (SingularChains (TopCat.of X)) xp hxp
  let xhom : AddCommGrpCat.of ℤ ⟶ (coverSmallChains U).cycles 0 :=
    AddCommGrpCat.asHom x
  let z : AddCommGrpCat.of ℤ ⟶ (coverSmallChains U).X 0 :=
    xhom ≫ (coverSmallChains U).iCycles 0
  let bhom : AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X 1 :=
    AddCommGrpCat.asHom b
  have hb_mor : bhom ≫ (SingularChains (TopCat.of X)).d 1 0 =
      z ≫ (coverSmallChains.ι U).f 0 := by
    apply AddCommGrpCat.int_hom_ext
    simp only [CategoryTheory.comp_apply]
    have hbeval : bhom (1 : ℤ) = b := by
      simp [bhom, AddCommGrpCat.asHom]
    have hzeval : z (1 : ℤ) = (coverSmallChains U).iCycles 0 x := by
      simp [z, xhom, AddCommGrpCat.asHom]
    rw [hbeval, hzeval]
    rw [hb]
    have hi := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (coverSmallChains.ι U) 0) x
    simpa only [CategoryTheory.comp_apply, xp, z, xhom, bhom,
      AddCommGrpCat.asHom] using hi
  obtain ⟨k, q, hq⟩ := productionChain_eventually_factors_coverSmallChains
    U hUOpen hUCover 1 b
  have hbas : AddCommGrpCat.asHom b = bhom := by
    apply AddCommGrpCat.int_hom_ext
    simp [bhom, AddCommGrpCat.asHom]
  rw [hbas] at hq
  have hqd : q ≫ (coverSmallChains U).d 1 0 = z := by
    apply (cancel_mono ((coverSmallChains.ι U).f 0)).1
    calc
      (q ≫ (coverSmallChains U).d 1 0) ≫ (coverSmallChains.ι U).f 0 =
          q ≫ ((coverSmallChains U).d 1 0 ≫
            (coverSmallChains.ι U).f 0) := Category.assoc _ _ _
      _ = q ≫ ((coverSmallChains.ι U).f 1 ≫
            (SingularChains (TopCat.of X)).d 1 0) := by
          rw [(coverSmallChains.ι U).comm]
      _ = (bhom ≫ singularSubdivisionIterate 1 k) ≫
            (SingularChains (TopCat.of X)).d 1 0 := by
          rw [← hq]
          exact (Category.assoc _ _ _).symm
      _ = (bhom ≫ (SingularChains (TopCat.of X)).d 1 0) ≫
            singularSubdivisionIterate 0 k := by
          simp only [Category.assoc, singularSubdivisionIterate_comm_d]
      _ = (z ≫ (coverSmallChains.ι U).f 0) ≫
            singularSubdivisionIterate 0 k := by rw [hb_mor]
      _ = z ≫ (coverSmallChains.ι U).f 0 := by
          rw [singularSubdivisionIterate_zero, Category.comp_id]
  have hz : z ≫ (coverSmallChains U).d 0 0 = 0 := by simp
  have hzero : (coverSmallChains U).liftCycles z 0 (by simp) hz ≫
      (coverSmallChains U).homologyπ 0 = 0 :=
    (coverSmallChains U).liftCycles_homologyπ_eq_zero_of_boundary
      z 0 (by simp) q hqd.symm
  have hzlift : (coverSmallChains U).liftCycles z 0 (by simp) hz = xhom := by
    apply (cancel_mono ((coverSmallChains U).iCycles 0)).1
    rw [(coverSmallChains U).liftCycles_i]
  have : y = 0 := by
    rw [← hx]
    have heval := ConcreteCategory.congr_hom hzero (1 : ℤ)
    simpa [xhom, AddCommGrpCat.asHom, hzlift] using heval
  exact this

/-- The cover-small inclusion is an isomorphism on zeroth homology. -/
theorem coverSmall_homologyMap_isIso_zero
    {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (hUOpen : ∀ a, IsOpen (U a)) (hUCover : Set.univ ⊆ ⋃ a, U a) :
    IsIso (HomologicalComplex.homologyMap (coverSmallChains.ι U) 0) := by
  apply (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2
  refine ⟨coverSmall_homologyMap_injective_zero U hUOpen hUCover, ?_⟩
  exact (AddCommGrpCat.epi_iff_surjective _).1
    (coverSmall_homologyMap_epi_zero U hUCover)

#print axioms coverSmall_homologyMap_injective_zero
#print axioms coverSmall_homologyMap_isIso_zero

/-- In every positive degree, the cover-small inclusion is surjective on
homology. -/
theorem coverSmall_homologyMap_surjective_succ
    {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (hUOpen : ∀ a, IsOpen (U a)) (hUCover : Set.univ ⊆ ⋃ a, U a)
    (n : ℕ) : Function.Surjective
      (HomologicalComplex.homologyMap (coverSmallChains.ι U) (n + 1)) := by
  intro y
  have hπ : Function.Surjective
      ((SingularChains (TopCat.of X)).homologyπ (n + 1)) :=
    (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨x, hx⟩ := hπ y
  let xhom : AddCommGrpCat.of ℤ ⟶
      (SingularChains (TopCat.of X)).cycles (n + 1) := AddCommGrpCat.asHom x
  let z : AddCommGrpCat.of ℤ ⟶
      (SingularChains (TopCat.of X)).X (n + 1) :=
    xhom ≫ (SingularChains (TopCat.of X)).iCycles (n + 1)
  have hz : z ≫ (SingularChains (TopCat.of X)).d (n + 1) n = 0 := by
    simp [z]
  have hzas : AddCommGrpCat.asHom
      ((SingularChains (TopCat.of X)).iCycles (n + 1) x) = z := by
    apply AddCommGrpCat.int_hom_ext
    simp [z, xhom, AddCommGrpCat.asHom]
  obtain ⟨k, q, hq⟩ := productionChain_eventually_factors_coverSmallChains
    U hUOpen hUCover (n + 1)
      ((SingularChains (TopCat.of X)).iCycles (n + 1) x)
  rw [hzas] at hq
  have hqcycle : q ≫ (coverSmallChains U).d (n + 1) n = 0 := by
    apply (cancel_mono ((coverSmallChains.ι U).f n)).1
    rw [Category.assoc, ← (coverSmallChains.ι U).comm]
    rw [← Category.assoc, hq, Category.assoc,
      singularSubdivisionIterate_comm_d, ← Category.assoc, hz, zero_comp]
    simp
  let w := ((coverSmallChains U).liftCycles q n (by simp) hqcycle ≫
    (coverSmallChains U).homologyπ (n + 1)) (1 : ℤ)
  refine ⟨w, ?_⟩
  obtain ⟨b, hb⟩ := productionCycle_homologous_to_iteratedSubdivision n k z hz
  have hclass :
      (SingularChains (TopCat.of X)).liftCycles
          (z ≫ singularSubdivisionIterate (n + 1) k) n (by simp) (by
            rw [Category.assoc, singularSubdivisionIterate_comm_d,
              ← Category.assoc, hz, zero_comp]) ≫
          (SingularChains (TopCat.of X)).homologyπ (n + 1) =
        (SingularChains (TopCat.of X)).liftCycles z n (by simp) hz ≫
          (SingularChains (TopCat.of X)).homologyπ (n + 1) := by
    rw [(SingularChains (TopCat.of X)).liftCycles_comp_homologyπ_eq_iff_up_to_refinements
      (n + 2) (n + 1) n (by simp) (by simp)]
    refine ⟨AddCommGrpCat.of ℤ, 𝟙 _, inferInstance, b, ?_⟩
    simp only [Category.id_comp]
    rw [← hb]
    abel
  have hzlift : (SingularChains (TopCat.of X)).liftCycles z n (by simp) hz =
      xhom := by
    apply (cancel_mono ((SingularChains (TopCat.of X)).iCycles (n + 1))).1
    rw [(SingularChains (TopCat.of X)).liftCycles_i]
  have hw_mor :
      (coverSmallChains U).liftCycles q n (by simp) hqcycle ≫
          (coverSmallChains U).homologyπ (n + 1) ≫
          HomologicalComplex.homologyMap (coverSmallChains.ι U) (n + 1) =
        xhom ≫ (SingularChains (TopCat.of X)).homologyπ (n + 1) := by
    rw [HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
    simpa only [hq, hzlift] using hclass
  change (HomologicalComplex.homologyMap (coverSmallChains.ι U) (n + 1)) w = y
  change ((coverSmallChains U).liftCycles q n (by simp) hqcycle ≫
    (coverSmallChains U).homologyπ (n + 1) ≫
    HomologicalComplex.homologyMap (coverSmallChains.ι U) (n + 1)) (1 : ℤ) = y
  rw [hw_mor]
  simpa [xhom, AddCommGrpCat.asHom] using hx

/-- In every positive degree, the cover-small inclusion is injective on
homology. -/
theorem coverSmall_homologyMap_injective_succ
    {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (hUOpen : ∀ a, IsOpen (U a)) (hUCover : Set.univ ⊆ ⋃ a, U a)
    (n : ℕ) : Function.Injective
      (HomologicalComplex.homologyMap (coverSmallChains.ι U) (n + 1)) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hπ : Function.Surjective
      ((coverSmallChains U).homologyπ (n + 1)) :=
    (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨x, hx⟩ := hπ y
  let xhom : AddCommGrpCat.of ℤ ⟶
      (coverSmallChains U).cycles (n + 1) := AddCommGrpCat.asHom x
  let z : AddCommGrpCat.of ℤ ⟶ (coverSmallChains U).X (n + 1) :=
    xhom ≫ (coverSmallChains U).iCycles (n + 1)
  have hz : z ≫ (coverSmallChains U).d (n + 1) n = 0 := by
    simp [z]
  have hzlift : (coverSmallChains U).liftCycles z n (by simp) hz = xhom := by
    apply (cancel_mono ((coverSmallChains U).iCycles (n + 1))).1
    rw [(coverSmallChains U).liftCycles_i]
  have hprodclass :
      (SingularChains (TopCat.of X)).liftCycles
          (z ≫ (coverSmallChains.ι U).f (n + 1)) n (by simp) (by
            calc
              (z ≫ (coverSmallChains.ι U).f (n + 1)) ≫
                    (SingularChains (TopCat.of X)).d (n + 1) n =
                  z ≫ ((coverSmallChains.ι U).f (n + 1) ≫
                    (SingularChains (TopCat.of X)).d (n + 1) n) :=
                Category.assoc _ _ _
              _ = z ≫ ((coverSmallChains U).d (n + 1) n ≫
                    (coverSmallChains.ι U).f n) := by
                rw [(coverSmallChains.ι U).comm]
              _ = 0 := by rw [← Category.assoc, hz, zero_comp]) ≫
        (SingularChains (TopCat.of X)).homologyπ (n + 1) = 0 := by
    have hnat := HomologicalComplex.homologyπ_naturality
      (coverSmallChains.ι U) (n + 1)
    have hlift := HomologicalComplex.liftCycles_comp_cyclesMap
      z n (by simp) hz (coverSmallChains.ι U)
    have hymor : xhom ≫ (coverSmallChains U).homologyπ (n + 1) ≫
        HomologicalComplex.homologyMap (coverSmallChains.ι U) (n + 1) = 0 := by
      apply AddCommGrpCat.int_hom_ext
      rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply]
      have hxhom1 : xhom (1 : ℤ) = x := by
        simp [xhom, AddCommGrpCat.asHom]
      rw [hxhom1, hx, hy]
      rfl
    calc
      (SingularChains (TopCat.of X)).liftCycles
            (z ≫ (coverSmallChains.ι U).f (n + 1)) n (by simp) _ ≫
          (SingularChains (TopCat.of X)).homologyπ (n + 1) =
        ((coverSmallChains U).liftCycles z n (by simp) hz ≫
            HomologicalComplex.cyclesMap (coverSmallChains.ι U) (n + 1)) ≫
          (SingularChains (TopCat.of X)).homologyπ (n + 1) := by rw [hlift]
      _ = (coverSmallChains U).liftCycles z n (by simp) hz ≫
          (HomologicalComplex.cyclesMap (coverSmallChains.ι U) (n + 1) ≫
            (SingularChains (TopCat.of X)).homologyπ (n + 1)) :=
              Category.assoc _ _ _
      _ = (coverSmallChains U).liftCycles z n (by simp) hz ≫
          ((coverSmallChains U).homologyπ (n + 1) ≫
            HomologicalComplex.homologyMap (coverSmallChains.ι U) (n + 1)) := by
              rw [hnat]
      _ = ((coverSmallChains U).liftCycles z n (by simp) hz ≫
          (coverSmallChains U).homologyπ (n + 1)) ≫
            HomologicalComplex.homologyMap (coverSmallChains.ι U) (n + 1) :=
              (Category.assoc _ _ _).symm
      _ = 0 := by rw [hzlift]; simpa only [Category.assoc] using hymor
  rw [(SingularChains (TopCat.of X)).liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements
    (n + 2) (n + 1) n (by simp) (by simp)] at hprodclass
  obtain ⟨A, π, hπepi, bA, hbA⟩ := hprodclass
  have hπsurj : Function.Surjective π :=
    (AddCommGrpCat.epi_iff_surjective π).1 hπepi
  obtain ⟨a, ha⟩ := hπsurj (1 : ℤ)
  let b : AddCommGrpCat.of ℤ ⟶
      (SingularChains (TopCat.of X)).X (n + 2) := AddCommGrpCat.asHom (bA a)
  have hb : z ≫ (coverSmallChains.ι U).f (n + 1) =
      b ≫ (SingularChains (TopCat.of X)).d (n + 2) (n + 1) := by
    apply AddCommGrpCat.int_hom_ext
    have heval := ConcreteCategory.congr_hom hbA a
    simpa [b, AddCommGrpCat.asHom, ha] using heval
  obtain ⟨k, q, hq⟩ := productionChain_eventually_factors_coverSmallChains
    U hUOpen hUCover (n + 2)
      (b (1 : ℤ))
  have hbas : AddCommGrpCat.asHom (b (1 : ℤ)) = b := by
    apply AddCommGrpCat.int_hom_ext
    simp [b, AddCommGrpCat.asHom]
  rw [hbas] at hq
  have hqd : q ≫ (coverSmallChains U).d (n + 2) (n + 1) =
      z ≫ coverSmallSubdivisionDegree U (n + 1) k := by
    apply (cancel_mono ((coverSmallChains.ι U).f (n + 1))).1
    calc
      (q ≫ (coverSmallChains U).d (n + 2) (n + 1)) ≫
          (coverSmallChains.ι U).f (n + 1) =
        q ≫ ((coverSmallChains U).d (n + 2) (n + 1) ≫
          (coverSmallChains.ι U).f (n + 1)) := Category.assoc _ _ _
      _ =
        q ≫ ((coverSmallChains.ι U).f (n + 2) ≫
          (SingularChains (TopCat.of X)).d (n + 2) (n + 1)) := by
            rw [(coverSmallChains.ι U).comm]
      _ = (b ≫ singularSubdivisionIterate (n + 2) k) ≫
          (SingularChains (TopCat.of X)).d (n + 2) (n + 1) := by
            rw [← hq]
            exact (Category.assoc _ _ _).symm
      _ = (b ≫ (SingularChains (TopCat.of X)).d (n + 2) (n + 1)) ≫
          singularSubdivisionIterate (n + 1) k := by
            simp only [Category.assoc, singularSubdivisionIterate_comm_d]
      _ = (z ≫ (coverSmallChains.ι U).f (n + 1)) ≫
          singularSubdivisionIterate (n + 1) k := by rw [hb]
      _ = (z ≫ coverSmallSubdivisionDegree U (n + 1) k) ≫
          (coverSmallChains.ι U).f (n + 1) := by
            rw [Category.assoc, ← coverSmallSubdivisionDegree_comp_ι,
              ← Category.assoc]
  obtain ⟨p, hp⟩ := coverSmallCycle_homologous_to_iteratedSubdivision
    U n k z hz
  have hzboundary : z = (q - p) ≫
      (coverSmallChains U).d (n + 2) (n + 1) := by
    simp only [Preadditive.sub_comp]
    rw [hqd, ← hp]
    abel
  have hzero :
      (coverSmallChains U).liftCycles z n (by simp) hz ≫
        (coverSmallChains U).homologyπ (n + 1) = 0 :=
    (coverSmallChains U).liftCycles_homologyπ_eq_zero_of_boundary
      z n (by simp) (q - p) hzboundary
  have : y = 0 := by
    rw [← hx]
    have heval := ConcreteCategory.congr_hom hzero (1 : ℤ)
    simpa [xhom, AddCommGrpCat.asHom, hzlift] using heval
  exact this

/-- The cover-small inclusion is an isomorphism on homology in every positive
degree. -/
theorem coverSmall_homologyMap_isIso_succ
    {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (hUOpen : ∀ a, IsOpen (U a)) (hUCover : Set.univ ⊆ ⋃ a, U a)
    (n : ℕ) : IsIso
      (HomologicalComplex.homologyMap (coverSmallChains.ι U) (n + 1)) :=
  (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2
    ⟨coverSmall_homologyMap_injective_succ U hUOpen hUCover n,
      coverSmall_homologyMap_surjective_succ U hUOpen hUCover n⟩

#print axioms productionCycle_homologous_to_subdivision
#print axioms singularPrismDegree_eq_realization
#print axioms coverSmallPrismDegree_comp_ι
#print axioms coverSmallSubdivisionDegree_comp_ι
#print axioms coverSmallSubdivisionDegree_comm_d
#print axioms coverSmallPrism_identity_succ
#print axioms singularZeroSimplex_mem_coverSmallSSet
#print axioms coverSmallChains_ι_component_epi_zero
#print axioms coverSmall_homologyMap_epi_zero
#print axioms coverSmallCycle_homologous_to_iteratedSubdivision
#print axioms coverSmall_homologyMap_surjective_succ
#print axioms coverSmall_homologyMap_injective_succ
#print axioms coverSmall_homologyMap_isIso_succ
#print axioms productionCycle_homologous_to_iteratedSubdivision
#print axioms productionChain_eventually_factors_coverSmallChains
#print axioms finiteProductionChainRealize_factors
#print axioms finiteProductionChainRealize_productionChainFinsupp
#print axioms productionChain_factors_coverSmallChains

#print axioms vertexSubdivision_comm_d
#print axioms singularGenerator_alexanderWhitneyFrontEdgeMap
#print axioms singularGenerator_alexanderWhitneyBackEdgeMap
#print axioms singularGenerator_boundary_two
#print axioms alexanderWhitneyFrontEdge_generator_natural
#print axioms singularSimplexOfContinuousMap_face
#print axioms affineSubdivision_boundary
#print axioms affineSubdivision_edge_boundary
#print axioms vertexPrism_identity
#print axioms vertexPrism_standardEdge_identity
#print axioms finiteVertexSubdivision_realize
#print axioms finiteVertexSubdivision_diameter_le
#print axioms finiteVertexSubdivision_standardEdge_diameter_le
#print axioms iteratedFiniteVertexSubdivision_realize
#print axioms iteratedFiniteVertexSubdivision_diameter_le
#print axioms exists_iteratedFiniteVertexSubdivision_subordinate
#print axioms exists_standardEdge_quarterBall_subdivision
#print axioms postcomposedIteratedSubdivision_small
#print axioms Finsupp.exists_uniform_depth
#print axioms finiteVertexPrism_realize
#print axioms postcomposedPrism_small
#print axioms affineSimplex_vertexBarycenter
#print axioms vertexSubdivision_natural
#print axioms vertexSubdivision_affine_natural
#print axioms affineSimplex_comp_affineSimplex
#print axioms vertexRealization_affine_natural
#print axioms vertexPrism_natural
#print axioms vertexPrism_affine_natural
#print axioms affineSimplex_standardSimplexVertices
#print axioms faceAffine_standardSimplexVertices
#print axioms subdividedFace_transport
#print axioms standardEdge_postcomposedSubdivision_small
#print axioms twoTermChain_uniform_depth
#print axioms standardEdge_postcomposedPrism_small
#print axioms ssetChainMap_eq_singularPostcomposition
#print axioms ssetHomologyMap_eq_singularPostcomposition
#print axioms singularHomologyFunctor_map_eq_singularPostcomposition
#print axioms singularHomologyFunctor_map_eq_ssetHomologyMap
#print axioms singularHomologyFunctor_map_eq_singularPostcomposition_comp


end ConstructionTargets.SingularSubdivision
