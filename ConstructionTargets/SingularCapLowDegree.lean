import ConstructionTargets.SingularSubdivision

/-!
# Low-degree integral singular cap products

This module constructs the Alexander--Whitney cap operation by an integral
singular one-cocycle in chain degrees one through three.  It proves the
low-degree Leibniz identities, restriction to cycles, descent from degree-two
homology to degree-one homology, and naturality under continuous maps.
-/

noncomputable section

namespace ConstructionTargets.SingularCapLowDegree

open CategoryTheory CategoryTheory.Limits Simplicial
open ConstructionTargets.SingularSubdivision
/-- An integral degree-one singular cocycle, represented directly as a
functional on singular one-chains which annihilates degree-two boundaries. -/
structure SingularOneCocycle (X : TopCat) where
  eval : (SingularChains X).X 1 ⟶ AddCommGrpCat.of ℤ
  boundary_zero : (SingularChains X).d 2 1 ≫ eval = 0

/-- Pullback of a singular one-cocycle along a continuous map. -/
def SingularOneCocycle.pullback
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularOneCocycle (TopCat.of Y)) (f : C(X, Y)) :
    SingularOneCocycle (TopCat.of X) where
  eval := (singularPostcomposition f).f 1 ≫ a.eval
  boundary_zero := by
    rw [← Category.assoc, ← (singularPostcomposition f).comm]
    rw [Category.assoc, a.boundary_zero]
    simp

/-- Evaluation of a one-cocycle on the Alexander--Whitney front edge of a
singular two-simplex. -/
def alexanderWhitneyFrontValue {X : TopCat}
    (a : SingularOneCocycle X) (s : SingularSimplex X 2) : ℤ :=
  a.eval (singularGenerator X 1 (alexanderWhitneyFrontEdge X s) 1)

/-- The degree `(1,2) → 1` cap operation: evaluate on the front edge and
scale the back-edge generator, extended linearly over singular two-chains. -/
def singularCapOneTwo {X : TopCat} (a : SingularOneCocycle X) :
    (SingularChains X).X 2 ⟶ (SingularChains X).X 1 := by
  dsimp [SingularChains, AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  exact Limits.Sigma.desc (fun s => alexanderWhitneyFrontValue a s •
    singularGenerator X 1 (alexanderWhitneyBackEdge X s))

@[reassoc]
theorem singularGenerator_singularCapOneTwo {X : TopCat}
    (a : SingularOneCocycle X) (s : SingularSimplex X 2) :
    singularGenerator X 2 s ≫ singularCapOneTwo a =
      alexanderWhitneyFrontValue a s •
        singularGenerator X 1 (alexanderWhitneyBackEdge X s) := by
  dsimp [singularGenerator, singularCapOneTwo]
  exact Limits.Sigma.ι_desc _ s

theorem singularCapOneTwo_add {X : TopCat} (a : SingularOneCocycle X)
    (x y : (SingularChains X).X 2) :
    singularCapOneTwo a (x + y) =
      singularCapOneTwo a x + singularCapOneTwo a y :=
  map_add _ _ _

theorem singularCapOneTwo_zsmul {X : TopCat} (a : SingularOneCocycle X)
    (k : ℤ) (x : (SingularChains X).X 2) :
    singularCapOneTwo a (k • x) = k • singularCapOneTwo a x :=
  map_zsmul _ _ _

/-- The cocycle equation on a two-simplex: evaluation on back, middle, and
front edges cancels with alternating signs. -/
theorem SingularOneCocycle.face_cancellation {X : TopCat}
    (a : SingularOneCocycle X) (s : SingularSimplex X 2) :
    a.eval (singularGenerator X 1 (alexanderWhitneyBackEdge X s) 1) -
      a.eval (singularGenerator X 1
        ((TopCat.toSSet.obj X).δ (1 : Fin 3) s) 1) +
      a.eval (singularGenerator X 1 (alexanderWhitneyFrontEdge X s) 1) = 0 := by
  have hm := congrArg (fun g => singularGenerator X 2 s ≫ g) a.boundary_zero
  simp at hm
  rw [← Category.assoc, singularGenerator_boundary_two] at hm
  have h := congrArg (fun g => g 1) hm
  simp only [ConcreteCategory.comp_apply] at h
  simpa using h

/-- Pulling a cocycle back and evaluating the front edge agrees with
evaluating the target cocycle on the postcomposed front edge. -/
theorem alexanderWhitneyFrontValue_pullback
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularOneCocycle (TopCat.of Y)) (f : C(X, Y))
    (τ : C(stdSimplex ℝ (Fin 3), X)) :
    alexanderWhitneyFrontValue (a.pullback f)
        (singularSimplexOfContinuousMap _ 2 τ) =
      alexanderWhitneyFrontValue a
        (singularSimplexOfContinuousMap _ 2 (f.comp τ)) := by
  have h := congrArg (fun g => a.eval (g 1))
    (alexanderWhitneyFrontEdge_generator_natural τ f)
  simpa [alexanderWhitneyFrontValue, SingularOneCocycle.pullback,
    ConcreteCategory.comp_apply] using h

/-- Boundary of the cap of a generator, expressed as the scaled boundary of
its Alexander--Whitney back edge. -/
theorem singularGenerator_singularCapOneTwo_boundary {X : TopCat}
    (a : SingularOneCocycle X) (s : SingularSimplex X 2) :
    singularGenerator X 2 s ≫ singularCapOneTwo a ≫
        (SingularChains X).d 1 0 =
      alexanderWhitneyFrontValue a s •
        (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) •
          singularGenerator X 0
            ((TopCat.toSSet.obj X).δ i (alexanderWhitneyBackEdge X s))) := by
  rw [singularGenerator_singularCapOneTwo_assoc]
  rw [Preadditive.zsmul_comp]
  rw [singularGenerator_boundary]

/-- Terminal vertex used by the degree `(1,1) → 0` cap operation. -/
def alexanderWhitneyBackVertex (X : TopCat) (s : SingularSimplex X 1) :
    SingularSimplex X 0 :=
  (TopCat.toSSet.obj X).δ (0 : Fin 2) s

/-- Companion cap operation on one-chains: evaluate the cocycle on the edge
and scale its terminal vertex. -/
def singularCapOneOne {X : TopCat} (a : SingularOneCocycle X) :
    (SingularChains X).X 1 ⟶ (SingularChains X).X 0 := by
  dsimp [SingularChains, AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  exact Limits.Sigma.desc (fun s =>
    a.eval (singularGenerator X 1 s 1) •
      singularGenerator X 0 (alexanderWhitneyBackVertex X s))

@[reassoc]
theorem singularGenerator_singularCapOneOne {X : TopCat}
    (a : SingularOneCocycle X) (s : SingularSimplex X 1) :
    singularGenerator X 1 s ≫ singularCapOneOne a =
      a.eval (singularGenerator X 1 s 1) •
        singularGenerator X 0 (alexanderWhitneyBackVertex X s) := by
  dsimp [singularGenerator, singularCapOneOne]
  exact Limits.Sigma.ι_desc _ s

theorem singularCapOneOne_add {X : TopCat} (a : SingularOneCocycle X)
    (x y : (SingularChains X).X 1) :
    singularCapOneOne a (x + y) =
      singularCapOneOne a x + singularCapOneOne a y :=
  map_add _ _ _

theorem singularCapOneOne_zsmul {X : TopCat} (a : SingularOneCocycle X)
    (k : ℤ) (x : (SingularChains X).X 1) :
    singularCapOneOne a (k • x) = k • singularCapOneOne a x :=
  map_zsmul _ _ _

/-- The terminal vertex of a singular two-simplex. -/
def alexanderWhitneyTerminalVertexTwo (X : TopCat)
    (s : SingularSimplex X 2) : SingularSimplex X 0 :=
  alexanderWhitneyBackVertex X (alexanderWhitneyBackEdge X s)

/-- Degree-two coboundary value of a one-cochain, written as the alternating
sum of its three edge evaluations. -/
def singularOneCoboundaryValueTwo {X : TopCat} (a : SingularOneCocycle X)
    (s : SingularSimplex X 2) : ℤ :=
  a.eval (singularGenerator X 1 (alexanderWhitneyBackEdge X s) 1) -
    a.eval (singularGenerator X 1
      ((TopCat.toSSet.obj X).δ (1 : Fin 3) s) 1) +
    a.eval (singularGenerator X 1 (alexanderWhitneyFrontEdge X s) 1)

/-- Full degree-two cap Leibniz identity on a simplex generator. -/
theorem singularCap_leibniz_generator {X : TopCat}
    (a : SingularOneCocycle X) (s : SingularSimplex X 2) :
    singularGenerator X 2 s ≫ singularCapOneTwo a ≫
          (SingularChains X).d 1 0 +
        singularGenerator X 2 s ≫ (SingularChains X).d 2 1 ≫
          singularCapOneOne a =
      singularOneCoboundaryValueTwo a s •
        singularGenerator X 0 (alexanderWhitneyTerminalVertexTwo X s) := by
  have hmid : (TopCat.toSSet.obj X).δ (0 : Fin 2)
      ((TopCat.toSSet.obj X).δ (1 : Fin 3) s) =
      (TopCat.toSSet.obj X).δ (0 : Fin 2)
        ((TopCat.toSSet.obj X).δ (0 : Fin 3) s) := by
    exact congrArg (fun g => g s)
      ((TopCat.toSSet.obj X).δ_comp_δ_self (i := (0 : Fin 2))).symm
  have hfront : (TopCat.toSSet.obj X).δ (0 : Fin 2)
      ((TopCat.toSSet.obj X).δ (2 : Fin 3) s) =
      (TopCat.toSSet.obj X).δ (1 : Fin 2)
        ((TopCat.toSSet.obj X).δ (0 : Fin 3) s) := by
    exact congrArg (fun g => g s)
      ((TopCat.toSSet.obj X).δ_comp_δ
        (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide))
  rw [singularGenerator_singularCapOneTwo_assoc]
  rw [Preadditive.zsmul_comp, singularGenerator_boundary]
  rw [← Category.assoc, singularGenerator_boundary_two]
  simp only [Preadditive.add_comp, Preadditive.sub_comp,
    singularGenerator_singularCapOneOne]
  dsimp [alexanderWhitneyFrontValue, singularOneCoboundaryValueTwo,
    alexanderWhitneyTerminalVertexTwo]
  simp [Fin.sum_univ_succ, alexanderWhitneyFrontEdge,
    alexanderWhitneyBackEdge, alexanderWhitneyBackVertex, hmid, hfront]
  simp only [add_smul, sub_smul]
  abel

/-- For a cocycle the coboundary term vanishes, giving the global
low-dimensional cap chain identity. -/
theorem singularCap_chain_identity {X : TopCat} (a : SingularOneCocycle X) :
    singularCapOneTwo a ≫ (SingularChains X).d 1 0 +
      (SingularChains X).d 2 1 ≫ singularCapOneOne a = 0 := by
  apply Limits.Sigma.hom_ext
  intro s
  change singularGenerator X 2 s ≫
      (singularCapOneTwo a ≫ (SingularChains X).d 1 0 +
        (SingularChains X).d 2 1 ≫ singularCapOneOne a) =
    singularGenerator X 2 s ≫ 0
  rw [Preadditive.comp_add, singularCap_leibniz_generator]
  rw [show singularOneCoboundaryValueTwo a s = 0 by
    exact a.face_cancellation s]
  simp

/-- Capping a degree-two cycle with an integral one-cocycle produces a
degree-one cycle. -/
theorem singularCapOneTwo_isCycle {X : TopCat} (a : SingularOneCocycle X)
    (c : (SingularChains X).X 2)
    (hc : (SingularChains X).d 2 1 c = 0) :
    (SingularChains X).d 1 0 (singularCapOneTwo a c) = 0 := by
  have h := congrArg (fun g => g c) (singularCap_chain_identity a)
  change (SingularChains X).d 1 0 (singularCapOneTwo a c) +
      singularCapOneOne a ((SingularChains X).d 2 1 c) = 0 at h
  rw [hc, map_zero, add_zero] at h
  exact h

/-! ## Degree-three cap foundation for homology descent -/

/-- Front edge `[0,1]` of a singular three-simplex. -/
def alexanderWhitneyFrontEdgeThree (X : TopCat)
    (s : SingularSimplex X 3) : SingularSimplex X 1 :=
  (TopCat.toSSet.obj X).δ (2 : Fin 3)
    ((TopCat.toSSet.obj X).δ (3 : Fin 4) s)

/-- Back two-face `[1,2,3]` of a singular three-simplex. -/
def alexanderWhitneyBackFaceThree (X : TopCat)
    (s : SingularSimplex X 3) : SingularSimplex X 2 :=
  (TopCat.toSSet.obj X).δ (0 : Fin 4) s

/-- Evaluation of a one-cocycle on the degree-three Alexander--Whitney front
edge. -/
def alexanderWhitneyFrontValueThree {X : TopCat}
    (a : SingularOneCocycle X) (s : SingularSimplex X 3) : ℤ :=
  a.eval (singularGenerator X 1 (alexanderWhitneyFrontEdgeThree X s) 1)

/-- Degree `(1,3) → 2` cap: evaluate on `[0,1]`, scale `[1,2,3]`, and
extend linearly over singular three-chains. -/
def singularCapOneThree {X : TopCat} (a : SingularOneCocycle X) :
    (SingularChains X).X 3 ⟶ (SingularChains X).X 2 := by
  dsimp [SingularChains, AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  exact Limits.Sigma.desc (fun s => alexanderWhitneyFrontValueThree a s •
    singularGenerator X 2 (alexanderWhitneyBackFaceThree X s))

@[reassoc]
theorem singularGenerator_singularCapOneThree {X : TopCat}
    (a : SingularOneCocycle X) (s : SingularSimplex X 3) :
    singularGenerator X 3 s ≫ singularCapOneThree a =
      alexanderWhitneyFrontValueThree a s •
        singularGenerator X 2 (alexanderWhitneyBackFaceThree X s) := by
  dsimp [singularGenerator, singularCapOneThree]
  exact Limits.Sigma.ι_desc _ s

theorem singularCapOneThree_add {X : TopCat} (a : SingularOneCocycle X)
    (x y : (SingularChains X).X 3) :
    singularCapOneThree a (x + y) =
      singularCapOneThree a x + singularCapOneThree a y :=
  map_add _ _ _

theorem singularCapOneThree_zsmul {X : TopCat} (a : SingularOneCocycle X)
    (k : ℤ) (x : (SingularChains X).X 3) :
    singularCapOneThree a (k • x) = k • singularCapOneThree a x :=
  map_zsmul _ _ _

/-- Explicit alternating four-face boundary of a singular three-simplex. -/
theorem singularGenerator_boundary_three (X : TopCat)
    (s : SingularSimplex X 3) :
    singularGenerator X 3 s ≫ (SingularChains X).d 3 2 =
      singularGenerator X 2 ((TopCat.toSSet.obj X).δ (0 : Fin 4) s) -
      singularGenerator X 2 ((TopCat.toSSet.obj X).δ (1 : Fin 4) s) +
      singularGenerator X 2 ((TopCat.toSSet.obj X).δ (2 : Fin 4) s) -
      singularGenerator X 2 ((TopCat.toSSet.obj X).δ (3 : Fin 4) s) := by
  rw [singularGenerator_boundary]
  simp [Fin.sum_univ_succ]
  abel

/-- Boundary of the degree-three cap generator is the front coefficient
times the alternating boundary of its back two-face. -/
theorem singularGenerator_singularCapOneThree_boundary {X : TopCat}
    (a : SingularOneCocycle X) (s : SingularSimplex X 3) :
    singularGenerator X 3 s ≫ singularCapOneThree a ≫
        (SingularChains X).d 2 1 =
      alexanderWhitneyFrontValueThree a s •
        (∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) •
          singularGenerator X 1
            ((TopCat.toSSet.obj X).δ i
              (alexanderWhitneyBackFaceThree X s))) := by
  rw [singularGenerator_singularCapOneThree_assoc]
  rw [Preadditive.zsmul_comp]
  rw [singularGenerator_boundary]

/-- Degree-three cap Leibniz identity on a simplex generator. -/
theorem singularCap_three_leibniz_generator {X : TopCat}
    (a : SingularOneCocycle X) (s : SingularSimplex X 3) :
    singularGenerator X 3 s ≫ singularCapOneThree a ≫
          (SingularChains X).d 2 1 +
        singularGenerator X 3 s ≫ (SingularChains X).d 3 2 ≫
          singularCapOneTwo a = 0 := by
  let S := TopCat.toSSet.obj X
  have h01 : S.δ (0 : Fin 3) (S.δ (1 : Fin 4) s) =
      S.δ (0 : Fin 3) (S.δ (0 : Fin 4) s) := by
    exact congrArg (fun g => g s) (S.δ_comp_δ_self (i := (0 : Fin 3))).symm
  have h02 : S.δ (0 : Fin 3) (S.δ (2 : Fin 4) s) =
      S.δ (1 : Fin 3) (S.δ (0 : Fin 4) s) := by
    exact congrArg (fun g => g s)
      (S.δ_comp_δ (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide))
  have h03 : S.δ (0 : Fin 3) (S.δ (3 : Fin 4) s) =
      S.δ (2 : Fin 3) (S.δ (0 : Fin 4) s) := by
    exact congrArg (fun g => g s)
      (S.δ_comp_δ (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide))
  have h21 : S.δ (2 : Fin 3) (S.δ (1 : Fin 4) s) =
      S.δ (1 : Fin 3) (S.δ (3 : Fin 4) s) := by
    exact congrArg (fun g => g s)
      (S.δ_comp_δ (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide)).symm
  have h22 : S.δ (2 : Fin 3) (S.δ (2 : Fin 4) s) =
      S.δ (2 : Fin 3) (S.δ (3 : Fin 4) s) := by
    exact congrArg (fun g => g s) (S.δ_comp_δ_self (i := (2 : Fin 3)))
  rw [singularGenerator_singularCapOneThree_boundary]
  rw [← Category.assoc, singularGenerator_boundary_three]
  simp only [Preadditive.add_comp, Preadditive.sub_comp,
    singularGenerator_singularCapOneTwo]
  dsimp [alexanderWhitneyFrontValueThree, alexanderWhitneyFrontValue,
    alexanderWhitneyFrontEdgeThree, alexanderWhitneyBackFaceThree,
    alexanderWhitneyFrontEdge, alexanderWhitneyBackEdge]
  dsimp [S] at h01 h02 h03 h21 h22
  simp [Fin.sum_univ_succ, h01, h02, h03, h21, h22]
  have hc := a.face_cancellation (S.δ (3 : Fin 4) s)
  dsimp [alexanderWhitneyFrontEdge, alexanderWhitneyBackEdge, S] at hc
  abel_nf
  simp only [neg_one_zsmul]
  rw [← h03, ← neg_smul, ← add_smul, ← add_smul]
  have hc' :
      a.eval (singularGenerator X 1 (S.δ 2 (S.δ 3 s)) 1) +
        (a.eval (singularGenerator X 1 (S.δ 0 (S.δ 3 s)) 1) -
          a.eval (singularGenerator X 1 (S.δ 1 (S.δ 3 s)) 1)) = 0 := by
    calc
      _ = a.eval (singularGenerator X 1 (S.δ 0 (S.δ 3 s)) 1) -
          a.eval (singularGenerator X 1 (S.δ 1 (S.δ 3 s)) 1) +
          a.eval (singularGenerator X 1 (S.δ 2 (S.δ 3 s)) 1) := by abel
      _ = 0 := hc
  simp only [sub_eq_add_neg] at hc'
  rw [hc']
  simp

/-- Global degree-three cap chain identity. -/
theorem singularCap_three_chain_identity {X : TopCat} (a : SingularOneCocycle X) :
    singularCapOneThree a ≫ (SingularChains X).d 2 1 +
      (SingularChains X).d 3 2 ≫ singularCapOneTwo a = 0 := by
  apply Limits.Sigma.hom_ext
  intro s
  change singularGenerator X 3 s ≫
      (singularCapOneThree a ≫ (SingularChains X).d 2 1 +
        (SingularChains X).d 3 2 ≫ singularCapOneTwo a) =
    singularGenerator X 3 s ≫ 0
  rw [Preadditive.comp_add, singularCap_three_leibniz_generator]
  simp

/-- Capping a degree-three boundary is explicitly a degree-one boundary. -/
theorem singularCapOneTwo_boundary_eq_boundary {X : TopCat}
    (a : SingularOneCocycle X) (b : (SingularChains X).X 3) :
    singularCapOneTwo a ((SingularChains X).d 3 2 b) =
      (SingularChains X).d 2 1 (-singularCapOneThree a b) := by
  have h := congrArg (fun g => g b) (singularCap_three_chain_identity a)
  change (SingularChains X).d 2 1 (singularCapOneThree a b) +
      singularCapOneTwo a ((SingularChains X).d 3 2 b) = 0 at h
  rw [map_neg]
  exact eq_neg_of_add_eq_zero_right h

/-- Homologous degree-two cycles have cap outputs differing by an explicit
degree-one boundary. -/
theorem singularCapOneTwo_sub_eq_boundary_of_sub_eq_boundary {X : TopCat}
    (a : SingularOneCocycle X) (c c' : (SingularChains X).X 2)
    (b : (SingularChains X).X 3)
    (h : c' - c = (SingularChains X).d 3 2 b) :
    singularCapOneTwo a c' - singularCapOneTwo a c =
      (SingularChains X).d 2 1 (-singularCapOneThree a b) := by
  rw [← map_sub, h]
  exact singularCapOneTwo_boundary_eq_boundary a b

/-- The degree-two cap operation restricted to cycles, with values in
degree-one cycles. -/
noncomputable def capCycles {X : TopCat} (a : SingularOneCocycle X) :
    (SingularChains X).cycles 2 ⟶ (SingularChains X).cycles 1 :=
  (SingularChains X).liftCycles
    ((SingularChains X).iCycles 2 ≫ singularCapOneTwo a) 0 (by simp) (by
      rw [Category.assoc]
      have h := congrArg (fun g => (SingularChains X).iCycles 2 ≫ g)
        (singularCap_chain_identity a)
      simp only [Preadditive.comp_add, ← Category.assoc,
        (SingularChains X).iCycles_d] at h
      simp at h
      exact h)

@[reassoc]
theorem capCycles_i {X : TopCat} (a : SingularOneCocycle X) :
    capCycles a ≫ (SingularChains X).iCycles 1 =
      (SingularChains X).iCycles 2 ≫ singularCapOneTwo a := by
  exact (SingularChains X).liftCycles_i _ _ _ _

/-- The cycle-level cap followed by projection to degree-one homology kills
the canonical image of degree-three boundaries. -/
theorem toCycles_capCycles_homologyπ_eq_zero {X : TopCat}
    (a : SingularOneCocycle X) :
    (SingularChains X).toCycles 3 2 ≫ capCycles a ≫
      (SingularChains X).homologyπ 1 = 0 := by
  let K := SingularChains X
  let z : K.X 3 ⟶ K.X 1 := K.d 3 2 ≫ singularCapOneTwo a
  have hz : z ≫ K.d 1 0 = 0 := by
    dsimp [z]
    have h := singularCap_three_chain_identity a
    have h' : K.d 3 2 ≫ singularCapOneTwo a =
        -(singularCapOneThree a ≫ K.d 2 1) := by
      simpa [K] using eq_neg_of_add_eq_zero_right h
    rw [h']
    rw [Preadditive.neg_comp, Category.assoc, K.d_comp_d]
    simp
  have hboundary : z = (-singularCapOneThree a) ≫ K.d 2 1 := by
    dsimp [z]
    have h := singularCap_three_chain_identity a
    simpa [K] using eq_neg_of_add_eq_zero_right h
  have hlift : K.toCycles 3 2 ≫ capCycles a =
      K.liftCycles z 0 (by simp) hz := by
    apply (cancel_mono (K.iCycles 1)).1
    rw [Category.assoc, capCycles_i, ← Category.assoc, K.toCycles_i]
    rw [K.liftCycles_i]
  rw [← Category.assoc, hlift]
  exact K.liftCycles_homologyπ_eq_zero_of_boundary
    z 0 (by simp) (-singularCapOneThree a) hboundary

/-- Capping with an integral singular one-cocycle descends canonically from
degree-two cycles modulo boundaries to an additive map `H₂(X; ℤ) → H₁(X; ℤ)`.
No representatives are chosen in this construction. -/
noncomputable def capHomologyOneTwo {X : TopCat} (a : SingularOneCocycle X) :
    (SingularChains X).homology 2 ⟶ (SingularChains X).homology 1 :=
  let K := SingularChains X
  let eZ := K.cyclesIsoSc' 3 2 1 (by simp) (by simp)
  let eH := K.homologyIsoSc' 3 2 1 (by simp) (by simp)
  eH.hom ≫ (K.sc' 3 2 1).descHomology
    (eZ.inv ≫ capCycles a ≫ K.homologyπ 1) (by
      have heq : (K.sc' 3 2 1).toCycles ≫ eZ.inv = K.toCycles 3 2 := by
        apply (cancel_mono eZ.hom).1
        dsimp [eZ]
        simp [Category.assoc,
          K.toCycles_cyclesIsoSc'_hom 3 2 1 (by simp) (by simp)]
      rw [← Category.assoc, heq]
      exact toCycles_capCycles_homologyπ_eq_zero a)

/-- The descended cap morphism is characterized on every degree-two cycle by
the original chain-level cap followed by the degree-one homology quotient. -/
@[reassoc]
theorem homologyπ_capHomologyOneTwo {X : TopCat} (a : SingularOneCocycle X) :
    (SingularChains X).homologyπ 2 ≫ capHomologyOneTwo a =
      capCycles a ≫ (SingularChains X).homologyπ 1 := by
  simp [capHomologyOneTwo]

/-- Elementwise representative formula for the descended cap morphism. -/
theorem capHomologyOneTwo_homologyπ_apply {X : TopCat}
    (a : SingularOneCocycle X) (z : (SingularChains X).cycles 2) :
    capHomologyOneTwo a ((SingularChains X).homologyπ 2 z) =
      (SingularChains X).homologyπ 1 (capCycles a z) := by
  change ((SingularChains X).homologyπ 2 ≫ capHomologyOneTwo a) z = _
  rw [homologyπ_capHomologyOneTwo]
  rfl

theorem alexanderWhitneyBackEdge_generator_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (τ : C(stdSimplex ℝ (Fin 3), X)) (f : C(X, Y)) :
    singularGenerator (TopCat.of X) 1
        (alexanderWhitneyBackEdge _
          (singularSimplexOfContinuousMap _ 2 τ)) ≫
        (singularPostcomposition f).f 1 =
      singularGenerator (TopCat.of Y) 1
        (alexanderWhitneyBackEdge _
          (singularSimplexOfContinuousMap _ 2 (f.comp τ))) := by
  have hx : alexanderWhitneyBackEdge (TopCat.of X)
      (singularSimplexOfContinuousMap _ 2 τ) =
      singularSimplexOfContinuousMap _ 1
        (τ.comp (affineSimplex (fun j : Fin 2 =>
          ⟨Pi.single ((0 : Fin 3).succAbove j) 1,
            single_mem_stdSimplex ℝ ((0 : Fin 3).succAbove j)⟩))) :=
    singularSimplexOfContinuousMap_face τ (0 : Fin 3)
  rw [hx, singularGenerator_singularPostcomposition]
  have hy : alexanderWhitneyBackEdge (TopCat.of Y)
      (singularSimplexOfContinuousMap _ 2 (f.comp τ)) =
      singularSimplexOfContinuousMap _ 1
        ((f.comp τ).comp (affineSimplex (fun j : Fin 2 =>
          ⟨Pi.single ((0 : Fin 3).succAbove j) 1,
            single_mem_stdSimplex ℝ ((0 : Fin 3).succAbove j)⟩))) :=
    singularSimplexOfContinuousMap_face (f.comp τ) (0 : Fin 3)
  rw [hy]
  congr 2

@[reassoc] theorem singularCapOneTwo_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularOneCocycle (TopCat.of Y)) (f : C(X, Y)) :
    (singularPostcomposition f).f 2 ≫ singularCapOneTwo a =
      singularCapOneTwo (a.pullback f) ≫ (singularPostcomposition f).f 1 := by
  apply Limits.Sigma.hom_ext
  intro s
  let τ := continuousMapOfSingularSimplex 2 s
  have hs : singularSimplexOfContinuousMap (TopCat.of X) 2 τ = s := by
    exact (TopCat.toSSetObjEquiv (TopCat.of X)
      (Opposite.op (SimplexCategory.mk 2))).symm_apply_apply s
  rw [← hs]
  have hpost := singularGenerator_singularPostcomposition 2 τ f
  calc
    _ = (singularGenerator (TopCat.of X) 2
          (singularSimplexOfContinuousMap _ 2 τ) ≫
          (singularPostcomposition f).f 2) ≫ singularCapOneTwo a :=
      (Category.assoc _ _ _).symm
    _ = singularGenerator (TopCat.of Y) 2
          (singularSimplexOfContinuousMap _ 2 (f.comp τ)) ≫
          singularCapOneTwo a := by rw [hpost]
    _ = alexanderWhitneyFrontValue a
          (singularSimplexOfContinuousMap _ 2 (f.comp τ)) •
        singularGenerator (TopCat.of Y) 1
          (alexanderWhitneyBackEdge _
            (singularSimplexOfContinuousMap _ 2 (f.comp τ))) := by
      rw [singularGenerator_singularCapOneTwo]
    _ = alexanderWhitneyFrontValue (a.pullback f)
          (singularSimplexOfContinuousMap _ 2 τ) •
        (singularGenerator (TopCat.of X) 1
          (alexanderWhitneyBackEdge _
            (singularSimplexOfContinuousMap _ 2 τ)) ≫
            (singularPostcomposition f).f 1) := by
      rw [alexanderWhitneyFrontValue_pullback,
        alexanderWhitneyBackEdge_generator_natural]
    _ = (singularGenerator (TopCat.of X) 2
          (singularSimplexOfContinuousMap _ 2 τ) ≫
          singularCapOneTwo (a.pullback f)) ≫
            (singularPostcomposition f).f 1 := by
      rw [singularGenerator_singularCapOneTwo, Preadditive.zsmul_comp]
    _ = _ := Category.assoc _ _ _

@[reassoc] theorem capCycles_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularOneCocycle (TopCat.of Y)) (f : C(X, Y)) :
    HomologicalComplex.cyclesMap (singularPostcomposition f) 2 ≫ capCycles a =
      capCycles (a.pullback f) ≫
        HomologicalComplex.cyclesMap (singularPostcomposition f) 1 := by
  apply (cancel_mono ((SingularChains (TopCat.of Y)).iCycles 1)).1
  simp only [Category.assoc]
  rw [capCycles_i]
  rw [← Category.assoc, HomologicalComplex.cyclesMap_i]
  simp only [Category.assoc]
  rw [singularCapOneTwo_natural]
  rw [HomologicalComplex.cyclesMap_i]
  simpa only [Category.assoc] using congrArg
    (fun q => q ≫ (singularPostcomposition f).f 1)
    (capCycles_i (a.pullback f)).symm

@[reassoc] theorem capHomologyOneTwo_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularOneCocycle (TopCat.of Y)) (f : C(X, Y)) :
    HomologicalComplex.homologyMap (singularPostcomposition f) 2 ≫
        capHomologyOneTwo a =
      capHomologyOneTwo (a.pullback f) ≫
        HomologicalComplex.homologyMap (singularPostcomposition f) 1 := by
  apply (cancel_epi ((SingularChains (TopCat.of X)).homologyπ 2)).1
  calc
    _ = (((SingularChains (TopCat.of X)).homologyπ 2 ≫
          HomologicalComplex.homologyMap (singularPostcomposition f) 2) ≫
          capHomologyOneTwo a) := (Category.assoc _ _ _).symm
    _ = (HomologicalComplex.cyclesMap (singularPostcomposition f) 2 ≫
          (SingularChains (TopCat.of Y)).homologyπ 2) ≫
          capHomologyOneTwo a := by
      rw [HomologicalComplex.homologyπ_naturality]
    _ = HomologicalComplex.cyclesMap (singularPostcomposition f) 2 ≫
          capCycles a ≫ (SingularChains (TopCat.of Y)).homologyπ 1 := by
      rw [Category.assoc, homologyπ_capHomologyOneTwo]
    _ = capCycles (a.pullback f) ≫
          HomologicalComplex.cyclesMap (singularPostcomposition f) 1 ≫
          (SingularChains (TopCat.of Y)).homologyπ 1 := by
      simpa only [Category.assoc] using congrArg
        (fun q => q ≫ (SingularChains (TopCat.of Y)).homologyπ 1)
        (capCycles_natural a f)
    _ = capCycles (a.pullback f) ≫
          (SingularChains (TopCat.of X)).homologyπ 1 ≫
          HomologicalComplex.homologyMap (singularPostcomposition f) 1 := by
      rw [HomologicalComplex.homologyπ_naturality]
    _ = ((SingularChains (TopCat.of X)).homologyπ 2 ≫
          capHomologyOneTwo (a.pullback f)) ≫
          HomologicalComplex.homologyMap (singularPostcomposition f) 1 := by
      simpa only [Category.assoc] using congrArg
        (fun q => q ≫ HomologicalComplex.homologyMap
          (singularPostcomposition f) 1)
        (homologyπ_capHomologyOneTwo (a.pullback f)).symm
    _ = _ := Category.assoc _ _ _

#print axioms singularGenerator_singularCapOneTwo
#print axioms SingularOneCocycle.face_cancellation
#print axioms singularCap_chain_identity
#print axioms singularCapOneTwo_isCycle
#print axioms singularCap_three_chain_identity
#print axioms singularCapOneTwo_boundary_eq_boundary
#print axioms capCycles
#print axioms toCycles_capCycles_homologyπ_eq_zero
#print axioms capHomologyOneTwo
#print axioms homologyπ_capHomologyOneTwo
#print axioms singularCapOneTwo_natural
#print axioms capCycles_natural
#print axioms capHomologyOneTwo_natural

end ConstructionTargets.SingularCapLowDegree
