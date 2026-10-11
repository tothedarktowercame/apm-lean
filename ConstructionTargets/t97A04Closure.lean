import ConstructionTargets.T97A04FrozenH1Coordinate
import ConstructionTargets.BoundaryTorusOpenCover

open CategoryTheory

noncomputable section

namespace ConstructionTargets.T97A04Closure

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.BoundaryTorusH2ConnectingIso
open ConstructionTargets.T97A04FrozenH1Coordinate
open ConstructionTargets.BoundaryTorusOpenCover

abbrev FrozenTorus :=
  ConstructionTargets.T97A04FrozenH1Coordinate.FrozenTorus

/-- The integral top-class coordinate on the frozen `AddCircle × AddCircle`
torus, transported along the same homeomorphism used by its aligned H₁
coordinate. -/
noncomputable def frozenTorusH2GroupIsoInt :
    SingularHomology 2 (TopCat.of FrozenTorus) ≅ AddCommGrpCat.of ℤ :=
  singularHomologyIsoOfHomotopyEquiv
      frozenTorusHomeomorphBoundaryTorus.toHomotopyEquiv 2 ≪≫
    boundaryTorusH2IsoInt

/-- The vertical two-open cover of the frozen torus, transported through the
fixed homeomorphism used to define its integral top-class coordinate. -/
structure FrozenYCover where
  U : Set FrozenTorus
  V : Set FrozenTorus
  U_isOpen : IsOpen U
  V_isOpen : IsOpen V
  union_eq_univ : U ∪ V = Set.univ
  U_eq_preimage :
    U = frozenTorusHomeomorphBoundaryTorus ⁻¹' leftOpen
  V_eq_preimage :
    V = frozenTorusHomeomorphBoundaryTorus ⁻¹' rightOpen

/-- The canonical vertical cover, not merely a homotopy-equivalent cover. -/
noncomputable def frozenYCover : FrozenYCover where
  U := frozenTorusHomeomorphBoundaryTorus ⁻¹' leftOpen
  V := frozenTorusHomeomorphBoundaryTorus ⁻¹' rightOpen
  U_isOpen := leftOpen_isOpen.preimage frozenTorusHomeomorphBoundaryTorus.continuous
  V_isOpen := rightOpen_isOpen.preimage frozenTorusHomeomorphBoundaryTorus.continuous
  union_eq_univ := by
    rw [← Set.preimage_union, leftOpen_union_rightOpen, Set.preimage_univ]
  U_eq_preimage := rfl
  V_eq_preimage := rfl

/-- Restrict a homeomorphism to the preimage of a set. -/
def homeomorphPreimageRestrict {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (s : Set Y) :
    e ⁻¹' s ≃ₜ s where
  toFun x := ⟨e x.1, x.2⟩
  invFun y := ⟨e.symm y.1, by simp only [Set.mem_preimage, e.apply_symm_apply]; exact y.2⟩
  left_inv x := by ext; exact e.symm_apply_apply x.1
  right_inv y := by ext; exact e.apply_symm_apply y.1
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The left member of `frozenYCover` is exactly the transported boundary
torus left member. -/
noncomputable def frozenYCoverUHomeomorph :
    frozenYCover.U ≃ₜ leftOpen :=
  (Homeomorph.ofEqSubtypes frozenYCover.U_eq_preimage).trans
    (homeomorphPreimageRestrict frozenTorusHomeomorphBoundaryTorus leftOpen)

/-- The right member of `frozenYCover` is exactly the transported boundary
torus right member. -/
noncomputable def frozenYCoverVHomeomorph :
    frozenYCover.V ≃ₜ rightOpen :=
  (Homeomorph.ofEqSubtypes frozenYCover.V_eq_preimage).trans
    (homeomorphPreimageRestrict frozenTorusHomeomorphBoundaryTorus rightOpen)

theorem frozenYCover_U_mem_iff (x : FrozenTorus) :
    x ∈ frozenYCover.U ↔ frozenTorusHomeomorphBoundaryTorus x ∈ leftOpen :=
  Iff.rfl

theorem frozenYCover_V_mem_iff (x : FrozenTorus) :
    x ∈ frozenYCover.V ↔ frozenTorusHomeomorphBoundaryTorus x ∈ rightOpen :=
  Iff.rfl

theorem frozenYCover_inter_mem_iff (x : FrozenTorus) :
    x ∈ frozenYCover.U ∩ frozenYCover.V ↔
      frozenTorusHomeomorphBoundaryTorus x ∈ leftOpen ∩ rightOpen :=
  Iff.rfl

/-- The cover overlap is transported by the same fixed homeomorphism. -/
noncomputable def frozenYCoverInterHomeomorph :
    (frozenYCover.U ∩ frozenYCover.V : Set FrozenTorus) ≃ₜ
      (leftOpen ∩ rightOpen : Set BoundaryTorus) :=
  (Homeomorph.ofEqSubtypes (by
    ext x
    exact frozenYCover_inter_mem_iff x)).trans
    (homeomorphPreimageRestrict frozenTorusHomeomorphBoundaryTorus
      (leftOpen ∩ rightOpen))

/-- The upper-triangular shear of the frozen torus.  Its second coordinate is
fixed, so it preserves the vertical cover literally. -/
def shearY (a b : ℤ) : C(FrozenTorus, FrozenTorus) where
  toFun p := (a • p.1 + b • p.2, p.2)
  continuous_toFun := by fun_prop

@[simp]
theorem shearY_apply (a b : ℤ) (p : FrozenTorus) :
    shearY a b p = (a • p.1 + b • p.2, p.2) :=
  rfl

theorem shearY_mem_U (a b : ℤ) {p : FrozenTorus}
    (hp : p ∈ frozenYCover.U) : shearY a b p ∈ frozenYCover.U := by
  rw [frozenYCover_U_mem_iff] at hp ⊢
  simpa [frozenTorusHomeomorphBoundaryTorus, leftOpen] using hp

theorem shearY_mem_V (a b : ℤ) {p : FrozenTorus}
    (hp : p ∈ frozenYCover.V) : shearY a b p ∈ frozenYCover.V := by
  rw [frozenYCover_V_mem_iff] at hp ⊢
  simpa [frozenTorusHomeomorphBoundaryTorus, rightOpen] using hp

theorem shearY_comp (a b c d : ℤ) :
    (shearY a b).comp (shearY c d) = shearY (a * c) (a * d + b) := by
  apply ContinuousMap.ext
  intro p
  apply Prod.ext
  · simp only [ContinuousMap.comp_apply, shearY_apply, smul_add, mul_smul, add_smul]
    abel
  · rfl

theorem shearY_three_one_apply (p : FrozenTorus) :
    shearY 3 1 p = ((3 : ℤ) • p.1 + p.2, p.2) := by
  simp only [shearY_apply, one_smul]

theorem shearY_one_neg_one_apply (p : FrozenTorus) :
    shearY 1 (-1) p = (p.1 - p.2, p.2) := by
  simp only [shearY_apply, one_smul, neg_smul, sub_eq_add_neg]

theorem shearY_one_zero_apply (p : FrozenTorus) :
    shearY 1 0 p = p := by
  rcases p with ⟨x, y⟩
  simp

#print axioms frozenTorusH2GroupIsoInt
#print axioms frozenYCover
#print axioms frozenYCoverUHomeomorph
#print axioms frozenYCoverVHomeomorph
#print axioms frozenYCoverInterHomeomorph
#print axioms shearY
#print axioms shearY_mem_U
#print axioms shearY_mem_V
#print axioms shearY_comp

end ConstructionTargets.T97A04Closure
