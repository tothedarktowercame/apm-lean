import ConstructionTargets.TorusCircleWedgeOpenCover
import ConstructionTargets.BoundaryTorusH0Cokernel
import ConstructionTargets.T00A01MayerVietorisAdapters

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

namespace ConstructionTargets.TorusCircleWedgeMayerVietoris

open ConstructionTargets.TorusCircleWedgeOpenCover
open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.BoundaryTorusMayerVietoris
open ConstructionTargets.BoundaryTorusH0Cokernel
open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.CircleHomology
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.IntegralSingularHomologyComparison
open ConstructionTargets.T00A01MayerVietorisAdapters
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.BoundaryTorusIntegralHomologyComplete
open ConstructionTargets.BoundaryTorusH2ConnectingIso

private abbrev H (n : ℕ) (X : Type) [TopologicalSpace X] :=
  SingularHomology n (TopCat.of X)

private abbrev MH (n : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

noncomputable instance : Nonempty U :=
  ⟨⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inl (1, 1)),
    ⟨.inl (1, 1), trivial, rfl⟩⟩⟩

noncomputable instance : Nonempty V :=
  ⟨⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inr 1),
    ⟨.inr 1, trivial, rfl⟩⟩⟩

noncomputable instance : Nonempty (U ∩ V : Set GenericWedge) :=
  ⟨⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inl (1, 1)),
    ⟨⟨.inl (1, 1), trivial, rfl⟩,
      ⟨.inl (1, 1), one_one_mem_N, rfl⟩⟩⟩⟩

noncomputable def overlapH0GroupIsoInt :
    H 0 (U ∩ V : Set GenericWedge) ≅ AddCommGrpCat.of ℤ :=
  singularHomologyIsoOfHomotopyEquiv UVHomotopyEquiv 0 ≪≫
    contractibleH0IsoInt Unit

noncomputable def leftH0GroupIsoInt :
    H 0 U ≅ AddCommGrpCat.of ℤ :=
  singularHomologyIsoOfHomotopyEquiv UHomotopyEquiv 0 ≪≫
    singularHomologyIsoOfHomotopyEquiv
      ((Homeomorph.refl Circle).prodCongr circleHomeomorphSphereOne).toHomotopyEquiv 0 ≪≫
    boundaryTorusH0GroupIsoInt

noncomputable def rightH0GroupIsoInt :
    H 0 V ≅ AddCommGrpCat.of ℤ :=
  singularHomologyIsoOfHomotopyEquiv VHomotopyEquiv 0 ≪≫
    circleH0GroupIsoInt

noncomputable def genericWedgeH0GroupIsoInt :
    H 0 GenericWedge ≅ AddCommGrpCat.of ℤ :=
  openCoverH0IsoOfCoordinates U V U_isOpen V_isOpen U_union_V
    overlapH0GroupIsoInt leftH0GroupIsoInt rightH0GroupIsoInt

noncomputable def genericWedgeH0ModuleIsoInt :
    MH 0 GenericWedge ≅ ModuleCat.of ℤ ℤ :=
  singularHomologyModuleIsoOfGroupIso (TopCat.of GenericWedge) 0 _
    genericWedgeH0GroupIsoInt

theorem overlapH1Group_isZero :
    IsZero (H 1 (U ∩ V : Set GenericWedge)) :=
  (contractibleHigherHomology_isZero Unit 1 (by omega)).of_iso
    (singularHomologyIsoOfHomotopyEquiv UVHomotopyEquiv 1)

noncomputable instance productionReassemblyArrow_H1_isIso :
    IsIso (productionReassemblyArrow U V 1) := by
  letI : Mono (productionReassemblyArrow U V 1) :=
    (productionMayerVietoris_exact_pieces U V U_isOpen V_isOpen U_union_V 1).mono_g_iff.mpr
      (overlapH1Group_isZero.eq_of_src _ _)
  letI : Mono (productionIntersectionArrow U V 0) :=
    productionIntersectionArrow_mono_zero_of_coordinates U V
      overlapH0GroupIsoInt leftH0GroupIsoInt
  have hconn : productionConnecting U V U_isOpen V_isOpen U_union_V 0 = 0 :=
    (productionMayerVietoris_exact_intersection U V U_isOpen V_isOpen U_union_V 0).mono_g_iff.mp
      (by infer_instance)
  letI : Epi (productionReassemblyArrow U V 1) :=
    (productionMayerVietoris_exact_union U V U_isOpen V_isOpen U_union_V 0).epi_f_iff.mpr hconn
  exact isIso_of_mono_of_epi _

noncomputable def leftH1GroupIsoFinTwo :
    H 1 U ≅ AddCommGrpCat.of (Fin 2 → ℤ) :=
  singularHomologyIsoOfHomotopyEquiv UHomotopyEquiv 1 ≪≫
    singularHomologyIsoOfHomotopyEquiv
      ((Homeomorph.refl Circle).prodCongr circleHomeomorphSphereOne).toHomotopyEquiv 1 ≪≫
    boundaryTorusH1GroupIsoFinTwo

noncomputable def rightH1GroupIsoInt :
    H 1 V ≅ AddCommGrpCat.of ℤ :=
  singularHomologyIsoOfHomotopyEquiv VHomotopyEquiv 1 ≪≫
    circleH1GroupIsoInt

/-- Identify the torus rank-two coordinates followed by the circle coordinate
with `Fin 3` coordinates in that same order. -/
def torusFirstFinThreeLinearEquiv :
    ((Fin 2 → ℤ) × ℤ) ≃ₗ[ℤ] (Fin 3 → ℤ) where
  toFun p := Fin.lastCases p.2 p.1
  invFun g := (fun i => g i.castSucc, g (Fin.last 2))
  left_inv p := by
    apply Prod.ext
    · funext i
      simp
    · simp only [Fin.lastCases_last]
  right_inv g := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
    · simp only [Fin.lastCases_castSucc]
  map_add' p q := by
    funext i
    fin_cases i <;> rfl
  map_smul' z p := by
    funext i
    fin_cases i <;> rfl

def torusFirstFinThreeModuleIso :
    ModuleCat.of ℤ ((Fin 2 → ℤ) × ℤ) ≅ ModuleCat.of ℤ (Fin 3 → ℤ) :=
  torusFirstFinThreeLinearEquiv.toModuleIso

@[simp] theorem torusFirstFinThreeLinearEquiv_apply_zero
    (f : Fin 2 → ℤ) (z : ℤ) :
    torusFirstFinThreeLinearEquiv (f, z) (0 : Fin 3) = f 0 := rfl

@[simp] theorem torusFirstFinThreeLinearEquiv_apply_one
    (f : Fin 2 → ℤ) (z : ℤ) :
    torusFirstFinThreeLinearEquiv (f, z) (1 : Fin 3) = f 1 := rfl

@[simp] theorem torusFirstFinThreeLinearEquiv_apply_two
    (f : Fin 2 → ℤ) (z : ℤ) :
    torusFirstFinThreeLinearEquiv (f, z) (2 : Fin 3) = z := rfl

noncomputable def genericWedgeH1GroupIsoFinThree :
    H 1 GenericWedge ≅ AddCommGrpCat.of (Fin 3 → ℤ) :=
  (asIso (productionReassemblyArrow U V 1)).symm ≪≫
    biprod.mapIso leftH1GroupIsoFinTwo rightH1GroupIsoInt ≪≫
    AddCommGrpCat.biprodIsoProd
      (AddCommGrpCat.of (Fin 2 → ℤ)) (AddCommGrpCat.of ℤ) ≪≫
    forgetIntModules.mapIso torusFirstFinThreeModuleIso

noncomputable def genericWedgeH1ModuleIsoFinThree :
    MH 1 GenericWedge ≅ ModuleCat.of ℤ (Fin 3 → ℤ) :=
  singularHomologyModuleIsoOfGroupIso (TopCat.of GenericWedge) 1 _
    genericWedgeH1GroupIsoFinThree

theorem overlapPositiveGroup_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero (H n (U ∩ V : Set GenericWedge)) :=
  (contractibleHigherHomology_isZero Unit n hn).of_iso
    (singularHomologyIsoOfHomotopyEquiv UVHomotopyEquiv n)

noncomputable instance productionReassemblyArrow_isIso_of_two_le
    (n : ℕ) (hn : 2 ≤ n) : IsIso (productionReassemblyArrow U V n) := by
  have hm : Mono (productionReassemblyArrow U V n) :=
    (productionMayerVietoris_exact_pieces U V U_isOpen V_isOpen U_union_V n).mono_g_iff.mpr
      ((overlapPositiveGroup_isZero n (by omega)).eq_of_src _ _)
  have heq : n - 1 + 1 = n := by omega
  have he : Epi (productionReassemblyArrow U V n) := by
    rw [← heq]
    exact (productionMayerVietoris_exact_union U V U_isOpen V_isOpen U_union_V (n - 1)).epi_f_iff.mpr
      ((overlapPositiveGroup_isZero (n - 1) (by omega)).eq_of_tgt _ _)
  letI := hm
  letI := he
  exact isIso_of_mono_of_epi _

theorem rightH2Group_isZero : IsZero (H 2 V) :=
  (circleHomology_isZero_of_one_lt 2 (by omega)).of_iso
    (singularHomologyIsoOfHomotopyEquiv VHomotopyEquiv 2)

noncomputable def leftH2GroupIsoInt : H 2 U ≅ AddCommGrpCat.of ℤ :=
  singularHomologyIsoOfHomotopyEquiv UHomotopyEquiv 2 ≪≫
    singularHomologyIsoOfHomotopyEquiv
      ((Homeomorph.refl Circle).prodCongr circleHomeomorphSphereOne).toHomotopyEquiv 2 ≪≫
    boundaryTorusH2IsoInt

noncomputable def genericWedgeH2GroupIsoInt :
    H 2 GenericWedge ≅ AddCommGrpCat.of ℤ := by
  letI := productionReassemblyArrow_isIso_of_two_le 2 (by omega)
  letI : IsIso (biprod.inl : H 2 U ⟶ (H 2 U ⊞ H 2 V)) :=
    (CategoryTheory.Biprod.isIso_inl_iff_isZero _ _).mpr rightH2Group_isZero
  exact (asIso (productionReassemblyArrow U V 2)).symm ≪≫
    (asIso (biprod.inl : H 2 U ⟶ (H 2 U ⊞ H 2 V))).symm ≪≫
    leftH2GroupIsoInt

noncomputable def genericWedgeH2ModuleIsoInt :
    MH 2 GenericWedge ≅ ModuleCat.of ℤ ℤ :=
  singularHomologyModuleIsoOfGroupIso (TopCat.of GenericWedge) 2 _
    genericWedgeH2GroupIsoInt

theorem leftHigherGroup_isZero (n : ℕ) (hn : 3 ≤ n) : IsZero (H n U) :=
  (boundaryTorusHomology_isZero_of_two_lt n (by omega)).of_iso
    (singularHomologyIsoOfHomotopyEquiv UHomotopyEquiv n ≪≫
      singularHomologyIsoOfHomotopyEquiv
        ((Homeomorph.refl Circle).prodCongr circleHomeomorphSphereOne).toHomotopyEquiv n)

theorem rightHigherGroup_isZero (n : ℕ) (hn : 3 ≤ n) : IsZero (H n V) :=
  (circleHomology_isZero_of_one_lt n (by omega)).of_iso
    (singularHomologyIsoOfHomotopyEquiv VHomotopyEquiv n)

theorem genericWedgeHigherGroup_isZero (n : ℕ) (hn : 3 ≤ n) :
    IsZero (H n GenericWedge) := by
  letI := productionReassemblyArrow_isIso_of_two_le n (by omega)
  let hp : IsZero (H n U ⊞ H n V) :=
    (biprod_isZero_iff _ _).mpr ⟨leftHigherGroup_isZero n hn, rightHigherGroup_isZero n hn⟩
  exact hp.of_iso (asIso (productionReassemblyArrow U V n)).symm

theorem genericWedgeHigherModule_isZero (n : ℕ) (hn : 3 ≤ n) :
    IsZero (MH n GenericWedge) :=
  singularHomologyModuleIsZeroOfGroupIsZero (TopCat.of GenericWedge) n
    (genericWedgeHigherGroup_isZero n hn)

theorem genericWedge_complete_module_homology :
    Nonempty (MH 0 GenericWedge ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (MH 1 GenericWedge ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    Nonempty (MH 2 GenericWedge ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ n, 3 ≤ n → IsZero (MH n GenericWedge) :=
  ⟨⟨genericWedgeH0ModuleIsoInt⟩, ⟨genericWedgeH1ModuleIsoFinThree⟩,
    ⟨genericWedgeH2ModuleIsoInt⟩, genericWedgeHigherModule_isZero⟩

#print axioms overlapH0GroupIsoInt
#print axioms leftH0GroupIsoInt
#print axioms rightH0GroupIsoInt
#print axioms genericWedgeH0GroupIsoInt
#print axioms genericWedgeH0ModuleIsoInt
#print axioms overlapH1Group_isZero
#print axioms productionReassemblyArrow_H1_isIso
#print axioms torusFirstFinThreeLinearEquiv
#print axioms torusFirstFinThreeLinearEquiv_apply_zero
#print axioms torusFirstFinThreeLinearEquiv_apply_one
#print axioms torusFirstFinThreeLinearEquiv_apply_two
#print axioms genericWedgeH1GroupIsoFinThree
#print axioms genericWedgeH1ModuleIsoFinThree
#print axioms genericWedgeH2ModuleIsoInt
#print axioms genericWedgeHigherModule_isZero
#print axioms genericWedge_complete_module_homology

end ConstructionTargets.TorusCircleWedgeMayerVietoris
