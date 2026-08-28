import ConstructionTargets.SingularPathChain
import ConstructionTargets.FundamentalGroupAbelianizationNaturality

/-!
# The degree-one Hurewicz homomorphism

This file constructs the natural homomorphism from the fundamental group to
the multiplicative form of integral singular first homology and factors it
through group abelianization.  It does not prove that the factor is an
isomorphism.
-/

noncomputable section

namespace ConstructionTargets.DegreeOneHurewiczMap

open CategoryTheory
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.SingularPathChain
open ConstructionTargets.FundamentalGroupAbelianizationNaturality

abbrev IntegralH1 (X : Type) [TopologicalSpace X] :=
  ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
    (TopCat.of X)

/-- The element of integral H1 represented by a based loop. -/
def basedLoopH1Element {X : Type} [TopologicalSpace X] {x : X}
    (gamma : Path x x) : IntegralH1 X :=
  basedLoopH1Class gamma (1 : ℤ)

theorem basedLoopH1Element_eq_of_homotopy {X : Type} [TopologicalSpace X]
    {x : X} {gamma delta : Path x x} (H : Path.Homotopy gamma delta) :
    basedLoopH1Element gamma = basedLoopH1Element delta := by
  exact congrArg (fun k ↦ k (1 : ℤ))
    (basedLoopH1Class_eq_of_homotopy H)

@[simp] theorem basedLoopH1Element_trans {X : Type} [TopologicalSpace X]
    {x : X} (gamma delta : Path x x) :
    basedLoopH1Element (gamma.trans delta) =
      basedLoopH1Element gamma + basedLoopH1Element delta := by
  exact congrArg (fun k ↦ k (1 : ℤ))
    (basedLoopH1Class_trans gamma delta)

@[simp] theorem basedLoopH1Element_refl {X : Type} [TopologicalSpace X]
    (x : X) : basedLoopH1Element (Path.refl x) = 0 := by
  have h := basedLoopH1Element_trans (Path.refl x) (Path.refl x)
  apply Eq.symm
  apply add_left_cancel (a := basedLoopH1Element (Path.refl x))
  simpa using h.symm

/-- Degree-one Hurewicz, with the additive target written multiplicatively so
that it is a genuine group homomorphism.  Fundamental-group multiplication
represents `p * q` by the path `q.trans p`; commutativity of H1 reconciles this
with path traversal order. -/
noncomputable def fundamentalGroupH1Hom {X : Type} [TopologicalSpace X]
    (x : X) : FundamentalGroup X x →* Multiplicative (IntegralH1 X) where
  toFun := Quotient.lift
    (fun gamma : Path x x ↦ Multiplicative.ofAdd (basedLoopH1Element gamma))
    (fun gamma delta h ↦ congrArg Multiplicative.ofAdd
      (basedLoopH1Element_eq_of_homotopy h.some))
  map_one' := by
    change Multiplicative.ofAdd (basedLoopH1Element (Path.refl x)) = 1
    simp
  map_mul' p q := by
    induction p, q using Path.Homotopic.Quotient.ind₂ with
    | mk gamma delta =>
      change Multiplicative.ofAdd (basedLoopH1Element (delta.trans gamma)) =
        Multiplicative.ofAdd (basedLoopH1Element gamma) *
          Multiplicative.ofAdd (basedLoopH1Element delta)
      simp [add_comm]

@[simp] theorem fundamentalGroupH1Hom_mk {X : Type} [TopologicalSpace X]
    {x : X} (gamma : Path x x) :
    fundamentalGroupH1Hom x (Path.Homotopic.Quotient.mk gamma) =
      Multiplicative.ofAdd (basedLoopH1Element gamma) := rfl

/-- Path-chain classes commute with continuous postcomposition. -/
theorem basedLoopH1Class_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) {x : X} (gamma : Path x x) :
    basedLoopH1Class gamma ≫
        HomologicalComplex.homologyMap (singularPostcomposition f) 1 =
      basedLoopH1Class (gamma.map f.continuous) := by
  rw [basedLoopH1Class, basedLoopH1Class]
  have hnat := HomologicalComplex.homologyπ_naturality
    (singularPostcomposition f) 1
  slice_lhs 2 3 => exact hnat
  have hcycles : basedLoopCycle gamma ≫
      HomologicalComplex.cyclesMap (singularPostcomposition f) 1 =
      basedLoopCycle (gamma.map f.continuous) := by
    apply (cancel_mono ((SingularChains (TopCat.of Y)).iCycles 1)).1
    rw [Category.assoc, HomologicalComplex.cyclesMap_i]
    simp only [← Category.assoc]
    rw [basedLoopCycle_i, pathChain_postcomp, basedLoopCycle_i]
  rw [← Category.assoc, hcycles]
  rfl

theorem fundamentalGroupH1Hom_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X)
    (p : FundamentalGroup X x) :
    Multiplicative.ofAdd
        ((HomologicalComplex.homologyMap (singularPostcomposition f) 1)
          (Multiplicative.toAdd (fundamentalGroupH1Hom x p))) =
      fundamentalGroupH1Hom (f x) (FundamentalGroup.map f x p) := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk gamma =>
    change Multiplicative.ofAdd
        ((HomologicalComplex.homologyMap (singularPostcomposition f) 1)
          (basedLoopH1Element gamma)) =
      Multiplicative.ofAdd (basedLoopH1Element (gamma.map f.continuous))
    apply congrArg Multiplicative.ofAdd
    exact congrArg (fun k ↦ k (1 : ℤ))
      (basedLoopH1Class_naturality f gamma)

/-- The canonical factor of degree-one Hurewicz through abelianization. -/
noncomputable def abelianizedFundamentalGroupToH1 {X : Type}
    [TopologicalSpace X] (x : X) :
    Abelianization (FundamentalGroup X x) →*
      Multiplicative (IntegralH1 X) :=
  Abelianization.lift (fundamentalGroupH1Hom x)

@[simp] theorem abelianizedFundamentalGroupToH1_of {X : Type}
    [TopologicalSpace X] (x : X) (p : FundamentalGroup X x) :
    abelianizedFundamentalGroupToH1 x (Abelianization.of p) =
      fundamentalGroupH1Hom x p := rfl

theorem abelianizedFundamentalGroupToH1_compatibility {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    (abelianizedFundamentalGroupToH1 (f x)).comp
        (fundamentalGroupAbelianizationMap f x) =
      Abelianization.lift
        ((fundamentalGroupH1Hom (f x)).comp (FundamentalGroup.map f x)) := by
  exact abelianizationLift_comp_fundamentalGroupAbelianizationMap f x _

#print axioms fundamentalGroupH1Hom
#print axioms basedLoopH1Class_naturality
#print axioms fundamentalGroupH1Hom_naturality
#print axioms abelianizedFundamentalGroupToH1_compatibility

end ConstructionTargets.DegreeOneHurewiczMap
