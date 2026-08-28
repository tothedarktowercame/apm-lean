import ConstructionTargets.SolidTorusGluingOpenCover
import ConstructionTargets.T02A06SphereShift
import ConstructionTargets.PuncturedNormedSpaceRadialEquivalence

/-!
# A pole-complement open cover of the boundary torus

The second circle factor is covered by the complements of two antipodal
poles.  The one-pole pieces retract to the first circle, while the overlap is
reduced to the unit sphere in the pole's one-dimensional orthogonal
complement, times the first circle.
-/

open Set Topology
open scoped ContinuousMap

noncomputable section

namespace ConstructionTargets.BoundaryTorusOpenCover

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.PuncturedNormedSpaceRadialEquivalence
open ConstructionTargets.T02A06SphereShift
open ConstructionTargets.T02A06HemisphereExcision
open T02A06

abbrev SphereOne := ambientSphere 1

def southPoleComplement : Set SphereOne := {x | x ≠ -(northPole 1)}

theorem southPoleComplement_isOpen : IsOpen southPoleComplement := by
  exact isClosed_singleton.isOpen_compl

def leftOpen : Set BoundaryTorus := {z | z.2 ∈ northPoleComplement 1}

def rightOpen : Set BoundaryTorus := {z | z.2 ∈ southPoleComplement}

theorem leftOpen_isOpen : IsOpen leftOpen :=
  (northPoleComplement_isOpen 1).preimage continuous_snd

theorem rightOpen_isOpen : IsOpen rightOpen :=
  southPoleComplement_isOpen.preimage continuous_snd

theorem northPole_ne_neg : northPole 1 ≠ -(northPole 1) := by
  intro h
  have hv : (northPole 1).1 = -(northPole 1).1 := congrArg Subtype.val h
  have htwo : (2 : ℝ) • (northPole 1).1 = 0 := by
    calc
      (2 : ℝ) • (northPole 1).1 = (northPole 1).1 + (northPole 1).1 := two_smul ℝ _
      _ = (northPole 1).1 + -(northPole 1).1 := congrArg ((northPole 1).1 + ·) hv
      _ = 0 := add_neg_cancel _
  have hz : (northPole 1).1 = 0 :=
    (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hn : ‖(northPole 1).1‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using (northPole 1).2
  rw [hz, norm_zero] at hn
  norm_num at hn

theorem leftOpen_union_rightOpen : leftOpen ∪ rightOpen = Set.univ := by
  ext z
  simp only [leftOpen, rightOpen, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  by_cases hz : z.2 = northPole 1
  · right
    simpa [southPoleComplement, hz] using northPole_ne_neg
  · left
    rw [northPoleComplement_eq_compl_singleton]
    simpa

def productSubtypeHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (s : Set Y) :
    {p : X × Y // p.2 ∈ s} ≃ₜ X × s where
  toFun p := (p.1.1, ⟨p.1.2, p.2⟩)
  invFun p := ⟨(p.1, p.2.1), p.2.2⟩
  left_inv p := by ext <;> rfl
  right_inv p := by ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def leftOpenProductHomeomorph : leftOpen ≃ₜ Circle × northPoleComplement 1 :=
  productSubtypeHomeomorph (northPoleComplement 1)

def negSphereOne : SphereOne ≃ₜ SphereOne where
  toFun x := -x
  invFun x := -x
  left_inv x := neg_neg x
  right_inv x := neg_neg x
  continuous_toFun := continuous_neg.comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun := continuous_neg.comp continuous_subtype_val |>.subtype_mk _

def southToNorthComplementHomeomorph :
    southPoleComplement ≃ₜ northPoleComplement 1 where
  toFun x := ⟨-x.1, by
    rw [northPoleComplement_eq_compl_singleton]
    change -x.1 ≠ northPole 1
    intro hx
    apply x.2
    have := congrArg Neg.neg hx
    simpa using this⟩
  invFun x := ⟨-x.1, by
    change -x.1 ≠ -(northPole 1)
    have hx : x.1 ≠ northPole 1 := by
      have hxmem : x.1 ∈ ({northPole 1}ᶜ : Set SphereOne) := by
        rw [← northPoleComplement_eq_compl_singleton]
        exact x.2
      exact hxmem
    simpa using hx⟩
  left_inv x := by apply Subtype.ext; exact neg_neg x.1
  right_inv x := by apply Subtype.ext; exact neg_neg x.1
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def rightOpenProductHomeomorph : rightOpen ≃ₜ Circle × northPoleComplement 1 :=
  (productSubtypeHomeomorph southPoleComplement).trans
    (Homeomorph.prodCongr (Homeomorph.refl Circle)
      southToNorthComplementHomeomorph)

noncomputable def northComplementHomotopyEquivUnit :
    northPoleComplement 1 ≃ₕ Unit :=
  Classical.choice (ContractibleSpace.hequiv_unit (northPoleComplement 1))

def circleTimesNorthComplementHomotopyEquiv :
    (Circle × northPoleComplement 1) ≃ₕ Circle :=
  ((ContinuousMap.HomotopyEquiv.refl Circle).prodCongr
      northComplementHomotopyEquivUnit).trans
    (Homeomorph.prodUnique Circle Unit).toHomotopyEquiv

def leftOpenHomotopyEquivCircle : leftOpen ≃ₕ Circle :=
  leftOpenProductHomeomorph.toHomotopyEquiv.trans
    circleTimesNorthComplementHomotopyEquiv

def rightOpenHomotopyEquivCircle : rightOpen ≃ₕ Circle :=
  rightOpenProductHomeomorph.toHomotopyEquiv.trans
    circleTimesNorthComplementHomotopyEquiv

abbrev Overlap := (leftOpen ∩ rightOpen : Set BoundaryTorus)

def northPoleVector : Plane := (northPole 1).1

theorem norm_northPoleVector : ‖northPoleVector‖ = 1 := by
  simpa [northPoleVector, Metric.mem_sphere, dist_zero_right] using
    (northPole 1).2

theorem polePoint_northPole :
    polePoint northPoleVector norm_northPoleVector = northPole 1 := by
  apply Subtype.ext
  rfl

def overlapProductHomeomorph :
    Overlap ≃ₜ Circle × TwoPoleComplement northPoleVector norm_northPoleVector where
  toFun z := ⟨z.1.1, ⟨z.1.2, by
    constructor
    · rw [polePoint_northPole]
      have hz := z.2.1
      change z.1.2 ∈ northPoleComplement 1 at hz
      rw [northPoleComplement_eq_compl_singleton] at hz
      exact hz
    · rw [polePoint_northPole]
      have hz := z.2.2
      change z.1.2 ∈ southPoleComplement at hz
      exact hz⟩⟩
  invFun z := ⟨(z.1, z.2.1), by
    constructor
    · change z.2.1 ∈ northPoleComplement 1
      rw [northPoleComplement_eq_compl_singleton]
      simpa [polePoint_northPole] using z.2.2.1
    · change z.2.1 ∈ southPoleComplement
      simpa [southPoleComplement, polePoint_northPole] using z.2.2.2⟩
  left_inv z := by ext <;> rfl
  right_inv z := by ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def overlapHomotopyEquivOrthogonalSphereTimesCircle :
    Overlap ≃ₕ
      (UnitSphere ((ℝ ∙ northPoleVector)ᗮ) × Circle) :=
  overlapProductHomeomorph.toHomotopyEquiv.trans <|
    ((ContinuousMap.HomotopyEquiv.refl Circle).prodCongr
      (twoPoleComplementHomotopyEquivOrthogonalSphere
        northPoleVector norm_northPoleVector)).trans
      (Homeomorph.prodComm Circle
        (UnitSphere ((ℝ ∙ northPoleVector)ᗮ))).toHomotopyEquiv

def northPoleOrthogonalLinearIsometryEquiv :
    ((ℝ ∙ northPoleVector)ᗮ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) := by
  letI : Fact (Module.finrank ℝ Plane = 1 + 1) := ⟨by simp⟩
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton 1
    (by
      intro h
      have hn := norm_northPoleVector
      rw [h, norm_zero] at hn
      norm_num at hn)).repr

def unitSphereHomeomorphOfLinearIsometryEquiv
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) : UnitSphere E ≃ₜ UnitSphere F where
  toFun x := ⟨e x.1, by
    simpa [Metric.mem_sphere, dist_zero_right] using x.2⟩
  invFun y := ⟨e.symm y.1, by
    simpa [Metric.mem_sphere, dist_zero_right] using y.2⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.1
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.1
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

abbrev SphereZero := ambientSphere 0

def orthogonalSphereHomeomorphSphereZero :
    UnitSphere ((ℝ ∙ northPoleVector)ᗮ) ≃ₜ SphereZero :=
  unitSphereHomeomorphOfLinearIsometryEquiv
    northPoleOrthogonalLinearIsometryEquiv

theorem sphereZero_coord (x : SphereZero) :
    x.1 0 = 1 ∨ x.1 0 = -1 := by
  have hs : (x.1 0) ^ 2 = (1 : ℝ) := by
    have hx := x.2
    change x.1 ∈ Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 1)) 1 at hx
    rw [EuclideanSpace.sphere_zero_eq 1 zero_le_one] at hx
    simpa using hx
  exact sq_eq_one_iff.mp hs

def sphereZeroSign (x : SphereZero) : Bool :=
  decide (x.1 0 = 1)

theorem sphereZeroSign_injective : Function.Injective sphereZeroSign := by
  intro x y hxy
  apply Subtype.ext
  ext i
  fin_cases i
  rcases sphereZero_coord x with hx | hx <;>
    rcases sphereZero_coord y with hy | hy
  · exact hx.trans hy.symm
  · have hx' : sphereZeroSign x = true := by simp [sphereZeroSign, hx]
    have hy' : sphereZeroSign y = false := by
      simp [sphereZeroSign, hy]
      norm_num
    rw [hx', hy'] at hxy
    contradiction
  · have hx' : sphereZeroSign x = false := by
      simp [sphereZeroSign, hx]
      norm_num
    have hy' : sphereZeroSign y = true := by simp [sphereZeroSign, hy]
    rw [hx', hy'] at hxy
    contradiction
  · exact hx.trans hy.symm

def sphereZeroPositive : SphereZero := northPole 0

def sphereZeroNegative : SphereZero := -(northPole 0)

theorem sphereZeroSign_positive : sphereZeroSign sphereZeroPositive = true := by
  simp [sphereZeroPositive, sphereZeroSign, northPole, euclideanSnoc]

theorem sphereZeroSign_negative : sphereZeroSign sphereZeroNegative = false := by
  simp [sphereZeroNegative, sphereZeroSign, northPole, euclideanSnoc]
  norm_num

theorem sphereZeroSign_surjective : Function.Surjective sphereZeroSign := by
  intro b
  cases b
  · exact ⟨sphereZeroNegative, sphereZeroSign_negative⟩
  · exact ⟨sphereZeroPositive, sphereZeroSign_positive⟩

def sphereZeroEquivBool : SphereZero ≃ Bool :=
  Equiv.ofBijective sphereZeroSign
    ⟨sphereZeroSign_injective, sphereZeroSign_surjective⟩

noncomputable instance sphereZeroFinite : Finite SphereZero :=
  Finite.of_injective sphereZeroSign sphereZeroSign_injective

noncomputable instance sphereZeroDiscreteTopology : DiscreteTopology SphereZero :=
  Finite.instDiscreteTopology

def sphereZeroHomeomorphBool : SphereZero ≃ₜ Bool :=
  Homeomorph.ofDiscrete sphereZeroEquivBool

def orthogonalSphereHomeomorphBool :
    UnitSphere ((ℝ ∙ northPoleVector)ᗮ) ≃ₜ Bool :=
  orthogonalSphereHomeomorphSphereZero.trans sphereZeroHomeomorphBool

def boolTimesCircleHomeomorphTwoCircles :
    Bool × Circle ≃ₜ Circle ⊕ Circle :=
  ((Homeomorph.ofDiscrete Equiv.boolEquivPUnitSumPUnit.{0, 0}).prodCongr
      (Homeomorph.refl Circle)).trans <|
    Homeomorph.sumProdDistrib.trans <|
      Homeomorph.sumCongr (Homeomorph.uniqueProd PUnit.{1} Circle)
        (Homeomorph.uniqueProd PUnit.{1} Circle)

def overlapHomotopyEquivTwoCircles : Overlap ≃ₕ Circle ⊕ Circle :=
  overlapHomotopyEquivOrthogonalSphereTimesCircle.trans <|
    ((orthogonalSphereHomeomorphBool.prodCongr (Homeomorph.refl Circle)).trans
      boolTimesCircleHomeomorphTwoCircles).toHomotopyEquiv

#print axioms leftOpen_union_rightOpen
#print axioms leftOpenHomotopyEquivCircle
#print axioms rightOpenHomotopyEquivCircle
#print axioms overlapProductHomeomorph
#print axioms overlapHomotopyEquivOrthogonalSphereTimesCircle
#print axioms sphereZeroHomeomorphBool
#print axioms overlapHomotopyEquivTwoCircles

end ConstructionTargets.BoundaryTorusOpenCover
