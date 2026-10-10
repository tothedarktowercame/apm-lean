import ConstructionTargets.ProjectiveSpaceTopology
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Continuous descent to projective space

This file packages the quotient-topology facts needed to descend homogeneous
maps and homotopies from nonzero vectors to projective space.  Establishing
that a particular formula is nonzero and constant on scalar orbits remains a
consumer-local algebraic obligation.
-/

open Set Topology
open ConstructionTargets.ProjectiveSpaceTopology

noncomputable section
namespace ConstructionTargets.ProjectiveQuotientDescent

variable (K : Type) [NontriviallyNormedField K]

private def projectiveUnitSmulHomeomorph (n : ℕ) (a : Kˣ) :
    NonzeroVectors K n ≃ₜ NonzeroVectors K n where
  toFun x := a • x
  invFun x := a⁻¹ • x
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val : Continuous
      (fun x : NonzeroVectors K n => x.1)).const_smul (a : K)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val : Continuous
      (fun x : NonzeroVectors K n => x.1)).const_smul ((a⁻¹ : Kˣ) : K)

/-- The canonical map from nonzero vectors to projective space is open. -/
theorem projectiveQuotientMap_isOpen (n : ℕ) :
    IsOpenMap (quotientMap K n) := by
  have hq : IsQuotientMap (quotientMap K n) :=
    ⟨surjective_quotientMap K n, rfl⟩
  intro U hU
  apply hq.isOpen_preimage.mp
  rw [show (quotientMap K n) ⁻¹' ((quotientMap K n) '' U) =
      ⋃ a : Kˣ, (a • ·) '' U by
    ext x
    simp only [mem_preimage, mem_image, mem_iUnion]
    constructor
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨a, ha⟩ :=
        (Projectivization.mk_eq_mk_iff K x.1 y.1 x.2 y.2).mp hxy.symm
      exact ⟨a, y, hy, Subtype.ext ha⟩
    · rintro ⟨a, y, hy, hxy⟩
      refine ⟨y, hy, ?_⟩
      apply (Projectivization.mk_eq_mk_iff K y.1 x.1 y.2 x.2).mpr
      exact ⟨a⁻¹, by
        have ha := congrArg Subtype.val hxy
        rw [← ha]
        simp⟩]
  exact isOpen_iUnion fun a =>
    (projectiveUnitSmulHomeomorph K n a).isOpenMap U hU

private theorem projectiveQuotientMap_isOpenQuotient (n : ℕ) :
    IsOpenQuotientMap (quotientMap K n) :=
  ⟨surjective_quotientMap K n, continuous_quotientMap K n,
    projectiveQuotientMap_isOpen K n⟩

/-- The projective quotient remains an open quotient after taking its product
with the closed unit interval. -/
theorem projectiveQuotientMap_prod_interval_isOpenQuotient (n : ℕ) :
    IsOpenQuotientMap
      (Prod.map (quotientMap K n)
        (fun t : Set.Icc (0 : ℝ) 1 => t)) :=
  (projectiveQuotientMap_isOpenQuotient K n).prodMap
    (IsOpenQuotientMap.id : IsOpenQuotientMap
      (fun t : Set.Icc (0 : ℝ) 1 => t))

/-- A continuous function on nonzero vectors which is constant on nonzero
scalar orbits factors continuously through projective space. -/
theorem projectiveHomogeneousMapDescent {n : ℕ} {Y : Type*}
    [TopologicalSpace Y] (f : NonzeroVectors K n → Y) (hf : Continuous f)
    (horbit : ∀ (a b : NonzeroVectors K n) (t : K),
      a = t • (b : Vectors K n) → f a = f b) :
    ∃ g : C(Space K n, Y), ∀ v, g (quotientMap K n v) = f v := by
  let g : Space K n → Y := Projectivization.lift f horbit
  have hcomp : g ∘ quotientMap K n = f := by
    funext v
    exact Projectivization.lift_mk f horbit v.1 v.2
  have hg : Continuous g :=
    (projectiveQuotientMap_isOpenQuotient K n).isQuotientMap.continuous_iff.mpr
      (hcomp.symm ▸ hf)
  exact ⟨⟨g, hg⟩, fun v => congrFun hcomp v⟩

/-- An interval-parametrized continuous function on nonzero vectors which is
constant on scalar orbits factors continuously through projective space times
the interval. -/
theorem projectiveHomogeneousHomotopyDescent {n : ℕ} {Y : Type*}
    [TopologicalSpace Y]
    (f : NonzeroVectors K n × Set.Icc (0 : ℝ) 1 → Y) (hf : Continuous f)
    (horbit : ∀ (a b : NonzeroVectors K n) (s : Set.Icc (0 : ℝ) 1) (t : K),
      a = t • (b : Vectors K n) → f (a, s) = f (b, s)) :
    ∃ g : C(Space K n × Set.Icc (0 : ℝ) 1, Y),
      ∀ z, g (quotientMap K n z.1, z.2) = f z := by
  let g : Space K n × Set.Icc (0 : ℝ) 1 → Y := fun z =>
    Projectivization.lift (fun v => f (v, z.2))
      (fun a b t hab => horbit a b z.2 t hab) z.1
  have hcomp : g ∘ Prod.map (quotientMap K n)
      (fun t : Set.Icc (0 : ℝ) 1 => t) = f := by
    funext z
    exact Projectivization.lift_mk (fun v => f (v, z.2))
      (fun a b t hab => horbit a b z.2 t hab) z.1.1 z.1.2
  have hg : Continuous g :=
    (projectiveQuotientMap_prod_interval_isOpenQuotient K n).isQuotientMap.continuous_iff.mpr
      (hcomp.symm ▸ hf)
  exact ⟨⟨g, hg⟩, fun z => congrFun hcomp z⟩

-- The two consumer generalities elaborate without specialized infrastructure.
#check projectiveHomogeneousMapDescent (K := ℝ) (n := 3)
#check projectiveHomogeneousMapDescent (K := ℂ)
#check projectiveHomogeneousHomotopyDescent (K := ℝ) (n := 3)
#check projectiveHomogeneousHomotopyDescent (K := ℂ)

end ConstructionTargets.ProjectiveQuotientDescent
