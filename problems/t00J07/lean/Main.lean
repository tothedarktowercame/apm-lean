import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t00J07

## Statement repairs

The former conclusion used opaque adjunction and homology types, together with
axioms merely to inhabit them.  The disk adjunction is now the actual quotient
of `RP² ⊕ D²` by its attaching relation, and all homology groups are Mathlib's
integral singular homology.  No source claim is changed.
-/

open CategoryTheory Set
open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t00j07_RP2 := Projectivization ℝ (Fin 3 → ℝ)

noncomputable instance : TopologicalSpace apm_t00j07_RP2 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ (Fin 3 → ℝ))))

abbrev apm_t00j07_Disk := Metric.closedBall (0 : ℂ) 1

def apm_t00j07_circleToDisk (z : Circle) : apm_t00j07_Disk :=
  ⟨(z : ℂ), by simpa [mem_closedBall_zero_iff] using (Circle.norm_coe z).le⟩

inductive apm_t00j07_attachRel (f : C(Circle, apm_t00j07_RP2)) :
    Sum apm_t00j07_RP2 apm_t00j07_Disk →
      Sum apm_t00j07_RP2 apm_t00j07_Disk → Prop
  | glue (z : Circle) :
      apm_t00j07_attachRel f (.inl (f z)) (.inr (apm_t00j07_circleToDisk z))

def apm_t00j07_attachDisk (f : C(Circle, apm_t00j07_RP2)) :=
  Quotient (Relation.EqvGen.setoid (apm_t00j07_attachRel f))

noncomputable instance (f : C(Circle, apm_t00j07_RP2)) :
    TopologicalSpace (apm_t00j07_attachDisk f) :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t00j07_RP2 apm_t00j07_Disk =>
      Quotient.mk (Relation.EqvGen.setoid (apm_t00j07_attachRel f)) x)
    inferInstance

def apm_t00j07_diskCenter : apm_t00j07_Disk :=
  ⟨0, by simp⟩

def apm_t00j07_basepoint (f : C(Circle, apm_t00j07_RP2)) :
    apm_t00j07_attachDisk f :=
  Quotient.mk _ (.inr apm_t00j07_diskCenter)

abbrev apm_t00j07_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t00j07_invariants
    (f : C(Circle, apm_t00j07_RP2))
    (piOne : Type) [Group piOne] (hOne : ModuleCat ℤ) : Prop :=
  Nonempty
      (FundamentalGroup (apm_t00j07_attachDisk f)
        (apm_t00j07_basepoint f) ≃* piOne) ∧
    Nonempty
      (apm_t00j07_H 0 (apm_t00j07_attachDisk f) ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t00j07_H 1 (apm_t00j07_attachDisk f) ≅ hOne) ∧
    Nonempty
      (apm_t00j07_H 2 (apm_t00j07_attachDisk f) ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k, 3 ≤ k → Limits.IsZero (apm_t00j07_H k (apm_t00j07_attachDisk f))

theorem apm_t00j07 :
    ∀ f : C(Circle, apm_t00j07_RP2),
      Topology.IsEmbedding (f : Circle → apm_t00j07_RP2) →
      ((∃ p : apm_t00j07_RP2,
          ContinuousMap.Homotopic f (ContinuousMap.const _ p)) →
        apm_t00j07_invariants f (Multiplicative (ZMod 2))
          (ModuleCat.of ℤ (ZMod 2))) ∧
      ((¬∃ p : apm_t00j07_RP2,
          ContinuousMap.Homotopic f (ContinuousMap.const _ p)) →
        apm_t00j07_invariants f (Multiplicative (ZMod 1))
          (ModuleCat.of ℤ (ZMod 1))) := by
  sorry
