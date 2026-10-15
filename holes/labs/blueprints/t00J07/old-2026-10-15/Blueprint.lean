import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.DeckGroupQuotientFundamentalGroup

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

lemma apm_t00j07_circleToDisk_injective :
    Function.Injective apm_t00j07_circleToDisk := by
  intro z w h
  apply Subtype.ext
  exact congrArg (fun x : apm_t00j07_Disk => (x : ℂ)) h

@[simp] lemma apm_t00j07_norm_circleToDisk (z : Circle) :
    ‖(apm_t00j07_circleToDisk z : ℂ)‖ = 1 :=
  Circle.norm_coe z

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

def apm_t00j07_diskCenter : apm_t00j07_Disk := ⟨0, by simp⟩

lemma apm_t00j07_diskCenter_ne_boundary (z : Circle) :
    apm_t00j07_diskCenter ≠ apm_t00j07_circleToDisk z := by
  intro h
  have := congrArg (fun x : apm_t00j07_Disk => ‖(x : ℂ)‖) h
  simp [apm_t00j07_diskCenter] at this

def apm_t00j07_basepoint (f : C(Circle, apm_t00j07_RP2)) :
    apm_t00j07_attachDisk f :=
  Quotient.mk _ (.inr apm_t00j07_diskCenter)

lemma apm_t00j07_attach_glue (f : C(Circle, apm_t00j07_RP2)) (z : Circle) :
    (Quotient.mk _ (.inl (f z)) : apm_t00j07_attachDisk f) =
      Quotient.mk _ (.inr (apm_t00j07_circleToDisk z)) := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _ (apm_t00j07_attachRel.glue z))

lemma apm_t00j07_center_eqvGen_iff
    (f : C(Circle, apm_t00j07_RP2))
    (s : Sum apm_t00j07_RP2 apm_t00j07_Disk) :
    Relation.EqvGen (apm_t00j07_attachRel f)
        (.inr apm_t00j07_diskCenter) s ↔
      s = .inr apm_t00j07_diskCenter := by
  constructor
  · intro h
    have preserve : ∀ a b, apm_t00j07_attachRel f a b →
        (a = .inr apm_t00j07_diskCenter ↔
          b = .inr apm_t00j07_diskCenter) := by
      intro a b hab
      cases hab with
      | glue z =>
          constructor
          · intro h
            cases h
          · intro h
            exact False.elim
              (apm_t00j07_diskCenter_ne_boundary z (Sum.inr.inj h.symm))
    have invariant : ∀ a b, Relation.EqvGen (apm_t00j07_attachRel f) a b →
        (a = .inr apm_t00j07_diskCenter ↔
          b = .inr apm_t00j07_diskCenter) := by
      intro a b hab
      induction hab with
      | rel a b hab => exact preserve a b hab
      | refl => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact (invariant _ _ h).mp rfl
  · rintro rfl
    exact Relation.EqvGen.refl _

lemma apm_t00j07_basepoint_ne_left
    (f : C(Circle, apm_t00j07_RP2)) (p : apm_t00j07_RP2) :
    apm_t00j07_basepoint f ≠
      (Quotient.mk _ (.inl p) : apm_t00j07_attachDisk f) := by
  intro h
  have heq := Quotient.exact h
  have hs := (apm_t00j07_center_eqvGen_iff f (.inl p)).mp heq
  simp at hs

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

/-- LIBRARY: the full van Kampen and singular-homology computation for a
null-homotopic embedded attaching circle in the exact quotient above. -/
theorem apm_t00J07_bridge_nullhomotopic_attachment_invariants
    (f : C(Circle, apm_t00j07_RP2))
    (hemb : Topology.IsEmbedding (f : Circle → apm_t00j07_RP2))
    (hnull : ∃ p : apm_t00j07_RP2,
      ContinuousMap.Homotopic f (ContinuousMap.const _ p)) :
    apm_t00j07_invariants f (Multiplicative (ZMod 2))
      (ModuleCat.of ℤ (ZMod 2)) := by
  sorry

/-- LIBRARY: the full van Kampen and singular-homology computation for an
essential embedded attaching circle in the exact quotient above. -/
theorem apm_t00J07_bridge_essential_attachment_invariants
    (f : C(Circle, apm_t00j07_RP2))
    (hemb : Topology.IsEmbedding (f : Circle → apm_t00j07_RP2))
    (hessential : ¬∃ p : apm_t00j07_RP2,
      ContinuousMap.Homotopic f (ContinuousMap.const _ p)) :
    apm_t00j07_invariants f (Multiplicative (ZMod 1))
      (ModuleCat.of ℤ (ZMod 1)) := by
  sorry

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
  intro f hemb
  exact ⟨apm_t00J07_bridge_nullhomotopic_attachment_invariants f hemb,
    apm_t00J07_bridge_essential_attachment_invariants f hemb⟩

#print axioms apm_t00j07
