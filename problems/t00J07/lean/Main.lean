import Mathlib

/-!
# APM t00J07

## Statement repairs

None.

## Encoding questions

`RP²` is the actual real projectivization of `ℝ³`, with its quotient
topology, and the attaching map has the actual circle as domain. Mathlib does
not yet expose a topological disk-adjunction construction or general integral
singular-homology groups in a form usable here. Those two constructions are
therefore isolated as opaque, typed helpers; no geometric object is replaced
by a numerical surrogate.
-/

open Set
open scoped LinearAlgebra.Projectivization

abbrev apm_t00J07_RP2 := Projectivization ℝ (Fin 3 → ℝ)

noncomputable instance : TopologicalSpace apm_t00J07_RP2 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ (Fin 3 → ℝ))))

abbrev apm_t00J07_S1 := Metric.sphere (0 : ℂ) 1

/-- The adjunction space `RP² ∪_f D²`. -/
opaque apm_t00J07_attachDisk (f : C(apm_t00J07_S1, apm_t00J07_RP2)) : Type

axiom apm_t00J07_attachDiskNonempty
    (f : C(apm_t00J07_S1, apm_t00J07_RP2)) :
    Nonempty (apm_t00J07_attachDisk f)

opaque apm_t00J07_attachDiskTopology
    (f : C(apm_t00J07_S1, apm_t00J07_RP2)) :
    TopologicalSpace (apm_t00J07_attachDisk f)

noncomputable instance (f : C(apm_t00J07_S1, apm_t00J07_RP2)) :
    TopologicalSpace (apm_t00J07_attachDisk f) :=
  apm_t00J07_attachDiskTopology f

noncomputable def apm_t00J07_basepoint
    (f : C(apm_t00J07_S1, apm_t00J07_RP2)) : apm_t00J07_attachDisk f :=
  Classical.choice (apm_t00J07_attachDiskNonempty f)

/-- Integral singular homology of a topological space. -/
opaque apm_t00J07_homology (X : Type*) [TopologicalSpace X] (ℕdegree : ℕ) : Type

axiom apm_t00J07_homologyAddCommGroupExists
    (X : Type*) [TopologicalSpace X] (degree : ℕ) :
    Nonempty (AddCommGroup (apm_t00J07_homology X degree))

noncomputable instance (X : Type*) [TopologicalSpace X] (degree : ℕ) :
    AddCommGroup (apm_t00J07_homology X degree) :=
  Classical.choice (apm_t00J07_homologyAddCommGroupExists X degree)

/-- The requested fundamental-group and integral-homology values. -/
def apm_t00J07_invariants
    (f : C(apm_t00J07_S1, apm_t00J07_RP2))
    (piOne : Type*) [Group piOne] : Prop :=
  Nonempty
      (FundamentalGroup (apm_t00J07_attachDisk f)
        (apm_t00J07_basepoint f) ≃* piOne) ∧
    Nonempty (apm_t00J07_homology (apm_t00J07_attachDisk f) 0 ≃+ ℤ) ∧
    Nonempty (apm_t00J07_homology (apm_t00J07_attachDisk f) 2 ≃+ ℤ) ∧
    (∀ k, 3 ≤ k →
      Nonempty (apm_t00J07_homology (apm_t00J07_attachDisk f) k ≃+ ZMod 1))

theorem apm_t00j07 :
    ∀ f : C(apm_t00J07_S1, apm_t00J07_RP2),
      Topology.IsEmbedding (f : apm_t00J07_S1 → apm_t00J07_RP2) →
      ((∃ p : apm_t00J07_RP2,
          ContinuousMap.Homotopic f (ContinuousMap.const _ p)) →
        apm_t00J07_invariants f (Multiplicative (ZMod 2)) ∧
        Nonempty
          (apm_t00J07_homology (apm_t00J07_attachDisk f) 1 ≃+ ZMod 2)) ∧
      ((¬∃ p : apm_t00J07_RP2,
          ContinuousMap.Homotopic f (ContinuousMap.const _ p)) →
        apm_t00J07_invariants f (Multiplicative (ZMod 1)) ∧
        Nonempty
          (apm_t00J07_homology (apm_t00J07_attachDisk f) 1 ≃+ ZMod 1)) := by
  sorry
