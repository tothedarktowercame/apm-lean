import Mathlib

/-! Projective space with the quotient topology from nonzero vectors.
This adds no global instance to Mathlib's algebraic Projectivization: Space is
our explicit type wrapper, so later smooth-chart work has one specified topology.
No homology, smooth structure or classification theorem is assumed. -/

noncomputable section
namespace ConstructionTargets.ProjectiveSpaceTopology

variable (K : Type) [NontriviallyNormedField K]

abbrev Vectors (n : ℕ) := Fin (n + 1) → K
abbrev NonzeroVectors (n : ℕ) := {v : Vectors K n // v ≠ 0}

def Space (n : ℕ) := Projectivization K (Vectors K n)

def quotientMap (n : ℕ) (v : NonzeroVectors K n) : Space K n :=
  Projectivization.mk K v.val v.property

instance (n : ℕ) : TopologicalSpace (Space K n) :=
  TopologicalSpace.coinduced (quotientMap K n) inferInstance

theorem continuous_quotientMap (n : ℕ) : Continuous (quotientMap K n) :=
  continuous_coinduced_rng

theorem surjective_quotientMap (n : ℕ) : Function.Surjective (quotientMap K n) := by
  intro x
  induction x using Projectivization.ind with
  | h v hv => exact ⟨⟨v, hv⟩, rfl⟩

/-- The affine coordinate axes give named points in every projective space. -/
def coordinateLine (n : ℕ) (i : Fin (n + 1)) : Space K n :=
  quotientMap K n ⟨Pi.single i 1, by
    intro h
    have hi := congrFun h i
    simp at hi⟩

end ConstructionTargets.ProjectiveSpaceTopology
