import Mathlib

/-!
# APM t96J06 — the mod-two self-intersection obstruction

## Statement repairs

None.

## Encoding note

`ℝP²` is Mathlib's actual real projectivization. Its standard `ℝP¹` is the
projectivization of the coordinate plane `x₂ = 0`, so both the ambient product
and the embedded product are concrete. To bound means to be the intrinsic
boundary of an actual compact three-manifold-with-boundary embedded as a
subset of the ambient product. The mod-two self-intersection obstruction is
therefore proof content rather than a hypothesis.
-/

open Set
open scoped LinearAlgebra.Projectivization Manifold

noncomputable section

abbrev apm_t96j06_RP2 := Projectivization ℝ (Fin 3 → ℝ)

noncomputable instance : TopologicalSpace apm_t96j06_RP2 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ (Fin 3 → ℝ))))

/-- The coordinate plane in `ℝ³` whose projectivization is the standard
embedded `ℝP¹ ⊂ ℝP²`. -/
def apm_t96j06_coordinatePlane : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {v | v 2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change x 2 = 0 at hx
    change y 2 = 0 at hy
    change x 2 + y 2 = 0
    rw [hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change x 2 = 0 at hx
    change c * x 2 = 0
    rw [hx, mul_zero]

def apm_t96j06_RP1InRP2 : Set apm_t96j06_RP2 :=
  apm_t96j06_coordinatePlane.projectivization

abbrev apm_t96j06_Ambient := apm_t96j06_RP2 × apm_t96j06_RP2

/-- The actual product `ℝP¹ × ℝP¹` inside `ℝP² × ℝP²`. -/
def apm_t96j06_ProductSubspace : Set apm_t96j06_Ambient :=
  {p | p.1 ∈ apm_t96j06_RP1InRP2 ∧ p.2 ∈ apm_t96j06_RP1InRP2}

/-- A compact embedded three-manifold in the ambient product whose intrinsic
manifold boundary is exactly `T`. -/
def apm_t96j06_BoundsThreeManifold
    (T : Set apm_t96j06_Ambient) : Prop :=
  ∃ W : Set apm_t96j06_Ambient,
    IsCompact W ∧
    ∃ charts : ChartedSpace (EuclideanHalfSpace 3) W,
      let _ := charts
      IsManifold (𝓡∂ 3) ⊤ W ∧
      Subtype.val '' ((𝓡∂ 3).boundary W) = T

private lemma apm_t96j06_single_zero_ne :
    (Pi.single 0 1 : Fin 3 → ℝ) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simpa using h0

def apm_t96j06_coordinatePoint : apm_t96j06_RP2 :=
  Projectivization.mk ℝ (Pi.single 0 1) apm_t96j06_single_zero_ne

lemma apm_t96j06_coordinatePoint_mem :
    apm_t96j06_coordinatePoint ∈ apm_t96j06_RP1InRP2 := by
  change Projectivization.mk ℝ (Pi.single 0 1) apm_t96j06_single_zero_ne ∈
    apm_t96j06_coordinatePlane.projectivization
  apply (apm_t96j06_coordinatePlane.mk_mem_projectivization_iff
    apm_t96j06_single_zero_ne).2
  change (Pi.single 0 1 : Fin 3 → ℝ) 2 = 0
  simp

/-- The embedded product is an actual nonempty projective torus, so the
non-bounding statement is not a vacuous boundary-equality obstruction. -/
lemma apm_t96j06_ProductSubspace_nonempty :
    apm_t96j06_ProductSubspace.Nonempty := by
  exact ⟨(apm_t96j06_coordinatePoint, apm_t96j06_coordinatePoint),
    apm_t96j06_coordinatePoint_mem, apm_t96j06_coordinatePoint_mem⟩

theorem apm_t96j06 :
    ¬apm_t96j06_BoundsThreeManifold apm_t96j06_ProductSubspace := by
  /-
  PARTIAL boundary (closer hop 1).

  New progress: `apm_t96j06_coordinatePoint` constructs an explicit point of
  the coordinate `ℝP¹`, with membership proved through Mathlib's
  `Submodule.mk_mem_projectivization_iff`.
  `apm_t96j06_ProductSubspace_nonempty` then certifies that the embedded
  product is genuinely nonempty.  This removes projectivization
  representative bookkeeping and rules out any vacuous proof through an empty
  alleged boundary.

  The remaining proof is the mod-two self-intersection obstruction.  It needs
  (1) a mod-two fundamental class for the embedded `ℝP¹ × ℝP¹`, (2) the fact
  that an intrinsic manifold boundary maps to zero in ambient homology, and
  (3) computation of the product class's self-intersection as one.  Searches
  of `LEMMA-INDEX.md`, `ConstructionTargets/`, all closed artifacts, Mathlib's
  projectivization, singular-homology, manifold-boundary, intersection, and
  bordism sources, and git history found none of these bridges.  Mathlib's
  `Geometry/Manifold/Bordism.lean` explicitly describes bordisms, bordism
  groups, and their homology theory as future work; it currently only develops
  preliminary singular-manifold machinery.  No corpus artifact computes
  `H*(ℝP²; ZMod 2)`, a Künneth product, or the projective-line intersection
  pairing.  Consequently the live boundary is a substantial new mod-two
  homology/intersection-theory development, not a remaining coordinate lemma.
  -/
  sorry
