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

private lemma apm_t96j06_single_two_ne :
    (Pi.single 2 1 : Fin 3 → ℝ) ≠ 0 := by
  intro h
  have h2 := congrFun h 2
  simpa using h2

def apm_t96j06_offLinePoint : apm_t96j06_RP2 :=
  Projectivization.mk ℝ (Pi.single 2 1) apm_t96j06_single_two_ne

/-- The standard projective line is a proper subset of the projective plane. -/
lemma apm_t96j06_offLinePoint_not_mem :
    apm_t96j06_offLinePoint ∉ apm_t96j06_RP1InRP2 := by
  change Projectivization.mk ℝ (Pi.single 2 1) apm_t96j06_single_two_ne ∉
    apm_t96j06_coordinatePlane.projectivization
  rw [apm_t96j06_coordinatePlane.mk_mem_projectivization_iff
    apm_t96j06_single_two_ne]
  change (Pi.single 2 1 : Fin 3 → ℝ) 2 ≠ 0
  simp

lemma apm_t96j06_ProductSubspace_ne_univ :
    apm_t96j06_ProductSubspace ≠ Set.univ := by
  intro h
  have hp : (apm_t96j06_offLinePoint, apm_t96j06_coordinatePoint) ∈
      apm_t96j06_ProductSubspace := by simpa [h]
  exact apm_t96j06_offLinePoint_not_mem hp.1

/-- Membership of a pair of projective representatives in the embedded
product reduces exactly to the two coordinate-plane equations. This exposes
the concrete codimension-two incidence condition needed by any future
intersection calculation. -/
lemma apm_t96j06_mk_pair_mem_ProductSubspace_iff
    (u v : Fin 3 → ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    (Projectivization.mk ℝ u hu, Projectivization.mk ℝ v hv) ∈
        apm_t96j06_ProductSubspace ↔
      u 2 = 0 ∧ v 2 = 0 := by
  change
    Projectivization.mk ℝ u hu ∈ apm_t96j06_coordinatePlane.projectivization ∧
      Projectivization.mk ℝ v hv ∈ apm_t96j06_coordinatePlane.projectivization ↔
      u 2 = 0 ∧ v 2 = 0
  rw [apm_t96j06_coordinatePlane.mk_mem_projectivization_iff hu,
    apm_t96j06_coordinatePlane.mk_mem_projectivization_iff hv]
  rfl

/-- Why this unblocks `apm_t96j06`: this is the precise mod-two intersection
bridge absent from Mathlib.  The product of the two standard projective lines
has odd self-intersection in `ℝP² × ℝP²`, whereas the intrinsic boundary of a
compact embedded three-manifold has zero intersection with every closed
complementary cycle; hence that boundary cannot be the displayed product. -/
theorem apm_t96J06_bridge_1
    (W : Set apm_t96j06_Ambient) (hW : IsCompact W)
    (charts : ChartedSpace (EuclideanHalfSpace 3) W) :
    let _ := charts
    IsManifold (𝓡∂ 3) ⊤ W →
      Subtype.val '' ((𝓡∂ 3).boundary W) ≠
        apm_t96j06_ProductSubspace := by
  sorry

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

  Closer hop 2 constructs `apm_t96j06_offLinePoint` and proves the coordinate
  projective line, and consequently `apm_t96j06_ProductSubspace`, is proper.
  This further certifies the intended embedded geometry but does not provide
  its mod-two fundamental class or self-intersection pairing.

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

  Closer hop 3 compiles
  `apm_t96j06_mk_pair_mem_ProductSubspace_iff`, which characterizes an
  arbitrary pair of nonzero projective representatives as lying in the
  embedded product exactly when both third coordinates vanish. This exposes
  the actual codimension-two incidence equations required by a future
  transverse self-intersection calculation and goes beyond the two special
  witnesses from earlier hops. Renewed searches found no theorem promoting
  these incidence equations to a mod-two intersection number, nor any
  replacement through completed bordism groups. The invariant bridge remains
  open and the frozen statement is unchanged.
  -/
  sorry
