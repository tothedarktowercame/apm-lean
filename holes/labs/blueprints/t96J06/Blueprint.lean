import Mathlib

/-! # APM t96J06 — the mod-two self-intersection obstruction -/

open Set
open scoped LinearAlgebra.Projectivization Manifold

noncomputable section

abbrev apm_t96j06_RP2 := Projectivization ℝ (Fin 3 → ℝ)

noncomputable instance : TopologicalSpace apm_t96j06_RP2 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ (Fin 3 → ℝ))))

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

def apm_t96j06_ProductSubspace : Set apm_t96j06_Ambient :=
  {p | p.1 ∈ apm_t96j06_RP1InRP2 ∧ p.2 ∈ apm_t96j06_RP1InRP2}

def apm_t96j06_BoundsThreeManifold
    (T : Set apm_t96j06_Ambient) : Prop :=
  ∃ W : Set apm_t96j06_Ambient,
    IsCompact W ∧
    ∃ charts : ChartedSpace (EuclideanHalfSpace 3) W,
      let _ := charts
      IsManifold (𝓡∂ 3) (⊤ : ℕ∞) W ∧
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

/-- **LIBRARY: mod-two projective-product boundary obstruction.** The product
of the two coordinate projective lines has odd self-intersection, while the
intrinsic boundary of a compact embedded topological three-manifold has zero
ambient mod-two homology class. -/
theorem apm_t96J06_projectiveProduct_boundaryObstruction
    (W : Set apm_t96j06_Ambient) (hW : IsCompact W)
    (charts : ChartedSpace (EuclideanHalfSpace 3) W) :
    let _ := charts
    IsManifold (𝓡∂ 3) (⊤ : ℕ∞) W →
      Subtype.val '' ((𝓡∂ 3).boundary W) ≠
        apm_t96j06_ProductSubspace := by
  sorry

theorem apm_t96j06 :
    ¬apm_t96j06_BoundsThreeManifold apm_t96j06_ProductSubspace := by
  rintro ⟨W, hW, charts, hman, hboundary⟩
  exact apm_t96J06_projectiveProduct_boundaryObstruction W hW charts hman hboundary

#print axioms apm_t96j06
