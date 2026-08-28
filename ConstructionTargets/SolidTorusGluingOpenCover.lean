import Mathlib

/-!
# Open cover of two solid tori glued along their boundaries

This file constructs the quotient-side open cover needed before applying the
production Mayer--Vietoris sequence.  It does not assume that the quotient map
is open: openness is proved from saturated open preimages and the coinduced
quotient topology.
-/

open Set Topology

noncomputable section

namespace ConstructionTargets.SolidTorusGluingOpenCover

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Disk := Metric.closedBall (0 : Plane) 1
abbrev BoundaryCircle := Metric.sphere (0 : Plane) 1
abbrev SolidTorus := Circle × Disk
abbrev BoundaryTorus := Circle × BoundaryCircle

def boundaryInclusion : BoundaryTorus → SolidTorus :=
  fun z ↦ (z.1, ⟨z.2.1, le_of_eq z.2.2⟩)

theorem continuous_boundaryInclusion : Continuous boundaryInclusion :=
  continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

/-- The outer radial collar, open relative to the closed disk. -/
def annularBand : Set SolidTorus := {z | (1 / 2 : ℝ) < ‖z.2.1‖}

theorem annularBand_isOpen : IsOpen annularBand := by
  exact ((continuous_norm.comp
    (continuous_subtype_val.comp continuous_snd)).isOpen_preimage _ isOpen_Ioi)

theorem boundaryInclusion_mem_annularBand (z : BoundaryTorus) :
    boundaryInclusion z ∈ annularBand := by
  have hz : ‖z.2.1‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using z.2.2
  simp [annularBand, boundaryInclusion, hz]
  norm_num

inductive BoundaryGlueRel (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    Sum SolidTorus SolidTorus → Sum SolidTorus SolidTorus → Prop
  | glue (z : BoundaryTorus) :
      BoundaryGlueRel h (Sum.inl (boundaryInclusion z))
        (Sum.inr (boundaryInclusion (h z)))

abbrev Gluing (h : BoundaryTorus ≃ₜ BoundaryTorus) :=
  Quotient (Relation.EqvGen.setoid (BoundaryGlueRel h))

noncomputable instance (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    TopologicalSpace (Gluing h) :=
  TopologicalSpace.coinduced
    (fun x : Sum SolidTorus SolidTorus ↦ Quotient.mk _ x) inferInstance

def quotientMap (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    Sum SolidTorus SolidTorus → Gluing h := fun x ↦ Quotient.mk _ x

theorem quotientMap_surjective (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    Function.Surjective (quotientMap h) := by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩

theorem quotientMap_isQuotientMap (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    IsQuotientMap (quotientMap h) := ⟨quotientMap_surjective h, rfl⟩

def leftPreimage : Set (Sum SolidTorus SolidTorus)
  | .inl _ => True
  | .inr y => y ∈ annularBand

def rightPreimage : Set (Sum SolidTorus SolidTorus)
  | .inl x => x ∈ annularBand
  | .inr _ => True

theorem leftPreimage_isOpen : IsOpen leftPreimage := by
  rw [isOpen_sum_iff]
  exact ⟨isOpen_univ, annularBand_isOpen⟩

theorem rightPreimage_isOpen : IsOpen rightPreimage := by
  rw [isOpen_sum_iff]
  exact ⟨annularBand_isOpen, isOpen_univ⟩

theorem leftPreimage_respects (h : BoundaryTorus ≃ₜ BoundaryTorus) {x y}
    (hxy : Relation.EqvGen (BoundaryGlueRel h) x y) :
    x ∈ leftPreimage ↔ y ∈ leftPreimage := by
  induction hxy with
  | rel a b hab =>
      cases hab with
      | glue z =>
          exact (iff_true_intro (boundaryInclusion_mem_annularBand (h z))).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem rightPreimage_respects (h : BoundaryTorus ≃ₜ BoundaryTorus) {x y}
    (hxy : Relation.EqvGen (BoundaryGlueRel h) x y) :
    x ∈ rightPreimage ↔ y ∈ rightPreimage := by
  induction hxy with
  | rel a b hab =>
      cases hab with
      | glue z => exact iff_true_intro (boundaryInclusion_mem_annularBand z)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def leftOpen (h : BoundaryTorus ≃ₜ BoundaryTorus) : Set (Gluing h) :=
  quotientMap h '' leftPreimage

def rightOpen (h : BoundaryTorus ≃ₜ BoundaryTorus) : Set (Gluing h) :=
  quotientMap h '' rightPreimage

theorem quotientMap_preimage_leftOpen (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    quotientMap h ⁻¹' leftOpen h = leftPreimage := by
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    exact (leftPreimage_respects h (Quotient.exact heq)).mp hy
  · exact fun hx ↦ ⟨x, hx, rfl⟩

theorem quotientMap_preimage_rightOpen (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    quotientMap h ⁻¹' rightOpen h = rightPreimage := by
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    exact (rightPreimage_respects h (Quotient.exact heq)).mp hy
  · exact fun hx ↦ ⟨x, hx, rfl⟩

theorem leftOpen_isOpen (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    IsOpen (leftOpen h) := by
  rw [← (quotientMap_isQuotientMap h).isOpen_preimage,
    quotientMap_preimage_leftOpen]
  exact leftPreimage_isOpen

theorem rightOpen_isOpen (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    IsOpen (rightOpen h) := by
  rw [← (quotientMap_isQuotientMap h).isOpen_preimage,
    quotientMap_preimage_rightOpen]
  exact rightPreimage_isOpen

theorem leftOpen_union_rightOpen (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    leftOpen h ∪ rightOpen h = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨x⟩
  cases x with
  | inl x => exact Or.inl ⟨Sum.inl x, trivial, rfl⟩
  | inr x => exact Or.inr ⟨Sum.inr x, trivial, rfl⟩

def bothBandPreimage : Set (Sum SolidTorus SolidTorus)
  | .inl x => x ∈ annularBand
  | .inr x => x ∈ annularBand

theorem bothBandPreimage_isOpen : IsOpen bothBandPreimage := by
  rw [isOpen_sum_iff]
  exact ⟨annularBand_isOpen, annularBand_isOpen⟩

theorem quotientMap_preimage_inter_open (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    quotientMap h ⁻¹' (leftOpen h ∩ rightOpen h) = bothBandPreimage := by
  rw [preimage_inter, quotientMap_preimage_leftOpen,
    quotientMap_preimage_rightOpen]
  ext x
  cases x with
  | inl x =>
      change (True ∧ x ∈ annularBand) ↔ x ∈ annularBand
      simp
  | inr x =>
      change (x ∈ annularBand ∧ True) ↔ x ∈ annularBand
      simp

def leftPieceQuotientMap (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    (quotientMap h ⁻¹' leftOpen h) → leftOpen h :=
  (leftOpen h).restrictPreimage (quotientMap h)

def rightPieceQuotientMap (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    (quotientMap h ⁻¹' rightOpen h) → rightOpen h :=
  (rightOpen h).restrictPreimage (quotientMap h)

def intersectionPieceQuotientMap (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    (quotientMap h ⁻¹' (leftOpen h ∩ rightOpen h)) →
      ↥(leftOpen h ∩ rightOpen h) :=
  (leftOpen h ∩ rightOpen h).restrictPreimage (quotientMap h)

theorem leftPieceQuotientMap_isQuotientMap
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    IsQuotientMap (leftPieceQuotientMap h) :=
  (quotientMap_isQuotientMap h).restrictPreimage_isOpen (leftOpen_isOpen h)

theorem rightPieceQuotientMap_isQuotientMap
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    IsQuotientMap (rightPieceQuotientMap h) :=
  (quotientMap_isQuotientMap h).restrictPreimage_isOpen (rightOpen_isOpen h)

theorem intersectionPieceQuotientMap_isQuotientMap
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    IsQuotientMap (intersectionPieceQuotientMap h) :=
  (quotientMap_isQuotientMap h).restrictPreimage_isOpen
    ((leftOpen_isOpen h).inter (rightOpen_isOpen h))

#print axioms annularBand_isOpen
#print axioms leftPreimage_respects
#print axioms quotientMap_preimage_inter_open
#print axioms intersectionPieceQuotientMap_isQuotientMap

end ConstructionTargets.SolidTorusGluingOpenCover
