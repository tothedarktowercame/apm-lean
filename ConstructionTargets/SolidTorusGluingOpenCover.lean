import Mathlib

/-!
# Open cover of two solid tori glued along their boundaries

This file constructs the quotient-side open cover needed before applying the
production Mayer--Vietoris sequence.  It does not assume that the quotient map
is open: openness is proved from saturated open preimages and the coinduced
quotient topology.
-/

open Set Topology
open scoped ContinuousMap

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

/-- Radially move a band point toward radius one. -/
def annularRadialVector (s : unitInterval) (z : annularBand) : Plane :=
  ((1 - (s : ℝ)) + (s : ℝ) / ‖z.1.2.1‖) • z.1.2.1

theorem annular_norm_pos (z : annularBand) : 0 < ‖z.1.2.1‖ := by
  have hz : (1 / 2 : ℝ) < ‖z.1.2.1‖ := z.2
  linarith

theorem annularRadialVector_norm (s : unitInterval) (z : annularBand) :
    ‖annularRadialVector s z‖ =
      (1 - (s : ℝ)) * ‖z.1.2.1‖ + (s : ℝ) := by
  have hr := annular_norm_pos z
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have hscale : 0 ≤ (1 - (s : ℝ)) + (s : ℝ) / ‖z.1.2.1‖ :=
    add_nonneg (sub_nonneg.mpr hs1) (div_nonneg hs0 hr.le)
  rw [annularRadialVector, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hscale]
  field_simp

theorem annularRadialVector_mem_disk (s : unitInterval) (z : annularBand) :
    annularRadialVector s z ∈ Metric.closedBall (0 : Plane) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, annularRadialVector_norm]
  have hz : ‖z.1.2.1‖ ≤ 1 := by
    simpa only [dist_zero_right] using (Metric.mem_closedBall.mp z.1.2.2)
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  nlinarith

theorem annularRadialVector_norm_gt_half (s : unitInterval) (z : annularBand) :
    (1 / 2 : ℝ) < ‖annularRadialVector s z‖ := by
  rw [annularRadialVector_norm]
  have hz : (1 / 2 : ℝ) < ‖z.1.2.1‖ := z.2
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  by_cases hs : (s : ℝ) = 1
  · rw [hs]
    norm_num
  · have hslt : (s : ℝ) < 1 := lt_of_le_of_ne hs1 hs
    have hp : 0 < (1 - (s : ℝ)) * (‖z.1.2.1‖ - 1 / 2) :=
      mul_pos (sub_pos.mpr hslt) (sub_pos.mpr hz)
    nlinarith

/-- The radial deformation as a self-map of the annular band. -/
def annularRadial (s : unitInterval) (z : annularBand) : annularBand :=
  ⟨(z.1.1, ⟨annularRadialVector s z, annularRadialVector_mem_disk s z⟩),
    annularRadialVector_norm_gt_half s z⟩

theorem continuous_annularRadialVector :
    Continuous (fun p : unitInterval × annularBand ↦
      annularRadialVector p.1 p.2) := by
  have cs : Continuous (fun p : unitInterval × annularBand ↦ (p.1 : ℝ)) := by
    fun_prop
  have cx : Continuous (fun p : unitInterval × annularBand ↦ p.2.1.2.1) := by
    fun_prop
  have cn : Continuous (fun p : unitInterval × annularBand ↦ ‖p.2.1.2.1‖) :=
    continuous_norm.comp cx
  have cd : Continuous (fun p : unitInterval × annularBand ↦
      (p.1 : ℝ) / ‖p.2.1.2.1‖) :=
    cs.div₀ cn (fun p ↦ ne_of_gt (annular_norm_pos p.2))
  exact ((continuous_const.sub cs).add cd).smul cx

@[simp] theorem annularRadial_zero (z : annularBand) :
    annularRadial 0 z = z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp [annularRadial, annularRadialVector]

/-- At time one the deformation has reached the literal boundary torus. -/
def annularProjection (z : annularBand) : BoundaryTorus :=
  ⟨z.1.1, ⟨annularRadialVector 1 z, by
    rw [Metric.mem_sphere, dist_zero_right, annularRadialVector_norm]
    norm_num⟩⟩

@[simp] theorem annularRadial_one (z : annularBand) :
    annularRadial 1 z = ⟨boundaryInclusion (annularProjection z),
      boundaryInclusion_mem_annularBand (annularProjection z)⟩ := by
  rfl

@[simp] theorem annularProjection_boundary (z : BoundaryTorus) :
    annularProjection ⟨boundaryInclusion z, boundaryInclusion_mem_annularBand z⟩ = z := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp [annularProjection, annularRadialVector, boundaryInclusion,
      Metric.mem_sphere, dist_zero_right, z.2.2]

theorem continuous_annularRadial :
    Continuous (fun p : unitInterval × annularBand ↦ annularRadial p.1 p.2) := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun p : unitInterval × annularBand ↦ p.2.1.1) := by
    fun_prop
  apply hc.prodMk
  apply Continuous.subtype_mk
  exact continuous_annularRadialVector

theorem continuous_annularProjection : Continuous annularProjection := by
  apply (continuous_fst.comp continuous_subtype_val).prodMk
  apply Continuous.subtype_mk
  exact continuous_annularRadialVector.comp
    (continuous_const.prodMk continuous_id)

def annularProjectionMap : C(annularBand, annularBand) :=
  ⟨annularRadial 1, continuous_annularRadial.comp
    (continuous_const.prodMk continuous_id)⟩

def boundaryToBandMap : C(BoundaryTorus, annularBand) :=
  ⟨fun z ↦ ⟨boundaryInclusion z, boundaryInclusion_mem_annularBand z⟩,
    continuous_boundaryInclusion.subtype_mk _⟩

def bandToBoundaryMap : C(annularBand, BoundaryTorus) :=
  ⟨annularProjection, continuous_annularProjection⟩

def annularBandHomotopy : ContinuousMap.Homotopy
    (ContinuousMap.id annularBand) annularProjectionMap where
  toFun p := annularRadial p.1 p.2
  continuous_toFun := continuous_annularRadial
  map_zero_left := annularRadial_zero
  map_one_left _ := rfl

theorem boundaryToBand_comp_bandToBoundary :
    boundaryToBandMap.comp bandToBoundaryMap = annularProjectionMap := by
  apply ContinuousMap.ext
  intro z
  exact annularRadial_one z

theorem bandToBoundary_comp_boundaryToBand :
    bandToBoundaryMap.comp boundaryToBandMap = ContinuousMap.id BoundaryTorus := by
  apply ContinuousMap.ext
  intro z
  exact annularProjection_boundary z

def annularBandHomotopyEquiv : annularBand ≃ₕ BoundaryTorus where
  toFun := bandToBoundaryMap
  invFun := boundaryToBandMap
  left_inv := by
    rw [boundaryToBand_comp_bandToBoundary]
    exact ⟨annularBandHomotopy.symm⟩
  right_inv := by rw [bandToBoundary_comp_boundaryToBand]

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
