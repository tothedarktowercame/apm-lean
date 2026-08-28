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

@[simp] theorem annularRadial_boundary (s : unitInterval) (z : BoundaryTorus) :
    annularRadial s
      ⟨boundaryInclusion z, boundaryInclusion_mem_annularBand z⟩ =
        ⟨boundaryInclusion z, boundaryInclusion_mem_annularBand z⟩ := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    have hz : ‖z.2.1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using z.2.2
    simp [annularRadial, annularRadialVector, boundaryInclusion, hz]

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

def leftPieceSourceHomeomorph (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    leftPreimage ≃ₜ quotientMap h ⁻¹' leftOpen h :=
  Homeomorph.setCongr (quotientMap_preimage_leftOpen h).symm

def rightPieceSourceHomeomorph (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    rightPreimage ≃ₜ quotientMap h ⁻¹' rightOpen h :=
  Homeomorph.setCongr (quotientMap_preimage_rightOpen h).symm

def intersectionPieceSourceHomeomorph (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    bothBandPreimage ≃ₜ quotientMap h ⁻¹' (leftOpen h ∩ rightOpen h) :=
  Homeomorph.setCongr (quotientMap_preimage_inter_open h).symm

def namedLeftPieceQuotientMap (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    leftPreimage → leftOpen h :=
  leftPieceQuotientMap h ∘ leftPieceSourceHomeomorph h

def namedRightPieceQuotientMap (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    rightPreimage → rightOpen h :=
  rightPieceQuotientMap h ∘ rightPieceSourceHomeomorph h

def namedIntersectionPieceQuotientMap (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    bothBandPreimage → ↥(leftOpen h ∩ rightOpen h) :=
  intersectionPieceQuotientMap h ∘ intersectionPieceSourceHomeomorph h

theorem namedLeftPieceQuotientMap_isQuotientMap
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    IsQuotientMap (namedLeftPieceQuotientMap h) :=
  (leftPieceQuotientMap_isQuotientMap h).comp
    (leftPieceSourceHomeomorph h).isQuotientMap

theorem namedRightPieceQuotientMap_isQuotientMap
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    IsQuotientMap (namedRightPieceQuotientMap h) :=
  (rightPieceQuotientMap_isQuotientMap h).comp
    (rightPieceSourceHomeomorph h).isQuotientMap

theorem namedIntersectionPieceQuotientMap_isQuotientMap
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    IsQuotientMap (namedIntersectionPieceQuotientMap h) :=
  (intersectionPieceQuotientMap_isQuotientMap h).comp
    (intersectionPieceSourceHomeomorph h).isQuotientMap

/-! ## Explicit source decompositions and branchwise homotopies -/

def subtypeSumHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (p : X ⊕ Y → Prop)
    (hleft : IsOpen {x | p (Sum.inl x)})
    (hright : IsOpen {y | p (Sum.inr y)}) :
    {z // p z} ≃ₜ {x // p (Sum.inl x)} ⊕ {y // p (Sum.inr y)} where
  toEquiv := Equiv.subtypeSum
  continuous_toFun := by
    rw [continuous_def]
    intro u hu
    have hl := hu.preimage continuous_inl
    have hr := hu.preimage continuous_inr
    have hl' := hleft.isOpenMap_subtype_val _ hl
    have hr' := hright.isOpenMap_subtype_val _ hr
    have hs : IsOpen
        (Sum.inl '' (Subtype.val '' (Sum.inl ⁻¹' u)) ∪
          Sum.inr '' (Subtype.val '' (Sum.inr ⁻¹' u))) :=
      (isOpenMap_inl _ hl').union (isOpenMap_inr _ hr')
    change IsOpen (Equiv.subtypeSum ⁻¹' u)
    rw [show Equiv.subtypeSum ⁻¹' u =
        Subtype.val ⁻¹'
          (Sum.inl '' (Subtype.val '' (Sum.inl ⁻¹' u)) ∪
            Sum.inr '' (Subtype.val '' (Sum.inr ⁻¹' u))) by
      ext z
      rcases z with ⟨x | y, hz⟩ <;>
        simp only [Equiv.subtypeSum, Equiv.coe_fn_mk, Set.mem_preimage,
          Set.mem_union, Set.mem_image] <;> aesop]
    exact hs.preimage continuous_subtype_val
  continuous_invFun := by
    rw [continuous_sum_dom]
    constructor <;> apply Continuous.subtype_mk
    · exact continuous_inl.comp continuous_subtype_val
    · exact continuous_inr.comp continuous_subtype_val

def leftPreimageSumHomeomorph :
    leftPreimage ≃ₜ SolidTorus ⊕ annularBand :=
  (subtypeSumHomeomorph leftPreimage isOpen_univ annularBand_isOpen).trans <|
    Homeomorph.sumCongr
      ((Homeomorph.setCongr (by ext; exact iff_true_intro trivial)).trans
        (Homeomorph.Set.univ _))
      (Homeomorph.setCongr (by ext; rfl))

def rightPreimageSumHomeomorph :
    rightPreimage ≃ₜ annularBand ⊕ SolidTorus :=
  (subtypeSumHomeomorph rightPreimage annularBand_isOpen isOpen_univ).trans <|
    Homeomorph.sumCongr
      (Homeomorph.setCongr (by ext; rfl))
      ((Homeomorph.setCongr (by ext; exact iff_true_intro trivial)).trans
        (Homeomorph.Set.univ _))

def bothBandPreimageSumHomeomorph :
    bothBandPreimage ≃ₜ annularBand ⊕ annularBand :=
  (subtypeSumHomeomorph bothBandPreimage annularBand_isOpen
      annularBand_isOpen).trans <|
    Homeomorph.sumCongr (Homeomorph.setCongr (by ext; rfl))
      (Homeomorph.setCongr (by ext; rfl))

def fixedSolidTorusBranch : unitInterval × SolidTorus → SolidTorus := Prod.snd

def radialBandBranch : unitInterval × annularBand → annularBand :=
  fun p ↦ annularRadial p.1 p.2

theorem continuous_radialBandBranch : Continuous radialBandBranch :=
  continuous_annularRadial

def leftSplitBranchHomotopy :
    (unitInterval × SolidTorus) ⊕ (unitInterval × annularBand) →
      SolidTorus ⊕ annularBand :=
  Sum.elim (Sum.inl ∘ fixedSolidTorusBranch)
    (Sum.inr ∘ radialBandBranch)

def rightSplitBranchHomotopy :
    (unitInterval × annularBand) ⊕ (unitInterval × SolidTorus) →
      annularBand ⊕ SolidTorus :=
  Sum.elim (Sum.inl ∘ radialBandBranch)
    (Sum.inr ∘ fixedSolidTorusBranch)

def intersectionSplitBranchHomotopy :
    (unitInterval × annularBand) ⊕ (unitInterval × annularBand) →
      annularBand ⊕ annularBand :=
  Sum.elim (Sum.inl ∘ radialBandBranch) (Sum.inr ∘ radialBandBranch)

theorem continuous_leftSplitBranchHomotopy :
    Continuous leftSplitBranchHomotopy := by
  apply Continuous.sumElim
  · exact continuous_inl.comp continuous_snd
  · exact continuous_inr.comp continuous_radialBandBranch

theorem continuous_rightSplitBranchHomotopy :
    Continuous rightSplitBranchHomotopy := by
  apply Continuous.sumElim
  · exact continuous_inl.comp continuous_radialBandBranch
  · exact continuous_inr.comp continuous_snd

theorem continuous_intersectionSplitBranchHomotopy :
    Continuous intersectionSplitBranchHomotopy := by
  apply Continuous.sumElim <;>
    first | exact continuous_inl.comp continuous_radialBandBranch
          | exact continuous_inr.comp continuous_radialBandBranch

def leftPieceSourceHomotopy : unitInterval × leftPreimage → leftPreimage :=
  leftPreimageSumHomeomorph.symm ∘ leftSplitBranchHomotopy ∘
    Homeomorph.prodSumDistrib ∘ Prod.map id leftPreimageSumHomeomorph

def rightPieceSourceHomotopy : unitInterval × rightPreimage → rightPreimage :=
  rightPreimageSumHomeomorph.symm ∘ rightSplitBranchHomotopy ∘
    Homeomorph.prodSumDistrib ∘ Prod.map id rightPreimageSumHomeomorph

def intersectionPieceSourceHomotopy :
    unitInterval × bothBandPreimage → bothBandPreimage :=
  bothBandPreimageSumHomeomorph.symm ∘ intersectionSplitBranchHomotopy ∘
    Homeomorph.prodSumDistrib ∘ Prod.map id bothBandPreimageSumHomeomorph

theorem continuous_leftPieceSourceHomotopy :
    Continuous leftPieceSourceHomotopy :=
  leftPreimageSumHomeomorph.symm.continuous.comp <|
    continuous_leftSplitBranchHomotopy.comp <|
      Homeomorph.prodSumDistrib.continuous.comp <|
        continuous_id.prodMap leftPreimageSumHomeomorph.continuous

theorem continuous_rightPieceSourceHomotopy :
    Continuous rightPieceSourceHomotopy :=
  rightPreimageSumHomeomorph.symm.continuous.comp <|
    continuous_rightSplitBranchHomotopy.comp <|
      Homeomorph.prodSumDistrib.continuous.comp <|
        continuous_id.prodMap rightPreimageSumHomeomorph.continuous

theorem continuous_intersectionPieceSourceHomotopy :
    Continuous intersectionPieceSourceHomotopy :=
  bothBandPreimageSumHomeomorph.symm.continuous.comp <|
    continuous_intersectionSplitBranchHomotopy.comp <|
      Homeomorph.prodSumDistrib.continuous.comp <|
        continuous_id.prodMap bothBandPreimageSumHomeomorph.continuous

@[simp] theorem leftPieceSourceHomotopy_inl (s : unitInterval) (x : SolidTorus) :
    (leftPieceSourceHomotopy (s, ⟨Sum.inl x, trivial⟩)).1 = Sum.inl x := rfl

@[simp] theorem leftPieceSourceHomotopy_inr (s : unitInterval) (x : annularBand) :
    (leftPieceSourceHomotopy (s, ⟨Sum.inr x.1, x.2⟩)).1 =
      Sum.inr (annularRadial s x).1 := rfl

@[simp] theorem rightPieceSourceHomotopy_inl (s : unitInterval) (x : annularBand) :
    (rightPieceSourceHomotopy (s, ⟨Sum.inl x.1, x.2⟩)).1 =
      Sum.inl (annularRadial s x).1 := rfl

@[simp] theorem rightPieceSourceHomotopy_inr (s : unitInterval) (x : SolidTorus) :
    (rightPieceSourceHomotopy (s, ⟨Sum.inr x, trivial⟩)).1 = Sum.inr x := rfl

@[simp] theorem intersectionPieceSourceHomotopy_inl
    (s : unitInterval) (x : annularBand) :
    (intersectionPieceSourceHomotopy (s, ⟨Sum.inl x.1, x.2⟩)).1 =
      Sum.inl (annularRadial s x).1 := rfl

@[simp] theorem intersectionPieceSourceHomotopy_inr
    (s : unitInterval) (x : annularBand) :
    (intersectionPieceSourceHomotopy (s, ⟨Sum.inr x.1, x.2⟩)).1 =
      Sum.inr (annularRadial s x).1 := rfl

@[simp] theorem leftPieceSourceHomotopy_zero (x : leftPreimage) :
    leftPieceSourceHomotopy (0, x) = x := by
  rcases x with ⟨x, hx⟩
  cases x with
  | inl x => rfl
  | inr x =>
      apply Subtype.ext
      simpa only [leftPieceSourceHomotopy_inr] using
        congrArg (fun y : annularBand ↦ Sum.inr y.1)
          (annularRadial_zero ⟨x, hx⟩)

@[simp] theorem rightPieceSourceHomotopy_zero (x : rightPreimage) :
    rightPieceSourceHomotopy (0, x) = x := by
  rcases x with ⟨x, hx⟩
  cases x with
  | inl x =>
      apply Subtype.ext
      simpa only [rightPieceSourceHomotopy_inl] using
        congrArg (fun y : annularBand ↦ Sum.inl y.1)
          (annularRadial_zero ⟨x, hx⟩)
  | inr x => rfl

@[simp] theorem intersectionPieceSourceHomotopy_zero (x : bothBandPreimage) :
    intersectionPieceSourceHomotopy (0, x) = x := by
  rcases x with ⟨x, hx⟩
  cases x with
  | inl x =>
      apply Subtype.ext
      simpa only [intersectionPieceSourceHomotopy_inl] using
        congrArg (fun y : annularBand ↦ Sum.inl y.1)
          (annularRadial_zero ⟨x, hx⟩)
  | inr x =>
      apply Subtype.ext
      simpa only [intersectionPieceSourceHomotopy_inr] using
        congrArg (fun y : annularBand ↦ Sum.inr y.1)
          (annularRadial_zero ⟨x, hx⟩)

theorem leftPieceSourceHomotopy_fixes_inr_boundary (s : unitInterval)
    (z : BoundaryTorus) (hz : Sum.inr (boundaryInclusion z) ∈ leftPreimage) :
    leftPieceSourceHomotopy (s, ⟨Sum.inr (boundaryInclusion z), hz⟩) =
      ⟨Sum.inr (boundaryInclusion z), hz⟩ := by
  apply Subtype.ext
  simpa only [leftPieceSourceHomotopy_inr] using
    congrArg (fun y : annularBand ↦ Sum.inr y.1) (annularRadial_boundary s z)

theorem rightPieceSourceHomotopy_fixes_inl_boundary (s : unitInterval)
    (z : BoundaryTorus) (hz : Sum.inl (boundaryInclusion z) ∈ rightPreimage) :
    rightPieceSourceHomotopy (s, ⟨Sum.inl (boundaryInclusion z), hz⟩) =
      ⟨Sum.inl (boundaryInclusion z), hz⟩ := by
  apply Subtype.ext
  simpa only [rightPieceSourceHomotopy_inl] using
    congrArg (fun y : annularBand ↦ Sum.inl y.1) (annularRadial_boundary s z)

theorem intersectionPieceSourceHomotopy_fixes_inl_boundary (s : unitInterval)
    (z : BoundaryTorus) (hz : Sum.inl (boundaryInclusion z) ∈ bothBandPreimage) :
    intersectionPieceSourceHomotopy
      (s, ⟨Sum.inl (boundaryInclusion z), hz⟩) =
        ⟨Sum.inl (boundaryInclusion z), hz⟩ := by
  apply Subtype.ext
  simpa only [intersectionPieceSourceHomotopy_inl] using
    congrArg (fun y : annularBand ↦ Sum.inl y.1) (annularRadial_boundary s z)

theorem intersectionPieceSourceHomotopy_fixes_inr_boundary (s : unitInterval)
    (z : BoundaryTorus) (hz : Sum.inr (boundaryInclusion z) ∈ bothBandPreimage) :
    intersectionPieceSourceHomotopy
      (s, ⟨Sum.inr (boundaryInclusion z), hz⟩) =
        ⟨Sum.inr (boundaryInclusion z), hz⟩ := by
  apply Subtype.ext
  simpa only [intersectionPieceSourceHomotopy_inr] using
    congrArg (fun y : annularBand ↦ Sum.inr y.1) (annularRadial_boundary s z)

theorem leftPieceSourceHomotopy_eq_of_eqv
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (s : unitInterval) {a b}
    (ha : a ∈ leftPreimage) (hb : b ∈ leftPreimage)
    (hab : Relation.EqvGen (BoundaryGlueRel h) a b) :
    quotientMap h (leftPieceSourceHomotopy (s, ⟨a, ha⟩)).1 =
      quotientMap h (leftPieceSourceHomotopy (s, ⟨b, hb⟩)).1 := by
  induction hab with
  | rel a b hab =>
      cases hab with
      | glue z =>
          rw [leftPieceSourceHomotopy_fixes_inr_boundary]
          exact Quotient.sound (Relation.EqvGen.rel _ _ (BoundaryGlueRel.glue z))
  | refl => rfl
  | symm a b _ ih => exact (ih hb ha).symm
  | trans a b c hab hbc ih₁ ih₂ =>
      have hm := (leftPreimage_respects h hab).mp ha
      exact (ih₁ ha hm).trans (ih₂ hm hb)

theorem rightPieceSourceHomotopy_eq_of_eqv
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (s : unitInterval) {a b}
    (ha : a ∈ rightPreimage) (hb : b ∈ rightPreimage)
    (hab : Relation.EqvGen (BoundaryGlueRel h) a b) :
    quotientMap h (rightPieceSourceHomotopy (s, ⟨a, ha⟩)).1 =
      quotientMap h (rightPieceSourceHomotopy (s, ⟨b, hb⟩)).1 := by
  induction hab with
  | rel a b hab =>
      cases hab with
      | glue z =>
          rw [rightPieceSourceHomotopy_fixes_inl_boundary]
          exact Quotient.sound (Relation.EqvGen.rel _ _ (BoundaryGlueRel.glue z))
  | refl => rfl
  | symm a b _ ih => exact (ih hb ha).symm
  | trans a b c hab hbc ih₁ ih₂ =>
      have hm := (rightPreimage_respects h hab).mp ha
      exact (ih₁ ha hm).trans (ih₂ hm hb)

theorem intersectionPieceSourceHomotopy_eq_of_eqv
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (s : unitInterval) {a b}
    (ha : a ∈ bothBandPreimage) (hb : b ∈ bothBandPreimage)
    (hab : Relation.EqvGen (BoundaryGlueRel h) a b) :
    quotientMap h (intersectionPieceSourceHomotopy (s, ⟨a, ha⟩)).1 =
      quotientMap h (intersectionPieceSourceHomotopy (s, ⟨b, hb⟩)).1 := by
  induction hab with
  | rel a b hab =>
      cases hab with
      | glue z =>
          rw [intersectionPieceSourceHomotopy_fixes_inl_boundary,
            intersectionPieceSourceHomotopy_fixes_inr_boundary]
          exact Quotient.sound (Relation.EqvGen.rel _ _ (BoundaryGlueRel.glue z))
  | refl => rfl
  | symm a b _ ih => exact (ih hb ha).symm
  | trans a b c hab hbc ih₁ ih₂ =>
      have hal : a ∈ leftPreimage := by
        cases a with
        | inl => trivial
        | inr => exact ha
      have har : a ∈ rightPreimage := by
        cases a with
        | inl => exact ha
        | inr => trivial
      have hml := (leftPreimage_respects h hab).mp hal
      have hmr := (rightPreimage_respects h hab).mp har
      have hm : b ∈ bothBandPreimage := by
        cases b with
        | inl => exact hmr
        | inr => exact hml
      exact (ih₁ ha hm).trans (ih₂ hm hb)

theorem leftPieceSourceHomotopy_fiber_coherent
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (s : unitInterval)
    {a b : leftPreimage} (hab : namedLeftPieceQuotientMap h a =
      namedLeftPieceQuotientMap h b) :
    namedLeftPieceQuotientMap h (leftPieceSourceHomotopy (s, a)) =
      namedLeftPieceQuotientMap h (leftPieceSourceHomotopy (s, b)) := by
  apply Subtype.ext
  apply leftPieceSourceHomotopy_eq_of_eqv h s a.2 b.2
  exact Quotient.exact (congrArg Subtype.val hab)

theorem rightPieceSourceHomotopy_fiber_coherent
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (s : unitInterval)
    {a b : rightPreimage} (hab : namedRightPieceQuotientMap h a =
      namedRightPieceQuotientMap h b) :
    namedRightPieceQuotientMap h (rightPieceSourceHomotopy (s, a)) =
      namedRightPieceQuotientMap h (rightPieceSourceHomotopy (s, b)) := by
  apply Subtype.ext
  apply rightPieceSourceHomotopy_eq_of_eqv h s a.2 b.2
  exact Quotient.exact (congrArg Subtype.val hab)

theorem intersectionPieceSourceHomotopy_fiber_coherent
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (s : unitInterval)
    {a b : bothBandPreimage} (hab : namedIntersectionPieceQuotientMap h a =
      namedIntersectionPieceQuotientMap h b) :
    namedIntersectionPieceQuotientMap h
        (intersectionPieceSourceHomotopy (s, a)) =
      namedIntersectionPieceQuotientMap h
        (intersectionPieceSourceHomotopy (s, b)) := by
  apply Subtype.ext
  apply intersectionPieceSourceHomotopy_eq_of_eqv h s a.2 b.2
  exact Quotient.exact (congrArg Subtype.val hab)

/-! ## Descent to the quotient pieces -/

noncomputable def leftPieceHomotopyMap (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    unitInterval × leftOpen h → leftOpen h := fun p ↦
  namedLeftPieceQuotientMap h (leftPieceSourceHomotopy
    (p.1, Function.surjInv (namedLeftPieceQuotientMap_isQuotientMap h).surjective p.2))

theorem leftPieceHomotopyMap_pullback (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (p : unitInterval × leftPreimage) :
    leftPieceHomotopyMap h (p.1, namedLeftPieceQuotientMap h p.2) =
      namedLeftPieceQuotientMap h (leftPieceSourceHomotopy p) := by
  apply leftPieceSourceHomotopy_fiber_coherent h p.1
  exact Function.surjInv_eq
    (namedLeftPieceQuotientMap_isQuotientMap h).surjective _

theorem continuous_leftPieceHomotopyMap (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    Continuous (leftPieceHomotopyMap h) := by
  apply (namedLeftPieceQuotientMap_isQuotientMap h).continuous_lift_prod_right
  have hc := (namedLeftPieceQuotientMap_isQuotientMap h).continuous.comp
    continuous_leftPieceSourceHomotopy
  convert hc using 1
  funext p
  exact leftPieceHomotopyMap_pullback h p

noncomputable def rightPieceHomotopyMap (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    unitInterval × rightOpen h → rightOpen h := fun p ↦
  namedRightPieceQuotientMap h (rightPieceSourceHomotopy
    (p.1, Function.surjInv (namedRightPieceQuotientMap_isQuotientMap h).surjective p.2))

theorem rightPieceHomotopyMap_pullback (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (p : unitInterval × rightPreimage) :
    rightPieceHomotopyMap h (p.1, namedRightPieceQuotientMap h p.2) =
      namedRightPieceQuotientMap h (rightPieceSourceHomotopy p) := by
  apply rightPieceSourceHomotopy_fiber_coherent h p.1
  exact Function.surjInv_eq
    (namedRightPieceQuotientMap_isQuotientMap h).surjective _

theorem continuous_rightPieceHomotopyMap (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    Continuous (rightPieceHomotopyMap h) := by
  apply (namedRightPieceQuotientMap_isQuotientMap h).continuous_lift_prod_right
  have hc := (namedRightPieceQuotientMap_isQuotientMap h).continuous.comp
    continuous_rightPieceSourceHomotopy
  convert hc using 1
  funext p
  exact rightPieceHomotopyMap_pullback h p

noncomputable def intersectionPieceHomotopyMap
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    unitInterval × ↥(leftOpen h ∩ rightOpen h) →
      ↥(leftOpen h ∩ rightOpen h) := fun p ↦
  namedIntersectionPieceQuotientMap h (intersectionPieceSourceHomotopy
    (p.1, Function.surjInv
      (namedIntersectionPieceQuotientMap_isQuotientMap h).surjective p.2))

theorem intersectionPieceHomotopyMap_pullback
    (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (p : unitInterval × bothBandPreimage) :
    intersectionPieceHomotopyMap h
        (p.1, namedIntersectionPieceQuotientMap h p.2) =
      namedIntersectionPieceQuotientMap h
        (intersectionPieceSourceHomotopy p) := by
  apply intersectionPieceSourceHomotopy_fiber_coherent h p.1
  exact Function.surjInv_eq
    (namedIntersectionPieceQuotientMap_isQuotientMap h).surjective _

theorem continuous_intersectionPieceHomotopyMap
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    Continuous (intersectionPieceHomotopyMap h) := by
  apply (namedIntersectionPieceQuotientMap_isQuotientMap h).continuous_lift_prod_right
  have hc := (namedIntersectionPieceQuotientMap_isQuotientMap h).continuous.comp
    continuous_intersectionPieceSourceHomotopy
  convert hc using 1
  funext p
  exact intersectionPieceHomotopyMap_pullback h p

@[simp] theorem leftPieceHomotopyMap_zero
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (x : leftOpen h) :
    leftPieceHomotopyMap h (0, x) = x := by
  obtain ⟨y, rfl⟩ := (namedLeftPieceQuotientMap_isQuotientMap h).surjective x
  calc
    _ = namedLeftPieceQuotientMap h (leftPieceSourceHomotopy (0, y)) :=
      leftPieceHomotopyMap_pullback h (0, y)
    _ = _ := congrArg (namedLeftPieceQuotientMap h)
      (leftPieceSourceHomotopy_zero y)

@[simp] theorem rightPieceHomotopyMap_zero
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (x : rightOpen h) :
    rightPieceHomotopyMap h (0, x) = x := by
  obtain ⟨y, rfl⟩ := (namedRightPieceQuotientMap_isQuotientMap h).surjective x
  calc
    _ = namedRightPieceQuotientMap h (rightPieceSourceHomotopy (0, y)) :=
      rightPieceHomotopyMap_pullback h (0, y)
    _ = _ := congrArg (namedRightPieceQuotientMap h)
      (rightPieceSourceHomotopy_zero y)

@[simp] theorem intersectionPieceHomotopyMap_zero
    (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (x : ↥(leftOpen h ∩ rightOpen h)) :
    intersectionPieceHomotopyMap h (0, x) = x := by
  obtain ⟨y, rfl⟩ :=
    (namedIntersectionPieceQuotientMap_isQuotientMap h).surjective x
  calc
    _ = namedIntersectionPieceQuotientMap h
        (intersectionPieceSourceHomotopy (0, y)) :=
      intersectionPieceHomotopyMap_pullback h (0, y)
    _ = _ := congrArg (namedIntersectionPieceQuotientMap h)
      (intersectionPieceSourceHomotopy_zero y)

/-! ## Quotient-piece retractions and homotopy equivalences -/

def leftSolidTorusInclusion (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    C(SolidTorus, leftOpen h) :=
  ⟨fun x ↦ namedLeftPieceQuotientMap h ⟨Sum.inl x, trivial⟩,
    (namedLeftPieceQuotientMap_isQuotientMap h).continuous.comp
      ((continuous_inl.comp continuous_id).subtype_mk (fun _ ↦ trivial))⟩

def rightSolidTorusInclusion (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    C(SolidTorus, rightOpen h) :=
  ⟨fun x ↦ namedRightPieceQuotientMap h ⟨Sum.inr x, trivial⟩,
    (namedRightPieceQuotientMap_isQuotientMap h).continuous.comp
      ((continuous_inr.comp continuous_id).subtype_mk (fun _ ↦ trivial))⟩

def boundaryIntersectionInclusion (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    C(BoundaryTorus, ↥(leftOpen h ∩ rightOpen h)) :=
  ⟨fun z ↦ namedIntersectionPieceQuotientMap h
      ⟨Sum.inl (boundaryInclusion z), boundaryInclusion_mem_annularBand z⟩,
    (namedIntersectionPieceQuotientMap_isQuotientMap h).continuous.comp
      ((continuous_inl.comp continuous_boundaryInclusion).subtype_mk _)⟩

def leftSplitRetraction (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    SolidTorus ⊕ annularBand → SolidTorus :=
  Sum.elim id (boundaryInclusion ∘ h.symm ∘ annularProjection)

theorem continuous_leftSplitRetraction (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    Continuous (leftSplitRetraction h) := by
  apply Continuous.sumElim
  · exact continuous_id
  · exact continuous_boundaryInclusion.comp <|
      h.symm.continuous.comp continuous_annularProjection

def leftSourceRetraction (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    leftPreimage → SolidTorus :=
  leftSplitRetraction h ∘ leftPreimageSumHomeomorph

theorem continuous_leftSourceRetraction (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    Continuous (leftSourceRetraction h) :=
  (continuous_leftSplitRetraction h).comp leftPreimageSumHomeomorph.continuous

@[simp] theorem leftSourceRetraction_inl (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (x : SolidTorus) (hx : Sum.inl x ∈ leftPreimage) :
    leftSourceRetraction h ⟨Sum.inl x, hx⟩ = x := rfl

@[simp] theorem leftSourceRetraction_inr (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (x : annularBand) (hx : Sum.inr x.1 ∈ leftPreimage) :
    leftSourceRetraction h ⟨Sum.inr x.1, hx⟩ =
      boundaryInclusion (h.symm (annularProjection x)) := rfl

theorem leftSourceRetraction_eq_of_eqv (h : BoundaryTorus ≃ₜ BoundaryTorus)
    {a b : Sum SolidTorus SolidTorus} (ha : a ∈ leftPreimage)
    (hb : b ∈ leftPreimage) (hab : Relation.EqvGen (BoundaryGlueRel h) a b) :
    leftSourceRetraction h ⟨a, ha⟩ = leftSourceRetraction h ⟨b, hb⟩ := by
  induction hab with
  | rel a b hab =>
      cases hab with
      | glue z =>
          rw [leftSourceRetraction_inl]
          let xb : annularBand :=
            ⟨boundaryInclusion (h z), boundaryInclusion_mem_annularBand (h z)⟩
          have hp : annularProjection xb = h z := annularProjection_boundary (h z)
          have hr := leftSourceRetraction_inr h xb hb
          rw [hr, hp, Homeomorph.symm_apply_apply]
  | refl => rfl
  | symm a b _ ih => exact (ih hb ha).symm
  | trans a b c hab hbc ih₁ ih₂ =>
      have hm := (leftPreimage_respects h hab).mp ha
      exact (ih₁ ha hm).trans (ih₂ hm hb)

theorem leftSourceRetraction_fiber_coherent (h : BoundaryTorus ≃ₜ BoundaryTorus)
    {a b : leftPreimage} (hab : namedLeftPieceQuotientMap h a =
      namedLeftPieceQuotientMap h b) :
    leftSourceRetraction h a = leftSourceRetraction h b := by
  apply leftSourceRetraction_eq_of_eqv h a.2 b.2
  exact Quotient.exact (congrArg Subtype.val hab)

noncomputable def leftPieceRetraction (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    leftOpen h → SolidTorus := fun x ↦
  leftSourceRetraction h <|
    Function.surjInv (namedLeftPieceQuotientMap_isQuotientMap h).surjective x

theorem leftPieceRetraction_pullback (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (x : leftPreimage) :
    leftPieceRetraction h (namedLeftPieceQuotientMap h x) =
      leftSourceRetraction h x := by
  apply leftSourceRetraction_fiber_coherent h
  exact Function.surjInv_eq
    (namedLeftPieceQuotientMap_isQuotientMap h).surjective _

theorem continuous_leftPieceRetraction (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    Continuous (leftPieceRetraction h) := by
  rw [(namedLeftPieceQuotientMap_isQuotientMap h).continuous_iff]
  convert continuous_leftSourceRetraction h using 1
  funext x
  exact leftPieceRetraction_pullback h x

theorem leftPieceRetraction_comp_inclusion (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    (⟨leftPieceRetraction h, continuous_leftPieceRetraction h⟩ :
      C(leftOpen h, SolidTorus)).comp (leftSolidTorusInclusion h) =
        ContinuousMap.id SolidTorus := by
  apply ContinuousMap.ext
  intro x
  exact leftPieceRetraction_pullback h ⟨Sum.inl x, trivial⟩

theorem leftPieceHomotopyMap_one (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (x : leftOpen h) :
    leftPieceHomotopyMap h ((1 : unitInterval), x) =
      leftSolidTorusInclusion h (leftPieceRetraction h x) := by
  obtain ⟨y, rfl⟩ := (namedLeftPieceQuotientMap_isQuotientMap h).surjective x
  rw [leftPieceRetraction_pullback]
  calc
    _ = namedLeftPieceQuotientMap h
        (leftPieceSourceHomotopy ((1 : unitInterval), y)) :=
      leftPieceHomotopyMap_pullback h ((1 : unitInterval), y)
    _ = leftSolidTorusInclusion h (leftSourceRetraction h y) := by
      rcases y with ⟨y, hy⟩
      cases y with
      | inl y =>
          rw [leftSourceRetraction_inl]
          rfl
      | inr y =>
          let yb : annularBand := ⟨y, hy⟩
          let z : BoundaryTorus := h.symm (annularProjection yb)
          have hs : leftPieceSourceHomotopy
              ((1 : unitInterval), ⟨Sum.inr y, hy⟩) =
              ⟨Sum.inr (boundaryInclusion (annularProjection yb)),
                boundaryInclusion_mem_annularBand (annularProjection yb)⟩ := by
            apply Subtype.ext
            simpa only [leftPieceSourceHomotopy_inr] using
              congrArg (fun w : annularBand ↦ Sum.inr w.1) (annularRadial_one yb)
          have hr : leftSourceRetraction h ⟨Sum.inr y, hy⟩ =
              boundaryInclusion z := by rfl
          rw [hr, congrArg (namedLeftPieceQuotientMap h) hs]
          apply Subtype.ext
          have hg : quotientMap h (Sum.inl (boundaryInclusion z)) =
              quotientMap h (Sum.inr (boundaryInclusion (h z))) :=
            Quotient.sound (Relation.EqvGen.rel _ _ (BoundaryGlueRel.glue z))
          simpa only [z, Homeomorph.apply_symm_apply] using hg.symm

def leftPieceHomotopy (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    ContinuousMap.Homotopy (ContinuousMap.id (leftOpen h))
      ((leftSolidTorusInclusion h).comp
        ⟨leftPieceRetraction h, continuous_leftPieceRetraction h⟩) where
  toFun := leftPieceHomotopyMap h
  continuous_toFun := continuous_leftPieceHomotopyMap h
  map_zero_left := leftPieceHomotopyMap_zero h
  map_one_left := leftPieceHomotopyMap_one h

def leftPieceHomotopyEquiv (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    leftOpen h ≃ₕ SolidTorus where
  toFun := ⟨leftPieceRetraction h, continuous_leftPieceRetraction h⟩
  invFun := leftSolidTorusInclusion h
  left_inv := ⟨(leftPieceHomotopy h).symm⟩
  right_inv := by rw [leftPieceRetraction_comp_inclusion]

def rightSplitRetraction (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    annularBand ⊕ SolidTorus → SolidTorus :=
  Sum.elim (boundaryInclusion ∘ h ∘ annularProjection) id

theorem continuous_rightSplitRetraction (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    Continuous (rightSplitRetraction h) := by
  apply Continuous.sumElim
  · exact continuous_boundaryInclusion.comp <|
      h.continuous.comp continuous_annularProjection
  · exact continuous_id

def rightSourceRetraction (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    rightPreimage → SolidTorus :=
  rightSplitRetraction h ∘ rightPreimageSumHomeomorph

theorem continuous_rightSourceRetraction (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    Continuous (rightSourceRetraction h) :=
  (continuous_rightSplitRetraction h).comp rightPreimageSumHomeomorph.continuous

@[simp] theorem rightSourceRetraction_inl (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (x : annularBand) (hx : Sum.inl x.1 ∈ rightPreimage) :
    rightSourceRetraction h ⟨Sum.inl x.1, hx⟩ =
      boundaryInclusion (h (annularProjection x)) := rfl

@[simp] theorem rightSourceRetraction_inr (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (x : SolidTorus) (hx : Sum.inr x ∈ rightPreimage) :
    rightSourceRetraction h ⟨Sum.inr x, hx⟩ = x := rfl

theorem rightSourceRetraction_eq_of_eqv (h : BoundaryTorus ≃ₜ BoundaryTorus)
    {a b : Sum SolidTorus SolidTorus} (ha : a ∈ rightPreimage)
    (hb : b ∈ rightPreimage) (hab : Relation.EqvGen (BoundaryGlueRel h) a b) :
    rightSourceRetraction h ⟨a, ha⟩ = rightSourceRetraction h ⟨b, hb⟩ := by
  induction hab with
  | rel a b hab =>
      cases hab with
      | glue z =>
          let xb : annularBand :=
            ⟨boundaryInclusion z, boundaryInclusion_mem_annularBand z⟩
          have hp : annularProjection xb = z := annularProjection_boundary z
          have hl := rightSourceRetraction_inl h xb ha
          rw [hl, hp, rightSourceRetraction_inr]
  | refl => rfl
  | symm a b _ ih => exact (ih hb ha).symm
  | trans a b c hab hbc ih₁ ih₂ =>
      have hm := (rightPreimage_respects h hab).mp ha
      exact (ih₁ ha hm).trans (ih₂ hm hb)

theorem rightSourceRetraction_fiber_coherent (h : BoundaryTorus ≃ₜ BoundaryTorus)
    {a b : rightPreimage} (hab : namedRightPieceQuotientMap h a =
      namedRightPieceQuotientMap h b) :
    rightSourceRetraction h a = rightSourceRetraction h b := by
  apply rightSourceRetraction_eq_of_eqv h a.2 b.2
  exact Quotient.exact (congrArg Subtype.val hab)

noncomputable def rightPieceRetraction (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    rightOpen h → SolidTorus := fun x ↦
  rightSourceRetraction h <|
    Function.surjInv (namedRightPieceQuotientMap_isQuotientMap h).surjective x

theorem rightPieceRetraction_pullback (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (x : rightPreimage) :
    rightPieceRetraction h (namedRightPieceQuotientMap h x) =
      rightSourceRetraction h x := by
  apply rightSourceRetraction_fiber_coherent h
  exact Function.surjInv_eq
    (namedRightPieceQuotientMap_isQuotientMap h).surjective _

theorem continuous_rightPieceRetraction (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    Continuous (rightPieceRetraction h) := by
  rw [(namedRightPieceQuotientMap_isQuotientMap h).continuous_iff]
  convert continuous_rightSourceRetraction h using 1
  funext x
  exact rightPieceRetraction_pullback h x

theorem rightPieceRetraction_comp_inclusion (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    (⟨rightPieceRetraction h, continuous_rightPieceRetraction h⟩ :
      C(rightOpen h, SolidTorus)).comp (rightSolidTorusInclusion h) =
        ContinuousMap.id SolidTorus := by
  apply ContinuousMap.ext
  intro x
  exact rightPieceRetraction_pullback h ⟨Sum.inr x, trivial⟩

theorem rightPieceHomotopyMap_one (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (x : rightOpen h) :
    rightPieceHomotopyMap h ((1 : unitInterval), x) =
      rightSolidTorusInclusion h (rightPieceRetraction h x) := by
  obtain ⟨y, rfl⟩ := (namedRightPieceQuotientMap_isQuotientMap h).surjective x
  rw [rightPieceRetraction_pullback]
  calc
    _ = namedRightPieceQuotientMap h
        (rightPieceSourceHomotopy ((1 : unitInterval), y)) :=
      rightPieceHomotopyMap_pullback h ((1 : unitInterval), y)
    _ = rightSolidTorusInclusion h (rightSourceRetraction h y) := by
      rcases y with ⟨y, hy⟩
      cases y with
      | inl y =>
          let yb : annularBand := ⟨y, hy⟩
          let z : BoundaryTorus := annularProjection yb
          have hs : rightPieceSourceHomotopy
              ((1 : unitInterval), ⟨Sum.inl y, hy⟩) =
              ⟨Sum.inl (boundaryInclusion z),
                boundaryInclusion_mem_annularBand z⟩ := by
            apply Subtype.ext
            simpa only [rightPieceSourceHomotopy_inl, z] using
              congrArg (fun w : annularBand ↦ Sum.inl w.1) (annularRadial_one yb)
          have hr : rightSourceRetraction h ⟨Sum.inl y, hy⟩ =
              boundaryInclusion (h z) := by rfl
          rw [hr, congrArg (namedRightPieceQuotientMap h) hs]
          apply Subtype.ext
          exact Quotient.sound
            (Relation.EqvGen.rel _ _ (BoundaryGlueRel.glue z))
      | inr y =>
          rw [rightSourceRetraction_inr]
          rfl

def rightPieceHomotopy (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    ContinuousMap.Homotopy (ContinuousMap.id (rightOpen h))
      ((rightSolidTorusInclusion h).comp
        ⟨rightPieceRetraction h, continuous_rightPieceRetraction h⟩) where
  toFun := rightPieceHomotopyMap h
  continuous_toFun := continuous_rightPieceHomotopyMap h
  map_zero_left := rightPieceHomotopyMap_zero h
  map_one_left := rightPieceHomotopyMap_one h

def rightPieceHomotopyEquiv (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    rightOpen h ≃ₕ SolidTorus where
  toFun := ⟨rightPieceRetraction h, continuous_rightPieceRetraction h⟩
  invFun := rightSolidTorusInclusion h
  left_inv := ⟨(rightPieceHomotopy h).symm⟩
  right_inv := by rw [rightPieceRetraction_comp_inclusion]

def intersectionSplitRetraction (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    annularBand ⊕ annularBand → BoundaryTorus :=
  Sum.elim annularProjection (h.symm ∘ annularProjection)

theorem continuous_intersectionSplitRetraction
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    Continuous (intersectionSplitRetraction h) := by
  apply Continuous.sumElim
  · exact continuous_annularProjection
  · exact h.symm.continuous.comp continuous_annularProjection

def intersectionSourceRetraction (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    bothBandPreimage → BoundaryTorus :=
  intersectionSplitRetraction h ∘ bothBandPreimageSumHomeomorph

theorem continuous_intersectionSourceRetraction
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    Continuous (intersectionSourceRetraction h) :=
  (continuous_intersectionSplitRetraction h).comp
    bothBandPreimageSumHomeomorph.continuous

@[simp] theorem intersectionSourceRetraction_inl
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (x : annularBand)
    (hx : Sum.inl x.1 ∈ bothBandPreimage) :
    intersectionSourceRetraction h ⟨Sum.inl x.1, hx⟩ = annularProjection x := rfl

@[simp] theorem intersectionSourceRetraction_inr
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (x : annularBand)
    (hx : Sum.inr x.1 ∈ bothBandPreimage) :
    intersectionSourceRetraction h ⟨Sum.inr x.1, hx⟩ =
      h.symm (annularProjection x) := rfl

theorem intersectionSourceRetraction_eq_of_eqv
    (h : BoundaryTorus ≃ₜ BoundaryTorus) {a b : Sum SolidTorus SolidTorus}
    (ha : a ∈ bothBandPreimage) (hb : b ∈ bothBandPreimage)
    (hab : Relation.EqvGen (BoundaryGlueRel h) a b) :
    intersectionSourceRetraction h ⟨a, ha⟩ =
      intersectionSourceRetraction h ⟨b, hb⟩ := by
  induction hab with
  | rel a b hab =>
      cases hab with
      | glue z =>
          let xl : annularBand :=
            ⟨boundaryInclusion z, boundaryInclusion_mem_annularBand z⟩
          let xr : annularBand :=
            ⟨boundaryInclusion (h z), boundaryInclusion_mem_annularBand (h z)⟩
          have hpl : annularProjection xl = z := annularProjection_boundary z
          have hpr : annularProjection xr = h z := annularProjection_boundary (h z)
          have hl := intersectionSourceRetraction_inl h xl ha
          have hr := intersectionSourceRetraction_inr h xr hb
          rw [hl, hr, hpl, hpr, Homeomorph.symm_apply_apply]
  | refl => rfl
  | symm a b _ ih => exact (ih hb ha).symm
  | trans a b c hab hbc ih₁ ih₂ =>
      have hal : a ∈ leftPreimage := by cases a with | inl => trivial | inr => exact ha
      have har : a ∈ rightPreimage := by cases a with | inl => exact ha | inr => trivial
      have hml := (leftPreimage_respects h hab).mp hal
      have hmr := (rightPreimage_respects h hab).mp har
      have hm : b ∈ bothBandPreimage := by cases b with | inl => exact hmr | inr => exact hml
      exact (ih₁ ha hm).trans (ih₂ hm hb)

theorem intersectionSourceRetraction_fiber_coherent
    (h : BoundaryTorus ≃ₜ BoundaryTorus) {a b : bothBandPreimage}
    (hab : namedIntersectionPieceQuotientMap h a =
      namedIntersectionPieceQuotientMap h b) :
    intersectionSourceRetraction h a = intersectionSourceRetraction h b := by
  apply intersectionSourceRetraction_eq_of_eqv h a.2 b.2
  exact Quotient.exact (congrArg Subtype.val hab)

noncomputable def intersectionPieceRetraction
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    ↥(leftOpen h ∩ rightOpen h) → BoundaryTorus := fun x ↦
  intersectionSourceRetraction h <| Function.surjInv
    (namedIntersectionPieceQuotientMap_isQuotientMap h).surjective x

theorem intersectionPieceRetraction_pullback
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (x : bothBandPreimage) :
    intersectionPieceRetraction h (namedIntersectionPieceQuotientMap h x) =
      intersectionSourceRetraction h x := by
  apply intersectionSourceRetraction_fiber_coherent h
  exact Function.surjInv_eq
    (namedIntersectionPieceQuotientMap_isQuotientMap h).surjective _

theorem continuous_intersectionPieceRetraction
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    Continuous (intersectionPieceRetraction h) := by
  rw [(namedIntersectionPieceQuotientMap_isQuotientMap h).continuous_iff]
  convert continuous_intersectionSourceRetraction h using 1
  funext x
  exact intersectionPieceRetraction_pullback h x

theorem intersectionPieceRetraction_comp_inclusion
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    (⟨intersectionPieceRetraction h, continuous_intersectionPieceRetraction h⟩ :
      C(↥(leftOpen h ∩ rightOpen h), BoundaryTorus)).comp
        (boundaryIntersectionInclusion h) = ContinuousMap.id BoundaryTorus := by
  apply ContinuousMap.ext
  intro z
  change intersectionPieceRetraction h
      (namedIntersectionPieceQuotientMap h
        ⟨Sum.inl (boundaryInclusion z), boundaryInclusion_mem_annularBand z⟩) = z
  rw [intersectionPieceRetraction_pullback]
  exact annularProjection_boundary z

theorem intersectionPieceHomotopyMap_one (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (x : ↥(leftOpen h ∩ rightOpen h)) :
    intersectionPieceHomotopyMap h ((1 : unitInterval), x) =
      boundaryIntersectionInclusion h (intersectionPieceRetraction h x) := by
  obtain ⟨y, rfl⟩ :=
    (namedIntersectionPieceQuotientMap_isQuotientMap h).surjective x
  rw [intersectionPieceRetraction_pullback]
  calc
    _ = namedIntersectionPieceQuotientMap h
        (intersectionPieceSourceHomotopy ((1 : unitInterval), y)) :=
      intersectionPieceHomotopyMap_pullback h ((1 : unitInterval), y)
    _ = boundaryIntersectionInclusion h (intersectionSourceRetraction h y) := by
      rcases y with ⟨y, hy⟩
      cases y with
      | inl y =>
          let yb : annularBand := ⟨y, hy⟩
          have hs : intersectionPieceSourceHomotopy
              ((1 : unitInterval), ⟨Sum.inl y, hy⟩) =
              ⟨Sum.inl (boundaryInclusion (annularProjection yb)),
                boundaryInclusion_mem_annularBand (annularProjection yb)⟩ := by
            apply Subtype.ext
            simpa only [intersectionPieceSourceHomotopy_inl] using
              congrArg (fun w : annularBand ↦ Sum.inl w.1) (annularRadial_one yb)
          have hr : intersectionSourceRetraction h ⟨Sum.inl y, hy⟩ =
              annularProjection yb := rfl
          rw [hr, congrArg (namedIntersectionPieceQuotientMap h) hs]
          apply Subtype.ext
          rfl
      | inr y =>
          let yb : annularBand := ⟨y, hy⟩
          let z : BoundaryTorus := h.symm (annularProjection yb)
          have hs : intersectionPieceSourceHomotopy
              ((1 : unitInterval), ⟨Sum.inr y, hy⟩) =
              ⟨Sum.inr (boundaryInclusion (annularProjection yb)),
                boundaryInclusion_mem_annularBand (annularProjection yb)⟩ := by
            apply Subtype.ext
            simpa only [intersectionPieceSourceHomotopy_inr] using
              congrArg (fun w : annularBand ↦ Sum.inr w.1) (annularRadial_one yb)
          have hr : intersectionSourceRetraction h ⟨Sum.inr y, hy⟩ = z := rfl
          rw [hr, congrArg (namedIntersectionPieceQuotientMap h) hs]
          apply Subtype.ext
          have hg : quotientMap h (Sum.inl (boundaryInclusion z)) =
              quotientMap h (Sum.inr (boundaryInclusion (h z))) :=
            Quotient.sound (Relation.EqvGen.rel _ _ (BoundaryGlueRel.glue z))
          simpa only [z, Homeomorph.apply_symm_apply] using hg.symm

def intersectionPieceHomotopy (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    ContinuousMap.Homotopy
      (ContinuousMap.id ↥(leftOpen h ∩ rightOpen h))
      ((boundaryIntersectionInclusion h).comp
        ⟨intersectionPieceRetraction h,
          continuous_intersectionPieceRetraction h⟩) where
  toFun := intersectionPieceHomotopyMap h
  continuous_toFun := continuous_intersectionPieceHomotopyMap h
  map_zero_left := intersectionPieceHomotopyMap_zero h
  map_one_left := intersectionPieceHomotopyMap_one h

def intersectionPieceHomotopyEquiv (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    ↥(leftOpen h ∩ rightOpen h) ≃ₕ BoundaryTorus where
  toFun := ⟨intersectionPieceRetraction h,
    continuous_intersectionPieceRetraction h⟩
  invFun := boundaryIntersectionInclusion h
  left_inv := ⟨(intersectionPieceHomotopy h).symm⟩
  right_inv := by rw [intersectionPieceRetraction_comp_inclusion]

/-! ## Compatibility of the intersection and piece coordinates -/

def intersectionToLeftOpen (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    C(↥(leftOpen h ∩ rightOpen h), leftOpen h) :=
  ⟨fun x => ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩

def intersectionToRightOpen (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    C(↥(leftOpen h ∩ rightOpen h), rightOpen h) :=
  ⟨fun x => ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩

theorem intersectionToLeftOpen_named_inl
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (z : BoundaryTorus)
    (hz : Sum.inl (boundaryInclusion z) ∈ bothBandPreimage) :
    intersectionToLeftOpen h
        (namedIntersectionPieceQuotientMap h
          ⟨Sum.inl (boundaryInclusion z), hz⟩) =
      namedLeftPieceQuotientMap h
        ⟨Sum.inl (boundaryInclusion z), trivial⟩ := by
  apply Subtype.ext
  rfl

theorem intersectionToRightOpen_named_inl
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (z : BoundaryTorus)
    (hz : Sum.inl (boundaryInclusion z) ∈ bothBandPreimage) :
    intersectionToRightOpen h
        (namedIntersectionPieceQuotientMap h
          ⟨Sum.inl (boundaryInclusion z), hz⟩) =
      namedRightPieceQuotientMap h
        ⟨Sum.inl (boundaryInclusion z),
          boundaryInclusion_mem_annularBand z⟩ := by
  apply Subtype.ext
  rfl

theorem intersection_left_coordinate_strict (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    (leftPieceHomotopyEquiv h).toFun.comp
        ((intersectionToLeftOpen h).comp
          (intersectionPieceHomotopyEquiv h).invFun) =
      ⟨boundaryInclusion, continuous_boundaryInclusion⟩ := by
  apply ContinuousMap.ext
  intro z
  change leftPieceRetraction h
      (intersectionToLeftOpen h (boundaryIntersectionInclusion h z)) =
    boundaryInclusion z
  rw [show intersectionToLeftOpen h (boundaryIntersectionInclusion h z) =
      namedLeftPieceQuotientMap h
        ⟨Sum.inl (boundaryInclusion z), trivial⟩ by
    exact intersectionToLeftOpen_named_inl h z
      (boundaryInclusion_mem_annularBand z)]
  exact leftPieceRetraction_pullback h
    ⟨Sum.inl (boundaryInclusion z), trivial⟩

theorem intersection_right_coordinate_strict
    (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    (rightPieceHomotopyEquiv h).toFun.comp
        ((intersectionToRightOpen h).comp
          (intersectionPieceHomotopyEquiv h).invFun) =
      ⟨boundaryInclusion ∘ h,
        continuous_boundaryInclusion.comp h.continuous⟩ := by
  apply ContinuousMap.ext
  intro z
  change rightPieceRetraction h
      (intersectionToRightOpen h (boundaryIntersectionInclusion h z)) =
    boundaryInclusion (h z)
  rw [show intersectionToRightOpen h (boundaryIntersectionInclusion h z) =
      namedRightPieceQuotientMap h
        ⟨Sum.inl (boundaryInclusion z),
          boundaryInclusion_mem_annularBand z⟩ by
    exact intersectionToRightOpen_named_inl h z
      (boundaryInclusion_mem_annularBand z)]
  rw [rightPieceRetraction_pullback]
  let xb : annularBand :=
    ⟨boundaryInclusion z, boundaryInclusion_mem_annularBand z⟩
  have hr := rightSourceRetraction_inl h xb
    (boundaryInclusion_mem_annularBand z)
  rw [hr, annularProjection_boundary]

#print axioms annularBand_isOpen
#print axioms leftPreimage_respects
#print axioms quotientMap_preimage_inter_open
#print axioms intersectionPieceQuotientMap_isQuotientMap
#print axioms intersection_left_coordinate_strict
#print axioms intersection_right_coordinate_strict

end ConstructionTargets.SolidTorusGluingOpenCover
