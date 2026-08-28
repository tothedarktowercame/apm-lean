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

#print axioms annularBand_isOpen
#print axioms leftPreimage_respects
#print axioms quotientMap_preimage_inter_open
#print axioms intersectionPieceQuotientMap_isQuotientMap

end ConstructionTargets.SolidTorusGluingOpenCover
