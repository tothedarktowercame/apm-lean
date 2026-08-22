import ConstructionTargets.T02A06SphereH0
import Mathlib.Algebra.Homology.ShortComplex.QuasiIso

/-!
# The bottom class for the sphere-homology induction

This file identifies the native one-dimensional closed-disk pair with the
unit interval and its endpoint pair.  It then transports the already computed
relative interval fundamental class to `H₁(S¹)`.
-/

noncomputable section

namespace ConstructionTargets.T02A06SphereOne

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.T02A06DiskRadialComparison
open ConstructionTargets.T02A06SphereShift
open T02A06

private theorem euclideanOne_norm (x : EuclideanSpace ℝ (Fin 1)) :
    ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_one, Real.norm_eq_abs]
  rw [Real.sqrt_sq_eq_abs, abs_abs]

/-- The affine identification of the closed one-disk `[-1,1]` with `[0,1]`. -/
def closedDiskOneHomeomorphUnitInterval :
    euclideanClosedDisk 1 ≃ₜ unitInterval where
  toFun x := ⟨(x.1 0 + 1) / 2, by
    have hx : |x.1 0| ≤ 1 := by
      rw [← euclideanOne_norm]
      have hx' := x.2
      change dist x.1 0 ≤ 1 at hx'
      simpa [dist_zero_right] using hx'
    exact ⟨by nlinarith [neg_le_of_abs_le hx], by nlinarith [le_of_abs_le hx]⟩⟩
  invFun t := ⟨euclideanSnoc (0 : EuclideanSpace ℝ (Fin 0)) (2 * t.1 - 1), by
    rw [Metric.mem_closedBall, dist_zero_right, euclideanOne_norm]
    have hs : (euclideanSnoc (0 : EuclideanSpace ℝ (Fin 0))
        (2 * t.1 - 1)) 0 = 2 * t.1 - 1 := by
      simpa using euclideanSnoc_last (0 : EuclideanSpace ℝ (Fin 0)) (2 * t.1 - 1)
    rw [hs]
    rw [abs_le]
    exact ⟨by nlinarith [t.2.1], by nlinarith [t.2.2]⟩⟩
  left_inv x := by
    apply Subtype.ext
    ext i
    fin_cases i
    have hs : (euclideanSnoc (0 : EuclideanSpace ℝ (Fin 0))
        (2 * ((x.1 0 + 1) / 2) - 1)) 0 =
          2 * ((x.1 0 + 1) / 2) - 1 := by
      simpa using euclideanSnoc_last (0 : EuclideanSpace ℝ (Fin 0))
        (2 * ((x.1 0 + 1) / 2) - 1)
    change (euclideanSnoc (0 : EuclideanSpace ℝ (Fin 0))
      (2 * ((x.1 0 + 1) / 2) - 1)) 0 = x.1 0
    rw [hs]
    ring
  right_inv t := by
    apply Subtype.ext
    have hs : (euclideanSnoc (0 : EuclideanSpace ℝ (Fin 0))
        (2 * t.1 - 1)) 0 = 2 * t.1 - 1 := by
      simpa using euclideanSnoc_last (0 : EuclideanSpace ℝ (Fin 0)) (2 * t.1 - 1)
    change (((euclideanSnoc (0 : EuclideanSpace ℝ (Fin 0))
      (2 * t.1 - 1)) 0 + 1) / 2) = t.1
    rw [hs]
    ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_euclideanSnoc.comp
      (continuous_const.prodMk (by fun_prop))

theorem closedDiskOne_boundary_iff (x : euclideanClosedDisk 1) :
    x.1 ∈ euclideanUnitSphere 1 ↔
      closedDiskOneHomeomorphUnitInterval x ∈ intervalBoundary := by
  have hnorm : ‖x.1‖ = |x.1 0| := euclideanOne_norm x.1
  constructor
  · intro hx
    have ha : |x.1 0| = 1 := by
      rw [← hnorm]
      simpa [Metric.mem_sphere, dist_zero_right] using hx
    rcases (abs_eq zero_le_one).mp ha with h | h
    · right
      apply Subtype.ext
      change (x.1 0 + 1) / 2 = 1
      rw [h]
      norm_num
    · left
      apply Subtype.ext
      change (x.1 0 + 1) / 2 = 0
      rw [h]
      norm_num
  · intro hx
    have hcoord : x.1 0 = 1 ∨ x.1 0 = -1 := by
      rcases hx with hx | hx
      · right
        have hv := congrArg Subtype.val hx
        change (x.1 0 + 1) / 2 = 0 at hv
        linarith
      · left
        have hv := congrArg Subtype.val hx
        change (x.1 0 + 1) / 2 = 1 at hv
        linarith
    rw [Metric.mem_sphere, dist_zero_right, hnorm]
    rcases hcoord with h | h <;> simp [h]

/-- The affine disk homeomorphism identifies its boundary with the two
endpoints of the unit interval. -/
def closedDiskOneBoundaryHomeomorphIntervalBoundary :
    closedDiskBoundarySet 1 ≃ₜ intervalBoundary :=
  closedDiskOneHomeomorphUnitInterval.subtype closedDiskOne_boundary_iff

private def closedDiskOneToInterval : C(euclideanClosedDisk 1, unitInterval) :=
  ⟨closedDiskOneHomeomorphUnitInterval,
    closedDiskOneHomeomorphUnitInterval.continuous⟩

private theorem closedDiskOneToInterval_mapsTo :
    Set.MapsTo closedDiskOneToInterval (closedDiskBoundarySet 1)
      intervalBoundary := fun x hx =>
  closedDiskOne_boundary_iff x |>.mp hx

/-- The affine homeomorphism of pairs induces the corresponding relative
homology isomorphism in every degree. -/
noncomputable def closedDiskOneRelativeIsoInterval (k : ℕ) :
    (RelativeSingularChains (closedDiskBoundarySet 1)).homology k ≅
      (RelativeSingularChains intervalBoundary).homology k := by
  let f := closedDiskOneToInterval
  let hf := closedDiskOneToInterval_mapsTo
  have hambTop : TopCat.ofHom f =
      (TopCat.isoOfHomeo closedDiskOneHomeomorphUnitInterval).hom := rfl
  letI : IsIso (TopCat.ofHom f) := hambTop ▸ inferInstance
  have hsubTop : subspaceMap (closedDiskBoundarySet 1) intervalBoundary f hf =
      (TopCat.isoOfHomeo closedDiskOneBoundaryHomeomorphIntervalBoundary).hom := by
    ext x
    rfl
  letI : IsIso (subspaceMap (closedDiskBoundarySet 1) intervalBoundary f hf) :=
    hsubTop ▸ inferInstance
  have hamb (j : ℕ) : IsIso (HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)) j) := by
    infer_instance
  let hrel := relativeSingularMap_homologyMap_isIso
    (closedDiskBoundarySet 1) intervalBoundary f hf k
    (by infer_instance) (hamb k)
    (fun _ _ => by infer_instance) (fun j _ => hamb j)
  exact @asIso _ _ _ _
    (HomologicalComplex.homologyMap
      (relativeSingularMap (closedDiskBoundarySet 1) intervalBoundary f hf) k)
    hrel

/-- The fundamental computation `H₁(S¹) ≅ ℤ`. -/
noncomputable def sphereOneH1IsoInt :
    SingularHomology 1 (TopCat.of
      (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 1)) ≅
      AddCommGrpCat.of ℤ :=
  sphereH1IsoNativeDiskRelative 1 ≪≫
    closedDiskOneRelativeIsoInterval 1 ≪≫
    intervalBoundaryRelativeH1IsoInt

/-- The top-dimensional computation `H₂(S²) ≅ ℤ`. -/
noncomputable def sphereTwoH2IsoInt :
    SingularHomology 2 (TopCat.of
      (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2)) ≅
      AddCommGrpCat.of ℤ :=
  spherePositiveHomologyShift 2 1 (by decide) ≪≫ sphereOneH1IsoInt

/-- A concrete nonzero fundamental class in `H₂(S²)`. -/
noncomputable def sphereTwoH2Generator :
    SingularHomology 2 (TopCat.of
      (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2)) :=
  sphereTwoH2IsoInt.inv 1

@[simp] theorem sphereTwoH2IsoInt_generator :
    sphereTwoH2IsoInt.hom sphereTwoH2Generator = 1 := by
  simp [sphereTwoH2Generator]

theorem sphereTwoH2Generator_ne_zero : sphereTwoH2Generator ≠ 0 := by
  intro h
  have hgen := sphereTwoH2IsoInt_generator
  rw [h, map_zero] at hgen
  exact zero_ne_one hgen

theorem sphereTwo_homology_two_not_isZero :
    ¬ IsZero (SingularHomology 2 (TopCat.of
      (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2))) := by
  intro h
  have hid : (𝟙 (SingularHomology 2 (TopCat.of
      (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2)))) = 0 :=
    (IsZero.iff_id_eq_zero _).mp h
  have hzero := ConcreteCategory.congr_hom hid sphereTwoH2Generator
  exact sphereTwoH2Generator_ne_zero (by simpa using hzero)

private abbrev H₂Functor :=
  (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 2).obj
    (AddCommGrpCat.of ℤ)

private noncomputable def sphereTwoBasepoint :
    ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2 :=
  ⟨Classical.choose (NormedSpace.sphere_nonempty.mpr (by norm_num)),
    Classical.choose_spec (NormedSpace.sphere_nonempty.mpr (by norm_num))⟩

private def sphereTwoProductSection :
    TopCat.of (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2) ⟶
      TopCat.of (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2 ×
        ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2) :=
  TopCat.ofHom ⟨fun x ↦ (x, sphereTwoBasepoint),
    continuous_id.prodMk continuous_const⟩

private def sphereTwoProductRetraction :
    TopCat.of (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2 ×
        ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2) ⟶
      TopCat.of (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2) :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

private theorem sphereTwoProductSection_retraction :
    sphereTwoProductSection ≫ sphereTwoProductRetraction = 𝟙 _ := by
  ext x
  rfl

/-- There is no homeomorphism `S² × S² ≃ₜ S⁴`.  Only the retract
`S² ⇄ S² × S²` is needed; no Künneth theorem enters the proof. -/
theorem no_homeomorph_sphereTwo_product_sphereTwo_sphereFour :
    ¬ Nonempty
      ((ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2 ×
          ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2) ≃ₜ
        ConstructionTargets.T02A06HemisphereExcision.ambientSphere 4) := by
  rintro ⟨e⟩
  let eIso :
      TopCat.of (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2 ×
          ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2) ≅
        TopCat.of (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 4) :=
    TopCat.isoOfHomeo e
  have hezero : H₂Functor.map eIso.hom = 0 :=
    ConstructionTargets.T02A06SphereH0.sphereFour_homology_two_isZero.eq_of_tgt _ _
  have hsection : H₂Functor.map sphereTwoProductSection = 0 := by
    apply (cancel_mono (H₂Functor.map eIso.hom)).mp
    rw [hezero, comp_zero, zero_comp]
  have hretract :
      H₂Functor.map sphereTwoProductSection ≫
        H₂Functor.map sphereTwoProductRetraction = 𝟙 _ := by
    rw [← H₂Functor.map_comp, sphereTwoProductSection_retraction,
      H₂Functor.map_id]
  apply sphereTwo_homology_two_not_isZero
  rw [IsZero.iff_id_eq_zero, ← hretract, hsection, zero_comp]

#print axioms closedDiskOneHomeomorphUnitInterval
#print axioms closedDiskOneBoundaryHomeomorphIntervalBoundary
#print axioms closedDiskOneRelativeIsoInterval
#print axioms sphereOneH1IsoInt
#print axioms sphereTwoH2IsoInt
#print axioms sphereTwoH2Generator_ne_zero
#print axioms sphereTwo_homology_two_not_isZero
#print axioms no_homeomorph_sphereTwo_product_sphereTwo_sphereFour

end ConstructionTargets.T02A06SphereOne
