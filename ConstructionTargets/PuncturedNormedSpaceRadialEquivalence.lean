import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homotopy.Equiv

/-!
# Radial homotopy equivalence of a punctured normed space

Radial normalization identifies the complement of the origin in a real
normed space with its unit sphere up to homotopy.  The construction is
independent of finite dimensionality and does not use homology.
-/

noncomputable section

namespace ConstructionTargets.PuncturedNormedSpaceRadialEquivalence

open scoped ContinuousMap

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The punctured normed space, presented as a subtype. -/
abbrev PuncturedSpace := {x : E // x ≠ 0}

/-- The unit sphere, presented with the metric-space convention used by the
manifold sphere APIs. -/
abbrev UnitSphere := Metric.sphere (0 : E) 1

/-- Include the unit sphere into the complement of the origin. -/
def unitSphereInclusion : C(UnitSphere E, PuncturedSpace E) where
  toFun x := ⟨x.1, by
    intro hx
    have hxnorm : ‖x.1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using x.2
    rw [hx, norm_zero] at hxnorm
    norm_num at hxnorm⟩
  continuous_toFun := by fun_prop

/-- Normalize a nonzero vector onto the unit sphere. -/
def radialNormalize : C(PuncturedSpace E, UnitSphere E) where
  toFun x := ⟨NormedSpace.normalize x.1, by
    simpa [Metric.mem_sphere, dist_zero_right] using
      NormedSpace.norm_normalize x.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro x
    have hc : Continuous (fun y : PuncturedSpace E => ‖y.1‖) :=
      continuous_norm.comp continuous_subtype_val
    exact ((hc.continuousAt.inv₀ (norm_ne_zero_iff.mpr x.2)).smul
      continuous_subtype_val.continuousAt)

theorem radialNormalize_unitSphereInclusion (x : UnitSphere E) :
    radialNormalize E (unitSphereInclusion E x) = x := by
  apply Subtype.ext
  change NormedSpace.normalize x.1 = x.1
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (by
    simpa [Metric.mem_sphere, dist_zero_right] using x.2)

/-- Straight-line radial scaling from the normalized vector back to the
original nonzero vector.  Every interpolation coefficient is strictly
positive, so the homotopy remains in the punctured space. -/
def puncturedRadialHomotopy : ContinuousMap.Homotopy
    ((unitSphereInclusion E).comp (radialNormalize E)) (ContinuousMap.id _) where
  toFun tx := by
    let t : ℝ := tx.1
    let x : E := tx.2.1
    let a : ℝ := (1 - t) / ‖x‖ + t
    refine ⟨a • x, ?_⟩
    intro h
    have ht0 : 0 ≤ t := tx.1.2.1
    have ht1 : t ≤ 1 := tx.1.2.2
    have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr tx.2.2
    have ha0 : 0 < a := by
      dsimp [a]
      by_cases ht : t = 0
      · simp [ht, hx0]
      · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
        have hfirst : 0 ≤ (1 - t) / ‖x‖ :=
          div_nonneg (sub_nonneg.mpr ht1) hx0.le
        linarith
    exact tx.2.2 (smul_eq_zero.mp h |>.resolve_left ha0.ne')
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hnorm : Continuous (fun tx : unitInterval × PuncturedSpace E => ‖tx.2.1‖) :=
      continuous_norm.comp (continuous_subtype_val.comp continuous_snd)
    have hne : ∀ tx : unitInterval × PuncturedSpace E, ‖tx.2.1‖ ≠ 0 :=
      fun tx => norm_ne_zero_iff.mpr tx.2.2
    have ht : Continuous (fun tx : unitInterval × PuncturedSpace E => (tx.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun tx : unitInterval × PuncturedSpace E => tx.2.1) :=
      continuous_subtype_val.comp continuous_snd
    exact (((continuous_const.sub ht).div hnorm hne).add ht).smul hx
  map_zero_left x := by
    apply Subtype.ext
    simp [unitSphereInclusion, radialNormalize, NormedSpace.normalize]
  map_one_left x := by
    apply Subtype.ext
    simp

/-- Radial normalization is a homotopy inverse to inclusion of the unit
sphere into the punctured normed space. -/
def unitSphereHomotopyEquivPuncturedSpace :
    UnitSphere E ≃ₕ PuncturedSpace E where
  toFun := unitSphereInclusion E
  invFun := radialNormalize E
  left_inv := by
    rw [show (radialNormalize E).comp (unitSphereInclusion E) =
        ContinuousMap.id _ by
      apply ContinuousMap.ext
      exact radialNormalize_unitSphereInclusion E]
  right_inv := ⟨puncturedRadialHomotopy E⟩

/-- Product transport of the radial equivalence. -/
def unitSphereProductHomotopyEquivPuncturedSpaceProduct
    (Y : Type*) [TopologicalSpace Y] :
    (UnitSphere E × Y) ≃ₕ (PuncturedSpace E × Y) :=
  (unitSphereHomotopyEquivPuncturedSpace E).prodCongr
    (ContinuousMap.HomotopyEquiv.refl Y)

/-! ## Two antipodal points removed from a sphere -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A chosen unit vector as a point of the unit sphere. -/
def polePoint (v : E) (hv : ‖v‖ = 1) : UnitSphere E :=
  ⟨v, by simpa [Metric.mem_sphere, dist_zero_right] using hv⟩

/-- The unit sphere with a chosen pole and its antipode removed. -/
abbrev TwoPoleComplement (v : E) (hv : ‖v‖ = 1) :=
  {x : UnitSphere E // x ≠ polePoint v hv ∧ x ≠ -(polePoint v hv)}

/-- Stereographic projection identifies a two-pole complement with the
punctured orthogonal coordinate space. -/
def twoPoleComplementHomeomorphPuncturedOrthogonal
    (v : E) (hv : ‖v‖ = 1) :
    TwoPoleComplement v hv ≃ₜ PuncturedSpace ((ℝ ∙ v)ᗮ) := by
  let north := polePoint v hv
  let south : UnitSphere E := -north
  let e := stereographic hv
  have hsouth : e south = 0 := by
    simpa [north, south, e, polePoint] using stereographic_apply_neg north
  have hsouth_source : south ∈ e.source := by
    simp only [e, stereographic_source, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have hvneg : v = -v := (congrArg Subtype.val h).symm
    have htwo : (2 : ℝ) • v = 0 := by
      calc
        (2 : ℝ) • v = v + v := two_smul ℝ v
        _ = -v + v := congrArg (fun z => z + v) hvneg
        _ = 0 := neg_add_cancel v
    have : v = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    rw [this, norm_zero] at hv
    norm_num at hv
  exact
    { toFun := fun x => ⟨e x.1, by
        intro hz
        apply x.2.2
        apply Subtype.ext
        calc
          x.1.1 = (e.symm (e x.1)).1 := congrArg Subtype.val (e.left_inv (by
            simpa [e, stereographic_source] using x.2.1)).symm
          _ = (e.symm 0).1 := by rw [hz]
          _ = south.1 := by
            have hi := e.left_inv hsouth_source
            rw [hsouth] at hi
            exact congrArg Subtype.val hi ⟩
      invFun := fun y => ⟨e.symm y.1, by
        constructor
        · change e.symm y.1 ≠ north
          have hsrc : e.symm y.1 ∈ e.source := e.map_target (by simp [e])
          simpa only [e, stereographic_source, Set.mem_compl_iff,
            Set.mem_singleton_iff] using hsrc
        · intro h
          apply y.2
          calc
            y.1 = e (e.symm y.1) := (e.right_inv (by simp [e])).symm
            _ = e south := congrArg e h
            _ = 0 := hsouth ⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact e.left_inv (by simpa [e, stereographic_source] using x.2.1)
      right_inv := fun y => by
        apply Subtype.ext
        exact e.right_inv (by simp [e])
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact e.continuousOn.comp_continuous continuous_subtype_val
          (fun x => by simpa [e, stereographic_source] using x.2.1)
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact e.symm.continuousOn.comp_continuous continuous_subtype_val
          (fun _ => by simp [e]) }

/-- Removing two antipodal points from a unit sphere leaves a space homotopy
equivalent to the unit sphere in the orthogonal complement of the pole. -/
def twoPoleComplementHomotopyEquivOrthogonalSphere
    (v : E) (hv : ‖v‖ = 1) :
    TwoPoleComplement v hv ≃ₕ UnitSphere ((ℝ ∙ v)ᗮ) :=
  (twoPoleComplementHomeomorphPuncturedOrthogonal v hv).toHomotopyEquiv.trans
    (unitSphereHomotopyEquivPuncturedSpace ((ℝ ∙ v)ᗮ)).symm

/-- The two-pole equivalence is preserved after taking a product with any
topological space. -/
def twoPoleComplementProductHomotopyEquiv
    (v : E) (hv : ‖v‖ = 1) (Y : Type*) [TopologicalSpace Y] :
    (TwoPoleComplement v hv × Y) ≃ₕ
      (UnitSphere ((ℝ ∙ v)ᗮ) × Y) :=
  (twoPoleComplementHomotopyEquivOrthogonalSphere v hv).prodCongr
    (ContinuousMap.HomotopyEquiv.refl Y)

#print axioms radialNormalize_unitSphereInclusion
#print axioms puncturedRadialHomotopy
#print axioms unitSphereHomotopyEquivPuncturedSpace
#print axioms unitSphereProductHomotopyEquivPuncturedSpaceProduct
#print axioms twoPoleComplementHomeomorphPuncturedOrthogonal
#print axioms twoPoleComplementHomotopyEquivOrthogonalSphere
#print axioms twoPoleComplementProductHomotopyEquiv

end ConstructionTargets.PuncturedNormedSpaceRadialEquivalence
