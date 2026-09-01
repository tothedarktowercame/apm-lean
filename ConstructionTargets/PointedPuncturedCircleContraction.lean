import ConstructionTargets.PointWedgeQuotient
import ConstructionTargets.CircleMetricFundamentalGroup
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set
open unitInterval
open ConstructionTargets.CircleMetricFundamentalGroup

noncomputable section

set_option maxHeartbeats 800000

namespace ConstructionTargets.PointedPuncturedCircleContraction

/-- An explicit contraction from the identity to the chosen point, relative
to that point throughout the homotopy. -/
structure PointedContraction (X : Type*) [TopologicalSpace X] (x₀ : X) where
  homotopy : ContinuousMap.Homotopy
    (ContinuousMap.id X) (ContinuousMap.const X x₀)
  fixed : ∀ t : I, homotopy (t, x₀) = x₀

namespace PointedContraction

/-- Product of pointed contractions, with the same time parameter in both
coordinates. -/
def prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ : X} {y₀ : Y} (hX : PointedContraction X x₀)
    (hY : PointedContraction Y y₀) : PointedContraction (X × Y) (x₀, y₀) where
  homotopy :=
    { toFun := fun p => (hX.homotopy (p.1, p.2.1), hY.homotopy (p.1, p.2.2))
      continuous_toFun :=
        (hX.homotopy.continuous.comp
          (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (hY.homotopy.continuous.comp
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
      map_zero_left := by intro p; ext <;> simp
      map_one_left := by intro p; ext <;> simp }
  fixed := by
    intro t
    ext
    · exact hX.fixed t
    · exact hY.fixed t

@[simp] theorem prod_apply {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ : X} {y₀ : Y} (hX : PointedContraction X x₀)
    (hY : PointedContraction Y y₀) (t : I) (p : X × Y) :
    (hX.prod hY).homotopy (t, p) =
      (hX.homotopy (t, p.1), hY.homotopy (t, p.2)) := by
  rfl

end PointedContraction

abbrev PuncturedCircle := {z : Circle // (z : ℂ) ≠ -1}

def puncturedCircleBase : PuncturedCircle := ⟨1, by norm_num⟩

abbrev PuncturedMetricCircle :=
  {z : Metric.sphere (0 : ℂ) 1 // (z : ℂ) ≠ -1}

def puncturedCircleHomeomorphPuncturedMetricCircle :
    PuncturedCircle ≃ₜ PuncturedMetricCircle where
  toFun z := ⟨metricCircleHomeomorphCircle.symm z.1, z.2⟩
  invFun z := ⟨metricCircleHomeomorphCircle z.1, z.2⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem puncturedCirclePole_norm : ‖(-1 : ℂ)‖ = 1 := by simp

def puncturedMetricCircleCoordinate
    (z : PuncturedMetricCircle) : (ℝ ∙ (-1 : ℂ))ᗮ :=
  stereographic puncturedCirclePole_norm z.1

/-- Stereographic projection from `-1`, restricted to its source. The manual
bundling keeps the evaluation formula transparent to later quotient code. -/
def puncturedMetricCircleHomeomorphOrthogonal :
    PuncturedMetricCircle ≃ₜ (ℝ ∙ (-1 : ℂ))ᗮ where
  toFun := puncturedMetricCircleCoordinate
  invFun w := ⟨(stereographic puncturedCirclePole_norm).symm w, by
    have hs : (stereographic puncturedCirclePole_norm).symm w ∈
        (stereographic puncturedCirclePole_norm).source :=
      (stereographic puncturedCirclePole_norm).map_target (by
        simp [stereographic_target])
    rw [stereographic_source] at hs
    intro h
    apply hs
    apply Subtype.ext
    exact h⟩
  left_inv z := by
    apply Subtype.ext
    apply (stereographic puncturedCirclePole_norm).left_inv
    rw [stereographic_source]
    intro h
    exact z.2 (congrArg Subtype.val h)
  right_inv w := by
    apply (stereographic puncturedCirclePole_norm).right_inv
    simp [stereographic_target]
  continuous_toFun := by
    apply (stereographic puncturedCirclePole_norm).continuousOn.comp_continuous
      continuous_subtype_val
    intro z
    rw [stereographic_source]
    intro h
    exact z.2 (congrArg Subtype.val h)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (stereographic puncturedCirclePole_norm).symm.continuousOn.comp_continuous
      continuous_id
    intro w
    simp [stereographic_target]

/-- The requested punctured `Circle` model transported to stereographic
coordinates. -/
def puncturedCircleHomeomorphOrthogonal :
    PuncturedCircle ≃ₜ (ℝ ∙ (-1 : ℂ))ᗮ :=
  puncturedCircleHomeomorphPuncturedMetricCircle.trans
    puncturedMetricCircleHomeomorphOrthogonal

def puncturedMetricCircleBase : PuncturedMetricCircle :=
  ⟨⟨1, by simp⟩, by norm_num⟩

theorem puncturedMetricCircleHomeomorphOrthogonal_base :
    puncturedMetricCircleHomeomorphOrthogonal
      puncturedMetricCircleBase = 0 := by
  change stereographic puncturedCirclePole_norm
    (⟨1, by simp⟩ : Metric.sphere (0 : ℂ) 1) = 0
  let pole : Metric.sphere (0 : ℂ) 1 := ⟨-1, by simp⟩
  have harg : (⟨1, by simp⟩ : Metric.sphere (0 : ℂ) 1) = -pole := by
    apply Subtype.ext
    norm_num [pole]
  rw [harg]
  exact stereographic_apply_neg pole

/-- The distinguished point `1` is the antipode of the projection pole and
therefore has stereographic coordinate zero. -/
theorem puncturedCircleHomeomorphOrthogonal_base :
    puncturedCircleHomeomorphOrthogonal puncturedCircleBase = 0 := by
  exact puncturedMetricCircleHomeomorphOrthogonal_base

/-- The explicit contraction formula before it is bundled as a homotopy. -/
def puncturedCircleContractionMap (p : I × PuncturedCircle) :
    PuncturedCircle :=
  puncturedCircleHomeomorphOrthogonal.symm
    ((1 - (p.1 : ℝ)) • puncturedCircleHomeomorphOrthogonal p.2)

theorem puncturedCircleContractionMap_continuous :
    Continuous puncturedCircleContractionMap := by
  apply puncturedCircleHomeomorphOrthogonal.symm.continuous.comp
  exact (continuous_const.sub
    (continuous_subtype_val.comp continuous_fst)).smul
      (puncturedCircleHomeomorphOrthogonal.continuous.comp continuous_snd)

@[simp] theorem puncturedCircleContractionMap_zero (z : PuncturedCircle) :
    puncturedCircleContractionMap (0, z) = z := by
  simp [puncturedCircleContractionMap]

@[simp] theorem puncturedCircleContractionMap_one (z : PuncturedCircle) :
    puncturedCircleContractionMap (1, z) = puncturedCircleBase := by
  apply puncturedCircleHomeomorphOrthogonal.injective
  simp [puncturedCircleContractionMap,
    puncturedCircleHomeomorphOrthogonal_base]

@[simp] theorem puncturedCircleContractionMap_fixed (t : I) :
    puncturedCircleContractionMap (t, puncturedCircleBase) =
      puncturedCircleBase := by
  apply puncturedCircleHomeomorphOrthogonal.injective
  simp [puncturedCircleContractionMap,
    puncturedCircleHomeomorphOrthogonal_base]

/-- Straight-line contraction in stereographic coordinates, transported back
to the punctured circle. Time zero is the identity and time one is constant
at `1`. -/
def puncturedCirclePointedContraction :
    PointedContraction PuncturedCircle puncturedCircleBase where
  homotopy :=
    { toFun := puncturedCircleContractionMap
      continuous_toFun := puncturedCircleContractionMap_continuous
      map_zero_left := puncturedCircleContractionMap_zero
      map_one_left := puncturedCircleContractionMap_one }
  fixed := puncturedCircleContractionMap_fixed

@[simp] theorem puncturedCirclePointedContraction_apply
    (t : I) (z : PuncturedCircle) :
    puncturedCirclePointedContraction.homotopy (t, z) =
      puncturedCircleHomeomorphOrthogonal.symm
        ((1 - (t : ℝ)) • puncturedCircleHomeomorphOrthogonal z) := rfl

@[simp] theorem puncturedCirclePointedContraction_zero
    (z : PuncturedCircle) :
    puncturedCirclePointedContraction.homotopy (0, z) = z := by simp

@[simp] theorem puncturedCirclePointedContraction_one
    (z : PuncturedCircle) :
    puncturedCirclePointedContraction.homotopy (1, z) =
      puncturedCircleBase := by simp

@[simp] theorem puncturedCirclePointedContraction_fixed (t : I) :
    puncturedCirclePointedContraction.homotopy
      (t, puncturedCircleBase) = puncturedCircleBase :=
  puncturedCirclePointedContraction.fixed t

def puncturedTorusPointedContraction :
    PointedContraction (PuncturedCircle × PuncturedCircle)
      (puncturedCircleBase, puncturedCircleBase) :=
  puncturedCirclePointedContraction.prod puncturedCirclePointedContraction

@[simp] theorem puncturedTorusPointedContraction_apply
    (t : I) (z : PuncturedCircle × PuncturedCircle) :
    puncturedTorusPointedContraction.homotopy (t, z) =
      (puncturedCirclePointedContraction.homotopy (t, z.1),
       puncturedCirclePointedContraction.homotopy (t, z.2)) := by
  rfl

@[simp] theorem puncturedTorusPointedContraction_fixed (t : I) :
    puncturedTorusPointedContraction.homotopy
      (t, (puncturedCircleBase, puncturedCircleBase)) =
        (puncturedCircleBase, puncturedCircleBase) :=
  puncturedTorusPointedContraction.fixed t

/-- The literal torus neighborhood anticipated by the quotient consumer. -/
def torusPuncturedNeighborhood : Set (Circle × Circle) :=
  {z | (z.1 : ℂ) ≠ -1 ∧ (z.2 : ℂ) ≠ -1}

def puncturedTorusHomeomorphNeighborhood :
    PuncturedCircle × PuncturedCircle ≃ₜ torusPuncturedNeighborhood where
  toFun z := ⟨(z.1.1, z.2.1), ⟨z.1.2, z.2.2⟩⟩
  invFun z := (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
  left_inv z := rfl
  right_inv z := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    apply Continuous.prodMk
    · exact Continuous.subtype_mk
        (continuous_fst.comp continuous_subtype_val) _
    · exact Continuous.subtype_mk
        (continuous_snd.comp continuous_subtype_val) _

#print axioms PointedContraction.prod
#print axioms puncturedCircleHomeomorphOrthogonal_base
#print axioms puncturedCirclePointedContraction
#print axioms puncturedTorusPointedContraction
#print axioms puncturedTorusHomeomorphNeighborhood

end ConstructionTargets.PointedPuncturedCircleContraction
