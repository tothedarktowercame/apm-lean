import Mathlib
import ConstructionTargets.ManifoldFormTargets

/-! The standard R²/Z² torus, its required quotient smooth atlas, and integration
in its oriented fundamental square. No atlas inhabitant is postulated. -/
open scoped Manifold ContDiff
noncomputable section
namespace ConstructionTargets.TorusFormTargets
open ManifoldFormTargets
abbrev Plane := Fin 2 → ℝ
abbrev Torus := Fin 2 → AddCircle (1 : ℝ)
def projection (x : Plane) : Torus := fun i => (x i : AddCircle (1 : ℝ))

structure SmoothAtlas where
  charts : ChartedSpace Plane Torus
  smooth : letI := charts; IsManifold 𝓘(ℝ,Plane) ∞ Torus
  quotient_localDiffeomorph : letI := charts;
    IsLocalDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ projection

def areaForm : Plane [⋀^Fin 2]→L[ℝ] ℝ where
  toAlternatingMap := Matrix.detRowAlternating
  cont := by change Continuous (fun v : Fin 2 → Plane => Matrix.det v); fun_prop

def sourceForm : Form Plane Plane 2 := fun p =>
  (Real.sin (2 * Real.pi * p 0) ^ 2 * Real.cos (2 * Real.pi * p 1) ^ 2) • areaForm

def primitive : Form Plane Plane 1 := fun p =>
  ((p 0 / 2 - Real.sin (4 * Real.pi * p 0) / (8 * Real.pi)) *
    Real.cos (2 * Real.pi * p 1) ^ 2) •
    (ContinuousAlternatingMap.ofSubsingleton ℝ Plane ℝ (0 : Fin 1)
      (ContinuousLinearMap.proj (1 : Fin 2)))

/-- Integration of the pullback over the positively oriented fundamental domain. -/
def torusIntegral [ChartedSpace Plane Torus] (form : Form Plane Torus 2) : ℝ :=
  ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
    (pullback (E := Plane) projection form) ![x,y] ![Pi.single 0 1, Pi.single 1 1]

/-- The derivative of t ↦ (1-t)a+tb is b-a. -/
def segmentIntegral (form : Form Plane Plane 1) (a b : Plane) : ℝ :=
  ∫ t in (0 : ℝ)..1, form ((1-t) • a + t • b) ![b-a]

def parallelogramIntegral (form : Form Plane Plane 1) : ℝ :=
  segmentIntegral form ![0,0] ![1,0] + segmentIntegral form ![1,0] ![2,1] +
  segmentIntegral form ![2,1] ![1,1] + segmentIntegral form ![1,1] ![0,0]

end ConstructionTargets.TorusFormTargets
