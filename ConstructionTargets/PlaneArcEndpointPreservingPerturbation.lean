import ConstructionTargets.PlaneArcContainedSmallTranslations

noncomputable section
open Set
open scoped ContDiff

namespace PlaneArcEndpointPreservingPerturbation

abbrev Plane := ℝ × ℝ

def endpointWeight (t : ℝ) : ℝ := t * (1 - t)

def perturb (a : ℝ → Plane) (v : Plane) (t : ℝ) : Plane :=
  a t + endpointWeight t • v

@[simp] theorem endpointWeight_zero : endpointWeight 0 = 0 := by
  simp [endpointWeight]

@[simp] theorem endpointWeight_one : endpointWeight 1 = 0 := by
  simp [endpointWeight]

@[simp] theorem perturb_zero (a : ℝ → Plane) (v : Plane) :
    perturb a v 0 = a 0 := by
  simp [perturb]

@[simp] theorem perturb_one (a : ℝ → Plane) (v : Plane) :
    perturb a v 1 = a 1 := by
  simp [perturb]

theorem endpointWeight_contDiff : ContDiff ℝ ∞ endpointWeight := by
  unfold endpointWeight
  fun_prop

theorem perturb_contDiffOn (a : ℝ → Plane) (v : Plane) (U : Set ℝ)
    (ha : ContDiffOn ℝ ∞ a U) :
    ContDiffOn ℝ ∞ (perturb a v) U := by
  exact ha.add (endpointWeight_contDiff.contDiffOn.smul contDiffOn_const)

#print axioms perturb_zero
#print axioms perturb_one
#print axioms perturb_contDiffOn

end PlaneArcEndpointPreservingPerturbation
