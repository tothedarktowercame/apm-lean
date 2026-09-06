import Mathlib

/-!
# APM t93J04 — the two sphere factors are not homotopic

The sphere is the literal unit sphere in Euclidean three-space.  The two maps
are the inclusions into opposite factors at the chosen point.
-/

noncomputable section

abbrev apm_t93j04_Sphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def apm_t93j04_left (p : apm_t93j04_Sphere) :
    C(apm_t93j04_Sphere, apm_t93j04_Sphere × apm_t93j04_Sphere) :=
  ContinuousMap.prodMk (ContinuousMap.id _) (ContinuousMap.const _ p)

def apm_t93j04_right (p : apm_t93j04_Sphere) :
    C(apm_t93j04_Sphere, apm_t93j04_Sphere × apm_t93j04_Sphere) :=
  ContinuousMap.prodMk (ContinuousMap.const _ p) (ContinuousMap.id _)

theorem apm_t93j04 (p : apm_t93j04_Sphere) :
    ¬ (apm_t93j04_left p).Homotopic (apm_t93j04_right p) := by
  sorry
