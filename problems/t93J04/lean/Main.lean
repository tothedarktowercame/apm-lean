import Mathlib
import ConstructionTargets.CoefficientSphereAntipodal
import ConstructionTargets.SingularHomologyHomotopy

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

open CategoryTheory CategoryTheory.Limits ConstructionTargets in
theorem apm_t93j04_id_ne_zero :
    𝟙 ((CoefficientCoordinateReflections.H ℤ 2).obj (TopCat.of apm_t93j04_Sphere)) ≠ 0 := by
  intro h
  have e := CoefficientFirstReflection.topIso ℤ 1
  have hz : IsZero ((CoefficientCoordinateReflections.H ℤ 2).obj (TopCat.of apm_t93j04_Sphere)) :=
    (IsZero.iff_id_eq_zero _).2 h
  have hz' : IsZero (ModuleCat.of ℤ ℤ) := hz.of_iso e.symm
  have := congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => f.hom (1 : ℤ))
    ((IsZero.iff_id_eq_zero _).1 hz')
  simp at this

theorem apm_t93j04 (p : apm_t93j04_Sphere) :
    ¬ (apm_t93j04_left p).Homotopic (apm_t93j04_right p) := by
  intro H
  have H' := (ContinuousMap.Homotopic.refl (ContinuousMap.fst : C(apm_t93j04_Sphere × apm_t93j04_Sphere, apm_t93j04_Sphere))).comp H
  have H'' : (ContinuousMap.id apm_t93j04_Sphere).Homotopic (ContinuousMap.const _ p) := by
    simpa [apm_t93j04_left, apm_t93j04_right] using H'
  have h1 := ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
    (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) H'' 2
  rw [ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_const_eq_zero _ _ _ (by omega)] at h1
  exact apm_t93j04_id_ne_zero (by simpa using h1)
