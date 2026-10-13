import Mathlib
import ConstructionTargets.RadialSquaredFiber
import ConstructionTargets.ManifoldRegularFiberGlobalAtlas
import ConstructionTargets.TransverseIncidenceChosenAtlas

/-! # Blueprint for APM t96J05 -/

open scoped ContDiff Manifold

noncomputable section

abbrev apm_t96j05_E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev apm_t96j05_I (n : ℕ) := 𝓘(ℝ, apm_t96j05_E n)

def apm_t96j05_IsEmbeddedSmoothSubmanifold {m n : ℕ}
    (X : Set (apm_t96j05_E n)) : Prop :=
  ∃ charts : ChartedSpace (apm_t96j05_E m) X,
    let _ := charts
    IsManifold (apm_t96j05_I m) ∞ X ∧
    ContMDiff (apm_t96j05_I m) (apm_t96j05_I n) ∞
      (fun x : X ↦ x.1)

abbrev apm_t96j05_radialLevel {n : ℕ}
    (X : Set (apm_t96j05_E n)) (r : ℝ) :=
  {x : X // ‖x.1‖ = r}

def apm_t96j05_IsEmbeddedSmoothRadialLevel {m n : ℕ}
    (X : Set (apm_t96j05_E n)) (r : ℝ) : Prop :=
  ∃ k : ℕ, k ≤ m ∧ ∃ charts : ChartedSpace (apm_t96j05_E k)
      (apm_t96j05_radialLevel X r),
    letI := charts
    IsManifold (apm_t96j05_I k) ∞
        (apm_t96j05_radialLevel X r) ∧
      ContMDiff (apm_t96j05_I k) (apm_t96j05_I n) ∞
        (fun x : apm_t96j05_radialLevel X r ↦ x.1.1)

/-- The constant-radius branch: the radial level is all of `X`, so its
existing atlas and smooth ambient inclusion transport to the literal subtype. -/
-- BEGIN SEAT AREA
theorem apm_t96j05_constant_radius_level
    {m n : ℕ} {X : Set (apm_t96j05_E n)}
    (hX : apm_t96j05_IsEmbeddedSmoothSubmanifold (m := m) X)
    {r : ℝ} (hr : 0 < r) (hall : ∀ x : X, ‖x.1‖ = r) :
    Nonempty X →
      Nonempty (apm_t96j05_radialLevel X r) ∧
      apm_t96j05_IsEmbeddedSmoothRadialLevel (m := m) X r := by
  sorry
-- END SEAT AREA

/-- LIBRARY (manifold Sard plus connected-image selection).  For a smooth
squared-radius map which is not constant on a positive sphere, choose an
attained positive radius at which its manifold derivative is surjective. -/
theorem apm_t96j05_exists_regular_radius
    {m n : ℕ} (hm : 0 < m) {X : Set (apm_t96j05_E n)}
    [Nonempty X] [ChartedSpace (apm_t96j05_E m) X]
    [IsManifold (apm_t96j05_I m) ∞ X]
    (hconn : IsConnected (Set.univ : Set X))
    (hsm : ContMDiff (apm_t96j05_I m) 𝓘(ℝ, ℝ) ∞
      (fun x : X => ‖x.1‖ ^ 2))
    (hnconst : ¬ ∃ r : ℝ, 0 < r ∧ ∀ x : X, ‖x.1‖ = r) :
    ∃ r : ℝ, 0 < r ∧
      Nonempty (apm_t96j05_radialLevel X r) ∧
      ∀ x : X, ‖x.1‖ ^ 2 = r ^ 2 →
        Function.Surjective
          (mfderiv (apm_t96j05_I m) 𝓘(ℝ, ℝ)
            (fun y : X => ‖y.1‖ ^ 2) x) := by
  sorry

/-- A positive attained regular squared-radius fiber has the required global
atlas and smooth inclusion after fixed-model and predicate transport. -/
theorem apm_t96j05_regular_radius_level
    {m n : ℕ} {X : Set (apm_t96j05_E n)}
    [ChartedSpace (apm_t96j05_E m) X]
    [IsManifold (apm_t96j05_I m) ∞ X]
    (hinc : ContMDiff (apm_t96j05_I m) (apm_t96j05_I n) ∞
      (fun x : X ↦ x.1))
    {r : ℝ} (hr : 0 < r)
    (hlevel : Nonempty (apm_t96j05_radialLevel X r))
    (hsm : ContMDiff (apm_t96j05_I m) 𝓘(ℝ, ℝ) ∞
      (fun x : X => ‖x.1‖ ^ 2))
    (hreg : ∀ x : X, ‖x.1‖ ^ 2 = r ^ 2 →
      Function.Surjective
        (mfderiv (apm_t96j05_I m) 𝓘(ℝ, ℝ)
          (fun y : X => ‖y.1‖ ^ 2) x)) :
    apm_t96j05_IsEmbeddedSmoothRadialLevel (m := m) X r := by
  sorry

theorem apm_t96j05
    (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (X : Set (apm_t96j05_E n))
    (hXne : X.Nonempty)
    (hXconn : IsConnected (Set.univ : Set X))
    (hX : apm_t96j05_IsEmbeddedSmoothSubmanifold (m := m) X) :
    ∃ r : ℝ, 0 < r ∧
      Nonempty (apm_t96j05_radialLevel X r) ∧
      apm_t96j05_IsEmbeddedSmoothRadialLevel (m := m) X r := by
  have _ := hmn
  rcases hX with ⟨charts, hman, hinc⟩
  letI : ChartedSpace (apm_t96j05_E m) X := charts
  letI : IsManifold (apm_t96j05_I m) ∞ X := hman
  letI : Nonempty X := hXne.to_subtype
  by_cases hc : ∃ r : ℝ, 0 < r ∧ ∀ x : X, ‖x.1‖ = r
  · rcases hc with ⟨r, hr, hall⟩
    refine ⟨r, hr, ?_⟩
    exact apm_t96j05_constant_radius_level
      ⟨charts, hman, hinc⟩ hr hall inferInstance
  · have hsm : ContMDiff (apm_t96j05_I m) 𝓘(ℝ, ℝ) ∞
        (fun x : X => ‖x.1‖ ^ 2) := by
      exact (contDiff_norm_sq ℝ).contMDiff.comp hinc
    rcases apm_t96j05_exists_regular_radius hm hXconn hsm hc with
      ⟨r, hr, hlevel, hreg⟩
    exact ⟨r, hr, hlevel,
      apm_t96j05_regular_radius_level hinc hr hlevel hsm hreg⟩

#print axioms apm_t96j05
