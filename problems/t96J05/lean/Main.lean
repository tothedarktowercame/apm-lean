import Mathlib

/-!
# APM t96J05 — a regular radial level of an embedded manifold

## Statement repairs

None.

## Encoding note

The object is an actual subset of Euclidean space. Its subtype carries a
positive-dimensional smooth manifold structure and its inclusion into the
ambient Euclidean space is smooth. The conclusion is the literal nonempty
intersection with an origin-centred sphere, equipped with the expected
codimension-one manifold structure. No regular value or Sard consequence is
assumed.
-/

open scoped ContDiff Manifold

noncomputable section

abbrev apm_t96j05_E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev apm_t96j05_I (n : ℕ) := 𝓘(ℝ, apm_t96j05_E n)

def apm_t96j05_IsEmbeddedSmoothSubmanifold {m n : ℕ}
    (X : Set (apm_t96j05_E n)) : Prop :=
  ∃ charts : ChartedSpace (apm_t96j05_E m) X,
    let _ := charts
    IsManifold (apm_t96j05_I m) ⊤ X ∧
    ContMDiff (apm_t96j05_I m) (apm_t96j05_I n) ⊤
      (fun x : X ↦ x.1)

/-- The actual intersection of `X` with the sphere of radius `r`. -/
abbrev apm_t96j05_radialLevel {n : ℕ}
    (X : Set (apm_t96j05_E n)) (r : ℝ) :=
  {x : X // ‖x.1‖ = r}

def apm_t96j05_IsSmoothRadialLevel {m n : ℕ}
    (X : Set (apm_t96j05_E n)) (r : ℝ) : Prop :=
  ∃ charts : ChartedSpace (apm_t96j05_E (m - 1))
      (apm_t96j05_radialLevel X r),
    let _ := charts
    IsManifold (apm_t96j05_I (m - 1)) ⊤
      (apm_t96j05_radialLevel X r)

theorem apm_t96j05
    (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (X : Set (apm_t96j05_E n))
    (hXne : X.Nonempty)
    (hXconn : IsConnected (Set.univ : Set X))
    (hX : apm_t96j05_IsEmbeddedSmoothSubmanifold (m := m) X) :
    ∃ r : ℝ, 0 < r ∧
      Nonempty (apm_t96j05_radialLevel X r) ∧
      apm_t96j05_IsSmoothRadialLevel (m := m) X r := by
  sorry
