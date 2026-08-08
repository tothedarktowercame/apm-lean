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

/-- A nonzero point supplies a positive attained radial level. This separates
the elementary existence part from Sard and regular-level smoothness. -/
lemma apm_t96j05_exists_positive_nonempty_radialLevel
    {n : ℕ} {X : Set (apm_t96j05_E n)}
    (hXnz : ∃ x : X, (x.1 : apm_t96j05_E n) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Nonempty (apm_t96j05_radialLevel X r) := by
  obtain ⟨x, hx⟩ := hXnz
  refine ⟨‖x.1‖, norm_pos_iff.mpr hx, ⟨x, rfl⟩⟩

theorem apm_t96j05
    (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (X : Set (apm_t96j05_E n))
    (hXne : X.Nonempty)
    (hXconn : IsConnected (Set.univ : Set X))
    (hX : apm_t96j05_IsEmbeddedSmoothSubmanifold (m := m) X) :
    ∃ r : ℝ, 0 < r ∧
      Nonempty (apm_t96j05_radialLevel X r) ∧
      apm_t96j05_IsSmoothRadialLevel (m := m) X r := by
  /-
  CLOSER HOP 1 boundary: the intended proof applies Sard to the smooth norm
  (or squared norm) restricted to the positive-dimensional manifold `X`, then
  uses the regular-level-set theorem to install a manifold structure of model
  dimension `m - 1` on the literal subtype `apm_t96j05_radialLevel X r`.
  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, Sard/transversality
  siblings, Mathlib's vector-space Sard, `mfderiv`, submersion, preimage, and
  subtype-manifold APIs, and git history found no manifold-domain Sard theorem
  or constructor producing the exact `ChartedSpace`/`IsManifold` conclusion.

  CLOSER HOP 2: `apm_t96j05_exists_positive_nonempty_radialLevel` now compiles
  the full elementary part: any nonzero `x : X` yields radius `‖x‖ > 0` and an
  inhabitant of the corresponding literal level subtype. This exposes an
  additional prerequisite previously hidden inside the global sorry: derive a
  nonzero point from `0 < m`, nonemptiness, and the `m`-manifold structure
  (equivalently, rule out a positive-dimensional manifold whose underlying
  subtype is the singleton origin).

  Going beyond the prior search, the recently strengthened `t92J07` artifact
  was inspected. It compiles countable avoidance once nullity of manifold
  critical values is assumed, but the manifold-Sard nullity itself remains
  absent and the result is local to that problem. Mathlib's regular-level and
  implicit-function APIs provide local charts after a surjective derivative,
  but no assembled global charted-space instance for this exact fiber subtype.
  Thus the remaining bridges are: obtain a nonzero point from positive
  manifold dimension; obtain a positive regular value of the radial function;
  and globalize its local regular-level charts. The frozen statement is
  unchanged.
  -/
  sorry
