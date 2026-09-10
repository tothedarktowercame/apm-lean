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


namespace T96J05Counterexample
abbrev X := Metric.sphere (0 : apm_t96j05_E 2) 1
lemma norm_eq (x : X) : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
lemma embedded : apm_t96j05_IsEmbeddedSmoothSubmanifold (m := 1) X := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  letI : Fact (Module.finrank ℝ (apm_t96j05_E 2) = 1 + 1) := ⟨by simp⟩
  exact contMDiff_coe_sphere
lemma connected : IsConnected (Set.univ : Set X) := by
  have h : IsConnected X := isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  letI := isConnected_iff_connectedSpace.mp h
  exact isConnected_univ
noncomputable def levelHomeomorph : apm_t96j05_radialLevel X 1 ≃ₜ X where
  toFun := Subtype.val
  invFun := fun x => ⟨x, norm_eq x⟩
  left_inv := fun x => by rfl
  right_inv := fun x => rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _
lemma no_smooth_level (r : ℝ) (hne : Nonempty (apm_t96j05_radialLevel X r)) :
    ¬ apm_t96j05_IsSmoothRadialLevel (m := 1) X r := by
  obtain ⟨x⟩ := hne
  have hr : r = 1 := x.property.symm.trans (norm_eq x.val)
  subst r
  rintro ⟨charts, _⟩
  letI := charts
  letI : DiscreteTopology (apm_t96j05_radialLevel X 1) := ChartedSpace.discreteTopology (apm_t96j05_E 0) _
  letI : DiscreteTopology X := levelHomeomorph.discreteTopology
  have hsub := connected.isPreconnected.subsingleton
  let p : X := ⟨EuclideanSpace.single 0 1, by simp [X]⟩
  let q : X := ⟨EuclideanSpace.single 0 (-1), by simp [X]⟩
  have heq : p = q := hsub (Set.mem_univ p) (Set.mem_univ q)
  have := congrArg (fun x : X => x.val 0) heq
  norm_num [p, q] at this

theorem counterexample : ∃ (m n : ℕ) (X : Set (apm_t96j05_E n)),
    0 < m ∧ m ≤ n ∧ X.Nonempty ∧ IsConnected (Set.univ : Set X) ∧
    apm_t96j05_IsEmbeddedSmoothSubmanifold (m := m) X ∧
    ¬ (∃ r : ℝ, 0 < r ∧ Nonempty (apm_t96j05_radialLevel X r) ∧
      apm_t96j05_IsSmoothRadialLevel (m := m) X r) := by
  refine ⟨1, 2, X, by norm_num, by norm_num, ?_, connected, embedded, ?_⟩
  · exact ⟨EuclideanSpace.single 0 1, by simp [X]⟩
  · rintro ⟨r, _, hn, hs⟩
    exact no_smooth_level r hn hs
#print axioms counterexample
end T96J05Counterexample
