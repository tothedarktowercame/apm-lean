import ConstructionTargets.t97A07Closure

/-! # t97A07: critical values of a compact connected smooth manifold

The analytic manifold foundations are already proved, without placeholders, in
`ConstructionTargets.t97A07Closure`.  The only remaining lemma is the
connected-complement argument for infinitude of the critical-value set.
-/

open scoped Manifold ContDiff
noncomputable section

namespace T97A07

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def criticalValues {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (E m) X] (f : X → E n) : Set (E n) :=
  {y | ∃ x, f x = y ∧ ¬ Function.Surjective
    (mfderiv 𝓘(ℝ, E m) 𝓘(ℝ, E n) f x)}

theorem criticalValues_zero {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (E m) X] (f : X → E 0) : criticalValues (m := m) f = ∅ := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, _, hx⟩ := hy
    apply hx
    intro z
    have hzero : Subsingleton (TangentSpace 𝓘(ℝ, E 0) (f x)) := by
      change Subsingleton (E 0)
      infer_instance
    exact ⟨0, hzero.elim _ _⟩
  · intro h
    exact False.elim h

end T97A07

open T97A07

namespace t97A07Blueprint

/-- The critical-value set is the compact image of the closed set of critical
points.  This is a proved adapter to the sorry-free closure foundation. -/
theorem isCompact_criticalValues (m n : ℕ) {X : Type*}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [Nonempty X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace (E m) X] [IsManifold 𝓘(ℝ, E m) ∞ X]
    (f : X → E n)
    (hf : ContMDiff 𝓘(ℝ, E m) 𝓘(ℝ, E n) ∞ f) :
    IsCompact (criticalValues (m := m) f) := by
  rw [show criticalValues (m := m) f =
      f '' {x | ¬ Function.Surjective
        (mfderiv 𝓘(ℝ, E m) 𝓘(ℝ, E n) f x)} by
    ext y
    constructor
    · rintro ⟨x, hxy, hx⟩
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hxy, hx⟩]
  exact t97A07Closure.isCompact_image_criticalPoints f hf

/-- Positive-dimensional targets have a critical value.  This is a proved
adapter to the coordinate-maximum argument in the closure foundation. -/
theorem criticalValues_nonempty_of_pos (m n : ℕ) {X : Type*}
    [TopologicalSpace X] [Nonempty X] [CompactSpace X]
    [ChartedSpace (E m) X] [IsManifold 𝓘(ℝ, E m) ∞ X]
    (f : X → E n)
    (hf : ContMDiff 𝓘(ℝ, E m) 𝓘(ℝ, E n) ∞ f)
    (hn : 0 < n) :
    (criticalValues (m := m) f).Nonempty := by
  obtain ⟨x, hx⟩ :=
    t97A07Closure.exists_not_surjective_mfderiv_of_pos f hf hn
  exact ⟨f x, x, rfl, hx⟩

/-- Seat (claude-14 split): a compact connected subset of `ℝⁿ`, `n ≥ 2`, with two
distinct points has infinite frontier.  If its interior is empty the frontier is
the set itself (connected with two points, hence infinite); otherwise interior and
exterior are nonempty open sets covering `ℝⁿ ∖ frontier`, but `ℝⁿ` minus a finite
set is connected for `n ≥ 2` (`Set.Countable.isPathConnected_compl_of_one_lt_rank`). -/
theorem t97A07_frontier_infinite (n : ℕ) (hn : 1 < n) (K : Set (E n))
    (hK : IsCompact K) (hconn : IsConnected K) (hab : ∃ a ∈ K, ∃ b ∈ K, a ≠ b) :
    (frontier K).Infinite := by
  sorry

/-- Seat (claude-14 split): at a point where the manifold derivative is
surjective, `f` maps every neighbourhood onto a neighbourhood of `f x`, so
`f x` is an interior point of the range (in the chart at `x`:
`HasStrictFDerivAt.map_nhds_eq_of_surj`). -/
theorem t97A07_regular_image_interior (m n : ℕ) {X : Type*}
    [TopologicalSpace X] [ChartedSpace (E m) X] [IsManifold 𝓘(ℝ, E m) ∞ X]
    (f : X → E n) (hf : ContMDiff 𝓘(ℝ, E m) 𝓘(ℝ, E n) ∞ f) (x : X)
    (hx : Function.Surjective (mfderiv 𝓘(ℝ, E m) 𝓘(ℝ, E n) f x)) :
    f x ∈ interior (Set.range f) := by
  sorry

/-- If the target has dimension at least two and the map is nonconstant, its
set of critical values is infinite. -/
theorem criticalValues_infinite_of_one_lt_of_nonconstant
    (m n : ℕ) {X : Type*}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [Nonempty X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace (E m) X] [IsManifold 𝓘(ℝ, E m) ∞ X]
    (f : X → E n)
    (hf : ContMDiff 𝓘(ℝ, E m) 𝓘(ℝ, E n) ∞ f)
    (hn : 1 < n) (hnotconst : ∃ x y, f x ≠ f y) :
    (criticalValues (m := m) f).Infinite := by
  have hcont : Continuous f := hf.continuous
  have hK : IsCompact (Set.range f) := isCompact_range hcont
  have hconn : IsConnected (Set.range f) := isConnected_range hcont
  obtain ⟨x, y, hxy⟩ := hnotconst
  have hfr := t97A07_frontier_infinite n hn (Set.range f) hK hconn
    ⟨f x, ⟨x, rfl⟩, f y, ⟨y, rfl⟩, hxy⟩
  refine hfr.mono ?_
  intro v hv
  have hvK : v ∈ Set.range f := by
    have := frontier_subset_closure hv
    rwa [hK.isClosed.closure_eq] at this
  obtain ⟨z, rfl⟩ := hvK
  refine ⟨z, rfl, fun hsurj => ?_⟩
  have hint := t97A07_regular_image_interior m n f hf z hsurj
  exact (Set.disjoint_left.mp disjoint_interior_frontier) hint hv

end t97A07Blueprint

theorem apm_t97a07 (m n : ℕ) {X : Type*}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [Nonempty X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace (E m) X] [IsManifold 𝓘(ℝ,E m) ∞ X]
    (f : X → E n) (hf : ContMDiff 𝓘(ℝ,E m) 𝓘(ℝ,E n) ∞ f) :
    IsCompact (criticalValues (m := m) f) ∧
    (0 < n → (criticalValues (m := m) f).Nonempty) ∧
    (n = 0 → criticalValues (m := m) f = ∅) ∧
    (1 < n → (∃ x y, f x ≠ f y) →
      (criticalValues (m := m) f).Infinite) := by
  refine ⟨t97A07Blueprint.isCompact_criticalValues m n f hf, ?_, ?_, ?_⟩
  · exact t97A07Blueprint.criticalValues_nonempty_of_pos m n f hf
  · intro hn
    subst n
    exact T97A07.criticalValues_zero f
  · exact t97A07Blueprint.criticalValues_infinite_of_one_lt_of_nonconstant
      m n f hf

#print axioms apm_t97a07
