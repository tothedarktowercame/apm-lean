import ConstructionTargets.t97A07Closure

/-! # t97A07: critical values of a compact connected smooth manifold

The printed part (a) needs positive target dimension. We keep n arbitrary,
state nonemptiness only for 0 < n, and separately prove that the critical-value
set is empty for n = 0. This is a labelled corrected encoding, not a claim that
the literal unrestricted source is true. All remaining source hypotheses and
part (b) are retained. Criticality uses the actual manifold derivative.
-/
open scoped Manifold ContDiff
noncomputable section
namespace T97A07
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def criticalValues {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (E m) X] (f : X → E n) : Set (E n) :=
  {y | ∃ x, f x = y ∧ ¬ Function.Surjective (mfderiv 𝓘(ℝ,E m) 𝓘(ℝ,E n) f x)}

/-- Every derivative into the zero vector space is surjective, regardless of f. -/
theorem criticalValues_zero {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (E m) X] (f : X → E 0) : criticalValues (m := m) f = ∅ := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, _, hx⟩ := hy
    apply hx
    intro z
    have hzero : Subsingleton (TangentSpace 𝓘(ℝ,E 0) (f x)) := by
      change Subsingleton (E 0)
      infer_instance
    exact ⟨0, hzero.elim _ _⟩
  · intro h
    exact False.elim h

/-- In particular the printed nonemptiness conclusion cannot hold for n=0. -/
theorem not_nonempty_criticalValues_zero {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (E m) X] (f : X → E 0) : ¬ (criticalValues (m := m) f).Nonempty := by
  rw [criticalValues_zero (m := m)]
  exact Set.not_nonempty_empty
end T97A07
open T97A07

namespace t97A07Closure

/-- B4: the critical-value set is the compact image of the closed set of
critical points. -/
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
  exact isCompact_image_criticalPoints f hf

/-- B6: positive-dimensional targets have a critical value. -/
theorem criticalValues_nonempty_of_pos (m n : ℕ) {X : Type*}
    [TopologicalSpace X] [Nonempty X] [CompactSpace X]
    [ChartedSpace (E m) X] [IsManifold 𝓘(ℝ, E m) ∞ X]
    (f : X → E n)
    (hf : ContMDiff 𝓘(ℝ, E m) 𝓘(ℝ, E n) ∞ f)
    (hn : 0 < n) :
    (criticalValues (m := m) f).Nonempty := by
  obtain ⟨x, hx⟩ := exists_not_surjective_mfderiv_of_pos f hf hn
  exact ⟨f x, x, rfl, hx⟩

end t97A07Closure

/-- Corrected part (a), with the zero-dimensional exception exposed, and part (b). -/
theorem apm_t97a07 (m n : ℕ) {X : Type*}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [Nonempty X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace (E m) X] [IsManifold 𝓘(ℝ,E m) ∞ X]
    (f : X → E n) (hf : ContMDiff 𝓘(ℝ,E m) 𝓘(ℝ,E n) ∞ f) :
    IsCompact (criticalValues (m := m) f) ∧
    (0 < n → (criticalValues (m := m) f).Nonempty) ∧
    (n = 0 → criticalValues (m := m) f = ∅) ∧
    (1 < n → (∃ x y, f x ≠ f y) → (criticalValues (m := m) f).Infinite) := by
  sorry

#print axioms T97A07.criticalValues_zero
#print axioms T97A07.not_nonempty_criticalValues_zero
#print axioms t97A07Closure.isCompact_criticalValues
#print axioms t97A07Closure.criticalValues_nonempty_of_pos
#print axioms apm_t97a07
