import Mathlib
import ConstructionTargets.Surfaces

/-!
# APM t91J05 — finite covers of the genus-three orientable surface

The two remaining obligations are deliberately stated as independent library
boundaries: recognition of an arbitrary connected finite cover, and an
explicit connected finite cover of every positive degree.
-/

open Set ConstructionTargets.Surfaces

noncomputable section

abbrev apm_t91J05_Surface (g : ℕ) := Surface true g

def apm_t91J05_IsFiniteCover
    (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ p : X → apm_t91J05_Surface 3,
    IsCoveringMap p ∧ Function.Surjective p ∧
    ∀ s : apm_t91J05_Surface 3, (p ⁻¹' ({s} : Set _)).Finite

/-- The finite-cover predicate is invariant under replacing its source by a
homeomorphic space. -/
lemma apm_t91J05_isFiniteCover_of_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (hY : apm_t91J05_IsFiniteCover Y) :
    apm_t91J05_IsFiniteCover X := by
  obtain ⟨p, hpcover, hpsurj, hpfinite⟩ := hY
  refine ⟨p ∘ e, hpcover.comp_homeomorph e, hpsurj.comp e.surjective, ?_⟩
  intro s
  rw [show (p ∘ e) ⁻¹' ({s} : Set _) = e ⁻¹' (p ⁻¹' ({s} : Set _)) by
    ext x
    rfl]
  exact (hpfinite s).preimage e.injective.injOn

/-- The Euler-characteristic arithmetic behind the odd-genus formula. -/
lemma apm_t91J05_eulerCharacteristic_odd_genus (n : ℕ) :
    eulerCharacteristic true (2 * n + 1) =
      (n : ℤ) * eulerCharacteristic true 3 := by
  simp [eulerCharacteristic]
  omega

/-- LIBRARY: recognition and Euler-characteristic multiplication for a
connected finite cover of the concrete genus-three polygon surface. -/
theorem apm_t91J05_connected_finite_cover_classification
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X]
    (hX : apm_t91J05_IsFiniteCover X) :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (X ≃ₜ apm_t91J05_Surface (2 * n + 1)) := by
  sorry

/-- LIBRARY: the explicit connected cyclic cover of every positive degree,
presented directly between the concrete polygon surfaces. -/
theorem apm_t91J05_cyclic_surface_cover
    (n : ℕ) (hn : 0 < n) :
    apm_t91J05_IsFiniteCover (apm_t91J05_Surface (2 * n + 1)) := by
  sorry

theorem apm_t91j05
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] :
    apm_t91J05_IsFiniteCover X ↔
      ∃ n : ℕ, 0 < n ∧
        Nonempty (X ≃ₜ apm_t91J05_Surface (2 * n + 1)) := by
  constructor
  · exact apm_t91J05_connected_finite_cover_classification X
  · rintro ⟨n, hn, ⟨e⟩⟩
    exact apm_t91J05_isFiniteCover_of_homeomorph e
      (apm_t91J05_cyclic_surface_cover n hn)

#print axioms apm_t91j05
