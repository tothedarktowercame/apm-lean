import Mathlib
import ConstructionTargets.Surfaces

/-!
# APM t91J05 — finite covers of the genus-three orientable surface

Closed orientable surfaces are the explicit polygon quotients supplied by
`ConstructionTargets.Surfaces`.  Covering maps, finite fibers, connectedness,
and classification up to homeomorphism remain native topological notions.

## Statement repairs

The classification is stated for connected covering spaces.  Without
connectedness, a finite cover may be a finite disjoint union of the classified
connected covers, so “exactly the odd-genus surfaces” would be incomplete.

The former opaque carrier and topology are replaced by the concrete polygon
presentation `ConstructionTargets.Surfaces.Surface true g`.

## Encoding questions

None.
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
homeomorphic space. This discharges the transport part of the reverse
classification direction. -/
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

theorem apm_t91j05
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] :
    apm_t91J05_IsFiniteCover X ↔
      ∃ n : ℕ, 0 < n ∧
        Nonempty (X ≃ₜ apm_t91J05_Surface (2 * n + 1)) := by
  /-
  CLOSER HOP 3 goes beyond the previous bounded searches by closing two
  independent pieces of the classification assembly.
  `apm_t91J05_isFiniteCover_of_homeomorph` uses
  `IsCoveringMap.comp_homeomorph` and finite preimages under an embedding to
  prove that the frozen finite-cover predicate transports across any source
  homeomorphism. `apm_t91J05_eulerCharacteristic_odd_genus` compiles the exact
  arithmetic identity `χ(Σ_(2n+1)) = n * χ(Σ_3)` for the concrete surface
  data from `ConstructionTargets.Surfaces`.

  The remaining forward direction still requires the theorem that connected
  finite covers of a closed orientable surface are classified surfaces and
  multiply Euler characteristic. The reverse direction is reduced to
  constructing an actual `n`-sheeted covering map from each concrete polygon
  surface `Surface true (2*n+1)` to `Surface true 3`; the transport to an
  arbitrary homeomorphic `X` is now complete. Searches of covering-space
  classification, surface polygon maps, lifted CW structures, fundamental
  groups, `LEMMA-INDEX.md`, `ConstructionTargets/`, siblings, and git history
  found no such construction or classification theorem. The frozen statement
  remains unchanged and no unproved intermediate assertion was introduced.
  -/
  sorry
