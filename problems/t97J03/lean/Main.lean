import Mathlib

/-!
# APM t97J03

## Statement repairs

None. The notation `D¹` is read as the one-dimensional complex unit disk,
whose real dimension is two, consistently with the stated solid torus in
`ℂ²` and boundary `S¹ × S¹`.

## Encoding questions

The complex unit disk, its boundary circle, the solid torus, the boundary
inclusion, and the cubing covering map are all defined explicitly as subtype
spaces and functions. Extension means literal equality after composing with
the boundary inclusion.
-/

abbrev apm_t97J03_Disk := {z : ℂ // ‖z‖ ≤ 1}
abbrev apm_t97J03_Circle := {z : ℂ // ‖z‖ = 1}
abbrev apm_t97J03_Y := apm_t97J03_Disk × apm_t97J03_Circle
abbrev apm_t97J03_Torus := apm_t97J03_Circle × apm_t97J03_Circle

/-- Inclusion of the boundary torus into the solid torus. -/
def apm_t97J03_boundaryInclusion : apm_t97J03_Torus → apm_t97J03_Y :=
  fun q ↦ (⟨q.1.1, le_of_eq q.1.2⟩, q.2)

/-- The map `(z,w) ↦ (z,w³)` on the boundary torus. -/
def apm_t97J03_boundaryMap : apm_t97J03_Torus → apm_t97J03_Torus :=
  fun q ↦
    (q.1, ⟨q.2.1 ^ 3, by rw [norm_pow, q.2.2, one_pow]⟩)

theorem apm_t97j03 :
    ¬ ∃ F : apm_t97J03_Y → apm_t97J03_Torus,
      Continuous F ∧
      ∀ q : apm_t97J03_Torus,
        F (apm_t97J03_boundaryInclusion q) = apm_t97J03_boundaryMap q := by
  sorry
