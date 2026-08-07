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
  rintro ⟨F, hF, hboundary⟩
  let w₀ : apm_t97J03_Circle := ⟨1, by simp⟩
  let g : apm_t97J03_Disk → apm_t97J03_Circle := fun z => (F (z, w₀)).1
  have hg : Continuous g := by
    exact continuous_fst.comp (hF.comp (continuous_id.prodMk continuous_const))
  have hg_boundary : ∀ z : apm_t97J03_Circle,
      g ⟨z.1, le_of_eq z.2⟩ = z := by
    intro z
    have h := congrArg Prod.fst (hboundary (z, w₀))
    exact h
  /-
  Boundary (closer hop 1, still open): the solid-torus extension has now been
  reduced by compiled code to a continuous disk retraction `g`: fixing the
  second input coordinate and projecting the first output coordinate gives
  `hg`, while `hg_boundary` proves that it is the identity on the boundary.

  Closing the contradiction is precisely the no-retraction theorem for the
  complex unit disk. Searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`,
  Mathlib's Brouwer, retract, `FundamentalGroupoid`, singular-homology, circle,
  and contractibility APIs, fully closed artifacts, staging directories, and
  git history found no packaged theorem. Partial sibling `t91A05` is the exact
  no-retraction statement and now compiles the induced-fundamental-group
  injectivity step, but remains open because Mathlib does not compute
  `FundamentalGroup Circle 1 ≃* Multiplicative ℤ`. Siblings `t01J03`,
  `t93A03`, and `t02A03` record the same missing circle computation.
  No unproved intermediate assertion beyond the original theorem remains, and
  the frozen statement is unchanged.
  -/
  sorry
