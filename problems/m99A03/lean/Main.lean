import Mathlib

/-! # APM m99A03: compact powers and normal nilpotent operators

## Statement repairs

Part (b) cannot hold on every Hilbert space (for example, not on a
finite-dimensional one).  Its instruction to “construct an example” is encoded
as an existential example on the explicit infinite-dimensional Hilbert space
`m99A03ExampleSpace`.
-/

noncomputable section

abbrev m99A03L2 := lp (fun _ : ℕ => ℂ) 2
abbrev m99A03ExampleSpace := m99A03L2 × m99A03L2 × m99A03L2

theorem apm_m99a03 :
    (∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (A : H →L[ℂ] H),
      IsCompactOperator A → IsStarNormal A → A ^ 3 = 0 → A = 0) ∧
    (∃ A : m99A03ExampleSpace →L[ℂ] m99A03ExampleSpace,
      ¬IsCompactOperator A ∧
      ¬IsCompactOperator
        ((A ^ 2 : m99A03ExampleSpace →L[ℂ] m99A03ExampleSpace) :
          m99A03ExampleSpace → m99A03ExampleSpace) ∧
      IsCompactOperator
        ((A ^ 3 : m99A03ExampleSpace →L[ℂ] m99A03ExampleSpace) :
          m99A03ExampleSpace → m99A03ExampleSpace)) := by
  constructor
  · intro H _ _ _ A _hcompact hnormal hcube
    have hfourth : A ^ 4 = 0 := by
      calc
        A ^ 4 = A ^ 3 * A := by noncomm_ring
        _ = 0 := by rw [hcube, zero_mul]
    /-
    Boundary: nilpotence has been propagated above to the fourth power, the
    power needed by the standard dyadic C⋆-norm argument. It remains to bridge
    the proposition `IsStarNormal A` to the normal-element C⋆ spectral-radius
    or power-norm API and conclude `‖A‖ = 0` from `A ^ 4 = 0`. I searched
    `IsStarNormal.spectralRadius_eq_nnnorm`, C⋆ power-norm lemmas, and the
    compact-normal spectral theorem; I did not complete that interface bridge
    in this pass. (Compactness is mathematically unnecessary here.)
    -/
    sorry
  · /-
    Boundary: the existential clause requires bundling the block shift
    `(x,y,z) ↦ (y,z,0)` as a continuous linear map on a nested product of
    `lp` spaces, computing its second and third powers extensionally, and
    proving noncompactness of its first two powers via the standard orthonormal
    coordinate sequence. I searched product continuous-linear-map constructors,
    `lp.single`, orthonormal-sequence, and `IsCompactOperator` sequential
    criteria; the full bundled construction was not completed in this pass.
    -/
    sorry
