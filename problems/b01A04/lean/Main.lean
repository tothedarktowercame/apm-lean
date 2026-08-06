import Mathlib

/-!
# APM b01A04: Realizing groups as Galois groups over ℚ

## Statement repairs

None.

## Encoding questions

None. A field extension is existentially bundled with its field and
`ℚ`-algebra structures. Its Galois group is the full group of
`ℚ`-algebra automorphisms. `Multiplicative` converts the additive groups
`ZMod 3` and `ZMod 3 × ZMod 3` to the multiplicative convention used by
automorphism groups.
-/

noncomputable section

/-- A group `G` occurs as the Galois group of some field extension of `ℚ`. -/
def apm_b01A04_isGaloisGroup (G : Type) [Group G] : Prop :=
  ∃ K : Type,
    ∃ hK : Field K,
      letI := hK
      ∃ hA : Algebra ℚ K,
        letI := hA
        IsGalois ℚ K ∧ Nonempty ((K ≃ₐ[ℚ] K) ≃* G)

theorem apm_b01a04 :
    apm_b01A04_isGaloisGroup (Multiplicative (ZMod 3)) ∧
      apm_b01A04_isGaloisGroup
        (Multiplicative (ZMod 3 × ZMod 3)) := by
  -- SKIPPED: construct Galois extensions of ℚ with Galois groups Z/3Z and Z/3Z × Z/3Z.
  -- (a) Z/3Z: splitting field of an irreducible cubic with discriminant a perfect square,
  --     e.g. x³-3x+1 (discriminant = 81 = 9²). Gal ≅ A₃ ≅ Z/3Z.
  -- (b) Z/3Z × Z/3Z: compositum of two linearly disjoint Z/3Z extensions.
  -- Blocker: requires constructing specific splitting fields, proving irreducibility,
  -- computing discriminants, proving Galois property, computing Galois group structure.
  -- APIs: `IsGalois`, `AlgEquiv`, `Polynomial`, `IsSplittingField` — exist but
  --   assembling the full construction with explicit polynomials is very involved.
  sorry
