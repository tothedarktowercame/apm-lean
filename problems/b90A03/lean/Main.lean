import Mathlib

/-!
# APM b90A03: Sylow subgroups and intermediate fields

## Statement repairs

Part (b) asks whether `L` is a Galois extension of `L`, which is always true.
We replace the second `L` by `K`: the intended conclusion is that `L/K` is
Galois, as confirmed by the supplied solution and the Galois correspondence.

## Encoding questions

None. Intermediate fields are represented by `IntermediateField K F`, and
`[F : L]` by `Module.finrank (↥L) F`.
-/

open Set

noncomputable section

theorem apm_b90a03
    (K F : Type) [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    (p q n m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : 1 < n) (hm : 1 < m)
    (hdegree : Module.finrank K F = p ^ n * q ^ m) :
    (∃ L : IntermediateField K F,
      L ≠ ⊥ ∧ L ≠ ⊤ ∧ Module.finrank (↥L) F = p ^ n) ∧
    ∀ L : IntermediateField K F,
      L ≠ ⊥ → L ≠ ⊤ → Module.finrank (↥L) F = p ^ n →
      (({L' : IntermediateField K F |
          Module.finrank (↥L') F = p ^ n} : Set (IntermediateField K F)) =
          {L} ↔
        IsGalois K (↥L)) := by
  sorry
