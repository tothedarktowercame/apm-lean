import Mathlib

/-!
# APM b97A03 — the splitting field and subfields of `X⁶ + 3`

## Statement repairs

None.

## Encoding notes

For a chosen complex root `α`, `ℚ(α)` is represented by
`IntermediateField.adjoin ℚ {α}` inside `ℂ`.  Completeness of the subfield list
is stated for every intermediate field of `ℂ/ℚ` contained in `ℚ(α)`, so the
actual embedded fields—not merely their degrees—are retained.
-/

open Set Polynomial

noncomputable def apm_b97a03_polynomial : ℚ[X] :=
  Polynomial.X ^ 6 + Polynomial.C 3

noncomputable def apm_b97a03_field (α : ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {α}

noncomputable def apm_b97a03_zeta (α : ℂ) : ℂ :=
  (1 + α ^ 3) / 2

theorem apm_b97a03 :
    Irreducible apm_b97a03_polynomial ∧
    ∀ α : ℂ,
      (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α →
      (∀ z : ℂ,
        (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot z →
          z ∈ apm_b97a03_field α) ∧
      Nonempty
        ((apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) ≃*
          Equiv.Perm (Fin 3)) ∧
      ∀ L : IntermediateField ℚ ℂ,
        L ≤ apm_b97a03_field α →
        L = ⊥ ∨
        L = IntermediateField.adjoin ℚ {α ^ 3} ∨
        L = IntermediateField.adjoin ℚ {α ^ 2} ∨
        L = IntermediateField.adjoin ℚ
          {(apm_b97a03_zeta α) ^ 2 * α ^ 2} ∨
        L = IntermediateField.adjoin ℚ
          {(apm_b97a03_zeta α) ^ 4 * α ^ 2} ∨
        L = apm_b97a03_field α := by
  /-
  Boundary (pass-1 Codex, skipped): Mathlib contains Eisenstein machinery
  (`Polynomial.IsEisensteinAt.irreducible`), splitting-field/adjoin lemmas such
  as `IsSplittingField.adjoin_rootSet`, and the abstract correspondence
  `IsGalois.intermediateFieldEquivSubgroup`. Local source and solved-sibling
  searches found no implementation of the concrete bridges required here:
  deriving all six complex roots from an arbitrary root `α`, proving the
  embedded field `adjoin ℚ {α}` is the splitting field, constructing its six
  automorphisms and the displayed `S₃` equivalence, and identifying the fixed
  fields of the four proper nontrivial subgroups with the exact listed adjoins.

  The abstract Galois correspondence alone does not establish completeness of
  this explicit embedded-field list; it additionally needs a classification of
  subgroups of `Equiv.Perm (Fin 3)` and degree/fixed-point calculations for each
  generator. The statement appears mathematically sound, but this concrete
  splitting-field and fixed-field development exceeds the pass-1 bridge found.
  -/
  sorry
