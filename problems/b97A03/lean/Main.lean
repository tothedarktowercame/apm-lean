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

/-- The defining equation satisfied by any chosen complex root. -/
lemma apm_b97a03_root_pow_six {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    α ^ 6 = -3 := by
  have h : α ^ 6 + 3 = 0 := by
    simpa [apm_b97a03_polynomial, Polynomial.IsRoot] using hα
  exact eq_neg_of_add_eq_zero_left h

/-- The cubic power of a root is a square root of `-3`. -/
lemma apm_b97a03_root_pow_three_sq {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    (α ^ 3) ^ 2 = -3 := by
  rw [← pow_mul, show 3 * 2 = 6 by norm_num]
  exact apm_b97a03_root_pow_six hα

/-- The element extracted from a root satisfies the sixth-root-of-unity
quadratic relation used to generate the other roots. -/
lemma apm_b97a03_zeta_relation {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97a03_zeta α ^ 2 - apm_b97a03_zeta α + 1 = 0 := by
  have h := apm_b97a03_root_pow_three_sq hα
  rw [apm_b97a03_zeta]
  field_simp
  linear_combination h

/-- The derived element is a sixth root of unity with cube `-1`. -/
lemma apm_b97a03_zeta_pow_three {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97a03_zeta α ^ 3 = -1 := by
  have h := apm_b97a03_zeta_relation hα
  apply eq_neg_of_add_eq_zero_left
  linear_combination (apm_b97a03_zeta α + 1) * h

lemma apm_b97a03_zeta_pow_six {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97a03_zeta α ^ 6 = 1 := by
  rw [show 6 = 3 * 2 by norm_num, pow_mul, apm_b97a03_zeta_pow_three hα]
  norm_num

/-- The root of unity extracted from `α` belongs to the same generated
intermediate field. -/
lemma apm_b97a03_zeta_mem_field {α : ℂ} :
    apm_b97a03_zeta α ∈ apm_b97a03_field α := by
  unfold apm_b97a03_zeta apm_b97a03_field
  apply IntermediateField.div_mem
  · apply IntermediateField.add_mem
    · exact IntermediateField.one_mem _
    · have ha : α ∈ IntermediateField.adjoin ℚ ({α} : Set ℂ) :=
        IntermediateField.subset_adjoin ℚ {α} (by simp)
      simpa [pow_succ] using
        IntermediateField.mul_mem _ (IntermediateField.mul_mem _ ha ha) ha
  · exact IntermediateField.natCast_mem _ 2

/-- Multiplying a chosen root by any power of the derived sixth root of unity
again gives a root. -/
lemma apm_b97a03_zeta_mul_root {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) (k : ℕ) :
    (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot
      (apm_b97a03_zeta α ^ k * α) := by
  have hz := apm_b97a03_zeta_pow_six hα
  have ha := apm_b97a03_root_pow_six hα
  have hpow : (apm_b97a03_zeta α ^ k * α) ^ 6 = -3 := by
    rw [mul_pow, ← pow_mul, show k * 6 = 6 * k by omega, pow_mul, hz, one_pow, ha,
      one_mul]
  simpa [apm_b97a03_polynomial, Polynomial.IsRoot, hpow]

lemma apm_b97a03_zeta_mul_root_mem_field {α : ℂ} (k : ℕ) :
    apm_b97a03_zeta α ^ k * α ∈ apm_b97a03_field α := by
  have hz := apm_b97a03_zeta_mem_field (α := α)
  have ha : α ∈ apm_b97a03_field α := by
    exact IntermediateField.subset_adjoin ℚ {α} (by simp)
  apply IntermediateField.mul_mem
  · induction k with
    | zero => simpa using IntermediateField.one_mem (apm_b97a03_field α)
    | succ k ih =>
        rw [pow_succ]
        exact IntermediateField.mul_mem _ ih hz
  · exact ha

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
  generator.

  Closer hop 1 closes the first radical/root-of-unity calculation in three
  compiled lemmas. `apm_b97a03_root_pow_six` extracts `α⁶ = -3` from the
  mapped-polynomial root hypothesis; `apm_b97a03_root_pow_three_sq` obtains
  `(α³)² = -3`; and `apm_b97a03_zeta_relation` proves that the statement's
  `ζ = (1 + α³)/2` satisfies `ζ² - ζ + 1 = 0`. Thus the sixth-root-of-unity
  ingredient is now constructed explicitly from `α`, inside the same adjoin.
  Renewed searches of `LEMMA-INDEX.md`, all closed artifacts,
  `ConstructionTargets/`, Kummer extensions, and splitting-field APIs found no
  packaged theorem converting this quadratic relation into the exact six-root
  list or the four displayed fixed fields. The statement appears
  mathematically sound, but the remaining concrete splitting-field,
  automorphism, subgroup, and fixed-field development remains open.

  Closer hop 2 pushes the explicit root construction further.
  `apm_b97a03_zeta_pow_three` and `apm_b97a03_zeta_pow_six` turn the
  quadratic relation into `ζ³ = -1` and `ζ⁶ = 1`.
  `apm_b97a03_zeta_mem_field` proves `ζ ∈ ℚ(α)`, while
  `apm_b97a03_zeta_mul_root` and `apm_b97a03_zeta_mul_root_mem_field` prove
  that every `ζ^k α` is a root lying in the same adjoin. This supplies the
  candidate six-root orbit without a Kummer API. Remaining are proving the
  six candidates exhaust the root set (including distinctness), packaging the
  splitting field and automorphisms, and computing the exact fixed fields.
  -/
  sorry
