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

/-- The derived sixth root of unity is primitive, not merely a root of
unity. -/
lemma apm_b97a03_zeta_primitive {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    IsPrimitiveRoot (apm_b97a03_zeta α) 6 := by
  let z := apm_b97a03_zeta α
  have hrel : z ^ 2 - z + 1 = 0 := apm_b97a03_zeta_relation hα
  have h3 : z ^ 3 = -1 := apm_b97a03_zeta_pow_three hα
  have h6 : z ^ 6 = 1 := apm_b97a03_zeta_pow_six hα
  have ho : orderOf z = 6 := (orderOf_eq_iff (by norm_num : 0 < 6)).2 (by
    constructor
    · exact h6
    · intro m hm hm0 heq
      interval_cases m
      · have hz : z = 1 := by simpa only [pow_one] using heq
        rw [hz] at h3
        norm_num at h3
      · have hz2 : z ^ 2 = 1 := heq
        have hz : z = 2 := by linear_combination -hrel + hz2
        rw [hz] at h3
        norm_num at h3
      · rw [h3] at heq
        norm_num at heq
      · have hz2 : z ^ 2 = 1 := by
          calc z ^ 2 = z ^ 4 * z ^ 2 := by rw [heq, one_mul]
               _ = z ^ 6 := by ring
               _ = 1 := h6
        have hz : z = 2 := by linear_combination -hrel + hz2
        rw [hz] at h3
        norm_num at h3
      · have hz : z = 1 := by
          calc z = z ^ 5 * z := by rw [heq, one_mul]
               _ = z ^ 6 := by ring
               _ = 1 := h6
        rw [hz] at h3
        norm_num at h3)
  rw [← ho]
  exact IsPrimitiveRoot.orderOf z

/-- The six candidate roots obtained from a chosen root are pairwise
distinct. -/
lemma apm_b97a03_candidate_roots_injective {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Function.Injective
      (fun k : Fin 6 => apm_b97a03_zeta α ^ (k : ℕ) * α) := by
  have ha : α ≠ 0 := by
    intro ha
    have hpow := apm_b97a03_root_pow_six hα
    rw [ha] at hpow
    norm_num at hpow
  intro i j hij
  apply Fin.ext
  exact (apm_b97a03_zeta_primitive hα).pow_inj i.isLt j.isLt
    (mul_right_cancel₀ ha hij)

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

/-- Why this unblocks `apm_b97a03`: this is the independent arithmetic input
needed for the first conjunct; it can be proved by Eisenstein at `3`. -/
theorem apm_b97A03_bridge_1 :
    Irreducible apm_b97a03_polynomial := by
  sorry

/-- Why this unblocks `apm_b97a03`: it identifies every complex root with one
of the six compiled candidates and packages the resulting splitting-field
statement in Mathlib's exact API. -/
theorem apm_b97A03_bridge_2 {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    (∀ z : ℂ,
        (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot z →
          ∃ k : Fin 6, z = apm_b97a03_zeta α ^ (k : ℕ) * α) ∧
      Polynomial.IsSplittingField ℚ (apm_b97a03_field α)
        apm_b97a03_polynomial := by
  sorry

/-- Why this unblocks `apm_b97a03`: it is the concrete Galois-theoretic
classification left after root exhaustion: the automorphism group is `S₃`
and the displayed six fields exhaust the intermediate-field lattice. -/
theorem apm_b97A03_bridge_3 {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
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
  sorry

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

  Closer hop 3 proves `apm_b97a03_zeta_primitive`, showing that the derived
  element has exact order six, and
  `apm_b97a03_candidate_roots_injective`, showing the six compiled candidates
  are pairwise distinct.  Together with hop 2, this gives six distinct roots
  of the degree-six polynomial inside `ℚ(α)`.  The remaining bridge is to turn
  that fact into root-set exhaustion/splitting in the exact API, then package
  the automorphisms and fixed-field classification.
  -/
  sorry
