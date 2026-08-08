import Mathlib

/-!
# APM b97A02 — affine automorphisms of a finite-field rational function field

## Statement repairs

None.

## Encoding notes

`F` is an arbitrary finite field and `q = Fintype.card F`.  The fixed field is
stated elementwise inside `RatFunc F`; this avoids replacing the actual fixed
field by a cardinality surrogate.  A subfield between `F` and `F(x)` is encoded
as an `IntermediateField F (RatFunc F)`.
-/

open Set

noncomputable def apm_b97a02_affineAutomorphisms
    (F : Type*) [Field F] [Fintype F] :
    Set (RatFunc F ≃ₐ[F] RatFunc F) :=
  {σ | ∃ a b : F, a ≠ 0 ∧
    σ RatFunc.X = algebraMap F (RatFunc F) a * RatFunc.X +
      algebraMap F (RatFunc F) b}

noncomputable def apm_b97a02_invariant
    (F : Type*) [Field F] [Fintype F] : RatFunc F :=
  (RatFunc.X ^ Fintype.card F - RatFunc.X) ^ (Fintype.card F - 1)

/-- The scalar factor introduced by an affine change of variable disappears
after raising to the exponent used in the frozen invariant. -/
lemma apm_b97A02_algebraMap_pow_card_sub_one
    (F : Type*) [Field F] [Fintype F] (a : F) (ha : a ≠ 0) :
    (algebraMap F (RatFunc F) a) ^ (Fintype.card F - 1) = 1 := by
  rw [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha, map_one]

/-- Coefficients are fixed by the cardinal Frobenius, also after embedding in
the rational function field. -/
lemma apm_b97A02_algebraMap_pow_card
    (F : Type*) [Field F] [Fintype F] (a : F) :
    (algebraMap F (RatFunc F) a) ^ Fintype.card F =
      algebraMap F (RatFunc F) a := by
  rw [← map_pow, FiniteField.pow_card]

/-- Lüroth's degree development implies that the rational function field is
finite over every nonconstant intermediate field. -/
lemma apm_b97A02_finite_over_nontrivial_intermediate
    (F : Type*) [Field F]
    (K : IntermediateField F (RatFunc F)) (hK : K ≠ ⊥) :
    Module.Finite K (RatFunc F) := by
  have hX : IsAlgebraic K (RatFunc.X : RatFunc F) :=
    RatFunc.IntermediateField.isAlgebraic_X hK
  letI : FiniteDimensional K
      (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc F))) :=
    IntermediateField.adjoin.finiteDimensional hX.isIntegral
  exact (RatFunc.IntermediateField.adjoinXEquiv K).toLinearEquiv.finiteDimensional

/-- Every nondegenerate affine change of variable is realized by an algebra
automorphism of the rational function field.  Lüroth's
`algEquivOfTranscendental` supplies the map to the simple adjoin; solving the
affine equation for `X` shows that this adjoin is the whole field. -/
lemma apm_b97A02_exists_affineAlgEquiv
    (F : Type*) [Field F] (a b : F) (ha : a ≠ 0) :
    ∃ σ : RatFunc F ≃ₐ[F] RatFunc F,
      σ RatFunc.X = algebraMap F (RatFunc F) a * RatFunc.X +
        algebraMap F (RatFunc F) b := by
  let f : RatFunc F := algebraMap F (RatFunc F) a * RatFunc.X +
    algebraMap F (RatFunc F) b
  have hX : ¬ ∃ c : F, (RatFunc.X : RatFunc F) = RatFunc.C c := by
    rw [RatFunc.eq_C_iff]
    simp
  have hma : algebraMap F (RatFunc F) a ≠ 0 :=
    (map_ne_zero (algebraMap F (RatFunc F))).2 ha
  have hsolve : (RatFunc.X : RatFunc F) =
      algebraMap F (RatFunc F) a⁻¹ *
        (f - algebraMap F (RatFunc F) b) := by
    dsimp [f]
    rw [map_inv₀]
    calc
      RatFunc.X = (algebraMap F (RatFunc F) a)⁻¹ *
          (algebraMap F (RatFunc F) a * RatFunc.X) := by
            rw [← mul_assoc, inv_mul_cancel₀ hma, one_mul]
      _ = (algebraMap F (RatFunc F) a)⁻¹ *
          (algebraMap F (RatFunc F) a * RatFunc.X +
            algebraMap F (RatFunc F) b - algebraMap F (RatFunc F) b) := by ring
  have hf : ¬ ∃ c : F, f = RatFunc.C c := by
    rintro ⟨c, hc⟩
    apply hX
    refine ⟨a⁻¹ * (c - b), ?_⟩
    rw [hsolve, hc, ← RatFunc.algebraMap_eq_C]
    simp only [← map_sub, ← map_mul]
  have hadjoin : IntermediateField.adjoin F ({f} : Set (RatFunc F)) = ⊤ := by
    apply le_antisymm le_top
    rw [← RatFunc.adjoin_X]
    apply IntermediateField.adjoin_le_iff.mpr
    rw [Set.singleton_subset_iff]
    rw [hsolve]
    exact IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.sub_mem _
        (IntermediateField.subset_adjoin F ({f} : Set (RatFunc F))
          (Set.mem_singleton f))
        (IntermediateField.algebraMap_mem _ _))
  let e : RatFunc F ≃ₐ[F] RatFunc F :=
    (RatFunc.algEquivOfTranscendental f (f.transcendental_of_ne_C hf)).trans
      ((IntermediateField.equivOfEq hadjoin).trans IntermediateField.topEquiv)
  refine ⟨e, ?_⟩
  change e RatFunc.X = f
  simp [e, RatFunc.algEquivOfTranscendental_X]

theorem apm_b97a02 (F : Type*) [Field F] [Fintype F] :
    (∀ a b : F, a ≠ 0 →
      ∃! σ : RatFunc F ≃ₐ[F] RatFunc F,
        σ RatFunc.X = algebraMap F (RatFunc F) a * RatFunc.X +
          algebraMap F (RatFunc F) b) ∧
    Set.ncard (apm_b97a02_affineAutomorphisms F) =
      Fintype.card F * (Fintype.card F - 1) ∧
    (∀ r : RatFunc F,
      (∀ σ ∈ apm_b97a02_affineAutomorphisms F, σ r = r) ↔
        r ∈ IntermediateField.adjoin F
          ({apm_b97a02_invariant F} : Set (RatFunc F))) ∧
    (∀ K : IntermediateField F (RatFunc F), K ≠ ⊥ →
      Module.Finite K (RatFunc F)) := by
  refine ⟨?_, ?_, ?_, apm_b97A02_finite_over_nontrivial_intermediate F⟩
  /-
  PARTIAL boundary (closer hop 2): the finite-field coefficient arithmetic
  needed by the invariant calculation is now compiled above.
  `apm_b97A02_algebraMap_pow_card` handles Frobenius-fixed coefficients, and
  `apm_b97A02_algebraMap_pow_card_sub_one` proves that the nonzero affine
  scaling factor disappears at exponent `q-1`.

  Closer hop 2 found that `FieldTheory/RatFunc/Luroth.lean` is present in this
  snapshot despite the earlier bounded search missing it. The new compiled
  lemma `apm_b97A02_finite_over_nontrivial_intermediate` uses
  `RatFunc.IntermediateField.isAlgebraic_X`, finite dimensionality of a simple
  algebraic adjoin, and `RatFunc.IntermediateField.adjoinXEquiv` to close the
  theorem's entire last conjunct. The main proof now supplies that conjunct
  outside the remaining goals.

  The same source also provides `RatFunc.algEquivOfTranscendental` and
  `RatFunc.finrank_eq_max_natDegree`, correcting two earlier API-negative
  findings. For affine `aX+b`, closure can use the former after proving
  transcendence and `F⟮aX+b⟯ = ⊤`; the latter supplies the degree calculation
  needed after the automorphism action has been assembled. That construction,
  uniqueness, finite action count, and fixed-field equality remain open.

  Earlier local Mathlib source search found the
  low-level constructors `RatFunc.liftRingHom` and `RatFunc.liftAlgHom`, and
  the general fixed-field API `IntermediateField.fixedField`, but no packaged
  affine-substitution `AlgEquiv` for `RatFunc`, no theorem that such maps are
  determined by `RatFunc.X`, and no rational-function degree formula proving
  `[F(X) : F(t)] = max (degree numerator) (degree denominator)`.

  The available `IntermediateField.finrank_fixedField_eq_card` machinery
  assumes a finite-dimensional ambient extension and therefore does not apply
  directly to `F ⊂ F(X)`. Consequently the fixed-field identification still
  requires connecting the finite affine action to the newly found degree
  theorem. Searches of proved sibling artifacts found no implementation. The
  statement appears mathematically sound; this is an API/formalization blocker.

  CLOSER HOP 3: `apm_b97A02_exists_affineAlgEquiv` now constructs the affine
  substitution automorphism for every `a ≠ 0`. It explicitly solves
  `X = a⁻¹ ((aX+b)-b)`, uses this to prove `F⟮aX+b⟯ = ⊤`, rules out the affine
  expression being constant, and applies `RatFunc.algEquivOfTranscendental`
  followed by `IntermediateField.equivOfEq` and `topEquiv`. Its application
  lemma then gives exactly `σ X = aX+b`. Thus existence in the first frozen
  conjunct is complete; only uniqueness of an `F`-algebra automorphism from
  its value on `X` remains there.

  Searches beyond hop 2 covered the Lüroth equivalence implementation,
  `RatFunc.eq_C_iff`, `RatFunc.adjoin_X`, intermediate-field adjoin induction,
  and low-level `liftAlgHom` extensionality. The first group supplied the
  construction above. No packaged extensionality theorem for `RatFunc`
  algebra homomorphisms was found, so uniqueness, action counting, invariant
  fixedness, and the fixed-field degree comparison remain open.
  -/
  all_goals sorry
