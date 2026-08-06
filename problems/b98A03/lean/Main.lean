import Mathlib

/-!
# APM b98A03

## Statement repairs

None.

## Encoding questions

The inclusion `R ⊆ T` is represented by an injective `R`-algebra structure on
`T`. The conductor is defined as the supremum of all ideals of `T` contained in
the image of `R`; the theorem identifies its elements with the elementwise
definition in the question. The ring `R[u]` is `Algebra.adjoin R {u}`.
-/

noncomputable section

/-- The largest ideal of `T` whose elements all come from `R`. -/
def apm_b98A03_conductor (R T : Type*) [CommRing R] [CommRing T] [Algebra R T] : Ideal T :=
  sSup {J : Ideal T | (J : Set T) ⊆ Set.range (algebraMap R T)}

theorem apm_b98a03 :
    ∀ (R T : Type*) [CommRing R] [CommRing T] [IsDomain R] [IsDomain T]
      [Algebra R T] [FaithfulSMul R T]
      (P : Ideal R) (Q₁ Q₂ : Ideal T),
      P.IsPrime → Q₁.IsPrime → Q₂.IsPrime →
      Ideal.comap (algebraMap R T) Q₁ = P →
      Ideal.comap (algebraMap R T) Q₂ = P →
      let I := apm_b98A03_conductor R T
      (I : Set T) =
          {x | ∃ r : R, (∀ t : T, algebraMap R T r * t ∈ Set.range (algebraMap R T)) ∧
            algebraMap R T r = x} ∧
      (∀ J : Ideal T, (J : Set T) ⊆ Set.range (algebraMap R T) → J ≤ I) ∧
      ((∃ r : R, algebraMap R T r ∈ I ∧ r ∉ P) → Q₁ = Q₂) ∧
      (∀ (Q : Ideal T), Q.IsPrime → Ideal.comap (algebraMap R T) Q = P →
        ∀ u ∈ Q, ∀ p : Polynomial R,
          Polynomial.eval₂ (algebraMap R T) u p ∈ Q ↔ p.coeff 0 ∈ P) ∧
      (∀ u ∈ Q₁ ⊓ Q₂,
        Ideal.comap (Algebra.adjoin R {u}).val Q₁ =
          Ideal.comap (Algebra.adjoin R {u}).val Q₂) ∧
      (Q₁ ≠ Q₂ →
        (∀ S : Subalgebra R T,
          Ideal.comap S.val Q₁ = Ideal.comap S.val Q₂ → S = ⊥) →
        Ideal.map (algebraMap R T) P = Q₁ ⊓ Q₂ ∧ Q₁ ⊓ Q₂ = I) := by
  /-
  Boundary (pass-1 Codex, skipped): the informal solution cites sibling
  `b90A04`, but inspection showed that artifact is not proved and still ends in
  a placeholder proof, so it was discarded as a compiled dependency. Mathlib
  does provide `Ideal.coeff_zero_mem_comap_of_root_mem_of_eval_mem`, which gives
  the forward direction of the polynomial constant-term criterion when `u ∈ Q`.

  The first two conjuncts still require proving that the `sSup` of all ideals
  contained in `Set.range (algebraMap R T)` remains contained in that range.
  This is not an immediate `sSup_le`, because the range is a subring/set rather
  than an ideal of `T`; one must unpack membership in the ideal supremum and
  combine finitely many preimages in `R`. The reverse constant-term implication
  then needs a custom `eval₂` decomposition into the constant term plus terms
  divisible by `u`.

  Finally, the last conjunct must convert `S = ⊥` for every agreeing subalgebra
  into elementwise membership in the algebra-map range, identify the ideal
  intersection with `Ideal.map (algebraMap R T) P`, and use the conductor
  uniqueness lemma contrapositive to obtain the reverse inclusion. No searched
  theorem or proved sibling packages this chain. The statement appears sound.
  -/
  sorry
