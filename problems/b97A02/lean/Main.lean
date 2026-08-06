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
  /-
  Boundary (pass-1 Codex, skipped): local Mathlib source search found the
  low-level constructors `RatFunc.liftRingHom` and `RatFunc.liftAlgHom`, and
  the general fixed-field API `IntermediateField.fixedField`, but no packaged
  affine-substitution `AlgEquiv` for `RatFunc`, no theorem that such maps are
  determined by `RatFunc.X`, and no rational-function degree formula proving
  `[F(X) : F(t)] = max (degree numerator) (degree denominator)`.

  The available `IntermediateField.finrank_fixedField_eq_card` machinery
  assumes a finite-dimensional ambient extension and therefore does not apply
  directly to `F ⊂ F(X)`.  Consequently the fixed-field identification and the
  final assertion for every proper intermediate field still require a sizable
  custom development connecting substitution, degrees, and adjoins. Searches
  of proved sibling artifacts found no implementation of this bridge. The
  statement appears mathematically sound; this is an API/formalization blocker.
  -/
  sorry
