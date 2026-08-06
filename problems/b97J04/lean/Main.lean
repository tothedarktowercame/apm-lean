import Mathlib

/-!
# APM b97J04

## Statement repairs

Part (d) says “unique `S,N ∈ GL(V)`” but immediately uses the names `S,U` and
requires `U` to be unipotent. The second name is repaired from `N` to `U`.
The source also has the grammatical typo “there is are”, repaired to “there
are”.

## Encoding questions

None. Semisimplicity is Mathlib's `Module.End.IsSemisimple`; nilpotence is
`IsNilpotent` in the endomorphism ring; the eigenspaces and generalized
eigenspaces in part (c) are retained as actual subsets of `V`.
-/

/-- A commuting additive Jordan--Chevalley decomposition. -/
def APMAdditiveJC {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (T S N : Module.End F V) : Prop :=
  Module.End.IsSemisimple S ∧ IsNilpotent N ∧ S * N = N * S ∧ T = S + N

/-- The `λ`-eigenspace of an endomorphism, as a set. -/
def APMEigenspace {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (S : Module.End F V) (lam : F) : Set V :=
  {v | S v = lam • v}

/-- The generalized `λ`-eigenspace of an endomorphism, as a set. -/
def APMGeneralizedEigenspace {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) (lam : F) : Set V :=
  {v | ∃ k : ℕ, 0 < k ∧
    ((T - lam • (LinearMap.id : Module.End F V)) ^ k) v = 0}

/-- A linear automorphism is unipotent when its difference from the identity
is nilpotent. -/
def APMUnipotent {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (U : V ≃ₗ[F] V) : Prop :=
  IsNilpotent (U.toLinearMap - LinearMap.id)

theorem apm_b97j04 :
    ∀ (F V : Type*) [Field F] [IsAlgClosed F] [AddCommGroup V]
        [Module F V] [FiniteDimensional F V] (T : Module.End F V),
      (∃ S N : Module.End F V, APMAdditiveJC T S N) ∧
      (∀ S N : Module.End F V,
        APMAdditiveJC T S N → LinearMap.charpoly S = LinearMap.charpoly T) ∧
      (∀ S N : Module.End F V, APMAdditiveJC T S N →
        ∀ lam : F,
          APMEigenspace S lam ⊆ APMGeneralizedEigenspace T lam ∧
          APMGeneralizedEigenspace T lam ⊆ APMEigenspace S lam) ∧
      (∀ S N S' N' : Module.End F V,
        APMAdditiveJC T S N → APMAdditiveJC T S' N' → S = S' ∧ N = N') ∧
      (∀ T' : V ≃ₗ[F] V,
        ∃! p : (V ≃ₗ[F] V) × (V ≃ₗ[F] V),
          Module.End.IsSemisimple p.1.toLinearMap ∧
          APMUnipotent p.2 ∧ p.1 * p.2 = p.2 * p.1 ∧ T' = p.1 * p.2) := by
  sorry
