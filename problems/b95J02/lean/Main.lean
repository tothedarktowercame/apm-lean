import Mathlib

/-! # APM b95J02: cyclic modules and their annihilating invariants

## Statement repairs

The source has the evident spelling errors “pricipal” and “orde”; these do not
change the mathematical statement.
-/

noncomputable section

/-- The least positive common exponent of a group. -/
def groupExponent (G : Type*) [Group G] : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∀ g : G, g ^ m = 1}

/-- A linear endomorphism acts cyclically when one vector's iterates span. -/
def ActsCyclically {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) : Prop :=
  ∃ v₀ : V, Submodule.span F (Set.range fun i : ℕ => (T ^ i) v₀) = ⊤

/-- The finite-abelian-group and finite-dimensional-operator versions of the
same cyclic-module criterion. -/
theorem apm_b95j02 :
    (∀ (G : Type*) [CommGroup G] [Fintype G],
      0 < groupExponent G ∧
      (∀ g : G, g ^ groupExponent G = 1) ∧
      (∀ m : ℕ, 0 < m → (∀ g : G, g ^ m = 1) → groupExponent G ≤ m) ∧
      (IsCyclic G ↔ Nat.card G = groupExponent G)) ∧
    (∀ (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
      [FiniteDimensional F V] (T : Module.End F V),
      ActsCyclically T ↔
        Module.finrank F V = (minpoly F T).natDegree) := by
  constructor
  · intro G _ _
    have hexp : groupExponent G = Monoid.exponent G := by
      exact (Monoid.exponent_eq_sInf (G := G)).symm
    rw [hexp]
    refine ⟨Monoid.ExponentExists.of_finite.exponent_pos,
      Monoid.pow_exponent_eq_one, ?_, ?_⟩
    · intro m hm hpow
      exact Monoid.exponent_min' m hm hpow
    · simpa [eq_comm] using (IsCyclic.iff_exponent_eq_card (α := G))
  · -- Boundary: searched `linearIndependent_powers_iff_aeval`,
    -- `minpoly_dvd_charpoly`, and `span_minpoly_eq_annihilator`.  These prove
    -- the degree bound and the cyclic => equality direction, but Mathlib has
    -- no packaged cyclic-vector iff minpoly-degree-equals-finrank theorem;
    -- the reverse route requires formalizing rational canonical form/PID
    -- invariant factors, which did not fit the pass-1 budget.
    sorry
