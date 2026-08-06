import Mathlib

open Matrix

noncomputable section

/-!
# APM b96A01

## Statement repairs

Part (d) requires `G` to be nonabelian simple. As printed it includes cyclic groups
of prime order, for which the claimed injection can fail (for example into
`GL₁(𝔽₂)`).

## Encoding notes

All general linear groups are Mathlib's `Matrix.GeneralLinearGroup`; integral
conjugacy is expressed entrywise, and the congruence kernel uses the actual induced
map on general linear groups.
-/

def apmIntegralMatrix {n : Type*} [Fintype n]
    (A : Matrix n n ℚ) : Prop :=
  ∀ i j, ∃ z : ℤ, A i j = z

noncomputable def apmReduction (n : Type*) [Fintype n] [DecidableEq n]
    (p m : ℕ) (h : p ^ (m - 1) ∣ p ^ m) :
    Matrix.GeneralLinearGroup n (ZMod (p ^ m)) →*
      Matrix.GeneralLinearGroup n (ZMod (p ^ (m - 1))) :=
  Matrix.GeneralLinearGroup.map (ZMod.castHom h _)

theorem apm_b96a01 :
    (∀ (V : Type*) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (A : AddSubgroup V) (s : Finset V),
      A = AddSubgroup.closure (s : Set V) →
        ∃ (ι : Type*) (b : Module.Basis ι ℚ V),
          ∀ x ∈ s, ∃ i : ι, b i = x) ∧
    (∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → ∃ P : Matrix n n ℚ, IsUnit P ∧
        ∀ g : G, apmIntegralMatrix (P * (g.1 : Matrix n n ℚ) * P⁻¹)) ∧
    (∀ (n : Type*) [Fintype n] [DecidableEq n] (p m : ℕ)
      (hdiv : p ^ (m - 1) ∣ p ^ m), 2 ≤ m →
      ∀ a b, a ∈ (apmReduction n p m hdiv).ker →
        b ∈ (apmReduction n p m hdiv).ker → a * b = b * a) ∧
    (∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → IsSimpleGroup G → ¬(∀ a b : G, a * b = b * a) →
      ∀ p : ℕ, p.Prime →
        ∃ ρ : G →* Matrix.GeneralLinearGroup n (ZMod p),
          Function.Injective ρ) := by
  -- Boundary: the first frozen conjunct is false.  Take `V = ℚ`,
  -- `s = {1, 2}`, and `A = AddSubgroup.closure (s : Set ℚ)`.  Its
  -- hypothesis is reflexive, but the conclusion requires one ℚ-basis of the
  -- one-dimensional space ℚ to contain both distinct dependent vectors `1`
  -- and `2`.  No Mathlib API search can repair this statement-level issue;
  -- the intended claim would need a basis subset generating `A`, rather than
  -- requiring every element of the supplied generating set to occur in it.
  sorry
