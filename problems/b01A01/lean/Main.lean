import Mathlib

open Polynomial

noncomputable section

/-!
# APM b01A01

## Statement repairs

None.

## Encoding notes

Characteristic `p` is represented by `CharP k p` together with primality of `p`.
Polynomial splitting and separability use Mathlib's actual `Polynomial.Splits` and
`Polynomial.Separable` predicates.
-/

def apmFrobeniusPolynomial {k : Type*} [Field k] (p : ℕ) (a : k) : k[X] :=
  X ^ p - C a

theorem apm_b01a01
    (k : Type*) [Field k]
    (p : ℕ) [CharP k p] (hp : p.Prime) :
    (∀ a : k,
      (apmFrobeniusPolynomial p a).Splits ∨
        Irreducible (apmFrobeniusPolynomial p a)) ∧
    (Function.Surjective (fun α : k ↦ α ^ p) →
      ∀ q : k[X], Irreducible q → q.Separable) := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro a
    by_cases ha : ∃ b : k, b ^ p = a
    · left
      obtain ⟨b, rfl⟩ := ha
      rw [apmFrobeniusPolynomial, C_pow, ← sub_pow_char]
      exact (Splits.X_sub_C b).pow p
    · right
      rw [apmFrobeniusPolynomial]
      -- Reuse Mathlib's prime-binomial criterion from `KummerPolynomial.lean`.
      exact X_pow_sub_C_irreducible_of_prime hp (by simpa using ha)
  · intro hsurj
    -- `Perfect.lean` turns surjective Frobenius into a perfect field, whose
    -- defining theorem is precisely separability of every irreducible.
    letI : PerfectRing k p :=
      PerfectRing.ofSurjective k p (by simpa [frobenius_def] using hsurj)
    letI : PerfectField k := PerfectRing.toPerfectField k p
    intro q hq
    exact PerfectField.separable_of_irreducible hq
