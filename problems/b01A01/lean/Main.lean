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
  -- SKIPPED: two-part field theory in characteristic p.
  -- (a) x^p - a splits or is irreducible: Frobenius is x↦x^p; if a=b^p then x^p-a=(x-b)^p (splits);
  --     otherwise x^p-a has no root, and since gcd(p,p)=p the only factorization is trivial.
  -- (b) Surjective Frobenius ⟹ perfect field ⟹ every irreducible is separable.
  -- Blocker: requires `Polynomial.Splits`, `Irreducible`, `Polynomial.Separable`,
  -- `IsPerfect`, Frobenius theory — deep algebra infrastructure to assemble.
  sorry
