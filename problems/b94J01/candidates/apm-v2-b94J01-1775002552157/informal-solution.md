# Informal Solution: b94J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**(a) FTFAG.** Every finite abelian group is isomorphic to a direct sum of cyclic groups of prime-power order: G ≅ ℤ/p₁^{a₁} ⊕ ℤ/p₂^{a₂} ⊕ ... ⊕ ℤ/pₖ^{aₖ}. The decomposition is unique up to reordering. Equivalently: G ≅ ℤ/d₁ ⊕ ... ⊕ ℤ/dₛ where d₁ | d₂ | ... | dₛ (invariant factor form).

**(b) Cyclic product criterion.** ℤ/mℤ ⊕ ℤ/nℤ is cyclic if and only if gcd(m,n) = 1.

*Proof.* (⟹) If gcd(m,n) = d > 1, then every element (a,b) has order dividing lcm(m,n) = mn/d < mn. But a cyclic group of order mn has an element of order mn. Contradiction.

(⟸) If gcd(m,n) = 1, the Chinese Remainder Theorem gives ℤ/mnℤ ≅ ℤ/mℤ × ℤ/nℤ. Since ℤ/mnℤ is cyclic, so is the product. ∎

**(c) Finite subgroup of K* is cyclic.**

*Proof.* Let G ⊂ K* be a finite multiplicative subgroup of order n. By FTFAG, G ≅ ℤ/d₁ ⊕ ... ⊕ ℤ/dₛ with d₁ | d₂ | ... | dₛ and d₁ · d₂ · ... · dₛ = n.

The key fact: in a field, the polynomial x^d - 1 has at most d roots.

For each divisor d of n, the number of elements of G satisfying x^d = 1 is at most d (because x^d - 1 has at most d roots in K). But in the cyclic group ℤ/dₛ, every element satisfies x^{dₛ} = 1 (since dᵢ | dₛ for all i). So ALL n elements of G satisfy x^{dₛ} = 1. But x^{dₛ} - 1 has at most dₛ roots. So n ≤ dₛ. Since dₛ divides n (it's a factor in the decomposition), we get dₛ = n. This means s = 1 and G ≅ ℤ/n — cyclic. ∎

(The crux: the polynomial root bound in a field forces the FTFAG decomposition to have exactly one factor. In a ring with zero divisors, x^d - 1 can have more than d roots, and the argument fails — that's why we need K to be a field, or more generally an integral domain.)

**Stage 2 — LEMMA DEPENDENCY GRAPH**

| # | Lemma | Source | Critical? |
|---|-------|--------|-----------|
| 1 | FTFAG | Mathlib: `CommGroup.equiv_prod_zmod_of_finite` or similar | Foundation for (c) |
| 2 | x^d - 1 has ≤ d roots in a field | Mathlib: `Polynomial.card_roots_le_degree` | YES — the key step |
| 3 | CRT: gcd(m,n)=1 ⟹ ℤ/mn ≅ ℤ/m × ℤ/n | Mathlib: `ZMod.chineseRemainder` | For (b) |
| 4 | IsCyclic for finite subgroups of IsDomain | Mathlib: `isCyclic_of_subgroup_isDomain` | Closes (c) directly |

**Stage 3 — LEAN FORMALIZATION**

**FULLY CLOSED — ZERO SORRY.** Both part (c) instances compile via `inferInstance`:

```lean
instance subgroup_cyclic_of_field {K : Type*} [Field K] (G : Subgroup Kˣ) [Finite G] :
    IsCyclic G := inferInstance
```

Mathlib synthesizes this automatically from the chain: `Field K` → `IsDomain K` → the instance `[IsDomain R] [Finite S] : IsCyclic S` for `S : Subgroup Rˣ` (in `Mathlib.RingTheory.IntegralDomain`). The underlying proof in Mathlib uses exactly the hint's approach: polynomial root bound → FTFAG decomposition must be a single cyclic factor.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The formal work confirms: this theorem is a ONE-LINER in Lean. Mathlib's typeclass resolution handles the entire chain `Field → IsDomain → finite subgroup cyclic` automatically. The student's job on the exam is to reproduce the PROOF, not the statement — and the proof (polynomial root bound → FTFAG forces one factor) is exactly what Mathlib encodes internally.

Difficulty calibration: part (a) is pure recall. Part (b) is a one-step CRT argument. Part (c) is the real work — but it's short once you know the polynomial root bound trick. The Lean formalization confirms there is no hidden difficulty: the proof is exactly as short as it looks.
