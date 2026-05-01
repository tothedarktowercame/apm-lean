# Informal Solution: b94J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

(a) *Fundamental Theorem of Finite Abelian Groups.* Every finite abelian group `G` decomposes uniquely (up to ordering) as a direct product of cyclic p-power groups. Equivalently, there exist invariant factors `d₁ | d₂ | … | d_r` with `G ≅ ⊕_{i=1}^r ℤ/d_iℤ`.

(b) *When is ℤ/m ⊕ ℤ/n cyclic?* The direct sum is cyclic iff `gcd(m,n) = 1`. If `g = gcd(m,n) ≠ 1`, any element `(a,b)` has order dividing `lcm(m,n) = mn/g`, so no element reaches order `mn`. Conversely, when `gcd(m,n) = 1`, the element `(1,1)` has order `mn` (because `k(1,1)=0` implies `m|k` and `n|k`), so it generates the whole group.

(c) *Finite multiplicative subgroups are cyclic.* Let `G ⊆ Kˣ` be finite. For each divisor `d` of `|G|`, all elements whose order divides `d` are roots of `x^d - 1`, so there are at most `d` such elements. Since `∑_{d|n} φ(d) = n`, there must be an element whose order equals `|G|`, hence `G` is cyclic.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Primary decomposition** for finite abelian groups.
- **Order/lcm identities** to convert `gcd(m,n)=1` into the order of `(1,1)`.
- **Roots of unity counting**: in a field, `x^d - 1` has at most `d` roots.
- **Euler totient identity** `∑_{d|n} φ(d) = n` to finish part (c).

**Stage 3 — LEAN FORMALIZATION**

Targets:
- `finiteAbelian_invariantFactors` — cite Mathlib’s classification theorem (already present).
- `zmod_prod_isCyclic_iff (m n : ℕ)` — still missing, needs Chinese remainder input.
- `finite_mul_subgroup_cyclic (K : Type*) [Field K]` — not yet in mathlib; requires the roots-of-unity counting lemma.
All three pass the HtDP sanity check (they mention the real objects, avoid assuming the conclusion, and would be meaningful even without prose). However, mathlib currently lacks the CRT lemma “`ZMod m × ZMod n` cyclic iff `Nat.Coprime m n`” and the `x^d-1` counting API for arbitrary fields, so the Lean proofs remain blocked.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the CRT and root-counting lemmas land in mathlib, Stage 1 can cite the exact Lean theorem names. Until then, the textual argument stands on its own and Stage 3 records the open infrastructure work.
