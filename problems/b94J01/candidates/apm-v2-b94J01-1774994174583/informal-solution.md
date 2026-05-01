# Informal Solution: b94J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

(a) Every finite abelian group G splits uniquely (up to reordering) as a finite direct sum of cyclic p-power groups. Write |G| = (p1^e1)(p2^e2)...(pr^er). For each prime p_i there are integers a_{i,1} ≥ ... ≥ a_{i,r_i} with G isomorphic to a direct sum of copies of Z/(p_i^{a_{i,j}})Z. Equivalently, there exist integers d_1 | d_2 | ... | d_s with G ≅ ⊕_{k=1}^s Z/d_k Z. This is the fundamental theorem of finite abelian groups.

(b) Z/mZ ⊕ Z/nZ is cyclic iff gcd(m,n) = 1. If gcd(m,n) ≠ 1, any element has order dividing lcm(m,n) < mn, so the group cannot be cyclic of size mn. Conversely, pick x = (1 mod m, 1 mod n). When gcd(m,n) = 1 the relation kx = 0 forces m | k and n | k, hence mn | k, so x has order mn and generates.

(c) Let G be a finite subgroup of K^×. Choose g in G of maximal order d. For each divisor e of d the elements whose order divides e are roots of x^e − 1, and a degree-e polynomial has at most e roots in a field. Hence |G| ≤ ∑_{e|d} φ(e) = d, so |G| = d and g already generates. Therefore every finite subgroup of K^× is cyclic.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- (a) relies on primary decomposition G ≅ ⊕ G_p and the structure of finite abelian p-groups.
- (b) uses the formula order((a,b)) = lcm(order a, order b) together with lcm(m,n) = mn ⇔ gcd(m,n) = 1.
- (c) needs the polynomial root bound and the totient identity ∑_{e|d} φ(e) = d.

**Stage 3 — LEAN FORMALIZATION**

Planned declarations:
1. `finiteAbelian_invariantFactors` (restate or add the classification theorem in Mathlib).
2. `zmod_prod_isCyclic_iff (m n : ℕ)` proving `IsCyclic (ZMod m × ZMod n)` ↔ `Nat.Coprime m n`.
3. `finiteMulSubgroup_cyclic (K : Type*) [Field K]` proving every finite subgroup of `Units K` is cyclic.
Progress: established the special-case lemma `zmod_one_prod_isCyclic` (in Main.lean) covering part (b) when m = 1; remaining work is to extend this to general m,n and to formalize (a) and (c).
Execution: tackle the fully general (b) next, then (c) via the polynomial-root argument, and finally reconcile (a) with the existing algebraic hierarchy.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once (b) and (c) are in Lean, cite their lemma names here. If Mathlib lacks part (a), Stage 1 will explicitly point to the missing formal statement so readers know what remains to be mechanized.
