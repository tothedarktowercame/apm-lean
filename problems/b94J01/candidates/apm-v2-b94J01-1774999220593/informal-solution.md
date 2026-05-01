# Informal Solution: b94J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

# Stage 1 – Mathematical write-up
## Why it’s hard
(a) expects the exact statement of the structure theorem, but many prelim takers only remember one of the two equivalent formulations (elementary divisors vs invariant factors) and panic about uniqueness clauses. (b) lures people into staring at generators of \(\mathbf Z/m\mathbf Z\) and \(\mathbf Z/n\mathbf Z\) separately instead of isolating the number-theoretic obstruction: the direct sum is cyclic iff the orders are coprime. (c) looks innocuous (“finite subgroup of \(K^\times\)”) but the usual trick that finite abelian groups split as products is useless unless you pair it with the field fact that a degree-\(d\) polynomial has at most \(d\) roots; missing that interaction leads to cumbersome counting arguments that stall.

## Key insight
All three parts hinge on the same idea: factor the problem into cyclic pieces and use degree bounds on polynomials. (a) is the formal statement of this decomposition. (b) turns the decomposition into a coprimality test on the orders of the cyclic factors. (c) exploits that any finite subgroup of \(K^\times\) lies among the roots of \(x^{|G|}-1\); comparing “at most \(d\) roots in a field” with “at least \(d\) roots coming from a non-cyclic \(p\)-primary component” squeezes the group into being cyclic.

## Complete proof
### (a) Fundamental Theorem of Finite Abelian Groups
Let \(G\) be a finite abelian group of order \(n\). For each prime \(p\), set \(G_p=\{g\in G : g^{p^{v_p(n)}}=1\}\); each \(G_p\) is a subgroup and \(G\cong \bigoplus_p G_p\). Every \(G_p\) is a finite abelian \(p\)-group, so one proves inductively that it is a direct sum of cyclic groups of orders \(p^{e_{p,1}}\ge \dots \ge p^{e_{p,r_p}}\). The multi-set of integers \(p^{e_{p,i}}\) is uniquely determined, and combining the \(G_p\) across all primes produces two equivalent canonical forms:
- **Elementary divisors:** \(G\cong \bigoplus_{p\mid n}\bigoplus_i \mathbf Z/p^{e_{p,i}}\mathbf Z\).
- **Invariant factors:** reordering the summands into a chain of divisibility yields \(G\cong \mathbf Z/d_1\mathbf Z\oplus\cdots\oplus \mathbf Z/d_r\mathbf Z\) with \(d_i\mid d_{i+1}\).
Both forms classify finite abelian groups up to isomorphism and are equivalent.

### (b) When is \(\mathbf Z/m\mathbf Z\oplus\mathbf Z/n\mathbf Z\) cyclic?
Because \(\mathbf Z/m\mathbf Z\) and \(\mathbf Z/n\mathbf Z\) are cyclic, their direct sum is cyclic iff their orders are coprime. If \(\gcd(m,n)=1\), pick \(a\in\mathbf Z/m\mathbf Z\) and \(b\in\mathbf Z/n\mathbf Z\) as the canonical generators; the element \((a,b)\) has order \(\operatorname{lcm}(m,n)=mn\), so it generates. Conversely, if \(d=\gcd(m,n)>1\), then every element \((x,y)\) has order dividing \(\operatorname{lcm}(m,n)=mn/d\), so the group has no element of order \(mn\) and cannot be cyclic. Equivalently, apply the elementary divisor form: \(\mathbf Z/m\mathbf Z\oplus\mathbf Z/n\mathbf Z\) is cyclic iff the prime powers appearing in the two factors never share the same prime, i.e. iff \(m\) and \(n\) are coprime.

### (c) Finite subgroups of \(K^\times\) are cyclic
Let \(G\subset K^\times\) be finite of order \(n\). The field axiom that a degree-\(d\) polynomial has at most \(d\) roots implies that for each positive integer \(d\), the equation \(x^d=1\) in \(K\) admits at most \(d\) solutions. Suppose \(G\) were not cyclic. By the classification in (a), \(G\) contains a subgroup \(H\cong C_{p^{e_1}}\oplus C_{p^{e_2}}\) with the same prime \(p\) in both summands (take two copies from the \(p\)-primary component). Taking \(d=p^{e_1}\) shows \(x^d=1\) has at least \(p^{e_1+e_2}\ge p^{e_1+1}>d\) distinct solutions in \(K\), a contradiction. Hence every prime power shows up at most once, so \(G\) is cyclic.

## What connects / exam field kit
- Coprime-order test for direct sums crops up everywhere: deciding when a product of cyclic groups is cyclic, analyzing invariant factors, or understanding the structure of modules over PID’s.
- The argument for (c) is the same one used to show that every finite subgroup of the complex numbers’ unit circle is the set of \(n\)-th roots of unity—only the “degree at most \(d\)” property of polynomials matters, so it works over arbitrary fields.

# Stage 2 – Target & plan sanity
The main Lean target is `finite_subgroup_units_isCyclic : ∀ {K} [Field K] (G : Subgroup Kˣ) [Fintype G], IsCyclic G`. Helper goals: `(ZMod m × ZMod n)` is cyclic iff `Nat.Coprime m n`, and a lean restatement of the finite-abelian classification to reference in prose. These match the math plan above, pass the HtDP sanity checklist, and are recorded in proof-plan.edn/formal-alignment.edn.

# Stage 3 – Lean attempts & current block
- Verified there is no existing lemma to reuse: `rg -n "finite_subgroup_units_isCyclic" -g"*.lean" /home/joe/code` returned no matches, and broader searches such as `rg -n "Units" -g"IsCyclic"` surfaced only theorems about `RootsOfUnity` that require extra hypotheses.
- The standard proof needs either (i) the full finite-abelian classification inside Mathlib or (ii) a ready-made lemma that any finite subgroup of `Kˣ` embeds into roots of unity of order `|G|` with known cyclicity. Mathlib currently has neither packaged in a way that handles arbitrary fields (the existing `RootsOfUnity.isCyclic` lemmas assume primitive roots).
- Conclusion: Lean development is blocked on introducing a reusable statement such as `lemma IsCyclic.finiteSubgroup_units (G : Subgroup Kˣ) [Fintype G] : IsCyclic G`. Adding it would require formalizing the counting argument for roots of `X^d - 1`, which is non-trivial new work beyond this frame.

# Stage 4 – Next steps
1. Formal side: implement a lemma bounding the size of `{x ∈ K | x^d = 1}` by `d` and combine it with the existing classification of finite abelian `p`-groups to obtain `finite_subgroup_units_isCyclic`. 2. Once available, instantiate it to discharge part (c) and build `zmod_prod_isCyclic_iff` on top of Mathlib’s `IsCyclic` API for ℤ-modules. EOF
