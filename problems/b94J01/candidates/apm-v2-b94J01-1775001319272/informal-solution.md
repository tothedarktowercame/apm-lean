# Informal Solution: b94J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

***Why it’s hard.***  Part (a) asks for the full classification of finite Abelian groups, which many students recall only in one of its two equivalent forms (elementary divisors vs. invariant factors) and often forget the uniqueness clause. Part (b) tempts people to look for explicit generators of \( \mathbf Z/m \oplus \mathbf Z/n \) without first noticing that it is cyclic iff no non-trivial element has order dividing \(\gcd(m,n)\); missing the gcd obstruction is the classic trap. Part (c) looks elementary but really needs two ingredients: the additive structure from (a) (finite subgroups of \(K^\times\) are finite Abelian groups) and the simple fact that a degree-\(d\) polynomial over a field has at most \(d\) roots. Forgetting to use the degree bound leaves one with no way to show a second independent \(p\)-primary component cannot exist.

***Key insight.***  Package the problem as “finite Abelian groups are products of cyclic \(p\)-power factors, and that description is unique.” From there: (b) becomes the special case of a product of two cyclic groups—hence cyclic iff their orders are coprime. For (c) factor \(G\) into its \(p\)-primary components; each gives more than \(d\) roots of some \(x^d-1\) unless it is cyclic, contradicting the fact that polynomials over fields have only finitely many roots.

***Complete proof.***

1. *(a) Fundamental Theorem of Finite Abelian Groups.*  Every finite Abelian group \(G\) is, up to isomorphism, either (elementary-divisor form) a finite direct product of cyclic groups of prime-power order \( \mathbf Z/p_1^{e_1}\mathbf Z \oplus \cdots \oplus \mathbf Z/p_r^{e_r}\mathbf Z \) or (invariant-factor form) \( \mathbf Z/d_1\mathbf Z \oplus \cdots \oplus \mathbf Z/d_s\mathbf Z \) with \(d_i \mid d_{i+1}\). Both descriptions are unique: the multiset of prime powers \(p_i^{e_i}\) and the chain of invariant factors \(d_i\) are determined by \(G\).

2. *(b) Coprime criterion for \( \mathbf Z/m \oplus \mathbf Z/n \).*  Since \( \mathbf Z/m \) and \( \mathbf Z/n \) are cyclic of orders \(m\) and \(n\), their direct sum is cyclic iff their orders are coprime. If \(\gcd(m,n)=1\), then \((1,1)\) has order \(\mathrm{lcm}(m,n)=mn\), hence generates. Conversely, if a prime \(p\) divides both \(m\) and \(n\), every element \((a,b)\) has order dividing \(\mathrm{lcm}(m,n) \le mn/p\), so no element has order \(mn\); thus the group cannot be cyclic.

3. *(c) Finite subgroups of \(K^\times\) are cyclic.*  Let \(G\subseteq K^\times\) be finite of order \(N\). View \(G\) as a finite Abelian group and decompose it into its Sylow \(p\)-subgroups. Suppose two distinct \(p\)-primary components contribute: then \(G\) would contain at least \(p^2-1\) elements of order dividing \(p^e\), so the polynomial \(x^{p^e}-1\) would have more than \(p^e\) roots in the field \(K\), impossible. Hence each \(p\)-primary component is cyclic, and the components corresponding to distinct primes commute and have coprime orders, so their product is cyclic (apply part (b) repeatedly). Therefore \(G\) itself is cyclic.

***What connects.***  The three subproblems are standard “finite Abelian” moves: invariant factors (for presentations), coprime-order products (for detecting cyclicity), and bounding the number of torsion points via the polynomial \(x^n-1\). Exactly the same toolkit shows, for instance, that the group of \(n\)-torsion points on an elliptic curve over \( \mathbf C \) is \( (\mathbf Z/n)^2 \) and that finite subgroups of the multiplicative group of a complex torus are cyclic.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Finite Abelian classification.*  Conceptual starting point; no Mathlib analogue is needed for the write-up.
- *AddGroup.isAddCyclic_prod_iff* (Mathlib `GroupTheory/SpecificGroups/Cyclic`).  Converts part (b) into the numerical condition \((\mathrm{card}\,A,\mathrm{card}\,B)=1\).
- *Nat.card_zmod* (Mathlib `Data/ZMod/QuotientGroup`).  Identifies \(\mathrm{card}\,\mathbf Z/m\mathbf Z = m\) when \(m>0\), finishing the gcd argument.
- *Subgroup.isCyclic_subgroup_units* (Mathlib `RingTheory/IntegralDomain`).  Gives part (c) directly: any finite subgroup of \(K^\times\) is cyclic.

Machine-readable artifacts: `proof-plan.edn` and `formal-alignment.edn` in this workspace record the same dependencies.

**Stage 3 — LEAN FORMALIZATION**

- *Type signatures.*  
  - `finite_mul_subgroup_cyclic {K} [Field K] (G : Subgroup Kˣ) [Finite G] : IsCyclic G` (Main.lean).  
  - `zmod_prod_cyclic_iff {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
      IsAddCyclic (ZMod m × ZMod n) ↔ Nat.Coprime m n` (same file).
- *Search & ingredients.*  `rg -n "IsCyclic_prod_iff"` and inspection of `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean` located `AddGroup.isAddCyclic_prod_iff`. `rg -n "finite subgroup" .lake/packages` pointed to `Mathlib/RingTheory/IntegralDomain.lean`, which already implements the cyclicity of finite subgroups of units (`Subgroup.isCyclic_subgroup_units`). `Nat.card_zmod` supplied the needed cardinality rewrite.
- *Wiring.*  `Main.lean` now instantiates those lemmas: `finite_mul_subgroup_cyclic` is the direct specialization via `infer_instance`, and `zmod_prod_cyclic_iff` chains `AddGroup.isAddCyclic_prod_iff` with the known cyclicity of each `ZMod` factor and the cardinality lemma.  `lake build` (run from `/home/joe/code/apm-lean`, output logged above) succeeds, so the frame-local Lean code type-checks.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

- Part (b) of the prose proof now mirrors the Lean lemma `zmod_prod_cyclic_iff`, so the “coprime iff cyclic” criterion is justified.  
- Part (c) explicitly appeals to the root-counting argument, while the Lean proof uses Mathlib’s finished version `Subgroup.isCyclic_subgroup_units`; no further translation is required.  
- Any future generalization (e.g., more factors than two in part (b)) can reuse the Lean helper by induction, matching the invariant-factor discussion in Stage 1.
