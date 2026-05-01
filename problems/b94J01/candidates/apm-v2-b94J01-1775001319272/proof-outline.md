# Proof Outline: b94J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Solve parts (a)–(c) of apm-b94J01: state the finite-Abelian classification, decide when ZMod m ⊕ ZMod n is cyclic, and prove every finite subgroup of Kˣ is cyclic."
 :terms [{:name "finite Abelian classification"
          :meaning "Every finite Abelian group decomposes either into p-power cyclic factors or into invariant factors d₁ | d₂ | …"
          :needed-because "Part (a) is the statement itself and feeds the intuition for parts (b) and (c)."}
         {:name "IsCyclic.prod_iff"
          :meaning "A product of two finite groups is cyclic iff each factor is cyclic and their orders are coprime."
          :needed-because "Part (b) reduces to checking gcd(m,n)=1 and noting that ZMod m, ZMod n are cyclic."}
         {:name "finite subgroup of units is cyclic"
          :meaning "Any finite subgroup of the units of a domain (hence of a field) is cyclic."
          :needed-because "This gives part (c) once we view G as a finite subgroup of Kˣ."}]
 :strategy [{:id :s1
             :formal-dependency "GroupTheory/SpecificGroups/Cyclic for statements about cyclic groups"
             :informal-dependency "Stage 1 summary of the classification theorem"
             :why-this-now "Sets the global structure that the later parts exploit."
             :lean-target "Document only (Mathlib has no full finite-Abelian classification)."
             :mathlib-status "Covered informally; no Mathlib analogue yet."}
            {:id :s2
             :formal-dependency "AddGroup.isAddCyclic_prod_iff and the fact that ZMod n is cyclic"
             :informal-dependency "Stage 1 step describing gcd criterion for Z/m ⊕ Z/n"
             :why-this-now "Provides the necessary-and-sufficient condition in part (b)."
             :lean-target "theorem zmod_prod_cyclic_iff"
             :mathlib-status "Follows from `AddGroup.isAddCyclic_prod_iff`; available in Mathlib."}
            {:id :s3
             :formal-dependency "Mathlib/RingTheory/IntegralDomain: `Subgroup.isCyclic_subgroup_units`"
             :informal-dependency "Stage 1 argument that finite subgroups of Kˣ are cyclic"
             :why-this-now "Delivers part (c) verbatim."
             :lean-target "theorem finite_mul_subgroup_cyclic"
             :mathlib-status "Already in Mathlib as an instance on finite subgroups of units."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :done :stage4 :done}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'b94J01'
  :frame-id 'apm-v2-b94J01-1775001319272'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full textual solution with why-hard analysis, key insight, detailed proofs for (a)–(c), and connections."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Populated proof-plan.edn/formal-alignment.edn with the finite-Abelian classification, product cyclicity, and unit-subgroup lemmas."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-completed
 :summary "Implemented `finite_mul_subgroup_cyclic` and `zmod_prod_cyclic_iff` in Main.lean and verified with `lake build`."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage4-completed
  :summary "Documented how the Lean lemmas justify the prose solution and how to reuse them for extensions."
  :full-record? true
  :sorry? false
  :fully-closed? true}]
```

## Imported Execution Notes

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
