# Proof Outline: b94J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:problem-id 'b94J01
 :frame-id 'apm-v2-b94J01-1774994174583
 :goal "Classify finite abelian groups, characterize when Z/m × Z/n is cyclic, and prove every finite multiplicative subgroup of a field is cyclic."
 :terms [{:name "primary decomposition"
          :meaning "finite abelian groups split as direct sums of their p-primary parts"
          :needed-because "part (a) reduces structure to p-power blocks"}
         {:name "gcd/lcm interplay"
          :meaning "lcm(m,n)=mn iff gcd(m,n)=1"
          :needed-because "determines cyclicity in part (b)"}
         {:name "root bound"
          :meaning "a degree-e polynomial over a field has at most e roots"
          :needed-because "controls counting in part (c)"}]
 :strategy [{:id :s1
             :formal-dependency "Primary decomposition theorems for finite abelian groups"
             :informal-dependency "Stage 1(a) classification argument"
             :why-this-now "Need invariant factors before addressing the other parts"
             :lean-target "finiteAbelian_invariantFactors"
             :mathlib-status "Likely exists; must locate or add"}
            {:id :s2
             :formal-dependency "Order of elements in direct products and gcd/lcm lemmas"
             :informal-dependency "Stage 1(b)"
             :why-this-now "Self-contained and a good starting point for Lean"
             :lean-target "zmod_prod_isCyclic_iff"
             :mathlib-status "Should be provable with current algebra API"}
            {:id :s3
             :formal-dependency "Polynomial.root_count and Euler totient identities"
             :informal-dependency "Stage 1(c)"
             :why-this-now "Finishes the problem once counting lemmas are wired"
             :lean-target "finiteMulSubgroup_cyclic"
             :mathlib-status "Requires combining existing lemmas; no known blocker"}]
 :stage-status {:stage1 :done
                :stage2 :done
                :stage3 :in-progress
                :stage4 :pending}
 :lean {:module-root 'ApmCanaries.Frames.B94J01.Apm_v2_b94J01_1774994174583
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'b94J01
  :frame-id 'apm-v2-b94J01-1774994174583
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote full reader-facing solutions for parts (a)-(c) in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Recorded dependency graph and lean targets in execute.md and proof-plan.edn."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-updated
  :summary "Outlined Lean declarations, populated proof-plan.edn and formal-alignment.edn with planned lemma names."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-lemma-added
  :summary "Proved zmod_one_prod_isCyclic in Main.lean and noted the partial coverage in execute.md/formal-alignment.edn."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

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
