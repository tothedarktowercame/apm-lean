# Proof Outline: b94J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Explain the structure theorem for finite abelian groups, characterize when ℤ/m ⊕ ℤ/n is cyclic, and use those facts to prove every finite subgroup of a field’s multiplicative group is cyclic."
 :terms [{:name "Fundamental Theorem of Finite Abelian Groups"
          :meaning "Every finite abelian group decomposes uniquely (up to order) into a direct product of cyclic p-power groups"
          :needed-because "It supplies the template for parts (b) and (c)."}
         {:name "coprime decomposition"
          :meaning "ℤ/m ⊕ ℤ/n is cyclic iff gcd(m,n)=1"
          :needed-because "Part (b) isolates when the direct sum collapses to a single cyclic group."}
         {:name "maximal-order element"
          :meaning "In a finite abelian group, an element of maximum order generates the whole group"
          :needed-because "Part (c) finds such an element inside a finite subgroup of K×."}]
 :strategy [{:id :s1
             :formal-dependency "Structure theorem; lemmas on orders of elements; basic facts about polynomials x^k − 1."
             :informal-dependency "Describe the decomposition, show the coprime condition forces a single cyclic factor, then observe that the product of all distinct prime-power generators has order equal to |G|."
             :why-this-now "Part (c) is almost immediate once (a) and (b) clarify how cyclic factors behave."
             :lean-target "Lemma: finite abelian groups over a field’s units are cyclic; reuse Mathlib’s classification of finite abelian groups."
             :mathlib-status "Mathlib knows that finite subgroups of a field’s units are cyclic, so the formal part reduces to restating the existing theorem."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :pending :stage4 :pending}
 :lean {:module-root 'ApmCanaries.Frames.B94J01.Apm_v2_b94J01_1774992341688'
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'b94J01'
  :frame-id 'apm-v2-b94J01-1774992341688'
  :summary "Created the isolated frame with plan/changelog and Lean stubs."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full three-part solution: stated the structure theorem, proved the gcd criterion, and showed finite subgroups of K× are cyclic."
  :full-record? true
  :sorry? false
  :fully-closed? true}
 {:kind :stage2-completed
  :summary "Recorded the dependency plan (structure theorem → coprime criterion → maximal-order generator)."
  :full-record? true
  :sorry? false
  :fully-closed? true}
 {:kind :stage3-progress
  :summary "Noted that Main.lean still needs to import Mathlib’s classification/cyclicity lemmas; no Lean code has been written yet."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

(a) *Fundamental Theorem of Finite Abelian Groups.*  Every finite abelian group \(G\) is a finite direct product of cyclic \(p\)-power groups, and this decomposition is unique up to ordering.  Concretely,
\[
G\cong \bigoplus_{p\ \text{prime}} \bigoplus_{i=1}^{r_p} \mathbb Z/p^{e_{p,i}}\mathbb Z,
\]
with \(e_{p,1}\ge e_{p,2}\ge\cdots\).  Equivalently, \(G\) can be written as a product of cyclic groups whose orders divide one another.

(b) *When is \(\mathbb Z/m\oplus \mathbb Z/n\) cyclic?*  The group is cyclic iff \(\gcd(m,n)=1\).  Proof: write the invariant-factor decompositions \(m=\prod p^{a_p}\) and \(n=\prod p^{b_p}\).  The direct sum is isomorphic to the direct product over primes of \(\mathbb Z/p^{a_p}\oplus \mathbb Z/p^{b_p}\), so it is cyclic exactly when each prime contributes at most one nontrivial factor, i.e. for every \(p\) at most one of \(a_p,b_p\) is positive—equivalently, \(\gcd(m,n)=1\).

(c) *Finite subgroups of \(K^\times\) are cyclic.*  Let \(G\subset K^\times\) be finite.  Then \(G\) is abelian and finite, so the structure theorem applies: \(G\cong \bigoplus_i \mathbb Z/n_i\) with \(n_1\mid n_2\mid \cdots\).  Let \(g_i\) be elements of order \(n_i\).  Because the \(n_i\) divide one another, the product \(g=g_1\cdots g_r\) has order \(\text{lcm}(n_1,\dots,n_r)=n_r=|G|\), so \(g\) generates \(G\); hence \(G\) is cyclic.  Alternatively, use the hint: let \(d\) be the maximum order of an element; every element of \(G\) is a root of \(x^d-1\), so \(x^d-1\) has at most \(d\) roots, forcing \(d=|G|\) and giving a generator of order \(|G|\).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *FTA of finite abelian groups* is the foundational fact for (a).
- *Coprime condition* uses the primary decomposition to reduce \(\mathbb Z/m\oplus \mathbb Z/n\) to its \(p\)-parts.
- *Maximal-order element* combines the divisibility chain of orders with the polynomial-root bound in the hint.

**Stage 3 — LEAN FORMALIZATION**

`Main.lean` has not been populated yet.  Mathlib already contains both statements we need: the classification of finite abelian groups and the theorem `Finite.mulGroup_isCyclic` saying finite subgroups of a field’s units are cyclic.  The formal work would mostly consist of re-exporting these facts in the frame’s namespace.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the existing Mathlib lemmas are invoked, the Lean proof will match the reasoning above exactly.  No further reconciliation is needed.
