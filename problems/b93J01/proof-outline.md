# Proof Outline: b93J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Closer hop 1 (2026-08-08)

Three independent components now compile: the orders of `A₄` and `S₃`, and
Lagrange's divisibility theorem for every finite subgroup. The helpers use
`card_alternatingGroup`, `Fintype.card_perm`, and
`Subgroup.card_subgroup_dvd_card`.

The remaining statement requires several classification developments absent
from this Mathlib snapshot: simplicity of all alternating groups of degree at
least five, classification of groups of order eight, the finite-abelian
structure theorem in the custom `iSupIndep` encoding, and the order-`pq`
cyclicity theorem. The main theorem remains partial with one `sorry`; its
frozen statement is unchanged.

## Imported Proof Plan

```clojure
{:goal "Give counterexamples to each false statement and record precise corrected theorems."
 :terms [{:name "simplicity of A_n"
          :meaning "A_n is simple exactly when n is at least five."
          :needed-because "Statement (a) fails at n=3,4; we must know the correct range."
         }
         {:name "classification of order-eight groups"
          :meaning "The five types are Zmod8, Z4 x Z2, Z2 x Z2 x Z2, D4, and Q8."
          :needed-because "Statement (b) omits the elementary abelian and quaternion cases."
         }
         {:name "Sylow and Cauchy"
          :meaning "Guarantee subgroups only for prime divisors or prime powers."
          :needed-because "Statement (c) overreaches; S3 and A4 give counterexamples."
         }
         {:name "structure theorem"
          :meaning "Only finitely generated abelian groups split as direct sums of cyclic groups."
          :needed-because "Statement (d) ignores groups like Q or Prüfer p-groups."
         }
         {:name "groups of order pq"
          :meaning "For primes p<q, a group of order pq is cyclic exactly when p does not divide q-1."
          :needed-because "Statement (e) ignores the semidirect-product cases."
         }]
 :strategy [{:id :s1
             :formal-dependency "simplicity_of_An_for_large_n"
             :informal-dependency "Show A3 and A4 have normal subgroups; cite the n>=5 simplicity theorem."
             :why-this-now "Fixes part (a)."
             :lean-target "GroupTheory.Alt.simplicity"
             :mathlib-status "Mathlib already proves simplicity for n>=5."}
            {:id :s2
             :formal-dependency "order_8_classification"
             :informal-dependency "List the missing isomorphism types (Z2 x Z2 x Z2 and Q8)."
             :why-this-now "Fixes part (b)."
             :lean-target "Group.orderEight_classification"
             :mathlib-status "Finite order-eight classification is standard."}
            {:id :s3
             :formal-dependency "Sylow_theory"
             :informal-dependency "Use S3 or A4 to show no subgroup exists for every divisor; restate Sylow."
             :why-this-now "Fixes part (c)."
             :lean-target "GroupTheory.sylow"
             :mathlib-status "Sylow theorems formalized."}
            {:id :s4
             :formal-dependency "fg_abelian_structure"
             :informal-dependency "Give Q or a Prüfer group as counterexample; corrected version restricts to finitely generated groups."
             :why-this-now "Fixes part (d)."
             :lean-target "FinitelyGeneratedAbelian.structure"
             :mathlib-status "Structure theorem already proven."}
            {:id :s5
             :formal-dependency "order_pq_classification"
             :informal-dependency "Explain the p divides (q-1) criterion and exhibit the semidirect-product counterexample."
             :why-this-now "Fixes part (e)."
             :lean-target "Group.order_pq_classification"
             :mathlib-status "Available in Mathlib finite-group library."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'b93J01'
  :frame-id 'apm-v2-b93J01-1775006040768'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full reader-facing solution: counterexamples for (a)–(e), the corrected theorems, and the study-notes sections (Why it’s hard, Key insight, What connects)."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Expanded the lemma dependency graph text plus the machine-readable plan to spell out the counterexample strategy for each bullet."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Added Lean lemmas `Examples.card_sym3`, `Examples.sym3_not_isCyclic`, and `Examples.card_zmod2_cubed`; ran `lake build` (clean). Remaining gaps: formal non-simplicity of A4 and the Sylow/structure-theorem statements."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** Each sentence *almost* echoes a textbook theorem, so it is tempting to accept it without checking the hidden hypotheses: simplicity of alternating groups requires \(n \ge 5\); classifying groups of order eight forces you to remember the elementary abelian and quaternion cases; Sylow’s theorem speaks only about prime powers, not every divisor; the structure theorem for abelian groups assumes finite generation; and finite groups of order \(pq\) are not always cyclic because semidirect products may exist whenever \(p \mid (q-1)\). Missing any one of these caveats leaves you with no counterexample in mind on exam day.

**Key insight.** Track the *first* obstruction that breaks each claim: \(A_n\) fails at \(n=4\); order-eight groups need five models; \(A_4\) has no subgroup of order six although 6 divides 12, so “every divisor” is wrong; \(\mathbb Q\) and the Prüfer \(p\)-groups are abelian yet not direct sums of cyclic groups; and \(S_3\) gives the prototypical non-cyclic group of order \(pq\) because \(2\mid (3-1)\).

**Complete solution.**
- **(a)** The statement is false at \(n=4\) because \(A_4\) contains the Klein four subgroup \(V=\{(),(12)(34),(13)(24),(14)(23)\}\), which is normal (conjugation permutes the three double transpositions). Thus \(A_4\) is not simple. The correct theorem is: “\(A_n\) is simple iff \(n=3\) (prime order) or \(n\ge 5\).” (More precisely, \(A_3\cong C_3\) is simple because it has prime order, while \(A_n\) is simple for every \(n\ge 5\).)
- **(b)** Besides the three listed groups there are two more isomorphism types of order eight: the elementary abelian group \((\mathbb Z/2\mathbb Z)^3\) (all elements of order 2) and the quaternion group \(Q_8=\{\pm1,\pm i,\pm j,\pm k\}\). Thus the corrected classification reads: “Up to isomorphism there are five groups of order eight: \(\mathbb Z/8\mathbb Z,\ \mathbb Z/4\mathbb Z\oplus\mathbb Z/2\mathbb Z,\ (\mathbb Z/2\mathbb Z)^3,\ D_4,\ Q_8\).”
- **(c)** Let \(G=A_4\). Its order is 12, yet it has no subgroup of order six: any subgroup of index two would be normal, but every normal subgroup of \(A_4\) lies inside \(V\) and has order 1, 2, or 4. Hence the blanket statement fails. The correct version is Lagrange/Sylow: “If \(p^k\) divides \(|G|\) (with \(p\) prime), then \(G\) has a subgroup of order \(p^k\).” No general theorem guarantees subgroups for arbitrary divisors that are not prime powers.
- **(d)** The countable abelian group \(\mathbb Q\) (under addition) is not a direct sum of cyclic groups: every element has infinite divisibility, whereas a direct sum of cyclic groups contains elements whose orders have bounded \(p\)-power divisibility on each coordinate. Similarly the Prüfer \(p\)-group \(\mathbb Z_{p^\infty}\) fails to split as a direct sum of cyclics. The standard correction is: “Every **finitely generated** abelian group is isomorphic to a direct sum of cyclic groups.”
- **(e)** Take \(p=2, q=3\): the symmetric group \(S_3\) has order six but is non-abelian, hence not cyclic. More generally, for primes \(p<q\) a group of order \(pq\) is cyclic iff \(p\nmid (q-1)\); if \(p\mid(q-1)\) there exists a non-abelian semidirect product \(\mathbb Z/q \rtimes \mathbb Z/p\).

**What connects.** Every fix hinges on remembering the exact hypotheses of the textbook theorems (Jordan–Hölder for alternating groups, Sylow/Cauchy, the structure theorem for finitely generated abelian groups, and the classification of groups of order \(pq\)). The exam-day mantra is: “Identify the missing hypothesis, supply a concrete counterexample, and then quote the precise theorem.”

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *(a)* Use the known Klein four subgroup of \(A_4\) to witness non-simplicity; rely on the theorem “\(A_n\) is simple for \(n\ge5\).”
- *(b)* Exhibit \((\mathbb Z/2)^3\) (all elements order 2) and \(Q_8\) (Hamilton quaternion) as additional order-eight groups; invariant used: exponent/abelian vs non-abelian.
- *(c)* Apply Sylow theory to describe all normal subgroups of \(A_4\); deduce absence of a subgroup of order six; corrected statement references Sylow/Cauchy.
- *(d)* Compare \(\mathbb Q\) or \(\mathbb Z_{p^\infty}\) with a direct sum of cyclic groups using divisibility arguments; cite the structure theorem for finitely generated abelian groups.
- *(e)* Deploy the classification of order-\(pq\) groups: if \(p\nmid(q-1)\) the group is cyclic, otherwise there is a non-abelian semidirect product (e.g. \(S_3\) for \(p=2,q=3\)).

(Full machine-readable plan: `/home/joe/code/futon6/.state/proof-frames/b93J01/apm-v2-b93J01-1775006040768/proof-plan.edn`.)

**Stage 3 — LEAN FORMALIZATION**

Implemented concrete counterexample lemmas:
- `SymmetricGroup (Fin 3)` has cardinality 6 and is not cyclic (witnessing part (e)).
- The elementary abelian group `(ZMod 2) × (ZMod 2) × (ZMod 2)` has order 8 and exponent 2, hence cannot be isomorphic to `ZMod 8` or `ZMod 4 × ZMod 2`, covering the missing order-eight types.
Remaining Lean gap: Mathlib currently lacks ready-made declarations that `A4` is not simple and that `A4` has no subgroup of order six, so completing formal counterparts to parts (a) and (c) would require building those subgroup analyses from scratch. Notes on closing the gap are recorded inline in `Main.lean`.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean witnesses exactly match the narrative invariants: non-cyclicity of `S₃` mirrors the semidirect-product obstruction in (e), and the exponent-2 argument for `(Z/2)^3` formalizes the “missing” order-eight groups in (b). What still sits outside Lean (A₄’s lattice of normal subgroups and the non-finitely-generated abelian examples) is explicitly called out in Stage 3 so a future pass knows precisely which theorems must be added.
