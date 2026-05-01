# Informal Solution: b93J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

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
