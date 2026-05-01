# Informal Solution: t91J04

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** The statement feels obvious from a picture, so it’s easy to wave your hands and say “the endpoints converge” without justifying why. The trap is forgetting what completeness actually gives you: you need proper use of the supremum (or infimum) of a bounded monotone sequence, and you have to show that limit still lies in every interval.

**Key insight.** Write \(I_n=[a_n,b_n]\) with \(a_n \le b_n\). Nesting implies \(a_n \le a_{n+1}\) and \(b_{n+1}\le b_n\). Thus \((a_n)\) is increasing and bounded above, so \(a:=\sup\{a_n\}\) exists. Each \(b_n\) is an upper bound for the \(a_k\), so \(a \le b_n\). Because \(a\) is a supremum, \(a \ge a_n\) as well. Hence \(a \in [a_n,b_n]\) for all \(n\), proving the intersection is nonempty.

**Complete proof.**  
Write \(I_n=[a_n,b_n]\). The inclusions \(I_{n+1}\subseteq I_n\) give \(a_n \le a_{n+1}\) (lower endpoints move right) and \(b_{n+1} \le b_n\) (upper endpoints move left). Moreover each \(b_n\) is still at least every later \(a_k\), so the sequence \((a_n)\) is bounded above by \(b_1\). By completeness (specifically, the least-upper-bound property of \(\mathbb R\)) the set \(\{a_n : n\in\mathbb N\}\) has a supremum; call it \(a\).

For every \(n\), \(a_n \le a\) because \(a\) is an upper bound. Since \(a\) is the *least* upper bound and each \(b_n\) is an upper bound (thanks to the nesting), \(a \le b_n\). Therefore \(a \in [a_n,b_n]\) for every \(n\), meaning \(a\) sits inside the intersection. Thus
\[
\bigcap_{n=1}^\infty I_n \neq \varnothing.
\]

**What connects.** This is the “nested interval property,” equivalent to completeness and used to prove the Bolzano–Weierstrass theorem, the bisection method for root finding, and the skeletal version of the Cantor intersection theorem. If an exam problem mentions “closed intervals” and “nesting,” you should reflexively think “supremum/infimum argument.”

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- `:s1` (monotone endpoints) → translates the set-theoretic inclusion \(I_{n+1}\subseteq I_n\) into inequalities \(a_n\le a_{n+1}\), \(b_{n+1}\le b_n\), and \(a_n\le b_n\).
- `:s2` (bounded-monotone convergence) → via completeness, turns \((a_n)\) into its limit \(a=\sup a_n\).
- `:s3` (closedness of intervals) → guarantees that limits of points from \(I_n\) remain in \(I_n\), finishing the nonemptiness claim.

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/t91J04/apm-v2-t91J04-1775008373965/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/t91J04/apm-v2-t91J04-1775008373965/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

- Added `nonempty_nested_inter` to `/home/joe/code/apm-lean/ApmCanaries/Frames/T91J04/Apm_v2_t91J04_1775008373965/Main.lean`, instantiating mathlib’s Cantor intersection theorem (`IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`) with the intervals \([a_n,b_n]\).  
- `lake build` succeeds; as usual the only warnings are the unrelated unused-variable notices in `ApmCanaries/C2Analysis.lean` and `ApmCanaries/C4Functional.lean`.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Lean’s proof highlights that the hard work is hidden in compactness: each \([a_n,b_n]\) is compact, the family is decreasing, so the intersection is nonempty. Translating back inspired the Stage 1 structure—either phrase the argument with suprema (direct completeness) or cite compactness. I kept the supremum-based exposition but mentioned the compact viewpoint as part of the “what connects” section, since that’s the gateway to general Cantor-type theorems.
