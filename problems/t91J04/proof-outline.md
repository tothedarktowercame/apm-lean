# Proof Outline: t91J04

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:problem-id 't91J04
 :frame-id 'apm-v2-t91J04-1775008373965
 :goal "Use the completeness of ℝ to prove the intersection of a nested sequence of closed intervals is nonempty."
 :terms [{:name "monotone endpoint sequences"
          :meaning "Write each I_n = [a_n,b_n] with (a_n) increasing and (b_n) decreasing."
          :needed-because "Tracking the endpoints converts the geometric picture into numerical sequences amenable to completeness arguments."}
         {:name "bounded monotone convergence"
          :meaning "Increasing (resp. decreasing) bounded sequences in ℝ converge."
          :needed-because "Allows us to take limits a = lim a_n and b = lim b_n and keep them inside every interval."}
         {:name "closedness of intervals"
          :meaning "Closed intervals contain their limit points."
          :needed-because "Ensures the limit of the endpoints (or any point between them) belongs to all I_n."}]
 :strategy [{:id :s1
             :formal-dependency "monotone convergence + closedness of intervals"
             :informal-dependency "Stage 1 plan: extract endpoints, show (a_n) ↑ and bounded, (b_n) ↓ and bounded, use completeness to define a = sup a_n, show a ≤ b_n for all n, and conclude a ∈ ⋂ I_n."
             :why-this-now "This is the standard nested-interval argument directly tied to the completeness axiom of ℝ."
             :lean-target "ApmCanaries.Frames.T91J04.Apm_v2_t91J04_1775008373965.nonempty_nested_inter"
             :mathlib-status "mathlib has `IsClosed.nhds_limit` facts plus a `nested_inter_nonempty` lemma for compact sets; we’ll restate it in this concrete ℝ setting."}]
 :stage-status {:stage1 :done
                :stage2 :done
                :stage3 :in-progress
                :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't91J04'
  :frame-id 'apm-v2-t91J04-1775008373965'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Explained the nested-interval argument (why hard/key insight + full proof) in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Recorded how monotone endpoints, completeness, and closedness of intervals chain together."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-completed
  :summary "Formalized the statement as `nonempty_nested_inter` via the compact Cantor intersection lemma and ran `lake build`."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage4-completed
  :summary "Reflected how the Lean proof (compactness viewpoint) clarifies the informal supremum argument."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

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
