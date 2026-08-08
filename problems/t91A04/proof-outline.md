# Proof Outline: t91A04

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Closer hop 1 (2026-08-08)

The theorem is closed by the already compiled authoritative-frame proof
`contraction_fixedPoint`. The real constant is bundled as an `NNReal`, the
given distance estimate becomes `LipschitzWith.of_dist_le_mul`, and Mathlib's
`ContractingWith.fixedPoint_isFixedPt` and `fixedPoint_unique` supply existence
and uniqueness. The frozen statement is unchanged and the proof is sorry-free.

## Imported Proof Plan

```clojure
{:problem-id 't91A04
 :frame-id 'apm-v2-t91A04-1775008241824
 :goal "Prove the Banach fixed point theorem for a λ-contraction T on a complete metric space M."
 :terms [{:name "λ-contraction"
          :meaning "A map satisfying d(Tx,Ty) ≤ λ d(x,y) with λ∈[0,1)."
          :needed-because "This inequality is the engine that makes the iterates Cauchy and yields uniqueness."}
         {:name "Cauchy estimate for iterates"
          :meaning "Bounds of the form d(T^m x, T^n x) ≤ λ^n/(1-λ)·d(Tx,x)."
          :needed-because "Gives a concrete tail control showing {T^n x} is Cauchy."
         }
         {:name "completeness of M"
          :meaning "Every Cauchy sequence converges in M."
          :needed-because "Supplies the candidate limit y and allows passing the contraction inequality to the limit to show T y = y."}]
 :strategy [{:id :s1
             :formal-dependency "contraction estimates → completeness → uniqueness"
             :informal-dependency "Stage 1 plan: iterate T, prove the sequence is Cauchy via geometric decay, extract its limit y using completeness, then verify T y = y and uniqueness."
             :why-this-now "This is the standard Banach fixed-point argument and matches mathlib’s `ContractingWith.exists_unique_fixedPoint`."
             :lean-target "ApmCanaries.Frames.T91A04.Apm_v2_t91A04_1775008241824.contraction_fixedPoint"
             :mathlib-status "mathlib has `ContractingWith.exists_unique_fixedPoint` in `Topology/Bornology`. We'll wrap it for this metric-space setting."}]
 :stage-status {:stage1 :done
                :stage2 :done
                :stage3 :in-progress
                :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't91A04'
  :frame-id 'apm-v2-t91A04-1775008241824'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the Banach fixed-point argument (why hard/key insight + full proof) in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Captured how the contraction estimate, completeness, and uniqueness pieces depend on one another."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-completed
  :summary "Implemented `contraction_fixedPoint` via mathlib’s `ContractingWith` and ran `lake build`."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage4-completed
  :summary "Explained how the Lean API (geometric tails + `fixedPoint_unique`) streamlines the informal proof."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** You have to use completeness only once, but identifying exactly *what* sequence is Cauchy trips people up. It is tempting to hope that \((x_n)\) converges simply because distances shrink, yet without a geometric tail bound this argument collapses. Forgetting to keep track of the geometric series \(\sum λ^k\) is the common failure point.

**Key insight.** Iterate \(T\) starting from any \(x\in M\). The contraction inequality produces the quantitative estimate
\[
d(T^{n+m}x,T^n x)\le λ^n \frac{d(Tx,x)}{1-λ},
\]
so \(\{T^n x\}\) is Cauchy. Completeness gives a limit \(y\), and continuity of \(T\) (it is 1-Lipschitz) lets you pass the limit through \(T\) to obtain \(T y = y\). If two fixed points existed, the contraction inequality would force their distance to satisfy \(d(z_1,z_2) \le λ d(z_1,z_2)\), hence they are equal.

**Complete proof.**  
Let \(x \in M\) and set \(x_n := T^n(x)\).

1. **The iterates are Cauchy.** For \(m \ge 0\) we have
   \[
   d(x_{n+m},x_n) \le λ^n d(x_m,x_0) \le λ^n \sum_{k=0}^{m-1} λ^k\, d(x_1,x_0)
   \le \frac{λ^n}{1-λ} d(x_1,x_0).
   \]
   Thus, given \(\varepsilon>0\), choose \(N\) with \(λ^N d(x_1,x_0)/(1-λ)<\varepsilon\); then \(d(x_{n+m},x_n)<\varepsilon\) for all \(n\ge N\), showing \((x_n)\) is Cauchy.

2. **Existence of a limit and fixed point.** As \(M\) is complete, \(x_n\to y\) for some \(y\in M\). Since \(T\) is Lipschitz with constant \(λ<1\), it is continuous, so
   \[
   T y = T\bigl(\lim_{n\to\infty} x_n\bigr)
       = \lim_{n\to\infty} T x_n
       = \lim_{n\to\infty} x_{n+1}
       = y.
   \]
   Hence \(y\) is a fixed point.

3. **Uniqueness.** Suppose \(y,z\) are fixed points. Then
   \[
   d(y,z)=d(T y,T z)\le λ d(y,z).
   \]
   Because \(λ<1\), the only nonnegative number equal to a strict contraction of itself is \(0\), so \(d(y,z)=0\) and \(y=z\).

Therefore \(T\) has a unique fixed point.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- `:s1` (contractive iterate estimates) — the geometric decay bound that makes \((T^n x)\) Cauchy.
- `:s2` (completeness of \(M\)) — extracts the limit of the Cauchy sequence.
- `:s3` (contraction plus uniqueness) — uses the contraction inequality to pass limits through \(T\) and to rule out distinct fixed points.

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/t91A04/apm-v2-t91A04-1775008241824/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/t91A04/apm-v2-t91A04-1775008241824/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

- Added `contraction_fixedPoint` in `/home/joe/code/apm-lean/ApmCanaries/Frames/T91A04/Apm_v2_t91A04_1775008241824/Main.lean`. The implementation packages the given inequality into mathlib’s `ContractingWith` structure and instantly recovers the fixed point via `ContractingWith.fixedPoint`.  
- `lake build` succeeds. The only warnings are the long-standing unused-variable notices in `ApmCanaries/C2Analysis.lean` and `ApmCanaries/C4Functional.lean`; the new lemma introduces none.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The formal proof emphasized how everything flows from the `ContractingWith` API: once you’ve encoded the contraction constant, the Cauchy estimate, existence, and uniqueness are off-the-shelf. That prompted me to highlight the geometric tail bound and uniqueness argument explicitly in Stage 1, mirroring the structure of `ContractingWith.toLipschitzWith` and `fixedPoint_unique`.
