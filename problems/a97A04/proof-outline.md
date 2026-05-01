# Proof Outline: a97A04

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that the set of points where (f_n(x)) converges is measurable."
 :terms [{:name "Cauchy characterization"
          :meaning "Sequence converges iff (∃N)∀n,m≥N, |f_n-f_m|<ε. Limit to ε=1/k."
          :needed-because "It rewrites convergence as a countable intersection/union of inequalities between measurable functions."}
         {:name "stability of measurability"
          :meaning "If f_n are measurable, so are |f_n-f_m| and their sublevel sets."
          :needed-because "Ensures each set {x:|f_n(x)-f_m(x)|<1/k} is in Σ."}
         {:name "countable unions/intersections"
          :meaning "σ-algebras are closed under countable unions/intersections."
          :needed-because "The definition of E will involve ⋂_k ⋃_N ⋂_{n,m≥N}."}]
 :strategy [{:id :s1
             :formal-dependency "Cauchy criterion for convergence in ℝ"
             :informal-dependency "Stage 1 rewrite using ε=1/k"
             :why-this-now "Express E as ⋂_k ⋃_N ⋂_{n,m≥N} {x: |f_n-f_m|<1/k}."
             :lean-target "setOf_pointwise_converges"
             :mathlib-status "Relies on existing completeness of ℝ (Cauchy ⇔ convergent)."}
            {:id :s2
             :formal-dependency "measurability of algebraic combinations"
             :informal-dependency "Stage 1 measurability argument"
             :why-this-now "Show each {x:|f_n-f_m|<1/k} is measurable, hence the whole countable expression is measurable."
             :lean-target "setOf_limit_is_measurable"
             :mathlib-status "Sublevel sets of measurable functions are measurable."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a97A04'
  :frame-id 'apm-v2-a97A04-1775003958890'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full informal solution (difficulty analysis, key insight, proof, connections) in execute.md Stage 1."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Documented the Cauchy-measurability plan in Stage 2 and synced proof-plan/formal-alignment artifacts."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-completed
  :summary "Implemented the Lean proof (`measurableSet_convergenceSet`) via the Cauchy expansion and ran lake build."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.*  The set \(E=\{x : (f_n(x))\text{ converges}\}\) is defined by a limit that depends on \(x\); novices try to reason with “\(\lim\)” directly, but the limit operation is neither algebraic nor visibly measurable.  The trick is to replace the convergence condition by a countable collection of inequalities involving the *measurable* functions \(f_n\).  Missing this translation is the main stumbling block.

*Key insight.*  A real sequence is convergent iff it is Cauchy.  For our pointwise sequence, that translates to: \(x\in E\) iff for every \(k\in\mathbb N\) there exists an \(N\) such that for all \(n,m\ge N\) we have \(|f_n(x)-f_m(x)|<1/k\).  Each inequality describes a measurable set because sublevel sets of measurable functions are measurable, and σ-algebras are closed under countable unions and intersections.  So write \(E\) as \(\bigcap_k\bigcup_N\bigcap_{n,m\ge N}\{\dots\}\) and measurability follows.

*Proof.*  For \(k\in\mathbb N\) and \(N\in\mathbb N\) set
  \[
  A_{k,N} = \bigcap_{n=N}^\infty \ \bigcap_{m=N}^\infty \Bigl\{x\in X : |f_n(x)-f_m(x)| < 1/k\Bigr\}.
  \]
  Because each \(f_n\) is measurable, the map \(x\mapsto |f_n(x)-f_m(x)|\) is measurable, hence each set in braces is in \(\Sigma\); closure under countable intersections shows \(A_{k,N}\in\Sigma\).  Define
  \[
  E = \bigcap_{k=1}^\infty \ \bigcup_{N=1}^\infty A_{k,N}.
  \]
  Again, σ-algebras are closed under countable unions and intersections, so \(E\in\Sigma\).

  It remains to check that this \(E\) equals the desired convergence set.  Fix \(x\in X\).  If \(x\in E\), then for each \(k\) there exists \(N\) such that for all \(n,m\ge N\), \(|f_n(x)-f_m(x)|<1/k\); that is exactly the Cauchy criterion for \((f_n(x))\).  Since bounded sequences in \(\mathbb R\) are complete (indeed, completeness of \(\mathbb R\) suffices), the sequence converges.

  Conversely, if \((f_n(x))\) converges, it is Cauchy, so for every \(k\) we can find \(N\) such that the inequalities above hold; hence \(x\in E\).  Therefore \(E\) is the set of convergence points and is measurable.

*What connects.*  Writing “limit sets’’ as countable unions/intersections of measurable events (`∀/∃` turning into `⋂/⋃`) is a standard trick everywhere in measure theory and probability: e.g. the limsup of events, the set where a martingale converges, or the event \(\{\liminf X_n < \infty\}\).  Anytime you see a quantifier over \(\epsilon>0\), think of restricting to rationals so you only deal with countably many measurable sets.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Cauchy encoding* (`setOf_pointwise_converges`): relies on completeness of \(\mathbb R\) and expresses \(E\) as \(\bigcap_k\bigcup_N\bigcap_{n,m\ge N}\{\dots\}\).
- *Measurability of inequality sets* (`measurable_set_lt_abs`): uses the fact that measurable functions are closed under subtraction and absolute value, so \(\{x:|f_n-f_m|<1/k\}\in\Sigma\).

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/a97A04/apm-v2-a97A04-1775003958890/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/a97A04/apm-v2-a97A04-1775003958890/formal-alignment.edn

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/a97A04/apm-v2-a97A04-1775003958890/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/a97A04/apm-v2-a97A04-1775003958890/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

*Status.*  Done.  The statement appears as `measurable_set_pointwiseConverges` in `Main.lean`.  Implementation steps:
1. Define the countable approximants `cauchySet k N` using intersections over pairs `(n,m)`.
2. Prove `MeasurableSet (cauchySet k N)` via `MeasurableSet.iInter` and the measurability of `fun x => |f n x - f m x|`.
3. Show the convergence set equals `⋂ k, ⋃ N, cauchySet k N` using the Cauchy criterion.
4. Conclude measurability via closure properties of σ-algebras.

Lean successfully compiles (`lake build`).

Frame-local Lean files:
- /home/joe/code/apm-lean/ApmCanaries/Frames/A97A04/Apm_v2_a97A04_1775003958890/Main.lean
- /home/joe/code/apm-lean/ApmCanaries/Frames/A97A04/Apm_v2_a97A04_1775003958890/Scratch.lean

Shared extension root for promoted lemmas:
- /home/joe/code/apm-lean/ApmCanaries/Local

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

No back-porting needed: the informal presentation already mirrors the Lean argument (Cauchy encoding + measurability of sublevel sets).
