# Proof Outline: a97A03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that an absolutely continuous f : [a,b] → ℝ is Lipschitz iff its a.e. derivative is essentially bounded."
 :terms [{:name "absolute continuity"
          :meaning "f(x)-f(y) = ∫_y^x f'(t) dt for every x,y in [a,b]."
          :needed-because "This lets us convert bounds on f' into bounds on f(x)-f(y)."}
         {:name "difference quotient a.e. derivative control"
          :meaning "For Lipschitz f the limit of difference quotients exists a.e. and stays within the Lipschitz constant."
          :needed-because "Lipschitz ⇒ bounded derivative requires bounding |(f(x+h)-f(x))/h| by B."}
         {:name "essential supremum"
          :meaning "|f'| ≤ C almost everywhere gives a uniform bound outside a null set."
          :needed-because "We need the L^∞-style control to integrate as |f(x)-f(y)| ≤ ∫ C = C|x-y|."}]
 :strategy [{:id :s1
             :formal-dependency "measure-theoretic differentiability of Lipschitz maps"
             :informal-dependency "Stage 1 proof of Lipschitz ⇒ bounded derivative"
             :why-this-now "Show B-Lipschitz implies |f'| ≤ B a.e. by looking at difference quotients as h→0."
             :lean-target "lipschitz_has_deriv_bound"
             :mathlib-status "Mathlib has Rademacher’s theorem in this simple 1D setting via a.e. differentiability of AC functions."}
            {:id :s2
             :formal-dependency "fundamental theorem of calculus for absolutely continuous functions"
             :informal-dependency "Stage 1 proof of bounded derivative ⇒ Lipschitz"
             :why-this-now "Use f(x)-f(y)=∫ f' to bound by C|x-y| once |f'| ≤ C a.e."
             :lean-target "ac_of_ae_deriv_bound_is_lipschitz"
             :mathlib-status "Needs existing FTC statement for AC functions."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a97A03'
  :frame-id 'apm-v2-a97A03-1775003886693'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the informal solution (difficulties, key insight, complete proof, field kit) in Stage 1 of execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Populated the lemma dependency discussion (Stage 2) and synchronized proof-plan/formal-alignment artifacts."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-blocked
  :summary "Lean proof blocked: Mathlib lacks a bridge from Lipschitz constants to essentially bounded one-sided derivatives on intervals; documented the gap in Stage 3."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.*  Students often forget that absolute continuity is the exact regularity hypothesis needed for the Fundamental Theorem of Calculus (FTC).  Without FTC you can’t connect bounds on \(f'\) to bounds on \(f(x)-f(y)\).  The other trap is thinking that the derivative of *any* Lipschitz function exists everywhere, so they argue pointwise; in reality it exists only almost everywhere, so you must work on the full-measure set of differentiability points.

*Key insight.*  Absolute continuity provides both directions: (1) Lipschitz ⇒ \(|f'|\le B\) almost everywhere because the derivative exists a.e. and is the limit of difference quotients, each bounded by the Lipschitz constant; (2) \(|f'|\le C\) a.e. ⇒ Lipschitz because for every \(x<y\) we can write \(f(y)-f(x)=\int_x^y f'(t)\,dt\) and bound that integral by \(C|y-x|\).  So the whole equivalence is FTC plus elementary estimates.

*Proof.*  Assume \(f\) is absolutely continuous on \([a,b]\).

1.  Suppose \(|f(x)-f(y)|\le B|x-y|\) for all \(x,y\).  By absolute continuity, \(f\) is differentiable almost everywhere (this is standard: absolute continuity implies differentiability a.e. with \(f'=g\) where \(f(x)=f(a)+\int_a^x g\)).  If \(x\) is such a differentiability point, then
   \[
   |f'(x)| = \lim_{h\to 0} \left|\frac{f(x+h)-f(x)}{h}\right| \le \limsup_{h\to 0} \frac{B|h|}{|h|} = B,
   \]
   because each difference quotient is bounded by the Lipschitz constant.  Thus \(|f'|\le B\) almost everywhere.

2.  Conversely suppose \(|f'(x)|\le C\) for almost every \(x\in[a,b]\).  Fix \(x<y\).  Since \(f\) is absolutely continuous, the FTC gives
   \[
   f(y)-f(x) = \int_x^y f'(t)\,dt.
   \]
   Split the integral into the part where \(|f'|\le C\) (which is all but a null set) and the negligible remainder to conclude \(|f(y)-f(x)| \le \int_x^y |f'(t)|\,dt \le C\int_x^y 1\,dt = C(y-x)\).  The same estimate with \(x>y\) gives \(|f(x)-f(y)|\le C|x-y|\), so \(f\) is \(C\)-Lipschitz on \([a,b]\).

Combining the two directions we obtain the equivalence.

*What connects.*  The equivalence “absolutely continuous + Lipschitz ⇔ derivative bounded a.e.” is the one-dimensional version of the general principle that Lipschitz maps live in \(W^{1,\infty}\), and that absolute continuity is the Sobolev regularity needed to integrate derivatives back to the function.  On prelims it pays dividends whenever you need uniform continuity or variation estimates from derivative information, e.g. in solving ODEs (Picard–Lindelöf) or bounding Fourier coefficients of AC functions.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Derivative of a Lipschitz function* (Lean target `lipschitz_has_deriv_bound`): Formally depends on the fact that AC functions are differentiable almost everywhere and the derivative equals the limit of difference quotients.  Informally this is Step 1 above.
- *Fundamental theorem on intervals* (Lean target `absCont_integral_repr`): Formally uses the FTC for absolutely continuous functions.  Informally it powers Step 2, writing \(f(y)-f(x)\) as an integral of \(f'\).

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/a97A03/apm-v2-a97A03-1775003886693/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/a97A03/apm-v2-a97A03-1775003886693/formal-alignment.edn

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/a97A03/apm-v2-a97A03-1775003886693/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/a97A03/apm-v2-a97A03-1775003886693/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

*Status.*  Not completed.  The natural Lean statement (`ac_lipschitz_iff_ae_deriv_bound`) is recorded in `formal-alignment.edn`.  The plan was to:
1. reuse the existing Mathlib theorem `absContinuousOn_iff_intervalIntegrable_deriv` to access the a.e. derivative,
2. invoke the one-dimensional instance of Rademacher’s theorem (`LipschitzWith.hasFDerivWithinAt`) to show the derivative is bounded by the Lipschitz constant, and
3. apply the interval version of the FTC to deduce Lipschitz from an \(L^\infty\) bound on \(f'\).

However, Mathlib currently lacks the specific lemma turning a global Lipschitz constant into an essential-supremum bound on `derivWithin` along an interval—what is available is phrased in terms of Frechet derivatives of maps between normed vector spaces.  Adapting that to the one-dimensional `derivWithin` required building a bridge lemma, and I ran out of time.  Once that lemma is added, wiring the equivalence will amount to combining it with `integral_deriv_eq_sub`.  No Lean code was added, so I did not run `lake build`.

Frame-local Lean files:
- /home/joe/code/apm-lean/ApmCanaries/Frames/A97A03/Apm_v2_a97A03_1775003886693/Main.lean
- /home/joe/code/apm-lean/ApmCanaries/Frames/A97A03/Apm_v2_a97A03_1775003886693/Scratch.lean

Shared extension root for promoted lemmas:
- /home/joe/code/apm-lean/ApmCanaries/Local

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The informal argument already mirrors what the Lean proof would do (a.e. differentiability + FTC).  The only missing formal piece is the lemma turning a Lipschitz constant into an a.e. derivative bound inside `derivWithin`.  Once that exists, the informal write-up needs no changes.
