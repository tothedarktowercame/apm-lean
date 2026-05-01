# Proof Outline: a96J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Construct a sequence of nonnegative continuous bumps on [0,1] whose sup-norm series diverges but whose partial sums converge uniformly."
 :terms [{:name "disjoint supports"
          :meaning "each fₙ is supported on an interval disjoint from all previous ones"
          :needed-because "Uniform convergence becomes trivial: at each point only finitely many terms contribute."}
         {:name "height control"
          :meaning "choose max fₙ = 1/n"
          :needed-because "The sup-series becomes the harmonic series, ensuring divergence."}
         {:name "tent functions"
          :meaning "piecewise-linear bumps with compact support"
          :needed-because "They give continuous nonnegative examples whose sums are easy to analyze."}]
 :strategy [{:id :s1
             :formal-dependency "Definition of uniform convergence; facts about piecewise-linear functions"
             :informal-dependency "Place smaller and smaller tents near 1, so the limit function equals each tent on its interval and 0 elsewhere"
             :why-this-now "Disjoint supports guarantee the uniform limit while keeping the sup-series large."
             :lean-target "Explicit function sequence in Lean built from simple affine pieces"
             :mathlib-status "Mathlib has continuous functions built from affine pieces; no fundamental gap, just routine encoding."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :pending :stage4 :pending}
 :lean {:module-root 'ApmCanaries.Frames.A96J01.Apm_v2_a96J01_1774992421755'
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a96J01'
  :frame-id 'apm-v2-a96J01-1774992421755'
  :summary "Created the isolated frame and Lean stubs."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Constructed the disjoint tent functions with heights 1/n, proved uniform convergence, and checked the harmonic sup-series diverges."
  :full-record? true
  :sorry? false
  :fully-closed? true}
 {:kind :stage2-completed
  :summary "Captured the dependency chain (disjoint supports + continuity + harmonic heights)."
  :full-record? true
  :sorry? false
  :fully-closed? true}
 {:kind :stage3-progress
  :summary "Noted that Lean still needs the explicit piecewise definition of the bumps; no code yet."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

Let \(I_n = [1-2^{-n},\,1-2^{-(n+1)}]\); these intervals are pairwise disjoint and shrink to the point \(1\).  Define a “tent” function \(f_n\) supported on \(I_n\): linear on each half of \(I_n\), vanishing at the endpoints, and attaining height \(1/n\) at the midpoint.  Then \(f_n\) is continuous, nonnegative, and \(\sup_{[0,1]} f_n = 1/n\), so \(\sum \sup f_n = \sum 1/n = \infty\).  Because the supports are disjoint, at every fixed \(x\in[0,1]\) at most one \(f_n(x)\) is nonzero.  Let \(f\) be the pointwise limit defined by \(f(x)=f_n(x)\) if \(x\in I_n\) and \(0\) otherwise; by construction \(f\) is continuous.  For any \(\varepsilon>0\) choose \(N>1/\varepsilon\).  If \(x\notin \bigcup_{n\ge N} I_n\), then \(f_n(x)=0\) for all \(n\ge N\) and \(\sum_{k=1}^\infty f_k(x)=\sum_{k=1}^{N-1} f_k(x)\).  If \(x\in I_m\) with \(m\ge N\), then only \(f_m\) contributes and
\(|\sum_{k=1}^\infty f_k(x) - \sum_{k=1}^{N-1} f_k(x)| = f_m(x) \le 1/m < 1/N < \varepsilon\).  Hence the partial sums converge uniformly to \(f\).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Support disjointness* ⇒ uniform convergence reduces to tail control on heights.
- *Continuity of tents* ⇒ each \(f_n\) is continuous and nonnegative.
- *Harmonic heights* ⇒ the series of suprema diverges.

**Stage 3 — LEAN FORMALIZATION**

`Main.lean` is still empty.  To formalize the construction we would define each \(f_n\) as a piecewise-linear function (`continuousOn_Icc.mpr`) supported on the interval \(I_n\), then show the sum stabilizes pointwise and is uniformly Cauchy.  Mathlib already has the basic lemmas on uniform convergence and disjoint supports.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the explicit Lean definition of \(f_n\) is provided, the formal proof will mirror the argument above step-for-step.  No further reconciliation is needed.
