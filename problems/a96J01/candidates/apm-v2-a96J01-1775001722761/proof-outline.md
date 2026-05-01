# Proof Outline: a96J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Construct nonnegative continuous functions fₙ on [0,1] whose partial sums converge uniformly while ∑ ‖fₙ‖∞ diverges."
 :terms [{:name "dyadic partition"
          :meaning "Break [0,1] into shrinking disjoint intervals (e.g., [1-2^{-n}, 1-2^{-(n+1)}])"
          :needed-because "Gives disjoint supports so tails affect at most one point, enabling uniform control."}
         {:name "tent functions"
          :meaning "Continuous bumps supported on each interval, peaking at height 1/(n+1)"
          :needed-because "Ensures each fₙ ≥ 0, continuous, with prescribed sup norm."}
         {:name "harmonic divergence vs uniform convergence"
          :meaning "Sup norms add like ∑ 1/(n+1) (divergent) while tails are bounded by the largest remaining peak"
          :needed-because "Shows the required contrast between divergent sup norms and uniform convergence."}]
 :strategy [{:id :s1
             :formal-dependency "Definition of a continuous tent on an interval; continuity lemmas for piecewise linear maps"
             :informal-dependency "Stage 1 construction of fₙ supported on nested dyadic subintervals"
             :why-this-now "Forms the explicit sequence meeting the pointwise nonnegativity/continuity hypotheses."
             :lean-target "define_tent_function"
             :mathlib-status "Requires custom code; Mathlib does not yet ship a ready-made tent constructor."}
            {:id :s2
             :formal-dependency "Sup norm estimates on functions with small support"
             :informal-dependency "Stage 1 argument that tails are uniformly ≤ 1/(N+1)"
             :why-this-now "Turns the disjoint-support property into uniform convergence."
             :lean-target "uniform_tail_bound"
             :mathlib-status "Provable from basic inequalities; no external gap expected."}
            {:id :s3
             :formal-dependency "Comparison with the harmonic series"
             :informal-dependency "Stage 1 statement that ∑ sup fₙ diverges"
             :why-this-now "Certifies the divergent sup-norm sum."
             :lean-target "sup_norm_series_diverges"
             :mathlib-status "Follows from existing results on the harmonic series."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a96J01'
  :frame-id 'apm-v2-a96J01-1775001722761'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the tent-function construction, highlighted the uniform tail bound, and explained the harmonic divergence."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Recorded the dyadic-interval, tent-continuity, and uniform-tail dependencies in proof-plan.edn."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Formal target `tent_sequence_exists` stated; coding blocked by the lack of ready-made tent constructors in Mathlib."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

***Why it’s hard.***  Uniform convergence usually suggests applying the Weierstrass $M$-test, so your instinct is that $\sum \|f_n\|_\infty$ must converge. The trap is that the hypothesis only says “partial sums converge uniformly,” not “$\sum \|f_n\|_\infty$ converges.” If you concentrate each $f_n$ on a different subinterval of $[0,1]$, no two bumps are ever active at the same point. The tails are uniformly small even though the sup norms add up like the harmonic series.

***Key insight.***  Use disjoint supports: let $I_n=[1-2^{-n}, 1-2^{-(n+1)}]$ and let $f_n$ be the continuous “tent” over $I_n$ with height $1/n$ at its midpoint and value $0$ at the endpoints. Because the $I_n$ only meet at endpoints (where the tents vanish), at any $x$ at most one $f_n(x)$ is nonzero.

***Complete proof.***  (1) Define $f_n$ as above. Each $f_n$ is nonnegative and continuous on $[0,1]$, satisfies $\|f_n\|_\infty=1/n$, and has support contained in $I_n$. (2) For every $x$ there is at most one index $n$ with $f_n(x)>0$. Hence for every $N$ and every $x$, $\sum_{n\ge N} f_n(x) \le \sup_{n\ge N} \|f_n\|_\infty = 1/N$. This uniform tail bound implies the partial sums converge uniformly to the pointwise sum $f(x)=\sum_n f_n(x)$. (3) Because $\|f_n\|_\infty=1/n$, the series $\sum \|f_n\|_\infty$ diverges. Therefore the desired example exists.

***What connects.***  This is the classical way to show that uniform convergence does not imply absolute convergence of sup norms. The same trick—spreading the mass over disjoint intervals—appears in counterexamples to the Weierstrass $M$-test and in constructive proofs of approximation theorems.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Dyadic geometry.*  The endpoints $1-2^{-n}$ guarantee the supports are pairwise disjoint (except for endpoints where the tents vanish).
- *Tent continuity.*  Writing $f_n(x)=\max(0,1-|x-c_n|/r_n)$ shows each $f_n$ is continuous and nonnegative.
- *Uniform tail bound.*  At any $x$ the tail consists of at most one positive term, so $\sup_x \sum_{n\ge N} f_n(x) \le 1/N$, which yields uniform convergence.

**Stage 3 — LEAN FORMALIZATION**

- *Type signature.*  The target statement `tent_sequence_exists` (see `formal-alignment.edn`) asserts the existence of $f : \mathbb N \to C([0,1],\mathbb R)$ with the three properties above.
- *Status — blocked.*  Mathlib provides the Banach-space structure on `C([0,1], ℝ)` and the divergence of the harmonic series, but it lacks convenient constructors for these piecewise linear tent functions together with the lemmas about their disjoint supports. Implementing them would require a substantial amount of bespoke real-analysis code (continuity proofs for `max`/`abs` combinations on subtypes, dyadic-interval arithmetic, “at most one active index” lemmas). With the current time budget that work is not yet written, so `Main.lean` remains a stub. To finish, one would need to define the tents, prove they form a nonnegative sequence with the harmonic sup norms, and then encode the tail bound in the sup norm.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the tent constructors are available, the Lean proof will follow Stage 1 verbatim: disjoint supports give the uniform tail estimate, and evaluating at the midpoint shows each sup norm equals its prescribed height. Until then, the informal proof above serves as the authoritative argument and `formal-alignment.edn` documents the intended Lean target.
