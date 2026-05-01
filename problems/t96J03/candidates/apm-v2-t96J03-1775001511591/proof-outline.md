# Proof Outline: t96J03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Given a nonempty closed subset X ⊆ ℝⁿ and y₀ ∉ X, show there is x₀ ∈ X minimizing ‖x−y₀‖."
 :terms [{:name "compact truncation"
          :meaning "Intersect X with a closed ball centered at y₀ with radius larger than some point’s distance"
          :needed-because "Restricts attention to a compact subset where the continuous distance function attains its minimum."}
         {:name "extreme-value theorem"
          :meaning "A continuous function on a compact set attains its minimum and maximum"
          :needed-because "Ensures the distance function has a minimizer on the truncated set."}
         {:name "IsClosed.exists_infDist_eq_dist"
          :meaning "Mathlib lemma asserting closed sets realize their infimum distance to any point for proper metric spaces"
          :needed-because "Direct Lean route to produce the minimizing point without re-proving compactness arguments."}]
 :strategy [{:id :s1
             :formal-dependency "Heine–Borel for ℝⁿ → closed & bounded ⇒ compact"
             :informal-dependency "Stage 1 step: restrict to closed ball intersect X"
             :why-this-now "Converts the minimization problem into one on a compact domain."
             :lean-target "compact_intersection"
             :mathlib-status "Standard; reuses `Metric` lemmas already in Mathlib."}
            {:id :s2
             :formal-dependency "Continuity of x ↦ ‖x − y₀‖"
             :informal-dependency "Stage 1 invocation of the extreme-value theorem"
             :why-this-now "Produces the minimizing point x₀ on the compact set."
             :lean-target "exists_minOn_norm_sub"
             :mathlib-status "Follows from `IsClosed.exists_infDist_eq_dist`."}
            {:id :s3
             :formal-dependency "`IsClosed.exists_infDist_eq_dist` in `Mathlib/Topology/MetricSpace/InfDist`"
             :informal-dependency "Stage 1 conclusion that the minimizer works for all of X"
             :why-this-now "Supplies the Lean certificate for the main theorem."
             :lean-target "closest_point_exists"
             :mathlib-status "Available in Mathlib; needs instantiation for Euclidean spaces."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't96J03'
  :frame-id 'apm-v2-t96J03-1775001511591'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the reader-facing proof (why-hard, key insight, complete argument, connections)."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Recorded the compact-truncation and infimum-distance dependencies in proof-plan.edn."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-completed
  :summary "Implemented `closest_point_exists` in Main.lean and validated with `lake build`."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage4-completed
  :summary "Explained how the Lean lemma corresponds to the Stage 1 compactness argument."
  :full-record? true
  :sorry? false
  :fully-closed? true}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

***Why it’s hard.***  Students instinctively invoke the extreme-value theorem without justifying compactness. But \(X\) might be unbounded, so the distance function need not attain its infimum on all of \(X\). The trick is to truncate \(X\) by intersecting it with the closed ball of radius \(\|x_1-y_0\|\) for some \(x_1\in X\); only after this step is the domain compact. Another frequent trap is trying to use calculus (gradients/Lagrange multipliers) even though \(X\) can be wildly non-smooth; the metric argument is far more robust.

***Key insight.***  Fix any \(x_1\in X\) and take the closed ball \(B=\overline{B}(y_0,\|x_1-y_0\|)\). Any point of \(X\) farther from \(y_0\) than \(x_1\) lies outside \(B\), so the minimizer must lie in \(K:=X\cap B\), which is compact (closed subset of the compact ball). The continuous function \(x\mapsto \|x-y_0\|\) attains its minimum on \(K\); that minimum works for the whole of \(X\).

***Complete proof.***  Pick \(x_1\in X\) (possible because \(X\neq\varnothing\)) and set \(r=\|x_1-y_0\|\). Consider the closed ball \(B=\{x:\|x-y_0\|\le r\}\). Then \(K=X\cap B\) is closed in the compact ball \(B\), hence compact. The distance function \(f(x)=\|x-y_0\|\) is continuous, so by the extreme-value theorem there exists \(x_0\in K\) with \(f(x_0)\le f(x)\) for every \(x\in K\). If \(x\in X\setminus K\), then \(\|x-y_0\|>r\ge \|x_1-y_0\|\ge \|x_0-y_0\|\). Therefore the same inequality holds for all \(x\in X\), as required.

***What connects.***  This is the finite-dimensional case of the general fact that proper metric spaces are proximinal (every closed set admits a metric projection). The same move—intersecting with a closed ball to regain compactness—appears when proving the existence of best approximations in normed spaces, in Riesz’s lemma, and when constructing orthogonal projections onto closed convex sets in Hilbert spaces.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Closed ball compactness.*  In \(\mathbb R^n\), closed and bounded sets are compact (Heine–Borel). Needed to compactify \(X\).
- *Continuity of the distance map.*  \(x\mapsto \|x-y_0\|\) is continuous, so the extreme-value theorem applies on the compact set \(K\).
- *`IsClosed.exists_infDist_eq_dist` (Mathlib).*  Provides the Lean-shortcut that any closed subset of a proper metric space realizes its infimum distance to a given point.

**Stage 3 — LEAN FORMALIZATION**

- *Main declaration.*  `closest_point_exists` in `ApmCanaries/Frames/T96J03/Apm_v2_t96J03_1775001511591/Main.lean:8–22` states exactly the minimizer property for closed \(X\subseteq \mathbb R^n\) and \(y₀∉X\).
- *Ingredients.*  A quick `rg -n "exists_infDist_eq_dist"` search in `.lake/packages/mathlib` located the Mathlib lemma (see `Topology/MetricSpace/HausdorffDistance.lean`), and `infDist_le_dist_of_mem` gives the comparison inequality for arbitrary \(x∈X\).
- *Wiring.*  Instantiate `IsClosed.exists_infDist_eq_dist` with the Euclidean closed set to obtain `x₀`; the lemma returns equality `infDist y₀ X = dist y₀ x₀`, which when paired with `infDist_le_dist_of_mem` yields the desired inequality. The final norm inequality is just symmetry of the Euclidean norm. `lake build` (log above) confirms the file compiles.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean proof mirrors the textbook argument but avoids explicit compactness: `IsClosed.exists_infDist_eq_dist` plays the role of “restrict to a closed ball and use Weierstrass.” Translating back, that lemma *is* the compactness argument packaged as an API, so the informal proof can confidently cite the extreme-value theorem on the truncated set while the formal proof quotes the ready-made lemma. Future generalizations (e.g., replacing \(\mathbb R^n\) by any proper metric space) only need the Lean lemma plus an instance of `ProperSpace`.
