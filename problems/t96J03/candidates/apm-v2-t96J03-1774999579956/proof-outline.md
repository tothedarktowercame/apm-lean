# Proof Outline: t96J03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Given a nonempty closed subset of ℝⁿ and an exterior point y₀, find a point in the set realizing the minimal distance to y₀."
 :terms [{:name "properness of ℝⁿ"
          :meaning "closed and bounded subsets of ℝⁿ are compact"
          :needed-because "We intersect X with a large closed ball about y₀ to get a compact minimization domain."}
         {:name "continuous distance function"
          :meaning "x ↦ ‖x - y₀‖ is continuous on ℝⁿ"
          :needed-because "A continuous function attains its extrema on a compact set."}
         {:name "metric projection"
          :meaning "A point where the distance function attains its minimum"
          :needed-because "Any minimizer on the compact subset works for all of X."}]
 :strategy [{:id :s1
             :formal-dependency "Heine–Borel for ℝⁿ"
             :informal-dependency "Stage 1 step: restrict to X ∩ closed ball of radius R"
             :why-this-now "Show X ∩ closedBall y₀ R is compact because it is closed and bounded."
             :lean-target "subset_closedBall_isCompact"
             :mathlib-status "Available (Euclidean space is proper)."}
            {:id :s2
             :formal-dependency "Extreme value theorem on compact sets"
             :informal-dependency "Stage 1 minimization step"
             :why-this-now "A continuous map on a compact set achieves its infimum."
             :lean-target "Continuous.compact_min''"
             :mathlib-status "Available for continuous functions on compact sets."}
            {:id :s3
             :formal-dependency "Order properties of ℝ"
             :informal-dependency "Final comparison showing minimizer works for every x ∈ X"
             :why-this-now "If the minimizer beats everyone inside X ∩ B̄(y₀,R) and every other x lies outside, then its distance is still minimum."
             :lean-target "exists_dist_le_dist"
             :mathlib-status "Target theorem to prove."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't96J03'
  :frame-id 'apm-v2-t96J03-1774999579956'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Authored the full reader-facing solution (why hard, key insight, detailed proof, connections) in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Recorded the lemma dependency graph and Lean target (`exists_closest_point_closed_subset`) in the plan/alignment artifacts."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-completed
  :summary "Implemented `closest_point_exists` in Lean using `exists_infDist_eq_dist`, ran `lake build`, and noted the result in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage4-completed
  :summary "Back-propagated the formal argument to the prose write-up, noting how the Mathlib lemma subsumes the textbook proof."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

# Stage 1 — reader-facing solution
## Why it’s hard
Students often try to minimize the distance on all of \(X\) at once and forget that the extreme-value theorem only works on compact sets. Others reach for calculus (Lagrange multipliers) even though \(X\) need not be smooth. The main trap is failing to restrict the search to a bounded subset of \(X\), so the “minimum distance” might escape to infinity.

## Key insight
Pick any point \(x_1\in X\) and draw a large closed ball \(\overline{B}(y_0,R)\) around \(y_0\) with \(R>\|x_1-y_0\|\). The intersection \(K=X\cap \overline{B}(y_0,R)\) is nonempty, closed, and bounded, hence compact. The distance function \(x\mapsto \|x-y_0\|\) is continuous, so it achieves its minimum on the compact set \(K\). That minimizer automatically beats every point of \(X\), because any point outside the ball is even farther away than \(x_1\), while the minimizer is no worse than \(x_1\).

## Complete proof
Let \(x_1\in X\) and set \(R=\|x_1-y_0\|+1\). Define the closed ball \(B=\overline{B}(y_0,R)=\{x:\|x-y_0\|\le R\}\) and the compact set \(K=X\cap B\). The set \(K\) is nonempty (it contains \(x_1\)), closed, and bounded, so it is compact by Heine–Borel. The distance function \(f(x)=\|x-y_0\|\) is continuous, hence attains its minimum on \(K\): there exists \(x_0\in K\) with
\[
  f(x_0)=\min_{x\in K} f(x).
\]
In particular, \(\|x_0-y_0\|\le \|x_1-y_0\|\).

Take any \(x\in X\). If \(x\in K\), then \(\|x_0-y_0\|\le \|x-y_0\|\) by minimality. If \(x\notin K\), then \(x\notin B\), so \(\|x-y_0\|>R=\|x_1-y_0\|+1\), which implies
\[
  \|x-y_0\|> \|x_1-y_0\| \ge \|x_0-y_0\|.
\]
Combining the two cases shows \(\|x_0-y_0\|\le \|x-y_0\|\) for all \(x\in X\), as desired.

## What connects / exam kit
This argument is the prototype of “metric projection” onto a closed convex set in a Hilbert space. The same compactness-plus-continuity trick proves the existence of nearest points in many settings (e.g., Chebyshev sets, resolvents of convex functions). Always remember: restrict to a compact set before invoking the extreme-value theorem, and use an obvious base point to bound the minimizing region.

# Stage 2 — lemma dependency graph
The machine-readable plan (proof-plan.edn) highlights three ingredients: (1) ℝⁿ is proper (closed ∩ bounded ⇒ compact); (2) the distance map is continuous and achieves its minimum on a compact set; (3) the minimizer on \(X\cap\overline{B}(y_0,R)\) is the global minimizer on \(X\). The formal target recorded in formal-alignment.edn is the theorem `exists_closest_point_closed_subset`, matching the problem statement in Euclidean space. Helper alignment `distance_attains_inf_on_compact` captures the extreme-value step.

# Stage 3 — Lean formalization
The Lean proof lives in `ApmCanaries/Frames/T96J03/Apm_v2_t96J03_1774999579956/Main.lean` as `closest_point_exists`. Mathlib already supplies the heavy machinery via `IsClosed.exists_infDist_eq_dist` and `le_infDist`. After writing the short wrapper proof, I ran `lake build` (see output above) to ensure the project compiles; no new warnings were introduced beyond pre-existing lint notes in unrelated files.

# Stage 4 — back-propagation
The Lean certificate justifies the compactness/continuity argument exactly as in the handwritten proof. If one wanted a more general statement (e.g., in any proper metric space), Mathlib’s `exists_infDist_eq_dist` already works—the Euclidean version used here is a special case—so the informal proof could be advertised as an instance of the general “metric projection in proper spaces.”
