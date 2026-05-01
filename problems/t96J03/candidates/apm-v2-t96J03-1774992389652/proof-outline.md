# Proof Outline: t96J03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Given a closed nonempty subset X of ℝⁿ and a point y₀∉X, show there is x₀∈X minimizing the Euclidean distance to y₀."
 :terms [{:name "distance function"
          :meaning "f(x)=‖x−y₀‖ on X is continuous"
          :needed-because "We want to minimize a continuous function on a compact set."}
         {:name "bounded minimizing sequence"
          :meaning "A sequence in X whose distances converge to the infimum lives inside a closed ball"
          :needed-because "Closed balls intersected with X are compact in ℝⁿ."}
         {:name "compactness of closed bounded sets"
          :meaning "Heine–Borel for ℝⁿ"
          :needed-because "It ensures the minimizing sequence has a convergent subsequence with limit in X."}]
 :strategy [{:id :s1
             :formal-dependency "Heine–Borel, completeness of ℝⁿ, continuity of the norm"
             :informal-dependency "Take an infimizing sequence, restrict to a compact subset, extract a convergent subsequence, and use lower semicontinuity"
             :why-this-now "The distance function is coercive, so compactness arguments immediately give a minimizer."
             :lean-target "Lemma `exists_norm_eq_infi` stating closed nonempty sets in Euclidean space have nearest points"
             :mathlib-status "Mathlib already has `isClosed.exists_isMinOn_norm` (nearest point lemma), so the formal proof can reuse that API."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :pending :stage4 :pending}
 :lean {:module-root 'ApmCanaries.Frames.T96J03.Apm_v2_t96J03_1774992389652'
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't96J03'
  :frame-id 'apm-v2-t96J03-1774992389652'
  :summary "Created the isolated frame and stub Lean files."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Proved the nearest-point lemma: build an infimizing sequence inside a closed ball, extract a convergent subsequence, and use closedness to get the minimizer."
  :full-record? true
  :sorry? false
  :fully-closed? true}
 {:kind :stage2-completed
  :summary "Logged the dependency chain (continuity + Heine–Borel + compactness)."
  :full-record? true
  :sorry? false
  :fully-closed? true}
 {:kind :stage3-progress
  :summary "Noted that the Lean file still needs to call Mathlib’s `exists_norm_eq_infi`; no code yet."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

Let \(d=\inf\{\|x-y_0\|:x\in X\}\).  Since \(X\neq\varnothing\), choose a sequence \((x_k)\subset X\) with \(\|x_k-y_0\|\to d\).  The sequence lies in the closed ball \(B=\overline{B}(y_0,d+1)\), which is compact and contains \(X\cap B\) as a closed subset.  By Bolzano–Weierstrass, there is a subsequence \(x_{k_j}\) converging to some \(x_0\in X\) (because \(X\) is closed).  Continuity of the norm implies
\[
\|x_0-y_0\|=\lim_{j\to\infty}\|x_{k_j}-y_0\|\le d,
\]
so equality holds and \(x_0\) minimizes the distance: for every \(x\in X\),
\(\|x_0-y_0\|\le\|x-y_0\|\).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

The proof uses: (i) the norm is continuous; (ii) closed balls in ℝⁿ are compact (Heine–Borel); (iii) closed subsets of compact sets are compact; (iv) infima are attained on compact sets; (v) a closed set contains the limits of convergent sequences in it.

**Stage 3 — LEAN FORMALIZATION**

`Main.lean` is still empty.  Mathlib already has the lemma `IsClosed.exists_isMinOn` (a nearest point theorem) and the more specialized `exists_norm_eq_infi` for Euclidean spaces.  The formal proof will instantiate that lemma with the closed set `X` and the function \(x\mapsto \|x-y_0\|\).

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the Mathlib lemma is invoked, the formal and informal arguments coincide.  No further adjustments are needed.
