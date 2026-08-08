# Proof Outline: a94J03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that a continuous open map f:R→R must be strictly monotone."
 :terms [{:name "local extremum"
          :meaning "If f is not monotone there exist x<y<z with f(y) ≥ max(f(x),f(z)) or ≤ min."
          :needed-because "Such a point witnesses failure of openness."}
         {:name "open map property"
          :meaning "Images of open intervals must be open intervals."
          :needed-because "If f has a local extremum, the image of a symmetric interval is not open."}
         {:name "connectedness of intervals"
          :meaning "Continuous images of intervals are intervals."
          :needed-because "Helps describe f((a,b)) as an interval with endpoints given by limits."}]
 :strategy [{:id :s1
             :formal-dependency "Non-monotone ⇒ existence of local extremum"
             :informal-dependency "Stage 1 local extremum description"
             :why-this-now "Produce a point y where f takes a local maximum or minimum."
             :lean-target "nonmonotone_has_local_extremum"
             :mathlib-status "Need lemma for continuous real functions."}
            {:id :s2
             :formal-dependency "Open image of intervals"
             :informal-dependency "Stage 1 open map property"
             :why-this-now "Show that a local extremum contradicts openness."
             :lean-target "continuous_open_imp_monotone"
             :mathlib-status "Lean already knows continuous images of intervals are intervals; need to prove boundary point contradiction."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a94J03'
  :frame-id 'apm-v2-a94J03-1775003038480'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Explained why open maps on R must be strictly monotone; provided the local-maximum contradiction proof."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Logged lemma dependencies (local extremum lemma plus open-image argument)."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Outlined Lean plan (extremum lemma + open-set contradiction); implementation pending."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.* “Open map” feels weak at first glance: plenty of continuous maps send some open sets to open sets without being injective (e.g., \\(x↦x^2\\)). The trap is realizing that on the real line every open set is a union of intervals, so the hypothesis actually says *every interval* is mapped onto an open interval. Students often forget that any violation of monotonicity creates a local extremum, and local extrema force the image of a small interval to have a boundary point—contradicting openness.

*Key insight.* If \(f\) is not strictly monotone, there exist \(a<b<c\) with \(f(b)\) at least as large as both \(f(a)\) and \(f(c)\) (or at most as small). That makes \(b\) a local maximum or minimum. The image of a tiny open interval around \(b\) is then an interval whose endpoint is \(f(b)\), so it cannot be open. Hence no such local extremum exists and \(f\) must be strictly monotone.

*Complete proof.* Suppose \(f\) is continuous and maps every open set onto an open set. First, \(f\) cannot be constant on any nontrivial interval: if \(f\equiv c\) on \((u,v)\), then \(f((u,v))=\{c\}\), not open—a contradiction. Next, assume \(f\) is not strictly monotone. Then there exist \(x_1<x_2<x_3\) such that \(f(x_2) ≥ f(x_1)\) and \(f(x_2) ≥ f(x_3)\) (or both inequalities ≤). Because \(f\) is continuous on the compact interval \([x_1,x_3]\), it attains its maximum at some point \(y\) in \([x_1,x_3]\). If \(y\) lies at an endpoint we would have monotonicity on \([x_1,x_3]\); thus \(y\) lies in the interior, so \(f(y)\) is a strict local maximum. Choose \(δ>0\) with \(y±δ∈(x_1,x_3)\); then
\[
I=(y-δ,y+δ) \quad \text{is open, but} \quad f(I)=[m,f(y)) \text{ or } (f(y),M]
\]
for suitable \(m<M<f(y)\), because \(f(y)\) is the largest value on \(I\). Therefore \(f(I)\) is not open—contradiction. The same argument rules out local minima. Consequently \(f\) is strictly monotone on the whole line; if \(f\) were increasing on one subinterval and decreasing on another, the intermediate point would be a local extremum, which we just ruled out. Finally, strict monotonicity (either strictly increasing or strictly decreasing) follows.

*What connects.* This is a one-dimensional version of the Open Mapping Theorem: on \(\mathbf R\), “open map + continuity” forces a global homeomorphism onto its image. The “local extremum contradicts openness” trick is ubiquitous in real analysis (e.g., showing that differentiable functions with nonzero derivative are monotone). Keep it in mind whenever you see openness hypotheses on the line.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Helper lemma:* a continuous non-monotone function on an interval has a local extremum in the interior. (Uses compactness/Extreme Value Theorem.)
- *Open-image contradiction:* the image of a neighborhood of a strict extremum cannot be open because the extremal value is a boundary point of that image.
- *Global conclusion:* absence of local extrema implies strict monotonicity on \(\mathbb R\).

**Stage 3 — LEAN FORMALIZATION**

Plan: (1) formalize `nonmonotone_has_local_extremum` using the Extreme Value Theorem (available in Mathlib as `continuous.exists_extremum_on`). (2) Prove that if `y` is a local maximum, then there exists an open interval whose image has `f y` as endpoint, contradicting the open-map hypothesis. (3) Deduce `StrictMono f ∨ StrictAnti f`. Stage 3 is still in progress; these lemmas need to be implemented in `Main.lean`, but the necessary ingredients (extremum existence, connectedness of intervals, open-map definitions) already exist in Mathlib.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the Lean proof is wired, mirror the exact lemmas in the write-up (especially the extremum and open-set arguments) so the exposition matches the formal certificate.

## Closer hop 1 — complete

Mathlib's `exists_Ioo_extr_on_Icc` gives the precise injectivity argument:
if `a < b` and `f a = f b`, continuity produces an interior maximum or
minimum on `[a,b]`. Openness of `f '' Ioo a b` rules out either extremum,
because an open neighborhood of the extremal value contains a strictly larger
or smaller nearby value. Thus `f` is injective, and
`Continuous.strictMono_of_inj` supplies the global increasing/decreasing
dichotomy.
