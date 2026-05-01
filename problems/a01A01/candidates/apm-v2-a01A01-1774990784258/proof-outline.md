# Proof Outline: a01A01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Construct nonnegative functions f_k on [0,1] with ∫ f_k → 0 but limsup_k f_k(x) = ∞ for every x, and extend the construction to ℝⁿ."
 :terms [{:name "dyadic tiling"
          :meaning "partition [0,1] into 2^m equal half-open intervals at stage m"
          :needed-because "gives a canonical interval containing each x at every scale."}
         {:name "height-vs-width tradeoff"
          :meaning "choose spike height h_m and support width 2^{-m} so that h_m 2^{-m} → 0"
          :needed-because "forces ∫ f_k → 0 while the pointwise spikes still diverge."}
         {:name "enumeration by stage"
          :meaning "list the 2^m intervals of stage m consecutively so stage index → ∞"
          :needed-because "guarantees the integrals shrink along the actual sequence index."}]
 :strategy [{:id :s1
             :formal-dependency "Lebesgue integral of indicators of dyadic intervals on [0,1]"
             :informal-dependency "Assign height m+1 to each stage-m spike and order the spikes level-by-level"
             :why-this-now "Once the enumeration is fixed, every x sees the spike from each stage, so limsup diverges and the integral computation becomes routine."
             :lean-target "Define helper functions level/offset giving the stage and interval of the k-th function, then prove the integral formula and the limsup statement."
             :mathlib-status "Requires elementary lemmas about dyadic intervals and volumes; no external Mathlib gaps expected, though the helper combinatorics must be coded."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}
 :lean {:module-root 'ApmCanaries.Frames.A01A01.Apm_v2_a01A01_1774990784258'
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a01A01'
  :frame-id 'apm-v2-a01A01-1774990784258'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full reader-facing solution using dyadic spikes whose heights grow like m+1 but whose supports have length 2^{-m}, so ∫ f_k→0 while every point sees arbitrarily large spikes."
  :full-record? true
  :sorry? false
  :fully-closed? true}
 {:kind :stage2-completed
  :summary "Recorded the dependency graph: dyadic tilings, 'height×volume' integrals, and the level-by-level enumeration that drives the sequence of integrals to zero."
  :full-record? true
  :sorry? false
  :fully-closed? true}
 {:kind :stage3-progress
  :summary "Outlined the Lean plan (stageData recursion → dyadic indicator functions → integral/limsup lemmas); implementation still pending while those helper lemmas are coded."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.*  If you try to shrink the support of each \(f_k\) rapidly, particular points quickly stop seeing the spikes; if you keep the supports large, the integrals refuse to go to zero.  The trap is thinking you can concentrate the mass near finitely many locations and still drive the limsup to \(+\infty\) everywhere.  The right construction must simultaneously visit *every* point infinitely often *and* keep the total mass of each spike tiny.

*Key insight.*  Work stage-by-stage.  At stage \(m\) partition \([0,1]\) into the \(2^{m}\) dyadic intervals of length \(2^{-m}\) and place a spike of height \(m+1\) on each interval.  Enumerate all those spikes level-by-level: the integral of any stage-\(m\) spike equals \((m+1)2^{-m}\to 0\), while every point belongs to exactly one dyadic interval at each stage, so it sees spikes of height \(m+1\) for arbitrarily large \(m\).  The \(\mathbb{R}^{n}\) version just replaces dyadic intervals by dyadic cubes.

*Complete proof.*  For \(m\ge0\) let \(I_{m,j}=[j/2^{m},(j+1)/2^{m})\) with \(0\le j<2^{m}\).  Define the sequence by listing the functions
\[
g_{m,j}(x) = (m+1)\mathbf{1}_{I_{m,j}}(x)
\]
in the order \( (m,j) = (0,0), (1,0),(1,1),(2,0),(2,1),(2,2),(2,3),\dots\).  
For each \(k\) the associated level \(m\) is finite, and
\[
\int_{0}^{1} g_{m,j} = (m+1)\cdot |I_{m,j}| = \frac{m+1}{2^{m}},
\]
which tends to \(0\) with \(m\).  Because only finitely many spikes occur at each level and we cycle through the levels in order, the subsequence of integrals indexed by \((m,*)\) tends to zero, so the full sequence \(\int f_k\) tends to zero as \(k\to\infty\).

Fix \(x\in[0,1]\).  For every \(m\) there is exactly one \(j\) with \(x\in I_{m,j}\) (use the binary expansion; if \(x\) is dyadic, pick the unique interval that contains it on the left).  The subsequence \(f_{k(m)} := g_{m,j}\) then satisfies
\[
f_{k(m)}(x) = m+1 \longrightarrow \infty,
\]
so \(\limsup_{k\to\infty} f_{k}(x)=\infty\).  The same tiling argument works in \(\mathbb{R}^{n}\): cover the cube \([0,1]^{n}\) by dyadic cubes of side \(2^{-m}\), put spikes of height \(m+1\) on them, and then translate/scale the construction to cover all of \(\mathbb{R}^{n}\) by disjoint dyadic cubes.  Heights \(m+1\) and volumes \(2^{-mn}\) give integrals \((m+1)2^{-mn}\to0\), while every point lies in a unique dyadic cube at each level, so its limsup is still \(+\infty\).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

*Formal dependency.*  (i) Volume of a dyadic interval/cube is its side length (Lebesgue measure of `Icc`).  (ii) Indicators integrate to “height × volume”.  (iii) Enumerating the \(2^{m}\) cubes of level \(m\) consecutively makes the stage index tend to infinity.  

*Informal dependency.*  The dyadic tiling supplies the “every point sees every level” fact; the integral computation collapses to a one-line calculation once the tiling is fixed; the enumeration ensures the sequence of integrals actually tends to zero.

*Why this order.*  First fix the geometric tiling (without it the proof cannot start), next compute the integrals (so we know the mass goes to zero), and finally argue about limsups pointwise (once you know how the indices are ordered).

*Lean targets.*  Define a recursive helper `stageData : ℕ → ℕ × ℕ` returning the level \(m\) and the position \(j\), prove that `stageData (2^m - 1 + j) = (m, j)` for all `j < 2^m`, show the integral is `(m+1)/2^m`, and show the limsup is `∞` by constructing the subsequence `2^m - 1 + j(x,m)`.  These use only basic facts about powers of two and lengths of intervals.

**Stage 3 — LEAN FORMALIZATION**

`Main.lean` currently imports Mathlib and Scratch but the actual construction is still pending.  The next coding step is to implement `stageData` (level/offset recursion), define the dyadic indicator functions, and prove the integral formula plus the limsup lemma.  No Mathlib gaps are anticipated, but the combinatorial recursion and the real-floor lemma for `j(x,m)` still need to be written.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the recursion and floor lemmas are in place, the Lean development will match the prose proof verbatim: the enumeration guarantees stage growth, the integral computation will read “`intervalIntegral` of a constant over `Icc`”, and the pointwise limsup argument becomes a direct reference to the `j(x,m)` lemma.  Until those helpers are coded, the informal proof above remains the authoritative record.
