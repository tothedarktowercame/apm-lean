# Proof Outline: a94J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Prove absolute continuity of the integral for f ∈ L¹(ℝⁿ)."
 :terms [{:name "tail estimate"
          :meaning "Because f ∈ L¹, there exists R with ∫_{|f|>R} |f| < ε/2."
          :needed-because "Controls the portion where f is large."
         }
         {:name "measure control on bounded part"
          :meaning "On {|f|≤R}, we have |∫_E f| ≤ R·m(E)."
          :needed-because "Allows us to shrink δ based on the L∞ bound R."
         }
         {:name "set decomposition"
          :meaning "Split E into E∩{|f|>R} and E∩{|f|≤R}."
          :needed-because "Combines the tail estimate with the bounded part bound."}]
 :strategy [{:id :s1
             :formal-dependency "Integrable ⇒ tail integrals go to zero"
             :informal-dependency "Stage 1 tail estimate"
             :why-this-now "Ensures the part where |f| is large contributes < ε/2 regardless of E."
             :lean-target "l1_tail_control"
             :mathlib-status "Mathlib has `tendsto_integral_norm_of_dominated_loc`, but we just need Markov/Chebyshev-type tail control."}
            {:id :s2
             :formal-dependency "Bounded integrand × small measure"
             :informal-dependency "Stage 1 measure control"
             :why-this-now "Choose δ = ε/(2R) so that the bounded part of the integral is < ε/2."
             :lean-target "absolute_continuity_integral"
             :mathlib-status "Requires `volume` finiteness on small sets; straightforward multiplication bound."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a94J01'
  :frame-id 'apm-v2-a94J01-1775002964674'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the tail-splitting argument proving absolute continuity of the integral."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Recorded lemma dependencies (tail control + bounded-part estimate)."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Outlined Lean plan (tail lemma + integral bounds); coding not yet done."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.* This is an “absolute continuity of the integral” statement. The trap is to think of it as uniform continuity and try to use a naive estimate like \\(|f|≤M\\); but for general \\(f∈L^1\\) you only have integrability, not boundedness. You must split the integral into a tail where \\(|f|\\) is large (but whose mass is small) and a main part where \\(|f|\\) is bounded (so small measure means small integral). Forgetting to do this decomposition leaves you unable to choose \\(δ\\).

*Key insight.* Fix \\(ε>0\\). Because \\(f∈L^1\\), there exists \\(R>0\\) so that \\(∫_{|f|>R}|f|<ε/2\\). On the set where \\(|f|≤R\\) we have \\(|f|≤R\\), so integrating over a set of measure \\(δ=ε/(2R)\\) produces less than \\(ε/2\\). Splitting any measurable \\(E\\) into these two pieces yields the desired bound.

*Complete proof.* Let \\(ε>0\\). Choose \\(R>0\\) so that \\(∫_{|f|>R}|f|<ε/2\\) (possible by integrability). Set \\(δ=ε/(2R)\\). For any measurable \\(E\\) with \\(m(E)<δ\\), split
\\[
\int_E f = \int_{E∩\{|f|>R\}} f + \int_{E∩\{|f|≤R\}} f.
\\]
The first piece satisfies \\(|\int_{E∩\{|f|>R\}} f| ≤ ∫_{|f|>R}|f|<ε/2\\). For the second, \\(|f|≤R\\) on the domain, so \\(|\int_{E∩\{|f|≤R\}} f| ≤ R·m(E) < R·δ = ε/2\\). Summing the estimates yields \\(|\int_E f|<ε\\).

*What connects.* This is the measure-theoretic analogue of uniform continuity: an \(L^1\) function has “absolutely continuous integral” with respect to Lebesgue measure. The same technique appears in the proof that integrable functions form the dual of \(L^∞\), in Vitali’s theorem on absolute continuity of indefinite integrals, and in establishing countable additivity of measures defined via integrals.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Tail control:* lemma `l1_tail_control` supplying \(R\) with \(∫_{|f|>R}|f|<ε/2\). 
- *Bounded part estimate:* simple inequality \(|∫_{E∩\{|f|≤R\}} f| ≤ R·m(E)\).
- *Combination step:* combine the two estimates via set decomposition. Lean target: `integral_absolute_continuity`.

**Stage 3 — LEAN FORMALIZATION**

Implementation plan: (1) prove `l1_tail_control` using Chebyshev/Markov inequality or monotone convergence; (2) define the decomposition into `{x | |f x| ≤ R}` and its complement; (3) bound the integral of the bounded part via `norm_integral_le_integral_norm` plus the measure estimate; (4) add the tail contribution. Stage 3 remains in progress—these lemmas still need to be written in `Main.lean`, though Mathlib already contains most of the required facts (`MeasureTheory.integrable_iff_L1`).

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

After the Lean proof is coded, document exactly which Mathlib lemmas were used for the tail estimate and the bounded-part inequality to ensure the prose remains synchronized with the formal argument.
