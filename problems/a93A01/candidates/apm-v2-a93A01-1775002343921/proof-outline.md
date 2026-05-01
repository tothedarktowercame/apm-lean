# Proof Outline: a93A01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that f:(0,1)→ℝ is uniformly continuous iff large finite differences force small increments."
 :terms [{:name "uniform continuity"
          :meaning "∀ε>0 ∃δ>0, |x-y|<δ ⇒ |f x - f y|<ε"
          :needed-because "One side of the equivalence."}
         {:name "difference quotient control"
          :meaning "Whenever |(f x - f y)/(x-y)| is huge, the increment itself must be tiny"
          :needed-because "Encodes the other side of the equivalence."}
         {:name "contrapositive sequences"
          :meaning "If f is not uniformly continuous, there are sequences with |xₖ-yₖ|→0 but |f xₖ - f yₖ| ≥ ε₀"
          :needed-because "Used to contradict (b) when (a) fails."}]
 :strategy [{:id :s1
             :formal-dependency "Uniform continuity definition"
             :informal-dependency "Stage 1 step (a)⇒(b)"
             :why-this-now "Given ε pick δ, then any quotient exceeding N := ε/δ forces |x-y|<δ hence |f x - f y|<ε."
             :lean-target "uniformContinuous_implies_diffQuot_condition"
             :mathlib-status "Direct δ–ε argument; relies on arithmetic with ℝ."}
            {:id :s2
             :formal-dependency "Sequential criterion for failure of uniform continuity"
             :informal-dependency "Stage 1 step (b)⇒(a) via contrapositive"
             :why-this-now "Construct sequences violating (b) if uniform continuity fails."
             :lean-target "diffQuot_condition_implies_uniformContinuous"
             :mathlib-status "Uses `UniformContinuous`, sequence extraction, and algebra of difference quotients."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a93A01'
  :frame-id 'apm-v2-a93A01-1775002343921'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Explained both directions (uniform continuity ⇔ large-quotiens force tiny increments) in prose."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Captured the boundedness, contrapositive, and sequential tools needed for the equivalence."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Lean proof blocked: Mathlib lacks a sequential characterization of ¬UniformContinuous (see `rg -n \"not_uniformContinuous\"`)."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

***Why it’s hard.***  Condition (b) looks strange: it does not bound the usual difference quotient uniformly; instead it says “whenever the slope gets outrageously large, the actual increment must be tiny.” The trap is to think (b) is stronger than uniform continuity—it isn’t. You need to read it contrapositive: if two function values stay ε apart, the slope cannot blow up. That viewpoint makes the equivalence transparent.

***Key insight.***  Work with the contrapositive of (b): for each ε>0 there is N such that |f(x)-f(y)| ≥ ε forces |(f(x)-f(y))/(x-y)| ≤ N. Uniform continuity on a bounded domain implies (i) there exists δ so that |x-y|<δ ⇒ |f(x)-f(y)|<ε, and (ii) f is bounded, hence |f(x)-f(y)| ≤ 2M for some M. So when |f(x)-f(y)| ≥ ε, we have |x-y| ≥ δ, and therefore the difference quotient is ≤ 2M/δ. The other direction is proved by contrapositive: if f is not uniformly continuous there exist xₙ,yₙ with |xₙ-yₙ|→0 but |f(xₙ)-f(yₙ)| ≥ ε₀, so the quotients tend to ∞ and (b) fails.

***Complete proof.***
- *(a) ⇒ (b).*  Fix ε>0. Uniform continuity gives δ>0 with |x-y|<δ ⇒ |f(x)-f(y)|<ε. Since (0,1) is bounded and f is uniformly continuous, f is bounded: pick M>0 with |f(x)|≤M for all x. For |f(x)-f(y)|≥ε we must have |x-y|≥δ (contrapositive of uniform continuity), hence
  \[\frac{|f(x)-f(y)|}{|x-y|} ≤ \frac{2M}{δ} =: N.\]
  Taking contrapositive, |(f(x)-f(y))/(x-y)|>N forces |f(x)-f(y)|<ε.
- *(b) ⇒ (a).*  Suppose (a) fails. Then there exist ε₀>0 and sequences xₙ,yₙ∈(0,1) with |xₙ-yₙ|→0 but |f(xₙ)-f(yₙ)|≥ε₀. Then
  \[\left|\frac{f(xₙ)-f(yₙ)}{xₙ-yₙ}\right| ≥ \frac{ε₀}{|xₙ-yₙ|} → ∞.\]
  For ε=ε₀, property (b) provides an N; choose n so large that the quotient exceeds N while |f(xₙ)-f(yₙ)|≥ε₀, contradicting (b). Thus f must be uniformly continuous.

***What connects.***  This repackages the usual “uniform continuity prevents arbitrarily steep slopes on bounded domains” idea. The contrapositive construction is the same one used in the Heine–Cantor theorem (compactness) and in the Riesz sequential criterion for uniform continuity.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Uniform continuity ⇒ boundedness on bounded domains.*  Needed to control |f(x)-f(y)| by a global constant 2M.
- *Contrapositive of uniform continuity.*  |f(x)-f(y)|≥ε implies |x-y|≥δ.
- *Sequential characterization of non-uniform continuity.*  Used to prove (b)⇒(a).

**Stage 3 — LEAN FORMALIZATION**

- *Target.*  `uniformContinuous_iff_largeDiffQuot_smallIncrement` (see `formal-alignment.edn`).
- *Status — blocked.*  Mathlib lacks the “sequential characterization of failure of uniform continuity” needed for the (b)⇒(a) direction. A repository search (`rg -n "not_uniformContinuous" -g"*.lean"`) returned no hits. Without a lemma supplying the sequences xₙ,yₙ promised by the analysis proof, the contrapositive argument cannot yet be formalized. Filling the gap would require adding a result of the form `¬UniformContinuous f ↔ ∃ ε>0, ∀ δ>0, ∃ x y, |x-y|<δ ∧ |f x - f y| ≥ ε`, after which the Lean proof could proceed as above.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the sequential lemma exists, the Lean development will mirror Stage 1: derive boundedness and δ from uniform continuity for (a)⇒(b), and use the sequences to contradict (b) when uniform continuity fails.
