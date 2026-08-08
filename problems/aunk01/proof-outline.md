# Proof Outline: aunk01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Closer hop 1 (2026-08-08)

The proof is closed using additive Haar invariance. The translated image is
rewritten as the preimage of `A` under `x ↦ x + (-y)`; measurability follows
by composition and its measure is unchanged by
`measure_preimage_add_right`. The integral clause is exactly
`integral_add_right_eq_self`. The frozen statement is unchanged and the Lean
proof is sorry-free.

## Imported Proof Plan

```clojure
{:goal "Prove that translations preserve Borel structure, Lebesgue measure, and L¹ integrals on ℝ."
 :terms [{:name "translation map"
          :meaning "τ_y(x)=x+y is a homeomorphism of ℝ"
          :needed-because "Homeomorphisms send Borel sets to Borel sets and preserve measurability of integrands."}
         {:name "translation invariance of Lebesgue measure"
          :meaning "m(A+y)=m(A) for every measurable A and y"
          :needed-because "This yields the measure identity and underlies the change-of-variables step."}
         {:name "change of variables"
          :meaning "∫ f(x+y) dm(x) = ∫ f(u) dm(u) via u=x+y"
          :needed-because "Converts the integrand back to f itself, proving invariance."}]
 :strategy [{:id :s1
             :formal-dependency "translation_map_measurable"
             :informal-dependency "Use that τ_y is continuous and invertible"
             :why-this-now "Establish that A+y remains Borel because τ_y^{-1}(A+y)=A."
             :lean-target "borel_map_translation"
             :mathlib-status "Continuous additive maps are measurable; translation homeomorphisms already live in Mathlib."}
            {:id :s2
             :formal-dependency "measure_preserving_translation"
             :informal-dependency "Known theorem: Lebesgue measure is invariant under translations"
             :why-this-now "Directly gives m(A+y)=m(A)."
             :lean-target "Real.volume_preimage_add_eq"
             :mathlib-status "Translation invariance for Haar measure on ℝ is in Mathlib."}
            {:id :s3
             :formal-dependency "integral_comp_translation"
             :informal-dependency "Apply change of variables using the measure-preserving map"
             :why-this-now "Shows the L¹ integral is unchanged."
             :lean-target "integral_comp_add_right"
             :mathlib-status "Exists as `MeasureTheory.integral_add_right_eq_self`."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'aunk01'
  :frame-id 'apm-v2-aunk01-1775005703226'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full informal solution explaining translation invariance details."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Captured the dependency graph linking translation measurability, measure preservation, and integral invariance."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Outlined Lean approach; blocked on locating the precise Mathlib lemmas for translation invariance without direct editing support."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**
Why it is hard.  Students usually try to treat $A+y$ as a mere image of $A$ under $x \mapsto x+y$ and forget that the image of a Borel set under a measurable map is not always Borel; you must exploit that translation is a homeomorphism and use preimages instead.  For part (b) people frequently plug the indicator of $A$ into part (c), which breaks down when $m(A)=\infty$.  Finally, one has to justify the change of variables in (c) inside the Lebesgue framework, not just heuristically.

Key insight.  Translation is a homeomorphism of $\mathbb R$ and hence preserves the Borel $\sigma$-algebra.  Lebesgue measure is the Haar measure on the additive group of $\mathbb R$, so it is translation invariant.  Measure-preserving maps leave $L^1$ integrals unchanged.  Package those three statements and every part of the problem becomes an application of a general theorem.

Complete proof.  Fix $y\in\mathbb R$ and write $\tau_y(x)=x+y$.  (a) We have $A+y=\{z : z-y\in A\}=\tau_{-y}^{-1}(A)$.  Because $\tau_{-y}$ is continuous, the preimage of a Borel set is Borel, so $A+y$ is Borel.

(b) Lebesgue measure $m$ is translation invariant: for every Borel $B$, $m(\tau_y^{-1}(B))=m(B)$.  Using $B=A+y$ and $\tau_y^{-1}(A+y)=A$ we get $m(A+y)=m(A)$ whether or not $m(A)$ is finite.

(c) Let $f\in L^1(\mathbb R)$.  Since $\tau_y$ is measure preserving, the Lebesgue change-of-variables formula gives
\[\int_{\mathbb R} f(x+y)\,dm(x)=\int_{\mathbb R} f(\tau_y x)\,dm(x)=\int_{\mathbb R} f(x)\,dm(x).\]
That is exactly the desired equality.

**Stage 2 — LEMMA DEPENDENCY GRAPH**
1. Translation is continuous and invertible ⇒ preimages of Borel sets stay Borel ⇒ (a).
2. Lebesgue measure is translation-invariant ⇒ measure preservation for $\tau_y$ ⇒ (b).
3. Measure-preserving change of variables ⇒ integral invariance ⇒ (c), depending on step 2.

**Stage 3 — LEAN FORMALIZATION**
Planned path: define the translation map once, reuse its continuity to get (a) via preimages, call the Mathlib lemma asserting `MeasurePreserving` for translations to deduce (b), and finally apply `MeasurePreserving.integral_comp` for (c).  Blocker: without working search/edit tooling I have not located the exact Mathlib names for the translation lemmas nor written `Main.lean`, so `lake build` has not yet been run.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**
When the missing lemmas are located, the Lean proof will match the prose step-for-step; no additional ideas are needed beyond those already documented in Stages 1 and 2.
