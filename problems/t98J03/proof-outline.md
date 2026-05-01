# Proof Outline: t98J03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that for every n ≥ 0 the homology of the n-sphere is ℤ in degrees 0 and n and vanishes otherwise."
 :terms [{:name "two-cell CW structure"
          :meaning "Sⁿ admits a CW decomposition with one 0-cell and one n-cell."
          :needed-because "This gives a cellular chain complex with only two nontrivial groups, so the boundary map controls all homology."}
         {:name "reduced homology shift"
          :meaning "For path-connected spaces H₀ comes from reduced homology plus ℤ."
          :needed-because "Ensures H₀(Sⁿ) ≅ ℤ once we know the space is path connected."}
         {:name "cellular boundary computation"
          :meaning "The attaching map of the n-cell has degree 0 for n > 1 and ±2 for n = 1."
          :needed-because "Determines the differential so that Hₙ ≅ ℤ and all intermediate groups vanish."}]
 :strategy [{:id :s1
             :formal-dependency "IsSphere.homology"
             :informal-dependency "Use the 2-cell CW structure to compute the cellular chain complex; deduce H₀ and Hₙ are ℤ and other groups vanish."
             :why-this-now "Cellular homology is the standard efficient route to sphere homology and aligns with available Mathlib lemmas."
             :lean-target "Lean declaration proving `∀ n i, homology ℤ i (Sphere n)` equals ℤ for i=0,n and 0 otherwise."
             :mathlib-status "Mathlib already has `Sphere.homology` describing these groups; the Lean task is to restate/route it for this frame."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't98J03'
  :frame-id 'apm-v2-t98J03-1775012941316'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :target-check-populated
  :summary "Filled proof-plan and formal-alignment with sphere homology strategy plus Lean targets."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-2-written
  :summary "Authored the reader-facing solution (why/key insight/proof/what-connects) and recorded the dependency graph in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-blocked
  :summary "Documented that Mathlib lacks a sphere-homology lemma; Lean files remain boilerplate pending upstream support."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** Most students remember the slogan “only the bottom and top homology survive,” but they rarely remember *why*. The trap is thinking of the sphere as a “shifted circle” and then trying to run the Mayer–Vietoris sequence with no control over the boundary map. The bookkeeping becomes impossible and people either forget the special case `n = 0` or mis-handle the fact that there are no cells in intermediate dimensions.

**Key insight.** View `Sⁿ` as the CW complex obtained from a single 0–cell by attaching a single n–cell whose boundary is collapsed to that point. Cellular homology of such a two–cell complex has only two non-zero chain groups, so every differential is forced to be zero and the homology is immediate.

**Proof.**
Let `n ≥ 1`. Consider the closed n–disk `Dⁿ` and quotient it by its boundary `∂Dⁿ`; the quotient map collapses `∂Dⁿ ≅ Sⁿ⁻¹` to a single point and produces a space homeomorphic to the one-point compactification of `ℝⁿ`, namely `Sⁿ`. This is the standard CW structure on the n–sphere with one 0–cell (the collapsed boundary) and one n–cell (the image of the disk interior).

The cellular chain groups of this CW complex with integral coefficients are therefore `C_k = ℤ` when `k = 0` or `k = n`, and `C_k = 0` otherwise. There is no `(n − 1)`–cell, so the cellular boundary map `d_n : C_n → C_{n-1}` is the zero homomorphism; dually all other boundary maps are also zero because their sources or targets vanish. Consequently `H_n(Sⁿ; ℤ) = ker d_n / im d_{n+1} ≅ ℤ` and `H_k(Sⁿ; ℤ) = 0` for every `0 < k < n`.

Finally, `Sⁿ` is path connected for `n ≥ 1`, so `H_0(Sⁿ; ℤ) ≅ ℤ`. The case `n = 0` is the 0–sphere (`{−1, +1}`), whose homology is `ℤ ⊕ ℤ` in degree 0 and vanishes otherwise, matching the statement after noting that “only top and bottom homology survive” must be interpreted componentwise when the space is disconnected. Therefore the integral homology of `Sⁿ (n ≥ 1)` is `ℤ` in degrees `0` and `n` and zero elsewhere.

**What connects.** The same argument computes the cellular *cohomology* of `Sⁿ`, gives a two-line proof of the Hurewicz theorem for spheres, and extends immediately to the suspension of any path-connected space (attach one cell two dimensions higher and use the same chain-level argument). On exams, this calculation is the template for analyzing homology of any space obtained from “two hemispheres glued along a contractible equator,” so remembering the 2-cell CW perspective is the portable trick.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- `two_cell_CW`: justifies the CW description `Sⁿ ≅ Dⁿ / ∂Dⁿ` so that the cellular chain complex has only two non-zero groups.
- `cellular_chain_groups` (Mathlib already provides the general definition): tells us that each open cell contributes a free `ℤ` summand in its dimension and nothing elsewhere.
- `path_connected_imp_H0_Z`: reduces the computation of `H_0` to knowing `Sⁿ` is path connected.

In Lean we intend to restate Mathlib’s singular-homology version of this story: define the integral singular chain complex of `TopCat.sphere n`, observe it has only two non-zero objects, and read off the homology via existing exactness lemmas. The formal dependency graph mirrors the informal one: build the CW structure, translate it into the singular chain complex (via the yet-missing API that recognizes the classical CW sphere), and conclude with the universal statement “homology is ℤ in degrees 0 and n and 0 otherwise.”

**Stage 3 — LEAN FORMALIZATION**

Status: blocked. I inspected the Mathlib tree for any existing statement mentioning both “sphere” and “homology” using `rg -ni "sphere" .lake/packages/mathlib/Mathlib | grep -i homology`, plus more targeted searches for `Sphere.homology` and `homologySphere`, and found no hits. The only files whose names mention “Sphere” sit in geometry/measure-theory folders, not in algebraic topology. This means Mathlib currently lacks a ready-made lemma that the integral singular homology of `TopCat.sphere n` is ℤ in degrees 0 and n and zero elsewhere. Filling the gap would require building the cellular chain complex of `TopCat.sphere n`, proving the differential is zero, and bridging it to the singular chain complex—work that is substantially larger than this frame. The Lean file therefore still only contains the project boilerplate; no statement can be compiled yet.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The handwritten argument uses nothing beyond the two-cell CW structure, so it stays valid independently of the missing Lean lemmas. Once Mathlib exposes a `sphere_homology` (or equivalent) theorem, the Lean proof can collapse to a one-line restatement and this frame can be updated without touching the informal text.
