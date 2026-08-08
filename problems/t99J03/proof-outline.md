# Proof Outline: t99J03

## Compiled progress

The lemmas `apm_t99J03_eulerCharacteristic_orientable` and
`apm_t99J03_eulerCharacteristic_nonorientable` prove both displayed Euler
formulas definitionally. The main theorem is reduced by simplification to the
classification dichotomy and uniqueness alone.

## Remaining Lean boundary

Classify every compact connected smooth two-manifold as exactly one of the
concrete orientable polygon quotients or a positive-genus nonorientable
quotient. This requires triangulation, fundamental-polygon construction,
paired-edge normalization, homeomorphism assembly, and invariants proving
uniqueness. Neither Mathlib nor `ConstructionTargets.Surfaces` packages this
classification.

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Describe the connected-sum and Euler-characteristic classifications of compact connected triangulated surfaces and outline how the polygon-cutting proof produces them."
 :terms [{:name "connected sum model"
          :meaning "Every closed surface is built by connected sums of tori or of projective planes."
          :needed-because "Part (a) asks for this precise statement and the later parts rely on it."}
         {:name "orientability dichotomy"
          :meaning "Each surface is either orientable (handlebody) or nonorientable (crosscap sum)."
          :needed-because "The outline in part (b) splits into these two cases and the Euler characteristic formula depends on which case we are in."}
         {:name "Euler characteristic bookkeeping"
          :meaning "χ detects the number of handles or crosscaps via χ = 2 − 2g or χ = 2 − k."
          :needed-because "Part (c) phrases the classification numerically, so we must track how χ behaves under connected sum."}]
 :strategy [{:id :s1
             :formal-dependency "Surface.classification_connected_sum"
             :informal-dependency "Start from a triangulation, cut to obtain a polygon, and use edge pairings to read off handles or crosscaps."
             :why-this-now "This is the classical route to the classification and simultaneously answers parts (a) and (b)."
             :lean-target "A Lean theorem stating that any compact connected triangulated 2-manifold is homeomorphic to a connected sum of g tori or k projective planes."
             :mathlib-status "No such theorem is currently exposed in Mathlib; implementing it would require the full surface classification project."}
            {:id :s2
             :formal-dependency "Surface.euler_characteristic_classification"
             :informal-dependency "Combine χ(S#T) = χ(S)+χ(T)−2 with the connected-sum list to derive χ = 2−2g (orientable) and χ = 2−k (nonorientable)."
             :why-this-now "This converts the structural classification into the Euler-characteristic statement demanded in part (c)."
             :lean-target "A Lean corollary equating the Euler characteristic with the handle/crosscap count."
             :mathlib-status "Same blocker: Mathlib lacks the foundational classification, so this corollary is also unavailable."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't99J03'
  :frame-id 'apm-v2-t99J03-1775013445880'
  :summary "Created isolated proof-frame workspace for the surface-classification problem."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :target-check-populated
  :summary "Recorded the connected-sum/Euler plan and alignment targets for the surface classification."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-2-written
  :summary "Authored the Stage 1 explanation (why/key insight/proof/what connects) and Stage 2 dependency notes in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-blocked
  :summary "Documented that Mathlib lacks any surface-classification theorems, so no Lean development is possible yet."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** Most prelim takers can recite “handles versus crosscaps,” but the exam asks for more: the exact connected-sum statement, the proof strategy, and the Euler-characteristic reformulation. Students get lost when they cannot remember how to pass from a triangulation to a single polygon or how to detect orientability from edge pairings. Another frequent trap is stating the Euler-characteristic formulas without explaining why they follow from the connected-sum description.

**Key insight.** Cut the surface open until it turns into one polygon whose edges come in identified pairs. By sliding diagonals and re-gluing, every edge-pairing is equivalent either to a string of “oriented” pairs (producing handles) or to a string of “unoriented” pairs (producing crosscaps). Connected sum with a torus adds a handle; connected sum with a projective plane adds a crosscap. Because Euler characteristic is additive under connected sum and handles/crosscaps change χ in predictable ways, the polygon model simultaneously gives the structural classification and its Euler version.

**Proof.**
1. **(Part a: statement.)** Every compact, connected, triangulated surface is homeomorphic to exactly one of the following: (i) a connected sum of `g ≥ 0` copies of the torus `T²` (an orientable surface of genus `g`), or (ii) a connected sum of `k ≥ 1` copies of the projective plane `ℝP²` (a nonorientable surface with `k` crosscaps). The integers `g` and `k` are uniquely determined.
2. **(Part b: outline of proof.)**
   - Start with any triangulation. Choose a spanning tree in the dual 1-skeleton and cut along the corresponding edges. The surface opens into a single 2n-gon whose sides are glued in pairs. (All triangulated closed surfaces admit such a fundamental polygon.)
   - Label the polygon edges with arrows. Reversing the orientation of the 2n-gon if necessary, every edge occurs exactly twice; the two occurrences may point in the same direction (an “oriented” pair) or opposite directions (an “unoriented” pair). The polygon describes the surface obtained by gluing each pair.
   - Use cut-and-paste moves: (i) if two identical oriented pairs sit next to one another, they represent a handle (a torus summand); (ii) if two identical unoriented pairs are adjacent, they represent a crosscap (a projective-plane summand); (iii) sliding edges shows that any mixed pairing can be rewritten as a connected sum of only handles or only crosscaps. Crosscaps come in pairs, and two crosscaps can be converted into a single handle, so the normal form is either “all oriented” or “all unoriented.”
   - The number of handles (resp. crosscaps) is well defined because the polygon moves never change how many oriented or unoriented pairs remain. Hence each surface is homeomorphic to a connected sum of `g` tori or of `k` projective planes, with `g` and `k` uniquely determined; orientability decides which case occurs.
3. **(Part c: Euler-characteristic classification.)** Euler characteristic behaves additively under connected sum: `χ(S # S′) = χ(S) + χ(S′) − 2`, because removing a disk from each surface decreases χ by 1 and gluing along the resulting boundaries does not change χ. For the torus, `χ(T²) = 0`, so `χ(Σ_g T²) = 2 − 2g`. For the projective plane, `χ(ℝP²) = 1`, so `χ(Σ_k ℝP²) = 2 − k`. Therefore an orientable surface is determined uniquely by its genus `g = (2 − χ)/2`, and a nonorientable surface is determined uniquely by `k = 2 − χ`.

**What connects.** The polygon-cutting method is the same engine behind the classification of Fuchsian groups, computation of fundamental groups of surfaces, and the design of pair-of-pants decompositions used in Teichmüller theory. The Euler-characteristic bookkeeping also reappears whenever you need to identify whether a covering map is orientable or to bound the number of crosscaps a quotient surface can carry. On exams, keep the “cut to one polygon, read the arrows, simplify to handles or crosscaps” template handy.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- `fundamental_polygon`: from a triangulation we can cut along a dual spanning tree to get one polygon with paired edges.
- `polygon_moves`: edge slides and flips preserve the homeomorphism class but allow us to group oriented pairs (handles) or unoriented pairs (crosscaps).
- `orientability_dichotomy`: after simplifying, either all pairs are oriented (so the surface is orientable) or all are unoriented (nonorientable).
- `Euler_additivity`: `χ(S # S′) = χ(S) + χ(S′) − 2`, giving χ-formulas for the normal forms.

This mirrors the machine plan: s1 produces the connected-sum classification, and s2 converts it into the Euler-characteristic formulae.

**Stage 3 — LEAN FORMALIZATION**

Mathlib currently has no formal treatment of the surface-classification theorem, so there is no existing constant to restate or extend. Searching the dependency tree (`rg -n "Surface" .lake/packages/mathlib/Mathlib | grep -i classify`) reveals no occurrences, and neither the `Topology` nor `Geometry` directories contain the polygon-based classification. Building it in Lean would require a full CW-complex development of surfaces, polygon gluings, and handle/crosscap normal forms—significantly beyond this frame. Consequently `Main.lean` still contains only the intentional boilerplate, and no `lake build` is necessary (the file already compiles as-is). The gap to close is clear: implement polygonal schema for surfaces and prove the classification before attempting the Euler-characteristic corollary.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The informal write-up already states both the structural and Euler-characteristic versions of the classification plus the proof outline. Once Mathlib acquires a `surface_classification` theorem, this frame should be updated by replacing Stage 3 with a reference to that declaration and by citing the Lean file where the theorem is re-exported; no change to the Stage 1 narrative will be necessary.
