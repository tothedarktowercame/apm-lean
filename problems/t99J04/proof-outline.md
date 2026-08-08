# Proof Outline: t99J04

## Closer hop 4 update

The two remaining local gaps are now explicit Lean contracts. The general
`apm_t99J04_bridge_local_inverse_function` promotes `ContMDiffAt` plus a
bijective `mfderiv` to `IsLocalDiffeomorphAt`. The specialized
`apm_t99J04_bridge_coordinateMap_mfderiv_bijective` states the componentwise
derivative calculation and finite-dimensional conclusion for the frozen
coordinate map. Together they feed the first conjunct directly and the second
through `apm_t99J04_surjective_of_bijective_mfderiv_of_localIFT`.

## Closer hop 3 update

The second conjunct is now compiled modulo exactly the missing local theorem.
`apm_t99J04_surjective_of_bijective_mfderiv_of_localIFT` consumes the frozen
smoothness and pointwise-bijective-`mfderiv` assumptions, invokes an explicit
local inverse-function implication at each point, and feeds the resulting
`IsLocalDiffeomorph` into the compact-source/connected-target argument.

Mathlib's manifold API still only proves the reverse direction (a local
diffeomorphism has invertible `mfderiv`). Constructing the converse requires
manual chart transport and `PartialDiffeomorph` assembly. The first conjunct
also still needs the coordinatewise `mfderiv` identity before the existing
finite-dimensional algebra lemma applies.

## Closer hop 2 update

The finite-dimensional linear-algebra bridge now compiles for `n>0`.
An independent family of `n` covectors on an `n`-dimensional real space is
promoted to a dual basis; dual separation proves injectivity of the induced
coordinate map, and equality of finranks gives surjectivity. Thus the
mathematical step from independent coordinate differentials to an invertible
linear coordinate map is no longer open.

To use this in the frozen first conjunct, the manifold derivative of
`apm_t99J04_coordinateMap` must still be identified coordinatewise with the
given covectors, including a separate zero-dimensional case. Both conjuncts
then meet the same absent library bridge: assembling the chart-level Banach
inverse function theorem into `IsLocalDiffeomorphAt` from a bijective
`mfderiv`.

## Closer hop 1 update

The compiled helper `apm_t99J04_surjective_of_isLocalDiffeomorph` completes
the compact-to-connected global argument: the range is open by local
diffeomorphism, compact and therefore closed, nonempty, and hence all of the
connected target. Both frozen conjuncts now share one local obstruction:
Mathlib has the Banach-space inverse function theorem in charts, but its
manifold local-diffeomorphism file explicitly marks promotion from invertible
`mfderiv` as a TODO. The coordinate-map conjunct also needs the derivative
calculation and finite-dimensional linear-independence-to-bijectivity step.
The main theorem remains an honest partial with one `sorry` and an unchanged
declaration.

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that linearly independent differentials give a local coordinate chart and use that to prove a compact-source local diffeomorphism onto a connected target is surjective."
 :terms [{:name "inverse function theorem"
          :meaning "If the Jacobian of F = (f¹,…,fⁿ) at x is invertible, F restricts to a diffeomorphism from a neighborhood of x onto an open set of ℝⁿ."
          :needed-because "This produces the local coordinate system demanded in part (a)."}
         {:name "local diffeomorphism"
          :meaning "A map with everywhere-invertible derivative is locally a diffeomorphism, hence an open map with discrete fibers."
          :needed-because "Part (b) reduces to understanding the image of such a map."}
         {:name "open-and-closed image argument"
          :meaning "The image of a compact space under a continuous map is compact (so closed) and, when the map is open, also open."
          :needed-because "In a connected target, an open-and-closed subset must be all of Y, giving surjectivity."}]
 :strategy [{:id :s1
             :formal-dependency "Manifold.inverse_function_theorem"
             :informal-dependency "Apply the inverse function theorem to F = (f¹,…,fⁿ) to exhibit coordinates."
             :why-this-now "This resolves part (a) outright and supplies the local diffeomorphism input for part (b)."
             :lean-target "In Lean: from `LinearIndependent (dfᵢ x)` deduce that `(fun y ↦ (f¹ y,…,fⁿ y))` is a chart map at x."
             :mathlib-status "Mathlib already proves the inverse function theorem for smooth maps between finite-dimensional manifolds."}
            {:id :s2
             :formal-dependency "Manifold.compact_local_diffeomorphism_surjective"
             :informal-dependency "Use that f is open and proper (compact source) to show its image is nonempty, open, and closed, hence all of Y."
             :why-this-now "This solves part (b), leveraging the conclusion of part (a)."
             :lean-target "A Lean theorem stating that a smooth map between connected manifolds with compact source and invertible differentials is surjective."
             :mathlib-status "Mathlib does not currently bundle this exact corollary, but it has the ingredients (inverse function theorem plus topological facts)."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't99J04'
  :frame-id 'apm-v2-t99J04-1775013570926'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :target-check-populated
  :summary "Filled proof-plan/formal-alignment with the inverse-function and compact-local-diffeomorphism strategy."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-2-written
  :summary "Authored Stage 1 (why/key insight/proof/what connects) and Stage 2 dependency notes in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-blocked
  :summary "Documented that Mathlib lacks a bundled compact-local-diffeomorphism surjectivity lemma; Lean file still boilerplate."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** Students often remember the inverse function theorem in isolation but forget how to package several scalar-valued functions into a chart. Likewise, they hesitate on part (b) because “invertible derivative ⇒ diffeomorphism” is only local; turning that into a global statement requires both compactness and connectedness. The usual trap is to claim injectivity or surjectivity outright without justifying why the image of a local diffeomorphism is both open and closed.

**Key insight.** Bundle the functions into a single map `F = (f¹,…,fⁿ)` and apply the inverse function theorem: linear independence of the differentials means `dFₓ` is invertible, hence `F` provides coordinates near `x`. For part (b), notice that “everywhere-invertible derivative” makes `f` a local diffeomorphism and therefore an open map. With `X` compact the image is compact (hence closed), so in a connected target it must equal all of `Y`.

**Proof.**
1. Let `F : X → ℝⁿ`, `F(p) = (f¹(p),…,fⁿ(p))`. The linear independence of `df¹ₓ,…,dfⁿₓ` says that `dFₓ : TₓX → T_{F(x)}ℝⁿ ≅ ℝⁿ` is an isomorphism. By the inverse function theorem for manifolds, there exist neighborhoods `U` of `x` and `V` of `F(x)` such that `F|_U : U → V` is a diffeomorphism. The coordinate functions `f¹,…,fⁿ` therefore serve as local coordinates on `U`, as required.
2. Suppose `f : X → Y` satisfies the hypotheses in part (b). Since each `dfₓ` is invertible, the inverse function theorem gives neighborhoods `Uₓ` on which `f|_{Uₓ}` is a diffeomorphism onto an open subset of `Y`; hence `f` is a local diffeomorphism and in particular an open map. Because `X` is compact, `f(X)` is compact and thus closed in `Y`. An open, closed, nonempty subset of a connected space must be the whole space, so `f(X) = Y` and `f` is surjective.

**What connects.** The same argument reappears whenever you need to prove the existence of coordinates given an injective differential—e.g., showing that a submersion is locally a projection, or when constructing action-angle variables in symplectic geometry. The open-and-closed image trick is a staple for promoting local diffeomorphisms (or covering maps from compact sources) to global ones: it shows up in covering-space theory, Lie-group theory (proving that compact Lie groups map surjectively under local isomorphisms), and Riemann surface theory.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- `inverse_function_theorem`: takes the linear independence of the differentials and produces the local coordinate chart for part (a).
- `local_diffeomorphism_open`: a local diffeomorphism is an open map, used for part (b).
- `compact_image_closed`: image of a compact set is compact; in a Hausdorff manifold this makes it closed.
- `connected_open_closed`: in a connected space any subset that is both open and closed must be the entire space, giving surjectivity.

These steps match strategy nodes `s1` (coordinate chart) and `s2` (surjectivity) in `proof-plan.edn`.

**Stage 3 — LEAN FORMALIZATION**

Mathlib already contains a manifold-level inverse function theorem and facts about local diffeomorphisms being open, but it does **not** yet package the surjectivity corollary for compact-source local diffeomorphisms. Implementing it would require bundling the existing lemmas into a new theorem `compact_local_diffeomorphism_surjective`. Until that exists, our Lean files remain boilerplate (`Main.lean` just imports `Scratch.lean`), and `lake build ApmCanaries.Frames.T99J04.Apm_v2_t99J04_1775013570926.Main` trivially succeeds. To complete the formal side we would need to construct the `LocalHomeomorph` witnessing the local diffeomorphism, prove its openness, and combine it with compact-image-closed and connectedness.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

No changes needed: the informal proof already mirrors the structure that a future Lean lemma would follow (inverse function theorem → local diffeo → open/closed image). Once Mathlib gains the missing statement, Stage 3 can cite it directly without altering the exposition above.
