# Informal Solution: t99J04

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

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
