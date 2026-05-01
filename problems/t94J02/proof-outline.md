# Proof Outline: t94J02

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Given a compact Hausdorff topology \u03c3 on X, prove that any strictly finer topology \u03c4 loses compactness and any strictly coarser topology loses the Hausdorff property."
 :terms [{:name "finer vs. coarser topologies"
          :meaning "\u03c4 is finer than \u03c3 when every \u03c3-open set is \u03c4-open; coarser is the reverse ordering."
          :needed-because "It lets us view the identity map between (X,\u03c3) and (X,\u03c4) as continuous in the right direction, which is the mechanism for transferring compactness/Hausdorffness."}
         {:name "identity map continuity"
          :meaning "If \u03c4 is finer than \u03c3 the identity id_X : (X,\u03c4) \u2192 (X,\u03c3) is continuous, and if \u03c4 is coarser the opposite direction is continuous."
          :needed-because "Continuous bijections from compact spaces into Hausdorff spaces are embeddings; pushing compactness/Hausdorffness across identity maps exposes contradictions with strictness."}
         {:name "compact-to-Hausdorff surjections"
          :meaning "A continuous map from a compact space to a Hausdorff space is closed, hence a homeomorphism if bijective."
          :needed-because "This fact shows that a strictly finer topology cannot remain compact (id would be a homeomorphism otherwise) and a strictly coarser topology cannot remain Hausdorff."}]
 :strategy [{:id :s1
             :formal-dependency "Lean lemma that a continuous bijection from a compact space onto a Hausdorff space is a homeomorphism"
             :informal-dependency "Stage 1 (\u21d2) argument for stricter topology losing compactness"
             :why-this-now "By assuming \u03c4 finer and compact we would force id_X to be a homeomorphism, contradicting strictness."
             :lean-target "strictly_finer_not_compact"
             :mathlib-status "Lemma exists (e.g. `homeomorph_of_continuous_open` / `CompactSpace.inducing_of_surjective`)."}
            {:id :s2
             :formal-dependency "Lean lemma that a continuous bijection from a compact space is closed"
             :informal-dependency "Stage 1 (\u21d0) argument for coarser topology losing Hausdorff"
             :why-this-now "Assuming a strictly coarser topology remained Hausdorff would force the identity to be a homeomorphism again, contradicting strictness."
             :lean-target "strictly_coarser_not_hausdorff"
             :mathlib-status "Standard result; should already be in Mathlib as `T2Space.of_injective` variants."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't94J02'
  :frame-id 'apm-v2-t94J02-1775011263361'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-2-completed
  :summary "Wrote the reader-facing argument spelling out why strict refinement kills compactness/Hausdorffness and mapped the Lean dependencies (`continuous_id_of_le`, `Continuous.isClosedEmbedding`)."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-attempt
  :summary "Started encoding both topologies simultaneously via a wrapper type so the identity map can be treated as a morphism; blocked because Mathlib lacks a ready-made lemma turning a closed embedding of that identity back into equality of topologies."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** The definitions point in the “wrong” direction: compactness is phrased in terms of every open cover having a finite subcover, while “finer” means “more open sets”. Students often try to manufacture an explicit bad cover inside the finer topology, but that goes nowhere without knowing what the extra opens look like. Likewise, showing that a coarser topology is not Hausdorff feels strange because fewer opens usually make separation harder, yet we need a precise witness. The trap is ignoring the identity map between the two topological structures on the *same* underlying set.

**Key insight.** Treat both statements as consequences of functoriality. If \(\tau\) is finer than \(\sigma\), then the identity map
\[
\mathrm{id} : (X,\tau) \longrightarrow (X,\sigma)
\]
is continuous. Should \(\tau\) also be compact, this continuous bijection from a compact space to a Hausdorff space would be a homeomorphism, forcing the two topologies to coincide—contradicting strictness. The second clause is the same argument in reverse: if \(\tau\) is coarser, then the identity map \((X,\sigma)\to (X,\tau)\) is continuous; if \(\tau\) were Hausdorff we would again obtain a homeomorphism. Thus strict inequality of topologies prevents the “better” global property from surviving.

**Proof.** Let \(\sigma\) be a compact Hausdorff topology on \(X\).

1. Suppose \(\tau\) is strictly finer than \(\sigma\) and yet \((X,\tau)\) is compact. The underlying function \(\mathrm{id}:X\to X\) is bijective, and because \(\sigma\le \tau\) every \(\sigma\)-open set is \(\tau\)-open, so \(\mathrm{id}
:(X,\tau)\to (X,\sigma)\) is continuous. A continuous bijection from a compact space to a Hausdorff space is a homeomorphism, hence \(\mathrm{id}\) is a homeomorphism and \(\sigma=\tau\), contradicting the assumption that \(\tau\) is strictly finer. Therefore no strictly finer topology stays compact.

2. Suppose \(\tau\) is strictly coarser than \(\sigma\) and \((X,\tau)\) is Hausdorff. Then the identity map \((X,\sigma)\to (X,\tau)\) is continuous (because \(\tau\le\sigma\)). Since \((X,\sigma)\) is compact and \((X,\tau)\) is Hausdorff, the same “continuous bijection from compact to Hausdorff” criterion again gives that \(\mathrm{id}\) is a homeomorphism, forcing \(\sigma = \tau\), contradiction. Hence no strictly coarser topology stays Hausdorff.

That proves both claims.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Compact-to-Hausdorff bijection is a homeomorphism.** Formal dependency: `Continuous.isClosedMap` and `Continuous.isClosedEmbedding`. This supplies the engine for both directions by turning the identity into a homeomorphism whenever both topologies share compactness/Hausdorffness.
- **Order vs. continuity of the identity.** `continuous_id_of_le : σ ≤ τ → Continuous[t=τ,t'=σ] id` witnesses that the ordering on the lattice of topologies matches continuity of the identity map. This is the only place where the relation “finer/coarser” is used.
- **Strict inequality ⇒ contradiction.** Once the identity is known to be a homeomorphism, an antisymmetry argument in the lattice (or simply “a homeomorphism fixes the topology”) finishes each direction.

Lean search terms: `continuous_id_of_le`, `Continuous.isClosedEmbedding`, `Homeomorph`, `ClosedEmbedding.inducing`, `antisymm`.

**Stage 3 — LEAN FORMALIZATION**

- *Type-level bookkeeping.* I attempted to encode both topologies as explicit `TopologicalSpace` values on the same type. Lean’s type-class mechanism only allows one `TopologicalSpace` instance per type at a time, so expressing the identity map as a morphism between `(X,τ)` and `(X,σ)` requires either bundled `Top` objects or fresh type wrappers. I experimented with a wrapper `structure SpaceWith (σ : TopologicalSpace X)` that stores an `X` together with an induced topology. This makes the continuous identity routine, but threading the canonical equivalence back into Mathlib’s library (so that `CompactSpace`/`T2Space` instances transfer automatically) turned into a large amount of glue code.
- *Blocked lemma.* The missing piece is a clean statement that the identity map between two such wrappers is a homeomorphism exactly when the corresponding topologies coincide. Mathlib provides `continuous_id_of_le` and `Continuous.isClosedEmbedding`, but translating the result of `ClosedEmbedding` back into an equality of unbundled topologies requires a yet-to-be-written helper lemma. Until that lemma exists (or a convenient wrapper API is added), the formal proof remains stuck at the stage of defining the wrapper type and setting up the order/continuity lemmas.
- Build status: `lake build ApmCanaries.Frames.T94J02.Apm_v2_t94J02_1775011263361.Main` currently fails because the implementation of the wrapper/homeomorphism infrastructure is unfinished, so no `sorry`-free Lean theorem is available yet.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The informal proof hinges on the categorical viewpoint (identity as continuous bijection). The Lean work made it clear that we need a reusable interface for “the same underlying set equipped with two topologies”. A natural next step is to add a small API around the `Top` category or a dedicated wrapper so that `continuous_id_of_le`, `ClosedEmbedding`, and antisymmetry can be invoked without rebuilding the plumbing each time. Once that exists, the formal proof will mirror the Stage 1 argument line-for-line.
