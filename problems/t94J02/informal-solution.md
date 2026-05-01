# Informal Solution: t94J02

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

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
