# Informal Solution: t94A05

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** Manifolds are defined via charts, not via global structure, so it is tempting to assume “connected ⇒ path connected” automatically—but that fails for general spaces (e.g. the topologist’s sine curve). The trap is forgetting to use the local Euclidean property to upgrade connectedness to local path connectedness, which is precisely what makes the argument go through without van Kampen.

**Key insight.** Use the fact that charts land in open subsets of ℝⁿ, which are path connected. Therefore manifolds are locally path connected: every point has arbitrarily small path connected neighborhoods. In a locally path connected space, path components are open (and closed). If the whole manifold is connected, there can be only one path component; hence any two points lie in the same component and are joined by a path.

**Complete proof.** Let \(M\) be a connected topological manifold. Fix \(x\in M\) and consider its path component \(P\). For any \(y\in P\) choose a chart \((U,\varphi)\) around \(y\); \(U\) is open in \(M\) and \(\varphi(U)\subseteq \mathbf{R}^n\) is open, hence path connected. Pulling paths back via \(\varphi^{-1}\) shows that \(U\) is path connected, so \(U\subseteq P\). Thus every point of \(P\) has a neighborhood contained in \(P\), so \(P\) is open. Its complement is a union of other path components; therefore the complement is also open. Because \(M\) is connected, the only subsets that are simultaneously open and closed are \(\varnothing\) and \(M\) itself, so \(P=M\). Since every point belongs to the path component of \(x\), any two points are path connected, completing the proof.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Charts give locally path connected neighborhoods.** Each chart image is an open subset of Euclidean space, hence path connected; pulling back by the chart shows that neighborhoods in \(M\) are path connected.
- **Path components are open in locally path connected spaces.** This converts the local information into an openness statement.
- **Connectedness kills multiple components.** A nontrivial decomposition into disjoint open sets would contradict connectedness, so there is only one path component.

Lean search terms: `ChartedSpace.locPathConnectedSpace`, `pathConnectedSpace_iff_connectedSpace`, `isConnected_iff_connectedSpace`.

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/t94A05/apm-v2-t94A05-1775010453161/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/t94A05/apm-v2-t94A05-1775010453161/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

- Added `connected_manifold_path_connected` in `Main.lean` (lines 12–24). It assumes a charted space modeled on a locally path connected space (e.g. ℝⁿ) together with a `ConnectedSpace` instance, and concludes `PathConnectedSpace`.
- Mathlib already supplies `ChartedSpace.locPathConnectedSpace` and the equivalence `pathConnectedSpace_iff_connectedSpace`, so the Lean proof is a one-liner after instantiating the local path connectedness. No `sorry`s remain.
- Command: `lake build ApmCanaries.Frames.T94A05.Apm_v2_t94A05_1775010453161.Main`.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean statement matches the prose argument exactly: once the charted-space hypothesis gives the locally path connected instance, `ConnectedSpace ⟹ PathConnectedSpace` is formalized by `pathConnectedSpace_iff_connectedSpace`. The Stage 1 discussion already emphasized these two ingredients, so no additional revision is needed; the informal explanation now directly mirrors the completed Lean proof.
