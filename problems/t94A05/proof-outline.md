# Proof Outline: t94A05

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that any connected topological manifold (second countable, Hausdorff, locally Euclidean) is path connected."
 :terms [{:name "local Euclidean charts"
          :meaning "Each point has a neighborhood homeomorphic to an open ball in ℝⁿ."
          :needed-because "Open balls are path connected, so these charts witness local path connectedness."}
         {:name "path components are open in locally path connected spaces"
          :meaning "If every point has arbitrarily small path connected neighborhoods, then its path component is a union of open sets."
          :needed-because "Shows that the path component through any point is both open and closed, hence equal to the entire connected manifold."}
         {:name "connected + open-and-closed component"
          :meaning "Connectedness forces subsets that are simultaneously open and closed to be trivial."
          :needed-because "Concludes that only one path component exists."}]
 :strategy [{:id :s1
             :formal-dependency "manifold ⇒ locally path connected; open-and-closed nature of path components in locally path connected spaces; connectedness eliminates multiple components."
             :informal-dependency "Pick x in M. Its path component is a union of chart neighborhoods, hence open. Its complement is a union of other components, also open. Connectedness forces the complement to be empty, so every point joins to x via a path."
             :why-this-now "This is the standard elementary route that avoids heavier algebraic-topology tools."
             :lean-target "ApmCanaries.Frames.T94A05.Apm_v2_t94A05_1775010453161.connected_manifold_path_connected"
             :mathlib-status "Mathlib already proves that manifolds are locally path connected (`Manifold.locPathConnected`) and that connected + locally path connected ⇒ path connected, so the formal goal should follow from existing lemmas."}]
 :stage-status {:stage1 :done
                :stage2 :done
                :stage3 :in-progress
                :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't94A05'
  :frame-id 'apm-v2-t94A05-1775010453161'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stages-1-4-completed
  :summary "Recorded the open-path-component proof, mapped dependencies, implemented `connected_manifold_path_connected` in Lean (no sorrys), and synced the formal/informal narratives."
  :full-record? true
  :sorry? false
  :fully-closed? true}]
```

## Imported Execution Notes

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
