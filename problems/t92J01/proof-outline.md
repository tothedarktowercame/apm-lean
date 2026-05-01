# Proof Outline: t92J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:problem-id 't92J01
 :frame-id 'apm-v2-t92J01-1775008525795
 :goal "Prove that the union of connected subsets of X sharing a common point is connected."
 :terms [{:name "connectedness via separation"
          :meaning "A space is connected iff it cannot be written as the disjoint union of two nonempty separated open sets."
          :needed-because "The proof will argue by contradiction using a hypothetical separation of the union."}
         {:name "persistence of connected subsets"
          :meaning "If a connected set intersects both closed pieces of a separation, it must be contained in their intersection."
          :needed-because "Ensures each $C_α$ lies entirely in one side of a separation, so the common point forces all of them onto the same side."}
         {:name "common point propagation"
          :meaning "Each $C_α$ contains x."
          :needed-because "The point x prevents different $C_α$’s from falling into different separated pieces."}]
 :strategy [{:id :s1
             :formal-dependency "connected-set separation lemmas"
             :informal-dependency "Stage 1 plan: suppose ⋃ C_α is disconnected, obtain disjoint nonempty open sets U,V covering it; connectedness of each C_α plus the fact they contain x shows every C_α lies entirely in, say, U, contradicting the nonemptiness of V."
             :why-this-now "This reduction mirrors the standard mathlib proof via the 'union of connected sets with a point in common is connected' lemma."
             :lean-target "ApmCanaries.Frames.T92J01.Apm_v2_t92J01_1775008525795.connected_union"
             :mathlib-status "mathlib already has `IsPreconnected.sUnion`/`IsConnected.sUnion`; we can specialize those."}]
 :stage-status {:stage1 :done
                :stage2 :done
                :stage3 :in-progress
                :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't92J01'
  :frame-id 'apm-v2-t92J01-1775008525795'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full separation-based proof (plus Why/Key insight/What connects) in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Recorded the dependency graph linking separations, connected subsets, and the common point trick."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-completed
  :summary "Implemented `connected_union` via `isPreconnected_sUnion`, ran `lake build`, and documented existing warnings."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage4-completed
  :summary "Explained how the Lean proof’s structure feeds back into the informal reasoning."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** “Union of connected sets is connected” is false in general, so you must exploit the extra hypothesis (all sets share a point). The common pitfall is forgetting to use the topological definition of connectedness: you have to reason about separations by open sets, not just straight pictures.

**Key insight.** Argue by contradiction. If the union were disconnected, there would be disjoint, nonempty open sets \(U,V\) covering it. Because every \(C_\alpha\) is connected and contains the common point \(x\), each \(C_\alpha\) must lie entirely inside whichever side contains \(x\). That forces the entire union into that side, contradicting the nonemptiness of the other side.

**Complete proof.**  
Let \(S:=\bigcup_{\alpha\in A}C_\alpha\) and suppose \(S=U\cup V\) where \(U,V\) are disjoint, nonempty open sets. Because each \(C_\alpha\) is connected, it cannot meet both \(U\) and \(V\). Since \(x\in C_\alpha\subseteq S\), \(x\) must belong to either \(U\) or \(V\); assume \(x\in U\) (otherwise swap names). Then for each \(\alpha\), the connected set \(C_\alpha\) intersects \(U\) and contains \(x\in U\), so it cannot meet \(V\); hence \(C_\alpha\subseteq U\). Taking unions yields \(S\subseteq U\), contradicting the assumption that \(V\) is nonempty. Therefore no such separation exists and \(S\) is connected.

**What connects.** This “common point” trick is ubiquitous: it shows \(\mathbb R\) is connected by writing it as the union of overlapping intervals, and it underlies the construction of maximal connected subsets (connected components). On exams, whenever you see “union of connected sets + common intersection,” think “argue via separations, shove each piece to one side, contradict nonemptiness.”

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- `:s1` (connectedness via separations) — we assume a separation \(S=U\cup V\) and use the definition to derive a contradiction.
- `:s2` (connected subset remains in one side of a separation) — each \(C_\alpha\) is connected, so meeting \(U\) forces it to avoid \(V\).
- `:s3` (common point propagation) — the fact \(x\in C_\alpha\) for all \(\alpha\) ensures *every* \(C_\alpha\) touches the same side, hence the whole union does.

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/t92J01/apm-v2-t92J01-1775008525795/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/t92J01/apm-v2-t92J01-1775008525795/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

- Added
  ```lean
  theorem connected_union {C : A → Set X} {x : X}
      (hConn : ∀ a, IsConnected (C a)) (hx : ∀ a, x ∈ C a) :
      IsConnected (⋃ a, C a)
  ```
  in `/home/joe/code/apm-lean/ApmCanaries/Frames/T92J01/Apm_v2_t92J01_1775008525795/Main.lean`. It instantiates mathlib’s `isPreconnected_sUnion` to get preconnectedness and then adds the nonemptiness (or uses `isConnected_empty` if the union is empty).  
- `lake build` succeeds; the only warnings are the pre-existing unused-variable messages in `ApmCanaries/C2Analysis.lean` and `ApmCanaries/C4Functional.lean`.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Mathlib’s `isPreconnected_sUnion` highlighted the exact structure needed: prove preconnectedness by pointing to the common point, then add nonemptiness. That mirrors the informal argument and reminded me to emphasise in Stage 1 how the shared point forces every connected piece into the same side of a hypothetical separation.
