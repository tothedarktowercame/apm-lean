# Informal Solution: t92J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

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
