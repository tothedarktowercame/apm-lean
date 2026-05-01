# Informal Solution: t95A02

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** It is tempting to argue that a closed surjection sends compact sets to compact sets and therefore “pulls back” compactness, but the direction in the statement is the opposite: we must promote compactness from the target to the source. The only way to do that is to work with open covers of \(X\) and somehow use compactness of \(Y\); the trap is failing to use the compact fibres to localize the cover.

**Key insight.** Given an open cover of \(X\), every fibre \(f^{-1}(y)\) is compact, so it is contained in finitely many member sets. Using the fact that \(f\) is closed, those finitely many sets actually cover the entire preimage of some neighbourhood of \(y\). These neighbourhoods cover \(Y\); a finite subcover downstairs produces a finite subcover upstairs.

**Proof.** Let \(\mathcal U\) be an open cover of \(X\). We must extract finitely many sets from \(\mathcal U\) that still cover \(X\).

For each \(y\in Y\) the fibre \(F_y := f^{-1}(y)\) is compact. Since \(\mathcal U\) covers \(X\), in particular it covers \(F_y\), so there exist finitely many sets \(U_{y,1},\dots,U_{y,m_y} \in \mathcal U\) with \(F_y \subseteq \bigcup_{i=1}^{m_y} U_{y,i}\). Set \(W_y := X \setminus \bigcup_{i=1}^{m_y} U_{y,i}\), a closed subset of \(X\). Because \(f\) is closed, its image \(f(W_y)\) is closed in \(Y\). By construction, \(y\notin f(W_y)\) (otherwise its preimage would contain a point outside \(\bigcup U_{y,i}\)). Hence there is an open neighbourhood \(V_y\subseteq Y\) with \(y\in V_y\) and \(V_y \cap f(W_y)=\varnothing\). Then \(f^{-1}(V_y) \subseteq X\setminus W_y = \bigcup_{i=1}^{m_y} U_{y,i}\).

The open sets \(\{V_y : y\in Y\}\) cover \(Y\). Since \(Y\) is compact, finitely many of them suffice: choose \(y_1,\dots,y_k\) with \(Y = \bigcup_{j=1}^k V_{y_j}\). For each \(j\) keep the finite family \(U_{y_j,1},\dots,U_{y_j,m_{y_j}}\). Their union is a finite subcollection of \(\mathcal U\), and it covers \(X\) because
\[
X = f^{-1}(Y) = f^{-1}\Big(\bigcup_{j=1}^k V_{y_j}\Big) = \bigcup_{j=1}^k f^{-1}(V_{y_j}) \subseteq \bigcup_{j=1}^k \bigcup_{i=1}^{m_{y_j}} U_{y_j,i}.
\]
Thus every open cover of \(X\) admits a finite subcover; i.e. \(X\) is compact.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Compactness via open covers.** Lean dependency: `CompactSpace.compact_iff_finite_subcover`. Needed because the proof manipulates open covers directly.
- **Closed-map fibre shrinking.** Formal dependency: if \(f\) is closed and \(f^{-1}(y)\subseteq \bigcup_{i=1}^m U_i\), then there is an open neighbourhood \(V\ni y\) with \(f^{-1}(V)\subseteq \bigcup_{i=1}^m U_i\). This uses the compactness of the fibre for the finite cover and closedness of \(f\) to eliminate potential counterexamples.
- **Compactness pulled back through surjective maps.** Final step uses that \(f^{-1}(\bigcup V_j)=\bigcup f^{-1}(V_j)\). Once \(Y\) has a finite subcover, the corresponding finite union of preimages covers \(X\).

Lean search terms: `perfect_map`, `closedMap`, `compact_iff_finite_subcover`, `fibre_compact`. Intended Lean target: `perfect_map.compact_domain`. Mathlib status: there is no bundled `PerfectMap` structure yet, so the proof would require first introducing it or working manually with the hypotheses.

**Stage 3 — LEAN FORMALIZATION**

`/home/joe/code/apm-lean/ApmCanaries/Frames/T95A02/Apm_v2_t95A02_1775011739446/Main.lean` is still a stub because Mathlib currently lacks a definition/API for perfect maps (closed, continuous, fibre-compact surjections). Without that abstraction, the statement can’t even be registered as a named lemma; one would first need to add a structure capturing those hypotheses and basic lemmas about shrinking fibres. Consequently `lake build ...` still fails—the necessary framework is missing rather than a `sorry` proof.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The informal proof isolates exactly the ingredients Lean must know: (1) compact fibres admit finite subcovers of any open cover; (2) closed maps turn the complement of those sets into a closed subset downstairs; (3) compactness on \(Y\) yields a finite family of such neighbourhoods; (4) taking preimages produces the finite subcover of \(X\). Once Mathlib gains a `PerfectMap` structure and the supporting lemmas, the Lean proof will mirror this argument verbatim.
