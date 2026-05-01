# Informal Solution: t92J03

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.**  The statement is Baire’s theorem in disguise.  Students often try to prove density by intersecting the given sets directly, but you must show that *every* nonempty open set meets the intersection.  The trap is forgetting that the intersection of dense sets need not be dense unless the space is “big” enough (here, completeness replaces local compactness).  You have to cook up a sequence of nested balls that survives all the countably many constraints simultaneously.

**Key insight.**  Fix any nonempty open ball `B₀`.  Recursively shrink inside both `B₀` and the `n`‑th dense open set `U_n`, producing a chain of closed balls `B₀ ⊇ B₁ ⊇ …` whose radii go to zero.  Completeness turns the centers into a Cauchy sequence that converges to a point lying in every `U_n` and back in `B₀`.  Because this works for an arbitrary starting ball, the whole intersection is dense.

**Complete proof.**  Let `(X,d)` be complete and `U_n ⊆ X` be open dense sets.  To show `⋂ₙ U_n` is dense, let `V` be an arbitrary nonempty open subset of `X`.  Pick `x₀ ∈ V ∩ U₀` (possible because `U₀` is dense) and radius `r₀>0` with the closed ball `B̄(x₀,r₀)` contained in `V ∩ U₀`.  Inductively, having chosen `B̄(x_n,r_n) ⊆ V ∩ ⋂_{k≤n} U_k`, use density of `U_{n+1}` to find `x_{n+1} ∈ U_{n+1} ∩ B(x_n, r_n/2)` and set `r_{n+1} = r_n/2`.  Then the closed balls satisfy `B̄(x_{n+1}, r_{n+1}) ⊆ B̄(x_n, r_n) ∩ U_{n+1}`.  The centers form a Cauchy sequence because `d(x_m,x_n) ≤ r_n` for `m ≥ n`, and `r_n → 0`.  Completeness gives a limit point `x ∈ X`.  Since `x ∈ B̄(x_n, r_n)` for each `n`, it lies in every `U_n` and in `V`.  Therefore `V ∩ ⋂ₙ U_n` is nonempty.  Because `V` was arbitrary, the intersection is dense.

**What connects.**  This is the metric-space version of Baire’s category theorem.  The nested-ball trick reappears whenever you need to find a point satisfying countably many dense open conditions (generic points in dynamical systems, simultaneous Diophantine approximation, forcing arguments, etc.).  Completeness (or its analogues such as local compactness) is what guarantees the limit exists; without it the conclusion can fail.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Density × openness ⇒ plenty of room.**  Every `U_n` meets any open ball; this feeds the inductive selection of centers inside previous balls (`Dense.inter_open`).
- **Nested closed balls ⇒ Cauchy.**  The chosen radii halve each step, so the distances between later centers are bounded by the current radius; this is the quantitative backbone for invoking completeness.
- **Completeness ⇒ limit ⇒ membership.**  Once the sequence converges, the limit lies in all closures of the balls, hence in every `U_n` and the original `V`.  Formally this is `Metric.complete_iff_cauchySeq_tendsto` plus the standard fact that dense open sets contain the closure of the constructed balls.

**Stage 3 — LEAN FORMALIZATION**

- Implemented the frame-local restatement `dense_iInter_of_open_dense` in `ApmCanaries/Frames/T92J03/Apm_v2_t92J03_1775008978201/Main.lean`, relying on Mathlib’s `Topology.dense_iInter_of_open_dense` together with the fact that complete metric spaces are Baire spaces.
- Ran `lake build` (see `/home/joe/code/apm-lean` log); it succeeded, with only pre-existing warnings about unused variables in other modules.  No `sorry` remain in this frame.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean proof emphasizes that “complete metric ⇒ Baire space” is an instance argument—once that class is available, the dense-intersection statement is a one-line consequence.  This perspective clarifies the informal proof: all the work goes into showing completeness ⇒ Baire, and the nested-ball argument is precisely what instantiates that instance.
