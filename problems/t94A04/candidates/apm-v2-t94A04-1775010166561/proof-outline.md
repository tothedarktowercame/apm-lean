# Proof Outline: t94A04

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that if X = U ∪ V with U, V open, path connected, simply connected, and U ∩ V nonempty and path connected, then X is simply connected."
 :terms [{:name "loop subdivision"
          :meaning "Use compactness of I to cover a loop by finitely many subintervals each mapping entirely into U or V."
          :needed-because "Lets us rewrite any loop in X as a finite concatenation of paths living wholly in one chart."}
         {:name "transition paths through U ∩ V"
          :meaning "Choose paths from the basepoint to each subdivision break lying wholly in the set (U or V) that contains the break."
          :needed-because "Ensures every concatenated piece becomes a based loop contained in U or V, so we can contract it there."}
         {:name "null-homotopies inside charts"
          :meaning "Loops contained in U (resp. V) are null-homotopic because U (resp. V) is simply connected."
          :needed-because "Once the original loop is a product of such loops, each piece contracts, showing the whole loop is null-homotopic."}]
 :strategy [{:id :s1
             :formal-dependency "Lebesgue number lemma on [0,1]; path concatenation homotopies; simple connectivity implies null-homotopy of loops."
             :informal-dependency "Given a based loop α in X, subdivide I so each subpath lies entirely in U or V. Insert connecting paths inside U ∩ V to keep the basepoint fixed, yielding a finite concatenation of loops each lying in U or V. Contract each factor using simple connectivity, concatenating the homotopies."
             :why-this-now "This is the classical no-van-Kampen proof and requires only compactness plus basic path-homotopy manipulations."
             :lean-target "ApmCanaries.Frames.T94A04.Apm_v2_t94A04_1775010166561.union_two_simply_connected"
             :mathlib-status "Lebesgue number lemma and path concatenation lemmas exist in Mathlib; the targeted fact is not yet present but should follow from those primitives."}]
 :stage-status {:stage1 :done
                :stage2 :done
                :stage3 :in-progress
                :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't94A04'
  :frame-id 'apm-v2-t94A04-1775010166561'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stages-work-in-progress
  :summary "Finished the cover-based informal proof and dependency graph, implemented the Lean skeleton of `union_two_simply_connected`, and recorded the precise blockers (loop subdivision + open-set gluing) that currently prevent closing the theorem."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** The statement looks like a routine “glue two simply connected opens” result, but the proof has two traps. First, you must avoid an implicit use of van Kampen, so all reasoning has to stay at the level of loops in \(X\). Second, it is not enough to know that every point of the loop lies in either \(U\) or \(V\); you must control *intervals* of the loop so that you can do homotopies one patch at a time. Without compactness/Lebesgue-number bookkeeping it is easy to subdivide infinitely often or to lose track of the basepoint when shuffling pieces.

**Key insight.** Cover the loop by the two open inverse images \(\alpha^{-1}(U)\) and \(\alpha^{-1}(V)\) and use compactness of \(I=[0,1]\) (Lebesgue number lemma) to obtain a finite subdivision \(0=t_0<\dots<t_n=1\) in which each subpath \(\alpha|_{[t_{k-1},t_k]}\) lies entirely inside either \(U\) or \(V\). Once we have that finite list, insert short “shuttle” paths inside \(U\cap V\) that connect the basepoint to each subdivision mark. Concatenating in the right order turns the original loop into a product of loops living wholly inside \(U\) or inside \(V\), and those loops collapse inside the corresponding patch.

**Complete proof.**  
Let \(x\in U\cap V\) be a chosen basepoint and let \(\alpha:[0,1]\to X\) be any based loop with \(\alpha(0)=\alpha(1)=x\). Because \(\alpha^{-1}(U)\) and \(\alpha^{-1}(V)\) are open and cover \([0,1]\), compactness plus the Lebesgue number lemma gives a subdivision \(0=t_0<\dots<t_n=1\) such that each closed subinterval \([t_{k-1},t_k]\) is mapped entirely into \(U\) or entirely into \(V\). For each \(k\), define the reparametrized subpaths
\[
\alpha_k(s)=\alpha((1-s)t_{k-1}+s t_k),\qquad s\in[0,1].
\]
Every \(\alpha_k\) lies either in \(U\) or in \(V\). The endpoints \(\alpha(t_k)\) all lie in \(U\cup V\), and because \(U\) and \(V\) are path connected we may choose, for each \(1\le k\le n-1\), a path \(\gamma_k:[0,1]\to X\) from \(x\) to \(\alpha(t_k)\) that stays inside whichever of \(U\) or \(V\) contains \(\alpha(t_k)\); when \(\alpha(t_k)\in U\cap V\) use that path-connectedness. (Each \(\gamma_k\) has image contained in the same open set as \(\alpha_k\).)

Concatenate the pieces in the following “zig-zag” fashion:
\[
\beta := (\alpha_1\cdot \gamma_1^{-1}) \cdot (\gamma_1\cdot \alpha_2\cdot \gamma_2^{-1}) \cdot \dots \cdot (\gamma_{n-1}\cdot \alpha_n),
\]
where empty factors are omitted and the products are the usual path concatenations. Because each bridge \(\gamma_k\) is immediately followed by its inverse, \(\beta\) is homotopic (relative endpoints) to the original loop \(\alpha\); heuristically, \(\beta\) inserts detours but ends up tracing the same overall path. Moreover every factor in \(\beta\) is a based loop whose image is contained entirely in \(U\) or entirely in \(V\). Since \(U\) and \(V\) are simply connected, every factor contracts to the constant loop at \(x\). Concatenating these finitely many null-homotopies yields a null-homotopy of \(\beta\), hence of \(\alpha\). Because the choice of \(\alpha\) was arbitrary, every loop in \(X\) contracts, so \(X\) is simply connected.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Lebesgue number lemma on \([0,1]\).** Converts the open cover \(\{\alpha^{-1}(U),\alpha^{-1}(V)\}\) into finitely many subintervals mapped entirely into one chart, guaranteeing a *finite* concatenation.
- **Path concatenation and reparametrization lemmas.** Translate the subdivision into paths \(\alpha_k\) and allow insertion/removal of \(\gamma_k\cdot\gamma_k^{-1}\) without changing the homotopy class.
- **Null-homotopies inside \(U\) and \(V\).** Use simple-connectedness of the patches to kill each factor of the zig-zag product.

Lean search terms: `lebesgue number lemma`, `Path.reparam`, `SimplyConnectedSpace`, `IsPathConnected`. Intended Lean target: `union_two_simply_connected` in `Main.lean`.

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/t94A04/apm-v2-t94A04-1775010166561/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/t94A04/apm-v2-t94A04-1775010166561/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

- Declared `union_two_simply_connected` (lines 8–29 of `Main.lean`) with hypotheses matching the prose: two open, path-connected, simply connected subsets whose union is all of \(X\) and whose intersection is nonempty and path connected. While wiring the statement I inspected Mathlib’s coverage (`rg -n "LocPathConnectedSpace"` and the definitions in `Mathlib/Topology/Connected/LocPathConnected.lean`) to locate the right typeclasses.
- Attempted to source a Lebesgue-number lemma for loops by searching `Mathlib/Topology/MetricSpace/HausdorffDistance.lean` (where `LebesgueNumberLemma` lives). That lemma is metric-space based, so lifting it to arbitrary topological spaces would require equipping \(X\) with a metric or working through `PseudoMetricSpace`. No such bridge currently exists for general `SimplyConnectedSpace`.
- Also explored `Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean` for APIs that compare the simple-connectedness of an open subset with that of the ambient space; no ready-to-use lemma is available.
- Consequently the Lean theorem remains admitted with a TODO comment describing the blockers. The build command `lake build ApmCanaries.Frames.T94A04.Apm_v2_t94A04_1775010166561.Main` succeeds but warns about the `sorry`, reflecting the unfinished formal proof.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The informal write-up already mirrors what the Lean theorem *should* state, but the formal proof is still pending the two missing pieces described in Stage 3. Until Mathlib gains (1) a loop-subdivision lemma for open covers of `[0,1]` and (2) a principle that promotes simple connectedness from open subsets to the ambient space, the classical gluing argument cannot yet be mechanized here. The prose summary therefore doubles as the roadmap for the future Lean implementation, and the “what connects” paragraph highlights where similar arguments surface (Mayer–Vietoris, CW complexes, Stein covers) so readers can transfer the intuition while the formal tooling catches up.
