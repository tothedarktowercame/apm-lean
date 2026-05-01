# Proof Outline: t91A03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:problem-id 't91A03
 :frame-id 'apm-v2-t91A03-1775008066441
 :goal "Show that if X and Y are compact topological spaces, then the product space X×Y is compact."
 :terms [{:name "tube lemma"
          :meaning "Given compact K⊆X and y₀∈Y, every open set containing K×{y₀} contains a product U×V with K⊆U and y₀∈V."
          :needed-because "It lets an open cover of X×Y be refined into finitely many rectangles, reducing the cover of the product to two separate compactness arguments."}
         {:name "finite subcover of a fiber"
          :meaning "Fix x∈X; the slice {x}×Y inherits compactness from Y."
          :needed-because "Covering each slice by finitely many rectangles allows us to cover all of Y for finitely many x's."}
         {:name "compactness by open covers"
          :meaning "Characterization: a space is compact iff every open cover has a finite subcover."
          :needed-because "The entire argument is an open-cover proof, matching both the informal exposition and the Lean statement."}]
 :strategy [{:id :s1
             :formal-dependency "tube lemma and open-cover characterization of compactness"
             :informal-dependency "Stage 1 plan: start with an open cover of X×Y, extract neighborhood tubes around each point of X to obtain an open cover of Y, use compactness of Y to get a finite set of tubes, then use compactness of X to select finitely many of their bases."
             :why-this-now "This is the classical finite-subcover proof and mirrors mathlib’s `IsCompact.prod` lemma, ensuring the Lean and prose arguments stay aligned."
             :lean-target "ApmCanaries.Frames.T91A03.Apm_v2_t91A03_1775008066441.isCompact_prod"
             :mathlib-status "mathlib already has `IsCompact.prod` in `Topology/Basic`."}]
 :stage-status {:stage1 :done
                :stage2 :done
                :stage3 :in-progress
                :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't91A03'
  :frame-id 'apm-v2-t91A03-1775008066441'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the open-cover proof with the tube lemma together with the Why/Key insight commentary."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Explained in execute.md how the tube lemma, compact slices, and compactness of X interlock."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-completed
  :summary "Formalized `isCompact_prod` in Main.lean, ran `lake build`, and documented the existing external warnings."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage4-completed
  :summary "Described how the Lean proof (automatic use of `IsCompact.prod`) streamlines the informal argument."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** Compactness proofs via open covers are bookkeeping heavy: if you naively try to pull a subcover of \(X\times Y\), you quickly drown in indices because each open set mixes the two coordinates. Students often forget the “tube lemma” that lets you enlarge a cover of the slice \(\{x\}\times Y\) into a product neighborhood. Without that lemma you never get from finitely many sets over one \(x\) to an open neighborhood of \(x\) itself, so the argument stalls.

**Key insight.** Fix \(x\in X\). The slice \(\{x\}\times Y\) is compact (it is homeomorphic to \(Y\)), so any open cover of \(X\times Y\) restricts to a finite cover of this slice. The tube lemma then replaces each of the finitely many sets by a rectangle \(U_j\times V_j\) still sitting inside the original open set. The intersection \(O_x:=\bigcap_j U_j\) is an open neighborhood of \(x\) whose “tube” \(O_x\times Y\) is covered by the same finite union. Now \(\{O_x\}_{x\in X}\) covers \(X\), so compactness of \(X\) lets us keep only finitely many \(x\)’s—and hence only finitely many rectangles—which cover the entire product.

**Complete proof.**  
Let \(\{W_\lambda\}_{\lambda\in\Lambda}\) be an open cover of \(X\times Y\).

1. **Cover each vertical fiber by finitely many rectangles.** Fix \(x\in X\). The slice \(\{x\}\times Y\) is compact, so the subfamily \(\{W_\lambda\cap(\{x\}\times Y)\}_\lambda\) has a finite subcover \(W_{\lambda_1},\dots,W_{\lambda_{n_x}}\). For each \(j\) the tube lemma yields open sets \(U_{x,j}\subseteq X\) and \(V_{x,j}\subseteq Y\) with \(x\in U_{x,j}\), \(V_{x,j}\subseteq Y\), and \(U_{x,j}\times V_{x,j}\subseteq W_{\lambda_j}\). Then
   \[
   O_x:=\bigcap_{j=1}^{n_x} U_{x,j}
   \]
   is an open neighborhood of \(x\) that satisfies
   \[
   O_x\times Y \subseteq \bigcup_{j=1}^{n_x} (U_{x,j}\times V_{x,j}) \subseteq \bigcup_{j=1}^{n_x} W_{\lambda_j}.
   \]
   Consequently \(\bigcup_{x\in X} O_x = X\).

2. **Use compactness of \(X\).** Since \(\{O_x\}_{x\in X}\) is an open cover of \(X\), there exist finitely many points \(x_1,\dots,x_m\) such that \(X=\bigcup_{i=1}^m O_{x_i}\). The rectangles that appeared while constructing these \(O_{x_i}\)’s cover the product:
   \[
   X\times Y = \bigcup_{i=1}^m (O_{x_i}\times Y)
   \subseteq \bigcup_{i=1}^m \bigcup_{j=1}^{n_{x_i}} W_{\lambda_{i,j}}.
   \]
   The right-hand side is a finite union of members of the original cover \(\{W_\lambda\}\), so we have found a finite subcover of \(X\times Y\).

Thus every open cover of \(X\times Y\) has a finite subcover, meaning \(X\times Y\) is compact.

**What connects.** The exact same reasoning (tube lemma + iterative compactness) underlies Tychonoff’s theorem for finite products, the proof that a continuous image of a compact set is compact, and many arguments about approximation on product domains (e.g., uniform continuity on compact rectangles). Once you are comfortable shrinking covers around slices and then appealing to compactness of each factor in turn, more elaborate product and bundle arguments on exams become predictable.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- `:s1` (tube lemma) → turns the finite cover of the slice \(\{x\}\times Y\) into a block \(O_x\times Y\) contained in finitely many original opens.
- `:s2` (compact slice \(\{x\}\times Y\)) → justifies extracting the finite subcover for each fixed \(x\).
- `:s3` (compactness of \(X\) via open covers) → applied last to shrink \(\{O_x\}\) to finitely many tubes, yielding the global finite subcover.

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/t91A03/apm-v2-t91A03-1775008066441/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/t91A03/apm-v2-t91A03-1775008066441/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

- Implemented
  ```lean
  theorem isCompact_prod
    (hX : IsCompact (Set.univ : Set X)) (hY : IsCompact (Set.univ : Set Y)) :
    IsCompact (Set.univ : Set (X × Y))
  ```
  in `/home/joe/code/apm-lean/ApmCanaries/Frames/T91A03/Apm_v2_t91A03_1775008066441/Main.lean` by invoking mathlib’s `hX.prod hY`.  
- `lake build` succeeds; only the pre-existing warnings in `ApmCanaries/C2Analysis.lean` (unused variables `μ`, `F`) and `ApmCanaries/C4Functional.lean` (unused section variables `[CompleteSpace X]`) remain.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean proof stresses how little work is needed once you know `IsCompact.prod`; it literally collapses to “take compact singletons in each factor and use `prod`.” That mirrors the informal argument’s two compactness applications. Writing the formal proof before the prose reminded me to isolate the `O_x` neighborhoods explicitly (they are the `SetLike.tube`s hidden in the library), which is why Stage 1 now makes the passage from slices to tubes completely explicit.
