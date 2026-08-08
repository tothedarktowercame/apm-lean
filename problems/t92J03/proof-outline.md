# Proof Outline: t92J03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

Closer hop 1 closes the frozen theorem directly with
`dense_iInter_of_isOpen_nat hopen hdense`. The complete metric-space
assumptions provide Mathlib's `BaireSpace` instance, so no local nested-ball
construction is required.

## Imported Proof Plan

```clojure
{:problem-id 't92J03
 :frame-id 'apm-v2-t92J03-1775008978201
 :goal "Show that in a complete metric space every countable intersection of open dense sets is dense (Baire’s theorem in this special case)."
 :terms [{:name "dense open set"
          :meaning "A subset whose closure is the whole space and that is open."
          :needed-because "We repeatedly intersect a fixed open neighbourhood with each dense open set to build the desired point."}
         {:name "nested balls with shrinking radii"
          :meaning "Choose closed balls B₀ ⊇ B₁ ⊇ … with diameters → 0."
          :needed-because "These ensure the resulting centres form a Cauchy sequence contained in every chosen open dense set."}
         {:name "completeness ⇒ every Cauchy sequence converges"
          :meaning "In a complete metric space, Cauchy sequences converge to a limit inside the space."
          :needed-because "The constructed Cauchy sequence must converge to a point that lies in the intersection of all the dense sets."}]
 :strategy [{:id :s1
             :formal-dependency "metric completeness, Cauchy sequences, basic topology"
             :informal-dependency "Start with an arbitrary nonempty open set V. Use density to pick x₀ ∈ V ∩ U₀ and a ball whose closure sits inside that intersection. Iterate: choose x_{n+1} inside the previous ball and U_{n+1} with radius shrinking like 2^{-(n+1)}. The centres form a Cauchy sequence; completeness gives a limit x in all closures, hence in each U_n and in V. Therefore ⋂ₙ Uₙ meets every open V, i.e. it’s dense."
             :why-this-now "This is the constructive proof of the Baire category theorem specialized to complete metric spaces and countable families of open dense sets."
             :lean-target "ApmCanaries.Frames.T92J03.Apm_v2_t92J03_1775008978201.dense_iInter_of_open_dense"
             :mathlib-status "Mathlib already contains `dense_iInter_of_open_dense` as a corollary of the Baire theorem; we will restate it in this frame using the metric-space hypotheses."}]
 :stage-status {:stage1 :done
                :stage2 :done
                :stage3 :in-progress
                :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't92J03'
  :frame-id 'apm-v2-t92J03-1775008978201'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Authored the full reader-facing solution (why hard, key insight, complete proof, connections) for Baire’s theorem."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Documented the dependency chain: density ⇒ inductive balls ⇒ completeness ⇒ limit, matching the chosen lemmas."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-completed
  :summary "Implemented `dense_iInter_of_open_dense` in Main.lean and ran `lake build` successfully."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage4-completed
  :summary "Explained how the Lean proof perspective (complete ⇒ Baire) tightens the informal argument."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

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
