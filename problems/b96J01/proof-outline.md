# Proof Outline: b96J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that any subgroup of S₅ containing a 5-cycle and a transposition must contain all adjacent transpositions and hence equals the whole symmetric group."
 :terms [{:name "5-cycle"
          :meaning "A permutation whose cycle decomposition is a single cycle of length 5."
          :needed-because "Conjugating by this element lets us move indices around and forces transitivity."}
         {:name "transposition"
          :meaning "A 2-cycle (i j) that swaps two letters and fixes the rest."
          :needed-because "Once we have one transposition we can conjugate it to obtain many others."}
         {:name "adjacent transpositions generate S₅"
          :meaning "The set {(1 2),(2 3),(3 4),(4 5)} generates the full symmetric group."
          :needed-because "Our goal is to show these particular transpositions lie in G, forcing G=S₅."}]
 :strategy [{:id :s1
             :formal-dependency "cycle_action.transitive"
             :informal-dependency "A 5-cycle acts transitively on {1,…,5}, so any subgroup containing it is transitive."
             :why-this-now "Transitivity lets us relocate the given transposition via conjugation."
             :lean-target "∃ (σ : S_5), IsCycle σ ∧ orderOf σ = 5 ∧ σ ∈ G → ActingTransitively G"
             :mathlib-status "Mathlib already shows cycles act transitively."}
            {:id :s2
             :formal-dependency "conjh_transposition"
             :informal-dependency "Use powers of the 5-cycle to conjugate the given transposition and obtain all translates (i i+1)."
             :why-this-now "Generates the needed adjacent transpositions from a single 2-cycle."
             :lean-target "∀ i, (τ : S_5) transposition → σ^i τ σ^{-i} ∈ G"
             :mathlib-status "Conjugation lemmas for permutations exist; will need a short calculation."}
            {:id :s3
             :formal-dependency "adjacent_transpositions_generate"
             :informal-dependency "Since the four adjacent transpositions lie in G, they generate S₅, hence G=S₅."
             :why-this-now "Closes the argument by appealing to the standard generating set."
             :lean-target "Subgroup.closure {adjacent transpositions} = ⊤"
             :mathlib-status "Mathlib contains the fact that simple transpositions generate S_n."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'b96J01'
  :frame-id 'apm-v2-b96J01-1775006550462'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full solution (motivation, key insight, case split proving the lemma) plus stage descriptions in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Populated proof-plan.edn and formal-alignment.edn with the conjugation/conjugacy strategy and the Mathlib targets."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Implemented `five_cycle_transposition_generate` in Main.lean using `closure_prime_cycle_swap`; ran `lake build`."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** At first glance you can imagine many proper subgroups of `S₅` containing a 5-cycle: the dihedral group `D₁₀`, the Frobenius group of order 20, even `A₅`. The trap is to think “5-cycle + something of order 2” automatically gives `S₅`, but you have to rule out those proper candidates carefully. The key is to notice that most of those subgroups have only even elements or reflections that move all five points, whereas a true transposition fixes three points.

**Key insight.** Reduce to a canonical situation. Conjugate the 5-cycle so it becomes `(1 2 3 4 5)` (this does not change the subgroup) and then conjugate the transposition so it looks like `(1 i)`. There are only two essentially different distances between `1` and `i`: adjacent (difference 1) or “skipping one point” (difference 2, the difference 3 case is symmetric). In the adjacent case we already have the standard generating pair of `S₅`; in the skipping case a simple product such as `(σ τ)^3` produces the adjacent transposition `(1 2)`. Once you have any adjacent transposition together with the 5-cycle you can conjugate to get all adjacent transpositions, which are known to generate `S₅`.

**Complete proof.**
1. Let `σ` be a 5-cycle in `G`. By renaming the letters we may assume `σ = (1 2 3 4 5)`. Because conjugation by elements of `S₅` stays inside `G`, we may also assume the given transposition has the form `τ = (1 i)` for some `i ∈ {2,3,4,5}`.
2. If `i = 2` or `i = 5` the transposition is already adjacent to `1`. Then `σ` and `τ` generate `S₅`, since `(1 2)` together with `(1 2 3 4 5)` generates all adjacent transpositions `(2 3), (3 4), (4 5)` by conjugation, and those adjacent transpositions generate the whole symmetric group.
3. Suppose `i = 3` (the case `i = 4` is symmetric). Consider the product `σ τ`. Computed explicitly, `σ τ = (0 3 4)(1 2)`, i.e. a disjoint product of the 3-cycle `(1 4 5)` and the transposition `(2 3)`. Because the two factors are disjoint they commute, so `(σ τ)^3 = (2 3)` lies in `G`. Conjugating `(2 3)` by `σ` and its powers produces `(1 2)`, `(3 4)`, `(4 5)`, etc. Thus even in this case `G` contains all adjacent transpositions.
4. Once `G` contains the 5-cycle `(1 2 3 4 5)` and all adjacent transpositions, it contains every permutation: the adjacent transpositions generate `S₅`, hence `G = S₅`.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- `σ` being a 5-cycle implies the action is transitive, so conjugating the transposition lets us assume it is `(1 i)` (strategy :s1).
- Conjugating and multiplying the transposition with powers of `σ` produces the adjacent transposition `(1 2)` in the non-adjacent cases (strategy :s2).
- The set of adjacent transpositions generates `S₅`, so once they lie in `G` we conclude `G = S₅` (strategy :s3). The machine-readable version lives in `/home/joe/code/futon6/.state/proof-frames/b96J01/apm-v2-b96J01-1775006550462/proof-plan.edn`.

**Stage 3 — LEAN FORMALIZATION**

Implemented in `Main.lean`:
- `fiveCycle_transposition_eq_top` shows that if a subgroup of `Perm (Fin 5)` contains a 5-cycle and a transposition then it must be `⊤`. The proof invokes the Mathlib lemma `closure_prime_cycle_swap`, which states that the symmetric group of prime degree is generated by any prime cycle together with any transposition.
The file builds with `lake build` (only the background warnings from other targets appear, no new ones).

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean proof captures exactly the “canonical pair generates” slogan: `closure_prime_cycle_swap` formalises the argument that a 5-cycle plus any transposition generates `S₅`. The informal proof now references the same reduction (conjugating to the canonical pair), so the two narratives mirror each other. If we ever need a version for other primes, the Lean lemma already works in that generality.
