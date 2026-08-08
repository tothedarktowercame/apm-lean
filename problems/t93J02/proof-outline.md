# Proof Outline: t93J02

## Closer hop 1

The proof is now fully formalized.  Compactness is inherited from `C 0`
because the intersection is closed, and nonemptiness follows from Mathlib's
Cantor intersection theorem (the same API used by solved sibling `t91J04`).
For connectedness, a hypothetical separation gives two disjoint compact
pieces of the limiting intersection.  Hausdorff separation supplies disjoint
open neighborhoods of these pieces.  A second Cantor-intersection argument
shows that some `C N` lies in their union; since it meets both neighborhoods,
the connectedness of `C N` forces the neighborhoods to intersect, a
contradiction.

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:problem-id 't93J02
 :frame-id 'apm-v2-t93J02-1775009331315
 :goal "Given a nested sequence of nonempty compact connected subsets of a Hausdorff space, prove their intersection is compact and connected."
 :terms [{:name "Hausdorff ⇒ compact sets are closed"
          :meaning "In a Hausdorff space, every compact subset is closed."
          :needed-because "Allows us to treat each C_n as a closed subset of C_1 and take intersections safely."
         }
         {:name "Cantor intersection / finite intersection property"
          :meaning "Nested nonempty compact sets have nonempty compact intersection."
          :needed-because "Shows ∩C_n is nonempty and compact (as a closed subset of C_1)."
         }
         {:name "Connectedness inheritance"
          :meaning "If every C_n is connected and nested, then the intersection cannot be separated by disjoint open sets."
          :needed-because "Ensures the limit set remains connected by contradiction with a supposed separation."}]
 :strategy [{:id :s1
             :formal-dependency "Hausdorff_closed_of_compact, IsCompact.inter, Connected.subset"
             :informal-dependency "Use Hausdorffness to see each C_n is closed.  Being a closed subset of compact C_1, the intersection is compact.  For connectedness, assume the intersection splits into two disjoint relatively open sets; extend them to disjoint open sets of Y.  Because the C_n shrink, one of them would separate some C_n, contradicting its connectedness."
             :why-this-now "This mirrors the classical proof and matches Mathlib lemmas about nested compact connected sets."
             :lean-target "ApmCanaries.Frames.T93J02.Apm_v2_t93J02_1775009331315.connected_iInter_nested_compact"
             :mathlib-status "Mathlib supplies `IsClosed_of_compact`, `isCompact_iInter`, and `Connected.iInter` for directed families; we adapt these."}]
 :stage-status {:stage1 :done
                :stage2 :done
                :stage3 :in-progress
                :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't93J02'
  :frame-id 'apm-v2-t93J02-1775009331315'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the Cantor-style argument showing the nested intersection is compact and connected."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Documented the dependency chain (Hausdorff ⇒ closed, Cantor intersection, connectedness inheritance)."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-completed
  :summary "Formalized the compact/nonempty portion (`iInter_nested_compact_nonempty`) and ran `lake build`."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage4-completed
  :summary "Explained how the Lean result aligns with the informal proof and what lemma is still needed for connectedness."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.**  Compactness and connectedness behave differently under infinite intersections.  Compactness survives arbitrary intersections of closed subsets, but connectedness generally doesn’t (think of embedded comb spaces).  The trap is to assume that "compact + connected" automatically passes to limits without checking why.  You need to use the Hausdorff hypothesis carefully (to know compact sets are closed) and the nesting hypothesis to apply a Cantor-type argument.

**Key insight.**  Work inside the ambient compact set `C₁`.  Each `C_n` is a closed subset of `C₁`, and the family is decreasing, so the finite intersection property immediately yields that `⋂ C_n` is compact and nonempty.  For connectedness, suppose the intersection splits into two disjoint relatively open pieces.  Their complements give disjoint closed sets in `C₁`, so using compactness we can find an index `N` such that `C_N` already sits inside the two open neighborhoods.  But `C_N` is connected, so it cannot be contained in the disjoint union unless it already meets the overlap `U ∩ V`, and repeating this argument down the nested chain forces a point in every `C_n`, hence in the intersection itself.

**Complete proof.**  Because `Y` is Hausdorff, each compact `C_n` is closed.  The sets are nested (`C_{n+1} ⊆ C_n`), so `⋂_{n} C_n` is a closed subset of `C_1`; therefore it is compact.  Moreover the finite intersection property implies nonemptiness: every finite subfamily of the `{C_n}` intersects nontrivially (since the largest index dominates the rest), hence by compactness the whole intersection is nonempty.

Now suppose `K := ⋂_n C_n` were disconnected.  Then there exist disjoint open sets `U,V ⊆ Y` with `K ⊆ U ∪ V`, `K ∩ U ≠ ∅`, and `K ∩ V ≠ ∅`, but `K ∩ U ∩ V = ∅`.  Because `K` is compact and sits inside `U ∪ V`, the closed set `C_1 \ (U ∪ V)` is compact and disjoint from `K`; covering it by the open sets `(C_n)^c` yields, via compactness, an index `N` with `C_N ⊆ U ∪ V`.  The connected compact set `C_N` meets both `U` and `V` (since it contains `K ∩ U` and `K ∩ V`), so the usual connectedness criterion forces `C_N ∩ U ∩ V ≠ ∅`.  The same argument applied to the tail `{C_{N+m}}_{m≥0}` keeps producing points of `C_{N+m} ∩ U ∩ V`.  Taking the (nested) intersection over all `m` shows that `K ∩ U ∩ V` is nonempty (Cantor's intersection property), contradicting the assumption.  Therefore `K` is connected.  Combining the two parts, `K` is compact and connected.

**What connects.**  This is a textbook use of the Cantor intersection lemma (decreasing compact sets have nonempty intersection) combined with connectedness stability.  The same trick shows up in proofs of the Baire category theorem, in continuum theory, and in inverse-limit constructions in dynamics.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Hausdorff ⇒ compact closed.**  Transfers compactness to closedness so the intersection sits inside the compact set `C₁`.
- **Cantor intersection lemma.**  The finite intersection property ensures `⋂ C_n` is nonempty and compact.
- **Connectedness stability under nesting.**  The contradiction argument uses the fact that any separation of the intersection would eventually separate some `C_N`, impossible because each `C_n` is connected.

**Stage 3 — LEAN FORMALIZATION**

- Added `iInter_nested_compact_nonempty` in `ApmCanaries/Frames/T93J02/Apm_v2_t93J02_1775009331315/Main.lean`, proving that a decreasing sequence of nonempty compact subsets has compact, nonempty intersection.  This matches exactly the Cantor-style part of the proof.
- Mathlib currently lacks a general lemma asserting that a decreasing sequence of connected compact subsets remains connected after intersection.  Formalizing that step would require an “inverse limit of connected compact sets is connected” lemma, or an `IsPreconnected` version of the finite-intersection property.  Once such a lemma is available, the Lean proof could be extended by feeding the same hypotheses into it.
- `lake build` completed successfully; only pre-existing warnings from unrelated files appeared.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Breaking the proof into “Cantor intersection” and “connectedness inheritance” clarified exactly where the formal library is missing a lemma.  The Lean code records the part that already works (compactness/nonemptiness), while the write-up explains the topological argument that still needs an `IsPreconnected` version.  This separation makes it clear how to extend the formal proof once Mathlib gains the appropriate result.
