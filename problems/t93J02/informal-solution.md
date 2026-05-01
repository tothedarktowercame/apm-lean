# Informal Solution: t93J02

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

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
