# Borel overlap nullity including degenerate dimensions

Provides `localSet_criticalImage_zero_of_borel_overlap_all_dimensions`.

The theorem removes source and target nontriviality assumptions from localized overlap nullity. It retains finite-dimensional real inner-product Borel source and target spaces, a proper source, an add-Haar target measure, pointwise ambient C^(k+2) regularity on an arbitrary set s, classical order admissibility, Borel-compatible critical-nullity induction below the source dimension, and

`dim E + (dim E - 1) / dim F ≤ dim F + (k + 2) + 1`.

Subtraction and division here are natural-number operations, including Lean's division-by-zero convention. The conclusion is zero target measure of the image of the nonsurjective ambient derivative locus in s. The name `all_dimensions` means that nontriviality is no longer required; it does not remove the displayed overlap bound.

## Proof and observed dependencies

The direct import is `SardBorelLocalSetCriticalImageJetRangeOverlap`. If the target is subsingleton, every derivative is surjective since the source contains zero, so the critical set is empty. Otherwise, if the source is subsingleton, its finrank is zero and the transitively imported `criticalImage_zero_of_source_finrank_zero_borel` proves nullity. When both spaces are nontrivial, `localSet_criticalImage_zero_of_borel_jet_range_overlap_induction` applies. These are the two reviewed theorem dependencies.

## Boundary and intended consumers

No downstream uptake or full rectangular closure is claimed. Intended consumers are t93A04, t01A08, t01J04, t92J07, and t96J05. Borel-compatible dimension induction closure, the complementary analytic range, remaining regularity cases, and the remaining space-representation bridge are still obligations. The theorem does not imply the older arbitrary-measurable-target predicate. The frozen t93A04 statement and placeholder remain unchanged.

Stop only if subsingleton targets admit nonsurjective derivatives, the reviewed zero-source or nontrivial-space theorems fail under these hypotheses, or nonstandard axioms are required.

## Provenance

The source is byte-identical to `/tmp/SardBorelOverlapDegenerateDimensionsProbe.lean`, SHA-256 `327c398fae0ae4a785008900f45785144d86e7a8c4eaf9f56eedb7c1def0b784`. Statement lines 7–23 hash to `0d9c6c1d9dfa7e1c20e78d78570065253c954655fbf609b5c1b6cc54d0daaf1b`. The fixture compiles without warnings using only `propext`, `Classical.choice`, and `Quot.sound`.
