# Proof Outline: a00J04

## Problem

Let `p(z)` be a polynomial of degree `N ≥ 1` and let `L = {z ∈ ℂ | |p(z)| = 1}`.
Prove that the open set `ℂ \ L` has at most `N + 1` connected components.

## Formalization Strategy

The proof decomposes into four sub-results plus a final topological assembly.

### Proved sub-lemmas (Steps 1–4, no sorries)

1. **`isPreconnected_subset_superlevel_or_sublevel`** (Step 1):
   A preconnected set disjoint from the lemniscate lies entirely in the
   superlevel or the sublevel. Uses `IsPreconnected.mapsTo_Ioi_or_Iio`
   applied to the continuous map `z ↦ ‖aeval z p‖`.

2. **`not_bounded_isOpen_superlevel_frontier_lemniscate`** (Step 2):
   A bounded open set in the superlevel whose frontier lies in the lemniscate
   cannot exist. Uses Mathlib's `Complex.norm_le_of_forall_mem_frontier_norm_le`
   (maximum modulus principle) to get `‖p‖ ≤ 1` on the closure, contradicting
   `‖p‖ > 1` on the set.

3. **`exists_root_in_bounded_isOpen_sublevel_frontier_lemniscate`** (Step 3):
   A bounded open set in the sublevel whose frontier lies in the lemniscate
   must contain a root of `p`. Proof by contradiction: if `p ≠ 0` on `U`,
   then `1/p` is holomorphic on `closure U`, `‖1/p‖ = 1` on the frontier,
   and the maximum modulus principle gives `‖1/p‖ ≤ 1` on `U`, contradicting
   `‖1/p‖ > 1` there.

4. **`card_roots_le_degree`** (Step 4):
   The number of distinct roots of `p` is at most its degree.
   Uses `Polynomial.card_roots'` and `Multiset.toFinset_card_le`.

### Boundary (Step 5, 1 sorry)

5. **`connectedComponents_complement_lemniscate_le`** (main theorem):
   The final topological assembly is left as a sorry. It requires:
   - (a) Classifying connected components of `(lemniscate p)ᶜ` as sublevel
     or superlevel via Step 1, with frontier-inclusion hypotheses.
   - (b) Proving the superlevel is connected (using `|p(z)| → ∞`).
   - (c) Building an injection from sublevel components to roots of `p`
     via Step 3.
   These require connected-component topology for open subsets of `ℂ`
   not available at the needed generality in Mathlib.

## Statement Repair Note

The informal-solution-proposed statement used
`Nat.card (ConnectedComponents (lemniscate p)ᶜ)`. The correct target type is
`ConnectedComponents ↥((lemniscate p)ᶜ)` — the connected components of the
subtype with the subspace topology. Writing `(lemniscate p)ᶜ` directly in
that position is a set-complement (a `Set ℂ`), not a type, and does not
elaborate as a `Type*` for `ConnectedComponents`. The repair passes the
subtype `↥((lemniscate p)ᶜ)`.

## Lean State

- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 1 (on the main theorem; all helper lemmas are sorry-free)
- **Classification**: partial
