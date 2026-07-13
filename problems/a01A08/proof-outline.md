# Proof Outline: a01A08

## Problem

Let `p(z)` be a polynomial of degree `N ≥ 1` and define `L = {z ∈ ℂ | |p(z)| = 1}`.
Prove that the open set `ℂ \ L` has at most `N + 1` components.

## Statement repair

The informal proof file `apm-a01A08.md` was harvested with the **wrong content**:
it contains the proof for a01A07 (L¹ convergence of analytic functions), not
a01A08 (polynomial lemniscate). The actual problem from `a01A08.tex` is identical
to `a00J04.tex` — the TeX solution says "This is exactly the same as a00J04."

This file adapts the a00J04 formalization. The analytic core is fully proved;
only the topological assembly (Step 5) carries a sorry.

## Proof sketch

1. **Each component is purely sublevel or superlevel** (Step 1, PROVED).
   Connected set avoiding `{|p|=1}` → `|p|` image avoids `1` → entirely above or below.

2. **No bounded superlevel components** (Step 2, PROVED).
   Bounded open with `|p|>1` inside, `|p|=1` on frontier → contradicts maximum modulus.

3. **Each sublevel component contains a root** (Step 3, PROVED).
   Bounded open with `|p|<1` inside, `|p|=1` on frontier → `1/p` contradicts maximum modulus.

4. **Root count ≤ degree** (Step 4, PROVED).
   Standard Mathlib result: `Polynomial.card_roots'`.

5. **Final assembly** (Step 5, SORRY).
   Combining the above into a bound on `ConnectedComponents` requires connected-component
   topology not available in Mathlib at the needed generality.

## Lean formalization status

**Classification: partial** (1 sorry, 0 errors)

Steps 1-4 are fully proved with zero sorries. The single sorry is at the
topological assembly boundary (Step 5) — the same boundary as a00J04.

### Proved lemmas (zero sorry)

- `isPreconnected_subset_superlevel_or_sublevel` — Step 1
- `not_bounded_isOpen_superlevel_frontier_lemniscate` — Step 2
- `exists_root_in_bounded_isOpen_sublevel_frontier_lemniscate` — Step 3
- `card_roots_le_degree` — Step 4

### Sorry (1)

- `connectedComponents_complement_lemniscate_le` — Step 5: topological assembly
  (classify components, prove superlevel connected, inject sublevel components
  into roots). Same boundary as a00J04.

## Files

- Lean attempt: `lean/Main.lean`
