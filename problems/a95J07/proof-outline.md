# Proof Outline: a95J07

## Problem

(a) Vitali covering lemma: extract disjoint I₁, I₂, ... from A ⊂ open intervals
of (0,1) with ∪A ⊆ ∪Iₙ' (where I' is the 5× inflation of I).
(b) f(D) has measure zero where D = {x ∈ (0,1) : f'(x) = 0}.

## Proved lemmas

- `inflate5_center`: I = (α,β) and I' = (3α-2β, 3β-2α) have same center.
- `inflate5_length`: |I'| = 5|I|.

## Theory boundaries (3 sorries)

1. `tsum_volume_disjoint_le_one`: disjoint intervals in (0,1) have total measure ≤ 1.
   Needs `measure_iUnion` with measurable sets.
2. `vitali_covering_5` (part a): Vitali covering lemma with 5× factor.
   Mathlib has abstract VitaliFamily but not the 1D interval 5× formulation.
3. `measure_image_criticalSet_eq_zero` (part b): 1D Sard theorem. NOT in Mathlib.

## Checked Lean state

- `lake env lean problems/a95J07/lean/Main.lean`: exit 0
- Sorry count: 3
- Classification: partial
