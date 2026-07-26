# Proof Outline: a95J06

## Problem

C = Cantor set, f : [0,1] → [0,1] homeomorphism fixing C, AC on [0,1]\C.
Prove f is AC on [0,1].

## Proved lemma

- `conditionN_on_cantor_of_fix`: f = id on C ⟹ f maps null subsets of C to null sets.
  Key: f '' E = E when f = id on C ⊇ E.

## Theory boundaries (4 sorries)

1. `cantorSet_measure_zero`: Mathlib defines cantorSet but doesn't prove m(C) = 0.
2. `monotone_of_homeomorphism`: continuous bijection on interval ⟹ monotone.
3. `ac_of_bv_continuous_conditionN`: Banach-Zarecki theorem (BV + N ⟹ AC). NOT in Mathlib.
4. `ac_on_01_of_homeo_fixing_cantor`: main theorem (inherits from above).

## Checked Lean state

- `lake env lean problems/a95J06/lean/Main.lean`: exit 0
- Sorry count: 4
- Classification: partial
