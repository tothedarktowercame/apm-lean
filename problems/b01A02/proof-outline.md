# Proof Outline: b01A02

The canonical Lean attempt is `lean/Main.lean`. It fully proves the first main
conjunct:

- `apmSmallestPrimeDivisor_eq_minFac` identifies the frozen predicate with
  Mathlib's smallest-prime-factor operation;
- `apm_b01A02_normal_of_smallest_prime_index` applies
  `Subgroup.normal_of_index_eq_minFac_card` to obtain normality.
- `apm_b01A02_sylow17_normal_of_card_255` proves that the number of Sylow-17
  subgroups divides 15 and is congruent to one modulo 17.  Hence it is one,
  giving the frozen normal subgroup of order 17.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b01A02.md`

## Remaining boundary

- combine it with a Sylow-5 subgroup to construct an order-85 subgroup;
- apply the now-closed index-three normality result;
- prove the order-85 subgroup cyclic and show the final order-three conjugation
  action on it is trivial, yielding cyclicity of the full group.

The original source comment claiming Sylow theory was absent is stale in the
current Mathlib checkout.

`IsZGroup.of_squarefree` and `isZGroup_iff_exists_mulEquiv` were also checked.
They supply cyclic Sylow subgroups and an abstract semidirect-product
classification, but do not directly construct the frozen order-85 witness or
prove the two relevant actions trivial.
