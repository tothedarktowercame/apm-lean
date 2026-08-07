# Proof Outline: b01A02

The canonical Lean attempt is `lean/Main.lean`. Closer hop 1 fully proves the
first main conjunct:

- `apmSmallestPrimeDivisor_eq_minFac` identifies the frozen predicate with
  Mathlib's smallest-prime-factor operation;
- `apm_b01A02_normal_of_smallest_prime_index` applies
  `Subgroup.normal_of_index_eq_minFac_card` to obtain normality.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b01A02.md`

## Remaining boundary

- use Sylow cardinality divisibility and congruence to make the Sylow-17
  subgroup unique and normal;
- combine it with a Sylow-5 subgroup to construct an order-85 subgroup;
- apply the now-closed index-three normality result;
- prove the order-85 subgroup cyclic and show the final order-three conjugation
  action on it is trivial, yielding cyclicity of the full group.

The original source comment claiming Sylow theory was absent is stale in the
current Mathlib checkout.
