# Proof Outline: b90A01

The canonical Lean attempt is `lean/Main.lean`. Closer hop 1 proves
`apm_b90A01_perm_fin_of_card`, transporting any faithful permutation action on
a finite type of cardinality `k` to the exact frozen target `Perm (Fin k)`.

Closer hop 2 proves `apm_b90A01_sylow_action_faithful`. The kernel of the
Sylow conjugation action is normal, hence bottom or top by simplicity. If it
were top, every group element would fix every Sylow subgroup; pretransitivity
would then identify two distinct Sylow subgroups supplied by the cardinality
hypothesis. The wrapper `apm_b90A01_exists_faithful_sylow_perm` combines this
with hop 1's transport, and the main theorem now discharges its entire first
conjunct before the remaining boundary.

Closer hop 3 proves that multiple Sylow subgroups force `G` to be
noncommutative, since all subgroups of a commutative group are normal and the
Sylow conjugation action is pretransitive. It then factors the faithful action
through `alternatingGroup (Fin k)`: simplicity makes the sign kernel bottom or
top; a bottom kernel would inject `G` into the commutative group `ℤˣ`, while
top gives the required codomain restriction. Thus both permutation-
representation conjuncts are fully compiled.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b90A01.md`

## Remaining boundary

- locally develop simplicity of `alternatingGroup (Fin n)` for every `n ≥ 5`,
  since this checkout only packages the `n = 5` case;
- formalize the exact Sylow-5 count excluding simple groups of order 120.
