# Proof Outline: b90A01

The canonical Lean attempt is `lean/Main.lean`. Closer hop 1 proves
`apm_b90A01_perm_fin_of_card`, transporting any faithful permutation action on
a finite type of cardinality `k` to the exact frozen target `Perm (Fin k)`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b90A01.md`

## Remaining boundary

- prove the conjugation action on `Sylow p G` has non-top kernel using
  pretransitivity and `1 < k`, then simplicity makes the kernel bottom;
- prove the resulting faithful permutation action has even image and factor it
  through `alternatingGroup (Fin k)`;
- locally develop simplicity of `alternatingGroup (Fin n)` for every `n ≥ 5`,
  since this checkout only packages the `n = 5` case;
- formalize the exact Sylow-5 count excluding simple groups of order 120.
