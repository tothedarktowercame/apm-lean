# t98J03 keyed library increment

## Outcome

`apm_t98j03` closes through two reusable construction-target modules:

- `ConstructionTargets.IntegralSingularHomologyComparison` compares integral
  singular chains and homology across `ModuleCat ℤ` and `AddCommGrpCat`.
- `ConstructionTargets.SphereHomology` packages the existing production
  excision/subdivision sphere shift into the complete integral homology
  computation for every positive-dimensional Euclidean unit sphere.

The problem's zero-sphere branch normalizes the free module on its two
concrete points to `ℤ × ℤ`.

## Exact re-run commands

```bash
lake build ConstructionTargets.IntegralSingularHomologyComparison ConstructionTargets.SphereHomology
lake env lean problems/t98J03/lean/Main.lean
lake env lean Reports/t98J03Axioms.lean
scripts/t98J03-declaration-reachability.sh
```

All four commands exited `0`. The problem compilation emitted one pre-existing
style-linter warning at line 82 and zero `sorry` warnings. The frozen theorem
statement was compared programmatically with `edaaafe` and was byte-identical.

## Axioms (verbatim)

```text
'apm_t98j03' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Reachability summary

| Module | Total | Reachable | Orphans |
|---|---:|---:|---:|
| `ConstructionTargets.IntegralSingularHomologyComparison` | 8 | 8 | 0 |
| `ConstructionTargets.SphereHomology` | 20 | 20 | 0 |
| `ConstructionTargets.SingularHomologyConcrete` | 131 | 66 | 65 |
| `ConstructionTargets.SingularSubdivision` | 234 | 188 | 46 |
| `ConstructionTargets.SingularExcision` | 117 | 82 | 35 |

The exact reachable and orphan declaration names are recorded in
`Reports/t98J03-declaration-reachability.md`. Both modules added by this
increment have an empty orphan list. The nonempty lists belong to the measured
pre-existing modules and are not declarations added by this episode.
