# t02A06 singular-homology declaration reachability

Measured at commit `f1516336291d03efd93b2025dc393a43b510223a` on branch
`infra/SingularHomologyConcrete`. The target is the closing theorem
`apm_t02a06` in `problems/t02A06/lean/Main.lean`.

## Re-run

Run this exact command from the repository root:

```text
./scripts/t02A06-declaration-reachability.sh
```

The verbatim output, including every reachable declaration and every orphan,
is committed as `Reports/t02A06-declaration-reachability.txt`.

The tool adapts importGraph's explicit work-set traversal over
`ConstantInfo.getUsedConstantsAsSet`. It retains declaration names rather than
aggregating the closure to modules, restricts the result to non-blacklisted
declarations with declaration ranges in the three requested modules, and
prints the complement per module.

## Results

| Module | Lean declarations | Reachable | Raw orphans | Anti-vacuity terminals | Headline orphans |
|---|---:|---:|---:|---:|---:|
| `ConstructionTargets.SingularHomologyConcrete` | 131 | 66 | 65 | 9 | 56 |
| `ConstructionTargets.SingularSubdivision` | 234 | 188 | 46 | 0 | 46 |
| `ConstructionTargets.SingularExcision` | 117 | 82 | 35 | 0 | 35 |
| **Total** | **482** | **336** | **146** | **9** | **137** |

The nine deliberately terminal anti-vacuity results, excluded from the headline
orphan count, are:

- `ConstructionTargets.SingularHomologyConcrete.falsePairRelativeTrueClass_ne_zero`
- `ConstructionTargets.SingularHomologyConcrete.pointH0Generator_ne_zero`
- `ConstructionTargets.SingularHomologyConcrete.selfPairPointLES_generator_evaluates_to_one`
- `ConstructionTargets.SingularHomologyConcrete.intervalH0Generator_ne_zero`
- `ConstructionTargets.SingularHomologyConcrete.intervalBoundaryRelativeH1Generator_ne_zero`
- `ConstructionTargets.SingularHomologyConcrete.circleCellularModelH1Generator_ne_zero`
- `ConstructionTargets.SingularHomologyConcrete.circleCellularOneChain_ne_zero`
- `ConstructionTargets.SingularHomologyConcrete.circleCellularGenerator_ne_zero`
- `ConstructionTargets.SingularHomologyConcrete.circleCellularH1_nontrivial`

## Calibration against textual reference counts

The closure-based headline differs sharply from the textual proxy:

| Module | Textual proxy | Closure headline | Difference |
|---|---:|---:|---:|
| SingularHomologyConcrete | 23 | 56 | +33 |
| SingularSubdivision | 7 | 46 | +39 |
| SingularExcision | 6 | 35 | +29 |
| **Total** | **36** | **137** | **+101** |

The proxy asks whether a name occurs elsewhere anywhere in the repository. A
declaration can therefore look used because a sibling theorem or terminal
experimental branch names it, while neither that sibling nor its branch lies
on the dependency path to `apm_t02a06`. The closure measurement asks the
stricter question: whether Lean's compiled constant graph reaches the
declaration from the closing theorem. The denominators also differ because the
Lean environment includes named generated declarations such as reassociation
lemmas when they have real declaration ranges; the calibration's textual
declaration extractor counted source forms instead.

## Baseline gates

The three-module `lake build` exited 0. It reported one unused-section-variable
warning in `SingularHomologyConcrete` and two linter warnings in
`SingularSubdivision` (one no-op `change` and one `simpa` suggestion). The
complete verbatim build output was captured during the measurement run.

Warnings, verbatim:

```text
warning: ConstructionTargets/SingularHomologyConcrete.lean:127:0: automatically included section variable(s) unused in theorem `ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso_pointInclusion`:
  [HasZeroObject C]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [HasZeroObject C] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: ConstructionTargets/SingularSubdivision.lean:2816:2: 'change
  ((continuousMapOfSingularSimplex n
        ((TopCat.toSSet.map (coverSubspaceInclusion U a)).app (Opposite.op (SimplexCategory.mk n)) t))
      x) ∈
    U a' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
warning: ConstructionTargets/SingularSubdivision.lean:3436:2: Try `simp at hj` instead of `simpa using hj`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
```

`lake env lean problems/t02A06/lean/Main.lean` exited 0 with no sorry warnings.
Its warnings were linter suggestions only.

Required axiom output, verbatim:

```text
'ConstructionTargets.SingularExcision.relativeExcision' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConstructionTargets.SingularSubdivision.coverSmall_homologyMap_isIso_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ConstructionTargets.SingularHomologyConcrete.singularHomology_map_eq_of_topCatHomotopy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

No `sorryAx` occurs.
