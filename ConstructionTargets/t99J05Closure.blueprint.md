# t99J05 closure blueprint

Source: `holes/labs/blueprints/t99J05/BLUEPRINT.md` (reviewed plan). The
registered statement and definitions are frozen in
`problems/t99J05/lean/Main.lean`; the compiled reference assembly is
`holes/labs/blueprints/t99J05/Blueprint.lean`.

## Triage and representation

The theorem is true and faithful, including `n = 0`. It uses the literal
quotient model `CP n`, its actual affine charts, rational singular homology,
and the diagonal weights `i+1`. For `n = 2` these are the printed weights
`1,2,3`. No registered statement or definition may change.

Copy `T99J05Diagonal`, its comparison with `t99J05Diagonal`, the proved
homotopy descent, and `T99J05_affineChartConstruction` verbatim from the
reference. The only final quantified input is `n`; it determines the projective
space, diagonal map, coordinate lines, chart dimensions, homology range, and
the value `n+1`, so the final-hypothesis coverage gate is nonvacuous.

## Milestones

### C1. `t99J05_map_fixedPoints` — already proved

Copy the reference proof. At time one of the descended positive-weight
homotopy, define `f`. The endpoint equations give both the quotient formula
and `f ~ id`. Projective equality supplies a nonzero scalar. If two coordinates
of a representative are nonzero, their distinct natural weights must agree,
a contradiction; hence fixed points are exactly the coordinate lines.

Truth checks: a one-coordinate vector is fixed; a vector supported at two
indices is not. At `n = 0` there is exactly one coordinate line.

### C2. `t99J05_localIndices_one` — already proved

Copy the reference proof and its private affine-coordinate helpers. Given the
quotient formula from C1, the local map at coordinate line `i` is diagonal:

```text
z_j ↦ ((j+1)/(i+1)) z_j,  j ≠ i.
```

It is real `C¹`. The real determinant of `I-Df` is the product of
`|1-(j+1)/(i+1)|²`, hence is positive and nonzero because `j ≠ i`; therefore
the local index is `1`. The empty product handles `n = 0`.

### C3. `t99J05_cp_homology` — LIBRARY milestone

Construct the rational singular homology computation needed by the concrete
predicates in `ConstructionTargets.RationalLefschetz`:

```text
H_k(CP n; ℚ) ≃ ℚ  when k is even and k ≤ 2n,
H_k(CP n; ℚ) = 0  otherwise,
```

including finite-dimensionality and vanishing above `2n`. Use the standard
filtration `CP 0 ⊂ ... ⊂ CP n`, one even-dimensional cell at each stage, and
the coefficient Mayer–Vietoris infrastructure. The required missing bridge is
the arbitrary-coefficient range-to-literal-production comparison with
Mayer–Vietoris naturality. The analogous integral production result does not
supply a `ModuleCat ℚ` statement and must not be substituted.

The compiled structure
`ConstructionTargets.t99J05Closure.ComplexProjectiveRationalHomologyData`
fixes C3's output interface: finite dimensionality in every degree,
subsingleton homology above `2n` and in odd degrees, and a linear equivalence
with `ℚ` at each degree `2*i`, `i : Fin (n+1)`. Its accessor lemmas are the
first banked milestone. The remaining C3 work constructs this structure from
the filtration and Mayer–Vietoris bridge.

Dependencies already banked:

- `ConstructionTargets.CoefficientSubcomplexMayerVietoris`
- `ConstructionTargets.CoefficientSubspaceUnionRangeHomologyEquivalence`
- `ConstructionTargets.RationalLefschetz`

This is the large part of the program. Implement it in
`ConstructionTargets/t99J05Closure.lean` in reviewed, compiled submilestones;
do not add axioms or placeholders.

### C4. `t99J05_lefschetz_euler` — LIBRARY final milestone

For `f : C(CP n, CP n)` and `hf : f.Homotopic (ContinuousMap.id _)`, prove
both `HasLefschetzNumber f ((n : ℚ)+1)` and
`HasEulerCharacteristic (CP n) ((n : ℚ)+1)`.

Use C3 and homotopy invariance to identify the induced maps of `f` with the
identity. Each surviving even-degree group is one-dimensional, so its identity
trace is `1`; odd groups vanish, all surviving signs are positive, and the
finite sum over degrees `0,2,...,2n` is `n+1`. The Euler statement is the same
calculation for the identity. This milestone consumes the homotopy hypothesis
essentially and does not depend on the fixed-point or local-index proofs.

Truth checks: the values are `1` for `CP⁰`, `2` for `CP¹`, and `3` for `CP²`.

### C5. Main theorem assembly — already proved

Copy the reference assembly after C1–C4 are available. It returns the affine
charts, obtains `f` and its formula/homotopy/fixed-point description from C1,
passes the formula to C2 and the homotopy to C4, and uses
`localIndex f i = 1` plus `Fintype.card (Fin (n+1)) = n+1` to rewrite both
global values as the registered sum of local indices. No conclusion is packed
into a hypothesis.

## Dependency layers

- Layer 1: C1 and C2 are copied compiled proofs; C3 builds rational homology.
- Layer 2: C4 consumes C3 and the honest homotopy hypothesis.
- Layer 3: C5 is compiled modulo C1, C2, and C4.

The ledger-facing LIBRARY obligation remains
`t99J05_lefschetz_euler`; C3 is its explicit internal dependency and must be
reported as partial until its final interface compiles.

## Gates

Compile the reference with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t99J05/Blueprint.lean
```

Its sole `sorryAx` use is C4 (`t99J05_lefschetz_euler`); C1, C2, and the final
assembly already compile without placeholders. Final closure must compile
`problems/t99J05/lean/Main.lean`, pass the statement registry, contain no
placeholders or new axioms, and use only standard axioms.
