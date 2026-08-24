# Concrete integral singular homology of the circle

Status: production, axiom-clean, and imported by `ConstructionTargets.lean`.

This seam identifies Mathlib's `Circle` (the unit sphere in `ℂ`) with the
Euclidean unit one-sphere through the orthonormal real basis `(1, i)`. Applying
integral singular homology to that homeomorphism and composing with the
production sphere computation gives the reusable comparison

```text
H₁(Circle; ℤ) ≅ ℤ.
```

The class `circleSingularH1Generator` is defined as the inverse image of `1`.
Its normalization, nonvanishing, and the resulting `Nontrivial` instance are
proved rather than assumed. This is a genuine singular-homology comparison;
it does not use the separate cellular model as a substitute.

The independent consumer is `problems/t01A03/lean/Main.lean`, whose frozen
theorem uses the instance to close the zero-map obstruction for the separating
circle.

Validation:

```sh
lake env lean ConstructionTargets/CircleSingularHomology.lean
lake env lean problems/t01A03/lean/Main.lean
lake build ConstructionTargets
```

The production axiom audit is the exact declarations listed in
`problems/t01A03/targets.edn`; none may contain `sorryAx`.
