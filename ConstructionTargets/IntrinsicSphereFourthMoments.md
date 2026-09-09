# Intrinsic fourth moments relative to sphere mass

This module computes fourth moments on the literal unit two-sphere and
assembles the exact flux polynomial integral in terms of its total intrinsic
Hausdorff mass. Write `M_d = IntrinsicSphereSecondMoments.mass d`; this is
the real value of `hausdorffMeasure d univ` on `Sphere d`.

`rotate` is the explicit ambient map

```text
(x₀,x₁,x₂) ↦ ((x₀+x₁)/sqrt(2), (x₁-x₀)/sqrt(2), x₂).
```

`unrotate` uses `(x₀-x₁)/sqrt(2)` and `(x₁+x₀)/sqrt(2)` in the first
two coordinates. Both inverse identities, linearity, and norm preservation
are proved, yielding `rotation : E ≃ₗᵢ[ℝ] E`. Its actual sphere restriction
uses the banked `sphereIsometry` and Hausdorff integral transport.

Applying transport to `x₀⁴` gives `quartic_rotation_identity`, namely
`∫ (x₀+x₁)⁴ = 4 ∫ x₀⁴`. Polynomial expansion is justified by the
previously proved intrinsic integrability. Coordinate reflections cancel
the odd terms, and coordinate permutations equate the pure fourth moments.
Thus `fourth_eq_three_mixed` proves `∫ x₀⁴ = 3 ∫ x₀² x₁²`.

Multiplying the pointwise norm-one identity by `x₀²` and integrating gives
the second independent relation. Together with the imported second moment
`∫ x₀² = M₂/3`, this proves

```text
∫ xᵢ⁴ = M₂/5,       ∫ x₀² x₁² = M₂/15.
```

The module then expands the shifted cube and linear terms. Reflection
cancels odd powers, and all integral additions have explicit integrability
proofs. `unitFlux_moment` concludes

```text
∫ unitFlux c = M₂ * (11/15 + (c₀-1)² + (c₁-2)²).
```

The imported `IntrinsicSphereSecondMoments` results also give `∫ x₀² = M₃/4`
on the three-sphere and the projective pullback density integral `-M₃`.
The exact consumer audit checks all three formulas against the original
diagnostic definitions, including `T02A05Diagnostic.unitFlux` and
`t95J05InclusionPullback`.

No numerical sphere area, positive total mass, radial-measure identification,
or moment value is assumed. Numerical identification of `M₂` and `M₃`
remains downstream. This packet neither retries the stopped Hausdorff-cone
comparison nor closes either frozen integration consumer.

The canonical source is an unchanged promotion of
`/tmp/IntrinsicSphereFourthMomentsProbe.lean`, SHA-256
`c68fa1712227f928beb112983370d586814a5063e00f755309c51a3e463468ac`.
The separate consumer audit is `/tmp/IntrinsicFourthMomentConsumerAudit.lean`,
SHA-256 `d55b35a914d0e8b938861ea157cda591f149e5e4e3101652d153260d17c62c31`.
The second-moment dependency was independently reviewed PASS at
`99b196c3b27f65b150b595325a0fe3e9df4b5b37`.
Validation compiles both primary sources and the consumer audit, builds this
module with `IntrinsicSphereSecondMoments` and `IntrinsicSphereFinite`, and
checks all nine printed axiom audits. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. The consumer audit has three inherited
`unnecessarySimpa` warnings in diagnostic proofs.
