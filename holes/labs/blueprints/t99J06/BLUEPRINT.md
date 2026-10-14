# t99J06 blueprint

## Triage

Verdict: **true and faithful**.  The registered statement is the literal
reading of the source: `coordinateWedge 2 2` is zero by alternation, so the
printed `2yz dz wedge dz` contributes nothing.  The parameter orientation is
`dθ wedge dz`; on the cone parametrization the coefficient of `dx wedge dy` is
`1-z`, positive off the apex.  The loop's reviewed STOP was a scheduling STOP,
not a counterexample: it identified four independent missing packets and no
compiled consumer-specific theorem.

Degenerate checks: at `z=1` the whole circle collapses to the apex, which is why
global injectivity is not claimed.  The open parameter set has `z<1`, so the
angular derivative is nonzero there.  The seam values `θ=0,2π` coincide, but
both are excluded from `interiorParameters`.  At `z=0` the image is the unit
base circle and at `z=1` it is `(0,0,1)`, agreeing with both boundary pieces of
`cone`.

## Definitions

The five registered definitions are copied verbatim.  `parameterDerivative` is
the explicit directional derivative of `parametrization` and is shared by the
immersion and pullback calculations.  `alphaPullbackFormula` is the literal
coefficient of the pulled-back two-form.  Neither definition asserts a desired
conclusion.

## Lemmas

### `extDeriv_alpha`

Statement: `d alpha = (2z+1) dx wedge dy wedge dz`.

Sketch: use `extDeriv_apply`, differentiate the three scalar coefficients, and
evaluate on three arbitrary vectors.  Expand `coordinateWedge` and
`volumeForm` as determinants.  The `coordinateWedge 2 2` summand vanishes by
alternation; the `2x` contributions from the first two nonzero summands cancel.
The nearby sorry-free model is
`ConstructionTargets/ExteriorDerivativeSimplexCalculus.lean`, especially its
`extDeriv_alpha` and `extDeriv_beta` computations.

Estimate: 100–150 lines.  Dependencies: none.

Truth check: hand differentiation gives `(2z+2x)+(1-2x)=2z+1`; the zero wedge
term was also checked at arbitrary vectors by equal determinant columns.

### `image_parametrization_eq_cone`

Statement: the closed parameter rectangle maps onto exactly `cone`.

Sketch: forward inclusion is `sin_sq_add_cos_sq` plus bounds on `z`.  For the
reverse inclusion, split off the apex `z=1`.  Otherwise put `r=1-z>0`, normalize
`(x,y)` to the unit circle, and choose an angle in `[0,2π]` using Mathlib's
circle-angle/`atan2` API (or its unit-circle range theorem).  The cone equation
gives `x²+y²=r²`, hence the normalized point has norm one.

Estimate: 180–280 lines.  Dependencies: none.

Truth check: the cone equation and `0≤z≤1` imply radius `|z-1|=1-z`; the apex,
base circle, and seam were checked separately.

### `injOn_parametrization_interior`

Statement: the parametrization is injective on the open rectangle.

Sketch: equality of third coordinates gives equal `z`.  Since `1-z>0`, cancel
the radius to obtain equality of both sine and cosine.  Their arguments differ
by an integral multiple of `2π`; two angles strictly between `0` and `2π` must
therefore agree.  Use Mathlib's injectivity theorem for the standard circle
parametrization if available, otherwise derive it from `Real.sin_eq_sin` and
`Real.cos_eq_cos`.

Estimate: 80–140 lines.  Dependencies: none.

Truth check: the only polar-coordinate collisions are the seam and the apex,
and neither lies in the open parameter set.

### `fderiv_parametrization_formula`

Statement: the Fréchet derivative equals `parameterDerivative` at every point.

Sketch: extensionality in the three output coordinates, then `fun_prop` and
`fderiv` rules for projections, products, sine, and cosine; normalize each
coordinate with `ring`.

Estimate: 50–90 lines.  Dependencies: none.

Truth check: differentiating by hand in direction `(a,b)` gives
`(-b cos θ-r sin θ a, -b sin θ+r cos θ a, b)` with `r=1-z`.

### `fderiv_parametrization_injective_on_interior`

Statement: assuming the explicit derivative formula, the derivative is
injective at each interior parameter.

Sketch: if the displayed derivative sends `q` to zero, its third coordinate
gives `q₁=0`.  The sum of the first coordinate times `-sin θ` and the second
times `cos θ` gives `(1-z)q₀=0`; use `z<1` and
`Real.sin_sq_add_cos_sq` to conclude `q₀=0`.

Estimate: 40–70 lines.  Dependencies: takes the conclusion of
`fderiv_parametrization_formula` as an explicit hypothesis, so both seats can
be developed independently.

Truth check: the two derivative columns have third coordinates `0` and `1`,
and the first column has squared horizontal norm `(1-z)²>0`.

### `pullback_coefficients`

Statement: assuming the derivative formula, the pullback coefficients of
`dx wedge dy` and `alpha` are respectively `1-z` and
`alphaPullbackFormula`.

Sketch: unfold `pullbackCoefficient`, rewrite both basis derivatives with the
hypothesis, unfold the coordinate determinants, and simplify using
`Real.sin_sq_add_cos_sq` and `ring`.  Alternation makes the `dz wedge dz` term
zero.

Estimate: 90–140 lines.  Dependencies: takes the conclusion of
`fderiv_parametrization_formula` as a hypothesis.

Truth check: direct 2-by-2 determinants give `dx∧dy = 1-z` and
`dy∧dz = (1-z)cos θ`; substitution produces exactly the defined formula.

### `rectangle_integrals`

Statement: assuming the two pullback formulas, the oriented `dx wedge dy`
integral is positive and the `alpha` integral is `9π/2`.

Sketch: unfold `rectangleIntegral` and rewrite by the hypotheses.  Evaluate
the inner integrals using interval-integral linearity and the standard sine,
cosine, and cosine-square formulas; odd cosine powers integrate to zero.
Finish the remaining polynomial integrals by `intervalIntegral.integral_pow`
or antiderivatives plus `ring_nf`.  The first integral is `π`, hence positive.

Estimate: 120–200 lines.  Dependencies: takes both conclusions of
`pullback_coefficients` as hypotheses.

Truth check: hand integration gives
`2π ∫₀¹(1-z)(z²+4) dz + π ∫₀¹(1-z)² dz = 25π/6+π/3=9π/2`;
the orientation integral is `2π∫₀¹(1-z)dz=π>0`.

## Dependency layers

- Layer 1 (parallel): `extDeriv_alpha`, `image_parametrization_eq_cone`,
  `injOn_parametrization_interior`, `fderiv_parametrization_formula`.
- Layer 2 (parallel and independently testable using an assumed formula):
  `fderiv_parametrization_injective_on_interior`, `pullback_coefficients`.
- Layer 3: `rectangle_integrals`, assuming the two pullback equations.
- Assembly: `apm_t99j06`, which contains no `sorry` and only combines the seven
  results.

No additional ConstructionTargets module is needed.  I searched all sorry-free
files under `ConstructionTargets/` for `t99J06`, `rectangleIntegral`,
`pullbackCoefficient`, parametrization formulas, and exterior-derivative
computations.  `CoordinateSurfaceForms` supplies exactly the definitions;
`ExteriorDerivativeSimplexCalculus` is a useful proof model but has different
forms.  There is therefore no hidden LIBRARY obligation.

## Axiom audit

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t99J06/Blueprint.lean
```

The final `#print axioms` output is:

```text
'apm_t99j06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` reaches the main theorem only through the seven named blueprint
lemmas; the main theorem itself has no placeholder.
