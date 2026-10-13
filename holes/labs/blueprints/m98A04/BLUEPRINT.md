# Re-split blueprint for m98A04

## Triage

The registered theorem remains true and byte-identical. The previous two admitted lemmas were split by conclusion, but both required the same hard LF-topology argument: reflected translations and their difference quotients stay in one compact-support stage and converge there. That shared work is now isolated.

All previously compiled definitions and proofs remain. The two old public bridge lemmas are retained, but are now proved from four new admitted lemmas; they contain no `sorry` themselves.

## Local fixed-stage definitions

For `φ` and a base point `x₀`, `apm_m98a04_translateReflectStageLocal` takes values in the single Fréchet space supported in `translationCompact φ x₀`. It agrees with `y ↦ φ(x-y)` on the closed unit ball and uses zero outside; this fallback is irrelevant in a neighborhood of `x₀`.

`apm_m98a04_directionalTF v φ` is the finite coordinate sum representing `Dφ(v)`. `apm_m98a04_translationStageToTest` is the continuous inclusion of the fixed stage into the LF test-function space.

## New lemmas

### `apm_m98a04_translateReflectStageLocal_continuousAt`

**Statement.** The local reflected-translation map is continuous at its base point as a map into one fixed compact-support stage.

**Proof sketch.** On a smaller ball the zero fallback disappears. Every spatial derivative is a reflected translate of the corresponding derivative of `φ`. Uniform continuity on the compact enlarged support gives convergence for each stage seminorm; use the stage topology's seminorm characterization.

**Estimate:** 50–90 lines. **Dependencies:** only compiled stage definitions and translation estimates.

**Checks:** for `φ=0` the map is locally constant zero. In dimension zero the parameter space is a singleton. Pointwise, translation by `x→x₀` plainly converges to the base translate.

### `apm_m98a04_translateReflectStageLocal_difference_quotient`

**Statement.** After inclusion from that one fixed stage into test functions, the punctured directional difference quotient converges to the reflected translate of `Dφ(v)`.

**Proof sketch.** Apply the already compiled uniform quadratic Taylor remainder to every iterated spatial derivative. Reflection preserves the relevant sup norms. Divide the `O(|h|²‖v‖²)` remainder by `|h|`; each fixed-stage seminorm tends to zero. The inclusion into the LF space is continuous.

**Estimate:** 80–130 lines. **Dependencies:** compiled quadratic-remainder and fixed-stage estimates only; independent of the continuity lemma.

**Checks:** for `v=0` every quotient and the target are zero. For `φ=0` the result is trivial. For one-dimensional evaluation, it is the ordinary difference quotient for `φ(x-y)` with the positive parameter derivative sign.

### `apm_m98a04_translation_pairing_fderiv_of_stage_dq`

**Statement.** Given the difference-quotient conclusion explicitly as a hypothesis, evaluation by a distribution has the expected coordinate Fréchet derivative.

**Proof sketch.** Compose the supplied convergence with the continuous distribution. Specialize `v` to `EuclideanSpace.single i 1`; the finite directional test function simplifies to `partialListTF [i] φ`. Convert directional difference quotients to the scalar `fderiv` equality.

**Estimate:** 30–60 lines. **Dependencies:** the stage-DQ fact is an explicit hypothesis, so this seat can run in parallel with the DQ seat.

**Checks:** for the zero distribution both sides vanish. For Dirac evaluation at zero, this is the usual coordinate derivative of `φ(x)`.

### `apm_m98a04_translation_pairing_contDiff_of_stage_facts`

**Statement.** Given fixed-stage continuity and difference-quotient conclusions for every test function, the scalar translation pairing is `C∞`.

**Proof sketch.** Distribution evaluation preserves the supplied continuity and directional limits. The derivative is the finite coordinate-linear map obtained from translated first derivatives. Iterate the same argument on every `partialListTF indices φ`; induction on derivative order yields `ContDiff ℝ k` for every finite `k`, hence `ContDiff ℝ ∞`.

**Estimate:** 80–140 lines. **Dependencies:** both topology facts are explicit hypotheses, so this seat is independently provable before either lands.

**Checks:** the zero distribution gives a constant smooth function. In dimension zero all derivatives are vacuous. For Dirac evaluation the result reduces to the compiled smoothness of `φ`.

## Assembly

The old lemmas are now proved as follows:

- `translation_pairing_fderiv_single_of_pos_dim` applies the derivative-extraction lemma to the new DQ theorem.
- `translation_pairing_contDiff_of_pos_dim` applies the smoothness-extraction lemma to the new continuity and DQ theorems.

The dimension-zero bridge, analytic bridge, convolution construction, periodic computation, and main theorem remain proved.

## Dependency layers

- **Layer 1, fully parallel:** all four new lemmas. The two consumer lemmas receive shared facts as explicit hypotheses.
- **Layer 2, proved assembly:** the two old positive-dimensional lemmas.
- **Layer 3, proved assembly:** analytic bridge and main theorem.

## Compilation and axioms

Compiled with the prescribed command. Output:

```text
'apm_m98a04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

There are exactly four `sorry` warnings, one for each new lemma. The old lemmas and main theorem contain no direct `sorry`.

## Doubt

The statements are true. The only substantial engineering risk is expressing convergence simultaneously in every seminorm of `ContDiffMapSupportedIn`; the cached quadratic estimates already provide the required bounds.
