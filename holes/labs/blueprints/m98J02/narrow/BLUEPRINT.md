# Blueprint for m98J02

## Triage and repair

**Verdict: false.** The previous lemma `apm_m98J02_regular_convolution_is_C2`, and therefore canonical part (d), is false for arbitrary distributional fundamental solutions.

The symbol of `T = 2∂x² − ∂y + 3∂x∂y` is `−2ξ²−3ξη−iη`. Its complex zero branch `η(ξ)=−2ξ²/(3ξ+i)` has unbounded real part and bounded imaginary part, violating the constant-coefficient hypoellipticity criterion. Polynomially weighted sums of the resulting exponential modes give a nonsmooth distribution `h` with `Th=0`. Thus `w₀+h` is another fundamental solution; Banach–Steinhaus on a fixed `C²_c(K)` stage supplies some compactly supported `C²` function whose convolution with it is not `C²`.

The encoded predicate cannot choose a different smooth convolution. For fixed `u,v`, translated test functions are unique by extensionality, and two support/cutoff witnesses give the same distributional value by cutoff independence. Hence `apm_m98J02_isConvolution u v w₁` and the same predicate for `w₂` imply `w₁=w₂`. This is now an explicit blueprint lemma.

The informal solution's regularity paragraph explicitly treats `w₀` as a locally integrable function. `RevisedMain.lean` makes the smallest warranted repair by adding a function `k`, `LocallyIntegrable k`, and `apm_m98J02_representsFunction w₀ k`. Convolution of such `k` with compactly supported `C²` `f` is `C²`, with derivatives placed on `f`. The prior compact-support repair for `f` remains necessary to define the convolution used by the source argument. Strict hyperbolicity ensures the intended operator has locally bounded fundamental solutions, but the revised theorem only assumes the representation and need not formalize that construction.

Checks: for `f=0`, the convolution is zero and adding the compiled nonzero constant homogeneous distribution proves nonuniqueness. Locally bounded fundamental functions satisfy the new local-integrability premise. A zero distribution cannot satisfy `Tw₀=δ₀`.

## Reused work

The blueprint retains complete proofs for compact cutoffs, regular distributions of continuous compactly supported functions, translated and differentiated test functions, support calculus, the nonzero constant distribution, and addition of homogeneous solutions.

## Lemmas

### `apm_m98J02_cutoff_independence`

Two compactly supported cutoff realizations of one smooth function have equal evaluation under `u`, even with different support witnesses. Both witnesses contain the distributional support; decompose the difference into test functions supported away from the respective compact sets using compact separation. **Estimate:** 80–150 lines. **Dependencies:** compiled cutoff/support infrastructure. **Check:** for a Dirac mass both sides equal `F` at its support point; equal compact witnesses are immediate.

### `apm_m98J02_translated_pairing_calculus`

The map `x ↦ v(φ(x+·))` is `C²`, with first and second coordinate derivatives obtained by translating the bundled derivatives of `φ`. On compact parameter sets all translates occupy one fixed support stage; difference quotients converge in every seminorm, and continuity of `v` transports convergence to scalars. **Estimate:** 180–300 lines. **Dependencies:** compiled translation and derivative definitions. **Check:** for `v=δ₀` this is ordinary differentiation of `φ(x)`; for the constant distribution all derivatives vanish.

### `apm_m98J02_constantDistribution_homogeneous`

The nonzero constant regular distribution solves the homogeneous equation. Integrals of all compactly supported coordinate derivatives in the formal adjoint vanish by Fubini and one-dimensional FTC. **Estimate:** 90–160 lines. **Dependencies:** compiled adjoint/constant lemmas. **Check:** classically `T(1)=0`.

### `apm_m98J02_isConvolution_unique`

The encoded convolution predicate is functional. Unpack two witnesses, identify their translated test functions, and apply cutoff independence for every `φ`, then distribution extensionality. **Estimate:** 50–90 lines. **Dependencies:** cutoff independence. **Check:** for `u=0` every convolution is zero; for `u=δ₀` it reduces uniquely to `v` (up to the fixed translation convention).

### `apm_m98J02_bridge_2`

If `u` vanishes off compact `K`, its convolution with arbitrary `v` exists. Choose the compiled cutoff and set `Ψφ(x)=χ(x)v(φ(x+·))`; shared translation calculus gives smoothness and `χ` gives compact support. Prove fixed-stage continuity and bundle with `TestFunction.mkCLM`. **Estimate:** 180–280 lines. **Dependencies:** cutoff independence and translated-pairing calculus. **Check:** `u=0` gives zero; `u=δ₀` recovers the expected translate of `v`.

### `apm_m98J02_regular_convolution_is_C2`

If `w₀` is represented by locally integrable `k`, its encoded convolution with compactly supported `C²` `f` is represented by a `C²` function. Define the ordinary convolution integral; locally dominate on one compact set and differentiate twice with derivatives on `f`. Fubini identifies its regular distribution with an explicit encoded convolution, and uniqueness identifies it with abstract `w`. **Estimate:** 180–280 lines. **Dependencies:** translation calculus and convolution uniqueness. **Check:** `k=1` gives a constant; `f=0` gives zero; locally bounded `k` is the elementary case.

### `apm_m98J02_convolution_solves_fundamental`

Convolution with a fundamental solution solves `Tw=f`. Commute the bundled adjoint derivatives through translation using shared calculus, apply `Tw₀=δ₀`, and use cutoff independence to obtain `∫fφ`. **Estimate:** 150–250 lines. **Dependencies:** both shared lemmas. **Check:** this is `T(f*w₀)=f*(Tw₀)=f*δ₀=f`; for zero `f`, all pairings vanish.

## Dependency layers

- **Layer 1, parallel:** cutoff independence, translated-pairing calculus, constant homogeneous distribution.
- **Layer 2, parallel:** convolution uniqueness, convolution construction, and fundamental-solution PDE identity, after their relevant Layer 1 dependencies.
- **Layer 3:** regular convolution is `C²`, using translation calculus and uniqueness.
- **Layer 4:** the already compiled main assembly; it has no direct `sorry`.

## Compilation and axioms

Both Lean files compile under the prescribed memory scope. `Blueprint.lean` prints:

```text
'apm_m98j02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`sorryAx` enters only through the seven named lemmas.

## Doubt

The repair is mathematically sound. The principal implementation risk remains fixed-support-stage convergence in the translated-pairing calculus; Mathlib does not package smooth parameter dependence of test-function translations.
