# Blueprint and statement repair for a96A06

## Triage verdict: unfaithful (and false as encoded)

The informal problem explicitly assumes that `f` is analytic on the complex
plane except for a **simple pole** at `1`. The checked-in Lean theorem assumes
only

```lean
DifferentiableOn ℂ f ({1}ᶜ)
```

and the contour integral. It omits the simple-pole condition, so it permits
higher-order poles and essential singularities. Its main declaration is also
named `taylor_coeffs_tend_to_one`, whereas the solve loop expects
`apm_a96a06`.

### Counterexample to the checked-in statement

Take

```text
f(z) = (1-z)⁻¹ + (z-1)⁻².
```

This is holomorphic away from `1`. The first summand has contour integral
`-2πi` around `|z|=2`; the second-order-pole term has zero residue and hence
zero contour integral. Thus `f` satisfies both Lean hypotheses. But
`(z-1)⁻² = (1-z)⁻²` has Taylor coefficient `n+1`, so the normalized `n`th
derivative of `f` at zero is `1+(n+1)=n+2`, which does not tend to `1`.

This is the counterexample documented in `Main.lean` and the solve-loop
obstruction. A standalone fully compiled `Refute.lean` was not included:
formalizing both the second-order-pole circle integral and its complete
iterated-derivative sequence would be comparable in size to a proof seat, not
a short packaging exercise.

## Repair

`RevisedMain.lean` makes the smallest semantic repair: it preserves the two
existing hypotheses and adds the source's missing simple-pole assumption. As
Mathlib has no general `HasSimplePoleAt` predicate, the file defines

```lean
apm_a96A06_HasSimplePoleAtOne f :=
  ∃ c g, c ≠ 0 ∧ Differentiable ℂ g ∧
    ∀ z ≠ 1, f z = c / (z - 1) + g z
```

This is the standard Laurent decomposition of a function analytic everywhere
except for a simple pole at `1`. It neither fixes the residue in advance nor
weakens any source assumption. The contour integral subsequently forces
`c = -1`. The repaired theorem is named `apm_a96a06`.

Degenerate cases were checked: `c = 0` is excluded because the source says
“pole”; a constant or entire function therefore cannot satisfy the new pole
hypothesis. A higher-order pole such as the counterexample cannot be absorbed
into the entire remainder. The circle has radius `2`, so the pole at distance
`1` lies strictly inside it and never lies on the path.

## Reused compiled work

The blueprint retains these complete proofs from `Main.lean`:

- `cauchy_estimate_taylor`;
- `geom_iteratedDeriv` and `geom_taylor_coeff`;
- `entire_coeffs_tendsto_zero`.

Only the two bridges below remain.

## Remaining lemmas

### `apm_a96A06_pole_coefficient_eq_neg_one`

**Statement.** If off `1` the function is `c/(z-1) + g(z)`, with `g` entire,
and its integral around `C(0,2)` is `-2πi`, then `c=-1`.

**Proof sketch.** The representation holds everywhere on the circle because
`|z|=2` implies `z≠1`. Apply circle-integral congruence and linearity.
`circleIntegral.integral_sub_inv_of_mem_ball` evaluates the integral of
`(z-1)⁻¹` as `2πi`. The entire remainder integrates to zero using
`DiffContOnCl.circleIntegral_eq_zero`. The resulting scalar identity is
`c * 2πi = -2πi`; cancel the nonzero factor using `Real.pi_ne_zero` and
`I_ne_zero`.

**Estimate.** 70--120 lines.

**Dependencies.** Only the definitions and Mathlib's circle-integral API; no
remaining lemma.

**Truth check.** Direct residue computation gives
`∮f = 2πi·c`, so the supplied value forces `c=-1`. The test cases `c=1` and
`c=-1` give respectively `2πi` and `-2πi`, confirming the sign convention.

### `apm_a96A06_coeffs_tendsto_of_representation`

**Statement.** If `f = c/(z-1)+g` away from `1`, `g` is entire, and `c=-1`,
then the normalized iterated derivatives of `f` at zero tend to `1`.

**Proof sketch.** Near zero the representation becomes
`f(z) = (1-z)⁻¹ + g(z)`. Transfer iterated derivatives through this local
equality with `Filter.EventuallyEq.iteratedDeriv_eq`, then split them with
`iteratedDeriv_add`. The compiled `geom_taylor_coeff` makes the polar
coefficient exactly `1`, while `entire_coeffs_tendsto_zero hg` sends the
remainder coefficient to zero. Finish with `Tendsto.const_add` (or
`Tendsto.add tendsto_const_nhds`).

**Estimate.** 80--140 lines.

**Dependencies.** Definitions plus the already compiled geometric and entire
coefficient lemmas; no remaining lemma.

**Truth check.** For `g=0`, every coefficient is exactly `1`. For constant or
polynomial `g`, only finitely many extra coefficients are nonzero. The Cauchy
estimate already proved in the file handles arbitrary entire `g`.

## Dependency layers

- **Layer 1 (parallel):** both remaining lemmas. The coefficient-limit lemma
  accepts `c=-1` as a hypothesis, so it does not refer to the contour lemma.
- **Layer 2:** main theorem assembly: unpack the simple-pole representation,
  obtain `c=-1` from the first lemma, and pass it to the second.

## Confidence and doubt

The repaired statement and both lemma statements are mathematically sound.
The only mild design tradeoff is that the custom simple-pole predicate uses an
explicit global entire-remainder decomposition because Mathlib exposes no
general simple-pole predicate. This is equivalent to the source assumption in
this one-singularity setting and makes the intended argument available without
inventing a larger Laurent-series framework. The preserved `hf_holo`
hypothesis is redundant once this decomposition is known, but retaining it is
the smallest edit to the existing theorem and mirrors the source's
“analytic except at” clause.

## Compile gates and axioms

Both commands succeed:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/a96A06/RevisedMain.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/a96A06/Blueprint.lean
```

Output of `#print axioms apm_a96a06` in the blueprint:

```text
'apm_a96a06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The blueprint's main theorem has no `sorry`; `sorryAx` enters only through the
two named remaining lemmas.
