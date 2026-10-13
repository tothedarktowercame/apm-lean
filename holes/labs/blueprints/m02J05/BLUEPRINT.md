# Statement repair and blueprint for m02J05

## Triage verdict: false and unfaithful

The informal problem defines measurable functions on `[0,1]`, modulo the
usual almost-everywhere identification on that interval. The Lean statement
instead used `ℝ →ₘ[volume] ℝ`, whose equality is almost everywhere on all of
`ℝ`, while every modular integral observes only `[0,1]`. Consequently its
Luxemburg functional is merely a seminorm on the encoded ambient space.

The compiled `Refute.lean` is copied from the solve-loop refutation. It uses

```text
outside(x) = max (x - 1) 0.
```

This function is zero almost everywhere on `[0,1]`, so it belongs to every
encoded `L_A` and has Luxemburg value zero. It is positive on `(1,∞)`, hence
is nonzero in `ℝ →ₘ[volume] ℝ`. Taking `α=β=id` satisfies every scalar
hypothesis and contradicts the definiteness conjunct of `apm_m02j05`.

## Repair

`RevisedMain.lean` changes only the ambient measurable-function type:

```lean
abbrev apm_m02J05_Fun :=
  ℝ →ₘ[volume.restrict (Icc (0 : ℝ) 1)] ℝ
```

`K_A`, `L_A`, the Luxemburg functional, and the submodule conclusion now use
this type. All scalar hypotheses and all mathematical conclusions are
unchanged. This directly matches the problem's phrase “measurable” together
with its exclusive use of the domain `[0,1]`; no new mathematical assumption
has been added.

Degenerate checks:

- a function supported outside `[0,1]` is now literally the zero element, so
  the old counterexample disappears for the intended reason;
- the zero function remains in `K_A` and `L_A` (the proof was adjusted to use
  `AEEqFun.coeFn_zero` for the restricted measure);
- the interval has positive finite measure, so constants and characteristic
  functions retain the expected nonzero norm;
- `α=β=id` remains admissible and yields the familiar quadratic Young
  functions, providing a concrete sanity check for every conclusion.

## Reused compiled work

The blueprint retains compiled proofs that the Young primitive vanishes at
zero, is nonnegative and monotone on the nonnegative half-line, and that zero
belongs to `K_A` and `L_A`. The three bridge statements developed by the solve
loop have been transported to the repaired ambient type.

## Remaining lemmas

### `apm_m02J05_bridge_convex_and_submodule`

**Statement.** Under the hypotheses on `α`, `K_A` is convex and `L_A` is the
underlying set of a real submodule of the repaired function space.

**Proof sketch.** First show the primitive `A(t)=∫₀ᵗα` is convex on
`[0,∞)` because its derivative `α` is monotone. Combine convexity with the
already proved monotonicity of `A` and
`|r u+(1-r)v| ≤ r|u|+(1-r)|v|` to prove convexity of `K_A`. Prove solidity
under scalars of absolute value at most one. For `u,v∈L_A`, shrink their two
witness scalars to a common positive scalar and apply convexity at weight
`1/2`; scalar closure follows by rescaling the witness. Package the resulting
zero/add/smul closure as a `Submodule`.

**Estimate.** 180--280 lines.

**Dependencies.** Definitions and the already proved Young-zero,
Young-nonnegative, and Young-monotone lemmas. It does not depend on another
remaining bridge.

**Truth check.** For `α=id`, `A(t)=t²/2`, so `K_A` is the ordinary square-
integrable modular class and the construction reduces to the standard vector
space argument. The zero and scalar-zero cases were separately checked in
Lean.

### `apm_m02J05_bridge_luxemburg_laws`

**Statement.** On `L_A`, the repaired Luxemburg functional is nonnegative,
definite, absolutely homogeneous, and subadditive.

**Proof sketch.** Study the sublevel set in the `sInf` definition. It is
nonempty for each `u∈L_A`: use the integrable rescaling witness as a dominator
and send the denominator to infinity. It is bounded below by zero and upward
closed. Fatou's lemma gives closure/attainment at a positive infimum.
Definiteness uses coercivity of `A`: if `u` is nonzero in the restricted
`AEEqFun`, then `|u|≥ε` on a restricted-measure set of positive measure, which
excludes all sufficiently small denominators. Homogeneity follows by scaling
the sublevel set. For the triangle inequality, normalize by
`lux u + lux v`, use convexity of `A`, and integrate the resulting convex
combination.

**Estimate.** 260--320 lines.

**Dependencies.** Definitions and the scalar Young-function facts. Its proof
may reuse the convexity argument from the first bridge once merged, but its
statement is standalone and a seat can prove it directly.

**Truth check.** The former outside-support counterexample becomes zero in the
repaired quotient. For a nonzero constant `u=k` and `α=id`, the sublevel set
can be computed explicitly and has a strictly positive infimum proportional
to `|k|`; scaling and triangle laws reduce to those of absolute value.

### `apm_m02J05_bridge_complementary_young_holder`

**Statement.** For inverse nonnegative functions `α,β`, their integral
primitives satisfy pointwise Young's inequality, and functions in the two
Orlicz classes satisfy the Luxemburg Hölder estimate with constant two.

**Proof sketch.** Prove the complementary-area identity
`A(s)+Ã(α(s))=sα(s)` using interval integration and the inverse identities.
Monotonicity then treats separately `t≤α(s)` and `α(s)≤t`, yielding
`st≤A(s)+Ã(t)`. For nonzero norms, apply this pointwise to
`|u|/lux_A(u)` and `|v|/lux_Ã(v)`, integrate, and use attainment of both
Luxemburg sublevels to bound the two modular integrals by one. Treat either
zero-norm case using definiteness. Finally use `u*v ≤ |u|*|v|`.

**Estimate.** 220--300 lines.

**Dependencies.** Definitions and the inverse hypotheses. The Hölder half
uses the norm-sublevel/definiteness facts represented by the second bridge
when assembling a final proof, but the theorem statement itself is
self-contained and can be developed independently.

**Truth check.** With `α=β=id`, Young's inequality becomes
`st≤s²/2+t²/2`. With either function zero, both sides of Hölder are zero. For
constant functions, the estimate reduces to the scalar Young inequality on a
measure-one interval.

## Dependency layers

- **Layer 1 (parallel seats):** all three bridge lemmas. They have standalone
  statements from the definitions and scalar assumptions. The second and
  third seats may reproduce small convexity/attainment facts locally; after
  merging, they can instead call the first/second bridge where convenient.
- **Layer 2:** main theorem assembly. It projects the nonnegativity of `α` from
  the paired hypothesis, invokes all three bridges, and concatenates their
  conclusions. This assembly is already proved without `sorry`.

## Confidence and doubt

The repair is exact and the compiled refutation confirms the original defect.
I am convinced all three repaired bridge statements are true. The Luxemburg
bridge is at the upper edge of one session (estimated up to about 320 lines)
because Mathlib has no packaged Orlicz/Luxemburg theory; the fragile portion
will be `sInf` nonemptiness and definiteness on `AEEqFun`. Splitting it further
would expose several technical sublevel-set predicates in the public
definitions block, so the current boundary is the cleanest mathematical
interface despite that size risk.

## Compile gates and axioms

The following all compile:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m02J05/Refute.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m02J05/RevisedMain.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m02J05/Blueprint.lean
```

Output of `#print axioms apm_m02j05` in the blueprint:

```text
'apm_m02j05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The blueprint main theorem has no `sorry`; `sorryAx` enters only through the
three named bridge lemmas.
