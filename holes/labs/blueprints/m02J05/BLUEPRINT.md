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

## Parallel lemma split

### `apm_m02J05_young_shape`

**Statement.** The Young primitive is convex and monotone on `[0,∞)`.
**Sketch.** Its derivative is `α`; integrate the monotonicity inequality for
secant slopes. Monotonicity also follows from nonnegativity of `α` (the
pointwise version is already compiled). **Estimate:** 60--110 lines.
**Dependencies:** compiled scalar lemmas only. **Truth check:** for `α=id`,
the primitive is `t²/2`; at `t=0` both properties include the endpoint.

### `apm_m02J05_bridge_convex_and_submodule_of_young_shape`

**Statement.** Given the preceding shape fact explicitly, `K_A` is convex
and `L_A` is the carrier of a submodule. **Sketch.** Combine convexity and
monotonicity with the pointwise absolute-value inequality. Put two rescaling
witnesses over a common denominator to prove addition closure; scalar closure
is direct. **Estimate:** 90--140 lines. **Dependencies:** `hshape` is an
explicit hypothesis, so this seat is independent. **Truth check:** zero and
scalar-zero are already compiled; for `α=id` this is the usual `L²` class.

### `apm_m02J05_lux_sublevel_attained`

**Statement.** For `u∈L_A`, the positive modular sublevel is nonempty and
bounded below, its infimum is nonnegative, and for `u≠0` the infimum belongs
to the sublevel. **Sketch.** Enlarge the denominator from an integrable
rescaling witness; use dominated convergence for nonemptiness and Fatou for
closure at a positive infimum. The nonzero condition is necessary: for
`u=0`, the sublevel is all positive reals and its infimum zero is not a
member. **Estimate:** 100--150 lines. **Dependencies:** definitions only.
**Truth check:** this zero-function endpoint explains the precise statement;
for a nonzero constant and `α=id`, the sublevel is a closed ray with positive
left endpoint.

### `apm_m02J05_lux_definite`

**Statement.** On `L_A`, `lux u=0 ↔ u=0`. **Sketch.** Coercivity of the
Young primitive excludes arbitrarily small denominators whenever `|u|` is
bounded below on a positive-measure set; the converse computes the zero
sublevel. **Estimate:** 70--120 lines. **Dependencies:** standalone scalar
hypotheses. **Truth check:** the repaired quotient makes every function
supported outside `[0,1]` literally zero, while a nonzero constant has
positive gauge.

### `apm_m02J05_lux_homogeneous`

**Statement.** `lux (c • u)=|c| lux u`. **Sketch.** For `c≠0`, identify the
two sublevel sets by multiplication by `|c|` and transport their infima; treat
`c=0` directly. **Estimate:** 50--100 lines. **Dependencies:** standalone.
**Truth check:** `c=0`, negative `c`, and `u=0` all reduce to absolute-value
identities.

### `apm_m02J05_lux_triangle_of_facts`

**Statement.** Given Young convexity/monotonicity and the attained-sublevel
fact explicitly, the Luxemburg gauge satisfies the triangle inequality.
**Sketch.** Handle either zero norm separately. Otherwise normalize by the
sum of the norms, apply convexity to the pointwise weighted average, and use
the two attained modular bounds. **Estimate:** 70--120 lines.
**Dependencies:** `hshape` and `hsublevel` are explicit hypotheses, so this
seat can run in parallel with both suppliers. **Truth check:** if either
function is zero the claim is equality; for constants and `α=id` it is the
ordinary triangle inequality.

The original structural and Luxemburg bridges are now proved assembly
theorems. The Luxemburg bridge projects nonnegativity from the sublevel lemma
and combines the other three laws; it has no `sorry`.

### `apm_m02J05_inverse_partner_lux_facts`

**Statement.** The inverse-function hypotheses imply the sublevel/attainment
and definiteness facts for the complementary function `β`. **Sketch.** Derive
strict monotonicity, zero value, and divergence of `β` from the two inverse
identities, then apply the focused sublevel and definiteness arguments.
**Estimate:** 60--110 lines. **Dependencies:** standalone paired hypotheses.
**Truth check:** for `α=β=id` this is the checked quadratic case; the inverse
laws exclude a flat or bounded complementary function.

### `apm_m02J05_bridge_complementary_young_holder_of_lux_facts`

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

**Estimate.** 120--150 lines after the Luxemburg work has been separated.

**Dependencies.** The sublevel and definiteness results for both functions
are explicit hypotheses, so this seat is independent of their suppliers.

**Truth check.** With `α=β=id`, Young's inequality becomes
`st≤s²/2+t²/2`. With either function zero, both sides of Hölder are zero. For
constant functions, the estimate reduces to the scalar Young inequality on a
measure-one interval.

## Dependency layers

- **Layer 1 (parallel, eight seats):** Young shape, convex/submodule from an
  explicit shape hypothesis, sublevel/attainment, definiteness, homogeneity,
  triangle from explicit shape/sublevel hypotheses, inverse-partner Luxemburg
  facts, and complementary Young--Hölder from explicit Luxemburg facts.
- **Layer 2 (proved):** the original three bridges.
- **Layer 3 (proved):** the registered main theorem assembly.

## Confidence and doubt

The repair is exact and the compiled refutation confirms the original defect.
I am convinced all eight statements are true. The most delicate seat remains
sublevel attainment because it combines `sInf`, Fatou, and `AEEqFun`, but its
scope is now isolated and estimated within one session. The explicit
`u≠0` guard is essential and avoids a false attainment claim at the zero
function.

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

The blueprint main theorem has no `sorry`; `sorryAx` enters through exactly
the eight Layer 1 lemmas.
