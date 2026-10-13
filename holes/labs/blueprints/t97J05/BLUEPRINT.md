# Blueprint for t97J05

## Triage and repair

Verdict: **the registered statement needs a small faithfulness repair; the
repaired statement is true**.

The source asks whether `W` is a (smooth embedded) manifold.  The original
predicate supplied a smooth one-manifold structure on the subtype and required
the subtype inclusion to be a topological embedding, but did not require that
inclusion to be an immersion.  This is too weak: a topologically embedded
curve with a corner can be given a smooth source structure using a flat
parametrization, making its inclusion smooth while its derivative at the
corner is zero.  Thus the predicate can certify images which are not embedded
smooth submanifolds in the usual sense.  This is the defect identified by the
statement-registry grader.

`RevisedMain.lean` makes the smallest recommended change: inside
`apm_t97J05_IsSmoothSubmanifold`, it adds

```lean
∀ x : s, Function.Injective (mfderiv ... Subtype.val x)
```

so the inclusion is also an immersion.  No source hypothesis or conclusion is
dropped.  The grader's corner counterexample no longer passes: its flat
parametrization has zero derivative at the corner, which is not injective on a
one-dimensional tangent space.  I did not include `Refute.lean`, since fully
formalizing the exotic charted structure on the corner is substantially
larger than the one-line defect and the repair itself.

The repair is true for this fiber.  On `W`, `xz = 1`, hence `x ≠ 0`; and
`exp x * cos y = 0`, hence `cos y = 0` and `sin y = ±1`.  The derivative rows
there are `(0, -exp x * sin y, 0)` and `(z, 0, x)`, so they have rank two.
The regular-level theorem therefore gives a genuine embedded one-manifold and
an injective derivative for its inclusion.  Degenerate checks: `W` is not
empty (`p ∈ W`); `x = 0` cannot occur because `xz = 1`; and all branches
`y = π/2 + kπ`, including negative `x`, retain rank two.  The parameter target
restricts to `0 < y < π`, selecting exactly the branch `y = π/2` near `p`.

The source's typo giving the domain of `φ` as `ℝ²` while evaluating it on
three coordinates was already correctly repaired to `ℝ³` by `Main.lean` and
is preserved.

## Reused completed work

The solve-loop file already contained a sorry-free proof that
`γ(t) = (t, π/2, 1/t)` is a bijection from `(1/2,3/2)` to the stated local
piece of the fiber.  `Blueprint.lean` retains that calculation as
`apm_t97J05_f_gamma_eq_value` and `apm_t97J05_gamma_bijOn`; it is not assigned
to a lemma seat.

## Remaining lemmas

### `apm_t97J05_derivative_and_rank`

**Statement.** The derivative at `p` has the displayed formula and is
surjective.

**Why true.** Differentiate `exp x * cos y` and `xz` using Mathlib's Fréchet
derivative rules and simplify with `sin (π/2)=1`, `cos (π/2)=0`.  For
surjectivity, send `(a,b)` to `(b,-a/exp 1,0)` (or use the first two columns).

**Expected size.** 50–100 lines.  **Dependencies:** definitions only.

**Truth check.** The matrix is `[[0,-e,0],[1,0,1]]`; its first two columns
have determinant `e ≠ 0`.

### `apm_t97J05_gamma_smooth`

**Statement.** The explicit parameterization is smooth on `(1/2,3/2)`.

**Why true.** Coordinatewise smoothness reduces to constants, the identity,
and `t ↦ t⁻¹`; the interval excludes zero.  Use the `ContDiffWithinAt` rules
for inverse and assemble the finite Euclidean vector coordinatewise.

**Expected size.** 20–40 lines.  **Dependencies:** definitions only.

**Truth check.** The only possible singularity is `t=0`, while every domain
point satisfies `t>1/2`.

### Regular-fiber split

`apm_t97J05_regular_fiber_embedded` is now a sorry-free assembly.  Its leaves
are below.  Except for the final explicitly marked LIBRARY leaf, they are
independent seats; where one mathematical step consumes another, its statement
takes that result as an explicit hypothesis.

#### `apm_t97J05_fiber_third_ne_zero`

From the second fiber equation obtain `q 0 * q 2 = 1`, hence `q 2 ≠ 0`.
Use `mul_ne_zero` contrapositively after extracting coordinate 1 with
`congrArg`, or `mul_eq_zero`.  **Expected size:** 15–30 lines. **Independent.**
Degenerate check: this rules out the only problematic branch `x = 0`.

#### `apm_t97J05_fiber_sin_ne_zero`

The first fiber equation and `Real.exp_ne_zero` give `cos (q 1) = 0`.
Then use `Real.sin_sq_add_cos_sq` to show `sin (q 1)^2 = 1`, hence the sine is
nonzero.  (There is no need to classify all zeros of cosine.)
**Expected size:** 20–35 lines. **Independent.**  This includes every branch
`q 1 = π/2 + kπ`, with either sign of the sine.

#### `apm_t97J05_regular_aux_smooth`

Prove smoothness of `H(x,y,z)=(exp x cos y,xz,z)` coordinatewise with
`contDiff_piLp`, `ContDiff.exp`, `ContDiff.cos`, and `ContDiff.mul` (or
`fun_prop`). **Expected size:** 10–20 lines. **Independent.**

#### `apm_t97J05_regular_aux_deriv_apply`

Compute `DH_q(h)` at an arbitrary `q`.  Follow the already proved
`apm_t97J05_local_normal_form_aux_deriv_apply`, replacing simplification at
`p` by the product-rule expression.  Useful lemmas are `fderiv_pi`,
`fderiv_fun_mul`, `fderiv_exp`, `fderiv_cos`, and `PiLp.hasFDerivAt_toLp`.
**Expected size:** 60–100 lines. **Independent.**  The signs are fixed by
`D(cos)_y(h) = -sin(y)h`; the first coordinate is
`exp(x)cos(y)h₀ - exp(x)sin(y)h₁`.

#### `apm_t97J05_regular_aux_deriv_bijective`

Assuming explicitly `q 2 ≠ 0` and `sin(q 1) ≠ 0`, prove `DH_q` bijective.
(claude-14 review fix: det DH_q = q 2 · exp(q 0) · sin(q 1), so the hypothesis must be q 2 ≠ 0; with only q 0 ≠ 0 the lemma was false at q = (1, π/2, 0).)
Use `apm_t97J05_regular_aux_deriv_apply` only as a rewrite target in the
eventual proof; if strict seat independence is required, repeat that displayed
formula locally rather than invoking the lemma.  Solve successively from the
third, second, and first output coordinates; denominators are nonzero by the
hypotheses and `Real.exp_ne_zero`. **Expected size:** 45–80 lines.
**Independent statement.**  Neither `cos(q 1)=0` nor membership in the fiber
is needed, so boundary/off-fiber points satisfying the two hypotheses are
also covered.

#### `apm_t97J05_regular_aux_local_inverse`

The derivative bijectivity is an explicit hypothesis.  Convert it with
`ContinuousLinearEquiv.ofBijective`; apply
`ContDiffAt.toOpenPartialHomeomorph` and `ContDiffAt.to_localInverse` as in
`apm_t97J05_local_normal_form_aux_inverse_at_p`.  Restrict to the open set
where the derivative is a unit, as in
`apm_t97J05_local_normal_form_aux_smooth_local_inverse`, to obtain smoothness
of the inverse on the whole target.  Key lemmas:
`ContinuousLinearMap.isUnit_iff_bijective`, `Units.isOpen`,
`OpenPartialHomeomorph.restrOpen`, and `contDiffAt_symm`.
**Expected size:** 70–120 lines. **Independent given its explicit `hb`.**

#### `apm_t97J05_regular_aux_flattens_fiber`

Given a chart explicitly whose underlying map is `H`, unpack coordinates 0 and 1:
`z ∈ W` iff `f z=(0,1)` iff `(e z) 0=0 ∧ (e z) 1=1`, because `e=H`.
Use `Subtype`/set membership simplification, `Prod`-style coordinate
extensionality via `fin_cases`, and `congrArg` in the reverse direction.
**Expected size:** 25–45 lines. **Independent given its explicit chart
hypotheses.**  The equivalence is valid at every source point, not merely near
`q`, so no hidden connectedness or branch assumption occurs.

#### `apm_t97J05_regular_fiber_global_assembly` — LIBRARY

From a flat local model at every fiber point, construct the one-dimensional
charted structure on the subtype, prove transition-map smoothness, prove
`IsManifold`, and prove that `Subtype.val` is smooth with injective `mfderiv`.
`Topology.IsEmbedding` is already available as `Topology.isEmbedding_subtypeVal`.
The chart transition calculation should use that ambient transitions preserve
the affine plane `{u | u 0=0 ∧ u 1=1}` and restrict to its third coordinate;
the local inclusion in these coordinates is `t ↦ (0,1,t)`, whose derivative
is injective. **Expected size:** 180–300 lines. **Independent given `hlocal`.**

This is the genuine missing regular-level/preimage foundation in current
Mathlib, not an analytic difficulty particular to this example.  It remains
one marked LIBRARY leaf because splitting it further would require exposing a
large bespoke atlas data structure merely to pass the same charts between
lemmas.  Empty-set and dimension-zero cases are irrelevant to this concrete
statement (`p ∈ W`, and the model has exactly one free coordinate), while the
hypothesis covers all disconnected fiber components and boundary-free open
chart domains.

### `apm_t97J05_local_normal_form`

**Statement.** There are smooth open partial homeomorphisms around `0`, `p`,
`(0,1)`, and `0` which put `f` into the projection `(x,y,z) ↦ (x,y)`.

**Why true.** Complete `f` to
`Φ(x,y,z)=(exp x cos y,xz,z)`.  Its derivative at `p` has determinant `e`, so
the inverse function theorem gives a local inverse.  Translate source and
target: take `φ(u,v,w)=Φ⁻¹(u,v+1,w+1)` locally and `ψ(a,b)=(a,b-1)`.
The first two coordinates then give the demanded equality.

**Expected size.** 100–180 lines.  **Dependencies:** definitions only; use
the inverse function theorem directly so this seat is parallel to the explicit
derivative lemma.

**Truth check.** `DΦ_p=[[0,-e,0],[1,0,1],[0,0,1]]`, with determinant `e`,
and direct substitution gives `ψ(f(φ(u,v,w)))=(u,v)`.

## Dependency layers

* **Layer 1 (all parallel):** the four remaining lemmas above.  Each statement
  is closed over the definitions and does not consume another seat's theorem.
* **Layer 2 (already proved assembly):** `apm_t97j05`, using the four lemmas
  and the retained bijection proof.

## Compilation and axioms

Both files compiled with the prescribed 12G command.  The final output of
`#print axioms apm_t97j05` in `Blueprint.lean` was:

```text
'apm_t97j05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The four warnings are exactly the four top-level seat lemmas.  The main theorem
has no direct `sorry`.

## claude-14 restatement of the global assembly (2026-10-13)

lemma-6's attempt at a general regular-level atlas came back PARTIAL (only line-model helpers). The
fiber is explicit: W = {cos y = 0, x z = 1} = ⋃_k {(x, π/2 + kπ, 1/x) : x ≠ 0}, so the first coordinate is
a chart on each branch and every transition map is the identity. `apm_t97J05_regular_fiber_global_assembly`
is now a sorry-free assembly from `apm_t97J05_xChartedSpace` (a definition from the chosen charts) and four leaves:
- `fiber_second_coord_eq` (20-40): zeros of cos are π apart.
- `xCharts_exist` (80-140): the chart at q (source |w1 - q1| < π/2 and w0 q0 > 0; inverse t ↦ (t, q1, 1/t)).
- `xCharts_isManifold` (40-80): transitions are identity on their sources (isManifold_of_contDiffOn).
- `xCharts_inclusion` (60-120): val in charts is t ↦ (t, q1, 1/t), smooth for t ≠ 0, first derivative component h0.
Embedding is `Topology.IsEmbedding.subtypeVal`. `hlocal` is unused (kept so the caller is unchanged).
