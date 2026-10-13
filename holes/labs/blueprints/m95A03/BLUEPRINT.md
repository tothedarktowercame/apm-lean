# Statement repair and blueprint for m95A03

## Triage verdict: false as originally encoded; proposed repair adopted

The source asks for existence and uniqueness of the solution/minimizer on the
interval `[a,b]`. The frozen statement instead used `∃!` over global functions
`ℝ → ℝ`. Since the energy and endpoint constraints observe only `[a,b]`, this
global uniqueness is false.

The included compiled `Refute.lean` specializes to `a=0`, `b=1`, `p=1`, and
`q=f=0`. Given any global `C²` minimizer, it adds a nonzero smooth bump
supported near `2`. The perturbation and its derivative vanish on `[0,1]`, so
it has the same admissibility and energy while being a different global
function. The file proves the negation of the full original universally
quantified theorem without placeholders.

The solve-loop proposal replaces the final `∃!` by existence of one global
`C²` representative together with `Set.EqOn` uniqueness on `Icc a b`. This is
exactly the source's interval-local meaning, so `RevisedMain.lean` adopts the
proposal unchanged.

Degenerate and endpoint checks:

- `a<b` rules out the empty/zero-length interval;
- `p₀>0` and `p₀≤p` rule out degeneration of the leading coefficient;
- when `q=0`, equality of energies still forces the derivative difference to
  vanish, and the zero endpoint condition forces interval equality;
- exterior bumps remain possible, but are intentionally identified only by
  `EqOn` rather than global equality;
- the ODE is required on `Icc`, including endpoints. The residual is
  continuous under the stated `C¹/C²/continuous` hypotheses, so an equation
  first derived on `Ioo` extends to the endpoints.

## Remaining lemmas

### `apm_m95A03_isMinOn_of_solves`

**Statement.** Every classical solution of the inhomogeneous Dirichlet
problem is a global minimizer of the energy over the admissible class.

**Proof sketch.** For an admissible competitor `v`, put `h=v-u`. Expand
`J(v)-J(u)` into the cross term
`2∫(p u' h' + q u h + f h)` plus
`∫(p(h')²+q h²)`. Use
`intervalIntegral.integral_mul_deriv_eq_deriv_mul` on `(p u')h`; the endpoint
term vanishes because `h(a)=h(b)=0`. Substitute `(p u')'-qu=f` to cancel the
cross term. The remaining integral is nonnegative from `p≥p₀>0` and `q≥0`.

**Estimate.** 150--230 lines.

**Dependencies.** Definitions and Mathlib's interval integration-by-parts
API; no remaining lemma.

**Truth check.** With `p=1,q=f=0` and zero boundary data, the solution is zero
and the difference is exactly `∫(v')²≥0`. For `q=0`, the argument still works
without a zeroth-order term.

### `apm_m95A03_solves_of_isMinOn`

**Statement.** A global `C²` admissible energy minimizer satisfies the
Sturm--Liouville equation and endpoint data.

**Proof sketch.** For every smooth compactly supported test `η` inside
`(a,b)`, both `u+sη` and `u-sη` are admissible. Minimality of the exact
quadratic polynomial in `s` forces its linear coefficient to vanish. Integrate
`p u'η'` by parts to obtain the residual paired with every test. Apply
`ae_eq_zero_of_integral_contDiff_smul_eq_zero`, then upgrade a.e. vanishing to
pointwise vanishing on the open interval with
`MeasureTheory.Measure.eqOn_open_of_ae_eq`. Continuity of the residual extends
the equation to `a` and `b`; the boundary equations are hypotheses.

**Estimate.** 220--300 lines.

**Dependencies.** Definitions and the fundamental-lemma/integration-by-parts
APIs; no remaining lemma.

**Truth check.** The hand first variation is
`2∫(p u'η' + q uη + fη)`, whose integration by parts gives
`2∫(-(p u')'+qu+f)η`. Both signs agree with the encoded equation
`(p u')'-qu=f`. Constant variations are correctly excluded by the endpoint
constraint.

### `apm_m95A03_homogenization`

**Statement.** Subtracting the affine boundary lift converts the original BVP
to the zero-boundary BVP with the encoded modified right-hand side.

**Proof sketch.** Compute the affine lift at `a` and `b` using `a≠b`. Show it
is smooth and use `deriv_sub` and distributivity to expand
`(p(u-w)')'-q(u-w)`. The expression rearranges definitionally to
`f-((pw')'-qw)`. `ContDiff` and endpoint conditions transfer in both
directions.

**Estimate.** 80--140 lines.

**Dependencies.** Definitions only; no remaining lemma.

**Truth check.** Direct substitution gives `w(a)=α`, `w(b)=β`. When
`α=β=0`, `w=0` and the statement reduces to the original BVP.

### `apm_m95A03_exists_homogeneous_minimizer`

**Statement.** Under uniform positivity of `p` and nonnegativity of `q`, the
zero-boundary energy has a global `C²` minimizer.

**Proof sketch.** Solve the linear two-point BVP. One route is the source's
coercive weak formulation on `H¹₀(a,b)`: Poincaré plus `p≥p₀` makes the
bilinear form coercive; Riesz/Lax--Milgram gives a weak solution, and the
one-dimensional equation with `p∈C¹`, `q,f` continuous upgrades it to `C²`.
Because Mathlib lacks a bundled Sobolev/Lax--Milgram path matching these raw
function definitions, a more direct formal route is to rewrite as the
first-order system for `(u,p u')`, use linear ODE existence, and show the
Dirichlet shooting map has nonzero slope via the energy identity for the
homogeneous equation. Extend the interval solution to a global `C²` function
using its endpoint second-order jets. The first bridge then proves minimality.

**Estimate.** 260--350 lines.

**Dependencies.** Definitions and standard ODE/integration APIs. Its statement
is standalone; it may call the solve-implies-minimum bridge after merging.

**Truth check.** For `p=1,q=0`, the explicit solution of `u''=f` with zero
endpoints exists and is unique. For the homogeneous difference equation,
multiplication by the solution and integration by parts gives
`∫(p(u')²+qu²)=0`, ruling out a nonzero zero-boundary solution and hence
showing the shooting denominator is nonzero.

### `apm_m95A03_minimizers_eqOn`

**Statement.** Any two global `C²` zero-boundary minimizers agree throughout
`[a,b]`.

**Proof sketch.** Let `h=v-u`. Since both are minimizers, the midpoint is
admissible and convexity gives equality in the quadratic midpoint identity.
Equivalently compare the two exact energy expansions. Deduce
`∫(p(h')²+q h²)=0`. The continuous integrand is nonnegative, so it vanishes;
`p≥p₀>0` gives `h'=0` on the interval. The endpoint value `h(a)=0` then gives
`h=0` on all of `Icc a b` by the mean value theorem.

**Estimate.** 120--190 lines.

**Dependencies.** Definitions only; no remaining lemma.

**Truth check.** Exterior bumps demonstrate why only `EqOn` is possible, but
they satisfy the conclusion. With `q=0`, derivative equality plus one endpoint
still proves equality; with positive `q`, the conclusion is only stronger.

## Dependency layers

- **Layer 1 (parallel):** all five remaining lemmas have standalone
  statements. Homogenization and interval uniqueness are especially isolated;
  the two variational directions and existence can also be developed in
  separate files from the shared definitions.
- **Layer 2:** main theorem assembly. Part (a) combines the two implications,
  part (b) is the homogenization lemma, and part (c) combines existence with
  interval uniqueness. The assembly is already proved without `sorry`.

## Confidence and doubt

The proposed repair is correct and no further statement defect was found. I
am convinced all five lemmas are mathematically true. The substantial doubt is
engineering size for existence: Mathlib does not expose a ready-made
Lax--Milgram/Sobolev theorem for this raw `ℝ→ℝ` encoding, so the shooting/ODE
route plus construction of a global `C²` extension may exceed the nominal
300-line seat estimate. If that happens, split it internally into “Dirichlet
BVP existence on `[a,b]`” and “global `C²` extension plus minimality”; its
current public statement remains the clean interface needed by the theorem.

## Compile gates and axioms

All files compile:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m95A03/Refute.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m95A03/RevisedMain.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m95A03/Blueprint.lean
```

Output of `#print axioms apm_m95a03`:

```text
'apm_m95a03' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The blueprint main theorem has no `sorry`; `sorryAx` enters only through the
five named lemmas.
