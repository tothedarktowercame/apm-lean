# Blueprint for m99A01

## Triage verdict: true (already repaired)

The current Lean statement faithfully classifies stationary curves **on the
observed interval** `[0, π/2]` using `Set.EqOn`. This is the right reading of
the informal problem, whose curves live only on that interval even though the
Lean encoding extends them to functions `ℝ → ℝ`.

The solve-loop refutation concerns an older conclusion asserting equality on
all of `ℝ`. Its counterexample is valid: add the compiled smooth bump
`apm_m99A01_counterBump`, supported near `-2`, to the extremal. The bump and
its derivative vanish for every `x ≥ 0`, so the new curve has the same
endpoints, functional, and first variations, but differs at `-2`. This does
not refute the current `EqOn ... (Icc 0 (π/2))` conclusion. No statement repair
is needed.

The endpoint cases are also consistent: admissibility supplies equality at
both endpoints, while the Euler--Lagrange argument works on the open interval.
The interval is nondegenerate because `Real.pi_pos` gives `0 < π/2`.

All of the candidate calculation, exact quadratic energy decomposition,
global minimality, and nonexistence of a maximum are retained with their
compiled proofs from the solve-loop file. Only the classification bridge is
split below.

## Definitions

The file retains the problem's definitions of the functional, admissible
curves, intrinsic stationarity, and the explicit extremal. It adds
`apm_m99A01_residual y t = y''(t) - y(t) - 1`, so each remaining lemma has a
self-contained statement.

## Remaining lemmas

### `apm_m99A01_stationary_residual_zero`

**Statement.** A globally `C²`, admissible stationary curve has zero
Euler--Lagrange residual at every point of `(0, π/2)`.

**Proof sketch.** Differentiate the quadratic integrand with respect to the
variation parameter using
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`; compactness
of the interval and continuity supply a constant integrable dominator. For
smooth compactly supported tests inside the open interval, integrate the
`y'η'` term by parts with
`intervalIntegral.integral_mul_deriv_eq_deriv_mul`; the boundary term is zero.
Convert the interval integral to the whole-space compact-support formulation
and apply `ae_eq_zero_of_integral_contDiff_smul_eq_zero`. Finally use the
already proved `apm_m99A01_eq_zero_on_Ioo_of_ae` (whose proof invokes
`MeasureTheory.Measure.eqOn_open_of_ae_eq`) to upgrade almost-everywhere
vanishing to pointwise vanishing.

**Estimate.** 220--300 lines.

**Dependencies.** Definitions and the already proved
`apm_m99A01_eq_zero_on_Ioo_of_ae`; no remaining lemma.

**Truth check.** The first-variation calculation by hand is
`δJ(y)[η] = 2∫(y'η' + (y+1)η)`. Integration by parts gives
`-2∫(y''-y-1)η`, hence the asserted residual. Constant and endpoint-supported
degeneracies cause no issue because the fundamental-lemma tests are supported
strictly inside the interval.

### `apm_m99A01_eqOn_extremal_of_residual_zero`

**Statement.** A globally `C²` admissible curve satisfying
`y'' - y - 1 = 0` on `(0, π/2)` agrees with the displayed extremal throughout
`[0, π/2]`.

**Proof sketch.** Set `h = y - extremal`. The compiled lemma
`apm_m99A01_extremal_ode` shows `h'' = h` in the interior, and admissibility
gives `h(0)=h(π/2)=0`. Integrate `h h'' = h²` by parts. The boundary term
vanishes, leaving `∫(h'²+h²)=0`. Its continuous nonnegative integrand is zero,
so `h=0` on the open interval; add the two endpoints from admissibility.
Alternatively, solve the homogeneous equation in the `cosh`/`sinh` basis.

**Estimate.** 120--190 lines.

**Dependencies.** Definitions and `apm_m99A01_extremal_ode`; it accepts the
residual equation explicitly and therefore can be proved independently of the
previous remaining lemma.

**Truth check.** The hand energy argument rules out every nonzero homogeneous
Dirichlet solution. The endpoint linear system also has determinant
`sinh(π/2) ≠ 0`, since `π/2 > 0`.

### `apm_m99A01_stationary_of_eqOn_extremal`

**Statement.** A globally `C²` admissible curve agreeing with the extremal on
`[0, π/2]` is stationary for the encoded functional.

**Proof sketch.** For each endpoint-zero `C¹` variation and each scalar `s`,
the varied curve agrees on the interval with `extremal + s • η`. On interior
points, local equality gives equality of derivatives via
`Filter.EventuallyEq.deriv_eq`; the endpoints form a null set. Use
`intervalIntegral.integral_congr_ae` to identify the two scalar functions of
`s`, then transport the compiled
`apm_m99A01_extremal_stationary` derivative statement.

**Estimate.** 80--140 lines.

**Dependencies.** Definitions and the already proved
`apm_m99A01_extremal_stationary`; no remaining lemma.

**Truth check.** The explicit bump near `-2` is a nontrivial test of precisely
this locality claim: it changes the global curve while leaving all values and
derivatives seen by the functional unchanged. Direct substitution shows every
variation functional is identical.

## Dependency layers

- **Layer 1 (parallel):** all three remaining lemmas. Each statement stands on
  its own from the definitions and compiled helper lemmas.
- **Layer 2:** theorem assembly. The forward implication composes
  `stationary_residual_zero` with `eqOn_extremal_of_residual_zero`; the reverse
  implication uses `stationary_of_eqOn_extremal`. The remaining three
  variational conclusions use only already proved lemmas.

## Confidence and doubt

I am convinced all three statements are mathematically true. The main
engineering risk is the first lemma: adapting compactly supported whole-line
tests to the interval-integral API and discharging dominated-differentiation
side conditions is likely the largest seat. Its proposed 220--300-line size is
near the upper end of one session, but the distributional fundamental lemma
and the a.e.-to-pointwise upgrade are already compiled, so splitting it
further would mostly expose fragile measure-theoretic plumbing rather than a
clean independent mathematical interface.

## Compile gate and axioms

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m99A01/Blueprint.lean
```

Output of `#print axioms apm_m99a01`:

```text
'apm_m99a01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The main theorem contains no `sorry`; `sorryAx` enters only through the three
named remaining lemmas.
