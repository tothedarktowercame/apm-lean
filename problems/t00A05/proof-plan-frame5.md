# Frame 5 plan: close the angular-density period

The remaining target is

```lean
∫ t in Set.Icc (0 : ℝ) (2 * Real.pi),
  apm_t00a05_angularDensity γ t = 2 * Real.pi
```

The direct composite through `squareAngle` is periodic and has endpoint
change zero (`apm_t00a05_direct_squareAngle_endpoint_change_zero`).  The
argument below therefore uses the punctured chart to order the crossings and
uses local angle primitives on the resulting arcs.  The `2π` appears only in
the telescope across the seam; it is never asserted as the endpoint change of
the periodic composite.

1. **Unique preimages away from the duplicated endpoint.**

   ```lean
   lemma apm_t00a05_radialized_unique_on_Ico
       (hγ : apm_t00a05_IsC2 γ) {r} (hr : r ∈ Metric.sphere 0 1) :
       ∃! t : {t // t ∈ Set.Ico (0 : ℝ) (2 * Real.pi)},
         apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1) = r
   ```

   Obtain existence from `apm_t00a05_C2_radialized_surjOn`, moving a witness
   at `2π` to `0` using closedness.  Obtain uniqueness from
   `apm_t00a05_C2_radialized_injOn`.

2. **Canonical crossing parameters.** Define the unique `Ico` preimages of
   the four corners `(1,-1)`, `(1,1)`, `(-1,1)`, `(-1,-1)` and record their
   radial equalities, interval membership, distinctness, and the corresponding
   signs of the original `(x,y)` coordinates.  This upgrades
   `apm_t00a05_C2_has_four_corner_crossings` from unordered existential data to
   reusable canonical witnesses.

3. **Cyclic order from the punctured chart.** Apply
   `apm_t00a05_simple_loop_chart_monotone` to the radialized curve.  For its
   cut `β`, rotate the four perimeter coordinates and use strict monotonicity
   (or strict antitonicity) to show that their canonical times occur in one of
   exactly two cyclic orders.  Package the result as:

   ```lean
   lemma apm_t00a05_corner_order_dichotomy (hγ : apm_t00a05_IsC2 γ) :
     CounterclockwiseCornerOrder γ ∨ ClockwiseCornerOrder γ
   ```

   Here each order structure contains an increasing five-point subdivision of
   `[0,2π]`; the fifth point is the first corner repeated across the temporal
   seam.  No global real-valued angle is introduced.

4. **Coordinate nonvanishing on each ordered arc.** Use continuity plus the
   rotated-chart order and uniqueness of the four axis preimages from
   `apm_t00a05_C2_has_four_axis_crossings` to prove the alternating `x ≠ 0` and
   `y ≠ 0` hypotheses required by
   `apm_t00a05_angularDensity_integral_of_x_ne_zero` and
   `apm_t00a05_angularDensity_integral_of_y_ne_zero`.

5. **Counterclockwise telescope.** Apply those two FTC lemmas to the four
   arcs, split the `Icc` integral with `intervalIntegral.integral_add_adjacent`,
   substitute the corner signs/radial ratios, and simplify with
   `Real.arctan_one` and `Real.arctan_neg`.  Prove:

   ```lean
   lemma apm_t00a05_angular_period_of_ccw
       (hγ : apm_t00a05_IsC2 γ) (hord : CounterclockwiseCornerOrder γ) :
       ∫ t in Set.Icc 0 (2 * Real.pi),
         apm_t00a05_angularDensity γ t = 2 * Real.pi
   ```

6. **Clockwise telescope.** The same four local formulas in reverse cyclic
   order give `-2π`:

   ```lean
   lemma apm_t00a05_angular_period_of_cw
       (hγ : apm_t00a05_IsC2 γ) (hord : ClockwiseCornerOrder γ) :
       ∫ t in Set.Icc 0 (2 * Real.pi),
         apm_t00a05_angularDensity γ t = -(2 * Real.pi)
   ```

7. **Orientation exclusion from signed area.** On every non-axis local arc,
   the existing primitive-derivative lemmas identify angular density with the
   derivative of the corresponding local angle.  Clockwise chart order makes
   that primitive antitone; `AntitoneOn.deriv_nonpos` (or its pointwise
   `HasDerivAt` consequence) gives angular density `≤ 0` away from the finitely
   many axis crossings.  Since

   ```lean
   x * y' - y * x' = (x^2 + y^2) * apm_t00a05_angularDensity γ
   ```

   and `x²+y² > 0` on the level set, the signed-area integrand is nonpositive
   almost everywhere.  Its integral is therefore `≤ 0`, contradicting the
   positive signed-area conjunct of `hγ`.  Package this as:

   ```lean
   lemma apm_t00a05_not_clockwise
       (hγ : apm_t00a05_IsC2 γ) : ¬ ClockwiseCornerOrder γ
   ```

8. **Final assembly.** Eliminate the clockwise branch of step 3 with step 7,
   apply step 5, and discharge the remaining conjunct of `apm_t00a05` through
   `apm_t00a05_lineIntegral_eq_neg_angular`.

If step 7's library monotone-derivative lemma is unavailable at this pin, the
fallback is its elementary difference-quotient proof from `HasDerivAt`: the
sign of every nonzero difference quotient follows from antitonicity, and the
derivative sign follows by the limit.  This changes no mathematical interface.

## Revision after the first landings

Steps 1–2 survived contact: canonical `Ico` preimages, their uniqueness,
separation, perimeter coordinates, and original-coordinate signs are now
formal.  The signed-area identity and the final contradiction from an
everywhere nonpositive angular density are also formal.

Step 3 needs one refinement.  Applying the punctured chart at the original
parameter origin leaves a special case when a chosen corner is itself at time
zero.  Rather than proliferating endpoint cases, cyclically rebase the
*topological ordering argument* at the canonical `(-1,-1)` crossing.  This is
only a continuous piecewise translation of the parameter interval and is used
to order points; it does not reparametrize the differentiable curve in the
integral.  After deriving the cyclic inequalities, split and reorder the
original interval integrals algebraically.  This keeps all FTC applications on
the original `γ`, so no derivative-matching assumption at the temporal seam is
introduced.

I also checked the general covering-map/path-lift API (`Circle.isCoveringMap_exp`
and `IsCoveringMap.liftPath`).  It supplies a continuous angle lift, but proving
that this merely continuous lift is differentiable would recreate the local
chart work already completed.  The canonical-crossing/FTC route therefore
remains the shorter formal route at this pin.

## Progress boundary for the first frame-5 siege

The following plan interfaces now compile:

- unique canonical half-open-period preimages of every square-sphere point;
- a reusable canonical crossing-time definition and specification;
- distinct sphere points have distinct canonical crossing times;
- positive radial scaling transfers both coordinate signs to the original
  curve;
- exact perimeter coordinates `0,2,4,6` for the four corners;
- signed-area density equals positive radius-squared times angular density;
- positive signed area implies a positive angular-density witness in the open
  period, hence a positive derivative of one of the two compiled local angle
  primitives.

The next lemma is now sharply local: under the `StrictAntiOn` branch returned
by `apm_t00a05_simple_loop_chart_monotone`, the applicable local angle
primitive is antitone on a neighborhood of that positive-derivative witness.
The witness lies in `Ioo`; injectivity keeps it away from the temporal cut, and
its nonzero coordinate selects the `x` or `y` chart.  Composing local
antitonicity with `HasDerivAt.nonpos_of_antitoneOn` contradicts the proved
positive derivative.  This will eliminate the clockwise branch without any
global-angle endpoint assertion.  After that, only cyclically sorting the four
canonical corner times and applying the existing FTC telescope remains.

## Attempt-2 revision: the seam-corrected lift now exists

The local-only formulation above exposed a cleaner reusable object.  The file
now defines

```lean
apm_t00a05_squareAngleFrom β u =
  if u ≤ 8 - β then squareAngle (u + β)
  else squareAngle (u + β - 8) + 2π
```

This is the missing path lift.  The explicit `+2π` is the seam correction
whose absence made the naive composition periodic.  It is now proved:

- continuous on `ℝ`;
- strictly increasing on `[0,8]`;
- endpoint change exactly `2π`;
- explicitly computable after `rot β`;
- it transfers an antitone rotated chart into an antitone lifted angle.

The chart dichotomy now retains the provenance equation saying its cut decodes
to the initial radialized point, and injectivity proves every interior time is
away from that cut.  Thus the earlier structural gap is closed rather than
handled by temporal endpoint cases.

The remaining analytic lemma is now:

```lean
-- locally at every interior time
deriv (fun t => squareAngleFrom β
  (rot β (squarePerimeter (radialized γ t)))) t
  = apm_t00a05_angularDensity γ t
```

It will be proved chartwise by showing the lifted angle differs by a constant
from the already-compiled `atan (y/x)` or `-atan (x/y)` primitive.  Once this
lands, the antitone branch contradicts
`apm_t00a05_exists_local_angle_deriv_pos` immediately, and the monotone branch
can use FTC on the lift itself (or equivalently the four existing arc lemmas)
to obtain its proved `2π` endpoint change.  This route eliminates the separate
manual corner-sort/telescope step from the original plan.

## Attempt-3 boundary: pointwise chart identities are complete

The radial part of that analytic lemma is now formalized.  Positive gauge
scaling preserves both coordinate ratios, and on each of the four open square
edges the raw square angle of the radialized curve is proved equal to the
corresponding original-curve primitive plus its explicit branch constant:

- right: `atan (y/x) + 2π`;
- left: `atan (y/x) + 3π`;
- bottom: `-atan (x/y) + 3π/2`;
- top: `-atan (x/y) + 5π/2`.

The remaining brick is no longer an algebraic identity.  It is the
neighborhood upgrade needed by `deriv`: continuity of the radialized curve,
the strict open-edge inequalities, sphere membership on the period, and
avoidance of the rotated cut must be combined to show that one of these four
pointwise identities holds *eventually at* each interior non-corner time, with
the seam-correction branch fixed.  `Filter.EventuallyEq.deriv_eq` then turns
the existing primitive derivative lemmas into the desired lift derivative.
This is the sharp current boundary; no ratio, branch-constant, or radial-scale
algebra remains behind it.

## Attempt-4 boundary: orientation is now formally resolved

The neighborhood upgrade is complete on all four open edges.  Each local
identity now yields the actual derivative equality by
`Filter.EventuallyEq.deriv_eq`, and hence there is a machine-checked interior
point where the raw radial square angle has positive derivative.  A second
local argument proves that the seam-corrected lift has the same derivative at
that point.  This excludes the strictly antitone branch using
`AntitoneOn.derivWithin_nonpos`; consequently
`apm_t00a05_C2_radialized_chart_strictMono` now proves the positive traversal
orientation outright.

The sole remaining task is the global FTC assembly.  In the now-proved
strictly increasing order, split at the four canonical corner witnesses,
apply the existing `x ≠ 0` and `y ≠ 0` arc-integral lemmas, and telescope their
explicit `atan (±1)` endpoint values.  There is no longer an orientation
dichotomy or an unproved local derivative bridge in that step.
