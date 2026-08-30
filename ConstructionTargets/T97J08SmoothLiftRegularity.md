# t97J08 smooth lift regularity

This target proves the analytic regularity needed to use the frozen winding
wiring with the conditional beta-integral theorem.

## Results

- `circleLoop_coe_contDiff_one`: the complex coercion of the normalized frozen
  loop is `C¹`.  The proof lowers the stored `C∞` regularity of `f`, proves the
  norm is `C¹` away from zero, coerces that norm to `ℂ`, and divides by the
  resulting nonzero smooth denominator.
- `globalLift_circleLoop_contDiff_one`: the exact frozen `circleLoop` global
  lift is `C¹`, by `CircleExpLiftRegularity.contDiff_circleExp_lift`, the
  preceding normalized-loop result, and
  `T97J08PeriodicWindingAdapter.exp_globalLift`.

The target does not import or promote `T97J08BetaWindingIntegral`, and makes no
claim about the beta integral or the final frozen theorem.
