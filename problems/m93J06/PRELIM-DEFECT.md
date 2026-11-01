# Preliminary defect report: m93J06

## Failing printed claim

Part (d) says:

> Show that if \(f\) is Hölder continuous with exponent \(\alpha\), the map
> that takes \(y_0\) to \(y(t)\) is Hölder continuous with exponent
> \(\alpha\) for sufficiently small \(t\).

For \(0<\alpha<1\), Hölder continuity of the vector field in the dependent
variable does not imply uniqueness. Consequently, under the printed
hypothesis there need not be a map taking \(y_0\) to *the* value \(y(t)\).

## Complete counterexample

Take
\[
  f(t,y)=2\sqrt{|y|}.
\]
This field is globally Hölder in \(y\) with exponent \(1/2\):
\[
 |f(t,a)-f(t,b)|
 \le 2\sqrt{\bigl||a|-|b|\bigr|}
 \le 2\sqrt{|a-b|}.
\]
For the initial value \(y(0)=0\), both
\[
  y_1(t)=0
  \quad\text{and}\quad
  y_2(t)=t|t|
\]
are global classical solutions. Indeed, \(y_2'(t)=2|t|\), including at
\(t=0\), while
\[
  2\sqrt{|y_2(t)|}=2\sqrt{|t|^2}=2|t|.
\]
They have the same initial value and are distinct (for example at \(t=1\)).
More generally, the usual delayed solutions of
\(y'=|y|^\alpha\), \(y(0)=0\), give the same obstruction for every
\(0<\alpha<1\).

## Evident intent and smallest correction

The evident subject of (d) is dependence of a uniquely determined solution
on its initial value, but the text gives no definite additional uniqueness
hypothesis or parameter-dependence hypothesis. Several inequivalent repairs
are possible. For example, imposing the Lipschitz uniqueness hypothesis from
Picard--Lindelöf gives the stronger local Lipschitz estimate
\[
  |y(t;a)-y(t;b)|\le e^{L|t|}|a-b|,
\]
whereas merely adding an unrelated uniqueness assumption does not by itself
specify the claimed Hölder estimate. Thus the smallest non-inventive
correction is to replace (d) by the assertion that its printed conclusion is
false, together with the counterexample above. This is the correction used
in `apm_m93j06`.

Part (a) is underspecified as printed because it asks the solver to state the
existence-and-uniqueness theorem. Its standard reading is local: joint
continuity and local Lipschitz continuity in the state variable give a unique
solution on a neighborhood of the initial time. The uniform global Lipschitz
version in the current formal development is a useful corollary, but is not a
replacement for that local statement.

Likewise, parts (b), (c), and (e) must retain the local hypotheses of (a).
Part (b) should construct its local flow rather than assume a global one;
part (c) must use the linear-growth bound to continue the local solution for
all time; and part (e) asks how both the differentiable-dependence statement
and the proposed Hölder statement change under that growth bound. The growth
bound does not repair the nonuniqueness defect in (d). Under a genuinely
Lipschitz state hypothesis one instead has the stronger estimate
\(|\phi(t,a)-\phi(t,b)|\le e^{L|t|}|a-b|\) for every time for which the flow
exists.

## Formalized repair (current Main.lean)

- Part (d) is formalized as its own refutation (`apm_m93j06_part_d`): for the
  branching field `f(t, y) = sign y * |y|^α` (continuous, `2`-Hölder with
  exponent `α`; `apm_m93j06_powField_continuous`,
  `apm_m93j06_powField_holder`), no selection of local solutions can be
  Hölder-`α` in the initial value at arbitrarily small times.  The proof
  (`apm_m93j06_no_holder_flow_of_branch`) pins the selected solutions from
  initial values just above and below the branch point via the explicit
  formula `apm_m93j06_powField_formula` (the separation at time `t` is at
  least `2 * ((1-α) t)^{1/(1-α)} > 0`) while their initial distance tends to
  zero.
  The repaired statement is uniform in every `0 < α < 1` and is genuinely
  local in the initial value: it fixes the branch point `y₁ = 0` and rules
  out every flow on every open window around that point.  In particular, its
  Hölder estimate is only required for initial values in that window, so the
  contradiction cannot come from the identity map at `t = 0` on all of `ℝ`.
- Part (e) keeps the global `C^1` flow (`apm_m93j06_part_e_flow`) and the
  sharp Lipschitz estimate `apm_m93j06_part_e_lipschitz`, and adds
  `apm_m93j06_part_e_holder`: even under the growth bound `|f t y| ≤ C |y|`
  the Hölder-dependence claim fails.  The counterexample
  `apm_m93j06_truncField α y = ρ(y) * sign(y-1) * min(|y-1|^α, 1)` with
  `ρ(y) = min(2|y|, 1) * min(2|2-y|, 1)` is continuous, satisfies the growth
  bound with `C = 2`, is `6`-Hölder with exponent `α`, and branches at
  `y = 1`, where the same two-sided pinning argument applies.
  Here too the repaired assertion treats every `0 < α < 1`, fixes the branch
  point (`y₁ = 1`), and uses a local initial-value window.
- The assembled statement is `apm_m93j06` at the root of `Main.lean`;
  `#print axioms apm_m93j06` reports exactly `propext`, `Classical.choice`,
  `Quot.sound`.
