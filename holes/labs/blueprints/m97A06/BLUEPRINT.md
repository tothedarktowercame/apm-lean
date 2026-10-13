# Blueprint for m97A06

## Triage

Verdict: **true and faithful**.

The formal theorem covers all four requested parts:

1. stationarity under endpoint-preserving smooth variations is equivalent to
   the Euler–Lagrange equation;
2. the mechanical energy is constant along a classical solution;
3. the zero path solves the Euler–Lagrange equation (and plainly has both
   endpoint values zero);
4. the second directional derivative of the action at the zero path is the
   stated Hessian.

The assumptions `0 < T`, `ContDiffOn ℝ 2 φ` for classical Euler–Lagrange
solutions, and `ContDiffOn ℝ 1 η` for Hessian directions make explicit the
regularity and nondegenerate interval used by the informal calculation.  The
source's endpoint values `α, β` do not appear as parameters in the
stationarity equivalence because endpoint-preserving variations are encoded by
`η 0 = η T = 0`; the Euler–Lagrange equation is independent of the fixed
values.  Part (c) specializes both values to zero.

I tried the main degeneracies:

* `T = 0` is excluded, as needed by the interval and fundamental-lemma
  arguments.
* The constant zero path makes both sides of the Euler–Lagrange equation zero.
* The zero variation makes both sides of the Hessian identity zero.
* Constant nonzero paths satisfy the encoded Euler–Lagrange equation only when
  `sin (2c) = 0`, matching the informal differential equation.
* At interval endpoints the equation is asserted only on `Ioo 0 T`, while
  energy constancy is extended continuously to `Icc 0 T`; this avoids an
  invalid two-sided derivative claim at an endpoint.

No counterexample was recorded.  The canonical obstruction file concerns an
older statement whose Hessian clause quantified over unrestricted functions,
including nonmeasurable and nonsquare-integrable directions.  The current
statement repairs exactly that defect by requiring `ContDiffOn ℝ 1 η`; the
repair is explicitly documented in `Main.lean` and agrees with the source's
continuously differentiable function class.

## Remaining lemmas

**None (0).**

The current canonical `problems/m97A06/lean/Main.lean` is byte-for-byte equal
to the best cached solve-loop file and already proves the theorem without
`sorry`.  `Blueprint.lean` therefore preserves all completed lemmas and the
completed main proof.  Introducing artificial admitted lemmas would discard
proved work and would violate the instruction to reuse it.

The completed proof is already factored into reusable top-level results:

* `apm_m97A06_energy_hasDerivAt_zero` and
  `apm_m97A06_energy_constant` handle conservation of energy.
* `apm_m97A06_firstVariation_hasDerivAt`,
  `apm_m97A06_integrationByParts`, the bump-function test lemma, and
  `apm_m97A06_fundamental_lemma` prove both directions of the stationary/EL
  equivalence.
* `apm_m97A06_kinetic_secondDeriv`,
  `apm_m97A06_potential_derivs`, and the almost-everywhere conversion from
  `derivWithin` to `deriv` prove the Hessian formula.

## Dependency layers

There are no open seats and hence no dependency layers of admitted work.  The
theorem is complete.

## Checks of the analytic steps

The first-variation formula differentiates under the integral using an
integrable continuous bound on the compact interval.  The converse direction
uses a compactly supported `ContDiffBump` around any interior point where the
continuous residual has a strict sign.  For the Hessian, continuity of `η` on
`Icc 0 T` makes `η²` integrable, permitting two dominated differentiations of
the cosine term.  Direct scalar differentiation gives

`d²/de² (-cos (2 e η)/4)|_{e=0} = η²`,

and the kinetic term gives `(deriv η)²`.  These hand computations match the
integrands in `apm_m97a06_hessian`.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m97A06/Blueprint.lean
```

The final output of `#print axioms apm_m97a06` was:

```text
'apm_m97a06' depends on axioms: [propext, Classical.choice, Quot.sound]
```

In particular, `sorryAx` is absent.
