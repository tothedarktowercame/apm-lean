# T03J06 final adapter

`bulletIntegral_eq_seven_pi` joins the two completed scalar surface
calculations.  Its hypotheses are the pointwise pullback identities already
proved by the frozen substitutions:

- the cylinder pullback is `cylinderIntegrand`;
- the hemisphere pullback is `hemisphereIntegrand`.

The theorem invokes the existing pointwise adapters to derive `4π` and `3π`
and then proves their sum is `7π`.  Neither component value nor the final value
is an assumption.

`full_conjunction_of_frozen_helpers` packages this result with four arbitrary
proved local propositions in the same five-conjunct shape as the frozen
theorem: smoothness, the exterior-derivative value, exterior-derivative
nonvanishing, nonexactness, and the bullet integral.

The abstraction of the first four propositions is an import boundary, not a
mathematical gap.  Their concrete declarations and the pointwise pullback
lemmas live in `problems/t03J06/lean/Main.lean`, which is compiled standalone
and is not a Lake-importable module.  Reproducing its form definitions here
would create a second incompatible copy.  At the frozen theorem, those
existing helpers instantiate the four propositions and the two pointwise
equalities directly.
