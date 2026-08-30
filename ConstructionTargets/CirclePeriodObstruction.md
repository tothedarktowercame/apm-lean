# Circle period obstruction

This target proves the remaining global calculation for the frozen `t98A05`
one-form without using winding numbers or a Stokes theorem.

The explicit curve is

```lean
t ↦ (cos t, sin t, 0).
```

Its derivative is `(-sin t, cos t, 0)`.  Substitution into the specified form
`x dy - y dx` gives the constant integrand `1`, hence period `2π`.  If the
restricted form were the differential of a global real function on the
circle, the frozen derivative condition and the fundamental theorem of
calculus would instead make this integral equal to the potential's endpoint
difference.  The parametrization has equal endpoints, so that difference is
zero, contradicting `π > 0`.

The definitions `IsAlpha`, `IsRestriction`, and `IsDifferential` reproduce the
corresponding frozen interfaces generically because standalone problem files
are not Lake-importable modules.  `circle_not_differential` therefore has the
same mathematical inputs and conclusion as the remaining frozen bridge, with
no assumed period value, nonexactness statement, winding classification, or
Stokes theorem.
