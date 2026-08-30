# t97J08 periodic winding adapter

This target constructs the existence half of the frozen periodic winding
classification in circle-valued form.

For a continuous `2π`-periodic `g : ℝ → Circle`, it chooses an initial real
argument and uses Mathlib's simply-connected-domain covering lift to obtain a
global continuous `globalLift : ℝ → ℝ`.  The endpoint exponential equation
and `CircleWindingUniqueness` determine a unique integer `winding` over one
period.  Covering uniqueness then proves the seam equation

```
globalLift (t + 2π) = globalLift t + winding * 2π.
```

Consequently the straight-line lift-coordinate interpolation between
`globalLift t` and `winding * t` exponentiates to a continuous periodic
homotopy.  Its zero end is `g`, and its one end is the standard winding loop.

The frozen predicate stores values as complex numbers of norm one.  Coercing
this target's `Circle` values to `ℂ` supplies those norm equations directly.
The remaining frozen-file wiring is the routine construction of the
continuous circle-valued normalized loop from
`t97J08_norm_normalizedLoop`; uniqueness of arbitrary supplied frozen
homotopy witnesses uses `PeriodicCircleHomotopyWinding` after restricting and
rescaling `[0,2π] × [0,1]` to the unit square.
