# Refutation of `apm_m02j05`

The frozen theorem is false because its functions are `AEEqFun`s modulo
Lebesgue measure on all of `ℝ`, while `K`, `L`, and the Luxemburg functional
only inspect the interval `[0,1]`.

The compiled file `Counterexample.lean` defines

```text
outside(x) = max (x - 1) 0.
```

This function is zero almost everywhere on `[0,1]`, so for every `α` it lies
in `apm_m02J05_L α` and its Luxemburg functional is zero. It is nevertheless
nonzero as an element of `ℝ →ₘ[volume] ℝ`, since it is positive on `(1,∞)`.
Thus the claimed definiteness equivalence

```text
lux α u = 0 ↔ u = 0
```

fails.

The final theorem in `Counterexample.lean` also chooses `α = id` and `β = id`
and proves that all eight hypotheses of `apm_m02j05` hold simultaneously while
the definiteness conjunct is false. Hence the universal implication in the
frozen statement cannot be proved in consistent Lean.

Validation:

```text
cd /home/joe/code/apm-lean
lake env lean /tmp/solve-loop/m02J05/Counterexample.lean
```

This exits successfully. A scan found no `sorry`, `admit`, `axiom`, `opaque`,
or `native_decide` in the counterexample.

A structural repair would quotient functions only by almost-everywhere equality
for `volume.restrict (Icc 0 1)`, or require representatives to vanish outside
`[0,1]`. Merely adding integrability to the Luxemburg sublevel set does not fix
this mismatch.
