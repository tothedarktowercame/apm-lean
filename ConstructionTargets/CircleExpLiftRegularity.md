# Circle exponential lift regularity

This target proves that a continuous real lift `theta` of a circle-valued map
`g` is `C^n` whenever the complex-valued coercion of `g` is `C^n` and `n` is
nonzero.

At a point `x`, with `a = theta x`, the proof uses the scalar coordinate

```text
r |-> im (exp (-i a) * exp (i r)).
```

This coordinate is `sin (r - a)`, so its derivative at `a` is exactly `1`.
The corresponding coordinate of `g` is smooth by the supplied hypothesis,
and the lift equation identifies the two composites.  The generic local
inverse theorem from `ContinuousLiftLocalInverseRegularity` then transfers
regularity pointwise.

The next `t97J08` seam is proving `ContDiff` for the frozen normalized loop and
specializing the global lift to it.
