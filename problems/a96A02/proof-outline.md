# Proof Outline: a96A02

## Problem

f piecewise linear on [0,1] with f(0)=0, f(1/n)=0, f(midpoint_n)=1/n.
(a) |f(x)-f(y)| ≤ A|x-y|^{1/2} (Hölder-1/2).
(b) f not absolutely continuous.

## Proved lemma

- `spike_base_length`: |1/n - 1/(n+1)| = 1/(n(n+1)) (field_simp + ring).

## Theory boundaries (3 sorries)

1. `spike_height_slope_bound`: (1/n)·2(n+1) ≤ 4 — trivial but division API friction.
2. `spikeFunction_holderWith` (part a): Hölder-1/2 bound. Needs spike function def.
3. `spikeFunction_not_absolutelyContinuous` (part b): non-AC. Needs interval collection.

Main obstacle: defining the piecewise linear spike function with infinitely many pieces.

## Checked Lean state

- `lake env lean problems/a96A02/lean/Main.lean`: exit 0
- Sorry count: 3
- Classification: partial
