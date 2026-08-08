# Proof Outline: m96A06

The frozen theorem has a compiling partial Lean development.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m96A06.md`

## Compiled progress

- Products of two `L²` representatives, the forcing pairing, and the weighted
  `L∞ × L² × L²` expression are proved integrable.
- `apm_m96a06_eLpNorm_weighted_le` proves the raw multiplier estimate
  `‖a*f‖₂ ≤ ‖a‖∞ * ‖f‖₂`.
- `apm_m96a06_forceCLM` packages an arbitrary `L²` forcing term as a
  continuous linear functional on quotient `Lp`, and its application lemma
  identifies it with the exact representative-level integral.
- `apm_m96a06_forceOnH` composes that functional with `value`, completing the
  right-hand side of the weak problem as a continuous linear map on `H`.
- `apm_m96a06_multiplier` descends a raw `MemLp a ⊤` coefficient through
  `ha.toLp a` and heterogeneous `Lp` multiplication; its a.e. representative
  and quotient norm bound are compiled.
- `apm_m96a06_multiplierCLM` specializes Mathlib's Hölder continuous bilinear
  map to package the descended multiplier as a bounded linear operator on
  quotient `L²`.

## Remaining boundary

- combine the compiled multiplier operator with
  `ContinuousLinearMap.lpPairing` to build the bounded left-hand bilinear form
  (the forcing functional is now complete);
- prove coercivity, apply Mathlib's Lax–Milgram theorem, and establish the
  representative-level Fréchet derivative formula.
