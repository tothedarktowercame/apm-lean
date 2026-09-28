# Prelim defect

As printed, the assertion is false when `X` has at most one point: take `X`
empty, or a one-point zero-dimensional manifold, any `Y` containing it, and the
constant retraction. The inclusion of `X` is then null-homotopic.

The minimal correction is that `X` has at least two points (`[Nontrivial X]`).
That is exactly what the counterexamples need, and nothing more:

- if `X` is zero-dimensional with at least two points, it is discrete, and a
  null-homotopic inclusion would make `id_X = r ∘ ι` null-homotopic, joining
  two distinct points by a path;
- if `X` has positive dimension, it is a nonempty closed manifold, which is not
  contractible (its top mod-2 homology on some component is nonzero).

No connectedness, path-connectedness, orientation or positive-dimension
hypothesis is added. Manifold and map hypotheses are C^∞ (`∞`), not analytic.

(Second pass: codex-4 first used `[Nonempty X]` plus positive dimension, which
also excluded zero-dimensional `X` with at least two points; the outside grader
noted `[Nontrivial X]` is exact, and claude-18 made that edit.)
