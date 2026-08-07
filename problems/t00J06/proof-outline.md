# Proof Outline: t00J06

The canonical Lean attempt is `lean/Main.lean`. It routes around surface-group
theory using a countably sheeted trivial cover.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00J06.md`

## Compiled progress

- `apm_t00J06_isCoveringMap_fst_nat` constructs a global trivialization and
  proves `S × ℕ → S` is a covering map.
- `apm_t00J06_fst_nat_fiber_infinite` injects `ℕ` into every projection fiber.
- The theorem uses `ULift (S × ℕ)` as the existential total space.  The map is
  `x ↦ x.down.1`, and `IsCoveringMap.comp_homeomorph Homeomorph.ulift`
  transports the compiled trivial-cover proof into the required universe.
- Each lifted fiber contains the injective image `n ↦ ULift.up (s, n)`.
- The continuous lift is the universe-lifted zero section
  `x ↦ ULift.up (f x, 0)`.

There is no remaining proof boundary and `lean/Main.lean` contains no `sorry`.
