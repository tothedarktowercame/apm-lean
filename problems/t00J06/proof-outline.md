# Proof Outline: t00J06

The canonical Lean attempt is `lean/Main.lean`. It routes around surface-group
theory using a countably sheeted trivial cover.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00J06.md`

## Compiled progress

- `apm_t00J06_isCoveringMap_fst_nat` constructs a global trivialization and
  proves `S × ℕ → S` is a covering map.
- `apm_t00J06_fst_nat_fiber_infinite` injects `ℕ` into every projection fiber.
- The intended lift is the continuous zero section `x ↦ (f x, 0)`.

## Remaining boundary

The frozen existential quantifies its total-space universe independently.
Transport the compiled trivial cover through `ULift`, including its topology,
covering-map proof, infinite fibers, and continuous zero-section lift. No
packaged `IsCoveringMap` universe-lift theorem was found.
