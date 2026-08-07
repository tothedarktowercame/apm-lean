# Proof Outline: t91J06

The frozen theorem is encoded in `lean/Main.lean`. Its embedded interval
images have been bundled as `apm_t91J06_stage`; they form a compact monotone
exhaustion of the ambient space.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t91J06.md`

## Compiled progress

- `apm_t91J06_stage_compact` and `apm_t91J06_stage_mono` give a compact
  monotone exhaustion.
- `apm_t91J06_exists_mem_stage` gives pointwise stage coverage.
- `apm_t91J06_exists_mem_stage_interior` proves every point occurs in the
  relative interior image of a later embedded interval, providing genuine
  local arc coordinates rather than endpoint-only coverage.

## Remaining boundary

- orient each stage compatibly with its predecessor;
- extend a chosen stage coordinate across the two complementary pieces of the
  next interval;
- glue the compatible coordinates into a bijection `X → ℝ`;
- prove continuity of the glued map using `hweak`, and continuity of its
  inverse using the compact exhaustion of `ℝ`.
- exploit the compiled interior coverage while making the stage coordinates
  compatible.

Mathlib provides compact-exhaustion and compactly-generated-space APIs, but no
theorem constructs the compatible interval coordinates or performs this
direct-limit gluing.
