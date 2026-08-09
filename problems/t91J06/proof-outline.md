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
- `apm_t91J06_exists_pair_mem_stage_interior` proves any two points occur in
  one common later interior chart, providing the directed comparison needed
  for a prospective global order.

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

## Hop 4 bridge contracts

- `apm_t91J06_bridge_compatible_stage_coordinates` states the missing
  orientation and extension construction as a compatible family of
  homeomorphisms from stage `n` onto `[-(n+1), n+1]`.
- `apm_t91J06_bridge_glue_compatible_stage_coordinates` states that such a
  family glues, under the cover and weak-topology hypotheses, to a
  homeomorphism `X ≃ₜ ℝ`.

The first bridge feeds directly into the second, whose conclusion is exactly
the frozen theorem's conclusion.
