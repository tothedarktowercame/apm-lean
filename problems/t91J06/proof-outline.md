# Proof Outline: t91J06

The frozen theorem is encoded in `lean/Main.lean`. Its embedded interval
images have been bundled as `apm_t91J06_stage`; they form a compact monotone
exhaustion of the ambient space.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t91J06.md`

## Remaining boundary

- orient each stage compatibly with its predecessor;
- extend a chosen stage coordinate across the two complementary pieces of the
  next interval;
- glue the compatible coordinates into a bijection `X → ℝ`;
- prove continuity of the glued map using `hweak`, and continuity of its
  inverse using the compact exhaustion of `ℝ`.

Mathlib provides compact-exhaustion and compactly-generated-space APIs, but no
theorem constructs the compatible interval coordinates or performs this
direct-limit gluing.
