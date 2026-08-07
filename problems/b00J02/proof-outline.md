# Proof Outline: b00J02

The canonical Lean attempt is `lean/Main.lean`, with one documented boundary.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b00J02.md`

## Verified route and current blocker

- The closer-hop-2 relay's zero-sorry count was stale: direct inspection of
  baseline `9f8ad918` shows the original sorry.
- Historical commit `30f7282` closed the exact theorem with `native_decide`.
  Re-running it on Lean 4.29-rc8 caused sustained host contention and did not
  finish within this closer hop, so it was not committed as a fresh proof.
- A resource-efficient proof should reduce matrices modulo two, prove that
  invertibility is detected by this reduction, count each fiber as `2^9`, and
  use `Matrix.card_GL_field` to compute `|GL₃(F₂)| = 168`.
