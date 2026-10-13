# Genus-0 audit: `Surface o 0` is the closed disk, not S²

Read-only audit (2026-10-13). Fact: `SurfaceRel o 0` is empty, so `Surface true 0` and `Surface false 0` are the closed disk. Line numbers refer to `problems/<id>/lean/Main.lean`.

| id | verdict | reason (Lean line) |
|---|---|---|
| t91J05 | UNAFFECTED | Only `Surface true 3` (l.29/33) and `Surface true (2*n+1)` with `0 < n` (l.81-82) appear, so genus ≥ 3. Genus 0 never occurs. |
| t92J05 | UNAFFECTED | Fixed `Surface true 2` (l.61). S² is `Metric.sphere 0 1` in ℝ³ (l.49) and ℝP² is `Projectivization` (l.42), so neither uses the polygon model. |
| t00A02 | UNAFFECTED | Fixed `Surface true 5` (l.51). ℝP² is its own antipodal quotient of a metric sphere (l.67-77), not the polygon model. |
| t01J01 | UNAFFECTED | Fixed `Surface true 2` (l.52, used at l.178). |
| t00A03 | UNAFFECTED | `isGenusSurface g F` takes any g (l.45-47), but the theorem assumes `2 ≤ g` (l.229), matching problem.md's g ≥ 2. |
| t03J03 | UNAFFECTED | `IsOrientableSurface Y := ∃ g, Y ≃ₜ Surface true g` (l.28-31) allows g = 0. It is only a hypothesis on a 2-fold cover Y of N₃ (l.189). A closed disk cannot cover the boundaryless N₃ (a covering map is a local homeomorphism), so the g = 0 case is vacuous. S² cannot double-cover N₃ either (χ would be -2), so the intended meaning is unchanged. The explicit covers are the fixed `Surface true 2` and `Surface false 4` (l.25-26). |
| t94J04 | UNAFFECTED | Fixed `Surface true 2` (l.50, used at l.102). The statement is about subgroups of π₁ and names no genus-(k+1) surface. |
| t96A01 | UNAFFECTED | Fixed `Surface true 4` (l.20). |
| t91A02 | UNAFFECTED | `Surface false 16 → Surface false 8` (l.59-61). The axiomatised `apm_t91a02_Surface` (l.22) is a separate helper. |
| t02A02 | UNAFFECTED | `apm_t02a02_F ≃ₜ Surface false 2` (l.116). |
| t97A01 | UNAFFECTED | Only `Surface false 3` / `SurfaceRel false 3` (l.104-146). The theorem (l.171) concerns concrete spaces. |
| t94J09 | UNAFFECTED | Uses its own `apm_t94J09_N6` genus-6 quotient (l.123) and does not use `Surface` in the statement (l.279-288). |
| t01A03 | UNAFFECTED | It imports Surfaces but does not use them. Genus two is given through homology (`hasGenusTwo`, l.61-65), the torus is `Circle × Circle` (l.33) and S² is `Metric.sphere` (l.204-205). |

No registered statement here is FALSE or NARROWER. The only open genus quantifier (t03J03) appears in a hypothesis that genus 0 cannot satisfy, as a disk or as S².
