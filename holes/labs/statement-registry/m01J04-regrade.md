# m01J04 statement regrade (2026-10-15)

Context: reopened 5e475969d (smoothness order ⊤ = ω -> ∞); the proof closed on lemmas (7a0246f96) but the statement was never re-admitted.

Grader (read-only Claude subagent, claude-14 2026-10-15), first pass on the ∞-statement: **narrower**.
- (a) faithful; (b) faithful under the disclosed HasRellichProperty repair (b is false on unbounded domains: bump translates with a bounded ψ summing ∇(bump²) over disjoint translates).
- (c) narrower: it inherited HasRellichProperty from the shared binder, but the div-curl statement holds on every open Ω (local Rellich on a ball around tsupport φ, strong × weak; H⁻¹ pairing for the f_nφ term).
- Definitions: all ContDiff orders are ∞; H1 is genuine H¹(Ω), isH1Zero = H¹₀(Ω), divStronglyConverges equivalent to strong H⁻¹ convergence (the limit must be div v); no vacuity.

Repair: Rellich guards (b) only; (c) gets `IsOpen Ω` and `tsupport φ ⊆ Ω` (φ ∈ C_c^∞(Ω)).
Second pass on the repaired statement: **faithful** (cosmetic only: isTestFunction's support conjunct now redundant).
Consequence: (c) is open again (needs local Rellich); (a), (b) proved.
