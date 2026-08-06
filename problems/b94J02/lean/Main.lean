import Mathlib

/-!
# APM b94J02

## Statement repairs

None.

## Encoding questions

In part (c), matrix rank is a natural number while trace lies in `K`; the
printed equality is therefore encoded as equality with the natural-number cast
`(D.rank : K)`, valid in arbitrary characteristic.
-/

theorem apm_b94j02 :
    ∀ (n : ℕ) (K : Type*) [Field K]
      (A C D : Matrix (Fin n) (Fin n) K),
      0 < n →
      (∀ m : ℕ, 0 < m → A ^ m = 0 → Matrix.trace A = 0) ∧
      ((∀ B : Matrix (Fin n) (Fin n) K, Matrix.trace (B * C) = 0) → C = 0) ∧
      (D ^ 2 = D → Matrix.trace D = (D.rank : K)) := by
  intro n K _ A C D hn
  refine ⟨?_, ?_, ?_⟩
  · /- PASS-1 boundary: searched `Matrix.charpoly`, the trace coefficient
       lemmas, minimal-polynomial divisibility, and nilpotent-matrix APIs.  The
       intended route is to show a matrix annihilated by `X ^ m` has
       characteristic polynomial `X ^ n`, then read off its trace.  I could
       not complete the required minimal/characteristic-polynomial bridge over
       an arbitrary field in pass 1. -/
    sorry
  · intro h
    ext i j
    let B : Matrix (Fin n) (Fin n) K :=
      fun r s ↦ if r = j then (if s = i then 1 else 0) else 0
    have hij := h B
    simp [B, Matrix.trace, Matrix.mul_apply] at hij
    exact hij
  · /- PASS-1 boundary: searched the matrix-rank, range/kernel decomposition,
       basis change, and trace-similarity APIs.  The intended proof decomposes
       `K^n` as `range D ⊕ ker D`, where an idempotent acts by identity and
       zero, then computes trace in an adapted basis.  I could not connect
       `Matrix.rank` to the cardinality of that identity block and transport
       the trace back through `LinearMap.toMatrix` within pass 1. -/
    sorry
