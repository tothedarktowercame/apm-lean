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
  · intro m hm hAm
    exact (Matrix.isNilpotent_trace_of_isNilpotent ⟨m, hAm⟩).eq_zero
  · intro h
    ext i j
    let B : Matrix (Fin n) (Fin n) K :=
      fun r s ↦ if r = j then (if s = i then 1 else 0) else 0
    have hij := h B
    simp [B, Matrix.trace, Matrix.mul_apply] at hij
    exact hij
  · intro hD
    let f : Module.End K (Fin n → K) := Matrix.toLin' D
    have hf : IsIdempotentElem f := by
      change f * f = f
      dsimp [f]
      rw [Module.End.mul_eq_comp]
      rw [← Matrix.toLin'_mul]
      simpa [pow_two] using congrArg Matrix.toLin' hD
    have hp : LinearMap.IsProj (LinearMap.range f) f :=
      (LinearMap.isProj_range_iff_isIdempotentElem f).2 hf
    have ht := hp.trace
    rw [Matrix.trace_toLin'_eq] at ht
    rw [D.rank_eq_finrank_range_toLin (Pi.basisFun K (Fin n))
      (Pi.basisFun K (Fin n)), Matrix.toLin_eq_toLin']
    exact ht
