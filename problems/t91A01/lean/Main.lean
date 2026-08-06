import Mathlib

/-!
# APM t91A01 — an index-three zero and the Poincaré–Hopf obstruction

## Statement repairs

None.

## Encoding note

Part (a) is encoded by the standard complex model `z ↦ z³`: its only zero is
the origin and its direction on the unit circle is `θ ↦ exp (3 i θ)`.  Part
(b) records exactly the finite-index conclusion of Poincaré–Hopf together with
the classification formula `χ = 2 - 2g`; this avoids pretending that Mathlib
already has a developed index theory for vector fields on surfaces.
-/

def apm_t91a01_vectorField (z : ℂ) : ℂ := z ^ 3

theorem apm_t91a01 :
    (∀ z : ℂ, apm_t91a01_vectorField z = 0 ↔ z = 0) ∧
    (∀ θ : ℝ,
      apm_t91a01_vectorField (Complex.exp (Complex.I * (θ : ℂ))) =
        Complex.exp (Complex.I * ((3 * θ : ℝ) : ℂ))) ∧
    ∀ (α : Type*) [DecidableEq α] (zeros : Finset α) (index : α → ℤ)
      (genus : ℕ) (p : α),
      (∑ q ∈ zeros, index q) = 2 - 2 * (genus : ℤ) →
      p ∈ zeros → index p = 3 →
      ∃ q ∈ zeros, q ≠ p := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    simp [apm_t91a01_vectorField]
  · intro θ
    simp only [apm_t91a01_vectorField]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  · intro α _ zeros index genus p hsum hp hip
    by_contra hother
    push_neg at hother
    have hzeros : zeros = {p} := by
      ext q
      constructor
      · intro hq
        have hqp := hother q hq
        simpa [hqp]
      · intro hq
        have hqp : q = p := by simpa using hq
        simpa [hqp] using hp
    rw [hzeros] at hsum
    simp [hip] at hsum
    omega
