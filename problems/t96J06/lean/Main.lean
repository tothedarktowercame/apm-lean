import Mathlib

/-!
# APM t96J06 — the mod-two self-intersection obstruction

## Statement repairs

None.

## Encoding note

The projective product is represented at the exact intersection-theory layer
requested by the hint: its mod-two middle homology, the class of
`ℝP¹ × ℝP¹`, the intersection pairing, and the boundary-class map.
-/

theorem apm_t96j06 :
    ∀ (H₂ C₃ : Type*) [AddCommGroup H₂] [Module (ZMod 2) H₂]
      (z : H₂) (intersection : H₂ →ₗ[ZMod 2] H₂ →ₗ[ZMod 2] ZMod 2)
      (boundaryClass : C₃ → H₂),
      (∀ w, intersection (boundaryClass w) (boundaryClass w) = 0) →
      intersection z z = 1 →
      ¬ ∃ w : C₃, boundaryClass w = z := by
  sorry
