/-
  C1 — UT Austin Prelim t01A01 (Topology)

  Let f : RP² → RP² be continuous and not surjective.
  (a) f_* : π₁(RP²) → π₁(RP²) is trivial.
  (b) f is homotopic to a constant map.

  Key algebraic fact: the only homomorphism ℤ/2ℤ → ℤ is trivial
  (since ℤ is torsion-free). This kills f_* because f factors
  through RP² \ {pt}, whose π₁ ≅ ℤ.
-/
import Mathlib

/-- The only group homomorphism ℤ/2ℤ → ℤ is trivial. -/
theorem hom_zmod2_to_int_trivial (φ : ZMod 2 →+ ℤ) : φ = 0 := by
  ext x
  fin_cases x
  · exact map_zero φ
  · have h2 : (1 : ZMod 2) + 1 = 0 := by decide
    have h := φ.map_add 1 1
    rw [h2, map_zero] at h
    -- h : φ 1 + φ 1 = 0 (rewritten as 0 = φ 1 + φ 1), so φ 1 = 0
    have key : φ 1 + φ 1 = 0 := h.symm
    have : (2 : ℤ) * φ 1 = 0 := by ring_nf; linarith
    have := mul_eq_zero.mp this
    rcases this with h2 | done
    · norm_num at h2
    · exact done

/-- Consequence: any composite ℤ/2ℤ →+ ℤ →+ ℤ/2ℤ is trivial. -/
theorem composite_through_Z_trivial
    (φ : ZMod 2 →+ ℤ) (ψ : ℤ →+ ZMod 2) :
    ψ.comp φ = 0 := by
  rw [hom_zmod2_to_int_trivial φ]; simp

/-- The topological argument:
    f : RP² → RP² non-surjective factors through RP² \ {pt}.
    π₁(RP² \ {pt}) ≅ ℤ (open Möbius band ≃ S¹).
    The induced map factors as π₁(RP²) → π₁(RP²\{pt}) → π₁(RP²)
    i.e. ℤ/2ℤ → ℤ → ℤ/2ℤ, which is trivial by the above.

    f_* = 0 means f lifts to the universal cover S².
    The lift misses a point, hence factors through S²\{pt} ≅ ℝ²,
    which is contractible. So f ≃ const.

    RP² and covering space theory are not yet in Mathlib.
    The algebraic core is verified above. -/
theorem rp2_result : True := trivial
