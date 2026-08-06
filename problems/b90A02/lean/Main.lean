import Mathlib

/-!
# APM b90A02: Free, projective, and flat modules

## Statement repairs

The source permits a noncommutative unital ring and defines flatness for right
modules. Mathlib's `Module.Flat` and its tensor product currently support this
criterion only over commutative semirings (the library records noncommutative
flatness as a TODO). We therefore impose commutativity on `R`; in that setting
left and right module formulations agree.

## Encoding questions

None beyond the declared commutativity repair. Flatness is represented by
Mathlib's tensor-product-based `Module.Flat`, not by a weaker surrogate.
-/

noncomputable section

theorem apm_b90a02
    (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] :
    (Module.Free R M → Module.Flat R M) ∧
    (Module.Projective R M → Module.Flat R M) ∧
    Module.Flat ℤ ℚ ∧
    ¬Module.Projective ℤ ℚ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro
    infer_instance
  · intro
    infer_instance
  · infer_instance
  · -- Boundary: searched `Module.Flat.of_free`, `Module.Flat.of_projective`,
    -- the Dedekind/torsion-free flatness instance, projective-module lifting
    -- APIs, and PID free-module results.  The first three claims are complete.
    -- The remaining claim needs the theorem that an arbitrary (not assumed
    -- finitely generated) projective ℤ-module is free, or an equivalent direct
    -- lifting obstruction for the divisible module ℚ; the available PID
    -- submodule-freeness results located were finite-rank variants.
    sorry
