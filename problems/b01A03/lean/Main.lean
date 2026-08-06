import Mathlib

noncomputable section

/-!
# APM b01A03

## Statement repairs

The typographical phrase "principle ideal domain" is repaired to the standard
"principal ideal domain"; no mathematical hypothesis is changed.

## Encoding notes

`apmComplemented S` uses an internal lattice complement `IsCompl S T`, which is
equivalent to the direct-sum conditions `S ⊓ T = ⊥` and `S ⊔ T = ⊤`.
The quotient is the genuine quotient module `M ⧸ S`.
-/

def apmComplemented {R M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (S : Submodule R M) : Prop :=
  ∃ T : Submodule R M, IsCompl S T

def apmSaturated {R M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (S : Submodule R M) : Prop :=
  ∀ (x : M), x ∈ S →
    ∀ (a : R) (y : M), a ≠ 0 → x = a • y → y ∈ S

theorem apm_b01a03
    (R M : Type*)
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (S : Submodule R M) :
    (apmComplemented S ↔ Module.Free R (M ⧸ S)) ∧
      (Module.Free R (M ⧸ S) ↔ apmSaturated S) := by
  sorry
