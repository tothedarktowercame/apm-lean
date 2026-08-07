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
  constructor
  · constructor
    · rintro ⟨T, hT⟩
      letI : Module.Free R T := inferInstance
      -- Reuse `Submodule.quotientEquivOfIsCompl` from Mathlib's projection API.
      exact Module.Free.of_equiv (S.quotientEquivOfIsCompl T hT).symm
    · intro hfree
      letI : Module.Free R (M ⧸ S) := hfree
      letI : Module.Projective R (M ⧸ S) := Module.Projective.of_free
      -- Projectivity splits the canonical quotient map; its section's range
      -- supplies the required internal lattice complement.
      obtain ⟨i, hi⟩ := S.mkQ.exists_rightInverse_of_surjective S.range_mkQ
      refine ⟨LinearMap.range i, isCompl_iff.mpr ⟨?_, ?_⟩⟩
      · rw [disjoint_iff_inf_le]
        intro x hx
        have hxS := hx.1
        have hxT := hx.2
        obtain ⟨z, rfl⟩ := hxT
        have hz : S.mkQ (i z) = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hxS
        have hiz : S.mkQ (i z) = z := by
          simpa only [LinearMap.comp_apply, LinearMap.id_apply] using DFunLike.congr_fun hi z
        have : z = 0 := hiz.symm.trans hz
        subst z
        simp
      · rw [codisjoint_iff]
        apply top_unique
        intro x _
        rw [Submodule.mem_sup]
        refine ⟨x - i (S.mkQ x), ?_, i (S.mkQ x), ⟨_, rfl⟩, sub_add_cancel _ _⟩
        rw [← Submodule.Quotient.mk_eq_zero, ← S.mkQ_apply, map_sub,
          show S.mkQ (i (S.mkQ x)) = S.mkQ x from DFunLike.congr_fun hi (S.mkQ x), sub_self]
  · constructor
    · intro hfree
      letI : Module.Free R (M ⧸ S) := hfree
      letI : Module.IsTorsionFree R (M ⧸ S) := inferInstance
      intro x hx a y ha hxy
      apply (Submodule.Quotient.mk_eq_zero S).mp
      have hzero : a • (S.mkQ y) = 0 := by
        rw [← map_smul, ← hxy]
        exact (Submodule.Quotient.mk_eq_zero S).mpr hx
      exact (smul_eq_zero.mp hzero).resolve_left ha
    · intro hsat
      -- The custom saturation predicate is exactly torsion-freeness of `M/S`.
      letI : Module.IsTorsionFree R (M ⧸ S) :=
        Module.IsTorsionFree.of_smul_eq_zero fun a z hz ↦ by
          obtain ⟨y, rfl⟩ := S.mkQ_surjective z
          by_cases ha : a = 0
          · exact Or.inl ha
          · right
            apply (Submodule.Quotient.mk_eq_zero S).mpr
            apply hsat (a • y) ((Submodule.Quotient.mk_eq_zero S).mp ?_) a y ha rfl
            simpa only [map_smul] using hz
      -- Reuse the finite torsion-free iff free theorem for PID modules.
      exact Module.free_iff_isTorsionFree.mpr inferInstance
