import Mathlib

/-!
# APM t01A01

## Statement repairs

None.

## Encoding questions

The real projective plane is encoded as the actual projectivization of `ℝ³`
with quotient topology. Triviality of the induced fundamental-group map is
stated at every basepoint; its codomain is based at `f x`, as required for a
not-necessarily-basepoint-preserving map.
-/

open scoped LinearAlgebra.Projectivization

abbrev apm_t01A01_RP2 := Projectivization ℝ (Fin 3 → ℝ)

noncomputable instance : TopologicalSpace apm_t01A01_RP2 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ (Fin 3 → ℝ))))

theorem apm_t01a01 :
    ∀ f : C(apm_t01A01_RP2, apm_t01A01_RP2),
      ¬Function.Surjective f →
      (∀ (x : apm_t01A01_RP2) (γ : FundamentalGroup apm_t01A01_RP2 x),
        FundamentalGroup.map f x γ = 1) ∧
      ∃ p : apm_t01A01_RP2,
        ContinuousMap.Homotopic f (ContinuousMap.const _ p) := by
  intro f hnot_surj
  have hfactor : ∃ q : apm_t01A01_RP2,
      ∃ g : C(apm_t01A01_RP2, {y : apm_t01A01_RP2 // y ≠ q}),
        ∀ x, (g x : apm_t01A01_RP2) = f x := by
    obtain ⟨q, hq⟩ : ∃ q : apm_t01A01_RP2, ∀ x, f x ≠ q := by
      simpa [Function.Surjective] using hnot_surj
    refine ⟨q, ⟨fun x ↦ ⟨f x, hq x⟩, ?_⟩, ?_⟩
    · exact f.continuous.subtype_mk _
    · intro x
      rfl
  /-
  Boundary: factorization through the complement of a missed point is proved
  above. Completing the frozen theorem requires the specific topology of real
  projective space: `RP² \ {q}` deformation retracts to `RP¹ ≃ S¹`,
  `π₁(RP²) ≃ ZMod 2`, and the circle's universal-cover lifting criterion.
  I searched Mathlib's `Projectivization`, `FundamentalGroup`, homotopy,
  covering-map lifting, sphere/circle, and quotient APIs. None of those
  projective-space computations or the punctured-plane deformation retraction
  is available, so the factorization cannot presently be converted into the
  two requested conclusions without a substantial new topology development.
  The partial siblings `t00J07` and `t92J05` confirm that the required `RP²`
  fundamental-group and cell-attachment computations are not packaged; the
  wedge-cover sibling `t98A03` is blocked by the same quotient-space gap. No
  relevant bridge occurs in `ConstructionTargets/` or `YoungL2.lean`.
  -/
  sorry
