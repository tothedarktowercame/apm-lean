import ConstructionTargets.T94A08AffineChartHomeomorph

open Set Topology
noncomputable section

namespace T94A08AffineSmoothConicParam

abbrev AffineConic := {z : ℂ × ℂ // 1 + z.1 ^ 2 + z.2 ^ 2 = 0}
abbrev Cstar := {a : ℂ // a ≠ 0}

/-- The exact affine representation needed for the smooth-conic chart.
The equations fix both orientations of the intended homeomorphism. -/
structure AffineConicParametrization where
  homeomorph : AffineConic ≃ₜ Cstar
  forward_eq : ∀ z, (homeomorph z).1 = z.1.1 + Complex.I * z.1.2
  inverse_fst_eq : ∀ a, (homeomorph.symm a).1.1 = (a.1 - a.1⁻¹) / 2
  inverse_snd_eq : ∀ a, (homeomorph.symm a).1.2 =
    (a.1 + a.1⁻¹) / (2 * Complex.I)

lemma affineConic_factor (z : AffineConic) :
    (z.1.1 + Complex.I * z.1.2) * (z.1.1 - Complex.I * z.1.2) = -1 := by
  calc
    _ = z.1.1 ^ 2 + z.1.2 ^ 2 := by
      ring_nf
      rw [Complex.I_sq]
      ring
    _ = -1 := by linear_combination z.2

def toCstar (z : AffineConic) : Cstar := ⟨z.1.1 + Complex.I * z.1.2, by
  intro h
  have hf := affineConic_factor z
  rw [h, zero_mul] at hf
  norm_num at hf⟩

def fromCstar (a : Cstar) : AffineConic :=
  ⟨((a.1 - a.1⁻¹) / 2, (a.1 + a.1⁻¹) / (2 * Complex.I)), by
    field_simp [a.2, Complex.I_ne_zero]
    ring_nf
    rw [Complex.I_sq]
    ring⟩

@[simp] theorem toCstar_fromCstar (a : Cstar) : toCstar (fromCstar a) = a := by
  apply Subtype.ext
  change (a.1 - a.1⁻¹) / 2 + Complex.I * ((a.1 + a.1⁻¹) / (2 * Complex.I)) = a.1
  field_simp [a.2, Complex.I_ne_zero]
  ring

theorem affineConic_inverse_formula (z : AffineConic) :
    (z.1.1 + Complex.I * z.1.2)⁻¹ = -(z.1.1 - Complex.I * z.1.2) := by
  apply inv_eq_of_mul_eq_one_left
  calc
    -(z.1.1 - Complex.I * z.1.2) * (z.1.1 + Complex.I * z.1.2) =
        -((z.1.1 + Complex.I * z.1.2) * (z.1.1 - Complex.I * z.1.2)) := by ring
    _ = 1 := by rw [affineConic_factor]; norm_num

@[simp] theorem fromCstar_toCstar (z : AffineConic) : fromCstar (toCstar z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · change ((z.1.1 + Complex.I * z.1.2) - (z.1.1 + Complex.I * z.1.2)⁻¹) / 2 = z.1.1
    rw [affineConic_inverse_formula]
    ring
  · change ((z.1.1 + Complex.I * z.1.2) + (z.1.1 + Complex.I * z.1.2)⁻¹) /
      (2 * Complex.I) = z.1.2
    rw [affineConic_inverse_formula]
    field_simp [Complex.I_ne_zero]
    ring

def affineConicHomeomorphCstar : AffineConic ≃ₜ Cstar where
  toFun := toCstar
  invFun := fromCstar
  left_inv := fromCstar_toCstar
  right_inv := toCstar_fromCstar
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).add
      (continuous_const.mul (continuous_snd.comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact ((continuous_subtype_val.sub
        (continuous_subtype_val.inv₀ (fun a => a.2))).div_const 2)
    · exact ((continuous_subtype_val.add
        (continuous_subtype_val.inv₀ (fun a => a.2))).div_const (2 * Complex.I))

def affineConicParametrization : AffineConicParametrization where
  homeomorph := affineConicHomeomorphCstar
  forward_eq := fun _ => rfl
  inverse_fst_eq := fun _ => rfl
  inverse_snd_eq := fun _ => rfl

end T94A08AffineSmoothConicParam
