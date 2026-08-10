import Mathlib

/-!
# Schwarz--Pick rigidity on the unit disk

This file packages the elementary disk Möbius transformation and the standard
consequence that a holomorphic disk self-map with two distinct fixed points is
the identity.  The norm-square and disk-preservation layer is adapted from the
compiled `a94A09` frame work at commit `721ec14c`.
-/

open Complex Metric Set
open scoped ComplexConjugate

noncomputable section

namespace ConstructionTargets.SchwarzPick

def diskMobius (a u : ℂ) : ℂ :=
  (u - a) / (1 - conj a * u)

def diskMobiusInv (a v : ℂ) : ℂ :=
  (v + a) / (1 + conj a * v)

theorem diskMobius_normSq_identity (a u : ℂ) :
    normSq (1 - conj a * u) - normSq (u - a) =
      (1 - normSq a) * (1 - normSq u) := by
  simp only [normSq_apply, sub_re, sub_im, one_re, one_im, conj_re, conj_im,
    mul_re, mul_im, neg_mul, zero_sub]
  ring

theorem diskMobius_den_ne_zero
    {a u : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hu : u ∈ ball 0 1) :
    1 - conj a * u ≠ 0 := by
  intro h
  have hone : conj a * u = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖a‖ * ‖u‖ = 1 := by
    have := congrArg norm hone
    simpa [norm_mul] using this
  have halt : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  have hult : ‖u‖ < 1 := by simpa [mem_ball_zero_iff] using hu
  by_cases ha0 : a = 0
  · subst a
    simp at hnorm
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hprod : ‖a‖ * ‖u‖ < 1 := calc
    ‖a‖ * ‖u‖ < ‖a‖ * 1 := mul_lt_mul_of_pos_left hult hapos
    _ < 1 := by simpa using halt
  linarith

theorem diskMobius_mem_ball
    {a u : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hu : u ∈ ball 0 1) :
    diskMobius a u ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, diskMobius, norm_div]
  rw [div_lt_one (norm_pos_iff.mpr (diskMobius_den_ne_zero ha hu))]
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
  have haSq : normSq a < 1 := by
    rw [normSq_eq_norm_sq]
    nlinarith [show ‖a‖ < 1 by simpa [mem_ball_zero_iff] using ha, norm_nonneg a]
  have huSq : normSq u < 1 := by
    rw [normSq_eq_norm_sq]
    nlinarith [show ‖u‖ < 1 by simpa [mem_ball_zero_iff] using hu, norm_nonneg u]
  nlinarith [diskMobius_normSq_identity a u]

theorem diskMobiusInv_mem_ball
    {a v : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hv : v ∈ ball 0 1) :
    diskMobiusInv a v ∈ ball (0 : ℂ) 1 := by
  have hneg : -a ∈ ball (0 : ℂ) 1 := by simpa [mem_ball_zero_iff] using ha
  simpa [diskMobiusInv, diskMobius, map_neg]
    using diskMobius_mem_ball hneg hv

theorem one_sub_conj_mul_self_ne_zero {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    1 - conj a * a ≠ 0 := by
  intro h
  have heq : conj a * a = 1 := (sub_eq_zero.mp h).symm
  have hnorm := congrArg norm heq
  have halt : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  simp only [norm_mul, norm_conj, norm_one] at hnorm
  nlinarith [norm_nonneg a]

theorem diskMobiusInv_denominator (a u : ℂ)
    (hden : 1 - conj a * u ≠ 0) :
    1 + conj a * diskMobius a u =
      (1 - conj a * a) / (1 - conj a * u) := by
  rw [diskMobius]
  field_simp [hden]
  ring

theorem diskMobius_add_center (a u : ℂ)
    (hden : 1 - conj a * u ≠ 0) :
    diskMobius a u + a =
      u * (1 - conj a * a) / (1 - conj a * u) := by
  have hden' : 1 - u * conj a ≠ 0 := by simpa [mul_comm] using hden
  rw [diskMobius]
  field_simp [hden, hden']
  ring

theorem diskMobiusInv_diskMobius
    {a u : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hu : u ∈ ball 0 1) :
    diskMobiusInv a (diskMobius a u) = u := by
  have hden := diskMobius_den_ne_zero ha hu
  have hden' : 1 - u * conj a ≠ 0 := by simpa [mul_comm] using hden
  have hself := one_sub_conj_mul_self_ne_zero ha
  rw [diskMobiusInv, diskMobiusInv_denominator a u hden,
    diskMobius_add_center a u hden]
  field_simp [hden, hden', hself]

theorem diskMobius_diskMobiusInv
    {a v : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hv : v ∈ ball 0 1) :
    diskMobius a (diskMobiusInv a v) = v := by
  have hneg : -a ∈ ball (0 : ℂ) 1 := by simpa [mem_ball_zero_iff] using ha
  simpa [diskMobiusInv, diskMobius, map_neg]
    using diskMobiusInv_diskMobius hneg hv

theorem diskMobius_zero (a : ℂ) : diskMobius a a = 0 := by
  simp [diskMobius]

theorem diskMobiusInv_zero (a : ℂ) : diskMobiusInv a 0 = a := by
  simp [diskMobiusInv]

theorem differentiableOn_diskMobius (a : ℂ)
    (ha : a ∈ ball (0 : ℂ) 1) :
    DifferentiableOn ℂ (diskMobius a) (ball 0 1) := by
  intro u hu
  apply DifferentiableAt.differentiableWithinAt
  have hnum : DifferentiableAt ℂ (fun x : ℂ ↦ x - a) u := by fun_prop
  have hden : DifferentiableAt ℂ (fun x : ℂ ↦ 1 - conj a * x) u := by fun_prop
  exact hnum.div hden (diskMobius_den_ne_zero ha hu)

theorem differentiableOn_diskMobiusInv (a : ℂ)
    (ha : a ∈ ball (0 : ℂ) 1) :
    DifferentiableOn ℂ (diskMobiusInv a) (ball 0 1) := by
  have heq : diskMobiusInv a = diskMobius (-a) := by
    funext v
    simp [diskMobiusInv, diskMobius, map_neg]
  rw [heq]
  exact differentiableOn_diskMobius (-a)
    (by simpa [mem_ball_zero_iff] using ha)

/-- **Schwarz--Pick fixed-point rigidity.** A holomorphic self-map of the open
unit disk with two distinct fixed points is the identity. -/
theorem eq_id_of_two_fixed_points
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmap : MapsTo f (ball 0 1) (ball 0 1))
    {z w : ℂ} (hz : z ∈ ball 0 1) (hw : w ∈ ball 0 1)
    (hzw : z ≠ w) (hfz : f z = z) (hfw : f w = w) :
    EqOn f id (ball 0 1) := by
  let phi : ℂ → ℂ := diskMobius z
  let psi : ℂ → ℂ := diskMobiusInv z
  let h : ℂ → ℂ := fun v ↦ phi (f (psi v))
  have hpsi : MapsTo psi (ball (0 : ℂ) 1) (ball 0 1) :=
    fun _ hv ↦ diskMobiusInv_mem_ball hz hv
  have hphi : MapsTo phi (ball (0 : ℂ) 1) (ball 0 1) :=
    fun _ hv ↦ diskMobius_mem_ball hz hv
  have hmaps : MapsTo h (ball (0 : ℂ) 1) (ball 0 1) := by
    intro v hv
    exact hphi (hmap (hpsi hv))
  have hdiff : DifferentiableOn ℂ h (ball (0 : ℂ) 1) := by
    intro v hv
    have hinner := (hf _ (hpsi hv)).comp v
      (differentiableOn_diskMobiusInv z hz _ hv) hpsi
    exact (differentiableOn_diskMobius z hz _ (hmap (hpsi hv))).comp v
      hinner (hmap.comp hpsi)
  have hzero : h 0 = 0 := by
    simp [h, phi, psi, diskMobiusInv_zero, hfz, diskMobius_zero]
  let b : ℂ := phi w
  have hb : b ∈ ball (0 : ℂ) 1 := hphi hw
  have hb0 : b ≠ 0 := by
    intro hbzero
    have heq := congrArg psi hbzero
    have hleft : psi (phi w) = w := diskMobiusInv_diskMobius hz hw
    have hright : psi 0 = z := diskMobiusInv_zero z
    exact hzw (hleft.symm.trans (heq.trans hright)).symm
  have hbfix : h b = b := by
    change phi (f (psi (phi w))) = phi w
    dsimp [phi, psi]
    rw [diskMobiusInv_diskMobius hz hw, hfw]
  have hslope : dslope h 0 b = 1 := by
    rw [dslope_of_ne _ hb0]
    simp [slope_def_module, hzero, hbfix, hb0]
  have hslope_norm : ‖dslope h 0 b‖ = (1 : ℝ) / 1 := by
    simp [hslope]
  have hclosed : MapsTo h (ball (0 : ℂ) 1) (closedBall (h 0) 1) := by
    intro v hv
    rw [hzero]
    exact ball_subset_closedBall (hmaps hv)
  have haffine := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
    hdiff hclosed hb hslope_norm
  have hid : EqOn h id (ball (0 : ℂ) 1) := by
    intro v hv
    simpa [hzero, hslope] using haffine hv
  intro x hx
  have hv : phi x ∈ ball (0 : ℂ) 1 := hphi hx
  have hh := hid hv
  change phi (f (psi (phi x))) = phi x at hh
  dsimp [phi, psi] at hh
  rw [diskMobiusInv_diskMobius hz hx] at hh
  have hfx : f x ∈ ball (0 : ℂ) 1 := hmap hx
  have := congrArg psi hh
  dsimp [psi] at this
  rw [diskMobiusInv_diskMobius hz hfx,
    diskMobiusInv_diskMobius hz hx] at this
  simpa using this

end ConstructionTargets.SchwarzPick
