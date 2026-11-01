import Mathlib
import ConstructionTargets.Surfaces
import ConstructionTargets.KleinBottlePiOne

/-! # The polygon torus is the flat torus

`Surface true 1` is homeomorphic to `UnitAddCircle × UnitAddCircle`, by the `ℓ¹` chart of the disk
followed by the lattice coordinates. Moved here unchanged from `problems/t95J03` so that other
problems can use the map; `t95J03_torus_bridge_spec` records that the homeomorphism is that map. -/

open Set

noncomputable section

namespace ConstructionTargets.FlatTorusBridge

open ConstructionTargets.Surfaces

abbrev T95J03Torus := UnitAddCircle × UnitAddCircle

lemma t95J03_torus_bridge_aux_chart_neg (w : ℂ) :
    KleinSquareDiskCutAndPaste.klein_cut_chart (-w) =
      -KleinSquareDiskCutAndPaste.klein_cut_chart w := by
  by_cases hw : w = 0
  · simp [hw, KleinSquareDiskCutAndPaste.klein_cut_chart]
  · have hnw : -w ≠ 0 := by simp [hw]
    have h2 : KleinSquareDiskCutAndPaste.klein_cut_l1 (-w) =
        KleinSquareDiskCutAndPaste.klein_cut_l1 w := by
      unfold KleinSquareDiskCutAndPaste.klein_cut_l1
      simp [Complex.neg_re, Complex.neg_im]
    have h3 : ‖-w‖ = ‖w‖ := norm_neg _
    unfold KleinSquareDiskCutAndPaste.klein_cut_chart
    rw [if_neg hnw, if_neg hw, h2, h3]
    push_cast
    ring

open KleinSquareDiskCutAndPaste

lemma t95J03_torus_bridge_aux_chart_I (w : ℂ) :
    klein_cut_chart (Complex.I * w) = Complex.I * klein_cut_chart w := by
  by_cases hw : w = 0
  · simp [hw, klein_cut_chart]
  · have hnw : Complex.I * w ≠ 0 := by simpa using hw
    have h1 : (Complex.I * w).re = -w.im ∧ (Complex.I * w).im = w.re := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    have h2 : klein_cut_l1 (Complex.I * w) = klein_cut_l1 w := by
      unfold klein_cut_l1; rw [h1.1, h1.2, abs_neg]; ring
    have h3 : ‖Complex.I * w‖ = ‖w‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    unfold klein_cut_chart
    rw [if_neg hnw, if_neg hw, h2, h3]
    push_cast
    ring

lemma t95J03_torus_bridge_aux_chart_exp_coords (θ : ℝ) :
    (klein_cut_chart (Complex.exp (Complex.I * θ))).re =
      Real.cos θ / (|Real.cos θ| + |Real.sin θ|) ∧
    (klein_cut_chart (Complex.exp (Complex.I * θ))).im =
      Real.sin θ / (|Real.cos θ| + |Real.sin θ|) := by
  have h0 : Complex.exp (Complex.I * θ) ≠ 0 := Complex.exp_ne_zero _
  have hrw : klein_cut_chart (Complex.exp (Complex.I * θ)) =
      ((‖Complex.exp (Complex.I * θ)‖ / klein_cut_l1 (Complex.exp (Complex.I * θ)) : ℝ) : ℂ) *
        Complex.exp (Complex.I * θ) := by
    rw [klein_cut_chart, if_neg h0]
  have hn : ‖Complex.exp (Complex.I * θ)‖ = 1 := by
    rw [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im]; norm_num
  have hc : (Complex.exp (Complex.I * (θ : ℂ))).re = Real.cos θ ∧
      (Complex.exp (Complex.I * (θ : ℂ))).im = Real.sin θ := by
    rw [mul_comm, Complex.exp_mul_I]
    simp [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have hl : klein_cut_l1 (Complex.exp (Complex.I * θ)) =
      |Real.cos θ| + |Real.sin θ| := by
    rw [klein_cut_l1, hc.1, hc.2]
  have hpos : (0 : ℝ) < |Real.cos θ| + |Real.sin θ| := by
    by_contra h
    push_neg at h
    have hn1 : 0 ≤ |Real.sin θ| := abs_nonneg _
    have hn2 : 0 ≤ |Real.cos θ| := abs_nonneg _
    have hc0 : Real.cos θ = 0 ∧ Real.sin θ = 0 := by
      constructor <;> apply abs_eq_zero.mp <;> linarith
    have := Real.sin_sq_add_cos_sq θ
    rw [hc0.1, hc0.2] at this
    norm_num at this
  have he : Complex.exp (Complex.I * (θ : ℂ)) =
      ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  constructor
  · rw [hrw, hn, hl, he]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    push_cast
    field_simp
    ring
  · rw [hrw, hn, hl, he]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    push_cast
    field_simp
    ring

lemma t95J03_torus_bridge_aux_edge_exp (j : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    (edgePoint 4 j t : ℂ) = Complex.exp (Complex.I * (Real.pi / 2 * ((j : ℝ) + t.1))) := by
  simp only [edgePoint, Subtype.coe_mk]
  congr 1
  push_cast
  ring

-- ## AddCircle coercion API

lemma t95J03_torus_bridge_aux_coe_eq_of_int {x y : ℝ} {n : ℤ} (h : x - y = n) :
    (x : UnitAddCircle) = (y : UnitAddCircle) := by
  have h2 : ((x - y : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨n, by rw [h]; simp⟩
  rw [AddCircle.coe_sub, sub_eq_zero] at h2
  exact h2

lemma t95J03_torus_bridge_aux_int_of_coe_eq {x y : ℝ}
    (h : (x : UnitAddCircle) = (y : UnitAddCircle)) : ∃ n : ℤ, x - y = n := by
  have h2 : ((x - y : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub]; exact sub_eq_zero.mpr h
  rw [AddCircle.coe_eq_zero_iff] at h2
  obtain ⟨n, hn⟩ := h2
  exact ⟨n, by rw [← hn]; simp⟩

lemma t95J03_torus_bridge_aux_continuous_coe :
    Continuous (fun x : ℝ => (x : UnitAddCircle)) := AddCircle.continuous_mk' 1

-- ## The map to the torus

noncomputable def t95J03_torus_bridge_aux_f (z : ℂ) : T95J03Torus :=
  Prod.mk (((((klein_cut_chart z).re + (klein_cut_chart z).im) / 2 : ℝ) : UnitAddCircle))
    (((((klein_cut_chart z).re - (klein_cut_chart z).im) / 2 : ℝ) : UnitAddCircle))

lemma t95J03_torus_bridge_aux_f_continuous : Continuous t95J03_torus_bridge_aux_f := by
  unfold t95J03_torus_bridge_aux_f
  exact Continuous.prodMk
    (t95J03_torus_bridge_aux_continuous_coe.comp
      (((Complex.continuous_re.comp klein_cut_chart_continuous).add
        (Complex.continuous_im.comp klein_cut_chart_continuous)).div
        continuous_const (by intro _; norm_num)))
    (t95J03_torus_bridge_aux_continuous_coe.comp
      (((Complex.continuous_re.comp klein_cut_chart_continuous).sub
        (Complex.continuous_im.comp klein_cut_chart_continuous)).div
        continuous_const (by intro _; norm_num)))

lemma t95J03_torus_bridge_aux_exp_coords (θ : ℝ) :
    (Complex.exp (Complex.I * ((θ : ℝ) : ℂ))).re = Real.cos θ ∧
    (Complex.exp (Complex.I * ((θ : ℝ) : ℂ))).im = Real.sin θ := by
  rw [mul_comm, Complex.exp_mul_I]
  simp [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma t95J03_torus_bridge_aux_exp_norm (θ : ℝ) :
    ‖Complex.exp (Complex.I * ((θ : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re]

lemma t95J03_torus_bridge_aux_chart_quadrant (w : ℂ)
    (h1 : ‖w‖ = 1) (h2 : 0 ≤ w.re) (h3 : 0 ≤ w.im) :
    (klein_cut_chart w).re = w.re / (w.re + w.im) ∧
    (klein_cut_chart w).im = w.im / (w.re + w.im) := by
  have hw : w ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  have hne : w.re + w.im ≠ 0 := by
    intro h
    have h4 : w.re = 0 := le_antisymm (by
      have := add_nonneg h2 h3; rw [h] at this; linarith) h2
    have h5 : w.im = 0 := le_antisymm (by
      have := add_nonneg h2 h3; rw [h] at this; linarith) h3
    exact hw (by apply Complex.ext <;> simp [h4, h5])
  have hl : klein_cut_l1 w = w.re + w.im := by
    unfold klein_cut_l1; rw [abs_of_nonneg h2, abs_of_nonneg h3]
  have hrw : klein_cut_chart w = ((1 / (w.re + w.im) : ℝ) : ℂ) * w := by
    rw [klein_cut_chart, if_neg hw, h1, hl]
  constructor
  · rw [hrw, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring
  · rw [hrw, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring

lemma t95J03_torus_bridge_aux_edge0_facts (t : Set.Icc (0 : ℝ) 1) :
    ‖(edgePoint 4 0 t : ℂ)‖ = 1 ∧
    (edgePoint 4 0 t : ℂ).re = Real.cos (Real.pi / 2 * (t : ℝ)) ∧
    (edgePoint 4 0 t : ℂ).im = Real.sin (Real.pi / 2 * (t : ℝ)) := by
  obtain ⟨hc1, hc2⟩ := t95J03_torus_bridge_aux_exp_coords (Real.pi / 2 * (t : ℝ))
  have hn := t95J03_torus_bridge_aux_exp_norm (Real.pi / 2 * (t : ℝ))
  have heq : (edgePoint 4 0 t : ℂ) =
      Complex.exp (Complex.I * ((Real.pi / 2 * (t : ℝ) : ℝ) : ℂ)) := by
    rw [t95J03_torus_bridge_aux_edge_exp]
    congr 1
    norm_num
  rw [heq]
  exact ⟨hn, hc1, hc2⟩

lemma t95J03_torus_bridge_aux_edge2_as_neg (u : Set.Icc (0 : ℝ) 1) :
    (edgePoint 4 2 u : ℂ) =
      -(Complex.exp (Complex.I * ((Real.pi / 2 * (u : ℝ) : ℝ)))) := by
  have hIpi : Complex.exp (Complex.I * (Real.pi : ℝ)) = -1 := by
    rw [mul_comm, Complex.exp_mul_I]
    simp [Real.cos_pi, Real.sin_pi]
  have hmul : ∀ w : ℂ, -(Complex.exp w) =
      Complex.exp (Complex.I * (Real.pi : ℝ)) * Complex.exp w := by
    intro w; rw [hIpi]; ring
  simp only [edgePoint, Subtype.coe_mk]
  rw [hmul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma t95J03_torus_bridge_aux_edge2_facts (u : Set.Icc (0 : ℝ) 1) :
    ‖(edgePoint 4 2 u : ℂ)‖ = 1 ∧
    (edgePoint 4 2 u : ℂ).re = -Real.cos (Real.pi / 2 * (u : ℝ)) ∧
    (edgePoint 4 2 u : ℂ).im = -Real.sin (Real.pi / 2 * (u : ℝ)) := by
  obtain ⟨hc1, hc2⟩ := t95J03_torus_bridge_aux_exp_coords (Real.pi / 2 * (u : ℝ))
  have hn := t95J03_torus_bridge_aux_exp_norm (Real.pi / 2 * (u : ℝ))
  have heq : (edgePoint 4 2 u : ℂ) =
      -(Complex.exp (Complex.I * ((Real.pi / 2 * (u : ℝ) : ℝ) : ℂ))) :=
    t95J03_torus_bridge_aux_edge2_as_neg u
  rw [heq, Complex.neg_re, Complex.neg_im]
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_neg]; exact hn
  · rw [hc1]
  · rw [hc2]

lemma t95J03_torus_bridge_aux_pair02 (t : Set.Icc (0 : ℝ) 1) :
    t95J03_torus_bridge_aux_f (edgePoint 4 0 t : ℂ) =
      t95J03_torus_bridge_aux_f
        (edgePoint 4 2 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : ℂ) := by
  have hb0 : 0 ≤ Real.pi / 2 * (t : ℝ) ∧ Real.pi / 2 * (t : ℝ) ≤ Real.pi / 2 := by
    constructor
    · exact mul_nonneg (by positivity) t.2.1
    · exact mul_le_of_le_one_right (by positivity) (by have := t.2.2; linarith)
  have hb1 : 0 ≤ Real.pi / 2 * (1 - (t : ℝ)) ∧
      Real.pi / 2 * (1 - (t : ℝ)) ≤ Real.pi / 2 := by
    constructor
    · exact mul_nonneg (by positivity) (by have := t.2.1; have := t.2.2; linarith)
    · exact mul_le_of_le_one_right (by positivity)
        (by have := t.2.1; have := t.2.2; linarith)
  have hb : Real.pi / 2 * (1 - (t : ℝ)) = Real.pi / 2 - Real.pi / 2 * (t : ℝ) := by
    ring_nf
  have hcosβ : Real.cos (Real.pi / 2 * (1 - (t : ℝ))) =
      Real.sin (Real.pi / 2 * (t : ℝ)) ∧
      Real.sin (Real.pi / 2 * (1 - (t : ℝ))) =
      Real.cos (Real.pi / 2 * (t : ℝ)) := by
    rw [hb, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    exact ⟨rfl, rfl⟩
  obtain ⟨hn0, hr0, hi0⟩ := t95J03_torus_bridge_aux_edge0_facts t
  obtain ⟨hn2, hr2, hi2⟩ :=
    t95J03_torus_bridge_aux_edge2_facts
      (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1)
  have hs0 : Real.cos (Real.pi / 2 * (t : ℝ)) + Real.sin (Real.pi / 2 * (t : ℝ)) ≠ 0 := by
    have hcc : 0 ≤ Real.cos (Real.pi / 2 * (t : ℝ)) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb0.2⟩
    have hss : 0 ≤ Real.sin (Real.pi / 2 * (t : ℝ)) :=
      Real.sin_nonneg_of_mem_Icc ⟨hb0.1, by linarith [Real.pi_pos]⟩
    have h1 := Real.cos_sq_add_sin_sq (Real.pi / 2 * (t : ℝ))
    intro h
    have hc0 : Real.cos (Real.pi / 2 * (t : ℝ)) = 0 := by linarith
    have hs0' : Real.sin (Real.pi / 2 * (t : ℝ)) = 0 := by linarith
    rw [hc0, hs0'] at h1
    norm_num at h1
  have hsβ : Real.cos (Real.pi / 2 * (1 - (t : ℝ))) +
      Real.sin (Real.pi / 2 * (1 - (t : ℝ))) ≠ 0 := by
    rw [hcosβ.1, hcosβ.2]; simpa [add_comm] using hs0
  have hsc : Real.sin (Real.pi / 2 * (t : ℝ)) + Real.cos (Real.pi / 2 * (t : ℝ)) ≠ 0 := by
    rw [add_comm]; exact hs0
  -- chart coordinates on the two edges
  obtain ⟨hc0r, hc0i⟩ := t95J03_torus_bridge_aux_chart_quadrant
    (edgePoint 4 0 t : ℂ) hn0
    (by rw [hr0]; exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb0.2⟩)
    (by rw [hi0]; exact Real.sin_nonneg_of_mem_Icc ⟨hb0.1, by linarith [Real.pi_pos]⟩)
  have hneg : klein_cut_chart (edgePoint 4 2
      (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1) : ℂ) =
      -(klein_cut_chart
        (-(edgePoint 4 2
          (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1) : ℂ))) := by
    rw [t95J03_torus_bridge_aux_chart_neg]
    try simp
  obtain ⟨hcmr, hcmi⟩ := t95J03_torus_bridge_aux_chart_quadrant
    (-(edgePoint 4 2
      (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1) : ℂ))
    (by rw [norm_neg]; exact hn2)
    (by rw [Complex.neg_re, hr2, neg_neg]; exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb1.2⟩)
    (by rw [Complex.neg_im, hi2, neg_neg]; exact Real.sin_nonneg_of_mem_Icc ⟨hb1.1, by linarith [Real.pi_pos]⟩)
  -- assemble
  simp only [t95J03_torus_bridge_aux_f, Prod.mk.injEq]
  rw [hneg, Complex.neg_re, Complex.neg_im]
  rw [hc0r, hc0i, hcmr, hcmi]
  rw [Complex.neg_re, Complex.neg_im, hr0, hi0, hr2, hi2]
  rw [hcosβ.1, hcosβ.2]
  simp only [neg_neg]
  constructor
  · refine t95J03_torus_bridge_aux_coe_eq_of_int (n := 1) ?_
    field_simp [hs0, hsc]
    have hE : 2 * ((Real.cos (Real.pi / 2 * (t : ℝ)) + Real.sin (Real.pi / 2 * (t : ℝ))) *
        (Real.cos (Real.pi / 2 * (t : ℝ)) + Real.sin (Real.pi / 2 * (t : ℝ)))⁻¹) = 2 := by
      rw [mul_inv_cancel₀ hs0, mul_one]
    linear_combination (norm := ring_nf) hE
  · refine t95J03_torus_bridge_aux_coe_eq_of_int (n := 0) ?_
    push_cast
    ring_nf

lemma t95J03_torus_bridge_aux_pair13 (t : Set.Icc (0 : ℝ) 1) :
    t95J03_torus_bridge_aux_f (edgePoint 4 1 t : ℂ) =
      t95J03_torus_bridge_aux_f
        (edgePoint 4 3 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : ℂ) := by
  have hs1 := klein_cut_edge_succ t
  have hs2 := klein_cut_edge_succ
    (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1)
  have hb0 : 0 ≤ Real.pi / 2 * (t : ℝ) ∧ Real.pi / 2 * (t : ℝ) ≤ Real.pi / 2 := by
    constructor
    · exact mul_nonneg (by positivity) t.2.1
    · exact mul_le_of_le_one_right (by positivity) (by have := t.2.2; linarith)
  have hb1 : 0 ≤ Real.pi / 2 * (1 - (t : ℝ)) ∧
      Real.pi / 2 * (1 - (t : ℝ)) ≤ Real.pi / 2 := by
    constructor
    · exact mul_nonneg (by positivity) (by have := t.2.1; have := t.2.2; linarith)
    · exact mul_le_of_le_one_right (by positivity)
        (by have := t.2.1; have := t.2.2; linarith)
  have hcosβ : Real.cos (Real.pi / 2 * (1 - (t : ℝ))) =
      Real.sin (Real.pi / 2 * (t : ℝ)) ∧
      Real.sin (Real.pi / 2 * (1 - (t : ℝ))) =
      Real.cos (Real.pi / 2 * (t : ℝ)) := by
    have hb : Real.pi / 2 * (1 - (t : ℝ)) = Real.pi / 2 - Real.pi / 2 * (t : ℝ) := by
      ring_nf
    rw [hb, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    exact ⟨rfl, rfl⟩
  obtain ⟨hn0, hr0, hi0⟩ := t95J03_torus_bridge_aux_edge0_facts t
  obtain ⟨hn2, hr2, hi2⟩ := t95J03_torus_bridge_aux_edge2_facts
    (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1)
  have hs0 : Real.cos (Real.pi / 2 * (t : ℝ)) + Real.sin (Real.pi / 2 * (t : ℝ)) ≠ 0 := by
    have hcc : 0 ≤ Real.cos (Real.pi / 2 * (t : ℝ)) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb0.2⟩
    have hss : 0 ≤ Real.sin (Real.pi / 2 * (t : ℝ)) :=
      Real.sin_nonneg_of_mem_Icc ⟨hb0.1, by linarith [Real.pi_pos]⟩
    have h1 := Real.cos_sq_add_sin_sq (Real.pi / 2 * (t : ℝ))
    intro h
    have hc0 : Real.cos (Real.pi / 2 * (t : ℝ)) = 0 := by linarith
    have hs0' : Real.sin (Real.pi / 2 * (t : ℝ)) = 0 := by linarith
    rw [hc0, hs0'] at h1
    norm_num at h1
  have hsc : Real.sin (Real.pi / 2 * (t : ℝ)) + Real.cos (Real.pi / 2 * (t : ℝ)) ≠ 0 := by
    rw [add_comm]; exact hs0
  obtain ⟨hc0r, hc0i⟩ := t95J03_torus_bridge_aux_chart_quadrant
    (edgePoint 4 0 t : ℂ) hn0
    (by rw [hr0]; exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb0.2⟩)
    (by rw [hi0]; exact Real.sin_nonneg_of_mem_Icc ⟨hb0.1, by linarith [Real.pi_pos]⟩)
  obtain ⟨hcmr, hcmi⟩ := t95J03_torus_bridge_aux_chart_quadrant
    (-(edgePoint 4 2
      (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1) : ℂ))
    (by rw [norm_neg]; exact hn2)
    (by rw [Complex.neg_re, hr2, neg_neg]; exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb1.2⟩)
    (by rw [Complex.neg_im, hi2, neg_neg]; exact Real.sin_nonneg_of_mem_Icc ⟨hb1.1, by linarith [Real.pi_pos]⟩)
  simp only [t95J03_torus_bridge_aux_f, Prod.mk.injEq]
  rw [hs1.1, hs2.2, t95J03_torus_bridge_aux_chart_I, t95J03_torus_bridge_aux_chart_I]
  have he2c : klein_cut_chart (edgePoint 4 2
      (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1) : ℂ) =
      -(klein_cut_chart
        (-(edgePoint 4 2
          (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1) : ℂ))) := by
    rw [t95J03_torus_bridge_aux_chart_neg]
    try simp
  rw [he2c, mul_neg]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_neg]
  rw [hc0r, hc0i, hcmr, hcmi, Complex.neg_re, Complex.neg_im,
    hr0, hi0, hr2, hi2, hcosβ.1, hcosβ.2]
  norm_num
  constructor
  · refine t95J03_torus_bridge_aux_coe_eq_of_int (n := 0) ?_
    push_cast
    ring_nf

  · refine t95J03_torus_bridge_aux_coe_eq_of_int (n := -1) ?_
    have hB1 : (-(Real.sin (Real.pi / 2 * (t : ℝ)) /
        (Real.cos (Real.pi / 2 * (t : ℝ)) + Real.sin (Real.pi / 2 * (t : ℝ)))) -
        Real.cos (Real.pi / 2 * (t : ℝ)) /
        (Real.cos (Real.pi / 2 * (t : ℝ)) + Real.sin (Real.pi / 2 * (t : ℝ)))) = -1 := by
      have hI1 : (Real.cos (Real.pi / 2 * (t : ℝ)) + Real.sin (Real.pi / 2 * (t : ℝ))) *
          (Real.cos (Real.pi / 2 * (t : ℝ)) + Real.sin (Real.pi / 2 * (t : ℝ)))⁻¹ = 1 :=
        mul_inv_cancel₀ hs0
      linear_combination (norm := ring_nf) -1 * hI1
    have hB3 : (Real.cos (Real.pi / 2 * (t : ℝ)) /
        (Real.sin (Real.pi / 2 * (t : ℝ)) + Real.cos (Real.pi / 2 * (t : ℝ))) +
        Real.sin (Real.pi / 2 * (t : ℝ)) /
        (Real.sin (Real.pi / 2 * (t : ℝ)) + Real.cos (Real.pi / 2 * (t : ℝ)))) = 1 := by
      have hI2 : (Real.sin (Real.pi / 2 * (t : ℝ)) + Real.cos (Real.pi / 2 * (t : ℝ))) *
          (Real.sin (Real.pi / 2 * (t : ℝ)) + Real.cos (Real.pi / 2 * (t : ℝ)))⁻¹ = 1 :=
        mul_inv_cancel₀ hsc
      linear_combination (norm := ring_nf) hI2
    rw [hB1, hB3]
    push_cast
    norm_num

lemma t95J03_torus_bridge_aux_descent (x y : Disk)
    (h : SurfaceRel true 1 x y) :
    t95J03_torus_bridge_aux_f (x : ℂ) = t95J03_torus_bridge_aux_f (y : ℂ) := by
  unfold SurfaceRel at h
  simp only [if_true] at h
  obtain ⟨j, hj, t, hcase⟩ := h
  have hj0 : j = 0 := Nat.lt_one_iff.mp hj
  subst hj0
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · norm_num at h1 h2
    rw [h1, h2]
    exact t95J03_torus_bridge_aux_pair02 t
  · norm_num at h1 h2
    rw [h1, h2]
    exact t95J03_torus_bridge_aux_pair13 t

lemma t95J03_torus_bridge_aux_sound (x y : Disk)
    (h : Relation.EqvGen (SurfaceRel true 1) x y) :
    t95J03_torus_bridge_aux_f (x : ℂ) = t95J03_torus_bridge_aux_f (y : ℂ) := by
  induction h with
  | refl => rfl
  | symm _ _ h' ih => exact ih.symm
  | trans _ _ _ h1 h2 ih1 ih2 => exact ih1.trans ih2
  | rel x y hrel => exact t95J03_torus_bridge_aux_descent x y hrel

noncomputable def t95J03_torus_bridge_aux_lift : Surface true 1 → T95J03Torus :=
  Quotient.lift (fun z : Disk => t95J03_torus_bridge_aux_f (z : ℂ))
    (fun x y h => t95J03_torus_bridge_aux_sound x y h)

lemma t95J03_torus_bridge_aux_lift_continuous : Continuous t95J03_torus_bridge_aux_lift := by
  unfold t95J03_torus_bridge_aux_lift
  exact Continuous.quotient_lift
    (t95J03_torus_bridge_aux_f_continuous.comp continuous_subtype_val)
    (fun a b h => t95J03_torus_bridge_aux_sound a b h)

lemma t95J03_torus_bridge_aux_abs_le (x y : ℝ) :
    |x + y| + |x - y| ≤ 2 * max |x| |y| := by
  have hA : |x + y| ^ 2 = (x + y) ^ 2 := sq_abs _
  have hB : |x - y| ^ 2 = (x - y) ^ 2 := sq_abs _
  have hAB : |x + y| * |x - y| = |x ^ 2 - y ^ 2| := by
    rw [← abs_mul]
    congr 1
    ring
  by_cases hc : x ^ 2 ≤ y ^ 2
  · have hmy : |x ^ 2 - y ^ 2| = -(x ^ 2 - y ^ 2) := abs_of_nonpos (by linarith)
    have hm : max |x| |y| = |y| := by
      refine max_eq_right ?_
      by_cases hle : |x| ≤ |y|
      · exact hle
      · exfalso
        push_neg at hle
        have hprod : (|x| - |y|) * (|x| + |y|) = |x| ^ 2 - |y| ^ 2 := by ring
        have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
        have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
        have hpp : 0 < (|x| - |y|) * (|x| + |y|) := by
          nlinarith [hle, abs_nonneg x, abs_nonneg y]
        linarith
    have hexp : (|x + y| + |x - y|) ^ 2 = 4 * y ^ 2 := by
      have e1 : (|x + y| + |x - y|) ^ 2 =
          (|x + y|) ^ 2 + (|x - y|) ^ 2 + 2 * (|x + y| * |x - y|) := by ring
      rw [e1, hA, hB, hAB, hmy]
      ring
    have hsq : (|x + y| + |x - y|) ^ 2 ≤ (2 * max |x| |y|) ^ 2 := by
      rw [hm]
      have h4 : (2 * |y|) ^ 2 = 4 * y ^ 2 := by rw [show (2 * |y|) ^ 2 = 4 * |y| ^ 2 from by ring, sq_abs y]
      rw [h4, hexp]
    have hnn2 : 0 ≤ 2 * max |x| |y| := by positivity
    nlinarith [hsq, hnn2]
  · have hmy : |x ^ 2 - y ^ 2| = x ^ 2 - y ^ 2 := abs_of_nonneg (by linarith)
    have hm : max |x| |y| = |x| := by
      refine max_eq_left ?_
      by_cases hle : |y| ≤ |x|
      · exact hle
      · exfalso
        push_neg at hle
        have hprod : (|y| - |x|) * (|y| + |x|) = |y| ^ 2 - |x| ^ 2 := by ring
        have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
        have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
        have hpp : 0 < (|y| - |x|) * (|y| + |x|) := by
          nlinarith [hle, abs_nonneg x, abs_nonneg y]
        linarith
    have hexp : (|x + y| + |x - y|) ^ 2 = 4 * x ^ 2 := by
      have e1 : (|x + y| + |x - y|) ^ 2 =
          (|x + y|) ^ 2 + (|x - y|) ^ 2 + 2 * (|x + y| * |x - y|) := by ring
      rw [e1, hA, hB, hAB, hmy]
      ring
    have hsq : (|x + y| + |x - y|) ^ 2 ≤ (2 * max |x| |y|) ^ 2 := by
      rw [hm]
      have h4 : (2 * |x|) ^ 2 = 4 * x ^ 2 := by rw [show (2 * |x|) ^ 2 = 4 * |x| ^ 2 from by ring, sq_abs x]
      rw [h4, hexp]
    have hnn2 : 0 ≤ 2 * max |x| |y| := by positivity
    nlinarith [hsq, hnn2]

lemma t95J03_torus_bridge_aux_rep (x : UnitAddCircle) :
    ∃ r : ℝ, r ∈ Set.Icc (-(1 / 2)) (1 / 2) ∧ (r : UnitAddCircle) = x := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨c - (Int.floor (c + 1 / 2) : ℤ), ⟨?_, ?_⟩, ?_⟩
  · have hf1 : ((Int.floor (c + 1 / 2) : ℤ) : ℝ) ≤ c + 1 / 2 := Int.floor_le _
    linarith
  · have hf2 : c + 1 / 2 < (((Int.floor (c + 1 / 2) : ℤ) : ℝ) + 1) := by
      have := Int.lt_floor_add_one (c + 1 / 2)
      push_cast at this
      linarith
    linarith
  · rw [← hc]
    exact t95J03_torus_bridge_aux_coe_eq_of_int (n := -(Int.floor (c + 1 / 2) : ℤ))
      (by push_cast; simp)

lemma t95J03_torus_bridge_aux_lift_surjective :
    Function.Surjective t95J03_torus_bridge_aux_lift := by
  intro p
  obtain ⟨a, b⟩ := p
  obtain ⟨ra, hra, hca⟩ := t95J03_torus_bridge_aux_rep a
  obtain ⟨rb, hrb, hcb⟩ := t95J03_torus_bridge_aux_rep b
  have hra1 : -(1 / 2) ≤ ra := hra.1
  have hra2 : ra ≤ 1 / 2 := hra.2
  have hrb1 : -(1 / 2) ≤ rb := hrb.1
  have hrb2 : rb ≤ 1 / 2 := hrb.2
  have hra' : |ra| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hrb' : |rb| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hl1 : |ra + rb| + |ra - rb| ≤ 1 := by
    have h1 := t95J03_torus_bridge_aux_abs_le ra rb
    have h2 : max |ra| |rb| ≤ 1 / 2 := by
      exact max_le hra' hrb'
    have : 2 * max |ra| |rb| ≤ 1 := by linarith
    linarith
  set w : ℂ := ⟨ra + rb, ra - rb⟩ with hw
  have hball : klein_cut_chartInv w ∈ (Metric.closedBall (0 : ℂ) 1) := by
    rw [Metric.mem_closedBall, dist_zero_right, klein_cut_norm_chartInv, klein_cut_l1]
    show |ra + rb| + |ra - rb| ≤ 1
    exact hl1
  refine ⟨Quotient.mk _ ⟨klein_cut_chartInv w, hball⟩, ?_⟩
  have hc : klein_cut_chart (klein_cut_chartInv w) = w := klein_cut_chart_chartInv w
  have hxr : (klein_cut_chart (klein_cut_chartInv w)).re = ra + rb := by rw [hc]
  have hxi : (klein_cut_chart (klein_cut_chartInv w)).im = ra - rb := by rw [hc]
  rw [t95J03_torus_bridge_aux_lift, Quotient.lift_mk]
  have hval : t95J03_torus_bridge_aux_f (klein_cut_chartInv w) = Prod.mk a b := by
    show Prod.mk _ _ = Prod.mk a b
    have hrw1 : ((ra + rb) + (ra - rb)) / 2 = ra := by ring
    have hrw2 : ((ra + rb) - (ra - rb)) / 2 = rb := by ring
    rw [hxr, hxi, hrw1, hrw2]
    rw [Prod.mk.injEq]
    exact ⟨hca, hcb⟩
  exact hval

-- ## Injectivity

lemma t95J03_torus_bridge_aux_chart_bound (z : Disk) :
    |(klein_cut_chart (z : ℂ)).re| ≤ 1 ∧ |(klein_cut_chart (z : ℂ)).im| ≤ 1 := by
  have hn : ‖(z : ℂ)‖ ≤ 1 := by
    have h := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hl : |(klein_cut_chart (z : ℂ)).re| + |(klein_cut_chart (z : ℂ)).im| = ‖(z : ℂ)‖ :=
    klein_cut_l1_chart _
  have hre := abs_nonneg (klein_cut_chart (z : ℂ)).re
  have him := abs_nonneg (klein_cut_chart (z : ℂ)).im
  constructor <;> linarith

-- ## Injectivity: helper lemmas

lemma t95J03_torus_bridge_aux_exp_corner :
    (edgePoint 4 0 ⟨(0 : ℝ), by norm_num⟩ : ℂ) = 1 ∧
    (edgePoint 4 2 ⟨(1 : ℝ), by norm_num⟩ : ℂ) = -Complex.I ∧
    (edgePoint 4 1 ⟨(0 : ℝ), by norm_num⟩ : ℂ) = Complex.I ∧
    (edgePoint 4 3 ⟨(1 : ℝ), by norm_num⟩ : ℂ) = 1 ∧
    (edgePoint 4 1 ⟨(1 : ℝ), by norm_num⟩ : ℂ) = -1 ∧
    (edgePoint 4 3 ⟨(0 : ℝ), by norm_num⟩ : ℂ) = -Complex.I := by
  have hI : Complex.exp (Complex.I * (((Real.pi : ℝ) : ℂ) / 2)) = Complex.I := by
    rw [mul_comm, Complex.exp_mul_I]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  have hIpi : Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ)) = -1 := by
    rw [mul_comm]; exact Complex.exp_pi_mul_I
  have hstep3 : Complex.exp (Complex.I * (((Real.pi : ℝ) : ℂ) / 2 * 3)) = -Complex.I := by
    rw [show ((Real.pi : ℝ) : ℂ) / 2 * 3 =
        ((Real.pi : ℝ) : ℂ) + ((Real.pi : ℝ) : ℂ) / 2 from by
      field_simp
      ring]
    rw [mul_add, Complex.exp_add]
    rw [show Complex.I * ((Real.pi : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) * Complex.I from mul_comm _ _,
      Complex.exp_pi_mul_I, hI]
    norm_num
  have hbridge : ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) / 2 := by
    rw [Complex.ofReal_div]
    norm_num
  constructor
  · rw [t95J03_torus_bridge_aux_edge_exp]
    norm_num
    try simp
  · constructor
    · rw [t95J03_torus_bridge_aux_edge_exp]
      norm_num
      rw [hstep3]
    · constructor
      · rw [(klein_cut_edge_succ ⟨(0 : ℝ), by norm_num⟩).1]
        rw [t95J03_torus_bridge_aux_edge_exp]
        norm_num
        try rw [Complex.exp_zero]
        try simp
      · constructor
        · rw [(klein_cut_edge_succ ⟨(1 : ℝ), by norm_num⟩).2]
          rw [t95J03_torus_bridge_aux_edge_exp]
          norm_num
          rw [hstep3]
          norm_num
        · constructor
          · rw [(klein_cut_edge_succ ⟨(1 : ℝ), by norm_num⟩).1]
            rw [t95J03_torus_bridge_aux_edge_exp]
            norm_num
            rw [hI]
            norm_num
          · rw [(klein_cut_edge_succ ⟨(0 : ℝ), by norm_num⟩).2]
            rw [t95J03_torus_bridge_aux_edge_exp]
            norm_num
            rw [hIpi]
            norm_num

lemma t95J03_torus_bridge_aux_angle_of_sin {a b : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ Real.pi / 2)
    (hb : 0 ≤ b) (hb2 : b ≤ Real.pi / 2) (h : Real.sin (b - a) = 0) : a = b := by
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
  push_cast at hk
  have hbd1 : b - a ≤ Real.pi / 2 := by linarith [hb2, ha]
  have hbd2 : -(Real.pi / 2) ≤ b - a := by linarith [ha2, hb]
  have hk0 : k = 0 := by
    by_contra h0
    by_cases hh : 1 ≤ k
    · have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hh
      nlinarith [Real.pi_pos, hk, hbd1]
    · have hk' : k ≤ -1 := by omega
      have h1 : (k : ℝ) ≤ -1 := by exact_mod_cast hk'
      nlinarith [Real.pi_pos, hk, hbd2]
  rw [hk0] at hk
  push_cast at hk
  linarith

lemma t95J03_torus_bridge_aux_g_inj {a b : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ Real.pi / 2)
    (hb : 0 ≤ b) (hb2 : b ≤ Real.pi / 2)
    (h : Real.cos a - Real.sin a = Real.cos b - Real.sin b) : a = b := by
  have hca : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], ha2⟩
  have hsa : 0 ≤ Real.sin a := Real.sin_nonneg_of_mem_Icc ⟨ha, by linarith [Real.pi_pos]⟩
  have hcb : 0 ≤ Real.cos b := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb2⟩
  have hsb : 0 ≤ Real.sin b := Real.sin_nonneg_of_mem_Icc ⟨hb, by linarith [Real.pi_pos]⟩
  have h1 := Real.cos_sq_add_sin_sq a
  have h2 := Real.cos_sq_add_sin_sq b
  have hsq : (Real.cos a + Real.sin a) ^ 2 = (Real.cos b + Real.sin b) ^ 2 := by
    have e1 : (Real.cos a + Real.sin a) ^ 2 + (Real.cos a - Real.sin a) ^ 2 =
        2 * (Real.cos a ^ 2 + Real.sin a ^ 2) := by ring
    have e2 : (Real.cos b + Real.sin b) ^ 2 + (Real.cos b - Real.sin b) ^ 2 =
        2 * (Real.cos b ^ 2 + Real.sin b ^ 2) := by ring
    rw [h1] at e1
    rw [h2] at e2
    have hPQ : (Real.cos a - Real.sin a) ^ 2 = (Real.cos b - Real.sin b) ^ 2 := by rw [h]
    linarith [e1, e2, hPQ]
  have hS : Real.cos a + Real.sin a = Real.cos b + Real.sin b := by
    have hprod : (Real.cos a + Real.sin a - (Real.cos b + Real.sin b)) *
        (Real.cos a + Real.sin a + (Real.cos b + Real.sin b)) = 0 := by
      have e3 : (Real.cos a + Real.sin a - (Real.cos b + Real.sin b)) *
          (Real.cos a + Real.sin a + (Real.cos b + Real.sin b)) =
          (Real.cos a + Real.sin a) ^ 2 - (Real.cos b + Real.sin b) ^ 2 := by ring
      rw [e3, hsq]
      ring
    have hsumpos : 0 < Real.cos a + Real.sin a + (Real.cos b + Real.sin b) := by
      by_contra hc0
      push_neg at hc0
      have e1 : Real.cos a + Real.sin a = 0 := by linarith [hca, hsa, hcb, hsb, hc0]
      have e2 : Real.cos b + Real.sin b = 0 := by linarith [hca, hsa, hcb, hsb, hc0]
      have hza : Real.cos a = 0 := by nlinarith [hca, hsa, e1]
      have hzb : Real.sin a = 0 := by nlinarith [hca, hsa, e1]
      rw [hza, hzb] at h1
      norm_num at h1
    nlinarith [hprod, hsumpos]
  have hcc : Real.cos a = Real.cos b := by linarith
  have hss : Real.sin a = Real.sin b := by linarith
  refine t95J03_torus_bridge_aux_angle_of_sin ha ha2 hb hb2 ?_
  rw [Real.sin_sub, hcc, hss]
  ring

lemma t95J03_torus_bridge_aux_val_inj {a b : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ Real.pi / 2)
    (hb : 0 ≤ b) (hb2 : b ≤ Real.pi / 2)
    (hne1 : Real.cos a + Real.sin a ≠ 0) (hne2 : Real.cos b + Real.sin b ≠ 0)
    (h : (Real.cos a - Real.sin a) / (Real.cos a + Real.sin a) =
      (Real.cos b - Real.sin b) / (Real.cos b + Real.sin b)) : a = b := by
  have hcross : (Real.cos a - Real.sin a) * (Real.cos b + Real.sin b) =
      (Real.cos b - Real.sin b) * (Real.cos a + Real.sin a) :=
    (div_eq_div_iff hne1 hne2).mp h
  refine t95J03_torus_bridge_aux_angle_of_sin ha ha2 hb hb2 ?_
  rw [Real.sin_sub]
  have e : (Real.cos a - Real.sin a) * (Real.cos b + Real.sin b) -
      (Real.cos b - Real.sin b) * (Real.cos a + Real.sin a) =
      2 * (Real.sin b * Real.cos a - Real.cos b * Real.sin a) := by ring
  have h2 : 2 * (Real.sin b * Real.cos a - Real.cos b * Real.sin a) = 0 := by
    linarith [hcross, e]
  linarith

lemma t95J03_torus_bridge_aux_edge1_of (z : ℂ) (h1 : ‖z‖ = 1) (hre : z.re ≤ 0)
    (him : 0 ≤ z.im) : ∃ t : Set.Icc (0 : ℝ) 1, z = edgePoint 4 1 t := by
  have hw : ‖-(Complex.I * z)‖ = 1 := by
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
    exact h1
  have hwr : (-(Complex.I * z)).re = z.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  have hwi : (-(Complex.I * z)).im = -z.re := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_im]
  have hball : (-(Complex.I * z)) ∈ (Metric.closedBall (0 : ℂ) 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hw.le
  have hwz : ‖((⟨-(Complex.I * z), hball⟩ : Disk) : ℂ)‖ = 1 := hw
  have hwrz : 0 ≤ ((⟨-(Complex.I * z), hball⟩ : Disk) : ℂ).re := by
    show 0 ≤ (-(Complex.I * z)).re
    rw [hwr]
    exact him
  have hwiz : 0 ≤ ((⟨-(Complex.I * z), hball⟩ : Disk) : ℂ).im := by
    show 0 ≤ (-(Complex.I * z)).im
    rw [hwi]
    exact neg_nonneg.mpr hre
  obtain ⟨t, ht⟩ := (klein_cut_edge_zero_iff (⟨-(Complex.I * z), hball⟩ : Disk)).mpr
    ⟨hwz, hwrz, hwiz⟩
  refine ⟨t, ?_⟩
  have hte : -(Complex.I * z) = (edgePoint 4 0 t : ℂ) := Subtype.ext_iff.mp ht
  have hzI : z = Complex.I * (-(Complex.I * z)) := by
    rw [mul_neg, ← mul_assoc, Complex.I_mul_I, neg_one_mul, neg_neg]
  rw [hzI, hte, (klein_cut_edge_succ t).1]

lemma t95J03_torus_bridge_aux_edge3_of (z : ℂ) (h1 : ‖z‖ = 1) (hre : 0 ≤ z.re)
    (him : z.im ≤ 0) : ∃ t : Set.Icc (0 : ℝ) 1, z = edgePoint 4 3 t := by
  have hw : ‖-(Complex.I * z)‖ = 1 := by
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
    exact h1
  have hwr : (-(Complex.I * z)).re = z.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  have hwi : (-(Complex.I * z)).im = -z.re := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_im]
  have hball : (-(Complex.I * z)) ∈ (Metric.closedBall (0 : ℂ) 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hw.le
  have hwz : ‖((⟨-(Complex.I * z), hball⟩ : Disk) : ℂ)‖ = 1 := hw
  have hwrz : ((⟨-(Complex.I * z), hball⟩ : Disk) : ℂ).re ≤ 0 := by
    show (-(Complex.I * z)).re ≤ 0
    rw [hwr]
    exact him
  have hwiz : ((⟨-(Complex.I * z), hball⟩ : Disk) : ℂ).im ≤ 0 := by
    show (-(Complex.I * z)).im ≤ 0
    rw [hwi]
    exact neg_nonpos.mpr hre
  obtain ⟨t, ht⟩ := (klein_cut_edge_two_iff (⟨-(Complex.I * z), hball⟩ : Disk)).mpr
    ⟨hwz, hwrz, hwiz⟩
  refine ⟨t, ?_⟩
  have hte : -(Complex.I * z) = (edgePoint 4 2 t : ℂ) := Subtype.ext_iff.mp ht
  have hzI : z = Complex.I * (-(Complex.I * z)) := by
    rw [mul_neg, ← mul_assoc, Complex.I_mul_I, neg_one_mul, neg_neg]
  rw [hzI, hte, (klein_cut_edge_succ t).2]

lemma t95J03_torus_bridge_aux_chart_self {z : ℂ} (h : ‖z‖ = 1)
    (hl : klein_cut_l1 z = 1) : klein_cut_chart z = z := by
  rw [klein_cut_chart, if_neg (by
    intro hz
    rw [hz] at h
    simp at h), h, hl]
  norm_num

lemma t95J03_torus_bridge_aux_signs {x y : ℝ} (h : x + y = 1) (hl : |x| + |y| ≤ 1) :
    0 ≤ x ∧ 0 ≤ y := by
  constructor
  · by_contra h0
    push_neg at h0
    have hy1 : 1 < y := by linarith
    have hya : 1 < |y| := by
      have := le_abs_self y
      linarith
    have hx1 : 0 ≤ |x| := abs_nonneg x
    linarith
  · by_contra h0
    push_neg at h0
    have hx1 : 1 < x := by linarith
    have hxa : 1 < |x| := by
      have := le_abs_self x
      linarith
    have hy1 : 0 ≤ |y| := abs_nonneg y
    linarith

set_option maxHeartbeats 2000000 in
/-- The n = 1 core: first-coordinate offset exactly 1. -/
lemma t95J03_torus_bridge_aux_inj_caseA (z z' : Disk) (m : ℤ)
    (hA : ((klein_cut_chart (z : ℂ)).re + (klein_cut_chart (z : ℂ)).im) / (2 : ℝ) = 1 / 2)
    (hA' : ((klein_cut_chart (z' : ℂ)).re + (klein_cut_chart (z' : ℂ)).im) / (2 : ℝ) = -(1 / 2))
    (hm : ((klein_cut_chart (z : ℂ)).re - (klein_cut_chart (z : ℂ)).im) / 2 -
        ((klein_cut_chart (z' : ℂ)).re - (klein_cut_chart (z' : ℂ)).im) / (2 : ℝ) = m)
    (hm1 : m = 1 ∨ m = -1 ∨ m = 0) :
    Relation.EqvGen (SurfaceRel true 1) z z' := by
  push_cast at hm
  norm_num at hm
  -- chart coordinate notation
  set x := (klein_cut_chart (z : ℂ)).re with hxdef
  set y := (klein_cut_chart (z : ℂ)).im with hydef
  set x' := (klein_cut_chart (z' : ℂ)).re with hx'def
  set y' := (klein_cut_chart (z' : ℂ)).im with hy'def
  have hsum : x + y = 1 := by rw [hxdef, hydef] at hA; linarith
  have hsum' : x' + y' = -1 := by rw [hx'def, hy'def] at hA'; linarith
  have hnormz : ‖(z : ℂ)‖ ≤ 1 := by
    have h := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hnormz' : ‖(z' : ℂ)‖ ≤ 1 := by
    have h := z'.2
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hc0 := klein_cut_l1_chart (z : ℂ)
  unfold klein_cut_l1 at hc0
  rw [← hxdef, ← hydef] at hc0
  have hl1 : |x| + |y| ≤ 1 := by rw [hc0]; exact hnormz
  have hs := t95J03_torus_bridge_aux_signs hsum hl1
  have hl1eq : |x| + |y| = 1 := by
    rw [abs_of_nonneg hs.1, abs_of_nonneg hs.2]
    linarith
  have hnz : ‖(z : ℂ)‖ = 1 := by rw [← hc0, hl1eq]
  have hc0' := klein_cut_l1_chart (z' : ℂ)
  unfold klein_cut_l1 at hc0'
  rw [← hx'def, ← hy'def] at hc0'
  have hl1' : |x'| + |y'| ≤ 1 := by rw [hc0']; exact hnormz'
  have hs' : x' ≤ 0 ∧ y' ≤ 0 := by
    have hn : (-x') + (-y') = 1 := by linarith
    have hl : |-x'| + |-y'| ≤ 1 := by rw [abs_neg, abs_neg]; exact hl1'
    obtain ⟨h1, h2⟩ := t95J03_torus_bridge_aux_signs hn hl
    exact ⟨neg_nonneg.mp h1, neg_nonneg.mp h2⟩
  have hl1eq' : |x'| + |y'| = 1 := by
    rw [abs_of_nonpos hs'.1, abs_of_nonpos hs'.2]
    linarith
  have hnz' : ‖(z' : ℂ)‖ = 1 := by rw [← hc0', hl1eq']
  have hc := t95J03_torus_bridge_aux_exp_corner
  have htri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
    intro a b
    have hle1 := le_abs_self a
    have hle2 := le_abs_self b
    have hle3 := neg_abs_le a
    have hle4 := neg_abs_le b
    rw [abs_le]
    constructor <;> linarith
  rcases hm1 with rfl | rfl | rfl
  · -- m = 1 : z = 1, z' = -1
    have hd : x - y - (x' - y') = 2 := by linarith
    have hbd1 : x - y ≤ 1 := by
      have := htri x y
      have hx' := abs_nonneg x
      have hy' := abs_nonneg y
      nlinarith [hl1eq]
    have hbd2 : x' - y' ≥ -1 := by
      have := htri x' y'
      have hx' := abs_nonneg x'
      have hy' := abs_nonneg y'
      nlinarith [hl1eq']
    have hx1 : x = 1 ∧ y = 0 := by constructor <;> linarith
    have hx1' : x' = -1 ∧ y' = 0 := by constructor <;> linarith
    have hcz1 : klein_cut_chart (z : ℂ) = 1 := by
      apply Complex.ext
      · rw [← hxdef, hx1.1]; norm_num
      · rw [← hydef, hx1.2]; norm_num
    have hcz1' : klein_cut_chart (z' : ℂ) = -1 := by
      apply Complex.ext
      · rw [← hx'def, hx1'.1]; norm_num
      · rw [← hy'def, hx1'.2]; norm_num
    have hz1 : (z : ℂ) = 1 := by
      rw [← klein_cut_chartInv_chart (z : ℂ), hcz1]
      simp [klein_cut_chartInv, klein_cut_l1]
    have hz1' : (z' : ℂ) = -1 := by
      rw [← klein_cut_chartInv_chart (z' : ℂ), hcz1']
      simp [klein_cut_chartInv, klein_cut_l1]
    set w : Disk := edgePoint 4 2 ⟨(1 : ℝ), by norm_num⟩ with hwdef
    have hwv : (w : ℂ) = -Complex.I := hc.2.1
    have he0 : z = edgePoint 4 0 ⟨(0 : ℝ), by norm_num⟩ :=
      Subtype.ext (by rw [hz1]; exact hc.1.symm)
    have he2 : w = edgePoint 4 2 ⟨(1 : ℝ), by norm_num⟩ := by rw [hwdef]
    have he1 : z' = edgePoint 4 1 ⟨(1 : ℝ), by norm_num⟩ :=
      Subtype.ext (by rw [hz1']; exact hc.2.2.2.2.1.symm)
    have he3 : w = edgePoint 4 3 ⟨(0 : ℝ), by norm_num⟩ :=
      Subtype.ext (by rw [hwdef, hwv]; exact hc.2.2.2.2.2.symm)
    have r1 : Relation.EqvGen (SurfaceRel true 1) z w :=
      @Relation.EqvGen.rel _ (SurfaceRel true 1) z w (by
        unfold SurfaceRel
        refine ⟨0, by norm_num, ⟨(⟨(0 : ℝ), by norm_num⟩ : Set.Icc (0 : ℝ) 1), ?_⟩⟩
        exact Or.inl ⟨by rw [he0]; try norm_num, by rw [he2]; try norm_num⟩)
    have rinner : Relation.EqvGen (SurfaceRel true 1) z' w :=
      @Relation.EqvGen.rel _ (SurfaceRel true 1) z' w (by
        unfold SurfaceRel
        refine ⟨0, by norm_num, ⟨(⟨(1 : ℝ), by norm_num⟩ : Set.Icc (0 : ℝ) 1), ?_⟩⟩
        exact Or.inr ⟨by rw [he1]; try norm_num, by rw [he3]; try norm_num⟩)
    have r2 : Relation.EqvGen (SurfaceRel true 1) w z' :=
      @Relation.EqvGen.symm _ (SurfaceRel true 1) z' w rinner
    exact @Relation.EqvGen.trans _ (SurfaceRel true 1) z w z' r1 r2
  · -- m = -1 : z = i, z' = -i
    have hd : x - y - (x' - y') = -2 := by linarith
    have hbd1 : x - y ≥ -1 := by
      have := htri x y
      have hx' := abs_nonneg x
      have hy' := abs_nonneg y
      nlinarith [hl1eq]
    have hbd2 : x' - y' ≤ 1 := by
      have := htri x' y'
      have hx' := abs_nonneg x'
      have hy' := abs_nonneg y'
      nlinarith [hl1eq']
    have hx0 : x = 0 ∧ y = 1 := by constructor <;> linarith
    have hx0' : x' = 0 ∧ y' = -1 := by constructor <;> linarith
    have hcz1 : klein_cut_chart (z : ℂ) = Complex.I := by
      apply Complex.ext
      · rw [← hxdef, hx0.1]; norm_num
      · rw [← hydef, hx0.2]; norm_num
    have hcz1' : klein_cut_chart (z' : ℂ) = -Complex.I := by
      apply Complex.ext
      · rw [← hx'def, hx0'.1]; norm_num
      · rw [← hy'def, hx0'.2]; norm_num
    have hz1 : (z : ℂ) = Complex.I := by
      rw [← klein_cut_chartInv_chart (z : ℂ), hcz1]
      simp [klein_cut_chartInv, klein_cut_l1]
    have hz1' : (z' : ℂ) = -Complex.I := by
      rw [← klein_cut_chartInv_chart (z' : ℂ), hcz1']
      simp [klein_cut_chartInv, klein_cut_l1]
    set w : Disk := edgePoint 4 3 ⟨(1 : ℝ), by norm_num⟩ with hwdef
    have hwv : (w : ℂ) = 1 := hc.2.2.2.1
    have he1 : z = edgePoint 4 1 ⟨(0 : ℝ), by norm_num⟩ :=
      Subtype.ext (by rw [hz1]; exact hc.2.2.1.symm)
    have he3 : w = edgePoint 4 3 ⟨(1 : ℝ), by norm_num⟩ := by rw [hwdef]
    have he0 : w = edgePoint 4 0 ⟨(0 : ℝ), by norm_num⟩ :=
      Subtype.ext (by rw [hwdef, hwv]; exact hc.1.symm)
    have he2 : z' = edgePoint 4 2 ⟨(1 : ℝ), by norm_num⟩ :=
      Subtype.ext (by rw [hz1']; exact hc.2.1.symm)
    have r1 : Relation.EqvGen (SurfaceRel true 1) z w :=
      @Relation.EqvGen.rel _ (SurfaceRel true 1) z w (by
        unfold SurfaceRel
        refine ⟨0, by norm_num, ⟨(⟨(0 : ℝ), by norm_num⟩ : Set.Icc (0 : ℝ) 1), ?_⟩⟩
        exact Or.inr ⟨by rw [he1]; try norm_num, by rw [he3]; try norm_num⟩)
    have r2' : Relation.EqvGen (SurfaceRel true 1) w z' :=
      @Relation.EqvGen.rel _ (SurfaceRel true 1) w z' (by
        unfold SurfaceRel
        refine ⟨0, by norm_num, ⟨(⟨(0 : ℝ), by norm_num⟩ : Set.Icc (0 : ℝ) 1), ?_⟩⟩
        exact Or.inl ⟨by rw [he0]; try norm_num, by rw [he2]; try norm_num⟩)
    exact @Relation.EqvGen.trans _ (SurfaceRel true 1) z w z' r1 r2'
  · -- m = 0 : the main case
    have hd : x - y = x' - y' := by linarith
    have hxy' : x' = -y ∧ y' = -x := by constructor <;> linarith
    obtain ⟨c, hc0, hcq⟩ := klein_cut_chartInv_pos (klein_cut_chart (z : ℂ))
    have hzc : (z : ℂ) = ((c : ℝ) : ℂ) * (klein_cut_chart (z : ℂ)) :=
      (klein_cut_chartInv_chart (z : ℂ)).symm.trans hcq
    have hzre : (z : ℂ).re = c * x := by
      rw [hzc]
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hxdef]
    have hzim : (z : ℂ).im = c * y := by
      rw [hzc]
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hydef]
    have hcnnc : 0 ≤ c := hc0.le
    obtain ⟨t, ht⟩ := (klein_cut_edge_zero_iff z).mpr
      ⟨hnz, by rw [hzre]; exact mul_nonneg hcnnc hs.1,
        by rw [hzim]; exact mul_nonneg hcnnc hs.2⟩
    obtain ⟨c', hc0', hcq'⟩ := klein_cut_chartInv_pos (klein_cut_chart (z' : ℂ))
    have hzc' : (z' : ℂ) = ((c' : ℝ) : ℂ) * (klein_cut_chart (z' : ℂ)) :=
      (klein_cut_chartInv_chart (z' : ℂ)).symm.trans hcq'
    have hzre' : (z' : ℂ).re = c' * x' := by
      rw [hzc']
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hx'def]
    have hzim' : (z' : ℂ).im = c' * y' := by
      rw [hzc']
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hy'def]
    have hc'nn : 0 ≤ c' := hc0'.le
    obtain ⟨u, hu⟩ := (klein_cut_edge_two_iff z').mpr
      ⟨hnz', by rw [hzre']; nlinarith [mul_nonneg hc'nn (neg_nonneg.mpr hs'.1)],
        by rw [hzim']; nlinarith [mul_nonneg hc'nn (neg_nonneg.mpr hs'.2)]⟩
    -- trigonometric parameters
    have hαb : 0 ≤ Real.pi / 2 * (t : ℝ) ∧ Real.pi / 2 * (t : ℝ) ≤ Real.pi / 2 :=
      ⟨mul_nonneg (by positivity) t.2.1,
        mul_le_of_le_one_right (by positivity) t.2.2⟩
    have hβb : 0 ≤ Real.pi / 2 * (u : ℝ) ∧ Real.pi / 2 * (u : ℝ) ≤ Real.pi / 2 :=
      ⟨mul_nonneg (by positivity) u.2.1,
        mul_le_of_le_one_right (by positivity) u.2.2⟩
    set α : ℝ := Real.pi / 2 * (t : ℝ) with hαdef
    set β : ℝ := Real.pi / 2 * (u : ℝ) with hβdef
    have hcα : 0 ≤ Real.cos α :=
      Real.cos_nonneg_of_mem_Icc ⟨by have := hαb.1; linarith [Real.pi_pos],
        by have := hαb.2; linarith [Real.pi_pos]⟩
    have hsα : 0 ≤ Real.sin α :=
      Real.sin_nonneg_of_mem_Icc ⟨hαb.1, by have := hαb.2; linarith [Real.pi_pos]⟩
    have hcβ : 0 ≤ Real.cos β :=
      Real.cos_nonneg_of_mem_Icc ⟨by have := hβb.1; linarith [Real.pi_pos],
        by have := hβb.2; linarith [Real.pi_pos]⟩
    have hsβ : 0 ≤ Real.sin β :=
      Real.sin_nonneg_of_mem_Icc ⟨hβb.1, by have := hβb.2; linarith [Real.pi_pos]⟩
    have hne1 : Real.cos α + Real.sin α ≠ 0 := by
      intro hh
      have h1 : Real.cos α = 0 := by nlinarith [hcα, hsα, hh]
      have h2 : Real.sin α = 0 := by nlinarith [hcα, hsα, hh]
      have h3 := Real.cos_sq_add_sin_sq α
      rw [h1, h2] at h3
      norm_num at h3
    have hne2 : Real.cos β + Real.sin β ≠ 0 := by
      intro hh
      have h1 : Real.cos β = 0 := by nlinarith [hcβ, hsβ, hh]
      have h2 : Real.sin β = 0 := by nlinarith [hcβ, hsβ, hh]
      have h3 := Real.cos_sq_add_sin_sq β
      rw [h1, h2] at h3
      norm_num at h3
    have hf0 := t95J03_torus_bridge_aux_edge0_facts t
    have hzrecos : (z : ℂ).re = Real.cos α := by rw [hαdef, ht]; exact hf0.2.1
    have hzimcos : (z : ℂ).im = Real.sin α := by rw [hαdef, ht]; exact hf0.2.2
    have hcs : klein_cut_l1 (z : ℂ) = Real.cos α + Real.sin α := by
      rw [klein_cut_l1, hzrecos, hzimcos, abs_of_nonneg hcα, abs_of_nonneg hsα]
    have hf2 := t95J03_torus_bridge_aux_edge2_facts u
    have hz'recos : (z' : ℂ).re = -Real.cos β := by rw [hβdef, hu]; exact hf2.2.1
    have hz'imcos : (z' : ℂ).im = -Real.sin β := by rw [hβdef, hu]; exact hf2.2.2
    have hcs' : klein_cut_l1 (z' : ℂ) = Real.cos β + Real.sin β := by
      rw [klein_cut_l1, hz'recos, hz'imcos, abs_neg, abs_neg,
        abs_of_nonneg hcβ, abs_of_nonneg hsβ]
    have hz0 : (z : ℂ) ≠ 0 := by
      intro hh
      rw [hh] at hnz
      simp at hnz
    have hz0' : (z' : ℂ) ≠ 0 := by
      intro hh
      rw [hh] at hnz'
      simp at hnz'
    have hchz : klein_cut_chart (z : ℂ) =
        ((1 / (Real.cos α + Real.sin α) : ℝ) : ℂ) * (z : ℂ) := by
      rw [klein_cut_chart, if_neg hz0, hnz, hcs]
    have hchz' : klein_cut_chart (z' : ℂ) =
        ((1 / (Real.cos β + Real.sin β) : ℝ) : ℂ) * (z' : ℂ) := by
      rw [klein_cut_chart, if_neg hz0', hnz', hcs']
    have hxα : x = Real.cos α / (Real.cos α + Real.sin α) := by
      rw [hxdef, hchz]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hzrecos]
      field_simp
      try ring
    have hyα : y = Real.sin α / (Real.cos α + Real.sin α) := by
      rw [hydef, hchz]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hzimcos]
      field_simp
      try ring
    have hx'β : x' = -Real.cos β / (Real.cos β + Real.sin β) := by
      rw [hx'def, hchz']
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hz'recos]
      field_simp
      try ring
    have hy'β : y' = -Real.sin β / (Real.cos β + Real.sin β) := by
      rw [hy'def, hchz']
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hz'imcos]
      field_simp
      try ring
    have hvalα : (Real.cos α - Real.sin α) / (Real.cos α + Real.sin α) = x - y := by
      rw [hxα, hyα, div_sub_div_same]
    have hvalβ : (Real.cos (Real.pi / 2 - β) - Real.sin (Real.pi / 2 - β)) /
        (Real.cos (Real.pi / 2 - β) + Real.sin (Real.pi / 2 - β)) = x' - y' := by
      rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, hx'β, hy'β,
        div_sub_div_same, add_comm (Real.sin β) (Real.cos β)]
      ring
    have hpb : 0 ≤ Real.pi / 2 - β ∧ Real.pi / 2 - β ≤ Real.pi / 2 :=
      ⟨by linarith, by linarith⟩
    have hpbne : Real.cos (Real.pi / 2 - β) + Real.sin (Real.pi / 2 - β) ≠ 0 := by
      rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
      simpa [add_comm] using hne2
    have hπ : Real.pi / 2 - β = α :=
      t95J03_torus_bridge_aux_val_inj hpb.1 hpb.2 hαb.1 hαb.2 hpbne hne1
        (by rw [hvalα, hvalβ]
            linarith [hd])
    have hut : (u : ℝ) = 1 - (t : ℝ) := by
      have hkey : (Real.pi / 2) * ((u : ℝ) + (t : ℝ)) = Real.pi / 2 := by
        rw [mul_add]
        rw [← hβdef, ← hαdef, ← hπ]
        ring
      have hsum1 : (u : ℝ) + (t : ℝ) = 1 := by
        have h2 : (Real.pi / 2) * ((u : ℝ) + (t : ℝ)) = (Real.pi / 2) * 1 := by
          rw [hkey]
          ring
        exact mul_left_cancel₀ (by positivity : (Real.pi / 2 : ℝ) ≠ 0) h2
      linarith
    have he2 : z' = edgePoint 4 2 ⟨1 - (t : ℝ),
        by have := t.2.1; have := t.2.2; constructor <;> linarith⟩ := by
      rw [hu, show u = ⟨1 - (t : ℝ),
        by have := t.2.1; have := t.2.2; constructor <;> linarith⟩ from Subtype.ext hut]
    exact @Relation.EqvGen.rel _ (SurfaceRel true 1) z z'
      ⟨0, by norm_num, ⟨t, Or.inl ⟨by rw [ht]; try norm_num, by rw [he2]; try norm_num⟩⟩⟩

set_option maxHeartbeats 2000000 in
/-- The m = 1 core: second-coordinate offset exactly 1. -/
lemma t95J03_torus_bridge_aux_inj_caseB (z z' : Disk)
    (hA : ((klein_cut_chart (z : ℂ)).re + (klein_cut_chart (z : ℂ)).im) / (2 : ℝ) =
      ((klein_cut_chart (z' : ℂ)).re + (klein_cut_chart (z' : ℂ)).im) / 2)
    (hB : ((klein_cut_chart (z : ℂ)).re - (klein_cut_chart (z : ℂ)).im) / (2 : ℝ) = 1 / 2)
    (hB' : ((klein_cut_chart (z' : ℂ)).re - (klein_cut_chart (z' : ℂ)).im) / (2 : ℝ) = -(1 / 2)) :
    Relation.EqvGen (SurfaceRel true 1) z z' := by
  set x := (klein_cut_chart (z : ℂ)).re with hxdef
  set y := (klein_cut_chart (z : ℂ)).im with hydef
  set x' := (klein_cut_chart (z' : ℂ)).re with hx'def
  set y' := (klein_cut_chart (z' : ℂ)).im with hy'def
  have hsub : x - y = 1 := by rw [hxdef, hydef] at hB; linarith
  have hsub' : x' - y' = -1 := by rw [hx'def, hy'def] at hB'; linarith
  have hAeq : x + y = x' + y' := by rw [hxdef, hydef, hx'def, hy'def] at hA; linarith
  have hnormz : ‖(z : ℂ)‖ ≤ 1 := by
    have h := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hnormz' : ‖(z' : ℂ)‖ ≤ 1 := by
    have h := z'.2
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hc0 := klein_cut_l1_chart (z : ℂ)
  unfold klein_cut_l1 at hc0
  rw [← hxdef, ← hydef] at hc0
  have hl1 : |x| + |y| ≤ 1 := by rw [hc0]; exact hnormz
  have hs : 0 ≤ x ∧ y ≤ 0 := by
    have hn : x + (-y) = 1 := by linarith
    have hl : |x| + |-y| ≤ 1 := by rw [abs_neg]; exact hl1
    obtain ⟨h1, h2⟩ := t95J03_torus_bridge_aux_signs hn hl
    exact ⟨h1, neg_nonneg.mp h2⟩
  have hl1eq : |x| + |y| = 1 := by
    rw [abs_of_nonneg hs.1, abs_of_nonpos hs.2]
    linarith
  have hnz : ‖(z : ℂ)‖ = 1 := by rw [← hc0, hl1eq]
  have hc0' := klein_cut_l1_chart (z' : ℂ)
  unfold klein_cut_l1 at hc0'
  rw [← hx'def, ← hy'def] at hc0'
  have hl1' : |x'| + |y'| ≤ 1 := by rw [hc0']; exact hnormz'
  have hs' : x' ≤ 0 ∧ 0 ≤ y' := by
    have hn : y' + (-x') = 1 := by linarith
    have hl : |y'| + |-x'| ≤ 1 := by rw [abs_neg]; linarith
    obtain ⟨h1, h2⟩ := t95J03_torus_bridge_aux_signs hn hl
    exact ⟨neg_nonneg.mp h2, h1⟩
  have hl1eq' : |x'| + |y'| = 1 := by
    rw [abs_of_nonpos hs'.1, abs_of_nonneg hs'.2]
    linarith
  have hnz' : ‖(z' : ℂ)‖ = 1 := by rw [← hc0', hl1eq']
  -- z on edge 3, z' on edge 1
  obtain ⟨c, hc0p, hcq⟩ := klein_cut_chartInv_pos (klein_cut_chart (z : ℂ))
  have hzc : (z : ℂ) = ((c : ℝ) : ℂ) * (klein_cut_chart (z : ℂ)) :=
    (klein_cut_chartInv_chart (z : ℂ)).symm.trans hcq
  have hzre : (z : ℂ).re = c * x := by
    rw [hzc]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hxdef]
  have hzim : (z : ℂ).im = c * y := by
    rw [hzc]
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hydef]
  have hcnn : 0 ≤ c := hc0p.le
  obtain ⟨t, ht⟩ := t95J03_torus_bridge_aux_edge3_of (z : ℂ) hnz
    (by rw [hzre]; exact mul_nonneg hcnn hs.1)
    (by rw [hzim]; nlinarith [mul_nonneg hcnn (neg_nonneg.mpr hs.2)])
  obtain ⟨c', hc0p', hcq'⟩ := klein_cut_chartInv_pos (klein_cut_chart (z' : ℂ))
  have hzc' : (z' : ℂ) = ((c' : ℝ) : ℂ) * (klein_cut_chart (z' : ℂ)) :=
    (klein_cut_chartInv_chart (z' : ℂ)).symm.trans hcq'
  have hzre' : (z' : ℂ).re = c' * x' := by
    rw [hzc']
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hx'def]
  have hzim' : (z' : ℂ).im = c' * y' := by
    rw [hzc']
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hy'def]
  have hcnn' : 0 ≤ c' := hc0p'.le
  obtain ⟨s, hs1⟩ := t95J03_torus_bridge_aux_edge1_of (z' : ℂ) hnz'
    (by rw [hzre']; nlinarith [mul_nonneg hcnn' (neg_nonneg.mpr hs'.1)])
    (by rw [hzim']; exact mul_nonneg hcnn' hs'.2)
  -- trigonometric parameters
  have hδb : 0 ≤ Real.pi / 2 * (t : ℝ) ∧ Real.pi / 2 * (t : ℝ) ≤ Real.pi / 2 :=
    ⟨mul_nonneg (by positivity) t.2.1, mul_le_of_le_one_right (by positivity) t.2.2⟩
  have hσb : 0 ≤ Real.pi / 2 * (s : ℝ) ∧ Real.pi / 2 * (s : ℝ) ≤ Real.pi / 2 :=
    ⟨mul_nonneg (by positivity) s.2.1, mul_le_of_le_one_right (by positivity) s.2.2⟩
  set δ : ℝ := Real.pi / 2 * (t : ℝ) with hδdef
  set σ : ℝ := Real.pi / 2 * (s : ℝ) with hσdef
  have hcδ : 0 ≤ Real.cos δ :=
    Real.cos_nonneg_of_mem_Icc ⟨by have := hδb.1; linarith [Real.pi_pos],
      by have := hδb.2; linarith [Real.pi_pos]⟩
  have hsδ : 0 ≤ Real.sin δ :=
    Real.sin_nonneg_of_mem_Icc ⟨hδb.1, by have := hδb.2; linarith [Real.pi_pos]⟩
  have hcσ : 0 ≤ Real.cos σ :=
    Real.cos_nonneg_of_mem_Icc ⟨by have := hσb.1; linarith [Real.pi_pos],
      by have := hσb.2; linarith [Real.pi_pos]⟩
  have hsσ : 0 ≤ Real.sin σ :=
    Real.sin_nonneg_of_mem_Icc ⟨hσb.1, by have := hσb.2; linarith [Real.pi_pos]⟩
  have hneδ : Real.cos δ + Real.sin δ ≠ 0 := by
    intro hh
    have h1 : Real.cos δ = 0 := by nlinarith [hcδ, hsδ, hh]
    have h2 : Real.sin δ = 0 := by nlinarith [hcδ, hsδ, hh]
    have h3 := Real.cos_sq_add_sin_sq δ
    rw [h1, h2] at h3
    norm_num at h3
  have hneσ : Real.cos σ + Real.sin σ ≠ 0 := by
    intro hh
    have h1 : Real.cos σ = 0 := by nlinarith [hcσ, hsσ, hh]
    have h2 : Real.sin σ = 0 := by nlinarith [hcσ, hsσ, hh]
    have h3 := Real.cos_sq_add_sin_sq σ
    rw [h1, h2] at h3
    norm_num at h3
  -- coordinates of z (edge 3 = I * edge 2) and z' (edge 1 = I * edge 0)
  have hw := klein_cut_edge_succ t
  have hf2 := t95J03_torus_bridge_aux_edge2_facts t
  have hz3 : (z : ℂ) = Complex.I * ((edgePoint 4 2 t : ℂ)) := by
    rw [ht]
    exact hw.2
  have hw' := klein_cut_edge_succ s
  have hf0 := t95J03_torus_bridge_aux_edge0_facts s
  have hz1' : (z' : ℂ) = Complex.I * ((edgePoint 4 0 s : ℂ)) := by
    rw [hs1]
    exact hw'.1
  have hzreδ : (z : ℂ).re = Real.sin δ := by
    rw [hz3]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, hδdef, hf2.2.2]
    push_cast
    ring
  have hzimδ : (z : ℂ).im = -Real.cos δ := by
    rw [hz3]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, hδdef, hf2.2.1]
    push_cast
    ring
  have hzre'σ : (z' : ℂ).re = -Real.sin σ := by
    rw [hz1']
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, hσdef, hf0.2.2]
    push_cast
    ring
  have hzim'σ : (z' : ℂ).im = Real.cos σ := by
    rw [hz1']
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, hσdef, hf0.2.1]
    push_cast
    ring
  have hcs : klein_cut_l1 (z : ℂ) = Real.cos δ + Real.sin δ := by
    rw [klein_cut_l1, hzreδ, hzimδ, abs_neg, abs_of_nonneg hsδ, abs_of_nonneg hcδ]
    ring
  have hcs' : klein_cut_l1 (z' : ℂ) = Real.cos σ + Real.sin σ := by
    rw [klein_cut_l1, hzre'σ, hzim'σ, abs_neg, abs_of_nonneg hsσ,
      abs_of_nonneg hcσ]
    ring
  have hz0 : (z : ℂ) ≠ 0 := by
    intro hh
    rw [hh] at hnz
    simp at hnz
  have hz0' : (z' : ℂ) ≠ 0 := by
    intro hh
    rw [hh] at hnz'
    simp at hnz'
  have hchz : klein_cut_chart (z : ℂ) =
      ((1 / (Real.cos δ + Real.sin δ) : ℝ) : ℂ) * (z : ℂ) := by
    rw [klein_cut_chart, if_neg hz0, hnz, hcs]
  have hchz' : klein_cut_chart (z' : ℂ) =
      ((1 / (Real.cos σ + Real.sin σ) : ℝ) : ℂ) * (z' : ℂ) := by
    rw [klein_cut_chart, if_neg hz0', hnz', hcs']
  have hxδ : x = Real.sin δ / (Real.cos δ + Real.sin δ) := by
    rw [hxdef, hchz]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hzreδ]
    field_simp
    try ring
  have hyδ : y = -Real.cos δ / (Real.cos δ + Real.sin δ) := by
    rw [hydef, hchz]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hzimδ]
    field_simp
    try ring
  have hx'σ : x' = -Real.sin σ / (Real.cos σ + Real.sin σ) := by
    rw [hx'def, hchz']
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hzre'σ]
    field_simp
    try ring
  have hy'σ : y' = Real.cos σ / (Real.cos σ + Real.sin σ) := by
    rw [hy'def, hchz']
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hzim'σ]
    field_simp
    try ring
  have hvalδ : (Real.cos δ - Real.sin δ) / (Real.cos δ + Real.sin δ) = -(x + y) := by
    rw [hxδ, hyδ]
    field_simp
    ring
  have hvalσ : (Real.cos (Real.pi / 2 - σ) - Real.sin (Real.pi / 2 - σ)) /
      (Real.cos (Real.pi / 2 - σ) + Real.sin (Real.pi / 2 - σ)) = -(x' + y') := by
    rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, hx'σ, hy'σ,
      add_comm (Real.sin σ) (Real.cos σ)]
    field_simp
    ring
  have hpb : 0 ≤ Real.pi / 2 - σ ∧ Real.pi / 2 - σ ≤ Real.pi / 2 :=
    ⟨by linarith, by linarith⟩
  have hpbne : Real.cos (Real.pi / 2 - σ) + Real.sin (Real.pi / 2 - σ) ≠ 0 := by
    rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    simpa [add_comm] using hneσ
  have hπ : Real.pi / 2 - σ = δ :=
    t95J03_torus_bridge_aux_val_inj hpb.1 hpb.2 hδb.1 hδb.2 hpbne hneδ
      (by rw [hvalδ, hvalσ]
          linarith)
  have hts : (t : ℝ) = 1 - (s : ℝ) := by
    have hkey : (Real.pi / 2) * ((t : ℝ) + (s : ℝ)) = Real.pi / 2 := by
      rw [mul_add]
      rw [← hδdef, ← hσdef, ← hπ]
      ring
    have hsum1 : (t : ℝ) + (s : ℝ) = 1 := by
      have h2 : (Real.pi / 2) * ((t : ℝ) + (s : ℝ)) = (Real.pi / 2) * 1 := by
        rw [hkey]
        ring
      exact mul_left_cancel₀ (by positivity : (Real.pi / 2 : ℝ) ≠ 0) h2
    linarith
  have hts' : t = ⟨1 - (s : ℝ),
      by have := s.2.1; have := s.2.2; constructor <;> linarith⟩ := Subtype.ext hts
  have he3 : z = edgePoint 4 3 ⟨1 - (s : ℝ),
      by have := s.2.1; have := s.2.2; constructor <;> linarith⟩ := by
    apply Subtype.ext
    rw [ht, hts']
  have res : Relation.EqvGen (SurfaceRel true 1) z' z :=
    @Relation.EqvGen.rel _ (SurfaceRel true 1) z' z
      ⟨0, by norm_num, ⟨s, Or.inr ⟨by apply Subtype.ext; rw [hs1]; try norm_num,
        by rw [he3]; try norm_num⟩⟩⟩
  exact @Relation.EqvGen.symm _ (SurfaceRel true 1) z' z res

set_option maxHeartbeats 1000000 in
lemma t95J03_torus_bridge_aux_inj_core (z z' : Disk)
    (h : t95J03_torus_bridge_aux_f (z : ℂ) = t95J03_torus_bridge_aux_f (z' : ℂ)) :
    Relation.EqvGen (SurfaceRel true 1) z z' := by
  simp only [t95J03_torus_bridge_aux_f, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨n, hn⟩ := t95J03_torus_bridge_aux_int_of_coe_eq h1
  obtain ⟨m, hm⟩ := t95J03_torus_bridge_aux_int_of_coe_eq h2
  set A := ((klein_cut_chart (z : ℂ)).re + (klein_cut_chart (z : ℂ)).im) / 2 with hAdef
  set A' := ((klein_cut_chart (z' : ℂ)).re + (klein_cut_chart (z' : ℂ)).im) / 2 with hA'def
  set B := ((klein_cut_chart (z : ℂ)).re - (klein_cut_chart (z : ℂ)).im) / 2 with hBdef
  set B' := ((klein_cut_chart (z' : ℂ)).re - (klein_cut_chart (z' : ℂ)).im) / 2 with hB'def
  have hnorm : ‖(z : ℂ)‖ ≤ 1 := by
    have h := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hnorm' : ‖(z' : ℂ)‖ ≤ 1 := by
    have h := z'.2
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hsumz : |(klein_cut_chart (z : ℂ)).re| + |(klein_cut_chart (z : ℂ)).im| ≤ 1 := by
    have hc := klein_cut_l1_chart (z : ℂ)
    unfold klein_cut_l1 at hc
    linarith
  have hsumz' : |(klein_cut_chart (z' : ℂ)).re| + |(klein_cut_chart (z' : ℂ)).im| ≤ 1 := by
    have hc := klein_cut_l1_chart (z' : ℂ)
    unfold klein_cut_l1 at hc
    linarith
  have hAne : |A| ≤ 1 / 2 := by
    have htri : |(klein_cut_chart (z : ℂ)).re + (klein_cut_chart (z : ℂ)).im| ≤
        |(klein_cut_chart (z : ℂ)).re| + |(klein_cut_chart (z : ℂ)).im| := by
      have hx := le_abs_self (klein_cut_chart (z : ℂ)).re
      have hy := le_abs_self (klein_cut_chart (z : ℂ)).im
      have hnx := neg_abs_le (klein_cut_chart (z : ℂ)).re
      have hny := neg_abs_le (klein_cut_chart (z : ℂ)).im
      rw [abs_le]
      constructor <;> linarith
    rw [hAdef, abs_le]
    constructor <;> nlinarith [htri, hsumz, le_abs_self ((klein_cut_chart (z : ℂ)).re + (klein_cut_chart (z : ℂ)).im), neg_abs_le ((klein_cut_chart (z : ℂ)).re + (klein_cut_chart (z : ℂ)).im)]
  have hAne' : |A'| ≤ 1 / 2 := by
    have htri : |(klein_cut_chart (z' : ℂ)).re + (klein_cut_chart (z' : ℂ)).im| ≤
        |(klein_cut_chart (z' : ℂ)).re| + |(klein_cut_chart (z' : ℂ)).im| := by
      have hx := le_abs_self (klein_cut_chart (z' : ℂ)).re
      have hy := le_abs_self (klein_cut_chart (z' : ℂ)).im
      have hnx := neg_abs_le (klein_cut_chart (z' : ℂ)).re
      have hny := neg_abs_le (klein_cut_chart (z' : ℂ)).im
      rw [abs_le]
      constructor <;> linarith
    rw [hA'def, abs_le]
    constructor <;> nlinarith [htri, hsumz', le_abs_self ((klein_cut_chart (z' : ℂ)).re + (klein_cut_chart (z' : ℂ)).im), neg_abs_le ((klein_cut_chart (z' : ℂ)).re + (klein_cut_chart (z' : ℂ)).im)]
  have hBne : |B| ≤ 1 / 2 := by
    have htri : |(klein_cut_chart (z : ℂ)).re - (klein_cut_chart (z : ℂ)).im| ≤
        |(klein_cut_chart (z : ℂ)).re| + |(klein_cut_chart (z : ℂ)).im| := by
      have hx := le_abs_self (klein_cut_chart (z : ℂ)).re
      have hy := le_abs_self (klein_cut_chart (z : ℂ)).im
      have hnx := neg_abs_le (klein_cut_chart (z : ℂ)).re
      have hny := neg_abs_le (klein_cut_chart (z : ℂ)).im
      rw [abs_le]
      constructor <;> linarith
    rw [hBdef, abs_le]
    constructor <;> nlinarith [htri, hsumz, le_abs_self ((klein_cut_chart (z : ℂ)).re - (klein_cut_chart (z : ℂ)).im), neg_abs_le ((klein_cut_chart (z : ℂ)).re - (klein_cut_chart (z : ℂ)).im)]
  have hBne' : |B'| ≤ 1 / 2 := by
    have htri : |(klein_cut_chart (z' : ℂ)).re - (klein_cut_chart (z' : ℂ)).im| ≤
        |(klein_cut_chart (z' : ℂ)).re| + |(klein_cut_chart (z' : ℂ)).im| := by
      have hx := le_abs_self (klein_cut_chart (z' : ℂ)).re
      have hy := le_abs_self (klein_cut_chart (z' : ℂ)).im
      have hnx := neg_abs_le (klein_cut_chart (z' : ℂ)).re
      have hny := neg_abs_le (klein_cut_chart (z' : ℂ)).im
      rw [abs_le]
      constructor <;> linarith
    rw [hB'def, abs_le]
    constructor <;> nlinarith [htri, hsumz', le_abs_self ((klein_cut_chart (z' : ℂ)).re - (klein_cut_chart (z' : ℂ)).im), neg_abs_le ((klein_cut_chart (z' : ℂ)).re - (klein_cut_chart (z' : ℂ)).im)]
  obtain ⟨hAlo, hAhi⟩ := abs_le.1 hAne
  obtain ⟨hA'lo, hA'hi⟩ := abs_le.1 hAne'
  obtain ⟨hBlo, hBhi⟩ := abs_le.1 hBne
  obtain ⟨hB'lo, hB'hi⟩ := abs_le.1 hBne'
  have hmR : (m : ℝ) = B - B' := by push_cast; linarith
  have hnR : (n : ℝ) = A - A' := by push_cast; linarith
  have hmlo : (-(1:ℝ)) ≤ B - B' := by linarith
  have hmhi : B - B' ≤ (1:ℝ) := by linarith
  have hnlo : (-(1:ℝ)) ≤ A - A' := by linarith
  have hnhi : A - A' ≤ (1:ℝ) := by linarith
  have hmC : m = 1 ∨ m = -1 ∨ m = 0 := by
    have hc1 : ((-1:ℤ):ℝ) ≤ (m:ℝ) := by rw [hmR]; push_cast; linarith
    have hc2 : ((m:ℝ)) ≤ ((1:ℤ):ℝ) := by rw [hmR]; push_cast; linarith
    have i1 : (-1:ℤ) ≤ m := by exact_mod_cast hc1
    have i2 : m ≤ (1:ℤ) := by exact_mod_cast hc2
    omega
  have hnC : n = 1 ∨ n = -1 ∨ n = 0 := by
    have hc1 : ((-1:ℤ):ℝ) ≤ (n:ℝ) := by rw [hnR]; push_cast; linarith
    have hc2 : ((n:ℝ)) ≤ ((1:ℤ):ℝ) := by rw [hnR]; push_cast; linarith
    have i1 : (-1:ℤ) ≤ n := by exact_mod_cast hc1
    have i2 : n ≤ (1:ℤ) := by exact_mod_cast hc2
    omega
  rcases hnC with rfl | rfl | rfl
  · push_cast at hn
    norm_num at hn
    -- n = 1
    have hA1 : A = 1 / 2 := by linarith
    have hA1' : A' = -(1 / 2) := by linarith
    rw [hAdef] at hA1
    rw [hA'def] at hA1'
    rw [hBdef, hB'def] at hm
    exact t95J03_torus_bridge_aux_inj_caseA z z' m hA1 hA1' hm hmC
  · push_cast at hn
    norm_num at hn
    -- n = -1 : swap
    apply Relation.EqvGen.symm
    have hA1 : A' - A = 1 := by linarith
    have hA1' : A = -(1 / 2) := by linarith
    have hA2 : A' = 1 / 2 := by linarith
    rw [hA'def] at hA2
    rw [hAdef] at hA1'
    have hm' : B' - B = (-(m : ℤ) : ℤ) := by
      push_cast
      have := hm
      push_cast at *
      linarith
    rw [hB'def, hBdef] at hm'
    have hmc : (-m) = 1 ∨ (-m) = -1 ∨ (-m) = 0 := by omega
    exact t95J03_torus_bridge_aux_inj_caseA z' z (-m) hA2 hA1' hm' hmc
  · push_cast at hn
    norm_num at hn
    -- n = 0
    have hAeq : A = A' := by linarith
    rcases hmC with rfl | rfl | rfl
    · push_cast at hm
      norm_num at hm
      -- m = 1
      have hB1 : B = 1 / 2 := by linarith
      have hB1' : B' = -(1 / 2) := by linarith
      rw [hAdef, hA'def] at hAeq
      rw [hBdef] at hB1
      rw [hB'def] at hB1'
      exact t95J03_torus_bridge_aux_inj_caseB z z' hAeq hB1 hB1'
    · push_cast at hm
      norm_num at hm
      -- m = -1 : swap
      apply Relation.EqvGen.symm
      have hAeq' : A' = A := by linarith
      have hB1 : B' = 1 / 2 := by linarith
      have hB1' : B = -(1 / 2) := by linarith
      rw [hA'def, hAdef] at hAeq'
      rw [hB'def] at hB1
      rw [hBdef] at hB1'
      exact t95J03_torus_bridge_aux_inj_caseB z' z hAeq' hB1 hB1'
    · push_cast at hm
      norm_num at hm
      -- both zero : z = z'
      have hBeq : B = B' := by linarith
      have hre : (klein_cut_chart (z : ℂ)).re + (klein_cut_chart (z : ℂ)).im =
          (klein_cut_chart (z' : ℂ)).re + (klein_cut_chart (z' : ℂ)).im := by
        rw [hAdef, hA'def] at hAeq
        linarith
      have him : (klein_cut_chart (z : ℂ)).re - (klein_cut_chart (z : ℂ)).im =
          (klein_cut_chart (z' : ℂ)).re - (klein_cut_chart (z' : ℂ)).im := by
        rw [hBdef, hB'def] at hBeq
        linarith
      have hchart : klein_cut_chart (z : ℂ) = klein_cut_chart (z' : ℂ) := by
        have e1 : (klein_cut_chart (z : ℂ)).re = (klein_cut_chart (z' : ℂ)).re := by linarith
        have e2 : (klein_cut_chart (z : ℂ)).im = (klein_cut_chart (z' : ℂ)).im := by linarith
        exact Complex.ext e1 e2
      have hzz' : z = z' := by
        apply Subtype.ext
        have h1 : (z : ℂ) = klein_cut_chartInv (klein_cut_chart (z : ℂ)) :=
          (klein_cut_chartInv_chart _).symm
        have h2 : (z' : ℂ) = klein_cut_chartInv (klein_cut_chart (z' : ℂ)) :=
          (klein_cut_chartInv_chart _).symm
        rw [h1, h2, hchart]
      rw [hzz']
      exact Relation.EqvGen.refl z'

lemma t95J03_torus_bridge_aux_lift_injective :
    Function.Injective t95J03_torus_bridge_aux_lift := by
  intro qa qb hq
  obtain ⟨z, rfl⟩ := Quotient.mk_surjective qa
  obtain ⟨z', rfl⟩ := Quotient.mk_surjective qb
  rw [t95J03_torus_bridge_aux_lift, Quotient.lift_mk, Quotient.lift_mk] at hq
  exact Quotient.sound (t95J03_torus_bridge_aux_inj_core z z' hq)

lemma t95J03_torus_bridge : Nonempty (Surface true 1 ≃ₜ T95J03Torus) := by
  haveI : CompactSpace (Surface true 1) := by
    have hcomp : IsCompact (Set.univ : Set (Surface true 1)) := by
      rw [← Set.range_eq_univ.2 (surjective_surfaceQuotient true 1)]
      have h := (isCompact_univ.image (continuous_surfaceQuotient true 1) :
        IsCompact (surfaceQuotient true 1 '' Set.univ))
      rwa [Set.image_univ] at h
    exact isCompact_univ_iff.mp hcomp
  have hbij : Function.Bijective t95J03_torus_bridge_aux_lift :=
    ⟨t95J03_torus_bridge_aux_lift_injective, t95J03_torus_bridge_aux_lift_surjective⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective t95J03_torus_bridge_aux_lift hbij)
    (t95J03_torus_bridge_aux_lift_continuous : Continuous
      (Equiv.ofBijective t95J03_torus_bridge_aux_lift hbij))⟩

theorem t95J03_torus_bridge_spec :
    ∃ e : Surface true 1 ≃ₜ T95J03Torus,
      ∀ z : Surfaces.Disk, e (surfaceQuotient true 1 z) = t95J03_torus_bridge_aux_f (z : ℂ) := by
  haveI : CompactSpace (Surface true 1) := by
    have hcomp : IsCompact (Set.univ : Set (Surface true 1)) := by
      rw [← Set.range_eq_univ.2 (surjective_surfaceQuotient true 1)]
      have h := (isCompact_univ.image (continuous_surfaceQuotient true 1) :
        IsCompact (surfaceQuotient true 1 '' Set.univ))
      rwa [Set.image_univ] at h
    exact isCompact_univ_iff.mp hcomp
  have hbij : Function.Bijective t95J03_torus_bridge_aux_lift :=
    ⟨t95J03_torus_bridge_aux_lift_injective, t95J03_torus_bridge_aux_lift_surjective⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective t95J03_torus_bridge_aux_lift hbij)
    (t95J03_torus_bridge_aux_lift_continuous : Continuous
      (Equiv.ofBijective t95J03_torus_bridge_aux_lift hbij)), fun z => rfl⟩

end ConstructionTargets.FlatTorusBridge
