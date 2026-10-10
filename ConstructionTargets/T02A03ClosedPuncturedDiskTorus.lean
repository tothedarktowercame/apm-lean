import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Homotopy.Equiv

noncomputable section

open scoped ContinuousMap

namespace ConstructionTargets.T02A03ClosedPuncturedDiskTorus

abbrev apm_t02a03_Disk := Metric.closedBall (0 : ℂ) 1
abbrev apm_t02a03_X := {p : apm_t02a03_Disk × Circle // p.1.1 ≠ 0}
abbrev apm_t02a03_Torus := Circle × Circle

def probeToTorus : C(apm_t02a03_X, apm_t02a03_Torus) where
  toFun p :=
    (⟨NormedSpace.normalize p.1.1.1,
      mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize p.2)⟩,
      p.1.2)
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      rw [continuous_iff_continuousAt]
      intro p
      have hn : Continuous (fun q : apm_t02a03_X => ‖q.1.1.1‖) :=
        continuous_norm.comp
          (continuous_subtype_val.comp
            (continuous_fst.comp continuous_subtype_val))
      exact ((hn.continuousAt.inv₀ (norm_ne_zero_iff.mpr p.2)).smul
        (continuous_subtype_val.comp
          (continuous_fst.comp continuous_subtype_val)).continuousAt)
    · exact continuous_snd.comp continuous_subtype_val

def torusToProbe : C(apm_t02a03_Torus, apm_t02a03_X) where
  toFun p := ⟨⟨⟨p.1.1, by
    simp [Metric.mem_closedBall, dist_zero_right]⟩, p.2⟩,
    Circle.coe_ne_zero p.1⟩
  continuous_toFun := by fun_prop

theorem probeToTorus_torusToProbe (p : apm_t02a03_Torus) :
    probeToTorus (torusToProbe p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (Circle.norm_coe p.1)
  · rfl

def probeRadialHomotopy : ContinuousMap.Homotopy
    (torusToProbe.comp probeToTorus) (ContinuousMap.id apm_t02a03_X) where
  toFun tp := by
    let t : ℝ := tp.1
    let z : ℂ := tp.2.1.1.1
    let a : ℝ := (1 - t) / ‖z‖ + t
    refine ⟨⟨⟨(a : ℂ) * z, ?_⟩, tp.2.1.2⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_eq_abs]
      have ht0 : 0 ≤ t := tp.1.2.1
      have ht1 : t ≤ 1 := tp.1.2.2
      have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr tp.2.2
      have hz1 : ‖z‖ ≤ 1 := by
        have h := Metric.mem_closedBall.mp tp.2.1.1.2
        simpa [z, dist_zero_right] using h
      have ha0 : 0 ≤ a := by
        dsimp [a]
        exact add_nonneg (div_nonneg (sub_nonneg.mpr ht1) hz0.le) ht0
      rw [abs_of_nonneg ha0]
      have hz_ne : ‖z‖ ≠ 0 := hz0.ne'
      have ha : a * ‖z‖ = (1 - t) + t * ‖z‖ := by
        dsimp [a]
        field_simp
      rw [ha]
      nlinarith
    · intro h
      have ht0 : 0 ≤ t := tp.1.2.1
      have ht1 : t ≤ 1 := tp.1.2.2
      have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr tp.2.2
      have ha0 : 0 < a := by
        dsimp [a]
        by_cases ht : t = 0
        · simp [ht, hz0]
        · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
          have hfirst : 0 ≤ (1 - t) / ‖z‖ :=
            div_nonneg (sub_nonneg.mpr ht1) hz0.le
          linarith
      exact tp.2.2 (mul_eq_zero.mp h |>.resolve_left (Complex.ofReal_ne_zero.mpr ha0.ne'))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      have hn : Continuous (fun tp : unitInterval × apm_t02a03_X => ‖tp.2.1.1.1‖) :=
        continuous_norm.comp
          (continuous_subtype_val.comp
            (continuous_fst.comp
              (continuous_subtype_val.comp continuous_snd)))
      have hne : ∀ tp : unitInterval × apm_t02a03_X, ‖tp.2.1.1.1‖ ≠ 0 :=
        fun tp => norm_ne_zero_iff.mpr tp.2.2
      have ht : Continuous (fun tp : unitInterval × apm_t02a03_X => (tp.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      have hz : Continuous (fun tp : unitInterval × apm_t02a03_X => tp.2.1.1.1) :=
        continuous_subtype_val.comp
          (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))
      exact (Complex.continuous_ofReal.comp
        (((continuous_const.sub ht).div hn hne).add ht)).mul hz
    · exact continuous_snd.comp (continuous_subtype_val.comp continuous_snd)
  map_zero_left p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change ((((1 - (0 : ℝ)) / ‖p.1.1.1‖ + 0 : ℝ) : ℂ) * p.1.1.1) =
        (‖p.1.1.1‖⁻¹ : ℝ) • p.1.1.1
      simp [Complex.real_smul, div_eq_mul_inv]
    · rfl
  map_one_left p := by
    apply Subtype.ext
    apply Prod.ext <;> simp

def closedPuncturedDiskProductHomotopyEquivTorus :
    ContinuousMap.HomotopyEquiv apm_t02a03_X apm_t02a03_Torus where
  toFun := probeToTorus
  invFun := torusToProbe
  left_inv := ⟨probeRadialHomotopy⟩
  right_inv := by
    rw [show probeToTorus.comp torusToProbe = ContinuousMap.id _ by
      apply ContinuousMap.ext
      exact probeToTorus_torusToProbe]

theorem t02a03_closed_punctured_disk_torus :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t02a03_X apm_t02a03_Torus) :=
  ⟨closedPuncturedDiskProductHomotopyEquivTorus⟩

end ConstructionTargets.T02A03ClosedPuncturedDiskTorus
