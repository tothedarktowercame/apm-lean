import ConstructionTargets.GenusTwoSurfacePiOne
import ConstructionTargets.PolygonSurfaceHomology
import ConstructionTargets.CollaredConnectedSumHomology
import ConstructionTargets.FlatTorusBridge

/-!
# APM t99J02: the double torus

The printed phrase “double torus” is made precise as the classified polygon
surface `Surface true 2`.  Its CW structure is encoded by the repository's
actual standard signed octagon quotient: all polygon vertices are identified,
its eight sides form four edge orbits, and the quotient of the single polygon
is homeomorphic to `X` (so it supplies the single 2-cell).  The requested
connected-sum description uses the genuine collared connected-sum quotient,
with both summands the concrete torus `Surface true 1`, rather than merely
recording genus arithmetic.

“Using the CW decomposition”, “using van Kampen”, and “using
Mayer--Vietoris” prescribe proof methods.  The statement records their
mathematical outputs: the integral singular homology groups (twice, once for
each requested computation) and the fundamental group presentation.  The
presentation's relator is the explicit product `[a₁,b₁][a₂,b₂]` defined in
`GenusTwoSurfacePiOne`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

open ConstructionTargets.Surfaces
open ConstructionTargets.PolygonSurfacePiOne
open ConstructionTargets.CollaredConnectedSumHomology
open ConstructionTargets.FlatTorusBridge

#check PairingData.oneVertex
#check orientableOrbitEquiv
#check standardPairingData_space_homeomorph
#check ConstructionTargets.PolygonSurfaceHomology.polygonQuotient_homology
#check ConstructionTargets.PolygonSurfaceHomology.lowDegreeHomology
#check ConstructionTargets.PolygonSurfaceHomology.highDegreeHomology
#check apm_t92J05_standard_genusTwo_fundamentalGroup

/-- Specialize the polygon Mayer--Vietoris calculation to the standard
orientable octagon.  Use
`PolygonSurfaceHomology.polygonQuotient_homology`, prove that its attaching
boundary is zero by expanding `attachingDegree` in the standard orientable
coordinates, identify `PairingOrbit` with `Fin 2 × Bool` via
`orientableOrbitEquiv`, and transport along
`standardPairingData_space_homeomorph`. -/
abbrev t99J02_genusTwo_homology_aux_P : PairingData :=
  standardPairingData true 2 Nat.zero_lt_two

open ConstructionTargets.PolygonSurfaceHomology

/-- The attaching degree of the standard orientable pairing vanishes: every
edge orbit consists of one positive and one negative edge. -/
theorem t99J02_genusTwo_homology_aux_attachingDegree :
    attachingDegree t99J02_genusTwo_homology_aux_P = 0 := by
  classical
  funext l
  rw [attachingDegree_apply]
  refine Quotient.inductionOn l ?_
  intro i₀
  show ∑ i, edgeOrbitContribution t99J02_genusTwo_homology_aux_P i
      (t99J02_genusTwo_homology_aux_P.orbit i₀) = 0
  have hdeg : ∀ i : Fin t99J02_genusTwo_homology_aux_P.edgeCount,
      edgeOrbitContribution t99J02_genusTwo_homology_aux_P i
          (t99J02_genusTwo_homology_aux_P.orbit i₀) =
        if i = i₀ ∨ i = t99J02_genusTwo_homology_aux_P.pair i₀ then
          edgeAttachingDegree t99J02_genusTwo_homology_aux_P i else 0 := by
    intro i
    by_cases h : t99J02_genusTwo_homology_aux_P.orbit i =
        t99J02_genusTwo_homology_aux_P.orbit i₀
    · rw [edgeOrbitContribution_of_mem _ _ _ h]
      rcases (t99J02_genusTwo_homology_aux_P.orbit_eq_iff i i₀).mp h with h1 | h1
      · rw [if_pos (Or.inl h1.symm)]
      · have hi : i = t99J02_genusTwo_homology_aux_P.pair i₀ := by
          rw [h1, t99J02_genusTwo_homology_aux_P.pair_pair]
        rw [if_pos (Or.inr hi)]
    · rw [edgeOrbitContribution_of_not_mem _ _ _ h, if_neg]
      rintro (rfl | rfl)
      · exact h rfl
      · exact h (t99J02_genusTwo_homology_aux_P.orbit_pair i₀)
  calc ∑ i, edgeOrbitContribution t99J02_genusTwo_homology_aux_P i
        (t99J02_genusTwo_homology_aux_P.orbit i₀)
      = ∑ i, (if i = i₀ ∨ i = t99J02_genusTwo_homology_aux_P.pair i₀ then
          edgeAttachingDegree t99J02_genusTwo_homology_aux_P i else 0) :=
        Finset.sum_congr rfl (fun i _ => hdeg i)
    _ = ∑ i ∈ Finset.univ.filter
          (fun i => i = i₀ ∨ i = t99J02_genusTwo_homology_aux_P.pair i₀),
          edgeAttachingDegree t99J02_genusTwo_homology_aux_P i :=
        (Finset.sum_filter _ _).symm
    _ = 0 := by
        have hfilter : Finset.univ.filter
            (fun i => i = i₀ ∨ i = t99J02_genusTwo_homology_aux_P.pair i₀) =
            {i₀, t99J02_genusTwo_homology_aux_P.pair i₀} := by
          ext i
          simp
        rw [hfilter,
          Finset.sum_insert
            (by simp only [Finset.mem_singleton]
                exact (t99J02_genusTwo_homology_aux_P.pair_ne i₀).symm),
          Finset.sum_singleton]
        have hne : t99J02_genusTwo_homology_aux_P.sign
            (t99J02_genusTwo_homology_aux_P.pair i₀) ≠
            t99J02_genusTwo_homology_aux_P.sign i₀ :=
          standardSign_orientable_pair 2 i₀
        cases hs : t99J02_genusTwo_homology_aux_P.sign i₀ with
        | false =>
            have hp : t99J02_genusTwo_homology_aux_P.sign
                (t99J02_genusTwo_homology_aux_P.pair i₀) = true := by
              cases hsp : t99J02_genusTwo_homology_aux_P.sign
                  (t99J02_genusTwo_homology_aux_P.pair i₀) with
              | false => rw [hsp, hs] at hne; exact (hne rfl).elim
              | true => rfl
            rw [edgeAttachingDegree_of_sign_false _ _ hs,
              edgeAttachingDegree_of_sign_true _ _ hp]
            norm_num
        | true =>
            have hp : t99J02_genusTwo_homology_aux_P.sign
                (t99J02_genusTwo_homology_aux_P.pair i₀) = false := by
              cases hsp : t99J02_genusTwo_homology_aux_P.sign
                  (t99J02_genusTwo_homology_aux_P.pair i₀) with
              | false => rfl
              | true => rw [hsp, hs] at hne; exact (hne rfl).elim
            rw [edgeAttachingDegree_of_sign_true _ _ hs,
              edgeAttachingDegree_of_sign_false _ _ hp]
            norm_num

/-- The degree-two attaching boundary map of the standard orientable octagon
is zero. -/
theorem t99J02_genusTwo_homology_aux_attachingBoundary :
    attachingBoundary t99J02_genusTwo_homology_aux_P = 0 := by
  ext n l
  rw [attachingBoundary_apply_apply,
    t99J02_genusTwo_homology_aux_attachingDegree]
  simp

/-- The degree-two homology model: the boundary kernel is all of `ℤ`. -/
noncomputable def t99J02_genusTwo_homology_aux_kernelIso :
    ModuleCat.of ℤ (BoundaryKernel t99J02_genusTwo_homology_aux_P) ≅
      ModuleCat.of ℤ ℤ := by
  have hker : BoundaryKernel t99J02_genusTwo_homology_aux_P = ⊤ := by
    show LinearMap.ker (attachingBoundary t99J02_genusTwo_homology_aux_P) = ⊤
    rw [t99J02_genusTwo_homology_aux_attachingBoundary]
    exact LinearMap.ker_zero
  rw [hker]
  exact Submodule.topEquiv.toModuleIso

/-- The degree-one homology model: the boundary cokernel is the free
abelian group on the four edge orbits. -/
noncomputable def t99J02_genusTwo_homology_aux_cokernelIso :
    ModuleCat.of ℤ (BoundaryCokernel t99J02_genusTwo_homology_aux_P) ≅
      ModuleCat.of ℤ (Fin 4 → ℤ) := by
  have hrange : LinearMap.range (attachingBoundary t99J02_genusTwo_homology_aux_P) = ⊥ := by
    rw [t99J02_genusTwo_homology_aux_attachingBoundary]
    exact LinearMap.range_zero
  have step1 : ModuleCat.of ℤ (BoundaryCokernel t99J02_genusTwo_homology_aux_P) ≅
      ModuleCat.of ℤ (PairingOrbit t99J02_genusTwo_homology_aux_P.pair → ℤ) :=
    (Submodule.quotEquivOfEqBot _ hrange).toModuleIso
  have step2 : ModuleCat.of ℤ (PairingOrbit t99J02_genusTwo_homology_aux_P.pair → ℤ) ≅
      ModuleCat.of ℤ (Fin 2 × Bool → ℤ) :=
    (LinearEquiv.funCongrLeft ℤ ℤ (orientableOrbitEquiv 2)).toModuleIso.symm
  have step3 : ModuleCat.of ℤ (Fin 2 × Bool → ℤ) ≅ ModuleCat.of ℤ (Fin 4 → ℤ) :=
    (LinearEquiv.funCongrLeft ℤ ℤ
      (((Equiv.refl (Fin 2)).prodCongr finTwoEquiv.symm).trans
        (finProdFinEquiv.trans (finCongr (show 2 * 2 = 4 by decide))))).toModuleIso.symm
  exact step1.trans (step2.trans step3)

-- Transport of the homology objects along the standard homeomorphism
-- between the polygon quotient and `Surface true 2`.
set_option maxHeartbeats 800000 in
noncomputable def t99J02_genusTwo_homology_aux_transport (k : ℕ) :
    H t99J02_genusTwo_homology_aux_P k ≅
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Surface true 2))) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).mapIso
      (TopCat.isoOfHomeo (standardPairingData_space_homeomorph true 2 Nat.zero_lt_two))

theorem t99J02_genusTwo_homology :
    let X := Surface true 2
    let H := fun (k : ℕ) =>
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))
    Nonempty (H 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (H 1 ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
      Nonempty (H 2 ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 3 ≤ k → IsZero (H k)) := by
  classical
  dsimp only
  refine ⟨⟨?_⟩, ⟨?_⟩, ⟨?_⟩, ?_⟩
  · exact (t99J02_genusTwo_homology_aux_transport 0).symm.trans
      (polygonQuotient_homology _).1.some
  · exact (t99J02_genusTwo_homology_aux_transport 1).symm.trans
      ((polygonQuotient_homology _).2.1.some.trans
        t99J02_genusTwo_homology_aux_cokernelIso)
  · exact (t99J02_genusTwo_homology_aux_transport 2).symm.trans
      ((polygonQuotient_homology _).2.2.1.some.trans
        t99J02_genusTwo_homology_aux_kernelIso)
  · intro k hk
    exact ((polygonQuotient_homology _).2.2.2 k hk).of_iso
      (t99J02_genusTwo_homology_aux_transport k).symm


/-! ## The connected sum

The route is in BLUEPRINT.md. Write `q₁`, `q₂` for the quotients of the disk onto `Surface true 1`,
`Surface true 2`. The hole in the torus is `ell` of the unit disk: it meets the unit circle only at
the vertex `1`. The upper half of the octagon goes onto the torus minus that hole by `phi`. -/

/-- `ell (z²) = (x + i y / 2)²` for `z = x + i y`, written without a square root. Homogeneous of
degree one, and `‖ell u‖ = 5/8 ‖u‖ + 3/8 Re u`. -/
def t99J02_ell (u : ℂ) : ℂ := ⟨3 / 8 * ‖u‖ + 5 / 8 * u.re, u.im / 2⟩

/-- The half-disk map: push the chord up to the half ellipse, fixing the arc, then square. -/
def t99J02_phi (z : ℂ) : ℂ :=
  (⟨z.re, (z.im + √(1 - z.re ^ 2)) / 2⟩ : ℂ) ^ 2

theorem t99J02_phi_mem (z : ConstructionTargets.Surfaces.Disk) : t99J02_phi (z : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
  have hz : ‖(z : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
  have hsq : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 ≤ 1 := by
    have h := Complex.sq_norm (z : ℂ)
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg (z : ℂ)]
  set x := (z : ℂ).re
  set y := (z : ℂ).im
  have hx : 0 ≤ 1 - x ^ 2 := by nlinarith [sq_nonneg y]
  set Y := √(1 - x ^ 2)
  have hY : 0 ≤ Y := Real.sqrt_nonneg _
  have hY2 : Y ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hx
  have hyY : y ^ 2 ≤ Y ^ 2 := by rw [hY2]; linarith
  have hb : |(y + Y) / 2| ≤ Y := by
    have := abs_le.mp (abs_le_of_sq_le_sq hyY hY)
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  rw [Metric.mem_closedBall, dist_zero_right, t99J02_phi, norm_pow, Complex.sq_norm,
    Complex.normSq_mk]
  have : ((y + Y) / 2) ^ 2 ≤ Y ^ 2 := by
    rw [← sq_abs ((y + Y) / 2)]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  nlinarith

/-- `phi` as a self-map of the disk. -/
def t99J02_phiDisk (z : ConstructionTargets.Surfaces.Disk) : ConstructionTargets.Surfaces.Disk := ⟨t99J02_phi (z : ℂ), t99J02_phi_mem z⟩

/-- The closed upper half of the octagon. -/
abbrev t99J02_Upper := {z : ConstructionTargets.Surfaces.Disk // 0 ≤ (z : ℂ).im}

/-- Rotation of the octagon by `π`, which exchanges the two handles. -/
def t99J02_neg (z : ConstructionTargets.Surfaces.Disk) : ConstructionTargets.Surfaces.Disk :=
  ⟨-(z : ℂ), mem_closedBall_zero_iff.mpr (by rw [norm_neg]; exact mem_closedBall_zero_iff.mp z.2)⟩

/-- `E 2` as `ℂ`. -/
def t99J02_chi (u : EuclideanSpace ℝ (Fin 2)) : ℂ := ⟨u 0, u 1⟩

/-- The reflection of `E 2` that becomes complex conjugation under `t99J02_chi`. -/
def t99J02_refl (u : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[u 0, -u 1]

/-- The stretch that takes radius `2` to radius `5/4` and fixes the unit disk. -/
def t99J02_stretch (u : ℂ) : ℂ :=
  if ‖u‖ ≤ 1 then u else (((1 + (‖u‖ - 1) / 4) / ‖u‖ : ℝ) : ℂ) * u

/-! ### Layer 0: plane geometry -/

/-- `‖ell u‖ = 5/8 ‖u‖ + 3/8 Re u`. Square both sides; `‖u‖² = re² + im²`. -/
theorem t99J02_ell_norm (u : ℂ) : ‖t99J02_ell u‖ = 5 / 8 * ‖u‖ + 3 / 8 * u.re := by
  have hu_sq : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hre : |u.re| ≤ ‖u‖ := Complex.abs_re_le_norm u
  have hrhs : 0 ≤ 5 / 8 * ‖u‖ + 3 / 8 * u.re := by
    have hre' : -‖u‖ ≤ u.re := by linarith [neg_abs_le u.re]
    nlinarith [norm_nonneg u]
  have hsq : ‖t99J02_ell u‖ ^ 2 = (5 / 8 * ‖u‖ + 3 / 8 * u.re) ^ 2 := by
    rw [Complex.sq_norm, t99J02_ell, Complex.normSq_mk]
    nlinarith
  nlinarith [norm_nonneg (t99J02_ell u)]

/-- `ell` is injective on all of `ℂ`. The imaginary part gives `Im u`; then `a ↦ 3/8 √(a²+b²) + 5/8 a`
is strictly increasing. -/
theorem t99J02_ell_injective : Function.Injective t99J02_ell := by
  intro u v h
  have him : u.im = v.im := by
    have him' := congrArg Complex.im h
    simp only [t99J02_ell] at him'
    linarith
  have hre : u.re = v.re := by
    have e1 : (3 / 8 : ℝ) * ‖u‖ + 5 / 8 * u.re = 3 / 8 * ‖v‖ + 5 / 8 * v.re := by
      have h' := congrArg Complex.re h
      simp only [t99J02_ell] at h'
      exact h'
    have e2 : (5 / 8 : ℝ) * ‖u‖ + 3 / 8 * u.re = 5 / 8 * ‖v‖ + 3 / 8 * v.re := by
      have h1 := t99J02_ell_norm u
      rw [h, t99J02_ell_norm v] at h1
      exact h1.symm
    linarith [e1, e2]
  exact Complex.ext hre him

/-- On the upper unit semicircle `phi z = z²`, since `√(1 - x²) = y`. -/
lemma t99J02_phi_edge_aux (z : ℂ) (hn : ‖z‖ = 1) (hi : 0 ≤ z.im) :
    t99J02_phi z = z ^ 2 := by
  have hre : 0 ≤ 1 - z.re ^ 2 := by
    have hn' : ‖z‖ ^ 2 = 1 := by rw [hn]; norm_num
    rw [Complex.sq_norm, Complex.normSq_apply] at hn'
    nlinarith
  have him : z.im ^ 2 = 1 - z.re ^ 2 := by
    have hn' : ‖z‖ ^ 2 = 1 := by rw [hn]; norm_num
    rw [Complex.sq_norm, Complex.normSq_apply] at hn'
    nlinarith
  have hsqrt : √(1 - z.re ^ 2) = z.im := by
    have hs := Real.sq_sqrt hre
    nlinarith [Real.sqrt_nonneg (1 - z.re ^ 2)]
  simp only [t99J02_phi, hsqrt]
  congr 1
  apply Complex.ext <;> simp <;> ring

theorem t99J02_phi_edge (e : ℕ) (he : e < 4) (t : Set.Icc (0 : ℝ) 1) :
    t99J02_phi (edgePoint 8 e t : ℂ) = (edgePoint 4 e t : ℂ) := by
  have hangle0 : 0 ≤ 2 * Real.pi * ((e : ℝ) + t.1) / 8 := by
    have he0 : (0 : ℝ) ≤ e := by positivity
    have ht0 := t.2.1
    positivity
  have hanglepi : 2 * Real.pi * ((e : ℝ) + t.1) / 8 ≤ Real.pi := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have he' : e ≤ 3 := by omega
    have heR : (e : ℝ) ≤ 3 := by exact_mod_cast he'
    have ht := t.2.2
    nlinarith
  have him : 0 ≤ ((edgePoint 8 e t : ConstructionTargets.Surfaces.Disk) : ℂ).im := by
    simp only [edgePoint, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, Complex.exp_im]
    convert Real.sin_nonneg_of_nonneg_of_le_pi hangle0 hanglepi using 1 <;> ring_nf <;> simp
  rw [t99J02_phi_edge_aux _ (norm_edgePoint 8 e t) him]
  simp only [edgePoint, pow_two, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A chord point lands on the boundary of the hole, at parameter `(x + i √(1-x²))²`. -/
theorem t99J02_phi_chord (x : ℝ) (hx : |x| ≤ 1) :
    t99J02_phi (x : ℂ) = t99J02_ell ((⟨x, √(1 - x ^ 2)⟩ : ℂ) ^ 2) := by
  have hx2 : 0 ≤ 1 - x ^ 2 := by
    have hxb := abs_le.mp hx
    nlinarith
  have hsqrt : (√(1 - x ^ 2)) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hx2
  have hsqrt_mul : √(1 - x ^ 2) * √(1 - x ^ 2) = 1 - x ^ 2 := by
    simpa [pow_two] using hsqrt
  have hbase : ‖(⟨x, √(1 - x ^ 2)⟩ : ℂ)‖ = 1 := by
    have hsquare : ‖(⟨x, √(1 - x ^ 2)⟩ : ℂ)‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_mk]
      nlinarith
    nlinarith [norm_nonneg (⟨x, √(1 - x ^ 2)⟩ : ℂ)]
  have hnorm : ‖(⟨x, √(1 - x ^ 2)⟩ : ℂ) ^ 2‖ = 1 := by
    rw [norm_pow, hbase]
    norm_num
  apply Complex.ext
  · rw [t99J02_phi, t99J02_ell]
    rw [hnorm]
    simp [pow_two]
    ring_nf at hsqrt_mul ⊢
    nlinarith
  · rw [t99J02_phi, t99J02_ell]
    simp [pow_two]
    ring

/-- Every unit complex number is `(x + i √(1-x²))²` for a real `x`, `|x| ≤ 1`, namely the root in
the closed upper half plane. -/
theorem t99J02_circle_param (s : ℂ) (hs : ‖s‖ = 1) :
    ∃ x : ℝ, |x| ≤ 1 ∧ s = (⟨x, √(1 - x ^ 2)⟩ : ℂ) ^ 2 := by
  have hs' : s.re ^ 2 + s.im ^ 2 = 1 := by
    have hnorm := Complex.sq_norm s
    rw [hs, Complex.normSq_apply] at hnorm
    nlinarith
  set y : ℝ := √((1 - s.re) / 2)
  have hre_le : s.re ≤ 1 := by
    nlinarith [sq_nonneg (s.re - 1), sq_nonneg s.im]
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y ^ 2 = (1 - s.re) / 2 := by
    exact Real.sq_sqrt (by linarith)
  by_cases hy : y = 0
  · have hre : s.re = 1 := by nlinarith
    have him : s.im = 0 := by nlinarith [sq_nonneg s.im]
    refine ⟨1, by norm_num, ?_⟩
    apply Complex.ext
    · norm_num [hre, pow_two, Complex.mul_re]
    · norm_num [him, pow_two, Complex.mul_im]
  · let x := s.im / (2 * y)
    have hxy : 2 * x * y = s.im := by
      dsimp [x]
      field_simp
    have hx2 : x ^ 2 = (1 + s.re) / 2 := by
      dsimp [x]
      field_simp [hy]
      nlinarith [hy2]
    have hx_le : |x| ≤ 1 := by
      rw [← sq_le_one_iff_abs_le_one]
      rw [hx2]
      nlinarith [sq_nonneg (s.re + 1), sq_nonneg s.im]
    have hsqrt : √(1 - x ^ 2) = y := by
      rw [← Real.sqrt_sq hy0]
      congr 1
      nlinarith [hx2, hy2]
    refine ⟨x, hx_le, ?_⟩
    rw [hsqrt]
    apply Complex.ext
    · simp [pow_two, Complex.mul_re]
      nlinarith [hx2, hy2]
    · simp [pow_two, Complex.mul_im]
      nlinarith

/-- The image of the closed upper half disk misses the open hole. Write `ζ = x + i y'` for the
inner point, `y' ≥ √(1-x²)/2`. If `ζ² = ell u`, `‖u‖ < 1`, take the root `u = v²`, `v = a + i b`,
`b ≥ 0`; then `ζ² = (a + i b/2)²` with `a² + b² < 1`, so `ζ = ±(a + i b/2)`, and each sign contradicts
`y' ≥ √(1-x²)/2`. -/
theorem t99J02_phi_not_hole (z : ConstructionTargets.Surfaces.Disk) (hz : 0 ≤ (z : ℂ).im) (u : ℂ) (hu : ‖u‖ < 1) :
    t99J02_phi (z : ℂ) ≠ t99J02_ell u := by
  intro h
  set x := (z : ℂ).re
  set y := (z : ℂ).im
  have hxy : x ^ 2 + y ^ 2 ≤ 1 := by
    have hz_norm : ‖(z : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
    have hn := Complex.sq_norm (z : ℂ)
    rw [Complex.normSq_apply] at hn
    nlinarith [norm_nonneg (z : ℂ)]
  have hx : 0 ≤ 1 - x ^ 2 := by nlinarith [sq_nonneg y]
  set Y := √(1 - x ^ 2)
  have hY : 0 ≤ Y := Real.sqrt_nonneg _
  have hY2 : Y ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hx
  have hphi_norm : ‖t99J02_phi (z : ℂ)‖ = x ^ 2 + ((y + Y) / 2) ^ 2 := by
    rw [t99J02_phi, norm_pow, Complex.sq_norm, Complex.normSq_mk]
    dsimp [x, y, Y]
    ring
  have hphi_re : (t99J02_phi (z : ℂ)).re = x ^ 2 - ((y + Y) / 2) ^ 2 := by
    dsimp [x, y, Y]
    simp only [t99J02_phi, pow_two, Complex.mul_re]
  have hell_norm := t99J02_ell_norm u
  have hell_re : (t99J02_ell u).re = 3 / 8 * ‖u‖ + 5 / 8 * u.re := by
    rfl
  rw [h, hell_norm] at hphi_norm
  rw [h, hell_re] at hphi_re
  have hlarge : 2 ≤
      5 * (5 / 8 * ‖u‖ + 3 / 8 * u.re) -
        3 * (3 / 8 * ‖u‖ + 5 / 8 * u.re) := by
    nlinarith [hz, hY, hY2]
  nlinarith

/-- Everything in the disk outside the open hole is hit from the upper half. Take the root
`ζ = x + i y'` of `w` with `y' ≥ 0`. If `y' < √(1-x²)/2` then `w = ell ((x + 2 i y')²)` with
`x² + 4y'² < 1`, a contradiction; so `z = x + i (2y' - √(1-x²))` works. -/
theorem t99J02_phi_surj (w : ConstructionTargets.Surfaces.Disk)
    (hw : ∀ u : ℂ, ‖u‖ < 1 → (w : ℂ) ≠ t99J02_ell u) :
    ∃ z : ConstructionTargets.Surfaces.Disk, 0 ≤ (z : ℂ).im ∧ t99J02_phi (z : ℂ) = (w : ℂ) := by
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (w : ℂ) (n := 2) (by norm_num)
  let ζ : ℂ := if 0 ≤ v.im then v else -v
  have hζim : 0 ≤ ζ.im := by
    dsimp [ζ]
    split_ifs with h
    · exact h
    · simp only [Complex.neg_im]
      linarith
  have hζsq : ζ ^ 2 = (w : ℂ) := by
    dsimp [ζ]
    split_ifs
    · exact hv
    · simpa using hv
  have hζnorm : ‖ζ‖ ≤ 1 := by
    have hw_norm : ‖(w : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp w.2
    have hpow : ‖ζ‖ ^ 2 = ‖(w : ℂ)‖ := by
      rw [← hζsq, norm_pow]
    nlinarith [norm_nonneg ζ]
  set x : ℝ := ζ.re
  set y : ℝ := ζ.im
  have hy : 0 ≤ y := hζim
  have hxy : x ^ 2 + y ^ 2 ≤ 1 := by
    have hn := Complex.sq_norm ζ
    rw [Complex.normSq_apply] at hn
    nlinarith [norm_nonneg ζ]
  have hx : 0 ≤ 1 - x ^ 2 := by nlinarith [sq_nonneg y]
  set Y : ℝ := √(1 - x ^ 2)
  have hY : 0 ≤ Y := Real.sqrt_nonneg _
  have hY2 : Y ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hx
  have hyY : y ≤ Y := by nlinarith
  have hhalf : Y / 2 ≤ y := by
    by_contra h
    have hylt : y < Y / 2 := lt_of_not_ge h
    let u : ℂ := (⟨x, 2 * y⟩ : ℂ) ^ 2
    have hu : ‖u‖ < 1 := by
      dsimp [u]
      rw [norm_pow, Complex.sq_norm, Complex.normSq_mk]
      nlinarith
    have hell : t99J02_ell u = ζ ^ 2 := by
      apply Complex.ext
      · rw [t99J02_ell]
        have hunorm : ‖u‖ = x ^ 2 + 4 * y ^ 2 := by
          dsimp [u]
          rw [norm_pow, Complex.sq_norm, Complex.normSq_mk]
          nlinarith [sq_nonneg x, sq_nonneg y]
        rw [hunorm]
        simp [u, pow_two, Complex.mul_re]
        ring
      · rw [t99J02_ell]
        simp [u, pow_two, Complex.mul_im]
        ring
    exact hw u hu (by rw [← hζsq, hell])
  let zc : ℂ := ⟨x, 2 * y - Y⟩
  have hzmem : zc ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, Complex.norm_def, Real.sqrt_le_one]
    · simp only [Complex.normSq_apply, zc]
      nlinarith
  let z : ConstructionTargets.Surfaces.Disk := ⟨zc, hzmem⟩
  refine ⟨z, ?_, ?_⟩
  · change 0 ≤ 2 * y - Y
    linarith
  · rw [t99J02_phi]
    change (⟨x, ((2 * y - Y) + √(1 - x ^ 2)) / 2⟩ : ℂ) ^ 2 = (w : ℂ)
    rw [show √(1 - x ^ 2) = Y by rfl]
    convert hζsq using 1
    apply Complex.ext <;> simp [x, y]

/-- `phi` is injective on the upper half except that `1` and `-1` both go to `1`. Since `ζ` has
nonnegative imaginary part, `ζ² = ζ'²` gives `ζ = ζ'` or `ζ = -ζ'`, and in the second case both are
real, so `ζ = ±1`. -/
theorem t99J02_phi_injOn (z z' : ConstructionTargets.Surfaces.Disk) (hz : 0 ≤ (z : ℂ).im) (hz' : 0 ≤ (z' : ℂ).im)
    (h : t99J02_phi (z : ℂ) = t99J02_phi (z' : ℂ)) :
    z = z' ∨ (((z : ℂ) = 1 ∨ (z : ℂ) = -1) ∧ ((z' : ℂ) = 1 ∨ (z' : ℂ) = -1)) := by
  let w : ℂ := ⟨(z : ℂ).re,
    ((z : ℂ).im + √(1 - (z : ℂ).re ^ 2)) / 2⟩
  let w' : ℂ := ⟨(z' : ℂ).re,
    ((z' : ℂ).im + √(1 - (z' : ℂ).re ^ 2)) / 2⟩
  have hsq : w ^ 2 = w' ^ 2 := by
    simpa only [t99J02_phi, w, w'] using h
  rcases eq_or_eq_neg_of_sq_eq_sq w w' hsq with heq | hneg
  · left
    apply Subtype.ext
    apply Complex.ext
    · simpa [w, w'] using congrArg Complex.re heq
    · have hre : (z : ℂ).re = (z' : ℂ).re := by
        simpa [w, w'] using congrArg Complex.re heq
      have him : ((z : ℂ).im + √(1 - (z : ℂ).re ^ 2)) / 2 =
          ((z' : ℂ).im + √(1 - (z' : ℂ).re ^ 2)) / 2 := by
        simpa [w, w'] using congrArg Complex.im heq
      rw [hre] at him
      linarith
  · right
    have hwim : 0 ≤ w.im := by
      dsimp [w]
      positivity
    have hwim' : 0 ≤ w'.im := by
      dsimp [w']
      positivity
    have himneg : w.im = -w'.im := congrArg Complex.im hneg
    have hw0 : w.im = 0 := by linarith
    have hw0' : w'.im = 0 := by linarith
    have hy0 : (z : ℂ).im = 0 := by
      have hs := Real.sqrt_nonneg (1 - (z : ℂ).re ^ 2)
      dsimp [w] at hw0
      linarith
    have hy0' : (z' : ℂ).im = 0 := by
      have hs := Real.sqrt_nonneg (1 - (z' : ℂ).re ^ 2)
      dsimp [w'] at hw0'
      linarith
    have hxnorm : (z : ℂ).re ^ 2 ≤ 1 := by
      have hn : ‖(z : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
      have hs := Complex.sq_norm (z : ℂ)
      rw [Complex.normSq_apply, hy0] at hs
      nlinarith [norm_nonneg (z : ℂ)]
    have hxnorm' : (z' : ℂ).re ^ 2 ≤ 1 := by
      have hn : ‖(z' : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp z'.2
      have hs := Complex.sq_norm (z' : ℂ)
      rw [Complex.normSq_apply, hy0'] at hs
      nlinarith [norm_nonneg (z' : ℂ)]
    have hsqrt0 : √(1 - (z : ℂ).re ^ 2) = 0 := by
      dsimp [w] at hw0
      rw [hy0] at hw0
      linarith
    have hsqrt0' : √(1 - (z' : ℂ).re ^ 2) = 0 := by
      dsimp [w'] at hw0'
      rw [hy0'] at hw0'
      linarith
    have hx2 : (z : ℂ).re ^ 2 = 1 := by
      have hs := Real.sq_sqrt (show 0 ≤ 1 - (z : ℂ).re ^ 2 by linarith)
      rw [hsqrt0] at hs
      nlinarith
    have hx2' : (z' : ℂ).re ^ 2 = 1 := by
      have hs := Real.sq_sqrt (show 0 ≤ 1 - (z' : ℂ).re ^ 2 by linarith)
      rw [hsqrt0'] at hs
      nlinarith
    constructor
    · rcases (sq_eq_one_iff).mp hx2 with hx | hx
      · left
        apply Complex.ext <;> simp [hx, hy0]
      · right
        apply Complex.ext <;> simp [hx, hy0]
    · rcases (sq_eq_one_iff).mp hx2' with hx | hx
      · left
        apply Complex.ext <;> simp [hx, hy0']
      · right
        apply Complex.ext <;> simp [hx, hy0']

/-- `phi` reaches the unit circle only from the unit circle: `‖ζ‖² = x² + ((y+Y)/2)²`. -/
theorem t99J02_phi_norm (z : ConstructionTargets.Surfaces.Disk) (hz : 0 ≤ (z : ℂ).im)
    (h : ‖t99J02_phi (z : ℂ)‖ = 1) : ‖(z : ℂ)‖ = 1 := by
  have hz_le : ‖(z : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
  set x := (z : ℂ).re
  set y := (z : ℂ).im
  have hxy : x ^ 2 + y ^ 2 ≤ 1 := by
    have hn := Complex.sq_norm (z : ℂ)
    rw [Complex.normSq_apply] at hn
    nlinarith [norm_nonneg (z : ℂ)]
  have hx : 0 ≤ 1 - x ^ 2 := by nlinarith [sq_nonneg y]
  set Y := √(1 - x ^ 2)
  have hY : 0 ≤ Y := Real.sqrt_nonneg _
  have hY2 : Y ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hx
  have heq : x ^ 2 + ((y + Y) / 2) ^ 2 = 1 := by
    rw [t99J02_phi, norm_pow, Complex.sq_norm, Complex.normSq_mk] at h
    nlinarith
  have hyY : y = Y := by
    nlinarith [hz, hY]
  have hnormsq : ‖(z : ℂ)‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  nlinarith [norm_nonneg (z : ℂ)]

/-- The stretch is continuous, injective on radius `2`, and lands in radius `5/4`. -/
theorem t99J02_stretch_spec :
    Continuous t99J02_stretch ∧
      Set.InjOn t99J02_stretch (Metric.closedBall 0 2) ∧
      (∀ u, ‖u‖ ≤ 2 → ‖t99J02_stretch u‖ ≤ 5 / 4) ∧
      (∀ u, ‖u‖ ≤ 1 → t99J02_stretch u = u) := by
  have hnorm : ∀ u : ℂ, ‖t99J02_stretch u‖ =
      if ‖u‖ ≤ 1 then ‖u‖ else 1 + (‖u‖ - 1) / 4 := by
    intro u
    by_cases hu : ‖u‖ ≤ 1
    · simp [t99J02_stretch, hu]
    · have hu0 : ‖u‖ ≠ 0 := by
        intro h
        apply hu
        rw [h]
        norm_num
      have hp : 0 ≤ 1 + (‖u‖ - 1) / 4 := by
        have : 1 < ‖u‖ := lt_of_not_ge hu
        linarith
      rw [t99J02_stretch, if_neg hu, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (div_nonneg hp (norm_nonneg u)),
        div_mul_cancel₀ _ hu0, if_neg hu]
  have hcont : Continuous t99J02_stretch := by
    change Continuous (fun u : ℂ =>
      if ‖u‖ ≤ 1 then u else (((1 + (‖u‖ - 1) / 4) / ‖u‖ : ℝ) : ℂ) * u)
    apply continuous_if_le continuous_norm continuous_const continuous_id.continuousOn
    · refine ContinuousOn.mul ?_ continuous_id.continuousOn
      intro u hu
      apply ContinuousAt.continuousWithinAt
      have hu0 : ‖u‖ ≠ 0 := by
        have : 1 ≤ ‖u‖ := hu
        positivity
      have hs : ContinuousAt (fun x : ℂ => (1 + (‖x‖ - 1) / 4) / ‖x‖) u := by
        exact (continuousAt_const.add
          ((continuous_norm.continuousAt.sub continuousAt_const).div_const 4)).div
            continuous_norm.continuousAt hu0
      exact Complex.continuous_ofReal.continuousAt.comp hs
    · intro u hu
      simp only at hu
      rw [hu]
      norm_num
  have hinj : Set.InjOn t99J02_stretch (Metric.closedBall 0 2) := by
    intro u hu v hv huv
    have hn : ‖t99J02_stretch u‖ = ‖t99J02_stretch v‖ := congrArg norm huv
    rw [hnorm, hnorm] at hn
    have huvnorm : ‖u‖ = ‖v‖ := by
      by_cases hu1 : ‖u‖ ≤ 1 <;> by_cases hv1 : ‖v‖ ≤ 1
      · simp [hu1, hv1] at hn
        exact hn
      · simp [hu1, hv1] at hn
        have hvgt : 1 < ‖v‖ := lt_of_not_ge hv1
        linarith
      · simp [hu1, hv1] at hn
        have hugt : 1 < ‖u‖ := lt_of_not_ge hu1
        linarith
      · simp [hu1, hv1] at hn
        linarith
    by_cases hu1 : ‖u‖ ≤ 1
    · have hv1 : ‖v‖ ≤ 1 := by rwa [← huvnorm]
      simpa [t99J02_stretch, hu1, hv1] using huv
    · have hv1 : ¬ ‖v‖ ≤ 1 := by rwa [← huvnorm]
      have hu0 : ‖u‖ ≠ 0 := by
        intro h
        apply hu1
        rw [h]
        norm_num
      have hc : (((1 + (‖u‖ - 1) / 4) / ‖u‖ : ℝ) : ℂ) ≠ 0 := by
        have hnum : 0 < 1 + (‖u‖ - 1) / 4 := by
          have : 1 < ‖u‖ := lt_of_not_ge hu1
          linarith
        have hden : (0 : ℝ) < ‖u‖ := lt_trans (by norm_num) (lt_of_not_ge hu1)
        exact_mod_cast (ne_of_gt (div_pos hnum hden))
      simp only [t99J02_stretch, if_neg hu1, if_neg hv1] at huv
      rw [← huvnorm] at huv
      exact mul_left_cancel₀ hc huv
  refine ⟨hcont, hinj, ?_, ?_⟩
  · intro u hu
    rw [hnorm]
    by_cases hu1 : ‖u‖ ≤ 1
    · simp [hu1]
      linarith
    · simp [hu1]
      linarith
  · intro u hu
    simp [t99J02_stretch, hu]

/-- `t99J02_chi` is a homeomorphism preserving norm, and conjugation is `t99J02_refl`. -/
theorem t99J02_chi_spec :
    Continuous t99J02_chi ∧ Function.Injective t99J02_chi ∧
      (∀ u, ‖t99J02_chi u‖ = ‖u‖) ∧
      (∀ u, t99J02_chi (t99J02_refl u) = (starRingEnd ℂ) (t99J02_chi u)) ∧
      Continuous t99J02_refl ∧ Function.Injective t99J02_refl ∧ (∀ u, ‖t99J02_refl u‖ = ‖u‖) ∧
      (∀ v : ℂ, ∃ u, t99J02_chi u = v) := by
  have hchi_cont : Continuous t99J02_chi := by
    simpa [t99J02_chi] using
      Complex.equivRealProdCLM.symm.continuous.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).prodMk
          (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1))
  have hchi_norm : ∀ u, ‖t99J02_chi u‖ = ‖u‖ := by
    intro u
    rw [Complex.norm_eq_sqrt_sq_add_sq, EuclideanSpace.norm_eq]
    simp [t99J02_chi, Fin.sum_univ_two]
  have hchi_inj : Function.Injective t99J02_chi := by
    intro u v h
    apply PiLp.ext
    intro i
    fin_cases i
    · exact congrArg Complex.re h
    · exact congrArg Complex.im h
  have hrefl_cont : Continuous t99J02_refl := by
    change Continuous (fun u : EuclideanSpace ℝ (Fin 2) => !₂[u 0, -u 1])
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      (continuous_pi fun i => by
        fin_cases i
        · simpa using PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
        · simpa using (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).neg)
  have hrefl_inj : Function.Injective t99J02_refl := by
    intro u v h
    apply PiLp.ext
    intro i
    fin_cases i
    · simpa [t99J02_refl] using congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h
    · have hi := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) h
      simpa [t99J02_refl] using congrArg Neg.neg hi
  have hrefl_norm : ∀ u, ‖t99J02_refl u‖ = ‖u‖ := by
    intro u
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp [t99J02_refl, Fin.sum_univ_two]
  refine ⟨hchi_cont, hchi_inj, hchi_norm, ?_, hrefl_cont, hrefl_inj, hrefl_norm, ?_⟩
  · intro u
    apply Complex.ext <;> simp [t99J02_chi, t99J02_refl]
  · intro v
    refine ⟨!₂[v.re, v.im], ?_⟩
    apply Complex.ext <;> simp [t99J02_chi]

/-- The dilated hole does not meet its own lattice translates. For `‖u‖ ≤ 5/4`, with
`w = ell u`: `Re w ± Im w ≥ -5/8` (Cauchy: `7/8 r + 5/8 a ± b/2 ≥ 0`, for `u = a + i b`, `r = ‖u‖`) and `‖w‖ ≤ 5/4`, so both coordinates `A, B` of the chart
`(chart w).re ± (chart w).im) / 2` lie in `[-5/16, 5/8]`. Two such with equal image in the torus
differ by integers of size at most `15/16`, hence are equal, and the chart is injective
(`klein_cut_chartInv_chart`). -/
theorem t99J02_torus_injOn (u v : ℂ) (hu : ‖u‖ ≤ 5 / 4) (hv : ‖v‖ ≤ 5 / 4)
    (h : t95J03_torus_bridge_aux_f (t99J02_ell u) = t95J03_torus_bridge_aux_f (t99J02_ell v)) :
    t99J02_ell u = t99J02_ell v := by
  sorry

/-! ### Layer 0: quotient facts -/

/-- `Surface` identifies only boundary points. -/
theorem t99J02_rel_boundary (o : Bool) (g : ℕ) {x y : ConstructionTargets.Surfaces.Disk}
    (h : Relation.EqvGen (SurfaceRel o g) x y) :
    x = y ∨ (‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1) := by
  induction h with
  | rel x y h =>
      right
      simp only [SurfaceRel] at h
      split at h
      · rcases h with ⟨j, hj, t, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
          constructor <;> apply norm_edgePoint
      · rcases h with ⟨j, hj, t, rfl, rfl⟩
        constructor <;> apply norm_edgePoint
  | refl x => exact Or.inl rfl
  | symm x y h ih =>
      rcases ih with hxy | ⟨hx, hy⟩
      · exact Or.inl hxy.symm
      · exact Or.inr ⟨hy, hx⟩
  | trans x y z hxy hyz ihxy ihyz =>
      rcases ihxy with rfl | ⟨hx, hy⟩
      · exact ihyz
      · rcases ihyz with rfl | ⟨hy', hz⟩
        · exact Or.inr ⟨hx, hy⟩
        · exact Or.inr ⟨hx, hz⟩

/-- Rotation by `π` descends to the octagon quotient: it sends the pairs of handle `j` to those of
handle `1 - j`. -/
lemma t99J02_q2_neg_aux_edge (e : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    t99J02_neg (edgePoint 8 e t) = edgePoint 8 (e + 4) t := by
  apply Subtype.ext
  simp only [t99J02_neg, edgePoint, Subtype.coe_mk]
  rw [← Complex.exp_add_pi_mul_I]
  congr 1
  push_cast
  ring

lemma t99J02_q2_neg_aux_period (e : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    edgePoint 8 (e + 8) t = edgePoint 8 e t := by
  apply Subtype.ext
  simp only [edgePoint, Subtype.coe_mk]
  have hexp : Complex.I * (2 * Real.pi * (((e + 8 : ℕ) : ℝ) + t.1) / (8 : ℕ)) =
      Complex.I * (2 * Real.pi * ((e : ℝ) + t.1) / (8 : ℕ)) + 2 * Real.pi * Complex.I := by
    push_cast
    ring
  rw [hexp]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma t99J02_q2_neg_aux_map {z z' : ConstructionTargets.Surfaces.Disk}
    (heq : Relation.EqvGen (SurfaceRel true 2) z z') :
    Relation.EqvGen (SurfaceRel true 2) (t99J02_neg z) (t99J02_neg z') := by
  induction heq with
  | rel x y hxy =>
      apply Relation.EqvGen.rel
      simp only [SurfaceRel, if_true] at hxy ⊢
      rcases hxy with ⟨j, hj, t, hxy⟩
      have hj' : j = 0 ∨ j = 1 := by omega
      rcases hj' with rfl | rfl
      · refine ⟨1, by omega, t, ?_⟩
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · left
          norm_num
          constructor <;> apply t99J02_q2_neg_aux_edge
        · right
          norm_num
          constructor <;> apply t99J02_q2_neg_aux_edge
      · refine ⟨0, by omega, t, ?_⟩
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · left
          norm_num
          constructor
          · rw [t99J02_q2_neg_aux_edge]
            exact t99J02_q2_neg_aux_period 0 t
          · rw [t99J02_q2_neg_aux_edge]
            exact t99J02_q2_neg_aux_period 2 _
        · right
          norm_num
          constructor
          · rw [t99J02_q2_neg_aux_edge]
            exact t99J02_q2_neg_aux_period 1 t
          · rw [t99J02_q2_neg_aux_edge]
            exact t99J02_q2_neg_aux_period 3 _
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ihxy ihyz => exact Relation.EqvGen.trans _ _ _ ihxy ihyz

theorem t99J02_q2_neg {z z' : ConstructionTargets.Surfaces.Disk}
    (h : surfaceQuotient true 2 z = surfaceQuotient true 2 z') :
    surfaceQuotient true 2 (t99J02_neg z) = surfaceQuotient true 2 (t99J02_neg z') := by
  apply Quotient.sound
  exact t99J02_q2_neg_aux_map (Quotient.exact h)

/-- The real points `1`, `-1` of the octagon are one point of the surface; both are vertices
(`orientable_standard_oneVertex`, transported by `orientableStandardSpaceHomeomorph`). -/
theorem t99J02_q2_one_neg_one (h1 : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1)
    (h2 : (-1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1) :
    surfaceQuotient true 2 ⟨1, h1⟩ = surfaceQuotient true 2 ⟨-1, h2⟩ := by
  sorry

/-- Identifications of the torus lift to the upper arc of the octagon. Induct on the `EqvGen`, with
`P x y := x = y ∨ (both on the circle and the statement holds)`. A generator is an edge pair of
`Surface true 1`, and its upper roots are the same edge pair of handle `0` of `Surface true 2`,
except that the root of `1` may be `1` or `-1`: use `t99J02_q2_one_neg_one`. -/
theorem t99J02_edge_lift {x y : ConstructionTargets.Surfaces.Disk} (h : Relation.EqvGen (SurfaceRel true 1) x y)
    (hx : ‖(x : ℂ)‖ = 1) (z z' : ConstructionTargets.Surfaces.Disk) (hz : 0 ≤ (z : ℂ).im) (hz' : 0 ≤ (z' : ℂ).im)
    (hzx : (z : ℂ) ^ 2 = x) (hzy : (z' : ℂ) ^ 2 = y) :
    surfaceQuotient true 2 z = surfaceQuotient true 2 z' := by
  sorry

/-! ### Layer 1: the two collars and the torus side -/

/-- The small map of the collar: `ell` into the disk, then the quotient. -/
theorem t99J02_ell_mem (u : ℂ) (hu : ‖u‖ ≤ 1) :
    t99J02_ell u ∈ Metric.closedBall (0 : ℂ) 1 := by
  sorry

/-- Fibres of `q₁ ∘ phi` on the upper half are fibres of `q₂`. Off the circle `phi z = phi z'`, so use
`t99J02_phi_injOn`; on the circle `phi z = z²` and use `t99J02_edge_lift`. -/
theorem t99J02_fibre (z z' : ConstructionTargets.Surfaces.Disk) (hz : 0 ≤ (z : ℂ).im) (hz' : 0 ≤ (z' : ℂ).im)
    (h : surfaceQuotient true 1 (t99J02_phiDisk z) = surfaceQuotient true 1 (t99J02_phiDisk z')) :
    surfaceQuotient true 2 z = surfaceQuotient true 2 z' := by
  sorry

/-- The collar. Its large map is `e⁻¹ ∘ f ∘ ell ∘ stretch ∘ chi`, for `e`, `f` from
`t95J03_torus_bridge_spec`; injective by `t99J02_torus_injOn`, and an embedding because the domain
is compact and `Surface true 1` is Hausdorff. -/
theorem t99J02_collar_exists :
    ∃ c : BallCollar 2 (Surface true 1),
      ∀ u : ConstructionTargets.CollaredConnectedSumHomology.Disk 2 1,
        ∃ h : t99J02_ell (t99J02_chi u.1) ∈ Metric.closedBall (0 : ℂ) 1,
          c.smallMap u = surfaceQuotient true 1 ⟨t99J02_ell (t99J02_chi u.1), h⟩ := by
  sorry

/-- The same collar precomposed with the reflection. -/
def t99J02_collar_reflect_aux_homeomorph (r : ℝ) :
    ConstructionTargets.CollaredConnectedSumHomology.Disk 2 r ≃ₜ
      ConstructionTargets.CollaredConnectedSumHomology.Disk 2 r where
  toFun u := ⟨t99J02_refl u.1, by
    apply mem_closedBall_zero_iff.mpr
    rw [t99J02_chi_spec.2.2.2.2.2.2.1]
    exact mem_closedBall_zero_iff.mp u.2⟩
  invFun u := ⟨t99J02_refl u.1, by
    apply mem_closedBall_zero_iff.mpr
    rw [t99J02_chi_spec.2.2.2.2.2.2.1]
    exact mem_closedBall_zero_iff.mp u.2⟩
  left_inv u := by
    apply Subtype.ext
    apply t99J02_chi_spec.2.1
    simp only [t99J02_chi_spec.2.2.2.1]
    simp
  right_inv u := by
    apply Subtype.ext
    apply t99J02_chi_spec.2.1
    simp only [t99J02_chi_spec.2.2.2.1]
    simp
  continuous_toFun :=
    (t99J02_chi_spec.2.2.2.2.1.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (t99J02_chi_spec.2.2.2.2.1.comp continuous_subtype_val).subtype_mk _

theorem t99J02_collar_reflect (c : BallCollar 2 (Surface true 1)) :
    ∃ c' : BallCollar 2 (Surface true 1),
      ∀ u : ConstructionTargets.CollaredConnectedSumHomology.Disk 2 1,
        ∃ hu : t99J02_refl u.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
          c'.smallMap u = c.smallMap ⟨t99J02_refl u.1, hu⟩ := by
  let e1 := t99J02_collar_reflect_aux_homeomorph 1
  let e2 := t99J02_collar_reflect_aux_homeomorph 2
  let c' : BallCollar 2 (Surface true 1) :=
    { smallMap := c.smallMap ∘ e1
      largeMap := c.largeMap ∘ e2
      smallEmbedding := c.smallEmbedding.comp e1.isEmbedding
      largeEmbedding := c.largeEmbedding.comp e2.isEmbedding
      compatible := by
        funext u
        exact c.largeMap_unitToLarge (e1 u) }
  refine ⟨c', ?_⟩
  intro u
  have hu : t99J02_refl u.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    apply mem_closedBall_zero_iff.mpr
    rw [t99J02_chi_spec.2.2.2.2.2.2.1]
    exact mem_closedBall_zero_iff.mp u.2
  exact ⟨hu, rfl⟩

/-! ### Layer 1: general facts about `ConnectedSum` -/

section ConnectedSumFacts

variable {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
  (c₁ : BallCollar 2 M₁) (c₂ : BallCollar 2 M₂)

/-- The quotient map of the connected sum. -/
def t99J02_mk (p : Sum c₁.Punctured c₂.Punctured) : ConnectedSum c₁ c₂ := Quotient.mk _ p

/-- Equalities in the connected sum: the relation is explicit, because `boundaryMap` is injective.
Descend `Sum → Prop` families through the quotient, or define the explicit equivalence relation and
show it contains `EqvGen (GlueRel c₁ c₂)`. -/
theorem t99J02_mk_eq (p p' : Sum c₁.Punctured c₂.Punctured)
    (h : t99J02_mk c₁ c₂ p = t99J02_mk c₁ c₂ p') :
    p = p' ∨ (∃ s, p = Sum.inl (c₁.boundaryMap s) ∧ p' = Sum.inr (c₂.boundaryMap s)) ∨
      (∃ s, p = Sum.inr (c₂.boundaryMap s) ∧ p' = Sum.inl (c₁.boundaryMap s)) := by
  let R : Sum c₁.Punctured c₂.Punctured → Sum c₁.Punctured c₂.Punctured → Prop :=
    fun p p' =>
      p = p' ∨ (∃ s, p = Sum.inl (c₁.boundaryMap s) ∧
        p' = Sum.inr (c₂.boundaryMap s)) ∨
        (∃ s, p = Sum.inr (c₂.boundaryMap s) ∧
          p' = Sum.inl (c₁.boundaryMap s))
  have boundary_injective (c : BallCollar 2 M₁) : Function.Injective c.boundaryMap := by
    intro s t hst
    have hsmall : sphereToDisk 2 s = sphereToDisk 2 t :=
      c.smallEmbedding.injective (congrArg Subtype.val hst)
    apply Subtype.ext
    exact congrArg (fun x : Disk 2 1 => x.1) hsmall
  have boundary_injective₂ : Function.Injective c₂.boundaryMap := by
    intro s t hst
    have hsmall : sphereToDisk 2 s = sphereToDisk 2 t :=
      c₂.smallEmbedding.injective (congrArg Subtype.val hst)
    apply Subtype.ext
    exact congrArg (fun x : Disk 2 1 => x.1) hsmall
  have hR : Equivalence R := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact Or.inl rfl
    · intro x y hxy
      rcases hxy with hxy | ⟨s, rfl, rfl⟩ | ⟨s, rfl, rfl⟩
      · exact Or.inl hxy.symm
      · exact Or.inr (Or.inr ⟨s, rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨s, rfl, rfl⟩)
    · intro x y z hxy hyz
      rcases hxy with rfl | ⟨s, rfl, rfl⟩ | ⟨s, rfl, rfl⟩
      · exact hyz
      · rcases hyz with hyz | ⟨t, ht, _⟩ | ⟨t, ht, rfl⟩
        · subst z
          exact Or.inr (Or.inl ⟨s, rfl, rfl⟩)
        · cases ht
        · have hst : s = t := boundary_injective₂ (Sum.inr.inj ht)
          subst t
          exact Or.inl rfl
      · rcases hyz with hyz | ⟨t, ht, rfl⟩ | ⟨t, ht, _⟩
        · subst z
          exact Or.inr (Or.inr ⟨s, rfl, rfl⟩)
        · have hst : s = t := boundary_injective c₁ (Sum.inl.inj ht)
          subst t
          exact Or.inl rfl
        · cases ht
  apply (hR.eqvGen_iff).mp
  apply Relation.EqvGen.mono (r := GlueRel c₁ c₂)
  · intro a b hab
    cases hab with
    | boundary s => exact Or.inr (Or.inl ⟨s, rfl, rfl⟩)
  · change
      Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) p =
        Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) p' at h
    exact Quotient.exact h

/-- A subset of the connected sum is closed when both pullbacks are. -/
theorem t99J02_isClosed_of (A : Set (ConnectedSum c₁ c₂))
    (h₁ : IsClosed ((fun p => t99J02_mk c₁ c₂ (Sum.inl p)) ⁻¹' A))
    (h₂ : IsClosed ((fun p => t99J02_mk c₁ c₂ (Sum.inr p)) ⁻¹' A)) : IsClosed A := by
  apply isClosed_coinduced.mpr
  exact isClosed_sum_iff.mpr ⟨h₁, h₂⟩

theorem t99J02_continuous_mk : Continuous (t99J02_mk c₁ c₂) := continuous_coinduced_rng

end ConnectedSumFacts

/-! ### Layer 2: the map from the octagon -/

/-- The upper half goes to the punctured torus, given that the open hole of `c` is inside the
image of `ell` of the open disk (`t99J02_phi_not_hole`, `t99J02_rel_boundary`, `t99J02_ell_norm`). -/
theorem t99J02_upper_exists (c : BallCollar 2 (Surface true 1))
    (hc : ∀ u : ConstructionTargets.CollaredConnectedSumHomology.Disk 2 1, dist u.1 0 < 1 →
      ∃ v : ℂ, ‖v‖ < 1 ∧ ∃ h : t99J02_ell v ∈ Metric.closedBall (0 : ℂ) 1,
        c.smallMap u = surfaceQuotient true 1 ⟨t99J02_ell v, h⟩) :
    ∃ g : t99J02_Upper → c.Punctured, Continuous g ∧
      ∀ z, (g z).1 = surfaceQuotient true 1 (t99J02_phiDisk z.1) := by
  sorry

/-- That map is onto, given that `ell` of the open disk is inside the hole of `c`
(`t99J02_phi_surj`, `surjective_surfaceQuotient`). -/
theorem t99J02_upper_surj (c : BallCollar 2 (Surface true 1))
    (hc : ∀ v : ℂ, ‖v‖ < 1 → ∀ h : t99J02_ell v ∈ Metric.closedBall (0 : ℂ) 1,
      ∃ u : ConstructionTargets.CollaredConnectedSumHomology.Disk 2 1, dist u.1 0 < 1 ∧
        c.smallMap u = surfaceQuotient true 1 ⟨t99J02_ell v, h⟩)
    (g : t99J02_Upper → c.Punctured)
    (hg : ∀ z, (g z).1 = surfaceQuotient true 1 (t99J02_phiDisk z.1)) :
    Function.Surjective g := by
  sorry

section Glue

variable {c₁ c₂ : BallCollar 2 (Surface true 1)}
  (g₁ : t99J02_Upper → c₁.Punctured) (g₂ : t99J02_Upper → c₂.Punctured)

/-- The octagon to the connected sum: `g₁` on the upper half, `g₂ ∘ neg` on the lower half. -/
def t99J02_G (z : ConstructionTargets.Surfaces.Disk) : ConnectedSum c₁ c₂ :=
  if h : 0 ≤ (z : ℂ).im then t99J02_mk c₁ c₂ (Sum.inl (g₁ ⟨z, h⟩))
  else t99J02_mk c₁ c₂ (Sum.inr (g₂ ⟨t99J02_neg z, by
    have : (z : ℂ).im < 0 := not_le.mp h
    simpa [t99J02_neg] using this.le⟩))

/-- The two halves agree along the chord. -/
def t99J02_Chord : Prop :=
  ∀ (z : ConstructionTargets.Surfaces.Disk) (h : (z : ℂ).im = 0),
    t99J02_mk c₁ c₂ (Sum.inl (g₁ ⟨z, h.ge⟩)) =
      t99J02_mk c₁ c₂ (Sum.inr (g₂ ⟨t99J02_neg z, by simp [t99J02_neg, h]⟩))

/-- The chord condition holds for `g₁`, `g₂` given by `phi` and collars related by conjugation:
`t99J02_phi_chord`, and `(-x + i Y)² = conj (x + i Y)²`; the parameter `s` is `chi⁻¹ ((x + i Y)²)`. -/
theorem t99J02_chord_holds
    (hg₁ : ∀ z, (g₁ z).1 = surfaceQuotient true 1 (t99J02_phiDisk z.1))
    (hg₂ : ∀ z, (g₂ z).1 = surfaceQuotient true 1 (t99J02_phiDisk z.1))
    (hc₁ : ∀ u : ConstructionTargets.CollaredConnectedSumHomology.Disk 2 1,
      ∃ h : t99J02_ell (t99J02_chi u.1) ∈ Metric.closedBall (0 : ℂ) 1,
        c₁.smallMap u = surfaceQuotient true 1 ⟨t99J02_ell (t99J02_chi u.1), h⟩)
    (hc₂ : ∀ u : ConstructionTargets.CollaredConnectedSumHomology.Disk 2 1,
      ∃ h : t99J02_ell ((starRingEnd ℂ) (t99J02_chi u.1)) ∈ Metric.closedBall (0 : ℂ) 1,
        c₂.smallMap u = surfaceQuotient true 1 ⟨t99J02_ell ((starRingEnd ℂ) (t99J02_chi u.1)), h⟩) :
    t99J02_Chord g₁ g₂ := by
  intro z hz
  let x : ℝ := (z : ℂ).re
  have hz_eq : (z : ℂ) = (x : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa [x] using hz
  have hx : |x| ≤ 1 := by
    have hn : ‖(z : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
    rw [hz_eq, Complex.norm_real] at hn
    exact hn
  let Y : ℝ := √(1 - x ^ 2)
  let w : ℂ := (⟨x, Y⟩ : ℂ) ^ 2
  have hx₂ : 0 ≤ 1 - x ^ 2 := by
    have h := abs_le.mp hx
    nlinarith
  have hY₂ : Y ^ 2 = 1 - x ^ 2 := by
    exact Real.sq_sqrt hx₂
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_pow, Complex.sq_norm, Complex.normSq_mk]
    nlinarith [Real.sqrt_nonneg (1 - x ^ 2), hY₂]
  let u : EuclideanSpace ℝ (Fin 2) := !₂[w.re, w.im]
  have hchi : t99J02_chi u = w := by
    apply Complex.ext <;> simp [t99J02_chi, u]
  have hu : ‖u‖ = 1 := by
    rw [← t99J02_chi_spec.2.2.1 u, hchi, hw]
  let s : ConstructionTargets.CollaredConnectedSumHomology.Sphere 2 :=
    ⟨u, by simpa [Metric.mem_sphere, dist_zero_right] using hu⟩
  have hsphere :
      ConstructionTargets.CollaredConnectedSumHomology.sphereToDisk 2 s =
        ⟨u, by simpa [Metric.mem_closedBall, dist_zero_right] using hu.le⟩ := rfl
  obtain ⟨h₁, hc₁'⟩ := hc₁ (ConstructionTargets.CollaredConnectedSumHomology.sphereToDisk 2 s)
  obtain ⟨h₂, hc₂'⟩ := hc₂ (ConstructionTargets.CollaredConnectedSumHomology.sphereToDisk 2 s)
  have hg₁' : g₁ ⟨z, hz.ge⟩ = c₁.boundaryMap s := by
    apply Subtype.ext
    change (g₁ ⟨z, hz.ge⟩).1 = c₁.smallMap
      (ConstructionTargets.CollaredConnectedSumHomology.sphereToDisk 2 s)
    rw [hg₁, hc₁']
    apply congrArg (surfaceQuotient true 1)
    apply Subtype.ext
    change t99J02_phi (z : ℂ) = t99J02_ell
      (t99J02_chi (ConstructionTargets.CollaredConnectedSumHomology.sphereToDisk 2 s).1)
    rw [hz_eq, t99J02_phi_chord x hx, hsphere, hchi]
  have hconj :
      (starRingEnd ℂ) w = (⟨-x, Y⟩ : ℂ) ^ 2 := by
    apply Complex.ext <;> simp [w, pow_two] <;> ring
  have hYneg : √(1 - (-x) ^ 2) = Y := by simp [Y]
  have hneg_eq : (t99J02_neg z : ℂ) = ((-x : ℝ) : ℂ) := by
    change -(z : ℂ) = ((-x : ℝ) : ℂ)
    rw [hz_eq]
    norm_num
  have hg₂' :
      g₂ ⟨t99J02_neg z, by simp [t99J02_neg, hz]⟩ = c₂.boundaryMap s := by
    apply Subtype.ext
    change (g₂ ⟨t99J02_neg z, by simp [t99J02_neg, hz]⟩).1 = c₂.smallMap
      (ConstructionTargets.CollaredConnectedSumHomology.sphereToDisk 2 s)
    rw [hg₂, hc₂']
    apply congrArg (surfaceQuotient true 1)
    apply Subtype.ext
    change t99J02_phi (t99J02_neg z : ℂ) = t99J02_ell
      ((starRingEnd ℂ)
        (t99J02_chi (ConstructionTargets.CollaredConnectedSumHomology.sphereToDisk 2 s).1))
    rw [hneg_eq, t99J02_phi_chord (-x) (by simpa using hx),
      hsphere, hchi, hconj, hYneg]
  rw [hg₁', hg₂']
  exact Quotient.sound (Relation.EqvGen.rel _ _
    (ConstructionTargets.CollaredConnectedSumHomology.GlueRel.boundary s))

/-- Pasting along the chord. -/
theorem t99J02_G_continuous (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hch : t99J02_Chord g₁ g₂) : Continuous (t99J02_G g₁ g₂) := by
  sorry

/-- On the closed lower half `G` is `g₂ ∘ neg`, including on the chord. -/
theorem t99J02_G_lower (hch : t99J02_Chord g₁ g₂) (z : ConstructionTargets.Surfaces.Disk) (h : (z : ℂ).im ≤ 0) :
    t99J02_G g₁ g₂ z = t99J02_mk c₁ c₂ (Sum.inr (g₂ ⟨t99J02_neg z, by simpa [t99J02_neg] using h⟩)) := by
  rw [t99J02_G]
  by_cases hz : 0 ≤ (z : ℂ).im
  · rw [dif_pos hz]
    exact hch z (le_antisymm h hz)
  · rw [dif_neg hz]

/-- `G` respects the octagon's identifications. For handle `0` both points are upper and
`t99J02_phi_edge` turns the generator into a generator of `Surface true 1`, so `g₁` agrees; for
handle `1` use `t99J02_G_lower` and `neg (edgePoint 8 (e + 4) t) = edgePoint 8 e t`. -/
lemma t99J02_G_rel_aux_upper (e : ℕ) (he : e < 4) (t : Set.Icc (0 : ℝ) 1) :
    0 ≤ ((edgePoint 8 e t : ConstructionTargets.Surfaces.Disk) : ℂ).im := by
  simp only [edgePoint, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, Complex.exp_im]
  convert Real.sin_nonneg_of_nonneg_of_le_pi (x :=
      2 * Real.pi * ((e : ℝ) + t.1) / 8) (by
        have he0 : (0 : ℝ) ≤ e := by positivity
        have ht0 := t.2.1
        positivity) (by
        have hpi : 0 < Real.pi := Real.pi_pos
        have he' : e ≤ 3 := by omega
        have heR : (e : ℝ) ≤ 3 := by exact_mod_cast he'
        have ht := t.2.2
        nlinarith) using 1 <;> ring_nf <;> simp

lemma t99J02_G_rel_aux_neg_edge (e : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    t99J02_neg (edgePoint 8 (e + 4) t) = edgePoint 8 e t := by
  apply Subtype.ext
  simp only [t99J02_neg, edgePoint, Subtype.coe_mk]
  calc
    -Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * ((((e + 4 : ℕ) : ℝ) : ℂ) +
        ((t.1 : ℝ) : ℂ)) / 8)) =
        -Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (((e : ℝ) : ℂ) +
          ((t.1 : ℝ) : ℂ)) / 8) + Real.pi * Complex.I) := by
            congr 2
            push_cast
            ring
    _ = -(-Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (((e : ℝ) : ℂ) +
          ((t.1 : ℝ) : ℂ)) / 8))) := by rw [Complex.exp_add_pi_mul_I]
    _ = _ := neg_neg _

lemma t99J02_G_rel_aux_lower (e : ℕ) (he : e < 4) (t : Set.Icc (0 : ℝ) 1) :
    ((edgePoint 8 (e + 4) t : ConstructionTargets.Surfaces.Disk) : ℂ).im ≤ 0 := by
  have h := congrArg (fun z : ConstructionTargets.Surfaces.Disk => (z : ℂ).im)
    (t99J02_G_rel_aux_neg_edge e t)
  simp only [t99J02_neg, Complex.neg_im] at h
  linarith [t99J02_G_rel_aux_upper e he t]

lemma t99J02_G_rel_aux_upper_pair
    (hg : ∀ z, (g₁ z).1 = surfaceQuotient true 1 (t99J02_phiDisk z.1))
    (a b : ℕ) (ha : a < 4) (hb : b < 4) (t u : Set.Icc (0 : ℝ) 1)
    (hr : SurfaceRel true 1 (t99J02_phiDisk (edgePoint 8 a t))
      (t99J02_phiDisk (edgePoint 8 b u))) :
    t99J02_G g₁ g₂ (edgePoint 8 a t) = t99J02_G g₁ g₂ (edgePoint 8 b u) := by
  rw [t99J02_G, dif_pos (t99J02_G_rel_aux_upper a ha t),
    t99J02_G, dif_pos (t99J02_G_rel_aux_upper b hb u)]
  congr 2
  apply Subtype.ext
  rw [hg, hg]
  exact Quotient.sound (Relation.EqvGen.rel _ _ hr)

lemma t99J02_G_rel_aux_lower_pair
    (hch : t99J02_Chord g₁ g₂)
    (hg : ∀ z, (g₂ z).1 = surfaceQuotient true 1 (t99J02_phiDisk z.1))
    (a b : ℕ) (ha : a < 4) (hb : b < 4) (t u : Set.Icc (0 : ℝ) 1)
    (hr : SurfaceRel true 1 (t99J02_phiDisk (edgePoint 8 a t))
      (t99J02_phiDisk (edgePoint 8 b u))) :
    t99J02_G g₁ g₂ (edgePoint 8 (a + 4) t) =
      t99J02_G g₁ g₂ (edgePoint 8 (b + 4) u) := by
  rw [t99J02_G_lower g₁ g₂ hch _ (t99J02_G_rel_aux_lower a ha t),
    t99J02_G_lower g₁ g₂ hch _ (t99J02_G_rel_aux_lower b hb u)]
  have hga : g₂ ⟨t99J02_neg (edgePoint 8 (a + 4) t), by
      simpa [t99J02_neg] using t99J02_G_rel_aux_lower a ha t⟩ =
      g₂ ⟨edgePoint 8 a t, t99J02_G_rel_aux_upper a ha t⟩ := by
    congr 1
    apply Subtype.ext
    exact t99J02_G_rel_aux_neg_edge a t
  have hgb : g₂ ⟨t99J02_neg (edgePoint 8 (b + 4) u), by
      simpa [t99J02_neg] using t99J02_G_rel_aux_lower b hb u⟩ =
      g₂ ⟨edgePoint 8 b u, t99J02_G_rel_aux_upper b hb u⟩ := by
    congr 1
    apply Subtype.ext
    exact t99J02_G_rel_aux_neg_edge b u
  rw [hga, hgb]
  congr 2
  apply Subtype.ext
  rw [hg, hg]
  exact Quotient.sound (Relation.EqvGen.rel _ _ hr)

theorem t99J02_G_rel (hch : t99J02_Chord g₁ g₂)
    (hg₁ : ∀ z, (g₁ z).1 = surfaceQuotient true 1 (t99J02_phiDisk z.1))
    (hg₂ : ∀ z, (g₂ z).1 = surfaceQuotient true 1 (t99J02_phiDisk z.1))
    {x y : ConstructionTargets.Surfaces.Disk} (h : Relation.EqvGen (SurfaceRel true 2) x y) :
    t99J02_G g₁ g₂ x = t99J02_G g₁ g₂ y := by
  induction h with
  | rel x y h =>
      simp only [SurfaceRel, if_true] at h
      rcases h with ⟨j, hj, t, h⟩
      interval_cases j <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · norm_num
        refine t99J02_G_rel_aux_upper_pair g₁ g₂ hg₁ 0 2 (by omega) (by omega)
          t ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ ?_
        simp only [SurfaceRel, if_true]
        refine ⟨0, by omega, t, Or.inl ⟨?_, ?_⟩⟩
        · apply Subtype.ext; exact t99J02_phi_edge 0 (by omega) t
        · apply Subtype.ext
          exact t99J02_phi_edge 2 (by omega)
            ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
      · norm_num
        refine t99J02_G_rel_aux_upper_pair g₁ g₂ hg₁ 1 3 (by omega) (by omega)
          t ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ ?_
        simp only [SurfaceRel, if_true]
        refine ⟨0, by omega, t, Or.inr ⟨?_, ?_⟩⟩
        · apply Subtype.ext; exact t99J02_phi_edge 1 (by omega) t
        · apply Subtype.ext
          exact t99J02_phi_edge 3 (by omega)
            ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
      · norm_num
        refine t99J02_G_rel_aux_lower_pair g₁ g₂ hch hg₂ 0 2 (by omega) (by omega)
          t ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ ?_
        simp only [SurfaceRel, if_true]
        refine ⟨0, by omega, t, Or.inl ⟨?_, ?_⟩⟩
        · apply Subtype.ext; exact t99J02_phi_edge 0 (by omega) t
        · apply Subtype.ext
          exact t99J02_phi_edge 2 (by omega)
            ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
      · norm_num
        refine t99J02_G_rel_aux_lower_pair g₁ g₂ hch hg₂ 1 3 (by omega) (by omega)
          t ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ ?_
        simp only [SurfaceRel, if_true]
        refine ⟨0, by omega, t, Or.inr ⟨?_, ?_⟩⟩
        · apply Subtype.ext; exact t99J02_phi_edge 1 (by omega) t
        · apply Subtype.ext
          exact t99J02_phi_edge 3 (by omega)
            ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/-- `G` separates points of the surface. Use `t99J02_mk_eq`. Two upper points: `t99J02_fibre`. Two
lower points: `t99J02_fibre` after `neg`, with `t99J02_q2_neg`. An upper and a lower point: both
sides lie on the boundary circle at the same `s`; `t99J02_circle_param` gives a chord point `x` with
`phi x` at `s` and `phi (-x)` at the reflected point, and `t99J02_fibre` twice gives
`q₂ z = q₂ x = q₂ z'`. -/
theorem t99J02_G_injective (hch : t99J02_Chord g₁ g₂)
    (hg₁ : ∀ z, (g₁ z).1 = surfaceQuotient true 1 (t99J02_phiDisk z.1))
    (hg₂ : ∀ z, (g₂ z).1 = surfaceQuotient true 1 (t99J02_phiDisk z.1))
    (hc₁ : ∀ u : ConstructionTargets.CollaredConnectedSumHomology.Disk 2 1,
      ∃ h : t99J02_ell (t99J02_chi u.1) ∈ Metric.closedBall (0 : ℂ) 1,
        c₁.smallMap u = surfaceQuotient true 1 ⟨t99J02_ell (t99J02_chi u.1), h⟩)
    (hc₂ : ∀ u : ConstructionTargets.CollaredConnectedSumHomology.Disk 2 1,
      ∃ h : t99J02_ell ((starRingEnd ℂ) (t99J02_chi u.1)) ∈ Metric.closedBall (0 : ℂ) 1,
        c₂.smallMap u = surfaceQuotient true 1 ⟨t99J02_ell ((starRingEnd ℂ) (t99J02_chi u.1)), h⟩)
    {z z' : ConstructionTargets.Surfaces.Disk} (h : t99J02_G g₁ g₂ z = t99J02_G g₁ g₂ z') :
    surfaceQuotient true 2 z = surfaceQuotient true 2 z' := by
  sorry

/-- Topology only. `G` descends to a continuous bijection from `Surface true 2`, compact, and it is
a closed map: the pullbacks of the image of a closed set to the two punctured tori are images of
compact sets under `g₁`, `g₂` (surjectivity and injectivity put every preimage on the right half),
so they are closed in Hausdorff spaces, and `t99J02_isClosed_of` applies. -/
theorem t99J02_homeomorph_of_G [T2Space (Surface true 1)] (hch : t99J02_Chord g₁ g₂)
    (hcont : Continuous (t99J02_G g₁ g₂))
    (hrel : ∀ {x y : ConstructionTargets.Surfaces.Disk}, Relation.EqvGen (SurfaceRel true 2) x y →
      t99J02_G g₁ g₂ x = t99J02_G g₁ g₂ y)
    (hinj : ∀ {z z' : ConstructionTargets.Surfaces.Disk}, t99J02_G g₁ g₂ z = t99J02_G g₁ g₂ z' →
      surfaceQuotient true 2 z = surfaceQuotient true 2 z')
    (hs₁ : Function.Surjective g₁) (hs₂ : Function.Surjective g₂)
    (hcg₁ : Continuous g₁) (hcg₂ : Continuous g₂) :
    Nonempty (ConnectedSum c₁ c₂ ≃ₜ Surface true 2) := by
  sorry

end Glue

/-- The two tori. The collars are `t99J02_collar_exists` and its reflection; the map is `G`. -/
theorem t99J02_two_tori_connectedSum :
    ∃ c₁ c₂ : BallCollar 2 (Surface true 1),
      Nonempty (ConnectedSum c₁ c₂ ≃ₜ Surface true 2) := by
  letI : T2Space (Surface true 1) :=
    letI : T2Space (standardPairingData true 1 Nat.one_pos).Space :=
      (standardPairingData true 1 Nat.one_pos).spaceT2
    (standardPairingData_space_homeomorph true 1 Nat.one_pos).t2Space
  obtain ⟨c₁, hc₁⟩ := t99J02_collar_exists
  obtain ⟨c₂, hc₂'⟩ := t99J02_collar_reflect c₁
  have hc₂ : ∀ u : ConstructionTargets.CollaredConnectedSumHomology.Disk 2 1,
      ∃ h : t99J02_ell ((starRingEnd ℂ) (t99J02_chi u.1)) ∈ Metric.closedBall (0 : ℂ) 1,
        c₂.smallMap u = surfaceQuotient true 1 ⟨t99J02_ell ((starRingEnd ℂ) (t99J02_chi u.1)), h⟩ := by
    intro u
    obtain ⟨hu, e⟩ := hc₂' u
    obtain ⟨h, e'⟩ := hc₁ ⟨t99J02_refl u.1, hu⟩
    have hχ := t99J02_chi_spec.2.2.2.1 u.1
    simp only [hχ] at h e'
    exact ⟨h, e.trans e'⟩
  have hnorm : ∀ u : ConstructionTargets.CollaredConnectedSumHomology.Disk 2 1,
      ‖t99J02_chi u.1‖ = ‖u.1‖ := fun u => t99J02_chi_spec.2.2.1 u.1
  have hup₁ : ∀ u : ConstructionTargets.CollaredConnectedSumHomology.Disk 2 1, dist u.1 0 < 1 →
      ∃ v : ℂ, ‖v‖ < 1 ∧ ∃ h : t99J02_ell v ∈ Metric.closedBall (0 : ℂ) 1,
        c₁.smallMap u = surfaceQuotient true 1 ⟨t99J02_ell v, h⟩ := by
    intro u hu
    obtain ⟨h, e⟩ := hc₁ u
    exact ⟨t99J02_chi u.1, by rw [hnorm]; simpa [dist_zero_right] using hu, h, e⟩
  have hup₂ : ∀ u : ConstructionTargets.CollaredConnectedSumHomology.Disk 2 1, dist u.1 0 < 1 →
      ∃ v : ℂ, ‖v‖ < 1 ∧ ∃ h : t99J02_ell v ∈ Metric.closedBall (0 : ℂ) 1,
        c₂.smallMap u = surfaceQuotient true 1 ⟨t99J02_ell v, h⟩ := by
    intro u hu
    obtain ⟨h, e⟩ := hc₂ u
    refine ⟨(starRingEnd ℂ) (t99J02_chi u.1), ?_, h, e⟩
    rw [RCLike.norm_conj, hnorm]; simpa [dist_zero_right] using hu
  obtain ⟨g₁, hg₁c, hg₁⟩ := t99J02_upper_exists c₁ hup₁
  obtain ⟨g₂, hg₂c, hg₂⟩ := t99J02_upper_exists c₂ hup₂
  have hballsub : ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ < 1 →
      u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := fun u hu => by
    exact mem_closedBall_zero_iff.mpr hu.le
  have hs₁ : Function.Surjective g₁ := by
    refine t99J02_upper_surj c₁ (fun v hv h => ?_) g₁ hg₁
    obtain ⟨u, rfl⟩ := t99J02_chi_spec.2.2.2.2.2.2.2 v
    have hu : ‖u‖ < 1 := by rwa [t99J02_chi_spec.2.2.1] at hv
    obtain ⟨_, e⟩ := hc₁ ⟨u, hballsub u hu⟩
    exact ⟨⟨u, hballsub u hu⟩, by simpa [dist_zero_right] using hu, e⟩
  have hs₂ : Function.Surjective g₂ := by
    refine t99J02_upper_surj c₂ (fun v hv h => ?_) g₂ hg₂
    obtain ⟨u, hu₀⟩ := t99J02_chi_spec.2.2.2.2.2.2.2 ((starRingEnd ℂ) v)
    have hconj : (starRingEnd ℂ) (t99J02_chi u) = v := by rw [hu₀]; simp
    have hu : ‖u‖ < 1 := by
      rw [← t99J02_chi_spec.2.2.1, hu₀, RCLike.norm_conj]; exact hv
    obtain ⟨_, e⟩ := hc₂ ⟨u, hballsub u hu⟩
    refine ⟨⟨u, hballsub u hu⟩, by simpa [dist_zero_right] using hu, ?_⟩
    simpa only [hconj] using e
  have hch := t99J02_chord_holds g₁ g₂ hg₁ hg₂ hc₁ hc₂
  exact ⟨c₁, c₂, t99J02_homeomorph_of_G g₁ g₂ hch (t99J02_G_continuous g₁ g₂ hg₁c hg₂c hch)
    (t99J02_G_rel g₁ g₂ hch hg₁ hg₂) (t99J02_G_injective g₁ g₂ hch hg₁ hg₂ hc₁ hc₂)
    hs₁ hs₂ hg₁c hg₂c⟩

/-- The standard CW, connected-sum, homology, and fundamental-group
descriptions of the closed orientable surface of genus two. -/
theorem apm_t99j02 :
    let X := Surface true 2
    let P := standardPairingData true 2 (by norm_num)
    let H := fun (k : ℕ) =>
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))
    -- One vertex, four 1-cells, and the one polygonal 2-cell.
    (P.edgeCount = 8 ∧
      Nat.card (PairingOrbit P.pair) = 4 ∧
      (∀ i j : Fin P.edgeCount,
        Relation.EqvGen P.Rel (polygonVertex P.edgeCount i)
          (polygonVertex P.edgeCount j)) ∧
      Nonempty (P.Space ≃ₜ X)) ∧
    -- The cellular computation of integral homology.
    (Nonempty (H 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (H 1 ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
      Nonempty (H 2 ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 3 ≤ k → IsZero (H k))) ∧
    -- X is the connected sum of two concrete tori.
    (∃ c₁ c₂ : BallCollar 2 (Surface true 1),
      Nonempty (ConnectedSum c₁ c₂ ≃ₜ X)) ∧
    -- The van Kampen presentation, at every basepoint.
    (∀ x : X, Nonempty
      (FundamentalGroup X x ≃*
        apm_t92J05_genusTwoGroup)) ∧
    -- The Mayer--Vietoris computation of integral homology.
    (Nonempty (H 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (H 1 ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
      Nonempty (H 2 ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 3 ≤ k → IsZero (H k))) := by
  dsimp
  let P := standardPairingData true 2 (by norm_num)
  have hcard : Nat.card (PairingOrbit P.pair) = 4 := by
    change Nat.card (PairingOrbit (orientablePair 2)) = 4
    rw [Nat.card_congr (orientableOrbitEquiv 2)]
    norm_num [Nat.card_eq_fintype_card]
  have hcw :
      (P.edgeCount = 8 ∧
        Nat.card (PairingOrbit P.pair) = 4 ∧
        (∀ i j : Fin P.edgeCount,
          Relation.EqvGen P.Rel (polygonVertex P.edgeCount i)
            (polygonVertex P.edgeCount j)) ∧
        Nonempty (P.Space ≃ₜ Surface true 2)) := by
    exact ⟨rfl, hcard, P.oneVertex,
      ⟨standardPairingData_space_homeomorph true 2 (by norm_num)⟩⟩
  exact ⟨hcw, t99J02_genusTwo_homology,
    t99J02_two_tori_connectedSum,
    apm_t92J05_standard_genusTwo_fundamentalGroup,
    t99J02_genusTwo_homology⟩

#print axioms apm_t99j02
