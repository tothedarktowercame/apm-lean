import Mathlib
import ConstructionTargets.ProjectiveSpaceTopology
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.ProjectiveConsumerLiftDemonstrations
import ConstructionTargets.RP3RationalHomology

/-! # Blueprint for t96A06 (revised 2026-10-17)

Everything except the action on rational `H₃` is already sorry-free here,
on top of the banked `ConstructionTargets.RP3RationalHomology`
(`H_*(ℝP³; ℚ) = ℚ, 0, 0, ℚ` via the double cover `S³ → ℝP³` and transfer).

The remaining content is "the descended map acts by `4` on `H₃(ℝP³; ℚ)`".
Route (no local degrees, no integral-to-rational comparison):

1. Lift: `f̄ ∘ p = p ∘ g` with `g x = F(x)/‖F(x)‖` on `S³` (sorry-free).
2. `g ≃ Q ∘ Q'` where `Q` is "complex squaring, renormalised" on the
   `(x₀,x₁)` plane and `Q' = P ∘ Q ∘ P⁻¹` the same on `(x₂,x₃)` (leaf H).
3. `Q` is a cone map (norm-preserving, commutes with `x ↦ x/2`), and the
   banked sphere-shift naturality for linear isometries holds verbatim for
   cone maps (leaf N1).  `Q` on `S^{n+1}` is the suspension of `Q` on `S^n`
   (leaf S4), so `deg Q` on `S³` equals `deg Q` on `S¹`.
4. `deg Q = 2` on `S¹` by an angle-displacement cochain (leaves C1, C2).
5. Assembly: `g_* = 2 · 2 = 4`; `p_*` is onto (banked transfer), hence
   `f̄_* = 4` on `H₃(ℝP³; ℚ)` (sorry-free).
-/

open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.RationalLefschetz
open ConstructionTargets.ProjectiveConsumerLiftDemonstrations
noncomputable section

namespace T96A06
abbrev RP3 := Space ℝ 3

def polynomialMap (v : Vectors ℝ 3) : Vectors ℝ 3 :=
  ![v 0 ^ 2 - v 1 ^ 2, 2 * v 0 * v 1,
    v 2 ^ 2 - v 3 ^ 2, 2 * v 2 * v 3]
end T96A06

lemma T96A06_polynomialMap_eq_consumerPolynomial (v : Vectors ℝ 3) :
    T96A06.polynomialMap v = t96A06Polynomial v := by
  rfl

/-- The printed quadratic formula has a continuous projective descent. -/
theorem T96A06_polynomialMap_descends :
    ∃ f : ContinuousMap T96A06.RP3 T96A06.RP3,
      ∀ v : NonzeroVectors ℝ 3,
        f (quotientMap ℝ 3 v) = quotientMap ℝ 3
          ⟨T96A06.polynomialMap v.val, by
            rw [T96A06_polynomialMap_eq_consumerPolynomial]
            exact t96A06Polynomial_nonzero v⟩ := by
  simpa only [T96A06_polynomialMap_eq_consumerPolynomial] using
    t96A06Polynomial_descends

namespace T96A06

/-- The polynomial as a map of nonzero vectors. -/
def polyNZ (v : NonzeroVectors ℝ 3) : NonzeroVectors ℝ 3 :=
  ⟨polynomialMap v.val, by
    change t96A06Polynomial v.val ≠ 0
    exact t96A06Polynomial_nonzero v⟩

/-- A map is the projective descent of the displayed quadratic formula. -/
def IsPolynomialDescent (f : ContinuousMap RP3 RP3) : Prop :=
  ∀ v : NonzeroVectors ℝ 3, f (quotientMap ℝ 3 v) = quotientMap ℝ 3 (polyNZ v)

end T96A06

open CategoryTheory

/-! ## Part A: already proved (copied from the 10-15 blueprint, sorry-free) -/

lemma T96A06_rp3_rationalHomology_finite (k : ℕ) :
    FiniteDimensional ℚ (Homology T96A06.RP3 k) := by
  rcases RP3Homology.rp3_rationalHomology with ⟨h0, hvanish, h3⟩
  by_cases hk0 : k = 0
  · subst k
    let e := Classical.choice h0
    exact e.symm.toLinearEquiv.finiteDimensional
  by_cases hk3 : k = 3
  · subst k
    let e := Classical.choice h3
    exact e.symm.toLinearEquiv.finiteDimensional
  · have hz := hvanish k hk0 hk3
    letI : Subsingleton (Homology T96A06.RP3 k) := ⟨by
      intro x y
      have hid : (𝟙 (RP3Homology.HQ k RP3Homology.RP3)) = 0 :=
        hz.eq_of_src _ _
      have hx := congrArg (fun f => f.hom x) hid
      have hy := congrArg (fun f => f.hom y) hid
      simpa using hx.trans hy.symm⟩
    exact FiniteDimensional.of_injective
      (0 : Homology T96A06.RP3 k →ₗ[ℚ] ℚ)
      (Function.injective_of_subsingleton _)

lemma T96A06_rp3_rationalHomology_vanishes_above_three (k : ℕ)
    (hk : 3 < k) :
    Subsingleton (Homology T96A06.RP3 k) := by
  rcases RP3Homology.rp3_rationalHomology with ⟨_, hvanish, _⟩
  apply ModuleCat.subsingleton_of_isZero
  exact hvanish k (by omega) (by omega)

lemma T96A06_polynomialDescent_trace_zero
    (f : ContinuousMap T96A06.RP3 T96A06.RP3) :
    LinearMap.trace ℚ (Homology T96A06.RP3 0) (induced f 0).hom = 1 := by
  letI : PathConnectedSpace T96A06.RP3 :=
    ConstructionTargets.t96A06Closure.rp3PathConnectedSpace
  let x : T96A06.RP3 := coordinateLine ℝ 3 0
  have hmap : induced f 0 = 𝟙 _ := by
    have h := ConstructionTargets.CoefficientConnectedH0Map.mapIso_hom ℚ f x x
    have h' :
        (ConstructionTargets.CoefficientConnectedH0Map.mapIso ℚ x x).hom =
          induced f 0 := by
      simpa [induced, ConstructionTargets.CoefficientH0.singularPostcomposition,
        AlgebraicTopology.singularHomologyFunctor] using h
    rw [← h']
    simp [ConstructionTargets.CoefficientConnectedH0Map.mapIso]
  letI : FiniteDimensional ℚ (Homology T96A06.RP3 0) :=
    ConstructionTargets.t96A06Closure.rp3RationalH0Iso.symm.toLinearEquiv.finiteDimensional
  rw [hmap]
  change LinearMap.trace ℚ (Homology T96A06.RP3 0) LinearMap.id = 1
  rw [LinearMap.trace_id]
  have hrank := LinearEquiv.finrank_eq
    (ConstructionTargets.t96A06Closure.rp3RationalH0Iso.toLinearEquiv)
  simpa using hrank

lemma T96A06_trace_of_isZero (f : ContinuousMap T96A06.RP3 T96A06.RP3) (k : ℕ)
    (hk0 : k ≠ 0) (hk3 : k ≠ 3) :
    LinearMap.trace ℚ (Homology T96A06.RP3 k) (induced f k).hom = 0 := by
  rcases RP3Homology.rp3_rationalHomology with ⟨_, hvanish, _⟩
  have hz := hvanish k hk0 hk3
  letI : Subsingleton (Homology T96A06.RP3 k) := ⟨by
    intro x y
    have hid : (𝟙 (RP3Homology.HQ k RP3Homology.RP3)) = 0 :=
      hz.eq_of_src _ _
    have hx := congrArg (fun g => g.hom x) hid
    have hy := congrArg (fun g => g.hom y) hid
    simpa using hx.trans hy.symm⟩
  have hinduced : (induced f k).hom = 0 := Subsingleton.elim _ _
  rw [hinduced]
  exact LinearMap.map_zero (LinearMap.trace ℚ (Homology T96A06.RP3 k))

lemma T96A06_rp3_finrank_three : Module.finrank ℚ (Homology T96A06.RP3 3) = 1 := by
  rcases RP3Homology.rp3_rationalHomology with ⟨_, _, h3⟩
  let e := Classical.choice h3
  rw [LinearEquiv.finrank_eq e.toLinearEquiv]
  simp

lemma T96A06_identity_trace_three :
    LinearMap.trace ℚ (Homology T96A06.RP3 3)
      (induced (ContinuousMap.id T96A06.RP3) 3).hom = 1 := by
  letI := T96A06_rp3_rationalHomology_finite 3
  have hinduced : (induced (ContinuousMap.id T96A06.RP3) 3).hom = LinearMap.id := by
    simp [induced]
  rw [hinduced, LinearMap.trace_id, T96A06_rp3_finrank_three]
  norm_num

open CategoryTheory.MonoidalCategory

noncomputable def T96A06_homotopic_induced_eq_aux_cylinder
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    TopCat.of X ⊗ TopCat.I ⟶ TopCat.of Y :=
  TopCat.ofHom ⟨fun p ↦ H (TopCat.I.homeomorph p.2, p.1),
    H.continuous.comp
      ((TopCat.I.homeomorph.continuous.comp continuous_snd).prodMk continuous_fst)⟩

lemma T96A06_homotopic_induced_eq_aux_zero
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    TopCat.ι₀ ≫ T96A06_homotopic_induced_eq_aux_cylinder H = TopCat.ofHom f := by
  ext x
  change H (0, x) = f x
  simp

lemma T96A06_homotopic_induced_eq_aux_one
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    TopCat.ι₁ ≫ T96A06_homotopic_induced_eq_aux_cylinder H = TopCat.ofHom g := by
  ext x
  change H (1, x) = g x
  simp

noncomputable def T96A06_homotopic_induced_eq_aux_sset
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    SSet.Homotopy (TopCat.toSSet.map (TopCat.ofHom f))
      (TopCat.toSSet.map (TopCat.ofHom g)) where
  h := (TopCat.toSSet.obj (TopCat.of X) ◁ SSet.stdSimplex.toSSetObjI) ≫
    CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of X) TopCat.I ≫
    TopCat.toSSet.map (T96A06_homotopic_induced_eq_aux_cylinder H)
  h₀ := by
    change _ = TopCat.toSSet.map (TopCat.ofHom f)
    simp only [SSet.stdSimplex.ι₀_whiskerLeft_toSSetObjI_μ_assoc,
      ← TopCat.toSSet.map_comp, T96A06_homotopic_induced_eq_aux_zero H]
  h₁ := by
    change _ = TopCat.toSSet.map (TopCat.ofHom g)
    simp only [SSet.stdSimplex.ι₁_whiskerLeft_toSSetObjI_μ_assoc,
      ← TopCat.toSSet.map_comp, T96A06_homotopic_induced_eq_aux_one H]
  rel := by
    ext n x
    exact x.1.property.elim

/-- Homotopic maps induce equal maps on rational singular homology (any spaces). -/
lemma T96A06_homotopic_induced_eq_general
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) (h : ContinuousMap.Homotopic f g) (k : ℕ) :
    induced f k = induced g k := by
  rcases h with ⟨H⟩
  simpa [induced, AlgebraicTopology.singularHomologyFunctor,
    AlgebraicTopology.singularChainComplexFunctor] using
    singularChainComplexFunctor_map_homology_eq_of_simplicialHomotopy
      (C := ModuleCat ℚ) (R := ModuleCat.of ℚ ℚ)
      (f := TopCat.toSSet.map (TopCat.ofHom f))
      (g := TopCat.toSSet.map (TopCat.ofHom g))
      (H := (T96A06_homotopic_induced_eq_aux_sset H).toSimplicialObjectHomotopy) k

/-! ## Part B: cone maps and the generalised sphere-shift naturality -/

namespace T96A06Deg
open CategoryTheory.Limits
open ConstructionTargets
open T02A06 T02A06HemisphereExcision T02A06DiskRadialComparison

/-- A continuous self-map of Euclidean space which preserves norms and commutes
with halving.  Linear isometries are examples; so is "complex squaring
renormalised", `u ↦ u²/‖u‖`, on one coordinate plane. -/
structure ConeMap (n : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  continuous_toFun : Continuous toFun
  norm_map : ∀ x, ‖toFun x‖ = ‖x‖
  map_half : ∀ x, toFun ((1 / 2 : ℝ) • x) = (1 / 2 : ℝ) • toFun x

variable {n : ℕ} (ψ : ConeMap n)

/-- The action on the closed unit disk. -/
def closedAction : C(euclideanClosedDisk n, euclideanClosedDisk n) where
  toFun x := ⟨ψ.toFun x.1, by
    have h := x.2
    simpa only [Metric.mem_closedBall, dist_zero_right, ψ.norm_map] using h⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ψ.continuous_toFun.comp continuous_subtype_val

/-- The action on the open unit disk. -/
def openAction : C(euclideanOpenDisk n, euclideanOpenDisk n) where
  toFun x := ⟨ψ.toFun x.1, by
    have h := x.2
    simpa only [Metric.mem_ball, dist_zero_right, ψ.norm_map] using h⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ψ.continuous_toFun.comp continuous_subtype_val

/-- The action on the unit sphere of `ℝⁿ`. -/
def boundaryAction : C(euclideanUnitSphere n, euclideanUnitSphere n) where
  toFun x := ⟨ψ.toFun x.1, by
    have h := x.2
    simpa only [Metric.mem_sphere, dist_zero_right, ψ.norm_map] using h⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ψ.continuous_toFun.comp continuous_subtype_val

/-- The suspension: act on the first `n` coordinates of the sphere in `ℝⁿ⁺¹`,
keep the height. -/
def sphereAction : C(ambientSphere n, ambientSphere n) where
  toFun x := ⟨euclideanSnoc (ψ.toFun (euclideanInit x.1)) (sphereHeight n x), by
    rw [Metric.mem_sphere, dist_zero_right]
    have hx : ‖x.1‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.2
    have he := euclideanInit_norm_sq_add_last x.1
    have hs : ‖euclideanSnoc (ψ.toFun (euclideanInit x.1)) (sphereHeight n x)‖ ^ 2 = 1 ^ 2 := by
      rw [euclideanSnoc_norm_sq, ψ.norm_map]
      simpa only [sphereHeight, hx] using he
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hs⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_euclideanSnoc.comp ((ψ.continuous_toFun.comp
      (continuous_euclideanInit.comp continuous_subtype_val)).prodMk (continuous_sphereHeight n))

theorem closed_mapsTo :
    Set.MapsTo (closedAction ψ) (closedDiskBoundarySet n) (closedDiskBoundarySet n) := by
  intro x hx
  change x.1 ∈ euclideanUnitSphere n at hx
  change ψ.toFun x.1 ∈ euclideanUnitSphere n
  simpa only [Metric.mem_sphere, dist_zero_right, ψ.norm_map] using hx

variable (R : Type) [CommRing R]

/-- The induced map of closed-disk pairs `(D, ∂D)`. -/
def closedPair := CoefficientRadialPair.pairMap R _ _ (closedAction ψ) (closed_mapsTo ψ)

/-- **Leaf N1.** Sphere-to-disk naturality for cone maps.  This is
`CoefficientOrthogonalSphere.sphereToDisk_naturality` with the linear isometry
`Q` replaced by a cone map; the banked proof (and the radial part in
`CoefficientOrthogonalRadial`) uses only `norm_map`, `map_half`, continuity and
the induced subspace maps, so it transfers line by line. -/
theorem T96A06_coneMap_sphereToDisk_naturality (j : ℕ) (hj : j ≠ 0) :
    HomologicalComplex.homologyMap (CoefficientRadialPair.absoluteMap R (sphereAction ψ)) j ≫
      (CoefficientSphereShift.sphereToDiskIso R n j hj).hom =
    (CoefficientSphereShift.sphereToDiskIso R n j hj).hom ≫
      HomologicalComplex.homologyMap (closedPair ψ R) j := by
  sorry

private theorem commute_comp' {C : Type*} [Category C] {A B D : C}
    {a : A ⟶ A} {b : B ⟶ B} {c : D ⟶ D} {f : A ⟶ B} {g : B ⟶ D}
    (h : a ≫ f = f ≫ b) (h' : b ≫ g = g ≫ c) : a ≫ (f ≫ g) = (f ≫ g) ≫ c := by
  calc
    _ = (a ≫ f) ≫ g := (Category.assoc _ _ _).symm
    _ = (f ≫ b) ≫ g := congrArg (fun t => t ≫ g) h
    _ = f ≫ (b ≫ g) := Category.assoc _ _ _
    _ = f ≫ (g ≫ c) := congrArg (fun t => f ≫ t) h'
    _ = _ := (Category.assoc _ _ _).symm

theorem coneMap_boundary_homeomorphism_naturality (k : ℕ) :
    HomologicalComplex.homologyMap (CoefficientRadialPair.subMap R (closedDiskBoundarySet n)
      (closedDiskBoundarySet n) (closedAction ψ) (closed_mapsTo ψ)) k ≫
      (CoefficientRadialPair.F R k).map (TopCat.isoOfHomeo (closedDiskBoundaryHomeomorph n)).hom =
    (CoefficientRadialPair.F R k).map (TopCat.isoOfHomeo (closedDiskBoundaryHomeomorph n)).hom ≫
      (CoefficientRadialPair.F R k).map (TopCat.ofHom (boundaryAction ψ)) := by
  change (CoefficientRadialPair.F R k).map _ ≫ (CoefficientRadialPair.F R k).map _ =
    (CoefficientRadialPair.F R k).map _ ≫ (CoefficientRadialPair.F R k).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Sphere-shift naturality for cone maps (sorry-free given leaf N1). -/
theorem coneMap_sphereShift_naturality (k : ℕ) (hk : k ≠ 0) :
    HomologicalComplex.homologyMap (CoefficientRadialPair.absoluteMap R (sphereAction ψ)) (k+1) ≫
      (CoefficientSphereShift.sphereShift R n k hk).hom =
    (CoefficientSphereShift.sphereShift R n k hk).hom ≫
      (CoefficientRadialPair.F R k).map (TopCat.ofHom (boundaryAction ψ)) := by
  rw [CoefficientSphereShift.sphereShift_hom]
  exact commute_comp' (T96A06_coneMap_sphereToDisk_naturality ψ R (k+1) (by omega))
    (commute_comp' (CoefficientPairNaturality.connecting_naturality R
      (closedDiskBoundarySet n) (closedDiskBoundarySet n) (closedAction ψ) (closed_mapsTo ψ) k).symm
      (coneMap_boundary_homeomorphism_naturality ψ R k))

/-! ## Part C: renormalised complex squaring on the first coordinate plane -/

/-- `u ↦ u²/‖u‖` on the plane of coordinates `0, 1` (with `0 ↦ 0`, by Lean's
division by zero); the other coordinates are fixed. -/
def sqFun (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 2))) : EuclideanSpace ℝ (Fin (n + 2)) :=
  WithLp.toLp 2 (fun i =>
    if i = 0 then (x 0 ^ 2 - x 1 ^ 2) / Real.sqrt (x 0 ^ 2 + x 1 ^ 2)
    else if i = 1 then 2 * x 0 * x 1 / Real.sqrt (x 0 ^ 2 + x 1 ^ 2)
    else x i)

/-- **Leaf S1.** `sqFun` is continuous.  Away from the plane's origin this is
algebra; at `x 0 = x 1 = 0` both new coordinates are bounded by
`√(x 0² + x 1²)`, which tends to `0`. -/
theorem T96A06_sqFun_continuous (n : ℕ) : Continuous (sqFun n) := by
  sorry

/-- **Leaf S2.** `sqFun` preserves the norm and commutes with halving.
`(a²-b²)² + (2ab)² = (a²+b²)²`; if `a = b = 0` both sides vanish. -/
-- BEGIN SEAT AREA
theorem T96A06_sqFun_norm_half (n : ℕ) :
    (∀ x, ‖sqFun n x‖ = ‖x‖) ∧
      ∀ x, sqFun n ((1 / 2 : ℝ) • x) = (1 / 2 : ℝ) • sqFun n x := by
  constructor
  · intro x
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ]
    simp only [sqFun]
    simp only [Fin.succ_zero_eq_one, if_pos, one_ne_zero, if_false]
    have hss0 (i : Fin n) : i.succ.succ ≠ (0 : Fin (n + 2)) := by
      intro h; have := congrArg Fin.val h; simp at this
    have hss1 (i : Fin n) : i.succ.succ ≠ (1 : Fin (n + 2)) := by
      intro h; have := congrArg Fin.val h; simp at this
    simp_rw [if_neg (hss0 _), if_neg (hss1 _)]
    simp only [Real.norm_eq_abs, sq_abs]
    have hs : 0 ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
    by_cases h : x 0 ^ 2 + x 1 ^ 2 = 0
    · have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
      have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
      simp [h0, h1]
    · rw [div_pow, div_pow, Real.sq_sqrt hs]
      field_simp
      ring
  · intro x
    ext i
    simp only [sqFun]
    simp only [PiLp.smul_apply, smul_eq_mul]
    by_cases hi0 : i = 0
    · subst i
      simp only [if_pos]
      have hs : 0 ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
      rw [show ((1 / 2 : ℝ) * x 0) ^ 2 + ((1 / 2 : ℝ) * x 1) ^ 2 =
          (1 / 4 : ℝ) * (x 0 ^ 2 + x 1 ^ 2) by ring]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      norm_num
      ring
    · by_cases hi1 : i = 1
      · subst i
        simp only [hi0, if_false, if_pos]
        have hs : 0 ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
        rw [show ((1 / 2 : ℝ) * x 0) ^ 2 + ((1 / 2 : ℝ) * x 1) ^ 2 =
            (1 / 4 : ℝ) * (x 0 ^ 2 + x 1 ^ 2) by ring]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
        norm_num
        ring
      · simp [hi0, hi1]
-- END SEAT AREA

/-- Renormalised squaring as a cone map. -/
def sqCone (n : ℕ) : ConeMap (n + 2) where
  toFun := sqFun n
  continuous_toFun := T96A06_sqFun_continuous n
  norm_map := (T96A06_sqFun_norm_half n).1
  map_half := (T96A06_sqFun_norm_half n).2

/-- **Leaf S4.** Squaring on `S^{n+2}` is the suspension of squaring on
`S^{n+1}`: appending the height coordinate does not touch coordinates `0, 1`. -/
theorem T96A06_sqCone_suspension (n : ℕ) :
    sphereAction (sqCone n) = boundaryAction (sqCone (n + 1)) := by
  sorry

/-! ## Part D: degree two on the circle -/

/-- The rational singular chains of the circle `S¹ ⊂ ℝ²`. -/
abbrev circleChains := CoefficientH0.SingularChains ℚ (TopCat.of (euclideanUnitSphere 2))

/-- The angle map `t ↦ (cos 2πt, sin 2πt)` onto the circle `S¹ ⊂ ℝ²`. -/
def angleMap (t : ℝ) : euclideanUnitSphere 2 :=
  ⟨WithLp.toLp 2 ![Real.cos (2 * Real.pi * t), Real.sin (2 * Real.pi * t)], by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, Real.cos_sq_add_sin_sq]⟩

/-- **Leaf C1a.** The angle map is a covering map.  Transport Mathlib's
`AddCircle.isCoveringMap_coe` (or the banked
`CircleUniversalCover.circleCover_isCoveringMap` for `Circle.exp`) along the
homeomorphism `Circle ≃ₜ S¹ ⊂ ℝ²`, `z ↦ (re z, im z)`. -/
theorem T96A06_angleMap_isCoveringMap : IsCoveringMap angleMap := by
  sorry

/-- **Leaf C1b.** The angle-displacement cochain.  For a singular 1-simplex
`σ` choose a lift `L` of `σ` through `angleMap` (Mathlib's
`IsCoveringMap.existsUnique_continuousMap_lifts`; simplices are convex, hence
simply and locally path connected) and put `W σ = L(v₁) - L(v₀)`, which does
not depend on the lift.  Extend `ℚ`-linearly over the coproduct of
generators, exactly as `CoefficientCoveringTransfer.transferDegree` is built
(`Sigma.desc`, `generator_transfer`).  `W ∘ d₂ = 0`: lift a whole 2-simplex;
by `CoefficientH0.singularGenerator_boundary` and
`singularSimplexOfContinuousMap_face` the three face terms telescope.  If `L`
lifts `σ` then `2L` lifts `squaring ∘ σ` (on `S¹` the cone map is
`(a,b) ↦ (a²-b², 2ab)`), so `W` scales by `2`.  The loop
`t ↦ angleMap t` read on the 1-simplex is a cycle (equal endpoints) with
`W = 1`. -/
theorem T96A06_circle_windingCochain (hcov : IsCoveringMap angleMap) :
    ∃ W : (circleChains.X 1) →ₗ[ℚ] ℝ,
      W ∘ₗ (circleChains.d 2 1).hom = 0 ∧
      W ∘ₗ ((CoefficientH0.singularPostcomposition ℚ
        (boundaryAction (sqCone 0))).f 1).hom = (2 : ℚ) • W ∧
      ∃ c : circleChains.X 1, (circleChains.d 1 0).hom c = 0 ∧ W c ≠ 0 := by
  sorry

/-- **Leaf C2.** From such a cochain, squaring acts by `2` on `H₁(S¹; ℚ)`.
`W` descends through `homologyι`/opcycles to `w : H₁ → ℝ`; the class `[c]`
has `w [c] ≠ 0`, so it spans the one-dimensional `H₁` (banked
`CoefficientFirstReflection.topIso ℚ 0`); `w (s_* [c]) = 2 w [c]` forces the
scalar of `s_*` to be `2`. -/
theorem T96A06_circle_degree_of_cochain
    (W : (circleChains.X 1) →ₗ[ℚ] ℝ)
    (hd : W ∘ₗ (circleChains.d 2 1).hom = 0)
    (hnat : W ∘ₗ ((CoefficientH0.singularPostcomposition ℚ
        (boundaryAction (sqCone 0))).f 1).hom = (2 : ℚ) • W)
    (c : circleChains.X 1) (hc : (circleChains.d 1 0).hom c = 0) (hW : W c ≠ 0) :
    (CoefficientRadialPair.F ℚ 1).map (TopCat.ofHom (boundaryAction (sqCone 0))) =
      (2 : ℚ) • 𝟙 _ := by
  sorry

/-- Squaring has degree two on every sphere `S^{n+1} ⊂ ℝ^{n+2}` (sorry-free
given the leaves): circle base case, then suspension. -/
theorem sqSphere_degree (n : ℕ) :
    (CoefficientRadialPair.F ℚ (n + 1)).map (TopCat.ofHom (boundaryAction (sqCone n))) =
      (2 : ℚ) • 𝟙 _ := by
  induction n with
  | zero =>
    obtain ⟨W, hd, hnat, c, hc, hW⟩ :=
      T96A06_circle_windingCochain T96A06_angleMap_isCoveringMap
    exact T96A06_circle_degree_of_cochain W hd hnat c hc hW
  | succ m ih =>
    have hs := coneMap_sphereShift_naturality (sqCone m) ℚ (m + 1) (by omega)
    rw [ih, T96A06_sqCone_suspension] at hs
    apply (cancel_mono (CoefficientSphereShift.sphereShift ℚ (m + 2) (m + 1) (by omega)).hom).mp
    refine hs.trans ?_
    ext x
    simp

end T96A06Deg

/-! ## Part E: the sphere lift and degree four -/

namespace T96A06Deg
open ConstructionTargets
open RP3Homology ConstructionTargets.CoefficientCoordinateReflections

/-- A point of `S³` as a nonzero vector. -/
def sphereVec (x : S3) : NonzeroVectors ℝ 3 :=
  ⟨WithLp.equiv 2 (Fin 4 → ℝ) x.1, by
    intro h
    have hx : x.1 = 0 := (WithLp.equiv 2 (Fin 4 → ℝ)).injective (by simpa using h)
    have := x.2
    simp [hx] at this⟩

theorem projFun_eq (x : S3) : projFun x = quotientMap ℝ 3 (sphereVec x) := rfl

theorem continuous_polyNZ_sphereVec :
    Continuous (fun x : S3 => T96A06.polyNZ (sphereVec x)) := by
  apply Continuous.subtype_mk
  have hv : Continuous (fun x : S3 => (WithLp.equiv 2 (Fin 4 → ℝ)) x.1) :=
    (PiLp.continuous_ofLp 2 _).comp continuous_subtype_val
  have hc : ∀ i : Fin 4, Continuous (fun x : S3 => (WithLp.equiv 2 (Fin 4 → ℝ)) x.1 i) :=
    fun i => (continuous_apply i).comp hv
  change Continuous (fun x : S3 => T96A06.polynomialMap ((WithLp.equiv 2 (Fin 4 → ℝ)) x.1))
  unfold T96A06.polynomialMap
  apply continuous_pi
  intro i
  fin_cases i
  · exact ((hc 0).pow 2).sub ((hc 1).pow 2)
  · exact (continuous_const.mul (hc 0)).mul (hc 1)
  · exact ((hc 2).pow 2).sub ((hc 3).pow 2)
  · exact (continuous_const.mul (hc 2)).mul (hc 3)

/-- The lift `g x = F(x)/‖F(x)‖` of the polynomial to `S³`. -/
def liftMap : C(S3, S3) where
  toFun x := proj_cover_aux_radial (T96A06.polyNZ (sphereVec x))
  continuous_toFun := proj_cover_aux_continuous_radial.comp continuous_polyNZ_sphereVec

/-- The covering projection as a continuous map. -/
def projC : C(S3, T96A06.RP3) := ⟨projFun, proj_cover.isCoveringMap.continuous⟩

/-- `f̄ ∘ p = p ∘ g` (sorry-free). -/
theorem lift_square (f : C(T96A06.RP3, T96A06.RP3)) (hf : T96A06.IsPolynomialDescent f) :
    f.comp projC = projC.comp liftMap := by
  ext x
  change f (projFun x) = projFun (proj_cover_aux_radial (T96A06.polyNZ (sphereVec x)))
  rw [projFun_eq, hf]
  exact (congrFun proj_cover_aux_comp_radial _).symm

/-- Swap the two complex coordinate planes `(x₀,x₁) ↔ (x₂,x₃)`. -/
def swapE : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

/-- Renormalised squaring on the plane `(x₀,x₁)` of `S³`. -/
def Q4 : C(S3, S3) := boundaryAction (sqCone 2)

/-- Renormalised squaring on the plane `(x₂,x₃)` of `S³`. -/
def Q4' : C(S3, S3) := (permutationMap swapE).comp (Q4.comp (permutationMap swapE.symm))

/-- **Leaf H.** In complex coordinates `x = (u, w)`, `g x = (u², w²)/‖(u², w²)‖`
and `Q4 (Q4' x) = (u²/|u|, w²/|w|)`.  Both are positive multiples of
`(a·u², b·w²)` with `a, b > 0`, so `g x ≠ -(Q4 (Q4' x))` (else `u² = w² = 0`).
The normalised straight-line homotopy therefore never passes through `0`. -/
theorem T96A06_liftMap_homotopic : ContinuousMap.Homotopic liftMap (Q4.comp Q4') := by
  sorry

/-! ### Sorry-free assembly of the degree -/

theorem Q4_degree : induced Q4 3 = (2 : ℚ) • 𝟙 _ := sqSphere_degree 2

theorem perm_cancel :
    induced (permutationMap swapE.symm) 3 ≫ induced (permutationMap swapE) 3 = 𝟙 _ := by
  unfold induced
  have h : TopCat.ofHom (permutationMap swapE.symm) ≫ TopCat.ofHom (permutationMap swapE) =
      𝟙 (TopCat.of S3) := by
    change TopCat.ofHom ((permutationMap swapE).comp (permutationMap swapE.symm)) =
      TopCat.ofHom (ContinuousMap.id S3)
    rw [permutation_inverse]
  rw [← Functor.map_comp, h, CategoryTheory.Functor.map_id]

theorem induced_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (a : C(Y, Z)) (b : C(X, Y)) (k : ℕ) :
    induced (a.comp b) k = induced b k ≫ induced a k := by
  unfold induced
  rw [← Functor.map_comp]
  rfl

theorem Q4'_degree : induced Q4' 3 = (2 : ℚ) • 𝟙 _ := by
  unfold Q4'
  rw [induced_comp, induced_comp, Q4_degree]
  ext x
  have h := congrArg (fun φ => φ.hom x) perm_cancel
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_coe,
    id_eq] at h
  simp [h]

theorem liftMap_degree : induced liftMap 3 = (4 : ℚ) • 𝟙 _ := by
  rw [T96A06_homotopic_induced_eq_general _ _ T96A06_liftMap_homotopic, induced_comp,
    Q4_degree, Q4'_degree]
  ext x
  simp [smul_smul]
  norm_num

/-- The descended map acts by `4` on `H₃(ℝP³; ℚ)` (sorry-free given the leaves). -/
theorem descent_degree (f : C(T96A06.RP3, T96A06.RP3)) (hf : T96A06.IsPolynomialDescent f) :
    induced f 3 = (4 : ℚ) • 𝟙 _ := by
  have hsq : induced projC 3 ≫ induced f 3 = induced liftMap 3 ≫ induced projC 3 := by
    rw [← induced_comp, ← induced_comp, lift_square f hf]
  rw [liftMap_degree] at hsq
  have hTP := CoefficientCoveringTransfer.rational_homology_projection (p := projFun) proj_cover 3
  let T := HomologicalComplex.homologyMap
    (CoefficientCoveringTransfer.transfer ℚ projFun proj_cover) 3
  have h1 : ∀ y, (induced projC 3).hom (T.hom y) = (2 : ℚ) • y := by
    intro y
    have := congrArg (fun φ => φ.hom y) hTP
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    change (induced projC 3).hom (T.hom y) = _ at this
    rw [this, two_smul, two_smul]
    rfl
  have h2 : ∀ z, (induced f 3).hom ((induced projC 3).hom z) =
      (4 : ℚ) • (induced projC 3).hom z := by
    intro z
    have := congrArg (fun φ => φ.hom z) hsq
    simpa using this
  ext y
  have hy : y = (2⁻¹ : ℚ) • (induced projC 3).hom (T.hom y) := by
    rw [h1]
    exact (inv_smul_smul₀ (two_ne_zero) y).symm
  rw [hy, map_smul, h2, h1]
  simp [smul_smul]

end T96A06Deg

/-! ## Part F: traces and the main theorem (sorry-free given the leaves) -/

lemma T96A06_polynomialDescent_trace_three
    (f : ContinuousMap T96A06.RP3 T96A06.RP3)
    (hf : T96A06.IsPolynomialDescent f) :
    LinearMap.trace ℚ (Homology T96A06.RP3 3) (induced f 3).hom = 4 := by
  letI := T96A06_rp3_rationalHomology_finite 3
  rw [T96A06Deg.descent_degree f hf]
  have h : ((4 : ℚ) • 𝟙 (Homology T96A06.RP3 3)).hom = (4 : ℚ) • LinearMap.id := rfl
  rw [h, map_smul, LinearMap.trace_id, T96A06_rp3_finrank_three]
  norm_num

theorem T96A06_polynomialDescent_invariants
    (f : ContinuousMap T96A06.RP3 T96A06.RP3)
    (hf : T96A06.IsPolynomialDescent f) :
    HasLefschetzNumber f (-3) ∧
      ¬ ContinuousMap.Homotopic f (ContinuousMap.id T96A06.RP3) := by
  constructor
  · refine ⟨T96A06_rp3_rationalHomology_finite, 3, ?_, ?_⟩
    · exact T96A06_rp3_rationalHomology_vanishes_above_three
    · rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ]
      rw [T96A06_polynomialDescent_trace_zero f,
        T96A06_trace_of_isZero f 1 (by norm_num) (by norm_num),
        T96A06_trace_of_isZero f 2 (by norm_num) (by norm_num),
        T96A06_polynomialDescent_trace_three f hf]
      norm_num
  · intro h
    have heq := T96A06_homotopic_induced_eq_general f
      (ContinuousMap.id T96A06.RP3) h 3
    have htrace := congrArg
      (fun u => LinearMap.trace ℚ (Homology T96A06.RP3 3) u.hom) heq
    dsimp only at htrace
    rw [T96A06_polynomialDescent_trace_three f hf,
      T96A06_identity_trace_three] at htrace
    norm_num at htrace

theorem apm_t96a06 :
    ∃ f : ContinuousMap T96A06.RP3 T96A06.RP3,
      (∀ v : NonzeroVectors ℝ 3, ∃ hv : T96A06.polynomialMap v.val ≠ 0,
        f (quotientMap ℝ 3 v) = quotientMap ℝ 3 ⟨T96A06.polynomialMap v.val, hv⟩) ∧
      HasLefschetzNumber f (-3) ∧
      ¬ ContinuousMap.Homotopic f (ContinuousMap.id T96A06.RP3) := by
  obtain ⟨f, hf⟩ := T96A06_polynomialMap_descends
  have hf' : T96A06.IsPolynomialDescent f := fun v => hf v
  exact ⟨f, fun v => ⟨(T96A06.polyNZ v).2, hf v⟩, T96A06_polynomialDescent_invariants f hf'⟩

#print axioms apm_t96a06
