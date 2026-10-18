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
theorem T96A06_coneMap_sphereToDisk_naturality_aux_open_mapsTo :
    Set.MapsTo (openAction ψ) (puncturedOpenDiskSet n) (puncturedOpenDiskSet n) := by
  intro x hx
  change ψ.toFun x.1 ≠ 0
  intro h
  have hn : ‖x.1‖ = 0 := by rw [← ψ.norm_map x.1, h, norm_zero]
  exact hx (norm_eq_zero.mp hn)

theorem T96A06_coneMap_sphereToDisk_naturality_aux_radial_square :
    (halfDiskMap n).comp (closedAction ψ) = (openAction ψ).comp (halfDiskMap n) := by
  ext x : 1
  apply Subtype.ext
  exact (ψ.map_half x.1).symm

def T96A06_coneMap_sphereToDisk_naturality_aux_openPair :=
  CoefficientRadialPair.pairMap R _ _ (openAction ψ)
    (T96A06_coneMap_sphereToDisk_naturality_aux_open_mapsTo ψ)

def T96A06_coneMap_sphereToDisk_naturality_aux_radialPair :=
  CoefficientRadialPair.pairMap R _ _ (halfDiskMap n) (halfDiskMap_mapsTo n)

theorem T96A06_coneMap_sphereToDisk_naturality_aux_relative_square :
    closedPair ψ R ≫ T96A06_coneMap_sphereToDisk_naturality_aux_radialPair R (n := n) =
    T96A06_coneMap_sphereToDisk_naturality_aux_radialPair R (n := n) ≫
      T96A06_coneMap_sphereToDisk_naturality_aux_openPair ψ R := by
  change CoefficientRadialPair.pairMap R _ _ _ _ ≫
      CoefficientRadialPair.pairMap R _ _ _ _ =
    CoefficientRadialPair.pairMap R _ _ _ _ ≫
      CoefficientRadialPair.pairMap R _ _ _ _
  rw [← CoefficientPairNaturality.pair_comp, ← CoefficientPairNaturality.pair_comp]
  congr 1
  exact T96A06_coneMap_sphereToDisk_naturality_aux_radial_square ψ

theorem T96A06_coneMap_sphereToDisk_naturality_aux_radial_naturality (j : ℕ) :
    HomologicalComplex.homologyMap (closedPair ψ R) j ≫
      (CoefficientRadialPair.radialIso R n j).hom =
    (CoefficientRadialPair.radialIso R n j).hom ≫
      HomologicalComplex.homologyMap
        (T96A06_coneMap_sphereToDisk_naturality_aux_openPair ψ R) j := by
  exact (HomologicalComplex.homologyMap_comp _ _ j).symm.trans
    ((congrArg (fun f => HomologicalComplex.homologyMap f j)
      (T96A06_coneMap_sphereToDisk_naturality_aux_relative_square ψ R)).trans
      (HomologicalComplex.homologyMap_comp _ _ j))

theorem T96A06_coneMap_sphereToDisk_naturality_aux_radial_inverse (j : ℕ) :
    HomologicalComplex.homologyMap
        (T96A06_coneMap_sphereToDisk_naturality_aux_openPair ψ R) j ≫
      (CoefficientRadialPair.radialIso R n j).inv =
    (CoefficientRadialPair.radialIso R n j).inv ≫
      HomologicalComplex.homologyMap (closedPair ψ R) j := by
  apply (cancel_epi (CoefficientRadialPair.radialIso R n j).hom).mp
  have h := congrArg (fun f => f ≫ (CoefficientRadialPair.radialIso R n j).inv)
    (T96A06_coneMap_sphereToDisk_naturality_aux_radial_naturality ψ R j)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc] using h.symm

theorem T96A06_coneMap_sphereToDisk_naturality_aux_height :
    sphereHeight n ∘ sphereAction ψ = sphereHeight n := by
  funext x
  exact euclideanSnoc_last _ _

theorem T96A06_coneMap_sphereToDisk_naturality_aux_north_mapsTo :
    Set.MapsTo (sphereAction ψ) (northPoleComplement n) (northPoleComplement n) := by
  intro x hx
  change sphereHeight n (sphereAction ψ x) < 1
  rw [show sphereHeight n (sphereAction ψ x) = sphereHeight n x from
    congrFun (T96A06_coneMap_sphereToDisk_naturality_aux_height ψ) x]
  exact hx

theorem T96A06_coneMap_sphereToDisk_naturality_aux_upper_mapsTo :
    Set.MapsTo (sphereAction ψ) (openUpperHemisphere n) (openUpperHemisphere n) := by
  intro x hx
  change ¬ sphereHeight n (sphereAction ψ x) ≤ 0
  rw [show sphereHeight n (sphereAction ψ x) = sphereHeight n x from
    congrFun (T96A06_coneMap_sphereToDisk_naturality_aux_height ψ) x]
  exact hx

def T96A06_coneMap_sphereToDisk_naturality_aux_upperAction :
    C(openUpperHemisphere n, openUpperHemisphere n) :=
  ⟨fun x => ⟨sphereAction ψ x.1,
      T96A06_coneMap_sphereToDisk_naturality_aux_upper_mapsTo ψ x.2⟩, by fun_prop⟩

theorem T96A06_coneMap_sphereToDisk_naturality_aux_punctured_mapsTo :
    Set.MapsTo (T96A06_coneMap_sphereToDisk_naturality_aux_upperAction ψ)
      (puncturedUpperHemisphere n) (puncturedUpperHemisphere n) := by
  intro x hx
  exact T96A06_coneMap_sphereToDisk_naturality_aux_north_mapsTo ψ hx

def T96A06_coneMap_sphereToDisk_naturality_aux_upperPair :=
  CoefficientRadialPair.pairMap R _ _
    (T96A06_coneMap_sphereToDisk_naturality_aux_upperAction ψ)
    (T96A06_coneMap_sphereToDisk_naturality_aux_punctured_mapsTo ψ)

def T96A06_coneMap_sphereToDisk_naturality_aux_spherePair :=
  CoefficientRadialPair.pairMap R _ _ (sphereAction ψ)
    (T96A06_coneMap_sphereToDisk_naturality_aux_north_mapsTo ψ)

theorem T96A06_coneMap_sphereToDisk_naturality_aux_coordinate_square :
    (T96A06_coneMap_sphereToDisk_naturality_aux_upperAction ψ).comp
        (openDiskToOpenUpperMap n) =
      (openDiskToOpenUpperMap n).comp (openAction ψ) := by
  ext x : 1
  apply Subtype.ext
  apply Subtype.ext
  change euclideanSnoc (ψ.toFun (euclideanInit (euclideanSnoc x.1 _)))
    ((euclideanSnoc x.1 _) (Fin.last n)) = euclideanSnoc (ψ.toFun x.1) _
  rw [euclideanInit_snoc, euclideanSnoc_last]
  change euclideanSnoc (ψ.toFun x.1) (Real.sqrt (1 - ‖x.1‖ ^ 2)) =
    euclideanSnoc (ψ.toFun x.1) (Real.sqrt (1 - ‖ψ.toFun x.1‖ ^ 2))
  rw [ψ.norm_map]

theorem T96A06_coneMap_sphereToDisk_naturality_aux_relative_coordinate :
    T96A06_coneMap_sphereToDisk_naturality_aux_openPair ψ R ≫
      CoefficientSphereShift.coordinateMap R n =
    CoefficientSphereShift.coordinateMap R n ≫
      T96A06_coneMap_sphereToDisk_naturality_aux_upperPair ψ R := by
  change CoefficientRadialPair.pairMap R _ _ _ _ ≫
      CoefficientRadialPair.pairMap R _ _ _ _ =
    CoefficientRadialPair.pairMap R _ _ _ _ ≫
      CoefficientRadialPair.pairMap R _ _ _ _
  rw [← CoefficientPairNaturality.pair_comp, ← CoefficientPairNaturality.pair_comp]
  congr 1
  exact (T96A06_coneMap_sphereToDisk_naturality_aux_coordinate_square ψ).symm

theorem T96A06_coneMap_sphereToDisk_naturality_aux_coordinate_naturality (j : ℕ) :
    HomologicalComplex.homologyMap
        (T96A06_coneMap_sphereToDisk_naturality_aux_openPair ψ R) j ≫
      (CoefficientSphereShift.coordinateIso R n j).hom =
    (CoefficientSphereShift.coordinateIso R n j).hom ≫
      HomologicalComplex.homologyMap
        (T96A06_coneMap_sphereToDisk_naturality_aux_upperPair ψ R) j := by
  exact (HomologicalComplex.homologyMap_comp _ _ j).symm.trans
    ((congrArg (fun f => HomologicalComplex.homologyMap f j)
      (T96A06_coneMap_sphereToDisk_naturality_aux_relative_coordinate ψ R)).trans
      (HomologicalComplex.homologyMap_comp _ _ j))

theorem T96A06_coneMap_sphereToDisk_naturality_aux_coordinate_inverse (j : ℕ) :
    HomologicalComplex.homologyMap
        (T96A06_coneMap_sphereToDisk_naturality_aux_upperPair ψ R) j ≫
      (CoefficientSphereShift.coordinateIso R n j).inv =
    (CoefficientSphereShift.coordinateIso R n j).inv ≫
      HomologicalComplex.homologyMap
        (T96A06_coneMap_sphereToDisk_naturality_aux_openPair ψ R) j := by
  apply (cancel_epi (CoefficientSphereShift.coordinateIso R n j).hom).mp
  have h := congrArg (fun f => f ≫ (CoefficientSphereShift.coordinateIso R n j).inv)
    (T96A06_coneMap_sphereToDisk_naturality_aux_coordinate_naturality ψ R j)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc] using h.symm

def T96A06_coneMap_sphereToDisk_naturality_aux_upperInclusion :
    C(openUpperHemisphere n, ambientSphere n) := ⟨Subtype.val, continuous_subtype_val⟩

theorem T96A06_coneMap_sphereToDisk_naturality_aux_upperInclusion_mapsTo :
    Set.MapsTo (T96A06_coneMap_sphereToDisk_naturality_aux_upperInclusion (n := n))
      (puncturedUpperHemisphere n) (northPoleComplement n) := fun _ h => h

theorem T96A06_coneMap_sphereToDisk_naturality_aux_excision_actual :
    CoefficientExcision.excisionMap R (northPoleComplement n) (closedLowerHemisphere n) =
      CoefficientRadialPair.pairMap R _ _
        (T96A06_coneMap_sphereToDisk_naturality_aux_upperInclusion (n := n))
        T96A06_coneMap_sphereToDisk_naturality_aux_upperInclusion_mapsTo := rfl

theorem T96A06_coneMap_sphereToDisk_naturality_aux_relative_excision :
    T96A06_coneMap_sphereToDisk_naturality_aux_upperPair ψ R ≫
      CoefficientExcision.excisionMap R (northPoleComplement n) (closedLowerHemisphere n) =
    CoefficientExcision.excisionMap R (northPoleComplement n) (closedLowerHemisphere n) ≫
      T96A06_coneMap_sphereToDisk_naturality_aux_spherePair ψ R := by
  rw [T96A06_coneMap_sphereToDisk_naturality_aux_excision_actual]
  change CoefficientRadialPair.pairMap R _ _ _ _ ≫
      CoefficientRadialPair.pairMap R _ _ _ _ =
    CoefficientRadialPair.pairMap R _ _ _ _ ≫
      CoefficientRadialPair.pairMap R _ _ _ _
  rw [← CoefficientPairNaturality.pair_comp, ← CoefficientPairNaturality.pair_comp]
  congr 1

theorem T96A06_coneMap_sphereToDisk_naturality_aux_excision_naturality (j : ℕ) :
    HomologicalComplex.homologyMap
        (T96A06_coneMap_sphereToDisk_naturality_aux_upperPair ψ R) j ≫
      (CoefficientSphereShift.hemisphereIso R n j).hom =
    (CoefficientSphereShift.hemisphereIso R n j).hom ≫
      HomologicalComplex.homologyMap
        (T96A06_coneMap_sphereToDisk_naturality_aux_spherePair ψ R) j := by
  rw [CoefficientSphereShift.hemisphereIso_hom]
  exact (HomologicalComplex.homologyMap_comp _ _ j).symm.trans
    ((congrArg (fun f => HomologicalComplex.homologyMap f j)
      (T96A06_coneMap_sphereToDisk_naturality_aux_relative_excision ψ R)).trans
      (HomologicalComplex.homologyMap_comp _ _ j))

theorem T96A06_coneMap_sphereToDisk_naturality_aux_excision_inverse (j : ℕ) :
    HomologicalComplex.homologyMap
        (T96A06_coneMap_sphereToDisk_naturality_aux_spherePair ψ R) j ≫
      (CoefficientSphereShift.hemisphereIso R n j).inv =
    (CoefficientSphereShift.hemisphereIso R n j).inv ≫
      HomologicalComplex.homologyMap
        (T96A06_coneMap_sphereToDisk_naturality_aux_upperPair ψ R) j := by
  apply (cancel_epi (CoefficientSphereShift.hemisphereIso R n j).hom).mp
  have h := congrArg (fun f => f ≫ (CoefficientSphereShift.hemisphereIso R n j).inv)
    (T96A06_coneMap_sphereToDisk_naturality_aux_excision_naturality ψ R j)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc] using h.symm

theorem T96A06_coneMap_sphereToDisk_naturality_aux_projection (j : ℕ) :
    HomologicalComplex.homologyMap
        (CoefficientRadialPair.absoluteMap R (sphereAction ψ)) j ≫
      HomologicalComplex.homologyMap
        (CoefficientPairSequence.projection R (northPoleComplement n)) j =
    HomologicalComplex.homologyMap
        (CoefficientPairSequence.projection R (northPoleComplement n)) j ≫
      HomologicalComplex.homologyMap
        (T96A06_coneMap_sphereToDisk_naturality_aux_spherePair ψ R) j := by
  exact (HomologicalComplex.homologyMap_comp _ _ j).symm.trans
    ((congrArg (fun f => HomologicalComplex.homologyMap f j)
      (CoefficientRadialPair.projection R _ _ (sphereAction ψ)
        (T96A06_coneMap_sphereToDisk_naturality_aux_north_mapsTo ψ)).symm).trans
      (HomologicalComplex.homologyMap_comp _ _ j))

private theorem T96A06_coneMap_sphereToDisk_naturality_aux_comp
    {C : Type*} [Category C] {A B D : C} {a : A ⟶ A} {b : B ⟶ B}
    {c : D ⟶ D} {f : A ⟶ B} {g : B ⟶ D}
    (h : a ≫ f = f ≫ b) (h' : b ≫ g = g ≫ c) :
    a ≫ (f ≫ g) = (f ≫ g) ≫ c := by
  calc
    _ = (a ≫ f) ≫ g := (Category.assoc _ _ _).symm
    _ = (f ≫ b) ≫ g := congrArg (fun t => t ≫ g) h
    _ = f ≫ (b ≫ g) := Category.assoc _ _ _
    _ = f ≫ (g ≫ c) := congrArg (fun t => f ≫ t) h'
    _ = _ := (Category.assoc _ _ _).symm

theorem T96A06_coneMap_sphereToDisk_naturality (j : ℕ) (hj : j ≠ 0) :
    HomologicalComplex.homologyMap (CoefficientRadialPair.absoluteMap R (sphereAction ψ)) j ≫
      (CoefficientSphereShift.sphereToDiskIso R n j hj).hom =
    (CoefficientSphereShift.sphereToDiskIso R n j hj).hom ≫
      HomologicalComplex.homologyMap (closedPair ψ R) j := by
  rw [CoefficientSphereShift.sphereToDiskIso_hom]
  exact T96A06_coneMap_sphereToDisk_naturality_aux_comp
    (T96A06_coneMap_sphereToDisk_naturality_aux_projection ψ R j)
    (T96A06_coneMap_sphereToDisk_naturality_aux_comp
      (T96A06_coneMap_sphereToDisk_naturality_aux_excision_inverse ψ R j)
      (T96A06_coneMap_sphereToDisk_naturality_aux_comp
        (T96A06_coneMap_sphereToDisk_naturality_aux_coordinate_inverse ψ R j)
        (T96A06_coneMap_sphereToDisk_naturality_aux_radial_inverse ψ R j)))

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
lemma T96A06_sqFun_continuous_aux_re :
    Continuous (fun p : ℝ × ℝ ↦
      (p.1 ^ 2 - p.2 ^ 2) / Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p.1 ^ 2 + p.2 ^ 2 = 0
  · have hp1 : p.1 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    have hp2 : p.2 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    rw [ContinuousAt, show (p.1 ^ 2 - p.2 ^ 2) /
      Real.sqrt (p.1 ^ 2 + p.2 ^ 2) = 0 by simp [hp1, hp2]]
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (g := fun q ↦ Real.sqrt (q.1 ^ 2 + q.2 ^ 2))
      (fun q ↦ abs_nonneg _) ?_ ?_
    · intro q
      by_cases hq : q.1 ^ 2 + q.2 ^ 2 = 0
      · simp [hq]
      · have hs : 0 < Real.sqrt (q.1 ^ 2 + q.2 ^ 2) :=
          Real.sqrt_pos.2 (by positivity)
        simp only [Function.comp_apply]
        rw [abs_div, abs_of_pos hs]
        apply (div_le_iff₀ hs).2
        have ha : abs (q.1 ^ 2 - q.2 ^ 2) ≤ q.1 ^ 2 + q.2 ^ 2 := by
          rw [abs_le]
          constructor <;> nlinarith [sq_nonneg q.1, sq_nonneg q.2]
        calc
          _ ≤ q.1 ^ 2 + q.2 ^ 2 := ha
          _ = _ := (Real.mul_self_sqrt (by positivity)).symm
    · convert ((continuous_fst.pow 2).add (continuous_snd.pow 2)).sqrt.tendsto p using 1
      simp [hp]
  · apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (by positivity) (Ne.symm hp))

lemma T96A06_sqFun_continuous_aux_im :
    Continuous (fun p : ℝ × ℝ ↦
      (2 * p.1 * p.2) / Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p.1 ^ 2 + p.2 ^ 2 = 0
  · have hp1 : p.1 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    have hp2 : p.2 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    rw [ContinuousAt, show (2 * p.1 * p.2) /
      Real.sqrt (p.1 ^ 2 + p.2 ^ 2) = 0 by simp [hp1, hp2]]
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (g := fun q ↦ Real.sqrt (q.1 ^ 2 + q.2 ^ 2))
      (fun q ↦ abs_nonneg _) ?_ ?_
    · intro q
      by_cases hq : q.1 ^ 2 + q.2 ^ 2 = 0
      · simp [hq]
      · have hs : 0 < Real.sqrt (q.1 ^ 2 + q.2 ^ 2) :=
          Real.sqrt_pos.2 (by positivity)
        simp only [Function.comp_apply]
        rw [abs_div, abs_of_pos hs]
        apply (div_le_iff₀ hs).2
        have ha : abs (2 * q.1 * q.2) ≤ q.1 ^ 2 + q.2 ^ 2 := by
          rw [abs_le]
          constructor <;> nlinarith [sq_nonneg (q.1 - q.2), sq_nonneg (q.1 + q.2)]
        calc
          _ ≤ q.1 ^ 2 + q.2 ^ 2 := ha
          _ = _ := (Real.mul_self_sqrt (by positivity)).symm
    · convert ((continuous_fst.pow 2).add (continuous_snd.pow 2)).sqrt.tendsto p using 1
      simp [hp]
  · apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (by positivity) (Ne.symm hp))

theorem T96A06_sqFun_continuous (n : ℕ) : Continuous (sqFun n) := by
  have hc (i : Fin (n + 2)) :
      Continuous (fun x : EuclideanSpace ℝ (Fin (n + 2)) ↦ x i) :=
    (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
  unfold sqFun
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  split_ifs with hi0 hi1
  · simpa using T96A06_sqFun_continuous_aux_re.comp
      ((hc 0).prodMk (hc 1))
  · simpa using T96A06_sqFun_continuous_aux_im.comp
      ((hc 0).prodMk (hc 1))
  · exact hc i

/-- **Leaf S2.** `sqFun` preserves the norm and commutes with halving.
`(a²-b²)² + (2ab)² = (a²+b²)²`; if `a = b = 0` both sides vanish. -/
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
  ext x i
  change euclideanSnoc (sqFun n (euclideanInit x.1)) (sphereHeight (n + 2) x) i =
    sqFun (n + 1) x.1 i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hlast : Fin.last (n + 2) ≠ (1 : Fin (n + 3)) := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    simp [sqFun, euclideanSnoc,
      euclideanInit, sphereHeight, hlast]
  · have hinit (k : Fin (n + 2)) : euclideanInit x.1 k = x.1 k.castSucc := by
      rfl
    by_cases h0 : j = 0
    · subst j
      simp [sqFun, euclideanSnoc,
        sphereHeight, hinit]
    · by_cases h1 : j = 1
      · subst j
        simp [sqFun, euclideanSnoc,
          sphereHeight, hinit]
        rw [show (1 : Fin (n + 3)) = (1 : Fin (n + 2)).castSucc by rfl,
          Fin.snoc_castSucc]
        simp
      · have hc0 : j.castSucc ≠ (0 : Fin (n + 3)) := by
          intro h
          apply h0
          apply Fin.ext
          exact congrArg (fun z : Fin (n + 3) => z.val) h
        have hc1 : j.castSucc ≠ (1 : Fin (n + 3)) := by
          intro h
          apply h1
          apply Fin.ext
          exact congrArg (fun z : Fin (n + 3) => z.val) h
        simp [sqFun, euclideanSnoc,
          sphereHeight, hinit, h0, h1, hc0, hc1]

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
noncomputable def T96A06_angleMap_isCoveringMap_aux_homeomorph :
    Circle ≃ₜ euclideanUnitSphere 2 where
  toFun z := ⟨Complex.orthonormalBasisOneI.repr z, by
    rw [Metric.mem_sphere, dist_zero_right,
      Complex.orthonormalBasisOneI.repr.norm_map]
    exact Circle.norm_coe z⟩
  invFun x := ⟨Complex.orthonormalBasisOneI.repr.symm x, by
    change Complex.orthonormalBasisOneI.repr.symm x ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm,
      Complex.orthonormalBasisOneI.repr.symm.norm_map,
      ← mem_sphere_zero_iff_norm]
    exact x.property⟩
  left_inv z := by
    apply Subtype.ext
    exact Complex.orthonormalBasisOneI.repr.symm_apply_apply z
  right_inv x := by
    apply Subtype.ext
    exact Complex.orthonormalBasisOneI.repr.apply_symm_apply x
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem T96A06_angleMap_isCoveringMap : IsCoveringMap angleMap := by
  have h :=
    (Circle.isCoveringMap_exp.comp_homeomorph
      (Homeomorph.mulLeft₀ (2 * Real.pi : ℝ) (by positivity))).homeomorph_comp
        T96A06_angleMap_isCoveringMap_aux_homeomorph
  convert h using 1
  funext t
  apply Subtype.ext
  ext i
  fin_cases i
  · change Real.cos (2 * Real.pi * t) =
      (Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)).re
    exact (Complex.exp_ofReal_mul_I_re (2 * Real.pi * t)).symm
  · change Real.sin (2 * Real.pi * t) =
      (Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)).im
    exact (Complex.exp_ofReal_mul_I_im (2 * Real.pi * t)).symm

/-- Banked from lemma-1's round-2 partial: every singular simplex of the circle
lifts through `angleMap` once one lifted vertex is chosen. -/
lemma T96A06_circle_windingCochain_aux_lift (hcov : IsCoveringMap angleMap)
    (n : ℕ) (s : C(stdSimplex ℝ (Fin (n + 1)), euclideanUnitSphere 2))
    (e : ℝ) (he : angleMap e =
      s ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n + 1))⟩) :
    ∃ L : C(stdSimplex ℝ (Fin (n + 1)), ℝ), angleMap ∘ L = s := by
  letI : ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ _).contractibleSpace
      ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n + 1))⟩
  letI : LocPathConnectedSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ _).locPathConnectedSpace
  obtain ⟨L, ⟨_, hL⟩, _⟩ := hcov.existsUnique_continuousMap_lifts s
    ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n + 1))⟩ e he
  exact ⟨L, hL⟩

open Classical in
/-- Endpoint displacement `L(v₁) - L(v₀)` of a singular 1-simplex of the
circle, read along a chosen lift through `angleMap` (`0` if there is none;
with `hcov` every simplex has one, `T96A06_circle_windingCochain_aux_lift`). -/
def windingDisp (s : C(stdSimplex ℝ (Fin 2), euclideanUnitSphere 2)) : ℝ :=
  if h : ∃ L : C(stdSimplex ℝ (Fin 2), ℝ), angleMap ∘ L = s then
    h.choose ⟨_, single_mem_stdSimplex ℝ (1 : Fin 2)⟩ -
      h.choose ⟨_, single_mem_stdSimplex ℝ (0 : Fin 2)⟩
  else 0

/-- The winding cochain: `windingDisp` extended `ℚ`-linearly over the
generators, built like `CoefficientCoveringTransfer.transferDegree`. -/
def windingCochain : circleChains.X 1 ⟶ ModuleCat.of ℚ ℝ :=
  Limits.Sigma.desc (fun σ : SingularSubdivision.SingularSimplex (TopCat.of (euclideanUnitSphere 2)) 1 =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ℝ
      (windingDisp ((TopCat.toSSetObjEquiv (TopCat.of (euclideanUnitSphere 2))
        (Opposite.op (SimplexCategory.mk 1))) σ))))

/-- **Leaf C1b-gen.** `windingCochain` on a generator.  Copy the proof of
`CoefficientCoveringTransfer.generator_transfer` (`Sigma.ι_desc`, then
`apply_symm_apply`). -/
theorem T96A06_circle_windingCochain_aux_generator
    (s : C(stdSimplex ℝ (Fin 2), euclideanUnitSphere 2)) :
    CoefficientH0.singularGenerator ℚ (TopCat.of (euclideanUnitSphere 2)) 1
        (SingularSubdivision.singularSimplexOfContinuousMap _ 1 s) ≫ windingCochain =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ℝ (windingDisp s)) := by
  unfold windingCochain CoefficientH0.singularGenerator
  simp only [id_eq]
  erw [Limits.Sigma.ι_desc]
  exact congrArg (fun x => ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ℝ (windingDisp x)))
    ((TopCat.toSSetObjEquiv (TopCat.of (euclideanUnitSphere 2))
      (Opposite.op (SimplexCategory.mk 1))).apply_symm_apply s)

/-- **Leaf C1b-surj.** `angleMap` is onto the circle: a unit vector `(a, b)` is
`(cos θ, sin θ)` for `θ = Complex.arg (a + b i)`; take `t = θ / 2π`. -/
-- BEGIN SEAT AREA
theorem T96A06_circle_windingCochain_aux_surjective : Function.Surjective angleMap := by
  sorry
-- END SEAT AREA

/-- **Leaf C1b-disp.** The displacement does not depend on the lift: two lifts
of `s` differ by a continuous function into `ℤ` (`cos`/`sin` periodicity),
constant on the connected simplex. -/
lemma T96A06_circle_windingCochain_aux_disp_eq_angle_shift
    (a b t : ℝ) (h : angleMap a = angleMap b) :
    angleMap (t + (a - b)) = angleMap t := by
  have hc : Real.cos (2 * Real.pi * a) = Real.cos (2 * Real.pi * b) := by
    have := congrArg (fun x : euclideanUnitSphere 2 => x.1 (0 : Fin 2)) h
    simpa [angleMap] using this
  have hs : Real.sin (2 * Real.pi * a) = Real.sin (2 * Real.pi * b) := by
    have := congrArg (fun x : euclideanUnitSphere 2 => x.1 (1 : Fin 2)) h
    simpa [angleMap] using this
  apply Subtype.ext
  ext i
  fin_cases i
  · change Real.cos (2 * Real.pi * (t + (a - b))) = Real.cos (2 * Real.pi * t)
    rw [show 2 * Real.pi * (t + (a - b)) =
      2 * Real.pi * t + (2 * Real.pi * a - 2 * Real.pi * b) by ring]
    rw [Real.cos_add, Real.cos_sub, Real.sin_sub, hc, hs]
    ring_nf
    calc
      _ = Real.cos (Real.pi * t * 2) *
          (Real.cos (Real.pi * b * 2) ^ 2 + Real.sin (Real.pi * b * 2) ^ 2) := by ring
      _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one]
  · change Real.sin (2 * Real.pi * (t + (a - b))) = Real.sin (2 * Real.pi * t)
    rw [show 2 * Real.pi * (t + (a - b)) =
      2 * Real.pi * t + (2 * Real.pi * a - 2 * Real.pi * b) by ring]
    rw [Real.sin_add, Real.cos_sub, Real.sin_sub, hc, hs]
    ring_nf
    calc
      _ = Real.sin (Real.pi * t * 2) *
          (Real.cos (Real.pi * b * 2) ^ 2 + Real.sin (Real.pi * b * 2) ^ 2) := by ring
      _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one]

theorem T96A06_circle_windingCochain_aux_disp_eq
    (s : C(stdSimplex ℝ (Fin 2), euclideanUnitSphere 2))
    (L : C(stdSimplex ℝ (Fin 2), ℝ)) (hL : angleMap ∘ L = s) :
    windingDisp s = L ⟨_, single_mem_stdSimplex ℝ (1 : Fin 2)⟩ -
      L ⟨_, single_mem_stdSimplex ℝ (0 : Fin 2)⟩ := by
  classical
  unfold windingDisp
  split_ifs with hex
  · let M := hex.choose
    let v0 : stdSimplex ℝ (Fin 2) :=
      ⟨_, single_mem_stdSimplex ℝ (0 : Fin 2)⟩
    let v1 : stdSimplex ℝ (Fin 2) :=
      ⟨_, single_mem_stdSimplex ℝ (1 : Fin 2)⟩
    have hM : angleMap ∘ M = s := hex.choose_spec
    have hbase : angleMap (M v0) = angleMap (L v0) := by
      rw [show angleMap (M v0) = s v0 from congrFun hM v0,
        show angleMap (L v0) = s v0 from congrFun hL v0]
    let L' : C(stdSimplex ℝ (Fin 2), ℝ) :=
      ⟨fun x => L x + (M v0 - L v0), by fun_prop⟩
    have hL' : angleMap ∘ L' = s := by
      funext x
      change angleMap (L x + (M v0 - L v0)) = s x
      rw [T96A06_circle_windingCochain_aux_disp_eq_angle_shift
        (M v0) (L v0) (L x) hbase]
      exact congrFun hL x
    have hL'0 : L' v0 = M v0 := by
      change L v0 + (M v0 - L v0) = M v0
      ring
    letI : ContractibleSpace (stdSimplex ℝ (Fin 2)) :=
      (convex_stdSimplex ℝ _).contractibleSpace
        ⟨_, single_mem_stdSimplex ℝ (0 : Fin 2)⟩
    letI : LocPathConnectedSpace (stdSimplex ℝ (Fin 2)) :=
      (convex_stdSimplex ℝ _).locPathConnectedSpace
    have heq : L' = M :=
      (T96A06_angleMap_isCoveringMap.existsUnique_continuousMap_lifts
        s v0 (M v0) (by simpa using congrFun hM v0)).unique
          ⟨hL'0, hL'⟩ ⟨rfl, hM⟩
    have hv1 := congrArg (fun F : C(stdSimplex ℝ (Fin 2), ℝ) => F v1) heq
    change M v1 - M v0 = L v1 - L v0
    change L' v1 = M v1 at hv1
    dsimp [L'] at hv1
    linarith
  · exact (hex ⟨L, hL⟩).elim

/-- **Leaf C1b-cocycle.** `W ∘ d₂ = 0`.  Ext over generators
(`Limits.Sigma.hom_ext`, `toSSetObjEquiv`); lift the whole 2-simplex
(`aux_lift`, vertex preimage from `aux_surjective`); by
`CoefficientH0.singularGenerator_boundary`,
`singularSimplexOfContinuousMap_face` and `aux_generator`, each face's
displacement is read off the restricted lift (`aux_disp_eq`), and the three
terms telescope. -/
theorem T96A06_circle_windingCochain_aux_cocycle (hcov : IsCoveringMap angleMap) :
    windingCochain.hom ∘ₗ (circleChains.d 2 1).hom = 0 := by
  sorry

/-- **Leaf C1b-sq-angle.** On the circle the squaring cone map doubles the
angle: `(cos x, sin x) ↦ (cos²x - sin²x, 2 sin x cos x) = (cos 2x, sin 2x)`. -/
theorem T96A06_circle_windingCochain_aux_sq_angle (t : ℝ) :
    boundaryAction (sqCone 0) (angleMap t) = angleMap (2 * t) := by
  sorry

/-- **Leaf C1b-sq.** `W` scales by `2` under squaring.  Ext over generators;
`CoefficientH0.singularGenerator_singularPostcomposition`; if `L` lifts `s`
then `2L` lifts `squaring ∘ s` (`aux_sq_angle`), so by `aux_disp_eq` the
displacement doubles. -/
theorem T96A06_circle_windingCochain_aux_sq (hcov : IsCoveringMap angleMap) :
    windingCochain.hom ∘ₗ ((CoefficientH0.singularPostcomposition ℚ
        (boundaryAction (sqCone 0))).f 1).hom = (2 : ℚ) • windingCochain.hom := by
  sorry

/-- **Leaf C1b-cycle.** A cycle with nonzero winding: the generator of the
simplex `x ↦ angleMap (x 1)` (equal endpoints `angleMap 0 = angleMap 1`, so its
boundary `v₁ - v₀` vanishes by `singularGenerator_boundary`); it lifts by
`x ↦ x 1`, so `aux_generator` and `aux_disp_eq` give `W = 1`. -/
theorem T96A06_circle_windingCochain_aux_cycle :
    ∃ c : circleChains.X 1, (circleChains.d 1 0).hom c = 0 ∧ windingCochain.hom c ≠ 0 := by
  let L : C(stdSimplex ℝ (Fin 2), ℝ) :=
    ⟨fun x => x.1 (1 : Fin 2),
      (continuous_apply (1 : Fin 2)).comp continuous_subtype_val⟩
  let s : C(stdSimplex ℝ (Fin 2), euclideanUnitSphere 2) :=
    ⟨fun x => angleMap (L x),
      T96A06_angleMap_isCoveringMap.continuous.comp L.continuous⟩
  let σ := SingularSubdivision.singularSimplexOfContinuousMap
    (TopCat.of (euclideanUnitSphere 2)) 1 s
  let c : circleChains.X 1 :=
    (CoefficientH0.singularGenerator ℚ
      (TopCat.of (euclideanUnitSphere 2)) 1 σ).hom 1
  refine ⟨c, ?_, ?_⟩
  · have hfaces :
        (TopCat.toSSet.obj (TopCat.of (euclideanUnitSphere 2))).δ (0 : Fin 2) σ =
          (TopCat.toSSet.obj (TopCat.of (euclideanUnitSphere 2))).δ (1 : Fin 2) σ := by
      rw [SingularSubdivision.singularSimplexOfContinuousMap_face,
        SingularSubdivision.singularSimplexOfContinuousMap_face]
      congr 1
      ext x
      simp [s, L, SingularSubdivision.affineSimplex, angleMap,
        Real.cos_two_pi, Real.sin_two_pi]
    have hboundary := CoefficientH0.singularGenerator_boundary ℚ
      (TopCat.of (euclideanUnitSphere 2)) 0 σ
    rw [Fin.sum_univ_two, hfaces] at hboundary
    simp at hboundary
    exact congrArg (fun f => f.hom 1) hboundary
  · have hcomp : angleMap ∘ L = s := by rfl
    have hdisp := T96A06_circle_windingCochain_aux_disp_eq s L hcomp
    have hgen := T96A06_circle_windingCochain_aux_generator s
    have heval := congrArg (fun f => f.hom 1) hgen
    change windingCochain.hom c ≠ 0
    have hone : windingCochain.hom c = 1 := by
      simpa [c, σ, hdisp, L] using heval
    rw [hone]
    norm_num

/-- **Leaf C1b.** The angle-displacement cochain (assembly of the C1b leaves). -/
theorem T96A06_circle_windingCochain (hcov : IsCoveringMap angleMap) :
    ∃ W : (circleChains.X 1) →ₗ[ℚ] ℝ,
      W ∘ₗ (circleChains.d 2 1).hom = 0 ∧
      W ∘ₗ ((CoefficientH0.singularPostcomposition ℚ
        (boundaryAction (sqCone 0))).f 1).hom = (2 : ℚ) • W ∧
      ∃ c : circleChains.X 1, (circleChains.d 1 0).hom c = 0 ∧ W c ≠ 0 :=
  ⟨windingCochain.hom, T96A06_circle_windingCochain_aux_cocycle hcov,
    T96A06_circle_windingCochain_aux_sq hcov, T96A06_circle_windingCochain_aux_cycle⟩

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
  let K := circleChains
  let φ := CoefficientH0.singularPostcomposition ℚ (boundaryAction (sqCone 0))
  have hd' : K.d 2 1 ≫ ModuleCat.ofHom W = 0 := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext_iff.mpr fun x => by
      have h := LinearMap.congr_fun hd x
      simpa [K, ModuleCat.hom_comp] using h
  let w : K.homology 1 ⟶ ModuleCat.of ℚ ℝ :=
    K.homologyι 1 ≫ K.descOpcycles (ModuleCat.ofHom W) 2 (by simp) hd'
  let ec : ModuleCat.of ℚ ℚ ⟶ K.X 1 :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ (K.X 1) c)
  have hec : ec 1 = c := by
    change (1 : ℚ) • c = c
    simp
  have hcycle : ec ≫ K.d 1 0 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    change K.d 1 0 (q • c) = 0
    rw [map_smul, hc, smul_zero]
  let z := K.liftCycles ec 0 (by simp) hcycle
  let x : K.homology 1 := K.homologyπ 1 (z 1)
  have hwx : w x = W c := by
    have hz := ConcreteCategory.congr_hom (K.liftCycles_i ec 0 (by simp) hcycle) 1
    have hp := ConcreteCategory.congr_hom (K.homology_π_ι 1) (z 1)
    have hdsc := ConcreteCategory.congr_hom
      (K.p_descOpcycles (ModuleCat.ofHom W) 2 (by simp) hd') (K.iCycles 1 (z 1))
    simp only [CategoryTheory.comp_apply] at hz hp hdsc
    change (K.descOpcycles (ModuleCat.ofHom W) 2 (by simp) hd')
      (K.homologyι 1 (K.homologyπ 1 (z 1))) = W c
    rw [hp, hdsc, hz, hec]
    rfl
  have hx : x ≠ 0 := by
    intro hx0
    apply hW
    rw [← hwx, hx0, map_zero]
  have hdim : Module.finrank ℚ (K.homology 1) = 1 := by
    let u := CoefficientFirstReflection.topIso ℚ 0
    exact u.toLinearEquiv.finrank_eq.trans (by simp)
  have winj : Function.Injective w := by
    intro y₁ y₂ hy
    have hy0 : w (y₁ - y₂) = 0 := by rw [map_sub, hy, sub_self]
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hdim hx (y₁ - y₂)
    rw [← ha, map_smul] at hy0
    have haw : a = 0 := by
      apply (smul_eq_zero.mp hy0).resolve_right
      simpa [hwx] using hW
    exact sub_eq_zero.mp (by rw [← ha, haw, zero_smul])
  have hmap :
      (CoefficientRadialPair.F ℚ 1).map
          (TopCat.ofHom (boundaryAction (sqCone 0))) =
        HomologicalComplex.homologyMap φ 1 := by
    rfl
  have hnatH : HomologicalComplex.homologyMap φ 1 ≫ w = (2 : ℚ) • w := by
    dsimp only [w]
    rw [HomologicalComplex.homologyι_naturality_assoc]
    rw [HomologicalComplex.opcyclesMap_comp_descOpcycles]
    have hop : K.descOpcycles (φ.f 1 ≫ ModuleCat.ofHom W) 2 (by simp) (by
        rw [← φ.comm_assoc, hd', comp_zero]) =
        K.descOpcycles (ModuleCat.ofHom ((2 : ℚ) • W)) 2 (by simp) (by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro q
          change (2 : ℚ) • W (K.d 2 1 q) = 0
          rw [show W (K.d 2 1 q) = 0 from LinearMap.congr_fun hd q, smul_zero]) := by
      apply (cancel_epi (K.pOpcycles 1)).mp
      rw [HomologicalComplex.p_descOpcycles, HomologicalComplex.p_descOpcycles]
      apply ModuleCat.hom_ext
      simpa [φ, K, ModuleCat.hom_comp] using hnat
    rw [hop]
    have hdesc : K.descOpcycles (ModuleCat.ofHom ((2 : ℚ) • W)) 2 (by simp) (by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro q
        change (2 : ℚ) • W (K.d 2 1 q) = 0
        rw [show W (K.d 2 1 q) = 0 from LinearMap.congr_fun hd q, smul_zero]) =
        (2 : ℚ) • K.descOpcycles (ModuleCat.ofHom W) 2 (by simp) hd' := by
      apply (cancel_epi (K.pOpcycles 1)).mp
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro q
      have hp := ConcreteCategory.congr_hom
        (K.p_descOpcycles (ModuleCat.ofHom W) 2 (by simp) hd') q
      have hp2 := ConcreteCategory.congr_hom
        (K.p_descOpcycles (ModuleCat.ofHom ((2 : ℚ) • W)) 2 (by simp) (by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro r
          change (2 : ℚ) • W (K.d 2 1 r) = 0
          rw [show W (K.d 2 1 r) = 0 from LinearMap.congr_fun hd r, smul_zero])) q
      simp only [CategoryTheory.comp_apply, ModuleCat.hom_smul,
        LinearMap.smul_apply] at hp hp2 ⊢
      rw [hp, hp2]
      rfl
    rw [hdesc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    simp only [CategoryTheory.comp_apply, ModuleCat.hom_smul, LinearMap.smul_apply]
    rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  apply winj
  have hy := ConcreteCategory.congr_hom hnatH y
  simp only [CategoryTheory.comp_apply, ModuleCat.hom_smul,
    LinearMap.smul_apply] at hy
  rw [hmap]
  change w (HomologicalComplex.homologyMap φ 1 y) = w ((2 : ℚ) • y)
  have hwy : w ((2 : ℚ) • y) = (2 : ℚ) • w y :=
    (ModuleCat.Hom.hom w).map_smul 2 y
  rw [hwy]
  exact hy

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
lemma T96A06_liftMap_homotopic_aux_swap :
    swapE 0 = 2 ∧ swapE 1 = 3 ∧ swapE 2 = 0 ∧ swapE 3 = 1 ∧
    swapE.symm 0 = 2 ∧ swapE.symm 1 = 3 ∧ swapE.symm 2 = 0 ∧ swapE.symm 3 = 1 := by
  decide

lemma T96A06_liftMap_homotopic_aux_Q (x : S3) (i : Fin 4) :
    (Q4.comp Q4' x).1 i =
      if i = 0 then (x.1 0 ^ 2 - x.1 1 ^ 2) / Real.sqrt (x.1 0 ^ 2 + x.1 1 ^ 2)
      else if i = 1 then 2 * x.1 0 * x.1 1 / Real.sqrt (x.1 0 ^ 2 + x.1 1 ^ 2)
      else if i = 2 then (x.1 2 ^ 2 - x.1 3 ^ 2) / Real.sqrt (x.1 2 ^ 2 + x.1 3 ^ 2)
      else 2 * x.1 2 * x.1 3 / Real.sqrt (x.1 2 ^ 2 + x.1 3 ^ 2) := by
  rcases T96A06_liftMap_homotopic_aux_swap with ⟨h0,h1,h2,h3,hs0,hs1,hs2,hs3⟩
  fin_cases i <;> simp [Q4, Q4', boundaryAction, sqCone, sqFun,
    permutationMap, sphereHomeo, permutation_apply, h0,h1,h2,h3,hs0,hs1,hs2,hs3]

lemma T96A06_liftMap_homotopic_aux_lift (x : S3) (i : Fin 4) :
    (liftMap x).1 i =
      ‖WithLp.toLp 2 (T96A06.polynomialMap (WithLp.equiv 2 (Fin 4 → ℝ) x.1))‖⁻¹ *
      T96A06.polynomialMap (WithLp.equiv 2 (Fin 4 → ℝ) x.1) i := by
  simp [liftMap, proj_cover_aux_radial, sphereVec, T96A06.polyNZ, PiLp.smul_apply]

lemma T96A06_liftMap_homotopic_aux_inner (x : S3) :
    0 ≤ @inner ℝ _ _ (liftMap x).1 (Q4.comp Q4' x).1 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp_rw [T96A06_liftMap_homotopic_aux_lift,
    T96A06_liftMap_homotopic_aux_Q]
  simp only [Fin.sum_univ_succ]
  norm_num
  simp [T96A06.polynomialMap]
  have hn : 0 ≤ ‖WithLp.toLp 2
      (T96A06.polynomialMap (WithLp.equiv 2 (Fin 4 → ℝ) x.1))‖⁻¹ := by positivity
  have hr : 0 ≤ Real.sqrt (x.1 0 ^ 2 + x.1 1 ^ 2) := Real.sqrt_nonneg _
  have hs : 0 ≤ Real.sqrt (x.1 2 ^ 2 + x.1 3 ^ 2) := Real.sqrt_nonneg _
  simp only [real_inner_eq_re_inner, RCLike.inner_apply', conj_trivial,
    RCLike.re_to_real, mul_comm]
  ring_nf
  positivity

lemma T96A06_liftMap_homotopic_aux_nezero (p : Set.Icc (0 : ℝ) 1 × S3) :
    (1 - (p.1 : ℝ)) • (liftMap p.2).1 + (p.1 : ℝ) • (Q4.comp Q4' p.2).1 ≠ 0 := by
  intro hz
  by_cases ht : (p.1 : ℝ) = 1
  · have : (Q4.comp Q4' p.2).1 = 0 := by simpa [ht] using hz
    have hu : ‖(Q4.comp Q4' p.2).1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using (Q4.comp Q4' p.2).2
    rw [this, norm_zero] at hu
    norm_num at hu
  · have htlt : (p.1 : ℝ) < 1 := lt_of_le_of_ne (p.1.property).2 ht
    have hnorm : @inner ℝ _ _ (liftMap p.2).1 (liftMap p.2).1 = 1 := by
      rw [real_inner_self_eq_norm_sq]
      have := (liftMap p.2).2
      simpa [Metric.mem_sphere, dist_zero_right] using congrArg (fun z : ℝ => z ^ 2) this
    have hi := T96A06_liftMap_homotopic_aux_inner p.2
    have hpos : 0 < @inner ℝ _ _ (liftMap p.2).1
        ((1 - (p.1 : ℝ)) • (liftMap p.2).1 + (p.1 : ℝ) • (Q4.comp Q4' p.2).1) := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hnorm]
      have ht0 : 0 ≤ (p.1 : ℝ) := (p.1.property).1
      nlinarith
    rw [hz, inner_zero_right] at hpos
    exact lt_irrefl 0 hpos

theorem T96A06_liftMap_homotopic : ContinuousMap.Homotopic liftMap (Q4.comp Q4') := by
  let v : Set.Icc (0 : ℝ) 1 × S3 → EuclideanSpace ℝ (Fin 4) := fun p =>
    (1 - (p.1 : ℝ)) • (liftMap p.2).1 + (p.1 : ℝ) • (Q4.comp Q4' p.2).1
  refine ⟨{
    toFun := fun p => ⟨‖v p‖⁻¹ • v p, ?_⟩
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (T96A06_liftMap_homotopic_aux_nezero p)
  · apply Continuous.subtype_mk
    have hv : Continuous v := by
      have ht : Continuous (fun p : Set.Icc (0 : ℝ) 1 × S3 => (p.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      have hf : Continuous (fun p : Set.Icc (0 : ℝ) 1 × S3 => (liftMap p.2).1) :=
        continuous_subtype_val.comp (liftMap.continuous.comp continuous_snd)
      have hg : Continuous (fun p : Set.Icc (0 : ℝ) 1 × S3 => (Q4.comp Q4' p.2).1) :=
        continuous_subtype_val.comp ((Q4.comp Q4').continuous.comp continuous_snd)
      exact ((continuous_const.sub ht).smul hf).add (ht.smul hg)
    exact ((continuous_norm.comp hv).inv₀
      (fun p => norm_ne_zero_iff.mpr (T96A06_liftMap_homotopic_aux_nezero p))).smul hv
  · intro x
    apply Subtype.ext
    change ‖v (0, x)‖⁻¹ • v (0, x) = (liftMap x).1
    have hn : ‖(liftMap x).1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using (liftMap x).2
    simp [v, hn]
  · intro x
    apply Subtype.ext
    change ‖v (1, x)‖⁻¹ • v (1, x) = (Q4.comp Q4' x).1
    have hn : ‖(Q4.comp Q4' x).1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using (Q4.comp Q4' x).2
    simp [v, hn]

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
