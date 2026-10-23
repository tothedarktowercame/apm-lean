import Mathlib
import ConstructionTargets.PointWedgeVanKampen
import ConstructionTargets.CollaredConnectedSumHomology

/-! # Blueprint for the repaired APM t93A03 statement. -/

open FundamentalGroupoid
open scoped ContinuousMap

noncomputable section

abbrev T93A03E3 := EuclideanSpace ℝ (Fin 3)
abbrev T93A03Disk := Metric.closedBall (0 : T93A03E3) 1
abbrev T93A03Sphere2 := Metric.sphere (0 : T93A03E3) 1
abbrev T93A03Summand := Circle × T93A03Sphere2
abbrev T93A03Boundary := Metric.sphere (0 : T93A03E3) 1
abbrev T93A03CollarBall := Metric.closedBall (0 : T93A03E3) 2

def t93A03BoundaryInDisk (x : T93A03Boundary) : T93A03Disk :=
  ⟨x, by simpa [Metric.mem_closedBall, Metric.mem_sphere] using x.property.le⟩

def t93A03DiskInCollarBall (u : T93A03Disk) : T93A03CollarBall :=
  ⟨u, Metric.closedBall_subset_closedBall (by norm_num) u.property⟩

abbrev T93A03Punctured (φ : T93A03Disk → T93A03Summand) :=
  {x : T93A03Summand //
    x ∉ φ '' {u : T93A03Disk | ‖(u : T93A03E3)‖ < 1}}

inductive T93A03ConnectedSumRel
    (φ₁ φ₂ : T93A03Disk → T93A03Summand) :
    Sum (T93A03Punctured φ₁) (T93A03Punctured φ₂) →
      Sum (T93A03Punctured φ₁) (T93A03Punctured φ₂) → Prop
  | boundary (s : T93A03Boundary)
      (h₁ : φ₁ (t93A03BoundaryInDisk s) ∉
        φ₁ '' {u : T93A03Disk | ‖(u : T93A03E3)‖ < 1})
      (h₂ : φ₂ (t93A03BoundaryInDisk s) ∉
        φ₂ '' {u : T93A03Disk | ‖(u : T93A03E3)‖ < 1}) :
      T93A03ConnectedSumRel φ₁ φ₂
        (Sum.inl ⟨φ₁ (t93A03BoundaryInDisk s), h₁⟩)
        (Sum.inr ⟨φ₂ (t93A03BoundaryInDisk s), h₂⟩)

def T93A03ConnectedSum
    (φ₁ φ₂ : T93A03Disk → T93A03Summand) :=
  Quotient (Relation.EqvGen.setoid (T93A03ConnectedSumRel φ₁ φ₂))

noncomputable instance
    (φ₁ φ₂ : T93A03Disk → T93A03Summand) :
    TopologicalSpace (T93A03ConnectedSum φ₁ φ₂) :=
  TopologicalSpace.coinduced (fun z ↦ Quotient.mk _ z) inferInstance

namespace T93A03PiOne

open ConstructionTargets.CollaredConnectedSumHomology

/-- A concrete basepoint on the gluing two-sphere. -/
def sphereBasepoint : Sphere 3 :=
  ⟨EuclideanSpace.single 0 1, by
    simp [Metric.mem_sphere, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩

/-- **LEAF (P1).** The frozen quotient presentation is the generic
collared connected sum built from the same small maps. -/
theorem quotientHomeomorph
    (φ₁ φ₂ : T93A03Disk → T93A03Summand)
    (c₁ c₂ : BallCollar 3 T93A03Summand)
    (hc₁ : c₁.smallMap = φ₁) (hc₂ : c₂.smallMap = φ₂) :
    Nonempty (T93A03ConnectedSum φ₁ φ₂ ≃ₜ ConnectedSum c₁ c₂) := by
  subst φ₁
  subst φ₂
  let p₁ : T93A03Punctured c₁.smallMap → c₁.Punctured := fun x ↦
    ⟨x.1, by simpa [dist_eq_norm] using x.2⟩
  let p₂ : T93A03Punctured c₂.smallMap → c₂.Punctured := fun x ↦
    ⟨x.1, by simpa [dist_eq_norm] using x.2⟩
  let q₁ : c₁.Punctured → T93A03Punctured c₁.smallMap := fun x ↦
    ⟨x.1, by simpa [dist_eq_norm] using x.2⟩
  let q₂ : c₂.Punctured → T93A03Punctured c₂.smallMap := fun x ↦
    ⟨x.1, by simpa [dist_eq_norm] using x.2⟩
  let f : Sum (T93A03Punctured c₁.smallMap) (T93A03Punctured c₂.smallMap) →
      Sum c₁.Punctured c₂.Punctured
    | Sum.inl x => Sum.inl (p₁ x)
    | Sum.inr x => Sum.inr (p₂ x)
  let g : Sum c₁.Punctured c₂.Punctured →
      Sum (T93A03Punctured c₁.smallMap) (T93A03Punctured c₂.smallMap)
    | Sum.inl x => Sum.inl (q₁ x)
    | Sum.inr x => Sum.inr (q₂ x)
  have hfg (x) : g (f x) = x := by
    cases x <;> simp [f, g, p₁, p₂, q₁, q₂]
  have hgf (x) : f (g x) = x := by
    cases x <;> simp [f, g, p₁, p₂, q₁, q₂]
  have hfrel {x y} (h : T93A03ConnectedSumRel c₁.smallMap c₂.smallMap x y) :
      Relation.EqvGen (GlueRel c₁ c₂) (f x) (f y) := by
    cases h with
    | boundary s h₁ h₂ =>
      apply Relation.EqvGen.rel
      exact GlueRel.boundary s
  have hgrel {x y} (h : GlueRel c₁ c₂ x y) :
      Relation.EqvGen (T93A03ConnectedSumRel c₁.smallMap c₂.smallMap) (g x) (g y) := by
    cases h with
    | boundary s =>
      apply Relation.EqvGen.rel
      apply T93A03ConnectedSumRel.boundary s
  let F : T93A03ConnectedSum c₁.smallMap c₂.smallMap → ConnectedSum c₁ c₂ :=
    Quotient.map' f (fun _ _ h => by
      change Relation.EqvGen (GlueRel c₁ c₂) _ _
      induction h with
      | rel _ _ h => exact hfrel h
      | refl x => exact (Relation.EqvGen.refl (f x) :
          Relation.EqvGen (GlueRel c₁ c₂) (f x) (f x))
      | symm _ _ _ ih => exact ih.symm
      | trans x y z _ _ ih₁ ih₂ =>
        exact Relation.EqvGen.trans (f x) (f y) (f z) ih₁ ih₂)
  let G : ConnectedSum c₁ c₂ → T93A03ConnectedSum c₁.smallMap c₂.smallMap :=
    Quotient.map' g (fun _ _ h => by
      change Relation.EqvGen (T93A03ConnectedSumRel c₁.smallMap c₂.smallMap) _ _
      induction h with
      | rel _ _ h => exact hgrel h
      | refl x => exact (Relation.EqvGen.refl (g x) :
          Relation.EqvGen (T93A03ConnectedSumRel c₁.smallMap c₂.smallMap) (g x) (g x))
      | symm _ _ _ ih => exact ih.symm
      | trans x y z _ _ ih₁ ih₂ =>
        exact Relation.EqvGen.trans (g x) (g y) (g z) ih₁ ih₂)
  have hFG (x) : G (F x) = x := by
    induction x using Quotient.inductionOn with
    | _ x =>
      have hh := congrArg
        (Quotient.mk (Relation.EqvGen.setoid
          (T93A03ConnectedSumRel c₁.smallMap c₂.smallMap))) (hfg x)
      simpa [F, G] using hh
  have hGF (x) : F (G x) = x := by
    induction x using Quotient.inductionOn with
    | _ x =>
      have hh := congrArg (Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))) (hgf x)
      simpa [F, G] using hh
  have hfcont : Continuous f := by
    rw [continuous_sum_dom]
    constructor
    · exact continuous_inl.comp (continuous_subtype_val.subtype_mk _)
    · exact continuous_inr.comp (continuous_subtype_val.subtype_mk _)
  have hgcont : Continuous g := by
    rw [continuous_sum_dom]
    constructor
    · exact continuous_inl.comp (continuous_subtype_val.subtype_mk _)
    · exact continuous_inr.comp (continuous_subtype_val.subtype_mk _)
  let E : T93A03ConnectedSum c₁.smallMap c₂.smallMap ≃ ConnectedSum c₁ c₂ :=
    { toFun := F
      invFun := G
      left_inv := hFG
      right_inv := hGF }
  refine ⟨{ toEquiv := E, continuous_toFun := ?_, continuous_invFun := ?_ }⟩
  · rw [continuous_coinduced_dom]
    exact continuous_coinduced_rng.comp hfcont
  · rw [continuous_coinduced_dom]
    exact continuous_coinduced_rng.comp hgcont

/-- **LEAF (P2).** The product `S¹ × S²`, viewed as a three-manifold
through an `E 1 × E 2 ≃ E 3` model change, has an open, path-connected
collared puncture. -/
def puncturedGeometry_aux_modelEquiv :
    (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin 3) :=
  (LinearEquiv.ofFinrankEq _ _ (by simp)).toContinuousLinearEquiv

noncomputable instance puncturedGeometry_aux_productChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2))
      T93A03Summand :=
  prodChartedSpace (EuclideanSpace ℝ (Fin 1)) Circle
    (EuclideanSpace ℝ (Fin 2)) T93A03Sphere2

def puncturedGeometry_aux_chart (x : T93A03Summand) :
    OpenPartialHomeomorph T93A03Summand (EuclideanSpace ℝ (Fin 3)) :=
  (chartAt (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) x).trans
      puncturedGeometry_aux_modelEquiv.toHomeomorph.toOpenPartialHomeomorph

noncomputable instance puncturedGeometry_aux_chartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) T93A03Summand where
  atlas := Set.range puncturedGeometry_aux_chart
  chartAt := puncturedGeometry_aux_chart
  mem_chart_source x := by simp [puncturedGeometry_aux_chart, mem_chart_source]
  chart_mem_atlas x := ⟨x, rfl⟩

theorem puncturedGeometry_aux_isManifold :
    IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (⊤ : ℕ∞) T93A03Summand := by
  let e := puncturedGeometry_aux_modelEquiv
  have hprod : IsManifold
      (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)))
      (⊤ : ℕ∞) T93A03Summand := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (I' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) Circle T93A03Sphere2
  apply isManifold_of_contDiffOn
  intro a b ha hb
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  have h := ((contDiffGroupoid (⊤ : ℕ∞)
      (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)))).compatible
      (chart_mem_atlas _ x) (chart_mem_atlas _ y)).1
  simp only [mfld_simps] at h
  have h' := e.contDiff.comp_contDiffOn
    (h.comp e.symm.contDiff.contDiffOn
      (s := e.symm ⁻¹' ((chartAt _ x).symm.trans (chartAt _ y)).source)
      (by intro z hz; simpa [mfld_simps] using hz))
  simpa [puncturedGeometry_aux_chart, Function.comp_def, mfld_simps] using h'

theorem puncturedGeometry (c : BallCollar 3 T93A03Summand) :
    IsOpen c.radialTwo ∧ PathConnectedSpace c.Punctured := by
  letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (⊤ : ℕ∞) T93A03Summand := puncturedGeometry_aux_isManifold
  letI : PathConnectedSpace T93A03Sphere2 :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (E := T93A03E3)
        (by rw [← Module.finrank_eq_rank']; norm_num)
        (0 : T93A03E3) (r := 1) (by norm_num))
  letI : PathConnectedSpace (ConstructionTargets.SphereHomology.Sphere 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere
        (E := EuclideanSpace ℝ (Fin 2))
        (by rw [← Module.finrank_eq_rank']; norm_num)
        (0 : EuclideanSpace ℝ (Fin 2)) (r := 1) (by norm_num))
  letI : PathConnectedSpace Circle :=
    pathConnectedSpace_iff_univ.mpr (by
      have h : IsPathConnected
          (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
            (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
        ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
          isPathConnected_univ
      simpa using h)
  letI : PathConnectedSpace T93A03Summand :=
    { nonempty := inferInstance
      joined := fun x y ↦ ⟨(PathConnectedSpace.somePath x.1 y.1).prod
        (PathConnectedSpace.somePath x.2 y.2)⟩ }
  have hopen := c.largeInterior_isOpen 3 T93A03Summand
  exact ⟨hopen, c.punctured_pathConnected 3 (by omega) T93A03Summand hopen⟩

/-- **LEAF (P3).** A collared puncture of `S¹ × S²` has the
rank-one free fundamental group, at the boundary basepoint. -/
def puncturedPiOne_aux_modelEquiv :
    (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin 3) :=
  (LinearEquiv.ofFinrankEq _ _ (by simp)).toContinuousLinearEquiv

noncomputable instance puncturedPiOne_aux_productChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2))
      T93A03Summand :=
  prodChartedSpace (EuclideanSpace ℝ (Fin 1)) Circle
    (EuclideanSpace ℝ (Fin 2)) T93A03Sphere2

def puncturedPiOne_aux_chart (x : T93A03Summand) :
    OpenPartialHomeomorph T93A03Summand (EuclideanSpace ℝ (Fin 3)) :=
  (chartAt (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) x).trans
      puncturedPiOne_aux_modelEquiv.toHomeomorph.toOpenPartialHomeomorph

noncomputable instance puncturedPiOne_aux_chartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) T93A03Summand where
  atlas := Set.range puncturedPiOne_aux_chart
  chartAt := puncturedPiOne_aux_chart
  mem_chart_source x := by simp [puncturedPiOne_aux_chart, mem_chart_source]
  chart_mem_atlas x := ⟨x, rfl⟩

theorem puncturedPiOne_aux_isManifold :
    IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (⊤ : ℕ∞) T93A03Summand := by
  let e := puncturedPiOne_aux_modelEquiv
  have hprod : IsManifold
      (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)))
      (⊤ : ℕ∞) T93A03Summand := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (I' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) Circle T93A03Sphere2
  apply isManifold_of_contDiffOn
  intro a b ha hb
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  have h := ((contDiffGroupoid (⊤ : ℕ∞)
      (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)))).compatible
      (chart_mem_atlas _ x) (chart_mem_atlas _ y)).1
  simp only [mfld_simps] at h
  have h' := e.contDiff.comp_contDiffOn
    (h.comp e.symm.contDiff.contDiffOn
      (s := e.symm ⁻¹' ((chartAt _ x).symm.trans (chartAt _ y)).source)
      (by intro z hz; simpa [mfld_simps] using hz))
  simpa [puncturedPiOne_aux_chart, Function.comp_def, mfld_simps] using h'

def puncturedPiOne_aux_prodPiOne {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) : FundamentalGroup (X × Y) (x, y) ≃*
      FundamentalGroup X x × FundamentalGroup Y y where
  toFun p := (Path.Homotopic.projLeft p, Path.Homotopic.projRight p)
  invFun p := Path.Homotopic.prod p.1 p.2
  left_inv := Path.Homotopic.prod_projLeft_projRight
  right_inv p := by ext <;> simp
  map_mul' p q := by
    ext
    · exact map_mul (FundamentalGroup.map ⟨Prod.fst, continuous_fst⟩ (x, y)) p q
    · exact map_mul (FundamentalGroup.map ⟨Prod.snd, continuous_snd⟩ (x, y)) p q

def puncturedPiOne_aux_prodSubsingleton (G H : Type*) [Group G] [Group H]
    [Subsingleton H] : G × H ≃* G where
  toFun := MonoidHom.fst G H
  invFun g := (g, 1)
  left_inv p := by ext <;> simp [Subsingleton.elim p.2 1]
  right_inv g := rfl
  map_mul' _ _ := rfl

theorem puncturedPiOne (c : BallCollar 3 T93A03Summand)
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured) :
    Nonempty (FundamentalGroup c.Punctured (c.boundaryMap sphereBasepoint) ≃*
      FreeGroup (Fin 1)) := by
  letI : ChartedSpace (E 3) T93A03Summand := puncturedPiOne_aux_chartedSpace
  letI : IsManifold (I 3) (⊤ : ℕ∞) T93A03Summand := puncturedPiOne_aux_isManifold
  let v : T93A03Sphere2 := sphereBasepoint
  have hv : ‖(v : T93A03E3)‖ = 1 := by simpa [Metric.mem_sphere] using v.property
  have hv0 : (v : T93A03E3) ≠ 0 := by intro h; rw [h, norm_zero] at hv; norm_num at hv
  haveI : Fact (Module.finrank ℝ T93A03E3 = 3) := ⟨by simp [Module.finrank_fin_fun]⟩
  have hsfin : Module.finrank ℝ (ℝ ∙ (v : T93A03E3))ᗮ = 2 := by
    simpa using Submodule.finrank_orthogonal_span_singleton hv0
  letI : SimplyConnectedSpace T93A03Sphere2 := by
    apply simplyConnectedSpace_sphere_of_pole (v : T93A03E3) hv
    rw [← Module.finrank_eq_rank, hsfin]
    norm_num
  letI : PathConnectedSpace T93A03Sphere2 :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (E := T93A03E3) (by
        rw [← Module.finrank_eq_rank]
        norm_num) 0 (by norm_num))
  letI : PathConnectedSpace Circle :=
    pathConnectedSpace_iff_univ.mpr (by
      have hc : IsPathConnected
          (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
            (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
        ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
          isPathConnected_univ
      simpa using hc)
  letI : PathConnectedSpace T93A03Summand :=
    ⟨⟨((1 : Circle), v)⟩, fun x y ↦
      ⟨Path.prod (PathConnectedSpace.somePath x.1 y.1)
        (PathConnectedSpace.somePath x.2 y.2)⟩⟩
  letI : Subsingleton (FundamentalGroup T93A03Sphere2 v) :=
    BallCollar.punctured_fundamentalGroup_three_aux_subsingleton v
  obtain ⟨e⟩ := c.punctured_fundamentalGroup_three T93A03Summand
    ((1 : Circle), v) sphereBasepoint hopen hpath
  exact ⟨e.trans ((puncturedPiOne_aux_prodPiOne (1 : Circle) v).trans
    ((puncturedPiOne_aux_prodSubsingleton _ _).trans
      (ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt.trans
        ConstructionTargets.PointWedgeVanKampen.multiplicativeIntEquivFreeGroupFinOne)))⟩

/-- **LIBRARY (P4).** Based van Kampen for the standard connected-sum cover.
This is the generic two-open free-product boundary missing from the existing
fundamental-groupoid pseudopushout API. -/
-- BEGIN SEAT AREA
theorem standardCoverPiOneFreeProduct
    (c₁ c₂ : BallCollar 3 T93A03Summand)
    (hcover : HasStandardCover c₁ c₂)
    (e₁ : FundamentalGroup c₁.Punctured (c₁.boundaryMap sphereBasepoint) ≃*
      FreeGroup (Fin 1))
    (e₂ : FundamentalGroup c₂.Punctured (c₂.boundaryMap sphereBasepoint) ≃*
      FreeGroup (Fin 1)) :
    ∃ x : ConnectedSum c₁ c₂,
      Nonempty (FundamentalGroup (ConnectedSum c₁ c₂) x ≃*
        Monoid.Coprod (FreeGroup (Fin 1)) (FreeGroup (Fin 1))) := by
  sorry
-- END SEAT AREA

/-- **LEAF (P5).** The free product of two rank-one free groups is the
rank-two free group. -/
theorem twoRankOneFreeProduct :
    Nonempty (Monoid.Coprod (FreeGroup (Fin 1)) (FreeGroup (Fin 1)) ≃*
      FreeGroup (Fin 2)) := by
  exact ⟨
    (ConstructionTargets.PointWedgeVanKampen.coprodFreeGroupEquivFreeGroupSum
        (Fin 1) (Fin 1)).trans
      (MulEquiv.ofBijective (FreeGroup.map finSumFinEquiv)
        ⟨FreeGroup.map_injective finSumFinEquiv.injective,
          FreeGroup.map_surjective finSumFinEquiv.surjective⟩)⟩

/-- **LEAF (P6).** Transport a based fundamental-group computation across
a homeomorphism, allowing the basepoint to move to its inverse image. -/
def transportPiOne_aux_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) where
  toFun := FundamentalGroup.map ⟨e, e.continuous⟩ x
  invFun := FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
    (e.symm_apply_apply x)
  left_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.map_apply]
      change (FundamentalGroup.mapOfEq _ _)
        (Path.Homotopic.Quotient.mk (p.map e.continuous)) = _
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact e.symm_apply_apply (p t)
  right_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact e.apply_symm_apply (p t)
  map_mul' := map_mul _

theorem transportPiOne {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (y : Y) (G : Type*) [Group G]
    (h : Nonempty (FundamentalGroup Y y ≃* G)) :
    Nonempty (FundamentalGroup X (e.symm y) ≃* G) := by
  obtain ⟨h⟩ := h
  exact ⟨(transportPiOne_aux_homeomorph e.symm y).symm.trans h⟩

end T93A03PiOne

/-- **LIBRARY.** Van Kampen for the concrete collared connected sum, including
the punctured-summand comparisons and the two circle computations. -/
theorem t93A03_collaredConnectedSum_piOne
    (φ₁ φ₂ : T93A03Disk → T93A03Summand)
    (hφ₁ : Topology.IsEmbedding φ₁) (hφ₂ : Topology.IsEmbedding φ₂)
    (hcollar₁ : ∃ ψ₁ : T93A03CollarBall → T93A03Summand,
      Topology.IsEmbedding ψ₁ ∧
        ∀ u, ψ₁ (t93A03DiskInCollarBall u) = φ₁ u)
    (hcollar₂ : ∃ ψ₂ : T93A03CollarBall → T93A03Summand,
      Topology.IsEmbedding ψ₂ ∧
        ∀ u, ψ₂ (t93A03DiskInCollarBall u) = φ₂ u) :
    ∃ x : T93A03ConnectedSum φ₁ φ₂,
      Nonempty (FundamentalGroup (T93A03ConnectedSum φ₁ φ₂) x ≃*
        FreeGroup (Fin 2)) := by
  open ConstructionTargets.CollaredConnectedSumHomology in
    rcases hcollar₁ with ⟨ψ₁, hψ₁, hcompat₁⟩
    rcases hcollar₂ with ⟨ψ₂, hψ₂, hcompat₂⟩
    let c₁ : BallCollar 3 T93A03Summand :=
      { smallMap := φ₁
        largeMap := ψ₁
        smallEmbedding := hφ₁
        largeEmbedding := hψ₁
        compatible := funext hcompat₁ }
    let c₂ : BallCollar 3 T93A03Summand :=
      { smallMap := φ₂
        largeMap := ψ₂
        smallEmbedding := hφ₂
        largeEmbedding := hψ₂
        compatible := funext hcompat₂ }
    obtain ⟨hopen₁, hpath₁⟩ := T93A03PiOne.puncturedGeometry c₁
    obtain ⟨hopen₂, hpath₂⟩ := T93A03PiOne.puncturedGeometry c₂
    letI := hpath₁
    letI := hpath₂
    let hcover := BallCollar.connectedSum_standardCover c₁ c₂ hopen₁ hopen₂
    obtain ⟨e₁⟩ := T93A03PiOne.puncturedPiOne c₁ hopen₁ hpath₁
    obtain ⟨e₂⟩ := T93A03PiOne.puncturedPiOne c₂ hopen₂ hpath₂
    obtain ⟨y, ⟨evk⟩⟩ :=
      T93A03PiOne.standardCoverPiOneFreeProduct c₁ c₂ hcover e₁ e₂
    obtain ⟨ealg⟩ := T93A03PiOne.twoRankOneFreeProduct
    obtain ⟨eq⟩ := T93A03PiOne.quotientHomeomorph φ₁ φ₂ c₁ c₂ rfl rfl
    refine ⟨eq.symm y, ?_⟩
    exact T93A03PiOne.transportPiOne eq y (FreeGroup (Fin 2)) ⟨evk.trans ealg⟩

/-- A fundamental-group equivalence with a nontrivial free group obstructs
simple connectivity. -/
theorem t93A03_not_simplyConnected_of_piOne_equiv
    {X : Type*} [TopologicalSpace X] (x : X)
    (e : FundamentalGroup X x ≃* FreeGroup (Fin 2)) :
    ¬ SimplyConnectedSpace X := by
  intro hsc
  letI : SimplyConnectedSpace X := hsc
  letI : Subsingleton (FundamentalGroup X x) :=
    inferInstanceAs (Subsingleton (Path.Homotopic.Quotient x x))
  have h := congrArg e
    (Subsingleton.elim (e.symm (FreeGroup.of (0 : Fin 2))) (e.symm 1))
  exact FreeGroup.of_ne_one (0 : Fin 2) (by simpa using h)

theorem apm_t93a03
    (φ₁ φ₂ : T93A03Disk → T93A03Summand)
    (hφ₁ : Topology.IsEmbedding φ₁) (hφ₂ : Topology.IsEmbedding φ₂)
    (hcollar₁ : ∃ ψ₁ : T93A03CollarBall → T93A03Summand,
      Topology.IsEmbedding ψ₁ ∧
        ∀ u, ψ₁ (t93A03DiskInCollarBall u) = φ₁ u)
    (hcollar₂ : ∃ ψ₂ : T93A03CollarBall → T93A03Summand,
      Topology.IsEmbedding ψ₂ ∧
        ∀ u, ψ₂ (t93A03DiskInCollarBall u) = φ₂ u) :
    ¬ SimplyConnectedSpace (T93A03ConnectedSum φ₁ φ₂) := by
  obtain ⟨x, ⟨e⟩⟩ :=
    t93A03_collaredConnectedSum_piOne φ₁ φ₂ hφ₁ hφ₂ hcollar₁ hcollar₂
  exact t93A03_not_simplyConnected_of_piOne_equiv x e

#print axioms apm_t93a03
