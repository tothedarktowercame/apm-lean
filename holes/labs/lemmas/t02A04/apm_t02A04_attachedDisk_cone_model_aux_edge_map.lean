import Mathlib
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.LefschetzCompactPolyhedron
import ConstructionTargets.CoefficientH0
import ConstructionTargets.AttachTwoCell
import ConstructionTargets.CP2RationalHomology
import ConstructionTargets.T00A01MayerVietorisAdapters
import ConstructionTargets.SingularHomologyConcrete
import ConstructionTargets.FiniteTriangulation
import ConstructionTargets.RealProjectivePlaneTriangulation
import ConstructionTargets.CompactClosedEquivalenceQuotient

/-! # APM t02A04 — fixed points after a `(1,2)` cell attachment -/

open ConstructionTargets.RationalLefschetz

abbrev apm_t02a04_Disk := Metric.closedBall (0 : ℂ) 1
abbrev apm_t02a04_SolidTorus := apm_t02a04_Disk × Circle

inductive apm_t02a04_Glue :
    Sum apm_t02a04_SolidTorus apm_t02a04_Disk →
      Sum apm_t02a04_SolidTorus apm_t02a04_Disk → Prop
  | boundary (z : Circle) :
      apm_t02a04_Glue
        (.inr ⟨(z : ℂ), by simpa using z.property.le⟩)
        (.inl (⟨(z : ℂ), by simpa using z.property.le⟩, z ^ 2))

def apm_t02a04_X :=
  Quotient (Relation.EqvGen.setoid apm_t02a04_Glue)

noncomputable instance : TopologicalSpace apm_t02a04_X :=
  TopologicalSpace.coinduced
    (fun a => Quotient.mk (Relation.EqvGen.setoid apm_t02a04_Glue) a)
    inferInstance

def apm_t02a04_solidInclusion (x : apm_t02a04_SolidTorus) : apm_t02a04_X :=
  Quotient.mk _ (Sum.inl x)

def apm_t02a04_diskInclusion (x : apm_t02a04_Disk) : apm_t02a04_X :=
  Quotient.mk _ (Sum.inr x)

lemma apm_t02a04_mk_disk_boundary_eq_mk_attachingCurve (z : Circle) :
    apm_t02a04_diskInclusion
        (⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk) =
      apm_t02a04_solidInclusion
        ((⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk), z ^ 2) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (apm_t02a04_Glue.boundary z)

lemma apm_t02a04_continuous_solidInclusion :
    Continuous apm_t02a04_solidInclusion := by
  exact continuous_coinduced_rng.comp continuous_inl

lemma apm_t02a04_continuous_diskInclusion :
    Continuous apm_t02a04_diskInclusion := by
  exact continuous_coinduced_rng.comp continuous_inr

lemma apm_t02a04_gluedDesc_respects
    {Y : Type*} [TopologicalSpace Y]
    (f : C(apm_t02a04_SolidTorus, Y)) (g : C(apm_t02a04_Disk, Y))
    (hfg : ∀ z : Circle,
      g (⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk) =
      f ((⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk), z ^ 2))
    {x y} (hxy : Relation.EqvGen apm_t02a04_Glue x y) :
    Sum.elim f g x = Sum.elim f g y := by
  induction hxy with
  | rel a b hab =>
    cases hab with
    | boundary z => exact hfg z
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

noncomputable def apm_t02a04_gluedDesc
    {Y : Type*} [TopologicalSpace Y]
    (f : C(apm_t02a04_SolidTorus, Y)) (g : C(apm_t02a04_Disk, Y))
    (hfg : ∀ z : Circle,
      g (⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk) =
      f ((⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk), z ^ 2)) :
    C(apm_t02a04_X, Y) := by
  let raw : Sum apm_t02a04_SolidTorus apm_t02a04_Disk → Y := Sum.elim f g
  have hraw : Continuous raw := continuous_sum_dom.2 ⟨f.continuous, g.continuous⟩
  exact ⟨Quotient.lift raw (fun _ _ hxy =>
      apm_t02a04_gluedDesc_respects f g hfg hxy),
    hraw.quotient_lift (fun _ _ hxy =>
      apm_t02a04_gluedDesc_respects f g hfg hxy)⟩

noncomputable abbrev apm_t02A04_HQ (k : ℕ) :=
  Homology apm_t02a04_X k

noncomputable def apm_t02A04_attachingCurve :
    C(Circle, apm_t02a04_SolidTorus) :=
  ⟨fun z ↦
      ((⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk), z ^ 2),
    by fun_prop⟩

def apm_t02A04_overlapToOuter (U V : Set apm_t02a04_X) :
    C((U ∩ V : Set apm_t02a04_X), U) :=
  ⟨fun x ↦ ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩

structure apm_t02A04_CompatibleOpenCover where
  outer : Set apm_t02a04_X
  inner : Set apm_t02a04_X
  open_outer : IsOpen outer
  open_inner : IsOpen inner
  cover : outer ∪ inner = Set.univ
  outerEquiv : ContinuousMap.HomotopyEquiv outer apm_t02a04_SolidTorus
  innerEquiv : ContinuousMap.HomotopyEquiv inner PUnit
  overlapEquiv : ContinuousMap.HomotopyEquiv
    (outer ∩ inner : Set apm_t02a04_X) Circle
  outer_compat :
    (outerEquiv.toFun.comp (apm_t02A04_overlapToOuter outer inner)).Homotopic
      (apm_t02A04_attachingCurve.comp overlapEquiv.toFun)

/-- The radial cover of the attached disk, transported from `AttachTwoCell.Cell`. -/
noncomputable def apm_t02A04_compatibleOpenCover_aux_homeomorph :
    ConstructionTargets.AttachTwoCell.Cell apm_t02A04_attachingCurve ≃ₜ
      apm_t02a04_X := by
  let f : ConstructionTargets.AttachTwoCell.Cell apm_t02A04_attachingCurve →
      apm_t02a04_X :=
    Quotient.lift
      (fun x ↦ Quotient.mk (Relation.EqvGen.setoid apm_t02a04_Glue) x)
      (by
        intro x y hxy
        apply Quotient.sound
        induction hxy with
        | rel a b hab =>
          cases hab with
          | boundary z =>
            exact Relation.EqvGen.symm _ _
              (Relation.EqvGen.rel _ _ (apm_t02a04_Glue.boundary z))
        | refl a => exact Relation.EqvGen.refl a
        | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
        | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂)
  let g : apm_t02a04_X →
      ConstructionTargets.AttachTwoCell.Cell apm_t02A04_attachingCurve :=
    Quotient.lift
      (fun x ↦ ConstructionTargets.AttachTwoCell.cellMk
        apm_t02A04_attachingCurve x)
      (by
        intro x y hxy
        apply Quotient.sound
        induction hxy with
        | rel a b hab =>
          cases hab with
          | boundary z =>
            exact Relation.EqvGen.symm _ _
              (Relation.EqvGen.rel _ _
                (ConstructionTargets.AttachTwoCell.CellRel.boundary z))
        | refl a => exact Relation.EqvGen.refl a
        | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
        | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂)
  have hf : Continuous f := by
    apply Continuous.quotient_lift continuous_coinduced_rng
  have hg : Continuous g := by
    apply Continuous.quotient_lift
    exact ConstructionTargets.AttachTwoCell.continuous_cellMk _
  exact
    { toFun := f
      invFun := g
      left_inv := by
        intro x
        refine Quotient.inductionOn x ?_
        intro a
        rfl
      right_inv := by
        intro x
        refine Quotient.inductionOn x ?_
        intro a
        rfl
      continuous_toFun := hf
      continuous_invFun := hg }

noncomputable def apm_t02A04_compatibleOpenCover_aux_restrict
    (S : Set (ConstructionTargets.AttachTwoCell.Cell apm_t02A04_attachingCurve)) :
    {x : apm_t02a04_X |
      apm_t02A04_compatibleOpenCover_aux_homeomorph.symm x ∈ S} ≃ₜ S where
  toFun x := ⟨apm_t02A04_compatibleOpenCover_aux_homeomorph.symm x.1, x.2⟩
  invFun x := ⟨apm_t02A04_compatibleOpenCover_aux_homeomorph x.1, by simp⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp
  continuous_toFun :=
    Continuous.subtype_mk
      (apm_t02A04_compatibleOpenCover_aux_homeomorph.symm.continuous.comp
        continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk
      (apm_t02A04_compatibleOpenCover_aux_homeomorph.continuous.comp
        continuous_subtype_val) _

theorem apm_t02A04_compatibleOpenCover :
    Nonempty apm_t02A04_CompatibleOpenCover := by
  let γ := apm_t02A04_attachingCurve
  let h := apm_t02A04_compatibleOpenCover_aux_homeomorph
  let U : Set apm_t02a04_X := h.symm ⁻¹' ConstructionTargets.AttachTwoCell.cellOuter γ
  let V : Set apm_t02a04_X := h.symm ⁻¹' ConstructionTargets.AttachTwoCell.cellInner γ
  obtain ⟨⟨hU, hV, hcover⟩, hcontract, ⟨eO, heO⟩, ⟨eU, heU⟩, hloop⟩ :=
    ConstructionTargets.AttachTwoCell.cell_facts γ
  let rU : U ≃ₜ ConstructionTargets.AttachTwoCell.cellOuter γ :=
    apm_t02A04_compatibleOpenCover_aux_restrict _
  let rV : V ≃ₜ ConstructionTargets.AttachTwoCell.cellInner γ :=
    apm_t02A04_compatibleOpenCover_aux_restrict _
  let rO : (U ∩ V : Set apm_t02a04_X) ≃ₜ
      (ConstructionTargets.AttachTwoCell.cellOuter γ ∩
        ConstructionTargets.AttachTwoCell.cellInner γ : Set _) :=
    { toFun := fun x ↦ ⟨h.symm x.1, x.2⟩
      invFun := fun x ↦ ⟨h x.1, ⟨by simpa [U] using x.2.1,
        by simpa [V] using x.2.2⟩⟩
      left_inv := fun x ↦ by apply Subtype.ext; simp
      right_inv := fun x ↦ by apply Subtype.ext; simp
      continuous_toFun := Continuous.subtype_mk
        (h.symm.continuous.comp continuous_subtype_val) _
      continuous_invFun := Continuous.subtype_mk
        (h.continuous.comp continuous_subtype_val) _ }
  letI : ContractibleSpace (ConstructionTargets.AttachTwoCell.cellInner γ) :=
    hcontract
  let eV : ContinuousMap.HomotopyEquiv V PUnit := rV.toHomotopyEquiv.trans
    (Classical.choice (ContractibleSpace.hequiv_unit _))
  refine ⟨⟨U, V, ?_, ?_, ?_,
    rU.toHomotopyEquiv.trans eU, eV,
    rO.toHomotopyEquiv.trans eO, ?_⟩⟩
  · exact hU.preimage h.symm.continuous
  · exact hV.preimage h.symm.continuous
  · apply Set.eq_univ_of_forall
    intro x
    have hx : h.symm x ∈ ConstructionTargets.AttachTwoCell.cellOuter γ ∪
        ConstructionTargets.AttachTwoCell.cellInner γ := by
      rw [hcover]
      trivial
    exact hx
  ·
    let i := apm_t92J05_twoOpen_overlapToLeft
      (ConstructionTargets.AttachTwoCell.cellOuter γ)
      (ConstructionTargets.AttachTwoCell.cellInner γ)
    have hloop' : (i.comp eO.invFun).Homotopic (eU.invFun.comp γ) := by
      rw [heO, heU]
      exact hloop
    have hs : (eU.toFun.comp i).Homotopic (γ.comp eO.toFun) := by
      have hstart : (eU.toFun.comp i).Homotopic
          (eU.toFun.comp ((i.comp eO.invFun).comp eO.toFun)) := by
        simpa only [ContinuousMap.comp_assoc, ContinuousMap.comp_id] using
          ContinuousMap.Homotopic.comp
            (ContinuousMap.Homotopic.refl (eU.toFun.comp i)) eO.left_inv.symm
      have hmiddle :
          (eU.toFun.comp ((i.comp eO.invFun).comp eO.toFun)).Homotopic
            (eU.toFun.comp ((eU.invFun.comp γ).comp eO.toFun)) := by
        simpa only [ContinuousMap.comp_assoc] using
          ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl eU.toFun)
            (ContinuousMap.Homotopic.comp
              hloop'
              (ContinuousMap.Homotopic.refl eO.toFun))
      have hend :
          (eU.toFun.comp ((eU.invFun.comp γ).comp eO.toFun)).Homotopic
            (γ.comp eO.toFun) := by
        simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
          ContinuousMap.Homotopic.comp eU.right_inv
            (ContinuousMap.Homotopic.refl (γ.comp eO.toFun))
      exact hstart.trans (hmiddle.trans hend)
    have ht := ContinuousMap.Homotopic.comp hs
      (ContinuousMap.Homotopic.refl rO.toHomotopyEquiv.toFun)
    change ((eU.toFun.comp i).comp rO.toHomotopyEquiv.toFun).Homotopic
      ((γ.comp eO.toFun).comp rO.toHomotopyEquiv.toFun)
    exact ht

/-- The concrete quotient is path-connected. -/
theorem apm_t02A04_pathConnected : PathConnectedSpace apm_t02a04_X := by
  let f : ConstructionTargets.AttachTwoCell.Cell apm_t02A04_attachingCurve →
      apm_t02a04_X :=
    Quotient.lift
      (fun x ↦ Quotient.mk (Relation.EqvGen.setoid apm_t02a04_Glue) x)
      (by
        intro x y hxy
        apply Quotient.sound
        induction hxy with
        | rel a b hab =>
          cases hab with
          | boundary z =>
            exact Relation.EqvGen.symm _ _
              (Relation.EqvGen.rel _ _ (apm_t02a04_Glue.boundary z))
        | refl a => exact Relation.EqvGen.refl a
        | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
        | trans a b c _ _ ih₁ ih₂ =>
          exact Relation.EqvGen.trans _ _ _ ih₁ ih₂)
  have hf : Continuous f := by
    apply Continuous.quotient_lift continuous_coinduced_rng
  have hsurj : Function.Surjective f := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact ⟨Quotient.mk _ a, rfl⟩
  letI : PathConnectedSpace apm_t02a04_Disk :=
    isPathConnected_iff_pathConnectedSpace.mp
      (Metric.isPathConnected_closedBall (by norm_num : (0 : ℝ) ≤ 1))
  letI : PathConnectedSpace Circle :=
    pathConnectedSpace_iff_univ.mpr (by
      have h : IsPathConnected
          (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
            (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
        ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
          isPathConnected_univ
      simpa using h)
  letI : PathConnectedSpace apm_t02a04_SolidTorus := by
    refine ⟨⟨(Classical.choice (inferInstance : Nonempty apm_t02a04_Disk),
      Classical.choice (inferInstance : Nonempty Circle))⟩, ?_⟩
    intro x y
    exact ⟨(PathConnectedSpace.somePath x.1 y.1).prod
      (PathConnectedSpace.somePath x.2 y.2)⟩
  letI : PathConnectedSpace
      (ConstructionTargets.AttachTwoCell.Cell apm_t02A04_attachingCurve) :=
    ConstructionTargets.AttachTwoCell.cell_pc apm_t02A04_attachingCurve
  exact hsurj.pathConnectedSpace hf

/-- In rational `H₁`, the attaching loop has invertible degree two. -/
noncomputable def apm_t02A04_attachingCurve_H1_isIso_aux_square : C(Circle, Circle) :=
  ⟨fun z ↦ z ^ 2, by fun_prop⟩

open CategoryTheory

noncomputable def apm_t02A04_attachingCurve_H1_isIso_aux_fiberEquiv
    (b : Circle) :
    {z : Circle // z ^ 2 = b} ≃ Fin 2 := by
  classical
  let c : Circle := Classical.choose
    ((Circle.isQuotientCoveringMap_npow 2).surjective b)
  have hc : c ^ 2 = b := Classical.choose_spec
    ((Circle.isQuotientCoveringMap_npow 2).surjective b)
  let f : {z : Circle // z ^ 2 = b} → Fin 2 := fun z ↦
    if z.1 = c then 0 else 1
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    by_cases hx : x.1 = c
    · have hy : y.1 = c := by
        by_contra hy
        simp [f, hx, hy] at hxy
      exact Subtype.ext (hx.trans hy.symm)
    · have hy : y.1 ≠ c := by
        intro hy
        simp [f, hx, hy] at hxy
      apply Subtype.ext
      have hxc : (x.1 : ℂ) = -(c : ℂ) := by
        have hs : (x.1 : ℂ) ^ 2 = (c : ℂ) ^ 2 := by
          exact congrArg (fun z : Circle ↦ ((z : Circle) : ℂ)) (x.2.trans hc.symm)
        rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h | h
        · exact (hx (Subtype.ext h)).elim
        · exact h
      have hyc : (y.1 : ℂ) = -(c : ℂ) := by
        have hs : (y.1 : ℂ) ^ 2 = (c : ℂ) ^ 2 := by
          exact congrArg (fun z : Circle ↦ ((z : Circle) : ℂ)) (y.2.trans hc.symm)
        rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h | h
        · exact (hy (Subtype.ext h)).elim
        · exact h
      exact Subtype.ext (hxc.trans hyc.symm)
  · intro i
    fin_cases i
    · exact ⟨⟨c, hc⟩, by simp [f]⟩
    · let nc : Circle := ⟨-(c : ℂ), by
        change -(c : ℂ) ∈ Metric.sphere (0 : ℂ) 1
        rw [mem_sphere_zero_iff_norm, norm_neg]
        exact mem_sphere_zero_iff_norm.mp c.property⟩
      have hnc : nc ^ 2 = b := by
        apply Subtype.ext
        simpa [nc] using congrArg (fun z : Circle ↦ (z : ℂ)) hc
      refine ⟨⟨nc, hnc⟩, ?_⟩
      simp only [f]
      rw [if_neg]
      · rfl
      · intro h
        have hz : (c : ℂ) = 0 := by
          have := congrArg (fun z : Circle ↦ (z : ℂ)) h
          exact CharZero.neg_eq_self_iff.mp (by simpa [nc] using this)
        have hc0 : (c : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := c.property
        rw [mem_sphere_zero_iff_norm, hz, norm_zero] at hc0
        norm_num at hc0

theorem apm_t02A04_attachingCurve_H1_isIso_aux_square_cover :
    ConstructionTargets.CoveringDegree.IsKSheetedCover
      (fun z : Circle ↦ z ^ 2) 2 where
  isCoveringMap := (Circle.isQuotientCoveringMap_npow 2).isCoveringMap
  finite_fiber b :=
    Finite.of_injective (apm_t02A04_attachingCurve_H1_isIso_aux_fiberEquiv b)
      (apm_t02A04_attachingCurve_H1_isIso_aux_fiberEquiv b).injective
  card_fiber b := by
    rw [Nat.card_congr (apm_t02A04_attachingCurve_H1_isIso_aux_fiberEquiv b)]
    simp

noncomputable def apm_t02A04_attachingCurve_H1_isIso_aux_circleIso :
    Homology Circle 1 ≅ ModuleCat.of ℚ ℚ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) 1).obj
      (ModuleCat.of ℚ ℚ)).mapIso
        (TopCat.isoOfHomeo
          ConstructionTargets.CircleHomology.circleHomeomorphSphereOne) ≪≫
    ConstructionTargets.CoefficientFirstReflection.topIso ℚ 0

theorem apm_t02A04_attachingCurve_H1_isIso_aux_square_isIso :
    CategoryTheory.IsIso
      (induced apm_t02A04_attachingCurve_H1_isIso_aux_square 1) := by
  let A := Homology Circle 1
  let f : A ⟶ A := induced apm_t02A04_attachingCurve_H1_isIso_aux_square 1
  let tr : A ⟶ A := HomologicalComplex.homologyMap
    (ConstructionTargets.CoefficientCoveringTransfer.transfer ℚ
      (fun z : Circle ↦ z ^ 2)
      apm_t02A04_attachingCurve_H1_isIso_aux_square_cover) 1
  have htf : tr ≫ f = 2 • 𝟙 A := by
    exact ConstructionTargets.CoefficientCoveringTransfer.rational_homology_projection
      (fun z : Circle ↦ z ^ 2)
      apm_t02A04_attachingCurve_H1_isIso_aux_square_cover 1
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨(2 : ℚ)⁻¹ • tr y, ?_⟩
    have heq := congrArg (fun g ↦ g y) htf
    change f (tr y) = 2 • y at heq
    rw [map_smul, heq]
    module
  letI : FiniteDimensional ℚ A :=
    Module.Finite.equiv
      apm_t02A04_attachingCurve_H1_isIso_aux_circleIso.toLinearEquiv.symm
  have hinj : Function.Injective f :=
    LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl |>.2 hsurj
  exact (ConcreteCategory.isIso_iff_bijective f).2 ⟨hinj, hsurj⟩

noncomputable def apm_t02A04_attachingCurve_H1_isIso_aux_projection :
    C(apm_t02a04_SolidTorus, Circle) :=
  ⟨Prod.snd, continuous_snd⟩

noncomputable def apm_t02A04_attachingCurve_H1_isIso_aux_core :
    C(Circle, apm_t02a04_SolidTorus) :=
  ⟨fun z ↦ (⟨0, by simp [apm_t02a04_Disk]⟩, z),
    continuous_const.prodMk continuous_id⟩

noncomputable def apm_t02A04_attachingCurve_H1_isIso_aux_contraction :
    ContinuousMap.Homotopy (ContinuousMap.id apm_t02a04_SolidTorus)
      (apm_t02A04_attachingCurve_H1_isIso_aux_core.comp
        apm_t02A04_attachingCurve_H1_isIso_aux_projection) where
  toFun := fun p ↦
      (⟨((1 - (p.1 : ℝ)) : ℂ) * (p.2.1 : ℂ), by
          rw [Metric.mem_closedBall, dist_zero_right, norm_mul]
          have hx : ‖(p.2.1 : ℂ)‖ ≤ 1 := by
            simpa only [dist_zero_right] using
              (Metric.mem_closedBall.mp p.2.1.2)
          have ht : 0 ≤ 1 - (p.1 : ℝ) := sub_nonneg.mpr p.1.2.2
          have ht' : 1 - (p.1 : ℝ) ≤ 1 := by linarith [p.1.2.1]
          have hn : ‖(1 : ℂ) - ((p.1 : ℝ) : ℂ)‖ = 1 - (p.1 : ℝ) := by
            calc
              _ = ‖(1 - (p.1 : ℝ) : ℝ)‖ := by
                rw [← Complex.norm_real]
                congr 1
                norm_num
              _ = _ := by rw [Real.norm_eq_abs, abs_of_nonneg ht]
          rw [hn]
          nlinarith⟩,
        p.2.2)
  continuous_toFun := by fun_prop
  map_zero_left x := by ext <;> simp
  map_one_left x := by ext <;> simp [apm_t02A04_attachingCurve_H1_isIso_aux_core,
    apm_t02A04_attachingCurve_H1_isIso_aux_projection]

theorem apm_t02A04_attachingCurve_H1_isIso_aux_projection_isIso :
    IsIso (induced apm_t02A04_attachingCurve_H1_isIso_aux_projection 1) := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) 1).obj
    (ModuleCat.of ℚ ℚ)
  let p := apm_t02A04_attachingCurve_H1_isIso_aux_projection
  let i := apm_t02A04_attachingCurve_H1_isIso_aux_core
  let fp := induced p 1
  let fi := induced i 1
  have hpi : fp ≫ fi = 𝟙 _ := by
    change F.map (TopCat.ofHom p) ≫ F.map (TopCat.ofHom i) = _
    rw [← F.map_comp]
    change F.map (TopCat.ofHom (i.comp p)) = _
    have hh := ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℚ) (ModuleCat.of ℚ ℚ)
      ⟨apm_t02A04_attachingCurve_H1_isIso_aux_contraction⟩ 1
    rw [← hh]
    exact F.map_id _
  have hip : fi ≫ fp = 𝟙 _ := by
    change F.map (TopCat.ofHom i) ≫ F.map (TopCat.ofHom p) = _
    rw [← F.map_comp]
    have heq : p.comp i = ContinuousMap.id Circle := by ext; rfl
    change F.map (TopCat.ofHom (p.comp i)) = _
    rw [heq]
    exact F.map_id _
  exact ⟨⟨fi, hpi, hip⟩⟩

theorem apm_t02A04_attachingCurve_H1_isIso :
    CategoryTheory.IsIso (induced apm_t02A04_attachingCurve 1) := by
  let a := induced apm_t02A04_attachingCurve 1
  let p := induced apm_t02A04_attachingCurve_H1_isIso_aux_projection 1
  have hap : a ≫ p =
      induced apm_t02A04_attachingCurve_H1_isIso_aux_square 1 := by
    change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) 1).obj
      (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom apm_t02A04_attachingCurve) ≫
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) 1).obj
      (ModuleCat.of ℚ ℚ)).map
        (TopCat.ofHom apm_t02A04_attachingCurve_H1_isIso_aux_projection) = _
    rw [← Functor.map_comp]
    rfl
  letI : IsIso p := apm_t02A04_attachingCurve_H1_isIso_aux_projection_isIso
  letI : IsIso (induced apm_t02A04_attachingCurve_H1_isIso_aux_square 1) :=
    apm_t02A04_attachingCurve_H1_isIso_aux_square_isIso
  letI : IsIso (a ≫ p) := by rw [hap]; infer_instance
  exact IsIso.of_isIso_comp_right a p

/-- The degree-one Mayer--Vietoris calculation for a compatible cover. -/
noncomputable def apm_t02A04_H1_zero_of_cover_aux_iso
    {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    (e : ContinuousMap.HomotopyEquiv S T) (k : ℕ) :
    Homology S k ≅ Homology T k where
  hom := induced e.toFun k
  inv := induced e.invFun k
  hom_inv_id := by
    dsimp [induced]
    rw [← CategoryTheory.Functor.map_comp]
    change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom (e.invFun.comp e.toFun)) = _
    rw [ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℚ) (ModuleCat.of ℚ ℚ) e.left_inv k]
    exact ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).map_id (TopCat.of S)
  inv_hom_id := by
    dsimp [induced]
    rw [← CategoryTheory.Functor.map_comp]
    change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom (e.toFun.comp e.invFun)) = _
    rw [ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℚ) (ModuleCat.of ℚ ℚ) e.right_inv k]
    exact ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).map_id (TopCat.of T)

open CategoryTheory

lemma apm_t02A04_H1_zero_of_cover_aux_pathConnected
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (e : ContinuousMap.HomotopyEquiv S T) [PathConnectedSpace T] :
    PathConnectedSpace S := by
  rcases e.left_inv with ⟨K⟩
  refine ⟨⟨e.invFun (Classical.choice (inferInstance : Nonempty T))⟩, ?_⟩
  intro x y
  exact ⟨(K.evalAt x).symm.trans
    (((PathConnectedSpace.somePath (e x) (e y)).map e.invFun.continuous).trans
      (K.evalAt y))⟩

lemma apm_t02A04_H1_zero_of_cover_aux_mv0_injective
    (C : apm_t02A04_CompatibleOpenCover) :
    Function.Injective (RP3Homology.mvI C.outer C.inner 0).hom := by
  letI : PathConnectedSpace Circle :=
    pathConnectedSpace_iff_univ.mpr (by
      have h : IsPathConnected
          (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
            (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
        ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
          isPathConnected_univ
      simpa using h)
  letI : PathConnectedSpace (C.outer ∩ C.inner : Set apm_t02a04_X) :=
    apm_t02A04_H1_zero_of_cover_aux_pathConnected C.overlapEquiv
  letI : PathConnectedSpace C.outer := by
    letI : PathConnectedSpace apm_t02a04_Disk :=
      isPathConnected_iff_pathConnectedSpace.mp
        (Metric.isPathConnected_closedBall (by norm_num : (0 : ℝ) ≤ 1))
    letI : PathConnectedSpace apm_t02a04_SolidTorus := by
      refine ⟨⟨(Classical.choice (inferInstance : Nonempty apm_t02a04_Disk),
        Classical.choice (inferInstance : Nonempty Circle))⟩, ?_⟩
      intro x y
      exact ⟨(PathConnectedSpace.somePath x.1 y.1).prod
        (PathConnectedSpace.somePath x.2 y.2)⟩
    exact apm_t02A04_H1_zero_of_cover_aux_pathConnected C.outerEquiv
  let f : C((C.outer ∩ C.inner : Set apm_t02a04_X), C.outer) :=
    apm_t02A04_overlapToOuter C.outer C.inner
  let p := Classical.choice
    (inferInstance : Nonempty (C.outer ∩ C.inner : Set apm_t02a04_X))
  let q := Classical.choice (inferInstance : Nonempty C.outer)
  let e := ConstructionTargets.CoefficientH0.h0Iso ℚ p ≪≫
    (ConstructionTargets.CoefficientH0.h0Iso ℚ q).symm
  have hmap : e.hom = RP3Homology.mvIncl Set.inter_subset_left 0 := by
    apply (CategoryTheory.cancel_mono
      (ConstructionTargets.CoefficientH0.h0Iso ℚ q).hom).mp
    change (ConstructionTargets.CoefficientH0.h0Augmentation ℚ ≫
        ConstructionTargets.CoefficientH0.singularVertexH0Class ℚ q) ≫
        ConstructionTargets.CoefficientH0.h0Augmentation ℚ = _
    rw [CategoryTheory.Category.assoc,
      ConstructionTargets.CoefficientH0.singularVertexH0Class_comp_h0Augmentation,
      CategoryTheory.Category.comp_id]
    exact (ConstructionTargets.CoefficientH0.h0Augmentation_naturality ℚ f).symm
  have hincl : Function.Injective
      (RP3Homology.mvIncl
        (Set.inter_subset_left : C.outer ∩ C.inner ⊆ C.outer) 0).hom := by
    rw [← hmap]
    exact (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  intro a b hab
  apply hincl
  have h := congrArg
    (fun z => (CategoryTheory.Limits.biprod.fst : Homology C.outer 0 ⊞
      Homology C.inner 0 ⟶ Homology C.outer 0).hom z) hab
  simp only [RP3Homology.mvI] at h
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    CategoryTheory.Limits.biprod.lift_fst] at h
  exact h

theorem apm_t02A04_H1_zero_of_cover
    (C : apm_t02A04_CompatibleOpenCover)
    (hdegree : CategoryTheory.IsIso (induced apm_t02A04_attachingCurve 1)) :
    CategoryTheory.Limits.IsZero (apm_t02A04_HQ 1) := by
  let eI := apm_t02A04_H1_zero_of_cover_aux_iso C.overlapEquiv 1
  let eO := apm_t02A04_H1_zero_of_cover_aux_iso C.outerEquiv 1
  let eN := apm_t02A04_H1_zero_of_cover_aux_iso C.innerEquiv 1
  have hinner : CategoryTheory.Limits.IsZero (Homology C.inner 1) := by
    letI : ContractibleSpace PUnit := inferInstance
    exact (ConstructionTargets.CoefficientContractiblePair.higher_zero ℚ PUnit 1
      (by decide)).of_iso eN
  have hsquare :
      (C.outerEquiv.toFun.comp (apm_t02A04_overlapToOuter C.outer C.inner)).Homotopic
        (apm_t02A04_attachingCurve.comp C.overlapEquiv.toFun) := C.outer_compat
  have hfirst : CategoryTheory.IsIso
      (RP3Homology.mvIncl
        (Set.inter_subset_left : (C.outer ∩ C.inner) ⊆ C.outer) 1) := by
    have heq : (RP3Homology.mvIncl
          (Set.inter_subset_left : (C.outer ∩ C.inner) ⊆ C.outer) 1) ≫ eO.hom =
        eI.hom ≫ induced apm_t02A04_attachingCurve 1 := by
      change induced (apm_t02A04_overlapToOuter C.outer C.inner) 1 ≫
          induced C.outerEquiv.toFun 1 =
        induced C.overlapEquiv.toFun 1 ≫ induced apm_t02A04_attachingCurve 1
      dsimp [induced]
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      exact ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
        (ModuleCat ℚ) (ModuleCat.of ℚ ℚ) hsquare 1
    haveI : CategoryTheory.IsIso
        (eI.hom ≫ induced apm_t02A04_attachingCurve 1) := inferInstance
    haveI : CategoryTheory.IsIso
        ((RP3Homology.mvIncl
          (Set.inter_subset_left : (C.outer ∩ C.inner) ⊆ C.outer) 1) ≫ eO.hom) :=
      heq.symm ▸ inferInstance
    exact CategoryTheory.IsIso.of_isIso_comp_right
      (RP3Homology.mvIncl
        (Set.inter_subset_left : (C.outer ∩ C.inner) ⊆ C.outer) 1) eO.hom
  obtain ⟨δ, hexI, hexJ, hexδ⟩ :=
    RP3Homology.rationalMayerVietoris C.outer C.inner
      C.open_outer C.open_inner C.cover
  have hmv0 := apm_t02A04_H1_zero_of_cover_aux_mv0_injective C
  have hd_zero : (δ 0).hom = 0 := by
    apply LinearMap.range_eq_bot.mp
    rw [hexδ 0, LinearMap.ker_eq_bot.mpr hmv0]
  have hJ_surj : Function.Surjective (RP3Homology.mvJ C.outer C.inner 1).hom := by
    rw [← LinearMap.range_eq_top, hexJ 0, hd_zero, LinearMap.ker_zero]
  have hI_surj : Function.Surjective (RP3Homology.mvI C.outer C.inner 1).hom := by
    intro x
    let xo := (CategoryTheory.Limits.biprod.fst :
      Homology C.outer 1 ⊞ Homology C.inner 1 ⟶ Homology C.outer 1).hom x
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
      (RP3Homology.mvIncl
        (Set.inter_subset_left : C.outer ∩ C.inner ⊆ C.outer) 1)).mp inferInstance xo
    refine ⟨z, ?_⟩
    have hproj : (Limits.biprod.fst : Homology C.outer 1 ⊞ Homology C.inner 1 ⟶ _) ≫
        Limits.biprod.inl = 𝟙 _ := by
      rw [← Limits.biprod.total]
      rw [hinner.eq_of_tgt (Limits.biprod.snd : _ ⟶ Homology C.inner 1) 0]
      simp
    have hx : (Limits.biprod.inl : Homology C.outer 1 ⟶
        Homology C.outer 1 ⊞ Homology C.inner 1).hom xo = x := by
      have hh := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hproj) x
      simpa [ModuleCat.hom_comp, xo] using hh
    rw [← hx]
    have hsnd : RP3Homology.mvIncl
        (Set.inter_subset_right : (C.outer ∩ C.inner) ⊆ C.inner) 1 = 0 :=
      hinner.eq_of_tgt _ _
    rw [RP3Homology.mvI, hsnd]
    have hlift : Limits.biprod.lift
        (RP3Homology.mvIncl
          (Set.inter_subset_left : (C.outer ∩ C.inner) ⊆ C.outer) 1) 0 =
        RP3Homology.mvIncl
          (Set.inter_subset_left : (C.outer ∩ C.inner) ⊆ C.outer) 1 ≫
          (Limits.biprod.inl : Homology C.outer 1 ⟶
            Homology C.outer 1 ⊞ Homology C.inner 1) := by
      apply Limits.biprod.hom_ext <;> simp
    rw [hlift, ModuleCat.comp_apply, hz]
  have hJ_zero : (RP3Homology.mvJ C.outer C.inner 1).hom = 0 := by
    apply LinearMap.ker_eq_top.mp
    rw [← hexI 1, LinearMap.range_eq_top.mpr hI_surj]
  letI : Subsingleton (apm_t02A04_HQ 1) := ⟨by
    intro x y
    obtain ⟨a, ha⟩ := hJ_surj x
    obtain ⟨b, hb⟩ := hJ_surj y
    have hza := DFunLike.congr_fun hJ_zero a
    have hzb := DFunLike.congr_fun hJ_zero b
    rw [← ha, ← hb]
    simpa using hza.trans hzb.symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The degree-two Mayer--Vietoris calculation: injectivity kills the kernel. -/
noncomputable def apm_t02A04_H2_zero_of_cover_aux_iso
    {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    (e : ContinuousMap.HomotopyEquiv S T) (k : ℕ) :
    Homology S k ≅ Homology T k where
  hom := induced e.toFun k
  inv := induced e.invFun k
  hom_inv_id := by
    dsimp [induced]
    rw [← CategoryTheory.Functor.map_comp]
    change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom (e.invFun.comp e.toFun)) = _
    rw [ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℚ) (ModuleCat.of ℚ ℚ) e.left_inv k]
    exact ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).map_id (TopCat.of S)
  inv_hom_id := by
    dsimp [induced]
    rw [← CategoryTheory.Functor.map_comp]
    change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom (e.toFun.comp e.invFun)) = _
    rw [ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℚ) (ModuleCat.of ℚ ℚ) e.right_inv k]
    exact ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).map_id (TopCat.of T)

open CategoryTheory

noncomputable def apm_t02A04_H2_zero_of_cover_aux_solidEquiv :
    ContinuousMap.HomotopyEquiv apm_t02a04_SolidTorus Circle where
  toFun := ⟨Prod.snd, continuous_snd⟩
  invFun := ⟨fun z ↦ (⟨0, by simp [apm_t02a04_Disk]⟩, z),
    continuous_const.prodMk continuous_id⟩
  left_inv := ⟨{
    toFun := fun p ↦
      (⟨((p.1 : ℝ) : ℂ) * p.2.1.1, by
        rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg p.1.2.1]
        have hx : ‖p.2.1.1‖ ≤ 1 := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using p.2.1.2
        exact mul_le_one₀ p.1.2.2 (norm_nonneg _) hx⟩, p.2.2)
    continuous_toFun := by fun_prop
    map_zero_left := by intro x; ext <;> simp
    map_one_left := by intro x; ext <;> simp }⟩
  right_inv := by rfl

lemma apm_t02A04_H2_zero_of_cover_aux_circle :
    CategoryTheory.Limits.IsZero (Homology Circle 2) := by
  let e : Homology Circle 2 ≅
      ConstructionTargets.CoefficientContractiblePair.H ℚ 1
        (TopCat.of (ConstructionTargets.SphereHomology.Sphere 0)) :=
    ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℚ
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.toHomotopyEquiv 2 ≪≫
    (by simpa using
      ConstructionTargets.CoefficientSphereShift.sphereShift ℚ 1 1 (by omega))
  exact (ConstructionTargets.SphereZeroCoefficients.positive_vanishing ℚ 1 (by omega)).of_iso e

theorem apm_t02A04_H2_zero_of_cover
    (C : apm_t02A04_CompatibleOpenCover)
    (hdegree : CategoryTheory.IsIso (induced apm_t02A04_attachingCurve 1)) :
    CategoryTheory.Limits.IsZero (apm_t02A04_HQ 2) := by
  let eI := apm_t02A04_H2_zero_of_cover_aux_iso C.overlapEquiv 1
  let eO := apm_t02A04_H2_zero_of_cover_aux_iso C.outerEquiv 1
  have hfirst : CategoryTheory.IsIso
      (RP3Homology.mvIncl
        (Set.inter_subset_left : (C.outer ∩ C.inner) ⊆ C.outer) 1) := by
    have heq : (RP3Homology.mvIncl
          (Set.inter_subset_left : (C.outer ∩ C.inner) ⊆ C.outer) 1) ≫ eO.hom =
        eI.hom ≫ induced apm_t02A04_attachingCurve 1 := by
      change induced (apm_t02A04_overlapToOuter C.outer C.inner) 1 ≫
          induced C.outerEquiv.toFun 1 =
        induced C.overlapEquiv.toFun 1 ≫ induced apm_t02A04_attachingCurve 1
      dsimp [induced]
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      exact ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
        (ModuleCat ℚ) (ModuleCat.of ℚ ℚ) C.outer_compat 1
    haveI : CategoryTheory.IsIso
        (eI.hom ≫ induced apm_t02A04_attachingCurve 1) := inferInstance
    haveI : CategoryTheory.IsIso
        ((RP3Homology.mvIncl
          (Set.inter_subset_left : (C.outer ∩ C.inner) ⊆ C.outer) 1) ≫ eO.hom) :=
      heq.symm ▸ inferInstance
    exact CategoryTheory.IsIso.of_isIso_comp_right _ eO.hom
  have hmvI : Function.Injective (RP3Homology.mvI C.outer C.inner 1).hom := by
    intro x y hxy
    apply (ModuleCat.mono_iff_injective
      (RP3Homology.mvIncl
        (Set.inter_subset_left : (C.outer ∩ C.inner) ⊆ C.outer) 1)).mp inferInstance
    have hp := congrArg
      (fun q => (CategoryTheory.Limits.biprod.fst :
        Homology C.outer 1 ⊞ Homology C.inner 1 ⟶ Homology C.outer 1).hom q) hxy
    change ((RP3Homology.mvI C.outer C.inner 1 ≫
      Limits.biprod.fst).hom x) =
      ((RP3Homology.mvI C.outer C.inner 1 ≫ Limits.biprod.fst).hom y) at hp
    have hm : RP3Homology.mvI C.outer C.inner 1 ≫ Limits.biprod.fst =
        RP3Homology.mvIncl Set.inter_subset_left 1 := by
      simp [RP3Homology.mvI]
    rw [hm] at hp
    exact hp
  have houter : CategoryTheory.Limits.IsZero (Homology C.outer 2) :=
    apm_t02A04_H2_zero_of_cover_aux_circle.of_iso
      (apm_t02A04_H2_zero_of_cover_aux_iso
        (C.outerEquiv.trans apm_t02A04_H2_zero_of_cover_aux_solidEquiv) 2)
  have hinner : CategoryTheory.Limits.IsZero (Homology C.inner 2) := by
    letI : ContractibleSpace PUnit := inferInstance
    exact (ConstructionTargets.CoefficientContractiblePair.higher_zero ℚ PUnit 2
      (by decide)).of_iso (apm_t02A04_H2_zero_of_cover_aux_iso C.innerEquiv 2)
  obtain ⟨δ, -, hexJ, hexδ⟩ := RP3Homology.rationalMayerVietoris
    C.outer C.inner C.open_outer C.open_inner C.cover
  have hpieces := RP3Homology.cp2_homology_of_mv_aux_biprod_zero houter hinner
  have hd_inj : Function.Injective (δ 1).hom := by
    rw [← LinearMap.ker_eq_bot, ← hexJ 1]
    apply LinearMap.range_eq_bot.mpr
    exact congrArg ModuleCat.Hom.hom (hpieces.eq_of_src _ 0)
  have hd_zero : (δ 1).hom = 0 := by
    apply LinearMap.range_eq_bot.mp
    rw [hexδ 1, LinearMap.ker_eq_bot.mpr hmvI]
  letI : Subsingleton (apm_t02A04_HQ 2) := ⟨by
    intro x y
    apply hd_inj
    rw [hd_zero]
    rfl⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Mayer--Vietoris above the dimensions of the circle and solid torus. -/
lemma apm_t02A04_Hhigh_zero_of_cover_aux_circle (n : ℕ) (hn : 2 ≤ n) :
    CategoryTheory.Limits.IsZero (Homology Circle n) := by
  let e : Homology Circle n ≅
      ConstructionTargets.CoefficientContractiblePair.H ℚ (n - 1)
        (TopCat.of (ConstructionTargets.SphereHomology.Sphere 0)) :=
    ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℚ
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.toHomotopyEquiv n ≪≫
    (by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
        ConstructionTargets.CoefficientSphereShift.sphereShift ℚ 1 (n - 1) (by omega))
  exact (ConstructionTargets.SphereZeroCoefficients.positive_vanishing ℚ
    (n - 1) (by omega)).of_iso e

noncomputable def apm_t02A04_Hhigh_zero_of_cover_aux_solidEquiv :
    ContinuousMap.HomotopyEquiv apm_t02a04_SolidTorus Circle where
  toFun := ⟨Prod.snd, continuous_snd⟩
  invFun := ⟨fun z ↦ (⟨0, by simp [apm_t02a04_Disk]⟩, z),
    continuous_const.prodMk continuous_id⟩
  left_inv := ⟨{
    toFun := fun p ↦
      (⟨((p.1 : ℝ) : ℂ) * p.2.1.1, by
        rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg p.1.2.1]
        have hx : ‖p.2.1.1‖ ≤ 1 := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using p.2.1.2
        exact mul_le_one₀ p.1.2.2 (norm_nonneg _) hx⟩, p.2.2)
    continuous_toFun := by fun_prop
    map_zero_left := by intro x; ext <;> simp
    map_one_left := by intro x; ext <;> simp }⟩
  right_inv := by rfl

lemma apm_t02A04_Hhigh_zero_of_cover_aux_outer
    (C : apm_t02A04_CompatibleOpenCover) (n : ℕ) (hn : 2 ≤ n) :
    CategoryTheory.Limits.IsZero (Homology C.outer n) := by
  exact (apm_t02A04_Hhigh_zero_of_cover_aux_circle n hn).of_iso
    (ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℚ
      (C.outerEquiv.trans apm_t02A04_Hhigh_zero_of_cover_aux_solidEquiv) n)

lemma apm_t02A04_Hhigh_zero_of_cover_aux_inner
    (C : apm_t02A04_CompatibleOpenCover) (n : ℕ) (hn : 0 < n) :
    CategoryTheory.Limits.IsZero (Homology C.inner n) := by
  have hz : CategoryTheory.Limits.IsZero (Homology PUnit n) := by
    letI : ContractibleSpace PUnit := inferInstance
    exact ConstructionTargets.CoefficientContractiblePair.higher_zero ℚ PUnit n
      (Nat.ne_of_gt hn)
  exact hz.of_iso
    (ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℚ
      C.innerEquiv n)

lemma apm_t02A04_Hhigh_zero_of_cover_aux_overlap
    (C : apm_t02A04_CompatibleOpenCover) (n : ℕ) (hn : 2 ≤ n) :
    CategoryTheory.Limits.IsZero (Homology (C.outer ∩ C.inner : Set apm_t02a04_X) n) := by
  exact (apm_t02A04_Hhigh_zero_of_cover_aux_circle n hn).of_iso
    (ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℚ
      C.overlapEquiv n)

theorem apm_t02A04_Hhigh_zero_of_cover
    (C : apm_t02A04_CompatibleOpenCover) (k : ℕ) (hk : 3 ≤ k) :
    CategoryTheory.Limits.IsZero (apm_t02A04_HQ k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨δ, -, hex, -⟩ := RP3Homology.rationalMayerVietoris
    C.outer C.inner C.open_outer C.open_inner C.cover
  apply RP3Homology.cp2_homology_of_mv_aux_exact_zero
    (RP3Homology.mvJ C.outer C.inner (m + 1)) (δ m)
  · exact RP3Homology.cp2_homology_of_mv_aux_biprod_zero
      (apm_t02A04_Hhigh_zero_of_cover_aux_outer C (m + 1) (by omega))
      (apm_t02A04_Hhigh_zero_of_cover_aux_inner C (m + 1) (by omega))
  · exact apm_t02A04_Hhigh_zero_of_cover_aux_overlap C m (by omega)
  · exact hex m

/-- Path-connectedness identifies rational degree-zero homology with `ℚ`. -/
theorem apm_t02A04_H0_of_pathConnected
    (hpc : PathConnectedSpace apm_t02a04_X) :
    Nonempty (apm_t02A04_HQ 0 ≅ ModuleCat.of ℚ ℚ) := by
  letI : PathConnectedSpace apm_t02a04_X := hpc
  exact ⟨ConstructionTargets.CoefficientH0.h0Iso ℚ
    (apm_t02a04_diskInclusion ⟨0, by simp [apm_t02a04_Disk]⟩)⟩

/-- **LIBRARY.** The concrete degree-two attachment is rationally acyclic. -/
theorem apm_t02A04_rational_homology :
    Nonempty (apm_t02A04_HQ 0 ≅ ModuleCat.of ℚ ℚ) ∧
      ∀ k : ℕ, 0 < k → CategoryTheory.Limits.IsZero (apm_t02A04_HQ k) := by
  let C := Classical.choice apm_t02A04_compatibleOpenCover
  have hdegree := apm_t02A04_attachingCurve_H1_isIso
  refine ⟨apm_t02A04_H0_of_pathConnected apm_t02A04_pathConnected, ?_⟩
  intro k hk
  rcases k with _ | _ | _ | k
  · omega
  · exact apm_t02A04_H1_zero_of_cover C hdegree
  · exact apm_t02A04_H2_zero_of_cover C hdegree
  · exact apm_t02A04_Hhigh_zero_of_cover C (k + 3) (by omega)

lemma apm_t02A04_lefschetz_number_aux_trace_H0_aux_induced_eq_id
    (e : apm_t02A04_HQ 0 ≅ ModuleCat.of ℚ ℚ)
    (f : C(apm_t02a04_X, apm_t02a04_X)) :
    (induced f 0).hom = LinearMap.id := by
  open CategoryTheory ConstructionTargets.CoefficientH0 in
    letI : FiniteDimensional ℚ (apm_t02A04_HQ 0) :=
      Module.Finite.equiv e.toLinearEquiv.symm
    let ε : apm_t02A04_HQ 0 ⟶ ModuleCat.of ℚ ℚ := h0Augmentation ℚ
    let p : apm_t02a04_X :=
      apm_t02a04_diskInclusion ⟨0, by simp [apm_t02a04_Disk]⟩
    have hsurj : Function.Surjective ε := by
      intro a
      refine ⟨singularVertexH0Class ℚ p a, ?_⟩
      exact congrArg (fun g => g a)
        (singularVertexH0Class_comp_h0Augmentation ℚ p)
    have hdim : Module.finrank ℚ (apm_t02A04_HQ 0) =
        Module.finrank ℚ (ModuleCat.of ℚ ℚ) := by
      simpa using e.toLinearEquiv.finrank_eq
    have hinj : Function.Injective ε :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
    letI : CategoryTheory.Mono ε := (ModuleCat.mono_iff_injective ε).2 hinj
    have hcat : (induced f 0) ≫ ε = (𝟙 _) ≫ ε := by
      rw [CategoryTheory.Category.id_comp]
      change HomologicalComplex.homologyMap (singularPostcomposition ℚ f) 0 ≫ ε = ε
      exact h0Augmentation_naturality ℚ f
    have h := (CategoryTheory.cancel_mono ε).1 hcat
    exact congrArg (fun g => g.hom) h

lemma apm_t02A04_lefschetz_number_aux_trace_H0
    [FiniteDimensional ℚ (apm_t02A04_HQ 0)]
    (e : apm_t02A04_HQ 0 ≅ ModuleCat.of ℚ ℚ)
    (f : C(apm_t02a04_X, apm_t02a04_X)) :
    LinearMap.trace ℚ (apm_t02A04_HQ 0) (induced f 0).hom = 1 := by
  rw [apm_t02A04_lefschetz_number_aux_trace_H0_aux_induced_eq_id e f,
    LinearMap.trace_id]
  have hfinrank : Module.finrank ℚ (apm_t02A04_HQ 0) = 1 := by
    simpa using e.toLinearEquiv.finrank_eq
  simp [hfinrank]

theorem apm_t02A04_lefschetz_number
    (hH : Nonempty (apm_t02A04_HQ 0 ≅ ModuleCat.of ℚ ℚ) ∧
      ∀ k : ℕ, 0 < k → CategoryTheory.Limits.IsZero (apm_t02A04_HQ k)) :
    ∀ f : C(apm_t02a04_X, apm_t02a04_X), HasLefschetzNumber f 1 := by
  intro f
  obtain ⟨e⟩ := hH.1
  letI : FiniteDimensional ℚ (apm_t02A04_HQ 0) :=
    Module.Finite.equiv e.toLinearEquiv.symm
  have hfd : ∀ k, FiniteDimensional ℚ (apm_t02A04_HQ k) := by
    intro k
    by_cases hk : k = 0
    · subst k; infer_instance
    · have hz := hH.2 k (Nat.pos_of_ne_zero hk)
      letI : Subsingleton (apm_t02A04_HQ k) :=
        ModuleCat.subsingleton_of_isZero hz
      exact Module.Finite.of_surjective (0 : ℚ →ₗ[ℚ] apm_t02A04_HQ k)
        (fun x ↦ ⟨0, Subsingleton.elim _ _⟩)
  refine ⟨hfd, ⟨0, ?_, ?_⟩⟩
  · intro k hk
    exact ModuleCat.subsingleton_of_isZero (hH.2 k hk)
  · simp only [Nat.zero_add, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, pow_zero, one_mul]
    exact apm_t02A04_lefschetz_number_aux_trace_H0 e f

abbrev apm_t02A04_gluingSetoid :=
  Relation.EqvGen.setoid apm_t02a04_Glue

/-- The equivalence relation generated by the attaching graph is closed. -/
def apm_t02A04_gluingSetoid_isClosed_aux_left (z : Circle) :
    Sum apm_t02a04_SolidTorus apm_t02a04_Disk :=
  .inr ⟨(z : ℂ), by simpa using z.property.le⟩

noncomputable def apm_t02A04_gluingSetoid_isClosed_aux_right (z : Circle) :
    Sum apm_t02a04_SolidTorus apm_t02a04_Disk :=
  .inl (⟨(z : ℂ), by simpa using z.property.le⟩, z ^ 2)

lemma apm_t02A04_gluingSetoid_isClosed_aux_cases {x y :
    Sum apm_t02a04_SolidTorus apm_t02a04_Disk}
    (h : Relation.EqvGen apm_t02a04_Glue x y) :
    x = y ∨
      (∃ z, x = apm_t02A04_gluingSetoid_isClosed_aux_left z ∧
        y = apm_t02A04_gluingSetoid_isClosed_aux_right z) ∨
      (∃ z, x = apm_t02A04_gluingSetoid_isClosed_aux_right z ∧
        y = apm_t02A04_gluingSetoid_isClosed_aux_left z) := by
  induction h with
  | rel x y h =>
      cases h with
      | boundary z => exact Or.inr (Or.inl ⟨z, rfl, rfl⟩)
  | refl x => exact Or.inl rfl
  | symm x y h ih =>
      rcases ih with hxy | hxy | hxy
      · exact Or.inl hxy.symm
      · rcases hxy with ⟨z, rfl, rfl⟩
        exact Or.inr (Or.inr ⟨z, rfl, rfl⟩)
      · rcases hxy with ⟨z, rfl, rfl⟩
        exact Or.inr (Or.inl ⟨z, rfl, rfl⟩)
  | trans x y z hxy hyz ihxy ihyz =>
      rcases ihxy with hxy | hxy | hxy
      · subst y; exact ihyz
      · rcases hxy with ⟨a, rfl, rfl⟩
        rcases ihyz with hyz | hyz | hyz
        · subst z; exact Or.inr (Or.inl ⟨a, rfl, rfl⟩)
        · rcases hyz with ⟨b, hb, -⟩
          cases hb
        · rcases hyz with ⟨b, hb, rfl⟩
          have hab : a = b := by
            apply Subtype.ext
            have hp := Sum.inl.inj hb
            simpa [apm_t02A04_gluingSetoid_isClosed_aux_right] using
              congrArg (fun q : apm_t02a04_SolidTorus => (q.1 : ℂ)) hp
          subst b
          exact Or.inl rfl
      · rcases hxy with ⟨a, rfl, rfl⟩
        rcases ihyz with hyz | hyz | hyz
        · subst z; exact Or.inr (Or.inr ⟨a, rfl, rfl⟩)
        · rcases hyz with ⟨b, hb, rfl⟩
          have hab : a = b := by
            apply Subtype.ext
            have hp := Sum.inr.inj hb
            simpa [apm_t02A04_gluingSetoid_isClosed_aux_left] using
              congrArg (fun q : apm_t02a04_Disk => (q : ℂ)) hp
          subst b
          exact Or.inl rfl
        · rcases hyz with ⟨b, hb, -⟩
          cases hb

theorem apm_t02A04_gluingSetoid_isClosed :
    IsClosed {p : (Sum apm_t02a04_SolidTorus apm_t02a04_Disk) ×
        (Sum apm_t02a04_SolidTorus apm_t02a04_Disk) |
      apm_t02A04_gluingSetoid.r p.1 p.2} := by
  let l := apm_t02A04_gluingSetoid_isClosed_aux_left
  let r := apm_t02A04_gluingSetoid_isClosed_aux_right
  have hl : Continuous l := by
    dsimp [l]
    unfold apm_t02A04_gluingSetoid_isClosed_aux_left
    fun_prop
  have hr : Continuous r := by
    dsimp [r]
    unfold apm_t02A04_gluingSetoid_isClosed_aux_right
    fun_prop
  have hset : {p : (Sum apm_t02a04_SolidTorus apm_t02a04_Disk) ×
        (Sum apm_t02a04_SolidTorus apm_t02a04_Disk) |
      apm_t02A04_gluingSetoid.r p.1 p.2} =
      {p | p.1 = p.2} ∪ (Set.range (fun z => (l z, r z)) ∪
        Set.range (fun z => (r z, l z))) := by
    ext p
    constructor
    · intro hp
      rcases apm_t02A04_gluingSetoid_isClosed_aux_cases hp with h | h | h
      · exact Or.inl h
      · rcases h with ⟨z, hz1, hz2⟩
        refine Or.inr (Or.inl ⟨z, ?_⟩)
        apply Prod.ext <;> simp only [l, r]
        · exact hz1.symm
        · exact hz2.symm
      · rcases h with ⟨z, hz1, hz2⟩
        refine Or.inr (Or.inr ⟨z, ?_⟩)
        apply Prod.ext <;> simp only [l, r]
        · exact hz1.symm
        · exact hz2.symm
    · intro hp
      change Relation.EqvGen apm_t02a04_Glue p.1 p.2
      rcases hp with h | h
      · change p.1 = p.2 at h
        rw [h]
        exact Relation.EqvGen.refl _
      · rcases h with h | h
        · rcases h with ⟨z, hz⟩
          rw [← hz]
          exact Relation.EqvGen.rel _ _ (apm_t02a04_Glue.boundary z)
        · rcases h with ⟨z, hz⟩
          rw [← hz]
          exact Relation.EqvGen.symm _ _
            (Relation.EqvGen.rel _ _ (apm_t02a04_Glue.boundary z))
  rw [hset]
  simpa only [Set.image_univ] using (isClosed_eq continuous_fst continuous_snd).union
    ((isCompact_univ.image ((hl.prodMk hr))).isClosed.union
      (isCompact_univ.image ((hr.prodMk hl))).isClosed)

/-- The concrete quotient is Hausdorff. -/
theorem apm_t02A04_t2Space
    (hclosed : IsClosed {p : (Sum apm_t02a04_SolidTorus apm_t02a04_Disk) ×
        (Sum apm_t02a04_SolidTorus apm_t02a04_Disk) |
      apm_t02A04_gluingSetoid.r p.1 p.2}) :
    T2Space apm_t02a04_X := by
  exact ConstructionTargets.compact_closed_equivalence_quotient_t2
    apm_t02A04_gluingSetoid hclosed

/-- A finite coordinate complex together with the marked vertex and the
piecewise-affine quotient map.  The individual properties of this datum are
kept outside the structure so that they are independent proof obligations. -/
structure apm_t02A04_TriangulationDatum where
  n : ℕ
  K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))
  v : K.space
  toQuotient : K.space → apm_t02a04_X

/-- The `i`-th sixth of the circle, at parameter `t ∈ [0,1]`
(claude-14 review fix, 2026-10-28: the two cell models must agree along the
attaching curve edge by edge, with the same parameter). -/
noncomputable def apm_t02A04_arcPoint (i : Fin 6) (t : ℝ) : Circle :=
  Circle.exp (2 * Real.pi * ((i : ℝ) + t) / 6)

/-- Six cyclic source vertices and three cyclic target vertices, with the
degree-two map pairing opposite source vertices. -/
structure apm_t02A04_CircleSubdivision where
  source : Fin 6 → Circle
  target : Fin 3 → Circle
  source_injective : Function.Injective source
  target_injective : Function.Injective target
  doubling : ∀ i, source i ^ 2 = target ⟨i.1 % 3, Nat.mod_lt _ (by decide)⟩
  source_eq : ∀ i, source i = apm_t02A04_arcPoint i 0

lemma apm_t02A04_doublingCircle_subdivision_aux_injective (n : ℕ) (hn : n ≤ 6) :
    Function.Injective (fun i : Fin n ↦ apm_t02A04_arcPoint ⟨i.1, lt_of_lt_of_le i.2 hn⟩ 0) := by
  intro i j hij
  dsimp [apm_t02A04_arcPoint] at hij
  rw [Circle.exp_eq_exp] at hij
  obtain ⟨m, hm⟩ := hij
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hm' : (i.1 : ℤ) = (j.1 : ℤ) + m * 6 := by
    apply_mod_cast (show (i.1 : ℝ) = (j.1 : ℝ) + (m : ℝ) * 6 from ?_)
    field_simp [hp] at hm ⊢
    linarith
  apply Fin.ext
  omega

lemma apm_t02A04_doublingCircle_subdivision_aux_target_injective :
    Function.Injective (fun i : Fin 3 ↦
      apm_t02A04_arcPoint ⟨2 * i.1, by omega⟩ 0) := by
  intro i j hij
  dsimp [apm_t02A04_arcPoint] at hij
  rw [Circle.exp_eq_exp] at hij
  obtain ⟨m, hm⟩ := hij
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hm' : (2 * i.1 : ℤ) = 2 * j.1 + m * 6 := by
    have hr : (2 * i.1 : ℝ) = 2 * j.1 + (m : ℝ) * 6 := by
      field_simp [hp] at hm
      norm_num [Nat.cast_mul] at hm
      linarith
    exact_mod_cast hr
  apply Fin.ext
  omega

theorem apm_t02A04_doublingCircle_subdivision :
    Nonempty apm_t02A04_CircleSubdivision := by
  let source : Fin 6 → Circle := fun i ↦ apm_t02A04_arcPoint i 0
  let target : Fin 3 → Circle := fun i ↦
    apm_t02A04_arcPoint ⟨2 * i.1, by omega⟩ 0
  refine ⟨⟨source, target, ?_, ?_, ?_, ?_⟩⟩
  · exact apm_t02A04_doublingCircle_subdivision_aux_injective 6 (by omega)
  · exact apm_t02A04_doublingCircle_subdivision_aux_target_injective
  · intro i
    fin_cases i <;>
      dsimp [source, target, apm_t02A04_arcPoint] <;>
      rw [← Circle.exp_natCast_mul] <;>
      apply Circle.exp_eq_exp.mpr
    · exact ⟨0, by ring⟩
    · exact ⟨0, by ring⟩
    · exact ⟨0, by ring⟩
    · exact ⟨1, by ring⟩
    · exact ⟨1, by ring⟩
    · exact ⟨1, by ring⟩
  · intro i
    rfl

/-- A finite prism triangulation of the solid torus in which all six points of
the attaching curve are vertices. -/
structure apm_t02A04_SolidPrismModel (C : apm_t02A04_CircleSubdivision) where
  n : ℕ
  K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))
  curveVertex : Fin 6 → K.space
  equiv : K.space ≃ₜ apm_t02a04_SolidTorus
  faces_finite : K.faces.Finite
  curveVertex_injective : Function.Injective curveVertex
  curveVertex_eq : ∀ i, equiv (curveVertex i) =
    (⟨(C.source i : ℂ), by simpa using (C.source i).property.le⟩, C.source i ^ 2)
  /-- consecutive curve vertices span an edge -/
  curve_edge : ∀ i : Fin 6,
    ({((curveVertex i : K.space) : EuclideanSpace ℝ (Fin n)),
      ((curveVertex (i + 1) : K.space) : EuclideanSpace ℝ (Fin n))} :
      Finset (EuclideanSpace ℝ (Fin n))) ∈ K.faces
  /-- the attaching curve runs along that edge, affinely in the arc parameter -/
  curve_affine : ∀ (i : Fin 6) (t : ℝ), 0 ≤ t → t ≤ 1 →
    ((equiv.symm (⟨((apm_t02A04_arcPoint i t : Circle) : ℂ),
        by simpa using (apm_t02A04_arcPoint i t).property.le⟩,
        apm_t02A04_arcPoint i t ^ 2) : K.space) : EuclideanSpace ℝ (Fin n)) =
      (1 - t) • ((curveVertex i : K.space) : EuclideanSpace ℝ (Fin n)) +
        t • ((curveVertex (i + 1) : K.space) : EuclideanSpace ℝ (Fin n))

theorem apm_t02A04_solidTorus_prism_model
    (C : apm_t02A04_CircleSubdivision) :
    Nonempty (apm_t02A04_SolidPrismModel C) := by
  sorry

/-! ### Coned hexagon (claude-14, 2026-10-29)
Vertices `Fin 7`: `0` is the centre, `apm_t02A04_coneIdx i = 1 + i` the boundary
vertex over `arcPoint i 0`.  On facet `i` (`0, i, i+1`) a point with weights
`(a, b, c)` goes to radius `b + c` at arc parameter `c / (b + c)`, so each
boundary edge is affine in the arc parameter by construction. -/

def apm_t02A04_coneIdx (i : Fin 6) : Fin 7 := ⟨1 + i.1, by omega⟩

def apm_t02A04_coneFacet (i : Fin 6) : Finset (Fin 7) :=
  {0, apm_t02A04_coneIdx i, apm_t02A04_coneIdx (i + 1)}

noncomputable def apm_t02A04_coneComplex : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 7)) :=
  ConstructionTargets.RealProjectivePlaneTriangulation.basisComplex 7 (Finset.univ.image apm_t02A04_coneFacet)

def apm_t02A04_coneHull (i : Fin 6) : Set (EuclideanSpace ℝ (Fin 7)) :=
  convexHull ℝ ↑((apm_t02A04_coneFacet i).image (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7))

noncomputable def apm_t02A04_conePoint (i : Fin 6) (y : EuclideanSpace ℝ (Fin 7)) : ℂ :=
  ((y (apm_t02A04_coneIdx i) + y (apm_t02A04_coneIdx (i + 1)) : ℝ) : ℂ) *
    ((apm_t02A04_arcPoint i (y (apm_t02A04_coneIdx (i + 1)) /
      (y (apm_t02A04_coneIdx i) + y (apm_t02A04_coneIdx (i + 1)))) : Circle) : ℂ)

noncomputable def apm_t02A04_coneMap (y : apm_t02A04_coneComplex.space) : apm_t02a04_Disk := by
  classical
  exact ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp (apm_t02A04_conePoint
    (if h : ∃ i, (y : EuclideanSpace ℝ (Fin 7)) ∈ apm_t02A04_coneHull i then Classical.choose h else 0) y)

lemma apm_t02A04_attachedDisk_cone_model_aux_basisVertex_injective (N : ℕ) :
    Function.Injective (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex N) := by
  intro i j hij
  have h := congrArg (fun z : EuclideanSpace ℝ (Fin N) => z i) hij
  simpa [ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex,
    EuclideanSpace.single_apply] using h

lemma apm_t02A04_attachedDisk_cone_model_aux_vertex_mem (k : Fin 7) :
    ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7 k ∈ apm_t02A04_coneComplex.space := by
  have h (i : Fin 6) (j : Fin 7) (hj : j ∈ apm_t02A04_coneFacet i) :
      ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7 j ∈
        apm_t02A04_coneComplex.space := by
    rw [Geometry.SimplicialComplex.mem_space_iff]
    refine ⟨{ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7 j},
      ConstructionTargets.RealProjectivePlaneTriangulation.basisComplex_vertex_mem
        (f := apm_t02A04_coneFacet i) ?_ hj, ?_⟩
    · exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    · simp
  fin_cases k
  · exact h 0 0 (by simp [apm_t02A04_coneFacet])
  · exact h 0 1 (by simp [apm_t02A04_coneFacet, apm_t02A04_coneIdx])
  · exact h 1 2 (by simp [apm_t02A04_coneFacet, apm_t02A04_coneIdx])
  · exact h 2 3 (by simp [apm_t02A04_coneFacet, apm_t02A04_coneIdx])
  · exact h 3 4 (by simp [apm_t02A04_coneFacet, apm_t02A04_coneIdx])
  · exact h 4 5 (by simp [apm_t02A04_coneFacet, apm_t02A04_coneIdx])
  · exact h 5 6 (by simp [apm_t02A04_coneFacet, apm_t02A04_coneIdx])

lemma apm_t02A04_attachedDisk_cone_model_aux_edge_mem (i : Fin 6) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7 (apm_t02A04_coneIdx i) +
      t • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7 (apm_t02A04_coneIdx (i + 1)) ∈ apm_t02A04_coneComplex.space := by
  classical
  apply Geometry.SimplicialComplex.convexHull_subset_space (K := apm_t02A04_coneComplex)
    (s := (apm_t02A04_coneFacet i).image
      (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7))
  · refine ⟨⟨apm_t02A04_coneFacet i, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      Finset.Subset.refl _⟩, ?_⟩
    simp [apm_t02A04_coneFacet]
  · apply segment_subset_convexHull
      (show ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7
          (apm_t02A04_coneIdx i) ∈
        ↑((apm_t02A04_coneFacet i).image
          (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7)) by
        simp [apm_t02A04_coneFacet])
      (show ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7
          (apm_t02A04_coneIdx (i + 1)) ∈
        ↑((apm_t02A04_coneFacet i).image
          (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7)) by
        simp [apm_t02A04_coneFacet])
    rw [segment_eq_image]
    exact ⟨t, ⟨ht0, ht1⟩, rfl⟩

lemma apm_t02A04_attachedDisk_cone_model_aux_cover (y : EuclideanSpace ℝ (Fin 7)) (hy : y ∈ apm_t02A04_coneComplex.space) :
    ∃ i, y ∈ apm_t02A04_coneHull i := by
  classical
  rw [Geometry.SimplicialComplex.mem_space_iff] at hy
  obtain ⟨S, hS, hy⟩ := hy
  have hSb : S ∈ ConstructionTargets.RealProjectivePlaneTriangulation.basisFaces 7
      (Finset.univ.image apm_t02A04_coneFacet) := by
    exact hS.1
  obtain ⟨f, hf, hSf⟩ := hSb
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hf
  refine ⟨i, ?_⟩
  exact convexHull_mono (by exact_mod_cast hSf) hy

lemma apm_t02A04_attachedDisk_cone_model_aux_point_norm (i : Fin 6) (y : EuclideanSpace ℝ (Fin 7)) (hy : y ∈ apm_t02A04_coneHull i) :
    ‖apm_t02A04_conePoint i y‖ ≤ 1 := by
  classical
  let a := apm_t02A04_coneIdx i
  let b := apm_t02A04_coneIdx (i + 1)
  let L : EuclideanSpace ℝ (Fin 7) →ₗ[ℝ] ℝ :=
    ((PiLp.proj 2 (fun _ : Fin 7 ↦ ℝ) a).toLinearMap :
      EuclideanSpace ℝ (Fin 7) →ₗ[ℝ] ℝ) +
    ((PiLp.proj 2 (fun _ : Fin 7 ↦ ℝ) b).toLinearMap :
      EuclideanSpace ℝ (Fin 7) →ₗ[ℝ] ℝ)
  have hsub : apm_t02A04_coneHull i ⊆ L ⁻¹' Set.Icc (0 : ℝ) 1 := by
    apply convexHull_min
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
      simp only [Set.mem_preimage, Set.mem_Icc]
      fin_cases i <;> fin_cases k <;>
        simp_all [L, a, b, apm_t02A04_coneFacet, apm_t02A04_coneIdx,
          ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex]
    · exact (convex_Icc (0 : ℝ) 1).linear_preimage L
  have hr := hsub hy
  change 0 ≤ L y ∧ L y ≤ 1 at hr
  rw [show apm_t02A04_conePoint i y = ((L y : ℝ) : ℂ) *
      (apm_t02A04_arcPoint i (y b / L y) : ℂ) by
    simp [apm_t02A04_conePoint, L, a, b]]
  rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, Real.norm_eq_abs,
    abs_of_nonneg hr.1]
  exact hr.2

/-- Facets sharing a point agree there: on the edge `0, i+1` both give arc
parameter `1` resp. `0` of adjacent arcs, the same circle point; at the centre
the radius is `0`. -/
lemma apm_t02A04_attachedDisk_cone_model_aux_agree_aux_zero
    (i : Fin 6) (y : EuclideanSpace ℝ (Fin 7))
    (hy : y ∈ apm_t02A04_coneHull i) (k : Fin 7)
    (hk : k ∉ apm_t02A04_coneFacet i) : y k = 0 := by
  let L : EuclideanSpace ℝ (Fin 7) →ₗ[ℝ] ℝ :=
    ((PiLp.proj 2 (fun _ : Fin 7 ↦ ℝ) k).toLinearMap :
      EuclideanSpace ℝ (Fin 7) →ₗ[ℝ] ℝ)
  have hsub : apm_t02A04_coneHull i ⊆ L.ker := by
    apply convexHull_min
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
      change ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7 j k = 0
      simp only [ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex,
        EuclideanSpace.single_apply]
      split_ifs with h
      · subst j
        exact (hk hj).elim
      · rfl
    · exact L.ker.convex
  exact hsub hy

lemma apm_t02A04_attachedDisk_cone_model_aux_agree_aux_arc (i : Fin 6) :
    apm_t02A04_arcPoint i 1 = apm_t02A04_arcPoint (i + 1) 0 := by
  apply Circle.exp_eq_exp.mpr
  fin_cases i <;> dsimp [apm_t02A04_arcPoint]
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨1, by ring⟩

set_option maxHeartbeats 2000000 in
lemma apm_t02A04_attachedDisk_cone_model_aux_agree (i j : Fin 6) (y : EuclideanSpace ℝ (Fin 7))
    (hi : y ∈ apm_t02A04_coneHull i) (hj : y ∈ apm_t02A04_coneHull j) :
    apm_t02A04_conePoint i y = apm_t02A04_conePoint j y := by
  classical
  have hzi : ∀ k, k ∉ apm_t02A04_coneFacet i → y k = 0 :=
    fun k hk ↦ apm_t02A04_attachedDisk_cone_model_aux_agree_aux_zero i y hi k hk
  have hzj : ∀ k, k ∉ apm_t02A04_coneFacet j → y k = 0 :=
    fun k hk ↦ apm_t02A04_attachedDisk_cone_model_aux_agree_aux_zero j y hj k hk
  by_cases hri : y (apm_t02A04_coneIdx i) + y (apm_t02A04_coneIdx (i + 1)) = 0
  · by_cases hrj : y (apm_t02A04_coneIdx j) + y (apm_t02A04_coneIdx (j + 1)) = 0
    · simp [apm_t02A04_conePoint, hri, hrj]
    · exfalso
      fin_cases i <;> fin_cases j <;>
        simp_all [apm_t02A04_coneIdx, apm_t02A04_coneFacet]
  by_cases hrj : y (apm_t02A04_coneIdx j) + y (apm_t02A04_coneIdx (j + 1)) = 0
  · exfalso
    fin_cases i <;> fin_cases j <;>
      simp_all [apm_t02A04_coneIdx, apm_t02A04_coneFacet]
  fin_cases i <;> fin_cases j <;>
    simp_all [apm_t02A04_conePoint, apm_t02A04_coneIdx,
      apm_t02A04_coneFacet,
      apm_t02A04_attachedDisk_cone_model_aux_agree_aux_arc]

lemma apm_t02A04_attachedDisk_cone_model_aux_continuous : Continuous apm_t02A04_coneMap := by
  sorry

lemma apm_t02A04_attachedDisk_cone_model_aux_injective : Function.Injective apm_t02A04_coneMap := by
  sorry

lemma apm_t02A04_attachedDisk_cone_model_aux_surjective : Function.Surjective apm_t02A04_coneMap := by
  sorry

lemma apm_t02A04_attachedDisk_cone_model_aux_centre_map :
    ((apm_t02A04_coneMap ⟨ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7 0, apm_t02A04_attachedDisk_cone_model_aux_vertex_mem 0⟩ : apm_t02a04_Disk) : ℂ) = 0 := by
  simp [apm_t02A04_coneMap, apm_t02A04_conePoint,
    ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp,
    ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex,
    apm_t02A04_coneIdx]

-- BEGIN SEAT AREA
lemma apm_t02A04_attachedDisk_cone_model_aux_edge_map (i : Fin 6) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((apm_t02A04_coneMap ⟨_, apm_t02A04_attachedDisk_cone_model_aux_edge_mem i t ht0 ht1⟩ : apm_t02a04_Disk) : ℂ) =
      ((apm_t02A04_arcPoint i t : Circle) : ℂ) := by
  sorry
-- END SEAT AREA

/-- A coned six-gon triangulation of the attached disk, with its boundary
vertices at the same six circle points and its centre retained as a vertex. -/
structure apm_t02A04_DiskConeModel (C : apm_t02A04_CircleSubdivision) where
  n : ℕ
  K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))
  centre : K.space
  boundaryVertex : Fin 6 → K.space
  equiv : K.space ≃ₜ apm_t02a04_Disk
  faces_finite : K.faces.Finite
  centre_vertex : {((centre : K.space) : EuclideanSpace ℝ (Fin n))} ∈ K.faces
  boundaryVertex_injective : Function.Injective boundaryVertex
  centre_ne_boundary : ∀ i, centre ≠ boundaryVertex i
  centre_eq : equiv centre = ⟨0, by simp [apm_t02a04_Disk]⟩
  boundaryVertex_eq : ∀ i, equiv (boundaryVertex i) =
    ⟨(C.source i : ℂ), by simpa using (C.source i).property.le⟩
  boundary_edge : ∀ i : Fin 6,
    ({((boundaryVertex i : K.space) : EuclideanSpace ℝ (Fin n)),
      ((boundaryVertex (i + 1) : K.space) : EuclideanSpace ℝ (Fin n))} :
      Finset (EuclideanSpace ℝ (Fin n))) ∈ K.faces
  boundary_affine : ∀ (i : Fin 6) (t : ℝ), 0 ≤ t → t ≤ 1 →
    ((equiv.symm ⟨((apm_t02A04_arcPoint i t : Circle) : ℂ),
        by simpa using (apm_t02A04_arcPoint i t).property.le⟩ : K.space) :
        EuclideanSpace ℝ (Fin n)) =
      (1 - t) • ((boundaryVertex i : K.space) : EuclideanSpace ℝ (Fin n)) +
        t • ((boundaryVertex (i + 1) : K.space) : EuclideanSpace ℝ (Fin n))

theorem apm_t02A04_attachedDisk_cone_model
    (C : apm_t02A04_CircleSubdivision) :
    Nonempty (apm_t02A04_DiskConeModel C) := by
  classical
  letI : CompactSpace apm_t02A04_coneComplex.space :=
    isCompact_iff_compactSpace.mp
      (ConstructionTargets.RealProjectivePlaneTriangulation.finite_simplicialComplex_space_isCompact _
        (ConstructionTargets.RealProjectivePlaneTriangulation.basisComplex_faces_finite 7 _))
  let e : apm_t02A04_coneComplex.space ≃ₜ apm_t02a04_Disk :=
    apm_t02A04_attachedDisk_cone_model_aux_continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective _ ⟨apm_t02A04_attachedDisk_cone_model_aux_injective, apm_t02A04_attachedDisk_cone_model_aux_surjective⟩)
  have hface : ∀ i : Fin 6, ∀ S ⊆ apm_t02A04_coneFacet i, S.Nonempty →
      S.image (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7) ∈ apm_t02A04_coneComplex.faces := by
    intro i S hS hne
    refine ⟨⟨apm_t02A04_coneFacet i, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      Finset.image_subset_image hS⟩, ?_⟩
    simpa [Finset.image_eq_empty] using hne.ne_empty
  have hbv : ∀ (i : Fin 6) (z : apm_t02A04_coneComplex.space),
      (z : EuclideanSpace ℝ (Fin 7)) = ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7 (apm_t02A04_coneIdx i) →
      ((e z : apm_t02a04_Disk) : ℂ) = ((apm_t02A04_arcPoint i 0 : Circle) : ℂ) := by
    intro i z hz
    have hz' : z = ⟨_, apm_t02A04_attachedDisk_cone_model_aux_edge_mem i 0 le_rfl zero_le_one⟩ := by
      apply Subtype.ext; rw [hz]; simp
    rw [hz']
    exact apm_t02A04_attachedDisk_cone_model_aux_edge_map i 0 le_rfl zero_le_one
  refine ⟨⟨7, apm_t02A04_coneComplex, ⟨_, apm_t02A04_attachedDisk_cone_model_aux_vertex_mem 0⟩,
    fun i => ⟨_, apm_t02A04_attachedDisk_cone_model_aux_vertex_mem (apm_t02A04_coneIdx i)⟩, e,
    ConstructionTargets.RealProjectivePlaneTriangulation.basisComplex_faces_finite 7 _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- centre_vertex
    simpa using hface 0 {0} (by simp [apm_t02A04_coneFacet]) (by simp)
  · -- boundaryVertex_injective
    intro i j hij
    have h := apm_t02A04_attachedDisk_cone_model_aux_basisVertex_injective 7 (congrArg Subtype.val hij)
    have h' := congrArg Fin.val h
    simp [apm_t02A04_coneIdx] at h'
    exact Fin.ext h'
  · -- centre_ne_boundary
    intro i hi
    have h := apm_t02A04_attachedDisk_cone_model_aux_basisVertex_injective 7 (congrArg Subtype.val hi)
    have h' := congrArg Fin.val h
    simp [apm_t02A04_coneIdx] at h'
    omega
  · -- centre_eq
    exact Subtype.ext apm_t02A04_attachedDisk_cone_model_aux_centre_map
  · -- boundaryVertex_eq
    intro i
    apply Subtype.ext
    rw [hbv i _ rfl, C.source_eq i]
  · -- boundary_edge
    intro i
    have := hface i {apm_t02A04_coneIdx i, apm_t02A04_coneIdx (i + 1)}
      (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> simp [apm_t02A04_coneFacet]) (by simp)
    simpa [Finset.image_insert, Finset.image_singleton] using this
  · -- boundary_affine
    intro i t ht0 ht1
    have hsymm : e.symm ⟨((apm_t02A04_arcPoint i t : Circle) : ℂ), by
        simpa using (apm_t02A04_arcPoint i t).property.le⟩ =
        ⟨_, apm_t02A04_attachedDisk_cone_model_aux_edge_mem i t ht0 ht1⟩ := by
      rw [Homeomorph.symm_apply_eq]
      exact Subtype.ext (apm_t02A04_attachedDisk_cone_model_aux_edge_map i t ht0 ht1).symm
    rw [hsymm]

/-- Glue the two finite complexes along the six distinct curve vertices.
The resulting coordinate realization has the required finite face set and
marked vertex, and carries the canonical piecewise-affine map to `X`. -/
theorem apm_t02A04_quotientComplex_model
    (C : apm_t02A04_CircleSubdivision)
    (S : apm_t02A04_SolidPrismModel C)
    (D : apm_t02A04_DiskConeModel C) :
    ∃ M : apm_t02A04_TriangulationDatum,
      M.K.faces.Finite ∧
      {((M.v : M.K.space) : EuclideanSpace ℝ (Fin M.n))} ∈ M.K.faces ∧
      M.toQuotient M.v =
        apm_t02a04_diskInclusion ⟨0, by simp [apm_t02a04_Disk]⟩ ∧
      Continuous M.toQuotient ∧ Function.Bijective M.toQuotient := by
  sorry

/-- Compatible finite solid-torus/cell triangulation, assembled from the
independent coordinate leaves above. -/
theorem apm_t02A04_hasFiniteVertexTriangulation :
    ConstructionTargets.FiniteTriangulation.HasFiniteVertexTriangulation
      apm_t02a04_X
      (apm_t02a04_diskInclusion ⟨0, by simp [apm_t02a04_Disk]⟩) := by
  obtain ⟨C⟩ := apm_t02A04_doublingCircle_subdivision
  obtain ⟨S⟩ := apm_t02A04_solidTorus_prism_model C
  obtain ⟨D⟩ := apm_t02A04_attachedDisk_cone_model C
  obtain ⟨M, hfin, hv, hmark, hcont, hbij⟩ :=
    apm_t02A04_quotientComplex_model C S D
  letI : CompactSpace M.K.space :=
    isCompact_iff_compactSpace.mp
      (ConstructionTargets.RealProjectivePlaneTriangulation.finite_simplicialComplex_space_isCompact
        M.K hfin)
  letI : T2Space apm_t02a04_X :=
    apm_t02A04_t2Space apm_t02A04_gluingSetoid_isClosed
  let e' : M.K.space ≃ₜ apm_t02a04_X :=
    hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective M.toQuotient hbij)
  let e : apm_t02a04_X ≃ₜ M.K.space := e'.symm
  refine ⟨M.n, M.K, e, (M.v : EuclideanSpace ℝ (Fin M.n)), hfin, hv, ?_⟩
  have heq : e (apm_t02a04_diskInclusion ⟨0, by simp [apm_t02a04_Disk]⟩) = M.v := by
    apply e'.injective
    simpa [e, e'] using hmark.symm
  exact congrArg Subtype.val heq

/-- The space admits a finite geometric
triangulation, as required by
`ConstructionTargets.LefschetzCompactPolyhedron.fixedPointOfNonzeroLefschetz`.
(claude-14, 2026-10-28; statement as recorded in that module's blueprint.) -/
theorem apm_t02A04_isFinitePolyhedron :
    ConstructionTargets.LefschetzCompactPolyhedron.IsFinitePolyhedron
      apm_t02a04_X := by
  exact ConstructionTargets.FiniteTriangulation.HasFiniteVertexTriangulation.isFinitePolyhedron
    apm_t02A04_hasFiniteVertexTriangulation

/-- **LIBRARY.** Specialized compact-polyhedron Lefschetz implication. -/
theorem apm_t02A04_fixed_point_of_lefschetz
    (hL : ∀ f : C(apm_t02a04_X, apm_t02a04_X), HasLefschetzNumber f 1) :
    ∀ f : C(apm_t02a04_X, apm_t02a04_X), ∃ x, f x = x := by
  intro f
  exact ConstructionTargets.LefschetzCompactPolyhedron.fixedPointOfNonzeroLefschetz
    apm_t02A04_isFinitePolyhedron f (hL f) one_ne_zero

theorem apm_t02a04 :
    ∀ f : apm_t02a04_X → apm_t02a04_X,
      Continuous f → ∃ x, f x = x := by
  intro f hf
  exact apm_t02A04_fixed_point_of_lefschetz
    (apm_t02A04_lefschetz_number apm_t02A04_rational_homology) ⟨f, hf⟩

#print axioms apm_t02a04
