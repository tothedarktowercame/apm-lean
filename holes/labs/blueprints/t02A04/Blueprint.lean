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
import ConstructionTargets.LefschetzFixedPoint
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

lemma apm_t02A04_attachedDisk_cone_model_aux_continuous_piece (i : Fin 6) :
    ContinuousOn (apm_t02A04_conePoint i) (apm_t02A04_coneHull i) := by
  intro x hx
  let r : EuclideanSpace ℝ (Fin 7) → ℝ := fun y ↦
    y (apm_t02A04_coneIdx i) + y (apm_t02A04_coneIdx (i + 1))
  by_cases hr : r x = 0
  · rw [ContinuousWithinAt]
    rw [show apm_t02A04_conePoint i x = 0 by simp [apm_t02A04_conePoint, r, hr]]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hcont : Continuous r := by unfold r; fun_prop
    have ht : Filter.Tendsto (fun y ↦ |r y|)
        (nhdsWithin x (apm_t02A04_coneHull i)) (nhds 0) := by
      simpa [hr] using
        ((continuous_abs.comp hcont).continuousAt (x := x)).continuousWithinAt.tendsto
    rw [show (fun y ↦ ‖apm_t02A04_conePoint i y‖) = (fun y ↦ |r y|) by
      funext y
      simp [apm_t02A04_conePoint, r, norm_mul, Complex.norm_real,
        Circle.norm_coe, Real.norm_eq_abs, ← Complex.ofReal_add]]
    exact ht
  · have hr' : ContinuousWithinAt r (apm_t02A04_coneHull i) x := by
      unfold r
      fun_prop
    unfold apm_t02A04_conePoint
    fun_prop (disch := assumption)

lemma apm_t02A04_attachedDisk_cone_model_aux_continuous : Continuous apm_t02A04_coneMap := by
  classical
  let C : Fin 6 → Set apm_t02A04_coneComplex.space := fun i ↦
    {y | (y : EuclideanSpace ℝ (Fin 7)) ∈ apm_t02A04_coneHull i}
  have hcover : ⋃ i, C i = Set.univ := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact apm_t02A04_attachedDisk_cone_model_aux_cover y y.2
  have hclosed : ∀ i, IsClosed (C i) := by
    intro i
    change IsClosed ((fun y : apm_t02A04_coneComplex.space ↦
      (y : EuclideanSpace ℝ (Fin 7))) ⁻¹' apm_t02A04_coneHull i)
    unfold apm_t02A04_coneHull
    simpa only [Finset.coe_image] using
      (((apm_t02A04_coneFacet i).finite_toSet.image
        (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7)).isCompact_convexHull ℝ).isClosed.preimage
          (continuous_subtype_val : Continuous
            (fun y : apm_t02A04_coneComplex.space ↦
              (y : EuclideanSpace ℝ (Fin 7))))
  refine (locallyFinite_of_finite C).continuous hcover hclosed ?_
  intro i
  rw [continuousOn_iff_continuous_restrict]
  apply continuous_induced_rng.mpr
  change Continuous (fun y : C i ↦ ((apm_t02A04_coneMap y : apm_t02a04_Disk) : ℂ))
  have hp : Continuous fun y : C i ↦ apm_t02A04_conePoint i
      ((y : apm_t02A04_coneComplex.space) : EuclideanSpace ℝ (Fin 7)) := by
    rw [← continuousOn_univ]
    have hv : Continuous (fun y : C i ↦
        ((y : apm_t02A04_coneComplex.space) : EuclideanSpace ℝ (Fin 7))) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (apm_t02A04_attachedDisk_cone_model_aux_continuous_piece i).comp
      hv.continuousOn (by intro y _; exact y.2)
  have heq : (fun y : C i ↦ ((apm_t02A04_coneMap y : apm_t02a04_Disk) : ℂ)) =
      fun y : C i ↦ apm_t02A04_conePoint i y := by
    funext y
    unfold apm_t02A04_coneMap
    have hc := apm_t02A04_attachedDisk_cone_model_aux_cover
      (y : EuclideanSpace ℝ (Fin 7)) y.1.2
    have ha := apm_t02A04_attachedDisk_cone_model_aux_agree
      (if h : ∃ j, (y : EuclideanSpace ℝ (Fin 7)) ∈ apm_t02A04_coneHull j
        then Classical.choose h else 0) i y
      (by simp only [dif_pos hc]; exact Classical.choose_spec hc) y.2
    have hn := apm_t02A04_attachedDisk_cone_model_aux_point_norm i y y.2
    simp [ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp, hn, ha]
  rw [heq]
  exact hp

lemma apm_t02A04_attachedDisk_cone_model_aux_injective_aux_conePoint
    (x y : apm_t02A04_coneComplex.space) (i j : Fin 6)
    (hxi : (x : EuclideanSpace ℝ (Fin 7)) ∈ apm_t02A04_coneHull i)
    (hyj : (y : EuclideanSpace ℝ (Fin 7)) ∈ apm_t02A04_coneHull j)
    (hxy : apm_t02A04_coneMap x = apm_t02A04_coneMap y) :
    apm_t02A04_conePoint i x = apm_t02A04_conePoint j y := by
  classical
  have hxex : ∃ k, (x : EuclideanSpace ℝ (Fin 7)) ∈ apm_t02A04_coneHull k := ⟨i, hxi⟩
  have hyex : ∃ k, (y : EuclideanSpace ℝ (Fin 7)) ∈ apm_t02A04_coneHull k := ⟨j, hyj⟩
  let ix : Fin 6 := Classical.choose hxex
  let iy : Fin 6 := Classical.choose hyex
  have hxix : (x : EuclideanSpace ℝ (Fin 7)) ∈ apm_t02A04_coneHull ix :=
    Classical.choose_spec hxex
  have hyiy : (y : EuclideanSpace ℝ (Fin 7)) ∈ apm_t02A04_coneHull iy :=
    Classical.choose_spec hyex
  have hnx : ‖apm_t02A04_conePoint ix x‖ ≤ 1 :=
    apm_t02A04_attachedDisk_cone_model_aux_point_norm ix x hxix
  have hny : ‖apm_t02A04_conePoint iy y‖ ≤ 1 :=
    apm_t02A04_attachedDisk_cone_model_aux_point_norm iy y hyiy
  have hagreex := apm_t02A04_attachedDisk_cone_model_aux_agree ix i x hxix hxi
  have hagreey := apm_t02A04_attachedDisk_cone_model_aux_agree iy j y hyiy hyj
  have hcoe := congrArg (fun z : apm_t02a04_Disk => (z : ℂ)) hxy
  simp only [apm_t02A04_coneMap, dif_pos hxex, dif_pos hyex] at hcoe
  change ((ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp
      (apm_t02A04_conePoint ix x) : apm_t02a04_Disk) : ℂ) =
    ((ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp
      (apm_t02A04_conePoint iy y) : apm_t02a04_Disk) : ℂ) at hcoe
  simp only [ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp,
    dif_pos hnx, dif_pos hny, Subtype.coe_mk] at hcoe
  exact hagreex.symm.trans (hcoe.trans hagreey)

/-- Barycentric description of a cone facet hull. -/
lemma apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet_aux_bary (i : Fin 6) (x : EuclideanSpace ℝ (Fin 7))
    (hx : x ∈ apm_t02A04_coneHull i) :
    (∀ k, 0 ≤ x k) ∧ x 0 + x (apm_t02A04_coneIdx i) + x (apm_t02A04_coneIdx (i + 1)) = 1 ∧
      (∀ k, k ∉ apm_t02A04_coneFacet i → x k = 0) := by
  have hstd : x ∈ {z : EuclideanSpace ℝ (Fin 7) |
      (∀ k, 0 ≤ z k) ∧ ∑ k, z k = 1} := by
    apply convexHull_min _ (show Convex ℝ {z : EuclideanSpace ℝ (Fin 7) |
        (∀ k, 0 ≤ z k) ∧ ∑ k, z k = 1} by
      intro y hy z hz a b ha hb hab
      simp only [Set.mem_setOf_eq] at hy hz ⊢
      constructor
      · intro k
        exact add_nonneg (mul_nonneg ha (hy.1 k)) (mul_nonneg hb (hz.1 k))
      · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hy.2, hz.2, hab]) hx
    rintro y hy
    simp only [apm_t02A04_coneHull, Finset.coe_image, Set.mem_image] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    constructor
    · intro k
      simp only [ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex,
        EuclideanSpace.single_apply]
      split_ifs <;> norm_num
    · simp [ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex]
  have hzero : ∀ k, k ∉ apm_t02A04_coneFacet i → x k = 0 := by
    intro k hk
    apply convexHull_min _ (show Convex ℝ {z : EuclideanSpace ℝ (Fin 7) | z k = 0} by
      intro y hy z hz a b ha hb hab
      simp only [Set.mem_setOf_eq] at hy hz ⊢
      simp [hy, hz]) hx
    rintro y hy
    simp only [apm_t02A04_coneHull, Finset.coe_image, Set.mem_image] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    simp only [Set.mem_setOf_eq,
      ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex,
      EuclideanSpace.single_apply]
    split_ifs with h
    · exact (hk (h ▸ hj)).elim
    · rfl
  have hsum : x 0 + x (apm_t02A04_coneIdx i) +
      x (apm_t02A04_coneIdx (i + 1)) = 1 := by
    apply convexHull_min _ (show Convex ℝ {z : EuclideanSpace ℝ (Fin 7) |
        z 0 + z (apm_t02A04_coneIdx i) +
          z (apm_t02A04_coneIdx (i + 1)) = 1} by
      intro y hy z hz a b ha hb hab
      simp only [Set.mem_setOf_eq] at hy hz ⊢
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      nlinarith [hy, hz]) hx
    rintro y hy
    simp only [Finset.coe_image, Set.mem_image] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    fin_cases i <;>
      simp [apm_t02A04_coneFacet, apm_t02A04_coneIdx,
        ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex,
        EuclideanSpace.single_apply] at hj ⊢ <;>
      aesop
  exact ⟨hstd.1, hsum, hzero⟩

/-- Equal arc points with parameters in `[0, 1]`: same arc and parameter, or the
shared endpoint of adjacent arcs.  (`Circle.exp` is `2π`-periodic and injective on
a half-open period; compare `2π(i + s)/6` with `2π(j + s')/6`.) -/
lemma apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet_aux_angle_aux_pi_pos :
    0 < Real.pi := Real.pi_pos

set_option maxHeartbeats 2000000 in
lemma apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet_aux_angle (i j : Fin 6) (s s' : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hs0' : 0 ≤ s') (hs1' : s' ≤ 1) (h : apm_t02A04_arcPoint i s = apm_t02A04_arcPoint j s') :
    (i = j ∧ s = s') ∨ (j = i + 1 ∧ s = 1 ∧ s' = 0) ∨ (i = j + 1 ∧ s = 0 ∧ s' = 1) := by
  unfold apm_t02A04_arcPoint at h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
  have heq : (i : ℝ) + s = (j : ℝ) + s' + (m : ℝ) * 6 := by
    have hp := Real.pi_pos
    push_cast at hm
    nlinarith
  fin_cases i <;> fin_cases j
  all_goals
    norm_num at heq
    have hmlo : (-1 : ℤ) ≤ m := by
      exact_mod_cast (show (-1 : ℝ) ≤ (m : ℝ) by linarith)
    have hmhi : m ≤ (1 : ℤ) := by
      exact_mod_cast (show (m : ℝ) ≤ (1 : ℝ) by linarith)
    interval_cases m <;> norm_num at heq
  all_goals
    aesop (add safe (by linarith))

/-- Two facet points agreeing on both facets' vertices are equal (`_aux_bary`: zero
off the facet). -/
lemma apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet_aux_coords
    (x y : EuclideanSpace ℝ (Fin 7)) (i j : Fin 6)
    (hxi : x ∈ apm_t02A04_coneHull i) (hyj : y ∈ apm_t02A04_coneHull j)
    (h : ∀ k, k ∈ apm_t02A04_coneFacet i ∨ k ∈ apm_t02A04_coneFacet j → x k = y k) :
    x = y := by
  obtain ⟨-, -, hx⟩ := apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet_aux_bary i x hxi
  obtain ⟨-, -, hy⟩ := apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet_aux_bary j y hyj
  ext k
  by_cases hk : k ∈ apm_t02A04_coneFacet i ∨ k ∈ apm_t02A04_coneFacet j
  · exact h k hk
  · push_neg at hk
    rw [hx k hk.1, hy k hk.2]

/-- The vertex before facet `i + 1` and the vertex after facet `i`. -/
lemma apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet_aux_notMem (i : Fin 6) :
    apm_t02A04_coneIdx i ∉ apm_t02A04_coneFacet (i + 1) ∧
      apm_t02A04_coneIdx (i + 1 + 1) ∉ apm_t02A04_coneFacet i := by
  fin_cases i <;> decide

/-- Plan: `‖conePoint i x‖ = x_b + x_c =: R` (arc points have norm one), so the radii
agree.  `R = 0` forces both to the centre vertex (`_aux_bary`: `x 0 = 1`).  Otherwise
cancel `R` to get equal arc points, apply `_aux_angle` with `s = x_c / R`, and in each
of the three cases read off all seven coordinates with `_aux_bary`. -/
lemma apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet
    (x y : EuclideanSpace ℝ (Fin 7)) (i j : Fin 6)
    (hxi : x ∈ apm_t02A04_coneHull i) (hyj : y ∈ apm_t02A04_coneHull j)
    (hxy : apm_t02A04_conePoint i x = apm_t02A04_conePoint j y) : x = y := by
  classical
  obtain ⟨hxnonneg, hxsum, hxzero⟩ :=
    apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet_aux_bary i x hxi
  obtain ⟨hynonneg, hysum, hyzero⟩ :=
    apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet_aux_bary j y hyj
  have hbx : 0 ≤ x (apm_t02A04_coneIdx i) := hxnonneg _
  have hcx : 0 ≤ x (apm_t02A04_coneIdx (i + 1)) := hxnonneg _
  have hby : 0 ≤ y (apm_t02A04_coneIdx j) := hynonneg _
  have hcy : 0 ≤ y (apm_t02A04_coneIdx (j + 1)) := hynonneg _
  have hrx : 0 ≤ x (apm_t02A04_coneIdx i) + x (apm_t02A04_coneIdx (i + 1)) := add_nonneg hbx hcx
  have hry : 0 ≤ y (apm_t02A04_coneIdx j) + y (apm_t02A04_coneIdx (j + 1)) := add_nonneg hby hcy
  have hr : x (apm_t02A04_coneIdx i) + x (apm_t02A04_coneIdx (i + 1)) =
      y (apm_t02A04_coneIdx j) + y (apm_t02A04_coneIdx (j + 1)) := by
    have hn := congrArg norm hxy
    simp only [apm_t02A04_conePoint, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
      Real.norm_eq_abs] at hn
    rwa [abs_of_nonneg hrx, abs_of_nonneg hry] at hn
  apply apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet_aux_coords x y i j hxi hyj
  intro k hk
  simp only [apm_t02A04_coneFacet, Finset.mem_insert, Finset.mem_singleton] at hk
  by_cases hr0 : x (apm_t02A04_coneIdx i) + x (apm_t02A04_coneIdx (i + 1)) = 0
  · have hbx0 : x (apm_t02A04_coneIdx i) = 0 := by linarith
    have hcx0 : x (apm_t02A04_coneIdx (i + 1)) = 0 := by linarith
    have hby0 : y (apm_t02A04_coneIdx j) = 0 := by linarith
    have hcy0 : y (apm_t02A04_coneIdx (j + 1)) = 0 := by linarith
    have hxo : ∀ k, k ∈ apm_t02A04_coneFacet i ∨ k ∈ apm_t02A04_coneFacet j → k ≠ 0 → x k = 0 := by
      intro k hk hk0
      by_cases hki : k ∈ apm_t02A04_coneFacet i
      · simp only [apm_t02A04_coneFacet, Finset.mem_insert, Finset.mem_singleton] at hki
        rcases hki with rfl | rfl | rfl
        · exact (hk0 rfl).elim
        · exact hbx0
        · exact hcx0
      · exact hxzero k hki
    have hyo : ∀ k, k ∈ apm_t02A04_coneFacet i ∨ k ∈ apm_t02A04_coneFacet j → k ≠ 0 → y k = 0 := by
      intro k hk hk0
      by_cases hkj : k ∈ apm_t02A04_coneFacet j
      · simp only [apm_t02A04_coneFacet, Finset.mem_insert, Finset.mem_singleton] at hkj
        rcases hkj with rfl | rfl | rfl
        · exact (hk0 rfl).elim
        · exact hby0
        · exact hcy0
      · exact hyzero k hkj
    have hk' : k ∈ apm_t02A04_coneFacet i ∨ k ∈ apm_t02A04_coneFacet j := by
      simp only [apm_t02A04_coneFacet, Finset.mem_insert, Finset.mem_singleton]; exact hk
    by_cases hk0 : k = 0
    · subst hk0; linarith
    · rw [hxo k hk' hk0, hyo k hk' hk0]
  have hrpos : 0 < x (apm_t02A04_coneIdx i) + x (apm_t02A04_coneIdx (i + 1)) :=
    lt_of_le_of_ne hrx (Ne.symm hr0)
  have hrypos : 0 < y (apm_t02A04_coneIdx j) + y (apm_t02A04_coneIdx (j + 1)) := hr ▸ hrpos
  have hs1 : x (apm_t02A04_coneIdx (i + 1)) /
      (x (apm_t02A04_coneIdx i) + x (apm_t02A04_coneIdx (i + 1))) ≤ 1 :=
    (div_le_one hrpos).2 (by linarith)
  have hs1' : y (apm_t02A04_coneIdx (j + 1)) /
      (y (apm_t02A04_coneIdx j) + y (apm_t02A04_coneIdx (j + 1))) ≤ 1 :=
    (div_le_one hrypos).2 (by linarith)
  have harc : apm_t02A04_arcPoint i (x (apm_t02A04_coneIdx (i + 1)) /
        (x (apm_t02A04_coneIdx i) + x (apm_t02A04_coneIdx (i + 1)))) =
      apm_t02A04_arcPoint j (y (apm_t02A04_coneIdx (j + 1)) /
        (y (apm_t02A04_coneIdx j) + y (apm_t02A04_coneIdx (j + 1)))) := by
    apply Subtype.ext
    have hp := hxy
    simp only [apm_t02A04_conePoint] at hp
    rw [show ((y (apm_t02A04_coneIdx j) + y (apm_t02A04_coneIdx (j + 1)) : ℝ) : ℂ) =
      ((x (apm_t02A04_coneIdx i) + x (apm_t02A04_coneIdx (i + 1)) : ℝ) : ℂ) by rw [hr]] at hp
    exact mul_left_cancel₀ (show ((x (apm_t02A04_coneIdx i) + x (apm_t02A04_coneIdx (i + 1)) : ℝ) : ℂ) ≠ 0 by
      exact_mod_cast hr0) hp
  rcases apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet_aux_angle i j _ _
      (div_nonneg hcx hrx) hs1 (div_nonneg hcy hry) hs1' harc with
    ⟨rfl, hss⟩ | ⟨rfl, hsone, hs'zero⟩ | ⟨rfl, hszero, hs'one⟩
  · rw [← hr, div_left_inj' hr0] at hss
    rcases hk with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;> first | exact hss | linarith
  · have hbx0 : x (apm_t02A04_coneIdx i) = 0 := by
      rw [div_eq_one_iff_eq hr0] at hsone; linarith
    have hcy0 : y (apm_t02A04_coneIdx (i + 1 + 1)) = 0 :=
      (div_eq_zero_iff.mp hs'zero).resolve_right (ne_of_gt hrypos)
    have hn := apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet_aux_notMem i
    rcases hk with (rfl | rfl | rfl) | (rfl | rfl | rfl)
    · linarith
    · rw [hbx0, hyzero _ hn.1]
    · linarith
    · linarith
    · linarith
    · rw [hcy0, hxzero _ hn.2]
  · have hcx0 : x (apm_t02A04_coneIdx (j + 1 + 1)) = 0 :=
      (div_eq_zero_iff.mp hszero).resolve_right (ne_of_gt hrpos)
    have hby0 : y (apm_t02A04_coneIdx j) = 0 := by
      rw [div_eq_one_iff_eq (ne_of_gt hrypos)] at hs'one; linarith
    have hn := apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet_aux_notMem j
    rcases hk with (rfl | rfl | rfl) | (rfl | rfl | rfl)
    · linarith
    · linarith
    · rw [hcx0, hyzero _ hn.2]
    · linarith
    · rw [hby0, hxzero _ hn.1]
    · linarith

lemma apm_t02A04_attachedDisk_cone_model_aux_injective : Function.Injective apm_t02A04_coneMap := by
  intro x y hxy
  obtain ⟨i, hxi⟩ := apm_t02A04_attachedDisk_cone_model_aux_cover x x.property
  obtain ⟨j, hyj⟩ := apm_t02A04_attachedDisk_cone_model_aux_cover y y.property
  apply Subtype.ext
  exact apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet x y i j hxi hyj
    (apm_t02A04_attachedDisk_cone_model_aux_injective_aux_conePoint x y i j hxi hyj hxy)

lemma apm_t02A04_attachedDisk_cone_model_aux_surjective_aux_circle
    (z : Circle) : ∃ (i : Fin 6) (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧
      apm_t02A04_arcPoint i t = z := by
  let a := Complex.arg (z : ℂ)
  let u := if a < 0 then a + 2 * Real.pi else a
  have hpi : 0 < Real.pi := Real.pi_pos
  have ha0 : -Real.pi < a := Complex.neg_pi_lt_arg _
  have ha1 : a ≤ Real.pi := Complex.arg_le_pi _
  have hu0 : 0 ≤ u := by
    dsimp [u]
    split_ifs with h
    · linarith
    · linarith
  have hu1 : u ≤ 2 * Real.pi := by
    dsimp [u]
    split_ifs with h <;> linarith
  have hexp : Circle.exp u = z := by
    dsimp [u]
    split_ifs with h
    · rw [Circle.exp_add]
      rw [show Circle.exp (2 * Real.pi) = 1 by
        apply Circle.ext
        simp [Circle.coe_exp, Complex.exp_mul_I]]
      simpa [a] using Circle.exp_arg z
    · exact Circle.exp_arg z
  by_cases h0 : u ≤ Real.pi / 3
  · refine ⟨0, 3 * u / Real.pi, by positivity, ?_, ?_⟩
    · apply (div_le_iff₀ hpi).2; linarith
    · rw [← hexp]
      apply congrArg Circle.exp
      simp [apm_t02A04_arcPoint]
      field_simp
      ring
  by_cases h1 : u ≤ 2 * Real.pi / 3
  · refine ⟨1, 3 * u / Real.pi - 1, ?_, ?_, ?_⟩
    · apply sub_nonneg.2; apply (le_div_iff₀ hpi).2; linarith
    · apply sub_le_iff_le_add.2; apply (div_le_iff₀ hpi).2; linarith
    · rw [← hexp]; apply congrArg Circle.exp
      simp [apm_t02A04_arcPoint]; field_simp; ring
  by_cases h2 : u ≤ Real.pi
  · refine ⟨2, 3 * u / Real.pi - 2, ?_, ?_, ?_⟩
    · apply sub_nonneg.2; apply (le_div_iff₀ hpi).2; linarith
    · apply sub_le_iff_le_add.2; apply (div_le_iff₀ hpi).2; linarith
    · rw [← hexp]; apply congrArg Circle.exp
      simp [apm_t02A04_arcPoint]; field_simp; ring
  by_cases h3 : u ≤ 4 * Real.pi / 3
  · refine ⟨3, 3 * u / Real.pi - 3, ?_, ?_, ?_⟩
    · apply sub_nonneg.2; apply (le_div_iff₀ hpi).2; linarith
    · apply sub_le_iff_le_add.2; apply (div_le_iff₀ hpi).2; linarith
    · rw [← hexp]; apply congrArg Circle.exp
      simp [apm_t02A04_arcPoint]; field_simp; ring
  by_cases h4 : u ≤ 5 * Real.pi / 3
  · refine ⟨4, 3 * u / Real.pi - 4, ?_, ?_, ?_⟩
    · apply sub_nonneg.2; apply (le_div_iff₀ hpi).2; linarith
    · apply sub_le_iff_le_add.2; apply (div_le_iff₀ hpi).2; linarith
    · rw [← hexp]; apply congrArg Circle.exp
      simp [apm_t02A04_arcPoint]; field_simp; ring
  · refine ⟨5, 3 * u / Real.pi - 5, ?_, ?_, ?_⟩
    · apply sub_nonneg.2; apply (le_div_iff₀ hpi).2; linarith
    · apply sub_le_iff_le_add.2; apply (div_le_iff₀ hpi).2; linarith
    · rw [← hexp]; apply congrArg Circle.exp
      simp [apm_t02A04_arcPoint]; field_simp; ring

lemma apm_t02A04_attachedDisk_cone_model_aux_surjective_aux_radial
    (i : Fin 6) (t r : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ y, ((apm_t02A04_coneMap y : apm_t02a04_Disk) : ℂ) =
      (r : ℂ) * (apm_t02A04_arcPoint i t : ℂ) := by
  classical
  let c := ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7 0
  let e := (1 - t) •
      ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7
        (apm_t02A04_coneIdx i) +
    t • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7
        (apm_t02A04_coneIdx (i + 1))
  let y := (1 - r) • c + r • e
  have hc : c ∈ apm_t02A04_coneHull i := by
    apply subset_convexHull ℝ
    simp [c, apm_t02A04_coneFacet]
  have he : e ∈ apm_t02A04_coneHull i := by
    apply segment_subset_convexHull
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
  have hyi : y ∈ apm_t02A04_coneHull i := by
    rw [show y = (1 - r) • c + r • e by rfl]
    exact (convex_convexHull ℝ _).segment_subset hc he
      (by rw [segment_eq_image]; exact ⟨r, ⟨hr0, hr1⟩, rfl⟩)
  have hyspace : y ∈ apm_t02A04_coneComplex.space := by
    apply Geometry.SimplicialComplex.convexHull_subset_space
      (K := apm_t02A04_coneComplex)
      (s := (apm_t02A04_coneFacet i).image
        (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7))
    · refine ⟨⟨apm_t02A04_coneFacet i,
        Finset.mem_image_of_mem _ (Finset.mem_univ _), Finset.Subset.refl _⟩, ?_⟩
      simp [apm_t02A04_coneFacet]
    · exact hyi
  refine ⟨⟨y, hyspace⟩, ?_⟩
  have hcover : ∃ j, y ∈ apm_t02A04_coneHull j := ⟨i, hyi⟩
  simp only [apm_t02A04_coneMap, dif_pos hcover]
  rw [apm_t02A04_attachedDisk_cone_model_aux_agree
    (Classical.choose hcover) i y (Classical.choose_spec hcover) hyi]
  have hnorm := apm_t02A04_attachedDisk_cone_model_aux_point_norm i y hyi
  simp only [ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp, hnorm,
    dite_true]
  by_cases hr : r = 0
  · subst r
    simp [apm_t02A04_conePoint, y, e, c,
      ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex,
      apm_t02A04_coneIdx]
  · have hri : r * (1 - t) + r * t = r := by ring
    simp only [apm_t02A04_conePoint]
    fin_cases i <;>
      simp [y, e, c, apm_t02A04_coneIdx,
        ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex,
        EuclideanSpace.single_apply, hri, hr] <;>
      field_simp <;> ring

lemma apm_t02A04_attachedDisk_cone_model_aux_surjective : Function.Surjective apm_t02A04_coneMap := by
  intro x
  by_cases hx : (x : ℂ) = 0
  · refine ⟨⟨ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7 0,
      apm_t02A04_attachedDisk_cone_model_aux_vertex_mem 0⟩, ?_⟩
    apply Subtype.ext
    simpa [hx, apm_t02A04_coneMap, apm_t02A04_conePoint,
      ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp,
      ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex,
      apm_t02A04_coneIdx]
  · let z : Circle := ⟨(x : ℂ) / ‖(x : ℂ)‖, by
        show _ ∈ Metric.sphere (0 : ℂ) 1
        rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm,
          div_self (norm_ne_zero_iff.mpr hx)]⟩
    obtain ⟨i, t, ht0, ht1, hzt⟩ :=
      apm_t02A04_attachedDisk_cone_model_aux_surjective_aux_circle z
    have hr0 : 0 ≤ ‖(x : ℂ)‖ := norm_nonneg _
    have hr1 : ‖(x : ℂ)‖ ≤ 1 := by
      change ‖(x : ℂ)‖ ≤ 1
      simpa only [apm_t02a04_Disk, Metric.mem_closedBall, dist_zero_right] using x.2
    obtain ⟨y, hy⟩ := apm_t02A04_attachedDisk_cone_model_aux_surjective_aux_radial
      i t ‖(x : ℂ)‖ ht0 ht1 hr0 hr1
    refine ⟨y, Subtype.ext ?_⟩
    rw [hy, hzt]
    change ((‖(x : ℂ)‖ : ℝ) : ℂ) * ((x : ℂ) / ‖(x : ℂ)‖) = x
    have hn : ((‖(x : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
    field_simp

lemma apm_t02A04_attachedDisk_cone_model_aux_centre_map :
    ((apm_t02A04_coneMap ⟨ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7 0, apm_t02A04_attachedDisk_cone_model_aux_vertex_mem 0⟩ : apm_t02a04_Disk) : ℂ) = 0 := by
  simp [apm_t02A04_coneMap, apm_t02A04_conePoint,
    ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp,
    ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex,
    apm_t02A04_coneIdx]

lemma apm_t02A04_attachedDisk_cone_model_aux_edge_map (i : Fin 6) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((apm_t02A04_coneMap ⟨_, apm_t02A04_attachedDisk_cone_model_aux_edge_mem i t ht0 ht1⟩ : apm_t02a04_Disk) : ℂ) =
      ((apm_t02A04_arcPoint i t : Circle) : ℂ) := by
  classical
  let y : EuclideanSpace ℝ (Fin 7) :=
    (1 - t) • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7
        (apm_t02A04_coneIdx i) +
      t • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7
        (apm_t02A04_coneIdx (i + 1))
  have hyi : y ∈ apm_t02A04_coneHull i := by
    apply segment_subset_convexHull
      (show ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7
          (apm_t02A04_coneIdx i) ∈
        (↑((apm_t02A04_coneFacet i).image
          (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7)) :
            Set (EuclideanSpace ℝ (Fin 7))) by
        simp [apm_t02A04_coneFacet])
      (show ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7
          (apm_t02A04_coneIdx (i + 1)) ∈
        (↑((apm_t02A04_coneFacet i).image
          (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7)) :
            Set (EuclideanSpace ℝ (Fin 7))) by
        simp [apm_t02A04_coneFacet])
    rw [segment_eq_image]
    exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
  have hex : ∃ j, y ∈ apm_t02A04_coneHull j := ⟨i, hyi⟩
  let j : Fin 6 := Classical.choose hex
  have hyj : y ∈ apm_t02A04_coneHull j := Classical.choose_spec hex
  have hagree : apm_t02A04_conePoint j y = apm_t02A04_conePoint i y :=
    apm_t02A04_attachedDisk_cone_model_aux_agree j i y hyj hyi
  have hpoint : apm_t02A04_conePoint i y =
      ((apm_t02A04_arcPoint i t : Circle) : ℂ) := by
    fin_cases i <;>
      simp [y, apm_t02A04_conePoint, apm_t02A04_coneIdx,
        ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex,
        EuclideanSpace.single_apply, sub_add_cancel]
  have hnorm : ‖apm_t02A04_conePoint j y‖ ≤ 1 := by
    exact apm_t02A04_attachedDisk_cone_model_aux_point_norm j y hyj
  simp only [apm_t02A04_coneMap]
  rw [dif_pos hex]
  change ((ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp
    (apm_t02A04_conePoint j y) : apm_t02a04_Disk) : ℂ) = _
  simp [ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp,
    hnorm, hagree, hpoint]

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

/-! ### Prism model of the solid torus (claude-14, 2026-10-29)
Vertices `Fin 21`: `prismIdx d w = 3d + w` for a cone vertex `d : Fin 7` and a circle
vertex `w : Fin 3`.  Over cone facet `i` (ordered `0, i, i+1` by `prismDisk i`) and
circle edge `j, j+1`, the prism is cut into the three staircase tetrahedra
`k = 0, 1, 2`: bottom vertices `m ≤ k`, top vertices `m ≥ k`.  A point goes to the
cone point of its disk weights (`diskProj`) and the circle point at angle
`2π(j + s)/3`, `s` = its weight on circle vertex `j + 1`.  The curve edge `i` is the
diagonal from `(i, i mod 3)` to `(i+1, i+1 mod 3)` of the boundary square, which
lies in tetrahedra `k = 1, 2`; along it disk and circle parameters are both `t`. -/

def apm_t02A04_prismIdx (d : Fin 7) (w : Fin 3) : Fin 21 := ⟨3 * d.1 + w.1, by omega⟩

def apm_t02A04_prismDisk (i : Fin 6) : Fin 3 → Fin 7 :=
  ![0, apm_t02A04_coneIdx i, apm_t02A04_coneIdx (i + 1)]

def apm_t02A04_prismFacet (q : Fin 6 × Fin 3 × Fin 3) : Finset (Fin 21) :=
  ((Finset.univ.filter fun m : Fin 3 => m ≤ q.2.2).image
      fun m => apm_t02A04_prismIdx (apm_t02A04_prismDisk q.1 m) q.2.1) ∪
  ((Finset.univ.filter fun m : Fin 3 => q.2.2 ≤ m).image
      fun m => apm_t02A04_prismIdx (apm_t02A04_prismDisk q.1 m) (q.2.1 + 1))

noncomputable def apm_t02A04_prismComplex :
    Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 21)) :=
  ConstructionTargets.RealProjectivePlaneTriangulation.basisComplex 21 (Finset.univ.image apm_t02A04_prismFacet)

def apm_t02A04_prismHull (q : Fin 6 × Fin 3 × Fin 3) : Set (EuclideanSpace ℝ (Fin 21)) :=
  convexHull ℝ ↑((apm_t02A04_prismFacet q).image (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21))

/-- Disk weights: sum over the circle coordinate. -/
noncomputable def apm_t02A04_diskProj (y : EuclideanSpace ℝ (Fin 21)) : EuclideanSpace ℝ (Fin 7) :=
  WithLp.toLp 2 fun d : Fin 7 => ∑ w : Fin 3, y (apm_t02A04_prismIdx d w)

/-- Weight on circle vertex `j + 1`. -/
noncomputable def apm_t02A04_circleWeight (j : Fin 3) (y : EuclideanSpace ℝ (Fin 21)) : ℝ :=
  ∑ d : Fin 7, y (apm_t02A04_prismIdx d (j + 1))

noncomputable def apm_t02A04_circlePoint (j : Fin 3) (y : EuclideanSpace ℝ (Fin 21)) : Circle :=
  Circle.exp (2 * Real.pi * ((j : ℝ) + apm_t02A04_circleWeight j y) / 3)

noncomputable def apm_t02A04_prismPoint (q : Fin 6 × Fin 3 × Fin 3)
    (y : EuclideanSpace ℝ (Fin 21)) : apm_t02a04_SolidTorus :=
  (ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp (apm_t02A04_conePoint q.1 (apm_t02A04_diskProj y)), apm_t02A04_circlePoint q.2.1 y)

noncomputable def apm_t02A04_prismMap (y : apm_t02A04_prismComplex.space) : apm_t02a04_SolidTorus := by
  classical
  exact apm_t02A04_prismPoint
    (if h : ∃ q, (y : EuclideanSpace ℝ (Fin 21)) ∈ apm_t02A04_prismHull q then Classical.choose h
      else (0, 0, 0)) y

/-- Curve vertex `i`: cone vertex `i` over circle vertex `i mod 3`. -/
def apm_t02A04_curveIdx (i : Fin 6) : Fin 21 :=
  apm_t02A04_prismIdx (apm_t02A04_coneIdx i) ⟨i.1 % 3, Nat.mod_lt _ (by decide)⟩

/-- Every point of the complex lies in one of the 54 tetrahedra (as `_cone_model_aux_cover`). -/
lemma apm_t02A04_solidTorus_prism_model_aux_cover (y : EuclideanSpace ℝ (Fin 21))
    (hy : y ∈ apm_t02A04_prismComplex.space) : ∃ q, y ∈ apm_t02A04_prismHull q := by
  classical
  rw [Geometry.SimplicialComplex.mem_space_iff] at hy
  obtain ⟨S, hS, hy⟩ := hy
  have hSb : S ∈ ConstructionTargets.RealProjectivePlaneTriangulation.basisFaces 21
      (Finset.univ.image apm_t02A04_prismFacet) := by
    exact hS.1
  obtain ⟨f, hf, hSf⟩ := hSb
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hf
  refine ⟨q, ?_⟩
  exact convexHull_mono (by exact_mod_cast hSf) hy

lemma apm_t02A04_solidTorus_prism_model_aux_vertex_mem (i : Fin 6) :
    ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21 (apm_t02A04_curveIdx i) ∈ apm_t02A04_prismComplex.space := by
  rw [Geometry.SimplicialComplex.mem_space_iff]
  refine ⟨{ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21
      (apm_t02A04_curveIdx i)},
    ConstructionTargets.RealProjectivePlaneTriangulation.basisComplex_vertex_mem
      (f := apm_t02A04_prismFacet
        (i, ⟨i.1 % 3, Nat.mod_lt _ (by decide)⟩, 1)) ?_ ?_, ?_⟩
  · exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · simp only [apm_t02A04_prismFacet, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and, apm_t02A04_curveIdx]
    left
    refine ⟨1, le_rfl, ?_⟩
    simp [apm_t02A04_prismDisk]
  · simp

/-- The curve edge `i` is an edge of tetrahedron `(i, i mod 3, 1)`. -/
lemma apm_t02A04_solidTorus_prism_model_aux_curve_edge (i : Fin 6) :
    ({ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21 (apm_t02A04_curveIdx i), ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21 (apm_t02A04_curveIdx (i + 1))} :
      Finset (EuclideanSpace ℝ (Fin 21))) ∈ apm_t02A04_prismComplex.faces := by
  classical
  let j : Fin 3 := ⟨i.1 % 3, Nat.mod_lt _ (by decide)⟩
  let q : Fin 6 × Fin 3 × Fin 3 := (i, j, 1)
  refine ⟨⟨apm_t02A04_prismFacet q, ?_, ?_⟩, by simp⟩
  · exact Finset.mem_image_of_mem apm_t02A04_prismFacet (Finset.mem_univ q)
  · intro x hx
    fin_cases i <;>
      simp [apm_t02A04_curveIdx, apm_t02A04_prismFacet,
        apm_t02A04_prismDisk, apm_t02A04_coneIdx, j, q] at hx ⊢ <;>
      rcases hx with rfl | rfl
    all_goals
      first
      | exact ⟨_, Or.inl ⟨1, by decide, rfl⟩, rfl⟩
      | exact ⟨_, Or.inr ⟨2, by decide, rfl⟩, rfl⟩

lemma apm_t02A04_solidTorus_prism_model_aux_edge_mem (i : Fin 6) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21 (apm_t02A04_curveIdx i) +
      t • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21 (apm_t02A04_curveIdx (i + 1)) ∈ apm_t02A04_prismComplex.space := by
  classical
  let q : Fin 6 × Fin 3 × Fin 3 :=
    (i, ⟨i.1 % 3, Nat.mod_lt _ (by decide)⟩, 1)
  have hi : apm_t02A04_curveIdx i ∈ apm_t02A04_prismFacet q := by
    dsimp [q]
    simp only [apm_t02A04_prismFacet, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and, apm_t02A04_curveIdx]
    left
    refine ⟨1, le_rfl, ?_⟩
    simp [apm_t02A04_prismDisk]
  have hj : apm_t02A04_curveIdx (i + 1) ∈ apm_t02A04_prismFacet q := by
    dsimp [q]
    simp only [apm_t02A04_prismFacet, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and]
    right
    refine ⟨2, by decide, ?_⟩
    fin_cases i <;>
      rfl
  apply Geometry.SimplicialComplex.convexHull_subset_space
    (K := apm_t02A04_prismComplex)
    (s := (apm_t02A04_prismFacet q).image
      (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21))
  · refine ⟨⟨apm_t02A04_prismFacet q,
        Finset.mem_image_of_mem _ (Finset.mem_univ q), Finset.Subset.refl _⟩, ?_⟩
    exact Finset.ne_empty_of_mem (Finset.mem_image_of_mem _ hi)
  · apply segment_subset_convexHull
      (show ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21
          (apm_t02A04_curveIdx i) ∈
        ↑((apm_t02A04_prismFacet q).image
          (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21)) by
        exact Finset.mem_image_of_mem _ hi)
      (show ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21
          (apm_t02A04_curveIdx (i + 1)) ∈
        ↑((apm_t02A04_prismFacet q).image
          (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21)) by
        exact Finset.mem_image_of_mem _ hj)
    rw [segment_eq_image]
    exact ⟨t, ⟨ht0, ht1⟩, rfl⟩

/-- A prism vertex projects to its disk vertex: `diskProj` sums the three circle
coordinates of cone vertex `a`, and `basisVertex 21 (3d + w)` has one nonzero coordinate. -/
lemma apm_t02A04_solidTorus_prism_model_aux_proj_vertex (d : Fin 7) (w : Fin 3) :
    apm_t02A04_diskProj (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21
        (apm_t02A04_prismIdx d w)) =
      ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 7 d := by
  ext a
  simp only [apm_t02A04_diskProj, ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex,
    EuclideanSpace.single_apply, apm_t02A04_prismIdx, Fin.ext_iff]
  by_cases had : a.1 = d.1
  · rw [if_pos had]
    rw [Finset.sum_eq_single w]
    · simp [had]
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext (by omega))
    · simp
  · rw [if_neg had]
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro h
    exact had (by omega)

/-- The disk weights of a prism point lie in the cone facet below it (convex hull of the
images of the prism vertices, by `_aux_proj_vertex`). -/
lemma apm_t02A04_solidTorus_prism_model_aux_proj
    (q : Fin 6 × Fin 3 × Fin 3) (y : EuclideanSpace ℝ (Fin 21))
    (hy : y ∈ apm_t02A04_prismHull q) :
    apm_t02A04_diskProj y ∈ apm_t02A04_coneHull q.1 := by
  let L : EuclideanSpace ℝ (Fin 21) →ₗ[ℝ] EuclideanSpace ℝ (Fin 7) :=
      { toFun := apm_t02A04_diskProj
        map_add' := by intro x z; ext d; simp [apm_t02A04_diskProj, Finset.sum_add_distrib]
        map_smul' := by
          intro (c : ℝ) x
          ext d
          simp [apm_t02A04_diskProj, Finset.mul_sum, smul_eq_mul] }
  have hsub : apm_t02A04_prismHull q ⊆ L ⁻¹' apm_t02A04_coneHull q.1 := by
    apply convexHull_min
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
      have hkd : ∃ (d : Fin 3) (w : Fin 3),
          apm_t02A04_prismIdx (apm_t02A04_prismDisk q.1 d) w = k := by
        simp only [apm_t02A04_prismFacet, Finset.mem_union, Finset.mem_image,
          Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rcases hk with ⟨d, -, rfl⟩ | ⟨d, -, rfl⟩
        · exact ⟨d, q.2.1, rfl⟩
        · exact ⟨d, q.2.1 + 1, rfl⟩
      obtain ⟨d, w, rfl⟩ := hkd
      change apm_t02A04_diskProj (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21
        (apm_t02A04_prismIdx (apm_t02A04_prismDisk q.1 d) w)) ∈ apm_t02A04_coneHull q.1
      rw [apm_t02A04_solidTorus_prism_model_aux_proj_vertex]
      apply subset_convexHull ℝ
      apply Finset.mem_coe.mpr
      apply Finset.mem_image_of_mem
      fin_cases d <;> simp [apm_t02A04_coneFacet, apm_t02A04_prismDisk]
    · exact (convex_convexHull ℝ _).linear_preimage L
  exact hsub hy

lemma apm_t02A04_solidTorus_prism_model_aux_agree_aux_zero
    (q : Fin 6 × Fin 3 × Fin 3) (y : EuclideanSpace ℝ (Fin 21))
    (hy : y ∈ apm_t02A04_prismHull q) (k : Fin 21)
    (hk : k ∉ apm_t02A04_prismFacet q) : y k = 0 := by
  let L : EuclideanSpace ℝ (Fin 21) →ₗ[ℝ] ℝ :=
    ((PiLp.proj 2 (fun _ : Fin 21 ↦ ℝ) k).toLinearMap :
      EuclideanSpace ℝ (Fin 21) →ₗ[ℝ] ℝ)
  have hsub : apm_t02A04_prismHull q ⊆ L.ker := by
    apply convexHull_min
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
      change ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21 j k = 0
      simp only [ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex,
        EuclideanSpace.single_apply]
      split_ifs with h
      · subst j
        exact (hk hj).elim
      · rfl
    · exact L.ker.convex
  exact hsub hy

/-- Total mass one, and no weight on circle column `j + 2` (`j = q.2.1`): `convexHull_min`
onto the hyperplane `∑ k, y k = 1`; column `j + 2` lies outside `prismFacet q`, so
`_aux_agree_aux_zero` kills each of its seven coordinates. -/
lemma apm_t02A04_solidTorus_prism_model_aux_agree_aux_mass
    (q : Fin 6 × Fin 3 × Fin 3) (y : EuclideanSpace ℝ (Fin 21))
    (hy : y ∈ apm_t02A04_prismHull q) :
    ∑ k, y k = 1 ∧ apm_t02A04_circleWeight (q.2.1 + 1) y = 0 := by
  classical
  constructor
  · let L : EuclideanSpace ℝ (Fin 21) →ₗ[ℝ] ℝ :=
      { toFun := fun z => ∑ k, z k
        map_add' := by intro x z; simp [Finset.sum_add_distrib]
        map_smul' := by intro c x; simp [Finset.mul_sum, smul_eq_mul] }
    have hsub : apm_t02A04_prismHull q ⊆ {z | L z = 1} := by
      apply convexHull_min
      · intro x hx
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
        simp [L, ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex]
      · exact (convex_singleton (1 : ℝ)).linear_preimage L
    exact hsub hy
  · apply Finset.sum_eq_zero
    intro d _
    apply apm_t02A04_solidTorus_prism_model_aux_agree_aux_zero q y hy
    simp only [apm_t02A04_prismFacet, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rintro (⟨m, -, h⟩ | ⟨m, -, h⟩)
    all_goals
      have hv := congrArg Fin.val h
      simp [apm_t02A04_prismIdx] at hv
      omega

/-- Adjacent circle edges: if `y` lies in prisms over circle edges `j` and `j + 1`, its
weight sits in column `j + 1` only (columns `j` and `j + 2` lie outside one of the two
facets, `_aux_agree_aux_zero`), so with `_aux_mass` the weight on circle vertex `j + 1`
is `1` read on edge `j` and `0` read on edge `j + 1`. -/
lemma apm_t02A04_solidTorus_prism_model_aux_agree_aux_step
    (q q' : Fin 6 × Fin 3 × Fin 3) (y : EuclideanSpace ℝ (Fin 21))
    (hq : y ∈ apm_t02A04_prismHull q) (hq' : y ∈ apm_t02A04_prismHull q')
    (hj : q'.2.1 = q.2.1 + 1) :
    apm_t02A04_circleWeight q.2.1 y = 1 ∧ apm_t02A04_circleWeight q'.2.1 y = 0 := by
  classical
  have hm := (apm_t02A04_solidTorus_prism_model_aux_agree_aux_mass q y hq).1
  have hz := (apm_t02A04_solidTorus_prism_model_aux_agree_aux_mass q y hq).2
  have hz' := (apm_t02A04_solidTorus_prism_model_aux_agree_aux_mass q' y hq').2
  constructor
  · generalize q.2.1 = j at hj hz ⊢
    generalize q'.2.1 = j' at hj hz'
    fin_cases j <;> fin_cases j' <;>
      simp [Fin.sum_univ_succ] at hm <;>
      simp only [apm_t02A04_circleWeight, Fin.sum_univ_succ] at hz hz' ⊢ <;>
      simp at hj <;>
      simp [apm_t02A04_prismIdx] at hz hz' ⊢ <;>
      linarith
  · rw [hj]
    exact (apm_t02A04_solidTorus_prism_model_aux_agree_aux_mass q y hq).2

/-- Case on `q'.2.1 - q.2.1 ∈ {0, 1, 2}`: equal edges are `rfl`; for adjacent edges
`_aux_step` gives angles `2π(j + 1)/3` and `2π(j + 1 + 0)/3` (for `j = 2` the second is
`2π·0/3`, equal modulo `2π`: `Circle.exp_eq_exp`); the third case is the second with
`q, q'` swapped. -/
lemma apm_t02A04_solidTorus_prism_model_aux_agree_aux_circle
    (q q' : Fin 6 × Fin 3 × Fin 3) (y : EuclideanSpace ℝ (Fin 21))
    (hq : y ∈ apm_t02A04_prismHull q) (hq' : y ∈ apm_t02A04_prismHull q') :
    apm_t02A04_circlePoint q.2.1 y = apm_t02A04_circlePoint q'.2.1 y := by
  have hstep : ∀ q q' : Fin 6 × Fin 3 × Fin 3, y ∈ apm_t02A04_prismHull q →
      y ∈ apm_t02A04_prismHull q' → q'.2.1 = q.2.1 + 1 →
        apm_t02A04_circlePoint q.2.1 y = apm_t02A04_circlePoint q'.2.1 y := by
    intro q q' hq hq' hj
    obtain ⟨h1, h0⟩ := apm_t02A04_solidTorus_prism_model_aux_agree_aux_step q q' y hq hq' hj
    unfold apm_t02A04_circlePoint
    rw [h1, h0, hj]
    apply Circle.exp_eq_exp.mpr
    generalize q.2.1 = j
    fin_cases j
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp; ring⟩
    · exact ⟨1, by simp; ring⟩
  have htri : ∀ a b : Fin 3, b = a ∨ b = a + 1 ∨ a = b + 1 := by decide
  rcases htri q.2.1 q'.2.1 with h | h | h
  · rw [h]
  · exact hstep q q' hq hq' h
  · exact (hstep q' q hq' hq h).symm

/-- The point does not depend on the tetrahedron: on a shared face the disk weights lie
in a shared cone face (`_cone_model_aux_agree`), and the circle points agree (same edge,
or circle vertex `j + 1` = weight `1` on edge `j` and weight `0` on edge `j + 1`, both at
angle `2π(j+1)/3`). -/
lemma apm_t02A04_solidTorus_prism_model_aux_agree (q q' : Fin 6 × Fin 3 × Fin 3)
    (y : EuclideanSpace ℝ (Fin 21)) (hq : y ∈ apm_t02A04_prismHull q)
    (hq' : y ∈ apm_t02A04_prismHull q') :
    apm_t02A04_prismPoint q y = apm_t02A04_prismPoint q' y := by
  classical
  have hd := apm_t02A04_attachedDisk_cone_model_aux_agree q.1 q'.1
    (apm_t02A04_diskProj y)
    (apm_t02A04_solidTorus_prism_model_aux_proj q y hq)
    (apm_t02A04_solidTorus_prism_model_aux_proj q' y hq')
  apply Prod.ext
  · exact congrArg ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp hd
  · exact apm_t02A04_solidTorus_prism_model_aux_agree_aux_circle q q' y hq hq'

/-- Along curve edge `i` the disk weights are `(0, 1 - t, t)` on facet `i` and the circle
weight is `t` on edge `i mod 3`, so the image is the curve point (`_cone_model_aux_edge_map`
for the disk factor; `Circle.exp` periodicity for `arcPoint i t ^ 2`).  Evaluate on the
explicit tetrahedron `(i, i mod 3, 1)` and use `_aux_agree` for the chosen one. -/
lemma apm_t02A04_solidTorus_prism_model_aux_edge_map (i : Fin 6) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    apm_t02A04_prismMap ⟨_, apm_t02A04_solidTorus_prism_model_aux_edge_mem i t ht0 ht1⟩ =
      (⟨((apm_t02A04_arcPoint i t : Circle) : ℂ), by
        simpa using (apm_t02A04_arcPoint i t).property.le⟩, apm_t02A04_arcPoint i t ^ 2) := by
  classical
  let y : EuclideanSpace ℝ (Fin 21) :=
    (1 - t) • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21
        (apm_t02A04_curveIdx i) +
      t • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21
        (apm_t02A04_curveIdx (i + 1))
  let j : Fin 3 := ⟨i.1 % 3, Nat.mod_lt _ (by decide)⟩
  let q : Fin 6 × Fin 3 × Fin 3 := (i, j, 1)
  have hi : apm_t02A04_curveIdx i ∈ apm_t02A04_prismFacet q := by
    dsimp [q, j]
    simp only [apm_t02A04_prismFacet, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and, apm_t02A04_curveIdx]
    left
    refine ⟨1, le_rfl, ?_⟩
    simp [apm_t02A04_prismDisk]
  have hi1 : apm_t02A04_curveIdx (i + 1) ∈ apm_t02A04_prismFacet q := by
    dsimp [q, j]
    simp only [apm_t02A04_prismFacet, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and]
    right
    refine ⟨2, by decide, ?_⟩
    fin_cases i <;> rfl
  have hyq : y ∈ apm_t02A04_prismHull q := by
    apply segment_subset_convexHull
      (show ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21
          (apm_t02A04_curveIdx i) ∈
        ↑((apm_t02A04_prismFacet q).image
          (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21)) by
        exact Finset.mem_image_of_mem _ hi)
      (show ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21
          (apm_t02A04_curveIdx (i + 1)) ∈
        ↑((apm_t02A04_prismFacet q).image
          (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21)) by
        exact Finset.mem_image_of_mem _ hi1)
    rw [segment_eq_image]
    exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
  have hex : ∃ q', y ∈ apm_t02A04_prismHull q' := ⟨q, hyq⟩
  let q' := Classical.choose hex
  have hyq' : y ∈ apm_t02A04_prismHull q' := Classical.choose_spec hex
  have hagree : apm_t02A04_prismPoint q' y = apm_t02A04_prismPoint q y :=
    apm_t02A04_solidTorus_prism_model_aux_agree q' q y hyq' hyq
  simp only [apm_t02A04_prismMap]
  rw [dif_pos hex]
  change apm_t02A04_prismPoint q' y = _
  rw [hagree]
  apply Prod.ext
  · apply Subtype.ext
    have hp : apm_t02A04_conePoint i (apm_t02A04_diskProj y) =
        ((apm_t02A04_arcPoint i t : Circle) : ℂ) := by
      fin_cases i <;>
        simp [y, apm_t02A04_diskProj, apm_t02A04_curveIdx,
          apm_t02A04_prismIdx, apm_t02A04_conePoint, apm_t02A04_coneIdx,
          ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex,
          EuclideanSpace.single_apply, Fin.sum_univ_succ, sub_add_cancel]
    simp [apm_t02A04_prismPoint, q, hp,
      ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp]
  · unfold apm_t02A04_prismPoint apm_t02A04_circlePoint
    have hw : apm_t02A04_circleWeight j y = t := by
      fin_cases i <;>
        simp [j, y, apm_t02A04_circleWeight, apm_t02A04_curveIdx,
          apm_t02A04_prismIdx, apm_t02A04_coneIdx,
          ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex,
          Fin.sum_univ_succ]
    change Circle.exp (2 * Real.pi * ((j : ℝ) + apm_t02A04_circleWeight j y) / 3) = _
    rw [hw]
    unfold apm_t02A04_arcPoint
    change Circle.exp (2 * Real.pi * ((j : ℝ) + t) / 3) =
      Circle.exp (2 * Real.pi * ((i : ℝ) + t) / 6) ^ 2
    rw [pow_two, ← Circle.exp_add]
    apply Circle.exp_eq_exp.mpr
    fin_cases i
    · exact ⟨0, by simp [j]; ring⟩
    · exact ⟨0, by simp [j]; ring⟩
    · exact ⟨0, by simp [j]; ring⟩
    · exact ⟨-1, by simp [j]; ring⟩
    · exact ⟨-1, by simp [j]; ring⟩
    · exact ⟨-1, by simp [j]; ring⟩

/-- Pasting over the 54 closed tetrahedra; adjacent tetrahedra give the same point
(shared radial and boundary faces; circle vertex `j + 1` has weight `1` on edge `j` and
`0` on edge `j + 1`, both at angle `2π(j+1)/3`). -/
lemma apm_t02A04_solidTorus_prism_model_aux_continuous_aux_piece (q : Fin 6 × Fin 3 × Fin 3) :
    ContinuousOn (apm_t02A04_prismPoint q) (apm_t02A04_prismHull q) := by
  apply ContinuousOn.prodMk
  · rw [continuousOn_iff_continuous_restrict]
    apply continuous_induced_rng.mpr
    change Continuous (fun y : apm_t02A04_prismHull q ↦
      ((ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp
        (apm_t02A04_conePoint q.1 (apm_t02A04_diskProj y)) : apm_t02a04_Disk) : ℂ))
    have hc : ContinuousOn (fun y ↦
        ((ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp
          (apm_t02A04_conePoint q.1 (apm_t02A04_diskProj y)) : apm_t02a04_Disk) : ℂ))
        (apm_t02A04_prismHull q) :=
      ((apm_t02A04_attachedDisk_cone_model_aux_continuous_piece q.1).comp
      (by
        unfold apm_t02A04_diskProj
        fun_prop : ContinuousOn apm_t02A04_diskProj (apm_t02A04_prismHull q))
      (apm_t02A04_solidTorus_prism_model_aux_proj q)).congr
        (by
          intro y hy
          have hn := apm_t02A04_attachedDisk_cone_model_aux_point_norm q.1
            (apm_t02A04_diskProj y)
            (apm_t02A04_solidTorus_prism_model_aux_proj q y hy)
          simp [ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp, hn])
    exact continuousOn_iff_continuous_restrict.mp hc
  · unfold apm_t02A04_circlePoint apm_t02A04_circleWeight
    fun_prop

lemma apm_t02A04_solidTorus_prism_model_aux_continuous : Continuous apm_t02A04_prismMap := by
  classical
  let C : Fin 6 × Fin 3 × Fin 3 → Set apm_t02A04_prismComplex.space := fun q ↦
    {y | (y : EuclideanSpace ℝ (Fin 21)) ∈ apm_t02A04_prismHull q}
  have hcover : ⋃ q, C q = Set.univ := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact apm_t02A04_solidTorus_prism_model_aux_cover y y.2
  have hclosed : ∀ q, IsClosed (C q) := by
    intro q
    change IsClosed ((fun y : apm_t02A04_prismComplex.space ↦
      (y : EuclideanSpace ℝ (Fin 21))) ⁻¹' apm_t02A04_prismHull q)
    unfold apm_t02A04_prismHull
    simpa only [Finset.coe_image] using
      (((apm_t02A04_prismFacet q).finite_toSet.image
        (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21)).isCompact_convexHull ℝ).isClosed.preimage
          (continuous_subtype_val : Continuous
            (fun y : apm_t02A04_prismComplex.space ↦ (y : EuclideanSpace ℝ (Fin 21))))
  refine (locallyFinite_of_finite C).continuous hcover hclosed ?_
  intro q
  rw [continuousOn_iff_continuous_restrict]
  have hv : Continuous (fun y : C q ↦
      ((y : apm_t02A04_prismComplex.space) : EuclideanSpace ℝ (Fin 21))) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hp : Continuous fun y : C q ↦ apm_t02A04_prismPoint q
      ((y : apm_t02A04_prismComplex.space) : EuclideanSpace ℝ (Fin 21)) := by
    rw [← continuousOn_univ]
    exact (apm_t02A04_solidTorus_prism_model_aux_continuous_aux_piece q).comp
      hv.continuousOn (by intro y _; exact y.2)
  convert hp using 1
  funext y
  change apm_t02A04_prismMap y.1 = _
  unfold apm_t02A04_prismMap
  have hex : ∃ q', ((y.1 : apm_t02A04_prismComplex.space) : EuclideanSpace ℝ (Fin 21)) ∈
      apm_t02A04_prismHull q' := ⟨q, y.2⟩
  rw [dif_pos hex]
  exact apm_t02A04_solidTorus_prism_model_aux_agree _ q _ (Classical.choose_spec hex) y.2

/-! #### Injectivity and surjectivity of the prism map: leaves (claude-14, 2026-10-30)
Notation: for `q = (i, j, k)` the rows are `d m = prismDisk i m` (`m : Fin 3`), the bottom
weights `y (prismIdx (d m) j)` and the top weights `y (prismIdx (d m) (j + 1))`. -/

/-- A point with nonnegative coordinates of total mass one, supported in `F`, lies in the
simplex spanned by `F` (write `y = ∑ k ∈ F, y k • basisVertex k`; `Finset.centerMass_mem_convexHull`). -/
lemma apm_t02A04_solidTorus_prism_model_aux_mem_hull (F : Finset (Fin 21))
    (y : EuclideanSpace ℝ (Fin 21)) (hnn : ∀ k, 0 ≤ y k) (hsum : ∑ k, y k = 1)
    (hF : ∀ k, k ∉ F → y k = 0) :
    y ∈ convexHull ℝ ↑(F.image (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21)) := by
  classical
  have hne : F.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hz : ∀ k, y k = 0 := by
      intro k
      exact hF k (by simp [h])
    simpa [hz] using hsum
  let i₀ : ↑F := ⟨hne.choose, hne.choose_spec⟩
  let z : Fin 21 → EuclideanSpace ℝ (Fin 21) := fun i ↦
    if hi : i ∈ F then
      ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21 i
    else
      ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21 i₀
  apply mem_convexHull_of_exists_fintype (fun i ↦ y i) z
  · exact hnn
  · exact hsum
  · intro i
    simp only [z]
    split_ifs with hi
    · exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, hi, rfl⟩)
    · exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i₀, i₀.property, rfl⟩)
  · rw [show (∑ i, y i • z i) =
        ∑ i, y i • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21 i by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ F
      · simp [z, hi]
      · rw [hF i hi]
        simp]
    apply (EuclideanSpace.equiv (Fin 21) ℝ).injective
    funext k
    simp [ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex,
      Pi.single_apply, eq_comm]

/-- Prism coordinates are nonnegative and the circle weight lies in `[0, 1]`
(`convexHull_min` onto the nonnegative orthant; then `_aux_agree_aux_mass`). -/
lemma apm_t02A04_solidTorus_prism_model_aux_weight_mem (q : Fin 6 × Fin 3 × Fin 3)
    (y : EuclideanSpace ℝ (Fin 21)) (hy : y ∈ apm_t02A04_prismHull q) :
    (∀ k, 0 ≤ y k) ∧ 0 ≤ apm_t02A04_circleWeight q.2.1 y ∧
      apm_t02A04_circleWeight q.2.1 y ≤ 1 := by
  classical
  have hnn : ∀ k, 0 ≤ y k := by
    intro k
    apply (convexHull_min
      (s := (↑((apm_t02A04_prismFacet q).image
        (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21)) :
          Set (EuclideanSpace ℝ (Fin 21))))
      (t := {x | 0 ≤ x k}) ?_ ?_) hy
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      simp [ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex]
      split <;> positivity
    · intro a ha b hb u v hu hv huv
      simp only [Set.mem_setOf_eq] at ha hb ⊢
      simp only [PiLp.add_apply, PiLp.smul_apply]
      positivity
  refine ⟨hnn, ?_, ?_⟩
  · unfold apm_t02A04_circleWeight
    exact Finset.sum_nonneg fun d _ ↦ hnn _
  · have hmass :=
      (apm_t02A04_solidTorus_prism_model_aux_agree_aux_mass q y hy).1
    unfold apm_t02A04_circleWeight
    rw [← hmass]
    rw [← Finset.sum_image]
    · exact Finset.sum_le_univ_sum_of_nonneg hnn
    · intro d _ d' _ h
      have hv := congrArg Fin.val h
      simp [apm_t02A04_prismIdx] at hv
      exact Fin.ext (by omega)

/-- Equal circle points with parameters in `[0, 1]`: same edge and parameter, or the shared
endpoint of adjacent edges. Copy `_cone_model_aux_injective_aux_facet_aux_angle` with
period `3` in place of `6`. -/
lemma apm_t02A04_solidTorus_prism_model_aux_injective_aux_angle (j j' : Fin 3) (s s' : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hs0' : 0 ≤ s') (hs1' : s' ≤ 1)
    (h : Circle.exp (2 * Real.pi * ((j : ℝ) + s) / 3) =
      Circle.exp (2 * Real.pi * ((j' : ℝ) + s') / 3)) :
    (j = j' ∧ s = s') ∨ (j' = j + 1 ∧ s = 1 ∧ s' = 0) ∨ (j = j' + 1 ∧ s = 0 ∧ s' = 1) := by
  set_option maxHeartbeats 2000000 in
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
    have heq : (j : ℝ) + s = (j' : ℝ) + s' + (m : ℝ) * 3 := by
      have hp := Real.pi_pos
      push_cast at hm
      nlinarith
    fin_cases j <;> fin_cases j'
    all_goals
      norm_num at heq
      have hmlo : (-1 : ℤ) ≤ m := by
        exact_mod_cast (show (-1 : ℝ) ≤ (m : ℝ) by linarith)
      have hmhi : m ≤ (1 : ℤ) := by
        exact_mod_cast (show (m : ℝ) ≤ (1 : ℝ) by linarith)
      interval_cases m <;> norm_num at heq
    all_goals
      simp <;> (try constructor) <;> linarith

/-- All weight on circle column `j + 1`: then column `j` is empty (mass one), so the point
is supported on `prismIdx (d m) (j + 1)`, all in the bottom of prism `(i, j + 1, 2)`
(`_aux_mem_hull`), and its weight on column `j + 2` is zero. -/
lemma apm_t02A04_solidTorus_prism_model_aux_top (i : Fin 6) (j k : Fin 3)
    (y : EuclideanSpace ℝ (Fin 21)) (hy : y ∈ apm_t02A04_prismHull (i, j, k))
    (h1 : apm_t02A04_circleWeight j y = 1) :
    y ∈ apm_t02A04_prismHull (i, j + 1, 2) ∧ apm_t02A04_circleWeight (j + 1) y = 0 := by
  classical
  have hnn : ∀ a, 0 ≤ y a := by
    intro a
    let L : EuclideanSpace ℝ (Fin 21) →ₗ[ℝ] ℝ :=
      ((PiLp.proj 2 (fun _ : Fin 21 ↦ ℝ) a).toLinearMap :
        EuclideanSpace ℝ (Fin 21) →ₗ[ℝ] ℝ)
    have hsub : apm_t02A04_prismHull (i, j, k) ⊆ {z | 0 ≤ L z} := by
      apply convexHull_min
      · intro z hz
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hz
        change 0 ≤ ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 21 b a
        by_cases hab : a = b <;>
          simp [ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex, hab]
      · intro x hx z hz p q hp hq hpq
        change 0 ≤ L (p • x + q • z)
        rw [map_add, map_smul, map_smul]
        exact add_nonneg (smul_nonneg hp hx) (smul_nonneg hq hz)
    exact hsub hy
  obtain ⟨hmass, hnext⟩ :=
    apm_t02A04_solidTorus_prism_model_aux_agree_aux_mass (i, j, k) y hy
  constructor
  · apply apm_t02A04_solidTorus_prism_model_aux_mem_hull
      (apm_t02A04_prismFacet (i, j + 1, 2)) y hnn hmass
    intro a ha
    by_cases haold : a ∈ apm_t02A04_prismFacet (i, j, k)
    · simp only [apm_t02A04_prismFacet, Finset.mem_union, Finset.mem_image,
          Finset.mem_filter, Finset.mem_univ, true_and] at haold
      rcases haold with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
      · let S : Finset (Fin 21) := Finset.univ.image
            (fun d : Fin 7 ↦ apm_t02A04_prismIdx d (j + 1))
        have hSinj : Function.Injective
            (fun d : Fin 7 ↦ apm_t02A04_prismIdx d (j + 1)) := by
          intro d e hde
          apply Fin.ext
          have := congrArg Fin.val hde
          simp [apm_t02A04_prismIdx] at this
          omega
        have hSsum : ∑ a ∈ S, y a = 1 := by
          rw [Finset.sum_image]
          · simpa [S, apm_t02A04_circleWeight] using h1
          · exact hSinj.injOn
        have hnotS : apm_t02A04_prismIdx (apm_t02A04_prismDisk i m) j ∉ S := by
          simp only [S, Finset.mem_image, Finset.mem_univ, true_and]
          rintro ⟨d, hd⟩
          have hd' := congrArg Fin.val hd
          simp [apm_t02A04_prismIdx] at hd'
          have hj : (j : Fin 3) ≠ j + 1 := by omega
          exact hj (Fin.ext (by omega))
        have hle : ∑ a ∈ insert
              (apm_t02A04_prismIdx (apm_t02A04_prismDisk i m) j) S, y a ≤
              ∑ a, y a := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.subset_univ _
          · intro a _ _
            exact hnn a
        rw [Finset.sum_insert hnotS, hSsum, hmass] at hle
        linarith [hnn (apm_t02A04_prismIdx (apm_t02A04_prismDisk i m) j)]
      · exfalso
        apply ha
        simp only [apm_t02A04_prismFacet, Finset.mem_union, Finset.mem_image,
          Finset.mem_filter, Finset.mem_univ, true_and]
        left
        exact ⟨m, by omega, rfl⟩
    · exact apm_t02A04_solidTorus_prism_model_aux_agree_aux_zero
        (i, j, k) y hy a haold
  · exact hnext

/-- Change of cone facet. If the disk weights also lie in facet `i'`, the support of `y`
lies in rows of `coneFacet i ∩ coneFacet i'` (`_cone_model_aux_injective_aux_facet_aux_bary`
for both), which keep their relative order, so `y` lies in a prism over `i'` and the same
circle edge (`_aux_mem_hull`). Cases: `i' = i`; `i' = i + 1` (shared rows `0, coneIdx (i+1)`
at positions `0, 2` of `i` and `0, 1` of `i'`: `k' = 0, 0, 1` for `k = 0, 1, 2`);
`i = i' + 1` (symmetric); otherwise only row `0` (`k' = 0`). -/
lemma apm_t02A04_solidTorus_prism_model_aux_reface_aux_row
    (q : Fin 6 × Fin 3 × Fin 3) (i' : Fin 6)
    (y : EuclideanSpace ℝ (Fin 21)) (hy : y ∈ apm_t02A04_prismHull q)
    (hi' : apm_t02A04_diskProj y ∈ apm_t02A04_coneHull i')
    (d : Fin 7) (hd : d ∉ apm_t02A04_coneFacet i') (w : Fin 3) :
    y (apm_t02A04_prismIdx d w) = 0 := by
  have hnn := (apm_t02A04_solidTorus_prism_model_aux_weight_mem q y hy).1
  have hz :=
    (apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet_aux_bary
      i' (apm_t02A04_diskProj y) hi').2.2 d hd
  simp only [apm_t02A04_diskProj, Fin.sum_univ_three] at hz
  have h0 := hnn (apm_t02A04_prismIdx d (0 : Fin 3))
  have h1 := hnn (apm_t02A04_prismIdx d (1 : Fin 3))
  have h2 := hnn (apm_t02A04_prismIdx d (2 : Fin 3))
  have hz0 : y (apm_t02A04_prismIdx d (0 : Fin 3)) = 0 := by linarith
  have hz1 : y (apm_t02A04_prismIdx d (1 : Fin 3)) = 0 := by linarith
  have hz2 : y (apm_t02A04_prismIdx d (2 : Fin 3)) = 0 := by linarith
  fin_cases w <;> assumption

set_option maxHeartbeats 20000000
lemma apm_t02A04_solidTorus_prism_model_aux_reface (q : Fin 6 × Fin 3 × Fin 3) (i' : Fin 6)
    (y : EuclideanSpace ℝ (Fin 21)) (hy : y ∈ apm_t02A04_prismHull q)
    (hi' : apm_t02A04_diskProj y ∈ apm_t02A04_coneHull i') :
    ∃ k', y ∈ apm_t02A04_prismHull (i', q.2.1, k') := by
  classical
  rcases q with ⟨i, j, k⟩
  let k' : Fin 3 :=
    if i' = i then k
    else if i' = i + 1 then if k = 2 then 1 else 0
    else if i = i' + 1 then if k = 0 then 0 else 2
    else 0
  refine ⟨k', apm_t02A04_solidTorus_prism_model_aux_mem_hull _ y
    (apm_t02A04_solidTorus_prism_model_aux_weight_mem (i, j, k) y hy).1
    (apm_t02A04_solidTorus_prism_model_aux_agree_aux_mass (i, j, k) y hy).1 ?_⟩
  intro x hx
  by_cases hxo : x ∈ apm_t02A04_prismFacet (i, j, k)
  · simp only [apm_t02A04_prismFacet, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and] at hxo hx
    rcases hxo with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
    all_goals
      by_cases hii : i' = i
      · subst i'
        exfalso
        apply hx
        simp [k']
        first | exact Or.inl ⟨m, hm, rfl⟩ | exact Or.inr ⟨m, hm, rfl⟩
      apply apm_t02A04_solidTorus_prism_model_aux_reface_aux_row
        (i, j, k) i' y hy hi'
      set_option maxHeartbeats 10000000 in
        fin_cases i <;> fin_cases i' <;> fin_cases j <;> fin_cases k <;> fin_cases m <;>
          simp_all [k', apm_t02A04_prismDisk, apm_t02A04_coneFacet,
            apm_t02A04_coneIdx, apm_t02A04_prismIdx, Fin.forall_fin_succ]
  · exact apm_t02A04_solidTorus_prism_model_aux_agree_aux_zero (i, j, k) y hy x hxo
set_option maxHeartbeats 200000

/-- Staircase uniqueness for three rows: bottom `b`, top `t`, with `t m = 0` below the
step `k` and `b m = 0` above it. Equal row sums `b + t` and equal top mass force equal
tops (`fin_cases k <;> fin_cases k'`, then `linarith` per row). -/
lemma apm_t02A04_solidTorus_prism_model_aux_staircase_real (k k' : Fin 3)
    (b t b' t' : Fin 3 → ℝ) (hb : ∀ m, 0 ≤ b m) (ht : ∀ m, 0 ≤ t m)
    (hb' : ∀ m, 0 ≤ b' m) (ht' : ∀ m, 0 ≤ t' m)
    (hrow : ∀ m, b m + t m = b' m + t' m) (htop : ∑ m, t m = ∑ m, t' m)
    (hk : ∀ m, m < k → t m = 0) (hk2 : ∀ m, k < m → b m = 0)
    (hk' : ∀ m, m < k' → t' m = 0) (hk2' : ∀ m, k' < m → b' m = 0) :
    t = t' := by
  have hr0 := hrow (0 : Fin 3)
  have hr1 := hrow (1 : Fin 3)
  have hr2 := hrow (2 : Fin 3)
  have hn0 := hb (0 : Fin 3)
  have hn1 := hb (1 : Fin 3)
  have hn2 := hb (2 : Fin 3)
  have hnt0 := ht (0 : Fin 3)
  have hnt1 := ht (1 : Fin 3)
  have hnt2 := ht (2 : Fin 3)
  have hn0' := hb' (0 : Fin 3)
  have hn1' := hb' (1 : Fin 3)
  have hn2' := hb' (2 : Fin 3)
  have hnt0' := ht' (0 : Fin 3)
  have hnt1' := ht' (1 : Fin 3)
  have hnt2' := ht' (2 : Fin 3)
  have hz0 := hk (0 : Fin 3)
  have hz1 := hk (1 : Fin 3)
  have hz2 := hk (2 : Fin 3)
  have hbz0 := hk2 (0 : Fin 3)
  have hbz1 := hk2 (1 : Fin 3)
  have hbz2 := hk2 (2 : Fin 3)
  have hz0' := hk' (0 : Fin 3)
  have hz1' := hk' (1 : Fin 3)
  have hz2' := hk' (2 : Fin 3)
  have hbz0' := hk2' (0 : Fin 3)
  have hbz1' := hk2' (1 : Fin 3)
  have hbz2' := hk2' (2 : Fin 3)
  have htop' : t 0 + t 1 + t 2 = t' 0 + t' 1 + t' 2 := by
    simpa [Fin.sum_univ_succ, add_assoc] using htop
  funext m
  fin_cases k <;> fin_cases k' <;> fin_cases m <;>
    simp at hz0 hz1 hz2 hbz0 hbz1 hbz2 hz0' hz1' hz2' hbz0' hbz1' hbz2' <;>
    simp at ⊢ <;>
    linarith

/-- Two points over the same facet and edge with equal disk weights and circle weight are
equal: read `b m = y (prismIdx (d m) j)`, `t m = y (prismIdx (d m) (j + 1))`; the step
conditions and all other coordinates come from `_aux_agree_aux_zero`; apply
`_aux_staircase_real`. -/
lemma apm_t02A04_solidTorus_prism_model_aux_staircase (i : Fin 6) (j k k' : Fin 3)
    (y y' : EuclideanSpace ℝ (Fin 21)) (hy : y ∈ apm_t02A04_prismHull (i, j, k))
    (hy' : y' ∈ apm_t02A04_prismHull (i, j, k'))
    (hd : apm_t02A04_diskProj y = apm_t02A04_diskProj y')
    (hw : apm_t02A04_circleWeight j y = apm_t02A04_circleWeight j y') : y = y' := by
  sorry

/-- The map on a chosen prism: `dif_pos` and `_aux_agree`. -/
lemma apm_t02A04_solidTorus_prism_model_aux_map_eq (q : Fin 6 × Fin 3 × Fin 3)
    (y : apm_t02A04_prismComplex.space)
    (hy : (y : EuclideanSpace ℝ (Fin 21)) ∈ apm_t02A04_prismHull q) :
    apm_t02A04_prismMap y = apm_t02A04_prismPoint q y := by
  classical
  unfold apm_t02A04_prismMap
  have hex : ∃ q', (y : EuclideanSpace ℝ (Fin 21)) ∈ apm_t02A04_prismHull q' := ⟨q, hy⟩
  rw [dif_pos hex]
  exact apm_t02A04_solidTorus_prism_model_aux_agree _ q _ (Classical.choose_spec hex) hy

/-- Equal disk components give equal disk weights: `diskClamp` is the identity on the cone
points (`_cone_model_aux_point_norm` with `_aux_proj`), then
`_cone_model_aux_injective_aux_facet`. -/
lemma apm_t02A04_solidTorus_prism_model_aux_injective_aux_disk (q q' : Fin 6 × Fin 3 × Fin 3)
    (y y' : EuclideanSpace ℝ (Fin 21)) (hy : y ∈ apm_t02A04_prismHull q)
    (hy' : y' ∈ apm_t02A04_prismHull q')
    (h : ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp
        (apm_t02A04_conePoint q.1 (apm_t02A04_diskProj y)) =
      ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp
        (apm_t02A04_conePoint q'.1 (apm_t02A04_diskProj y'))) :
    apm_t02A04_diskProj y = apm_t02A04_diskProj y' := by
  have hyproj : apm_t02A04_diskProj y ∈ apm_t02A04_coneHull q.1 :=
    apm_t02A04_solidTorus_prism_model_aux_proj q y hy
  have hy'proj : apm_t02A04_diskProj y' ∈ apm_t02A04_coneHull q'.1 :=
    apm_t02A04_solidTorus_prism_model_aux_proj q' y' hy'
  have hynorm : ‖apm_t02A04_conePoint q.1 (apm_t02A04_diskProj y)‖ ≤ 1 :=
    apm_t02A04_attachedDisk_cone_model_aux_point_norm q.1
      (apm_t02A04_diskProj y) hyproj
  have hy'norm : ‖apm_t02A04_conePoint q'.1 (apm_t02A04_diskProj y')‖ ≤ 1 :=
    apm_t02A04_attachedDisk_cone_model_aux_point_norm q'.1
      (apm_t02A04_diskProj y') hy'proj
  have hpoint : apm_t02A04_conePoint q.1 (apm_t02A04_diskProj y) =
      apm_t02A04_conePoint q'.1 (apm_t02A04_diskProj y') := by
    simpa only [ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp,
      dif_pos hynorm, dif_pos hy'norm, Subtype.mk.injEq] using h
  exact apm_t02A04_attachedDisk_cone_model_aux_injective_aux_facet
    (apm_t02A04_diskProj y) (apm_t02A04_diskProj y') q.1 q'.1
    hyproj hy'proj hpoint

/-- Every circle point is `Circle.exp (2π(j + s)/3)` with `s ∈ [0, 1]` (as
`_cone_model_aux_surjective_aux_circle`, period `3`). -/
lemma apm_t02A04_solidTorus_prism_model_aux_surjective_aux_circle (c : Circle) :
    ∃ (j : Fin 3) (s : ℝ), 0 ≤ s ∧ s ≤ 1 ∧
      Circle.exp (2 * Real.pi * ((j : ℝ) + s) / 3) = c := by
  sorry

/-- Every disk point is a cone point: `_cone_model_aux_surjective`, a facet from
`_cone_model_aux_cover`, then `_cone_model_aux_agree` and `_cone_model_aux_point_norm`
to remove the choice and the clamp. -/
lemma apm_t02A04_solidTorus_prism_model_aux_surjective_aux_disk (z : apm_t02a04_Disk) :
    ∃ (i : Fin 6) (x : EuclideanSpace ℝ (Fin 7)), x ∈ apm_t02A04_coneHull i ∧
      apm_t02A04_conePoint i x = (z : ℂ) := by
  sorry

/-- Staircase existence for three rows: for row sums `a ≥ 0` with `∑ a = 1` and
`s ∈ [0, 1]` there is a step `k` and a split `a = b + t` with `∑ t = s` (take `k` with
`∑_{m > k} a m ≤ s ≤ ∑_{m ≥ k} a m`; `t m = a m` above `k`, `0` below). -/
lemma apm_t02A04_solidTorus_prism_model_aux_staircase_exists (a : Fin 3 → ℝ)
    (ha : ∀ m, 0 ≤ a m) (hsum : ∑ m, a m = 1) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ (k : Fin 3) (b t : Fin 3 → ℝ), (∀ m, 0 ≤ b m) ∧ (∀ m, 0 ≤ t m) ∧
      (∀ m, b m + t m = a m) ∧ ∑ m, t m = s ∧
      (∀ m, m < k → t m = 0) ∧ (∀ m, k < m → b m = 0) := by
  sorry

/-- A prism point with given disk weights and circle weight: apply
`_aux_staircase_exists` to `a m = x (prismDisk i m)` (`_cone_model_aux_injective_aux_facet_aux_bary`),
put `b m` at `prismIdx (d m) j` and `t m` at `prismIdx (d m) (j + 1)`, and use
`_aux_mem_hull` for membership. -/
lemma apm_t02A04_solidTorus_prism_model_aux_surjective_aux_build (i : Fin 6) (j : Fin 3)
    (x : EuclideanSpace ℝ (Fin 7)) (hx : x ∈ apm_t02A04_coneHull i) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 21)), y ∈ apm_t02A04_prismHull (i, j, k) ∧
      apm_t02A04_diskProj y = x ∧ apm_t02A04_circleWeight j y = s := by
  sorry

/-- Staircase uniqueness: the disk weights `a` (cumulative `A_m`) and the circle weight
determine the tetrahedron and all its weights (`y (m, bottom) = max 0 (min A_m (1-s) - A_{m-1})`);
injectivity of the cone point and of `Circle.exp` on one turn give equal weights. -/
lemma apm_t02A04_solidTorus_prism_model_aux_injective : Function.Injective apm_t02A04_prismMap := by
  sorry

/-- Staircase existence: for a disk point (`_cone_model_aux_surjective`) and a circle point
at parameter `s` on edge `j`, the same formula gives a point of the prism. -/
lemma apm_t02A04_solidTorus_prism_model_aux_surjective : Function.Surjective apm_t02A04_prismMap := by
  sorry

theorem apm_t02A04_solidTorus_prism_model
    (C : apm_t02A04_CircleSubdivision) :
    Nonempty (apm_t02A04_SolidPrismModel C) := by
  classical
  letI : CompactSpace apm_t02A04_prismComplex.space :=
    isCompact_iff_compactSpace.mp
      (ConstructionTargets.RealProjectivePlaneTriangulation.finite_simplicialComplex_space_isCompact _ (ConstructionTargets.RealProjectivePlaneTriangulation.basisComplex_faces_finite 21 _))
  let e : apm_t02A04_prismComplex.space ≃ₜ apm_t02a04_SolidTorus :=
    apm_t02A04_solidTorus_prism_model_aux_continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective _ ⟨apm_t02A04_solidTorus_prism_model_aux_injective,
        apm_t02A04_solidTorus_prism_model_aux_surjective⟩)
  refine ⟨⟨21, apm_t02A04_prismComplex,
    fun i => ⟨_, apm_t02A04_solidTorus_prism_model_aux_vertex_mem i⟩, e,
    ConstructionTargets.RealProjectivePlaneTriangulation.basisComplex_faces_finite 21 _, ?_, ?_, ?_, ?_⟩⟩
  · -- curveVertex_injective
    intro i j hij
    have h := apm_t02A04_attachedDisk_cone_model_aux_basisVertex_injective 21 (congrArg Subtype.val hij)
    have h' := congrArg Fin.val h
    simp [apm_t02A04_curveIdx, apm_t02A04_prismIdx, apm_t02A04_coneIdx] at h'
    exact Fin.ext (by omega)
  · -- curveVertex_eq
    intro i
    have h0 := apm_t02A04_solidTorus_prism_model_aux_edge_map i 0 le_rfl zero_le_one
    have hv : (⟨_, apm_t02A04_solidTorus_prism_model_aux_edge_mem i 0 le_rfl zero_le_one⟩ :
        apm_t02A04_prismComplex.space) = ⟨_, apm_t02A04_solidTorus_prism_model_aux_vertex_mem i⟩ :=
      Subtype.ext (by simp)
    rw [hv] at h0
    change apm_t02A04_prismMap _ = _
    rw [h0]
    have hs := C.source_eq i
    ext
    · simp [hs]
    · simp [hs]
  · -- curve_edge
    exact apm_t02A04_solidTorus_prism_model_aux_curve_edge
  · -- curve_affine
    intro i t ht0 ht1
    have hsymm : e.symm (⟨((apm_t02A04_arcPoint i t : Circle) : ℂ), by
        simpa using (apm_t02A04_arcPoint i t).property.le⟩, apm_t02A04_arcPoint i t ^ 2) =
        ⟨_, apm_t02A04_solidTorus_prism_model_aux_edge_mem i t ht0 ht1⟩ := by
      rw [Homeomorph.symm_apply_eq]
      exact (apm_t02A04_solidTorus_prism_model_aux_edge_map i t ht0 ht1).symm
    rw [hsymm]

/-! ### The glued complex (claude-14, 2026-10-30)
Vertices `Fin 22`: prism vertex `k` is `k.castSucc`, the disk centre is `Fin.last 21`, and
disk boundary vertex `coneIdx i` is the curve vertex `curveIdx i`. The facets are the 54
prism facets and the 6 cone facets. A point of a prism hull goes to the solid torus by
`prismPoint`, a point of a cone hull to the disk by `conePoint`; the two kinds of hull meet
only along the curve edges, where `Glue.boundary` identifies the images. -/

def apm_t02A04_gluedIdxD : Fin 7 → Fin 22 :=
  Fin.cases (Fin.last 21) (fun i : Fin 6 => (apm_t02A04_curveIdx i).castSucc)

def apm_t02A04_gluedPrismFacet (q : Fin 6 × Fin 3 × Fin 3) : Finset (Fin 22) :=
  (apm_t02A04_prismFacet q).map Fin.castSuccEmb

def apm_t02A04_gluedConeFacet (i : Fin 6) : Finset (Fin 22) :=
  (apm_t02A04_coneFacet i).image apm_t02A04_gluedIdxD

noncomputable def apm_t02A04_gluedComplex : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 22)) :=
  ConstructionTargets.RealProjectivePlaneTriangulation.basisComplex 22
    (Finset.univ.image apm_t02A04_gluedPrismFacet ∪ Finset.univ.image apm_t02A04_gluedConeFacet)

def apm_t02A04_gluedPrismHull (q : Fin 6 × Fin 3 × Fin 3) : Set (EuclideanSpace ℝ (Fin 22)) :=
  convexHull ℝ ↑((apm_t02A04_gluedPrismFacet q).image (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 22))

def apm_t02A04_gluedConeHull (i : Fin 6) : Set (EuclideanSpace ℝ (Fin 22)) :=
  convexHull ℝ ↑((apm_t02A04_gluedConeFacet i).image (ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 22))

noncomputable def apm_t02A04_projS (z : EuclideanSpace ℝ (Fin 22)) : EuclideanSpace ℝ (Fin 21) :=
  WithLp.toLp 2 fun k => z k.castSucc

noncomputable def apm_t02A04_projD (z : EuclideanSpace ℝ (Fin 22)) : EuclideanSpace ℝ (Fin 7) :=
  WithLp.toLp 2 fun d => z (apm_t02A04_gluedIdxD d)

noncomputable def apm_t02A04_liftS (y : EuclideanSpace ℝ (Fin 21)) : EuclideanSpace ℝ (Fin 22) :=
  WithLp.toLp 2 fun k => if h : k = Fin.last 21 then 0 else y (k.castPred h)

noncomputable def apm_t02A04_liftD (x : EuclideanSpace ℝ (Fin 7)) : EuclideanSpace ℝ (Fin 22) :=
  ∑ d, x d • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 22 (apm_t02A04_gluedIdxD d)

noncomputable def apm_t02A04_gluedMap (z : apm_t02A04_gluedComplex.space) : apm_t02a04_X := by
  classical
  exact if h : ∃ q, (z : EuclideanSpace ℝ (Fin 22)) ∈ apm_t02A04_gluedPrismHull q then
      apm_t02a04_solidInclusion (apm_t02A04_prismPoint (Classical.choose h) (apm_t02A04_projS z))
    else apm_t02a04_diskInclusion (ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp (apm_t02A04_conePoint
      (if h' : ∃ i, (z : EuclideanSpace ℝ (Fin 22)) ∈ apm_t02A04_gluedConeHull i then Classical.choose h' else 0)
      (apm_t02A04_projD z)))

/-- `gluedIdxD` on boundary vertices (`fin_cases i <;> rfl`), and it is injective
(`decide`). -/
lemma apm_t02A04_quotientComplex_model_aux_idx :
    (∀ i : Fin 6, apm_t02A04_gluedIdxD (apm_t02A04_coneIdx i) = (apm_t02A04_curveIdx i).castSucc) ∧
      Function.Injective apm_t02A04_gluedIdxD := by
  sorry

/-- Every point of the glued complex lies in a prism hull or a cone hull (as
`_prism_model_aux_cover`). -/
lemma apm_t02A04_quotientComplex_model_aux_cover (z : EuclideanSpace ℝ (Fin 22))
    (hz : z ∈ apm_t02A04_gluedComplex.space) :
    (∃ q, z ∈ apm_t02A04_gluedPrismHull q) ∨ ∃ i, z ∈ apm_t02A04_gluedConeHull i := by
  sorry

/-- Restriction to the prism coordinates: `projS` is linear and sends `basisVertex 22
k.castSucc` to `basisVertex 21 k` (`convexHull_min`, as `_prism_model_aux_proj`); and
`liftS` is a right inverse that maps prism hulls into glued prism hulls. -/
lemma apm_t02A04_quotientComplex_model_aux_prism_coords (q : Fin 6 × Fin 3 × Fin 3) :
    (∀ z ∈ apm_t02A04_gluedPrismHull q, apm_t02A04_projS z ∈ apm_t02A04_prismHull q ∧
        apm_t02A04_liftS (apm_t02A04_projS z) = z) ∧
      ∀ y ∈ apm_t02A04_prismHull q, apm_t02A04_liftS y ∈ apm_t02A04_gluedPrismHull q ∧
        apm_t02A04_projS (apm_t02A04_liftS y) = y := by
  sorry

/-- The same for the cone coordinates, with `projD`, `liftD` and `gluedIdxD` injective
(`_aux_idx`). -/
lemma apm_t02A04_quotientComplex_model_aux_cone_coords (i : Fin 6) :
    (∀ z ∈ apm_t02A04_gluedConeHull i, apm_t02A04_projD z ∈ apm_t02A04_coneHull i ∧
        apm_t02A04_liftD (apm_t02A04_projD z) = z) ∧
      ∀ x ∈ apm_t02A04_coneHull i, apm_t02A04_liftD x ∈ apm_t02A04_gluedConeHull i ∧
        apm_t02A04_projD (apm_t02A04_liftD x) = x := by
  sorry

/-- A prism hull and a cone hull meet only on the curve edge `i`: the only vertices of
`gluedConeFacet i` that are prism vertices are `(curveIdx i).castSucc` and
`(curveIdx (i + 1)).castSucc` (the centre is `Fin.last 21`); points of both hulls vanish
off both facets and have mass one. -/
lemma apm_t02A04_quotientComplex_model_aux_overlap (q : Fin 6 × Fin 3 × Fin 3) (i : Fin 6)
    (z : EuclideanSpace ℝ (Fin 22)) (hq : z ∈ apm_t02A04_gluedPrismHull q) (hi : z ∈ apm_t02A04_gluedConeHull i) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      z = (1 - t) • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 22 (apm_t02A04_curveIdx i).castSucc +
        t • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 22 (apm_t02A04_curveIdx (i + 1)).castSucc := by
  sorry

/-- On curve edge `i` the two formulas give the same point of `X`: the prism side is
`(arcPoint i t, arcPoint i t ^ 2)` (`_prism_model_aux_edge_map` with `_aux_map_eq`), the
cone side is `arcPoint i t` (`_cone_model_aux_edge_map`, `_cone_model_aux_agree`), and
`apm_t02a04_mk_disk_boundary_eq_mk_attachingCurve` identifies them. -/
lemma apm_t02A04_quotientComplex_model_aux_edge_eq (q : Fin 6 × Fin 3 × Fin 3) (i i' : Fin 6)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hq : (1 - t) • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 22 (apm_t02A04_curveIdx i).castSucc +
        t • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 22 (apm_t02A04_curveIdx (i + 1)).castSucc ∈ apm_t02A04_gluedPrismHull q)
    (hi' : (1 - t) • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 22 (apm_t02A04_curveIdx i).castSucc +
        t • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 22 (apm_t02A04_curveIdx (i + 1)).castSucc ∈ apm_t02A04_gluedConeHull i') :
    apm_t02a04_solidInclusion (apm_t02A04_prismPoint q (apm_t02A04_projS
        ((1 - t) • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 22 (apm_t02A04_curveIdx i).castSucc +
          t • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 22 (apm_t02A04_curveIdx (i + 1)).castSucc))) =
      apm_t02a04_diskInclusion (ConstructionTargets.RealProjectivePlaneTriangulation.diskClamp (apm_t02A04_conePoint i' (apm_t02A04_projD
        ((1 - t) • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 22 (apm_t02A04_curveIdx i).castSucc +
          t • ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 22 (apm_t02A04_curveIdx (i + 1)).castSucc)))) := by
  sorry

/-- Points of `X`: `solidInclusion` and `diskInclusion` are injective, and they meet only
at `(z, z ^ 2)` against `z` for `z` on the circle. Use `apm_t02a04_gluedDesc_respects`
with invariants of the relation (for instance `Sum.elim` of the identity and
`fun d ↦ (d, d ^ 2)` on the circle, read in `SolidTorus ⊕ Disk`). -/
lemma apm_t02A04_quotientComplex_model_aux_inclusions :
    Function.Injective apm_t02a04_solidInclusion ∧
      Function.Injective apm_t02a04_diskInclusion ∧
      ∀ s d, apm_t02a04_solidInclusion s = apm_t02a04_diskInclusion d →
        ∃ c : Circle, (d : ℂ) = c ∧ s = (⟨(c : ℂ), by simpa using c.property.le⟩, c ^ 2) := by
  sorry

/-- The centre: `basisVertex 22 (Fin.last 21)` is a vertex of the glued complex, lies in no
prism hull (its last coordinate is `1`, prism hull points have `0` there), lies in cone
hull `0`, and goes to `diskInclusion 0`. -/
lemma apm_t02A04_quotientComplex_model_aux_centre :
    ∃ hv : ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 22 (Fin.last 21) ∈ apm_t02A04_gluedComplex.space,
      {ConstructionTargets.RealProjectivePlaneTriangulation.basisVertex 22 (Fin.last 21)} ∈ apm_t02A04_gluedComplex.faces ∧
      apm_t02A04_gluedMap ⟨_, hv⟩ =
        apm_t02a04_diskInclusion ⟨0, by simp [apm_t02a04_Disk]⟩ := by
  sorry

/-- Pasting over the 60 closed hulls (as `_prism_model_aux_continuous`): on a prism hull
`gluedMap` is `solidInclusion ∘ prismPoint q ∘ projS` (`_prism_model_aux_agree`,
`_prism_model_aux_continuous_aux_piece`); on a cone hull it is
`diskInclusion ∘ diskClamp ∘ conePoint i ∘ projD`, using `_aux_overlap` and `_aux_edge_eq`
where the cone hull meets a prism hull. -/
lemma apm_t02A04_quotientComplex_model_aux_continuous : Continuous apm_t02A04_gluedMap := by
  sorry

/-- Injectivity: two prism points by `_prism_model_aux_injective` and `_aux_prism_coords`;
two cone points by `_cone_model_aux_injective` and `_aux_cone_coords`; a prism point and a
cone point with the same image map to `(c, c ^ 2)` and `c` (`_aux_inclusions`), so both are
the curve point over `c` (`_cone_model_aux_surjective_aux_circle`, the two `_edge_map`s and
the two injectivities), equal in the glued complex. -/
lemma apm_t02A04_quotientComplex_model_aux_injective :
    Function.Injective apm_t02A04_gluedMap := by
  sorry

/-- Surjectivity: points of `X` are `solidInclusion s` or `diskInclusion d`
(`Quotient.ind`); lift a preimage under `prismMap` (`_prism_model_aux_surjective`) or
`coneMap` with `_aux_prism_coords` or `_aux_cone_coords`. -/
lemma apm_t02A04_quotientComplex_model_aux_surjective :
    Function.Surjective apm_t02A04_gluedMap := by
  sorry

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
  obtain ⟨hv, hface, hmark⟩ := apm_t02A04_quotientComplex_model_aux_centre
  exact ⟨⟨22, apm_t02A04_gluedComplex, ⟨_, hv⟩, apm_t02A04_gluedMap⟩,
    ConstructionTargets.RealProjectivePlaneTriangulation.basisComplex_faces_finite 22 _,
    hface, hmark, apm_t02A04_quotientComplex_model_aux_continuous,
    apm_t02A04_quotientComplex_model_aux_injective,
    apm_t02A04_quotientComplex_model_aux_surjective⟩

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
  exact ConstructionTargets.LefschetzFixedPoint.fixedPointOfNonzeroLefschetz
    apm_t02A04_isFinitePolyhedron f (hL f) one_ne_zero

theorem apm_t02a04 :
    ∀ f : apm_t02a04_X → apm_t02a04_X,
      Continuous f → ∃ x, f x = x := by
  intro f hf
  exact apm_t02A04_fixed_point_of_lefschetz
    (apm_t02A04_lefschetz_number apm_t02A04_rational_homology) ⟨f, hf⟩

#print axioms apm_t02a04
