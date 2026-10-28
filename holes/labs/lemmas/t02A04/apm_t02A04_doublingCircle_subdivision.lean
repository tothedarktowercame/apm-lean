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
theorem apm_t02A04_gluingSetoid_isClosed :
    IsClosed {p : (Sum apm_t02a04_SolidTorus apm_t02a04_Disk) ×
        (Sum apm_t02a04_SolidTorus apm_t02a04_Disk) |
      apm_t02A04_gluingSetoid.r p.1 p.2} := by
  sorry

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

-- BEGIN SEAT AREA
theorem apm_t02A04_doublingCircle_subdivision :
    Nonempty apm_t02A04_CircleSubdivision := by
  sorry
-- END SEAT AREA

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
