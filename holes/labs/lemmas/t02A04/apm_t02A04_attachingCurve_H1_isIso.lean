import Mathlib
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.CoefficientH0
import ConstructionTargets.AttachTwoCell
import ConstructionTargets.CP2RationalHomology
import ConstructionTargets.T00A01MayerVietorisAdapters
import ConstructionTargets.SingularHomologyConcrete

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
theorem apm_t02A04_compatibleOpenCover :
    Nonempty apm_t02A04_CompatibleOpenCover := by
  sorry

/-- The concrete quotient is path-connected. -/
theorem apm_t02A04_pathConnected : PathConnectedSpace apm_t02a04_X := by
  sorry

/-- In rational `H₁`, the attaching loop has invertible degree two. -/
-- BEGIN SEAT AREA
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
-- END SEAT AREA

/-- The degree-one Mayer--Vietoris calculation for a compatible cover. -/
theorem apm_t02A04_H1_zero_of_cover
    (C : apm_t02A04_CompatibleOpenCover)
    (hdegree : CategoryTheory.IsIso (induced apm_t02A04_attachingCurve 1)) :
    CategoryTheory.Limits.IsZero (apm_t02A04_HQ 1) := by
  sorry

/-- The degree-two Mayer--Vietoris calculation: injectivity kills the kernel. -/
theorem apm_t02A04_H2_zero_of_cover
    (C : apm_t02A04_CompatibleOpenCover)
    (hdegree : CategoryTheory.IsIso (induced apm_t02A04_attachingCurve 1)) :
    CategoryTheory.Limits.IsZero (apm_t02A04_HQ 2) := by
  sorry

/-- Mayer--Vietoris above the dimensions of the circle and solid torus. -/
theorem apm_t02A04_Hhigh_zero_of_cover
    (C : apm_t02A04_CompatibleOpenCover) (k : ℕ) (hk : 3 ≤ k) :
    CategoryTheory.Limits.IsZero (apm_t02A04_HQ k) := by
  sorry

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

/-- **LIBRARY.** Specialized compact-polyhedron Lefschetz implication. -/
theorem apm_t02A04_fixed_point_of_lefschetz
    (hL : ∀ f : C(apm_t02a04_X, apm_t02a04_X), HasLefschetzNumber f 1) :
    ∀ f : C(apm_t02a04_X, apm_t02a04_X), ∃ x, f x = x := by
  sorry

theorem apm_t02a04 :
    ∀ f : apm_t02a04_X → apm_t02a04_X,
      Continuous f → ∃ x, f x = x := by
  intro f hf
  exact apm_t02A04_fixed_point_of_lefschetz
    (apm_t02A04_lefschetz_number apm_t02A04_rational_homology) ⟨f, hf⟩

#print axioms apm_t02a04
