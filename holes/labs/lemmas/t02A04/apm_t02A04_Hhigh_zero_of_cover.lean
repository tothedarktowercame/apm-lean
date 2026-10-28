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
theorem apm_t02A04_attachingCurve_H1_isIso :
    CategoryTheory.IsIso (induced apm_t02A04_attachingCurve 1) := by
  sorry

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
-- BEGIN SEAT AREA
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
-- END SEAT AREA

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
