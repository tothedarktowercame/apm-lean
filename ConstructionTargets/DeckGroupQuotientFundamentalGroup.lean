import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocPathConnected

open Topology

namespace ConstructionTargets.DeckGroupQuotientFundamentalGroup

/-- The orbit projection of a free properly discontinuous action is a covering
map under the separation and local compactness hypotheses used by Mathlib's
quotient-covering construction. -/
theorem quotientMk_isCoveringMap
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
    [LocallyCompactSpace X] [T2Space X]
    (free : ∀ g : G, ∀ x : X, g • x = x → g = 1) :
    IsCoveringMap
      (Quotient.mk (MulAction.orbitRel G X) :
        X → MulAction.orbitRel.Quotient G X) := by
  letI : IsCancelSMul G X :=
    isCancelSMul_iff_eq_one_of_smul_eq.mpr free
  exact
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
      (G := G) (E := X)).isCoveringMap

/-- A quotient covering's fiber over `f e` is canonically coordinated by the
acting group: `g` corresponds to the point `g • e`. -/
noncomputable def quotientCoveringOrbitFiberEquiv
    {G E X : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace X]
    [MulAction G E] {f : E → X} (h : IsQuotientCoveringMap f G) (e : E) :
    G ≃ f ⁻¹' {f e} :=
  Equiv.ofBijective
    (fun g ↦ ⟨g • e, by
      change f (g • e) = f e
      exact h.apply_eq_iff_mem_orbit.mpr ⟨g, rfl⟩⟩)
    ⟨fun g g' eq ↦ by
        apply h.isCancelSMul.right_cancel g g' e
        exact congrArg Subtype.val eq,
      fun y ↦ by
        have hy : f y.1 = f e := by
          simpa only [Set.mem_preimage, Set.mem_singleton_iff] using y.property
        obtain ⟨g, hg⟩ := (@h.apply_eq_iff_mem_orbit y.1 e).mp hy
        exact ⟨g, Subtype.ext hg⟩⟩

@[simp] theorem quotientCoveringOrbitFiberEquiv_apply
    {G E X : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace X]
    [MulAction G E] {f : E → X} (h : IsQuotientCoveringMap f G) (e : E) (g : G) :
    (quotientCoveringOrbitFiberEquiv h e g : E) = g • e := rfl

/-- The fiber of the repaired program's orbit projection, expressed in the
acting group's coordinates. -/
noncomputable def orbitQuotientFiberEquiv
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
    [LocallyCompactSpace X] [T2Space X]
    (free : ∀ g : G, ∀ x : X, g • x = x → g = 1) (x : X) :
    G ≃ (Quotient.mk (MulAction.orbitRel G X) :
      X → MulAction.orbitRel.Quotient G X) ⁻¹' {Quotient.mk _ x} := by
  letI : IsCancelSMul G X :=
    isCancelSMul_iff_eq_one_of_smul_eq.mpr free
  exact quotientCoveringOrbitFiberEquiv
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
      (G := G) (E := X)) x

@[simp] theorem orbitQuotientFiberEquiv_apply
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
    [LocallyCompactSpace X] [T2Space X]
    (free : ∀ g : G, ∀ x : X, g • x = x → g = 1) (x : X) (g : G) :
    (orbitQuotientFiberEquiv free x g : X) = g • x := rfl

/-- Every deck translation is the unique global lift of the orbit projection
that takes the chosen basepoint to the corresponding point of its orbit.  The
global lifting theorem is where local path-connectedness enters the repaired
program. -/
theorem orbitProjection_existsUnique_lift
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
    [LocallyCompactSpace X] [T2Space X] [SimplyConnectedSpace X]
    [LocPathConnectedSpace X]
    (free : ∀ g : G, ∀ x : X, g • x = x → g = 1) (x : X) (g : G) :
    ∃! F : C(X, X), F x = g • x ∧
      Quotient.mk (MulAction.orbitRel G X) ∘ F =
        Quotient.mk (MulAction.orbitRel G X) := by
  let q : C(X, MulAction.orbitRel.Quotient G X) :=
    ⟨Quotient.mk (MulAction.orbitRel G X), continuous_quotient_mk'⟩
  exact (quotientMk_isCoveringMap free).existsUnique_continuousMap_lifts
    q x (g • x) (by
      change Quotient.mk (MulAction.orbitRel G X) (g • x) =
        Quotient.mk (MulAction.orbitRel G X) x
      exact Quotient.sound ⟨g, rfl⟩)

/-- Monodromy of an orbit-covering loop commutes with translation by a deck
transformation. -/
theorem orbitMonodromy_deck_equivariant
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
    [LocallyCompactSpace X] [T2Space X] [SimplyConnectedSpace X]
    [LocPathConnectedSpace X]
    (free : ∀ g : G, ∀ x : X, g • x = x → g = 1) (x : X)
    (γ : FundamentalGroup (MulAction.orbitRel.Quotient G X) (Quotient.mk _ x))
    (g : G) :
    (((quotientMk_isCoveringMap free).monodromy
        (FundamentalGroup.toPath γ) (orbitQuotientFiberEquiv free x g) :
          (Quotient.mk (MulAction.orbitRel G X) :
            X → MulAction.orbitRel.Quotient G X) ⁻¹' {Quotient.mk _ x}) : X) =
      g • (((quotientMk_isCoveringMap free).monodromy
        (FundamentalGroup.toPath γ) ⟨x, rfl⟩ :
          (Quotient.mk (MulAction.orbitRel G X) :
            X → MulAction.orbitRel.Quotient G X) ⁻¹' {Quotient.mk _ x}) : X) := by
  let q : C(X, MulAction.orbitRel.Quotient G X) :=
    ⟨Quotient.mk (MulAction.orbitRel G X), continuous_quotient_mk'⟩
  let cov := quotientMk_isCoveringMap free
  obtain ⟨F, hF, huniq⟩ := orbitProjection_existsUnique_lift free x g
  let T : C(X, X) := ⟨fun y ↦ g • y, continuous_const_smul g⟩
  have hT : T x = g • x ∧
      Quotient.mk (MulAction.orbitRel G X) ∘ T =
        Quotient.mk (MulAction.orbitRel G X) := by
    refine ⟨rfl, funext fun y ↦ ?_⟩
    exact Quotient.sound ⟨g, rfl⟩
  have hFT : F = T := (huniq T hT).symm
  have hxg : Quotient.mk (MulAction.orbitRel G X) x =
      Quotient.mk (MulAction.orbitRel G X) (g • x) :=
    (Quotient.sound (s := MulAction.orbitRel G X)
      (show g • x ∈ MulAction.orbit G x from ⟨g, rfl⟩)).symm
  obtain ⟨γ⟩ := γ
  change cov.liftPath γ (g • x) (γ.source.trans hxg) 1 =
    g • cov.liftPath γ x (by simp) 1
  have hlift : F.comp (cov.liftPath γ x (by simp)) =
      cov.liftPath γ (g • x) (γ.source.trans hxg) := by
    apply (cov.eq_liftPath_iff' _).mpr
    constructor
    · funext t
      exact (congr_fun hF.2 (cov.liftPath γ x (by simp) t)).trans
        (congr_fun (cov.liftPath_lifts γ x (by simp)) t)
    · change F (cov.liftPath γ x (by simp) 0) = g • x
      rw [cov.liftPath_zero]
      exact hF.1
  rw [← hlift, hFT]
  rfl

/-- Endpoint monodromy for the repaired orbit covering, expressed as the
unique acting-group element carrying the chosen lift `x` to the endpoint of
the lifted loop. The inverse needed to obtain a homomorphism into `G` is left
to the subsequent orientation lemma. -/
noncomputable def orbitEndpointMonodromyRaw
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
    [LocallyCompactSpace X] [T2Space X]
    (free : ∀ g : G, ∀ x : X, g • x = x → g = 1) (x : X) :
    FundamentalGroup (MulAction.orbitRel.Quotient G X) (Quotient.mk _ x) → G :=
  fun γ ↦ (orbitQuotientFiberEquiv free x).symm
    ((quotientMk_isCoveringMap free).monodromy
      (FundamentalGroup.toPath γ) ⟨x, rfl⟩)

@[simp] theorem orbitEndpointMonodromyRaw_one
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
    [LocallyCompactSpace X] [T2Space X]
    (free : ∀ g : G, ∀ x : X, g • x = x → g = 1) (x : X) :
    orbitEndpointMonodromyRaw free x 1 = 1 := by
  apply (orbitQuotientFiberEquiv free x).injective
  rw [orbitEndpointMonodromyRaw, Equiv.apply_symm_apply]
  change
    (quotientMk_isCoveringMap free).monodromy (.refl (Quotient.mk _ x)) ⟨x, rfl⟩ =
      orbitQuotientFiberEquiv free x 1
  rw [IsCoveringMap.monodromy_refl]
  exact Subtype.ext (one_smul G x).symm

/-- Raw endpoint coordinates reverse fundamental-group multiplication because
the endomorphism group multiplies in the order opposite categorical
composition. -/
theorem orbitEndpointMonodromyRaw_mul
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
    [LocallyCompactSpace X] [T2Space X] [SimplyConnectedSpace X]
    [LocPathConnectedSpace X]
    (free : ∀ g : G, ∀ x : X, g • x = x → g = 1) (x : X)
    (a b : FundamentalGroup (MulAction.orbitRel.Quotient G X) (Quotient.mk _ x)) :
    orbitEndpointMonodromyRaw free x (a * b) =
      orbitEndpointMonodromyRaw free x b * orbitEndpointMonodromyRaw free x a := by
  let E := orbitQuotientFiberEquiv free x
  let cov := quotientMk_isCoveringMap free
  apply E.injective
  rw [orbitEndpointMonodromyRaw, Equiv.apply_symm_apply]
  change cov.monodromy (FundamentalGroup.toPath (a * b)) ⟨x, rfl⟩ =
    E (orbitEndpointMonodromyRaw free x b * orbitEndpointMonodromyRaw free x a)
  change cov.monodromy ((FundamentalGroup.toPath b).trans
      (FundamentalGroup.toPath a)) ⟨x, rfl⟩ = _
  rw [IsCoveringMap.monodromy_trans_apply]
  apply Subtype.ext
  have hb : E (orbitEndpointMonodromyRaw free x b) =
      cov.monodromy (FundamentalGroup.toPath b) ⟨x, rfl⟩ := by
    rw [orbitEndpointMonodromyRaw, Equiv.apply_symm_apply]
  rw [← hb]
  calc
    ((cov.monodromy (FundamentalGroup.toPath a)
        (E (orbitEndpointMonodromyRaw free x b)) :
          (Quotient.mk (MulAction.orbitRel G X) :
            X → MulAction.orbitRel.Quotient G X) ⁻¹' {Quotient.mk _ x}) : X) =
        orbitEndpointMonodromyRaw free x b •
          (((cov.monodromy (FundamentalGroup.toPath a) ⟨x, rfl⟩ :
            (Quotient.mk (MulAction.orbitRel G X) :
              X → MulAction.orbitRel.Quotient G X) ⁻¹' {Quotient.mk _ x}) : X)) :=
      orbitMonodromy_deck_equivariant free x a
        (orbitEndpointMonodromyRaw free x b)
    _ = orbitEndpointMonodromyRaw free x b •
        (orbitEndpointMonodromyRaw free x a • x) := by
      congr 1
      change _ = (E (orbitEndpointMonodromyRaw free x a) : X)
      rw [orbitEndpointMonodromyRaw, Equiv.apply_symm_apply]
    _ = (orbitEndpointMonodromyRaw free x b *
        orbitEndpointMonodromyRaw free x a) • x := (mul_smul _ _ _).symm
    _ = (E (orbitEndpointMonodromyRaw free x b *
        orbitEndpointMonodromyRaw free x a) : X) := rfl

/-- Endpoint monodromy as a homomorphism into the acting group.  Inversion
corrects the order reversal in the raw endpoint coordinate. -/
noncomputable def orbitEndpointMonodromy
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
    [LocallyCompactSpace X] [T2Space X] [SimplyConnectedSpace X]
    [LocPathConnectedSpace X]
    (free : ∀ g : G, ∀ x : X, g • x = x → g = 1) (x : X) :
    FundamentalGroup (MulAction.orbitRel.Quotient G X) (Quotient.mk _ x) →* G where
  toFun a := (orbitEndpointMonodromyRaw free x a)⁻¹
  map_one' := by rw [orbitEndpointMonodromyRaw_one, inv_one]
  map_mul' a b := by
    rw [orbitEndpointMonodromyRaw_mul, mul_inv_rev]

@[simp] theorem orbitEndpointMonodromy_apply
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
    [LocallyCompactSpace X] [T2Space X] [SimplyConnectedSpace X]
    [LocPathConnectedSpace X]
    (free : ∀ g : G, ∀ x : X, g • x = x → g = 1) (x : X)
    (a : FundamentalGroup (MulAction.orbitRel.Quotient G X) (Quotient.mk _ x)) :
    orbitEndpointMonodromy free x a = (orbitEndpointMonodromyRaw free x a)⁻¹ := rfl

/-- Every acting-group element is realized by endpoint monodromy.  A path to
the inverse translate projects to a loop, and inversion in the definition of
`orbitEndpointMonodromy` restores the requested group element. -/
theorem orbitEndpointMonodromy_surjective
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
    [LocallyCompactSpace X] [T2Space X] [SimplyConnectedSpace X]
    [LocPathConnectedSpace X]
    (free : ∀ g : G, ∀ x : X, g • x = x → g = 1) (x : X) :
    Function.Surjective (orbitEndpointMonodromy free x) := by
  intro g
  let q : C(X, MulAction.orbitRel.Quotient G X) :=
    ⟨Quotient.mk (MulAction.orbitRel G X), continuous_quotient_mk'⟩
  let cov := quotientMk_isCoveringMap free
  let δ := PathConnectedSpace.somePath x (g⁻¹ • x)
  have hend : q (g⁻¹ • x) = q x := Quotient.sound ⟨g⁻¹, rfl⟩
  let γ : Path.Homotopic.Quotient (q x) (q x) :=
    ((Path.Homotopic.Quotient.mk δ).map q).cast rfl hend.symm
  refine ⟨FundamentalGroup.fromPath γ, ?_⟩
  rw [orbitEndpointMonodromy_apply]
  have hraw : orbitEndpointMonodromyRaw free x (FundamentalGroup.fromPath γ) = g⁻¹ := by
    apply (orbitQuotientFiberEquiv free x).injective
    rw [orbitEndpointMonodromyRaw, Equiv.apply_symm_apply]
    apply Subtype.ext
    simpa [γ, IsCoveringMap.monodromy, Path.Homotopic.Quotient.cast] using
      congrArg Subtype.val (cov.monodromy_map (Path.Homotopic.Quotient.mk δ))
  rw [hraw, inv_inv]

/-- Endpoint monodromy is injective when the total space is simply connected.
A loop in its kernel lifts to a loop upstairs, whose unique homotopy class
projects back to the identity class downstairs. -/
theorem orbitEndpointMonodromy_injective
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
    [LocallyCompactSpace X] [T2Space X] [SimplyConnectedSpace X]
    [LocPathConnectedSpace X]
    (free : ∀ g : G, ∀ x : X, g • x = x → g = 1) (x : X) :
    Function.Injective (orbitEndpointMonodromy free x) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext a
  simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro ha
    let q : C(X, MulAction.orbitRel.Quotient G X) :=
      ⟨Quotient.mk (MulAction.orbitRel G X), continuous_quotient_mk'⟩
    let cov := quotientMk_isCoveringMap free
    let E := orbitQuotientFiberEquiv free x
    have hraw : orbitEndpointMonodromyRaw free x a = 1 := by
      have : (orbitEndpointMonodromyRaw free x a)⁻¹ = 1 := by
        simpa only [orbitEndpointMonodromy_apply] using ha
      exact inv_eq_one.mp this
    have hmon : cov.monodromy (FundamentalGroup.toPath a) ⟨x, rfl⟩ = ⟨x, rfl⟩ := by
      have h := congrArg E hraw
      rw [orbitEndpointMonodromyRaw, Equiv.apply_symm_apply] at h
      exact h.trans (Subtype.ext (one_smul G x))
    obtain ⟨γ⟩ := a
    let lift := cov.liftPath γ x (by simp)
    have hend : lift 1 = x := by
      simpa [IsCoveringMap.monodromy, lift] using congrArg Subtype.val hmon
    let δ : Path x x := ⟨lift, cov.liftPath_zero _ _ _, hend⟩
    have hmap : (Path.Homotopic.Quotient.mk δ).map q =
        Path.Homotopic.Quotient.mk γ := by
      rw [← Path.Homotopic.Quotient.mk_map]
      congr 1
      ext t
      exact congrFun (cov.liftPath_lifts γ x (by simp)) t
    have hδ : Path.Homotopic.Quotient.mk δ =
        Path.Homotopic.Quotient.refl x := Subsingleton.elim _ _
    change Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.refl (q x)
    calc
      Path.Homotopic.Quotient.mk γ =
          (Path.Homotopic.Quotient.mk δ).map q := hmap.symm
      _ = (Path.Homotopic.Quotient.refl x).map q := congrArg (·.map q) hδ
      _ = Path.Homotopic.Quotient.refl (q x) := rfl
  · exact fun ha ↦ ha.symm ▸ map_one (orbitEndpointMonodromy free x)

private abbrev CounterexampleGroup := Multiplicative (ZMod 2)

private instance : TopologicalSpace CounterexampleGroup := ⊤

private instance : ContractibleSpace CounterexampleGroup := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨1, ⟨?_⟩⟩
  exact
    { toFun := fun tx ↦ if tx.1 = 0 then tx.2 else 1
      continuous_toFun := continuous_of_indiscreteTopology
      map_zero_left := fun x ↦ by simp
      map_one_left := fun x ↦ by simp }

private instance : MulAction.IsPretransitive CounterexampleGroup CounterexampleGroup where
  exists_smul_eq x y := ⟨y * x⁻¹, by simp⟩

/-- The regular action of the two-element group on itself with the indiscrete
topology satisfies the fixed theorem's hypotheses, but its orbit quotient is a
singleton and hence has trivial fundamental group. -/
theorem indiscreteRegularAction_no_fundamentalGroupEquiv :
    ¬ Nonempty
      (FundamentalGroup
          (MulAction.orbitRel.Quotient CounterexampleGroup CounterexampleGroup)
          (Quotient.mk _ (1 : CounterexampleGroup)) ≃* CounterexampleGroup) := by
  letI : Subsingleton
      (MulAction.orbitRel.Quotient CounterexampleGroup CounterexampleGroup) :=
    (MulAction.pretransitive_iff_subsingleton_quotient _ _).mp inferInstance
  intro h
  haveI : Subsingleton
      (FundamentalGroup
        (MulAction.orbitRel.Quotient CounterexampleGroup CounterexampleGroup)
        (Quotient.mk _ (1 : CounterexampleGroup))) := by
    change Subsingleton (Path.Homotopic.Quotient _ _)
    infer_instance
  have heq : h.some.symm (Multiplicative.ofAdd (1 : ZMod 2)) =
      h.some.symm (Multiplicative.ofAdd 0) := Subsingleton.elim _ _
  have hone : (1 : ZMod 2) ≠ 0 := by decide
  exact hone (Multiplicative.ofAdd.injective (h.some.symm.injective heq))

/-- The program's frozen final statement is false without a separation
hypothesis: the indiscrete regular action supplies a concrete counterexample. -/
theorem freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv_refuted :
    ¬ (∀ {G X : Type} [Group G] [TopologicalSpace X] [MulAction G X]
        [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X],
        (∀ g : G, ∀ x : X, g • x = x → g = 1) →
        ∀ [SimplyConnectedSpace X] [LocPathConnectedSpace X] (x : X),
          Nonempty
            (FundamentalGroup (MulAction.orbitRel.Quotient G X)
              (Quotient.mk _ x) ≃* G)) := by
  intro claimed
  apply indiscreteRegularAction_no_fundamentalGroupEquiv
  apply claimed (G := CounterexampleGroup) (X := CounterexampleGroup)
  · intro g x h
    have := congrArg (fun y ↦ y * x⁻¹) h
    simpa [smul_eq_mul] using this

#print axioms quotientMk_isCoveringMap
#print axioms quotientCoveringOrbitFiberEquiv
#print axioms orbitQuotientFiberEquiv
#print axioms orbitProjection_existsUnique_lift
#print axioms orbitMonodromy_deck_equivariant
#print axioms orbitEndpointMonodromyRaw
#print axioms orbitEndpointMonodromyRaw_one
#print axioms orbitEndpointMonodromyRaw_mul
#print axioms orbitEndpointMonodromy
#print axioms orbitEndpointMonodromy_surjective
#print axioms orbitEndpointMonodromy_injective
#print axioms indiscreteRegularAction_no_fundamentalGroupEquiv
#print axioms freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv_refuted

end ConstructionTargets.DeckGroupQuotientFundamentalGroup
