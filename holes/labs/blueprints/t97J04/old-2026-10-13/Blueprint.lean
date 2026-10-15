import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.GroupTheory.PresentedGroup
import ConstructionTargets.Surfaces
import ConstructionTargets.PointWedgeQuotient
import ConstructionTargets.PointWedgeVanKampen
import ConstructionTargets.GenericTargetNaturalSourceReconstruction
import ConstructionTargets.TorusCircleWedgeMayerVietoris
import ConstructionTargets.T00A01MayerVietorisAdapters

open CategoryTheory Set

noncomputable section

abbrev apm_t97J04_Disk := ConstructionTargets.Surfaces.Disk

def apm_t97J04_edgePoint (n : ℕ) (j : Fin n)
    (t : Set.Icc (0 : ℝ) 1) : apm_t97J04_Disk :=
  ConstructionTargets.Surfaces.edgePoint n j t

inductive apm_t97J04_ComplexRel :
    Sum apm_t97J04_Disk apm_t97J04_Disk →
      Sum apm_t97J04_Disk apm_t97J04_Disk → Prop
  | a (t : Set.Icc (0 : ℝ) 1) :
      apm_t97J04_ComplexRel
        (.inl (apm_t97J04_edgePoint 8 0 t))
        (.inl (apm_t97J04_edgePoint 8 2 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩))
  | b (t : Set.Icc (0 : ℝ) 1) :
      apm_t97J04_ComplexRel
        (.inl (apm_t97J04_edgePoint 8 1 t))
        (.inl (apm_t97J04_edgePoint 8 3 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩))
  | c (t : Set.Icc (0 : ℝ) 1) :
      apm_t97J04_ComplexRel
        (.inl (apm_t97J04_edgePoint 8 4 t))
        (.inl (apm_t97J04_edgePoint 8 6 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩))
  | d (t : Set.Icc (0 : ℝ) 1) :
      apm_t97J04_ComplexRel
        (.inl (apm_t97J04_edgePoint 8 5 t))
        (.inl (apm_t97J04_edgePoint 8 7 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩))
  | meridian (t : Set.Icc (0 : ℝ) 1) :
      apm_t97J04_ComplexRel
        (.inl (apm_t97J04_edgePoint 8 4 t))
        (.inr (apm_t97J04_edgePoint 1 0 t))

def apm_t97J04_X := Quotient (Relation.EqvGen.setoid apm_t97J04_ComplexRel)

noncomputable instance : TopologicalSpace apm_t97J04_X :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t97J04_Disk apm_t97J04_Disk ↦ Quotient.mk _ x)
    inferInstance

def apm_t97J04_basepoint : apm_t97J04_X :=
  Quotient.mk _ (.inl (0 : apm_t97J04_Disk))

def apm_t97J04_relator : FreeGroup (Fin 3) :=
  FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹

abbrev apm_t97J04_piOne :=
  PresentedGroup ({apm_t97J04_relator} : Set (FreeGroup (Fin 3)))

abbrev apm_t97J04_H (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t97J04_X))

abbrev apm_t97J04_W :=
  ConstructionTargets.TorusCircleWedgeOpenCover.GenericWedge

def apm_t97J04_wedgeBase : apm_t97J04_W :=
  ConstructionTargets.GenericTargetNaturalSourceReconstruction.wedgeBase

abbrev apm_t97J04_WH (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t97J04_W))

/-- LIBRARY: the remaining geometric core.  Construct the two quotient maps
and the two explicit homotopies which collapse the meridian disk together
with the `c`-handle.  This is kept as one leaf because the repository has no
polygon/CW coordinate model in which the four constructions can be stated
separately without making the compatibility condition circular. -/
theorem apm_t97J04_complex_wedge_homotopyEquiv :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t97J04_X apm_t97J04_W) := by
  sorry

/-- A supplied geometric homotopy equivalence gives the required based
fundamental-group comparison.  The conclusion of the geometric leaf is an
explicit hypothesis, so this transport can be proved independently. -/
local instance apm_t97J04_fundamentalGroup_of_homotopyEquiv_aux_circlePathConnected :
    PathConnectedSpace Circle :=
  pathConnectedSpace_iff_univ.mpr (by
    have hc : IsPathConnected
        (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
          (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
        isPathConnected_univ
    simpa using hc)

local instance apm_t97J04_fundamentalGroup_of_homotopyEquiv_aux_torusPathConnected :
    PathConnectedSpace (Circle × Circle) :=
  ⟨⟨(1, 1)⟩, fun x y ↦
    ⟨Path.prod (PathConnectedSpace.somePath x.1 y.1)
      (PathConnectedSpace.somePath x.2 y.2)⟩⟩

theorem apm_t97J04_fundamentalGroup_of_homotopyEquiv_aux_wedge_isPathConnected :
    IsPathConnected (Set.univ : Set apm_t97J04_W) := by
  let qmap := ConstructionTargets.PointWedgeQuotient.quotientMap
    ((1, 1) : Circle × Circle) (1 : Circle)
  refine ⟨qmap (.inl (1, 1)), Set.mem_univ _, ?_⟩
  intro r _
  obtain ⟨b, rfl⟩ :=
    ConstructionTargets.PointWedgeQuotient.surjective_quotientMap
      ((1, 1) : Circle × Circle) (1 : Circle) r
  have hleft : Continuous (fun x : Circle × Circle ↦ qmap (.inl x)) :=
    (ConstructionTargets.PointWedgeQuotient.continuous_quotientMap
      ((1, 1) : Circle × Circle) (1 : Circle)).comp continuous_inl
  have hright : Continuous (fun y : Circle ↦ qmap (.inr y)) :=
    (ConstructionTargets.PointWedgeQuotient.continuous_quotientMap
      ((1, 1) : Circle × Circle) (1 : Circle)).comp continuous_inr
  rw [joinedIn_univ]
  cases b with
  | inl x =>
      obtain ⟨γ⟩ := PathConnectedSpace.joined ((1, 1) : Circle × Circle) x
      exact ⟨γ.map hleft⟩
  | inr y =>
      obtain ⟨δ⟩ := PathConnectedSpace.joined (1 : Circle) y
      have hw : qmap (.inl (1, 1)) = qmap (.inr 1) :=
        Quotient.sound (Relation.EqvGen.rel _ _
          (ConstructionTargets.PointWedgeQuotient.Rel.base
            (x₀ := ((1, 1) : Circle × Circle)) (y₀ := (1 : Circle))))
      exact ⟨(Path.refl _).trans ((δ.map hright).cast hw rfl)⟩

local instance apm_t97J04_fundamentalGroup_of_homotopyEquiv_aux_wedgePathConnected :
    PathConnectedSpace apm_t97J04_W :=
  pathConnectedSpace_iff_univ.mpr
    apm_t97J04_fundamentalGroup_of_homotopyEquiv_aux_wedge_isPathConnected

theorem apm_t97J04_fundamentalGroup_of_homotopyEquiv
    (h : Nonempty (ContinuousMap.HomotopyEquiv apm_t97J04_X apm_t97J04_W)) :
    Nonempty
      (FundamentalGroup apm_t97J04_X apm_t97J04_basepoint ≃*
        FundamentalGroup apm_t97J04_W apm_t97J04_wedgeBase) := by
  obtain ⟨e⟩ := h
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  let eπ := E.fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk apm_t97J04_basepoint)
  exact ⟨eπ.trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
      (e apm_t97J04_basepoint) apm_t97J04_wedgeBase)⟩

/-- A supplied geometric homotopy equivalence induces the all-degree
singular-homology comparison.  This is independent of the based fundamental
group transport. -/
theorem apm_t97J04_homology_of_homotopyEquiv
    (h : Nonempty (ContinuousMap.HomotopyEquiv apm_t97J04_X apm_t97J04_W)) :
    ∀ k : ℕ, Nonempty (apm_t97J04_H k ≅ apm_t97J04_WH k) := by
  rcases h with ⟨e⟩
  intro k
  exact ⟨ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv e k⟩

/-- Assemble the two invariant transports from the common geometric
homotopy equivalence. -/
theorem apm_t97J04_complex_to_wedge :
    Nonempty
      (FundamentalGroup apm_t97J04_X apm_t97J04_basepoint ≃*
        FundamentalGroup apm_t97J04_W apm_t97J04_wedgeBase) ∧
    (∀ k : ℕ, Nonempty (apm_t97J04_H k ≅ apm_t97J04_WH k)) := by
  exact
    ⟨apm_t97J04_fundamentalGroup_of_homotopyEquiv
        apm_t97J04_complex_wedge_homotopyEquiv,
      apm_t97J04_homology_of_homotopyEquiv
        apm_t97J04_complex_wedge_homotopyEquiv⟩

/-- Pure group-presentation simplification: `ℤ² * ℤ` is the three-generator
presentation with the single commutator relation on the first two generators. -/
def apm_t97J04_coprod_equiv_presentation_aux_zpowHom {G : Type*} [Group G] (x : G) :
    Multiplicative ℤ →* G where
  toFun n := x ^ Multiplicative.toAdd n
  map_one' := by simp
  map_mul' m n := by
    change x ^ (Multiplicative.toAdd m + Multiplicative.toAdd n) = _
    exact zpow_add x _ _

def apm_t97J04_coprod_equiv_presentation_aux_prodHom {G : Type*} [Group G]
    (x y : G) (hxy : Commute x y) : Multiplicative (ℤ × ℤ) →* G :=
  (apm_t97J04_coprod_equiv_presentation_aux_zpowHom x).noncommCoprod
    (apm_t97J04_coprod_equiv_presentation_aux_zpowHom y)
    (fun m n ↦ hxy.zpow_zpow (Multiplicative.toAdd m) (Multiplicative.toAdd n))

theorem apm_t97J04_coprod_equiv_presentation :
    Nonempty
      (Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative ℤ) ≃*
        apm_t97J04_piOne) := by
  let P := apm_t97J04_piOne
  let a : P := PresentedGroup.of 0
  let b : P := PresentedGroup.of 1
  let c : P := PresentedGroup.of 2
  have hrel : a * b * a⁻¹ * b⁻¹ = 1 := by
    exact PresentedGroup.one_of_mem (by simp [apm_t97J04_relator, a, b])
  have hab : Commute a b := by
    rw [commute_iff_eq]
    exact (mul_inv_eq_iff_eq_mul).mp ((mul_eq_one_iff_eq_inv).mp hrel)
  let fAB : Multiplicative (ℤ × ℤ) →* P :=
    apm_t97J04_coprod_equiv_presentation_aux_prodHom a b hab
  let fC : Multiplicative ℤ →* P :=
    apm_t97J04_coprod_equiv_presentation_aux_zpowHom c
  let f : Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative ℤ) →* P :=
    Monoid.Coprod.lift fAB fC
  let A := Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative ℤ)
  let gen : Fin 3 → A := ![
    Monoid.Coprod.inl (Multiplicative.ofAdd (1, 0)),
    Monoid.Coprod.inl (Multiplicative.ofAdd (0, 1)),
    Monoid.Coprod.inr (Multiplicative.ofAdd 1)]
  have gen_rel : ∀ r ∈ ({apm_t97J04_relator} : Set (FreeGroup (Fin 3))),
      FreeGroup.lift gen r = 1 := by
    intro r hr
    simp only [Set.mem_singleton_iff] at hr
    subst r
    change gen 0 * gen 1 * (gen 0)⁻¹ * (gen 1)⁻¹ = 1
    simp only [gen, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    have hc : Commute
        ((Monoid.Coprod.inl : Multiplicative (ℤ × ℤ) →* A)
          (Multiplicative.ofAdd ((1 : ℤ), (0 : ℤ))))
        ((Monoid.Coprod.inl : Multiplicative (ℤ × ℤ) →* A)
          (Multiplicative.ofAdd ((0 : ℤ), (1 : ℤ)))) := by
      exact (Commute.all
        (Multiplicative.ofAdd ((1 : ℤ), (0 : ℤ)))
        (Multiplicative.ofAdd ((0 : ℤ), (1 : ℤ)))).map
          (Monoid.Coprod.inl : Multiplicative (ℤ × ℤ) →* A)
    rw [hc.mul_inv_cancel, mul_inv_cancel]
  let g : P →* A := PresentedGroup.toGroup gen_rel
  have hgf : g.comp f = MonoidHom.id A := by
    apply Monoid.Coprod.hom_ext
    · apply MonoidHom.ext
      intro p
      rcases p with ⟨m, n⟩
      change g (a ^ m * b ^ n) = Monoid.Coprod.inl (Multiplicative.ofAdd (m, n))
      rw [map_mul, map_zpow, map_zpow]
      simp only [g, a, b, PresentedGroup.toGroup.of, gen, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      change Monoid.Coprod.inl (Multiplicative.ofAdd ((1 : ℤ), (0 : ℤ))) ^ m *
        Monoid.Coprod.inl (Multiplicative.ofAdd ((0 : ℤ), (1 : ℤ))) ^ n =
        Monoid.Coprod.inl (Multiplicative.ofAdd (m, n))
      calc
        _ = Monoid.Coprod.inl
            ((Multiplicative.ofAdd ((1 : ℤ), (0 : ℤ))) ^ m) *
            Monoid.Coprod.inl
            ((Multiplicative.ofAdd ((0 : ℤ), (1 : ℤ))) ^ n) := by
              rw [map_zpow, map_zpow]
        _ = Monoid.Coprod.inl
            ((Multiplicative.ofAdd ((1 : ℤ), (0 : ℤ))) ^ m *
             (Multiplicative.ofAdd ((0 : ℤ), (1 : ℤ))) ^ n) := by rw [map_mul]
        _ = _ := by
          congr
          apply Multiplicative.toAdd.injective
          ext <;> simp
    · apply MonoidHom.ext
      intro n
      simp only [MonoidHom.comp_apply, f, Monoid.Coprod.lift_apply_inr, fC,
        apm_t97J04_coprod_equiv_presentation_aux_zpowHom, g, PresentedGroup.toGroup.of,
        MonoidHom.id_apply, gen]
      norm_num
      change Monoid.Coprod.inr (Multiplicative.ofAdd 1) ^ Multiplicative.toAdd n =
        Monoid.Coprod.inr n
      rw [← map_zpow]
      congr
      apply Multiplicative.toAdd.injective
      simp
  have hfg : f.comp g = MonoidHom.id P := by
    apply PresentedGroup.ext
    intro i
    change f (g (PresentedGroup.of i)) = PresentedGroup.of i
    rw [show g (PresentedGroup.of i) = gen i from PresentedGroup.toGroup.of gen_rel]
    fin_cases i
    · change a ^ (1 : ℤ) * b ^ (0 : ℤ) = PresentedGroup.of 0
      simp [a]
    · change a ^ (0 : ℤ) * b ^ (1 : ℤ) = PresentedGroup.of 1
      simp [b]
    · change c ^ (1 : ℤ) = PresentedGroup.of 2
      simp [c]
  exact ⟨MonoidHom.toMulEquiv f g hgf hfg⟩

/-- Transport the already-computed torus-circle wedge invariants across the
geometric comparison.  The comparison is an explicit hypothesis so this
lemma can be proved in parallel with the library construction. -/
theorem apm_t97J04_invariants_of_comparison
    (hπ : Nonempty
      (FundamentalGroup apm_t97J04_X apm_t97J04_basepoint ≃*
        FundamentalGroup apm_t97J04_W apm_t97J04_wedgeBase))
    (hH : ∀ k : ℕ, Nonempty (apm_t97J04_H k ≅ apm_t97J04_WH k))
    (hpres : Nonempty
      (Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative ℤ) ≃*
        apm_t97J04_piOne)) :
    Nonempty
      (FundamentalGroup apm_t97J04_X apm_t97J04_basepoint ≃*
        apm_t97J04_piOne) ∧
    Nonempty (apm_t97J04_H 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97J04_H 1 ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    Nonempty (apm_t97J04_H 2 ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t97J04_H k) := by
  rcases hπ with ⟨eπ⟩
  rcases hpres with ⟨epres⟩
  refine ⟨⟨(eπ.trans
    ConstructionTargets.GenericTargetNaturalSourceReconstruction.wedgeFundamentalGroupMulEquiv).trans
      epres⟩, ?_⟩
  rcases
      ConstructionTargets.TorusCircleWedgeMayerVietoris.genericWedge_complete_module_homology with
    ⟨⟨e0⟩, ⟨e1⟩, ⟨e2⟩, higher⟩
  refine ⟨⟨(Nonempty.some (hH 0)).trans e0⟩,
    ⟨(Nonempty.some (hH 1)).trans e1⟩,
    ⟨(Nonempty.some (hH 2)).trans e2⟩, ?_⟩
  intro k hk
  exact (higher k hk).of_iso (Nonempty.some (hH k))

theorem apm_t97j04 :
    Nonempty
      (FundamentalGroup apm_t97J04_X apm_t97J04_basepoint ≃*
        apm_t97J04_piOne) ∧
    Nonempty (apm_t97J04_H 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97J04_H 1 ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    Nonempty (apm_t97J04_H 2 ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t97J04_H k) := by
  rcases apm_t97J04_complex_to_wedge with ⟨hπ, hH⟩
  exact apm_t97J04_invariants_of_comparison hπ hH
    apm_t97J04_coprod_equiv_presentation

#print axioms apm_t97j04
