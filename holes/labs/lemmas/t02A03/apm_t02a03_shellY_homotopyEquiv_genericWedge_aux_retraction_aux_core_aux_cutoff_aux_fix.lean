import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.FundamentalGroupProduct
import ConstructionTargets.CircleUniversalCover
import ConstructionTargets.PointWedgeQuotient
import ConstructionTargets.GenericTargetNaturalSourceReconstruction
import ConstructionTargets.TorusCircleWedgeMayerVietoris
import ConstructionTargets.BoundaryTorusHurewiczIsomorphism
import ConstructionTargets.T02A03ClosedPuncturedDiskTorus

open CategoryTheory

/-!
# APM t02A03 — complements of core circles in handlebodies

## Statement repairs

None.

## Model geometry (revised 2026-10-12)

The source fixes no coordinates for the standardly embedded genus-two region.
The cores are unit circles centred at `(±6/5, 0, 0)`, 2/5 apart, and `W` is
their closed 1/4-neighbourhood: two solid tori meeting in a lens-shaped ball,
whose boundary is a standardly embedded genus-two surface. `C` is the left
core, which stays 2/5 from the right core and so lies in the interior of `W`
away from the right handle, going around one hole as `K` does. (The earlier
model used tangent circles centred at `(±1, 0, 0)`; there the left core
crossed the right tube in an arc. That model was also faithful, but its
right handle minus `C` was not a circle, which made the proof needlessly hard.)

## Encoding note

The two complements are represented by their explicit deformation-retract
models: a torus, and the wedge of a torus with a circle.  Unlike a list of
Betti numbers, the second model remains an actual topological quotient, so its
fundamental group and singular homology are the subjects of the statement.
-/

abbrev apm_t02a03_Torus := Circle × Circle

inductive apm_t02a03_WedgeGlue :
    Sum apm_t02a03_Torus Circle → Sum apm_t02a03_Torus Circle → Prop
  | base : apm_t02a03_WedgeGlue (.inl (1, 1)) (.inr 1)

def apm_t02a03_Y :=
  Quotient (Relation.EqvGen.setoid apm_t02a03_WedgeGlue)

noncomputable instance : TopologicalSpace apm_t02a03_Y :=
  TopologicalSpace.coinduced
    (fun a => Quotient.mk (Relation.EqvGen.setoid apm_t02a03_WedgeGlue) a)
    inferInstance

def apm_t02a03_wedgeQuotient : Sum apm_t02a03_Torus Circle → apm_t02a03_Y :=
  fun a => Quotient.mk _ a

/-- The explicit wedge is genuinely the continuous quotient of the disjoint
union used in its definition. -/
lemma apm_t02a03_continuous_wedgeQuotient :
    Continuous apm_t02a03_wedgeQuotient := by
  exact continuous_coinduced_rng

lemma apm_t02a03_surjective_wedgeQuotient :
    Function.Surjective apm_t02a03_wedgeQuotient := by
  exact Quotient.mk_surjective

def apm_t02a03_torusInclusion : apm_t02a03_Torus → apm_t02a03_Y :=
  fun x ↦ apm_t02a03_wedgeQuotient (.inl x)

def apm_t02a03_circleInclusion : Circle → apm_t02a03_Y :=
  fun z ↦ apm_t02a03_wedgeQuotient (.inr z)

lemma apm_t02a03_continuous_torusInclusion :
    Continuous apm_t02a03_torusInclusion := by
  exact apm_t02a03_continuous_wedgeQuotient.comp continuous_inl

lemma apm_t02a03_continuous_circleInclusion :
    Continuous apm_t02a03_circleInclusion := by
  exact apm_t02a03_continuous_wedgeQuotient.comp continuous_inr

/-- The two inclusion maps identify exactly the chosen wedge basepoints. -/
lemma apm_t02a03_inclusions_basepoint_eq :
    apm_t02a03_torusInclusion (1, 1) = apm_t02a03_circleInclusion 1 := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _ apm_t02a03_WedgeGlue.base)

noncomputable def apm_t02a03_ybase : apm_t02a03_Y :=
  Quotient.mk _ (.inl (1, 1))

@[simp] lemma apm_t02a03_torusInclusion_basepoint :
    apm_t02a03_torusInclusion (1, 1) = apm_t02a03_ybase := rfl

@[simp] lemma apm_t02a03_circleInclusion_basepoint :
    apm_t02a03_circleInclusion 1 = apm_t02a03_ybase := by
  exact apm_t02a03_inclusions_basepoint_eq.symm

/-- Compatible maps out of the torus and circle respect the generated wedge
relation. This follows the quotient eliminator pattern from sibling `t01J03`. -/
lemma apm_t02a03_wedgeDesc_respects
    {Z : Type*} [TopologicalSpace Z]
    (f : C(apm_t02a03_Torus, Z)) (g : C(Circle, Z))
    (hbase : f (1, 1) = g 1) {x y}
    (hxy : Relation.EqvGen apm_t02a03_WedgeGlue x y) :
    Sum.elim f g x = Sum.elim f g y := by
  induction hxy with
  | rel a b hab =>
      cases hab with
      | base => exact hbase
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Continuous pushout eliminator for the concrete wedge quotient. -/
noncomputable def apm_t02a03_wedgeDesc
    {Z : Type*} [TopologicalSpace Z]
    (f : C(apm_t02a03_Torus, Z)) (g : C(Circle, Z))
    (hbase : f (1, 1) = g 1) : C(apm_t02a03_Y, Z) := by
  let raw : Sum apm_t02a03_Torus Circle → Z := Sum.elim f g
  have hraw : Continuous raw := continuous_sum_dom.2 ⟨f.continuous, g.continuous⟩
  exact ⟨Quotient.lift raw (fun _ _ hxy ↦
      apm_t02a03_wedgeDesc_respects f g hbase hxy),
    hraw.quotient_lift (fun _ _ hxy ↦
      apm_t02a03_wedgeDesc_respects f g hbase hxy)⟩

@[simp] lemma apm_t02a03_wedgeDesc_torusInclusion
    {Z : Type*} [TopologicalSpace Z]
    (f : C(apm_t02a03_Torus, Z)) (g : C(Circle, Z))
    (hbase : f (1, 1) = g 1) (x : apm_t02a03_Torus) :
    apm_t02a03_wedgeDesc f g hbase (apm_t02a03_torusInclusion x) = f x := rfl

@[simp] lemma apm_t02a03_wedgeDesc_circleInclusion
    {Z : Type*} [TopologicalSpace Z]
    (f : C(apm_t02a03_Torus, Z)) (g : C(Circle, Z))
    (hbase : f (1, 1) = g 1) (z : Circle) :
    apm_t02a03_wedgeDesc f g hbase (apm_t02a03_circleInclusion z) = g z := rfl

/-- The descended map is uniquely determined by its two restrictions. -/
lemma apm_t02a03_wedgeDesc_unique
    {Z : Type*} [TopologicalSpace Z]
    (f : C(apm_t02a03_Torus, Z)) (g : C(Circle, Z))
    (hbase : f (1, 1) = g 1) (u : C(apm_t02a03_Y, Z))
    (huT : ∀ x, u (apm_t02a03_torusInclusion x) = f x)
    (huC : ∀ z, u (apm_t02a03_circleInclusion z) = g z) :
    u = apm_t02a03_wedgeDesc f g hbase := by
  ext y
  obtain ⟨x, rfl⟩ := apm_t02a03_surjective_wedgeQuotient y
  cases x with
  | inl x => exact huT x
  | inr z => exact huC z

/-- Why this unblocks `apm_t02a03`: this is the missing based fundamental-
group computation for the torus summand.  It isolates the circle computation
and product preservation from the separate wedge calculation. -/
theorem apm_t02A03_bridge_1 :
    Nonempty
      (FundamentalGroup apm_t02a03_Torus (1, 1) ≃*
        Multiplicative (ℤ × ℤ)) := by
  open ConstructionTargets.FundamentalGroupProduct in
    open ConstructionTargets.CircleUniversalCover in
      exact ⟨(fundamentalGroupProdMulEquiv (1 : Circle) (1 : Circle)).trans
        (circleFundamentalGroupMulEquivInt.prodCongr
          circleFundamentalGroupMulEquivInt) |>.trans
        (MulEquiv.prodMultiplicative ℤ ℤ).symm⟩

theorem apm_t02a03_rel_iff_production (a b : Sum apm_t02a03_Torus Circle) :
    ConstructionTargets.PointWedgeQuotient.Rel (1, 1) 1 a b ↔
      apm_t02a03_WedgeGlue a b := by
  constructor <;> intro h <;> cases h <;> constructor

noncomputable def apm_t02a03_productionHomeomorph :
    ConstructionTargets.TorusCircleWedgeOpenCover.GenericWedge ≃ₜ apm_t02a03_Y :=
  ConstructionTargets.PointWedgeQuotient.quotientHomeomorphOfRelIff
    _ _ apm_t02a03_rel_iff_production

@[simp] theorem apm_t02a03_productionHomeomorph_mk
    (z : Sum apm_t02a03_Torus Circle) :
    apm_t02a03_productionHomeomorph (Quotient.mk _ z) = Quotient.mk _ z := rfl

theorem apm_t02a03_productionHomeomorph_base :
    apm_t02a03_productionHomeomorph
      ConstructionTargets.GenericTargetNaturalSourceReconstruction.wedgeBase =
        apm_t02a03_ybase := rfl

/-- Why this unblocks `apm_t02a03`: this packages precisely the invariant
preservation and computation for the compiled torus-circle pushout.  Its five
conjuncts are the remaining fundamental-group and singular-homology claims for
the explicit wedge quotient. -/
theorem apm_t02A03_bridge_2 :
    Nonempty
      (FundamentalGroup apm_t02a03_Y apm_t02a03_ybase ≃*
        Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative ℤ)) ∧
    Nonempty
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a03_Y) ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a03_Y) ≅
        ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    Nonempty
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a03_Y) ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ n : ℕ, 3 ≤ n →
      Limits.IsZero
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a03_Y))) := by
  let e := apm_t02a03_productionHomeomorph
  let piIso : FundamentalGroup apm_t02a03_Y apm_t02a03_ybase ≃*
      Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative ℤ) :=
    ((ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph e
        ConstructionTargets.GenericTargetNaturalSourceReconstruction.wedgeBase).symm.trans
      ConstructionTargets.GenericTargetNaturalSourceReconstruction.wedgeFundamentalGroupMulEquiv)
  rcases ConstructionTargets.TorusCircleWedgeMayerVietoris.genericWedge_complete_module_homology with
    ⟨h0, h1, h2, hh⟩
  refine ⟨⟨piIso⟩, ?_, ?_, ?_, ?_⟩
  · rcases h0 with ⟨h0⟩
    exact ⟨(ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      e.toHomotopyEquiv 0).symm ≪≫ h0⟩
  · rcases h1 with ⟨h1⟩
    exact ⟨(ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      e.toHomotopyEquiv 1).symm ≪≫ h1⟩
  · rcases h2 with ⟨h2⟩
    exact ⟨(ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      e.toHomotopyEquiv 2).symm ≪≫ h2⟩
  · intro n hn
    exact (hh n hn).of_iso
      (ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
        e.toHomotopyEquiv n).symm

/-- Superseded because it computed only the deformation-retract models and did
not state the geometric complements or their deformation retractions. -/
theorem apm_t02a03_previous_encoding :
    Nonempty
      (FundamentalGroup apm_t02a03_Torus (1, 1) ≃*
        Multiplicative (ℤ × ℤ)) ∧
    Nonempty
      (FundamentalGroup apm_t02a03_Y apm_t02a03_ybase ≃*
        Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative ℤ)) ∧
    Nonempty
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a03_Y) ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a03_Y) ≅
        ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    Nonempty
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a03_Y) ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ n : ℕ, 3 ≤ n →
      Limits.IsZero
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a03_Y))) := by
  -- (Sibling: t01J03)
  /-
  Boundary (skipped): this needs concrete computations of
  `FundamentalGroup Circle`, the product formula specialized to based
  fundamental groups, Seifert--van Kampen for the quotient wedge, and the
  singular-homology wedge/Mayer--Vietoris calculation. I searched Mathlib's
  `FundamentalGroup`, `FundamentalGroupoidFunctor.prodIso`,
  `singularHomologyFunctor`, wedge, van Kampen, and Mayer--Vietoris APIs.
  Mathlib provides product preservation for the fundamental groupoid, but no
  computation identifying the fundamental group of `Circle` with `ℤ`, no
  van Kampen theorem for this quotient, and no singular Mayer--Vietoris
  sequence yielding the stated degreewise module isomorphisms. Consequently
  even the first conjunct cannot currently be established from the available
  APIs without developing substantial missing algebraic-topology foundations.

  Closer hop 1 packaged the canonical quotient map and proved it continuous
  and surjective in `apm_t02a03_continuous_wedgeQuotient` and
  `apm_t02a03_surjective_wedgeQuotient`. This confirms the raw quotient-space
  presentation needed by any future gluing theorem. Mathlib's
  `FundamentalGroupoidFunctor.prodIso` still stops at groupoids, and its
  Mayer--Vietoris files concern sheaf cohomology rather than the singular
  homology used here. No API upgrades this generated-relation quotient to a
  topological pushout carrying the required computations.

  Closer hop 2 exposes the based cocone that such a theorem would consume.
  `apm_t02a03_torusInclusion` and `apm_t02a03_circleInclusion` are now explicit
  continuous maps, `apm_t02a03_inclusions_basepoint_eq` proves the generating
  identification, and the two `_basepoint` lemmas rewrite both images to
  `apm_t02a03_ybase`. This removes all local quotient and basepoint bookkeeping
  from the remaining fundamental-group argument. A renewed search of
  topological pushout, van Kampen, circle fundamental-group, and singular
  wedge-homology APIs still found no computation theorem applicable to this
  cocone, so the displayed algebraic invariants remain open. The frozen
  statement is unchanged.

  Closer hop 3 goes beyond the cocone by proving its full continuous universal
  property, reusing the quotient-eliminator pattern from solved helper layer
  `t01J03`. `apm_t02a03_wedgeDesc_respects` propagates basepoint compatibility
  through `Relation.EqvGen`; `apm_t02a03_wedgeDesc` descends compatible maps
  continuously; the two restriction lemmas compute it on each summand; and
  `apm_t02a03_wedgeDesc_unique` proves uniqueness using quotient
  surjectivity. Thus this concrete wedge is no longer missing any point-set
  pushout bookkeeping.

  A renewed inspection after establishing the universal property still found
  no topological Seifert--van Kampen theorem, no singular Mayer--Vietoris
  sequence or colimit-preservation theorem for `singularHomologyFunctor`, and
  no computation of `FundamentalGroup Circle 1`. Mathlib's categorically named
  `Limits.VanKampen` concerns universal colimits, not the fundamental-group
  theorem. Consequently the remaining bridge is now exclusively invariant
  preservation/computation from this compiled pushout, rather than quotient
  construction. The frozen statement is unchanged.
  -/
  exact ⟨apm_t02A03_bridge_1, apm_t02A03_bridge_2⟩

abbrev apm_t02a03_Disk := Metric.closedBall (0 : ℂ) 1

/-- The actual complement of the core circle in the solid torus. -/
abbrev apm_t02a03_X :=
  {p : apm_t02a03_Disk × Circle // p.1.1 ≠ 0}

abbrev apm_t02a03_E3 := EuclideanSpace ℝ (Fin 3)

noncomputable def apm_t02a03_leftCore (t : ℝ) : apm_t02a03_E3 :=
  WithLp.toLp 2 ![-6 / 5 + Real.cos t, Real.sin t, 0]

noncomputable def apm_t02a03_rightCore (t : ℝ) : apm_t02a03_E3 :=
  WithLp.toLp 2 ![6 / 5 - Real.cos t, Real.sin t, 0]

/-- The two disjoint planar core circles of the standard genus-two handlebody;
`W` is their closed 1/4-neighbourhood, in which the two tubes overlap. -/
def apm_t02a03_genusTwoSpine : Set apm_t02a03_E3 :=
  Set.range apm_t02a03_leftCore ∪ Set.range apm_t02a03_rightCore

/-- A fixed closed regular-neighborhood model of the bounded genus-two
handlebody. -/
def apm_t02a03_W : Set apm_t02a03_E3 :=
  {p | Metric.infDist p apm_t02a03_genusTwoSpine ≤ (1 / 4 : ℝ)}

def apm_t02a03_C : Set apm_t02a03_E3 :=
  Set.range apm_t02a03_leftCore

/-- The geometric complement in part (b), before replacing it by its wedge
spine. -/
abbrev apm_t02a03_geometricY :=
  {p : apm_t02a03_E3 // p ∈ apm_t02a03_W ∧ p ∉ apm_t02a03_C}

/-- The part of `W` at distance at least `1/4` from the left core: the
boundary torus of the left tube together with the right tube minus the open
left tube.  It lies inside `geometricY` and is compact. -/
abbrev apm_t02a03_shellY :=
  {p : apm_t02a03_E3 // p ∈ apm_t02a03_W ∧ (1 / 4 : ℝ) ≤ Metric.infDist p apm_t02a03_C}

/-- LIBRARY: radial push off the deleted core.  Inside the left tube, move
each point along its normal ray from the nearest core point out to distance
`1/4`; outside the left tube, fix it.  This is a strong deformation
retraction of `geometricY` onto `shellY`. -/
theorem apm_t02a03_geometricY_homotopyEquiv_shellY :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t02a03_geometricY apm_t02a03_shellY) := by
  sorry

/-- The point where the auxiliary loop touches the boundary torus of the left
tube: the outermost point `(1/20,0,0)` of that torus on the `x`-axis. -/
noncomputable def apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_q0 : apm_t02a03_E3 :=
  WithLp.toLp 2 ![1 / 20, 0, 0]

/-- The boundary torus of the left tube. -/
def apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus : Set apm_t02a03_E3 :=
  {p | Metric.infDist p apm_t02a03_C = (1 / 4 : ℝ)}

/-- A planar circle about the right centre, of radius `23/20`: it stays within
`3/20` of the right core and touches the left boundary torus only at `q0`. -/
def apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop : Set apm_t02a03_E3 :=
  Set.range fun t : ℝ =>
    (WithLp.toLp 2 ![6 / 5 - 23 / 20 * Real.cos t, 23 / 20 * Real.sin t, 0] :
      apm_t02a03_E3)

/-- LIBRARY: the left boundary torus is a torus, with `q0` at the basepoint
(parametrise by core angle and normal angle; uses the closed form of the
distance to the planar circle `C`). -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph :
    ∃ e : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ≃ₜ
        ConstructionTargets.TorusCircleWedgeOpenCover.Torus,
      ∀ h : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_q0 ∈
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus,
        e ⟨_, h⟩ = ((1 : Circle), (1 : Circle)) := by
  sorry

/-- LIBRARY: the loop is a circle, with `q0` (parameter `t = 0`) at `1`. -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph :
    ∃ e : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop ≃ₜ Circle,
      ∀ h : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_q0 ∈
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop,
        e ⟨_, h⟩ = 1 := by
  sorry

/-- LIBRARY: the loop lies in `W`, at distance at least `1/4` from the left
core, and meets the left boundary torus exactly at `q0`. -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_geometry :
    (∀ p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop,
      p ∈ apm_t02a03_W ∧ (1 / 4 : ℝ) ≤ Metric.infDist p apm_t02a03_C) ∧
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∩
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop =
      {apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_q0} := by
  sorry

/-- LIBRARY (pure topology): two subsets of a Hausdorff space, homeomorphic to
the torus and the circle, meeting in exactly one point that goes to both
basepoints, have union homeomorphic to `GenericWedge`.  Route: the map from
`Sum torus circle` is continuous, respects the wedge relation, and descends
to a continuous bijection from the compact wedge onto a Hausdorff space. -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_wedge_homeomorph
    {X : Type*} [TopologicalSpace X] [T2Space X] (A B : Set X) (x : X)
    (hAB : A ∩ B = {x})
    (eA : A ≃ₜ ConstructionTargets.TorusCircleWedgeOpenCover.Torus)
    (eB : B ≃ₜ Circle)
    (heA : ∀ h : x ∈ A, eA ⟨x, h⟩ = ((1 : Circle), (1 : Circle)))
    (heB : ∀ h : x ∈ B, eB ⟨x, h⟩ = 1) :
    Nonempty ((A ∪ B : Set X) ≃ₜ
      ConstructionTargets.TorusCircleWedgeOpenCover.GenericWedge) := by
  sorry

/-- The right tube minus the open left tube: the part of `shellY` outside the
left boundary torus, together with the patch of that torus inside the right
tube. -/
def apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right :
    Set apm_t02a03_E3 :=
  {p | Metric.infDist p (Set.range apm_t02a03_rightCore) ≤ (1 / 4 : ℝ) ∧
    (1 / 4 : ℝ) ≤ Metric.infDist p apm_t02a03_C}

/-- Packages a strong deformation of `shellY` onto `torus ∪ loop` as the
required retraction (banked from lemma-2's partial, 2026-10-19). -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_of_deformation
    (H : C(Set.Icc (0 : ℝ) 1 × apm_t02a03_shellY, apm_t02a03_shellY))
    (hzero : ∀ p, H (⟨0, by norm_num⟩, p) = p)
    (hone : ∀ p,
      (H (⟨1, by norm_num⟩, p)).1 ∈
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop)
    (hfix : ∀ t p,
      p.1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop →
        H (t, p) = p) :
    ∃ r : C(apm_t02a03_shellY, apm_t02a03_shellY),
      (∀ p, (r p).1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop) ∧
      (∀ p, p.1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop → r p = p) ∧
      (ContinuousMap.id apm_t02a03_shellY).Homotopic r := by
  let r : C(apm_t02a03_shellY, apm_t02a03_shellY) :=
    H.comp (ContinuousMap.prodMk (ContinuousMap.const _ ⟨1, by norm_num⟩)
      (ContinuousMap.id _))
  refine ⟨r, ?_, ?_, ?_⟩
  · intro p
    exact hone p
  · intro p hp
    exact hfix ⟨1, by norm_num⟩ p hp
  · exact ⟨{
      toFun := H
      map_zero_left := hzero
      map_one_left := fun p ↦ rfl }⟩

/-- LIBRARY: every point of `shellY` lies on the left boundary torus or in the
right tube.  `W` is the union of the two closed tubes (`infDist` to a union
of two sets is the minimum); a point of the left tube at distance at least
`1/4` from `C` is at distance exactly `1/4`. -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_cover :
    ∀ p : apm_t02a03_shellY,
      p.1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∨
        p.1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right := by
  sorry

/-- LIBRARY: the geometric core.  The right tube minus the open left tube
strong-deformation-retracts onto the patch of the left boundary torus it
contains together with the loop.  (It is a solid torus with a disk `D` on its
boundary; the loop runs parallel to the right core and touches `D` only at
`q0`.) -/
abbrev apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X :=
  apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right

abbrev apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z
    (p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X) : Prop :=
  p.1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop

/-- Points of the right piece that are already in the target `D ∪ loop`, or
lie in the sector `x ≤ 4/5` of the right tube.  The bite (open left tube)
lies in `x < 1/20`, so the sector contains the whole bite region; in the
right-tube angle `θ` (`rightCore θ = (6/5 - cos θ, sin θ, 0)`) every tube
point with `|θ| ≤ 0.82` has `x ≤ 6/5 - (3/4) cos 0.82 < 4/5`. -/
abbrev apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y
    (p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X) : Prop :=
  apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z p ∨ (p.1 : apm_t02a03_E3) 0 ≤ (4 / 5 : ℝ)

/-- Planar distance `s` from the right centre `(6/5, 0)`; on the right tube
`3/4 ≤ s ≤ 5/4` (split by claude-14 from lemma-2's partial, 2026-10-19). -/
noncomputable def apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad (p : apm_t02a03_E3) : ℝ :=
  Real.sqrt ((p 0 - 6 / 5) ^ 2 + p 1 ^ 2)

/-- The cutoff `φ` as a clamp of `cos θ = (6/5 - x)/s`: `φ = 0` when
`cos θ ≥ 23/25`, `φ = 1` when `cos θ ≤ 17/25`. -/
noncomputable def apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi (p : apm_t02a03_E3) : ℝ :=
  min 1 (max 0 ((23 - 25 * ((6 / 5 - p 0) / apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p)) / 6))

/-- `F_t`: keep the angle about the right centre and move the meridian offset
`(s - 1, z)` toward the loop's offset `(3/20, 0)` by the fraction `a = t φ`:
`s ↦ s + a (23/20 - s)`, `z ↦ (1 - a) z`. -/
noncomputable def apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move (t : ℝ) (p : apm_t02a03_E3) : apm_t02a03_E3 :=
  WithLp.toLp 2 ![6 / 5 + (1 + t * apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi p * (23 / 20 / apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p - 1)) * (p 0 - 6 / 5),
    (1 + t * apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi p * (23 / 20 / apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p - 1)) * p 1,
    (1 - t * apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi p) * p 2]

/-- LIBRARY: `F` is continuous on `[0,1] × right` (there `s ≥ 3/4 > 0`, so the
divisions by `s` are continuous). -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_continuous :
    ContinuousOn (fun q : ℝ × apm_t02a03_E3 => apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move q.1 q.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right) := by
  sorry

/-- LIBRARY: `F_t` stays in the closed right tube.  The distance to the right
core is `√((s - 1)² + z²)`; the new `(s - 1, z)` is a convex combination of the
old one and `(3/20, 0)`, both in the disk of radius `1/4`. -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right) :
    Metric.infDist (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move t p) (Set.range apm_t02a03_rightCore) ≤ (1 / 4 : ℝ) := by
  sorry

/-- LIBRARY: `F_t` stays at least `1/4` from the left core.  If `t φ = 0` the
point is fixed.  Otherwise `cos θ < 23/25` and the new `s' ≤ 5/4`, so
`x' = 6/5 - s' cos θ > 1/20`; a point with `x > 1/20` is at planar distance
`> 5/4` from `(-6/5, 0)`, hence more than `1/4` from `C`. -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_far (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right) :
    (1 / 4 : ℝ) ≤ Metric.infDist (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move t p) apm_t02a03_C := by
  sorry

/-- LIBRARY: `F_t` fixes `torus ∪ loop` in the right piece.  Loop points have
`s = 23/20`, `z = 0`.  Torus points have `x ≤ 1/20`, so `cos θ ≥ (23/20)/s ≥
23/25` and `φ = 0`. -/
-- BEGIN SEAT AREA
lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_fix_aux_loop
    (t : ℝ) (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop) :
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move t p = p := by
  rcases hp with ⟨u, rfl⟩
  have htrig : Real.cos u ^ 2 + Real.sin u ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  have hrad :
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad
        (WithLp.toLp 2 ![6 / 5 - 23 / 20 * Real.cos u,
          23 / 20 * Real.sin u, 0] : apm_t02a03_E3) = 23 / 20 := by
    rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad]
    simp
    rw [show (23 / 20 * Real.cos u) ^ 2 +
        (23 / 20 * Real.sin u) ^ 2 = (23 / 20 : ℝ) ^ 2 by
      nlinarith]
    rw [Real.sqrt_sq_eq_abs]
    norm_num
  ext i
  fin_cases i <;>
    simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move,
      hrad] <;> ring

lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_fix_aux_torus
    (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right)
    (hT : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus) :
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi p = 0 := by
  sorry

theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_fix (t : ℝ) (p : apm_t02a03_E3) (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right)
    (hZ : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop) :
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move t p = p := by
  rcases hZ with hT | hL
  · have hphi :=
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_fix_aux_torus
        p hp hT
    ext i
    fin_cases i <;>
      simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move,
        hphi]
  · exact
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_fix_aux_loop
        t p hL
-- END SEAT AREA

/-- LIBRARY: the end of the collapse.  If `φ = 1` the point goes to `s = 23/20`,
`z = 0`, the angle `θ` with `cos θ = (6/5 - x)/s`, `sin θ = y/s`: a loop point.
If `φ < 1` then `cos θ > 17/25` and `s' ≥ 3/4`, so
`x' ≤ 6/5 - (3/4)(17/25) < 4/5`. -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_end (p : apm_t02a03_E3) (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right) :
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move 1 p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop ∨ (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move 1 p) 0 ≤ (4 / 5 : ℝ) := by
  sorry

/-- Stage 1, the cutoff collapse.  With `w = (u, z)` the meridian offset and
`ℓ = (3/20, 0)` the loop's offset, `F_t(θ, w) = (θ, w + t φ(θ) (ℓ - w))`
where `φ = 1` for `|θ| ≥ 0.82` and `φ = 0` for `|θ| ≤ 0.41`.  The bite lies in
`|θ| < 0.41` (it needs `s cos θ ≥ 23/20` with `s ≤ 5/4`), so the segments
avoid it; the meridian disk is convex; `D` and the loop are fixed.  At the
end every point has either `φ = 1` (it is on the loop) or `|θ| < 0.82` (it is
in the sector `x ≤ 4/5`). -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff :
    ∃ m : C(apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X),
      ∃ F : ContinuousMap.Homotopy (ContinuousMap.id _) m,
        (∀ t p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z p → F (t, p) = p) ∧
        (∀ p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y (m p)) := by
  have hmaps : ∀ q : Set.Icc (0 : ℝ) 1 × apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X,
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move q.1 q.2.1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right := fun q =>
    ⟨apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube q.1.1 q.1.2 q.2.1 q.2.2, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_far q.1.1 q.1.2 q.2.1 q.2.2⟩
  let G : C(Set.Icc (0 : ℝ) 1 × apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X) :=
    { toFun := fun q => ⟨apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move q.1 q.2.1, hmaps q⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_continuous.comp_continuous
          ((continuous_subtype_val.comp continuous_fst).prodMk
            (continuous_subtype_val.comp continuous_snd))
          (fun q => ⟨q.1.2, q.2.2⟩) }
  let m : C(apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X) :=
    G.comp (ContinuousMap.prodMk (ContinuousMap.const _ ⟨1, by norm_num⟩) (ContinuousMap.id _))
  have h0 : ∀ p : apm_t02a03_E3, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move 0 p = p := fun p => by
    ext i; fin_cases i <;> simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move]
  let F : ContinuousMap.Homotopy (ContinuousMap.id _) m :=
    { toContinuousMap := G,
      map_zero_left := fun p => Subtype.ext (h0 p.1),
      map_one_left := fun p => rfl }
  refine ⟨m, F, ?_, ?_⟩
  · intro t p hp
    exact Subtype.ext (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_fix t p.1 p.2 hp)
  · intro p
    rcases apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_end p.1 p.2 with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- Stage 2, the sector-ball collapse.  The subspace `Y` is the sector piece
`Σ = right ∩ {x ≤ 4/5}` (a 3-ball: a fibrewise-convex slab of the tube over
an interval of angles, with the bite removed as a dent from its boundary)
together with the rest of the loop.  `Σ` strongly deformation retracts onto
`Σ ∩ (D ∪ loop)`, the disk `D` with the loop arc through `q0` (a contractible
subpolyhedron, the arc's ends on the face `x = 4/5`); extend by the identity
on the rest of the loop, which meets `Σ` only in that arc. -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_sector :
    ∃ H : C(Set.Icc (0 : ℝ) 1 × {p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X // apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y p},
        {p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X // apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y p}),
      (∀ p, H (0, p) = p) ∧
      (∀ p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z (H (1, p)).1) ∧
      (∀ t p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z p.1 → H (t, p) = p) := by
  sorry

/-- The two geometric stages promised in the blueprint.  The intermediate
map is the cutoff collapse: away from the bite it has already collapsed the
meridian disk to the distinguished loop.  The second homotopy collapses the
remaining sector ball, relative to the target `D ∪ loop`. -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_stages :
    ∃ m e : C(
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X,
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X),
      ∃ F : ContinuousMap.Homotopy
          (ContinuousMap.id _) m,
        ∃ K : ContinuousMap.Homotopy m e,
          (∀ p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z
              (e p)) ∧
          (∀ t p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z p →
              F (t, p) = p) ∧
          (∀ t p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z p →
              K (t, p) = p) := by
  obtain ⟨m, F, hF, hm⟩ := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff
  obtain ⟨H, h0, h1, hfix⟩ := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_sector
  let j : C(apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X, {p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X // apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y p}) :=
    ⟨fun p => ⟨m p, hm p⟩, (map_continuous m).subtype_mk _⟩
  have hmZ : ∀ p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z p → m p = p := fun p hp => by
    rw [← F.apply_one p]; exact hF 1 p hp
  let e : C(apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X) :=
    ⟨fun p => (H (1, j p)).1,
      continuous_subtype_val.comp
        (H.continuous.comp (continuous_const.prodMk j.continuous))⟩
  let K : ContinuousMap.Homotopy m e :=
    { toFun := fun x => (H (x.1, j x.2)).1
      continuous_toFun := continuous_subtype_val.comp
        (H.continuous.comp (continuous_fst.prodMk (j.continuous.comp continuous_snd)))
      map_zero_left := fun p => by
        change (H (0, j p)).1 = m p
        rw [h0]; rfl
      map_one_left := fun p => rfl }
  refine ⟨m, e, F, K, ?_, hF, ?_⟩
  · intro p
    exact h1 (j p)
  · intro t p hp
    change (H (t, j p)).1 = p
    have hj : j p = ⟨p, Or.inl hp⟩ := Subtype.ext (hmZ p hp)
    rw [hj]
    exact congrArg Subtype.val (hfix t ⟨p, Or.inl hp⟩ hp)

/-- Concatenating the cutoff collapse and the sector-ball collapse preserves
the relative (strong-deformation-retraction) condition. -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_concat
    (m e : C(
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X,
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X))
    (F : ContinuousMap.Homotopy (ContinuousMap.id _) m)
    (K : ContinuousMap.Homotopy m e)
    (he : ∀ p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z
      (e p))
    (hF : ∀ t p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z p →
      F (t, p) = p)
    (hK : ∀ t p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z p →
      K (t, p) = p) :
    ∃ G : C(Set.Icc (0 : ℝ) 1 ×
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right,
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right),
      (∀ p, G (⟨0, by norm_num⟩, p) = p) ∧
      (∀ p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z
        (G (⟨1, by norm_num⟩, p))) ∧
      (∀ t p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z p →
        G (t, p) = p) := by
  let H := F.trans K
  refine ⟨H.toContinuousMap, H.map_zero_left, ?_, ?_⟩
  · intro p
    change apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z
      (H (⟨1, by norm_num⟩, p))
    have ht : (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) = (1 : Set.Icc (0 : ℝ) 1) :=
      Subtype.ext (by norm_num)
    rw [ht]
    simpa only [ContinuousMap.Homotopy.apply_one] using he p
  · intro t p hp
    change H (t, p) = p
    change (F.trans K) (t, p) = p
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact hF _ p hp
    · exact hK _ p hp

theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core :
    ∃ G : C(Set.Icc (0 : ℝ) 1 ×
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right,
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right),
      (∀ p, G (⟨0, by norm_num⟩, p) = p) ∧
      (∀ p, (G (⟨1, by norm_num⟩, p)).1 ∈
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop) ∧
      (∀ t p, p.1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop →
        G (t, p) = p) := by
  obtain ⟨m, e, F, K, he, hF, hK⟩ :=
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_stages
  exact apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_concat
    m e F K he hF hK

/-- LIBRARY (point-set topology): extend a deformation of the right part that
fixes the torus patch by the identity on the left boundary torus.  Both pieces
are closed in `shellY` (`infDist` is continuous), they cover it by `hcover`,
and on their overlap (which lies in the torus) both formulas give `p`; glue
with `ContinuousMap.liftCover` or `Continuous.piecewise`. -/
lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_glue_aux_right_shell
    (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right) :
    p ∈ apm_t02a03_W ∧ (1 / 4 : ℝ) ≤ Metric.infDist p apm_t02a03_C := by
  refine ⟨?_, hp.2⟩
  have hne : (Set.range apm_t02a03_rightCore).Nonempty :=
    ⟨apm_t02a03_rightCore 0, Set.mem_range_self 0⟩
  have hsub : Set.range apm_t02a03_rightCore ⊆ apm_t02a03_genusTwoSpine :=
    Set.subset_union_right
  exact (Metric.infDist_le_infDist_of_subset hsub hne).trans hp.1

theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_glue
    (hcover : ∀ p : apm_t02a03_shellY,
      p.1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∨
        p.1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right)
    (G : C(Set.Icc (0 : ℝ) 1 ×
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right,
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right))
    (hzero : ∀ p, G (⟨0, by norm_num⟩, p) = p)
    (hone : ∀ p, (G (⟨1, by norm_num⟩, p)).1 ∈
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop)
    (hfix : ∀ t p, p.1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop →
        G (t, p) = p) :
    ∃ H : C(Set.Icc (0 : ℝ) 1 × apm_t02a03_shellY, apm_t02a03_shellY),
      (∀ p, H (⟨0, by norm_num⟩, p) = p) ∧
      (∀ p, (H (⟨1, by norm_num⟩, p)).1 ∈
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop) ∧
      (∀ t p, p.1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop →
        H (t, p) = p) := by
  classical
  let right := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right
  let torus := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus
  let g : Set.Icc (0 : ℝ) 1 × right → apm_t02a03_shellY := fun z =>
    ⟨(G z).1,
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_glue_aux_right_shell
        (G z).1 (G z).2⟩
  have hg : Continuous g := by
    exact (continuous_subtype_val.comp G.continuous).subtype_mk _
  let f : Set.Icc (0 : ℝ) 1 × apm_t02a03_shellY → apm_t02a03_shellY := fun z =>
    if hz : z.2.1 ∈ right then g ⟨z.1, ⟨z.2.1, hz⟩⟩ else z.2
  let R : Set (Set.Icc (0 : ℝ) 1 × apm_t02a03_shellY) :=
    {z | z.2.1 ∈ right}
  let T : Set (Set.Icc (0 : ℝ) 1 × apm_t02a03_shellY) :=
    {z | z.2.1 ∈ torus}
  have hRclosed : IsClosed R := by
    exact (isClosed_le
      ((Metric.continuous_infDist_pt _).comp
        (continuous_subtype_val.comp continuous_snd)) continuous_const).inter
      (isClosed_le continuous_const
        ((Metric.continuous_infDist_pt _).comp
          (continuous_subtype_val.comp continuous_snd)))
  have hTclosed : IsClosed T := by
    exact isClosed_eq
      ((Metric.continuous_infDist_pt _).comp
        (continuous_subtype_val.comp continuous_snd)) continuous_const
  have hfR : ContinuousOn f R := by
    rw [continuousOn_iff_continuous_restrict]
    let q : C(R, Set.Icc (0 : ℝ) 1 × right) :=
      ⟨fun z => ⟨z.1.1, ⟨z.1.2.1, z.2⟩⟩,
        (continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_subtype_val.comp
            (continuous_snd.comp continuous_subtype_val)).subtype_mk _)⟩
    have heq : R.restrict f = g ∘ q := by
      funext z
      simp only [Set.restrict_apply, f, q, Function.comp_apply]
      have hz : z.1.2.1 ∈ right := z.2
      rw [dif_pos hz]
      congr 1
    rw [heq]
    exact hg.comp q.continuous
  have hfT : ContinuousOn f T := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : T.restrict f = fun z => z.1.2 := by
      funext z
      simp only [Set.restrict_apply, f]
      split_ifs with hz
      · apply Subtype.ext
        change (G (z.1.1, ⟨z.1.2.1, hz⟩)).1 = z.1.2.1
        exact congrArg Subtype.val (hfix z.1.1 ⟨z.1.2.1, hz⟩ (Or.inl z.2))
      · rfl
    rw [heq]
    exact continuous_snd.comp continuous_subtype_val
  have hcover' : R ∪ T = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true, R, T, right, torus]
    exact (hcover z.2).symm
  have hf : Continuous f := by
    rw [← continuousOn_univ, ← hcover']
    exact hfR.union_of_isClosed hfT hRclosed hTclosed
  let H : C(Set.Icc (0 : ℝ) 1 × apm_t02a03_shellY, apm_t02a03_shellY) := ⟨f, hf⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro p
    change f (⟨0, by norm_num⟩, p) = p
    simp only [f]
    split_ifs with hp
    · apply Subtype.ext
      change (G (⟨0, by norm_num⟩, ⟨p.1, hp⟩)).1 = p.1
      exact congrArg Subtype.val (hzero ⟨p.1, hp⟩)
    · rfl
  · intro p
    change (f (⟨1, by norm_num⟩, p)).1 ∈ _
    simp only [f]
    split_ifs with hp
    · exact hone ⟨p.1, hp⟩
    · exact Or.inl ((hcover p).resolve_right hp)
  · intro t p hp
    change f (t, p) = p
    simp only [f]
    split_ifs with hr
    · apply Subtype.ext
      change (G (t, ⟨p.1, hr⟩)).1 = p.1
      exact congrArg Subtype.val (hfix t ⟨p.1, hr⟩ hp)
    · rfl

/-- `shellY` deformation retracts onto the spine `torus ∪ loop`: glue the
core deformation of the right part to the identity on the torus (split
2026-10-19 from lemma-2's partial). -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction :
    ∃ r : C(apm_t02a03_shellY, apm_t02a03_shellY),
      (∀ p, (r p).1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop) ∧
      (∀ p, p.1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop → r p = p) ∧
      (ContinuousMap.id apm_t02a03_shellY).Homotopic r := by
  obtain ⟨G, hG0, hG1, hGfix⟩ :=
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core
  obtain ⟨H, hH0, hH1, hHfix⟩ :=
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_glue
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_cover G hG0 hG1 hGfix
  exact apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_of_deformation
    H hH0 hH1 hHfix

/-- LIBRARY: the compact shell is the boundary torus of the left tube glued,
along a disk, to the right tube minus the open left tube, which retracts to
the right core; so it has the homotopy type of the production torus-circle
wedge.  Assembly: retract onto the spine `torus ∪ loop`, which is
homeomorphic to `GenericWedge`. -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t02a03_shellY
      ConstructionTargets.TorusCircleWedgeOpenCover.GenericWedge) := by
  obtain ⟨r, hrZ, hrfix, hr⟩ :=
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction
  obtain ⟨hloop, hint⟩ :=
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_geometry
  obtain ⟨eT, heT⟩ :=
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph
  obtain ⟨eL, heL⟩ :=
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph
  obtain ⟨g⟩ :=
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_wedge_homeomorph
      _ _ _ hint eT eL heT heL
  have hCne : apm_t02a03_C.Nonempty := ⟨_, Set.mem_range_self 0⟩
  have hZ : ∀ p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop,
      p ∈ apm_t02a03_W ∧ (1 / 4 : ℝ) ≤ Metric.infDist p apm_t02a03_C := by
    rintro p (hp | hp)
    · refine ⟨?_, le_of_eq hp.symm⟩
      have hsub : apm_t02a03_C ⊆ apm_t02a03_genusTwoSpine := Set.subset_union_left
      have := Metric.infDist_le_infDist_of_subset (x := p) hsub hCne
      show Metric.infDist p apm_t02a03_genusTwoSpine ≤ 1 / 4
      have hp' : Metric.infDist p apm_t02a03_C = 1 / 4 := hp
      linarith
    · exact hloop p hp
  let i : C(↥(apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop), apm_t02a03_shellY) :=
    ⟨fun z => ⟨z.1, hZ z.1 z.2⟩, continuous_subtype_val.subtype_mk _⟩
  let ρ : C(apm_t02a03_shellY, ↥(apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop)) :=
    ⟨fun p => ⟨(r p).1, hrZ p⟩,
      (continuous_subtype_val.comp r.continuous).subtype_mk _⟩
  have hir : i.comp ρ = r := ContinuousMap.ext fun p => rfl
  have hρi : ρ.comp i = ContinuousMap.id _ := by
    refine ContinuousMap.ext fun z => Subtype.ext ?_
    show (r (i z)).1 = z.1
    rw [hrfix (i z) z.2]
    rfl
  let e : ContinuousMap.HomotopyEquiv apm_t02a03_shellY
      ↥(apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop) :=
    { toFun := ρ
      invFun := i
      left_inv := by rw [hir]; exact hr.symm
      right_inv := by rw [hρi] }
  exact ⟨e.trans g.toHomotopyEquiv⟩

/-- The explicit complement of the left core in the fixed genus-two
regular-neighborhood model has the homotopy type of the production
torus-circle wedge: compose the radial push with the shell equivalence. -/
theorem apm_t02a03_geometricY_homotopyEquiv_genericWedge :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t02a03_geometricY
      ConstructionTargets.TorusCircleWedgeOpenCover.GenericWedge) := by
  rcases apm_t02a03_geometricY_homotopyEquiv_shellY with ⟨e⟩
  rcases apm_t02a03_shellY_homotopyEquiv_genericWedge with ⟨f⟩
  exact ⟨e.trans f⟩

/-- Transport a geometric equivalence to the production wedge across the
already compiled homeomorphism with the registered quotient model.  The
geometric equivalence is an explicit hypothesis so this lemma is independent
of the admitted geometric construction. -/
theorem apm_t02a03_transport_genericWedge_homotopyEquiv
    (h : Nonempty (ContinuousMap.HomotopyEquiv apm_t02a03_geometricY
      ConstructionTargets.TorusCircleWedgeOpenCover.GenericWedge)) :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t02a03_geometricY apm_t02a03_Y) := by
  rcases h with ⟨e⟩
  exact ⟨e.trans apm_t02a03_productionHomeomorph.toHomotopyEquiv⟩

/-- The explicit complement of the left core in the fixed genus-two regular
neighborhood has the homotopy type of the registered torus-circle wedge. -/
theorem apm_t02a03_geometricY_homotopyEquiv_wedge :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t02a03_geometricY apm_t02a03_Y) := by
  exact apm_t02a03_transport_genericWedge_homotopyEquiv
    apm_t02a03_geometricY_homotopyEquiv_genericWedge

theorem apm_t02a03 :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t02a03_X apm_t02a03_Torus) ∧
    Nonempty (ContinuousMap.HomotopyEquiv apm_t02a03_geometricY apm_t02a03_Y) ∧
    Nonempty
      (FundamentalGroup apm_t02a03_Torus (1, 1) ≃*
        Multiplicative (ℤ × ℤ)) ∧
    Nonempty
      (FundamentalGroup apm_t02a03_Y apm_t02a03_ybase ≃*
        Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative ℤ)) ∧
    Nonempty
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a03_Y) ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a03_Y) ≅
        ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    Nonempty
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a03_Y) ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ n : ℕ, 3 ≤ n →
      Limits.IsZero
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a03_Y))) := by
  refine ⟨?_, ?_, apm_t02A03_bridge_1, apm_t02A03_bridge_2⟩
  · exact ConstructionTargets.T02A03ClosedPuncturedDiskTorus.t02a03_closed_punctured_disk_torus
  · exact apm_t02a03_geometricY_homotopyEquiv_wedge

#print axioms apm_t02a03
