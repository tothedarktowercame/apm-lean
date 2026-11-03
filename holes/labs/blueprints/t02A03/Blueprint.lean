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
noncomputable def apm_t02a03_geometricY_homotopyEquiv_shellY_aux_inclusion :
    C(apm_t02a03_shellY, apm_t02a03_geometricY) where
  toFun p := ⟨p.1, p.2.1, by
    intro hpC
    have hz : Metric.infDist p.1 apm_t02a03_C = 0 :=
      Metric.infDist_zero_of_mem hpC
    linarith [p.2.2]⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The geometric leaf: a strong deformation which radially pushes every
point less than `1/4` from the deleted left core out to the distance shell.
Keeping the endpoint and fixed-point assertions explicit makes the purely
homotopy-theoretic packaging independent of its coordinate construction. -/
lemma apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_infDist
    (p : apm_t02a03_E3) :
    Metric.infDist p apm_t02a03_C =
      Real.sqrt ((Real.sqrt ((p 0 + 6 / 5) ^ 2 + p 1 ^ 2) - 1) ^ 2 + p 2 ^ 2) := by
  let a : ℝ := p 0 + 6 / 5
  let b : ℝ := p 1
  let s : ℝ := Real.sqrt (a ^ 2 + b ^ 2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a ^ 2 + b ^ 2 := by
    dsimp [s]
    rw [Real.sq_sqrt]
    positivity
  have lower : Real.sqrt ((s - 1) ^ 2 + p 2 ^ 2) ≤
      Metric.infDist p (Set.range apm_t02a03_leftCore) := by
    rw [Metric.le_infDist]
    · rintro q ⟨t, rfl⟩
      have htrig : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 :=
        Real.sin_sq_add_cos_sq t
      have hcs : (a * Real.cos t + b * Real.sin t) ^ 2 ≤ s ^ 2 := by
        nlinarith [sq_nonneg (a * Real.sin t - b * Real.cos t)]
      have hdot : a * Real.cos t + b * Real.sin t ≤ s := by
        nlinarith [sq_nonneg (s - (a * Real.cos t + b * Real.sin t))]
      rw [show dist p (apm_t02a03_leftCore t) =
          Real.sqrt ((a - Real.cos t) ^ 2 + (b - Real.sin t) ^ 2 + p 2 ^ 2) by
        simp [dist_eq_norm, apm_t02a03_leftCore, a, b, EuclideanSpace.norm_eq,
          Fin.sum_univ_succ]
        congr 1 <;> ring]
      exact Real.sqrt_le_sqrt (by nlinarith)
    · exact ⟨apm_t02a03_leftCore 0, ⟨0, rfl⟩⟩
  apply le_antisymm
  · by_cases hz : (a : ℂ) + b * Complex.I = 0
    · have ha : a = 0 := by
        have := congrArg Complex.re hz
        simpa using this
      have hb : b = 0 := by
        have := congrArg Complex.im hz
        simpa using this
      have hs : s = 0 := by simp [s, ha, hb]
      have hp0 : p 0 = -6 / 5 := by dsimp [a] at ha; linarith
      have hp1 : p 1 = 0 := by simpa [b] using hb
      calc
        Metric.infDist p (Set.range apm_t02a03_leftCore)
            ≤ dist p (apm_t02a03_leftCore 0) :=
              Metric.infDist_le_dist_of_mem ⟨0, rfl⟩
        _ = Real.sqrt ((s - 1) ^ 2 + p 2 ^ 2) := by
          simp [dist_eq_norm, apm_t02a03_leftCore, hp0, hp1, hs,
            EuclideanSpace.norm_eq, Fin.sum_univ_succ]
    · let z : ℂ := (a : ℂ) + b * Complex.I
      have hz' : z ≠ 0 := by simpa [z] using hz
      have hnorm : ‖z‖ = s := by
        rw [Complex.norm_def]
        congr 1
        simp [Complex.normSq_apply, z, s]
        ring
      have hc : Real.cos (Complex.arg z) = a / s := by
        rw [Complex.cos_arg hz', hnorm]
        simp [z]
      have hsi : Real.sin (Complex.arg z) = b / s := by
        rw [Complex.sin_arg, hnorm]
        simp [z]
      have hspos : 0 < s := lt_of_le_of_ne hs0 (by
        intro h
        apply hz'
        apply Complex.ext <;> simp [z] at * <;> nlinarith [hs2])
      calc
        Metric.infDist p (Set.range apm_t02a03_leftCore)
            ≤ dist p (apm_t02a03_leftCore (Complex.arg z)) :=
              Metric.infDist_le_dist_of_mem ⟨_, rfl⟩
        _ = Real.sqrt ((s - 1) ^ 2 + p 2 ^ 2) := by
          rw [show dist p (apm_t02a03_leftCore (Complex.arg z)) =
              Real.sqrt ((a - Real.cos (Complex.arg z)) ^ 2 +
                (b - Real.sin (Complex.arg z)) ^ 2 + p 2 ^ 2) by
            simp [dist_eq_norm, apm_t02a03_leftCore, a, b, EuclideanSpace.norm_eq,
              Fin.sum_univ_succ]
            congr 1 <;> ring]
          congr 1
          rw [hc, hsi]
          field_simp
          nlinarith [hs2]
  · change Real.sqrt ((s - 1) ^ 2 + p 2 ^ 2) ≤ _
    exact lower

/-- Radial push off the left core: at time `t` a point at distance `d < 1/4`
from `C` moves along its normal ray in the meridian half-plane by the factor
`1 + gain`, ending at distance `d + t * (1/4 - d)`.  Points at distance
`≥ 1/4` have `gain = 0`.  The `max s (1/2)` only guards the core axis `s = 0`,
which is at distance `≥ 1` from `C` and so has `gain = 0` anyway. -/
noncomputable def apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_gain (t : ℝ) (p : apm_t02a03_E3) : ℝ :=
  t * max 0 (1 / 4 - Metric.infDist p apm_t02a03_C) / Metric.infDist p apm_t02a03_C

noncomputable def apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move (t : ℝ) (p : apm_t02a03_E3) : apm_t02a03_E3 :=
  let g := apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_gain t p
  let s := Real.sqrt ((p 0 + 6 / 5) ^ 2 + p 1 ^ 2)
  let k := g * (s - 1) / max s (1 / 2)
  WithLp.toLp 2 ![p 0 + k * (p 0 + 6 / 5), p 1 + k * p 1, p 2 + g * p 2]

/-- Leaf: points off the left core are at positive distance from it. -/
lemma apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_pos (p : apm_t02a03_E3) (hp : p ∉ apm_t02a03_C) :
    0 < Metric.infDist p apm_t02a03_C := by
  rw [Metric.infDist_nonneg.lt_iff_ne]
  intro hd
  rw [apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_infDist] at hd
  have hrad : (Real.sqrt ((p 0 + 6 / 5) ^ 2 + p 1 ^ 2) - 1) ^ 2 + p 2 ^ 2 = 0 := by
    have hle := (Real.sqrt_eq_zero').mp hd.symm
    nlinarith [sq_nonneg (Real.sqrt ((p 0 + 6 / 5) ^ 2 + p 1 ^ 2) - 1),
      sq_nonneg (p 2)]
  have hs : Real.sqrt ((p 0 + 6 / 5) ^ 2 + p 1 ^ 2) = 1 := by
    nlinarith [sq_nonneg (Real.sqrt ((p 0 + 6 / 5) ^ 2 + p 1 ^ 2) - 1),
      sq_nonneg (p 2)]
  have hp2 : p 2 = 0 := by nlinarith [sq_nonneg (p 2)]
  let z : ℂ := (p 0 + 6 / 5 : ℝ) + p 1 * Complex.I
  have hz : z ≠ 0 := by
    intro hz0
    have hre : p 0 + 6 / 5 = 0 := by
      have := congrArg Complex.re hz0
      simpa [z] using this
    have him : p 1 = 0 := by
      have := congrArg Complex.im hz0
      simpa [z] using this
    simp [hre, him] at hs
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def]
    simp [Complex.normSq_apply, z]
    rw [show (p 0 + 6 / 5) * (p 0 + 6 / 5) + p 1 * p 1 =
        (p 0 + 6 / 5) ^ 2 + p 1 ^ 2 by ring]
    have hsq : (p 0 + 6 / 5) ^ 2 + p 1 ^ 2 = 1 := by
      have hr := Real.sq_sqrt (show 0 ≤ (p 0 + 6 / 5) ^ 2 + p 1 ^ 2 by positivity)
      nlinarith [congrArg (fun x : ℝ ↦ x ^ 2) hs]
    rw [hsq]
  apply hp
  refine ⟨Complex.arg z, ?_⟩
  ext i
  fin_cases i
  · have hc : Real.cos (Complex.arg z) = p 0 + 6 / 5 := by
      rw [Complex.cos_arg hz, hn]
      simp [z]
    simp [apm_t02a03_leftCore, hc]
    ring
  · have hsin : Real.sin (Complex.arg z) = p 1 := by
      rw [Complex.sin_arg, hn]
      simp [z]
    simp [apm_t02a03_leftCore, hsin]
  · simp [apm_t02a03_leftCore, hp2]

/-- Leaf: the push is continuous on `[0,1] × geometricY`. -/
lemma apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_continuous_aux_ne
    (p : apm_t02a03_E3) (hp : p ∉ apm_t02a03_C) :
    Metric.infDist p apm_t02a03_C ≠ 0 := by
  intro hd
  rw [apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_infDist] at hd
  have hrad : (Real.sqrt ((p 0 + 6 / 5) ^ 2 + p 1 ^ 2) - 1) ^ 2 + p 2 ^ 2 = 0 := by
    have hle := (Real.sqrt_eq_zero').mp hd
    nlinarith [sq_nonneg (Real.sqrt ((p 0 + 6 / 5) ^ 2 + p 1 ^ 2) - 1),
      sq_nonneg (p 2)]
  have hs : Real.sqrt ((p 0 + 6 / 5) ^ 2 + p 1 ^ 2) = 1 := by
    nlinarith [sq_nonneg (Real.sqrt ((p 0 + 6 / 5) ^ 2 + p 1 ^ 2) - 1),
      sq_nonneg (p 2)]
  have hp2 : p 2 = 0 := by nlinarith [sq_nonneg (p 2)]
  let z : ℂ := (p 0 + 6 / 5 : ℝ) + p 1 * Complex.I
  have hz : z ≠ 0 := by
    intro hz0
    have hre : p 0 + 6 / 5 = 0 := by
      have := congrArg Complex.re hz0
      simpa [z] using this
    have him : p 1 = 0 := by
      have := congrArg Complex.im hz0
      simpa [z] using this
    simp [hre, him] at hs
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def]
    simp [Complex.normSq_apply, z]
    rw [show (p 0 + 6 / 5) * (p 0 + 6 / 5) + p 1 * p 1 =
        (p 0 + 6 / 5) ^ 2 + p 1 ^ 2 by ring]
    have hsq : (p 0 + 6 / 5) ^ 2 + p 1 ^ 2 = 1 := by
      have hr := Real.sq_sqrt (show 0 ≤ (p 0 + 6 / 5) ^ 2 + p 1 ^ 2 by positivity)
      nlinarith [congrArg (fun x : ℝ ↦ x ^ 2) hs]
    rw [hsq]
  apply hp
  refine ⟨Complex.arg z, ?_⟩
  ext i
  fin_cases i
  · have hc : Real.cos (Complex.arg z) = p 0 + 6 / 5 := by
      rw [Complex.cos_arg hz, hn]
      simp [z]
    simp [apm_t02a03_leftCore, hc]
    ring
  · have hsin : Real.sin (Complex.arg z) = p 1 := by
      rw [Complex.sin_arg, hn]
      simp [z]
    simp [apm_t02a03_leftCore, hsin]
  · simp [apm_t02a03_leftCore, hp2]

lemma apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_continuous :
    Continuous (fun q : Set.Icc (0 : ℝ) 1 × apm_t02a03_geometricY =>
      apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move q.1.1 q.2.1) := by
  let d : Set.Icc (0 : ℝ) 1 × apm_t02a03_geometricY → ℝ :=
    fun q ↦ Metric.infDist q.2.1 apm_t02a03_C
  have hd : Continuous d :=
    (Metric.continuous_infDist_pt _).comp
      (continuous_subtype_val.comp continuous_snd)
  have hd0 : ∀ q, d q ≠ 0 := fun q ↦
    apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_continuous_aux_ne
      q.2.1 q.2.2.2
  let g : Set.Icc (0 : ℝ) 1 × apm_t02a03_geometricY → ℝ :=
    fun q ↦ q.1.1 * max 0 (1 / 4 - d q) / d q
  have hg : Continuous g := by
    dsimp [g]
    exact ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_const.max (continuous_const.sub hd))).div₀ hd hd0
  let s : Set.Icc (0 : ℝ) 1 × apm_t02a03_geometricY → ℝ :=
    fun q ↦ Real.sqrt ((q.2.1 0 + 6 / 5) ^ 2 + q.2.1 1 ^ 2)
  have hs : Continuous s := by dsimp [s]; fun_prop
  have hmax : ∀ q, max (s q) (1 / 2) ≠ 0 := by
    intro q
    have : (0 : ℝ) < 1 / 2 := by norm_num
    exact ne_of_gt (this.trans_le (le_max_right _ _))
  let k : Set.Icc (0 : ℝ) 1 × apm_t02a03_geometricY → ℝ :=
    fun q ↦ g q * (s q - 1) / max (s q) (1 / 2)
  have hk : Continuous k := by
    dsimp [k]
    exact (hg.mul (hs.sub continuous_const)).div₀
      (hs.max continuous_const) hmax
  unfold apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move
  change Continuous (fun q => WithLp.toLp 2
    ![q.2.1 0 + k q * (q.2.1 0 + 6 / 5),
      q.2.1 1 + k q * q.2.1 1, q.2.1 2 + g q * q.2.1 2])
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_)
  fin_cases i <;> simp <;> fun_prop

/-- Leaf: the distance to `C` after the push (use `_aux_infDist`). -/
lemma apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move_infDist (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (p : apm_t02a03_E3) (hp : 0 < Metric.infDist p apm_t02a03_C) :
    Metric.infDist (apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move t p) apm_t02a03_C =
      Metric.infDist p apm_t02a03_C + t * max 0 (1 / 4 - Metric.infDist p apm_t02a03_C) := by
  let d := Metric.infDist p apm_t02a03_C
  let s := Real.sqrt ((p 0 + 6 / 5) ^ 2 + p 1 ^ 2)
  let e := max 0 (1 / 4 - d)
  let g := t * e / d
  have hd : d = Real.sqrt ((s - 1) ^ 2 + p 2 ^ 2) := by
    simp only [d, s]
    exact apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_infDist p
  have hd0 : 0 < d := hp
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  by_cases he : e = 0
  · have hg : g = 0 := by simp [g, he]
    have hgain : apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_gain t p = 0 := by
      change t * max 0 (1 / 4 - d) / d = 0
      change t * e / d = 0
      simp [he]
    have hmove : apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move t p = p := by
      ext i
      fin_cases i <;>
        simp [apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move,
          hgain]
    rw [hmove]
    change d = d + t * e
    simp [he]
  · have heq : e = 1 / 4 - d := by
      dsimp [e]
      rw [max_eq_right]
      by_contra h
      have : 1 / 4 - d ≤ 0 := le_of_not_ge h
      apply he
      dsimp [e]
      exact max_eq_left this
    have hdlt : d < 1 / 4 := by
      have hepos : 0 < e := lt_of_le_of_ne (le_max_left _ _) (Ne.symm he)
      linarith
    have hs : 1 / 2 < s := by
      have hsq : (s - 1) ^ 2 < (1 / 4 : ℝ) ^ 2 := by
        have hd_sq : d ^ 2 = (s - 1) ^ 2 + p 2 ^ 2 := by
          rw [hd, Real.sq_sqrt]
          positivity
        nlinarith [sq_nonneg (p 2)]
      nlinarith [sq_nonneg (s - 1 / 2)]
    have hmax : max s (1 / 2) = s := max_eq_left (le_of_lt hs)
    have hg0 : 0 ≤ g := by positivity
    have hgs : 0 < 1 + g * (s - 1) / s := by
      have hgd : g * d = t * e := by
        dsimp [g]
        field_simp [ne_of_gt hd0]
      have hg_le : g * d ≤ e := by nlinarith
      have habs : |s - 1| ≤ d := by
        have hd_sq : d ^ 2 = (s - 1) ^ 2 + p 2 ^ 2 := by
          rw [hd, Real.sq_sqrt]
          positivity
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (p 2), sq_nonneg (d + (s - 1)),
          sq_nonneg (d - (s - 1))]
      have : g * |s - 1| ≤ e := (mul_le_mul_of_nonneg_left habs hg0).trans hg_le
      have he_lt : e < s := by rw [heq]; nlinarith
      rcases le_total 1 s with h | h
      · exact add_pos_of_pos_of_nonneg zero_lt_one
          (div_nonneg (mul_nonneg hg0 (sub_nonneg.mpr h)) hs0)
      · rw [abs_of_nonpos (sub_nonpos.mpr h)] at this
        have hsmall : g * (1 - s) < s := by nlinarith [lt_of_le_of_lt this he_lt]
        rw [show 1 + g * (s - 1) / s = (s + g * (s - 1)) / s by
          field_simp]
        exact div_pos (by nlinarith) (by linarith)
    rw [apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_infDist]
    have hgain_eq : apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_gain t p = g := by
      rfl
    simp only [apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hgain_eq, hmax]
    change Real.sqrt ((Real.sqrt
      ((p 0 + g * (s - 1) / s * (p 0 + 6 / 5) + 6 / 5) ^ 2 +
       (p 1 + g * (s - 1) / s * p 1) ^ 2) - 1) ^ 2 +
       (p 2 + g * p 2) ^ 2) = d + t * e
    have hs_sq : s ^ 2 = (p 0 + 6 / 5) ^ 2 + p 1 ^ 2 := by
      dsimp [s]
      rw [Real.sq_sqrt]
      positivity
    have hradius : Real.sqrt
        ((p 0 + g * (s - 1) / s * (p 0 + 6 / 5) + 6 / 5) ^ 2 +
         (p 1 + g * (s - 1) / s * p 1) ^ 2) =
        s + g * (s - 1) := by
      rw [show
        (p 0 + g * (s - 1) / s * (p 0 + 6 / 5) + 6 / 5) ^ 2 +
          (p 1 + g * (s - 1) / s * p 1) ^ 2 =
          (1 + g * (s - 1) / s) ^ 2 * s ^ 2 by
            field_simp
            nlinarith [hs_sq]]
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
        Real.sqrt_sq_eq_abs, abs_of_nonneg hs0, abs_of_pos hgs]
      field_simp
    rw [hradius]
    have hinside :
        (s + g * (s - 1) - 1) ^ 2 + (p 2 + g * p 2) ^ 2 =
          (1 + g) ^ 2 * d ^ 2 := by
      have hd_sq : d ^ 2 = (s - 1) ^ 2 + p 2 ^ 2 := by
        rw [hd, Real.sq_sqrt]
        positivity
      rw [hd_sq]
      ring
    rw [hinside, Real.sqrt_mul (sq_nonneg (1 + g)),
      Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 1 + g), abs_of_pos hd0]
    have hgd : g * d = t * e := by
      dsimp [g]
      field_simp [ne_of_gt hd0]
    calc
      (1 + g) * d = d + g * d := by ring
      _ = d + t * e := by rw [hgd]

lemma apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move_of_gain (t : ℝ) (p : apm_t02a03_E3)
    (h : apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_gain t p = 0) : apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move t p = p := by
  ext i; fin_cases i <;> simp [apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move, h]

lemma apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move_zero (p : apm_t02a03_E3) : apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move 0 p = p :=
  apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move_of_gain 0 p (by simp [apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_gain])

lemma apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move_far (t : ℝ) (p : apm_t02a03_E3)
    (hp : (1 / 4 : ℝ) ≤ Metric.infDist p apm_t02a03_C) : apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move t p = p :=
  apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move_of_gain t p (by
    unfold apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_gain; rw [max_eq_left (by linarith)]; simp)

lemma apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_mem (t : Set.Icc (0 : ℝ) 1) (p : apm_t02a03_geometricY) :
    apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move t.1 p.1 ∈ apm_t02a03_W ∧ apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move t.1 p.1 ∉ apm_t02a03_C := by
  have hpos := apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_pos p.1 p.2.2
  by_cases hfar : (1 / 4 : ℝ) ≤ Metric.infDist p.1 apm_t02a03_C
  · rw [apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move_far t.1 p.1 hfar]; exact p.2
  have hd := apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move_infDist t.1 t.2.1 t.2.2 p.1 hpos
  have hm : max 0 (1 / 4 - Metric.infDist p.1 apm_t02a03_C) =
      1 / 4 - Metric.infDist p.1 apm_t02a03_C := max_eq_right (by linarith)
  rw [hm] at hd
  refine ⟨?_, fun hC => ?_⟩
  · show Metric.infDist _ apm_t02a03_genusTwoSpine ≤ 1 / 4
    refine (Metric.infDist_le_infDist_of_subset
      (Set.subset_union_left : Set.range apm_t02a03_leftCore ⊆ apm_t02a03_genusTwoSpine)
      (show (Set.range apm_t02a03_leftCore).Nonempty from ⟨_, ⟨0, rfl⟩⟩)).trans ?_
    change Metric.infDist _ apm_t02a03_C ≤ 1 / 4
    rw [hd]; nlinarith [t.2.1, t.2.2]
  · have h0 := Metric.infDist_zero_of_mem hC
    rw [hd] at h0; nlinarith [t.2.1, t.2.2]

theorem apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation :
    ∃ H : C(Set.Icc (0 : ℝ) 1 × apm_t02a03_geometricY,
        apm_t02a03_geometricY),
      (∀ p, H (⟨0, by norm_num⟩, p) = p) ∧
      (∀ p, (1 / 4 : ℝ) ≤ Metric.infDist (H (⟨1, by norm_num⟩, p)).1
        apm_t02a03_C) ∧
      (∀ t p, (1 / 4 : ℝ) ≤ Metric.infDist p.1 apm_t02a03_C →
        H (t, p) = p) := by
  refine ⟨⟨fun q => ⟨apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move q.1.1 q.2.1, apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_mem q.1 q.2⟩,
    (apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_continuous).subtype_mk _⟩, ?_, ?_, ?_⟩
  · intro p; apply Subtype.ext; exact apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move_zero p.1
  · intro p
    show (1 / 4 : ℝ) ≤ Metric.infDist (apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move 1 p.1) apm_t02a03_C
    by_cases hfar : (1 / 4 : ℝ) ≤ Metric.infDist p.1 apm_t02a03_C
    · rw [apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move_far 1 p.1 hfar]; exact hfar
    rw [apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move_infDist 1 zero_le_one le_rfl p.1 (apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_pos p.1 p.2.2),
      max_eq_right (by linarith)]
    linarith
  · intro t p hp; apply Subtype.ext; exact apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation_aux_move_far t.1 p.1 hp

theorem apm_t02a03_geometricY_homotopyEquiv_shellY_aux_of_deformation
    (H : C(Set.Icc (0 : ℝ) 1 × apm_t02a03_geometricY,
      apm_t02a03_geometricY))
    (hzero : ∀ p, H (⟨0, by norm_num⟩, p) = p)
    (hone : ∀ p, (1 / 4 : ℝ) ≤ Metric.infDist
      (H (⟨1, by norm_num⟩, p)).1 apm_t02a03_C)
    (hfix : ∀ t p, (1 / 4 : ℝ) ≤ Metric.infDist p.1 apm_t02a03_C →
      H (t, p) = p) :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t02a03_geometricY
      apm_t02a03_shellY) := by
  let r : C(apm_t02a03_geometricY, apm_t02a03_shellY) :=
    { toFun := fun p ↦ ⟨(H (⟨1, by norm_num⟩, p)).1,
        (H (⟨1, by norm_num⟩, p)).2.1, hone p⟩
      continuous_toFun := by fun_prop }
  let i := apm_t02a03_geometricY_homotopyEquiv_shellY_aux_inclusion
  have hleft : (i.comp r).Homotopic (ContinuousMap.id _) := by
    symm
    exact ⟨{
      toFun := H
      map_zero_left := hzero
      map_one_left := fun p ↦ rfl }⟩
  have hright : (r.comp i).Homotopic (ContinuousMap.id _) := by
    rw [show r.comp i = ContinuousMap.id _ by
      apply ContinuousMap.ext
      intro p
      apply Subtype.ext
      dsimp [r, i]
      exact congrArg Subtype.val (hfix ⟨1, by norm_num⟩ (i p) p.2.2)]
  exact ⟨{
    toFun := r
    invFun := i
    left_inv := hleft
    right_inv := hright }⟩

theorem apm_t02a03_geometricY_homotopyEquiv_shellY :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t02a03_geometricY apm_t02a03_shellY) := by
  rcases apm_t02a03_geometricY_homotopyEquiv_shellY_aux_deformation with
    ⟨H, hzero, hone, hfix⟩
  exact apm_t02a03_geometricY_homotopyEquiv_shellY_aux_of_deformation
    H hzero hone hfix

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
lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_infDist
    (p : apm_t02a03_E3) :
    Metric.infDist p apm_t02a03_C =
      Real.sqrt ((Real.sqrt ((p 0 + 6 / 5) ^ 2 + p 1 ^ 2) - 1) ^ 2 + p 2 ^ 2) := by
  let a : ℝ := p 0 + 6 / 5
  let b : ℝ := p 1
  let s : ℝ := Real.sqrt (a ^ 2 + b ^ 2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a ^ 2 + b ^ 2 := by
    dsimp [s]
    rw [Real.sq_sqrt]
    positivity
  have lower : Real.sqrt ((s - 1) ^ 2 + p 2 ^ 2) ≤
      Metric.infDist p (Set.range apm_t02a03_leftCore) := by
    rw [Metric.le_infDist]
    · rintro q ⟨t, rfl⟩
      have htrig : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 :=
        Real.sin_sq_add_cos_sq t
      have hcs : (a * Real.cos t + b * Real.sin t) ^ 2 ≤ s ^ 2 := by
        nlinarith [sq_nonneg (a * Real.sin t - b * Real.cos t)]
      have hdot : a * Real.cos t + b * Real.sin t ≤ s := by
        nlinarith [sq_nonneg (s - (a * Real.cos t + b * Real.sin t))]
      rw [show dist p (apm_t02a03_leftCore t) =
          Real.sqrt ((a - Real.cos t) ^ 2 + (b - Real.sin t) ^ 2 + p 2 ^ 2) by
        simp [dist_eq_norm, apm_t02a03_leftCore, a, b, EuclideanSpace.norm_eq,
          Fin.sum_univ_succ]
        congr 1 <;> ring]
      exact Real.sqrt_le_sqrt (by nlinarith)
    · exact ⟨apm_t02a03_leftCore 0, ⟨0, rfl⟩⟩
  apply le_antisymm
  · by_cases hz : (a : ℂ) + b * Complex.I = 0
    · have ha : a = 0 := by
        have := congrArg Complex.re hz
        simpa using this
      have hb : b = 0 := by
        have := congrArg Complex.im hz
        simpa using this
      have hs : s = 0 := by simp [s, ha, hb]
      have hp0 : p 0 = -6 / 5 := by dsimp [a] at ha; linarith
      have hp1 : p 1 = 0 := by simpa [b] using hb
      calc
        Metric.infDist p (Set.range apm_t02a03_leftCore)
            ≤ dist p (apm_t02a03_leftCore 0) :=
              Metric.infDist_le_dist_of_mem ⟨0, rfl⟩
        _ = Real.sqrt ((s - 1) ^ 2 + p 2 ^ 2) := by
          simp [dist_eq_norm, apm_t02a03_leftCore, hp0, hp1, hs,
            EuclideanSpace.norm_eq, Fin.sum_univ_succ]
    · let z : ℂ := (a : ℂ) + b * Complex.I
      have hz' : z ≠ 0 := by simpa [z] using hz
      have hnorm : ‖z‖ = s := by
        rw [Complex.norm_def]
        congr 1
        simp [Complex.normSq_apply, z, s]
        ring
      have hc : Real.cos (Complex.arg z) = a / s := by
        rw [Complex.cos_arg hz', hnorm]
        simp [z]
      have hsi : Real.sin (Complex.arg z) = b / s := by
        rw [Complex.sin_arg, hnorm]
        simp [z]
      have hspos : 0 < s := lt_of_le_of_ne hs0 (by
        intro h
        apply hz'
        apply Complex.ext <;> simp [z] at * <;> nlinarith [hs2])
      calc
        Metric.infDist p (Set.range apm_t02a03_leftCore)
            ≤ dist p (apm_t02a03_leftCore (Complex.arg z)) :=
              Metric.infDist_le_dist_of_mem ⟨_, rfl⟩
        _ = Real.sqrt ((s - 1) ^ 2 + p 2 ^ 2) := by
          rw [show dist p (apm_t02a03_leftCore (Complex.arg z)) =
              Real.sqrt ((a - Real.cos (Complex.arg z)) ^ 2 +
                (b - Real.sin (Complex.arg z)) ^ 2 + p 2 ^ 2) by
            simp [dist_eq_norm, apm_t02a03_leftCore, a, b, EuclideanSpace.norm_eq,
              Fin.sum_univ_succ]
            congr 1 <;> ring]
          congr 1
          rw [hc, hsi]
          field_simp
          nlinarith [hs2]
  · change Real.sqrt ((s - 1) ^ 2 + p 2 ^ 2) ≤ _
    exact lower

/-- The standard parametrisation of the left boundary torus: core angle `x.1`,
normal angle `x.2` (measured from the outward radial direction). -/
noncomputable def apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param (x : apm_t02a03_Torus) : apm_t02a03_E3 :=
  WithLp.toLp 2 ![-6 / 5 + (1 + (x.2 : ℂ).re / 4) * (x.1 : ℂ).re,
    (1 + (x.2 : ℂ).re / 4) * (x.1 : ℂ).im, (x.2 : ℂ).im / 4]

lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param_continuous : Continuous apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param := by
  unfold apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_)
  fin_cases i <;> simp <;> fun_prop

lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param_one : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param (1, 1) =
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_q0 := by
  ext i
  fin_cases i <;>
    simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_q0] <;> norm_num

/-- The parametrisation lands on the torus (use `_aux_infDist`: the planar radius
is `1 + re v / 4 > 0`). -/
lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_mem (x : apm_t02a03_Torus) :
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param x ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus := by
  have hu : (x.1 : ℂ).re ^ 2 + (x.1 : ℂ).im ^ 2 = 1 := by
    calc
      (x.1 : ℂ).re ^ 2 + (x.1 : ℂ).im ^ 2 = Complex.normSq (x.1 : ℂ) := by
        rw [Complex.normSq_apply]
        ring
      _ = ‖(x.1 : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq _
      _ = 1 := by rw [Circle.norm_coe]; norm_num
  have hv : (x.2 : ℂ).re ^ 2 + (x.2 : ℂ).im ^ 2 = 1 := by
    calc
      (x.2 : ℂ).re ^ 2 + (x.2 : ℂ).im ^ 2 = Complex.normSq (x.2 : ℂ) := by
        rw [Complex.normSq_apply]
        ring
      _ = ‖(x.2 : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq _
      _ = 1 := by rw [Circle.norm_coe]; norm_num
  have hvre : -1 ≤ (x.2 : ℂ).re := by
    have h := Complex.abs_re_le_norm (x.2 : ℂ)
    rw [Circle.norm_coe] at h
    exact (neg_le_of_abs_le h)
  have hr : 0 ≤ 1 + (x.2 : ℂ).re / 4 := by linarith
  have hsqrt :
      Real.sqrt (((1 + (x.2 : ℂ).re / 4) * (x.1 : ℂ).re) ^ 2 +
        ((1 + (x.2 : ℂ).re / 4) * (x.1 : ℂ).im) ^ 2) =
        1 + (x.2 : ℂ).re / 4 := by
    rw [show
      ((1 + (x.2 : ℂ).re / 4) * (x.1 : ℂ).re) ^ 2 +
          ((1 + (x.2 : ℂ).re / 4) * (x.1 : ℂ).im) ^ 2 =
        (1 + (x.2 : ℂ).re / 4) ^ 2 by nlinarith]
    exact Real.sqrt_sq hr
  change Metric.infDist _ apm_t02a03_C = (1 / 4 : ℝ)
  rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_infDist]
  simp only [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
    Matrix.head_cons, Matrix.tail_cons]
  rw [show -6 / 5 + (1 + (x.2 : ℂ).re / 4) * (x.1 : ℂ).re + 6 / 5 =
    (1 + (x.2 : ℂ).re / 4) * (x.1 : ℂ).re by ring, hsqrt]
  change Real.sqrt ((1 + (x.2 : ℂ).re / 4 - 1) ^ 2 +
    ((x.2 : ℂ).im / 4) ^ 2) = 1 / 4
  rw [show
    ((1 + (x.2 : ℂ).re / 4 - 1) ^ 2 + ((x.2 : ℂ).im / 4) ^ 2) =
      (1 / 4 : ℝ) ^ 2 by nlinarith]
  norm_num

/-- The parametrisation is injective (the planar radius `1 + re v / 4` is
positive, so `u` is the planar direction and then `v` is read off). -/
lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_injective : Function.Injective apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  have hcoord (i : Fin 3) := congrArg (fun p : apm_t02a03_E3 ↦ p i) h
  have him : (v : ℂ).im = (v' : ℂ).im := by
    simpa [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param]
      using hcoord 2
  have hplan :
      (1 + (v : ℂ).re / 4 : ℝ) * (u : ℂ) =
        (1 + (v' : ℂ).re / 4 : ℝ) * (u' : ℂ) := by
    apply Complex.ext
    · simpa [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param]
        using hcoord 0
    · simpa [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param]
        using hcoord 1
  have hvnorm : (v : ℂ).re ^ 2 + (v : ℂ).im ^ 2 = 1 := by
    calc
      _ = Complex.normSq (v : ℂ) := by simp [Complex.normSq_apply]; ring
      _ = ‖(v : ℂ)‖ ^ 2 := (Complex.sq_norm _).symm
      _ = 1 := by rw [Circle.norm_coe]; norm_num
  have hvnorm' : (v' : ℂ).re ^ 2 + (v' : ℂ).im ^ 2 = 1 := by
    calc
      _ = Complex.normSq (v' : ℂ) := by simp [Complex.normSq_apply]; ring
      _ = ‖(v' : ℂ)‖ ^ 2 := (Complex.sq_norm _).symm
      _ = 1 := by rw [Circle.norm_coe]; norm_num
  have hre : (v : ℂ).re = (v' : ℂ).re := by
    have hsquares : (v : ℂ).re ^ 2 = (v' : ℂ).re ^ 2 := by
      rw [him] at hvnorm
      nlinarith
    have hle : (v : ℂ).re ≥ -1 := by nlinarith [sq_nonneg ((v : ℂ).im)]
    have hle' : (v' : ℂ).re ≥ -1 := by nlinarith [sq_nonneg ((v' : ℂ).im)]
    have hscale : 1 + (v : ℂ).re / 4 = 1 + (v' : ℂ).re / 4 := by
      have hunorm : Complex.normSq (u : ℂ) = 1 := by
        rw [Complex.normSq_eq_norm_sq, Circle.norm_coe]
        norm_num
      have hunorm' : Complex.normSq (u' : ℂ) = 1 := by
        rw [Complex.normSq_eq_norm_sq, Circle.norm_coe]
        norm_num
      have hn := congrArg Complex.normSq hplan
      rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
        Complex.normSq_ofReal, hunorm, hunorm'] at hn
      nlinarith
    linarith
  have hv : v = v' := by
    apply Subtype.ext
    apply Complex.ext <;> assumption
  subst v'
  have hu : u = u' := by
    apply Subtype.ext
    apply (mul_left_cancel₀ (show (1 + (v : ℂ).re / 4 : ℂ) ≠ 0 by
      have hle : (v : ℂ).re ≥ -1 := by
        nlinarith [hvnorm]
      exact_mod_cast (show (1 + (v : ℂ).re / 4 : ℝ) ≠ 0 by linarith)))
    exact_mod_cast hplan
  subst u'
  rfl

/-- Every torus point is parametrised (use `_aux_infDist`: with `s` the planar
radius about the core centre, `s ≥ 3/4`; take `u = (a + b i)/s` and
`v = 4((s - 1) + z i)`). -/
lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_surj (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus) :
    ∃ x, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param x = p := by
  let a : ℝ := p 0 + 6 / 5
  let b : ℝ := p 1
  let c : ℝ := p 2
  let s : ℝ := Real.sqrt (a ^ 2 + b ^ 2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a ^ 2 + b ^ 2 := by
    dsimp [s]
    rw [Real.sq_sqrt]
    positivity
  have hdist : Real.sqrt ((s - 1) ^ 2 + c ^ 2) = (1 / 4 : ℝ) := by
    change Metric.infDist p apm_t02a03_C = (1 / 4 : ℝ) at hp
    calc
      _ = Metric.infDist p apm_t02a03_C := by
        symm
        simpa [a, b, c, s] using
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_infDist p
      _ = _ := hp
  have hrad : (s - 1) ^ 2 + c ^ 2 = (1 / 4 : ℝ) ^ 2 := by
    have := congrArg (fun x : ℝ ↦ x ^ 2) hdist
    change (Real.sqrt ((s - 1) ^ 2 + c ^ 2)) ^ 2 = (1 / 4 : ℝ) ^ 2 at this
    rwa [Real.sq_sqrt (by positivity)] at this
  have hspos : 0 < s := by
    nlinarith [sq_nonneg (s - 1), sq_nonneg c]
  let u0 : ℂ := (a / s : ℝ) + (b / s : ℝ) * Complex.I
  have hu0 : ‖u0‖ = 1 := by
    rw [Complex.norm_def]
    simp [Complex.normSq_apply, u0]
    rw [show a / s * (a / s) + b / s * (b / s) = 1 by
      field_simp
      nlinarith [hs2]]
  let v0 : ℂ := (4 * (s - 1) : ℝ) + (4 * c : ℝ) * Complex.I
  have hv0 : ‖v0‖ = 1 := by
    rw [Complex.norm_def]
    simp [Complex.normSq_apply, v0]
    rw [show 4 * (s - 1) * (4 * (s - 1)) + 4 * c * (4 * c) = 1 by
      nlinarith [hrad]]
  let u : Circle := ⟨u0, by simpa [Submonoid.unitSphere] using hu0⟩
  let v : Circle := ⟨v0, by simpa [Submonoid.unitSphere] using hv0⟩
  refine ⟨(u, v), ?_⟩
  ext i
  fin_cases i
  · simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param,
      u, v, u0, v0, a, b, c]
    field_simp
    nlinarith
  · simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param,
      u, v, u0, v0, a, b, c]
    field_simp
  · simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param,
      u, v, u0, v0, a, b, c]

theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph :
    ∃ e : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ≃ₜ
        ConstructionTargets.TorusCircleWedgeOpenCover.Torus,
      ∀ h : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_q0 ∈
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus,
        e ⟨_, h⟩ = ((1 : Circle), (1 : Circle)) := by
  let f : apm_t02a03_Torus → apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus :=
    fun x ↦ ⟨apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param x, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_mem x⟩
  have hf : Continuous f := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param_continuous.subtype_mk _
  have hbij : Function.Bijective f := by
    refine ⟨fun x y h ↦ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_injective (congrArg Subtype.val h), ?_⟩
    rintro ⟨p, hp⟩
    obtain ⟨x, hx⟩ := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_surj p hp
    exact ⟨x, Subtype.ext hx⟩
  let e0 : apm_t02a03_Torus ≃ₜ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus :=
    (show Continuous (Equiv.ofBijective f hbij) from hf).homeoOfEquivCompactToT2
  refine ⟨e0.symm, fun h ↦ ?_⟩
  rw [Homeomorph.symm_apply_eq]
  exact Subtype.ext apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_param_one.symm

/-- LIBRARY: the loop is a circle, with `q0` (parameter `t = 0`) at `1`. -/
noncomputable def apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_param
    (z : Circle) : apm_t02a03_E3 :=
  WithLp.toLp 2 ![6 / 5 - 23 / 20 * (z : ℂ).re,
    23 / 20 * (z : ℂ).im, 0]

lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_continuous :
    Continuous apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_param := by
  unfold apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_param
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_)
  fin_cases i <;> simp <;> fun_prop

lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_mem
    (z : Circle) :
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_param z ∈
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop := by
  have hz : (z : ℂ) ≠ 0 := by
    intro h
    have := Circle.norm_coe z
    simp [h] at this
  refine ⟨Complex.arg (z : ℂ), ?_⟩
  ext i
  fin_cases i
  · simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_param,
      Complex.cos_arg hz, Circle.norm_coe]
  · simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_param,
      Complex.sin_arg, Circle.norm_coe]
  · simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_param]

lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_injective :
    Function.Injective
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_param := by
  intro z w h
  apply Subtype.ext
  apply Complex.ext
  · have h0 := congrArg (fun x : apm_t02a03_E3 ↦ x 0) h
    simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_param] at h0
    linarith
  · have h1 := congrArg (fun x : apm_t02a03_E3 ↦ x 1) h
    simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_param] at h1
    linarith

lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_surjective :
    Function.Surjective (fun z : Circle ↦
      (⟨apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_param z,
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_mem z⟩ :
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop)) := by
  rintro ⟨p, hp⟩
  rcases hp with ⟨t, rfl⟩
  let z : Circle := Circle.exp t
  refine ⟨z, Subtype.ext ?_⟩
  ext i
  fin_cases i <;>
    simp [z, Circle.coe_exp, Complex.exp_mul_I,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_param]

theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph :
    ∃ e : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop ≃ₜ Circle,
      ∀ h : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_q0 ∈
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop,
        e ⟨_, h⟩ = 1 := by
  let f : Circle → apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop :=
    fun z ↦ ⟨apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_param z,
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_mem z⟩
  have hf : Continuous f :=
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_continuous.subtype_mk _
  have hbij : Function.Bijective f := ⟨fun _ _ h ↦
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_injective
      (congrArg Subtype.val h),
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_surjective⟩
  let e0 : Circle ≃ₜ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop :=
    (show Continuous (Equiv.ofBijective f hbij) from hf).homeoOfEquivCompactToT2
  refine ⟨e0.symm, fun h ↦ ?_⟩
  rw [Homeomorph.symm_apply_eq]
  change ⟨_, h⟩ = f 1
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [e0, f, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_homeomorph_aux_param,
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_q0] <;> norm_num

/-- LIBRARY: the loop lies in `W`, at distance at least `1/4` from the left
core, and meets the left boundary torus exactly at `q0`. -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop_geometry :
    (∀ p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop,
      p ∈ apm_t02a03_W ∧ (1 / 4 : ℝ) ≤ Metric.infDist p apm_t02a03_C) ∧
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∩
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop =
      {apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_q0} := by
  let L : ℝ → apm_t02a03_E3 := fun t ↦
    WithLp.toLp 2 ![6 / 5 - 23 / 20 * Real.cos t,
      23 / 20 * Real.sin t, 0]
  have hcoords (t : ℝ) :
      (L t 0 = 6 / 5 - 23 / 20 * Real.cos t) ∧
      (L t 1 = 23 / 20 * Real.sin t) ∧ L t 2 = 0 := by
    simp [L]
  have hsquare (t : ℝ) :
      (L t 0 + 6 / 5) ^ 2 + (L t 1) ^ 2 =
        (5 / 4 : ℝ) ^ 2 + (138 / 25) * (1 - Real.cos t) := by
    rcases hcoords t with ⟨h0, h1, h2⟩
    rw [h0, h1]
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hradius (t : ℝ) :
      (5 / 4 : ℝ) ≤ Real.sqrt ((L t 0 + 6 / 5) ^ 2 + (L t 1) ^ 2) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 4)]
    apply Real.sqrt_le_sqrt
    rw [hsquare]
    have hc : Real.cos t ≤ 1 := Real.cos_le_one t
    nlinarith
  have hleft (t : ℝ) :
      (1 / 4 : ℝ) ≤ Metric.infDist (L t) apm_t02a03_C := by
    rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_infDist]
    rw [(hcoords t).2.2]
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg (by linarith [hradius t])]
    linarith [hradius t]
  have hright (t : ℝ) : L t ∈ apm_t02a03_W := by
    unfold apm_t02a03_W
    have hmem : apm_t02a03_rightCore t ∈ apm_t02a03_genusTwoSpine := by
      exact Set.mem_union_right _ ⟨t, rfl⟩
    refine (Metric.infDist_le_dist_of_mem hmem).trans ?_
    simp [L, apm_t02a03_rightCore, dist_eq_norm, EuclideanSpace.norm_eq,
      Fin.sum_univ_succ]
    rw [show (Real.cos t - 23 / 20 * Real.cos t) ^ 2 +
        (23 / 20 * Real.sin t - Real.sin t) ^ 2 = (3 / 20 : ℝ) ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq t]]
    norm_num
  constructor
  · intro p hp
    rcases hp with ⟨t, rfl⟩
    exact ⟨hright t, hleft t⟩
  · ext p
    constructor
    · rintro ⟨hpT, hpL⟩
      rcases hpL with ⟨t, rfl⟩
      have heq : Metric.infDist (L t) apm_t02a03_C = (1 / 4 : ℝ) := hpT
      have hrsqrt : Real.sqrt ((L t 0 + 6 / 5) ^ 2 + (L t 1) ^ 2) = 5 / 4 := by
        rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_infDist,
          (hcoords t).2.2] at heq
        rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq_eq_abs] at heq
        rw [abs_of_nonneg (by linarith [hradius t])] at heq
        linarith
      have hsq : (L t 0 + 6 / 5) ^ 2 + (L t 1) ^ 2 = (5 / 4 : ℝ) ^ 2 := by
        have hnonneg : 0 ≤ (L t 0 + 6 / 5) ^ 2 + (L t 1) ^ 2 := by positivity
        nlinarith [Real.sq_sqrt hnonneg]
      have hc : Real.cos t = 1 := by
        rw [hsquare] at hsq
        nlinarith
      have hsin : Real.sin t = 0 := by
        nlinarith [Real.sin_sq_add_cos_sq t]
      simp only [Set.mem_singleton_iff]
      ext i
      fin_cases i <;>
        simp [L, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_q0, hc, hsin] <;>
        norm_num
    · intro hp
      simp only [Set.mem_singleton_iff] at hp
      subst p
      constructor
      · change Metric.infDist _ apm_t02a03_C = (1 / 4 : ℝ)
        rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_infDist]
        simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_q0]
        norm_num
      · exact ⟨0, by
          ext i
          fin_cases i <;>
            simp [L, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_q0] <;>
            norm_num⟩

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
  let f : Sum ConstructionTargets.TorusCircleWedgeOpenCover.Torus Circle →
      (A ∪ B : Set X) := fun z ↦ match z with
    | .inl a => ⟨eA.symm a, Or.inl (eA.symm a).property⟩
    | .inr b => ⟨eB.symm b, Or.inr (eB.symm b).property⟩
  have hxA : x ∈ A := by
    have : x ∈ A ∩ B := by simpa [hAB]
    exact this.1
  have hxB : x ∈ B := by
    have : x ∈ A ∩ B := by simpa [hAB]
    exact this.2
  have hfbase : f (.inl ((1 : Circle), (1 : Circle))) = f (.inr (1 : Circle)) := by
    apply Subtype.ext
    simp only [f]
    have hA : eA.symm ((1 : Circle), (1 : Circle)) = ⟨x, hxA⟩ := by
      apply eA.injective
      simp [heA hxA]
    have hB : eB.symm (1 : Circle) = ⟨x, hxB⟩ := by
      apply eB.injective
      simp [heB hxB]
    exact (congrArg Subtype.val hA).trans (congrArg Subtype.val hB).symm
  have hfrespect {u v}
      (huv : Relation.EqvGen
        (ConstructionTargets.PointWedgeQuotient.Rel
          ((1 : Circle), (1 : Circle)) (1 : Circle)) u v) : f u = f v := by
    induction huv with
    | rel u v huv => cases huv; exact hfbase
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  let g : ConstructionTargets.TorusCircleWedgeOpenCover.GenericWedge →
      (A ∪ B : Set X) := Quotient.lift f (fun _ _ h ↦ hfrespect h)
  have hfcont : Continuous f := by
    apply continuous_sum_dom.2
    constructor
    · exact (eA.symm.continuous.subtype_val).subtype_mk _
    · exact (eB.symm.continuous.subtype_val).subtype_mk _
  have hgcont : Continuous g := hfcont.quotient_lift _
  have hgsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rcases hy with hyA | hyB
    · refine ⟨Quotient.mk _ (.inl (eA ⟨y, hyA⟩)), ?_⟩
      apply Subtype.ext
      simp [g, f]
    · refine ⟨Quotient.mk _ (.inr (eB ⟨y, hyB⟩)), ?_⟩
      apply Subtype.ext
      simp [g, f]
  have hginj : Function.Injective g := by
    rintro ⟨u⟩ ⟨v⟩ huv
    apply Quotient.sound
    cases u with
    | inl a =>
      cases v with
      | inl a' =>
        change f (.inl a) = f (.inl a') at huv
        simp only [f] at huv
        have hval : (eA.symm a : X) = eA.symm a' :=
          congrArg (fun z : (A ∪ B : Set X) ↦ (z : X)) huv
        have hsub : eA.symm a = eA.symm a' := Subtype.ext hval
        have haa : a = a' := eA.symm.injective hsub
        subst a'
        exact Relation.EqvGen.refl _
      | inr b =>
        change f (.inl a) = f (.inr b) at huv
        simp only [f] at huv
        have hmem : (eA.symm a : X) ∈ A ∩ B :=
          ⟨(eA.symm a).property, by
            rw [show (eA.symm a : X) = eB.symm b from congrArg Subtype.val huv]
            exact (eB.symm b).property⟩
        have hx : (eA.symm a : X) = x := by
          have : (eA.symm a : X) ∈ ({x} : Set X) := by simpa [hAB] using hmem
          simpa using this
        have ha : a = ((1 : Circle), (1 : Circle)) := by
          calc
            a = eA (eA.symm a) := (eA.apply_symm_apply a).symm
            _ = eA ⟨x, hxA⟩ := congrArg eA (Subtype.ext hx)
            _ = _ := heA hxA
        have hb : b = (1 : Circle) := by
          calc
            b = eB (eB.symm b) := (eB.apply_symm_apply b).symm
            _ = eB ⟨x, hxB⟩ := congrArg eB (Subtype.ext
              ((congrArg Subtype.val huv).symm.trans hx))
            _ = _ := heB hxB
        subst a
        subst b
        exact Relation.EqvGen.rel _ _
          (ConstructionTargets.PointWedgeQuotient.Rel.base)
    | inr b =>
      cases v with
      | inl a =>
        change f (.inr b) = f (.inl a) at huv
        simp only [f] at huv
        have hmem : (eB.symm b : X) ∈ A ∩ B :=
          ⟨by
            rw [show (eB.symm b : X) = eA.symm a from congrArg Subtype.val huv]
            exact (eA.symm a).property,
           (eB.symm b).property⟩
        have hx : (eB.symm b : X) = x := by
          have : (eB.symm b : X) ∈ ({x} : Set X) := by simpa [hAB] using hmem
          simpa using this
        have hb : b = (1 : Circle) := by
          calc
            b = eB (eB.symm b) := (eB.apply_symm_apply b).symm
            _ = eB ⟨x, hxB⟩ := congrArg eB (Subtype.ext hx)
            _ = _ := heB hxB
        have ha : a = ((1 : Circle), (1 : Circle)) := by
          calc
            a = eA (eA.symm a) := (eA.apply_symm_apply a).symm
            _ = eA ⟨x, hxA⟩ := congrArg eA (Subtype.ext
              ((congrArg Subtype.val huv).symm.trans hx))
            _ = _ := heA hxA
        subst a
        subst b
        exact (Relation.EqvGen.rel _ _
          (ConstructionTargets.PointWedgeQuotient.Rel.base)).symm
      | inr b' =>
        change f (.inr b) = f (.inr b') at huv
        simp only [f] at huv
        have hval : (eB.symm b : X) = eB.symm b' :=
          congrArg (fun z : (A ∪ B : Set X) ↦ (z : X)) huv
        have hsub : eB.symm b = eB.symm b' := Subtype.ext hval
        have hbb : b = b' := eB.symm.injective hsub
        subst b'
        exact Relation.EqvGen.refl _
  let eg : ConstructionTargets.TorusCircleWedgeOpenCover.GenericWedge ≃
      (A ∪ B : Set X) := Equiv.ofBijective g ⟨hginj, hgsurj⟩
  letI : CompactSpace ConstructionTargets.TorusCircleWedgeOpenCover.GenericWedge :=
    Quotient.compactSpace
  exact ⟨(Continuous.homeoOfEquivCompactToT2 (f := eg) hgcont).symm⟩

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
lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_cover_aux_infDist_union
    (p : apm_t02a03_E3) :
    Metric.infDist p apm_t02a03_genusTwoSpine =
      min (Metric.infDist p apm_t02a03_C)
        (Metric.infDist p (Set.range apm_t02a03_rightCore)) := by
  have hleft : (Set.range apm_t02a03_leftCore).Nonempty :=
    ⟨apm_t02a03_leftCore 0, ⟨0, rfl⟩⟩
  have hright : (Set.range apm_t02a03_rightCore).Nonempty :=
    ⟨apm_t02a03_rightCore 0, ⟨0, rfl⟩⟩
  simp only [apm_t02a03_genusTwoSpine, apm_t02a03_C, Metric.infDist,
    Metric.infEDist_union]
  exact ENNReal.toReal_inf (Metric.infEDist_ne_top hleft)
    (Metric.infEDist_ne_top hright)

theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_cover :
    ∀ p : apm_t02a03_shellY,
      p.1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∨
        p.1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right := by
  intro p
  have hpW := p.2.1
  change Metric.infDist p.1 apm_t02a03_genusTwoSpine ≤ (1 / 4 : ℝ) at hpW
  rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_cover_aux_infDist_union]
    at hpW
  rw [min_le_iff] at hpW
  rcases hpW with hleft | hright
  · left
    exact le_antisymm hleft p.2.2
  · right
    exact ⟨hright, p.2.2⟩

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

/-- Planar distance `s` from the right centre `(6/5, 0)`. -/
noncomputable def apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad (p : apm_t02a03_E3) : ℝ :=
  Real.sqrt ((p 0 - 6 / 5) ^ 2 + p 1 ^ 2)

/-- Points of the right piece that are already in the target `D ∪ loop`, or
lie in the sector `x ≤ 4/5` of the right tube.  The bite (open left tube)
lies in `x < 1/20`, so the sector contains the whole bite region; in the
right-tube angle `θ` (`rightCore θ = (6/5 - cos θ, sin θ, 0)`) every tube
point with `|θ| ≤ 0.82` has `x ≤ 6/5 - (3/4) cos 0.82 < 4/5`. -/
abbrev apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y
    (p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X) : Prop :=
  apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z p ∨
    (17 / 25 : ℝ) ≤ (6 / 5 - (p.1 : apm_t02a03_E3) 0) /
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p.1

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
lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_continuous_aux_dist
    (p : apm_t02a03_E3)
    (hp : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p = 0) :
    (1 : ℝ) ≤ Metric.infDist p (Set.range apm_t02a03_rightCore) := by
  rw [Metric.le_infDist]
  · rintro q ⟨t, rfl⟩
    simp only [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad,
      Real.sqrt_eq_zero'] at hp
    have hx : p 0 = 6 / 5 := by
      nlinarith [sq_nonneg (p 1)]
    have hy : p 1 = 0 := by
      nlinarith [sq_nonneg (p 0 - 6 / 5)]
    rw [show dist p (apm_t02a03_rightCore t) =
        Real.sqrt ((Real.cos t) ^ 2 + (Real.sin t) ^ 2 + (p 2) ^ 2) by
      simp [dist_eq_norm, apm_t02a03_rightCore, hx, hy, EuclideanSpace.norm_eq,
        Fin.sum_univ_succ]
      congr 1
      nlinarith [Real.sin_sq_add_cos_sq t]]
    rw [Real.one_le_sqrt]
    nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (p 2)]
  · exact ⟨apm_t02a03_rightCore 0, ⟨0, rfl⟩⟩

theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_continuous :
    ContinuousOn (fun q : ℝ × apm_t02a03_E3 => apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move q.1 q.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right) := by
  intro q hq
  have hrad :
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad q.2 ≠ 0 := by
    intro hz
    have hone :=
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_continuous_aux_dist
        q.2 hz
    exact (not_le_of_gt (by norm_num : (1 / 4 : ℝ) < 1))
      (hone.trans hq.2.1)
  have hsqrt : Real.sqrt ((q.2 0 - 6 / 5) ^ 2 + q.2 1 ^ 2) ≠ 0 := by
    simpa [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad]
      using hrad
  have hc (i : Fin 3) : ContinuousAt (fun y : ℝ × apm_t02a03_E3 => y.2 i) q :=
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp continuous_snd).continuousAt
  apply ContinuousAt.continuousWithinAt
  unfold apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad
  apply (PiLp.continuous_toLp 2 _).continuousAt.comp
  rw [continuousAt_pi]
  intro i
  fin_cases i <;> simp <;> fun_prop (disch := aesop)

/-- LIBRARY: `F_t` stays in the closed right tube.  The distance to the right
core is `√((s - 1)² + z²)`; the new `(s - 1, z)` is a convex combination of the
old one and `(3/20, 0)`, both in the disk of radius `1/4`. -/
lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_phi_bounds
    (p : apm_t02a03_E3) :
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi p ∈
      Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_fraction
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (p : apm_t02a03_E3) :
    t * apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi p ∈
      Set.Icc (0 : ℝ) 1 := by
  rcases ht with ⟨ht0, ht1⟩
  rcases apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_phi_bounds p with
    ⟨hφ0, hφ1⟩
  constructor
  · positivity
  · nlinarith

/-- LIBRARY: closed form of the distance to the right core circle:
`√((s - 1)² + z²)` with `s` the planar distance from `(6/5, 0)` (split by
claude-14 from lemma-3's partial, 2026-10-19). -/
lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_dist_eq (p : apm_t02a03_E3) :
    Metric.infDist p (Set.range apm_t02a03_rightCore) =
      Real.sqrt ((apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p - 1) ^ 2 + p 2 ^ 2) := by
  let a : ℝ := p 0 - 6 / 5
  let b : ℝ := p 1
  let s : ℝ := Real.sqrt (a ^ 2 + b ^ 2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a ^ 2 + b ^ 2 := by
    dsimp [s]
    rw [Real.sq_sqrt]
    positivity
  have lower : Real.sqrt ((s - 1) ^ 2 + p 2 ^ 2) ≤
      Metric.infDist p (Set.range apm_t02a03_rightCore) := by
    rw [Metric.le_infDist]
    · rintro q ⟨t, rfl⟩
      have htrig : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 :=
        Real.sin_sq_add_cos_sq t
      have hcs : (a * Real.cos t - b * Real.sin t) ^ 2 ≤ s ^ 2 := by
        nlinarith [sq_nonneg (a * Real.sin t + b * Real.cos t)]
      have hdot : -s ≤ a * Real.cos t - b * Real.sin t := by
        nlinarith [sq_nonneg (s + (a * Real.cos t - b * Real.sin t))]
      rw [show dist p (apm_t02a03_rightCore t) =
          Real.sqrt ((a + Real.cos t) ^ 2 + (b - Real.sin t) ^ 2 + p 2 ^ 2) by
        simp [dist_eq_norm, apm_t02a03_rightCore, a, b, EuclideanSpace.norm_eq,
          Fin.sum_univ_succ]
        congr 1 <;> ring]
      exact Real.sqrt_le_sqrt (by nlinarith)
    · exact ⟨apm_t02a03_rightCore 0, ⟨0, rfl⟩⟩
  apply le_antisymm
  · by_cases hz : (-a : ℂ) + b * Complex.I = 0
    · have ha : a = 0 := by
        have := congrArg Complex.re hz
        simpa using this
      have hb : b = 0 := by
        have := congrArg Complex.im hz
        simpa using this
      have hs : s = 0 := by simp [s, ha, hb]
      have hp0 : p 0 = 6 / 5 := by dsimp [a] at ha; linarith
      have hp1 : p 1 = 0 := by simpa [b] using hb
      calc
        Metric.infDist p (Set.range apm_t02a03_rightCore)
            ≤ dist p (apm_t02a03_rightCore 0) :=
              Metric.infDist_le_dist_of_mem ⟨0, rfl⟩
        _ = Real.sqrt ((s - 1) ^ 2 + p 2 ^ 2) := by
          simp [dist_eq_norm, apm_t02a03_rightCore, hp0, hp1, hs,
            EuclideanSpace.norm_eq, Fin.sum_univ_succ]
    · let z : ℂ := (-a : ℂ) + b * Complex.I
      have hz' : z ≠ 0 := by simpa [z] using hz
      have hnorm : ‖z‖ = s := by
        rw [Complex.norm_def]
        congr 1
        simp [Complex.normSq_apply, z, s]
        ring
      have hc : -Real.cos (Complex.arg z) = a / s := by
        rw [Complex.cos_arg hz', hnorm]
        simp [z]
        ring
      have hsi : Real.sin (Complex.arg z) = b / s := by
        rw [Complex.sin_arg, hnorm]
        simp [z]
      have hspos : 0 < s := lt_of_le_of_ne hs0 (by
        intro h
        apply hz'
        apply Complex.ext <;> simp [z] at * <;> nlinarith [hs2])
      calc
        Metric.infDist p (Set.range apm_t02a03_rightCore)
            ≤ dist p (apm_t02a03_rightCore (Complex.arg z)) :=
              Metric.infDist_le_dist_of_mem ⟨_, rfl⟩
        _ = Real.sqrt ((s - 1) ^ 2 + p 2 ^ 2) := by
          rw [show dist p (apm_t02a03_rightCore (Complex.arg z)) =
              Real.sqrt ((a + Real.cos (Complex.arg z)) ^ 2 +
                (b - Real.sin (Complex.arg z)) ^ 2 + p 2 ^ 2) by
            simp [dist_eq_norm, apm_t02a03_rightCore, a, b, EuclideanSpace.norm_eq,
              Fin.sum_univ_succ]
            congr 1 <;> ring]
          congr 1
          have hc' : Real.cos (Complex.arg z) = -a / s := by
            calc
              Real.cos (Complex.arg z) = -(-Real.cos (Complex.arg z)) := by ring
              _ = -(a / s) := congrArg Neg.neg hc
              _ = -a / s := by ring
          rw [hc', hsi]
          field_simp
          nlinarith [hs2]
  · change Real.sqrt ((s - 1) ^ 2 + p 2 ^ 2) ≤ _
    exact lower

/-- LIBRARY: the move rescales the planar offset by `1 + a (23/20/s - 1) ≥ 0`,
so the new planar distance is `s + a (23/20 - s)`, `a = t φ`. -/
lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_rad_move (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (p : apm_t02a03_E3)
    (hs : 0 < apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p) :
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move t p) =
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p + t * apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi p * (23 / 20 - apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p) := by
  let s := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p
  let a := t * apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi p
  let k := 1 + a * (23 / 20 / s - 1)
  have ha :=
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_fraction
      t ht p
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hks : k * s = s + a * (23 / 20 - s) := by
    dsimp [k]
    field_simp [hs0]
  have hk : 0 < k := by
    rcases ha with ⟨ha0, ha1⟩
    have htarget : 0 < (23 / 20 : ℝ) := by norm_num
    have hratio : 0 < (23 / 20 : ℝ) / s := div_pos htarget hs
    dsimp [k]
    nlinarith
  have hs_sq : (p 0 - 6 / 5) ^ 2 + p 1 ^ 2 = s ^ 2 := by
    dsimp [s, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad]
    rw [Real.sq_sqrt]
    positivity
  change Real.sqrt
      (((6 / 5 + k * (p 0 - 6 / 5) - 6 / 5) ^ 2) +
        (k * p 1) ^ 2) = s + a * (23 / 20 - s)
  rw [show (6 / 5 + k * (p 0 - 6 / 5) - 6 / 5) ^ 2 + (k * p 1) ^ 2 =
      (k * s) ^ 2 by nlinarith [sq_nonneg k, hs_sq]]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hk hs), hks]

/-- The disk of radius `1/4` is convex and contains `(3/20, 0)`. -/
lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_convex (s z a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (h : (s - 1) ^ 2 + z ^ 2 ≤ 1 / 16) :
    (s + a * (23 / 20 - s) - 1) ^ 2 + ((1 - a) * z) ^ 2 ≤ 1 / 16 := by
  rcases ha with ⟨ha0, ha1⟩
  have hw : 0 ≤ a * (1 - a) * ((s - 1 - 3 / 20) ^ 2 + z ^ 2) :=
    mul_nonneg (mul_nonneg ha0 (by linarith)) (by positivity)
  nlinarith

theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right) :
    Metric.infDist (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move t p) (Set.range apm_t02a03_rightCore) ≤ (1 / 4 : ℝ) := by
  rcases apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_fraction t ht p with ⟨ha0, ha1⟩
  have hp1 := hp.1
  rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_dist_eq] at hp1 ⊢
  have hsq : (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p - 1) ^ 2 + p 2 ^ 2 ≤ 1 / 16 := by
    rw [Real.sqrt_le_left (by norm_num)] at hp1
    linarith
  have hs : 0 < apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p := by nlinarith [sq_nonneg (p 2)]
  rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_rad_move t ht p hs]
  have hz : (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move t p) 2 =
      (1 - t * apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi p) * p 2 := by
    simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move]
  rw [hz, Real.sqrt_le_left (by norm_num)]
  norm_num only [show ((1 : ℝ) / 4) ^ 2 = 1 / 16 by norm_num]
  exact apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_convex _ _ _ ⟨ha0, ha1⟩ hsq

/-- LIBRARY: `F_t` stays at least `1/4` from the left core.  If `t φ = 0` the
point is fixed.  Otherwise `cos θ < 23/25` and the new `s' ≤ 5/4`, so
`x' = 6/5 - s' cos θ > 1/20`; a point with `x > 1/20` is at planar distance
`> 5/4` from `(-6/5, 0)`, hence more than `1/4` from `C`. -/
lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_far_aux_of_x
    (q : apm_t02a03_E3) (hq : (1 / 20 : ℝ) ≤ q 0) :
    (1 / 4 : ℝ) ≤ Metric.infDist q apm_t02a03_C := by
  rw [Metric.le_infDist]
  · rintro z ⟨u, rfl⟩
    have hx : (1 / 4 : ℝ) ≤ dist (q 0) ((apm_t02a03_leftCore u) 0) := by
      rw [Real.dist_eq]
      simp only [apm_t02a03_leftCore, Matrix.cons_val_zero]
      rw [abs_of_nonneg]
      · nlinarith [Real.cos_le_one u]
      · nlinarith [Real.cos_le_one u]
    exact hx.trans (PiLp.dist_apply_le q (apm_t02a03_leftCore u) 0)
  · exact ⟨apm_t02a03_leftCore 0, ⟨0, rfl⟩⟩

lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_far_aux_move_x_aux_rad_le
    (p : apm_t02a03_E3)
    (hp : Metric.infDist p (Set.range apm_t02a03_rightCore) ≤ (1 / 4 : ℝ)) :
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p ≤ 5 / 4 := by
  let z : ℂ := (p 0 - 6 / 5 : ℝ) + (p 1 : ℝ) * Complex.I
  have hz : ‖z‖ =
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p := by
    rw [Complex.norm_def]
    simp [z, Complex.normSq_apply, pow_two,
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad]
  have hlower :
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p - 1 ≤
        Metric.infDist p (Set.range apm_t02a03_rightCore) := by
    rw [Metric.le_infDist]
    · rintro q ⟨u, rfl⟩
      let w : ℂ := (-Real.cos u : ℝ) + (Real.sin u : ℝ) * Complex.I
      have hw : ‖w‖ = 1 := by
        rw [Complex.norm_def]
        norm_num [w, Complex.normSq_apply, pow_two, Real.sin_sq_add_cos_sq,
          Complex.cos_ofReal_re, Complex.sin_ofReal_re]
        nlinarith [Real.sin_sq_add_cos_sq u]
      have hzw : ‖z - w‖ ≤ dist p (apm_t02a03_rightCore u) := by
        rw [dist_eq_norm, EuclideanSpace.norm_eq, Complex.norm_def]
        norm_num [z, w, Complex.normSq_apply, apm_t02a03_rightCore,
          Fin.sum_univ_succ, pow_two, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
        apply Real.sqrt_le_sqrt
        nlinarith [sq_nonneg (p 2)]
      have hrev := abs_norm_sub_norm_le z w
      rw [hw, hz] at hrev
      exact (le_trans (le_abs_self _) hrev).trans hzw
    · exact ⟨apm_t02a03_rightCore 0, ⟨0, rfl⟩⟩
  linarith

lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_far_aux_move_x
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right) :
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move t p = p ∨
      (1 / 20 : ℝ) ≤
        (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move t p) 0 := by
  let r := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p
  let ph := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi p
  by_cases ha : t * ph = 0
  · left
    have ha' : t * apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi p = 0 := by
      simpa [ph] using ha
    ext i
    fin_cases i <;>
      simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move,
        ha'] <;> ring
  · right
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hph0 : 0 ≤ ph := by
      dsimp [ph]
      exact le_min (by norm_num) (le_max_left _ _)
    have hph1 : ph ≤ 1 := by
      dsimp [ph]
      exact min_le_left _ _
    have htpos : 0 < t := lt_of_le_of_ne ht0 (fun h ↦ ha (by rw [← h]; simp))
    have hphpos : 0 < ph := lt_of_le_of_ne hph0 (fun h ↦ ha (by rw [← h]; simp))
    have hr0 : 0 ≤ r := by
      dsimp [r, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad]
      positivity
    have hrne : r ≠ 0 := by
      intro hr
      have h := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_continuous_aux_dist p (by simpa [r] using hr)
      linarith [hp.1]
    have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrne)
    have hrle : r ≤ 5 / 4 := by
      exact apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_far_aux_move_x_aux_rad_le p hp.1
    have hc : (6 / 5 - p 0) / r < 23 / 25 := by
      dsimp [ph, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi] at hphpos
      have hraw : 0 < (23 - 25 * ((6 / 5 - p 0) / r)) / 6 := by
        simpa [r] using (lt_of_lt_of_le hphpos (min_le_right _ _))
      linarith
    have ha0 : 0 ≤ t * ph := mul_nonneg ht0 hph0
    have ha1 : t * ph ≤ 1 := by nlinarith
    have hsnonneg : 0 ≤ r + t * ph * (23 / 20 - r) := by
      nlinarith
    have hsle : r + t * ph * (23 / 20 - r) ≤ 5 / 4 := by
      nlinarith
    change (1 / 20 : ℝ) ≤ 6 / 5 +
      (1 + t * ph * (23 / 20 / r - 1)) * (p 0 - 6 / 5)
    rw [show (1 + t * ph * (23 / 20 / r - 1)) * (p 0 - 6 / 5) =
        -(r + t * ph * (23 / 20 - r)) * ((6 / 5 - p 0) / r) by
      field_simp
      ring]
    by_cases hc0 : 0 ≤ (6 / 5 - p 0) / r
    · nlinarith [mul_lt_mul_of_pos_right hc (by norm_num : (0 : ℝ) < 5 / 4),
        mul_le_mul_of_nonneg_right hsle hc0]
    · have hcneg : (6 / 5 - p 0) / r < 0 := lt_of_not_ge hc0
      have := mul_nonpos_of_nonneg_of_nonpos hsnonneg (le_of_lt hcneg)
      linarith

theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_far (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right) :
    (1 / 4 : ℝ) ≤ Metric.infDist (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move t p) apm_t02a03_C := by
  rcases apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_far_aux_move_x
      t ht p hp with h | h
  · simpa [h] using hp.2
  · exact apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_far_aux_of_x _ h

/-- LIBRARY: `F_t` fixes `torus ∪ loop` in the right piece.  Loop points have
`s = 23/20`, `z = 0`.  Torus points have `x ≤ 1/20`, so `cos θ ≥ (23/20)/s ≥
23/25` and `φ = 0`. -/
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

lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_fix_aux_torus_aux_x
    (p : apm_t02a03_E3)
    (hT : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus) :
    p 0 ≤ (1 / 20 : ℝ) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hi : Metric.infDist p apm_t02a03_C < 1 / 4 + ε := by
    rw [hT]
    linarith
  have hne : apm_t02a03_C.Nonempty := ⟨apm_t02a03_leftCore 0, ⟨0, rfl⟩⟩
  rw [Metric.infDist_lt_iff hne] at hi
  rcases hi with ⟨q, ⟨u, rfl⟩, hq⟩
  have hc : p 0 - (-6 / 5 + Real.cos u) ≤
      dist p (apm_t02a03_leftCore u) := by
    calc
      p 0 - (-6 / 5 + Real.cos u) ≤
          |p 0 - (-6 / 5 + Real.cos u)| := le_abs_self _
      _ = dist (p 0) ((apm_t02a03_leftCore u) 0) := by
        simp [apm_t02a03_leftCore, Real.dist_eq]
      _ ≤ dist p (apm_t02a03_leftCore u) := PiLp.dist_apply_le _ _ _
  have hcos := Real.cos_le_one u
  nlinarith

lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_fix_aux_torus_aux_rad
    (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right) :
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p ≤
      (5 / 4 : ℝ) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hi : Metric.infDist p (Set.range apm_t02a03_rightCore) < 1 / 4 + ε :=
    lt_of_le_of_lt hp.1 (by linarith)
  have hne : (Set.range apm_t02a03_rightCore).Nonempty :=
    ⟨apm_t02a03_rightCore 0, ⟨0, rfl⟩⟩
  rw [Metric.infDist_lt_iff hne] at hi
  rcases hi with ⟨q, ⟨u, rfl⟩, hq⟩
  let c : apm_t02a03_E3 := WithLp.toLp 2 ![6 / 5, 0, 0]
  have hrad : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p ≤
      dist p c := by
    rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad]
    simp [c, dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
    rw [Real.sqrt_le_sqrt_iff]
    all_goals nlinarith [sq_nonneg (p 0 - 6 / 5), sq_nonneg (p 1), sq_nonneg (p 2)]
  have hqc : dist (apm_t02a03_rightCore u) c = 1 := by
    simp [c, apm_t02a03_rightCore, dist_eq_norm, EuclideanSpace.norm_eq,
      Fin.sum_univ_succ]
  apply le_of_lt
  calc
    _ ≤ dist p c := hrad
    _ ≤ dist p (apm_t02a03_rightCore u) + dist (apm_t02a03_rightCore u) c := dist_triangle _ _ _
    _ < 5 / 4 + ε := by rw [hqc]; linarith

lemma apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_fix_aux_torus
    (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right)
    (hT : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus) :
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi p = 0 := by
  have hx :=
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_fix_aux_torus_aux_x p hT
  have hs :=
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_fix_aux_torus_aux_rad p hp
  have hs0 : 0 < apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p := by
    by_contra hn
    have hz : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p = 0 :=
      le_antisymm (le_of_not_gt hn) (Real.sqrt_nonneg _)
    have hone :=
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_continuous_aux_dist p hz
    linarith [hp.1]
  have hratio : (23 / 25 : ℝ) ≤
      (6 / 5 - p 0) /
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p := by
    apply (le_div_iff₀ hs0).2
    nlinarith
  unfold apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi
  have hnonpos : (23 - 25 * ((6 / 5 - p 0) /
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p)) / 6 ≤ 0 := by
    nlinarith
  rw [max_eq_left hnonpos]
  norm_num

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

/-- LIBRARY: the end of the collapse.  If `φ = 1` the point goes to `s = 23/20`,
`z = 0`, the angle `θ` with `cos θ = (6/5 - x)/s`, `sin θ = y/s`: a loop point.
If `φ < 1` then `cos θ > 17/25` and `s' ≥ 3/4`, so
`x' ≤ 6/5 - (3/4)(17/25) < 4/5`. -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_end (p : apm_t02a03_E3) (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right) :
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move 1 p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop ∨
      (17 / 25 : ℝ) ≤
        (6 / 5 - (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move 1 p) 0) /
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad
            (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move 1 p) := by
  let s := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p
  let ph := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi p
  have hdist := hp.1
  rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_dist_eq] at hdist
  have hsq : (s - 1) ^ 2 + p 2 ^ 2 ≤ 1 / 16 := by
    have hsqrt : Real.sqrt ((s - 1) ^ 2 + p 2 ^ 2) ≤ 1 / 4 := by
      simpa [s] using hdist
    have hroot0 : 0 ≤ Real.sqrt ((s - 1) ^ 2 + p 2 ^ 2) := Real.sqrt_nonneg _
    have hsqrt' := mul_self_le_mul_self hroot0 hsqrt
    rw [Real.mul_self_sqrt (by positivity : 0 ≤ (s - 1) ^ 2 + p 2 ^ 2)] at hsqrt'
    nlinarith
  have hslo : (3 / 4 : ℝ) ≤ s := by nlinarith [sq_nonneg (s - 1), sq_nonneg (p 2)]
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hslo
  have hsne : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p ≠ 0 := by
    simpa [s] using hspos.ne'
  have hs_sq : s ^ 2 = (p 0 - 6 / 5) ^ 2 + p 1 ^ 2 := by
    dsimp [s, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad]
    rw [Real.sq_sqrt]
    positivity
  by_cases hph : ph = 1
  · left
    let z : ℂ := ((6 / 5 - p 0) : ℝ) + (p 1 : ℝ) * Complex.I
    have hz : z ≠ 0 := by
      intro hz0
      have hre : (6 / 5 - p 0 : ℝ) = 0 := by
        have := congrArg Complex.re hz0
        simpa [z] using this
      have him : p 1 = 0 := by
        have := congrArg Complex.im hz0
        simpa [z] using this
      nlinarith [hs_sq]
    have hnorm : ‖z‖ = s := by
      rw [Complex.norm_def]
      simp [Complex.normSq_apply, z]
      congr 1
      nlinarith
    have hcos : Real.cos (Complex.arg z) = (6 / 5 - p 0) / s := by
      rw [Complex.cos_arg hz, hnorm]
      simp [z]
    have hsin : Real.sin (Complex.arg z) = p 1 / s := by
      rw [Complex.sin_arg, hnorm]
      simp [z]
    refine ⟨Complex.arg z, ?_⟩
    ext i
    fin_cases i
    · simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move,
        ph, hph, s, hcos]
      field_simp [hspos.ne']
      ring
    · simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move,
        ph, hph, s, hsin]
      field_simp [hspos.ne', hsne]
    · simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move,
        ph, hph]
  · right
    have hphlt : ph < 1 := by
      have hb := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_phi_bounds p
      exact lt_of_le_of_ne hb.2 hph
    have hratio : (17 / 25 : ℝ) < (6 / 5 - p 0) / s := by
      dsimp [ph, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_phi] at hphlt
      rw [min_lt_iff] at hphlt
      rcases hphlt with hphlt | hfalse
      · norm_num at hphlt
      · have hm : (23 - 25 * ((6 / 5 - p 0) / s)) / 6 < 1 := by
          apply lt_of_le_of_lt (le_max_right _ _) hfalse
        linarith
    have hmove :
        (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move 1 p) 0 =
          6 / 5 - (s + ph * (23 / 20 - s)) * ((6 / 5 - p 0) / s) := by
      simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move,
        s, ph]
      field_simp [hspos.ne', hsne]
      ring
    have hph0 : 0 ≤ ph :=
      (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_phi_bounds p).1
    have hs_hi :=
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_fix_aux_torus_aux_rad p hp
    have hsprime : (3 / 4 : ℝ) ≤ s + ph * (23 / 20 - s) := by
      change s ≤ (5 / 4 : ℝ) at hs_hi
      nlinarith
    have hmove1 :
        (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move 1 p) 1 =
          (s + ph * (23 / 20 - s)) * (p 1 / s) := by
      simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move,
        s, ph]
      field_simp [hspos.ne', hsne]
    have hsp : 0 < s + ph * (23 / 20 - s) := by linarith
    have hrad' : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad
        (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_move 1 p) =
          s + ph * (23 / 20 - s) := by
      unfold apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad
      rw [hmove, hmove1]
      have he : (6 / 5 - p 0) ^ 2 + p 1 ^ 2 = s ^ 2 := by rw [hs_sq]; ring
      have hsq' : (6 / 5 - (s + ph * (23 / 20 - s)) * ((6 / 5 - p 0) / s) - 6 / 5) ^ 2 +
          ((s + ph * (23 / 20 - s)) * (p 1 / s)) ^ 2 = (s + ph * (23 / 20 - s)) ^ 2 := by
        have : (6 / 5 - (s + ph * (23 / 20 - s)) * ((6 / 5 - p 0) / s) - 6 / 5) ^ 2 +
            ((s + ph * (23 / 20 - s)) * (p 1 / s)) ^ 2 =
            (s + ph * (23 / 20 - s)) ^ 2 * (((6 / 5 - p 0) ^ 2 + p 1 ^ 2) / s ^ 2) := by
          field_simp
          ring
        rw [this, he, div_self (pow_ne_zero 2 hspos.ne'), mul_one]
      rw [hsq', Real.sqrt_sq hsp.le]
    rw [hmove, hrad']
    have hc : (6 / 5 - (6 / 5 - (s + ph * (23 / 20 - s)) * ((6 / 5 - p 0) / s))) /
        (s + ph * (23 / 20 - s)) = (6 / 5 - p 0) / s := by
      rw [sub_sub_cancel, mul_div_assoc', mul_comm, div_div, mul_comm s, ← div_div, mul_div_assoc, div_self hsp.ne', mul_one]
    rw [hc]
    exact hratio.le

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
noncomputable def apm_t02a03_sector_aux_theta (p : apm_t02a03_E3) : ℝ :=
  Real.arctan (p 1 / (6 / 5 - p 0))

noncomputable def apm_t02a03_sector_aux_a (z : ℝ) : ℝ :=
  Real.sqrt (1 / 16 - z ^ 2)

def apm_t02a03_sector_aux_Delta (q : ℝ × ℝ) : Prop :=
  |q.2| ≤ 3 / 20 ∧
    6 / (5 * (1 + apm_t02a03_sector_aux_a q.2)) ≤ Real.cos q.1

noncomputable def apm_t02a03_sector_aux_b (theta z : ℝ) : ℝ :=
  (12 / 5) * Real.cos theta -
    Real.sqrt ((1 + apm_t02a03_sector_aux_a z) ^ 2 -
      (144 / 25) * (Real.sin theta) ^ 2) - 1

noncomputable def apm_t02a03_sector_aux_c (theta z : ℝ) : ℝ := by
  classical
  exact if apm_t02a03_sector_aux_Delta (theta, z) then
    apm_t02a03_sector_aux_b theta z
  else apm_t02a03_sector_aux_a z

noncomputable def apm_t02a03_sector_aux_clampZ (z : ℝ) : ℝ :=
  max (-1 / 5) (min (1 / 5) z)

noncomputable def apm_t02a03_sector_aux_Psi (p : apm_t02a03_E3) : ℝ × ℝ × ℝ :=
  let theta := apm_t02a03_sector_aux_theta p
  let z := p 2
  let u := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p - 1
  (theta, z, (u + apm_t02a03_sector_aux_a z) /
    (apm_t02a03_sector_aux_c theta z + apm_t02a03_sector_aux_a z))

noncomputable def apm_t02a03_sector_aux_PsiInv (q : ℝ × ℝ × ℝ) : apm_t02a03_E3 :=
  let theta := q.1
  let z := q.2.1
  let v := q.2.2
  let u := -apm_t02a03_sector_aux_a z +
    v * (apm_t02a03_sector_aux_c theta z + apm_t02a03_sector_aux_a z)
  WithLp.toLp 2 ![6 / 5 - (1 + u) * Real.cos theta,
    (1 + u) * Real.sin theta, z]

noncomputable def apm_t02a03_sector_aux_thetaOne : ℝ :=
  Real.arccos (17 / 25)

def apm_t02a03_sector_aux_box (q : ℝ × ℝ × ℝ) : Prop :=
  q.1 ∈ Set.Icc (-apm_t02a03_sector_aux_thetaOne) apm_t02a03_sector_aux_thetaOne ∧
    q.2.1 ∈ Set.Icc (-1 / 5) (1 / 5) ∧ q.2.2 ∈ Set.Icc 0 1

noncomputable def apm_t02a03_sector_aux_vArc (theta : ℝ) : ℝ :=
  (2 / 5) / (apm_t02a03_sector_aux_c theta 0 + 1 / 4)

noncomputable def apm_t02a03_sector_aux_Theta (z : ℝ) : ℝ :=
  Real.arccos (6 / (5 * (1 + apm_t02a03_sector_aux_a z)))

noncomputable def apm_t02a03_sector_aux_piDelta (q : ℝ × ℝ) : ℝ × ℝ :=
  let z' := max (-3 / 20) (min (3 / 20) q.2)
  let T := apm_t02a03_sector_aux_Theta z'
  (max (-T) (min T q.1), z')

noncomputable def apm_t02a03_sector_aux_deltaArc (q : ℝ × ℝ × ℝ) : ℝ :=
  |q.2.1| + |q.2.2 - apm_t02a03_sector_aux_vArc q.1|

noncomputable def apm_t02a03_sector_aux_deltaD (q : ℝ × ℝ × ℝ) : ℝ :=
  (1 - q.2.2) + dist (q.1, q.2.1) (apm_t02a03_sector_aux_piDelta (q.1, q.2.1))

noncomputable def apm_t02a03_sector_aux_lambda (q : ℝ × ℝ × ℝ) : ℝ :=
  apm_t02a03_sector_aux_deltaArc q /
    (apm_t02a03_sector_aux_deltaArc q + apm_t02a03_sector_aux_deltaD q)

noncomputable def apm_t02a03_sector_aux_r (q : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let l := apm_t02a03_sector_aux_lambda q
  if l ≤ 1 / 2 then
    let theta' := (1 - 2 * l) * q.1
    (theta', 0, apm_t02a03_sector_aux_vArc theta')
  else
    let base := apm_t02a03_sector_aux_piDelta
      ((2 * l - 1) * q.1, (2 * l - 1) * q.2.1)
    (base.1, base.2, 1)

noncomputable def apm_t02a03_sector_aux_clampMove (t : ℝ) (p : apm_t02a03_E3) : apm_t02a03_E3 :=
  WithLp.toLp 2 ![p 0, p 1,
    (1 - t) * p 2 + t * apm_t02a03_sector_aux_clampZ (p 2)]

lemma apm_t02a03_sector_aux_L2a_box_aux_theta_aux_angle_bound
    (x y : ℝ) (hx : 0 < x)
    (h : (17 / 25 : ℝ) ≤ x / Real.sqrt (x ^ 2 + y ^ 2)) :
    Real.arctan (y / x) ∈
      Set.Icc (-Real.arccos (17 / 25)) (Real.arccos (17 / 25)) := by
  set t := Real.arctan (y / x) with ht
  have hcos : Real.cos t = x / Real.sqrt (x ^ 2 + y ^ 2) := by
    rw [ht, Real.cos_arctan]
    have h1 : (1 : ℝ) + (y / x) ^ 2 = (x ^ 2 + y ^ 2) / x ^ 2 := by
      field_simp
    rw [h1, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hx.le]
    have hs : 0 < Real.sqrt (x ^ 2 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
    field_simp
  have habs : |t| ≤ Real.pi := by
    rw [abs_le]
    have h1 := Real.neg_pi_div_two_lt_arctan (y / x)
    have h2 := Real.arctan_lt_pi_div_two (y / x)
    have := Real.pi_pos
    constructor <;> linarith
  have hle : |t| ≤ Real.arccos (17 / 25) := by
    rw [← Real.arccos_cos (abs_nonneg t) habs, Real.cos_abs]
    exact Real.arccos_le_arccos (hcos ▸ h)
  exact abs_le.mp hle

lemma apm_t02a03_sector_aux_L2a_box_aux_theta_aux_positive (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right)
    (hcos : (17 / 25 : ℝ) ≤ (6 / 5 - p 0) /
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p) :
    0 < 6 / 5 - p 0 ∧
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p =
        Real.sqrt ((6 / 5 - p 0) ^ 2 + (p 1) ^ 2) := by
  have htube := hp.1
  rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_dist_eq,
    Real.sqrt_le_left (by norm_num)] at htube
  have hs : 0 <
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p := by
    nlinarith [sq_nonneg (p 2)]
  constructor
  · have : 0 < (6 / 5 - p 0) /
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 17 / 25) hcos
    rcases div_pos_iff.mp this with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge hs.le) h.2)
  · unfold apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad
    congr 1
    ring

lemma apm_t02a03_sector_aux_L2a_box_aux_theta (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right)
    (hcos : (17 / 25 : ℝ) ≤ (6 / 5 - p 0) /
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p) :
    apm_t02a03_sector_aux_theta p ∈
      Set.Icc (-apm_t02a03_sector_aux_thetaOne) apm_t02a03_sector_aux_thetaOne := by
  obtain ⟨hx, hrad⟩ :=
    apm_t02a03_sector_aux_L2a_box_aux_theta_aux_positive p hp hcos
  unfold apm_t02a03_sector_aux_theta apm_t02a03_sector_aux_thetaOne
  apply apm_t02a03_sector_aux_L2a_box_aux_theta_aux_angle_bound
      (6 / 5 - p 0) (p 1) hx
  rwa [← hrad]

lemma apm_t02a03_sector_aux_L2_aux_a_le (z : ℝ) : apm_t02a03_sector_aux_a z ≤ 1 / 4 := by
  unfold apm_t02a03_sector_aux_a
  rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg z])

lemma apm_t02a03_sector_aux_L2_aux_a_pos (z : ℝ) (hz : |z| ≤ 1 / 5) :
    0 < apm_t02a03_sector_aux_a z := by
  unfold apm_t02a03_sector_aux_a
  apply Real.sqrt_pos.mpr
  have : z ^ 2 ≤ (1 / 5) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg z) hz 2
  nlinarith

/-- The fibre width `c + a` is positive on the box (claude-14). -/
lemma apm_t02a03_sector_aux_L2_aux_cpa_pos (θ z : ℝ) (hz : |z| ≤ 1 / 5) :
    0 < apm_t02a03_sector_aux_c θ z + apm_t02a03_sector_aux_a z := by
  have ha := apm_t02a03_sector_aux_L2_aux_a_pos z hz
  have ha4 := apm_t02a03_sector_aux_L2_aux_a_le z
  unfold apm_t02a03_sector_aux_c
  split_ifs with hD
  · obtain ⟨_, hcos⟩ := hD
    set R := 1 + apm_t02a03_sector_aux_a z with hR
    have hR0 : 0 < R := by linarith
    have hc : 6 / (5 * R) ≤ Real.cos θ := hcos
    have hc' : 72 / 25 ≤ (12 / 5) * Real.cos θ * R := by
      rw [div_le_iff₀ (by positivity)] at hc; nlinarith
    have hY : 0 < (12 / 5) * Real.cos θ + R - 2 := by nlinarith
    unfold apm_t02a03_sector_aux_b
    rw [← hR]
    have hsq : Real.sqrt (R ^ 2 - (144 / 25) * Real.sin θ ^ 2) <
        (12 / 5) * Real.cos θ + R - 2 := by
      rw [Real.sqrt_lt' hY]
      nlinarith [Real.sin_sq_add_cos_sq θ, Real.cos_le_one θ]
    linarith
  · linarith

lemma apm_t02a03_sector_aux_L2_aux_u_ge (q : ℝ × ℝ × ℝ) (hq : apm_t02a03_sector_aux_box q) :
    -apm_t02a03_sector_aux_a q.2.1 ≤ -apm_t02a03_sector_aux_a q.2.1 +
        q.2.2 * (apm_t02a03_sector_aux_c q.1 q.2.1 + apm_t02a03_sector_aux_a q.2.1) := by
  have hz : |q.2.1| ≤ 1 / 5 := abs_le.mpr ⟨by linarith [hq.2.1.1], hq.2.1.2⟩
  have := apm_t02a03_sector_aux_L2_aux_cpa_pos q.1 q.2.1 hz
  nlinarith [hq.2.2.1]

lemma apm_t02a03_sector_aux_L2_aux_PsiInv_coords (q : ℝ × ℝ × ℝ) :
    let u := -apm_t02a03_sector_aux_a q.2.1 +
      q.2.2 * (apm_t02a03_sector_aux_c q.1 q.2.1 + apm_t02a03_sector_aux_a q.2.1)
    apm_t02a03_sector_aux_PsiInv q 0 = 6 / 5 - (1 + u) * Real.cos q.1 ∧
      apm_t02a03_sector_aux_PsiInv q 1 = (1 + u) * Real.sin q.1 ∧
      apm_t02a03_sector_aux_PsiInv q 2 = q.2.1 := by
  simp [apm_t02a03_sector_aux_PsiInv]

lemma apm_t02a03_sector_aux_L2b_inv_aux_cos_aux_rad (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad
        (apm_t02a03_sector_aux_PsiInv q) =
      1 + (-apm_t02a03_sector_aux_a q.2.1 +
        q.2.2 * (apm_t02a03_sector_aux_c q.1 q.2.1 +
          apm_t02a03_sector_aux_a q.2.1)) := by
  obtain ⟨h0, h1, -⟩ := apm_t02a03_sector_aux_L2_aux_PsiInv_coords q
  have hu := apm_t02a03_sector_aux_L2_aux_u_ge q hq
  have ha4 := apm_t02a03_sector_aux_L2_aux_a_le q.2.1
  set u := -apm_t02a03_sector_aux_a q.2.1 +
    q.2.2 * (apm_t02a03_sector_aux_c q.1 q.2.1 + apm_t02a03_sector_aux_a q.2.1)
  unfold apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad
  rw [h0, h1]
  have : (6 / 5 - (1 + u) * Real.cos q.1 - 6 / 5) ^ 2 + ((1 + u) * Real.sin q.1) ^ 2 =
      (1 + u) ^ 2 := by
    have := Real.sin_sq_add_cos_sq q.1; nlinarith
  rw [this, Real.sqrt_sq (by linarith)]

lemma apm_t02a03_sector_aux_L2_aux_a_sq (z : ℝ) (hz : |z| ≤ 1 / 5) :
    apm_t02a03_sector_aux_a z ^ 2 = 1 / 16 - z ^ 2 := by
  unfold apm_t02a03_sector_aux_a
  rw [Real.sq_sqrt]
  have : z ^ 2 ≤ (1 / 5) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg z) hz 2
  nlinarith

/-- On `Delta` the bite boundary lies inside the right tube: `b ≤ a`, which after
squaring is the `Delta` inequality `cos θ · (1 + a) ≥ 6/5` (claude-14). -/
lemma apm_t02a03_sector_aux_L2_aux_c_le_a (θ z : ℝ) :
    apm_t02a03_sector_aux_c θ z ≤ apm_t02a03_sector_aux_a z := by
  unfold apm_t02a03_sector_aux_c
  split_ifs with hD
  · obtain ⟨_, hcos⟩ := hD
    have ha0 : 0 ≤ apm_t02a03_sector_aux_a z := Real.sqrt_nonneg _
    set R := 1 + apm_t02a03_sector_aux_a z with hR
    have hR0 : 0 < R := by linarith
    have hcR : 6 / 5 ≤ Real.cos θ * R := by
      have h := hcos; rw [div_le_iff₀ (by positivity)] at h; linarith
    unfold apm_t02a03_sector_aux_b
    rw [← hR]
    rcases le_or_gt ((12 / 5) * Real.cos θ - R) 0 with h | h
    · have := Real.sqrt_nonneg (R ^ 2 - (144 / 25) * Real.sin θ ^ 2); linarith
    · have : (12 / 5) * Real.cos θ - R ≤ Real.sqrt (R ^ 2 - (144 / 25) * Real.sin θ ^ 2) := by
        rw [Real.le_sqrt' h]
        nlinarith [Real.sin_sq_add_cos_sq θ]
      linarith
  · exact le_rfl

lemma apm_t02a03_sector_aux_L2b_inv_aux_right_aux_tube (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    Metric.infDist (apm_t02a03_sector_aux_PsiInv q)
      (Set.range apm_t02a03_rightCore) ≤ (1 / 4 : ℝ) := by
  have hz : |q.2.1| ≤ 1 / 5 := abs_le.mpr ⟨by linarith [hq.2.1.1], hq.2.1.2⟩
  have hrad := apm_t02a03_sector_aux_L2b_inv_aux_cos_aux_rad q hq
  obtain ⟨-, -, h2⟩ := apm_t02a03_sector_aux_L2_aux_PsiInv_coords q
  have hpos := apm_t02a03_sector_aux_L2_aux_cpa_pos q.1 q.2.1 hz
  have hca := apm_t02a03_sector_aux_L2_aux_c_le_a q.1 q.2.1
  have ha2 := apm_t02a03_sector_aux_L2_aux_a_sq q.2.1 hz
  have ha0 : 0 ≤ apm_t02a03_sector_aux_a q.2.1 := Real.sqrt_nonneg _
  rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_dist_eq, hrad, h2]
  set u := -apm_t02a03_sector_aux_a q.2.1 +
    q.2.2 * (apm_t02a03_sector_aux_c q.1 q.2.1 + apm_t02a03_sector_aux_a q.2.1) with hu
  have hv0 := hq.2.2.1
  have hv1 := hq.2.2.2
  have hu1 : -apm_t02a03_sector_aux_a q.2.1 ≤ u := by rw [hu]; nlinarith
  have hu2 : u ≤ apm_t02a03_sector_aux_a q.2.1 := by rw [hu]; nlinarith
  have hsq : (1 + u - 1) ^ 2 + q.2.1 ^ 2 ≤ 1 / 16 := by nlinarith
  rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt hsq

lemma apm_t02a03_sector_aux_L2b_inv_aux_right_aux_left (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    (1 / 4 : ℝ) ≤ Metric.infDist (apm_t02a03_sector_aux_PsiInv q) apm_t02a03_C := by
  have hz : |q.2.1| ≤ 1 / 5 := abs_le.mpr ⟨by linarith [hq.2.1.1], hq.2.1.2⟩
  obtain ⟨h0, h1, h2⟩ := apm_t02a03_sector_aux_L2_aux_PsiInv_coords q
  have hpos := apm_t02a03_sector_aux_L2_aux_cpa_pos q.1 q.2.1 hz
  have hca := apm_t02a03_sector_aux_L2_aux_c_le_a q.1 q.2.1
  have ha2 := apm_t02a03_sector_aux_L2_aux_a_sq q.2.1 hz
  have ha0 : 0 ≤ apm_t02a03_sector_aux_a q.2.1 := Real.sqrt_nonneg _
  have ha4 := apm_t02a03_sector_aux_L2_aux_a_le q.2.1
  have hcosb : (17 / 25 : ℝ) ≤ Real.cos q.1 := by
    have hb := hq.1
    have hθ : |q.1| ≤ apm_t02a03_sector_aux_thetaOne := abs_le.mpr ⟨hb.1, hb.2⟩
    rw [← Real.cos_abs]
    have hpi : apm_t02a03_sector_aux_thetaOne ≤ Real.pi := Real.arccos_le_pi _
    calc (17 / 25 : ℝ) = Real.cos apm_t02a03_sector_aux_thetaOne := by
          unfold apm_t02a03_sector_aux_thetaOne; rw [Real.cos_arccos (by norm_num) (by norm_num)]
      _ ≤ Real.cos |q.1| := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hpi hθ
  set a := apm_t02a03_sector_aux_a q.2.1 with ha
  set c := apm_t02a03_sector_aux_c q.1 q.2.1 with hc
  set u := -a + q.2.2 * (c + a) with hu
  have hv0 := hq.2.2.1
  have hv1 := hq.2.2.2
  have hu1 : -a ≤ u := by rw [hu]; nlinarith
  have hu2 : u ≤ c := by rw [hu]; nlinarith
  set R := 1 + a with hR
  set co := Real.cos q.1 with hco
  set sn := Real.sin q.1 with hsn
  have htrig : sn ^ 2 + co ^ 2 = 1 := Real.sin_sq_add_cos_sq q.1
  -- f(s) := s² - (24/5) co s + 144/25 - R² ≥ 0 at s = 1 + u
  have hca' : c ≤ a := hca
  have hs2 : 1 + u ≤ 5 / 4 := by linarith
  have hfs : (12 / 5 - (1 + u) * co) ^ 2 + ((1 + u) * sn) ^ 2 - R ^ 2 =
      (1 + u) ^ 2 - (24 / 5) * co * (1 + u) + 144 / 25 - R ^ 2 := by
    linear_combination (1 + u) ^ 2 * htrig
  have hf : R ^ 2 ≤ (12 / 5 - (1 + u) * co) ^ 2 + ((1 + u) * sn) ^ 2 := by
    by_cases hD : apm_t02a03_sector_aux_Delta (q.1, q.2.1)
    · have hcb : c = apm_t02a03_sector_aux_b q.1 q.2.1 := by
        rw [hc]; unfold apm_t02a03_sector_aux_c; rw [if_pos hD]
      obtain ⟨_, hcos⟩ := hD
      have hR0 : 0 < R := by linarith
      have hcR : 6 / 5 ≤ co * R := by
        have h := hcos; rw [div_le_iff₀ (by positivity)] at h; linarith
      set X := R ^ 2 - (144 / 25) * sn ^ 2 with hX
      have hcoR2 : (6 / 5) ^ 2 ≤ (co * R) ^ 2 := pow_le_pow_left₀ (by norm_num) hcR 2
      have hXR : 0 ≤ X * R ^ 2 := by
        have hid : X * R ^ 2 = (R ^ 2 - 72 / 25) ^ 2 - (72 / 25) ^ 2 +
            (144 / 25) * (co * R) ^ 2 := by
          rw [hX]; linear_combination (-(144 / 25) * R ^ 2) * htrig
        rw [hid]
        have := sq_nonneg (R ^ 2 - 72 / 25)
        linarith
      have hX0 : 0 ≤ X := by
        by_contra hneg; push_neg at hneg
        have : X * R ^ 2 < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
        linarith
      have hsX : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX0
      have hb : c = (12 / 5) * co - Real.sqrt X - 1 := by
        rw [hcb]; unfold apm_t02a03_sector_aux_b; rfl
      have hsm : 1 + u ≤ (12 / 5) * co - Real.sqrt X := by linarith
      have hsp : 1 + u ≤ (12 / 5) * co + Real.sqrt X := by
        have := Real.sqrt_nonneg X; linarith
      have hprod : (1 + u) ^ 2 - (24 / 5) * co * (1 + u) + 144 / 25 - R ^ 2 =
          ((1 + u) - ((12 / 5) * co - Real.sqrt X)) *
            ((1 + u) - ((12 / 5) * co + Real.sqrt X)) := by
        linear_combination (-(144 / 25)) * htrig + hsX + hX
      have : 0 ≤ ((1 + u) - ((12 / 5) * co - Real.sqrt X)) *
          ((1 + u) - ((12 / 5) * co + Real.sqrt X)) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      linarith
    · have hR0 : 0 < R := by linarith
      have hcR : co * R ≤ 6 / 5 := by
        by_cases hz3 : |q.2.1| ≤ 3 / 20
        · have : ¬ (6 / (5 * R) ≤ co) := fun h => hD ⟨hz3, h⟩
          push_neg at this
          rw [lt_div_iff₀ (by positivity)] at this; linarith
        · push_neg at hz3
          have hz2 : (3 / 20) ^ 2 < q.2.1 ^ 2 := by
            rw [← sq_abs q.2.1]; exact pow_lt_pow_left₀ hz3 (by norm_num) (by norm_num)
          have ha5 : a < 1 / 5 := by
            by_contra hge; push_neg at hge
            have := pow_le_pow_left₀ (by norm_num) hge 2
            linarith
          have := mul_le_mul_of_nonneg_right (Real.cos_le_one q.1) hR0.le
          linarith
      have hcA : c = a := by
        rw [hc]; unfold apm_t02a03_sector_aux_c; rw [if_neg hD]
      have hprod : (1 + u) ^ 2 - (24 / 5) * co * (1 + u) + 144 / 25 - R ^ 2 =
          ((1 + u) - R) * ((1 + u) + R - (24 / 5) * co) + (144 / 25 - (24 / 5) * (co * R)) := by
        ring
      have : 0 ≤ ((1 + u) - R) * ((1 + u) + R - (24 / 5) * co) :=
        mul_nonneg_of_nonpos_of_nonpos (by rw [hR]; linarith) (by rw [hR]; linarith)
      linarith
  rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_infDist, h0, h1, h2]
  have hsL : R ≤ Real.sqrt ((6 / 5 - (1 + u) * co + 6 / 5) ^ 2 + ((1 + u) * sn) ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have : (6 / 5 - (1 + u) * co + 6 / 5) = 12 / 5 - (1 + u) * co := by ring
    rw [this]; exact hf
  have hsq : 1 / 16 ≤ (Real.sqrt ((6 / 5 - (1 + u) * co + 6 / 5) ^ 2 + ((1 + u) * sn) ^ 2) - 1) ^ 2 +
      q.2.1 ^ 2 := by
    have h1 : a ≤ Real.sqrt ((6 / 5 - (1 + u) * co + 6 / 5) ^ 2 + ((1 + u) * sn) ^ 2) - 1 := by
      linarith
    have := pow_le_pow_left₀ ha0 h1 2
    linarith
  rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt hsq

lemma apm_t02a03_sector_aux_L2b_inv_aux_right (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    apm_t02a03_sector_aux_PsiInv q ∈
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right := by
  exact ⟨apm_t02a03_sector_aux_L2b_inv_aux_right_aux_tube q hq,
    apm_t02a03_sector_aux_L2b_inv_aux_right_aux_left q hq⟩

set_option maxHeartbeats 1000000 in
lemma apm_t02a03_sector_aux_L2a_box_aux_v_aux_bounds (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right)
    (hz : |p 2| ≤ 1 / 5)
    (hcos : (17 / 25 : ℝ) ≤ (6 / 5 - p 0) /
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p) :
    let theta := apm_t02a03_sector_aux_theta p
    let z := p 2
    let u := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p - 1
    (-apm_t02a03_sector_aux_a z ≤ u ∧
      u ≤ apm_t02a03_sector_aux_c theta z ∧
      0 < apm_t02a03_sector_aux_c theta z + apm_t02a03_sector_aux_a z) := by
  intro theta z u
  obtain ⟨hX, hrad⟩ := apm_t02a03_sector_aux_L2a_box_aux_theta_aux_positive p hp hcos
  have hpos := apm_t02a03_sector_aux_L2_aux_cpa_pos theta z hz
  have hca := apm_t02a03_sector_aux_L2_aux_c_le_a theta z
  have ha2 := apm_t02a03_sector_aux_L2_aux_a_sq z hz
  have ha0 : 0 ≤ apm_t02a03_sector_aux_a z := Real.sqrt_nonneg _
  have ha4 := apm_t02a03_sector_aux_L2_aux_a_le z
  set X := 6 / 5 - p 0 with hXdef
  set Y := p 1 with hYdef
  set sr := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p with hsr
  have hsr' : sr = Real.sqrt (X ^ 2 + Y ^ 2) := hrad
  have hsr2 : sr ^ 2 = X ^ 2 + Y ^ 2 := by rw [hsr', Real.sq_sqrt (by positivity)]
  have hsqrt : Real.sqrt (1 + (Y / X) ^ 2) = sr / X := by
    rw [hsr', show (1 : ℝ) + (Y / X) ^ 2 = (X ^ 2 + Y ^ 2) / X ^ 2 by field_simp,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq hX.le]
  have hsr0 : 0 < sr := by rw [hsr']; exact Real.sqrt_pos.mpr (by positivity)
  have hcosθ : sr * Real.cos theta = X := by
    show sr * Real.cos (apm_t02a03_sector_aux_theta p) = X
    unfold apm_t02a03_sector_aux_theta
    rw [Real.cos_arctan, ← hXdef, ← hYdef, hsqrt]; field_simp
  -- inside the right tube
  have htube := hp.1
  rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_dist_eq, ← hsr] at htube
  have hsq1 : (sr - 1) ^ 2 + z ^ 2 ≤ 1 / 16 := by
    have h0 : 0 ≤ (sr - 1) ^ 2 + z ^ 2 := by positivity
    rw [Real.sqrt_le_left (by norm_num)] at htube; linarith
  have hu2 : (sr - 1) ^ 2 ≤ apm_t02a03_sector_aux_a z ^ 2 := by
    show (sr - 1) ^ 2 ≤ apm_t02a03_sector_aux_a (p 2) ^ 2
    have : z = p 2 := rfl
    rw [ha2]; linarith
  have habs := abs_le_of_sq_le_sq' hu2 ha0
  refine ⟨by show -apm_t02a03_sector_aux_a z ≤ sr - 1; linarith [habs.1], ?_, hpos⟩
  show sr - 1 ≤ apm_t02a03_sector_aux_c theta z
  by_cases hD : apm_t02a03_sector_aux_Delta (theta, z)
  · have hcb : apm_t02a03_sector_aux_c theta z = apm_t02a03_sector_aux_b theta z := by
      unfold apm_t02a03_sector_aux_c; rw [if_pos hD]
    obtain ⟨_, hcosD⟩ := hD
    set R := 1 + apm_t02a03_sector_aux_a z with hR
    set co := Real.cos theta with hco
    set sn := Real.sin theta with hsn
    have htrig : sn ^ 2 + co ^ 2 = 1 := Real.sin_sq_add_cos_sq theta
    have hR0 : 0 < R := by linarith
    have hcR : 6 / 5 ≤ co * R := by
      have h := hcosD; rw [div_le_iff₀ (by positivity)] at h; linarith
    have hco0 : 0 ≤ co := by
      by_contra h; push_neg at h
      have := mul_le_mul_of_nonneg_right h.le hR0.le
      rw [zero_mul] at this; linarith
    have hco96 : 24 / 25 ≤ co := by
      have := mul_le_mul_of_nonneg_left (show R ≤ 5 / 4 by linarith) hco0
      linarith
    -- outside the open left tube: s_L ≥ R
    have hleft := hp.2
    rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_infDist] at hleft
    set sL := Real.sqrt ((p 0 + 6 / 5) ^ 2 + p 1 ^ 2) with hsL
    have hsL2 : sL ^ 2 = sr ^ 2 - (24 / 5) * co * sr + 144 / 25 := by
      rw [hsL, Real.sq_sqrt (by positivity)]
      have : p 0 + 6 / 5 = 12 / 5 - X := by rw [hXdef]; ring
      rw [this]; nlinarith [hcosθ, hsr2]
    have hsL0 : 0 ≤ sL := Real.sqrt_nonneg _
    have hsr54 : sr ≤ 5 / 4 := by linarith [habs.2]
    have hsLbig : 1 < sL := by
      have : (1 : ℝ) ^ 2 < sL ^ 2 := by
        rw [hsL2]; have := Real.cos_le_one theta; nlinarith
      nlinarith
    have hl2 : 1 / 16 ≤ (sL - 1) ^ 2 + z ^ 2 := by
      have h := hleft
      rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
        rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
      exact (Real.sqrt_le_sqrt_iff (by positivity)).mp h
    have hsLR : R ≤ sL := by
      have : apm_t02a03_sector_aux_a z ^ 2 ≤ (sL - 1) ^ 2 := by
        show apm_t02a03_sector_aux_a (p 2) ^ 2 ≤ _
        rw [ha2]; linarith
      have := abs_le_of_sq_le_sq' this (by linarith)
      rw [hR]; linarith [this.2]
    have hf : 0 ≤ sr ^ 2 - (24 / 5) * co * sr + 144 / 25 - R ^ 2 := by
      have := pow_le_pow_left₀ hR0.le hsLR 2; linarith
    set Xq := R ^ 2 - (144 / 25) * sn ^ 2 with hXq
    have hcoR2 : (6 / 5) ^ 2 ≤ (co * R) ^ 2 := pow_le_pow_left₀ (by norm_num) hcR 2
    have hXR : 0 ≤ Xq * R ^ 2 := by
      have hid : Xq * R ^ 2 = (R ^ 2 - 72 / 25) ^ 2 - (72 / 25) ^ 2 + (144 / 25) * (co * R) ^ 2 := by
        rw [hXq]; linear_combination (-(144 / 25) * R ^ 2) * htrig
      rw [hid]; have := sq_nonneg (R ^ 2 - 72 / 25); linarith
    have hX0 : 0 ≤ Xq := by
      by_contra hneg; push_neg at hneg
      have : Xq * R ^ 2 < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
      linarith
    have hsX : Real.sqrt Xq ^ 2 = Xq := Real.sq_sqrt hX0
    have hprod : sr ^ 2 - (24 / 5) * co * sr + 144 / 25 - R ^ 2 =
        (sr - ((12 / 5) * co - Real.sqrt Xq)) * (sr - ((12 / 5) * co + Real.sqrt Xq)) := by
      linear_combination (-(144 / 25)) * htrig + hsX + hXq
    have hplus : sr - ((12 / 5) * co + Real.sqrt Xq) < 0 := by
      have := Real.sqrt_nonneg Xq; linarith
    have hminus : sr - ((12 / 5) * co - Real.sqrt Xq) ≤ 0 := by
      by_contra h; push_neg at h
      have : (sr - ((12 / 5) * co - Real.sqrt Xq)) * (sr - ((12 / 5) * co + Real.sqrt Xq)) < 0 :=
        mul_neg_of_pos_of_neg h hplus
      linarith
    rw [hcb]
    unfold apm_t02a03_sector_aux_b
    rw [← hR, ← hco, ← hsn]
    linarith
  · have hcA : apm_t02a03_sector_aux_c theta z = apm_t02a03_sector_aux_a z := by
      unfold apm_t02a03_sector_aux_c; rw [if_neg hD]
    rw [hcA]; linarith [habs.2]

lemma apm_t02a03_sector_aux_L2a_box_aux_v (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right)
    (hz : |p 2| ≤ 1 / 5)
    (hcos : (17 / 25 : ℝ) ≤ (6 / 5 - p 0) /
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p) :
    (apm_t02a03_sector_aux_Psi p).2.2 ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hlower, hupper, hden⟩ :=
    apm_t02a03_sector_aux_L2a_box_aux_v_aux_bounds p hp hz hcos
  simp only [apm_t02a03_sector_aux_Psi]
  constructor
  · exact div_nonneg (by linarith) (le_of_lt hden)
  · apply (div_le_one hden).2
    linarith

theorem apm_t02a03_sector_aux_L2a_box (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right) (hz : |p 2| ≤ 1 / 5)
    (hcos : (17 / 25 : ℝ) ≤ (6 / 5 - p 0) / apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p) :
    apm_t02a03_sector_aux_box (apm_t02a03_sector_aux_Psi p) := by
  refine ⟨apm_t02a03_sector_aux_L2a_box_aux_theta p hp hcos, ?_,
    apm_t02a03_sector_aux_L2a_box_aux_v p hp hz hcos⟩
  have hz' := abs_le.mp hz
  simp only [apm_t02a03_sector_aux_Psi]
  constructor <;> linarith

/-- On the box angles `c = min a b`: on `Delta` the bite boundary is inside the
tube (`b ≤ a`), off it `b ≥ a` (squaring gives `cos θ · (1 + a) ≤ 6/5`).  Both `a`
and `b` are continuous, so this is the continuity of `c` (claude-14). -/
lemma apm_t02a03_sector_aux_L1_aux_c_eq_min (θ z : ℝ) (hz : |z| ≤ 1 / 5)
    (hcos : (17 / 25 : ℝ) ≤ Real.cos θ) :
    apm_t02a03_sector_aux_c θ z =
      min (apm_t02a03_sector_aux_a z) (apm_t02a03_sector_aux_b θ z) := by
  have ha0 : 0 ≤ apm_t02a03_sector_aux_a z := Real.sqrt_nonneg _
  have ha4 := apm_t02a03_sector_aux_L2_aux_a_le z
  have ha2 := apm_t02a03_sector_aux_L2_aux_a_sq z hz
  by_cases hD : apm_t02a03_sector_aux_Delta (θ, z)
  · have hle : apm_t02a03_sector_aux_b θ z ≤ apm_t02a03_sector_aux_a z := by
      have := apm_t02a03_sector_aux_L2_aux_c_le_a θ z
      unfold apm_t02a03_sector_aux_c at this; rwa [if_pos hD] at this
    unfold apm_t02a03_sector_aux_c; rw [if_pos hD, min_eq_right hle]
  · set R := 1 + apm_t02a03_sector_aux_a z with hR
    have hR0 : 0 < R := by linarith
    have hcR : Real.cos θ * R ≤ 6 / 5 := by
      by_cases hz3 : |z| ≤ 3 / 20
      · have : ¬ (6 / (5 * R) ≤ Real.cos θ) := fun h => hD ⟨hz3, h⟩
        push_neg at this
        rw [lt_div_iff₀ (by positivity)] at this; linarith
      · push_neg at hz3
        have hz2 : (3 / 20) ^ 2 < z ^ 2 := by
          rw [← sq_abs z]; exact pow_lt_pow_left₀ hz3 (by norm_num) (by norm_num)
        have ha5 : apm_t02a03_sector_aux_a z < 1 / 5 := by
          by_contra hge; push_neg at hge
          have := pow_le_pow_left₀ (by norm_num) hge 2
          linarith
        have := mul_le_mul_of_nonneg_right (Real.cos_le_one θ) hR0.le
        linarith
    have hge : apm_t02a03_sector_aux_a z ≤ apm_t02a03_sector_aux_b θ z := by
      unfold apm_t02a03_sector_aux_b
      rw [← hR]
      have hY : 0 ≤ (12 / 5) * Real.cos θ - R := by linarith
      have : Real.sqrt (R ^ 2 - (144 / 25) * Real.sin θ ^ 2) ≤ (12 / 5) * Real.cos θ - R := by
        rw [Real.sqrt_le_left hY]
        have htrig := Real.sin_sq_add_cos_sq θ
        have hid : ((12 / 5) * Real.cos θ - R) ^ 2 - (R ^ 2 - (144 / 25) * Real.sin θ ^ 2) =
            (144 / 25) - (24 / 5) * (Real.cos θ * R) := by
          linear_combination (144 / 25) * htrig
        linarith
      linarith
    unfold apm_t02a03_sector_aux_c; rw [if_neg hD, min_eq_left hge]

lemma apm_t02a03_sector_aux_L1_aux_cos_box (q : ℝ × ℝ × ℝ) (hq : apm_t02a03_sector_aux_box q) :
    (17 / 25 : ℝ) ≤ Real.cos q.1 := by
  have hb := hq.1
  have hθ : |q.1| ≤ apm_t02a03_sector_aux_thetaOne := abs_le.mpr ⟨hb.1, hb.2⟩
  rw [← Real.cos_abs]
  have hpi : apm_t02a03_sector_aux_thetaOne ≤ Real.pi := Real.arccos_le_pi _
  calc (17 / 25 : ℝ) = Real.cos apm_t02a03_sector_aux_thetaOne := by
        unfold apm_t02a03_sector_aux_thetaOne; rw [Real.cos_arccos (by norm_num) (by norm_num)]
    _ ≤ Real.cos |q.1| := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hpi hθ

lemma apm_t02a03_sector_aux_L1_aux_b_continuous :
    Continuous (fun x : ℝ × ℝ => apm_t02a03_sector_aux_b x.1 x.2) := by
  unfold apm_t02a03_sector_aux_b apm_t02a03_sector_aux_a
  fun_prop

lemma apm_t02a03_sector_aux_L1_aux_minab_continuous :
    Continuous (fun x : ℝ × ℝ =>
      min (apm_t02a03_sector_aux_a x.2) (apm_t02a03_sector_aux_b x.1 x.2)) :=
  ((show Continuous apm_t02a03_sector_aux_a by
      unfold apm_t02a03_sector_aux_a; fun_prop).comp continuous_snd).min
    apm_t02a03_sector_aux_L1_aux_b_continuous

lemma apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_roundtrip_aux_coord
    (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right)
    (hz : |p 2| ≤ 1 / 5)
    (hcos : (17 / 25 : ℝ) ≤ (6 / 5 - p 0) /
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p)
    (i : Fin 3) :
    apm_t02a03_sector_aux_PsiInv (apm_t02a03_sector_aux_Psi p) i = p i := by
  obtain ⟨hX, hrad⟩ := apm_t02a03_sector_aux_L2a_box_aux_theta_aux_positive p hp hcos
  have hpos := apm_t02a03_sector_aux_L2_aux_cpa_pos (apm_t02a03_sector_aux_theta p) (p 2) hz
  set X := 6 / 5 - p 0 with hXdef
  set Y := p 1 with hYdef
  set sr := apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p with hsr
  have hsr' : sr = Real.sqrt (X ^ 2 + Y ^ 2) := hrad
  have hsqrt : Real.sqrt (1 + (Y / X) ^ 2) = sr / X := by
    rw [hsr', show (1 : ℝ) + (Y / X) ^ 2 = (X ^ 2 + Y ^ 2) / X ^ 2 by field_simp,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq hX.le]
  have hsr0 : 0 < sr := by rw [hsr']; exact Real.sqrt_pos.mpr (by positivity)
  have hcosθ : sr * Real.cos (apm_t02a03_sector_aux_theta p) = X := by
    unfold apm_t02a03_sector_aux_theta
    rw [Real.cos_arctan, ← hXdef, ← hYdef, hsqrt]; field_simp
  have hsinθ : sr * Real.sin (apm_t02a03_sector_aux_theta p) = Y := by
    unfold apm_t02a03_sector_aux_theta
    rw [Real.sin_arctan, ← hXdef, ← hYdef, hsqrt]; field_simp
  have hu : -apm_t02a03_sector_aux_a (p 2) + ((sr - 1 + apm_t02a03_sector_aux_a (p 2)) /
      (apm_t02a03_sector_aux_c (apm_t02a03_sector_aux_theta p) (p 2) +
        apm_t02a03_sector_aux_a (p 2))) *
      (apm_t02a03_sector_aux_c (apm_t02a03_sector_aux_theta p) (p 2) +
        apm_t02a03_sector_aux_a (p 2)) = sr - 1 := by
    rw [div_mul_cancel₀ _ hpos.ne']; ring
  fin_cases i
  · show 6 / 5 - (1 + (-apm_t02a03_sector_aux_a (p 2) + ((sr - 1 + apm_t02a03_sector_aux_a (p 2)) /
      (apm_t02a03_sector_aux_c (apm_t02a03_sector_aux_theta p) (p 2) +
        apm_t02a03_sector_aux_a (p 2))) *
      (apm_t02a03_sector_aux_c (apm_t02a03_sector_aux_theta p) (p 2) +
        apm_t02a03_sector_aux_a (p 2)))) * Real.cos (apm_t02a03_sector_aux_theta p) = p 0
    rw [hu, show (1 : ℝ) + (sr - 1) = sr by ring, hcosθ, hXdef]; ring
  · show (1 + (-apm_t02a03_sector_aux_a (p 2) + ((sr - 1 + apm_t02a03_sector_aux_a (p 2)) /
      (apm_t02a03_sector_aux_c (apm_t02a03_sector_aux_theta p) (p 2) +
        apm_t02a03_sector_aux_a (p 2))) *
      (apm_t02a03_sector_aux_c (apm_t02a03_sector_aux_theta p) (p 2) +
        apm_t02a03_sector_aux_a (p 2)))) * Real.sin (apm_t02a03_sector_aux_theta p) = p 1
    rw [hu, show (1 : ℝ) + (sr - 1) = sr by ring, hsinθ]
  · rfl

lemma apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_roundtrip
    (p : apm_t02a03_E3)
    (hp : p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right)
    (hz : |p 2| ≤ 1 / 5)
    (hcos : (17 / 25 : ℝ) ≤ (6 / 5 - p 0) /
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p) :
    apm_t02a03_sector_aux_PsiInv (apm_t02a03_sector_aux_Psi p) = p := by
  ext i
  exact apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_roundtrip_aux_coord
    p hp hz hcos i

lemma apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_psi_aux_theta :
    ContinuousOn (fun p : apm_t02a03_E3 => (apm_t02a03_sector_aux_Psi p).1)
      {p | |p 2| ≤ 1 / 5 ∧ p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right ∧
        (17 / 25 : ℝ) ≤ (6 / 5 - p 0) / apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p} := by
  intro p hp
  obtain ⟨hX, -⟩ := apm_t02a03_sector_aux_L2a_box_aux_theta_aux_positive p hp.2.1 hp.2.2
  show ContinuousWithinAt (fun p : apm_t02a03_E3 => Real.arctan (p 1 / (6 / 5 - p 0))) _ p
  apply ContinuousAt.continuousWithinAt
  apply Real.continuous_arctan.continuousAt.comp
  exact ContinuousAt.div (f := fun p : apm_t02a03_E3 => p 1) (g := fun p : apm_t02a03_E3 => 6 / 5 - p 0)
    (by fun_prop) (by fun_prop) hX.ne'

lemma apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_psi_aux_z :
    ContinuousOn (fun p : apm_t02a03_E3 => (apm_t02a03_sector_aux_Psi p).2.1)
      {p | |p 2| ≤ 1 / 5 ∧ p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right ∧
        (17 / 25 : ℝ) ≤ (6 / 5 - p 0) / apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p} := by
  show ContinuousOn (fun p : apm_t02a03_E3 => p 2) _
  exact (by fun_prop : Continuous fun p : apm_t02a03_E3 => p 2).continuousOn

lemma apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_psi_aux_v :
    ContinuousOn (fun p : apm_t02a03_E3 => (apm_t02a03_sector_aux_Psi p).2.2)
      {p | |p 2| ≤ 1 / 5 ∧ p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right ∧
        (17 / 25 : ℝ) ≤ (6 / 5 - p 0) / apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p} := by
  have hθc := apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_psi_aux_theta
  set S := {p : apm_t02a03_E3 | |p 2| ≤ 1 / 5 ∧ p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right ∧
        (17 / 25 : ℝ) ≤ (6 / 5 - p 0) / apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p} with hS
  have hcos : ∀ p ∈ S, (17 / 25 : ℝ) ≤ Real.cos (apm_t02a03_sector_aux_theta p) := by
    intro p hp
    obtain ⟨hX, hrad⟩ := apm_t02a03_sector_aux_L2a_box_aux_theta_aux_positive p hp.2.1 hp.2.2
    have hsr0 : 0 < apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p := by rw [hrad]; exact Real.sqrt_pos.mpr (by positivity)
    set X := 6 / 5 - p 0 with hXd
    set Y := p 1 with hYd
    have hsqrt : Real.sqrt (1 + (Y / X) ^ 2) = apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p / X := by
      rw [hrad, show (1 : ℝ) + (Y / X) ^ 2 = (X ^ 2 + Y ^ 2) / X ^ 2 by field_simp,
        Real.sqrt_div' _ (by positivity), Real.sqrt_sq hX.le]
    have : Real.cos (apm_t02a03_sector_aux_theta p) = X / apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p := by
      unfold apm_t02a03_sector_aux_theta; rw [Real.cos_arctan, ← hXd, ← hYd, hsqrt, one_div_div]
    rw [this]; exact hp.2.2
  have hg : ContinuousOn (fun p : apm_t02a03_E3 =>
      (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p - 1 + apm_t02a03_sector_aux_a (p 2)) /
        (min (apm_t02a03_sector_aux_a (p 2)) (apm_t02a03_sector_aux_b (apm_t02a03_sector_aux_theta p) (p 2)) +
          apm_t02a03_sector_aux_a (p 2))) S := by
    apply ContinuousOn.div
    · have : Continuous fun p : apm_t02a03_E3 => apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p - 1 + apm_t02a03_sector_aux_a (p 2) := by
        unfold apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad apm_t02a03_sector_aux_a; fun_prop
      exact this.continuousOn
    · have hm := apm_t02a03_sector_aux_L1_aux_minab_continuous.comp_continuousOn
        (hθc.prodMk (by fun_prop : Continuous fun p : apm_t02a03_E3 => p 2).continuousOn)
      exact hm.add ((show Continuous apm_t02a03_sector_aux_a by
        unfold apm_t02a03_sector_aux_a; fun_prop).comp (by fun_prop : Continuous fun p : apm_t02a03_E3 => p 2)).continuousOn
    · intro p hp
      have := apm_t02a03_sector_aux_L2_aux_cpa_pos (apm_t02a03_sector_aux_theta p) (p 2) hp.1
      rw [← apm_t02a03_sector_aux_L1_aux_c_eq_min _ _ hp.1 (hcos p hp)]
      exact this.ne'
  refine hg.congr ?_
  intro p hp
  show (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p - 1 + apm_t02a03_sector_aux_a (p 2)) /
      (apm_t02a03_sector_aux_c (apm_t02a03_sector_aux_theta p) (p 2) + apm_t02a03_sector_aux_a (p 2)) = _
  rw [apm_t02a03_sector_aux_L1_aux_c_eq_min _ _ hp.1 (hcos p hp)]

lemma apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_psi :
    ContinuousOn apm_t02a03_sector_aux_Psi
      {p | |p 2| ≤ 1 / 5 ∧ p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right ∧
        (17 / 25 : ℝ) ≤ (6 / 5 - p 0) / apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p} := by
  apply ContinuousOn.prodMk
  · exact apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_psi_aux_theta
  · apply ContinuousOn.prodMk
    · exact apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_psi_aux_z
    · exact apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_psi_aux_v

lemma apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_inv_aux_coord
    (i : Fin 3) :
    ContinuousOn (fun q : ℝ × ℝ × ℝ => apm_t02a03_sector_aux_PsiInv q i)
      {q | apm_t02a03_sector_aux_box q} := by
  have ha : Continuous apm_t02a03_sector_aux_a := by unfold apm_t02a03_sector_aux_a; fun_prop
  have hm := apm_t02a03_sector_aux_L1_aux_minab_continuous
  set u' : ℝ × ℝ × ℝ → ℝ := fun q => -apm_t02a03_sector_aux_a q.2.1 +
    q.2.2 * (min (apm_t02a03_sector_aux_a q.2.1) (apm_t02a03_sector_aux_b q.1 q.2.1) +
      apm_t02a03_sector_aux_a q.2.1) with hu'
  have hu'c : Continuous u' := by
    rw [hu']
    have h1 : Continuous fun q : ℝ × ℝ × ℝ =>
        min (apm_t02a03_sector_aux_a q.2.1) (apm_t02a03_sector_aux_b q.1 q.2.1) :=
      hm.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    exact ((ha.comp (continuous_fst.comp continuous_snd)).neg).add
      ((continuous_snd.comp continuous_snd).mul (h1.add (ha.comp (continuous_fst.comp continuous_snd))))
  have hcongr : ∀ q ∈ {q : ℝ × ℝ × ℝ | apm_t02a03_sector_aux_box q},
      -apm_t02a03_sector_aux_a q.2.1 +
        q.2.2 * (apm_t02a03_sector_aux_c q.1 q.2.1 + apm_t02a03_sector_aux_a q.2.1) = u' q := by
    intro q hq
    have hz : |q.2.1| ≤ 1 / 5 := abs_le.mpr ⟨by linarith [hq.2.1.1], hq.2.1.2⟩
    rw [hu', apm_t02a03_sector_aux_L1_aux_c_eq_min _ _ hz
      (apm_t02a03_sector_aux_L1_aux_cos_box q hq)]
  fin_cases i
  · refine ContinuousOn.congr (f := fun q => 6 / 5 - (1 + u' q) * Real.cos q.1) ?_ ?_
    · exact (continuous_const.sub ((continuous_const.add hu'c).mul
        (Real.continuous_cos.comp continuous_fst))).continuousOn
    · intro q hq; simp only [Fin.zero_eta, Fin.isValue]
      rw [(apm_t02a03_sector_aux_L2_aux_PsiInv_coords q).1, hcongr q hq]
  · refine ContinuousOn.congr (f := fun q => (1 + u' q) * Real.sin q.1) ?_ ?_
    · exact ((continuous_const.add hu'c).mul (Real.continuous_sin.comp continuous_fst)).continuousOn
    · intro q hq; simp only [Fin.mk_one, Fin.isValue]
      rw [(apm_t02a03_sector_aux_L2_aux_PsiInv_coords q).2.1, hcongr q hq]
  · refine ContinuousOn.congr (f := fun q => q.2.1) ?_ ?_
    · exact (continuous_fst.comp continuous_snd).continuousOn
    · intro q _; exact (apm_t02a03_sector_aux_L2_aux_PsiInv_coords q).2.2

lemma apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_inv :
    ContinuousOn apm_t02a03_sector_aux_PsiInv
      {q | apm_t02a03_sector_aux_box q} := by
  have hpi : ContinuousOn
      (fun q : ℝ × ℝ × ℝ => fun i : Fin 3 =>
        apm_t02a03_sector_aux_PsiInv q i)
      {q | apm_t02a03_sector_aux_box q} :=
    continuousOn_pi.2
      apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_inv_aux_coord
  have h := (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).continuousOn.comp
    hpi (Set.mapsTo_univ _ _)
  simpa using h

theorem apm_t02a03_sector_aux_L1_roundtrip_continuity :
    (∀ p : apm_t02a03_E3, p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right →
      |p 2| ≤ 1 / 5 →
      (17 / 25 : ℝ) ≤ (6 / 5 - p 0) / apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p →
      apm_t02a03_sector_aux_PsiInv (apm_t02a03_sector_aux_Psi p) = p) ∧
    ContinuousOn apm_t02a03_sector_aux_Psi
      {p | |p 2| ≤ 1 / 5 ∧ p ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right ∧
        (17 / 25 : ℝ) ≤ (6 / 5 - p 0) / apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p} ∧
    ContinuousOn apm_t02a03_sector_aux_PsiInv
      {q | apm_t02a03_sector_aux_box q} := by
  exact ⟨fun p hp hz hcos ↦
    apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_roundtrip p hp hz hcos,
    apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_psi,
    apm_t02a03_sector_aux_L1_roundtrip_continuity_aux_inv⟩

lemma apm_t02a03_sector_aux_L2b_inv_aux_cos_aux_ratio (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    (6 / 5 - apm_t02a03_sector_aux_PsiInv q 0) /
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad
        (apm_t02a03_sector_aux_PsiInv q) = Real.cos q.1 := by
  rw [apm_t02a03_sector_aux_L2b_inv_aux_cos_aux_rad q hq]
  obtain ⟨h0, -, -⟩ := apm_t02a03_sector_aux_L2_aux_PsiInv_coords q
  have hu := apm_t02a03_sector_aux_L2_aux_u_ge q hq
  have ha4 := apm_t02a03_sector_aux_L2_aux_a_le q.2.1
  set u := -apm_t02a03_sector_aux_a q.2.1 +
    q.2.2 * (apm_t02a03_sector_aux_c q.1 q.2.1 + apm_t02a03_sector_aux_a q.2.1)
  have hne : (1 : ℝ) + u ≠ 0 := by linarith
  rw [h0, show (6 / 5 : ℝ) - (6 / 5 - (1 + u) * Real.cos q.1) = (1 + u) * Real.cos q.1 by ring,
    mul_div_cancel_left₀ _ hne]

lemma apm_t02a03_sector_aux_L2b_inv_aux_cos_aux_bound (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    (17 / 25 : ℝ) ≤ Real.cos q.1 := by
  have htheta := hq.1
  change -Real.arccos (17 / 25) ≤ q.1 ∧
    q.1 ≤ Real.arccos (17 / 25) at htheta
  have habs : |q.1| ≤ Real.arccos (17 / 25) := by
    rw [abs_le]
    exact htheta
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (abs_nonneg q.1) (Real.arccos_le_pi (17 / 25)) habs
  rw [Real.cos_arccos (by norm_num : (-1 : ℝ) ≤ 17 / 25)
    (by norm_num : (17 / 25 : ℝ) ≤ 1), Real.cos_abs] at hcos
  exact hcos

lemma apm_t02a03_sector_aux_L2b_inv_aux_cos (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    (17 / 25 : ℝ) ≤ (6 / 5 - apm_t02a03_sector_aux_PsiInv q 0) /
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad
        (apm_t02a03_sector_aux_PsiInv q) := by
  rw [apm_t02a03_sector_aux_L2b_inv_aux_cos_aux_ratio q hq]
  exact apm_t02a03_sector_aux_L2b_inv_aux_cos_aux_bound q hq

lemma apm_t02a03_sector_aux_L2b_inv_aux_roundtrip_aux_theta (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    (apm_t02a03_sector_aux_Psi (apm_t02a03_sector_aux_PsiInv q)).1 = q.1 := by
  obtain ⟨h0, h1, -⟩ := apm_t02a03_sector_aux_L2_aux_PsiInv_coords q
  have hu := apm_t02a03_sector_aux_L2_aux_u_ge q hq
  have ha4 := apm_t02a03_sector_aux_L2_aux_a_le q.2.1
  set u := -apm_t02a03_sector_aux_a q.2.1 +
    q.2.2 * (apm_t02a03_sector_aux_c q.1 q.2.1 + apm_t02a03_sector_aux_a q.2.1)
  have hne : (1 : ℝ) + u ≠ 0 := by linarith
  have hθ1 : apm_t02a03_sector_aux_thetaOne < Real.pi / 2 := by
    unfold apm_t02a03_sector_aux_thetaOne
    rw [Real.arccos_lt_pi_div_two]; norm_num
  have hb := hq.1
  have hcos : Real.cos q.1 ≠ 0 := (Real.cos_pos_of_mem_Ioo ⟨by linarith [hb.1], by linarith [hb.2]⟩).ne'
  show Real.arctan ((apm_t02a03_sector_aux_PsiInv q) 1 / (6 / 5 - (apm_t02a03_sector_aux_PsiInv q) 0)) = q.1
  rw [h0, h1, show (6 / 5 : ℝ) - (6 / 5 - (1 + u) * Real.cos q.1) = (1 + u) * Real.cos q.1 by ring,
    mul_div_mul_left _ _ hne, ← Real.tan_eq_sin_div_cos]
  exact Real.arctan_tan (by linarith [hb.1]) (by linarith [hb.2])

lemma apm_t02a03_sector_aux_L2b_inv_aux_roundtrip_aux_z (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    (apm_t02a03_sector_aux_Psi (apm_t02a03_sector_aux_PsiInv q)).2.1 = q.2.1 := by
  rfl

lemma apm_t02a03_sector_aux_L2b_inv_aux_roundtrip_aux_v (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    (apm_t02a03_sector_aux_Psi (apm_t02a03_sector_aux_PsiInv q)).2.2 = q.2.2 := by
  have hθ := apm_t02a03_sector_aux_L2b_inv_aux_roundtrip_aux_theta q hq
  have hrad := apm_t02a03_sector_aux_L2b_inv_aux_cos_aux_rad q hq
  obtain ⟨-, -, h2⟩ := apm_t02a03_sector_aux_L2_aux_PsiInv_coords q
  have hz : |q.2.1| ≤ 1 / 5 := abs_le.mpr ⟨by linarith [hq.2.1.1], hq.2.1.2⟩
  have hpos := apm_t02a03_sector_aux_L2_aux_cpa_pos q.1 q.2.1 hz
  show (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad (apm_t02a03_sector_aux_PsiInv q) - 1 +
      apm_t02a03_sector_aux_a ((apm_t02a03_sector_aux_PsiInv q) 2)) /
    (apm_t02a03_sector_aux_c (apm_t02a03_sector_aux_theta (apm_t02a03_sector_aux_PsiInv q))
        ((apm_t02a03_sector_aux_PsiInv q) 2) +
      apm_t02a03_sector_aux_a ((apm_t02a03_sector_aux_PsiInv q) 2)) = q.2.2
  have hθ' : apm_t02a03_sector_aux_theta (apm_t02a03_sector_aux_PsiInv q) = q.1 := hθ
  rw [hrad, h2, hθ']
  field_simp
  ring

lemma apm_t02a03_sector_aux_L2b_inv_aux_roundtrip (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    apm_t02a03_sector_aux_Psi (apm_t02a03_sector_aux_PsiInv q) = q := by
  apply Prod.ext
  · exact apm_t02a03_sector_aux_L2b_inv_aux_roundtrip_aux_theta q hq
  · apply Prod.ext
    · exact apm_t02a03_sector_aux_L2b_inv_aux_roundtrip_aux_z q hq
    · exact apm_t02a03_sector_aux_L2b_inv_aux_roundtrip_aux_v q hq

theorem apm_t02a03_sector_aux_L2b_inv (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    apm_t02a03_sector_aux_PsiInv q ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right ∧
      |apm_t02a03_sector_aux_PsiInv q 2| ≤ 1 / 5 ∧
      (17 / 25 : ℝ) ≤ (6 / 5 - apm_t02a03_sector_aux_PsiInv q 0) /
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad (apm_t02a03_sector_aux_PsiInv q) ∧
      apm_t02a03_sector_aux_Psi (apm_t02a03_sector_aux_PsiInv q) = q := by
  refine ⟨apm_t02a03_sector_aux_L2b_inv_aux_right q hq, ?_,
    apm_t02a03_sector_aux_L2b_inv_aux_cos q hq,
    apm_t02a03_sector_aux_L2b_inv_aux_roundtrip q hq⟩
  change |q.2.1| ≤ 1 / 5
  rw [abs_le]
  have hz := hq.2.1
  change (-1 / 5 : ℝ) ≤ q.2.1 ∧ q.2.1 ≤ 1 / 5 at hz
  constructor <;> linarith [hz.1, hz.2]

lemma apm_t02a03_sector_aux_L3_target_iff_aux_torus_aux_geometry (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    (apm_t02a03_sector_aux_PsiInv q ∈
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus) ↔
      apm_t02a03_sector_aux_Delta (q.1, q.2.1) ∧
        (-apm_t02a03_sector_aux_a q.2.1 +
          q.2.2 * (apm_t02a03_sector_aux_c q.1 q.2.1 +
            apm_t02a03_sector_aux_a q.2.1) =
          apm_t02a03_sector_aux_b q.1 q.2.1) := by
  sorry

lemma apm_t02a03_sector_aux_L3_target_iff_aux_torus_aux_endpoint (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q)
    (hDelta : apm_t02a03_sector_aux_Delta (q.1, q.2.1)) :
    (-apm_t02a03_sector_aux_a q.2.1 +
        q.2.2 * (apm_t02a03_sector_aux_c q.1 q.2.1 +
          apm_t02a03_sector_aux_a q.2.1) =
        apm_t02a03_sector_aux_b q.1 q.2.1) ↔ q.2.2 = 1 := by
  have hc : apm_t02a03_sector_aux_c q.1 q.2.1 =
      apm_t02a03_sector_aux_b q.1 q.2.1 := by
    simp [apm_t02a03_sector_aux_c, hDelta]
  obtain ⟨hright, hz, hcos, hround⟩ :=
    apm_t02a03_sector_aux_L2b_inv q hq
  obtain ⟨_, _, hden⟩ :=
    apm_t02a03_sector_aux_L2a_box_aux_v_aux_bounds
      (apm_t02a03_sector_aux_PsiInv q) hright hz hcos
  have hden' : 0 < apm_t02a03_sector_aux_c q.1 q.2.1 +
      apm_t02a03_sector_aux_a q.2.1 := by
    rw [← hround]
    simpa [apm_t02a03_sector_aux_Psi] using hden
  rw [hc] at hden' ⊢
  constructor
  · intro h
    have : (q.2.2 - 1) *
        (apm_t02a03_sector_aux_b q.1 q.2.1 +
          apm_t02a03_sector_aux_a q.2.1) = 0 := by
      linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (ne_of_gt hden'))
  · intro h
    rw [h]
    ring

lemma apm_t02a03_sector_aux_L3_target_iff_aux_torus (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    (apm_t02a03_sector_aux_PsiInv q ∈
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus) ↔
      q.2.2 = 1 ∧ apm_t02a03_sector_aux_Delta (q.1, q.2.1) := by
  rw [apm_t02a03_sector_aux_L3_target_iff_aux_torus_aux_geometry q hq]
  constructor
  · rintro ⟨hDelta, hu⟩
    exact ⟨(apm_t02a03_sector_aux_L3_target_iff_aux_torus_aux_endpoint q hq hDelta).1 hu,
      hDelta⟩
  · rintro ⟨hv, hDelta⟩
    exact ⟨hDelta,
      (apm_t02a03_sector_aux_L3_target_iff_aux_torus_aux_endpoint q hq hDelta).2 hv⟩

lemma apm_t02a03_sector_aux_L3_target_iff_aux_loop_aux_coordinates (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    (apm_t02a03_sector_aux_PsiInv q ∈
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop) ↔
      q.2.1 = 0 ∧
        (-apm_t02a03_sector_aux_a q.2.1 +
          q.2.2 * (apm_t02a03_sector_aux_c q.1 q.2.1 +
            apm_t02a03_sector_aux_a q.2.1) = 3 / 20) := by
  obtain ⟨h0, h1, h2⟩ := apm_t02a03_sector_aux_L2_aux_PsiInv_coords q
  have hu := apm_t02a03_sector_aux_L2_aux_u_ge q hq
  have ha4 := apm_t02a03_sector_aux_L2_aux_a_le q.2.1
  set u := -apm_t02a03_sector_aux_a q.2.1 +
    q.2.2 * (apm_t02a03_sector_aux_c q.1 q.2.1 + apm_t02a03_sector_aux_a q.2.1) with hu'
  have hs : 0 < 1 + u := by linarith
  have htrig := Real.sin_sq_add_cos_sq q.1
  constructor
  · rintro ⟨t, ht⟩
    have e0 := congrArg (fun p : apm_t02a03_E3 => p 0) ht
    have e1 := congrArg (fun p : apm_t02a03_E3 => p 1) ht
    have e2 := congrArg (fun p : apm_t02a03_E3 => p 2) ht
    simp only at e0 e1 e2
    rw [h0] at e0; rw [h1] at e1; rw [h2] at e2
    simp at e0 e1 e2
    refine ⟨e2.symm, ?_⟩
    have ht2 := Real.sin_sq_add_cos_sq t
    have hsq : (1 + u) ^ 2 = (23 / 20) ^ 2 := by
      calc (1 + u) ^ 2 = ((1 + u) * Real.sin q.1) ^ 2 + ((1 + u) * Real.cos q.1) ^ 2 := by
            linear_combination (-(1 + u) ^ 2) * htrig
        _ = (23 / 20 * Real.sin t) ^ 2 + (23 / 20 * Real.cos t) ^ 2 := by rw [← e1, ← e0]
        _ = (23 / 20) ^ 2 := by linear_combination (23 / 20) ^ 2 * ht2
    have := (pow_left_inj₀ hs.le (by norm_num) two_ne_zero).mp hsq
    linarith
  · rintro ⟨hz, hu3⟩
    refine ⟨q.1, ?_⟩
    have hs' : 1 + u = 23 / 20 := by linarith
    ext i; fin_cases i
    · simp [h0, hs']
    · simp [h1, hs']
    · simp [h2, hz]

lemma apm_t02a03_sector_aux_L3_target_iff_aux_loop_aux_parameter (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) (hz : q.2.1 = 0) :
    (-apm_t02a03_sector_aux_a q.2.1 +
        q.2.2 * (apm_t02a03_sector_aux_c q.1 q.2.1 +
          apm_t02a03_sector_aux_a q.2.1) = 3 / 20) ↔
      q.2.2 = apm_t02a03_sector_aux_vArc q.1 := by
  have ha0 : apm_t02a03_sector_aux_a 0 = 1 / 4 := by
    unfold apm_t02a03_sector_aux_a
    rw [show (1 / 16 - (0 : ℝ) ^ 2) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hpos := apm_t02a03_sector_aux_L2_aux_cpa_pos q.1 0 (by norm_num)
  rw [hz, ha0] at *
  rw [ha0] at hpos
  unfold apm_t02a03_sector_aux_vArc
  rw [eq_div_iff hpos.ne']
  constructor <;> intro h <;> linarith

lemma apm_t02a03_sector_aux_L3_target_iff_aux_loop (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    (apm_t02a03_sector_aux_PsiInv q ∈
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop) ↔
      q.2.1 = 0 ∧ q.2.2 = apm_t02a03_sector_aux_vArc q.1 := by
  rw [apm_t02a03_sector_aux_L3_target_iff_aux_loop_aux_coordinates q hq]
  constructor
  · rintro ⟨hz, hu⟩
    exact ⟨hz, (apm_t02a03_sector_aux_L3_target_iff_aux_loop_aux_parameter q hq hz).1 hu⟩
  · rintro ⟨hz, hv⟩
    exact ⟨hz, (apm_t02a03_sector_aux_L3_target_iff_aux_loop_aux_parameter q hq hz).2 hv⟩

theorem apm_t02a03_sector_aux_L3_target_iff (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    ((apm_t02a03_sector_aux_PsiInv q ∈
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus) ↔
      q.2.2 = 1 ∧ apm_t02a03_sector_aux_Delta (q.1, q.2.1)) ∧
    ((apm_t02a03_sector_aux_PsiInv q ∈
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop) ↔
      q.2.1 = 0 ∧ q.2.2 = apm_t02a03_sector_aux_vArc q.1) := by
  exact ⟨apm_t02a03_sector_aux_L3_target_iff_aux_torus q hq,
    apm_t02a03_sector_aux_L3_target_iff_aux_loop q hq⟩

lemma apm_t02a03_sector_aux_L4_clamp_aux_continuous :
    Continuous (Function.uncurry apm_t02a03_sector_aux_clampMove) := by
  unfold apm_t02a03_sector_aux_clampMove apm_t02a03_sector_aux_clampZ
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_)
  fin_cases i <;> simp <;> fun_prop

/-- In the right tube at height `|z| ≥ 1/5` the planar distance from the left
centre is at least `5/4` (claude-14). -/
lemma apm_t02a03_sector_aux_L4_aux_left_planar (p : apm_t02a03_E3)
    (hpR : Metric.infDist p (Set.range apm_t02a03_rightCore) ≤ (1 / 4 : ℝ))
    (hz : (1 / 5 : ℝ) ≤ |p 2|) :
    (5 / 4 : ℝ) ≤ Real.sqrt ((p 0 + 6 / 5) ^ 2 + p 1 ^ 2) := by
  rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_dist_eq] at hpR
  have hsq : (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p - 1) ^ 2 + p 2 ^ 2 ≤ 1 / 16 := by
    have h0 : 0 ≤ (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p - 1) ^ 2 + p 2 ^ 2 := by positivity
    have := Real.sqrt_le_sqrt (le_of_eq (rfl : (apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p - 1) ^ 2 + p 2 ^ 2 = _))
    rw [Real.sqrt_le_left (by norm_num)] at hpR
    linarith
  have hz2 : (1 / 25 : ℝ) ≤ p 2 ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (p 2)]
  have hr0 : 0 ≤ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p := Real.sqrt_nonneg _
  have hr : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p ≤ 23 / 20 := by nlinarith
  have hr2 : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p ^ 2 = (p 0 - 6 / 5) ^ 2 + p 1 ^ 2 := by
    unfold apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad; rw [Real.sq_sqrt (by positivity)]
  have hx : 6 / 5 - apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p ≤ p 0 := by
    have : (p 0 - 6 / 5) ^ 2 ≤ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p ^ 2 := by rw [hr2]; nlinarith [sq_nonneg (p 1)]
    nlinarith [abs_le_of_sq_le_sq' this hr0]
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  nlinarith

lemma apm_t02a03_sector_aux_L4_aux_clamp_abs (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (z : ℝ) :
    |(1 - t) * z + t * apm_t02a03_sector_aux_clampZ z| ≤ |z| ∧
      ((1 / 5 : ℝ) < |z| → (1 / 5 : ℝ) ≤ |(1 - t) * z + t * apm_t02a03_sector_aux_clampZ z|) ∧
      (|z| ≤ 1 / 5 → (1 - t) * z + t * apm_t02a03_sector_aux_clampZ z = z) := by
  obtain ⟨ht0, ht1⟩ := ht
  unfold apm_t02a03_sector_aux_clampZ
  rcases le_or_gt z (-1 / 5) with h | h
  · rw [min_eq_right (by linarith), max_eq_left h]
    have hz : |z| = -z := abs_of_neg (by linarith)
    have hw : |(1 - t) * z + t * (-1 / 5)| = -((1 - t) * z + t * (-1 / 5)) :=
      abs_of_nonpos (by nlinarith)
    rw [hz, hw]
    refine ⟨by nlinarith, fun _ => by nlinarith, fun h' => ?_⟩
    have hz5 : z = -1 / 5 := by linarith
    subst hz5; ring
  rcases le_or_gt z (1 / 5) with h' | h'
  · rw [min_eq_right h', max_eq_right h.le]
    refine ⟨by ring_nf; exact le_rfl, fun h'' => ?_, fun _ => by ring⟩
    exact absurd h'' (not_lt.mpr (abs_le.mpr ⟨by linarith, h'⟩))
  · rw [min_eq_left h'.le, max_eq_right (by norm_num)]
    have hz : |z| = z := abs_of_pos (by linarith)
    have hw : |(1 - t) * z + t * (1 / 5)| = (1 - t) * z + t * (1 / 5) :=
      abs_of_nonneg (by nlinarith)
    rw [hz, hw]
    refine ⟨by nlinarith, fun _ => by nlinarith, fun h'' => by linarith⟩

lemma apm_t02a03_sector_aux_L4_clamp_aux_fix_aux_z_bound
    (p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X)
    (hp : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z p) :
    |(p.1 : apm_t02a03_E3) 2| ≤ (1 / 5 : ℝ) := by
  rcases hp with hT | hL
  · by_contra hz
    push_neg at hz
    have hpR := p.2.1
    have hsL := apm_t02a03_sector_aux_L4_aux_left_planar p.1 hpR hz.le
    have hT' : Metric.infDist (p.1 : apm_t02a03_E3) apm_t02a03_C = 1 / 4 := hT
    rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_infDist] at hT'
    have hz2 : (1 / 25 : ℝ) < (p.1 : apm_t02a03_E3) 2 ^ 2 := by
      rw [← sq_abs]; nlinarith [abs_nonneg ((p.1 : apm_t02a03_E3) 2)]
    have h1 : (1 / 16 : ℝ) < (Real.sqrt (((p.1 : apm_t02a03_E3) 0 + 6 / 5) ^ 2 +
        (p.1 : apm_t02a03_E3) 1 ^ 2) - 1) ^ 2 + (p.1 : apm_t02a03_E3) 2 ^ 2 := by nlinarith
    have h2 := Real.sqrt_lt_sqrt (by norm_num) h1
    rw [show Real.sqrt (1 / 16 : ℝ) = 1 / 4 by
      rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h2
    linarith
  · obtain ⟨u, hu⟩ := hL
    rw [← hu]
    simp

lemma apm_t02a03_sector_aux_L4_clamp_aux_fix_aux_clampZ
    (z : ℝ) (hz : |z| ≤ (1 / 5 : ℝ)) :
    apm_t02a03_sector_aux_clampZ z = z := by
  rw [abs_le] at hz
  unfold apm_t02a03_sector_aux_clampZ
  rw [min_eq_right (by norm_num at hz ⊢; exact hz.2)]
  rw [max_eq_right (by norm_num at hz ⊢; exact hz.1)]

lemma apm_t02a03_sector_aux_L4_clamp_aux_right_aux_right_tube
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (p : apm_t02a03_E3)
    (hp : Metric.infDist p (Set.range apm_t02a03_rightCore) ≤ (1 / 4 : ℝ)) :
    Metric.infDist (apm_t02a03_sector_aux_clampMove t p)
        (Set.range apm_t02a03_rightCore) ≤ (1 / 4 : ℝ) := by
  rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_tube_aux_dist_eq] at hp ⊢
  have hrad : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad (apm_t02a03_sector_aux_clampMove t p) = apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p := by
    simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad, apm_t02a03_sector_aux_clampMove]
  have hz := (apm_t02a03_sector_aux_L4_aux_clamp_abs t ht (p 2)).1
  have hz2 : (apm_t02a03_sector_aux_clampMove t p) 2 ^ 2 ≤ p 2 ^ 2 := by
    have : (apm_t02a03_sector_aux_clampMove t p) 2 =
        (1 - t) * p 2 + t * apm_t02a03_sector_aux_clampZ (p 2) := by
      simp [apm_t02a03_sector_aux_clampMove]
    rw [this, ← sq_abs, ← sq_abs (p 2)]
    exact pow_le_pow_left₀ (abs_nonneg _) hz 2
  rw [hrad]
  exact (Real.sqrt_le_sqrt (by linarith)).trans hp

lemma apm_t02a03_sector_aux_L4_clamp_aux_right_aux_left_far
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (p : apm_t02a03_E3)
    (hpR : Metric.infDist p (Set.range apm_t02a03_rightCore) ≤ (1 / 4 : ℝ))
    (hpL : (1 / 4 : ℝ) ≤ Metric.infDist p apm_t02a03_C) :
    (1 / 4 : ℝ) ≤
      Metric.infDist (apm_t02a03_sector_aux_clampMove t p) apm_t02a03_C := by
  have hcl := apm_t02a03_sector_aux_L4_aux_clamp_abs t ht (p 2)
  rcases le_or_gt |p 2| (1 / 5) with hz | hz
  · have hfix : apm_t02a03_sector_aux_clampMove t p = p := by
      ext i; fin_cases i <;> simp [apm_t02a03_sector_aux_clampMove, hcl.2.2 hz]
    rw [hfix]; exact hpL
  · have hsL := apm_t02a03_sector_aux_L4_aux_left_planar p hpR hz.le
    rw [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus_homeomorph_aux_infDist]
    have h0 : (apm_t02a03_sector_aux_clampMove t p) 0 = p 0 := by
      simp [apm_t02a03_sector_aux_clampMove]
    have h1 : (apm_t02a03_sector_aux_clampMove t p) 1 = p 1 := by
      simp [apm_t02a03_sector_aux_clampMove]
    rw [h0, h1]
    have hq : (1 / 16 : ℝ) ≤ (Real.sqrt ((p 0 + 6 / 5) ^ 2 + p 1 ^ 2) - 1) ^ 2 +
        (apm_t02a03_sector_aux_clampMove t p) 2 ^ 2 := by
      nlinarith [sq_nonneg ((apm_t02a03_sector_aux_clampMove t p) 2)]
    rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
      rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hq

lemma apm_t02a03_sector_aux_L4_clamp_aux_right
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X)
    (hp : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y p) :
    apm_t02a03_sector_aux_clampMove t p.1 ∈
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right := by
  exact ⟨apm_t02a03_sector_aux_L4_clamp_aux_right_aux_right_tube t ht p.1 p.2.1,
    apm_t02a03_sector_aux_L4_clamp_aux_right_aux_left_far t ht p.1 p.2.1 p.2.2⟩

lemma apm_t02a03_sector_aux_L4_clamp_aux_target
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X)
    (hp : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y p) :
    let moved := apm_t02a03_sector_aux_clampMove t p.1
    (moved ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop) ∨
      (17 / 25 : ℝ) ≤ (6 / 5 - moved 0) /
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad moved := by
  rcases hp with hp | hp
  · left
    have hfix : apm_t02a03_sector_aux_clampMove t p.1 = p.1 := by
      have hz := apm_t02a03_sector_aux_L4_clamp_aux_fix_aux_z_bound p hp
      have hclamp := apm_t02a03_sector_aux_L4_clamp_aux_fix_aux_clampZ (p.1 2) hz
      ext i
      fin_cases i <;>
        simp [apm_t02a03_sector_aux_clampMove, hclamp] <;> ring
    simpa [hfix] using hp
  · right
    have h0 : apm_t02a03_sector_aux_clampMove t p.1 0 = p.1 0 := by
      simp [apm_t02a03_sector_aux_clampMove]
    have h1 : apm_t02a03_sector_aux_clampMove t p.1 1 = p.1 1 := by
      simp [apm_t02a03_sector_aux_clampMove]
    have hrad :
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad
            (apm_t02a03_sector_aux_clampMove t p.1) =
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad p.1 := by
      simp [apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad,
        h0, h1]
    simpa [h0, hrad] using hp

lemma apm_t02a03_sector_aux_L4_clamp_aux_fix
    (t : ℝ)
    (p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X)
    (hp : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z p) :
    apm_t02a03_sector_aux_clampMove t p.1 = p.1 := by
  have hz := apm_t02a03_sector_aux_L4_clamp_aux_fix_aux_z_bound p hp
  have hclamp := apm_t02a03_sector_aux_L4_clamp_aux_fix_aux_clampZ (p.1 2) hz
  ext i
  fin_cases i <;> simp [apm_t02a03_sector_aux_clampMove, hclamp] <;> ring

theorem apm_t02a03_sector_aux_L4_clamp :
    Continuous (Function.uncurry apm_t02a03_sector_aux_clampMove) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X,
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y p →
      let moved := apm_t02a03_sector_aux_clampMove t p.1
      moved ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right ∧
        ((moved ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∪
            apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_loop) ∨
          (17 / 25 : ℝ) ≤ (6 / 5 - moved 0) /
            apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad moved)) ∧
    (∀ t (p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X),
      apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z p →
      apm_t02a03_sector_aux_clampMove t p.1 = p.1) := by
  refine ⟨apm_t02a03_sector_aux_L4_clamp_aux_continuous, ?_, ?_⟩
  · intro t ht p hp
    exact ⟨apm_t02a03_sector_aux_L4_clamp_aux_right t ht p hp,
      apm_t02a03_sector_aux_L4_clamp_aux_target t ht p hp⟩
  · exact apm_t02a03_sector_aux_L4_clamp_aux_fix

lemma apm_t02a03_sector_aux_L5_aux_a_continuous : Continuous apm_t02a03_sector_aux_a := by
  unfold apm_t02a03_sector_aux_a; fun_prop

lemma apm_t02a03_sector_aux_L5_aux_Theta_continuous :
    Continuous apm_t02a03_sector_aux_Theta := by
  unfold apm_t02a03_sector_aux_Theta
  refine Real.continuous_arccos.comp (continuous_const.div
    (continuous_const.mul (continuous_const.add apm_t02a03_sector_aux_L5_aux_a_continuous)) ?_)
  intro z
  have := Real.sqrt_nonneg (1 / 16 - z ^ 2)
  unfold apm_t02a03_sector_aux_a
  positivity

lemma apm_t02a03_sector_aux_L5_piDelta_aux_continuous :
    Continuous apm_t02a03_sector_aux_piDelta := by
  have hz : Continuous fun q : ℝ × ℝ => max (-3 / 20 : ℝ) (min (3 / 20) q.2) :=
    continuous_const.max (continuous_const.min continuous_snd)
  have hT := apm_t02a03_sector_aux_L5_aux_Theta_continuous.comp hz
  unfold apm_t02a03_sector_aux_piDelta
  exact (hT.neg.max (hT.min continuous_fst)).prodMk hz

/-- On `|z| ≤ 3/20` the arccos argument of `Theta` lies in `(0, 1]`. -/
lemma apm_t02a03_sector_aux_L5_aux_arg_le_one (z : ℝ) (hz : |z| ≤ 3 / 20) :
    6 / (5 * (1 + apm_t02a03_sector_aux_a z)) ≤ 1 := by
  have ha : (1 / 5 : ℝ) ≤ apm_t02a03_sector_aux_a z := by
    unfold apm_t02a03_sector_aux_a
    apply Real.le_sqrt_of_sq_le
    have : z ^ 2 ≤ (3 / 20) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg z) hz 2
    nlinarith
  rw [div_le_one (by positivity)]
  linarith

lemma apm_t02a03_sector_aux_L5_piDelta_aux_maps (q : ℝ × ℝ) :
    apm_t02a03_sector_aux_Delta (apm_t02a03_sector_aux_piDelta q) := by
  set z' := max (-3 / 20 : ℝ) (min (3 / 20) q.2) with hz'
  have hz'abs : |z'| ≤ 3 / 20 := by
    rw [abs_le]; constructor
    · have := le_max_left (-3 / 20 : ℝ) (min (3 / 20) q.2); linarith
    · exact max_le (by norm_num) (min_le_left _ _)
  set T := apm_t02a03_sector_aux_Theta z' with hT
  have hT0 : 0 ≤ T := Real.arccos_nonneg _
  have hTpi : T ≤ Real.pi := Real.arccos_le_pi _
  set θ' := max (-T) (min T q.1) with hθ'
  have hθ'abs : |θ'| ≤ T := by
    rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hpd : apm_t02a03_sector_aux_piDelta q = (θ', z') := rfl
  rw [hpd]
  refine ⟨hz'abs, ?_⟩
  have harg := apm_t02a03_sector_aux_L5_aux_arg_le_one z' hz'abs
  have harg0 : (-1 : ℝ) ≤ 6 / (5 * (1 + apm_t02a03_sector_aux_a z')) := by
    have := Real.sqrt_nonneg (1 / 16 - z' ^ 2)
    have : 0 ≤ 6 / (5 * (1 + apm_t02a03_sector_aux_a z')) := by
      unfold apm_t02a03_sector_aux_a; positivity
    linarith
  have hcosT : Real.cos T = 6 / (5 * (1 + apm_t02a03_sector_aux_a z')) :=
    Real.cos_arccos harg0 harg
  show 6 / (5 * (1 + apm_t02a03_sector_aux_a z')) ≤ Real.cos θ'
  rw [← hcosT, ← Real.cos_abs θ']
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hTpi hθ'abs

lemma apm_t02a03_sector_aux_L5_piDelta_aux_fix (q : ℝ × ℝ)
    (hq : q.1 ∈ Set.Icc (-apm_t02a03_sector_aux_thetaOne)
      apm_t02a03_sector_aux_thetaOne)
    (hDelta : apm_t02a03_sector_aux_Delta q) :
    apm_t02a03_sector_aux_piDelta q = q := by
  obtain ⟨θ, z⟩ := q
  obtain ⟨hz, hcos⟩ := hDelta
  simp only at hz hcos hq
  have hzc : max (-3 / 20 : ℝ) (min (3 / 20) z) = z := by
    rw [abs_le] at hz
    rw [min_eq_right hz.2, max_eq_right (by linarith [hz.1])]
  have hθpi : |θ| ≤ Real.pi := by
    rw [abs_le]; have := Real.arccos_le_pi (17 / 25 : ℝ)
    unfold apm_t02a03_sector_aux_thetaOne at hq
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hθT : |θ| ≤ apm_t02a03_sector_aux_Theta z := by
    unfold apm_t02a03_sector_aux_Theta
    rw [← Real.arccos_cos (abs_nonneg θ) hθpi, Real.cos_abs]
    exact Real.arccos_le_arccos hcos
  have hθc : max (-apm_t02a03_sector_aux_Theta z) (min (apm_t02a03_sector_aux_Theta z) θ) = θ := by
    rw [abs_le] at hθT
    rw [min_eq_right hθT.2, max_eq_right hθT.1]
  show (max (-apm_t02a03_sector_aux_Theta (max (-3 / 20) (min (3 / 20) z)))
      (min (apm_t02a03_sector_aux_Theta (max (-3 / 20) (min (3 / 20) z))) θ),
      max (-3 / 20) (min (3 / 20) z)) = (θ, z)
  rw [hzc, hθc]

theorem apm_t02a03_sector_aux_L5_piDelta :
    Continuous apm_t02a03_sector_aux_piDelta ∧
    (∀ q, apm_t02a03_sector_aux_Delta (apm_t02a03_sector_aux_piDelta q)) ∧
    (∀ q, q.1 ∈ Set.Icc (-apm_t02a03_sector_aux_thetaOne) apm_t02a03_sector_aux_thetaOne →
      apm_t02a03_sector_aux_Delta q → apm_t02a03_sector_aux_piDelta q = q) := by
  exact ⟨apm_t02a03_sector_aux_L5_piDelta_aux_continuous,
    apm_t02a03_sector_aux_L5_piDelta_aux_maps,
    apm_t02a03_sector_aux_L5_piDelta_aux_fix⟩

def apm_t02a03_sector_aux_q0 : ℝ × ℝ × ℝ := (0, 0, 1)

lemma apm_t02a03_sector_aux_L6c_r_fixes_target_aux_torus (q : ℝ × ℝ × ℝ)
    (hbox : apm_t02a03_sector_aux_box q)
    (hq : q.2.2 = 1 ∧ apm_t02a03_sector_aux_Delta (q.1, q.2.1)) :
    apm_t02a03_sector_aux_r q = q := by
  obtain ⟨θ, z, v⟩ := q
  obtain ⟨hv, hD⟩ := hq
  simp only at hv hD
  subst hv
  have hfix : apm_t02a03_sector_aux_piDelta (θ, z) = (θ, z) :=
    apm_t02a03_sector_aux_L5_piDelta_aux_fix (θ, z) hbox.1 hD
  have hdD : apm_t02a03_sector_aux_deltaD (θ, z, 1) = 0 := by
    simp [apm_t02a03_sector_aux_deltaD, hfix]
  by_cases harc : apm_t02a03_sector_aux_deltaArc (θ, z, 1) = 0
  · -- on the arc as well: z = 0 and vArc θ = 1; λ = 0/0 = 0
    have hl : apm_t02a03_sector_aux_lambda (θ, z, 1) = 0 := by
      simp [apm_t02a03_sector_aux_lambda, harc, hdD]
    have hz : z = 0 ∧ 1 = apm_t02a03_sector_aux_vArc θ := by
      simp only [apm_t02a03_sector_aux_deltaArc] at harc
      have h1 := abs_nonneg z
      have h2 := abs_nonneg (1 - apm_t02a03_sector_aux_vArc θ)
      constructor
      · exact abs_eq_zero.mp (by linarith)
      · have : |1 - apm_t02a03_sector_aux_vArc θ| = 0 := by linarith
        linarith [abs_eq_zero.mp this]
    obtain ⟨rfl, hva⟩ := hz
    simp only [apm_t02a03_sector_aux_r, hl]
    norm_num [← hva]
  · have hl : apm_t02a03_sector_aux_lambda (θ, z, 1) = 1 := by
      simp [apm_t02a03_sector_aux_lambda, hdD, harc]
    simp only [apm_t02a03_sector_aux_r, hl]
    norm_num [hfix]

lemma apm_t02a03_sector_aux_L6c_r_fixes_target_aux_arc (q : ℝ × ℝ × ℝ)
    (hbox : apm_t02a03_sector_aux_box q)
    (hq : q.2.1 = 0 ∧ q.2.2 = apm_t02a03_sector_aux_vArc q.1) :
    apm_t02a03_sector_aux_r q = q := by
  obtain ⟨θ, z, v⟩ := q
  obtain ⟨hz, hv⟩ := hq
  simp only at hz hv
  subst hz; subst hv
  have harc : apm_t02a03_sector_aux_deltaArc (θ, 0, apm_t02a03_sector_aux_vArc θ) = 0 := by
    simp [apm_t02a03_sector_aux_deltaArc]
  have hl : apm_t02a03_sector_aux_lambda (θ, 0, apm_t02a03_sector_aux_vArc θ) = 0 := by
    simp [apm_t02a03_sector_aux_lambda, harc]
  simp only [apm_t02a03_sector_aux_r, hl]
  norm_num

theorem apm_t02a03_sector_aux_L6c_r_fixes_target (q : ℝ × ℝ × ℝ)
    (hbox : apm_t02a03_sector_aux_box q)
    (hq : (q.2.2 = 1 ∧ apm_t02a03_sector_aux_Delta (q.1, q.2.1)) ∨
      (q.2.1 = 0 ∧ q.2.2 = apm_t02a03_sector_aux_vArc q.1)) :
    apm_t02a03_sector_aux_r q = q := by
  rcases hq with hq | hq
  · exact apm_t02a03_sector_aux_L6c_r_fixes_target_aux_torus q hbox hq
  · exact apm_t02a03_sector_aux_L6c_r_fixes_target_aux_arc q hbox hq

lemma apm_t02a03_sector_aux_L6e_aux_a_le (z : ℝ) : apm_t02a03_sector_aux_a z ≤ 1 / 4 := by
  unfold apm_t02a03_sector_aux_a
  rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg z])

lemma apm_t02a03_sector_aux_L6e_aux_Theta_le (z : ℝ) :
    apm_t02a03_sector_aux_Theta z ≤ apm_t02a03_sector_aux_thetaOne := by
  unfold apm_t02a03_sector_aux_Theta apm_t02a03_sector_aux_thetaOne
  apply Real.arccos_le_arccos
  have ha := apm_t02a03_sector_aux_L6e_aux_a_le z
  have ha0 : 0 ≤ apm_t02a03_sector_aux_a z := Real.sqrt_nonneg _
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma apm_t02a03_sector_aux_L6e_aux_piDelta_bounds (q : ℝ × ℝ) :
    |(apm_t02a03_sector_aux_piDelta q).1| ≤ apm_t02a03_sector_aux_thetaOne ∧
      |(apm_t02a03_sector_aux_piDelta q).2| ≤ 3 / 20 := by
  have hT0 : 0 ≤ apm_t02a03_sector_aux_Theta (max (-3 / 20) (min (3 / 20) q.2)) :=
    Real.arccos_nonneg _
  have hT1 := apm_t02a03_sector_aux_L6e_aux_Theta_le (max (-3 / 20) (min (3 / 20) q.2))
  constructor
  · show |max (-apm_t02a03_sector_aux_Theta (max (-3 / 20) (min (3 / 20) q.2)))
        (min (apm_t02a03_sector_aux_Theta (max (-3 / 20) (min (3 / 20) q.2))) q.1)| ≤ _
    rw [abs_le]; constructor
    · have := le_max_left (-apm_t02a03_sector_aux_Theta (max (-3 / 20) (min (3 / 20) q.2)))
        (min (apm_t02a03_sector_aux_Theta (max (-3 / 20) (min (3 / 20) q.2))) q.1)
      linarith
    · exact max_le (by linarith) ((min_le_left _ _).trans hT1)
  · show |max (-3 / 20 : ℝ) (min (3 / 20) q.2)| ≤ 3 / 20
    rw [abs_le]; constructor
    · have := le_max_left (-3 / 20 : ℝ) (min (3 / 20) q.2); linarith
    · exact max_le (by norm_num) (min_le_left _ _)

lemma apm_t02a03_sector_aux_L6e_aux_lambda_mem (q : ℝ × ℝ × ℝ) (hv : q.2.2 ≤ 1) :
    apm_t02a03_sector_aux_lambda q ∈ Set.Icc (0 : ℝ) 1 := by
  have ha : 0 ≤ apm_t02a03_sector_aux_deltaArc q := by
    unfold apm_t02a03_sector_aux_deltaArc; positivity
  have hd : 0 ≤ apm_t02a03_sector_aux_deltaD q := by
    unfold apm_t02a03_sector_aux_deltaD
    have := dist_nonneg (x := (q.1, q.2.1))
      (y := apm_t02a03_sector_aux_piDelta (q.1, q.2.1))
    linarith
  unfold apm_t02a03_sector_aux_lambda
  rcases eq_or_lt_of_le (add_nonneg ha hd) with h | h
  · rw [← h, div_zero]; exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨div_nonneg ha h.le, (div_le_one h).mpr (by linarith)⟩

/-- On the arc's base angle the bite boundary is at least `3/20` out:
squaring reduces `b θ 0 ≥ 3/20` to `cos θ ≤ 1`. -/
lemma apm_t02a03_sector_aux_L6e_aux_c_ge (θ : ℝ) :
    (3 / 20 : ℝ) ≤ apm_t02a03_sector_aux_c θ 0 := by
  have ha0 : apm_t02a03_sector_aux_a 0 = 1 / 4 := by
    unfold apm_t02a03_sector_aux_a
    rw [show (1 / 16 - (0 : ℝ) ^ 2) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold apm_t02a03_sector_aux_c
  split_ifs with hD
  · obtain ⟨_, hcos⟩ := hD
    simp only [ha0] at hcos
    have hc : (24 / 25 : ℝ) ≤ Real.cos θ := by
      have : (6 : ℝ) / (5 * (1 + 1 / 4)) = 24 / 25 := by norm_num
      linarith
    unfold apm_t02a03_sector_aux_b
    rw [ha0]
    have hY : 0 ≤ (12 / 5) * Real.cos θ - 23 / 20 := by linarith
    have hsq : Real.sqrt ((1 + 1 / 4) ^ 2 - (144 / 25) * Real.sin θ ^ 2) ≤
        (12 / 5) * Real.cos θ - 23 / 20 := by
      rw [Real.sqrt_le_left hY]
      nlinarith [Real.sin_sq_add_cos_sq θ, Real.cos_le_one θ]
    linarith
  · rw [ha0]; norm_num

lemma apm_t02a03_sector_aux_L6e_aux_vArc_mem (θ : ℝ) :
    apm_t02a03_sector_aux_vArc θ ∈ Set.Icc (0 : ℝ) 1 := by
  have hc := apm_t02a03_sector_aux_L6e_aux_c_ge θ
  unfold apm_t02a03_sector_aux_vArc
  refine ⟨div_nonneg (by norm_num) (by linarith), (div_le_one (by linarith)).mpr (by linarith)⟩

lemma apm_t02a03_sector_aux_L6e_r_box_aux_theta (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    (apm_t02a03_sector_aux_r q).1 ∈
      Set.Icc (-apm_t02a03_sector_aux_thetaOne) apm_t02a03_sector_aux_thetaOne := by
  have hl := apm_t02a03_sector_aux_L6e_aux_lambda_mem q hq.2.2.2
  unfold apm_t02a03_sector_aux_r
  simp only
  split_ifs with h
  · have hθ := hq.1
    have h0 : 0 ≤ 1 - 2 * apm_t02a03_sector_aux_lambda q := by linarith [hl.1]
    have h1 : 1 - 2 * apm_t02a03_sector_aux_lambda q ≤ 1 := by linarith [hl.1]
    rw [Set.mem_Icc] at hθ ⊢
    have hθ1 : 0 ≤ apm_t02a03_sector_aux_thetaOne := Real.arccos_nonneg _
    constructor <;> nlinarith
  · have := (apm_t02a03_sector_aux_L6e_aux_piDelta_bounds
      ((2 * apm_t02a03_sector_aux_lambda q - 1) * q.1,
        (2 * apm_t02a03_sector_aux_lambda q - 1) * q.2.1)).1
    exact abs_le.mp this

lemma apm_t02a03_sector_aux_L6e_r_box_aux_z (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    (apm_t02a03_sector_aux_r q).2.1 ∈ Set.Icc (-1 / 5) (1 / 5) := by
  unfold apm_t02a03_sector_aux_r
  simp only
  split_ifs with h
  · norm_num
  · have := abs_le.mp (apm_t02a03_sector_aux_L6e_aux_piDelta_bounds
      ((2 * apm_t02a03_sector_aux_lambda q - 1) * q.1,
        (2 * apm_t02a03_sector_aux_lambda q - 1) * q.2.1)).2
    exact ⟨by linarith [this.1], by linarith [this.2]⟩

lemma apm_t02a03_sector_aux_L6e_r_box_aux_v (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    (apm_t02a03_sector_aux_r q).2.2 ∈ Set.Icc 0 1 := by
  unfold apm_t02a03_sector_aux_r
  simp only
  split_ifs with h
  · exact apm_t02a03_sector_aux_L6e_aux_vArc_mem _
  · exact ⟨zero_le_one, le_rfl⟩

theorem apm_t02a03_sector_aux_L6e_r_box (q : ℝ × ℝ × ℝ)
    (hq : apm_t02a03_sector_aux_box q) :
    apm_t02a03_sector_aux_box (apm_t02a03_sector_aux_r q) := by
  exact ⟨apm_t02a03_sector_aux_L6e_r_box_aux_theta q hq,
    apm_t02a03_sector_aux_L6e_r_box_aux_z q hq,
    apm_t02a03_sector_aux_L6e_r_box_aux_v q hq⟩

theorem apm_t02a03_sector_aux_L6d_r_lands_target (q : ℝ × ℝ × ℝ) :
    let rq := apm_t02a03_sector_aux_r q
    (rq.2.2 = 1 ∧ apm_t02a03_sector_aux_Delta (rq.1, rq.2.1)) ∨
      (rq.2.1 = 0 ∧ rq.2.2 = apm_t02a03_sector_aux_vArc rq.1) := by
  dsimp
  simp only [apm_t02a03_sector_aux_r]
  split_ifs with h
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl,
      apm_t02a03_sector_aux_L5_piDelta.2.1
        ((2 * apm_t02a03_sector_aux_lambda q - 1) * q.1,
          (2 * apm_t02a03_sector_aux_lambda q - 1) * q.2.1)⟩

lemma apm_t02a03_sector_aux_L6_aux_a_zero : apm_t02a03_sector_aux_a 0 = 1 / 4 := by
  unfold apm_t02a03_sector_aux_a
  rw [show (1 / 16 - (0 : ℝ) ^ 2) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma apm_t02a03_sector_aux_L6_aux_cos_of_abs_le (x : ℝ)
    (hx : |x| ≤ apm_t02a03_sector_aux_thetaOne) : (17 / 25 : ℝ) ≤ Real.cos x := by
  rw [← Real.cos_abs]
  have hpi : apm_t02a03_sector_aux_thetaOne ≤ Real.pi := Real.arccos_le_pi _
  calc (17 / 25 : ℝ) = Real.cos apm_t02a03_sector_aux_thetaOne := by
        unfold apm_t02a03_sector_aux_thetaOne; rw [Real.cos_arccos (by norm_num) (by norm_num)]
    _ ≤ Real.cos |x| := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hpi hx

/-- A globally continuous stand-in for `vArc` that agrees with it on the box angles. -/
noncomputable def apm_t02a03_sector_aux_L6_aux_V (θ : ℝ) : ℝ :=
  (2 / 5) / (max (3 / 20) (min (apm_t02a03_sector_aux_a 0) (apm_t02a03_sector_aux_b θ 0)) + 1 / 4)

lemma apm_t02a03_sector_aux_L6_aux_V_continuous : Continuous apm_t02a03_sector_aux_L6_aux_V := by
  have hm : Continuous fun θ : ℝ =>
      min (apm_t02a03_sector_aux_a 0) (apm_t02a03_sector_aux_b θ 0) :=
    apm_t02a03_sector_aux_L1_aux_minab_continuous.comp (continuous_id.prodMk continuous_const)
  unfold apm_t02a03_sector_aux_L6_aux_V
  exact continuous_const.div (continuous_const.max hm |>.add continuous_const) (fun θ => by
    have := le_max_left (3 / 20 : ℝ) (min (apm_t02a03_sector_aux_a 0) (apm_t02a03_sector_aux_b θ 0))
    linarith)

lemma apm_t02a03_sector_aux_L6_aux_vArc_eq_V (θ : ℝ) (hθ : (17 / 25 : ℝ) ≤ Real.cos θ) :
    apm_t02a03_sector_aux_vArc θ = apm_t02a03_sector_aux_L6_aux_V θ := by
  have hc := apm_t02a03_sector_aux_L1_aux_c_eq_min θ 0 (by norm_num) hθ
  have hge := apm_t02a03_sector_aux_L6e_aux_c_ge θ
  unfold apm_t02a03_sector_aux_vArc apm_t02a03_sector_aux_L6_aux_V
  rw [← hc, max_eq_right hge]

lemma apm_t02a03_sector_aux_L6_aux_vArc_zero : apm_t02a03_sector_aux_vArc 0 = 1 := by
  have hD : apm_t02a03_sector_aux_Delta (0, 0) := by
    refine ⟨by norm_num, ?_⟩
    simp only [apm_t02a03_sector_aux_L6_aux_a_zero, Real.cos_zero]; norm_num
  have hb : apm_t02a03_sector_aux_b 0 0 = 3 / 20 := by
    unfold apm_t02a03_sector_aux_b
    rw [apm_t02a03_sector_aux_L6_aux_a_zero, Real.sin_zero, Real.cos_zero,
      show ((1 : ℝ) + 1 / 4) ^ 2 - 144 / 25 * 0 ^ 2 = (5 / 4) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    norm_num
  unfold apm_t02a03_sector_aux_vArc apm_t02a03_sector_aux_c
  rw [if_pos hD, hb]; norm_num

lemma apm_t02a03_sector_aux_L6_aux_piDelta_zero :
    apm_t02a03_sector_aux_piDelta (0, 0) = (0, 0) := by
  have hT := Real.arccos_nonneg (6 / (5 * (1 + apm_t02a03_sector_aux_a
    (max (-3 / 20) (min (3 / 20) 0)))))
  show (max (-apm_t02a03_sector_aux_Theta (max (-3 / 20) (min (3 / 20) 0)))
      (min (apm_t02a03_sector_aux_Theta (max (-3 / 20) (min (3 / 20) 0))) 0),
      max (-3 / 20) (min (3 / 20) (0 : ℝ))) = (0, 0)
  have hz : max (-3 / 20 : ℝ) (min (3 / 20) 0) = 0 := by norm_num
  rw [hz]
  have hT0 : 0 ≤ apm_t02a03_sector_aux_Theta 0 := Real.arccos_nonneg _
  rw [min_eq_right hT0, max_eq_right (by linarith)]

lemma apm_t02a03_sector_aux_L6_aux_piDelta_fst_abs (q : ℝ × ℝ) :
    |(apm_t02a03_sector_aux_piDelta q).1| ≤ |q.1| := by
  have hT : 0 ≤ apm_t02a03_sector_aux_Theta (max (-3 / 20) (min (3 / 20) q.2)) :=
    Real.arccos_nonneg _
  show |max (-apm_t02a03_sector_aux_Theta (max (-3 / 20) (min (3 / 20) q.2)))
      (min (apm_t02a03_sector_aux_Theta (max (-3 / 20) (min (3 / 20) q.2))) q.1)| ≤ |q.1|
  rw [abs_le]
  constructor
  · have h1 := neg_abs_le q.1
    have h2 : -|q.1| ≤ min (apm_t02a03_sector_aux_Theta (max (-3 / 20) (min (3 / 20) q.2))) q.1 :=
      le_min (by linarith [abs_nonneg q.1]) h1
    exact h2.trans (le_max_right _ _)
  · exact max_le (by linarith [abs_nonneg q.1]) ((min_le_right _ _).trans (le_abs_self _))

lemma apm_t02a03_sector_aux_L6_aux_piDelta_snd_abs (q : ℝ × ℝ) :
    |(apm_t02a03_sector_aux_piDelta q).2| ≤ |q.2| := by
  show |max (-3 / 20 : ℝ) (min (3 / 20) q.2)| ≤ |q.2|
  rw [abs_le]
  constructor
  · have h1 := neg_abs_le q.2
    exact (le_min (by linarith [abs_nonneg q.2]) h1).trans (le_max_right _ _)
  · exact max_le (by linarith [abs_nonneg q.2]) ((min_le_right _ _).trans (le_abs_self _))

/-- `r` without the branch on `λ`: the two branches agree at `λ = 1/2`. -/
lemma apm_t02a03_sector_aux_L6_aux_r_eq (q : ℝ × ℝ × ℝ) :
    apm_t02a03_sector_aux_r q =
      ((apm_t02a03_sector_aux_piDelta
          (max 0 (2 * apm_t02a03_sector_aux_lambda q - 1) * q.1,
            max 0 (2 * apm_t02a03_sector_aux_lambda q - 1) * q.2.1)).1 +
          max 0 (1 - 2 * apm_t02a03_sector_aux_lambda q) * q.1,
        (apm_t02a03_sector_aux_piDelta
          (max 0 (2 * apm_t02a03_sector_aux_lambda q - 1) * q.1,
            max 0 (2 * apm_t02a03_sector_aux_lambda q - 1) * q.2.1)).2,
        apm_t02a03_sector_aux_vArc (max 0 (1 - 2 * apm_t02a03_sector_aux_lambda q) * q.1)) := by
  unfold apm_t02a03_sector_aux_r
  simp only
  split_ifs with h
  · rw [max_eq_left (by linarith : 2 * apm_t02a03_sector_aux_lambda q - 1 ≤ 0),
      max_eq_right (by linarith : (0 : ℝ) ≤ 1 - 2 * apm_t02a03_sector_aux_lambda q),
      zero_mul, zero_mul, apm_t02a03_sector_aux_L6_aux_piDelta_zero]
    simp
  · push_neg at h
    rw [max_eq_right (by linarith : (0 : ℝ) ≤ 2 * apm_t02a03_sector_aux_lambda q - 1),
      max_eq_left (by linarith : 1 - 2 * apm_t02a03_sector_aux_lambda q ≤ 0),
      zero_mul, add_zero, apm_t02a03_sector_aux_L6_aux_vArc_zero]

lemma apm_t02a03_sector_aux_L6_aux_vArc_r (q : ℝ × ℝ × ℝ) (hq : apm_t02a03_sector_aux_box q) :
    apm_t02a03_sector_aux_vArc (max 0 (1 - 2 * apm_t02a03_sector_aux_lambda q) * q.1) =
      apm_t02a03_sector_aux_L6_aux_V (max 0 (1 - 2 * apm_t02a03_sector_aux_lambda q) * q.1) := by
  have hl := apm_t02a03_sector_aux_L6e_aux_lambda_mem q hq.2.2.2
  apply apm_t02a03_sector_aux_L6_aux_vArc_eq_V
  apply apm_t02a03_sector_aux_L6_aux_cos_of_abs_le
  have hm0 : 0 ≤ max 0 (1 - 2 * apm_t02a03_sector_aux_lambda q) := le_max_left _ _
  have hm1 : max 0 (1 - 2 * apm_t02a03_sector_aux_lambda q) ≤ 1 :=
    max_le (by norm_num) (by linarith [hl.1])
  have hθ : |q.1| ≤ apm_t02a03_sector_aux_thetaOne := abs_le.mpr ⟨hq.1.1, hq.1.2⟩
  rw [abs_mul, abs_of_nonneg hm0]
  nlinarith [abs_nonneg q.1]

/-- On the box the denominator of `λ` vanishes only at `q0`: there the arc
point is `(θ, 0, 1)` with `(θ, 0) ∈ Δ`, and `vArc θ = 1` forces `b θ 0 = 3/20`,
which after squaring is `cos θ = 1`. -/
lemma apm_t02a03_sector_aux_L6_aux_denom_ne (q : ℝ × ℝ × ℝ) (hq : apm_t02a03_sector_aux_box q)
    (hq0 : q ≠ apm_t02a03_sector_aux_q0) :
    apm_t02a03_sector_aux_deltaArc q + apm_t02a03_sector_aux_deltaD q ≠ 0 := by
  obtain ⟨θ, z, v⟩ := q
  intro h0
  have ha : 0 ≤ |z| := abs_nonneg _
  have hb : 0 ≤ |v - apm_t02a03_sector_aux_vArc θ| := abs_nonneg _
  have hdist := dist_nonneg (x := (θ, z)) (y := apm_t02a03_sector_aux_piDelta (θ, z))
  have hv1 : v ≤ 1 := hq.2.2.2
  unfold apm_t02a03_sector_aux_deltaArc apm_t02a03_sector_aux_deltaD at h0
  simp only at h0
  have hz : |z| = 0 := by linarith
  have hvA : |v - apm_t02a03_sector_aux_vArc θ| = 0 := by linarith
  have hv : v = 1 := by linarith
  have hd : dist (θ, z) (apm_t02a03_sector_aux_piDelta (θ, z)) = 0 := by linarith
  have hz0 : z = 0 := abs_eq_zero.mp hz
  subst hz0 hv
  have hfix : apm_t02a03_sector_aux_piDelta (θ, 0) = (θ, 0) := (dist_eq_zero.mp hd).symm
  have hD : apm_t02a03_sector_aux_Delta (θ, 0) := by
    have := apm_t02a03_sector_aux_L5_piDelta_aux_maps (θ, 0)
    rwa [hfix] at this
  have hvarc : apm_t02a03_sector_aux_vArc θ = 1 := by
    have := abs_eq_zero.mp hvA; linarith
  have hcpos := apm_t02a03_sector_aux_L6e_aux_c_ge θ
  have hc : apm_t02a03_sector_aux_c θ 0 = 3 / 20 := by
    unfold apm_t02a03_sector_aux_vArc at hvarc
    rw [div_eq_one_iff_eq (by linarith)] at hvarc
    linarith
  unfold apm_t02a03_sector_aux_c at hc
  rw [if_pos hD] at hc
  obtain ⟨-, hcos⟩ := hD
  simp only [apm_t02a03_sector_aux_L6_aux_a_zero] at hcos
  have hc24 : (24 / 25 : ℝ) ≤ Real.cos θ := by
    have : (6 : ℝ) / (5 * (1 + 1 / 4)) = 24 / 25 := by norm_num
    linarith
  unfold apm_t02a03_sector_aux_b at hc
  rw [apm_t02a03_sector_aux_L6_aux_a_zero] at hc
  have htrig := Real.sin_sq_add_cos_sq θ
  have hR : 0 ≤ (1 + 1 / 4 : ℝ) ^ 2 - 144 / 25 * Real.sin θ ^ 2 := by
    nlinarith [Real.cos_le_one θ]
  have hsq := Real.sq_sqrt hR
  have hX : Real.sqrt ((1 + 1 / 4 : ℝ) ^ 2 - 144 / 25 * Real.sin θ ^ 2) =
      12 / 5 * Real.cos θ - 23 / 20 := by linarith
  rw [hX] at hsq
  have hcos1 : Real.cos θ = 1 := by linear_combination (-(25 : ℝ) / 138) * hsq + ((144 : ℝ) / 138) * htrig
  have hθpi : |θ| ≤ Real.pi := by
    have := Real.arccos_le_pi (17 / 25 : ℝ)
    have h1 := hq.1
    unfold apm_t02a03_sector_aux_thetaOne at h1
    exact abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hθ0 : θ = 0 := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [abs_le.mp hθpi, Real.pi_pos])
    (by linarith [abs_le.mp hθpi, Real.pi_pos])).mp hcos1
  exact hq0 (by rw [hθ0]; rfl)

lemma apm_t02a03_sector_aux_L6a_r_continuous_off_q0_aux_lambda :
    ContinuousOn apm_t02a03_sector_aux_lambda
      ({q | apm_t02a03_sector_aux_box q} \ {apm_t02a03_sector_aux_q0}) := by
  have hArc : ContinuousOn apm_t02a03_sector_aux_deltaArc
      ({q | apm_t02a03_sector_aux_box q} \ {apm_t02a03_sector_aux_q0}) := by
    have hc : Continuous fun q : ℝ × ℝ × ℝ =>
        |q.2.1| + |q.2.2 - apm_t02a03_sector_aux_L6_aux_V q.1| :=
      (continuous_snd.fst.abs).add ((continuous_snd.snd.sub
        (apm_t02a03_sector_aux_L6_aux_V_continuous.comp continuous_fst)).abs)
    refine hc.continuousOn.congr (fun q hq => ?_)
    unfold apm_t02a03_sector_aux_deltaArc
    rw [apm_t02a03_sector_aux_L6_aux_vArc_eq_V q.1
      (apm_t02a03_sector_aux_L1_aux_cos_box q hq.1)]
  have hD : Continuous apm_t02a03_sector_aux_deltaD := by
    unfold apm_t02a03_sector_aux_deltaD
    exact (continuous_const.sub continuous_snd.snd).add
      ((continuous_fst.prodMk continuous_snd.fst).dist
        (apm_t02a03_sector_aux_L5_piDelta_aux_continuous.comp
          (continuous_fst.prodMk continuous_snd.fst)))
  unfold apm_t02a03_sector_aux_lambda
  exact hArc.div (hArc.add hD.continuousOn) (fun q hq =>
    apm_t02a03_sector_aux_L6_aux_denom_ne q hq.1 hq.2)

lemma apm_t02a03_sector_aux_L6a_r_continuous_off_q0_aux_theta_aux :
    ContinuousOn (fun q : ℝ × ℝ × ℝ => (apm_t02a03_sector_aux_r q).1)
      ({q | apm_t02a03_sector_aux_box q} \ {apm_t02a03_sector_aux_q0}) := by
  have hl := apm_t02a03_sector_aux_L6a_r_continuous_off_q0_aux_lambda
  have hp : ContinuousOn (fun q : ℝ × ℝ × ℝ => max 0 (2 * apm_t02a03_sector_aux_lambda q - 1))
      ({q | apm_t02a03_sector_aux_box q} \ {apm_t02a03_sector_aux_q0}) :=
    (continuous_const.max continuous_id : Continuous fun x : ℝ => max 0 x).comp_continuousOn ((continuousOn_const.mul hl).sub continuousOn_const)
  have hm : ContinuousOn (fun q : ℝ × ℝ × ℝ => max 0 (1 - 2 * apm_t02a03_sector_aux_lambda q))
      ({q | apm_t02a03_sector_aux_box q} \ {apm_t02a03_sector_aux_q0}) :=
    (continuous_const.max continuous_id : Continuous fun x : ℝ => max 0 x).comp_continuousOn (continuousOn_const.sub (continuousOn_const.mul hl))
  simp_rw [apm_t02a03_sector_aux_L6_aux_r_eq]
  exact (continuous_fst.comp_continuousOn (apm_t02a03_sector_aux_L5_piDelta_aux_continuous.comp_continuousOn
    ((hp.mul continuous_fst.continuousOn).prodMk (hp.mul continuous_snd.fst.continuousOn)))).add
    (hm.mul continuous_fst.continuousOn)

lemma apm_t02a03_sector_aux_L6a_r_continuous_off_q0_aux_theta :
    ContinuousOn (fun q : ℝ × ℝ × ℝ => (apm_t02a03_sector_aux_r q).1)
      ({q | apm_t02a03_sector_aux_box q} \ {apm_t02a03_sector_aux_q0}) := by
  exact apm_t02a03_sector_aux_L6a_r_continuous_off_q0_aux_theta_aux

lemma apm_t02a03_sector_aux_L6a_r_continuous_off_q0_aux_z_aux :
    ContinuousOn (fun q : ℝ × ℝ × ℝ => (apm_t02a03_sector_aux_r q).2.1)
      ({q | apm_t02a03_sector_aux_box q} \ {apm_t02a03_sector_aux_q0}) := by
  have hl := apm_t02a03_sector_aux_L6a_r_continuous_off_q0_aux_lambda
  have hp : ContinuousOn (fun q : ℝ × ℝ × ℝ => max 0 (2 * apm_t02a03_sector_aux_lambda q - 1))
      ({q | apm_t02a03_sector_aux_box q} \ {apm_t02a03_sector_aux_q0}) :=
    (continuous_const.max continuous_id : Continuous fun x : ℝ => max 0 x).comp_continuousOn ((continuousOn_const.mul hl).sub continuousOn_const)
  simp_rw [apm_t02a03_sector_aux_L6_aux_r_eq]
  exact continuous_snd.comp_continuousOn (apm_t02a03_sector_aux_L5_piDelta_aux_continuous.comp_continuousOn
    ((hp.mul continuous_fst.continuousOn).prodMk (hp.mul continuous_snd.fst.continuousOn)))

lemma apm_t02a03_sector_aux_L6a_r_continuous_off_q0_aux_z :
    ContinuousOn (fun q : ℝ × ℝ × ℝ => (apm_t02a03_sector_aux_r q).2.1)
      ({q | apm_t02a03_sector_aux_box q} \ {apm_t02a03_sector_aux_q0}) := by
  exact apm_t02a03_sector_aux_L6a_r_continuous_off_q0_aux_z_aux

lemma apm_t02a03_sector_aux_L6a_r_continuous_off_q0_aux_v_aux :
    ContinuousOn (fun q : ℝ × ℝ × ℝ => (apm_t02a03_sector_aux_r q).2.2)
      ({q | apm_t02a03_sector_aux_box q} \ {apm_t02a03_sector_aux_q0}) := by
  have hl := apm_t02a03_sector_aux_L6a_r_continuous_off_q0_aux_lambda
  have hm : ContinuousOn (fun q : ℝ × ℝ × ℝ => max 0 (1 - 2 * apm_t02a03_sector_aux_lambda q))
      ({q | apm_t02a03_sector_aux_box q} \ {apm_t02a03_sector_aux_q0}) :=
    (continuous_const.max continuous_id : Continuous fun x : ℝ => max 0 x).comp_continuousOn (continuousOn_const.sub (continuousOn_const.mul hl))
  refine (apm_t02a03_sector_aux_L6_aux_V_continuous.comp_continuousOn
    (hm.mul continuous_fst.continuousOn)).congr (fun q hq => ?_)
  rw [apm_t02a03_sector_aux_L6_aux_r_eq]
  exact apm_t02a03_sector_aux_L6_aux_vArc_r q hq.1

lemma apm_t02a03_sector_aux_L6a_r_continuous_off_q0_aux_v :
    ContinuousOn (fun q : ℝ × ℝ × ℝ => (apm_t02a03_sector_aux_r q).2.2)
      ({q | apm_t02a03_sector_aux_box q} \ {apm_t02a03_sector_aux_q0}) := by
  exact apm_t02a03_sector_aux_L6a_r_continuous_off_q0_aux_v_aux

theorem apm_t02a03_sector_aux_L6a_r_continuous_off_q0 :
    ContinuousOn apm_t02a03_sector_aux_r
      ({q | apm_t02a03_sector_aux_box q} \ {apm_t02a03_sector_aux_q0}) := by
  exact apm_t02a03_sector_aux_L6a_r_continuous_off_q0_aux_theta.prodMk
    (apm_t02a03_sector_aux_L6a_r_continuous_off_q0_aux_z.prodMk
      apm_t02a03_sector_aux_L6a_r_continuous_off_q0_aux_v)

lemma apm_t02a03_sector_aux_L6_aux_r_q0 :
    apm_t02a03_sector_aux_r apm_t02a03_sector_aux_q0 = apm_t02a03_sector_aux_q0 := by
  have hl : apm_t02a03_sector_aux_lambda apm_t02a03_sector_aux_q0 = 0 := by
    have harc : apm_t02a03_sector_aux_deltaArc apm_t02a03_sector_aux_q0 = 0 := by
      show |(0 : ℝ)| + |1 - apm_t02a03_sector_aux_vArc 0| = 0
      rw [apm_t02a03_sector_aux_L6_aux_vArc_zero]; norm_num
    unfold apm_t02a03_sector_aux_lambda
    rw [harc, zero_div]
  unfold apm_t02a03_sector_aux_r
  rw [hl]
  simp [apm_t02a03_sector_aux_q0, apm_t02a03_sector_aux_L6_aux_vArc_zero]

/-- Within the box `λ ∈ [0,1]`, so both weights `max 0 (±(2λ-1))` lie in
`[0,1]` and every coordinate of `r` is squeezed by `|θ|`, `|z|`. -/
lemma apm_t02a03_sector_aux_L6_aux_weights (q : ℝ × ℝ × ℝ) (hq : apm_t02a03_sector_aux_box q) :
    0 ≤ max 0 (2 * apm_t02a03_sector_aux_lambda q - 1) ∧
      max 0 (2 * apm_t02a03_sector_aux_lambda q - 1) ≤ 1 ∧
      0 ≤ max 0 (1 - 2 * apm_t02a03_sector_aux_lambda q) ∧
      max 0 (1 - 2 * apm_t02a03_sector_aux_lambda q) ≤ 1 := by
  have hl := apm_t02a03_sector_aux_L6e_aux_lambda_mem q hq.2.2.2
  exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith [hl.2]),
    le_max_left _ _, max_le (by norm_num) (by linarith [hl.1])⟩

lemma apm_t02a03_sector_aux_L6b_r_continuous_at_q0_aux_theta_aux :
    ContinuousWithinAt (fun q : ℝ × ℝ × ℝ => (apm_t02a03_sector_aux_r q).1)
      {q | apm_t02a03_sector_aux_box q} apm_t02a03_sector_aux_q0 := by
  show Filter.Tendsto _ _ (nhds (apm_t02a03_sector_aux_r apm_t02a03_sector_aux_q0).1)
  rw [apm_t02a03_sector_aux_L6_aux_r_q0]
  have hlim : Filter.Tendsto (fun q : ℝ × ℝ × ℝ => 2 * |q.1|)
      (nhdsWithin apm_t02a03_sector_aux_q0 {q | apm_t02a03_sector_aux_box q}) (nhds 0) := by
    exact ((continuous_const.mul continuous_fst.abs :
      Continuous fun q : ℝ × ℝ × ℝ => 2 * |q.1|).tendsto' apm_t02a03_sector_aux_q0 0
        (by simp [apm_t02a03_sector_aux_q0])).mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with q hq
  obtain ⟨hp0, hp1, hm0, hm1⟩ := apm_t02a03_sector_aux_L6_aux_weights q hq
  rw [apm_t02a03_sector_aux_L6_aux_r_eq, Real.norm_eq_abs]
  have h1 := apm_t02a03_sector_aux_L6_aux_piDelta_fst_abs
    (max 0 (2 * apm_t02a03_sector_aux_lambda q - 1) * q.1,
      max 0 (2 * apm_t02a03_sector_aux_lambda q - 1) * q.2.1)
  simp only [abs_mul, abs_of_nonneg hp0] at h1
  calc _ ≤ |(apm_t02a03_sector_aux_piDelta
          (max 0 (2 * apm_t02a03_sector_aux_lambda q - 1) * q.1,
            max 0 (2 * apm_t02a03_sector_aux_lambda q - 1) * q.2.1)).1| +
        |max 0 (1 - 2 * apm_t02a03_sector_aux_lambda q) * q.1| := abs_add_le _ _
    _ ≤ 2 * |q.1| := by
        rw [abs_mul, abs_of_nonneg hm0]
        nlinarith [abs_nonneg q.1]

lemma apm_t02a03_sector_aux_L6b_r_continuous_at_q0_aux_theta :
    ContinuousWithinAt (fun q : ℝ × ℝ × ℝ => (apm_t02a03_sector_aux_r q).1)
      {q | apm_t02a03_sector_aux_box q} apm_t02a03_sector_aux_q0 := by
  exact apm_t02a03_sector_aux_L6b_r_continuous_at_q0_aux_theta_aux

lemma apm_t02a03_sector_aux_L6b_r_continuous_at_q0_aux_z_aux :
    ContinuousWithinAt (fun q : ℝ × ℝ × ℝ => (apm_t02a03_sector_aux_r q).2.1)
      {q | apm_t02a03_sector_aux_box q} apm_t02a03_sector_aux_q0 := by
  show Filter.Tendsto _ _ (nhds (apm_t02a03_sector_aux_r apm_t02a03_sector_aux_q0).2.1)
  rw [apm_t02a03_sector_aux_L6_aux_r_q0]
  have hlim : Filter.Tendsto (fun q : ℝ × ℝ × ℝ => |q.2.1|)
      (nhdsWithin apm_t02a03_sector_aux_q0 {q | apm_t02a03_sector_aux_box q}) (nhds 0) := by
    exact ((continuous_snd.fst.abs :
      Continuous fun q : ℝ × ℝ × ℝ => |q.2.1|).tendsto' apm_t02a03_sector_aux_q0 0
        (by simp [apm_t02a03_sector_aux_q0])).mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with q hq
  obtain ⟨hp0, hp1, -, -⟩ := apm_t02a03_sector_aux_L6_aux_weights q hq
  rw [apm_t02a03_sector_aux_L6_aux_r_eq, Real.norm_eq_abs]
  have h1 := apm_t02a03_sector_aux_L6_aux_piDelta_snd_abs
    (max 0 (2 * apm_t02a03_sector_aux_lambda q - 1) * q.1,
      max 0 (2 * apm_t02a03_sector_aux_lambda q - 1) * q.2.1)
  simp only [abs_mul, abs_of_nonneg hp0] at h1
  refine h1.trans ?_
  nlinarith [abs_nonneg q.2.1]

lemma apm_t02a03_sector_aux_L6b_r_continuous_at_q0_aux_z :
    ContinuousWithinAt (fun q : ℝ × ℝ × ℝ => (apm_t02a03_sector_aux_r q).2.1)
      {q | apm_t02a03_sector_aux_box q} apm_t02a03_sector_aux_q0 := by
  exact apm_t02a03_sector_aux_L6b_r_continuous_at_q0_aux_z_aux

lemma apm_t02a03_sector_aux_L6b_r_continuous_at_q0_aux_v_aux :
    ContinuousWithinAt (fun q : ℝ × ℝ × ℝ => (apm_t02a03_sector_aux_r q).2.2)
      {q | apm_t02a03_sector_aux_box q} apm_t02a03_sector_aux_q0 := by
  show Filter.Tendsto _ _ (nhds (apm_t02a03_sector_aux_r apm_t02a03_sector_aux_q0).2.2)
  rw [apm_t02a03_sector_aux_L6_aux_r_q0]
  have harg : Filter.Tendsto
      (fun q : ℝ × ℝ × ℝ => max 0 (1 - 2 * apm_t02a03_sector_aux_lambda q) * q.1)
      (nhdsWithin apm_t02a03_sector_aux_q0 {q | apm_t02a03_sector_aux_box q}) (nhds 0) := by
    have hlim : Filter.Tendsto (fun q : ℝ × ℝ × ℝ => |q.1|)
        (nhdsWithin apm_t02a03_sector_aux_q0 {q | apm_t02a03_sector_aux_box q}) (nhds 0) := by
      exact ((continuous_fst.abs :
        Continuous fun q : ℝ × ℝ × ℝ => |q.1|).tendsto' apm_t02a03_sector_aux_q0 0
          (by simp [apm_t02a03_sector_aux_q0])).mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with q hq
    obtain ⟨-, -, hm0, hm1⟩ := apm_t02a03_sector_aux_L6_aux_weights q hq
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm0]
    nlinarith [abs_nonneg q.1]
  have hV := (apm_t02a03_sector_aux_L6_aux_V_continuous.tendsto 0).comp harg
  have hV0 : apm_t02a03_sector_aux_L6_aux_V 0 = (apm_t02a03_sector_aux_q0).2.2 := by
    rw [← apm_t02a03_sector_aux_L6_aux_vArc_eq_V 0 (by rw [Real.cos_zero]; norm_num),
      apm_t02a03_sector_aux_L6_aux_vArc_zero]; rfl
  rw [hV0] at hV
  refine hV.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [Function.comp_apply, apm_t02a03_sector_aux_L6_aux_r_eq]
  exact (apm_t02a03_sector_aux_L6_aux_vArc_r q hq).symm

lemma apm_t02a03_sector_aux_L6b_r_continuous_at_q0_aux_v :
    ContinuousWithinAt (fun q : ℝ × ℝ × ℝ => (apm_t02a03_sector_aux_r q).2.2)
      {q | apm_t02a03_sector_aux_box q} apm_t02a03_sector_aux_q0 := by
  exact apm_t02a03_sector_aux_L6b_r_continuous_at_q0_aux_v_aux

/-- Continuity of `r` at `q0` holds within the box only: off the box (`v > 1`)
the weight `λ` is unbounded near `q0` (e.g. along `(θ, 0, 1 + θ)`). -/
theorem apm_t02a03_sector_aux_L6b_r_continuous_at_q0 :
    ContinuousWithinAt apm_t02a03_sector_aux_r
      {q | apm_t02a03_sector_aux_box q} apm_t02a03_sector_aux_q0 := by
  exact apm_t02a03_sector_aux_L6b_r_continuous_at_q0_aux_theta.prodMk
    (apm_t02a03_sector_aux_L6b_r_continuous_at_q0_aux_z.prodMk
      apm_t02a03_sector_aux_L6b_r_continuous_at_q0_aux_v)

/-- The clamp stage, restricted to `Y`.  This is the direct packaging of
`L4`: its endpoint has height in the coordinate box, and every point not
already in the target lies in the sector chart. -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_sector_aux_clamp :
    ∃ j : C({p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X //
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y p},
        {p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X //
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y p}),
      ∃ J : ContinuousMap.Homotopy (ContinuousMap.id _) j,
        (∀ p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z p.1 →
          ∀ t, J (t, p) = p) ∧
        (∀ p, ¬ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z (j p).1 →
          |(j p).1.1 2| ≤ 1 / 5 ∧
          (17 / 25 : ℝ) ≤ (6 / 5 - (j p).1.1 0) /
            apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad (j p).1.1) := by
  let S := {p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X //
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y p}
  let j : C(S, S) :=
    ⟨fun p ↦ ⟨⟨apm_t02a03_sector_aux_clampMove 1 p.1.1,
      apm_t02a03_sector_aux_L4_clamp.2.1 1 (by simp) p.1 p.2 |>.1⟩,
      Or.elim (apm_t02a03_sector_aux_L4_clamp.2.1 1 (by simp) p.1 p.2 |>.2)
        Or.inl Or.inr⟩,
      (apm_t02a03_sector_aux_L4_clamp.1.comp
        (continuous_const.prodMk
          (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _ |>.subtype_mk _⟩
  let J : ContinuousMap.Homotopy (ContinuousMap.id S) j :=
    { toFun := fun q ↦ ⟨⟨apm_t02a03_sector_aux_clampMove q.1.1 q.2.1.1,
          apm_t02a03_sector_aux_L4_clamp.2.1 q.1.1 q.1.2 q.2.1 q.2.2 |>.1⟩,
        Or.elim (apm_t02a03_sector_aux_L4_clamp.2.1 q.1.1 q.1.2 q.2.1 q.2.2 |>.2)
          Or.inl Or.inr⟩
      continuous_toFun := ((apm_t02a03_sector_aux_L4_clamp.1.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          ((continuous_subtype_val.comp continuous_subtype_val).comp
            continuous_snd))).subtype_mk _).subtype_mk _
      map_zero_left := by
        intro p
        apply Subtype.ext
        apply Subtype.ext
        ext i
        fin_cases i <;> simp [apm_t02a03_sector_aux_clampMove]
      map_one_left := fun p ↦ rfl }
  refine ⟨j, J, ?_, ?_⟩
  · intro p hp t
    apply Subtype.ext
    apply Subtype.ext
    exact apm_t02a03_sector_aux_L4_clamp.2.2 t p.1 hp
  · intro p hn
    have ht := apm_t02a03_sector_aux_L4_clamp.2.1 1 (by simp) p.1 p.2
    rcases ht.2 with hz | hcos
    · exact False.elim (hn (by simpa [j] using hz))
    · refine ⟨?_, hcos⟩
      simp [j, apm_t02a03_sector_aux_clampMove,
        apm_t02a03_sector_aux_clampZ, abs_le]
      norm_num

/-- The box-collapse stage after clamping.  Pull back the straight segment
from `q` to `r q` using `PsiInv`; L1, L2a/b and L6e keep it in the box, L3
and L6d give the endpoint, and L6c makes it relative to `Z`. -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_sector_aux_box
    (j : C({p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X //
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y p},
        {p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X //
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y p}))
    (hj : ∀ p, ¬ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z (j p).1 →
      |(j p).1.1 2| ≤ 1 / 5 ∧
      (17 / 25 : ℝ) ≤ (6 / 5 - (j p).1.1 0) /
        apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_cutoff_aux_rad (j p).1.1) :
    ∃ e : C({p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X //
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y p},
        {p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X //
          apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y p}),
      ∃ K : ContinuousMap.Homotopy j e,
        (∀ p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z (e p).1) ∧
        (∀ p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z (j p).1 →
          ∀ t, K (t, p) = j p) := by
  sorry

/-- Assembly uses L4 to enter the clamped sector, L1--L3 for box coordinates
and target identification, L5--L6 for the box retraction, and then pulls the
straight-line homotopy back through `PsiInv`, gluing it to the identity on the
rest of the loop. -/
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_sector :
    ∃ H : C(Set.Icc (0 : ℝ) 1 × {p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X // apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y p},
        {p : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_X // apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Y p}),
      (∀ p, H (0, p) = p) ∧
      (∀ p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z (H (1, p)).1) ∧
      (∀ t p, apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z p.1 → H (t, p) = p) := by
  obtain ⟨j, J, hJfix, hj⟩ :=
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_sector_aux_clamp
  obtain ⟨e, K, he, hKfix⟩ :=
    apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_sector_aux_box j hj
  let H := J.trans K
  refine ⟨H.toContinuousMap, ?_, ?_, ?_⟩
  · intro p
    exact H.map_zero_left p
  · intro p
    change apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z
      ((J.trans K) (1, p)).1
    rw [ContinuousMap.Homotopy.apply_one]
    exact he p
  · intro t p hp
    change (J.trans K) (t, p) = p
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · exact hJfix p hp _
    · have hjp : j p = p := by
        rw [← J.apply_one p]
        exact hJfix p hp 1
      have hzj : apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_core_aux_Z
          (j p).1 := by rw [hjp]; exact hp
      exact (hKfix p hzj _).trans hjp

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
