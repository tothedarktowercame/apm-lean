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
  sorry

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
-- BEGIN SEAT AREA
theorem apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_cover :
    ∀ p : apm_t02a03_shellY,
      p.1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_torus ∨
        p.1 ∈ apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_retraction_aux_right := by
  sorry
-- END SEAT AREA

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
