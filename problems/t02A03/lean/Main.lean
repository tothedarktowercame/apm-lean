import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.FundamentalGroupProduct
import ConstructionTargets.CircleUniversalCover

open CategoryTheory

/-!
# APM t02A03 — complements of core circles in handlebodies

## Statement repairs

None.

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
  sorry

theorem apm_t02a03 :
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
  sorry
