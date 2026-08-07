import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

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
  -/
  sorry
