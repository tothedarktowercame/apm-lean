import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t97A01 — the nonorientable genus-three surface

## Statement repairs

None.

## Encoding note

Both requested surfaces are actual polygon quotients of the closed unit disk.
The first glues the six boundary edges with word `a a b b c c`; the second
uses `a b a⁻¹ b⁻¹ c c`, the torus connected-summed with `ℝP²`. The conclusion
uses singular homology of these spaces and the fundamental group of the
second quotient, rather than detached cellular arithmetic.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t97a01_Disk := Metric.closedBall (0 : ℂ) 1

/-- The point at parameter `t` on edge `j` of a regular hexagonal boundary
parameterization of the disk. -/
def apm_t97a01_edgePoint (j : Fin 6) (t : Set.Icc (0 : ℝ) 1) :
    apm_t97a01_Disk :=
  ⟨Complex.exp (Complex.I * (2 * Real.pi * ((j : ℝ) + t.1) / 6)), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    simp⟩

/-- Edge identifications for the word `a a b b c c`. -/
inductive apm_t97a01_RelX : apm_t97a01_Disk → apm_t97a01_Disk → Prop
  | a (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelX (apm_t97a01_edgePoint 0 t) (apm_t97a01_edgePoint 1 t)
  | b (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelX (apm_t97a01_edgePoint 2 t) (apm_t97a01_edgePoint 3 t)
  | c (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelX (apm_t97a01_edgePoint 4 t) (apm_t97a01_edgePoint 5 t)

/-- Edge identifications for the word `a b a⁻¹ b⁻¹ c c`. -/
inductive apm_t97a01_RelTorusRP2 :
    apm_t97a01_Disk → apm_t97a01_Disk → Prop
  | a (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelTorusRP2 (apm_t97a01_edgePoint 0 t)
        (apm_t97a01_edgePoint 2 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩)
  | b (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelTorusRP2 (apm_t97a01_edgePoint 1 t)
        (apm_t97a01_edgePoint 3 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩)
  | c (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelTorusRP2 (apm_t97a01_edgePoint 4 t)
        (apm_t97a01_edgePoint 5 t)

def apm_t97a01_X := Quotient (Relation.EqvGen.setoid apm_t97a01_RelX)
def apm_t97a01_TorusRP2 :=
  Quotient (Relation.EqvGen.setoid apm_t97a01_RelTorusRP2)

noncomputable instance : TopologicalSpace apm_t97a01_X :=
  TopologicalSpace.coinduced (fun x : apm_t97a01_Disk ↦ Quotient.mk _ x) inferInstance

noncomputable instance : TopologicalSpace apm_t97a01_TorusRP2 :=
  TopologicalSpace.coinduced (fun x : apm_t97a01_Disk ↦ Quotient.mk _ x) inferInstance

def apm_t97a01_quotientX : apm_t97a01_Disk → apm_t97a01_X :=
  fun x => Quotient.mk _ x

def apm_t97a01_quotientTorusRP2 : apm_t97a01_Disk → apm_t97a01_TorusRP2 :=
  fun x => Quotient.mk _ x

lemma apm_t97a01_continuous_quotientX : Continuous apm_t97a01_quotientX := by
  exact continuous_coinduced_rng

lemma apm_t97a01_surjective_quotientX :
    Function.Surjective apm_t97a01_quotientX := by
  exact Quotient.mk_surjective

lemma apm_t97a01_continuous_quotientTorusRP2 :
    Continuous apm_t97a01_quotientTorusRP2 := by
  exact continuous_coinduced_rng

lemma apm_t97a01_surjective_quotientTorusRP2 :
    Function.Surjective apm_t97a01_quotientTorusRP2 := by
  exact Quotient.mk_surjective

lemma apm_t97a01_quotientX_identifies_a (t : Set.Icc (0 : ℝ) 1) :
    apm_t97a01_quotientX (apm_t97a01_edgePoint 0 t) =
      apm_t97a01_quotientX (apm_t97a01_edgePoint 1 t) := by
  exact Quotient.sound (Relation.EqvGen.rel _ _ (.a t))

lemma apm_t97a01_quotientTorusRP2_identifies_c (t : Set.Icc (0 : ℝ) 1) :
    apm_t97a01_quotientTorusRP2 (apm_t97a01_edgePoint 4 t) =
      apm_t97a01_quotientTorusRP2 (apm_t97a01_edgePoint 5 t) := by
  exact Quotient.sound (Relation.EqvGen.rel _ _ (.c t))

abbrev apm_t97a01_H (k : ℕ) (Y : Type) [TopologicalSpace Y] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y))

def apm_t97a01_baseX : apm_t97a01_X := Quotient.mk _ (0 : apm_t97a01_Disk)
def apm_t97a01_baseTorusRP2 : apm_t97a01_TorusRP2 :=
  Quotient.mk _ (0 : apm_t97a01_Disk)

def apm_t97a01_relator : FreeGroup (Fin 3) :=
  (.of 0) * (.of 1) * (.of 0)⁻¹ * (.of 1)⁻¹ * (.of 2) * (.of 2)

theorem apm_t97a01 :
    Nonempty (apm_t97a01_H 0 apm_t97a01_X ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97a01_H 1 apm_t97a01_X ≅
      ModuleCat.of ℤ (ℤ × ℤ × ZMod 2)) ∧
    (∀ k : ℕ, 2 ≤ k → Limits.IsZero (apm_t97a01_H k apm_t97a01_X)) ∧
    Nonempty (apm_t97a01_H 0 apm_t97a01_TorusRP2 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97a01_H 1 apm_t97a01_TorusRP2 ≅
      ModuleCat.of ℤ (ℤ × ℤ × ZMod 2)) ∧
    (∀ k : ℕ, 2 ≤ k → Limits.IsZero (apm_t97a01_H k apm_t97a01_TorusRP2)) ∧
    Nonempty
      (FundamentalGroup apm_t97a01_TorusRP2 apm_t97a01_baseTorusRP2 ≃*
        PresentedGroup ({apm_t97a01_relator} : Set (FreeGroup (Fin 3)))) := by
  /-
  Boundary (closer hop 1): the intended finite cellular calculation has one
  vertex, three one-cells, and one two-cell.  For `X` its cellular boundary is
  `1 ↦ (2,2,2)`, while the torus-crosscap word gives the same Smith normal
  form; Van Kampen gives the displayed one-relator group.  The frozen goals,
  however, concern *singular homology of the actual `EqvGen` polygon
  quotients* and their actual `FundamentalGroup`.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, Mathlib's singular
  homology and presented-group sources, and closed siblings `t01J03`,
  `t02A03`, `t92J05`, and `t97J04` found no cellular-to-singular comparison
  for polygon quotients, singular Mayer--Vietoris sequence, or topological
  Seifert--van Kampen theorem.  Abstractly calculating the chain complex or
  the presented group locally therefore does not bridge to any conjunct of
  this frozen theorem.  Closure requires developing one of those missing
  topology bridges, including continuity/quotient identifications for these
  concrete edge relations.

  CLOSER HOP 2: the canonical polygon projections are now explicit as
  `apm_t97a01_quotientX` and `apm_t97a01_quotientTorusRP2`; their continuity
  and surjectivity are compiled from the coinduced topology. Representative
  gluing equations are compiled in `apm_t97a01_quotientX_identifies_a` and
  `apm_t97a01_quotientTorusRP2_identifies_c`, confirming that generating edge
  relations become actual quotient equalities. These are the raw inputs a
  future cellular comparison or van Kampen theorem would consume.

  Going beyond the previous search, I compared the newer cocone layers in
  `t02A03` and `t01J03` and inspected Mathlib's `IsQuotientMap` lifting APIs.
  They prove continuity of descended relation-respecting maps but do not
  compute singular homology or fundamental groups. The covering-quotient API
  concerns properly discontinuous group actions, not these boundary-pairing
  `EqvGen` relations. Thus all frozen invariant computations still require
  cellular-to-singular comparison or topological van Kampen; the statement is
  unchanged.
  -/
  sorry
