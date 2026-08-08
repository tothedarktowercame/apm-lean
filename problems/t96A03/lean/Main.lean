import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t96A03 — two 2-spheres glued along their equators

## Statement repairs

The review packet suggests `H₂(X) = ℤ²`, but this is not the homology of the
space in the source. Mayer–Vietoris gives
`0 → ℤ² → H₂(X) → ℤ → 0`, so `H₂(X) ≅ ℤ³`. Equivalently, the quotient has
four 2-cells attached to one circle, with a rank-one cellular boundary map.
The statement below records the corrected value `ℤ³`.

## Encoding questions

None. Both spheres, their equator, the gluing homeomorphism, the quotient
space, and Mathlib's integral singular homology functor are used directly.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t96A03_Sphere2 :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def apm_t96A03_Equator : Set apm_t96A03_Sphere2 :=
  {x | (x.1 : EuclideanSpace ℝ (Fin 3)) 2 = 0}

abbrev apm_t96A03_EquatorSpace := apm_t96A03_Equator

inductive apm_t96A03_glueRel
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :
    Sum apm_t96A03_Sphere2 apm_t96A03_Sphere2 →
      Sum apm_t96A03_Sphere2 apm_t96A03_Sphere2 → Prop
  | glue (x : apm_t96A03_EquatorSpace) :
      apm_t96A03_glueRel h (Sum.inl x.1) (Sum.inr (h x).1)

def apm_t96A03_X
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :=
  Quotient (Relation.EqvGen.setoid (apm_t96A03_glueRel h))

noncomputable instance
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :
    TopologicalSpace (apm_t96A03_X h) :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t96A03_Sphere2 apm_t96A03_Sphere2 ↦ Quotient.mk _ x)
    inferInstance

def apm_t96A03_quotient
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :
    Sum apm_t96A03_Sphere2 apm_t96A03_Sphere2 → apm_t96A03_X h :=
  fun x => Quotient.mk _ x

lemma apm_t96A03_continuous_quotient
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :
    Continuous (apm_t96A03_quotient h) := by
  exact continuous_coinduced_rng

lemma apm_t96A03_surjective_quotient
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :
    Function.Surjective (apm_t96A03_quotient h) := by
  exact Quotient.mk_surjective

lemma apm_t96A03_isQuotientMap_quotient
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :
    Topology.IsQuotientMap (apm_t96A03_quotient h) := by
  refine ⟨apm_t96A03_surjective_quotient h, ?_⟩
  rfl

lemma apm_t96A03_quotient_glue
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace)
    (x : apm_t96A03_EquatorSpace) :
    apm_t96A03_quotient h (Sum.inl x.1) =
      apm_t96A03_quotient h (Sum.inr (h x).1) := by
  exact Quotient.sound (Relation.EqvGen.rel _ _ (.glue x))

def apm_t96A03_inl
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :
    apm_t96A03_Sphere2 → apm_t96A03_X h :=
  fun x => apm_t96A03_quotient h (Sum.inl x)

def apm_t96A03_inr
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :
    apm_t96A03_Sphere2 → apm_t96A03_X h :=
  fun x => apm_t96A03_quotient h (Sum.inr x)

lemma apm_t96A03_continuous_inl
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :
    Continuous (apm_t96A03_inl h) := by
  exact (apm_t96A03_continuous_quotient h).comp continuous_inl

lemma apm_t96A03_continuous_inr
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :
    Continuous (apm_t96A03_inr h) := by
  exact (apm_t96A03_continuous_quotient h).comp continuous_inr

lemma apm_t96A03_inl_eq_inr_on_equator
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :
    (fun x : apm_t96A03_EquatorSpace => apm_t96A03_inl h x.1) =
      (fun x => apm_t96A03_inr h (h x).1) := by
  funext x
  exact apm_t96A03_quotient_glue h x

lemma apm_t96A03_glueDesc_respects
    {Z : Type*} [TopologicalSpace Z]
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace)
    (f g : C(apm_t96A03_Sphere2, Z))
    (hfg : ∀ x : apm_t96A03_EquatorSpace, f x.1 = g (h x).1)
    {x y : Sum apm_t96A03_Sphere2 apm_t96A03_Sphere2}
    (hxy : Relation.EqvGen (apm_t96A03_glueRel h) x y) :
    Sum.elim f g x = Sum.elim f g y := by
  induction hxy with
  | rel a b hab =>
      cases hab with
      | glue x => exact hfg x
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Continuous maps-out universal property of the equator gluing. -/
noncomputable def apm_t96A03_glueDesc
    {Z : Type*} [TopologicalSpace Z]
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace)
    (f g : C(apm_t96A03_Sphere2, Z))
    (hfg : ∀ x : apm_t96A03_EquatorSpace, f x.1 = g (h x).1) :
    C(apm_t96A03_X h, Z) := by
  let raw : Sum apm_t96A03_Sphere2 apm_t96A03_Sphere2 → Z := Sum.elim f g
  have hraw : Continuous raw := continuous_sum_dom.2 ⟨f.continuous, g.continuous⟩
  exact ⟨Quotient.lift raw (fun _ _ hxy ↦
      apm_t96A03_glueDesc_respects h f g hfg hxy),
    hraw.quotient_lift (fun _ _ hxy ↦
      apm_t96A03_glueDesc_respects h f g hfg hxy)⟩

@[simp] lemma apm_t96A03_glueDesc_inl
    {Z : Type*} [TopologicalSpace Z]
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace)
    (f g : C(apm_t96A03_Sphere2, Z))
    (hfg : ∀ x : apm_t96A03_EquatorSpace, f x.1 = g (h x).1)
    (x : apm_t96A03_Sphere2) :
    apm_t96A03_glueDesc h f g hfg (apm_t96A03_inl h x) = f x := rfl

@[simp] lemma apm_t96A03_glueDesc_inr
    {Z : Type*} [TopologicalSpace Z]
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace)
    (f g : C(apm_t96A03_Sphere2, Z))
    (hfg : ∀ x : apm_t96A03_EquatorSpace, f x.1 = g (h x).1)
    (x : apm_t96A03_Sphere2) :
    apm_t96A03_glueDesc h f g hfg (apm_t96A03_inr h x) = g x := rfl

lemma apm_t96A03_glueDesc_unique
    {Z : Type*} [TopologicalSpace Z]
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace)
    (f g : C(apm_t96A03_Sphere2, Z))
    (hfg : ∀ x : apm_t96A03_EquatorSpace, f x.1 = g (h x).1)
    (u : C(apm_t96A03_X h, Z))
    (hul : ∀ x, u (apm_t96A03_inl h x) = f x)
    (hur : ∀ x, u (apm_t96A03_inr h x) = g x) :
    u = apm_t96A03_glueDesc h f g hfg := by
  ext y
  obtain ⟨x, rfl⟩ := apm_t96A03_surjective_quotient h y
  cases x with
  | inl x => exact hul x
  | inr x => exact hur x

abbrev apm_t96A03_H (k : ℕ) (Y : Type) [TopologicalSpace Y] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y))

theorem apm_t96a03
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :
    Nonempty (apm_t96A03_H 0 (apm_t96A03_X h) ≅ ModuleCat.of ℤ ℤ) ∧
    Limits.IsZero (apm_t96A03_H 1 (apm_t96A03_X h)) ∧
    Nonempty
      (apm_t96A03_H 2 (apm_t96A03_X h) ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t96A03_H k (apm_t96A03_X h)) := by
  /-
  CLOSER HOP 1: beyond the original frame's detached cellular boundary map,
  this file now packages the actual topological gluing cocone.
  `apm_t96A03_isQuotientMap_quotient` proves that the canonical projection is
  a quotient map for the frozen coinduced topology; the two continuous sphere
  inclusions `apm_t96A03_inl` and `apm_t96A03_inr` are compiled; and
  `apm_t96A03_inl_eq_inr_on_equator` proves their exact compatibility with the
  supplied homeomorphism `h`.

  Desk research covered `LEMMA-INDEX.md`, all `ConstructionTargets/`, the
  authoritative T96A03 frame, all solved/partial gluing and homology siblings,
  Mathlib's `TopCat` pushout/colimit, quotient-map, singular-homology,
  suspension, wedge, CW-complex, and Mayer--Vietoris sources, and git history.
  The frame's `sumLinearMap_surjective` only computes a proposed cellular
  boundary and has no comparison map to the frozen singular homology functor.
  No source supplies singular homology of the metric circle or sphere in this
  encoding, a singular Mayer--Vietoris sequence, or a cellular-to-singular
  comparison.  The named Mayer--Vietoris library concerns sheaf cohomology.

  Thus the live bridge is to promote the compiled cocone to a topological
  pushout and apply a singular Mayer--Vietoris exact sequence (or construct a
  CW structure and prove cellular comparison).  Only then can the rank-one
  boundary calculation yield `H₁ = 0` and `H₂ ≅ ℤ³`, together with the degree
  bounds.  The frozen statement is unchanged; no axiom or opaque placeholder
  was introduced.

  CLOSER HOP 2: the cocone is now promoted to its complete function-level
  topological pushout property.  `apm_t96A03_glueDesc_respects` extends the
  equator compatibility through the generated equivalence relation;
  `apm_t96A03_glueDesc` descends compatible continuous maps from the two
  spheres; and its two computation lemmas plus `apm_t96A03_glueDesc_unique`
  prove existence and uniqueness of the induced continuous map.  This reuses
  Mathlib's `Continuous.quotient_lift` and the compiled quotient-eliminator
  pattern in siblings `t01J03`, `t02A03`, and `t97J04`.

  Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, the gluing and
  homology siblings, Mathlib's categorical pushout, singular-homology, sphere,
  and Mayer--Vietoris sources, and git history found no theorem sending this
  now-explicit pushout to a homological exact sequence.  Nor was a computation
  of the metric sphere/equator singular homology found.  Thus all point-set
  pushout bookkeeping is closed; the remaining bridge is exclusively the
  missing functorial algebraic-topology computation.  The frozen statement is
  unchanged.
  -/
  sorry
