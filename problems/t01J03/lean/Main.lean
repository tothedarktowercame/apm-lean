import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t01J03: A twice-wound gluing of solid tori

## Statement repairs

None.

## Encoding questions

The informal "spirals twice" curve is encoded algebraically in genuine
fundamental groups. Boundary coordinates are required to be compatible with
the inclusions into the solid tori: the meridian is killed and the longitude
maps to the core generator. The glued space is the actual topological quotient.
-/

open CategoryTheory

noncomputable section

abbrev apm_t01J03_Torus := Circle × Circle
abbrev apm_t01J03_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t01J03_Disk2 := Metric.closedBall (0 : apm_t01J03_E2) 1
abbrev apm_t01J03_BoundaryCircle := Metric.sphere (0 : apm_t01J03_E2) 1
abbrev apm_t01J03_SolidTorus := Circle × apm_t01J03_Disk2
abbrev apm_t01J03_BoundaryTorus := Circle × apm_t01J03_BoundaryCircle

def apm_t01J03_boundaryInclusion :
    apm_t01J03_BoundaryTorus → apm_t01J03_SolidTorus :=
  fun z ↦ (z.1, ⟨z.2.1, le_of_eq z.2.2⟩)

/-- The boundary torus embeds continuously into the solid torus. This is the
map used in both fundamental-group homomorphisms below. -/
lemma apm_t01J03_continuous_boundaryInclusion :
    Continuous apm_t01J03_boundaryInclusion := by
  exact continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

inductive apm_t01J03_glueRel (h : apm_t01J03_BoundaryTorus ≃ₜ
    apm_t01J03_BoundaryTorus) :
    Sum apm_t01J03_SolidTorus apm_t01J03_SolidTorus →
      Sum apm_t01J03_SolidTorus apm_t01J03_SolidTorus → Prop
  | glue (z : apm_t01J03_BoundaryTorus) :
      apm_t01J03_glueRel h
        (Sum.inl (apm_t01J03_boundaryInclusion z))
        (Sum.inr (apm_t01J03_boundaryInclusion (h z)))

def apm_t01J03_gluedSpace (h : apm_t01J03_BoundaryTorus ≃ₜ
    apm_t01J03_BoundaryTorus) :=
  Quotient (Relation.EqvGen.setoid (apm_t01J03_glueRel h))

noncomputable instance (h : apm_t01J03_BoundaryTorus ≃ₜ
    apm_t01J03_BoundaryTorus) : TopologicalSpace (apm_t01J03_gluedSpace h) :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t01J03_SolidTorus apm_t01J03_SolidTorus ↦
      Quotient.mk (Relation.EqvGen.setoid (apm_t01J03_glueRel h)) z)
    inferInstance

def apm_t01J03_gluedInl (h : apm_t01J03_BoundaryTorus ≃ₜ
    apm_t01J03_BoundaryTorus) :
    apm_t01J03_SolidTorus → apm_t01J03_gluedSpace h :=
  fun x ↦ Quotient.mk _ (Sum.inl x)

def apm_t01J03_gluedInr (h : apm_t01J03_BoundaryTorus ≃ₜ
    apm_t01J03_BoundaryTorus) :
    apm_t01J03_SolidTorus → apm_t01J03_gluedSpace h :=
  fun x ↦ Quotient.mk _ (Sum.inr x)

lemma apm_t01J03_continuous_gluedInl
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus) :
    Continuous (apm_t01J03_gluedInl h) := by
  exact continuous_coinduced_rng.comp continuous_inl

lemma apm_t01J03_continuous_gluedInr
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus) :
    Continuous (apm_t01J03_gluedInr h) := by
  exact continuous_coinduced_rng.comp continuous_inr

/-- The two canonical maps into the quotient agree on precisely the boundary
points prescribed by the gluing homeomorphism. -/
lemma apm_t01J03_gluedInl_boundary_eq_gluedInr
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (z : apm_t01J03_BoundaryTorus) :
    apm_t01J03_gluedInl h (apm_t01J03_boundaryInclusion z) =
      apm_t01J03_gluedInr h (apm_t01J03_boundaryInclusion (h z)) := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _ (apm_t01J03_glueRel.glue z))

/-- Compatible maps out of the two solid tori respect the equivalence relation
used to form the glued space. -/
lemma apm_t01J03_gluedDesc_respects
    {Y : Type*} [TopologicalSpace Y]
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (f g : C(apm_t01J03_SolidTorus, Y))
    (hfg : ∀ z, f (apm_t01J03_boundaryInclusion z) =
      g (apm_t01J03_boundaryInclusion (h z))) {x y}
    (hxy : Relation.EqvGen (apm_t01J03_glueRel h) x y) :
    Sum.elim f g x = Sum.elim f g y := by
  induction hxy with
  | rel a b hab =>
    cases hab with
    | glue z => exact hfg z
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The actual continuous pushout eliminator for the generated-relation
quotient: compatible continuous maps from the two pieces descend to the glued
space. -/
def apm_t01J03_gluedDesc
    {Y : Type*} [TopologicalSpace Y]
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (f g : C(apm_t01J03_SolidTorus, Y))
    (hfg : ∀ z, f (apm_t01J03_boundaryInclusion z) =
      g (apm_t01J03_boundaryInclusion (h z))) :
    C(apm_t01J03_gluedSpace h, Y) := by
  let raw : Sum apm_t01J03_SolidTorus apm_t01J03_SolidTorus → Y := Sum.elim f g
  have hraw : Continuous raw := continuous_sum_dom.2 ⟨f.continuous, g.continuous⟩
  exact ⟨Quotient.lift raw (fun _ _ hxy =>
      apm_t01J03_gluedDesc_respects h f g hfg hxy),
    hraw.quotient_lift (fun _ _ hxy =>
      apm_t01J03_gluedDesc_respects h f g hfg hxy)⟩

@[simp] lemma apm_t01J03_gluedDesc_gluedInl
    {Y : Type*} [TopologicalSpace Y]
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (f g : C(apm_t01J03_SolidTorus, Y))
    (hfg : ∀ z, f (apm_t01J03_boundaryInclusion z) =
      g (apm_t01J03_boundaryInclusion (h z))) (x : apm_t01J03_SolidTorus) :
    apm_t01J03_gluedDesc h f g hfg (apm_t01J03_gluedInl h x) = f x := rfl

@[simp] lemma apm_t01J03_gluedDesc_gluedInr
    {Y : Type*} [TopologicalSpace Y]
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (f g : C(apm_t01J03_SolidTorus, Y))
    (hfg : ∀ z, f (apm_t01J03_boundaryInclusion z) =
      g (apm_t01J03_boundaryInclusion (h z))) (x : apm_t01J03_SolidTorus) :
    apm_t01J03_gluedDesc h f g hfg (apm_t01J03_gluedInr h x) = g x := rfl

/-- The descended map is uniquely determined by its restrictions to the two
solid-torus pieces. -/
lemma apm_t01J03_gluedDesc_unique
    {Y : Type*} [TopologicalSpace Y]
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (f g : C(apm_t01J03_SolidTorus, Y))
    (hfg : ∀ z, f (apm_t01J03_boundaryInclusion z) =
      g (apm_t01J03_boundaryInclusion (h z)))
    (u : C(apm_t01J03_gluedSpace h, Y))
    (hul : ∀ x, u (apm_t01J03_gluedInl h x) = f x)
    (hur : ∀ x, u (apm_t01J03_gluedInr h x) = g x) :
    u = apm_t01J03_gluedDesc h f g hfg := by
  ext q
  refine Quotient.inductionOn q ?_
  rintro (x | x)
  · exact hul x
  · exact hur x

def apm_t01J03_gluedBasepoint (h : apm_t01J03_BoundaryTorus ≃ₜ
    apm_t01J03_BoundaryTorus) (z₀ : apm_t01J03_BoundaryTorus) :
    apm_t01J03_gluedSpace h :=
  Quotient.mk _ (Sum.inl (apm_t01J03_boundaryInclusion z₀))

abbrev apm_t01J03_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t01J03_hasTwiceSpiral
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (z₀ : apm_t01J03_BoundaryTorus)
    (e₁ : FundamentalGroup apm_t01J03_BoundaryTorus z₀ ≃*
      Multiplicative (ℤ × ℤ))
    (e₂ : FundamentalGroup apm_t01J03_BoundaryTorus (h z₀) ≃*
      Multiplicative (ℤ × ℤ))
    (c₁ : FundamentalGroup apm_t01J03_SolidTorus
      (apm_t01J03_boundaryInclusion z₀) ≃* Multiplicative ℤ)
    (c₂ : FundamentalGroup apm_t01J03_SolidTorus
      (apm_t01J03_boundaryInclusion (h z₀)) ≃* Multiplicative ℤ) : Prop :=
  (∀ g, c₁ ((FundamentalGroup.map
      ⟨apm_t01J03_boundaryInclusion, continuous_fst.prodMk
        ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩ z₀) g) =
      Multiplicative.ofAdd (e₁ g).toAdd.2) ∧
  (∀ g, c₂ ((FundamentalGroup.map
      ⟨apm_t01J03_boundaryInclusion, continuous_fst.prodMk
        ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩ (h z₀)) g) =
      Multiplicative.ofAdd (e₂ g).toAdd.2) ∧
  e₂ ((FundamentalGroup.map ⟨h, h.continuous⟩ z₀)
    (e₁.symm (Multiplicative.ofAdd (1, 0)))) =
      Multiplicative.ofAdd (1, 2)

/-- Why this unblocks the first five conjuncts of `apm_t01j03`: this is the
missing fundamental-group and integral singular-homology computation for the
actual product `Circle × Circle`, including vanishing above its dimension. -/
theorem apm_t01J03_bridge_1 :
    Nonempty
      (FundamentalGroup apm_t01J03_Torus (1, 1) ≃*
        Multiplicative (ℤ × ℤ)) ∧
    Nonempty (apm_t01J03_H 0 apm_t01J03_Torus ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t01J03_H 1 apm_t01J03_Torus ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    Nonempty (apm_t01J03_H 2 apm_t01J03_Torus ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t01J03_H k apm_t01J03_Torus) := by
  sorry

/-- Why this unblocks the final conjunct of `apm_t01j03`: this is the missing
Seifert--van Kampen and singular Mayer--Vietoris computation for the concrete
pushout quotient under precisely the encoded twice-spiral boundary relation. -/
theorem apm_t01J03_bridge_2
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (z₀ : apm_t01J03_BoundaryTorus)
    (e₁ : FundamentalGroup apm_t01J03_BoundaryTorus z₀ ≃*
      Multiplicative (ℤ × ℤ))
    (e₂ : FundamentalGroup apm_t01J03_BoundaryTorus (h z₀) ≃*
      Multiplicative (ℤ × ℤ))
    (c₁ : FundamentalGroup apm_t01J03_SolidTorus
      (apm_t01J03_boundaryInclusion z₀) ≃* Multiplicative ℤ)
    (c₂ : FundamentalGroup apm_t01J03_SolidTorus
      (apm_t01J03_boundaryInclusion (h z₀)) ≃* Multiplicative ℤ)
    (hspiral : apm_t01J03_hasTwiceSpiral h z₀ e₁ e₂ c₁ c₂) :
    let M := apm_t01J03_gluedSpace h
    let m₀ := apm_t01J03_gluedBasepoint h z₀
    Nonempty (FundamentalGroup M m₀ ≃* Multiplicative (ZMod 2)) ∧
    Nonempty (apm_t01J03_H 0 M ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t01J03_H 1 M ≅ ModuleCat.of ℤ (ZMod 2)) ∧
    Limits.IsZero (apm_t01J03_H 2 M) ∧
    Nonempty (apm_t01J03_H 3 M ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k : ℕ, 4 ≤ k → Limits.IsZero (apm_t01J03_H k M) := by
  sorry

theorem apm_t01j03 :
    Nonempty
      (FundamentalGroup apm_t01J03_Torus (1, 1) ≃*
        Multiplicative (ℤ × ℤ)) ∧
    Nonempty (apm_t01J03_H 0 apm_t01J03_Torus ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t01J03_H 1 apm_t01J03_Torus ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    Nonempty (apm_t01J03_H 2 apm_t01J03_Torus ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t01J03_H k apm_t01J03_Torus)) ∧
    (∀ (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
        (z₀ : apm_t01J03_BoundaryTorus)
        (e₁ : FundamentalGroup apm_t01J03_BoundaryTorus z₀ ≃*
          Multiplicative (ℤ × ℤ))
        (e₂ : FundamentalGroup apm_t01J03_BoundaryTorus (h z₀) ≃*
          Multiplicative (ℤ × ℤ))
        (c₁ : FundamentalGroup apm_t01J03_SolidTorus
          (apm_t01J03_boundaryInclusion z₀) ≃* Multiplicative ℤ)
        (c₂ : FundamentalGroup apm_t01J03_SolidTorus
          (apm_t01J03_boundaryInclusion (h z₀)) ≃* Multiplicative ℤ),
      apm_t01J03_hasTwiceSpiral h z₀ e₁ e₂ c₁ c₂ →
      let M := apm_t01J03_gluedSpace h
      let m₀ := apm_t01J03_gluedBasepoint h z₀
      Nonempty (FundamentalGroup M m₀ ≃* Multiplicative (ZMod 2)) ∧
      Nonempty (apm_t01J03_H 0 M ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (apm_t01J03_H 1 M ≅ ModuleCat.of ℤ (ZMod 2)) ∧
      Limits.IsZero (apm_t01J03_H 2 M) ∧
      Nonempty (apm_t01J03_H 3 M ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ k : ℕ, 4 ≤ k → Limits.IsZero (apm_t01J03_H k M)) := by
  /-
  Boundary (skipped): the requested computation needs Seifert--van Kampen
  for the quotient gluing and the singular-homology Mayer--Vietoris long
  exact sequence, together with concrete computations for `Circle`, disks,
  and their products. I searched Mathlib's `FundamentalGroupoid` product,
  `FundamentalGroup`, singular-homology, Künneth, pushout, and
  Mayer--Vietoris APIs. Product preservation of the fundamental *groupoid*
  exists, but the fundamental group of `Circle` is not computed as `ℤ`, and
  there is no van Kampen theorem or singular Mayer--Vietoris sequence that
  can turn the encoded twice-spiral relation into the `ZMod 2` and homology
  conclusions. The partial siblings `t00A01` and `t02A03` independently
  record the same missing gluing and wedge APIs. The `CircleParam` target
  concerns analytic contour integrals rather than fundamental groups, and no
  relevant result occurs elsewhere in `ConstructionTargets/` or
  `YoungL2.lean`. Developing those foundations is beyond this pass.

  Closer hop 1 factored the repeated local topology obligation into the compiled
  lemma `apm_t01J03_continuous_boundaryInclusion`. Inspection of
  `AlgebraicTopology.FundamentalGroupoid.Product` confirms preservation of
  categorical products, but specializing automorphism groups still requires a
  computed `FundamentalGroup Circle 1 ≃* Multiplicative ℤ`, which is absent.
  The available Mayer--Vietoris results are specifically for sheaf cohomology,
  not the singular-homology functor used here. Thus neither route reaches the
  quotient gluing computation.

  Closer hop 2 goes beyond the library search by exposing the quotient's
  canonical cocone explicitly. `apm_t01J03_gluedInl` and `.gluedInr` are the
  two maps from the solid tori; `apm_t01J03_continuous_gluedInl` and `.gluedInr`
  prove continuity directly from the coinduced topology; and
  `apm_t01J03_gluedInl_boundary_eq_gluedInr` proves their composites with the
  two boundary maps agree using the generating relation. These are precisely
  the local inputs a future van Kampen or singular Mayer--Vietoris theorem
  would consume. A renewed search of quotient/pushout and colimit APIs found
  no theorem promoting this cocone to the required fundamental-group or
  singular-homology computation, so all numerical invariants in the frozen
  conclusion remain open. The statement is unchanged.

  CLOSER HOP 3: the cocone has now been promoted to its full function-level
  topological universal property. `apm_t01J03_gluedDesc_respects` proves that
  compatible maps from the solid tori respect the generated equivalence
  relation. `apm_t01J03_gluedDesc` descends them to a continuous map from the
  glued space, its two simp lemmas recover the original restrictions, and
  `apm_t01J03_gluedDesc_unique` proves uniqueness by quotient induction. Thus
  the concrete quotient is no longer missing a continuous pushout eliminator.
  Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, all problem
  artifacts, Mathlib's fundamental-group/pushout and singular-homology
  sources, and git history found no functorial theorem that consumes this
  universal property: there is still no Seifert--van Kampen theorem, singular
  Mayer--Vietoris sequence, or circle fundamental-group computation. The
  numerical invariants therefore remain open and the frozen statement is
  unchanged.
  -/
  sorry
