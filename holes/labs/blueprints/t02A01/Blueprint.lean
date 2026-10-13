import Mathlib
import ConstructionTargets.CoveringMonodromyCosets

open Set

def apm_t02a01_boundaryMonodromy (n : ℕ) (a b : ZMod n) : Equiv.Perm (ZMod n) :=
  Equiv.addRight a * Equiv.addRight b * (Equiv.addRight a)⁻¹ * (Equiv.addRight b)⁻¹

noncomputable def apm_t02a01_boundaryComponentCount (n : ℕ) (a b : ZMod n) : ℕ :=
  Nat.card {x : ZMod n // apm_t02a01_boundaryMonodromy n a b x = x}

theorem apm_t02a01_previous_encoding :
    ∀ (n : ℕ), 0 < n → ∀ a b : ZMod n,
      apm_t02a01_boundaryMonodromy n a b = 1 ∧
      apm_t02a01_boundaryComponentCount n a b = n := by
  intro n hn a b
  have hmon : apm_t02a01_boundaryMonodromy n a b = 1 := by
    ext x
    simp [apm_t02a01_boundaryMonodromy, Equiv.Perm.mul_apply]
    abel
  constructor
  · exact hmon
  · simp [apm_t02a01_boundaryComponentCount, hmon, Nat.card_zmod]

abbrev apm_t02a01_squareAnnulus :=
  {x : ℝ × ℝ // x.1 ∈ Set.Icc 0 1 ∧ x.2 ∈ Set.Icc 0 1 ∧
    (1 / 4 : ℝ) ≤ ‖x - (1 / 2, 1 / 2)‖}

inductive apm_t02a01_edgeRel :
    apm_t02a01_squareAnnulus → apm_t02a01_squareAnnulus → Prop
  | horizontal (y : ℝ) (hy : y ∈ Set.Icc 0 1)
      (h₀ : (1 / 4 : ℝ) ≤ ‖((0, y) : ℝ × ℝ) - (1 / 2, 1 / 2)‖)
      (h₁ : (1 / 4 : ℝ) ≤ ‖((1, y) : ℝ × ℝ) - (1 / 2, 1 / 2)‖) :
      apm_t02a01_edgeRel ⟨(0, y), ⟨by norm_num, hy, h₀⟩⟩
        ⟨(1, y), ⟨by norm_num, hy, h₁⟩⟩
  | vertical (x : ℝ) (hx : x ∈ Set.Icc 0 1)
      (h₀ : (1 / 4 : ℝ) ≤ ‖((x, 0) : ℝ × ℝ) - (1 / 2, 1 / 2)‖)
      (h₁ : (1 / 4 : ℝ) ≤ ‖((x, 1) : ℝ × ℝ) - (1 / 2, 1 / 2)‖) :
      apm_t02a01_edgeRel ⟨(x, 0), ⟨hx, by norm_num, h₀⟩⟩
        ⟨(x, 1), ⟨hx, by norm_num, h₁⟩⟩

def apm_t02a01_puncturedTorus :=
  Quotient (Relation.EqvGen.setoid apm_t02a01_edgeRel)

noncomputable instance : TopologicalSpace apm_t02a01_puncturedTorus :=
  TopologicalSpace.coinduced
    (fun x : apm_t02a01_squareAnnulus ↦
      (Quotient.mk _ x : apm_t02a01_puncturedTorus)) inferInstance

def apm_t02a01_boundary : Set apm_t02a01_puncturedTorus :=
  (fun x : apm_t02a01_squareAnnulus ↦
    (Quotient.mk _ x : apm_t02a01_puncturedTorus)) ''
      {x | ‖x.1 - ((1 / 2, 1 / 2) : ℝ × ℝ)‖ = (1 / 4 : ℝ)}

abbrev apm_t02a01_boundarySpace :=
  apm_t02a01_boundary

def apm_t02a01_restrictedCover {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) :
    p ⁻¹' apm_t02a01_boundary → apm_t02a01_boundarySpace :=
  fun x => ⟨p x.1, x.2⟩

/-- LIBRARY (punctured-torus geometry): the concrete inner boundary is a
circle, with the local hypotheses needed for covering monodromy. -/
theorem apm_t02a01_boundary_geometry :
    Nonempty (PathConnectedSpace apm_t02a01_boundarySpace) ∧
      Nonempty (LocPathConnectedSpace apm_t02a01_boundarySpace) := by
  sorry

/-- LIBRARY (boundary commutator + abelian deck group): monodromy of every
loop in the restricted boundary cover is trivial. -/
theorem apm_t02a01_boundary_monodromy_trivial
    {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) (n : ℕ)
    (hcover : IsCoveringMap p)
    (deck : ZMod n → Homeomorph Stilde Stilde)
    (hdeck_zero : deck 0 = Homeomorph.refl Stilde)
    (hdeck_add : ∀ z w, deck (z + w) = (deck z).trans (deck w))
    (hdeck_over : ∀ z x, p (deck z x) = p x)
    (hdeck_transitive : ∀ x y, p x = p y → ∃! z, deck z x = y) :
    ∃ hcov : IsCoveringMap (apm_t02a01_restrictedCover p),
      ∀ (e : p ⁻¹' apm_t02a01_boundary)
        (γ : FundamentalGroup apm_t02a01_boundarySpace
          (apm_t02a01_restrictedCover p e)),
        hcov.monodromy γ ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
  sorry

/-- LIBRARY (covering monodromy): a path-connected base with trivial
monodromy has one connected component per point of a fiber. -/
theorem apm_t02a01_components_equiv_fiber
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace B] [LocPathConnectedSpace B]
    (q : E → B) (hq : IsCoveringMap q)
    (e : E)
    (hmono : ∀ γ : FundamentalGroup B (q e),
      hq.monodromy γ ⟨e, rfl⟩ = ⟨e, rfl⟩) :
    Nonempty (ConnectedComponents E ≃ q ⁻¹' {q e}) := by
  sorry

/-- The supplied simply transitive `ZMod n` deck action identifies every
fiber with `ZMod n`. -/
theorem apm_t02a01_fiber_card
    {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) (n : ℕ)
    (deck : ZMod n → Homeomorph Stilde Stilde)
    (hdeck_over : ∀ z x, p (deck z x) = p x)
    (hdeck_transitive : ∀ x y, p x = p y → ∃! z, deck z x = y)
    (x : p ⁻¹' apm_t02a01_boundary) :
    Nat.card (apm_t02a01_restrictedCover p ⁻¹'
      {apm_t02a01_restrictedCover p x}) = n := by
  sorry

theorem apm_t02a01
    {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) (n : ℕ)
    (hn : 0 < n)
    (hcover : IsCoveringMap p)
    (hp_surjective : Function.Surjective p)
    (deck : ZMod n → Homeomorph Stilde Stilde)
    (hdeck_zero : deck 0 = Homeomorph.refl Stilde)
    (hdeck_add : ∀ z w, deck (z + w) = (deck z).trans (deck w))
    (hdeck_over : ∀ z x, p (deck z x) = p x)
    (hdeck_transitive : ∀ x y, p x = p y → ∃! z, deck z x = y) :
    Nat.card (ConnectedComponents (p ⁻¹' apm_t02a01_boundary)) = n := by
  letI := (apm_t02a01_boundary_geometry).1.some
  letI := (apm_t02a01_boundary_geometry).2.some
  let a := Classical.choice (inferInstance : Nonempty apm_t02a01_boundarySpace)
  obtain ⟨b, hb⟩ := hp_surjective a.1
  let e : p ⁻¹' apm_t02a01_boundary := ⟨b, by
    change p b ∈ apm_t02a01_boundary
    rw [hb]
    exact a.property⟩
  obtain ⟨hcov, hmono⟩ := apm_t02a01_boundary_monodromy_trivial p n hcover deck
    hdeck_zero hdeck_add hdeck_over hdeck_transitive
  obtain ⟨equiv⟩ := apm_t02a01_components_equiv_fiber
    (apm_t02a01_restrictedCover p) hcov e (hmono e)
  rw [Nat.card_congr equiv]
  exact apm_t02a01_fiber_card p n deck hdeck_over hdeck_transitive e

#print axioms apm_t02a01
