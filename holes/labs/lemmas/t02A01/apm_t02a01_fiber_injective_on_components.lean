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

def apm_t02a01_boundary_homeomorph_circle_aux_interior
    (x : apm_t02a01_squareAnnulus) : Prop :=
  x.1.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ x.1.2 ∈ Set.Ioo (0 : ℝ) 1

theorem apm_t02a01_boundary_homeomorph_circle_aux_rel_not_interior
    {x y : apm_t02a01_squareAnnulus} (h : apm_t02a01_edgeRel x y) :
    ¬ apm_t02a01_boundary_homeomorph_circle_aux_interior x ∧
      ¬ apm_t02a01_boundary_homeomorph_circle_aux_interior y := by
  cases h with
  | horizontal y hy h₀ h₁ =>
      constructor
      · intro h; exact (lt_irrefl (0 : ℝ)) h.1.1
      · intro h; exact (lt_irrefl (1 : ℝ)) h.1.2
  | vertical x hx h₀ h₁ =>
      constructor
      · intro h; exact (lt_irrefl (0 : ℝ)) h.2.1
      · intro h; exact (lt_irrefl (1 : ℝ)) h.2.2

theorem apm_t02a01_boundary_homeomorph_circle_aux_eq_of_eqvGen
    {x y : apm_t02a01_squareAnnulus}
    (h : Relation.EqvGen apm_t02a01_edgeRel x y) :
    (apm_t02a01_boundary_homeomorph_circle_aux_interior x → x = y) ∧
      (apm_t02a01_boundary_homeomorph_circle_aux_interior y → x = y) := by
  induction h with
  | rel x y h =>
      obtain ⟨hx, hy⟩ :=
        apm_t02a01_boundary_homeomorph_circle_aux_rel_not_interior h
      exact ⟨fun hi ↦ (hx hi).elim, fun hi ↦ (hy hi).elim⟩
  | refl x => exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  | symm x y h ih => exact ⟨fun hi ↦ (ih.2 hi).symm, fun hi ↦ (ih.1 hi).symm⟩
  | trans x y z hxy hyz ihxy ihyz =>
      constructor
      · intro hx
        have hxy' := ihxy.1 hx
        subst y
        exact ihyz.1 hx
      · intro hz
        have hyz' := ihyz.2 hz
        subst z
        exact ihxy.2 hz

/-- The inner sphere of the square annulus (for the max norm on `ℝ × ℝ`, the
boundary of the square `[1/4, 3/4]²`) is a topological circle, e.g. by radial
projection `x ↦ (x - c) / ‖x - c‖₂` composed with `Circle` coordinates. -/
theorem apm_t02a01_boundary_homeomorph_circle_aux_sphere :
    Nonempty ({x : apm_t02a01_squareAnnulus |
      ‖x.1 - ((1 / 2, 1 / 2) : ℝ × ℝ)‖ = (1 / 4 : ℝ)} ≃ₜ Circle) := by
  sorry

/-- The quotient map restricts to a homeomorphism from the inner sphere onto
the boundary subtype.  Injectivity: inner-sphere points are interior to
`(0,1)²`, so their classes are singletons
(`apm_t02a01_boundary_homeomorph_circle_aux_eq_of_eqvGen`).  Openness: the
interior points form an open saturated set, on which the quotient map is an
open embedding. -/
theorem apm_t02a01_boundary_homeomorph_circle_aux_quotient :
    Nonempty ({x : apm_t02a01_squareAnnulus |
      ‖x.1 - ((1 / 2, 1 / 2) : ℝ × ℝ)‖ = (1 / 4 : ℝ)} ≃ₜ
        apm_t02a01_boundarySpace) := by
  sorry

/-- The inner metric circle survives the outer-edge quotient and gives the
boundary subtype. -/
theorem apm_t02a01_boundary_homeomorph_circle :
    Nonempty (apm_t02a01_boundarySpace ≃ₜ Circle) := by
  obtain ⟨q⟩ := apm_t02a01_boundary_homeomorph_circle_aux_quotient
  obtain ⟨c⟩ := apm_t02a01_boundary_homeomorph_circle_aux_sphere
  exact ⟨q.symm.trans c⟩

/-- Transport path connectedness across the concrete boundary-circle
homeomorphism.  The homeomorphism is an explicit hypothesis so this leaf is
independent of its construction. -/
theorem apm_t02a01_boundary_pathConnected
    (h : Nonempty (apm_t02a01_boundarySpace ≃ₜ Circle)) :
    Nonempty (PathConnectedSpace apm_t02a01_boundarySpace) := by
  let e := h.some
  haveI : PathConnectedSpace Circle :=
    isPathConnected_iff_pathConnectedSpace.mp (by
      change IsPathConnected (Metric.sphere (0 : ℂ) 1)
      apply isPathConnected_sphere
      · rw [Complex.rank_real_complex]
        norm_num
      · norm_num)
  exact ⟨e.symm.surjective.pathConnectedSpace e.symm.continuous⟩

/-- Transport local path connectedness across the concrete boundary-circle
homeomorphism. -/
theorem apm_t02a01_boundary_locPathConnected
    (h : Nonempty (apm_t02a01_boundarySpace ≃ₜ Circle)) :
    Nonempty (LocPathConnectedSpace apm_t02a01_boundarySpace) := by
  obtain ⟨e⟩ := h
  let circleEquiv : AddCircle (1 : ℝ) ≃ₜ Circle :=
    AddCircle.homeomorphCircle one_ne_zero
  letI : LocPathConnectedSpace (AddCircle (1 : ℝ)) :=
    isQuotientMap_quotient_mk'.locPathConnectedSpace
  letI : LocPathConnectedSpace Circle :=
    circleEquiv.isQuotientMap.locPathConnectedSpace
  exact ⟨e.symm.isQuotientMap.locPathConnectedSpace⟩

/-- The two geometric instances used below, assembled from the independently
provable circle leaves. -/
theorem apm_t02a01_boundary_geometry :
    Nonempty (PathConnectedSpace apm_t02a01_boundarySpace) ∧
      Nonempty (LocPathConnectedSpace apm_t02a01_boundarySpace) := by
  have h := apm_t02a01_boundary_homeomorph_circle
  exact ⟨apm_t02a01_boundary_pathConnected h,
    apm_t02a01_boundary_locPathConnected h⟩

/-- Restricting a covering map to the full inverse image of a subtype is again
a covering map. -/
theorem apm_t02a01_restrictedCover_isCovering
    {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) (hcover : IsCoveringMap p) :
    IsCoveringMap (apm_t02a01_restrictedCover p) := by
  exact hcover.restrictPreimage apm_t02a01_boundary

/-- LIBRARY (polygon boundary word): lifting any loop on the inner boundary of
the square-annulus quotient ends at a deck translate by a commutator.
Repaired 2026-10-14 (lemma-6 counterexample): `deck` must be an action
(`hdeck_zero`, `hdeck_add`), else `deck 0` may move points and the statement is
false for the constant loop; the global cover `hcover` is also supplied, since
the boundary loop is a commutator only in π₁ of the punctured torus. -/
theorem apm_t02a01_boundary_monodromy_is_deck_commutator
    {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) (n : ℕ)
    (hcover : IsCoveringMap p)
    (hcov : IsCoveringMap (apm_t02a01_restrictedCover p))
    (deck : ZMod n → Homeomorph Stilde Stilde)
    (hdeck_zero : deck 0 = Homeomorph.refl Stilde)
    (hdeck_add : ∀ z w, deck (z + w) = (deck z).trans (deck w))
    (hdeck_over : ∀ z x, p (deck z x) = p x)
    (hdeck_transitive : ∀ x y, p x = p y → ∃! z, deck z x = y)
    (e : p ⁻¹' apm_t02a01_boundary)
    (γ : FundamentalGroup apm_t02a01_boundarySpace
      (apm_t02a01_restrictedCover p e)) :
    ∃ u v : ZMod n,
      (hcov.monodromy γ ⟨e, rfl⟩).1.1 = deck (u + v - u - v) e.1 := by
  sorry

/-- The commutator translation is the identity because the deck group is the
abelian group `ZMod n`.  This is independent of the boundary geometry. -/
theorem apm_t02a01_deck_commutator_apply
    {Stilde : Type*} [TopologicalSpace Stilde] (n : ℕ)
    (deck : ZMod n → Homeomorph Stilde Stilde)
    (hdeck_zero : deck 0 = Homeomorph.refl Stilde)
    (u v : ZMod n) (x : Stilde) :
    deck (u + v - u - v) x = x := by
  have hcomm : u + v - u - v = 0 := by
    abel
  rw [hcomm, hdeck_zero]
  rfl

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
  let hcov := apm_t02a01_restrictedCover_isCovering p hcover
  refine ⟨hcov, ?_⟩
  intro e γ
  obtain ⟨u, v, huv⟩ :=
    apm_t02a01_boundary_monodromy_is_deck_commutator p n hcover hcov deck
      hdeck_zero hdeck_add hdeck_over hdeck_transitive e γ
  apply Subtype.ext
  apply Subtype.ext
  exact huv.trans (apm_t02a01_deck_commutator_apply n deck hdeck_zero u v e.1)

/-- A covering over a path-connected base has a point above the chosen
basepoint in every connected component of its total space. -/
theorem apm_t02a01_component_meets_fiber
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace B] [LocPathConnectedSpace B]
    (q : E → B) (hq : IsCoveringMap q) (e : E) :
    Function.Surjective
      (fun x : q ⁻¹' {q e} => (x.1 : ConnectedComponents E)) := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨γ⟩ := PathConnectedSpace.joined (q x) (q e)
  let Γ := hq.liftPath γ x (by simp)
  have hΓ0 : Γ 0 = x := hq.liftPath_zero γ x (by simp)
  have hΓ1 : q (Γ 1) = q e := by
    exact (congr_fun (hq.liftPath_lifts γ x (by simp)) 1).trans γ.target
  refine ⟨⟨Γ 1, by simpa using hΓ1⟩, ?_⟩
  rw [ConnectedComponents.coe_eq_coe']
  apply pathComponent_subset_component x
  exact ⟨⟨Γ, hΓ0, rfl⟩⟩

/-- Trivial monodromy (at every point) separates two points of the chosen
fiber into different connected components.  Repaired 2026-10-14 (lemma-2
counterexample): monodromy trivial only at `e` is not enough — add a connected
two-sheet cover as a second summand. -/
-- BEGIN SEAT AREA
theorem apm_t02a01_fiber_injective_on_components
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace B] [LocPathConnectedSpace B]
    (q : E → B) (hq : IsCoveringMap q) (e : E)
    (hmono : ∀ (x : E) (γ : FundamentalGroup B (q x)),
      hq.monodromy γ ⟨x, rfl⟩ = ⟨x, rfl⟩) :
    Function.Injective
      (fun x : q ⁻¹' {q e} => (x.1 : ConnectedComponents E)) := by
  sorry
-- END SEAT AREA

/-- LIBRARY (covering monodromy): a path-connected base with trivial
monodromy has one connected component per point of a fiber. -/
theorem apm_t02a01_components_equiv_fiber
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace B] [LocPathConnectedSpace B]
    (q : E → B) (hq : IsCoveringMap q)
    (e : E)
    (hmono : ∀ (x : E) (γ : FundamentalGroup B (q x)),
      hq.monodromy γ ⟨x, rfl⟩ = ⟨x, rfl⟩) :
    Nonempty (ConnectedComponents E ≃ q ⁻¹' {q e}) := by
  let f : q ⁻¹' {q e} → ConnectedComponents E := fun x => x.1
  have hf : Function.Bijective f :=
    ⟨apm_t02a01_fiber_injective_on_components q hq e hmono,
      apm_t02a01_component_meets_fiber q hq e⟩
  exact ⟨(Equiv.ofBijective f hf).symm⟩

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
  let f : ZMod n → (apm_t02a01_restrictedCover p ⁻¹'
      {apm_t02a01_restrictedCover p x}) := fun z =>
    ⟨⟨deck z x.1, by
      change p (deck z x.1) ∈ apm_t02a01_boundary
      rw [hdeck_over]
      exact x.2⟩, by
        apply Subtype.ext
        exact hdeck_over z x.1⟩
  have hf_injective : Function.Injective f := by
    intro z w hzw
    have hz : deck z x.1 = (f w).1.1 := by
      simpa [f] using congrArg (fun y => y.1.1) hzw
    have hw : deck w x.1 = (f w).1.1 := by
      rfl
    obtain ⟨u, hu, huniq⟩ := hdeck_transitive x.1 (f w).1.1 (by
      change p x.1 = p (deck w x.1)
      symm
      exact hdeck_over w x.1)
    exact (huniq z hz).trans (huniq w hw).symm
  have hf_surjective : Function.Surjective f := by
    intro y
    have hpy : p x.1 = p y.1.1 := by
      have h := congrArg Subtype.val y.2
      exact h.symm
    obtain ⟨z, hz, _⟩ := hdeck_transitive x.1 y.1.1 hpy
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hz
  let e : ZMod n ≃ (apm_t02a01_restrictedCover p ⁻¹'
      {apm_t02a01_restrictedCover p x}) :=
    Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  rw [← Nat.card_congr e]
  exact Nat.card_zmod n

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
    (apm_t02a01_restrictedCover p) hcov e hmono
  rw [Nat.card_congr equiv]
  exact apm_t02a01_fiber_card p n deck hdeck_over hdeck_transitive e

#print axioms apm_t02a01
