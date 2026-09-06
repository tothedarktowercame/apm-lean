import Mathlib

noncomputable section

/-!
# APM b96A03

## Statement repairs

None.

## Encoding notes

The polynomial ring is the genuine `MvPolynomial (Fin n) F`. The orbit product
uses `Finset.image`, so repeated orbit elements are removed exactly as required.
The invariant ring is defined as the actual fixed-element subring.
-/

def apmFPure (F G : Type*) [Field F] [Group G] : Prop :=
  ∀ (H : Subgroup G) (chi : H →* Fˣ) (h : H), chi h = 1

noncomputable def apmOrbitProduct {F n : Type*} [Field F] [Fintype n]
    (G : Subgroup (MvPolynomial n F ≃ₐ[F] MvPolynomial n F)) [Fintype G]
    (π : MvPolynomial n F) : MvPolynomial n F := by
  classical
  exact ∏ δ ∈ Finset.univ.image (fun g : G ↦ g.1 π), δ

def apmFixedRing {F n : Type*} [Field F] [Fintype n]
    (G : Subgroup (MvPolynomial n F ≃ₐ[F] MvPolynomial n F)) :
    Subring (MvPolynomial n F) where
  carrier := {a | ∀ g : G, g.1 a = a}
  zero_mem' := fun g ↦ map_zero g.1
  one_mem' := fun g ↦ map_one g.1
  add_mem' ha hb g := by rw [map_add, ha g, hb g]
  neg_mem' ha g := by rw [map_neg, ha g]
  mul_mem' ha hb g := by rw [map_mul, ha g, hb g]

set_option synthInstance.maxHeartbeats 100000 in
def apmAssociateStabilizer {F n : Type*} [Field F] [Fintype n]
    (G : Subgroup (MvPolynomial n F ≃ₐ[F] MvPolynomial n F))
    (π : MvPolynomial n F) : Subgroup G where
  carrier := {g | Associated (g.1 π) π}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    exact (Associated.map g.1 hh).trans hg
  inv_mem' := by
    intro g hg
    have hmap := Associated.map
      (↑(g⁻¹) : MvPolynomial n F ≃ₐ[F] MvPolynomial n F) hg
    simpa using hmap.symm

@[simp] lemma apmAssociateStabilizer_mem {F n : Type*} [Field F] [Fintype n]
    (G : Subgroup (MvPolynomial n F ≃ₐ[F] MvPolynomial n F))
    (π : MvPolynomial n F) (g : G) :
    g ∈ apmAssociateStabilizer G π ↔ Associated (g.1 π) π := Iff.rfl

lemma apmAssociated_eq_C_mul_unique {F n : Type*} [Field F]
    {x y : MvPolynomial n F} (hy : y ≠ 0) (hxy : Associated x y) :
    ∃! c : Fˣ, x = MvPolynomial.C (c : F) * y := by
  obtain ⟨u, hu⟩ := hxy
  have hui : IsUnit ((u⁻¹ : (MvPolynomial n F)ˣ) : MvPolynomial n F) := Units.isUnit _
  obtain ⟨r, hr, hur⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced (P :=
      ((u⁻¹ : (MvPolynomial n F)ˣ) : MvPolynomial n F))).mp hui
  let c : Fˣ := hr.unit
  have hc : x = MvPolynomial.C (c : F) * y := by
    calc
      x = (x * (u : MvPolynomial n F)) *
          ((u⁻¹ : (MvPolynomial n F)ˣ) : MvPolynomial n F) := by simp
      _ = y * ((u⁻¹ : (MvPolynomial n F)ˣ) : MvPolynomial n F) := by rw [hu]
      _ = MvPolynomial.C (c : F) * y := by
        rw [hur, ← IsUnit.unit_spec hr]
        simp [c, mul_comm]
  refine ⟨c, hc, ?_⟩
  · intro d hd
    apply Units.ext
    apply MvPolynomial.C_injective n F
    apply mul_right_cancel₀ hy
    exact hd.symm.trans hc

/-! ## Attempt 2 (student) -/

section Attempt2

variable {F n : Type*} [Field F] [Fintype n]
  (G : Subgroup (MvPolynomial n F ≃ₐ[F] MvPolynomial n F)) [Fintype G]

lemma coeMulApp (g h : G) (π : MvPolynomial n F) :
    (g * h : G).1 π = g.1 (h.1 π) := by
  simp [Subgroup.coe_mul, AlgEquiv.mul_apply]

lemma oneApp (x : MvPolynomial n F) : ((1 : G) : MvPolynomial n F ≃ₐ[F] MvPolynomial n F) x = x := by
  simp

lemma appC (e : MvPolynomial n F ≃ₐ[F] MvPolynomial n F) (c : F) :
    e (MvPolynomial.C c) = MvPolynomial.C c := by
  rw [show (MvPolynomial.C c) = algebraMap F (MvPolynomial n F) c from rfl, AlgEquiv.commutes]

/-- The coefficient character of the associate stabilizer. -/
noncomputable def apmCoefChar (hπ0 : π ≠ 0) (k : apmAssociateStabilizer G π) : Fˣ :=
  (apmAssociated_eq_C_mul_unique hπ0
    ((apmAssociateStabilizer_mem G π (k : G)).mp k.2)).choose

lemma apmCoefChar_spec (hπ0 : π ≠ 0) (k : apmAssociateStabilizer G π) :
    ((k : G) : MvPolynomial n F ≃ₐ[F] MvPolynomial n F) π
      = MvPolynomial.C (apmCoefChar G hπ0 k : F) * π :=
  ((apmAssociated_eq_C_mul_unique hπ0
    ((apmAssociateStabilizer_mem G π (k : G)).mp k.2)).choose_spec).1

lemma stabilizerTrivial (hFP : apmFPure F G) {π : MvPolynomial n F} (hπ : Prime π)
    {g : G} (hg : Associated (g.1 π) π) : g.1 π = π := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hmul : ∀ a b : apmAssociateStabilizer G π,
      apmCoefChar G hπ0 (a * b) = apmCoefChar G hπ0 b * apmCoefChar G hπ0 a := by
    intro a b
    have hA := apmCoefChar_spec G hπ0 a
    have hB := apmCoefChar_spec G hπ0 b
    have hAB := apmCoefChar_spec G hπ0 (a * b)
    have e1 : ((↑(a * b) : G) : MvPolynomial n F ≃ₐ[F] MvPolynomial n F) π
        = MvPolynomial.C ((apmCoefChar G hπ0 b : F) * (apmCoefChar G hπ0 a : F)) * π := by
      have hm : (((a * b : apmAssociateStabilizer G π) : G))
          = ((a : G)) * ((b : G)) :=
        map_mul (Subgroup.subtype (apmAssociateStabilizer G π)) a b
      have e0 : (((a * b : apmAssociateStabilizer G π) : G) :
          MvPolynomial n F ≃ₐ[F] MvPolynomial n F) π
          = ((a : G) : MvPolynomial n F ≃ₐ[F] MvPolynomial n F)
            (((b : G) : MvPolynomial n F ≃ₐ[F] MvPolynomial n F) π) := by
        rw [hm, Subgroup.coe_mul, AlgEquiv.mul_apply]
      rw [e0, hB, map_mul, appC, hA, ← mul_assoc, ← MvPolynomial.C_mul]
    have hC := MvPolynomial.C_injective n F (mul_right_cancel₀ hπ0 (e1.symm.trans hAB))
    apply Units.ext
    simpa [Units.val_mul] using hC.symm
  let chi : apmAssociateStabilizer G π →* Fˣ :=
    { toFun := apmCoefChar G hπ0
      map_one' := by
        have h1app : ((↑(1 : apmAssociateStabilizer G π) : G) :
            MvPolynomial n F ≃ₐ[F] MvPolynomial n F) π = π := by
          have hm : ((1 : apmAssociateStabilizer G π) : G) = (1 : G) :=
            map_one (Subgroup.subtype (apmAssociateStabilizer G π))
          rw [hm, oneApp]
        have e0 := apmCoefChar_spec G hπ0 (1 : apmAssociateStabilizer G π)
        rw [h1app] at e0
        exact Units.ext (MvPolynomial.C_injective n F
          (mul_right_cancel₀ hπ0 (by rw [← e0]; simp)))
      map_mul' := by
        intro a b
        rw [hmul a b, mul_comm] }
  have htriv := hFP (apmAssociateStabilizer G π) chi ⟨g, hg⟩
  have hspec := apmCoefChar_spec G hπ0 ⟨g, hg⟩
  have hchi : apmCoefChar G hπ0 ⟨g, hg⟩ = 1 := htriv
  rw [hspec, hchi]
  simp

/-- Purity + primality: associated orbit images are equal. -/
lemma assocOrbitEq (hFP : apmFPure F G) {π : MvPolynomial n F} (hπ : Prime π)
    {g h : G} (ha : Associated (g.1 π) (h.1 π)) : g.1 π = h.1 π := by
  have h1 : ((h⁻¹ * g : G).1) π = π := by
    refine stabilizerTrivial G hFP hπ ?_
    have hmap := Associated.map ((h⁻¹ : G) : MvPolynomial n F ≃ₐ[F] MvPolynomial n F) ha
    have e1 : ((h⁻¹ : G).1) (g.1 π) = ((h⁻¹ * g : G).1) π := (coeMulApp G (h⁻¹) g π).symm
    have e2 : ((h⁻¹ : G).1) (h.1 π) = π := by
      rw [← coeMulApp G (h⁻¹) h π, inv_mul_cancel, oneApp]
    rw [e1, e2] at hmap
    exact hmap
  calc g.1 π = ((h * (h⁻¹ * g) : G).1) π := by rw [show h * (h⁻¹ * g) = g from by
        rw [mul_inv_cancel_left]]
  _ = (h.1) (((h⁻¹ * g : G).1) π) := coeMulApp G h (h⁻¹ * g) π
  _ = h.1 π := by rw [h1]

lemma orbitPrime {π : MvPolynomial n F} (hπ : Prime π) (g : G) : Prime (g.1 π) := by
  rw [← irreducible_iff_prime] at hπ ⊢
  exact (MulEquiv.irreducible_iff g.1).mpr hπ

lemma orbitInv (g₀ : G) (π : MvPolynomial n F) :
    g₀.1 (apmOrbitProduct G π) = apmOrbitProduct G π := by
  classical
  simp only [apmOrbitProduct]
  set S : Finset (MvPolynomial n F) := Finset.univ.image (fun g : G ↦ g.1 π) with hSdef
  have hinj : ∀ δ ∈ S, ∀ ε ∈ S,
      g₀.1 δ = g₀.1 ε → δ = ε := fun _ _ _ _ he => g₀.1.toEquiv.injective he
  have hcl : ∀ (k : G), ∀ δ ∈ S, k.1 δ ∈ S := by
    intro k δ hδ
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hδ
    exact Finset.mem_image.2 ⟨k * g, Finset.mem_univ _, coeMulApp G k g π⟩
  have hSinv : S.image (fun δ => g₀.1 δ) = S := by
    refine Finset.ext fun δ => ?_
    constructor
    · intro hmem
      obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.1 hmem
      exact hcl g₀ ε hε
    · intro hδ
      have hmem : ((g₀⁻¹ : G) : MvPolynomial n F ≃ₐ[F] MvPolynomial n F) δ ∈ S :=
        hcl (g₀⁻¹) δ hδ
      refine Finset.mem_image.2 ⟨_, hmem, ?_⟩
      rw [← coeMulApp G g₀ (g₀⁻¹) δ, mul_inv_cancel, oneApp]
  rw [map_prod, ← Finset.prod_image (f := fun x => x) (g := fun δ => g₀.1 δ)
    (fun a ha b hb hab => hinj a ha b hb hab), hSinv]

lemma orbitProdDvd (hFP : apmFPure F G) {π a : MvPolynomial n F} (hπ : Prime π)
    (ha : ∀ g : G, g.1 a = a) (hdvd : π ∣ a) : apmOrbitProduct G π ∣ a := by
  classical
  simp only [apmOrbitProduct]
  set S : Finset (MvPolynomial n F) := Finset.univ.image (fun g : G ↦ g.1 π) with hSdef
  have hprimes : ∀ q ∈ S, Prime q := by
    intro q hq
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hq
    exact orbitPrime G hπ g
  have hdvds : ∀ q ∈ S, q ∣ a := by
    intro q hq
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hq
    rw [← ha g]
    exact map_dvd ((g : MvPolynomial n F ≃ₐ[F] MvPolynomial n F)) hdvd
  have hcount : ∀ x : MvPolynomial n F, S.val.countP (Associated x) ≤ 1 := by
    intro x
    have hOrbEq : ∀ (y : MvPolynomial n F), y ∈ S → ∀ (z : MvPolynomial n F), z ∈ S →
        Associated y z → y = z := by
      intro y hy z hz ha
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 hz
      exact assocOrbitEq G hFP hπ ha
    by_cases hx : ∃ δ ∈ S, Associated δ x
    · obtain ⟨δ, hδS, hδ⟩ := hx
      have hfe : S.val.filter (Associated x) = S.val.filter (· = δ) := by
        refine Multiset.filter_congr fun y hyS => ?_
        constructor
        · intro hy
          exact hOrbEq y (by simpa using hyS) δ hδS (hy.symm.trans hδ.symm)
        · intro hy
          exact hδ.symm.trans (hy ▸ Associated.refl δ)
      rw [Multiset.countP_eq_card_filter, hfe]
      have hflip : S.val.filter (· = δ) = S.val.filter (δ = ·) :=
        Multiset.filter_congr fun y _ => by constructor <;> intro h <;> exact eq_comm.mp h
      rw [hflip, ← Multiset.count_eq_card_filter_eq]
      exact Multiset.nodup_iff_count_le_one.1 (Finset.nodup S) δ
    · have h0 : S.val.countP (Associated x) = 0 :=
        Multiset.countP_eq_zero.2 (fun y hy hyx => hx ⟨y, hy, hyx.symm⟩)
      exact (Nat.le_of_eq h0).trans (Nat.zero_le 1)
  rw [Finset.prod_eq_multiset_prod,
    show Multiset.map (fun δ => δ) S.val = S.val from Multiset.map_id S.val]
  exact Multiset.prod_primes_dvd a (fun q hq => hprimes q (by simpa using hq))
    (fun q hq => hdvds q (by simpa using hq)) hcount

lemma orbitProdPrime (hFP : apmFPure F G) {π : MvPolynomial n F} (hπ : Prime π) :
    ∃ hfix : ∀ g : G, g.1 (apmOrbitProduct G π) = apmOrbitProduct G π,
      Prime (⟨apmOrbitProduct G π, hfix⟩ : apmFixedRing G) := by
  classical
  have hfix : ∀ g : G, g.1 (apmOrbitProduct G π) = apmOrbitProduct G π :=
    fun g => orbitInv G g π
  refine ⟨hfix, ?_⟩
  have hπS : π ∈ Finset.univ.image (fun g : G ↦ g.1 π) :=
    Finset.mem_image.2 ⟨1, Finset.mem_univ _, oneApp G π⟩
  have hdvdπ : π ∣ apmOrbitProduct G π :=
    Finset.dvd_prod_of_mem (f := fun δ => δ) hπS
  have hOP0 : apmOrbitProduct G π ≠ 0 := by
    rw [apmOrbitProduct]
    intro h0
    obtain ⟨δ, hδ, hδ0⟩ := Finset.prod_eq_zero_iff.1 h0
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hδ
    exact (orbitPrime G hπ g).ne_zero hδ0
  have hOP0' : (⟨apmOrbitProduct G π, hfix⟩ : apmFixedRing G) ≠ 0 := by
    intro h0
    exact hOP0 (by
      have := congrArg (fun t : apmFixedRing G => (t : MvPolynomial n F)) h0
      simpa using this)
  refine ⟨hOP0', ?_, ?_⟩
  · intro hu
    obtain ⟨v, hv⟩ : ∃ v : apmFixedRing G,
        (⟨apmOrbitProduct G π, hfix⟩ : apmFixedRing G) * v = 1 :=
      ⟨hu.unit.inv, hu.unit.mul_inv⟩
    have hunit : apmOrbitProduct G π * (v : MvPolynomial n F) = 1 := by
      simpa [Subring.coe_mul, Subring.coe_one] using
        congrArg (fun t : apmFixedRing G => (t : MvPolynomial n F)) hv
    exact hπ.not_unit (isUnit_of_dvd_one (dvd_trans hdvdπ ⟨(v : MvPolynomial n F), hunit.symm⟩))
  · intro x y hxy
    obtain ⟨z, hz⟩ := hxy
    have hz' : (x : MvPolynomial n F) * (y : MvPolynomial n F)
        = apmOrbitProduct G π * (z : MvPolynomial n F) := by
      have := congrArg (fun t : apmFixedRing G => (t : MvPolynomial n F)) hz
      simpa [Subring.coe_mul] using this
    have hx : ∀ g : G, g.1 (x : MvPolynomial n F) = (x : MvPolynomial n F) := x.2
    have hy : ∀ g : G, g.1 (y : MvPolynomial n F) = (y : MvPolynomial n F) := y.2
    have subDvd : ∀ (w : MvPolynomial n F) (hw : ∀ g : G, g.1 w = w) (hdw : π ∣ w),
        (⟨apmOrbitProduct G π, hfix⟩ : apmFixedRing G) ∣ ⟨w, fun g => hw g⟩ := by
      intro w hw hdw
      obtain ⟨k, hk⟩ := orbitProdDvd G hFP hπ hw hdw
      have hkfix : ∀ g : G, g.1 k = k := by
        intro g
        have e1 : g.1 (apmOrbitProduct G π * k) = apmOrbitProduct G π * g.1 k := by
          rw [map_mul, hfix g]
        have e2 : g.1 (apmOrbitProduct G π * k) = g.1 w := by rw [hk]
        have e3 : g.1 w = w := hw g
        have e4 : w = apmOrbitProduct G π * k := hk
        exact mul_left_cancel₀ hOP0 (e1.symm.trans (e2.trans (e3.trans e4)))
      exact ⟨⟨k, hkfix⟩, Subtype.ext hk⟩
    rcases hπ.dvd_or_dvd (hdvdπ.trans ⟨_, hz'⟩) with hd | hd
    · exact Or.inl (subDvd _ hx hd)
    · exact Or.inr (subDvd _ hy hd)

end Attempt2

theorem apm_b96a03 :
    (∀ (G : Type*) [Group G] [Fintype G], Odd (Fintype.card G) →
      apmFPure ℚ G) ∧
    (∀ (F : Type*) [Field F] (n : Type*) [Fintype n]
      (G : Subgroup (MvPolynomial n F ≃ₐ[F] MvPolynomial n F)) [Fintype G],
      (∀ (g : G) (α : MvPolynomial n F), Prime (g.1 α) ↔ Prime α) ∧
      (apmFPure F G →
        (∀ (g : G) (π : MvPolynomial n F), Prime π →
          g.1 π = π ∨ (Prime (g.1 π) ∧ ¬Associated (g.1 π) π)) ∧
        (∀ π : MvPolynomial n F, Prime π →
          (∀ g : G, g.1 (apmOrbitProduct G π) = apmOrbitProduct G π) ∧
          (∀ α : MvPolynomial n F, (∀ g : G, g.1 α = α) →
            π ∣ α → apmOrbitProduct G π ∣ α) ∧
          ∃ hfix : ∀ g : G, g.1 (apmOrbitProduct G π) = apmOrbitProduct G π,
            Prime (⟨apmOrbitProduct G π, hfix⟩ : apmFixedRing G)))) := by
  constructor
  · intro G _ _ hodd H chi h
    have hh : h ^ Fintype.card G = 1 := by
      ext
      exact pow_card_eq_one (x := (h : G))
    have hchi := congrArg chi hh
    apply Units.ext
    apply hodd.pow_injective
    simpa using congrArg Units.val hchi
  · intro F _ n _ G _
    constructor
    · intro g α
      rw [← irreducible_iff_prime, ← irreducible_iff_prime]
      exact MulEquiv.irreducible_iff g.1
    · -- CLOSER HOP 1 boundary: searched `MulEquiv.irreducible_iff`,
      -- `MvPolynomial.isUnit_iff_eq_C_of_isReduced`, `MulAction.stabilizer`,
      -- `Finset.prod_bij`, `Prime.dvd_finset_prod_iff`, and
      -- `Finset.prod_primes_dvd`.  The last theorem assumes
      -- `Subsingleton Rˣ`, so it does not apply to `MvPolynomial n F`, whose
      -- units are the nonzero constants classified by the MvPolynomial lemma.
      -- New progress: the immediately preceding theorem
      -- `Multiset.prod_primes_dvd` does *not* assume `Subsingleton Rˣ`.
      -- Instead it accepts exactly the orbit fact needed here:
      -- `∀ a, s.countP (Associated a) ≤ 1`.  Thus the product-divisibility
      -- step can be routed around the unusable finset theorem once purity has
      -- shown that associated orbit elements are equal; no custom UFD
      -- factorization argument is required.
      --
      -- The remaining implication therefore requires a custom subgroup of
      -- automorphisms sending `π` to an associate, extraction and uniqueness
      -- of its coefficient character into `Fˣ`.  After purity trivializes
      -- that character, orbit reindexing supplies invariance and the
      -- `countP` hypothesis for `Multiset.prod_primes_dvd`; cancellation then
      -- transfers primality to the custom fixed subring.  The open technical
      -- bridge is now confined to constructing that subgroup/character and
      -- proving the orbit's `countP` uniqueness condition.
      --
      -- Closer hop 2 extracts and proves the subgroup half as
      -- `apmAssociateStabilizer G π`: its carrier is precisely the
      -- automorphisms whose image of `π` is associated to `π`, and closure
      -- follows from `Associated.map`, transitivity, and inverse transport.
      -- The remaining character half must choose, for each subgroup element,
      -- the unit relating `g π` and `π`, use
      -- `MvPolynomial.isUnit_iff_eq_C_of_isReduced` to express it as a unique
      -- nonzero constant, and prove multiplicativity by canceling the prime
      -- `π`. No packaged `Associates` action or coefficient-character
      -- constructor was found, so that coherent-choice proof and the
      -- downstream `countP` assembly remain open.
      --
      -- Closer hop 3 proves `apmAssociated_eq_C_mul_unique`: for every
      -- associate relation `Associated x y` with `y ≠ 0`, there is a unique
      -- `c : Fˣ` such that `x = C c * y`. This uses
      -- `MvPolynomial.isUnit_iff_eq_C_of_isReduced`, inversion of the unit
      -- witnessing `Associated`, `MvPolynomial.C_injective`, and cancellation
      -- by `y`. Thus scalar extraction and uniqueness are now closed. The
      -- remaining coherent-choice step is to define these scalars on
      -- `apmAssociateStabilizer G π` and prove multiplicativity from
      -- uniqueness; after purity trivializes that homomorphism, orbit
      -- reindexing, `Multiset.prod_primes_dvd` count uniqueness, and the
      -- fixed-subring primality argument remain.
      -- Attempt-2 student assembly of the residual.
      intro hFP
      constructor
      · intro g π hπ
        by_cases hg : Associated (g.1 π) π
        · exact Or.inl (stabilizerTrivial G hFP hπ hg)
        · exact Or.inr ⟨orbitPrime G hπ g, hg⟩
      · intro π hπ
        exact ⟨fun g => orbitInv G g π,
          fun α ha hdvd => orbitProdDvd G hFP hπ ha hdvd,
          orbitProdPrime G hFP hπ⟩