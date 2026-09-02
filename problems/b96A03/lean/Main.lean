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

noncomputable def apmAssociateScalar {F n : Type*} [Field F] [Fintype n]
    (G : Subgroup (MvPolynomial n F ≃ₐ[F] MvPolynomial n F))
    (π : MvPolynomial n F) (hπ : π ≠ 0) (g : apmAssociateStabilizer G π) : Fˣ :=
  Classical.choose (apmAssociated_eq_C_mul_unique hπ g.property)

lemma apmAssociateScalar_spec {F n : Type*} [Field F] [Fintype n]
    (G : Subgroup (MvPolynomial n F ≃ₐ[F] MvPolynomial n F))
    (π : MvPolynomial n F) (hπ : π ≠ 0) (g : apmAssociateStabilizer G π) :
    g.1.1 π = MvPolynomial.C (apmAssociateScalar G π hπ g : F) * π :=
  (Classical.choose_spec (apmAssociated_eq_C_mul_unique hπ g.property)).1

noncomputable def apmAssociateCharacter {F n : Type*} [Field F] [Fintype n]
    (G : Subgroup (MvPolynomial n F ≃ₐ[F] MvPolynomial n F))
    (π : MvPolynomial n F) (hπ : π ≠ 0) : apmAssociateStabilizer G π →* Fˣ where
  toFun := apmAssociateScalar G π hπ
  map_one' := by
    symm
    apply (Classical.choose_spec (apmAssociated_eq_C_mul_unique hπ
      (show Associated ((1 : apmAssociateStabilizer G π).1.1 π) π from (1 : apmAssociateStabilizer G π).property))).2
    simp
  map_mul' := by
    intro g h
    symm
    apply (Classical.choose_spec (apmAssociated_eq_C_mul_unique hπ (g * h).property)).2
    rw [show (g * h).1.1 π = g.1.1 (h.1.1 π) by rfl]
    rw [apmAssociateScalar_spec G π hπ h, map_mul,
      apmAssociateScalar_spec G π hπ g]
    have hc : g.1.1 (MvPolynomial.C (apmAssociateScalar G π hπ h : F)) =
        MvPolynomial.C (apmAssociateScalar G π hπ h : F) := by
      rw [← MvPolynomial.algebraMap_eq]
      exact g.1.1.commutes _
    rw [hc]
    simp [mul_comm, mul_left_comm]

lemma apmOrbitProduct_invariant {F n : Type*} [Field F] [Fintype n]
    (G : Subgroup (MvPolynomial n F ≃ₐ[F] MvPolynomial n F)) [Fintype G]
    (π : MvPolynomial n F) (g : G) :
    g.1 (apmOrbitProduct G π) = apmOrbitProduct G π := by
  classical
  unfold apmOrbitProduct
  simp only [map_prod]
  have himage : Finset.univ.image (fun h : G ↦ g.1 (h.1 π)) =
      Finset.univ.image (fun h : G ↦ h.1 π) := by
    ext δ
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨g * h, rfl⟩
    · rintro ⟨h, rfl⟩
      refine ⟨g⁻¹ * h, ?_⟩
      change ((g * (g⁻¹ * h)).1 : MvPolynomial n F ≃ₐ[F] MvPolynomial n F) π = h.1 π
      rw [mul_inv_cancel_left]
  let S := Finset.univ.image (fun h : G ↦ h.1 π)
  change S.prod (fun δ ↦ g.1 δ) = S.prod id
  have hS : S.image (fun δ ↦ g.1 δ) = S := by
    rw [Finset.image_image]
    exact himage
  have hp := congrArg (fun T : Finset (MvPolynomial n F) ↦ T.prod id) hS
  dsimp only at hp
  rw [Finset.prod_image] at hp
  · exact hp
  · exact fun _ _ _ _ hab ↦ g.1.injective hab

set_option synthInstance.maxHeartbeats 100000 in
lemma apmOrbit_eq_of_associated {F n : Type*} [Field F] [Fintype n]
    (G : Subgroup (MvPolynomial n F ≃ₐ[F] MvPolynomial n F))
    (π : MvPolynomial n F)
    (hdich : ∀ g : G, g.1 π = π ∨ ¬Associated (g.1 π) π)
    (g h : G) (ha : Associated (g.1 π) (h.1 π)) : g.1 π = h.1 π := by
  have ha' := Associated.map h⁻¹.1 ha
  have hk : (h⁻¹ * g).1 π = π ∨ ¬Associated ((h⁻¹ * g).1 π) π := hdich (h⁻¹ * g)
  have hassoc : Associated ((h⁻¹ * g).1 π) π := by
    simpa using ha'
  rcases hk with heq | hna
  · have := congrArg h.1 heq
    simpa using this
  · exact (hna hassoc).elim

lemma apmOrbit_countP_le_one {F n : Type*} [Field F] [Fintype n]
    [DecidableEq F] [DecidableEq n]
    [∀ a : MvPolynomial n F, DecidablePred (Associated a)]
    (G : Subgroup (MvPolynomial n F ≃ₐ[F] MvPolynomial n F)) [Fintype G]
    (π a : MvPolynomial n F)
    (hdich : ∀ g : G, g.1 π = π ∨ ¬Associated (g.1 π) π) :
    (Finset.univ.image (fun g : G ↦ g.1 π)).val.countP (Associated a) ≤ 1 := by
  classical
  let S := Finset.univ.image (fun g : G ↦ g.1 π)
  change S.val.countP (Associated a) ≤ 1
  by_cases hz : S.val.countP (Associated a) = 0
  · omega
  · obtain ⟨b, hbS, hab⟩ := Multiset.countP_pos.mp (Nat.pos_of_ne_zero hz)
    have hpred : ∀ x ∈ S.val, Associated a x ↔ b = x := by
      intro x hxS
      constructor
      · intro hax
        have hbx : Associated b x := hab.symm.trans hax
        change b ∈ S at hbS
        change x ∈ S at hxS
        simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hbS hxS
        obtain ⟨g, rfl⟩ := hbS
        obtain ⟨h, rfl⟩ := hxS
        exact apmOrbit_eq_of_associated G π hdich g h hbx
      · rintro rfl
        exact hab
    rw [Multiset.countP_congr rfl (fun x hx ↦ propext (hpred x hx))]
    exact Multiset.nodup_iff_count_le_one.mp S.nodup b

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
      intro hpure
      constructor
      · intro g π hprime
        by_cases ha : Associated (g.1 π) π
        · left
          let s : apmAssociateStabilizer G π := ⟨g, ha⟩
          have hs := apmAssociateScalar_spec G π hprime.ne_zero s
          have hone := hpure (apmAssociateStabilizer G π)
            (apmAssociateCharacter G π hprime.ne_zero) s
          change apmAssociateScalar G π hprime.ne_zero s = 1 at hone
          rw [hone] at hs
          simpa [s] using hs
        · right
          exact ⟨irreducible_iff_prime.mp ((MulEquiv.irreducible_iff g.1).mpr
            (irreducible_iff_prime.mpr hprime)), ha⟩
      · -- Remaining orbit-product package: invariance, divisibility into
        -- invariant multiples, and primality after descent to `apmFixedRing`.
        intro π hprime
        have hdiv : ∀ α : MvPolynomial n F, (∀ g : G, g.1 α = α) →
            π ∣ α → apmOrbitProduct G π ∣ α := by
          intro α hinv hpid
          classical
          have hdich : ∀ g : G, g.1 π = π ∨ ¬Associated (g.1 π) π := by
            intro g
            by_cases ha : Associated (g.1 π) π
            · left
              let s : apmAssociateStabilizer G π := ⟨g, ha⟩
              have hs := apmAssociateScalar_spec G π hprime.ne_zero s
              have hone := hpure (apmAssociateStabilizer G π)
                (apmAssociateCharacter G π hprime.ne_zero) s
              change apmAssociateScalar G π hprime.ne_zero s = 1 at hone
              rw [hone] at hs
              simpa [s] using hs
            · exact Or.inr ha
          let S := Finset.univ.image (fun g : G ↦ g.1 π)
          have hprod : S.val.prod ∣ α := Multiset.prod_primes_dvd α
            (fun a ha ↦ by
              change a ∈ S at ha
              simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at ha
              obtain ⟨g, rfl⟩ := ha
              exact irreducible_iff_prime.mp ((MulEquiv.irreducible_iff g.1).mpr
                (irreducible_iff_prime.mpr hprime)))
            (fun a ha ↦ by
              change a ∈ S at ha
              simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at ha
              obtain ⟨g, rfl⟩ := ha
              have hmapped : g.1 π ∣ g.1 α := map_dvd g.1 hpid
              rwa [hinv g] at hmapped)
            (apmOrbit_countP_le_one G π · hdich)
          rw [Finset.prod_val] at hprod
          simpa [apmOrbitProduct, S] using hprod
        refine ⟨apmOrbitProduct_invariant G π, hdiv, ?_⟩
        · -- This final descent uses the preceding divisibility statement on
          -- either invariant factor after projecting a factorization in the
          -- fixed subring to the ambient polynomial ring.
          let hfix := apmOrbitProduct_invariant G π
          refine ⟨hfix, ?_⟩
          have hnonzero : apmOrbitProduct G π ≠ 0 := by
            classical
            unfold apmOrbitProduct
            rw [Finset.prod_ne_zero_iff]
            intro a ha
            simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha
            obtain ⟨g, rfl⟩ := ha
            intro hz
            apply hprime.ne_zero
            apply g.1.injective
            simpa using hz
          refine ⟨fun hz ↦ hnonzero (congrArg Subtype.val hz), ?_, ?_⟩
          · intro hu
            have hu' : IsUnit (apmOrbitProduct G π) :=
              hu.map (apmFixedRing G).subtype
            have hpi : π ∣ apmOrbitProduct G π := by
              classical
              unfold apmOrbitProduct
              apply Finset.dvd_prod_of_mem id
              exact Finset.mem_image.mpr ⟨(1 : G), Finset.mem_univ _, by simp⟩
            exact hprime.not_unit (isUnit_of_dvd_unit hpi hu')
          · intro a b hpab
            have hpab' : apmOrbitProduct G π ∣ (a : MvPolynomial n F) * b := by
              obtain ⟨c, hc⟩ := hpab
              exact ⟨c, congrArg Subtype.val hc⟩
            have hpi : π ∣ apmOrbitProduct G π := by
              classical
              unfold apmOrbitProduct
              apply Finset.dvd_prod_of_mem id
              exact Finset.mem_image.mpr ⟨(1 : G), Finset.mem_univ _, by simp⟩
            rcases hprime.dvd_or_dvd (hpi.trans hpab') with ha | hb
            · left
              obtain ⟨c, hc⟩ := hdiv a a.property ha
              refine ⟨⟨c, ?_⟩, Subtype.ext ?_⟩
              · intro g
                apply mul_left_cancel₀ hnonzero
                calc
                  apmOrbitProduct G π * g.1 c =
                      g.1 (apmOrbitProduct G π * c) := by rw [map_mul, hfix g]
                  _ = g.1 a := by rw [← hc]
                  _ = a := a.property g
                  _ = apmOrbitProduct G π * c := hc
              · exact hc
            · right
              obtain ⟨c, hc⟩ := hdiv b b.property hb
              refine ⟨⟨c, ?_⟩, Subtype.ext ?_⟩
              · intro g
                apply mul_left_cancel₀ hnonzero
                calc
                  apmOrbitProduct G π * g.1 c =
                      g.1 (apmOrbitProduct G π * c) := by rw [map_mul, hfix g]
                  _ = g.1 b := by rw [← hc]
                  _ = b := b.property g
                  _ = apmOrbitProduct G π * c := hc
              · exact hc
