import Mathlib
import ConstructionTargets.Surfaces
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.PolygonSurfaceHomology
import ConstructionTargets.GenusTwoSurfacePiOne
import ConstructionTargets.CoveringMonodromyCosets
import ConstructionTargets.FiniteIndexFreeGroupSchreierRank

/-! # t91A02: no finite cover `N₁₆ → N₈` (blueprint, revision 2026-10-15)

Route: the fundamental group and the first rational Betti number of groups,
`b₁(G) = dim_ℚ Hom(G, ℚ)`.  No Euler characteristic and no `H₂` of a cover is
needed.

* A connected `k`-sheeted cover `E → B` makes `π₁(E)` an index-`k` subgroup of
  `π₁(B)` (banked: `coveringFiberCard_eq_index`).
* `π₁` of any one-vertex polygon quotient is `F_n ⧸ ⟪r⟫`, `n` the number of
  edge orbits, with `r` rationally nonzero iff the attaching degree is nonzero.
* (Reidemeister–Schreier, rank-only form.)  An index-`k` subgroup `H` of
  `F_n ⧸ ⟪r⟫` is `F_{(n-1)k+1} ⧸ ⟪t₁,…,t_m⟫`, `1 ≤ m ≤ k`, each `tᵢ` a
  conjugate of `r` (Schreier rank banked).  Hence
  `(n-1)k + 1 - k ≤ b₁(H)`, and `b₁(H) ≤ (n-1)k` if `r` is rationally nonzero.
* For `N₁₆ → N₈`: `b₁(π₁ N₁₆) = 15`, so `7k + 1 - k ≤ 15 ≤ 7k`, i.e. `k ≤ 2`
  and `k ≥ 3`.

Leaves are generic (any group, any `PairingData`) except the standard
crosscap-data computation.
-/

open ConstructionTargets
open ConstructionTargets.Surfaces
open ConstructionTargets.RationalLefschetz
open ConstructionTargets.PolygonSurfacePiOne
open ConstructionTargets.PolygonSurfaceHomology

noncomputable section

/-! ## Retained from the 2026-10-13 blueprint (proved; unused by the new route) -/

/-- An Euler characteristic represented by the alternating trace in
`HasEulerCharacteristic` is unique. -/
theorem t91A02_hasEulerCharacteristic_unique
    {X : Type} [TopologicalSpace X] {a b : ℚ}
    (ha : HasEulerCharacteristic X a)
    (hb : HasEulerCharacteristic X b) :
    a = b := by
  rcases ha with ⟨hfinite, m, hm, rfl⟩
  rcases hb with ⟨_, n, hn, rfl⟩
  let N := max m n
  have hmN : m + 1 ≤ N + 1 := Nat.add_le_add_right (le_max_left m n) 1
  have hnN : n + 1 ≤ N + 1 := Nat.add_le_add_right (le_max_right m n) 1
  have extend (r : ℕ) (hrN : r + 1 ≤ N + 1)
      (hr : ∀ k, r < k → Subsingleton (Homology X k)) :
      (∑ k ∈ Finset.range (r + 1),
          (-1 : ℚ)^k * LinearMap.trace ℚ (Homology X k)
            (induced (ContinuousMap.id X) k).hom) =
        ∑ k ∈ Finset.range (N + 1),
          (-1 : ℚ)^k * LinearMap.trace ℚ (Homology X k)
            (induced (ContinuousMap.id X) k).hom := by
    apply Finset.sum_subset (Finset.range_mono hrN)
    intro k hkN hkr
    have hrk : r < k := by
      simpa [Finset.mem_range] using hkr
    letI : FiniteDimensional ℚ (Homology X k) := hfinite k
    haveI : Subsingleton (Homology X k) := hr k hrk
    have hz : (induced (ContinuousMap.id X) k).hom = 0 := Subsingleton.elim _ _
    simp [hz]
  exact (extend m hmN hm).trans (extend n hnN hn).symm

/-! ## First rational Betti number of a group -/

/-- `b₁(G) = dim_ℚ Hom(G, ℚ)` (`finrank`, so `0` if infinite-dimensional;
every use below has a finite-dimensionality certificate). -/
def t91A02_b1 (G : Type*) [Group G] : ℕ :=
  Module.finrank ℚ (Additive G →+ ℚ)

/-- Precomposition with a group isomorphism. -/
def t91A02_homCongr {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') :
    (Additive G' →+ ℚ) ≃ₗ[ℚ] (Additive G →+ ℚ) where
  toFun f := f.comp (MulEquiv.toAdditive e).toAddMonoidHom
  invFun f := f.comp (MulEquiv.toAdditive e.symm).toAddMonoidHom
  left_inv f := by
    ext x
    simp
  right_inv f := by
    ext x
    simp
  map_add' f g := by
    ext x
    simp
  map_smul' c f := by
    ext x
    simp

theorem t91A02_b1_congr {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') :
    t91A02_b1 G = t91A02_b1 G' :=
  (t91A02_homCongr e).finrank_eq.symm

theorem t91A02_finiteDimensional_congr {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') [FiniteDimensional ℚ (Additive G' →+ ℚ)] :
    FiniteDimensional ℚ (Additive G →+ ℚ) :=
  (t91A02_homCongr e).finiteDimensional

/-! ## Generic algebra leaves -/

/-- **Leaf A1 (generic).**  `Hom(F_n, ℚ) ≅ ℚⁿ`: finite-dimensional of
dimension `n`.

Route: build the linear equivalence `(Additive (FreeGroup (Fin n)) →+ ℚ) ≃ₗ[ℚ]
(Fin n → ℚ)`, `f ↦ fun i => f (Additive.ofMul (FreeGroup.of i))`, inverse
`v ↦ MonoidHom.toAdditive' (FreeGroup.lift fun i => Multiplicative.ofAdd (v i))`
(or `MonoidHom.toAdditive` with codomain `Additive (Multiplicative ℚ)`);
injectivity by `FreeGroup.ext_hom`.  Then `LinearEquiv.finiteDimensional` and
`LinearEquiv.finrank_eq`, `Module.finrank_fin_fun`.  Edge case `n = 0`:
both sides are zero-dimensional. -/
lemma t91A02_b1_freeGroup (n : ℕ) :
    FiniteDimensional ℚ (Additive (FreeGroup (Fin n)) →+ ℚ) ∧
      t91A02_b1 (FreeGroup (Fin n)) = n := by
  let e : (Additive (FreeGroup (Fin n)) →+ ℚ) ≃ₗ[ℚ] (Fin n → ℚ) :=
    { toFun := fun f i => f (Additive.ofMul (FreeGroup.of i))
      invFun := fun v => MonoidHom.toAdditive
        (FreeGroup.lift (fun i => Multiplicative.ofAdd (v i)))
      left_inv := by
        intro f
        apply AddMonoidHom.ext
        intro x
        change (MonoidHom.toAdditive
          (FreeGroup.lift (fun i => Multiplicative.ofAdd
            (f (Additive.ofMul (FreeGroup.of i)))))) x = f x
        have h : FreeGroup.lift (fun i => Multiplicative.ofAdd
              (f (Additive.ofMul (FreeGroup.of i)))) =
            AddMonoidHom.toMultiplicative f := by
          apply FreeGroup.ext_hom
          intro i
          rw [FreeGroup.lift_apply_of]
          rfl
        exact DFunLike.congr_fun (congrArg MonoidHom.toAdditive h) x
      right_inv := by
        intro v
        funext i
        change (FreeGroup.lift (fun i => Multiplicative.ofAdd (v i)))
          (FreeGroup.of i) = Multiplicative.ofAdd (v i)
        exact FreeGroup.lift_apply_of
      map_add' := by
        intro f g
        funext i
        simp
      map_smul' := by
        intro c f
        funext i
        simp }
  have hfd : FiniteDimensional ℚ (Additive (FreeGroup (Fin n)) →+ ℚ) :=
    e.symm.finiteDimensional
  refine ⟨hfd, ?_⟩
  unfold t91A02_b1
  rw [e.finrank_eq, Module.finrank_fin_fun]

/-- **Leaf A2 (generic).**  Killing a finite set `S` lowers `b₁` by at most
`|S|`, and by at least one if some homomorphism to `ℚ` is nonzero on `S`.

Route: `Hom(G ⧸ ⟪S⟫, ℚ) ≃ₗ[ℚ] ker (ev_S)`, where
`ev_S : Hom(G, ℚ) →ₗ[ℚ] (S → ℚ)`, `φ ↦ fun s => φ (ofMul s)`; forward map is
precomposition with `QuotientGroup.mk'`, inverse uses `QuotientGroup.lift`
(`Subgroup.normalClosure_le_normal` with the kernel of the multiplicative
version of `φ`; `MonoidHom.toAdditive`/`AddMonoidHom.toMultiplicative`).
Rank–nullity (`LinearMap.finrank_range_add_finrank_ker`) with
`finrank (range ev_S) ≤ finrank (S → ℚ) = S.card` gives the first claim;
the second is `Submodule.finrank_le` for `ker ev_S`; for the third,
`range ev_S ≠ ⊥` so `finrank (range) ≥ 1`
(`Submodule.one_le_finrank_iff`/`Submodule.finrank_eq_zero`).
Edge cases: `S = ∅` (quotient by `⊥`, equality); infinite-dimensional
quotient impossible since `ker` is a subspace of a finite-dimensional space. -/
lemma t91A02_b1_quotient_normalClosure_bounds {G : Type*} [Group G]
    [FiniteDimensional ℚ (Additive G →+ ℚ)] (S : Finset G) :
    t91A02_b1 G ≤
        t91A02_b1 (G ⧸ Subgroup.normalClosure (S : Set G)) + S.card ∧
      t91A02_b1 (G ⧸ Subgroup.normalClosure (S : Set G)) ≤ t91A02_b1 G ∧
      ((∃ s ∈ S, ∃ φ : Additive G →+ ℚ, φ (Additive.ofMul s) ≠ 0) →
        t91A02_b1 (G ⧸ Subgroup.normalClosure (S : Set G)) + 1 ≤
          t91A02_b1 G) := by
  let N : Subgroup G := Subgroup.normalClosure (S : Set G)
  let ev : (Additive G →+ ℚ) →ₗ[ℚ] (s : S) → ℚ :=
    { toFun := fun φ s => φ (Additive.ofMul (s : G))
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  let E : (Additive (G ⧸ N) →+ ℚ) ≃ₗ[ℚ] LinearMap.ker ev :=
    { toFun := fun φ => ⟨φ.comp (MonoidHom.toAdditive
          (QuotientGroup.mk' N)), by
        ext s
        change φ (Additive.ofMul ((QuotientGroup.mk' N) (s : G))) = 0
        have hq : (QuotientGroup.mk' N) (s : G) = 1 :=
          (QuotientGroup.eq_one_iff (s : G)).mpr
            (Subgroup.subset_normalClosure
              (show (s : G) ∈ (S : Set G) from s.property))
        rw [hq]
        exact φ.map_zero⟩
      invFun := fun φ => MonoidHom.toAdditive
        (QuotientGroup.lift N (AddMonoidHom.toMultiplicative φ.1) (by
          apply Subgroup.normalClosure_le_normal
          intro x hx
          apply MonoidHom.mem_ker.mpr
          change Multiplicative.ofAdd (φ.1 (Additive.ofMul x)) = 1
          change φ.1 (Additive.ofMul x) = 0
          change ev φ.1 (⟨x, hx⟩ : S) = 0
          exact congrFun φ.2 ⟨x, hx⟩))
      left_inv := by
        intro φ
        change MonoidHom.toAdditive
          (QuotientGroup.lift N
            (AddMonoidHom.toMultiplicative
              (φ.comp (MonoidHom.toAdditive (QuotientGroup.mk' N)))) _) = φ
        apply AddMonoidHom.ext
        intro x
        change Additive.ofMul
          ((QuotientGroup.lift N
            (AddMonoidHom.toMultiplicative
              (φ.comp (MonoidHom.toAdditive (QuotientGroup.mk' N)))) _)
              (Additive.toMul x)) = φ x
        obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (Additive.toMul x)
        rw [← ofMul_toMul x, ← hg]
        rfl
      right_inv := by
        intro φ
        apply Subtype.ext
        change (MonoidHom.toAdditive
          (QuotientGroup.lift N (AddMonoidHom.toMultiplicative φ.1) _)).comp
            (MonoidHom.toAdditive (QuotientGroup.mk' N)) = φ.1
        apply AddMonoidHom.ext
        intro x
        rw [← ofMul_toMul x]
        rfl
      map_add' := by
        intros
        apply Subtype.ext
        ext
        simp
      map_smul' := by
        intros
        apply Subtype.ext
        ext
        simp }
  letI : FiniteDimensional ℚ (Additive (G ⧸ N) →+ ℚ) := E.symm.finiteDimensional
  have hdim : Module.finrank ℚ (LinearMap.range ev) +
      Module.finrank ℚ (LinearMap.ker ev) = Module.finrank ℚ (Additive G →+ ℚ) :=
    ev.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℚ (LinearMap.range ev) ≤ S.card := by
    calc
      Module.finrank ℚ (LinearMap.range ev) ≤ Module.finrank ℚ ((s : S) → ℚ) :=
        Submodule.finrank_le _
      _ = S.card := by simp [Module.finrank_fin_fun]
  have hquot : t91A02_b1 (G ⧸ N) = Module.finrank ℚ (LinearMap.ker ev) := by
    exact E.finrank_eq
  have hlow : t91A02_b1 G ≤ t91A02_b1 (G ⧸ N) + S.card := by
    unfold t91A02_b1
    rw [show Module.finrank ℚ (Additive (G ⧸ N) →+ ℚ) =
      Module.finrank ℚ (LinearMap.ker ev) from hquot, ← hdim]
    omega
  have hupp : t91A02_b1 (G ⧸ N) ≤ t91A02_b1 G := by
    unfold t91A02_b1
    rw [show Module.finrank ℚ (Additive (G ⧸ N) →+ ℚ) =
      Module.finrank ℚ (LinearMap.ker ev) from hquot, ← hdim]
    omega
  refine ⟨?_, ?_, ?_⟩
  · simpa [N] using hlow
  · simpa [N] using hupp
  · rintro ⟨s, hs, φ, hφ⟩
    have hevne : ev φ ≠ 0 := by
      intro h
      have := congrFun h (⟨s, hs⟩ : S)
      exact hφ (by simpa [ev] using this)
    have hrne : LinearMap.range ev ≠ ⊥ := by
      intro h
      have : ev φ ∈ (⊥ : Submodule ℚ ((s : S) → ℚ)) := by
        rw [← h]
        exact LinearMap.mem_range_self ev φ
      exact hevne (by simpa using this)
    have hone : 1 ≤ Module.finrank ℚ (LinearMap.range ev) :=
      Submodule.one_le_finrank_iff.mpr hrne
    unfold t91A02_b1
    rw [show Module.finrank ℚ (Additive (G ⧸ Subgroup.normalClosure (S : Set G)) →+ ℚ) =
        Module.finrank ℚ (LinearMap.ker ev) by simpa [N] using hquot,
      ← hdim]
    omega

/-- **Leaf A3 (generic, Reidemeister–Schreier without rewriting).**  An
index-`k` subgroup `H` of `G ⧸ ⟪r⟫` is the quotient of its preimage
`H̃ = H.comap mk` by the normal closure (inside `H̃`) of at most `k`
conjugates of `r`.

Route: `N := normalClosure {r} ≤ H̃` (`QuotientGroup.ker_mk'` ≤ comap).
`H ≃* H̃ ⧸ N.subgroupOf H̃` (`QuotientGroup.quotientKerEquivOfSurjective` for
`mk' ∘ H̃.subtype` corestricted to `H`, kernel `N.subgroupOf H̃`).  Pick a left
transversal `R` of `H̃` (`Subgroup.exists_left_transversal 1` or
`Quotient.out` on `Finset.univ : Finset (G ⧸ H̃)`, finite by
`Subgroup.finiteIndex_of_index_ne_zero`; `Nat.card` of the quotient is `k`).
Let `T := {t⁻¹ r t | t ∈ R}` (each in `N ≤ H̃`).  Then
`N.subgroupOf H̃ = normalClosure T`: `⊇` since `N.subgroupOf H̃` is normal in
`H̃` and contains `T`; `⊆` by `Subgroup.normalClosure_le_normal`-style
induction on `normalClosure {r}` (`Subgroup.normalClosure_induction`):
for `g ∈ G` write `g⁻¹ = t h` (`t ∈ R`, `h ∈ H̃`), so
`g r g⁻¹ = h⁻¹ (t⁻¹ r t) h`.  Finish with `QuotientGroup.quotientMulEquivOfEq`.
`T.card ≤ R.card = k` (`Finset.card_image_le`); `T` nonempty as `k > 0`. -/
lemma t91A02_finiteIndex_relators {G : Type*} [Group G] (r : G)
    (H : Subgroup (G ⧸ Subgroup.normalClosure ({r} : Set G)))
    (k : ℕ) (hk : 0 < k) (hH : H.index = k) :
    ∃ T : Finset (H.comap (QuotientGroup.mk' (Subgroup.normalClosure ({r} : Set G)))),
      T.Nonempty ∧ T.card ≤ k ∧
      (∀ t ∈ T, ∃ g : G, (t : G) = g⁻¹ * r * g) ∧
      Nonempty (H ≃* (H.comap (QuotientGroup.mk'
          (Subgroup.normalClosure ({r} : Set G)))) ⧸
        Subgroup.normalClosure (T : Set (H.comap (QuotientGroup.mk'
          (Subgroup.normalClosure ({r} : Set G)))))) := by
  classical
  let N : Subgroup G := Subgroup.normalClosure ({r} : Set G)
  letI : N.Normal := by dsimp [N]; infer_instance
  let q : G →* G ⧸ Subgroup.normalClosure ({r} : Set G) :=
    QuotientGroup.mk' (Subgroup.normalClosure ({r} : Set G))
  let K : Subgroup G := H.comap q
  have hNK : N ≤ K := by
    intro x hx
    change q x ∈ H
    have : q x = 1 := by
      change QuotientGroup.mk' N x = 1
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hx
    simpa [this]
  letI : Fintype (G ⧸ K) := K.fintypeOfIndexNeZero (by
    rw [show K.index = H.index from Subgroup.index_comap_of_surjective
      (f := q) H (by simpa [q] using
        (QuotientGroup.mk'_surjective (N := Subgroup.normalClosure ({r} : Set G))))]
    omega)
  let rep : G ⧸ K → G := fun c => Quotient.out c
  have hrep (c : G ⧸ K) : QuotientGroup.mk (rep c) = c := Quotient.out_eq c
  have hrK (c : G ⧸ K) : (rep c)⁻¹ * r * rep c ∈ K := by
    apply hNK
    simpa using (Subgroup.normalClosure_normal (s := ({r} : Set G))).conj_mem r
      (Subgroup.subset_normalClosure (Set.mem_singleton r)) (rep c)⁻¹
  let a : G ⧸ K → K := fun c => ⟨(rep c)⁻¹ * r * rep c, hrK c⟩
  let T : Finset K := Finset.univ.image a
  have hTmem (c : G ⧸ K) : a c ∈ T := by
    dsimp [T]
    exact Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩
  have hTne : T.Nonempty := ⟨a (QuotientGroup.mk 1 : G ⧸ K), hTmem _⟩
  have hTcard : T.card ≤ k := by
    calc
      T.card ≤ Fintype.card (G ⧸ K) := Finset.card_image_le
      _ = K.index := by rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
      _ = H.index := Subgroup.index_comap_of_surjective H (by
        simpa [q] using (QuotientGroup.mk'_surjective
          (N := Subgroup.normalClosure ({r} : Set G))))
      _ = k := hH
  have hTconj : ∀ t ∈ T, ∃ g : G, (t : G) = g⁻¹ * r * g := by
    intro t ht
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 ht
    exact ⟨rep c, rfl⟩
  let L : Subgroup K := Subgroup.normalClosure (T : Set K)
  letI : L.Normal := by dsimp [L]; infer_instance
  have hNL : N.subgroupOf K = L := by
    apply le_antisymm
    · intro x hx
      change x.1 ∈ N at hx
      have main : ∀ (y : G) (hy : y ∈ N), (⟨y, hNK hy⟩ : K) ∈ L := by
        intro y hy
        change y ∈ Subgroup.closure (Group.conjugatesOfSet ({r} : Set G)) at hy
        induction hy using Subgroup.closure_induction with
        | mem y hy =>
          rcases Group.mem_conjugatesOfSet_iff.1 hy with ⟨z, hz, hconj⟩
          have hz' : z = r := Set.mem_singleton_iff.1 hz
          subst z
          obtain ⟨g, rfl⟩ := isConj_iff.1 hconj
          let c : G ⧸ K := QuotientGroup.mk g⁻¹
          have huK : (rep c)⁻¹ * g⁻¹ ∈ K := by
            apply QuotientGroup.leftRel_apply.1
            apply Quotient.exact
            exact (hrep c).trans rfl
          let u : G := (rep c)⁻¹ * g⁻¹
          have hg : g⁻¹ = rep c * u := by simp [u]
          have heq : g * r * g⁻¹ = u⁻¹ * ((rep c)⁻¹ * r * rep c) * u := by
            rw [hg, mul_inv_rev]
            simp [mul_assoc]
          have ha : a c ∈ L := Subgroup.subset_normalClosure (hTmem c)
          have hc := (inferInstance : L.Normal).conj_mem (a c) ha
            ⟨u⁻¹, K.inv_mem huK⟩
          convert hc using 1
          apply Subtype.ext
          simpa [a] using heq
        | one => exact L.one_mem
        | mul x y _ _ hx hy => exact L.mul_mem hx hy
        | inv x _ hx => exact L.inv_mem hx
      exact main x.1 hx
    · apply Subgroup.normalClosure_le_normal (s := (T : Set K))
      intro x hx
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      change (rep c)⁻¹ * r * rep c ∈ N
      simpa using
        ((Subgroup.normalClosure_normal (s := ({r} : Set G))).conj_mem r
          (Subgroup.subset_normalClosure (Set.mem_singleton r)) (rep c)⁻¹)
  let f : K →* H := (q.restrict K).codRestrict H (fun x => x.2)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := (QuotientGroup.mk'_surjective
      (N := Subgroup.normalClosure ({r} : Set G))) y.1
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change QuotientGroup.mk' (Subgroup.normalClosure ({r} : Set G)) x ∈ H
    rw [hx]
    exact y.2
  have hker : f.ker = L := by
    rw [show f.ker = N.subgroupOf K by
      ext x
      simp [f, q, N, QuotientGroup.ker_mk']]
    exact hNL
  refine ⟨T, hTne, hTcard, hTconj, ?_⟩
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

/-! ## Generic algebra assemblies (sorry-free) -/

/-- `b₁` of a one-relator group `F_n ⧸ ⟪r⟫` with `r` rationally nonzero is
`n - 1`. -/
theorem t91A02_b1_oneRelator (n : ℕ) (r : FreeGroup (Fin n))
    (hr : ∃ φ : Additive (FreeGroup (Fin n)) →+ ℚ, φ (Additive.ofMul r) ≠ 0) :
    t91A02_b1 (FreeGroup (Fin n) ⧸ Subgroup.normalClosure ({r} : Set _)) + 1 = n := by
  obtain ⟨hfd, hb⟩ := t91A02_b1_freeGroup n
  obtain ⟨hlow, -, hup⟩ := t91A02_b1_quotient_normalClosure_bounds ({r} : Finset _)
  have hup' := hup ⟨r, Finset.mem_singleton_self r, hr⟩
  have hq : t91A02_b1 (FreeGroup (Fin n) ⧸
        Subgroup.normalClosure ((({r} : Finset (FreeGroup (Fin n))) : Set _))) =
      t91A02_b1 (FreeGroup (Fin n) ⧸ Subgroup.normalClosure ({r} : Set _)) :=
    t91A02_b1_congr (QuotientGroup.quotientMulEquivOfEq (by rw [Finset.coe_singleton]))
  simp only [Finset.card_singleton] at hlow
  omega

/-- Rank bounds for an index-`k` subgroup of a one-relator group. -/
theorem t91A02_b1_finiteIndex_bounds (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (r : FreeGroup (Fin n))
    (H : Subgroup (FreeGroup (Fin n) ⧸ Subgroup.normalClosure ({r} : Set _)))
    (hH : H.index = k) :
    (n - 1) * k + 1 ≤ t91A02_b1 H + k ∧
      ((∃ φ : Additive (FreeGroup (Fin n)) →+ ℚ, φ (Additive.ofMul r) ≠ 0) →
        t91A02_b1 H + 1 ≤ (n - 1) * k + 1) := by
  obtain ⟨T, hTne, hTcard, hTconj, ⟨eH⟩⟩ := t91A02_finiteIndex_relators r H k hk hH
  have hidx : (H.comap (QuotientGroup.mk'
      (Subgroup.normalClosure ({r} : Set (FreeGroup (Fin n)))))).index = k := by
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact hH
  let eF := FiniteIndexFreeGroupSchreierRank.finiteIndexSubgroupFreeGroupEquiv
    n k hn hk _ hidx
  obtain ⟨hfdF, hbF⟩ := t91A02_b1_freeGroup ((n - 1) * k + 1)
  haveI := t91A02_finiteDimensional_congr eF
  have hbHt := (t91A02_b1_congr eF).trans hbF
  have hbH := t91A02_b1_congr eH
  obtain ⟨hlow, -, hup⟩ := t91A02_b1_quotient_normalClosure_bounds T
  refine ⟨by omega, ?_⟩
  rintro ⟨φ, hφ⟩
  obtain ⟨t, ht⟩ := hTne
  obtain ⟨g, hg⟩ := hTconj t ht
  have hψ : (φ.comp (MonoidHom.toAdditive (Subgroup.subtype _))) (Additive.ofMul t) ≠ 0 := by
    change φ (Additive.ofMul (t : FreeGroup (Fin n))) ≠ 0
    rw [hg, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
    intro h
    apply hφ
    linarith
  have := hup ⟨t, ht, _, hψ⟩
  omega

/-! ## Generic topology leaves -/

/-- **Leaf T1 (generic, LIBRARY-sized).**  Van Kampen for one-vertex polygon
quotients: `π₁(P.Space, x) ≅ π₁(wedge of orbit circles) ⧸ ⟪boundary class⟫`.

Route: `P.Space ≃ₜ Cell (polygonBoundaryWedgeLoop P)` (shared with the
t97A01 polygon ≅ `Cell(word)` leaf), then `AttachTwoCell.cell_piOne` with its
inputs from `cell_facts`, `loopClassAt` matched to
`polygonBoundaryFundamentalClass` (`polygonBoundaryWedgeLoop_one`), and a
basepoint change along a path (`P.Space` is path connected).  Alternative
direct route: the genus-two specialization in `GenusTwoSurfacePiOne`
(`apm_t92J05_genusTwo_polygon_attach_specialization_aux_*`) is already written
for the radial cover `openCover P`; generalize it over `P` and feed
`apm_t92J05_twoOpen_attach_one_cell`, `punctureDeformationRetract`,
`PairingData.skeletonHomeomorphWedge`. -/
lemma t91A02_polygon_pi1_wedge_quotient (P : PairingData) (x : P.Space) :
    Nonempty (FundamentalGroup P.Space x ≃*
      FundamentalGroup
          (PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair)) (orbitWedgeBase P) ⧸
        Subgroup.normalClosure ({polygonBoundaryFundamentalClass P} : Set _)) := by
  sorry

/-- Leaf (generic, split from `t91A02_polygonBoundary_freeWord`, lemma-2 PARTIAL
2026-10-15).  A homomorphism from π₁ of the finite wedge to `ℚ` vanishes on
elements with zero Hurewicz image.  Route: `ℚ` is abelian, so `f` factors
through the abelianization; for a path-connected space the Hurewicz map
identifies the abelianization of π₁ with H₁ (Hurewicz utilities in
`PolygonSurfaceHomology` / `GenusTwoSurfacePiOne`), so a class with zero
Hurewicz image lies in the commutator subgroup, on which `f` vanishes. -/
lemma t91A02_polygonBoundary_freeWord_aux_kernel_aux_word (P : PairingData)
    (f : Additive (FundamentalGroup
      (PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair))
      (orbitWedgeBase P)) →+ ℚ)
    (w : FiniteWedgeLegWord P) :
    f (Additive.ofMul (finiteWedgeLegWordGroup P w)) =
      ∑ l, (finiteWedgeLegWordCoordinatesList P w l : ℚ) *
        f (Additive.ofMul (finiteWedgeLegFundamentalClassAtBase P l)) := by
  classical
  induction w with
  | nil => simp [finiteWedgeLegWordGroup, finiteWedgeLegWordCoordinatesList]
  | cons q w ih =>
      rw [show finiteWedgeLegWordGroup P (q :: w) =
          finiteWedgeLegFundamentalClassAtBase P q.1 ^ q.2 *
            finiteWedgeLegWordGroup P w by rfl]
      rw [show finiteWedgeLegWordCoordinatesList P (q :: w) =
          q.2 • orbitBasis P q.1 1 + finiteWedgeLegWordCoordinatesList P w by rfl]
      change f (Additive.ofMul (finiteWedgeLegFundamentalClassAtBase P q.1 ^ q.2) +
          Additive.ofMul (finiteWedgeLegWordGroup P w)) = _
      rw [AddMonoidHom.map_add, ih]
      simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
      congr 1
      rw [show Additive.ofMul
          (finiteWedgeLegFundamentalClassAtBase P q.1 ^ q.2) =
            q.2 • Additive.ofMul
              (finiteWedgeLegFundamentalClassAtBase P q.1) by rfl,
        map_zsmul]
      rw [Finset.sum_eq_single q.1]
      · simp [orbitBasis]
      · intro b _ hb
        simp [orbitBasis, Pi.single_apply, hb]
      · simp

lemma t91A02_polygonBoundary_freeWord_aux_kernel (P : PairingData)
    (f : Additive (FundamentalGroup
      (PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair))
      (orbitWedgeBase P)) →+ ℚ)
    (g : FundamentalGroup
      (PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair))
      (orbitWedgeBase P))
    (hg : moduleHurewicz (orbitWedgeBase P) g = 0) :
    f (Additive.ofMul g) = 0 := by
  obtain ⟨w, hw⟩ :=
    finiteWedgeFundamentalGroup_generated_by_legs_of_freeGroup_surjective P
      (finiteWedgeLegFreeGroupMap_surjective P) g
  have hv : finiteWedgeLegWordCoordinatesList P w = 0 := by
    have hinj := (ModuleCat.mono_iff_injective
      (finiteWedgeH1CoordinateMap P)).mp inferInstance
    apply hinj
    rw [← finiteWedgeLegWord_hurewicz P w, hw, hg]
    exact (map_zero (finiteWedgeH1CoordinateMap P).hom).symm
  rw [← hw,
    t91A02_polygonBoundary_freeWord_aux_kernel_aux_word P f w, hv]
  simp

/-- **Leaf T2 (generic).**  Free coordinates on the orbit wedge in which the
boundary class has the attaching-degree abelianization.

Route: `finiteWedgeOrbitHomeomorphFinZero`, `finiteWedge_finSucc_fundamentalGroup_free`
(`GenusTwoSurfacePiOne`; `Nat.card` of the orbits is positive because
`P.edgeCount_pos`), giving `e` sending the `l`-th leg class
(`finiteWedgeLegFundamentalClassAtBase`) to a free generator.  Both
`φ ∘ e` and `coordinate ∘ moduleHurewicz` are homomorphisms to abelian groups
agreeing on legs (`finiteWedgeLegFundamentalClassAtBase_hurewicz_eq_coordinate`),
so the abelianized image of `e (polygonBoundaryFundamentalClass P)` is
`attachingDegree P` up to the orbit/`Fin` relabelling
(`polygonBoundaryFundamentalClass_hurewicz_eq_attachingDegree`).  Then `→`:
a nonzero ℚ-hom on a word with zero abelianization is impossible;
`←`: take `φ` = the exponent-sum on an orbit with nonzero degree. -/
lemma t91A02_polygonBoundary_freeWord (P : PairingData) :
    ∃ e : FundamentalGroup
        (PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair)) (orbitWedgeBase P) ≃*
        FreeGroup (Fin (Nat.card (PairingOrbit P.pair))),
      (∃ φ : Additive (FreeGroup (Fin (Nat.card (PairingOrbit P.pair)))) →+ ℚ,
          φ (Additive.ofMul (e (polygonBoundaryFundamentalClass P))) ≠ 0) ↔
        attachingDegree P ≠ 0 := by
  sorry

/-- **Leaf T3 (standard crosscap data).**  The standard `g`-crosscap polygon
has `g` edge orbits and nonzero attaching degree (it is `-2` on every orbit:
all signs are `false`, `standardSign_nonorientable`, and each orbit is
`{2j, 2j+1}`).

Route: `standardPairingData false g hg` unfolds to
`nonorientableStandardPairingData`, whose `pair` is `standardPair false g =
nonorientablePair g`; `Nat.card_congr (nonorientableOrbitEquiv g)`.  For the
degree: evaluate at the orbit of edge `0`; `orbit_eq_iff`/
`nonorientableOrbitLabel_pair` show exactly edges `0, 1` lie in it, so the sum
in `attachingDegree_apply` is `-1 + -1`. -/
lemma t91A02_standard_nonorientable_data_aux_orbit (g : ℕ) (hg : 0 < g)
    (i : Fin (2 * g)) (j : Fin g) :
    (standardPairingData false g hg).orbit i =
        (nonorientableOrbitEquiv g).symm j ↔
      nonorientableOrbitLabel g i = j := by
  change Quotient.mk _ i = (nonorientableOrbitEquiv g).symm j ↔ _
  constructor
  · intro h
    have := congrArg (nonorientableOrbitEquiv g) h
    simpa using this
  · intro h
    apply (nonorientableOrbitEquiv g).injective
    simpa using h

lemma t91A02_standard_nonorientable_data_aux_degree (g : ℕ) (hg : 0 < g)
    (j : Fin g) :
    attachingDegree (standardPairingData false g hg)
        ((nonorientableOrbitEquiv g).symm j) = -2 := by
  rw [attachingDegree_apply]
  calc
    _ = ∑ p : Fin g × Fin 2,
        edgeOrbitContribution (standardPairingData false g hg)
          ((nonorientableCoord g).symm p) ((nonorientableOrbitEquiv g).symm j) :=
      ((nonorientableCoord g).symm.sum_comp fun i =>
        edgeOrbitContribution (standardPairingData false g hg) i
          ((nonorientableOrbitEquiv g).symm j)).symm
    _ = -2 := by
      simp only [edgeOrbitContribution]
      simp_rw [t91A02_standard_nonorientable_data_aux_orbit]
      simp [standardPairingData, nonorientableStandardPairingData,
        standardPairingDataOfOneVertex, standardPair, standardSign,
        nonorientableOrbitLabel, edgeAttachingDegree, Fintype.sum_prod_type]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
        if_pos]
      norm_num

lemma t91A02_standard_nonorientable_data (g : ℕ) (hg : 0 < g) :
    Nat.card (PairingOrbit (standardPairingData false g hg).pair) = g ∧
      attachingDegree (standardPairingData false g hg) ≠ 0 := by
  constructor
  · change Nat.card (PairingOrbit (nonorientablePair g)) = g
    simpa using Nat.card_congr (nonorientableOrbitEquiv g)
  · intro hzero
    have h : attachingDegree (standardPairingData false g hg)
          ((nonorientableOrbitEquiv g).symm ⟨0, hg⟩) = 0 := by
      simpa using congrFun hzero ((nonorientableOrbitEquiv g).symm ⟨0, hg⟩)
    rw [t91A02_standard_nonorientable_data_aux_degree] at h
    norm_num at h

/-! ## Topology assemblies (sorry-free) -/

/-- A homeomorphism transports the based fundamental group.
Copied from `ConstructionTargets.t97A01Closure.fundamentalGroupEquivOfHomeomorph`. -/
def t91A02_fundamentalGroupEquivOfHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) where
  toFun := FundamentalGroup.map ⟨e, e.continuous⟩ x
  invFun := FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
    (e.symm_apply_apply x)
  left_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.map_apply]
      change (FundamentalGroup.mapOfEq _ _)
        (Path.Homotopic.Quotient.mk (p.map e.continuous)) = _
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact e.symm_apply_apply (p t)
  right_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact e.apply_symm_apply (p t)
  map_mul' := map_mul _

/-- Transport a one-relator quotient along a group isomorphism. -/
def t91A02_quotientSingletonCongr {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (r : G) :
    G ⧸ Subgroup.normalClosure ({r} : Set G) ≃*
      G' ⧸ Subgroup.normalClosure ({e r} : Set G') :=
  QuotientGroup.congr _ _ e (by
    rw [Subgroup.map_normalClosure _ _ e.surjective, Set.image_singleton]
    rfl)

/-- One-relator presentation of any one-vertex polygon quotient. -/
theorem t91A02_polygon_presentation (P : PairingData) (x : P.Space) :
    ∃ r : FreeGroup (Fin (Nat.card (PairingOrbit P.pair))),
      Nonempty (FundamentalGroup P.Space x ≃*
        FreeGroup (Fin (Nat.card (PairingOrbit P.pair))) ⧸
          Subgroup.normalClosure ({r} : Set _)) ∧
      ((∃ φ : Additive (FreeGroup (Fin (Nat.card (PairingOrbit P.pair)))) →+ ℚ,
          φ (Additive.ofMul r) ≠ 0) ↔ attachingDegree P ≠ 0) := by
  obtain ⟨eq⟩ := t91A02_polygon_pi1_wedge_quotient P x
  obtain ⟨e, he⟩ := t91A02_polygonBoundary_freeWord P
  exact ⟨e (polygonBoundaryFundamentalClass P),
    ⟨eq.trans (t91A02_quotientSingletonCongr e _)⟩, he⟩

instance t91A02_disk_pathConnected : PathConnectedSpace Disk :=
  isPathConnected_iff_pathConnectedSpace.mp
    ((convex_closedBall (0 : ℂ) 1).isPathConnected
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩)

theorem t91A02_surface_pathConnected (o : Bool) (g : ℕ) :
    PathConnectedSpace (Surface o g) :=
  (surjective_surfaceQuotient o g).pathConnectedSpace (continuous_surfaceQuotient o g)

/-- One-relator presentation of `π₁(N_g)` with a rationally nonzero relator. -/
theorem t91A02_surface_presentation (g : ℕ) (hg : 0 < g) (x : Surface false g) :
    ∃ r : FreeGroup (Fin g),
      Nonempty (FundamentalGroup (Surface false g) x ≃*
        FreeGroup (Fin g) ⧸ Subgroup.normalClosure ({r} : Set _)) ∧
      ∃ φ : Additive (FreeGroup (Fin g)) →+ ℚ, φ (Additive.ofMul r) ≠ 0 := by
  let P := standardPairingData false g hg
  let h := standardPairingData_space_homeomorph false g hg
  obtain ⟨hcard, hdeg⟩ := t91A02_standard_nonorientable_data g hg
  obtain ⟨r, ⟨eP⟩, hiff⟩ := t91A02_polygon_presentation P (h.symm x)
  let c : FreeGroup (Fin (Nat.card (PairingOrbit P.pair))) ≃* FreeGroup (Fin g) :=
    FreeGroup.freeGroupCongr (finCongr hcard)
  obtain ⟨φ, hφ⟩ := hiff.mpr hdeg
  refine ⟨c r, ⟨?_⟩, φ.comp (MulEquiv.toAdditive c.symm).toAddMonoidHom, ?_⟩
  · have hx : h (h.symm x) = x := h.apply_symm_apply x
    exact ((t91A02_fundamentalGroupEquivOfHomeomorph h.symm x).trans eP).trans
      (t91A02_quotientSingletonCongr c r)
  · simpa using hφ

/-! ## Main theorem -/

theorem apm_t91a02 :
    ¬ ∃ (p : Surface false 16 → Surface false 8) (sheets : ℕ),
      IsCoveringMap p ∧ 0 < sheets ∧
      ∀ x : Surface false 8, Nat.card {e : Surface false 16 // p e = x} = sheets := by
  rintro ⟨p, sheets, hp, hsheets, hfiber⟩
  haveI : PathConnectedSpace (Surface false 16) := t91A02_surface_pathConnected false 16
  let e0 : Surface false 16 :=
    surfaceQuotient false 16 ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  let f := coveringInducedFundamentalGroupMap hp e0
  have hidx : f.range.index = sheets := by
    rw [← coveringFiberCard_eq_index hp e0, ← hfiber (p e0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun _ => Set.mem_singleton_iff))
  obtain ⟨r8, ⟨e8⟩, hφ8⟩ := t91A02_surface_presentation 8 (by norm_num) (p e0)
  obtain ⟨r16, ⟨e16⟩, hφ16⟩ := t91A02_surface_presentation 16 (by norm_num) e0
  let H := f.range.map (e8 : FundamentalGroup (Surface false 8) (p e0) →*
    FreeGroup (Fin 8) ⧸ Subgroup.normalClosure ({r8} : Set _))
  have hHidx : H.index = sheets := (Subgroup.index_map_equiv f.range e8).trans hidx
  have eH : FundamentalGroup (Surface false 16) e0 ≃* H :=
    (MonoidHom.ofInjective (coveringInducedFundamentalGroupMap_injective hp e0)).trans
      (f.range.equivMapOfInjective _ e8.injective)
  have hbE : t91A02_b1 H + 1 = 16 := by
    rw [← t91A02_b1_congr eH, t91A02_b1_congr e16]
    exact t91A02_b1_oneRelator 16 r16 hφ16
  obtain ⟨hlow, hup⟩ :=
    t91A02_b1_finiteIndex_bounds 8 sheets (by norm_num) hsheets r8 H hHidx
  have hup' := hup hφ8
  norm_num at hlow hup'
  omega

end
