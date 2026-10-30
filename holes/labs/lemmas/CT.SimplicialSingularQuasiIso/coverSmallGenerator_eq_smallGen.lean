import ConstructionTargets.SimplicialChainMaps

/-!
# Ordered faces compute singular homology

The two directions of the ordered-face/singular comparison, and the theorem
`orderedFace_singular_quasiIso` they assemble into. These were in
`SimplicialSingularComparison`; they moved here (claude-14, 2026-10-30) because
the standard proof needs iterated barycentric subdivision and simplicial
approximation chain maps, which live in `SimplicialChainMaps`, and that file
imports `SimplicialSingularComparison`. The consumer of the final theorem is
`SimplicialChainModel`. The carrier-invariance half,
`affineComparison_homologyMap_eq`, stays in `SimplicialSingularComparison`.
-/

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.SimplicialSingularComparison

open ConstructionTargets.OrientedSimplicialChains

/-! ## Route S: a chain map from open-star-small singular chains to ordered faces

Plan (claude-14, 2026-10-30). `U = starCover K` is the cover of `K.space` by open
stars of vertices. An acyclic-carrier construction gives a chain map
`ψ : coverSmallChains ℚ U ⟶ ChainComplex.of _ d hdd` (`smallToFace_exists`) whose
value on a small simplex `σ` is supported in `starCarrier K (range σ)`: the faces
lying under a minimal face of some point of `range σ`. When `range σ` lies in the
open star of `a`, every such face can be coned to `a`, so this carrier is acyclic
(`coneSupported_cycle_bounds`), and its polyhedron is star-shaped about `a`
(`starCarrier_pointlike`).

* Surjectivity: `ψ ≫ cmpH` and the small-chain inclusion agree on homology
  (`smallToFace_homology`), and the inclusion is an isomorphism on homology
  (`CoefficientSmallComparison.inclusion_isIso`).
* Injectivity: `cmpH ≫ Sd^r` lifts through the inclusion to `Φ`
  (`affineCmp_small_lift`), and `Φ ≫ ψ` is a face-carried endomorphism that is the
  identity in degree zero (`smallLift_comp_carried`), hence the identity on
  homology (`faceCarried_endo_homology`).

The leaves are stated for an arbitrary affine comparison `cmp` packaged as a chain
map `cmpH` (as in `SimplicialChainMaps.orientedPackage_homology_bijective`); the
two directional theorems at the end of this section transport them to the
`ChainComplex.ofHom` form. -/

/-- The open stars of the vertices of `K`, as subsets of `K.space`. Points that
are not vertices index the empty set. -/
def starCover {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n)) :
    Euc n → Set K.space :=
  fun v ↦ (Subtype.val : K.space → Euc n) ⁻¹' GeometricSimplicialSubdivision.openStar K v

theorem starCover_isOpen {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (hK : K.faces.Finite) (v : Euc n) : IsOpen (starCover K v) :=
  SimplicialChainMaps.openStar_isOpen K hK v

theorem starCover_covers {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n)) :
    Set.univ ⊆ ⋃ v, starCover K v := by
  intro x _
  obtain ⟨w, -, hw⟩ := SimplicialChainMaps.openStar_cover K x
  exact Set.mem_iUnion.mpr ⟨w, hw⟩

/-- `t` is a face whose hull contains `x` while no facet of `t` does (so `x` lies
in the open simplex of `t`). -/
def IsMinimalFace {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n)) (x : Euc n)
    (t : Finset (Euc n)) : Prop :=
  t ∈ K.faces ∧ x ∈ convexHull ℝ (t : Set (Euc n)) ∧
    ∀ w ∈ t, x ∉ convexHull ℝ ((t.erase w : Finset (Euc n)) : Set (Euc n))

/-- Every point of `K.space` has a minimal face: take a face of least card whose
hull contains it (`Nat.find` on the card, as at the start of
`SimplicialChainMaps.openStar_cover`). The facet `t.erase w` of a face is a face
when nonempty (`K.down_closed`), and the hull of the empty set is empty. -/
theorem exists_isMinimalFace {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (x : K.space) : ∃ t, IsMinimalFace K (x : Euc n) t := by
  obtain ⟨t, ht, hxt, hmin⟩ :=
    GeometricSimplicialSubdivision.inducedMap_homotopic_of_star_condition_aux_source_carrier
      K x
  exact ⟨t, ht, hxt, hmin⟩

/-- A minimal face of `x` lies inside every face whose hull contains `x`.
`K.inter_subset_convexHull` puts `x` in the hull of `t ∩ s`; if `t ∩ s ≠ t`, pick
`w ∈ t \ s`, so `t ∩ s ⊆ t.erase w` and `convexHull_mono` contradicts minimality. -/
theorem isMinimalFace_subset {n : ℕ} {K : Geometry.SimplicialComplex ℝ (Euc n)}
    {x : Euc n} {t s : Finset (Euc n)} (ht : IsMinimalFace K x t) (hs : s ∈ K.faces)
    (hx : x ∈ convexHull ℝ (s : Set (Euc n))) : t ⊆ s := by
  intro w hwt
  by_contra hws
  have hxinter : x ∈ convexHull ℝ ((t ∩ s : Finset (Euc n)) : Set (Euc n)) :=
    by simpa only [Finset.coe_inter] using
      K.inter_subset_convexHull ht.1 hs ⟨ht.2.1, hx⟩
  apply ht.2.2 w hwt
  apply convexHull_mono (𝕜 := ℝ) _ hxinter
  intro y hy
  simp only [Finset.coe_inter, Set.mem_inter_iff] at hy
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe]
  exact ⟨hy.1, fun hyw ↦ hws (hyw ▸ hy.2)⟩

/-- A point in the open star of `a` has `a` in its minimal face. From the
definition of `openStar`, `x` lies in the hull of a face `r ∋ a` but not of
`r.erase a`; `isMinimalFace_subset` gives `t ⊆ r`, and if `a ∉ t` then
`t ⊆ r.erase a`, contradicting `convexHull_mono`. -/
theorem isMinimalFace_mem_of_openStar {n : ℕ} {K : Geometry.SimplicialComplex ℝ (Euc n)}
    {x a : Euc n} {t : Finset (Euc n)} (ht : IsMinimalFace K x t)
    (ha : x ∈ GeometricSimplicialSubdivision.openStar K a) : a ∈ t := by
  obtain ⟨r, hr, har, hxr, hxr'⟩ := ha
  have htr : t ⊆ r := isMinimalFace_subset ht hr hxr
  by_contra hat
  have hsub : t ⊆ r.erase a := fun w hw =>
    Finset.mem_erase.mpr ⟨fun h => hat (h ▸ hw), htr hw⟩
  exact hxr' (convexHull_mono (by exact_mod_cast hsub) ht.2.1)

/-- The carrier of a set `A ⊆ K.space`: nonempty subsets of minimal faces of points
of `A`. It shrinks with `A` (so it is a carrier for small simplices and their
faces). -/
def starCarrier {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n)) (A : Set K.space) :
    Set (Finset (Euc n)) :=
  {s | s.Nonempty ∧ ∃ x ∈ A, ∃ t, IsMinimalFace K (x : Euc n) t ∧ s ⊆ t}

theorem starCarrier_mono {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    {A B : Set K.space} (h : A ⊆ B) : starCarrier K A ⊆ starCarrier K B := by
  rintro s ⟨hne, x, hx, t, ht, hst⟩
  exact ⟨hne, x, h hx, t, ht, hst⟩

theorem starCarrier_faces {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (A : Set K.space) {s : Finset (Euc n)} (hs : s ∈ starCarrier K A) : s ∈ K.faces := by
  obtain ⟨hne, _x, _hx, t, ht, hst⟩ := hs
  exact K.down_closed ht.1 hst hne

theorem starCarrier_down {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (A : Set K.space) {s u : Finset (Euc n)} (hs : s ∈ starCarrier K A) (hu : u ⊆ s)
    (hne : u.Nonempty) : u ∈ starCarrier K A := by
  obtain ⟨-, x, hx, t, ht, hst⟩ := hs
  exact ⟨hne, x, hx, t, ht, hu.trans hst⟩

theorem starCarrier_cone {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    {A : Set K.space} {a : Euc n} (hA : A ⊆ starCover K a) {s : Finset (Euc n)}
    (hs : s ∈ starCarrier K A) : insert a s ∈ starCarrier K A := by
  obtain ⟨-, x, hx, t, ht, hst⟩ := hs
  exact ⟨Finset.insert_nonempty a s, x, hx, t, ht,
    Finset.insert_subset (isMinimalFace_mem_of_openStar ht (hA hx)) hst⟩

/-- The polyhedron of the carrier is star-shaped about `a`: each carrier face `s`
has `insert a s` in the carrier (`starCarrier_cone`), and its hull is convex, contains
`a`, and contains the hull of `s`. A nonempty star-convex set is contractible
(`StarConvex.contractibleSpace`); conclude as in
`AcyclicCarriers.faceHull_rationallyPointlike` and transport to the preimage in
`K.space` as in `AcyclicCarriers.faceHullPreimage_rationallyPointlike`. -/
theorem starCarrier_pointlike {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    {A : Set K.space} {a : Euc n} (hA : A ⊆ starCover K a) (hne : A.Nonempty) :
    ProjectivePlaneWedgeRationalHomology.RationallyPointlike
      ((Subtype.val : K.space → Euc n) ⁻¹'
        ⋃ s ∈ starCarrier K A, convexHull ℝ (s : Set (Euc n))) := by
  sorry

/-- Each point of `A` lies in the carrier polyhedron (its minimal face, from
`exists_isMinimalFace`, is in the carrier). -/
theorem subset_starCarrier_hull {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (A : Set K.space) :
    A ⊆ (Subtype.val : K.space → Euc n) ⁻¹'
      ⋃ s ∈ starCarrier K A, convexHull ℝ (s : Set (Euc n)) := by
  intro x hx
  obtain ⟨t, ht⟩ := exists_isMinimalFace K x
  have htne : t.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := ht.2.1
    simp [h] at this
  exact Set.mem_iUnion₂.mpr ⟨t, ⟨htne, x, hx, t, ht, subset_rfl⟩, ht.2.1⟩

/-- Cone acyclicity in positive degree. Let `Λ` be a down-closed family of faces
closed under `insert a`. A cycle supported in `Λ` bounds a chain supported in `Λ`.
Split `z = z₁ + z₂`, where `z₁` is the part on faces not containing `a`
(`ConeAdmissible`). Then `w = SimplicialChainMaps.subdivisionCone o K a (k+1) z₁`
works: by `subdivisionChainMap_commutes_aux_cone_boundary`, `d w = z₁ - cone (d z₁)`,
and `cone (d z₁) = -z₂` because `d z₁ = -d z₂` and the cone of the part of `d z₂`
off `a` recovers `z₂` (the sign identity is
`subdivisionChainMap_commutes_aux_cone_boundary_aux_single_aux_sign`). The pieces
of the cone stay in `Λ` by `hcone`. -/
lemma coneSupported_cycle_bounds_aux_admissible {n k : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (Λ : Set (Finset (Euc n)))
    (a : Euc n) (hΛ : ∀ s ∈ Λ, s ∈ K.faces)
    (hcone : ∀ s ∈ Λ, insert a s ∈ Λ) (z : FaceModule K (k + 1))
    (hz : ∀ u, z u ≠ 0 → u.1 ∈ Λ) :
    SimplicialChainMaps.ConeAdmissible K a
      (Finsupp.filter (fun u : FaceIndex K (k + 1) => a ∉ u.1) z) := by
  intro u hu
  have hua : a ∉ u.1 := by
    by_contra h
    simp [Finsupp.filter_apply, h] at hu
  have huz : z u ≠ 0 := by
    simpa [Finsupp.filter_apply, hua] using hu
  exact ⟨hua, hΛ _ (hcone _ (hz u huz))⟩

lemma coneSupported_cycle_bounds_aux_support {n k : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n))
    (Λ : Set (Finset (Euc n))) (a : Euc n)
    (hcone : ∀ s ∈ Λ, insert a s ∈ Λ) (z : FaceModule K (k + 1))
    (hz : ∀ u, z u ≠ 0 → u.1 ∈ Λ) :
    ∀ u, SimplicialChainMaps.subdivisionCone o K a (k + 1)
      (Finsupp.filter (fun u : FaceIndex K (k + 1) => a ∉ u.1) z) u ≠ 0 → u.1 ∈ Λ := by
  intro u hu
  have hau : a ∈ u.1 := by
    by_contra h
    exact hu (SimplicialChainMaps.subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_cone_apply_not_mem
        o K a _ u h)
  have herase_ne : (u.1.erase a).Nonempty := by
    apply Finset.card_ne_zero.mp
    rw [Finset.card_erase_of_mem hau, u.2.2]
    omega
  have herase_face : u.1.erase a ∈ K.faces :=
    K.down_closed u.2.1 (Finset.erase_subset a u.1) herase_ne
  let w : FaceIndex K (k + 1) :=
    ⟨u.1.erase a, herase_face, by
      rw [Finset.card_erase_of_mem hau, u.2.2]
      omega⟩
  have hw : w.1 = u.1.erase a := rfl
  have hfiltered :
      Finsupp.filter (fun v : FaceIndex K (k + 1) => a ∉ v.1) z w ≠ 0 := by
    intro hzero
    apply hu
    rw [SimplicialChainMaps.subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_cone_apply_mem
        o K a _ u w hau hw, hzero, mul_zero]
  have haw : a ∉ w.1 := by simp [hw]
  have hzw : z w ≠ 0 := by
    simpa [Finsupp.filter_apply, haw] using hfiltered
  have := hcone w.1 (hz w hzw)
  simpa [hw, Finset.insert_erase hau] using this

lemma coneSupported_cycle_bounds_aux_boundary_aux_single {n k : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ j, FaceModuleCat K (j + 1) ⟶ FaceModuleCat K j)
    (hd : IsSignedDeletion o K d) (a : Euc n) (u : FaceIndex K (k + 1))
    (ha : a ∈ u.1) :
    SimplicialChainMaps.subdivisionCone o K a k (d k (Finsupp.single u 1)) =
      Finsupp.single u 1 := by
  classical
  rw [signedDeletion_sq_zero_aux_generator_aux_boundary o K d hd u, map_sum]
  simp only [map_smul]
  rw [Finset.sum_eq_single (⟨a, ha⟩ : {x // x ∈ u.1})]
  · have hidx : List.idxOf a (u.1.sort o.le) =
        (u.1.filter fun q => @LT.lt (Euc n) o.toLT q a).card :=
      SimplicialChainMaps.sort_idxOf_eq_card_lt o u.1 a ha
    have herase : ((u.1.erase a).filter fun q => @LT.lt (Euc n) o.toLT q a).card =
        (u.1.filter fun q => @LT.lt (Euc n) o.toLT q a).card := by
      rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
      simp
    simp [SimplicialChainMaps.subdivisionCone,
      signedDeletion_sq_zero_aux_generator_aux_erase, ha, u.2.1, hidx,
      herase, ← pow_add, ← two_mul, pow_mul]
  · intro p _ hpa
    have hne : p.1 ≠ a := by
      intro h
      apply hpa
      exact Subtype.ext h
    have hmem : a ∈ u.1.erase p.1 := Finset.mem_erase.mpr ⟨hne.symm, ha⟩
    simp [SimplicialChainMaps.subdivisionCone,
      signedDeletion_sq_zero_aux_generator_aux_erase, hmem]
  · simp

lemma coneSupported_cycle_bounds_aux_boundary_aux_containing {n k : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ j, FaceModuleCat K (j + 1) ⟶ FaceModuleCat K j)
    (hd : IsSignedDeletion o K d) (a : Euc n) (x : FaceModule K (k + 1))
    (hx : ∀ u, x u ≠ 0 → a ∈ u.1) :
    SimplicialChainMaps.subdivisionCone o K a k (d k x) = x := by
  classical
  rw [← Finsupp.sum_single x]
  change SimplicialChainMaps.subdivisionCone o K a k
      (d k (∑ u ∈ x.support, Finsupp.single u (x u))) =
    ∑ u ∈ x.support, Finsupp.single u (x u)
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← Finsupp.smul_single_one, map_smul, map_smul,
    coneSupported_cycle_bounds_aux_boundary_aux_single o K d hd a u
      (hx u (Finsupp.mem_support_iff.mp hu))]

lemma coneSupported_cycle_bounds_aux_boundary {n k : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ j, FaceModuleCat K (j + 1) ⟶ FaceModuleCat K j)
    (hd : IsSignedDeletion o K d) (a : Euc n) (z : FaceModule K (k + 1))
    (hcyc : d k z = 0)
    (hadm : SimplicialChainMaps.ConeAdmissible K a
      (Finsupp.filter (fun u : FaceIndex K (k + 1) => a ∉ u.1) z)) :
    d (k + 1) (SimplicialChainMaps.subdivisionCone o K a (k + 1)
      (Finsupp.filter (fun u : FaceIndex K (k + 1) => a ∉ u.1) z)) = z := by
  classical
  let x := Finsupp.filter (fun u : FaceIndex K (k + 1) => a ∉ u.1) z
  let y := Finsupp.filter (fun u : FaceIndex K (k + 1) => a ∈ u.1) z
  have hxy : x + y = z := by
    ext u
    simp only [x, y, Finsupp.add_apply, Finsupp.filter_apply]
    by_cases h : a ∈ u.1 <;> simp [h]
  have hy : ∀ u, y u ≠ 0 → a ∈ u.1 := by
    intro u hu
    by_contra h
    simp [y, Finsupp.filter_apply, h] at hu
  have hdx : d k x = -(d k y) := by
    have := congrArg (fun q => q - d k y) hcyc
    rw [← hxy, map_add] at hcyc
    exact eq_neg_of_add_eq_zero_left hcyc
  rw [SimplicialChainMaps.subdivisionChainMap_commutes_aux_cone_boundary
    o K d hd a x hadm, hdx, map_neg,
    coneSupported_cycle_bounds_aux_boundary_aux_containing o K d hd a y hy]
  rw [sub_neg_eq_add, hxy]

theorem coneSupported_cycle_bounds {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (Λ : Set (Finset (Euc n))) (a : Euc n)
    (hΛ : ∀ s ∈ Λ, s ∈ K.faces)
    (hdown : ∀ s ∈ Λ, ∀ u, u ⊆ s → u.Nonempty → u ∈ Λ)
    (hcone : ∀ s ∈ Λ, insert a s ∈ Λ) {k : ℕ} (z : FaceModule K (k + 1))
    (hz : ∀ u, z u ≠ 0 → u.1 ∈ Λ) (hcyc : d k z = 0) :
    ∃ w : FaceModule K (k + 2), (∀ u, w u ≠ 0 → u.1 ∈ Λ) ∧ d (k + 1) w = z := by
  let z₁ := Finsupp.filter (fun u : FaceIndex K (k + 1) => a ∉ u.1) z
  let w := SimplicialChainMaps.subdivisionCone o K a (k + 1) z₁
  have hadm : SimplicialChainMaps.ConeAdmissible K a z₁ :=
    coneSupported_cycle_bounds_aux_admissible K Λ a hΛ hcone z hz
  refine ⟨w, ?_, ?_⟩
  · exact coneSupported_cycle_bounds_aux_support o K Λ a hcone z hz
  · exact coneSupported_cycle_bounds_aux_boundary o K d hd a z hcyc hadm

/-- Cone acyclicity in degree zero: a 0-chain supported in `Λ` with coefficient
sum zero is the boundary of a 1-chain supported in `Λ`. Same cone construction,
using `subdivisionChainMap_commutes_aux_cone_boundary_zero`; `{a} ∈ Λ` follows
from `hcone` and `hdown` once `z ≠ 0`. -/
theorem coneSupported_zero_bounds {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (Λ : Set (Finset (Euc n))) (a : Euc n)
    (hΛ : ∀ s ∈ Λ, s ∈ K.faces)
    (hdown : ∀ s ∈ Λ, ∀ u, u ⊆ s → u.Nonempty → u ∈ Λ)
    (hcone : ∀ s ∈ Λ, insert a s ∈ Λ) (z : FaceModule K 0)
    (hz : ∀ u, z u ≠ 0 → u.1 ∈ Λ) (hsum : (z.sum fun _ c ↦ c) = 0) :
    ∃ w : FaceModule K 1, (∀ u, w u ≠ 0 → u.1 ∈ Λ) ∧ d 0 w = z := by
  classical
  by_cases hz0 : z = 0
  · subst z
    exact ⟨0, by simp⟩
  obtain ⟨u, hu⟩ := Finsupp.ne_iff.mp hz0
  have hua : u.1 ∈ Λ := hz u hu
  have haΛ : ({a} : Finset (Euc n)) ∈ Λ := by
    apply hdown (insert a u.1) (hcone u.1 hua) {a}
    · exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
    · exact Finset.singleton_nonempty _
  have haK : ({a} : Finset (Euc n)) ∈ K.faces := hΛ _ haΛ
  let A : FaceIndex K 0 := ⟨{a}, haK, by simp⟩
  let x := z - Finsupp.single A (z A)
  let w := SimplicialChainMaps.subdivisionCone o K a 0 x
  have hadm : SimplicialChainMaps.ConeAdmissible K a x := by
    intro v hv
    have hva : a ∉ v.1 := by
      by_contra h
      have hvA : v = A := by
        apply Subtype.ext
        obtain ⟨b, hb⟩ := Finset.card_eq_one.mp v.2.2
        change v.1 = {a}
        have hab : a = b := by simpa [hb] using h
        rw [hb, hab]
      subst v
      exact hv (by simp [x])
    have hvz : z v ≠ 0 := by
      have hAv : A ≠ v := by
        intro hAv
        apply hva
        rw [← hAv]
        exact Finset.mem_singleton_self a
      simpa [x, Finsupp.single_apply, hAv] using hv
    exact ⟨hva, hΛ _ (hcone v.1 (hz v hvz))⟩
  refine ⟨w, ?_, ?_⟩
  · intro U hU
    have haU : a ∈ U.1 := by
      by_contra haU
      exact hU (SimplicialChainMaps.subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_cone_apply_not_mem
          o K a x U haU)
    have herase_ne : (U.1.erase a).Nonempty := by
      apply Finset.card_ne_zero.mp
      rw [Finset.card_erase_of_mem haU, U.2.2]
      omega
    have herase_face : U.1.erase a ∈ K.faces :=
      K.down_closed U.2.1 (Finset.erase_subset a U.1) herase_ne
    let v : FaceIndex K 0 :=
      ⟨U.1.erase a, herase_face, by
        rw [Finset.card_erase_of_mem haU, U.2.2]⟩
    have hvx : x v ≠ 0 := by
      intro hv
      apply hU
      rw [SimplicialChainMaps.subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_cone_apply_mem
          o K a x U v haU rfl, hv, mul_zero]
    have hva : a ∉ v.1 := by simp [v]
    have hvz : z v ≠ 0 := by
      have hAv : A ≠ v := by
        intro hAv
        apply hva
        rw [← hAv]
        exact Finset.mem_singleton_self a
      simpa [x, Finsupp.single_apply, hAv] using hvx
    simpa [v, Finset.insert_erase haU] using hcone v.1 (hz v hvz)
  · have hxsum : x.sum (fun _ c ↦ c) = -z A := by
      rw [show x = z - Finsupp.single A (z A) from rfl,
        Finsupp.sum_sub_index (by intros; ring)]
      simp [hsum]
    have hA : A = (⟨{a}, haK, by simp⟩ : FaceIndex K 0) := Subtype.ext rfl
    have hb := SimplicialChainMaps.subdivisionChainMap_commutes_aux_cone_boundary_zero
      o K d hd a haK x hadm
    rw [hxsum, ← hA] at hb
    have hrhs : x - (-z A) • Finsupp.single A 1 = z := by
      ext v
      by_cases hv : v = A
      · subst v
        simp [x]
      · simp [x, Finsupp.single_apply, hv]
    exact hb.trans hrhs

/-- Degree-`k` simplices of the small-chain complex: singular simplices lying in
one member of `U`. -/
abbrev SmallSimplex {X α : Type} [TopologicalSpace X] (U : α → Set X) (k : ℕ) :=
  (SingularSubdivision.coverSmallSSet U : SSet).obj (Opposite.op (SimplexCategory.mk k))

/-- The image of a small simplex. -/
def smallRange {X α : Type} [TopologicalSpace X] (U : α → Set X) {k : ℕ}
    (t : SmallSimplex U k) : Set X :=
  Set.range (SingularSubdivision.continuousMapOfSingularSimplex k t.1)

/-- The generator of the small-chain module at a small simplex. -/
noncomputable def smallGen {X α : Type} [TopologicalSpace X] (U : α → Set X) {k : ℕ}
    (t : SmallSimplex U k) :
    ModuleCat.of ℚ ℚ ⟶ (CoefficientSmallPath.coverSmallChains ℚ U).X k := by
  change ModuleCat.of ℚ ℚ ⟶ ∐ fun _ : SmallSimplex U k => ModuleCat.of ℚ ℚ
  exact Limits.Sigma.ι (fun _ : SmallSimplex U k => ModuleCat.of ℚ ℚ) t

/-- A small simplex lies in one member of the cover: unfold membership in
`coverSmallSSet U = ⨆ a, range (toSSet.map (coverSubspaceInclusion U a))`
(a supremum of subcomplexes is computed pointwise, `SSet.Subcomplex.iSup_obj`),
and the range of a simplex pushed forward from `U a` lies in `U a`. -/
theorem smallSimplex_range_subset {X α : Type} [TopologicalSpace X] (U : α → Set X)
    {k : ℕ} (t : SmallSimplex U k) : ∃ a, smallRange U t ⊆ U a := by
  sorry

/-- `coverSmallGenerator` is `smallGen` at the small simplex of `σ`, whose image is
the range of `σ` (`continuousMapOfSingularSimplex_ofContinuousMap`). The equation
should be `rfl` after unfolding `coverSmallGenerator`. -/
-- BEGIN SEAT AREA
theorem coverSmallGenerator_eq_smallGen {X α : Type} [TopologicalSpace X]
    (U : α → Set X) {k : ℕ} (σ : C(stdSimplex ℝ (Fin (k + 1)), X)) (a : α)
    (hσ : Set.range σ ⊆ U a) :
    ∃ t : SmallSimplex U k,
      CoefficientSmallPath.coverSmallGenerator ℚ U σ a hσ = smallGen U t ∧
        smallRange U t = Set.range σ := by
  let τ := SingularSubdivision.singularSimplexOfContinuousMap (TopCat.of (U a)) k
    (SingularSubdivision.liftSimplexToCover U σ a hσ)
  let f := TopCat.toSSet.map (SingularSubdivision.coverSubspaceInclusion U a)
  have hmapped : f.app (Opposite.op (SimplexCategory.mk k)) τ =
      SingularSubdivision.singularSimplexOfContinuousMap (TopCat.of X) k σ := by
    change (TopCat.toSSetObjEquiv (TopCat.of X) _).symm
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U a, X)).comp
        (SingularSubdivision.liftSimplexToCover U σ a hσ)) = _
    congr 1
  have hmem : SingularSubdivision.singularSimplexOfContinuousMap (TopCat.of X) k σ ∈
      (SingularSubdivision.coverSmallSSet U).obj
        (Opposite.op (SimplexCategory.mk k)) := by
    rw [← hmapped]
    apply (le_iSup (fun a => SSet.Subcomplex.range
      (TopCat.toSSet.map (SingularSubdivision.coverSubspaceInclusion U a))) a)
    exact ⟨τ, rfl⟩
  let t : SmallSimplex U k :=
    ⟨SingularSubdivision.singularSimplexOfContinuousMap (TopCat.of X) k σ, hmem⟩
  refine ⟨t, ?_, ?_⟩
  · rfl
  · simp [smallRange, t]
-- END SEAT AREA

/-- The boundary of a small generator is a combination of small generators at its
faces, and each face has smaller image. Use the generator boundary formula through
the injective inclusion into singular chains (`CoefficientH0.singularGenerator_boundary`,
`coverSmallGeneratorOfMem_comp_ι`), or compute with the simplicial-set face maps of
`coverSmallSSet U` directly; a face is the simplex precomposed with a face inclusion
of the standard simplex, so its range is contained in the original range. -/
theorem smallChains_d_span {X α : Type} [TopologicalSpace X] (U : α → Set X) {k : ℕ}
    (t : SmallSimplex U (k + 1)) :
    (CoefficientSmallPath.coverSmallChains ℚ U).d (k + 1) k (smallGen U t 1) ∈
      Submodule.span ℚ {x | ∃ t' : SmallSimplex U k,
        smallRange U t' ⊆ smallRange U t ∧ x = smallGen U t' 1} := by
  sorry

/-- The boundary of a small 1-simplex is a difference of two small 0-generators
(the alternating face sum with two terms). -/
theorem smallChains_d_one {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (t : SmallSimplex U 1) :
    ∃ t₀ t₁ : SmallSimplex U 0,
      (CoefficientSmallPath.coverSmallChains ℚ U).d 1 0 (smallGen U t 1) =
        smallGen U t₀ 1 - smallGen U t₁ 1 := by
  sorry

theorem smallToFace_aux_fill_succ {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) {k : ℕ} (t : SmallSimplex (starCover K) (k + 2))
    (c : FaceModule K (k + 1))
    (hc : ∀ u, c u ≠ 0 → u.1 ∈ starCarrier K (smallRange _ t)) (hcyc : d k c = 0) :
    ∃ w : FaceModule K (k + 2),
      (∀ u, w u ≠ 0 → u.1 ∈ starCarrier K (smallRange _ t)) ∧ d (k + 1) w = c := by
  obtain ⟨a, ha⟩ := smallSimplex_range_subset (starCover K) t
  exact coneSupported_cycle_bounds o K d hd _ a (fun s hs => starCarrier_faces K _ hs)
    (fun s hs u hu hne => starCarrier_down K _ hs hu hne)
    (fun s hs => starCarrier_cone K ha hs) c hc hcyc

theorem smallToFace_aux_fill_zero {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (t : SmallSimplex (starCover K) 1)
    (c : FaceModule K 0)
    (hc : ∀ u, c u ≠ 0 → u.1 ∈ starCarrier K (smallRange _ t))
    (hsum : (c.sum fun _ x ↦ x) = 0) :
    ∃ w : FaceModule K 1,
      (∀ u, w u ≠ 0 → u.1 ∈ starCarrier K (smallRange _ t)) ∧ d 0 w = c := by
  obtain ⟨a, ha⟩ := smallSimplex_range_subset (starCover K) t
  exact coneSupported_zero_bounds o K d hd _ a (fun s hs => starCarrier_faces K _ hs)
    (fun s hs u hu hne => starCarrier_down K _ hs hu hne)
    (fun s hs => starCarrier_cone K ha hs) c hc hsum

/-- One stage of the recursion for `ψ`: two consecutive components, both carried
by `starCarrier` of the generator's image, commuting with the differentials. -/
structure SmallStage {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k) (k : ℕ) where
  f : (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).X k ⟶ FaceModuleCat K k
  f' : (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).X (k + 1) ⟶
    FaceModuleCat K (k + 1)
  cf : ∀ (t : SmallSimplex (starCover K) k) (u : FaceIndex K k),
    (show FaceModule K k from f (smallGen _ t 1)) u ≠ 0 →
      u.1 ∈ starCarrier K (smallRange _ t)
  cf' : ∀ (t : SmallSimplex (starCover K) (k + 1)) (u : FaceIndex K (k + 1)),
    (show FaceModule K (k + 1) from f' (smallGen _ t 1)) u ≠ 0 →
      u.1 ∈ starCarrier K (smallRange _ t)
  comm : f' ≫ d k = (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).d (k + 1) k ≫ f

/-- The first stage, with coefficient sum one in degree zero. Degree 0: on a small
point `t`, send it to `single {v} 1` for a vertex `v` of a minimal face of the point
(`exists_isMinimalFace`; `{v}` is in `starCarrier` by `starCarrier_down`); define the
component by `Sigma.desc` of `CoefficientSmallComparison.elementHom`. Degree 1: on a
small 1-simplex `t`, `f (d (smallGen t 1))` has coefficient sum `1 - 1 = 0`
(`smallChains_d_one`) and is carried by `starCarrier K (smallRange t)`
(`smallChains_d_span`, `starCarrier_mono`, span induction), so fill it with
`smallToFace_aux_fill_zero`. `comm` holds on generators (`Limits.Sigma.hom_ext`). -/
theorem smallToFace_aux_base {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) :
    ∃ S : SmallStage K d 0, ∀ t : SmallSimplex (starCover K) 0,
      ((show FaceModule K 0 from S.f (smallGen _ t 1)).sum fun _ c ↦ c) = 1 := by
  sorry

/-- Extend a stage by one degree, keeping its top component. On a small simplex
`t` of degree `k + 2`, `c = S.f' (d (smallGen t 1))` is carried by
`starCarrier K (smallRange t)` (`smallChains_d_span`, `S.cf'`, `starCarrier_mono`,
span induction) and is a cycle (`S.comm` and `d ≫ d = 0` in the small complex), so
fill it with `smallToFace_aux_fill_succ`. The new top component is the
`Sigma.desc` of the fillings; `comm` holds on generators. -/
theorem smallToFace_aux_step {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) {k : ℕ} (S : SmallStage K d k) :
    ∃ S' : SmallStage K d (k + 1), S'.f = S.f' := by
  sorry

/-- The acyclic-carrier chain map from small chains to ordered faces. Build the
components by recursion on degree, as in `AcyclicCarriers.carried_chainHomotopy_exists`
(a `CarriedStage`-style structure carrying two consecutive components). Degree 0:
send a small point `p` to the vertex `{v}` for a vertex `v` of a minimal face of
`p` (`exists_isMinimalFace`). Degree `k+1`: on a small simplex `σ` with range in
`starCover K a`, `ψ (d σ)` is a cycle supported in `starCarrier K (range σ)`
(faces of `σ` have smaller range, `starCarrier_mono`), so choose a filling from
`coneSupported_cycle_bounds` (degree 1: `coneSupported_zero_bounds`, the
coefficient sum of `ψ (d σ)` being `1 - 1`), with `Λ = starCarrier K (range σ)`
(`starCarrier_faces`, `starCarrier_down`, `starCarrier_cone`). The small chain
modules are coproducts over small simplices (`CoefficientSmallPath.coverSmallChains`),
so a component is a `Sigma.desc`; `coverSmallGenerator` names the generators. -/
theorem smallToFace_exists {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0) :
    ∃ ψ : CoefficientSmallPath.coverSmallChains ℚ (starCover K) ⟶ ChainComplex.of _ d hdd,
      (∀ k (σ : C(stdSimplex ℝ (Fin (k + 1)), K.space)) (a : Euc n)
          (hσ : Set.range σ ⊆ starCover K a) (u : FaceIndex K k),
        (show FaceModule K k from ψ.f k
          (CoefficientSmallPath.coverSmallGenerator ℚ (starCover K) σ a hσ 1)) u ≠ 0 →
          u.1 ∈ starCarrier K (Set.range σ)) ∧
      (∀ (σ : C(stdSimplex ℝ (Fin 1), K.space)) (a : Euc n)
          (hσ : Set.range σ ⊆ starCover K a),
        ((show FaceModule K 0 from ψ.f 0
          (CoefficientSmallPath.coverSmallGenerator ℚ (starCover K) σ a hσ 1)).sum
            fun _ c ↦ c) = 1) := by
  classical
  obtain ⟨S0, hS0⟩ := smallToFace_aux_base o K d hd
  have hstep : ∀ k (S : SmallStage K d k), ∃ S' : SmallStage K d (k + 1), S'.f = S.f' :=
    fun k S => smallToFace_aux_step o K d hd S
  choose g hg using hstep
  let st : ∀ k, SmallStage K d k := fun k => Nat.rec S0 (fun k S => g k S) k
  have hst : ∀ k, (st (k + 1)).f = (st k).f' := fun k => hg k (st k)
  let ψ : CoefficientSmallPath.coverSmallChains ℚ (starCover K) ⟶ ChainComplex.of _ d hdd :=
    { f := fun k => (st k).f
      comm' := by
        rintro i j (rfl : j + 1 = i)
        rw [ChainComplex.of_d, hst j]
        exact (st j).comm }
  refine ⟨ψ, ?_, ?_⟩
  · intro k σ a hσ u hu
    obtain ⟨t, ht, hrange⟩ := coverSmallGenerator_eq_smallGen (starCover K) σ a hσ
    rw [← hrange]
    rw [ht] at hu
    exact (st k).cf t u hu
  · intro σ a hσ
    obtain ⟨t, ht, -⟩ := coverSmallGenerator_eq_smallGen (starCover K) σ a hσ
    rw [ht]
    exact hS0 t

/-- `ψ ≫ cmpH` and the small-chain inclusion agree on homology. They are chain
homotopic by acyclic carriers with source the small chains: a small simplex `σ`
is carried by the polyhedron of `starCarrier K (Set.range σ)` (it contains `range σ`
by `subset_starCarrier_hull`, and contains `cmp` of each carrier face because
`IsAffineComparison` gives range equal to the face hull). The carrier is rationally
pointlike (`starCarrier_pointlike`), so carried cycles bound carried chains in
positive degree (`AcyclicCarriers.subsetCarriedCycle_bounds`). In degree zero the
two maps send a small point to points of the same star-shaped carrier, whose
difference bounds there (H₀ of a pointlike space). Build the homotopy degree by
degree as in `AcyclicCarriers.carried_chainHomotopy_exists`. -/
theorem smallToFace_homology {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (cmp : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (hcmp : IsAffineComparison K cmp)
    (cmpH : ChainComplex.of _ d hdd ⟶ CoefficientH0.SingularChains ℚ (TopCat.of K.space))
    (cmpH_f : ∀ k, cmpH.f k = cmp k)
    (ψ : CoefficientSmallPath.coverSmallChains ℚ (starCover K) ⟶ ChainComplex.of _ d hdd)
    (hψ : ∀ k (σ : C(stdSimplex ℝ (Fin (k + 1)), K.space)) (a : Euc n)
          (hσ : Set.range σ ⊆ starCover K a) (u : FaceIndex K k),
        (show FaceModule K k from ψ.f k
          (CoefficientSmallPath.coverSmallGenerator ℚ (starCover K) σ a hσ 1)) u ≠ 0 →
          u.1 ∈ starCarrier K (Set.range σ))
    (hψ0 : ∀ (σ : C(stdSimplex ℝ (Fin 1), K.space)) (a : Euc n)
          (hσ : Set.range σ ⊆ starCover K a),
        ((show FaceModule K 0 from ψ.f 0
          (CoefficientSmallPath.coverSmallGenerator ℚ (starCover K) σ a hσ 1)).sum
            fun _ c ↦ c) = 1) :
    ∀ k, HomologicalComplex.homologyMap (ψ ≫ cmpH) k =
      HomologicalComplex.homologyMap
        (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)) k := by
  sorry

/-- A chain endomorphism of the ordered-face complex that sends each face into
chains on its own subsets, and is the identity in degree zero, is the identity on
homology. It is chain homotopic to `𝟙` by acyclic carriers with carrier
`Λ s = {u | u.Nonempty ∧ u ⊆ s}` (a cone on any vertex of `s`), filling with
`coneSupported_cycle_bounds`; build the homotopy degree by degree as in
`AcyclicCarriers.carried_chainHomotopy_exists`, starting from `F.f 0 = 𝟙`. -/
theorem faceCarried_endo_homology {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (F : ChainComplex.of _ d hdd ⟶ ChainComplex.of _ d hdd)
    (hF : ∀ k (s : FaceIndex K k) (u : FaceIndex K k),
      (show FaceModule K k from F.f k (Finsupp.single s 1)) u ≠ 0 → u.1 ⊆ s.1)
    (h0 : F.f 0 = 𝟙 _) :
    ∀ k, HomologicalComplex.homologyMap F k = 𝟙 _ := by
  classical
  have hdiag : ∀ k (s : FaceIndex K k),
      F.f k (Finsupp.single s 1) =
        Finsupp.single s ((show FaceModule K k from
          F.f k (Finsupp.single s 1)) s) := by
    intro k s
    apply Finsupp.ext
    intro u
    by_cases hus : u = s
    · subst u
      simp only [Finsupp.single_eq_same]
    · rw [Finsupp.single_apply]
      simp only [hus, ↓reduceIte]
      rw [if_neg (Ne.symm hus)]
      by_contra hu
      have hsub := hF k s u hu
      have heq : u.1 = s.1 := Finset.eq_of_subset_of_card_le hsub (by
        rw [u.2.2, s.2.2])
      apply hus
      exact Subtype.ext heq
  have hcomp : ∀ k, F.f k = 𝟙 _ := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext'
      intro s
      apply LinearMap.ext_ring
      simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
        ModuleCat.hom_id, LinearMap.id_coe, id_eq]
      suffices F.f (k + 1) (Finsupp.single s 1) = Finsupp.single s 1 by
        exact this
      rw [hdiag]
      let v : Euc n := s.1.min' (by
        rw [Finset.nonempty_iff_ne_empty]
        intro hs
        have := s.2.2
        rw [hs, Finset.card_empty] at this
        omega)
      have hv : v ∈ s.1 := Finset.min'_mem _ _
      have herase_ne : (s.1.erase v).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro he
        have hc := Finset.card_erase_of_mem hv
        rw [he, Finset.card_empty, s.2.2] at hc
        omega
      have herase_face : s.1.erase v ∈ K.faces :=
        K.down_closed s.2.1 (Finset.erase_subset _ _) herase_ne
      let t : FaceIndex K k := ⟨s.1.erase v, herase_face, by
        rw [Finset.card_erase_of_mem hv, s.2.2]
        omega⟩
      obtain ⟨z, hz, hzformula⟩ := hd k s
      have hcomm : F.f (k + 1) ≫ d k = d k ≫ F.f k := by
        simpa only [ChainComplex.of_d] using F.comm (k + 1) k
      rw [ih] at hcomm
      have hcomm' : F.f (k + 1) ≫ d k = d k := by simpa using hcomm
      have heval := congrArg (fun f => f (Finsupp.single s 1)) hcomm'
      simp only [CategoryTheory.comp_apply] at heval
      rw [hdiag] at heval
      rw [show Finsupp.single s
          ((show FaceModule K (k + 1) from F.f (k + 1) (Finsupp.single s 1)) s) =
          ((show FaceModule K (k + 1) from F.f (k + 1) (Finsupp.single s 1)) s) •
            Finsupp.single s 1 by simp] at heval
      change (d k).hom
          (((show FaceModule K (k + 1) from F.f (k + 1) (Finsupp.single s 1)) s) •
            Finsupp.single s 1) = (d k).hom (Finsupp.single s 1) at heval
      rw [(d k).hom.map_smul, hz] at heval
      have ht := congrArg (fun x : FaceModule K k => x t) heval
      simp only [Finsupp.smul_apply, hzformula, t] at ht
      rw [Finset.sum_eq_single v] at ht
      · simp only [Finset.erase_eq_self, hv, not_true_eq_false, ↓reduceIte,
          one_mul] at ht
        apply Finsupp.ext
        intro u
        rw [Finsupp.single_apply, Finsupp.single_apply]
        split_ifs with hu
        · subst u
          simpa using ht
        · rfl
      · intro b hb hbv
        split_ifs with h
        · have : b = v := (Finset.erase_inj s.1 hb).mp h
          exact (hbv this).elim
        · rfl
      · intro hv'
        exact (hv' hv).elim
  intro k
  have hFid : F = 𝟙 _ := by
    apply HomologicalComplex.Hom.ext
    funext j
    exact hcomp j
  subst F
  exact HomologicalComplex.homologyMap_id _ _

/-- Uniformly iterated subdivision makes the affine comparison small, and it lifts
through the small-chain inclusion. There are finitely many faces in all degrees
together (`hK`; `FaceIndex K k` is empty once `k + 1` exceeds every face card), so
one `r` works for all generators (`CoefficientEventualSmallness.actual_chain_eventual`
gives `∀ k ≥ N`). The inclusion is injective in each degree (it is induced by
an inclusion of simplicial sets), so the chosen lifts of the generators assemble
into a chain map. -/
theorem affineCmp_small_lift {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (hK : K.faces.Finite)
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (cmpH : ChainComplex.of _ d hdd ⟶ CoefficientH0.SingularChains ℚ (TopCat.of K.space)) :
    ∃ (r : ℕ) (Φ : ChainComplex.of _ d hdd ⟶
        CoefficientSmallPath.coverSmallChains ℚ (starCover K)),
      Φ ≫ CoefficientSmallPath.coverSmallInclusion ℚ (starCover K) =
        cmpH ≫ CoefficientEventualSmallness.subdivisionIterate ℚ r := by
  sorry

/-- Iterated singular subdivision keeps a chain inside a subset: subdivision is
natural (`CoefficientSingularSubdivision`, or `subsetPush` naturality), and a chain
is carried by `A` exactly when it is in the range of `AcyclicCarriers.subsetPush`
(`subsetPush_lift`, `subsetPush_carried`). -/
theorem subdivisionIterate_subsetCarried {X : Type} [TopologicalSpace X] (A : Set X)
    (r : ℕ) {k : ℕ} (c : (CoefficientH0.SingularChains ℚ (TopCat.of X)).X k)
    (hc : AcyclicCarriers.SubsetCarriedChain X A c) :
    AcyclicCarriers.SubsetCarriedChain X A
      ((CoefficientEventualSmallness.subdivisionIterate ℚ r).f k c) := by
  sorry

/-- A small chain whose image in all singular chains is carried by `A` is a
combination of small generators with range in `A`. The small chain module is a
coproduct over small simplices and the inclusion is injective on it; compare
coefficients of `Sigma.ι` summands. -/
theorem smallChain_span_of_subsetCarried {X α : Type} [TopologicalSpace X]
    (U : α → Set X) (A : Set X) {k : ℕ}
    (q : (CoefficientSmallPath.coverSmallChains ℚ U).X k)
    (hq : AcyclicCarriers.SubsetCarriedChain X A
      ((CoefficientSmallPath.coverSmallInclusion ℚ U).f k q)) :
    q ∈ Submodule.span ℚ {x | ∃ (σ : C(stdSimplex ℝ (Fin (k + 1)), X)) (a : α)
      (hσ : Set.range σ ⊆ U a), Set.range σ ⊆ A ∧
        x = CoefficientSmallPath.coverSmallGenerator ℚ U σ a hσ 1} := by
  sorry

/-- `Φ ≫ ψ` is face-carried and the identity in degree zero. Positive degree:
`Φ (single s)` maps to `Sd^r (cmp s)`, which is carried by the hull of `s`
(`IsAffineComparison`, `subdivisionIterate_subsetCarried`), so `Φ (single s)` is a
combination of small generators with range in the hull
(`smallChain_span_of_subsetCarried`); each goes under `ψ` to faces under a minimal
face of a point of the hull of `s`, which is a subset of `s`
(`isMinimalFace_subset`). Degree zero: subdivision fixes 0-simplices, the minimal
face of a vertex `v` is `{v}`, and `hψ0` fixes the coefficient. -/
theorem smallLift_comp_carried {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (cmp : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (hcmp : IsAffineComparison K cmp)
    (cmpH : ChainComplex.of _ d hdd ⟶ CoefficientH0.SingularChains ℚ (TopCat.of K.space))
    (cmpH_f : ∀ k, cmpH.f k = cmp k) (r : ℕ)
    (Φ : ChainComplex.of _ d hdd ⟶ CoefficientSmallPath.coverSmallChains ℚ (starCover K))
    (hΦ : Φ ≫ CoefficientSmallPath.coverSmallInclusion ℚ (starCover K) =
        cmpH ≫ CoefficientEventualSmallness.subdivisionIterate ℚ r)
    (ψ : CoefficientSmallPath.coverSmallChains ℚ (starCover K) ⟶ ChainComplex.of _ d hdd)
    (hψ : ∀ k (σ : C(stdSimplex ℝ (Fin (k + 1)), K.space)) (a : Euc n)
          (hσ : Set.range σ ⊆ starCover K a) (u : FaceIndex K k),
        (show FaceModule K k from ψ.f k
          (CoefficientSmallPath.coverSmallGenerator ℚ (starCover K) σ a hσ 1)) u ≠ 0 →
          u.1 ∈ starCarrier K (Set.range σ))
    (hψ0 : ∀ (σ : C(stdSimplex ℝ (Fin 1), K.space)) (a : Euc n)
          (hσ : Set.range σ ⊆ starCover K a),
        ((show FaceModule K 0 from ψ.f 0
          (CoefficientSmallPath.coverSmallGenerator ℚ (starCover K) σ a hσ 1)).sum
            fun _ c ↦ c) = 1) :
    (∀ k (s : FaceIndex K k) (u : FaceIndex K k),
      (show FaceModule K k from (Φ ≫ ψ).f k (Finsupp.single s 1)) u ≠ 0 → u.1 ⊆ s.1) ∧
    (Φ ≫ ψ).f 0 = 𝟙 _ := by
  sorry

/-- Surjectivity for a packaged affine comparison. With `ψ` from
`smallToFace_exists`, `smallToFace_homology` gives
`H(ψ) ≫ H(cmpH) = H(inc)`, and `H(inc)` is an isomorphism
(`CoefficientSmallComparison.inclusion_isIso` with `starCover_isOpen`,
`starCover_covers`), so every class is `H(cmpH)` of `H(ψ) (H(inc)⁻¹ x)`. -/
theorem package_homology_surjective {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (cmp : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (hcmp : IsAffineComparison K cmp)
    (cmpH : ChainComplex.of _ d hdd ⟶ CoefficientH0.SingularChains ℚ (TopCat.of K.space))
    (cmpH_f : ∀ k, cmpH.f k = cmp k) (k : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap cmpH k).hom := by
  sorry

/-- Injectivity for a packaged affine comparison. Take `r, Φ` from
`affineCmp_small_lift` and `ψ` from `smallToFace_exists`. By
`smallLift_comp_carried` and `faceCarried_endo_homology`, `H(Φ) ≫ H(ψ) = 𝟙`.
From `hΦ` and `CoefficientIteratedHomotopy.absolute_homology_identity`,
`H(Φ) ≫ H(inc) = H(cmpH)`. If `H(cmpH) x = 0` then `H(inc) (H(Φ) x) = 0`, so
`H(Φ) x = 0` (`inclusion_isIso`), so `x = H(ψ) (H(Φ) x) = 0`. -/
theorem package_homology_injective {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (cmp : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (hcmp : IsAffineComparison K cmp)
    (cmpH : ChainComplex.of _ d hdd ⟶ CoefficientH0.SingularChains ℚ (TopCat.of K.space))
    (cmpH_f : ∀ k, cmpH.f k = cmp k) (k : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap cmpH k).hom := by
  sorry

/-- Injective half for the concrete affine comparison, in `ChainComplex.ofHom`
form. Apply `package_homology_injective` to `cmpH := q ≫ e`, where `q` is the
`ofHom` map below and `e` is the identity from `ChainComplex.of _ (C.d (j+1) j) _`
to `C` (the map `e` in `SimplicialChainMaps.orientedPackage_homology_bijective`).
`IsAffineComparison` for `affineCmp` is `⟨faceSimplex o s, affineCmp_single o K k s,
faceSimplex_range o s⟩`. Then `H(q ≫ e) = H(q) ≫ H(e)` and `Function.Injective.of_comp`. -/
theorem affineCmp_homologyMap_injective {n : ℕ}
    (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0) (k : ℕ) :
    Function.Injective
      (HomologicalComplex.homologyMap
        (ChainComplex.ofHom _ _ hdd _ _
          (fun j => (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d_comp_d
            (j + 2) (j + 1) j) (affineCmp o K) (affineCmp_comm o K d hd)) k).hom := by
  sorry

/-- Surjective half for the concrete affine comparison, in `ChainComplex.ofHom`
form. As for the injective half, apply `package_homology_surjective` to
`cmpH := q ≫ e`; since `H(e)` is bijective (`e` is an isomorphism), surjectivity
of `H(e) ∘ H(q)` gives surjectivity of `H(q)`. -/
theorem affineCmp_homologyMap_surjective {n : ℕ}
    (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0) (k : ℕ) :
    Function.Surjective
      (HomologicalComplex.homologyMap
        (ChainComplex.ofHom _ _ hdd _ _
          (fun j => (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d_comp_d
            (j + 2) (j + 1) j) (affineCmp o K) (affineCmp_comm o K d hd)) k).hom := by
  sorry

/-- The concrete affine comparison is the reference quasi-isomorphism. -/
theorem affine_reference_quasiIso_exists {n : ℕ}
    (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0) :
    ∃ cmp₀ : ∀ k, FaceModuleCat K k ⟶
        (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k,
      IsAffineComparison K cmp₀ ∧
      (∃ hchain₀ : ∀ k, cmp₀ (k + 1) ≫
          (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 1) k =
        d k ≫ cmp₀ k,
        ∀ k, Function.Bijective
          (HomologicalComplex.homologyMap
            (ChainComplex.ofHom _ _ hdd _ _
              (fun k => (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d_comp_d
              (k + 2) (k + 1) k) cmp₀ hchain₀) k).hom) := by
  refine ⟨affineCmp o K, ?_, affineCmp_comm o K d hd, ?_⟩
  · intro k s
    exact ⟨faceSimplex o s, affineCmp_single o K k s, faceSimplex_range o s⟩
  · intro k
    exact ⟨affineCmp_homologyMap_injective o K hK d hd hdd k,
      affineCmp_homologyMap_surjective o K hK d hd hdd k⟩

/-- The ordered-face comparison theorem, with the statement kept identical to
`OrientedSimplicialChains.orderedFace_singular_quasiIso`. -/
theorem orderedFace_singular_quasiIso {n : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (cmp : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (hcmp : IsAffineComparison K cmp)
    (hchain : ∀ k, cmp (k + 1) ≫
        (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 1) k =
      d k ≫ cmp k) :
    ∀ k, Function.Bijective
      (HomologicalComplex.homologyMap
        (ChainComplex.ofHom _ _ hdd _ _
          (fun k => (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d_comp_d
            (k + 2) (k + 1) k) cmp hchain) k).hom := by
  obtain ⟨cmp₀, hcmp₀, hchain₀, hbij⟩ :=
    affine_reference_quasiIso_exists o K hK d hd hdd
  intro k
  rw [← affineComparison_homologyMap_eq o K d hd hdd cmp₀ cmp
    hcmp₀ hcmp hchain₀ hchain k]
  exact hbij k

#print axioms orderedFace_singular_quasiIso

end ConstructionTargets.SimplicialSingularComparison
