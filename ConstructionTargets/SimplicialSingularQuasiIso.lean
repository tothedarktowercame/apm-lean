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
  let U : Set (Euc n) := ⋃ s ∈ starCarrier K A, convexHull ℝ (s : Set (Euc n))
  have hU_ne : U.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨t, ht⟩ := exists_isMinimalFace K x
    have htne : t.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      simpa [h] using ht.2.1
    refine ⟨x, Set.mem_iUnion₂.mpr ⟨t, ?_, ht.2.1⟩⟩
    exact ⟨htne, x, hx, t, ht, subset_rfl⟩
  have hU_star : StarConvex ℝ a U := by
    intro y hy b c hb hc hbc
    obtain ⟨s, hs, hys⟩ := Set.mem_iUnion₂.mp hy
    have his : insert a s ∈ starCarrier K A := starCarrier_cone K hA hs
    have ha : a ∈ convexHull ℝ ((insert a s : Finset (Euc n)) : Set (Euc n)) :=
      (subset_convexHull ℝ ((insert a s : Finset (Euc n)) : Set (Euc n)))
        (by exact Finset.mem_insert_self a s)
    refine Set.mem_iUnion₂.mpr ⟨insert a s, his, ?_⟩
    apply (convex_convexHull ℝ ((insert a s : Finset (Euc n)) : Set (Euc n)))
      ha
      (convexHull_mono (by exact_mod_cast Finset.subset_insert a s) hys)
      hb hc hbc
  have hU_space : U ⊆ K.space := by
    intro y hy
    obtain ⟨s, hs, hys⟩ := Set.mem_iUnion₂.mp hy
    exact K.convexHull_subset_space (starCarrier_faces K A hs) hys
  letI : ContractibleSpace U := hU_star.contractibleSpace hU_ne
  have hU_point : ProjectivePlaneWedgeRationalHomology.RationallyPointlike U := by
    obtain ⟨e⟩ := ContractibleSpace.hequiv_unit U
    exact ProjectivePlaneWedgeRationalHomology.rationallyPointlike_of_homotopyEquiv e
      ProjectivePlaneWedgeRationalHomology.rationallyPointlike_unit
  let e : ((Subtype.val : K.space → Euc n) ⁻¹' U) ≃ₜ U :=
    { toEquiv :=
        { toFun := fun x => ⟨x.1.1, x.2⟩
          invFun := fun x => ⟨⟨x.1, hU_space x.2⟩, x.2⟩
          left_inv := fun x => by ext; rfl
          right_inv := fun x => by ext; rfl }
      continuous_toFun :=
        continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _
      continuous_invFun :=
        (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  exact ProjectivePlaneWedgeRationalHomology.rationallyPointlike_of_homotopyEquiv
    e.toHomotopyEquiv hU_point

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
  exact SingularSubdivision.range_subset_of_singularSimplex_mem_coverSmallSSet
    U t.1 t.2

/-- `coverSmallGenerator` is `smallGen` at the small simplex of `σ`, whose image is
the range of `σ` (`continuousMapOfSingularSimplex_ofContinuousMap`). The equation
should be `rfl` after unfolding `coverSmallGenerator`. -/
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

/-- The boundary of a small generator is a combination of small generators at its
faces, and each face has smaller image. Use the generator boundary formula through
the injective inclusion into singular chains (`CoefficientH0.singularGenerator_boundary`,
`coverSmallGeneratorOfMem_comp_ι`), or compute with the simplicial-set face maps of
`coverSmallSSet U` directly; a face is the simplex precomposed with a face inclusion
of the standard simplex, so its range is contained in the original range. -/
lemma smallChains_d_span_aux_boundary {X α : Type} [TopologicalSpace X]
    (U : α → Set X) {k : ℕ} (t : SmallSimplex U (k + 1)) :
    smallGen U t ≫ (CoefficientSmallPath.coverSmallChains ℚ U).d (k + 1) k =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        smallGen U ((SingularSubdivision.coverSmallSSet U : SSet).δ i t) := by
  dsimp [smallGen, CoefficientSmallPath.coverSmallChains,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  unfold AlgebraicTopology.AlternatingFaceMapComplex.objD
  calc
    _ = ∑ i : Fin (k + 2), Limits.Sigma.ι
          (fun _ : SmallSimplex U (k + 1) ↦ ModuleCat.of ℚ ℚ) t ≫
        ((-1 : ℤ) ^ (i : ℕ) •
          ((((SimplicialObject.whiskering Type (ModuleCat ℚ)).obj
              (CategoryTheory.Limits.sigmaConst.obj (ModuleCat.of ℚ ℚ))).obj
                (SingularSubdivision.coverSmallSSet U : SSet)).δ i)) := by
      simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte]
        using Preadditive.comp_sum (Finset.univ : Finset (Fin (k + 2)))
          (Limits.Sigma.ι
            (fun _ : SmallSimplex U (k + 1) ↦ ModuleCat.of ℚ ℚ) t)
          (fun i ↦ (-1 : ℤ) ^ (i : ℕ) •
            ((((SimplicialObject.whiskering Type (ModuleCat ℚ)).obj
              (CategoryTheory.Limits.sigmaConst.obj (ModuleCat.of ℚ ℚ))).obj
                (SingularSubdivision.coverSmallSSet U : SSet)).δ i))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = (-1 : ℤ) ^ (i : ℕ) •
            (Limits.Sigma.ι (fun _ : SmallSimplex U (k + 1) ↦
              ModuleCat.of ℚ ℚ) t ≫
              ((((SimplicialObject.whiskering Type (ModuleCat ℚ)).obj
                (CategoryTheory.Limits.sigmaConst.obj (ModuleCat.of ℚ ℚ))).obj
                  (SingularSubdivision.coverSmallSSet U : SSet)).δ i)) := by
          exact CategoryTheory.Preadditive.comp_zsmul _ _ _
        _ = _ := by
          congr 1
          dsimp [SimplicialObject.δ, SimplicialObject.whiskering,
            CategoryTheory.Limits.sigmaConst]
          rw [Limits.Sigma.ι_comp_map']
          rfl

theorem smallChains_d_span {X α : Type} [TopologicalSpace X] (U : α → Set X) {k : ℕ}
    (t : SmallSimplex U (k + 1)) :
    (CoefficientSmallPath.coverSmallChains ℚ U).d (k + 1) k (smallGen U t 1) ∈
      Submodule.span ℚ {x | ∃ t' : SmallSimplex U k,
        smallRange U t' ⊆ smallRange U t ∧ x = smallGen U t' 1} := by
  classical
  rw [← CategoryTheory.comp_apply, smallChains_d_span_aux_boundary]
  simp only [ModuleCat.hom_sum, LinearMap.coe_sum, Finset.sum_apply,
    ModuleCat.hom_zsmul]
  apply Submodule.sum_mem
  intro i _
  change ((-1 : ℤ) ^ (i : ℕ)) •
    smallGen U ((SingularSubdivision.coverSmallSSet U : SSet).δ i t) 1 ∈ _
  rw [← Int.cast_smul_eq_zsmul ℚ]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨(SingularSubdivision.coverSmallSSet U : SSet).δ i t, ?_, rfl⟩
  let σ := SingularSubdivision.continuousMapOfSingularSimplex (k + 1) t.1
  have hσ : SingularSubdivision.singularSimplexOfContinuousMap (TopCat.of X) (k + 1) σ =
      t.1 := Equiv.symm_apply_apply _ _
  dsimp [smallRange]
  rw [show ((SingularSubdivision.coverSmallSSet U : SSet).δ i t).1 =
      (TopCat.toSSet.obj (TopCat.of X)).δ i t.1 from rfl]
  rw [← hσ, SingularSubdivision.singularSimplexOfContinuousMap_face]
  simp only [SingularSubdivision.continuousMapOfSingularSimplex_ofContinuousMap]
  rintro x ⟨y, rfl⟩
  exact ⟨_, rfl⟩

/-- The boundary of a small 1-chain has augmentation zero: the inclusion is a chain
map and `CoefficientH0.boundary_comp_zeroChainAugmentation_eq_zero`. (Replaces an
explicit two-face formula, whose coproduct computation timed out.) -/
theorem smallChains_d_aug {X α : Type} [TopologicalSpace X] (U : α → Set X) :
    (CoefficientSmallPath.coverSmallChains ℚ U).d 1 0 ≫
      (CoefficientSmallPath.coverSmallInclusion ℚ U).f 0 ≫
        CoefficientH0.zeroChainAugmentation ℚ = 0 := by
  rw [← Category.assoc, ← (CoefficientSmallPath.coverSmallInclusion ℚ U).comm 1 0,
    Category.assoc, CoefficientH0.boundary_comp_zeroChainAugmentation_eq_zero,
    Limits.comp_zero]

/-- A small point has augmentation one: the inclusion sends `smallGen U t` to the
singular generator of `t.1` (as in `singCoeff_inclusion`), and the augmentation is
`Sigma.desc` of identities (`Limits.Sigma.ι_desc`). -/
theorem smallGen_aug {X α : Type} [TopologicalSpace X] (U : α → Set X)
    (t : SmallSimplex U 0) :
    smallGen U t ≫ (CoefficientSmallPath.coverSmallInclusion ℚ U).f 0 ≫
      CoefficientH0.zeroChainAugmentation ℚ = 𝟙 _ := by
  dsimp [smallGen, CoefficientSmallPath.coverSmallInclusion,
    CoefficientSmallPath.coverSmallChains, CoefficientH0.SingularChains,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor,
    CoefficientH0.zeroChainAugmentation]
  rw [← Category.assoc, Limits.Sigma.ι_comp_map', Category.assoc,
    Limits.Sigma.ι_desc, Category.comp_id]

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
small 1-simplex `t`, `f (d (smallGen t 1))` has coefficient sum zero: the
coefficient-sum map `FaceModule K 0 → ℚ` composed after `f` equals
`inc.f 0 ≫ zeroChainAugmentation` (both are `1` on each generator, by the degree-0
definition and `smallGen_aug`; `Limits.Sigma.hom_ext`), and `smallChains_d_aug` and is carried by `starCarrier K (smallRange t)`
(`smallChains_d_span`, `starCarrier_mono`, span induction), so fill it with
`smallToFace_aux_fill_zero`. `comm` holds on generators (`Limits.Sigma.hom_ext`). -/
theorem smallToFace_aux_base {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) :
    ∃ S : SmallStage K d 0, ∀ t : SmallSimplex (starCover K) 0,
      ((show FaceModule K 0 from S.f (smallGen _ t 1)).sum fun _ c ↦ c) = 1 := by
  classical
  let C := CoefficientSmallPath.coverSmallChains ℚ (starCover K)
  have hq : ∀ t : SmallSimplex (starCover K) 0, ∃ q : FaceModule K 0,
      (∀ u, q u ≠ 0 → u.1 ∈ starCarrier K (smallRange _ t)) ∧
      q.sum (fun _ c ↦ c) = 1 := by
    intro t
    obtain ⟨x, hx⟩ := Set.range_nonempty
      (SingularSubdivision.continuousMapOfSingularSimplex 0 t.1)
    obtain ⟨s, hs⟩ := exists_isMinimalFace K x
    have hsne : s.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      simpa [h] using hs.2.1
    obtain ⟨v, hv⟩ := hsne
    have hvK : ({v} : Finset (Euc n)) ∈ K.faces :=
      K.down_closed hs.1 (by simpa using hv) (by simp)
    let u : FaceIndex K 0 := ⟨{v}, hvK, by simp⟩
    refine ⟨Finsupp.single u 1, ?_, by simp⟩
    intro u' hu'
    have huu : u' = u := by
      by_contra hne
      simp [Finsupp.single_apply, hne] at hu'
    subst u'
    refine ⟨by simp [u], x, hx, s, hs, ?_⟩
    · simpa [u] using hv
  choose q hqc hqsum using hq
  let f : C.X 0 ⟶ FaceModuleCat K 0 :=
    Limits.Sigma.desc (fun t => CoefficientSmallComparison.elementHom ℚ (q t))
  have hf (t : SmallSimplex (starCover K) 0) : f (smallGen _ t 1) = q t := by
    change (smallGen _ t ≫ f) 1 = _
    rw [show smallGen (starCover K) t ≫ f =
      CoefficientSmallComparison.elementHom ℚ (q t) from Limits.Sigma.ι_desc _ t]
    exact CoefficientSmallComparison.elementHom_one ℚ (M := FaceModuleCat K 0) (q t)
  let aug : FaceModuleCat K 0 ⟶ ModuleCat.of ℚ ℚ :=
    ModuleCat.ofHom
      (Finsupp.lsum ℚ (fun _ : FaceIndex K 0 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)))
  have haug : f ≫ aug =
      (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)).f 0 ≫
        CoefficientH0.zeroChainAugmentation ℚ := by
    apply Limits.Sigma.hom_ext
    intro t
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    dsimp [aug]
    change (f (smallGen _ t 1)).sum (fun _ c ↦ c) = _
    rw [hf, hqsum]
    have h := ConcreteCategory.congr_hom (smallGen_aug (starCover K) t) 1
    simpa [CategoryTheory.comp_apply] using h.symm
  have hfill : ∀ t : SmallSimplex (starCover K) 1, ∃ w : FaceModule K 1,
      (∀ u, w u ≠ 0 → u.1 ∈ starCarrier K (smallRange _ t)) ∧
      d 0 w = f (C.d 1 0 (smallGen _ t 1)) := by
    intro t
    apply smallToFace_aux_fill_zero o K d hd t
    · intro u hu
      have hs := smallChains_d_span (starCover K) t
      refine Submodule.span_induction (p := fun x _ =>
        ∀ u, (show FaceModule K 0 from f x) u ≠ 0 →
          u.1 ∈ starCarrier K (smallRange _ t)) ?_ ?_ ?_ ?_ hs u hu
      · rintro y ⟨t', ht', rfl⟩ u hu
        exact starCarrier_mono K ht' (hqc t' u (by simpa [hf] using hu))
      · intro u hu; simp at hu
      · intro x y hx hy ihx ihy u hu
        rw [map_add] at hu
        by_cases hxu : (show FaceModule K 0 from f x) u = 0
        · apply ihy u; simpa [hxu] using hu
        · exact ihx u hxu
      · intro a x hx ih u hu
        rw [map_smul] at hu
        apply ih u
        intro hz
        simp [hz] at hu
    · have he := ConcreteCategory.congr_hom haug (C.d 1 0 (smallGen _ t 1))
      have h := ConcreteCategory.congr_hom (smallChains_d_aug (starCover K))
        (smallGen _ t 1)
      dsimp [aug] at he
      have he' : (f (C.d 1 0 (smallGen _ t 1))).sum (fun _ c ↦ c) =
          ((CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)).f 0 ≫
            CoefficientH0.zeroChainAugmentation ℚ)
              (C.d 1 0 (smallGen _ t 1)) := by
        simpa only [id_eq, CategoryTheory.comp_apply] using he
      change (f (C.d 1 0 (smallGen _ t 1))).sum (fun _ c ↦ c) = 0
      rw [he']
      simpa [CategoryTheory.comp_apply] using h
  choose w hwc hwd using hfill
  let f' : C.X 1 ⟶ FaceModuleCat K 1 :=
    Limits.Sigma.desc (fun t => CoefficientSmallComparison.elementHom ℚ (w t))
  have hf' (t : SmallSimplex (starCover K) 1) : f' (smallGen _ t 1) = w t := by
    change (smallGen _ t ≫ f') 1 = _
    rw [show smallGen (starCover K) t ≫ f' =
      CoefficientSmallComparison.elementHom ℚ (w t) from Limits.Sigma.ι_desc _ t]
    exact CoefficientSmallComparison.elementHom_one ℚ (M := FaceModuleCat K 1) (w t)
  have hcf : ∀ (t : SmallSimplex (starCover K) 0) (u : FaceIndex K 0),
      (show FaceModule K 0 from f (smallGen _ t 1)) u ≠ 0 →
        u.1 ∈ starCarrier K (smallRange _ t) := by
    intro t u hu
    apply hqc t u
    simpa [hf] using hu
  have hcf' : ∀ (t : SmallSimplex (starCover K) 1) (u : FaceIndex K 1),
      (show FaceModule K 1 from f' (smallGen _ t 1)) u ≠ 0 →
        u.1 ∈ starCarrier K (smallRange _ t) := by
    intro t u hu
    apply hwc t u
    simpa [hf'] using hu
  refine ⟨{ f := f, f' := f', cf := hcf, cf' := hcf', comm := ?_ }, ?_⟩
  · apply Limits.Sigma.hom_ext
    intro t
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change d 0 (f' (smallGen _ t 1)) = f (C.d 1 0 (smallGen _ t 1))
    rw [hf', hwd]
  · intro t
    simpa [hf] using hqsum t

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
  classical
  let C := CoefficientSmallPath.coverSmallChains ℚ (starCover K)
  have hcarried (t : SmallSimplex (starCover K) (k + 2)) :
      ∀ x ∈ Submodule.span ℚ {x | ∃ t' : SmallSimplex (starCover K) (k + 1),
          smallRange _ t' ⊆ smallRange _ t ∧ x = smallGen _ t' 1},
        ∀ u, (show FaceModule K (k + 1) from S.f' x) u ≠ 0 →
          u.1 ∈ starCarrier K (smallRange _ t) := by
    intro x hx
    refine Submodule.span_induction
      (p := fun x _ => ∀ u, (show FaceModule K (k + 1) from S.f' x) u ≠ 0 →
        u.1 ∈ starCarrier K (smallRange _ t)) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨t', ht', rfl⟩ u hu
      exact starCarrier_mono K ht' (S.cf' t' u hu)
    · intro u hu
      simp at hu
    · intro x y hx hy ihx ihy u hu
      rw [map_add] at hu
      by_cases hxu : (show FaceModule K (k + 1) from S.f' x) u = 0
      · apply ihy u
        simpa [hxu] using hu
      · exact ihx u hxu
    · intro a x hx ih u hu
      rw [map_smul] at hu
      apply ih u
      intro hzero
      simp [hzero] at hu
  have hfill : ∀ t : SmallSimplex (starCover K) (k + 2),
      ∃ w : FaceModule K (k + 2),
        (∀ u, w u ≠ 0 → u.1 ∈ starCarrier K (smallRange _ t)) ∧
        d (k + 1) w = S.f' (C.d (k + 2) (k + 1) (smallGen _ t 1)) := by
    intro t
    apply smallToFace_aux_fill_succ o K d hd t
    · exact hcarried t _ (smallChains_d_span (starCover K) t)
    · have hcomm := ConcreteCategory.congr_hom S.comm
          (C.d (k + 2) (k + 1) (smallGen _ t 1))
      have hcomm' : d k (S.f' (C.d (k + 2) (k + 1) (smallGen _ t 1))) =
          S.f (C.d (k + 1) k (C.d (k + 2) (k + 1) (smallGen _ t 1))) := by
        simpa [CategoryTheory.comp_apply] using hcomm
      rw [hcomm']
      change S.f ((C.d (k + 2) (k + 1) ≫ C.d (k + 1) k)
        (smallGen _ t 1)) = 0
      rw [C.d_comp_d]
      simp
  choose w hwc hwd using hfill
  let f'' : C.X (k + 2) ⟶ FaceModuleCat K (k + 2) :=
    Limits.Sigma.desc (fun t => CoefficientSmallComparison.elementHom ℚ (w t))
  have hf'' (t : SmallSimplex (starCover K) (k + 2)) :
      f'' (smallGen _ t 1) = w t := by
    change (smallGen _ t ≫ f'') 1 = _
    rw [show smallGen (starCover K) t ≫ f'' =
        CoefficientSmallComparison.elementHom ℚ (w t) from Limits.Sigma.ι_desc _ t]
    simpa using (CoefficientSmallComparison.elementHom_one ℚ (M := FaceModuleCat K (k + 2)) (w t))
  refine ⟨{
    f := S.f'
    f' := f''
    cf := S.cf'
    cf' := fun t u hu => hwc t u (by simpa [hf''] using hu)
    comm := ?_ }, rfl⟩
  apply Limits.Sigma.hom_ext
  intro t
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change d (k + 1) (f'' (smallGen _ t 1)) =
    S.f' (C.d (k + 2) (k + 1) (smallGen _ t 1))
  rw [hf'', hwd]

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

/-- Every small generator is a `coverSmallGenerator` with the same image: take
`σ = continuousMapOfSingularSimplex k t.1`, `a` from `smallSimplex_range_subset`,
and compare with `coverSmallGenerator_eq_smallGen` (the small simplex it produces
is `t`, since `singularSimplexOfContinuousMap ∘ continuousMapOfSingularSimplex = id`
by `Equiv.symm_apply_apply`, and small simplices are equal when their underlying
simplices are, `Subtype.ext`). -/
theorem smallGen_eq_coverSmallGenerator {X α : Type} [TopologicalSpace X]
    (U : α → Set X) {k : ℕ} (t : SmallSimplex U k) :
    ∃ (σ : C(stdSimplex ℝ (Fin (k + 1)), X)) (a : α) (hσ : Set.range σ ⊆ U a),
      smallGen U t = CoefficientSmallPath.coverSmallGenerator ℚ U σ a hσ ∧
        Set.range σ = smallRange U t := by
  obtain ⟨a, ha⟩ := smallSimplex_range_subset U t
  let σ := SingularSubdivision.continuousMapOfSingularSimplex k t.1
  refine ⟨σ, a, ha, ?_, rfl⟩
  dsimp [smallGen, CoefficientSmallPath.coverSmallGenerator, σ]
  congr 1

/-- The properties of `ψ` from `smallToFace_exists`, in terms of `smallGen`. -/
def StarCarriedMap {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (ψ : CoefficientSmallPath.coverSmallChains ℚ (starCover K) ⟶ ChainComplex.of _ d hdd) :
    Prop :=
  (∀ k (t : SmallSimplex (starCover K) k) (u : FaceIndex K k),
    (show FaceModule K k from ψ.f k (smallGen _ t 1)) u ≠ 0 →
      u.1 ∈ starCarrier K (smallRange _ t)) ∧
  ∀ t : SmallSimplex (starCover K) 0,
    ((show FaceModule K 0 from ψ.f 0 (smallGen _ t 1)).sum fun _ c ↦ c) = 1

/-- The polyhedron of `starCarrier K A`, inside `K.space`. -/
def starHull {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n)) (A : Set K.space) :
    Set K.space :=
  (Subtype.val : K.space → Euc n) ⁻¹' ⋃ s ∈ starCarrier K A, convexHull ℝ (s : Set (Euc n))

/-- A map out of small chains whose value on each small generator `t` is carried by
`starHull K (smallRange t)`. -/
def SmallCarried {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n)) {k j : ℕ}
    (g : (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).X k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X j) : Prop :=
  ∀ t : SmallSimplex (starCover K) k,
    AcyclicCarriers.SubsetCarriedChain K.space (starHull K (smallRange _ t))
      (g (smallGen _ t 1))

/-- Restate the hypotheses of `smallToFace_homology` as `StarCarriedMap`, using
`smallGen_eq_coverSmallGenerator`. -/
theorem starCarriedMap_of_coverSmallGenerator {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
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
    StarCarriedMap K d hdd ψ := by
  refine ⟨fun k t u hu => ?_, fun t => ?_⟩
  · obtain ⟨σ, a, hσ, ht, hr⟩ := smallGen_eq_coverSmallGenerator (starCover K) t
    rw [ht] at hu
    rw [← hr]
    exact hψ k σ a hσ u hu
  · obtain ⟨σ, a, hσ, ht, -⟩ := smallGen_eq_coverSmallGenerator (starCover K) t
    rw [ht]
    exact hψ0 σ a hσ

/-- Carried chains are closed under subtraction: concatenate the two finite
presentations (`Fin.append`), negating the coefficients of the second. -/
theorem subsetCarriedChain_sub (X : Type) [TopologicalSpace X] (A : Set X) {k : ℕ}
    (x y : (CoefficientH0.SingularChains ℚ (TopCat.of X)).X k)
    (hx : AcyclicCarriers.SubsetCarriedChain X A x)
    (hy : AcyclicCarriers.SubsetCarriedChain X A y) :
    AcyclicCarriers.SubsetCarriedChain X A (x - y) := by
  exact
    SimplicialChainMaps.vertexChainMap_affineComparison_square_aux_carrier_homotopy_aux_sub
      X A x y hx hy

/-- The difference `ψ ≫ cmpH - inc` is small-carried. `inc (smallGen t)` is the
singular generator of `t` (`coverSmallGeneratorOfMem_comp_ι` in the `ℚ` form, or
via `smallGen_eq_coverSmallGenerator` and `CoefficientSmallPath`), whose range lies
in `starHull` by `subset_starCarrier_hull`. `ψ (smallGen t)` is a combination of
faces `s ∈ starCarrier K (smallRange t)`, and `cmp (single s)` is a generator with
range the hull of `s` (`IsAffineComparison`), inside `starHull`. Close up with
`subsetCarriedChain_sub` and the analogous sum/scalar closure. -/
theorem smallHomotopy_aux_diff_carried_aux_zero {X : Type} [TopologicalSpace X]
    (A : Set X) {k : ℕ} :
    AcyclicCarriers.SubsetCarriedChain X A
      (0 : (CoefficientH0.SingularChains ℚ (TopCat.of X)).X k) := by
  refine ⟨0, Fin.elim0, Fin.elim0, ?_, fun i ↦ i.elim0⟩
  simp

theorem smallHomotopy_aux_diff_carried_aux_smul {X : Type} [TopologicalSpace X]
    (A : Set X) {k : ℕ} (z : (CoefficientH0.SingularChains ℚ (TopCat.of X)).X k)
    (hz : AcyclicCarriers.SubsetCarriedChain X A z) (r : ℚ) :
    AcyclicCarriers.SubsetCarriedChain X A (r • z) := by
  rcases hz with ⟨m, a, σ, rfl, hσ⟩
  refine ⟨m, fun i ↦ r * a i, σ, ?_, hσ⟩
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← map_smul]
  rfl

theorem smallHomotopy_aux_diff_carried_aux_add {X : Type} [TopologicalSpace X]
    (A : Set X) {k : ℕ} (x y : (CoefficientH0.SingularChains ℚ (TopCat.of X)).X k)
    (hx : AcyclicCarriers.SubsetCarriedChain X A x)
    (hy : AcyclicCarriers.SubsetCarriedChain X A y) :
    AcyclicCarriers.SubsetCarriedChain X A (x + y) := by
  classical
  rcases hx with ⟨m, a, σ, rfl, hσ⟩
  rcases hy with ⟨m', a', σ', rfl, hσ'⟩
  let e : Fin m ⊕ Fin m' ≃ Fin (m + m') := finSumFinEquiv
  let b : Fin (m + m') → ℚ := Sum.elim a a' ∘ e.symm
  let τ : Fin (m + m') → SingularSubdivision.SingularSimplex (TopCat.of X) k :=
    Sum.elim σ σ' ∘ e.symm
  refine ⟨m + m', b, τ, ?_, ?_⟩
  · rw [← e.sum_comp]
    simp [b, τ, Fintype.sum_sum_type]
  · intro i
    obtain ⟨i, rfl⟩ := e.surjective i
    cases i with
    | inl i => simpa [τ, e] using hσ i
    | inr i => simpa [τ, e] using hσ' i

theorem smallHomotopy_aux_diff_carried_aux_cmp {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (cmp : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (hcmp : IsAffineComparison K cmp) {k : ℕ} (A : Set K.space)
    (z : FaceModule K k) (hz : ∀ u, z u ≠ 0 → u.1 ∈ starCarrier K A) :
    AcyclicCarriers.SubsetCarriedChain K.space (starHull K A) (cmp k z) := by
  classical
  induction z using Finsupp.induction with
  | zero => simpa using smallHomotopy_aux_diff_carried_aux_zero (starHull K A)
  | @single_add u r z huz hr ih =>
      rw [map_add]
      apply smallHomotopy_aux_diff_carried_aux_add
      · rw [show Finsupp.single u r = r • Finsupp.single u 1 by simp, map_smul]
        apply smallHomotopy_aux_diff_carried_aux_smul
        obtain ⟨σ, hσ, hrange⟩ := hcmp k u
        refine ⟨1, fun _ ↦ 1, fun _ ↦ σ, ?_, ?_⟩
        · simpa [hσ]
        · intro i x hx
          refine Set.mem_iUnion₂.mpr ⟨u.1, ?_, ?_⟩
          · apply hz u
            have hzu : z u = 0 := by
              simpa [Finsupp.mem_support_iff] using huz
            simpa [hzu] using hr
          · change (x : Euc n) ∈ convexHull ℝ (u.1 : Set (Euc n))
            rw [← Set.mem_preimage, ← hrange]
            exact hx
      · apply ih
        intro v hv
        apply hz v
        simp only [Finsupp.add_apply]
        by_cases h : v = u
        · subst v
          exact False.elim (huz (Finsupp.mem_support_iff.mpr hv))
        · simpa [Finsupp.single_apply, h] using hv

theorem smallHomotopy_aux_diff_carried {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (cmp : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (hcmp : IsAffineComparison K cmp)
    (cmpH : ChainComplex.of _ d hdd ⟶ CoefficientH0.SingularChains ℚ (TopCat.of K.space))
    (cmpH_f : ∀ k, cmpH.f k = cmp k)
    (ψ : CoefficientSmallPath.coverSmallChains ℚ (starCover K) ⟶ ChainComplex.of _ d hdd)
    (hψ : StarCarriedMap K d hdd ψ) (k : ℕ) :
    SmallCarried K ((ψ ≫ cmpH).f k -
      (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)).f k) := by
  classical
  intro t
  apply subsetCarriedChain_sub
  · rw [HomologicalComplex.comp_f, cmpH_f]
    apply smallHomotopy_aux_diff_carried_aux_cmp K cmp hcmp
    exact hψ.1 k t
  · obtain ⟨σ, a, hσ, ht, hrange⟩ :=
      smallGen_eq_coverSmallGenerator (starCover K) t
    rw [ht, ← CategoryTheory.comp_apply,
      CoefficientSmallPath.coverSmallGenerator_comp_ι]
    refine ⟨1, fun _ ↦ 1,
      fun _ ↦ SingularSubdivision.singularSimplexOfContinuousMap
        (TopCat.of K.space) k σ, ?_, ?_⟩
    · simp
    · intro i x hx
      apply subset_starCarrier_hull K (smallRange _ t)
      rw [← hrange]
      simpa only [SingularSubdivision.continuousMapOfSingularSimplex_ofContinuousMap]

/-- Precomposing a small-carried map with the small boundary keeps it carried:
`smallChains_d_span` writes `d (smallGen t)` as a combination of generators at
faces with smaller image, `starCarrier_mono` makes their `starHull` smaller, and
carried chains are closed under linear combinations (span induction). -/
theorem smallHomotopy_aux_comp_d_carried_aux_starHull_mono {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) {A B : Set K.space} (hAB : A ⊆ B) :
    starHull K A ⊆ starHull K B := by
  intro x hx
  rcases Set.mem_iUnion₂.mp hx with ⟨s, hs, hxs⟩
  exact Set.mem_iUnion₂.mpr ⟨s, starCarrier_mono K hAB hs, hxs⟩

theorem smallHomotopy_aux_comp_d_carried_aux_mono {X : Type} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) {j : ℕ}
    {z : (CoefficientH0.SingularChains ℚ (TopCat.of X)).X j}
    (hz : AcyclicCarriers.SubsetCarriedChain X A z) :
    AcyclicCarriers.SubsetCarriedChain X B z := by
  rcases hz with ⟨m, a, σ, heq, hσ⟩
  exact ⟨m, a, σ, heq, fun i ↦ (hσ i).trans hAB⟩

theorem smallHomotopy_aux_comp_d_carried {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    {k j : ℕ}
    (g : (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).X k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X j)
    (hg : SmallCarried K g) :
    SmallCarried K ((CoefficientSmallPath.coverSmallChains ℚ (starCover K)).d (k + 1) k ≫ g) := by
  intro t
  rw [CategoryTheory.comp_apply]
  have hd := smallChains_d_span (starCover K) t
  generalize
    (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).d (k + 1) k
      (smallGen (starCover K) t 1) = z at hd ⊢
  induction hd using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t', ht', rfl⟩ := hx
    exact smallHomotopy_aux_comp_d_carried_aux_mono
      (smallHomotopy_aux_comp_d_carried_aux_starHull_mono K ht') (hg t')
  | zero =>
    rw [map_zero]
    exact
      SimplicialChainMaps.vertexChainMap_affineComparison_square_aux_carrier_homotopy_aux_zero
        K.space (starHull K (smallRange (starCover K) t))
  | add x y _ _ hx hy =>
    rw [map_add]
    exact
      SimplicialChainMaps.vertexChainMap_affineComparison_square_aux_carrier_homotopy_aux_add
        K.space (starHull K (smallRange (starCover K) t)) (g x) (g y) hx hy
  | smul r x _ hx =>
    rw [map_smul]
    exact
      SimplicialChainMaps.vertexChainMap_affineComparison_square_aux_carrier_homotopy_aux_smul
        K.space (starHull K (smallRange (starCover K) t)) (g x) hx r

/-- Small-carried maps are closed under subtraction (`subsetCarriedChain_sub`). -/
theorem smallCarried_sub {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n)) {k j : ℕ}
    (g g' : (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).X k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X j)
    (hg : SmallCarried K g) (hg' : SmallCarried K g') : SmallCarried K (g - g') := by
  intro t
  exact subsetCarriedChain_sub K.space _ _ _ (hg t) (hg' t)

/-- Positive-degree filling of a small-carried map of cycles. For each small
generator `t`, `g (smallGen t)` is a carried cycle; `starHull K (smallRange t)` is
rationally pointlike (`starCarrier_pointlike`, with `smallSimplex_range_subset` and
the range nonempty), so `AcyclicCarriers.subsetCarriedCycle_bounds` gives a carried
filling. Assemble the fillings with `Limits.Sigma.desc` and
`CoefficientSmallComparison.elementHom`; check `f ≫ d = g` on generators. -/
theorem smallHomotopy_aux_fill_succ {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    {k : ℕ}
    (g : (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).X (k + 1) ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X (k + 1))
    (hg : SmallCarried K g)
    (hcyc : g ≫ (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 1) k = 0) :
    ∃ f : (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).X (k + 1) ⟶
        (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X (k + 2),
      SmallCarried K f ∧
        f ≫ (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 2) (k + 1) = g := by
  classical
  let C := CoefficientH0.SingularChains ℚ (TopCat.of K.space)
  have hw : ∀ t : SmallSimplex (starCover K) (k + 1), ∃ w : C.X (k + 2),
      AcyclicCarriers.SubsetCarriedChain K.space (starHull K (smallRange _ t)) w ∧
        C.d (k + 2) (k + 1) w = g (smallGen _ t 1) := by
    intro t
    obtain ⟨a, ha⟩ := smallSimplex_range_subset (starCover K) t
    apply AcyclicCarriers.subsetCarriedCycle_bounds K.space
      (starHull K (smallRange _ t)) (starCarrier_pointlike K ha (Set.range_nonempty _))
      (Nat.succ_pos k) (g (smallGen _ t 1)) (hg t)
    have h := ConcreteCategory.congr_hom hcyc (smallGen _ t 1)
    simpa [CategoryTheory.comp_apply, C] using h
  choose w hwc hwd using hw
  let f : (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).X (k + 1) ⟶
      C.X (k + 2) :=
    Limits.Sigma.desc (fun t => CoefficientSmallComparison.elementHom ℚ (w t))
  have hf (t : SmallSimplex (starCover K) (k + 1)) :
      f (smallGen _ t 1) = w t := by
    change (smallGen _ t ≫ f) 1 = _
    rw [show smallGen (starCover K) t ≫ f =
        CoefficientSmallComparison.elementHom ℚ (w t) from Limits.Sigma.ι_desc _ t]
    exact CoefficientSmallComparison.elementHom_one ℚ (w t)
  refine ⟨f, fun t => by rw [hf]; exact hwc t, ?_⟩
  apply Limits.Sigma.hom_ext
  intro t
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change C.d (k + 2) (k + 1) (f (smallGen _ t 1)) = g (smallGen _ t 1)
  rw [hf, hwd]

/-- Degree-zero filling: a small-carried map to 0-chains with augmentation zero is
a carried boundary. In a rationally pointlike carrier, a carried 0-chain of
augmentation zero bounds there (lift to the subspace with
`AcyclicCarriers.subsetPush_lift`, use `H₀ ≅ ℚ` through the augmentation, and push
the filling forward). Assemble generatorwise as in `smallHomotopy_aux_fill_succ`. -/
theorem smallHomotopy_aux_fill_zero_aux_bounds
    (X : Type) [TopologicalSpace X] (A : Set X)
    (hA : ProjectivePlaneWedgeRationalHomology.RationallyPointlike A)
    (hAn : A.Nonempty)
    (z : (CoefficientH0.SingularChains ℚ (TopCat.of X)).X 0)
    (hz : AcyclicCarriers.SubsetCarriedChain X A z)
    (haug : CoefficientH0.zeroChainAugmentation ℚ z = 0) :
    ∃ w : (CoefficientH0.SingularChains ℚ (TopCat.of X)).X 1,
      AcyclicCarriers.SubsetCarriedChain X A w ∧
        (CoefficientH0.SingularChains ℚ (TopCat.of X)).d 1 0 w = z := by
  letI : Nonempty A := hAn.to_subtype
  let C := CoefficientH0.SingularChains ℚ (TopCat.of A)
  obtain ⟨z', hz'⟩ := AcyclicCarriers.subsetPush_lift X A z hz
  have haug' : CoefficientH0.zeroChainAugmentation ℚ z' = 0 := by
    have hn := CoefficientH0.chainMap_comp_zeroChainAugmentation ℚ
      (X := A) (Y := X) ⟨Subtype.val, continuous_subtype_val⟩
    have he := ConcreteCategory.congr_hom hn z'
    simp only [CategoryTheory.comp_apply] at he
    exact he.symm.trans (hz' ▸ haug)
  obtain ⟨e⟩ := hA.1
  letI : FiniteDimensional ℚ (C.homology 0) :=
    Module.Finite.equiv e.toLinearEquiv.symm
  let ε : C.homology 0 ⟶ ModuleCat.of ℚ ℚ := CoefficientH0.h0Augmentation ℚ
  have hεs : Function.Surjective ε.hom := by
    intro a
    let p : A := Classical.choice (inferInstance : Nonempty A)
    refine ⟨(CoefficientH0.singularVertexH0Class ℚ p).hom a, ?_⟩
    exact congrArg (fun q => q.hom a)
      (CoefficientH0.singularVertexH0Class_comp_h0Augmentation ℚ p)
  have hdim : Module.finrank ℚ (C.homology 0) =
      Module.finrank ℚ (ModuleCat.of ℚ ℚ) := by
    simpa using e.toLinearEquiv.finrank_eq
  have hεi : Function.Injective ε.hom :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hεs
  have hclass : CoefficientH0.zeroChainH0Class ℚ z' = 0 := by
    apply hεi
    have heq := ConcreteCategory.congr_hom
      (CoefficientH0.zeroChainH0Class_comp_h0Augmentation ℚ (X := A)) z'
    calc
      ε.hom (CoefficientH0.zeroChainH0Class ℚ z') = 0 := by
        simpa [ε, CategoryTheory.comp_apply, haug'] using heq
      _ = ε.hom 0 := (ε.hom.map_zero).symm
  let x : C.cycles 0 := CoefficientH0.zeroChainsToCycles ℚ z'
  have hx : C.iCycles 0 x = z' := by
    exact ConcreteCategory.congr_hom (CoefficientH0.zeroChainsToCycles_i ℚ (X := A)) z'
  have hπ : C.homologyπ 0 x = 0 := by
    exact hclass
  obtain ⟨b, hb⟩ := AcyclicCarriers.faceCarriedCycle_bounds_aux_exists_boundary C 0 x hπ
  refine ⟨(AcyclicCarriers.subsetPush X A).f 1 b,
    AcyclicCarriers.subsetPush_carried X A b, ?_⟩
  have hc := congrArg (fun q => q b) ((AcyclicCarriers.subsetPush X A).comm 1 0)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
  erw [hc, hb, hx, hz']

theorem smallHomotopy_aux_fill_zero {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (g : (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).X 0 ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X 0)
    (hg : SmallCarried K g)
    (haug : g ≫ CoefficientH0.zeroChainAugmentation ℚ = 0) :
    ∃ f : (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).X 0 ⟶
        (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X 1,
      SmallCarried K f ∧
        f ≫ (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d 1 0 = g := by
  classical
  let C := CoefficientH0.SingularChains ℚ (TopCat.of K.space)
  have hw : ∀ t : SmallSimplex (starCover K) 0, ∃ w : C.X 1,
      AcyclicCarriers.SubsetCarriedChain K.space (starHull K (smallRange _ t)) w ∧
        C.d 1 0 w = g (smallGen _ t 1) := by
    intro t
    obtain ⟨a, ha⟩ := smallSimplex_range_subset (starCover K) t
    apply smallHomotopy_aux_fill_zero_aux_bounds K.space
      (starHull K (smallRange _ t))
      (starCarrier_pointlike K ha (Set.range_nonempty _))
      (Set.range_nonempty _ |>.mono (subset_starCarrier_hull K (smallRange _ t)))
      (g (smallGen _ t 1)) (hg t)
    have h := ConcreteCategory.congr_hom haug (smallGen _ t 1)
    simpa [CategoryTheory.comp_apply] using h
  choose w hwc hwd using hw
  let f : (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).X 0 ⟶ C.X 1 :=
    Limits.Sigma.desc (fun t => CoefficientSmallComparison.elementHom ℚ (w t))
  have hf (t : SmallSimplex (starCover K) 0) : f (smallGen _ t 1) = w t := by
    change (smallGen _ t ≫ f) 1 = _
    rw [show smallGen (starCover K) t ≫ f =
        CoefficientSmallComparison.elementHom ℚ (w t) from Limits.Sigma.ι_desc _ t]
    exact CoefficientSmallComparison.elementHom_one ℚ (w t)
  refine ⟨f, fun t => by rw [hf]; exact hwc t, ?_⟩
  apply Limits.Sigma.hom_ext
  intro t
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change C.d 1 0 (f (smallGen _ t 1)) = g (smallGen _ t 1)
  rw [hf, hwd]

/-- The two maps have the same augmentation in degree zero: on a small point `t`,
`inc (smallGen t)` has augmentation `1`, and `cmp (ψ (smallGen t))` has augmentation
the coefficient sum of `ψ (smallGen t)`, which is `1` (`hψ.2`), since `cmp` sends each
vertex to a single generator (`IsAffineComparison`). Check on generators
(`Limits.Sigma.hom_ext`). -/
theorem smallHomotopy_aux_aug_zero {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (cmp : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (hcmp : IsAffineComparison K cmp)
    (cmpH : ChainComplex.of _ d hdd ⟶ CoefficientH0.SingularChains ℚ (TopCat.of K.space))
    (cmpH_f : ∀ k, cmpH.f k = cmp k)
    (ψ : CoefficientSmallPath.coverSmallChains ℚ (starCover K) ⟶ ChainComplex.of _ d hdd)
    (hψ : StarCarriedMap K d hdd ψ) :
    ((ψ ≫ cmpH).f 0 - (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)).f 0) ≫
      CoefficientH0.zeroChainAugmentation ℚ = 0 := by
  classical
  have hcmp_aug (z : FaceModule K 0) :
      CoefficientH0.zeroChainAugmentation ℚ (cmp 0 z) =
        z.sum (fun _ c ↦ c) := by
    induction z using Finsupp.induction with
    | zero => simp
    | @single_add s c z hsz hc ih =>
        obtain ⟨σ, hσ, -⟩ := hcmp 0 s
        rw [map_add, map_add, ih]
        rw [show Finsupp.single s c = c • Finsupp.single s 1 by simp,
          map_smul, hσ, map_smul]
        have hgen : CoefficientH0.zeroChainAugmentation ℚ
            ((CoefficientH0.singularGenerator ℚ _ 0 σ) 1) = 1 := by
          change ((Limits.Sigma.ι (fun _ : SingularSubdivision.SingularSimplex
              (TopCat.of K.space) 0 ↦
            ModuleCat.of ℚ ℚ) σ ≫ Limits.Sigma.desc (fun _ ↦ 𝟙 _)) 1) = 1
          rw [Limits.Sigma.ι_desc]
          rfl
        rw [hgen]
        simp [Finsupp.sum_add_index, hc]
  apply Limits.Sigma.hom_ext
  intro t
  rw [Preadditive.sub_comp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [CategoryTheory.comp_apply, map_sub, map_zero]
  change CoefficientH0.zeroChainAugmentation ℚ
      (cmpH.f 0 (ψ.f 0 (smallGen _ t 1))) -
      CoefficientH0.zeroChainAugmentation ℚ
        ((CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)).f 0
          (smallGen _ t 1)) = 0
  rw [cmpH_f]
  have ha := hcmp_aug (ψ.f 0 (smallGen _ t 1))
  have hs := hψ.2 t
  have hinc := ConcreteCategory.congr_hom (smallGen_aug (starCover K) t) (1 : ℚ)
  have hi : CoefficientH0.zeroChainAugmentation ℚ
      ((CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)).f 0
        (smallGen _ t 1)) = 1 := by
    simpa [CategoryTheory.comp_apply] using hinc
  exact sub_eq_zero.mpr (ha.trans (hs.trans hi.symm))

/-- One stage of the homotopy between `ψ ≫ cmpH` and the inclusion. -/
structure SmallHomotopyStage {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (cmpH : ChainComplex.of _ d hdd ⟶ CoefficientH0.SingularChains ℚ (TopCat.of K.space))
    (ψ : CoefficientSmallPath.coverSmallChains ℚ (starCover K) ⟶ ChainComplex.of _ d hdd)
    (k : ℕ) where
  f : (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).X k ⟶
    (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X (k + 1)
  f' : (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).X (k + 1) ⟶
    (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X (k + 2)
  cf : SmallCarried K f
  cf' : SmallCarried K f'
  eq : (ψ ≫ cmpH).f (k + 1) - (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)).f (k + 1) =
    (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).d (k + 1) k ≫ f +
      f' ≫ (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 2) (k + 1)

/-- The first stage. `f` is `smallHomotopy_aux_fill_zero` applied to
`φ₀ = (ψ ≫ cmpH).f 0 - inc.f 0` (`smallHomotopy_aux_diff_carried`,
`smallHomotopy_aux_aug_zero`). `f'` is `smallHomotopy_aux_fill_succ` (with `k = 0`)
applied to `φ₁ - d ≫ f`, carried by `smallCarried_sub` and
`smallHomotopy_aux_comp_d_carried`; it is a cycle because `φ` is a chain map
difference (`Hom.comm` of `ψ ≫ cmpH` and of `inc`) and `f ≫ d = φ₀`. -/
theorem smallHomotopy_aux_base {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (cmp : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (hcmp : IsAffineComparison K cmp)
    (cmpH : ChainComplex.of _ d hdd ⟶ CoefficientH0.SingularChains ℚ (TopCat.of K.space))
    (cmpH_f : ∀ k, cmpH.f k = cmp k)
    (ψ : CoefficientSmallPath.coverSmallChains ℚ (starCover K) ⟶ ChainComplex.of _ d hdd)
    (hψ : StarCarriedMap K d hdd ψ) :
    ∃ S : SmallHomotopyStage K d hdd cmpH ψ 0,
      (ψ ≫ cmpH).f 0 - (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)).f 0 =
        S.f ≫ (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d 1 0 := by
  let A := CoefficientSmallPath.coverSmallChains ℚ (starCover K)
  let C := CoefficientH0.SingularChains ℚ (TopCat.of K.space)
  let inc := CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)
  let φ : ∀ k, A.X k ⟶ C.X k := fun k => (ψ ≫ cmpH).f k - inc.f k
  obtain ⟨f, hfcar, hf⟩ := smallHomotopy_aux_fill_zero K (φ 0)
    (smallHomotopy_aux_diff_carried K d hdd cmp hcmp cmpH cmpH_f ψ hψ 0)
    (smallHomotopy_aux_aug_zero K d hdd cmp hcmp cmpH cmpH_f ψ hψ)
  let g : A.X 1 ⟶ C.X 1 := φ 1 - A.d 1 0 ≫ f
  have hgcar : SmallCarried K g := smallCarried_sub K _ _
    (smallHomotopy_aux_diff_carried K d hdd cmp hcmp cmpH cmpH_f ψ hψ 1)
    (smallHomotopy_aux_comp_d_carried K f hfcar)
  have hφ : φ 1 ≫ C.d 1 0 = A.d 1 0 ≫ φ 0 := by
    dsimp [φ, A, C, inc]
    rw [Preadditive.sub_comp, Preadditive.comp_sub]
    congr 1
    · simpa only [HomologicalComplex.comp_f, Category.assoc] using (ψ ≫ cmpH).comm 1 0
    · exact (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)).comm 1 0
  have hgcyc : g ≫ C.d 1 0 = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, hf, hφ]
    exact sub_self _
  obtain ⟨f', hf'car, hf'⟩ := smallHomotopy_aux_fill_succ K g hgcar hgcyc
  let S : SmallHomotopyStage K d hdd cmpH ψ 0 :=
    { f := f
      f' := f'
      cf := hfcar
      cf' := hf'car
      eq := by
        change φ 1 = A.d 1 0 ≫ f + f' ≫ C.d 2 1
        rw [hf']
        dsimp [g]
        abel }
  exact ⟨S, hf.symm⟩

/-- Extend a stage, keeping its top component: apply `smallHomotopy_aux_fill_succ`
to `φ (k+2) - d ≫ S.f'`, carried by `smallCarried_sub` and
`smallHomotopy_aux_comp_d_carried`, a cycle by `S.eq`, `d ≫ d = 0` and the chain-map
property of `φ`; compare the `hstep` block of
`AcyclicCarriers.carried_chainHomotopy_exists`. -/
theorem smallHomotopy_aux_step {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (cmp : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (hcmp : IsAffineComparison K cmp)
    (cmpH : ChainComplex.of _ d hdd ⟶ CoefficientH0.SingularChains ℚ (TopCat.of K.space))
    (cmpH_f : ∀ k, cmpH.f k = cmp k)
    (ψ : CoefficientSmallPath.coverSmallChains ℚ (starCover K) ⟶ ChainComplex.of _ d hdd)
    (hψ : StarCarriedMap K d hdd ψ) {k : ℕ} (S : SmallHomotopyStage K d hdd cmpH ψ k) :
    ∃ S' : SmallHomotopyStage K d hdd cmpH ψ (k + 1), S'.f = S.f' := by
  let C := CoefficientH0.SingularChains ℚ (TopCat.of K.space)
  let D := CoefficientSmallPath.coverSmallChains ℚ (starCover K)
  let inc := CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)
  let g : D.X (k + 2) ⟶ C.X (k + 2) :=
    (ψ ≫ cmpH).f (k + 2) - inc.f (k + 2) -
      D.d (k + 2) (k + 1) ≫ S.f'
  have hg : SmallCarried K g := by
    apply smallCarried_sub K
    · exact smallHomotopy_aux_diff_carried K d hdd cmp hcmp cmpH cmpH_f ψ hψ (k + 2)
    · exact smallHomotopy_aux_comp_d_carried K S.f' S.cf'
  have hcyc : g ≫ C.d (k + 2) (k + 1) = 0 := by
    have hdiffcomm :
        ((ψ ≫ cmpH).f (k + 2) - inc.f (k + 2)) ≫ C.d (k + 2) (k + 1) =
          D.d (k + 2) (k + 1) ≫
            ((ψ ≫ cmpH).f (k + 1) - inc.f (k + 1)) := by
      rw [Preadditive.sub_comp, (ψ ≫ cmpH).comm (k + 2) (k + 1),
        inc.comm (k + 2) (k + 1), Preadditive.comp_sub]
    dsimp only [g]
    rw [Preadditive.sub_comp, hdiffcomm, Category.assoc,
      ← Preadditive.comp_sub, S.eq,
      show (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 2) (k + 1) =
        C.d (k + 2) (k + 1) from rfl,
      add_sub_cancel_right,
      ← Category.assoc, (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).d_comp_d,
      Limits.zero_comp]
  obtain ⟨f'', hf'', hfd⟩ := smallHomotopy_aux_fill_succ K g hg hcyc
  refine ⟨⟨S.f', f'', S.cf', hf'', ?_⟩, rfl⟩
  dsimp [g, C, D, inc] at hfd ⊢
  rw [hfd]
  abel

/-- `ψ ≫ cmpH` and the small-chain inclusion agree on homology, by a chain homotopy
built from `SmallHomotopyStage`s (`smallHomotopy_aux_base`, `smallHomotopy_aux_step`)
and assembled as at the end of `AcyclicCarriers.carried_chainHomotopy_exists`,
except that the degree-zero equation is the base stage's equation instead of
`hzero`. The hypotheses become `StarCarriedMap` by
`starCarriedMap_of_coverSmallGenerator`. -/
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
  classical
  have hψ' := starCarriedMap_of_coverSmallGenerator K d hdd ψ hψ hψ0
  obtain ⟨S0, hS0⟩ := smallHomotopy_aux_base K d hdd cmp hcmp cmpH cmpH_f ψ hψ'
  have hstep : ∀ k (S : SmallHomotopyStage K d hdd cmpH ψ k),
      ∃ S' : SmallHomotopyStage K d hdd cmpH ψ (k + 1), S'.f = S.f' :=
    fun k S => smallHomotopy_aux_step K d hdd cmp hcmp cmpH cmpH_f ψ hψ' S
  choose g hg using hstep
  let F : ∀ k, SmallHomotopyStage K d hdd cmpH ψ k := fun k =>
    Nat.rec (motive := fun k => SmallHomotopyStage K d hdd cmpH ψ k) S0 (fun k S => g k S) k
  have hF0 : F 0 = S0 := rfl
  have hF : ∀ k, (F (k + 1)).f = (F k).f' := fun k => hg k (F k)
  let hom : ∀ i j, (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).X i ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X j := fun i j =>
    if h : i + 1 = j then (F i).f ≫ eqToHom
      (congrArg (fun m => (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X m) h)
    else 0
  let H : Homotopy (ψ ≫ cmpH) (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)) :=
    { hom := hom
      zero := by
        intro i j hij
        simp only [hom]
        split_ifs with h
        · exact absurd (by simp [ComplexShape.down_Rel]; omega) hij
        · rfl
      comm := by
        intro i
        cases i with
        | zero =>
          rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
          simp only [hom, dif_pos, eqToHom_refl, Category.comp_id, zero_add]
          rw [hF0, ← hS0]
          abel
        | succ i =>
          rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
          simp only [hom, dif_pos, eqToHom_refl, Category.comp_id, hF]
          rw [← sub_eq_iff_eq_add, (F i).eq] }
  intro k
  exact H.homologyMap_eq k

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
  classical
  let faceEquiv : Sigma (FaceIndex K) ≃ K.faces := {
    toFun := fun (p : Sigma (FaceIndex K)) => ⟨p.2.1, p.2.2.1⟩
    invFun := fun (s : K.faces) => ⟨s.1.card - 1, ⟨s.1, s.2, by
      rw [Nat.sub_add_cancel (Finset.one_le_card.mpr (K.nonempty_of_mem_faces s.2))]⟩⟩
    left_inv := fun p => by
      rcases p with ⟨k, s⟩
      rcases s with ⟨val, hface, hcard⟩
      simp_all [Sigma.ext_iff]
      have hk : val.card - 1 = k := by omega
      subst k
      exact heq_of_eq (Subtype.ext rfl)
    right_inv := fun s => by
      apply Subtype.ext
      rfl }
  letI : Fintype K.faces := hK.fintype
  letI : Fintype (Sigma (FaceIndex K)) :=
    Fintype.ofEquiv K.faces faceEquiv.symm
  have hev (s : Sigma (FaceIndex K)) :
      ∃ N, ∀ r, N ≤ r → ∃ q :
          (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).X s.1,
        (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)).f s.1 q =
          (CoefficientEventualSmallness.subdivisionIterate ℚ r).f s.1
            (cmpH.f s.1 (Finsupp.single s.2 1)) :=
    CoefficientEventualSmallness.actual_chain_eventual ℚ (starCover K) s.1
      (cmpH.f s.1 (Finsupp.single s.2 1))
      (starCover_isOpen K hK) (starCover_covers K)
  choose N hN using hev
  let r := Finset.univ.sup N
  have hNr (s : Sigma (FaceIndex K)) : N s ≤ r :=
    Finset.le_sup (f := N) (Finset.mem_univ s)
  choose q hq using fun s : Sigma (FaceIndex K) => hN s r (hNr s)
  let liftComponent (k : ℕ) : FaceModuleCat K k ⟶
      (CoefficientSmallPath.coverSmallChains ℚ (starCover K)).X k :=
    ModuleCat.ofHom (Finsupp.lsum ℚ (fun s : FaceIndex K k =>
      LinearMap.toSpanSingleton ℚ _ (q ⟨k, s⟩)))
  have hcomponent (k : ℕ) :
      liftComponent k ≫ (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)).f k =
        cmpH.f k ≫ (CoefficientEventualSmallness.subdivisionIterate ℚ r).f k := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
      ModuleCat.hom_comp]
    change (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)).f k
        ((Finsupp.lsum ℚ (fun t : FaceIndex K k =>
          LinearMap.toSpanSingleton ℚ _ (q ⟨k, t⟩))) (Finsupp.single s 1)) = _
    rw [Finsupp.lsum_single]
    simp only [LinearMap.toSpanSingleton_apply, one_smul]
    exact hq ⟨k, s⟩
  let Φ : ChainComplex.of _ d hdd ⟶
      CoefficientSmallPath.coverSmallChains ℚ (starCover K) := {
    f := liftComponent
    comm' := fun i j _ => by
      apply (cancel_mono
        ((CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)).f j)).1
      rw [Category.assoc, ←
        (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)).comm]
      change (liftComponent i ≫
        (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)).f i) ≫ _ = _
      rw [hcomponent]
      rw [Category.assoc]
      change _ = _ ≫ (liftComponent j ≫
        (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)).f j)
      rw [hcomponent]
      exact
        (Category.assoc _ _ _).trans <|
          (congrArg (fun z => cmpH.f i ≫ z)
            ((CoefficientEventualSmallness.subdivisionIterate ℚ r).comm i j)).trans <|
          (Category.assoc _ _ _).symm.trans <|
          (congrArg (fun z => z ≫
              (CoefficientEventualSmallness.subdivisionIterate ℚ r).f j)
            (cmpH.comm i j)).trans <|
          Category.assoc _ _ _ }
  refine ⟨r, Φ, ?_⟩
  apply HomologicalComplex.Hom.ext
  exact funext hcomponent

/-- Iterated singular subdivision keeps a chain inside a subset: subdivision is
natural (`CoefficientSingularSubdivision`, or `subsetPush` naturality), and a chain
is carried by `A` exactly when it is in the range of `AcyclicCarriers.subsetPush`
(`subsetPush_lift`, `subsetPush_carried`). -/
theorem subdivisionIterate_subsetCarried {X : Type} [TopologicalSpace X] (A : Set X)
    (r : ℕ) {k : ℕ} (c : (CoefficientH0.SingularChains ℚ (TopCat.of X)).X k)
    (hc : AcyclicCarriers.SubsetCarriedChain X A c) :
    AcyclicCarriers.SubsetCarriedChain X A
      ((CoefficientEventualSmallness.subdivisionIterate ℚ r).f k c) := by
  induction r with
  | zero =>
      simpa [CoefficientEventualSmallness.subdivisionIterate] using hc
  | succ r ih =>
      obtain ⟨c', hc'⟩ := AcyclicCarriers.subsetPush_lift X A _ ih
      rw [show (CoefficientEventualSmallness.subdivisionIterate ℚ (r + 1)).f k c =
          (CoefficientSingularSubdivision.singularSubdivision ℚ).f k
            ((CoefficientEventualSmallness.subdivisionIterate ℚ r).f k c) by rfl,
        ← hc']
      have hnat := congrArg (fun f => f.f k)
        (CoefficientSingularSubdivision.naturality ℚ
          (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))
      have happ := congrArg (fun f => f c') hnat
      rw [show (AcyclicCarriers.subsetPush X A).f k =
          (CoefficientH0.singularPostcomposition ℚ
            (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))).f k by rfl]
      rw [show (CoefficientSingularSubdivision.singularSubdivision ℚ).f k
            ((CoefficientH0.singularPostcomposition ℚ
              (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))).f k c') =
          (CoefficientH0.singularPostcomposition ℚ
            (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))).f k
              ((CoefficientSingularSubdivision.singularSubdivision ℚ).f k c') by
            simpa only [CategoryTheory.comp_apply] using happ]
      exact AcyclicCarriers.subsetPush_carried X A
        ((CoefficientSingularSubdivision.singularSubdivision ℚ).f k c')

/-- A coproduct of copies of `ℚ` (the shape of the singular and small chain modules). -/
abbrev SigmaQ (I : Type) : ModuleCat.{0} ℚ := ∐ fun _ : I => ModuleCat.of ℚ ℚ

/-- The coefficient at `t` of an element of a coproduct of copies of `ℚ`. -/
noncomputable def sigmaCoeff {I : Type} (t : I) :
    SigmaQ I ⟶ ModuleCat.of ℚ ℚ := by
  classical
  exact Limits.Sigma.desc fun i => if i = t then 𝟙 _ else 0

/-- An element of a coproduct of copies of `ℚ` is the finite sum of its
coefficients times the generators. In `ModuleCat` the coproduct is a direct sum
(`ModuleCat.coprodIsoDirectSum`-style isomorphisms, or the cofan
`ModuleCat.coproductCocone`); both sides are linear in `q`, so it suffices to
check on generators, where `Limits.Sigma.ι_desc` evaluates `sigmaCoeff`. -/
theorem sigma_eq_sum {I : Type} (q : SigmaQ I) :
    ∃ F : Finset I, q = ∑ t ∈ F, (sigmaCoeff t q) •
      (Limits.Sigma.ι (fun _ : I => ModuleCat.of ℚ ℚ) t) (1 : ℚ) := by
  classical
  let e := ModuleCat.coprodIsoDirectSum (fun _ : I => ModuleCat.of ℚ ℚ)
  let x := e.hom q
  have hcoeff (t : I) : sigmaCoeff t q = x t := by
    have hm : sigmaCoeff t =
        e.hom ≫ ModuleCat.ofHom
          (DirectSum.component ℚ I (fun _ : I => ℚ) t) := by
      apply Limits.Sigma.hom_ext
      intro i
      dsimp [e]
      rw [← Category.assoc]
      change Limits.Sigma.ι (fun _ : I => ModuleCat.of ℚ ℚ) i ≫
          Limits.Sigma.desc (fun j => if j = t then 𝟙 _ else 0) = _
      rw [Limits.Sigma.ι_desc]
      rw [ModuleCat.ι_coprodIsoDirectSum_hom]
      by_cases h : i = t
      · subst i
        ext a
        simp [ModuleCat.hom_comp, DirectSum.component.lof_self]
      · ext a
        simp [ModuleCat.hom_comp, DirectSum.component.of, h]
    exact congrArg (fun f => f q) hm
  have hgen (t : I) (a : ℚ) :
      e.hom (a • (Limits.Sigma.ι (fun _ : I => ModuleCat.of ℚ ℚ) t) (1 : ℚ)) =
        DirectSum.of (fun _ : I => ℚ) t a := by
    rw [map_smul]
    dsimp [e]
    change a • ((Limits.Sigma.ι (fun _ : I => ModuleCat.of ℚ ℚ) t ≫
      (ModuleCat.coprodIsoDirectSum (fun _ : I => ModuleCat.of ℚ ℚ)).hom) (1 : ℚ)) = _
    rw [ModuleCat.ι_coprodIsoDirectSum_hom]
    change a • (DirectSum.lof ℚ I (fun _ : I => ℚ) t) 1 =
      (DirectSum.lof ℚ I (fun _ : I => ℚ) t) a
    rw [← map_smul]
    simp
  refine ⟨x.support, ?_⟩
  have heinj : Function.Injective (fun z => e.hom z) := by
    intro a b hab
    have h := congrArg (fun z => e.inv z) hab
    simpa using h
  apply_fun e.hom using heinj
  simp_rw [hcoeff]
  simp only [map_sum]
  change x = ∑ t ∈ x.support,
    e.hom ((x t) • (Limits.Sigma.ι (fun _ : I => ModuleCat.of ℚ ℚ) t) (1 : ℚ))
  calc
    x = ∑ t ∈ x.support, DirectSum.of (fun _ : I => ℚ) t (x t) :=
      (DirectSum.sum_support_of x).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      exact (hgen t (x t)).symm

/-- The coefficient of a small chain at a small simplex. -/
noncomputable def smallCoeff {X α : Type} [TopologicalSpace X] (U : α → Set X) {k : ℕ}
    (t : SmallSimplex U k) :
    (CoefficientSmallPath.coverSmallChains ℚ U).X k ⟶ ModuleCat.of ℚ ℚ := by
  change (∐ fun _ : SmallSimplex U k => ModuleCat.of ℚ ℚ) ⟶ _
  exact sigmaCoeff t

/-- The coefficient of a singular chain at a singular simplex. -/
noncomputable def singCoeff {X : Type} [TopologicalSpace X] {k : ℕ}
    (σ : SingularSubdivision.SingularSimplex (TopCat.of X) k) :
    (CoefficientH0.SingularChains ℚ (TopCat.of X)).X k ⟶ ModuleCat.of ℚ ℚ := by
  change (∐ fun _ : SingularSubdivision.SingularSimplex (TopCat.of X) k =>
    ModuleCat.of ℚ ℚ) ⟶ _
  exact sigmaCoeff σ

/-- A small chain and its image under the inclusion have the same coefficients.
Both sides are linear in `q`; on a generator `smallGen U t' 1` the inclusion gives
the singular generator of `t'.1` (the inclusion is `Sigma.map'` along `Subtype.val`,
as in the proof of `SingularSubdivision.coverSmallGeneratorOfMem_comp_ι`), and both
coefficients are `if t' = t then 1 else 0` (`Subtype.ext`). Reduce to generators
by proving the morphism equation `inc.f k ≫ singCoeff t.1 = smallCoeff U t` with
`Limits.Sigma.hom_ext` (no need for `sigma_eq_sum`). -/
theorem singCoeff_inclusion {X α : Type} [TopologicalSpace X] (U : α → Set X) {k : ℕ}
    (t : SmallSimplex U k) (q : (CoefficientSmallPath.coverSmallChains ℚ U).X k) :
    singCoeff t.1 ((CoefficientSmallPath.coverSmallInclusion ℚ U).f k q) =
      smallCoeff U t q := by
  classical
  have h : (CoefficientSmallPath.coverSmallInclusion ℚ U).f k ≫ singCoeff t.1 =
      smallCoeff U t := by
    apply Limits.Sigma.hom_ext
    intro t'
    dsimp [CoefficientSmallPath.coverSmallInclusion,
      CoefficientSmallPath.coverSmallChains, CoefficientH0.SingularChains,
      AlgebraicTopology.singularChainComplexFunctor,
      AlgebraicTopology.SSet.singularChainComplexFunctor, singCoeff, smallCoeff,
      sigmaCoeff]
    rw [← Category.assoc, Limits.Sigma.ι_comp_map', Category.id_comp,
      Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
    by_cases ht : t' = t
    · subst t'
      simp
    · have hv : (t' : SingularSubdivision.SingularSimplex (TopCat.of X) k) ≠ t.1 := by
        intro he
        apply ht
        exact Subtype.ext he
      have hv' : (SingularSubdivision.coverSmallSSet U).ι.app
          (Opposite.op (SimplexCategory.mk k)) t' ≠ t.1 := by
        exact hv
      rw [if_neg hv']
      split <;> simp_all
  exact ConcreteCategory.congr_hom h q

/-- A chain carried by `A` has nonzero coefficients only at simplices with range in
`A`: in the carried presentation `c = ∑ i, gen (σ i) (a i)`, the coefficient at `σ`
is the sum of the `a i` with `σ i = σ` (`Limits.Sigma.ι_desc` on each term), which
is zero if no `σ i` equals `σ`. -/
theorem singCoeff_ne_zero_of_subsetCarried {X : Type} [TopologicalSpace X] (A : Set X)
    {k : ℕ} (c : (CoefficientH0.SingularChains ℚ (TopCat.of X)).X k)
    (hc : AcyclicCarriers.SubsetCarriedChain X A c)
    (σ : SingularSubdivision.SingularSimplex (TopCat.of X) k) (hσ : singCoeff σ c ≠ 0) :
    Set.range (SingularSubdivision.continuousMapOfSingularSimplex k σ) ⊆ A := by
  classical
  obtain ⟨m, a, τ, rfl, hτ⟩ := hc
  by_contra hrange
  apply hσ
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : τ i ≠ σ := by
    intro h
    apply hrange
    simpa [h] using hτ i
  change ((Limits.Sigma.ι
      (fun _ : SingularSubdivision.SingularSimplex (TopCat.of X) k =>
        ModuleCat.of ℚ ℚ) (τ i) ≫ sigmaCoeff σ) (a i)) = 0
  calc
    _ = ((if τ i = σ then 𝟙 (ModuleCat.of ℚ ℚ) else 0) (a i)) := by
      apply ConcreteCategory.congr_hom
      dsimp [sigmaCoeff]
      exact Limits.Sigma.ι_desc _ _
    _ = 0 := by simp [hne]

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
  classical
  obtain ⟨F, hF⟩ := sigma_eq_sum (I := SmallSimplex U k) q
  change q ∈ _
  rw [hF]
  refine Submodule.sum_mem _ fun t _ => ?_
  by_cases h0 : sigmaCoeff t q = 0
  · rw [h0, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    obtain ⟨σ, a, hσ, ht, hr⟩ := smallGen_eq_coverSmallGenerator U t
    refine ⟨σ, a, hσ, ?_, ?_⟩
    · rw [hr]
      apply singCoeff_ne_zero_of_subsetCarried A _ hq t.1
      rw [singCoeff_inclusion U t q]
      exact h0
    · rw [← ht]
      rfl

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
  obtain ⟨ψ, hψ, hψ0⟩ := smallToFace_exists o K d hd hdd
  have hH := smallToFace_homology o K d hd hdd cmp hcmp cmpH cmpH_f ψ hψ hψ0 k
  letI := CoefficientSmallComparison.inclusion_isIso ℚ (starCover K)
    (starCover_isOpen K hK) (starCover_covers K) k
  have hcomp : HomologicalComplex.homologyMap ψ k ≫ HomologicalComplex.homologyMap cmpH k =
      HomologicalComplex.homologyMap
        (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)) k := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact hH
  intro x
  refine ⟨(HomologicalComplex.homologyMap ψ k).hom ((inv (HomologicalComplex.homologyMap
    (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)) k)).hom x), ?_⟩
  have h2 : inv (HomologicalComplex.homologyMap
      (CoefficientSmallPath.coverSmallInclusion ℚ (starCover K)) k) ≫
      HomologicalComplex.homologyMap ψ k ≫ HomologicalComplex.homologyMap cmpH k = 𝟙 _ := by
    rw [hcomp, IsIso.inv_hom_id]
  have := congrArg (fun g => g.hom x) h2
  simpa using this

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
