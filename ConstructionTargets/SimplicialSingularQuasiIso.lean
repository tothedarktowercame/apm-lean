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
  sorry

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
  sorry

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
  sorry

lemma coneSupported_cycle_bounds_aux_boundary {n k : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ j, FaceModuleCat K (j + 1) ⟶ FaceModuleCat K j)
    (hd : IsSignedDeletion o K d) (a : Euc n) (z : FaceModule K (k + 1))
    (hcyc : d k z = 0)
    (hadm : SimplicialChainMaps.ConeAdmissible K a
      (Finsupp.filter (fun u : FaceIndex K (k + 1) => a ∉ u.1) z)) :
    d (k + 1) (SimplicialChainMaps.subdivisionCone o K a (k + 1)
      (Finsupp.filter (fun u : FaceIndex K (k + 1) => a ∉ u.1) z)) = z := by
  sorry

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
  sorry

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
  sorry

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
