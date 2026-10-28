import Mathlib

/-! # Geometric barycentric subdivision and simplicial approximation interfaces -/

open Set

noncomputable section
namespace ConstructionTargets.GeometricSimplicialSubdivision

abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The barycenter of a nonempty finite set (the empty value is harmless). -/
def barycenter {n : ℕ} (s : Finset (Euc n)) : Euc n :=
  s.centerMass (fun _ => (1 : ℝ)) id

/-- A finite collection of old faces, linearly ordered by strict inclusion. -/
def IsStrictFaceChain {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (c : Finset (Finset (Euc n))) : Prop :=
  (∀ s ∈ c, s ∈ K.faces) ∧ ∀ s ∈ c, ∀ t ∈ c, s ≠ t → s ⊂ t ∨ t ⊂ s

/-- Vertex sets prescribed for the barycentric subdivision. -/
def barycentricFaces {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n)) :
    Set (Finset (Euc n)) :=
  {u | ∃ c : Finset (Finset (Euc n)), IsStrictFaceChain K c ∧
      u = c.image barycenter}

/-- Barycenters of a strict chain of nonempty faces are affinely independent. -/
theorem barycentricFaces_affineIndependent {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) :
    ∀ u ∈ barycentricFaces K, AffineIndependent ℝ ((↑) : u → Euc n) := by
  sorry

/-- Subsets of barycenter sets of strict chains are again such sets. -/
theorem barycentricFaces_isLowerSet {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) :
    IsLowerSet (barycentricFaces K) := by
  intro u v hv hu
  obtain ⟨c, hc, rfl⟩ := hu
  refine ⟨c.filter (fun s ↦ barycenter s ∈ v), ?_, ?_⟩
  · constructor
    · intro s hs
      exact hc.1 s (Finset.mem_filter.mp hs).1
    · intro s hs t ht hst
      exact hc.2 s (Finset.mem_filter.mp hs).1 t
        (Finset.mem_filter.mp ht).1 hst
  · ext x
    rw [Finset.mem_image]
    constructor
    · intro hx
      have hx' : x ∈ c.image barycenter := hv hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx'
      exact ⟨s, Finset.mem_filter.mpr ⟨hs, hx⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact (Finset.mem_filter.mp hs).2

/-- (I1) A point of the hull of finitely many barycenters is a positive-weight
combination of the barycenters of some sub-collection (drop the zero weights;
if two faces share a barycenter keep one). -/
theorem barycentricFaces_inter_subset_aux_positive_subchain {n : ℕ}
    (c : Finset (Finset (Euc n))) (x : Euc n)
    (hx : x ∈ convexHull ℝ ((c.image barycenter : Finset (Euc n)) : Set (Euc n))) :
    ∃ c₀ ⊆ c, ∃ w : Finset (Euc n) → ℝ, (∀ s ∈ c₀, 0 < w s) ∧
      ∑ s ∈ c₀, w s = 1 ∧ ∑ s ∈ c₀, w s • barycenter s = x := by
  sorry

/-- (I2) Uniqueness of the barycentric carrier chain: two strict chains of faces
of `K` with positive weights representing the same point are equal.  Both top
faces are the carrier of the point in `K` (positive weight on the top barycenter
puts positive barycentric weight on every vertex of the top face and none
outside it; `K`'s intersection axiom makes the carrier unique), and inside that
simplex the chain is the family of superlevel sets of the point's barycentric
coordinates. -/
theorem barycentricFaces_inter_subset_aux_chain_unique {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (c₀ c₁ : Finset (Finset (Euc n)))
    (h₀ : IsStrictFaceChain K c₀) (h₁ : IsStrictFaceChain K c₁)
    (w₀ w₁ : Finset (Euc n) → ℝ)
    (hw₀ : ∀ s ∈ c₀, 0 < w₀ s) (hw₁ : ∀ s ∈ c₁, 0 < w₁ s)
    (hs₀ : ∑ s ∈ c₀, w₀ s = 1) (hs₁ : ∑ s ∈ c₁, w₁ s = 1)
    (heq : ∑ s ∈ c₀, w₀ s • barycenter s = ∑ s ∈ c₁, w₁ s • barycenter s) :
    c₀ = c₁ := by
  sorry

/-- (I3) A nonnegative normalized combination of barycenters lies in their hull. -/
-- BEGIN SEAT AREA
theorem barycentricFaces_inter_subset_aux_mem_hull {n : ℕ}
    (c : Finset (Finset (Euc n))) (w : Finset (Euc n) → ℝ)
    (hw : ∀ s ∈ c, 0 ≤ w s) (hs : ∑ s ∈ c, w s = 1) :
    ∑ s ∈ c, w s • barycenter s ∈
      convexHull ℝ ((c.image barycenter : Finset (Euc n)) : Set (Euc n)) := by
  refine (convex_convexHull ℝ _).sum_mem hw hs ?_
  intro s hs
  apply subset_convexHull ℝ _
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
-- END SEAT AREA

/-- The common barycentric coordinates of two chain simplices are supported on
their common barycenters.  This is the hard intersection axiom. -/
theorem barycentricFaces_inter_subset {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) :
    ∀ᵉ (s ∈ barycentricFaces K) (t ∈ barycentricFaces K),
      convexHull ℝ (s : Set (Euc n)) ∩ convexHull ℝ (t : Set (Euc n)) ⊆
        convexHull ℝ (s ∩ t : Set (Euc n)) := by
  rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ x ⟨hx, hx'⟩
  obtain ⟨c₀, hsub, w₀, hw₀, hs₀, hx₀⟩ :=
    barycentricFaces_inter_subset_aux_positive_subchain c x hx
  obtain ⟨c₁, hsub', w₁, hw₁, hs₁, hx₁⟩ :=
    barycentricFaces_inter_subset_aux_positive_subchain c' x hx'
  have hchain : ∀ {d e : Finset (Finset (Euc n))}, IsStrictFaceChain K d → e ⊆ d →
      IsStrictFaceChain K e := fun hd he =>
    ⟨fun s hs => hd.1 s (he hs), fun s hs t ht hne => hd.2 s (he hs) t (he ht) hne⟩
  have hc01 : c₀ = c₁ :=
    barycentricFaces_inter_subset_aux_chain_unique K c₀ c₁ (hchain hc hsub)
      (hchain hc' hsub') w₀ w₁ hw₀ hw₁ hs₀ hs₁ (hx₀.trans hx₁.symm)
  subst hc01
  rw [← hx₀]
  refine convexHull_mono ?_ (barycentricFaces_inter_subset_aux_mem_hull c₀ w₀
    (fun s hs => (hw₀ s hs).le) hs₀)
  intro y hy
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  simp only [Finset.coe_inter, Finset.coe_image, Set.mem_inter_iff, Set.mem_image,
    Finset.mem_coe]
  exact ⟨⟨s, hsub hs, rfl⟩, ⟨s, hsub' hs, rfl⟩⟩

/-- Assemble the three independent face facts into Mathlib's geometric complex. -/
def barycentricSubdivision {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (hi : ∀ u ∈ barycentricFaces K, AffineIndependent ℝ ((↑) : u → Euc n))
    (hd : IsLowerSet (barycentricFaces K))
    (hx : ∀ᵉ (s ∈ barycentricFaces K) (t ∈ barycentricFaces K),
      convexHull ℝ (s : Set (Euc n)) ∩ convexHull ℝ (t : Set (Euc n)) ⊆
        convexHull ℝ (s ∩ t : Set (Euc n))) :
    Geometry.SimplicialComplex ℝ (Euc n) :=
  Geometry.SimplicialComplex.ofErase (barycentricFaces K) hi hd hx

/-- Subdivision preserves finiteness of the face set. -/
theorem barycentricSubdivision_finite {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (hi hd hx) :
    (barycentricSubdivision K hi hd hx).faces.Finite := by
  sorry

/-- Every old simplex is the union of the chain simplices, and conversely. -/
theorem barycentricSubdivision_space {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hi hd hx) :
    (barycentricSubdivision K hi hd hx).space = K.space := by
  sorry

/-- Hatcher's mesh estimate for one barycentric subdivision. -/
theorem barycentricSubdivision_mesh {n d : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (hdim : ∀ s ∈ K.faces, s.card ≤ d + 1) (hi hd hx) :
    ∀ u ∈ (barycentricSubdivision K hi hd hx).faces,
      Metric.diam (convexHull ℝ (u : Set (Euc n))) ≤
        (d / (d + 1 : ℝ)) *
          sSup {r : ℝ | ∃ s ∈ K.faces,
            r = Metric.diam (convexHull ℝ (s : Set (Euc n)))} := by
  sorry

/-- Iterating any finite, space-preserving subdivision with the barycentric
mesh contraction produces a prescribed mesh. -/
theorem exists_fine_of_barycentric_step {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (step : ∀ L : Geometry.SimplicialComplex ℝ (Euc n), L.faces.Finite →
      ∃ L' : Geometry.SimplicialComplex ℝ (Euc n), L'.faces.Finite ∧
        L'.space = L.space ∧
        ∀ u ∈ L'.faces,
          Metric.diam (convexHull ℝ (u : Set (Euc n))) ≤
            (n / (n + 1 : ℝ)) *
              sSup {r : ℝ | ∃ s ∈ L.faces,
                r = Metric.diam (convexHull ℝ (s : Set (Euc n)))})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K' : Geometry.SimplicialComplex ℝ (Euc n),
      K'.faces.Finite ∧ K'.space = K.space ∧
      ∀ s ∈ K'.faces,
        Metric.diam (convexHull ℝ (↑s : Set (Euc n))) < ε := by
  sorry

/-- Every finite geometric simplicial complex admits an arbitrarily fine
finite subdivision with unchanged realization. -/
theorem exists_fine_subdivision {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) {ε : ℝ} (hε : 0 < ε) :
    ∃ K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      K'.faces.Finite ∧ K'.space = K.space ∧
      ∀ s ∈ K'.faces, Metric.diam (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))) < ε := by
  have step : ∀ L : Geometry.SimplicialComplex ℝ (Euc n), L.faces.Finite →
      ∃ L' : Geometry.SimplicialComplex ℝ (Euc n), L'.faces.Finite ∧
        L'.space = L.space ∧
        ∀ u ∈ L'.faces,
          Metric.diam (convexHull ℝ (u : Set (Euc n))) ≤
            (n / (n + 1 : ℝ)) *
              sSup {r : ℝ | ∃ s ∈ L.faces,
                r = Metric.diam (convexHull ℝ (s : Set (Euc n)))} := by
    intro L hL
    let hi := barycentricFaces_affineIndependent L
    let hd := barycentricFaces_isLowerSet L
    let hx := barycentricFaces_inter_subset L
    refine ⟨barycentricSubdivision L hi hd hx,
      barycentricSubdivision_finite L hL hi hd hx,
      barycentricSubdivision_space L hi hd hx, ?_⟩
    apply barycentricSubdivision_mesh L hL
    intro s hs
    have hspan := Submodule.finrank_le
      (vectorSpan ℝ (Set.range ((↑) : s → Euc n)))
    have hcard := (L.indep hs).card_le_finrank_succ.trans
      (Nat.add_le_add_right hspan 1)
    simpa using hcard
  exact exists_fine_of_barycentric_step K hK step hε

/-! ## Simplicial approximation interfaces -/

/-- A vertex map which sends every face to a face. -/
def IsSimplicialVertexMap {n m : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (L : Geometry.SimplicialComplex ℝ (Euc m)) (h : Euc n → Euc m) : Prop :=
  (∀ v ∈ K.vertices, h v ∈ L.vertices) ∧
    ∀ s ∈ K.faces, s.image h ∈ L.faces

/-- The (relative) open star expressed using positive barycentric support. -/
def openStar {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (v : Euc n) : Set (Euc n) :=
  {x | ∃ s ∈ K.faces, v ∈ s ∧ x ∈ convexHull ℝ (s : Set (Euc n)) ∧
      x ∉ convexHull ℝ ((s.erase v : Finset (Euc n)) : Set (Euc n))}

/-- A simplicial vertex map has a continuous affine realization. -/
theorem exists_inducedContinuousMap {n m : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (L : Geometry.SimplicialComplex ℝ (Euc m)) (h : Euc n → Euc m)
    (hh : IsSimplicialVertexMap K L h) :
    ∃ f : C(K.space, L.space),
      (∀ v (hv : v ∈ K.vertices), f ⟨v, Geometry.SimplicialComplex.vertices_subset_space hv⟩ =
        ⟨h v, Geometry.SimplicialComplex.vertices_subset_space (hh.1 v hv)⟩) ∧
      ∀ s ∈ K.faces, ∀ x : K.space,
        (x : Euc n) ∈ convexHull ℝ (s : Set (Euc n)) →
        (f x : Euc m) ∈ convexHull ℝ (s.image h : Set (Euc m)) := by
  sorry

/-- The star condition makes the affine realization straight-line homotopic
to the original map. -/
theorem inducedMap_homotopic_of_star_condition {n m : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (L : Geometry.SimplicialComplex ℝ (Euc m))
    (g f : C(K.space, L.space)) (h : Euc n → Euc m)
    (hstar : ∀ v ∈ K.vertices,
      g '' ((Subtype.val : K.space → Euc n) ⁻¹' openStar K v) ⊆
        (Subtype.val : L.space → Euc m) ⁻¹' openStar L (h v))
    (haff : ∀ s ∈ K.faces, ∀ x : K.space,
      (x : Euc n) ∈ convexHull ℝ (s : Set (Euc n)) →
      (f x : Euc m) ∈ convexHull ℝ (s.image h : Set (Euc m))) :
    ContinuousMap.Homotopic g f := by
  sorry

/-- Lebesgue-number simplicial approximation: sufficiently small stars admit
a vertex choice satisfying the star condition. -/
theorem exists_vertexMap_of_mesh_lt_lebesgue {n m : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (L : Geometry.SimplicialComplex ℝ (Euc m)) (g : C(K.space, L.space))
    (δ : ℝ) (hδ : 0 < δ)
    (hlebesgue : ∀ x : K.space, ∃ w ∈ L.vertices,
      Metric.ball x δ ⊆ g ⁻¹' ((Subtype.val : L.space → Euc m) ⁻¹' openStar L w))
    (hmesh : ∀ s ∈ K.faces,
      Metric.diam (convexHull ℝ (s : Set (Euc n))) < δ / 2) :
    ∃ h : Euc n → Euc m, IsSimplicialVertexMap K L h ∧
      ∀ v ∈ K.vertices,
        g '' ((Subtype.val : K.space → Euc n) ⁻¹' openStar K v) ⊆
          (Subtype.val : L.space → Euc m) ⁻¹' openStar L (h v) := by
  sorry

end ConstructionTargets.GeometricSimplicialSubdivision

#print axioms ConstructionTargets.GeometricSimplicialSubdivision.exists_fine_subdivision
