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
-- BEGIN SEAT AREA
theorem barycentricFaces_affineIndependent {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) :
    ∀ u ∈ barycentricFaces K, AffineIndependent ℝ ((↑) : u → Euc n) := by
  sorry
-- END SEAT AREA

/-- Subsets of barycenter sets of strict chains are again such sets. -/
theorem barycentricFaces_isLowerSet {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) :
    IsLowerSet (barycentricFaces K) := by
  sorry

/-- The common barycentric coordinates of two chain simplices are supported on
their common barycenters.  This is the hard intersection axiom. -/
theorem barycentricFaces_inter_subset {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) :
    ∀ᵉ (s ∈ barycentricFaces K) (t ∈ barycentricFaces K),
      convexHull ℝ (s : Set (Euc n)) ∩ convexHull ℝ (t : Set (Euc n)) ⊆
        convexHull ℝ (s ∩ t : Set (Euc n)) := by
  sorry

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
