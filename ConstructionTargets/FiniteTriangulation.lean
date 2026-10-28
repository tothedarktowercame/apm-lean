import Mathlib
import ConstructionTargets.LefschetzCompactPolyhedron
import ConstructionTargets.PointWedgeQuotient
import ConstructionTargets.StatementSurfaceModels

/-! # Finite triangulations and point wedges

Interfaces used by the three finite-polyhedron adapters in the Lefschetz
cluster.  A marked triangulation remembers that the distinguished point is a
vertex; this is the datum needed to glue triangulations across a point wedge.
-/

open Set

noncomputable section

namespace ConstructionTargets.FiniteTriangulation

open ConstructionTargets.LefschetzCompactPolyhedron
open ConstructionTargets.PointWedgeQuotient

/-- A finite geometric triangulation in which `x₀` is represented by a vertex. -/
def HasFiniteVertexTriangulation (X : Type) [TopologicalSpace X] (x₀ : X) : Prop :=
  ∃ (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
      (e : X ≃ₜ K.space) (v : EuclideanSpace ℝ (Fin n)),
    K.faces.Finite ∧ {v} ∈ K.faces ∧ (e x₀ : EuclideanSpace ℝ (Fin n)) = v

/-- Forgetting the marked vertex gives an ordinary finite triangulation. -/
theorem HasFiniteVertexTriangulation.isFinitePolyhedron
    {X : Type} [TopologicalSpace X] {x₀ : X}
    (h : HasFiniteVertexTriangulation X x₀) : IsFinitePolyhedron X := by
  obtain ⟨n, K, e, _v, hfinite, _hv, _hx⟩ := h
  exact ⟨n, K, hfinite, ⟨e⟩⟩

/-- **LIBRARY (stellar subdivision).** A chosen point of a finite polyhedron
can be made a vertex by a finite subdivision, without changing its topology. -/
theorem hasFiniteVertexTriangulation_of_isFinitePolyhedron
    {X : Type} [TopologicalSpace X] (x₀ : X)
    (hX : IsFinitePolyhedron X) : HasFiniteVertexTriangulation X x₀ := by
  sorry

theorem wedge_isFinitePolyhedron_of_vertexTriangulations_aux_base_eq
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) :
    quotientMap x₀ y₀ (.inl x₀) = quotientMap x₀ y₀ (.inr y₀) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ Rel.base

/-- Banked from lemma-3's partial (2026-10-28). Route for (G1), claude-14:
`j₁ x := WithLp.toLp 2 (Fin.append (WithLp.ofLp (x - v₁)) 0)`,
`j₂ y := WithLp.toLp 2 (Fin.append 0 (WithLp.ofLp (y - v₂)))` (affine, injective,
continuous); faces `F := (Finset.image j₁) '' K₁.faces ∪ (Finset.image j₂) '' K₂.faces`;
build `K` by `Geometry.SimplicialComplex.ofErase F` inside the proof (independence:
affine-injective images; lower set: images of subsets; intersection: a point in
both a `j₁`-face and a `j₂`-face is `0`, which then is a vertex of both by
`_aux_vertex_mem_hull_iff`; same-side faces by `K₁`/`K₂`'s own axiom pulled back
along the injective affine map); `p := 0`. -/
theorem wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_vertex_mem_space
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (v : EuclideanSpace ℝ (Fin n)) (hv : {v} ∈ K.faces) : v ∈ K.space := by
  exact K.subset_space hv (by simp)

theorem wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_vertex_mem_hull_iff
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (v : EuclideanSpace ℝ (Fin n)) (s : Finset (EuclideanSpace ℝ (Fin n)))
    (hv : {v} ∈ K.faces) (hs : s ∈ K.faces) :
    v ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin n))) ↔ v ∈ s := by
  exact K.vertex_mem_convexHull_iff hv hs

def wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1
    {a b : ℕ} (v₁ : EuclideanSpace ℝ (Fin a)) :
    EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin (a + b)) :=
  fun x => WithLp.toLp 2 (Fin.append (WithLp.ofLp (x - v₁)) 0)

def wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j2
    {a b : ℕ} (v₂ : EuclideanSpace ℝ (Fin b)) :
    EuclideanSpace ℝ (Fin b) → EuclideanSpace ℝ (Fin (a + b)) :=
  fun y => WithLp.toLp 2 (Fin.append 0 (WithLp.ofLp (y - v₂)))

theorem wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1_injective
    {a b : ℕ} (v₁ : EuclideanSpace ℝ (Fin a)) :
    Function.Injective
      (wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1 (b := b) v₁) := by
  intro x y h
  have h' := congrArg WithLp.ofLp h
  have hv : x - v₁ = y - v₁ := by
    ext i
    have hi := congrFun h' (Fin.castAdd b i)
    simpa [wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1] using hi
  exact sub_left_inj.mp hv

theorem wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j2_injective
    {a b : ℕ} (v₂ : EuclideanSpace ℝ (Fin b)) :
    Function.Injective
      (wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j2 (a := a) v₂) := by
  intro x y h
  have h' := congrArg WithLp.ofLp h
  have hv : x - v₂ = y - v₂ := by
    ext i
    have hi := congrFun h' (Fin.natAdd a i)
    simpa [wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j2] using hi
  exact sub_left_inj.mp hv

open scoped Classical in
/-- Faces of the glued complex: subsets of images of faces of either side. -/
def wedgeFaces {a b : ℕ}
    (K₁ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (K₂ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin b)))
    (v₁ : EuclideanSpace ℝ (Fin a)) (v₂ : EuclideanSpace ℝ (Fin b)) : Set (Finset (EuclideanSpace ℝ (Fin (a + b)))) :=
  {u | (∃ s ∈ K₁.faces, u ⊆ s.image (wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1 (b := b) v₁)) ∨
      (∃ s ∈ K₂.faces, u ⊆ s.image (wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j2 (a := a) v₂))}

theorem wedgeFaces_isLowerSet {a b : ℕ}
    (K₁ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (K₂ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin b)))
    (v₁ : EuclideanSpace ℝ (Fin a)) (v₂ : EuclideanSpace ℝ (Fin b)) : IsLowerSet (wedgeFaces K₁ K₂ v₁ v₂) := by
  intro u w hwu hu
  rcases hu with ⟨s, hs, h⟩ | ⟨s, hs, h⟩
  · exact Or.inl ⟨s, hs, (Finset.le_iff_subset.mp hwu).trans h⟩
  · exact Or.inr ⟨s, hs, (Finset.le_iff_subset.mp hwu).trans h⟩

/-- (E1) Faces are affinely independent (subsets of affine-injective images of
independent sets). -/
theorem wedgeFaces_indep {a b : ℕ}
    (K₁ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (K₂ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin b)))
    (v₁ : EuclideanSpace ℝ (Fin a)) (v₂ : EuclideanSpace ℝ (Fin b)) :
    ∀ u ∈ wedgeFaces K₁ K₂ v₁ v₂, AffineIndependent ℝ ((↑) : u → EuclideanSpace ℝ (Fin (a + b))) := by
  sorry

/-- (E2) Intersection axiom: same-side faces pull back to `K₁`/`K₂`'s axiom;
a point in a `j₁`-face and a `j₂`-face is `j₁ v₁ = j₂ v₂ = 0`, a vertex of both
(`_aux_vertex_mem_hull_iff`). -/
theorem wedgeFaces_inter {a b : ℕ}
    (K₁ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (K₂ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin b)))
    (v₁ : EuclideanSpace ℝ (Fin a)) (v₂ : EuclideanSpace ℝ (Fin b))
    (hv₁ : {v₁} ∈ K₁.faces) (hv₂ : {v₂} ∈ K₂.faces) :
    ∀ᵉ (s ∈ wedgeFaces K₁ K₂ v₁ v₂) (t ∈ wedgeFaces K₁ K₂ v₁ v₂),
      convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (a + b)))) ∩ convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin (a + b)))) ⊆
        convexHull ℝ (s ∩ t : Set (EuclideanSpace ℝ (Fin (a + b)))) := by
  sorry

/-- (E3) The union of the face hulls is the union of the two embedded spaces. -/
theorem wedgeFaces_space {a b : ℕ}
    (K₁ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (K₂ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin b)))
    (v₁ : EuclideanSpace ℝ (Fin a)) (v₂ : EuclideanSpace ℝ (Fin b)) (z : EuclideanSpace ℝ (Fin (a + b))) :
    (∃ s ∈ wedgeFaces K₁ K₂ v₁ v₂, z ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (a + b))))) ↔
      (∃ x ∈ K₁.space, wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1 (b := b) v₁ x = z) ∨ (∃ y ∈ K₂.space, wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j2 (a := a) v₂ y = z) := by
  sorry

/-- (E4) The two embeddings meet only at the marked vertices. -/
theorem wedge_j_meet {a b : ℕ} (v₁ : EuclideanSpace ℝ (Fin a)) (v₂ : EuclideanSpace ℝ (Fin b)) (x : EuclideanSpace ℝ (Fin a)) (y : EuclideanSpace ℝ (Fin b)) :
    wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1 (b := b) v₁ x = wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j2 (a := a) v₂ y ↔ x = v₁ ∧ y = v₂ := by
  constructor
  · intro h
    have h' := congrArg WithLp.ofLp h
    constructor
    · apply sub_eq_zero.mp
      ext i
      have hi := congrFun h' (Fin.castAdd b i)
      simpa [wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1,
        wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j2] using hi
    · apply sub_eq_zero.mp
      ext i
      have hi := congrFun h' (Fin.natAdd a i)
      simpa [wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1,
        wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j2] using hi.symm
  · rintro ⟨rfl, rfl⟩
    simp [wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1,
      wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j2]

/-- (E5) Finitely many faces. -/
theorem wedgeFaces_finite {a b : ℕ}
    (K₁ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (K₂ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin b)))
    (h₁ : K₁.faces.Finite) (h₂ : K₂.faces.Finite)
    (v₁ : EuclideanSpace ℝ (Fin a)) (v₂ : EuclideanSpace ℝ (Fin b)) : (wedgeFaces K₁ K₂ v₁ v₂).Finite := by
  sorry

/-- (E6) The embeddings are continuous (affine). -/
theorem wedge_j_continuous {a b : ℕ} (v₁ : EuclideanSpace ℝ (Fin a)) (v₂ : EuclideanSpace ℝ (Fin b)) :
    Continuous (wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1 (b := b) v₁) ∧ Continuous (wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j2 (a := a) v₂) := by
  sorry

/-- (G1) Two finite complexes glued at one vertex each: translate the marked
vertices to the origin and place the complexes in the two factors of
`ℝ^(a+b)`.  The images meet only at the origin; the intersection axiom holds
because a vertex lying in the hull of a face is a vertex of that face. -/
theorem wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed {a b : ℕ}
    (K₁ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (K₂ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin b)))
    (h₁ : K₁.faces.Finite) (h₂ : K₂.faces.Finite)
    (v₁ : EuclideanSpace ℝ (Fin a)) (v₂ : EuclideanSpace ℝ (Fin b))
    (hv₁ : {v₁} ∈ K₁.faces) (hv₂ : {v₂} ∈ K₂.faces) :
    ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
      (ι₁ : C(K₁.space, K.space)) (ι₂ : C(K₂.space, K.space))
      (p : EuclideanSpace ℝ (Fin N)),
      K.faces.Finite ∧ {p} ∈ K.faces ∧
      Function.Injective ι₁ ∧ Function.Injective ι₂ ∧
      (∀ z : K.space, (∃ x, ι₁ x = z) ∨ (∃ y, ι₂ y = z)) ∧
      (∀ x y, ι₁ x = ι₂ y ↔
        ((x : EuclideanSpace ℝ (Fin a)) = v₁ ∧ (y : EuclideanSpace ℝ (Fin b)) = v₂)) ∧
      (∀ x : K₁.space, (x : EuclideanSpace ℝ (Fin a)) = v₁ →
        (ι₁ x : EuclideanSpace ℝ (Fin N)) = p) := by
  classical
  let F := wedgeFaces K₁ K₂ v₁ v₂
  let K := Geometry.SimplicialComplex.ofErase F (wedgeFaces_indep K₁ K₂ v₁ v₂)
    (wedgeFaces_isLowerSet K₁ K₂ v₁ v₂) (wedgeFaces_inter K₁ K₂ v₁ v₂ hv₁ hv₂)
  have hspace : ∀ z, z ∈ K.space ↔
      (∃ x ∈ K₁.space, wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1 (b := b) v₁ x = z) ∨ (∃ y ∈ K₂.space, wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j2 (a := a) v₂ y = z) := by
    intro z
    rw [← wedgeFaces_space K₁ K₂ v₁ v₂ z, Geometry.SimplicialComplex.mem_space_iff]
    constructor
    · rintro ⟨u, hu, hz⟩; exact ⟨u, hu.1, hz⟩
    · rintro ⟨u, hu, hz⟩
      refine ⟨u, ⟨hu, ?_⟩, hz⟩
      rintro rfl
      simp at hz
  obtain ⟨hc₁, hc₂⟩ := wedge_j_continuous (a := a) (b := b) v₁ v₂
  let ι₁ : C(K₁.space, K.space) :=
    ⟨fun x => ⟨wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1 v₁ x, (hspace _).2 (Or.inl ⟨x, x.2, rfl⟩)⟩,
      (hc₁.comp continuous_subtype_val).subtype_mk _⟩
  let ι₂ : C(K₂.space, K.space) :=
    ⟨fun y => ⟨wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j2 v₂ y, (hspace _).2 (Or.inr ⟨y, y.2, rfl⟩)⟩,
      (hc₂.comp continuous_subtype_val).subtype_mk _⟩
  refine ⟨a + b, K, ι₁, ι₂, wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1 v₁ v₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (wedgeFaces_finite K₁ K₂ h₁ h₂ v₁ v₂).diff
  · refine ⟨Or.inl ⟨{v₁}, hv₁, by simp⟩, by simp⟩
  · intro x y h
    exact Subtype.ext (wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1_injective v₁ (congrArg Subtype.val h))
  · intro x y h
    exact Subtype.ext (wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j2_injective v₂ (congrArg Subtype.val h))
  · intro z
    rcases (hspace z).1 z.2 with ⟨x, hx, hxz⟩ | ⟨y, hy, hyz⟩
    · exact Or.inl ⟨⟨x, hx⟩, Subtype.ext hxz⟩
    · exact Or.inr ⟨⟨y, hy⟩, Subtype.ext hyz⟩
  · intro x y
    rw [← wedge_j_meet v₁ v₂ x y]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · intro x hx
    change wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1 v₁ x = wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed_aux_j1 v₁ v₁
    rw [hx]

/-- (G2) From (G1)'s embedding data and marked homeomorphisms `X ≃ₜ K₁.space`,
`Y ≃ₜ K₂.space`, the wedge is homeomorphic to `K.space` with the wedge point at
`p`: the map induced on the quotient by `Sum.elim (ι₁ ∘ e₁) (ι₂ ∘ e₂)` is a
continuous bijection from a compact space to a Hausdorff one. -/
theorem wedge_isFinitePolyhedron_of_vertexTriangulations_aux_homeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) {a b N : ℕ}
    (K₁ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (K₂ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin b)))
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (h₁ : K₁.faces.Finite) (h₂ : K₂.faces.Finite) (hK : K.faces.Finite)
    (e₁ : X ≃ₜ K₁.space) (e₂ : Y ≃ₜ K₂.space)
    (v₁ : EuclideanSpace ℝ (Fin a)) (v₂ : EuclideanSpace ℝ (Fin b))
    (he₁ : (e₁ x₀ : EuclideanSpace ℝ (Fin a)) = v₁)
    (he₂ : (e₂ y₀ : EuclideanSpace ℝ (Fin b)) = v₂)
    (ι₁ : C(K₁.space, K.space)) (ι₂ : C(K₂.space, K.space))
    (p : EuclideanSpace ℝ (Fin N))
    (hinj₁ : Function.Injective ι₁) (hinj₂ : Function.Injective ι₂)
    (hcov : ∀ z : K.space, (∃ x, ι₁ x = z) ∨ (∃ y, ι₂ y = z))
    (hmeet : ∀ x y, ι₁ x = ι₂ y ↔
      ((x : EuclideanSpace ℝ (Fin a)) = v₁ ∧ (y : EuclideanSpace ℝ (Fin b)) = v₂))
    (hp : ∀ x : K₁.space, (x : EuclideanSpace ℝ (Fin a)) = v₁ →
      (ι₁ x : EuclideanSpace ℝ (Fin N)) = p) :
    ∃ e : Wedge x₀ y₀ ≃ₜ K.space,
      (e (quotientMap x₀ y₀ (.inl x₀)) : EuclideanSpace ℝ (Fin N)) = p := by
  let g : Sum X Y → K.space :=
    Sum.elim (fun x => ι₁ (e₁ x)) (fun y => ι₂ (e₂ y))
  have hgbase : g (.inl x₀) = g (.inr y₀) := by
    apply (hmeet (e₁ x₀) (e₂ y₀)).2
    exact ⟨he₁, he₂⟩
  have hgrel : ∀ s t, Relation.EqvGen (Rel x₀ y₀) s t → g s = g t := by
    intro s t h
    induction h with
    | rel s t hst => cases hst; exact hgbase
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  let f : Wedge x₀ y₀ → K.space := Quotient.lift g hgrel
  have hf_surj : Function.Surjective f := by
    intro z
    rcases hcov z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · refine ⟨quotientMap x₀ y₀ (.inl (e₁.symm x)), ?_⟩
      change ι₁ (e₁ (e₁.symm x)) = ι₁ x
      rw [e₁.apply_symm_apply]
    · refine ⟨quotientMap x₀ y₀ (.inr (e₂.symm y)), ?_⟩
      change ι₂ (e₂ (e₂.symm y)) = ι₂ y
      rw [e₂.apply_symm_apply]
  have hf_inj : Function.Injective f := by
    rintro ⟨s⟩ ⟨t⟩ h
    apply Quotient.sound
    cases s with
    | inl x =>
      cases t with
      | inl x' =>
        have : e₁ x = e₁ x' := hinj₁ h
        have hxx : x = x' := e₁.injective this
        subst x'
        exact Relation.EqvGen.refl _
      | inr y =>
        have hm := (hmeet (e₁ x) (e₂ y)).1 h
        have hx : x = x₀ := e₁.injective (Subtype.ext (hm.1.trans he₁.symm))
        have hy : y = y₀ := e₂.injective (Subtype.ext (hm.2.trans he₂.symm))
        subst x; subst y
        exact Relation.EqvGen.rel _ _ Rel.base
    | inr y =>
      cases t with
      | inl x =>
        have hm := (hmeet (e₁ x) (e₂ y)).1 h.symm
        have hx : x = x₀ := e₁.injective (Subtype.ext (hm.1.trans he₁.symm))
        have hy : y = y₀ := e₂.injective (Subtype.ext (hm.2.trans he₂.symm))
        subst x; subst y
        exact (Relation.EqvGen.rel _ _ Rel.base).symm
      | inr y' =>
        have : e₂ y = e₂ y' := hinj₂ h
        have hyy : y = y' := e₂.injective this
        subst y'
        exact Relation.EqvGen.refl _
  have hgcont : Continuous g := by
    apply continuous_sum_dom.2
    exact ⟨ι₁.continuous.comp e₁.continuous, ι₂.continuous.comp e₂.continuous⟩
  have hfcont : Continuous f := by
    apply Continuous.quotient_lift
    exact hgcont
  have hcompact₁ : IsCompact K₁.space := by
    rw [Geometry.SimplicialComplex.space]
    exact h₁.isCompact_biUnion fun s _ => s.finite_toSet.isCompact_convexHull ℝ
  have hcompact₂ : IsCompact K₂.space := by
    rw [Geometry.SimplicialComplex.space]
    exact h₂.isCompact_biUnion fun s _ => s.finite_toSet.isCompact_convexHull ℝ
  letI : CompactSpace K₁.space := isCompact_iff_compactSpace.mp hcompact₁
  letI : CompactSpace K₂.space := isCompact_iff_compactSpace.mp hcompact₂
  letI : CompactSpace X := e₁.symm.compactSpace
  letI : CompactSpace Y := e₂.symm.compactSpace
  have hwcompact : IsCompact (Set.univ : Set (Wedge x₀ y₀)) := by
    rw [← Set.range_eq_univ.mpr (surjective_quotientMap x₀ y₀), ← image_univ]
    exact isCompact_univ.image (continuous_quotientMap x₀ y₀)
  letI : CompactSpace (Wedge x₀ y₀) := ⟨hwcompact⟩
  let e : Wedge x₀ y₀ ≃ₜ K.space :=
    hfcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  refine ⟨e, ?_⟩
  change (ι₁ (e₁ x₀) : EuclideanSpace ℝ (Fin N)) = p
  exact hp (e₁ x₀) he₁

/-- **LIBRARY (simplicial point gluing).** Triangulations whose marked points
are vertices glue to a finite geometric triangulation of the point wedge. -/
theorem wedge_isFinitePolyhedron_of_vertexTriangulations
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y)
    (hX : HasFiniteVertexTriangulation X x₀)
    (hY : HasFiniteVertexTriangulation Y y₀) :
    HasFiniteVertexTriangulation (Wedge x₀ y₀) (quotientMap x₀ y₀ (.inl x₀)) := by
  obtain ⟨a, K₁, e₁, v₁, hK₁, hv₁, he₁⟩ := hX
  obtain ⟨b, K₂, e₂, v₂, hK₂, hv₂, he₂⟩ := hY
  obtain ⟨N, K, ι₁, ι₂, p, hK, hp, hinj₁, hinj₂, hcov, hmeet, hpv⟩ :=
    wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed K₁ K₂ hK₁ hK₂ v₁ v₂ hv₁ hv₂
  obtain ⟨e, he⟩ := wedge_isFinitePolyhedron_of_vertexTriangulations_aux_homeomorph
    x₀ y₀ K₁ K₂ K hK₁ hK₂ hK e₁ e₂ v₁ v₂ he₁ he₂ ι₁ ι₂ p hinj₁ hinj₂ hcov hmeet hpv
  exact ⟨N, K, e, p, hK, hp, he⟩

/-- Finite polyhedra are closed under point wedges. -/
theorem wedge_isFinitePolyhedron
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (hX : IsFinitePolyhedron X)
    (hY : IsFinitePolyhedron Y) : IsFinitePolyhedron (Wedge x₀ y₀) := by
  exact (wedge_isFinitePolyhedron_of_vertexTriangulations x₀ y₀
    (hasFiniteVertexTriangulation_of_isFinitePolyhedron x₀ hX)
    (hasFiniteVertexTriangulation_of_isFinitePolyhedron y₀ hY)).isFinitePolyhedron

/-- SUPERSEDED (claude-14, 2026-10-28): consumers use
`RealProjectivePlaneTriangulation.realProjectivePlane_hasFiniteVertexTriangulation`
(that module imports this one); not queued.
**LIBRARY (concrete `RP²` triangulation).** The subdivided polygon model
has a finite triangulation in which the disk centre is a vertex. -/
theorem realProjectivePlane_hasFiniteVertexTriangulation :
    HasFiniteVertexTriangulation
      ConstructionTargets.StatementSurfaceModels.RealProjectivePlane
      (ConstructionTargets.StatementSurfaceModels.surfacePoint false 1) := by
  sorry

end ConstructionTargets.FiniteTriangulation
