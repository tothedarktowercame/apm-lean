import ConstructionTargets.FiniteTriangulation
import ConstructionTargets.CompactClosedEquivalenceQuotient

/-! # A finite marked triangulation of the real projective plane

This file isolates the concrete polygon-triangulation input from the compact-to-Hausdorff
topological upgrade.  The intended proof of `rp2_explicit_finite_model` uses the six-vertex
triangulation of `RP²` (ten triangles), realized by coordinate vertices.
-/

open Set

noncomputable section

namespace ConstructionTargets.RealProjectivePlaneTriangulation

open ConstructionTargets.FiniteTriangulation
open ConstructionTargets.StatementSurfaceModels

/-- The one-crosscap polygon quotient is Hausdorff.  Concretely, its generating relation
identifies a boundary point with its antipode and is a closed equivalence relation on the
compact disk. -/
theorem rp2_t2Space_aux_edge_neg (t : Set.Icc (0 : ℝ) 1) :
    ((Surfaces.edgePoint 2 1 t : Surfaces.Disk) : ℂ) =
      -((Surfaces.edgePoint 2 0 t : Surfaces.Disk) : ℂ) := by
  simp only [Surfaces.edgePoint, Subtype.coe_mk]
  norm_num
  change Complex.exp (Complex.I * (2 * (Real.pi : ℂ) *
    (1 + (t.1 : ℂ)) / 2)) =
    -Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (t.1 : ℂ) / 2))
  calc
    _ = Complex.exp (Real.pi * Complex.I) *
        Complex.exp (Complex.I * (Real.pi * t.1)) := by
          rw [← Complex.exp_add]
          congr 1
          ring_nf
    _ = _ := by rw [Complex.exp_pi_mul_I]; ring

theorem rp2_t2Space_aux_rel_cases {x y : Surfaces.Disk}
    (h : Surfaces.SurfaceRel false 1 x y) :
    ‖(x : ℂ)‖ = 1 ∧ (y : ℂ) = -(x : ℂ) := by
  simp only [Surfaces.SurfaceRel, Bool.false_eq_true, if_false] at h
  rcases h with ⟨j, hj, t, rfl, rfl⟩
  have : j = 0 := by omega
  subst j
  constructor
  · simp [Surfaces.edgePoint, Complex.norm_exp]
  · exact rp2_t2Space_aux_edge_neg t

theorem rp2_t2Space_aux_eqv_cases {x y : Surfaces.Disk}
    (h : Relation.EqvGen (Surfaces.SurfaceRel false 1) x y) :
    x = y ∨ (‖(x : ℂ)‖ = 1 ∧ (y : ℂ) = -(x : ℂ)) := by
  induction h with
  | rel x y h => exact Or.inr (rp2_t2Space_aux_rel_cases h)
  | refl x => exact Or.inl rfl
  | symm x y _ ih =>
      rcases ih with rfl | ⟨hx, hy⟩
      · exact Or.inl rfl
      · right
        constructor
        · rw [hy, norm_neg, hx]
        · rw [hy, neg_neg]
  | trans x y z _ _ ih₁ ih₂ =>
      rcases ih₁ with rfl | ⟨hx, hy⟩
      · exact ih₂
      · rcases ih₂ with rfl | ⟨hy', hz⟩
        · exact Or.inr ⟨hx, hy⟩
        · left
          apply Subtype.ext
          change (x : ℂ) = (z : ℂ)
          rw [hz, hy, neg_neg]

/-- Converse of `rp2_t2Space_aux_eqv_cases`: every boundary point is identified
with its antipode (write it as `edgePoint 2 0 t` or `edgePoint 2 1 t`). -/
theorem rp2_t2Space_aux_boundary_rel {x y : Surfaces.Disk}
    (hx : ‖(x : ℂ)‖ = 1) (hy : (y : ℂ) = -(x : ℂ)) :
    Relation.EqvGen (Surfaces.SurfaceRel false 1) x y := by
  by_cases harg : 0 ≤ Complex.arg (x : ℂ)
  · let t : Set.Icc (0 : ℝ) 1 :=
      ⟨Complex.arg (x : ℂ) / Real.pi, by
        constructor
        · exact div_nonneg harg Real.pi_pos.le
        · exact (div_le_one Real.pi_pos).2 (Complex.arg_le_pi _)⟩
    apply Relation.EqvGen.rel _ _
    simp only [Surfaces.SurfaceRel, Bool.false_eq_true, if_false]
    refine ⟨0, by omega, t, ?_, ?_⟩
    · apply Subtype.ext
      simp only [Surfaces.edgePoint, Subtype.coe_mk]
      norm_num
      change (x : ℂ) = Complex.exp
        (Complex.I * (2 * Real.pi * t.1 / 2))
      rw [show (x : ℂ) = Complex.exp (Complex.arg (x : ℂ) * Complex.I) by
        symm
        simpa [hx] using Complex.norm_mul_exp_arg_mul_I (x : ℂ)]
      congr 1
      simp [t]
      field_simp [ne_of_gt Real.pi_pos]
    · apply Subtype.ext
      simp only [Surfaces.edgePoint, Subtype.coe_mk]
      norm_num
      change (y : ℂ) = Complex.exp
        (Complex.I * (2 * Real.pi * ((1 : ℝ) + t.1) / 2))
      rw [hy, show (x : ℂ) = Complex.exp (Complex.arg (x : ℂ) * Complex.I) by
        symm
        simpa [hx] using Complex.norm_mul_exp_arg_mul_I (x : ℂ)]
      rw [show -Complex.exp (Complex.arg (x : ℂ) * Complex.I) =
          Complex.exp (Real.pi * Complex.I) *
            Complex.exp (Complex.arg (x : ℂ) * Complex.I) by
        rw [Complex.exp_pi_mul_I]
        simp]
      rw [← Complex.exp_add]
      apply congrArg Complex.exp
      simp [t]
      field_simp [ne_of_gt Real.pi_pos]
  · let t : Set.Icc (0 : ℝ) 1 :=
      ⟨Complex.arg (x : ℂ) / Real.pi + 1, by
        constructor
        · have h := Complex.neg_pi_lt_arg (x : ℂ)
          have : (-1 : ℝ) < Complex.arg (x : ℂ) / Real.pi :=
            (lt_div_iff₀ Real.pi_pos).2 (by linarith)
          linarith
        · have ha : Complex.arg (x : ℂ) ≤ 0 := le_of_not_ge harg
          have := div_nonpos_of_nonpos_of_nonneg ha Real.pi_pos.le
          linarith⟩
    apply Relation.EqvGen.symm _ _
    apply Relation.EqvGen.rel _ _
    simp only [Surfaces.SurfaceRel, Bool.false_eq_true, if_false]
    refine ⟨0, by omega, t, ?_, ?_⟩
    · apply Subtype.ext
      simp only [Surfaces.edgePoint, Subtype.coe_mk]
      norm_num
      change (y : ℂ) = Complex.exp
        (Complex.I * (2 * Real.pi * t.1 / 2))
      rw [hy, show (x : ℂ) = Complex.exp (Complex.arg (x : ℂ) * Complex.I) by
        symm
        simpa [hx] using Complex.norm_mul_exp_arg_mul_I (x : ℂ)]
      rw [show -Complex.exp (Complex.arg (x : ℂ) * Complex.I) =
          Complex.exp (Real.pi * Complex.I) *
            Complex.exp (Complex.arg (x : ℂ) * Complex.I) by
        rw [Complex.exp_pi_mul_I]
        simp]
      rw [← Complex.exp_add]
      apply congrArg Complex.exp
      simp [t]
      field_simp [ne_of_gt Real.pi_pos]
      ring
    · apply Subtype.ext
      simp only [Surfaces.edgePoint, Subtype.coe_mk]
      norm_num
      change (x : ℂ) = Complex.exp
        (Complex.I * (2 * Real.pi * ((1 : ℝ) + t.1) / 2))
      rw [show (x : ℂ) = Complex.exp (Complex.arg (x : ℂ) * Complex.I) by
        symm
        simpa [hx] using Complex.norm_mul_exp_arg_mul_I (x : ℂ)]
      rw [← mul_one (Complex.exp (Complex.arg (x : ℂ) * Complex.I)),
        ← Complex.exp_two_pi_mul_I, ← Complex.exp_add]
      apply congrArg Complex.exp
      simp [t]
      field_simp [ne_of_gt Real.pi_pos]
      ring

theorem rp2_t2Space_aux_isClosed :
    IsClosed {p : Surfaces.Disk × Surfaces.Disk |
      (Relation.EqvGen.setoid (Surfaces.SurfaceRel false 1)).r p.1 p.2} := by
  have hset : {p : Surfaces.Disk × Surfaces.Disk |
      (Relation.EqvGen.setoid (Surfaces.SurfaceRel false 1)).r p.1 p.2} =
      {p | p.1 = p.2} ∪ {p | ‖(p.1 : ℂ)‖ = 1 ∧ (p.2 : ℂ) = -(p.1 : ℂ)} := by
    ext p
    constructor
    · intro h
      exact rp2_t2Space_aux_eqv_cases h
    · rintro (h | ⟨hx, hy⟩)
      · obtain ⟨a, b⟩ := p
        change a = b at h
        subst h
        exact Relation.EqvGen.refl _
      · exact rp2_t2Space_aux_boundary_rel hx hy
  rw [hset]
  refine (isClosed_diagonal).union (IsClosed.inter ?_ ?_)
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_eq (by fun_prop) (by fun_prop)

theorem rp2_t2Space : T2Space RealProjectivePlane := by
  haveI : CompactSpace Surfaces.Disk :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  exact compact_closed_equivalence_quotient_t2 _ rp2_t2Space_aux_isClosed

/-- A finite geometric simplicial complex has compact underlying space. -/
theorem finite_simplicialComplex_space_isCompact
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) : IsCompact K.space := by
  rw [Geometry.SimplicialComplex.space]
  exact hK.isCompact_biUnion fun s _ =>
    s.finite_toSet.isCompact_convexHull ℝ

/-- Standard basis vector, used to realize an abstract complex on `Fin N`. -/
def basisVertex (N : ℕ) (i : Fin N) : EuclideanSpace ℝ (Fin N) :=
  EuclideanSpace.single i 1

/-- Basis vertices of any finite vertex set are affinely independent. -/
lemma rp2_explicit_finite_model_aux_basis_indep {N : ℕ} (s : Finset (Fin N)) :
    AffineIndependent ℝ
      ((↑) : ↥(s.image (basisVertex N)) → EuclideanSpace ℝ (Fin N)) := by
  apply LinearIndependent.affineIndependent
  rw [linearIndependent_subtype_iff]
  apply EuclideanSpace.orthonormal_single.linearIndependent.linearIndepOn_id.mono
  intro x hx
  simp only [Finset.mem_coe, Finset.mem_image] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact ⟨i, rfl⟩

/-- Convex hulls of basis-vertex faces meet in the hull of the common face
(a point of either hull has nonnegative coordinates summing to `1`, supported
on the face's index set). -/
lemma rp2_explicit_finite_model_aux_basis_inter {N : ℕ} (s t : Finset (Fin N)) :
    convexHull ℝ (↑(s.image (basisVertex N)) : Set (EuclideanSpace ℝ (Fin N))) ∩
        convexHull ℝ ↑(t.image (basisVertex N)) ⊆
      convexHull ℝ
        ((↑(s.image (basisVertex N)) : Set (EuclideanSpace ℝ (Fin N))) ∩
          ↑(t.image (basisVertex N))) := by
  classical
  let u := s ∪ t
  have hlin : LinearIndependent ℝ (basisVertex N) := by
    simpa [basisVertex] using
      (Pi.linearIndependent_single_one (Fin N) ℝ).map'
        (EuclideanSpace.equiv (Fin N) ℝ).symm.toLinearMap
        (LinearMap.ker_eq_bot.mpr
          (EuclideanSpace.equiv (Fin N) ℝ).symm.injective)
  have hu : AffineIndependent ℝ
      ((↑) : ↥(u.image (basisVertex N)) → EuclideanSpace ℝ (Fin N)) := by
    refine hlin.affineIndependent.range.mono ?_
    rintro x hx
    simp only [Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact ⟨i, rfl⟩
  rw [hu.convexHull_inter (t₁ := s.image (basisVertex N))
    (t₂ := t.image (basisVertex N))]
  · intro x hx
    simp only [Finset.mem_image] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, Finset.mem_union_left t hi, rfl⟩
  · intro x hx
    simp only [Finset.mem_image] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, Finset.mem_union_right s hi, rfl⟩

/-- Vertex sets lying in the basis image of one of the facets `F`. -/
def basisFaces (N : ℕ) (F : Finset (Finset (Fin N))) :
    Set (Finset (EuclideanSpace ℝ (Fin N))) :=
  {S | ∃ f ∈ F, S ⊆ f.image (basisVertex N)}

lemma basisFaces_eq_image {N : ℕ} {f : Finset (Fin N)}
    {S : Finset (EuclideanSpace ℝ (Fin N))} (hS : S ⊆ f.image (basisVertex N)) :
    (Finset.univ.filter fun i => basisVertex N i ∈ S).image (basisVertex N) = S := by
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (hS hx)
    exact ⟨i, hx, rfl⟩

/-- The geometric realization of the abstract complex generated by the facets
`F`, on the standard basis vertices of `ℝ^N`. -/
def basisComplex (N : ℕ) (F : Finset (Finset (Fin N))) :
    Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)) :=
  Geometry.SimplicialComplex.ofErase (basisFaces N F)
    (by
      rintro S ⟨f, -, hS⟩
      have h := rp2_explicit_finite_model_aux_basis_indep
        (Finset.univ.filter fun i => basisVertex N i ∈ S)
      rw [basisFaces_eq_image hS] at h
      exact h)
    (by
      rintro S T hTS ⟨f, hf, hS⟩
      exact ⟨f, hf, (show T ⊆ S from hTS).trans hS⟩)
    (by
      rintro S ⟨f, -, hS⟩ T ⟨g, -, hT⟩
      have h := rp2_explicit_finite_model_aux_basis_inter
        (Finset.univ.filter fun i => basisVertex N i ∈ S)
        (Finset.univ.filter fun i => basisVertex N i ∈ T)
      rw [basisFaces_eq_image hS, basisFaces_eq_image hT] at h
      exact h)

lemma basisComplex_faces_finite (N : ℕ) (F : Finset (Finset (Fin N))) :
    (basisComplex N F).faces.Finite := by
  classical
  have : basisFaces N F ⊆
      ↑((F.image fun f => f.image (basisVertex N)).biUnion Finset.powerset) := by
    rintro S ⟨f, hf, hS⟩
    simp only [Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Finset.mem_coe,
      Finset.mem_powerset, Set.mem_image, exists_prop]
    exact ⟨_, ⟨f, hf, rfl⟩, hS⟩
  exact ((Finset.finite_toSet _).subset this).subset Set.diff_subset

lemma basisComplex_vertex_mem {N : ℕ} {F : Finset (Finset (Fin N))} {f : Finset (Fin N)}
    (hf : f ∈ F) {i : Fin N} (hi : i ∈ f) :
    {basisVertex N i} ∈ (basisComplex N F).faces := by
  refine ⟨⟨f, hf, ?_⟩, ?_⟩
  · simpa using Finset.mem_image_of_mem (basisVertex N) hi
  · simp

/-! ### The 10-vertex model (plan in the blueprint, 2026-10-28)

Vertices `Fin 10`: `0` is the centre `O`, `ringIdx j = 1 + j % 6` is `m_j`, and
`bdryIdx j = 7 + j % 3` is the boundary label of the hexagon vertex `ζ_j`
(so `ζ_j` and `ζ_{j+3} = -ζ_j` share a label).  Facet `(i, 0)` is
`O m_i m_{i+1}`, `(i, 1)` is `B_i B_{i+1} m_i`, `(i, 2)` is `B_{i+1} m_i m_{i+1}`.
`checks/rp2_ten_vertex_check.py` and `checks/rp2_planar_tiling_check.py` (in
the lemma-packet notes) check the surface and the planar tiling. -/

/-- Hexagon vertex `ζ_j = exp(2πij/6)`. -/
def hexVertex (j : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / 6)

/-- Ring vertex `m_j`, two thirds of the way to the midpoint of `ζ_j ζ_{j+1}`. -/
def ringVertex (j : ℕ) : ℂ := (hexVertex j + hexVertex (j + 1)) / 3

/-- The closed hexagon. -/
def hexagon : Set ℂ := convexHull ℝ (Set.range fun j : Fin 6 => hexVertex j)

def ringIdx (j : ℕ) : Fin 10 := ⟨1 + j % 6, by omega⟩

def bdryIdx (j : ℕ) : Fin 10 := ⟨7 + j % 3, by omega⟩

def rp2Facet (p : Fin 6 × Fin 3) : Finset (Fin 10) :=
  if p.2.1 = 0 then {0, ringIdx p.1, ringIdx (p.1 + 1)}
  else if p.2.1 = 1 then {bdryIdx p.1, bdryIdx (p.1 + 1), ringIdx p.1}
  else {bdryIdx (p.1 + 1), ringIdx p.1, ringIdx (p.1 + 1)}

def rp2Facets : Finset (Finset (Fin 10)) := Finset.univ.image rp2Facet

def rp2Complex : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 10)) :=
  basisComplex 10 rp2Facets

/-- Planar position of vertex `k` in facet `p` (the value off the facet is
irrelevant). -/
def rp2Corner (p : Fin 6 × Fin 3) (k : Fin 10) : ℂ :=
  if k = 0 then 0
  else if k = ringIdx p.1 then ringVertex p.1
  else if k = ringIdx (p.1 + 1) then ringVertex (p.1 + 1)
  else if k = bdryIdx p.1 ∧ p.2.1 = 1 then hexVertex p.1
  else if k = bdryIdx (p.1 + 1) then hexVertex (p.1 + 1)
  else 0

/-- The affine map of facet `p` into the plane, in barycentric coordinates. -/
def rp2Affine (p : Fin 6 × Fin 3) (y : EuclideanSpace ℝ (Fin 10)) : ℂ :=
  ∑ k, (y k : ℂ) * rp2Corner p k

def facetHull (p : Fin 6 × Fin 3) : Set (EuclideanSpace ℝ (Fin 10)) :=
  convexHull ℝ ↑((rp2Facet p).image (basisVertex 10))

/-- Radial map from the hexagon onto the round disk: rescale by the hexagon
gauge. -/
def hexToDisk (z : ℂ) : ℂ := (gauge hexagon z / ‖z‖) • z

/-- Points outside the disk are sent to the centre; only used on the disk. -/
def diskClamp (w : ℂ) : Surfaces.Disk :=
  if h : ‖w‖ ≤ 1 then ⟨w, by simpa [Metric.mem_closedBall] using h⟩
  else ⟨0, by simp [Metric.mem_closedBall]⟩

/-- The characteristic map: on a facet containing `y`, go affinely to the
hexagon, radially to the disk, then to the quotient. -/
def rp2Map (y : rp2Complex.space) : RealProjectivePlane := by
  classical
  exact Surfaces.surfaceQuotient false 1 (diskClamp (hexToDisk (rp2Affine
    (if h : ∃ p, (y : EuclideanSpace ℝ (Fin 10)) ∈ facetHull p then Classical.choose h
      else (0, 0)) y)))

-- Stage 3: the radial map.
lemma rp2_explicit_finite_model_aux_hex_norm (z : ℂ) : ‖hexToDisk z‖ = gauge hexagon z := by
  by_cases hz : z = 0
  · simp [hz, hexToDisk]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    change ‖((gauge hexagon z / ‖z‖ : ℝ) : ℂ) * z‖ = gauge hexagon z
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (gauge_nonneg _) (norm_nonneg z))]
    exact div_mul_cancel₀ (gauge hexagon z) hn

lemma rp2_explicit_finite_model_aux_hex_continuous : Continuous hexToDisk := by
  sorry

lemma rp2_explicit_finite_model_aux_hex_neg (z : ℂ) : hexToDisk (-z) = -hexToDisk z := by
  sorry

lemma rp2_explicit_finite_model_aux_hex_injOn : Set.InjOn hexToDisk hexagon := by
  sorry

lemma rp2_explicit_finite_model_aux_hex_surj (w : ℂ) (hw : ‖w‖ ≤ 1) : ∃ z ∈ hexagon, hexToDisk z = w := by
  sorry

/-- `gauge hexagon z ≤ 1` exactly on the hexagon (closed, convex, `0` inside). -/
-- BEGIN SEAT AREA
lemma rp2_explicit_finite_model_aux_hex_gauge_le_one (z : ℂ) : gauge hexagon z ≤ 1 ↔ z ∈ hexagon := by
  sorry
-- END SEAT AREA

-- Stage 4: the facets.
lemma rp2_explicit_finite_model_aux_cover (y : EuclideanSpace ℝ (Fin 10)) (hy : y ∈ rp2Complex.space) :
    ∃ p, y ∈ facetHull p := by
  sorry

lemma rp2_explicit_finite_model_aux_affine_mem (p : Fin 6 × Fin 3) (y : EuclideanSpace ℝ (Fin 10))
    (hy : y ∈ facetHull p) : rp2Affine p y ∈ hexagon := by
  sorry

/-- Two facets containing `y` give the same point of `RP²`: their planar
positions agree, or (on a boundary edge) are antipodal boundary points. -/
lemma rp2_explicit_finite_model_aux_agree (p p' : Fin 6 × Fin 3) (y : EuclideanSpace ℝ (Fin 10))
    (hy : y ∈ facetHull p) (hy' : y ∈ facetHull p') :
    Surfaces.surfaceQuotient false 1 (diskClamp (hexToDisk (rp2Affine p y))) =
      Surfaces.surfaceQuotient false 1 (diskClamp (hexToDisk (rp2Affine p' y))) := by
  sorry

/-- Pasting over the 18 closed facet hulls (finite closed cover, `_agree`). -/
lemma rp2_explicit_finite_model_aux_continuous : Continuous rp2Map := by
  sorry

lemma rp2_explicit_finite_model_aux_injective : Function.Injective rp2Map := by
  sorry

lemma rp2_explicit_finite_model_aux_surjective : Function.Surjective rp2Map := by
  sorry

lemma rp2_explicit_finite_model_aux_centre_mem : basisVertex 10 0 ∈ rp2Complex.space := by
  sorry

lemma rp2_explicit_finite_model_aux_mark :
    rp2Map ⟨basisVertex 10 0, rp2_explicit_finite_model_aux_centre_mem⟩ = surfacePoint false 1 := by
  sorry

/-- **LIBRARY (explicit six-vertex model).** There is a finite coordinate realization of
the standard six-vertex, ten-triangle triangulation of `RP²`, together with a continuous
bijection to the disk quotient.  The distinguished vertex maps to the disk centre.

The combinatorial model has vertices `Fin 6`; its ten facets are the complementary pairs
in the standard minimal triangulation.  Realizing vertices by standard basis vectors makes
affine independence and the face-intersection axiom coordinate-support calculations. -/
theorem rp2_explicit_finite_model :
    ∃ (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
      (v : K.space) (f : K.space → RealProjectivePlane),
      K.faces.Finite ∧ {(v : EuclideanSpace ℝ (Fin n))} ∈ K.faces ∧
      Continuous f ∧ Function.Bijective f ∧
      f v = surfacePoint false 1 := by
  refine ⟨10, rp2Complex, ⟨basisVertex 10 0, rp2_explicit_finite_model_aux_centre_mem⟩, rp2Map,
    basisComplex_faces_finite 10 rp2Facets, ?_, rp2_explicit_finite_model_aux_continuous,
    ⟨rp2_explicit_finite_model_aux_injective, rp2_explicit_finite_model_aux_surjective⟩, rp2_explicit_finite_model_aux_mark⟩
  exact basisComplex_vertex_mem (f := rp2Facet (0, 0))
    (Finset.mem_image_of_mem _ (Finset.mem_univ _)) (by simp [rp2Facet])

/-- Upgrade the explicit continuous bijection to a marked finite vertex triangulation. -/
theorem realProjectivePlane_hasFiniteVertexTriangulation :
    HasFiniteVertexTriangulation RealProjectivePlane (surfacePoint false 1) := by
  obtain ⟨n, K, v, f, hfin, hv, hfcont, hfbij, hmark⟩ :=
    rp2_explicit_finite_model
  letI : CompactSpace K.space :=
    isCompact_iff_compactSpace.mp (finite_simplicialComplex_space_isCompact K hfin)
  letI : T2Space RealProjectivePlane := rp2_t2Space
  let e' : K.space ≃ₜ RealProjectivePlane :=
    hfcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hfbij)
  let e : RealProjectivePlane ≃ₜ K.space := e'.symm
  refine ⟨n, K, e, (v : EuclideanSpace ℝ (Fin n)), hfin, hv, ?_⟩
  have heq : e (surfacePoint false 1) = v := by
    apply e'.injective
    simpa [e, e'] using hmark.symm
  exact congrArg Subtype.val heq

#print axioms realProjectivePlane_hasFiniteVertexTriangulation

end ConstructionTargets.RealProjectivePlaneTriangulation
