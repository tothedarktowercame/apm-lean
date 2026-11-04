import Mathlib

/-!
# APM t02A08: geometric statement repair

The printed cycle `{p} × S²` has dimension two inside the three-manifold
`S¹ × S²`, so its intersection with a surface is not zero-dimensional and
has no integer-valued oriented intersection number.  We therefore use the
dimensionally forced repair `S¹ × {q}`.

All objects below are defined extrinsically in Euclidean space.  This is the
standard regular-level-set model of the spheres.  `apm_t02a08_Tangent` is the
kernel of the derivative of `x ↦ ‖x‖²`, hence is the usual tangent space.
`apm_t02a08_SmoothMap` says that the ambient map is smooth and maps the unit
2-sphere to `S¹ × S²`; its restriction is consequently the required smooth
map.  `apm_t02a08_Transverse` is the standard condition
`df(TₓS²) + T_{f(x)}Z = T_{f(x)}Y`, written as an explicit span equality.

The orientation convention is "outward normals first": a tangent frame of a
sphere is positive when prefixing its outward radial normal gives positive
ambient determinant.  The product `S¹ × S²` uses first the circle normal and
then the sphere normal.  The repaired cycle is oriented by the circle's
counterclockwise tangent.  Thus the local sign is the sign of the resulting
five-column determinant.  `apm_t02a08_Intersection` is the standard finite
sum of these local signs; it requires finiteness rather than using an infinite
`finsum` (which could silently produce zero).
-/

noncomputable section

abbrev apm_t02a08_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t02a08_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t02a08_E5 := EuclideanSpace ℝ (Fin 5)
abbrev apm_t02a08_S1 := Metric.sphere (0 : apm_t02a08_E2) 1
abbrev apm_t02a08_S2 := Metric.sphere (0 : apm_t02a08_E3) 1
abbrev apm_t02a08_Y := apm_t02a08_S1 × apm_t02a08_S2

def apm_t02a08_Z (q : apm_t02a08_S2) : Set apm_t02a08_Y :=
  {y | y.2 = q}

def apm_t02a08_Tangent {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
  LinearMap.ker (innerSL ℝ x).toLinearMap

def apm_t02a08_SmoothMap
    (F : apm_t02a08_E3 → apm_t02a08_E2 × apm_t02a08_E3) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) F ∧
    ∀ x : apm_t02a08_S2,
      F x.1 ∈ (Metric.sphere (0 : apm_t02a08_E2) 1) ×ˢ
        (Metric.sphere (0 : apm_t02a08_E3) 1)

def apm_t02a08_restrict
    (F : apm_t02a08_E3 → apm_t02a08_E2 × apm_t02a08_E3)
    (hF : apm_t02a08_SmoothMap F) : apm_t02a08_S2 → apm_t02a08_Y :=
  fun x ↦ ⟨⟨(F x.1).1, (hF.2 x).1⟩, ⟨(F x.1).2, (hF.2 x).2⟩⟩

def apm_t02a08_Preimage
    (F : apm_t02a08_E3 → apm_t02a08_E2 × apm_t02a08_E3)
    (q : apm_t02a08_S2) : Set apm_t02a08_S2 :=
  {x | (F x.1).2 = q.1}

def apm_t02a08_inE5 (a : apm_t02a08_E2) (b : apm_t02a08_E3) :
    apm_t02a08_E5 :=
  WithLp.toLp 2 ![a 0, a 1, b 0, b 1, b 2]

def apm_t02a08_ccw (p : apm_t02a08_E2) : apm_t02a08_E2 :=
  WithLp.toLp 2 ![-p 1, p 0]

def apm_t02a08_columns
    (v : Fin 5 → apm_t02a08_E5) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j ↦ v j i

def apm_t02a08_OrientedFrame (x u v : apm_t02a08_E3) : Prop :=
  u ∈ apm_t02a08_Tangent x ∧ v ∈ apm_t02a08_Tangent x ∧
  inner ℝ u u = 1 ∧ inner ℝ v v = 1 ∧ inner ℝ u v = 0 ∧
  Matrix.det (fun i j : Fin 3 ↦ ![x, u, v] j i) > 0

def apm_t02a08_frame (x : apm_t02a08_S2) :
    apm_t02a08_E3 × apm_t02a08_E3 := by
  classical
  exact if h : ∃ u v, apm_t02a08_OrientedFrame x.1 u v then
      (Classical.choose h, Classical.choose (Classical.choose_spec h))
    else (0, 0)

def apm_t02a08_localDet
    (F : apm_t02a08_E3 → apm_t02a08_E2 × apm_t02a08_E3)
    (q : apm_t02a08_S2) (x : apm_t02a08_S2) : ℝ :=
  let p := (F x.1).1
  let uv := apm_t02a08_frame x
  let dF := fderiv ℝ F x.1
  Matrix.det (apm_t02a08_columns ![
    apm_t02a08_inE5 p 0,
    apm_t02a08_inE5 0 q.1,
    apm_t02a08_inE5 (dF uv.1).1 (dF uv.1).2,
    apm_t02a08_inE5 (dF uv.2).1 (dF uv.2).2,
    apm_t02a08_inE5 (apm_t02a08_ccw p) 0])

def apm_t02a08_localSign
    (F : apm_t02a08_E3 → apm_t02a08_E2 × apm_t02a08_E3)
    (q : apm_t02a08_S2) (x : apm_t02a08_S2) : ℤ :=
  if 0 < apm_t02a08_localDet F q x then 1 else -1

def apm_t02a08_Transverse
    (F : apm_t02a08_E3 → apm_t02a08_E2 × apm_t02a08_E3)
    (q : apm_t02a08_S2) : Prop :=
  ∀ x : apm_t02a08_S2, x ∈ apm_t02a08_Preimage F q →
    Submodule.map
        ((ContinuousLinearMap.snd ℝ apm_t02a08_E2 apm_t02a08_E3).comp
          (fderiv ℝ F x.1)).toLinearMap (apm_t02a08_Tangent x.1) =
      apm_t02a08_Tangent q.1

def apm_t02a08_Intersection
    (F : apm_t02a08_E3 → apm_t02a08_E2 × apm_t02a08_E3)
    (q : apm_t02a08_S2) : ℤ := by
  classical
  exact if hfin : (apm_t02a08_Preimage F q).Finite then
    ∑ x ∈ hfin.toFinset, apm_t02a08_localSign F q x
  else 0

/-- The repaired cycle really is the whole circle over the single point `q`. -/
theorem apm_t02a08_Z_membership (q : apm_t02a08_S2) (y : apm_t02a08_Y) :
    y ∈ apm_t02a08_Z q ↔ y.2 = q := by
  rfl

/-- Sanity check: the standard inclusion `x ↦ (p,x)` meets the repaired cycle
in exactly one transverse point and has intersection number `-1` with the
orientation convention fixed above (normals-first orients Y opposite to the
product orientation of S¹ × S², a single global sign; see open5-grades.md). -/
theorem apm_t02a08_standard_inclusion_sanity
    (p : apm_t02a08_S1) (q : apm_t02a08_S2) :
    let F : apm_t02a08_E3 → apm_t02a08_E2 × apm_t02a08_E3 := fun x ↦ (p.1, x)
    apm_t02a08_SmoothMap F ∧
      apm_t02a08_Transverse F q ∧
      (apm_t02a08_Preimage F q).Finite ∧
      apm_t02a08_Intersection F q = -1 := by
  sorry

theorem apm_t02a08 :
    ∀ q : apm_t02a08_S2, ∀ n : ℤ,
      ∃ F : apm_t02a08_E3 → apm_t02a08_E2 × apm_t02a08_E3,
        apm_t02a08_SmoothMap F ∧
        apm_t02a08_Transverse F q ∧
        (apm_t02a08_Preimage F q).Finite ∧
        apm_t02a08_Intersection F q = n := by
  sorry
