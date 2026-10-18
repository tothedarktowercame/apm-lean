import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.PointWedgeExactEquality
import ConstructionTargets.SimplyConnectedOpenCover

/-! # APM t99A02: universal covers of two wedges

The problem asks for pictures of the universal covers of `RP² ∨ RP²` and
`S¹ ∨ RP²`.  The statement names each picture as a concrete quotient space and
asserts that it IS the universal cover: it is simply connected and admits a
surjective covering map onto the wedge.  (A simply connected covering space of
a connected, locally path-connected space is its universal cover.)

## Encoding

* `RP²` is the repository polygon model `Surface false 1` (disk with boundary
  word `aa`), wedged at the image of the disk centre (`surfacePoint false 1`);
  `S¹` is Mathlib's `Circle`, wedged at `1`.  These are the same models as
  `StatementSurfaceModels.ProjectivePlaneWedge`.  All quotients carry the
  coinduced (quotient) topology.
* `S²` is the unit sphere in `ℝ³`, with poles `north = e₂` and `south = -e₂`.
* `SphereChain` (picture for `RP² ∨ RP²`): copies `ℤ × S²`, the north pole of
  sphere `n` glued to the south pole of sphere `n + 1`: a bi-infinite chain of
  2-spheres, each touching the next at one point.
* `LineSphereTree` (picture for `S¹ ∨ RP²`): the Cayley-type complex of
  `G = ℤ * ℤ/2 = ⟨a⟩ * ⟨b | b²⟩`.  One vertex per `g ∈ G`; a unit edge from `g`
  to `g a` (so each coset `g⟨a⟩` forms a line covering the circle); for each
  coset `{g, g b}` one 2-sphere with `g` at its north pole and `g b` at its
  south pole (sphere copies `g` and `g b` are identified antipodally, so each
  coset contributes exactly one sphere).  The incidence pattern is the
  Bass--Serre tree of `ℤ * ℤ/2`: lines and spheres meeting at points in a tree.
-/

open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.StatementSurfaceModels

noncomputable section

namespace APMT99A02

/-- The round 2-sphere in `ℝ³`. -/
abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def north : S2 :=
  ⟨EuclideanSpace.single 2 1, by simp⟩

def south : S2 :=
  ⟨-EuclideanSpace.single 2 1, by simp⟩

/-- Gluing relation for the chain: north pole of sphere `n` to the south pole
of sphere `n + 1`. -/
inductive ChainRel : ℤ × S2 → ℤ × S2 → Prop
  | link (n : ℤ) : ChainRel (n, north) (n + 1, south)

/-- The bi-infinite chain of 2-spheres. -/
abbrev SphereChain := RelationQuotient ChainRel

/-- `ℤ * ℤ/2`, the fundamental group of `S¹ ∨ RP²`. -/
abbrev G := Monoid.Coprod (Multiplicative ℤ) (Multiplicative (ZMod 2))

/-- `G` indexes the cells, so it carries the discrete topology. -/
instance : TopologicalSpace G := ⊥

instance : DiscreteTopology G := ⟨rfl⟩

/-- The circle generator. -/
def a : G := Monoid.Coprod.inl (Multiplicative.ofAdd 1)

/-- The projective-plane generator, of order two. -/
def b : G := Monoid.Coprod.inr (Multiplicative.ofAdd 1)

/-- Gluing relation for the tree of lines and spheres. -/
inductive TreeRel : (G × unitInterval) ⊕ (G × S2) → (G × unitInterval) ⊕ (G × S2) → Prop
  /-- the edge at `g` ends where the edge at `g a` starts -/
  | edge (g : G) : TreeRel (.inl (g, 1)) (.inl (g * a, 0))
  /-- vertex `g` is the north pole of sphere copy `g` -/
  | vertex (g : G) : TreeRel (.inl (g, 0)) (.inr (g, north))
  /-- sphere copies `g` and `g b` are the same sphere, antipodally -/
  | pair (g : G) (x : S2) : TreeRel (.inr (g, x)) (.inr (g * b, -x))

/-- The tree of lines and spheres. -/
abbrev LineSphereTree := RelationQuotient TreeRel

/-- The wedge `S¹ ∨ RP²`. -/
abbrev CircleWedgeProjectivePlane := Wedge (1 : Circle) (surfacePoint false 1)

end APMT99A02

/-! # Blueprint

Route (details in `BLUEPRINT.md`):

* **RP² cover.**  `rp2Proj : S² → RP²` is written explicitly (orthogonal
  projection of the upper hemisphere onto the disk, the lower hemisphere
  through the antipode).  It factors through the antipodal quotient
  `S²/±` by a homeomorphism (leaf `rp2Proj_factor`); the antipodal quotient
  map is a covering (proof copied from the t00A02 blueprint).
* **Covers.**  Both covers are quotient maps by a deck group acting on the
  disjoint union upstairs (`D∞` on `ℤ × S²`, `G` on `(G × I) ⊕ (G × S²)`).
  The generic leaf `isCoveringMap_quotLift_of_deck` turns upstairs data
  (quotient map, fibres = orbits, saturated neighbourhoods with disjoint
  translates) into `IsCoveringMap` through Mathlib's `IsQuotientCoveringMap`.
* **Simple connectivity.**  Each total space is covered by contractible open
  "stars" whose nerve is a tree (`TreeCover`); generic leaves glue simply
  connected opens along path-connected overlaps and pass to directed unions.
  A star is the image of a saturated open set that contracts upstairs
  (generic leaf `isSimplyConnected_image_of_contraction`, explicit
  contraction `spherePush`).  For the tree, the Cayley graph of `ℤ * ℤ/2`
  being a tree is the normal form theorem (`G_normalForm`, `G_cayleyTree`).
-/

namespace APMT99A02

open Set Topology ConstructionTargets.Surfaces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. Sphere basics -/

lemma neg_north : -north = south := rfl

lemma neg_south : -south = north := by
  rw [← neg_north, neg_neg]

lemma north_ne_south : north ≠ south := by
  intro h
  have h2 := congrArg (fun x : S2 => (x : E3) 2) h
  simp [north, south] at h2
  norm_num at h2

/-- **Leaf (generic sphere fact).**  The sphere minus both poles is path
connected.  Route: stereographic projection from `north`
(`stereographic`, as in the proof of `simplyConnectedSpace_sphere_of_pole`
in `ConstructionTargets/SimplyConnectedOpenCover.lean`, whose `hoverlap`
step is exactly this statement) identifies it with the punctured plane
`(ℝ ∙ e₂)ᗮ \ {0}`, path connected by
`isPathConnected_compl_singleton_of_one_lt_rank`.  About 50 lines. -/
lemma sphere_compl_poles_isPathConnected :
    IsPathConnected {x : S2 | x ≠ north ∧ x ≠ south} := by
  let v : E3 := EuclideanSpace.single 2 1
  have hv : ‖v‖ = 1 := by simp [v]
  let eN := stereographic hv
  let eS := stereographic (show ‖-v‖ = 1 by simpa using hv)
  have hsouth : eN south = 0 := by
    simpa [north, south, v, eN] using stereographic_apply_neg north
  have hns : north ≠ south := north_ne_south
  have hrank : 1 < Module.rank ℝ (ℝ ∙ v)ᗮ := by
    rw [← Module.finrank_eq_rank]
    have hv0 : v ≠ 0 := by simp [v]
    letI : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
    rw [Submodule.finrank_orthogonal_span_singleton (n := 2) hv0]
    norm_num
  have hpunct : IsPathConnected ({0}ᶜ : Set (ℝ ∙ v)ᗮ) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  have himage := hpunct.image'
    (eN.symm.continuousOn.mono (by intro; simp [eN]))
  have hset : eN.symm '' ({0}ᶜ : Set (ℝ ∙ v)ᗮ) = eN.source ∩ eS.source := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨eN.symm.map_source (by simp [eN]), ?_⟩
      simp only [eS, stereographic_source, Set.mem_compl_iff,
        Set.mem_singleton_iff]
      intro h
      apply hy
      calc
        y = eN (eN.symm y) := (eN.right_inv (by simp [eN])).symm
        _ = eN south := congrArg eN h
        _ = 0 := hsouth
    · rintro ⟨hxN, hxS⟩
      refine ⟨eN x, ?_, eN.left_inv hxN⟩
      intro hz
      apply hxS
      have hsouthN : south ∈ eN.source := by
        simpa [eN, north, south, v] using hns.symm
      calc
        x = eN.symm (eN x) := (eN.left_inv hxN).symm
        _ = eN.symm 0 := congrArg eN.symm hz
        _ = eN.symm (eN south) := congrArg eN.symm hsouth.symm
        _ = south := eN.left_inv hsouthN
  rw [hset] at himage
  convert himage using 1

/-! ## 1. The antipodal cover in the polygon model of RP²

The relation, its classes and the covering proof are copied from
`holes/labs/blueprints/t00A02/Blueprint.lean`
(`apm_t00A02_antipodalCover_isCoveringMap` and its helpers, sorry-free). -/

/-- The antipodal identification on the sphere. -/
inductive AntipodalRel : S2 → S2 → Prop
  | antipodal (x : S2) : AntipodalRel x (-x)

/-- `S² / ±`, with the coinduced topology. -/
abbrev AntipodalQuotient := RelationQuotient AntipodalRel

/-- The antipodal quotient map. -/
def antipodalMk : S2 → AntipodalQuotient := fun x => Quotient.mk _ x

@[simp] lemma antipodalMk_neg (x : S2) : antipodalMk (-x) = antipodalMk x := by
  apply Quotient.sound
  exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (AntipodalRel.antipodal x))

lemma antipodal_eqvGen_iff (x y : S2) :
    Relation.EqvGen AntipodalRel x y ↔ y = x ∨ y = -x := by
  constructor
  · intro h
    induction h with
    | rel x y h => cases h; exact Or.inr rfl
    | refl => exact Or.inl rfl
    | symm x y _ ih => rcases ih with rfl | h <;> simp_all
    | trans x y z _ _ ih₁ ih₂ =>
        rcases ih₁ with rfl | h₁ <;> rcases ih₂ with rfl | h₂ <;> simp_all
  · rintro (rfl | rfl)
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ (AntipodalRel.antipodal x)

lemma antipodalMk_eq_iff (x y : S2) :
    antipodalMk x = antipodalMk y ↔ y = x ∨ y = -x := by
  unfold antipodalMk
  constructor
  · intro h
    exact (antipodal_eqvGen_iff x y).mp (Quotient.exact h)
  · intro h
    exact Quotient.sound ((antipodal_eqvGen_iff x y).mpr h)

lemma antipodalMk_surjective : Function.Surjective antipodalMk := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x => exact ⟨x, rfl⟩

/-- The antipodal `ZMod 2` action (copied from t00A02). -/
def antipodalVAdd (g : ZMod 2) (x : S2) : S2 := if g = 0 then x else -x

local instance : AddAction (ZMod 2) S2 where
  vadd := antipodalVAdd
  zero_vadd x := by
    change antipodalVAdd 0 x = x
    simp [antipodalVAdd]
  add_vadd g h x := by
    change antipodalVAdd (g + h) x = antipodalVAdd g (antipodalVAdd h x)
    fin_cases g <;> fin_cases h
    · change antipodalVAdd 0 x = antipodalVAdd 0 (antipodalVAdd 0 x)
      simp [antipodalVAdd]
    · change antipodalVAdd 1 x = antipodalVAdd 0 (antipodalVAdd 1 x)
      simp [antipodalVAdd, show (1 : ZMod 2) ≠ 0 by decide]
    · change antipodalVAdd 1 x = antipodalVAdd 1 (antipodalVAdd 0 x)
      simp [antipodalVAdd, show (1 : ZMod 2) ≠ 0 by decide]
    · change antipodalVAdd 0 x = antipodalVAdd 1 (antipodalVAdd 1 x)
      simp [antipodalVAdd, show (1 : ZMod 2) ≠ 0 by decide]

local instance : ContinuousConstVAdd (ZMod 2) S2 where
  continuous_const_vadd g := by
    fin_cases g
    · simpa [antipodalVAdd] using (continuous_id : Continuous (id : S2 → S2))
    · exact (continuous_neg.comp continuous_subtype_val).subtype_mk _

/-- The antipodal quotient map is a covering map (copied from t00A02,
`apm_t00A02_antipodalCover_isCoveringMap`). -/
theorem antipodalMk_isCoveringMap : IsCoveringMap antipodalMk := by
  have hfree : ∀ g : ZMod 2, ∀ x : S2, g +ᵥ x = x → g = 0 := by
    intro g x hg
    fin_cases g
    · rfl
    · exfalso
      have hx0 : (x : E3) ≠ 0 := by
        intro hx
        have hs := x.property
        simp [hx] at hs
      apply hx0
      have h' : -(x : E3) = x := by
        simpa [antipodalVAdd] using congrArg Subtype.val hg
      have htwo : (2 : ℝ) • (x : E3) = 0 := by
        rw [two_smul]
        simpa using (congrArg (fun z ↦ z + (x : E3)) h').symm
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hq : Topology.IsQuotientMap antipodalMk := isQuotientMap_quotient_mk'
  have horbit : ∀ {x y : S2},
      antipodalMk x = antipodalMk y ↔ x ∈ AddAction.orbit (ZMod 2) y := by
    intro x y
    rw [antipodalMk_eq_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨(1 : ZMod 2), by
          change antipodalVAdd (1 : ZMod 2) (-x) = x
          simp only [antipodalVAdd, if_neg (show (1 : ZMod 2) ≠ 0 by decide), neg_neg]⟩
    · rintro ⟨g, rfl⟩
      fin_cases g
      · left
        change y = antipodalVAdd (0 : ZMod 2) y
        norm_num [antipodalVAdd]
      · right
        change y = -antipodalVAdd (1 : ZMod 2) y
        norm_num [antipodalVAdd]
  letI : IsCancelVAdd (ZMod 2) S2 := isCancelVAdd_iff_eq_zero_of_vadd_eq.mpr hfree
  exact (hq.isAddQuotientCoveringMap_of_properlyDiscontinuousVAdd horbit).isCoveringMap _ _

/-- Horizontal coordinates `x₀ + i x₁` of a sphere point. -/
def planar (x : S2) : ℂ := ⟨(x : E3) 0, (x : E3) 1⟩

lemma norm_planar_le (x : S2) : ‖planar x‖ ≤ 1 := by
  have hx : ‖(x : E3)‖ = 1 := by simp
  have h2 : ‖(x : E3)‖ ^ 2 = (x : E3) 0 ^ 2 + (x : E3) 1 ^ 2 + (x : E3) 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
    simp [Real.norm_eq_abs, sq_abs]
  have hp : ‖planar x‖ ^ 2 = (x : E3) 0 ^ 2 + (x : E3) 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [planar]; ring
  nlinarith [sq_nonneg ((x : E3) 2), norm_nonneg (planar x)]

/-- The disk point of a sphere point: orthogonal projection of the closed upper
hemisphere, and of the antipode for the open lower hemisphere. -/
def diskOf (x : S2) : Disk :=
  ⟨if 0 ≤ (x : E3) 2 then planar x else -planar x, by
    rw [Metric.mem_closedBall, dist_zero_right]
    split_ifs
    · exact norm_planar_le x
    · rw [norm_neg]; exact norm_planar_le x⟩

/-- **The explicit antipodal double cover `S² → RP²`** in the polygon model
`Surface false 1` (disk with boundary word `aa`). -/
def rp2Proj (x : S2) : RealProjectivePlane := surfaceQuotient false 1 (diskOf x)

/-- **Leaf (generic RP² model).**  `rp2Proj` factors through the antipodal
quotient by a homeomorphism `S²/± ≃ₜ Surface false 1`.

Route.  Forward map: `Quotient.lift rp2Proj`, using `rp2Proj (-x) = rp2Proj x`
(for `x₂ ≠ 0` both sides are `surfaceQuotient (planar x)` up to sign
conventions; for `x₂ = 0` the two disk points `z, -z` lie on the unit circle
and `SurfaceRel false 1 z (-z)` holds with `edgePoint 2 0 t = exp(iπt)`,
`edgePoint 2 1 t = -exp(iπt)`).  Continuity: `rp2Proj` is continuous by the
pasting lemma on the closed hemispheres `{0 ≤ x₂}`, `{x₂ ≤ 0}` (they agree on
the equator after `surfaceQuotient`).  Inverse map: lift
`z ↦ antipodalMk ⟨(Re z, Im z, √(1 - ‖z‖²))⟩` along `surfaceQuotient`
(continuous; respects `SurfaceRel` because boundary `z ~ -z` lands on
antipodal equator points).  Both composites are the identity on
representatives (for `x₂ < 0` use `antipodalMk_neg`).  Do not prove
Hausdorffness; build the `Homeomorph` from the two lifts.  About 150 lines. -/
def rp2Proj_factor_aux_sphere (z : Disk) : S2 :=
  ⟨WithLp.toLp 2 ![z.1.re, z.1.im, Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2)], by
    have hz := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    have hnonneg : 0 ≤ 1 - ‖(z : ℂ)‖ ^ 2 := by nlinarith [norm_nonneg (z : ℂ)]
    rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [Real.sq_sqrt hnonneg]
    have he : z.1.re ^ 2 + z.1.im ^ 2 + (1 - ‖(z : ℂ)‖ ^ 2) = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [he, Real.sqrt_one]⟩

lemma rp2Proj_factor_aux_sphere_planar (z : Disk) :
    planar (rp2Proj_factor_aux_sphere z) = z := by
  apply Complex.ext <;> simp [rp2Proj_factor_aux_sphere, planar]

lemma rp2Proj_factor_aux_sphere_last (z : Disk) :
    ((rp2Proj_factor_aux_sphere z : S2) : E3) 2 =
      Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2) := by
  simp [rp2Proj_factor_aux_sphere]

lemma rp2Proj_factor_aux_sphere_continuous : Continuous rp2Proj_factor_aux_sphere := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact Complex.continuous_re.comp continuous_subtype_val
  · exact Complex.continuous_im.comp continuous_subtype_val
  · exact Real.continuous_sqrt.comp
      (continuous_const.sub ((continuous_norm.comp continuous_subtype_val).pow 2))

def rp2Proj_factor_aux_inv0 (z : Disk) : AntipodalQuotient :=
  antipodalMk (rp2Proj_factor_aux_sphere z)

lemma rp2Proj_factor_aux_inv0_continuous : Continuous rp2Proj_factor_aux_inv0 := by
  exact continuous_coinduced_rng.comp rp2Proj_factor_aux_sphere_continuous

/-- Leaf (split from `rp2Proj_factor`).  `rp2Proj` is continuous: pasting
lemma (`Continuous.if_le` / `continuous_if_le` on `0 ≤ x₂`) for `diskOf`,
the two branches `planar`, `-planar` being continuous and agreeing after
`surfaceQuotient` on the equator `x₂ = 0` (there `‖planar x‖ = 1` and
`SurfaceRel false 1 z (-z)`); then `continuous_surfaceQuotient`. -/
def rp2Proj_factor_aux_continuous_edgePointCircle
    (n e : ℕ) (t : Set.Icc (0 : ℝ) 1) : Circle :=
  ⟨edgePoint n e t, by
    rw [show ((edgePoint n e t : Disk) : ℂ) =
      Complex.exp (Complex.I * (2 * Real.pi * ((e : ℝ) + t.1) / n)) by rfl]
    simpa [Submonoid.unitSphere, Complex.norm_exp]⟩

lemma rp2Proj_factor_aux_continuous_edgePointCircle_eq (n e : ℕ)
    (t : Set.Icc (0 : ℝ) 1) :
    rp2Proj_factor_aux_continuous_edgePointCircle n e t =
      AddCircle.toCircle (((e : ℝ) + t.1 : AddCircle (n : ℝ))) := by
  apply Subtype.ext
  change Complex.exp _ = Complex.exp _
  congr 1
  push_cast
  field_simp

lemma rp2Proj_factor_aux_continuous_boundary (x : Disk)
    (hx : ‖(x : ℂ)‖ = 1) :
    ∃ (i : Fin 2) (t : Set.Icc (0 : ℝ) 1), edgePoint 2 i t = x := by
  letI : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
  let z : Circle := ⟨x.1, by simpa [Circle, Submonoid.unitSphere] using hx⟩
  let a : AddCircle (2 : ℝ) :=
    (AddCircle.homeomorphCircle (T := (2 : ℝ)) (by norm_num)).symm z
  let s := AddCircle.equivIco (2 : ℝ) 0 a
  have hs0 : 0 ≤ s.1 := s.2.1
  have hsn : s.1 < 2 := by simpa using s.2.2
  let e := ⌊s.1⌋₊
  have hen : e < 2 := (Nat.floor_lt hs0).2 hsn
  let t : Set.Icc (0 : ℝ) 1 :=
    ⟨s.1 - e, by
      constructor
      · exact sub_nonneg.mpr (Nat.floor_le hs0)
      · linarith [Nat.lt_floor_add_one s.1]⟩
  have hsa : (s.1 : AddCircle (2 : ℝ)) = a := by
    apply (AddCircle.equivIco (2 : ℝ) 0).injective
    rw [AddCircle.equivIco_coe_eq]
  have haz : AddCircle.toCircle a = z := by
    rw [← AddCircle.homeomorphCircle_apply]
    exact Homeomorph.apply_symm_apply _ z
  refine ⟨⟨e, hen⟩, t, ?_⟩
  apply Subtype.ext
  have hcircle : rp2Proj_factor_aux_continuous_edgePointCircle 2 e t = z := by
    rw [rp2Proj_factor_aux_continuous_edgePointCircle_eq]
    have het : (e : ℝ) + t.1 = s.1 := by dsimp [t]; ring
    have heq : (((e : ℝ) + t.1 : ℝ) : AddCircle (2 : ℝ)) =
        (s.1 : AddCircle (2 : ℝ)) := congrArg (fun r : ℝ => (r : AddCircle (2 : ℝ))) het
    have heq' : ((e : ℝ) : AddCircle (2 : ℝ)) +
        (t.1 : AddCircle (2 : ℝ)) = (s.1 : AddCircle (2 : ℝ)) := by simpa using heq
    exact (congrArg AddCircle.toCircle heq').trans (by rw [hsa]; exact haz)
  exact congrArg (fun w : Circle => (w : ℂ)) hcircle

lemma rp2Proj_factor_aux_continuous_edge_neg (t : Set.Icc (0 : ℝ) 1) :
    ((edgePoint 2 1 t : Disk) : ℂ) =
      -((edgePoint 2 0 t : Disk) : ℂ) := by
  simp only [edgePoint, Subtype.coe_mk]
  norm_num
  change Complex.exp (Complex.I * (2 * Real.pi * ((1 : ℂ) + t.1) / 2)) =
    -Complex.exp (Complex.I * (2 * Real.pi * t.1 / 2))
  calc
    _ = Complex.exp (Real.pi * Complex.I) *
        Complex.exp (Complex.I * (Real.pi * t.1)) := by rw [← Complex.exp_add]; congr 1 <;> ring
    _ = _ := by rw [Complex.exp_pi_mul_I]; ring

lemma rp2Proj_factor_aux_continuous_antipodal_boundary {x y : Disk}
    (hx : ‖(x : ℂ)‖ = 1) (hy : (y : ℂ) = -(x : ℂ)) :
    Relation.EqvGen (SurfaceRel false 1) x y := by
  obtain ⟨i, t, hi⟩ := rp2Proj_factor_aux_continuous_boundary x hx
  fin_cases i
  · have hy' : y = edgePoint 2 1 t := by
      apply Subtype.ext
      rw [hy, ← hi]
      exact (rp2Proj_factor_aux_continuous_edge_neg t).symm
    apply Relation.EqvGen.rel _ _
    simp only [SurfaceRel, Bool.false_eq_true, if_false]
    exact ⟨0, by omega, t, hi.symm, hy'⟩
  · have hy' : y = edgePoint 2 0 t := by
      apply Subtype.ext
      rw [hy, ← hi]
      rw [rp2Proj_factor_aux_continuous_edge_neg, neg_neg]
    apply Relation.EqvGen.symm _ _
    apply Relation.EqvGen.rel _ _
    simp only [SurfaceRel, Bool.false_eq_true, if_false]
    exact ⟨0, by omega, t, hy', hi.symm⟩

lemma rp2Proj_factor_aux_continuous : Continuous rp2Proj := by
  let f : S2 → RealProjectivePlane := fun x =>
    if 0 ≤ (x : E3) 2 then
      surfaceQuotient false 1 ⟨planar x, by
        simpa [Metric.mem_closedBall, dist_zero_right] using norm_planar_le x⟩
    else surfaceQuotient false 1 ⟨-planar x, by
      simpa [Metric.mem_closedBall, dist_zero_right] using norm_planar_le x⟩
  have hrf : rp2Proj = f := by
    funext x
    simp only [rp2Proj, diskOf, f]
    split_ifs <;> rfl
  rw [hrf]
  unfold f
  have hp : Continuous planar := by
    have h0 : Continuous (fun x : S2 => ((x : E3) 0 : ℂ)) :=
      Complex.continuous_ofReal.comp (by fun_prop)
    have h1 : Continuous (fun x : S2 => ((x : E3) 1 : ℂ)) :=
      Complex.continuous_ofReal.comp (by fun_prop)
    have h := h0.add ((continuous_const : Continuous (fun _ : S2 => Complex.I)).mul h1)
    convert h using 1
    funext x
    apply Complex.ext <;> simp [planar]
  apply Continuous.if_le
  · exact (continuous_surfaceQuotient false 1).comp
      (Continuous.subtype_mk hp _)
  · exact (continuous_surfaceQuotient false 1).comp
      (Continuous.subtype_mk hp.neg _)
  · exact continuous_const
  · fun_prop
  · intro x hx
    apply Quotient.sound
    apply rp2Proj_factor_aux_continuous_antipodal_boundary
    · have hs : ‖(x : E3)‖ ^ 2 = (x : E3) 0 ^ 2 + (x : E3) 1 ^ 2 + (x : E3) 2 ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
        simp [Real.norm_eq_abs, sq_abs]
      have hp : ‖planar x‖ ^ 2 = (x : E3) 0 ^ 2 + (x : E3) 1 ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp [planar]; ring
      have hsphere : ‖(x : E3)‖ = 1 := by simp
      have hnonneg := norm_nonneg (planar x)
      rw [hsphere] at hs
      rw [← hx] at hs
      norm_num at hs
      nlinarith
    · rfl

/-- Leaf (split from `rp2Proj_factor`).  `rp2Proj` is antipodally invariant:
for `x₂ ≠ 0` exactly one of `x, -x` is in the upper hemisphere and `diskOf`
gives the same disk point; for `x₂ = 0`, `diskOf x = planar x` and
`diskOf (-x) = -planar x` (as `0 ≤ -x₂`), boundary points identified by
`SurfaceRel false 1` (`edgePoint 2 0 t = exp(iπt)`, `edgePoint 2 1 t = -exp(iπt)`). -/
lemma rp2Proj_factor_aux_neg_boundary (z : Disk) (hz : ‖(z : ℂ)‖ = 1) :
    surfaceQuotient false 1 (-z) = surfaceQuotient false 1 z := by
  have relate (w : Disk) (hw : ‖(w : ℂ)‖ = 1) (him : 0 ≤ (w : ℂ).im) :
      SurfaceRel false 1 w (-w) := by
    let t : Set.Icc (0 : ℝ) 1 := ⟨Complex.arg (w : ℂ) / Real.pi, by
      constructor
      · exact div_nonneg (Complex.arg_nonneg_iff.mpr him) Real.pi_nonneg
      · exact (div_le_one Real.pi_pos).mpr (Complex.arg_le_pi _) ⟩
    refine ⟨0, by omega, t, ?_, ?_⟩
    · apply Subtype.ext
      simp only [edgePoint, t]
      norm_num
      rw [show Complex.I *
          (2 * Real.pi * (Complex.arg (w : ℂ) / Real.pi) / 2) =
          Complex.arg (w : ℂ) * Complex.I by
        push_cast
        field_simp [Real.pi_ne_zero]]
      simpa [hw] using (Complex.norm_mul_exp_arg_mul_I (w : ℂ)).symm
    · apply Subtype.ext
      simp only [edgePoint, t]
      change -(w : ℂ) = _
      norm_num
      rw [show Complex.I *
          (2 * Real.pi * (1 + Complex.arg (w : ℂ) / Real.pi) / 2) =
          Complex.arg (w : ℂ) * Complex.I + Real.pi * Complex.I by
        push_cast
        field_simp [Real.pi_ne_zero]
        ring]
      rw [Complex.exp_add, Complex.exp_pi_mul_I]
      simpa [hw] using congrArg Neg.neg
        (Complex.norm_mul_exp_arg_mul_I (w : ℂ)).symm
  apply Quotient.sound
  by_cases him : 0 ≤ (z : ℂ).im
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (relate z hz him))
  · have hn : 0 ≤ ((-z : Disk) : ℂ).im := by simp; exact le_of_not_ge him
    exact Relation.EqvGen.rel _ _ (by simpa only [neg_neg] using
      (relate (-z) (by simpa using hz) hn))

lemma rp2Proj_factor_aux_neg (x : S2) : rp2Proj (-x) = rp2Proj x := by
  by_cases h : ((x : S2) : E3) 2 = 0
  · change surfaceQuotient false 1 (diskOf (-x)) =
      surfaceQuotient false 1 (diskOf x)
    have hp : ‖planar x‖ = 1 := by
      have hx : ‖(x : E3)‖ = 1 := by simp
      have h2 : ‖(x : E3)‖ ^ 2 = (x : E3) 0 ^ 2 + (x : E3) 1 ^ 2 + (x : E3) 2 ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
        simp [Real.norm_eq_abs, sq_abs]
      have hp2 : ‖planar x‖ ^ 2 = (x : E3) 0 ^ 2 + (x : E3) 1 ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [planar]
        ring
      nlinarith [norm_nonneg (planar x)]
    have hs : planar (-x) = -planar x := by
      apply Complex.ext <;> simp [planar]
    simp only [diskOf]
    simp [h, hs]
    exact rp2Proj_factor_aux_neg_boundary
      (⟨planar x, by simpa [Metric.mem_closedBall, dist_zero_right] using norm_planar_le x⟩ : Disk) hp
  · change surfaceQuotient false 1 (diskOf (-x)) =
      surfaceQuotient false 1 (diskOf x)
    congr 1
    apply Subtype.ext
    have hp : planar (-x) = -planar x := by
      apply Complex.ext <;> simp [planar]
    simp only [diskOf, PiLp.neg_apply, hp]
    by_cases hx : 0 < ((x : S2) : E3) 2
    · rw [if_pos hx.le, if_neg]
      · simp
      · simpa using hx
    · have hx' : ((x : S2) : E3) 2 < 0 := lt_of_le_of_ne (le_of_not_gt hx) h
      simp [not_le_of_gt hx', hx'.le]

/-- Leaf (split from `rp2Proj_factor`).  The upper-hemisphere lift respects
the polygon gluing: generators of `SurfaceRel false 1` relate boundary points
`z, -z` (`‖z‖ = 1`), whose lifts `(Re z, Im z, 0)` and `(-Re z, -Im z, 0)` are
antipodal (`antipodalMk_neg`). -/
lemma rp2Proj_factor_aux_inv0_respects (a b : Disk) (h : SurfaceRel false 1 a b) :
    rp2Proj_factor_aux_inv0 a = rp2Proj_factor_aux_inv0 b := by
  simp only [SurfaceRel, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨j, hj, t, rfl, rfl⟩ := h
  interval_cases j
  rw [show rp2Proj_factor_aux_inv0 (edgePoint 2 1 t) =
      rp2Proj_factor_aux_inv0 (edgePoint 2 0 t) by
    unfold rp2Proj_factor_aux_inv0
    rw [← antipodalMk_neg]
    congr 1
    apply Subtype.ext
    ext i
    fin_cases i
    · simp [rp2Proj_factor_aux_sphere, edgePoint, Complex.exp_re]
      rw [show 2 * Real.pi * (1 + (t : ℝ)) / 2 =
        2 * Real.pi * (t : ℝ) / 2 + Real.pi by ring, Real.cos_add_pi]
      simp
    · simp [rp2Proj_factor_aux_sphere, edgePoint, Complex.exp_im]
      rw [show 2 * Real.pi * (1 + (t : ℝ)) / 2 =
        2 * Real.pi * (t : ℝ) / 2 + Real.pi by ring, Real.sin_add_pi]
      simp
    · simp [rp2Proj_factor_aux_sphere, edgePoint, Complex.norm_exp,
        Complex.mul_re]]

/-- Leaf (split from `rp2Proj_factor`).  `inv0 ∘ diskOf = antipodalMk`:
if `0 ≤ x₂` the lift of `planar x` is `x` (third coordinate
`√(1 - x₀² - x₁²) = x₂`); otherwise the lift of `-planar x` is `-x`
(`antipodalMk_neg`). -/
lemma rp2Proj_factor_aux_left (x : S2) :
    rp2Proj_factor_aux_inv0 (diskOf x) = antipodalMk x := by
  have hxnorm : ‖(x : E3)‖ = 1 := by simp
  have hcoord :
      1 - ‖planar x‖ ^ 2 = ((x : E3) 2) ^ 2 := by
    have hnormsq :
        ‖(x : E3)‖ ^ 2 =
          (x : E3) 0 ^ 2 + (x : E3) 1 ^ 2 + (x : E3) 2 ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
      simp [Real.norm_eq_abs, sq_abs]
    have hplanar :
        ‖planar x‖ ^ 2 = (x : E3) 0 ^ 2 + (x : E3) 1 ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [planar]
      ring
    rw [hxnorm, one_pow] at hnormsq
    rw [hplanar]
    linarith
  by_cases hx : 0 ≤ (x : E3) 2
  · have hsqrt : Real.sqrt (1 - ‖planar x‖ ^ 2) = (x : E3) 2 := by
      rw [hcoord, Real.sqrt_sq hx]
    unfold rp2Proj_factor_aux_inv0
    congr 1
    apply Subtype.ext
    ext i
    fin_cases i
    · simp [rp2Proj_factor_aux_sphere, diskOf, hx, planar]
    · simp [rp2Proj_factor_aux_sphere, diskOf, hx, planar]
    · simpa [rp2Proj_factor_aux_sphere, diskOf, hx] using hsqrt
  · have hxneg : (x : E3) 2 ≤ 0 := le_of_not_ge hx
    have hsqrt : Real.sqrt (1 - ‖planar x‖ ^ 2) = -(x : E3) 2 := by
      rw [hcoord, Real.sqrt_sq_eq_abs, abs_of_nonpos hxneg]
    rw [← antipodalMk_neg x]
    unfold rp2Proj_factor_aux_inv0
    congr 1
    apply Subtype.ext
    ext i
    fin_cases i
    · simp [rp2Proj_factor_aux_sphere, diskOf, hx, planar]
    · simp [rp2Proj_factor_aux_sphere, diskOf, hx, planar]
    · simpa [rp2Proj_factor_aux_sphere, diskOf, hx] using hsqrt

/-- Leaf (split from `rp2Proj_factor`).  `diskOf` of the upper-hemisphere
lift of `z` is `z` (third coordinate `√(…) ≥ 0`;
`rp2Proj_factor_aux_sphere_planar`). -/
lemma rp2Proj_factor_aux_right (z : Disk) :
    rp2Proj (rp2Proj_factor_aux_sphere z) = surfaceQuotient false 1 z := by
  simp [rp2Proj, diskOf, rp2Proj_factor_aux_sphere_last,
    Real.sqrt_nonneg, rp2Proj_factor_aux_sphere_planar]

lemma rp2Proj_factor_aux_eqvGen {α β : Type*} {R : α → α → Prop} (f : α → β)
    (hf : ∀ a b, R a b → f a = f b) (a b : α) (h : Relation.EqvGen R a b) :
    f a = f b := by
  induction h with
  | rel _ _ h => exact hf _ _ h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma rp2Proj_factor :
    ∃ h : AntipodalQuotient ≃ₜ RealProjectivePlane,
      ∀ x, h (antipodalMk x) = rp2Proj x := by
  let F : AntipodalQuotient → RealProjectivePlane :=
    Quotient.lift rp2Proj (rp2Proj_factor_aux_eqvGen rp2Proj (by
      rintro a b ⟨⟩; exact (rp2Proj_factor_aux_neg a).symm))
  let G : RealProjectivePlane → AntipodalQuotient :=
    Quotient.lift (s := Relation.EqvGen.setoid (SurfaceRel false 1))
      rp2Proj_factor_aux_inv0
      (rp2Proj_factor_aux_eqvGen _ rp2Proj_factor_aux_inv0_respects)
  have hGF : ∀ q, G (F q) = q := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => exact rp2Proj_factor_aux_left x
  have hFG : ∀ p, F (G p) = p := by
    intro p
    induction p using Quotient.inductionOn with
    | h z => exact rp2Proj_factor_aux_right z
  have hFc : Continuous F := continuous_coinduced_dom.mpr rp2Proj_factor_aux_continuous
  have hGc : Continuous G := continuous_coinduced_dom.mpr rp2Proj_factor_aux_inv0_continuous
  exact ⟨Homeomorph.mk ⟨F, G, hGF, hFG⟩ hFc hGc, fun x => rfl⟩

theorem rp2Proj_isCoveringMap : IsCoveringMap rp2Proj := by
  obtain ⟨h, hh⟩ := rp2Proj_factor
  have : rp2Proj = h ∘ antipodalMk := funext fun x => (hh x).symm
  rw [this]
  exact antipodalMk_isCoveringMap.homeomorph_comp h

lemma rp2Proj_eq_iff (x y : S2) : rp2Proj x = rp2Proj y ↔ y = x ∨ y = -x := by
  obtain ⟨h, hh⟩ := rp2Proj_factor
  rw [← hh, ← hh, h.injective.eq_iff, antipodalMk_eq_iff]

@[simp] lemma rp2Proj_neg (x : S2) : rp2Proj (-x) = rp2Proj x :=
  (rp2Proj_eq_iff x (-x)).mpr (Or.inr rfl) |>.symm

lemma rp2Proj_surjective : Function.Surjective rp2Proj := by
  obtain ⟨h, hh⟩ := rp2Proj_factor
  intro y
  obtain ⟨q, rfl⟩ := h.surjective y
  obtain ⟨x, rfl⟩ := antipodalMk_surjective q
  exact ⟨x, (hh x).symm⟩

lemma rp2Proj_north : rp2Proj north = surfacePoint false 1 := by
  unfold rp2Proj surfacePoint
  congr 1
  apply Subtype.ext
  simp [diskOf, planar, north]
  rfl

lemma rp2Proj_south : rp2Proj south = surfacePoint false 1 := by
  rw [← neg_north, rp2Proj_neg, rp2Proj_north]

lemma rp2Proj_eq_base_iff (x : S2) :
    rp2Proj x = surfacePoint false 1 ↔ x = north ∨ x = south := by
  rw [← rp2Proj_north, rp2Proj_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · right; rw [← neg_north, h, neg_neg]
  · rintro (h | h)
    · exact Or.inl h.symm
    · right; rw [h, neg_south]

/-! ## 2. Generic tools for relation quotients -/

section QuotientTools

variable {Z : Type*} [TopologicalSpace Z] (R : Z → Z → Prop)

/-- The quotient map onto `RelationQuotient R`. -/
abbrev qmk : Z → RelationQuotient R := Quotient.mk _

lemma continuous_qmk : Continuous (qmk R) := continuous_coinduced_rng

/-- A set is saturated if it is a union of generating-relation classes. -/
def Saturated (V : Set Z) : Prop := ∀ a b, R a b → (a ∈ V ↔ b ∈ V)

variable {R}

omit [TopologicalSpace Z] in
lemma Saturated.mem_iff {V : Set Z} (hV : Saturated R V) {a b : Z}
    (h : Relation.EqvGen R a b) : a ∈ V ↔ b ∈ V := by
  induction h with
  | rel a b hab => exact hV a b hab
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

omit [TopologicalSpace Z] in
lemma Saturated.preimage_image {V : Set Z} (hV : Saturated R V) :
    qmk R ⁻¹' (qmk R '' V) = V := by
  ext a
  constructor
  · rintro ⟨b, hb, hba⟩
    exact (hV.mem_iff (Quotient.exact hba)).mp hb
  · intro ha
    exact ⟨a, ha, rfl⟩

lemma Saturated.isOpen_image {V : Set Z} (hV : Saturated R V) (ho : IsOpen V) :
    IsOpen (qmk R '' V) := by
  change IsOpen (qmk R ⁻¹' (qmk R '' V))
  rw [hV.preimage_image]
  exact ho

omit [TopologicalSpace Z] in
lemma Saturated.image_inter {V W : Set Z} (hV : Saturated R V) :
    qmk R '' V ∩ qmk R '' W = qmk R '' (V ∩ W) := by
  ext q
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, ⟨w, hw, hwv⟩⟩
    exact ⟨w, ⟨(hV.mem_iff (Quotient.exact hwv)).mpr hv, hw⟩, hwv⟩
  · rintro ⟨w, ⟨hv, hw⟩, rfl⟩
    exact ⟨⟨w, hv, rfl⟩, ⟨w, hw, rfl⟩⟩

omit [TopologicalSpace Z] in
lemma eqvGen_respects {X : Type*} (F : Z → X) (hF : ∀ a b, R a b → F a = F b)
    {a b : Z} (h : Relation.EqvGen R a b) : F a = F b := by
  induction h with
  | rel a b hab => exact hF a b hab
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

variable (R)

/-- The map induced on the quotient by a relation-respecting map. -/
def quotLift {X : Type*} (F : Z → X) (hF : ∀ a b, R a b → F a = F b) :
    RelationQuotient R → X :=
  Quotient.lift F (fun _ _ h => eqvGen_respects F hF h)

omit [TopologicalSpace Z] in
@[simp] lemma quotLift_mk {X : Type*} (F : Z → X) (hF : ∀ a b, R a b → F a = F b)
    (z : Z) : quotLift R F hF (qmk R z) = F z := rfl

omit [TopologicalSpace Z] in
lemma quotLift_surjective {X : Type*} (F : Z → X) (hF : ∀ a b, R a b → F a = F b)
    (hs : Function.Surjective F) : Function.Surjective (quotLift R F hF) := by
  intro y
  obtain ⟨z, rfl⟩ := hs y
  exact ⟨qmk R z, rfl⟩

/-- **Leaf (generic: covering maps out of a relation quotient by a deck
group).**  Let a group `Γ` act on `Z` by homeomorphisms preserving `R`, and let
`F : Z → X` be a quotient map that respects `R`, is `Γ`-invariant, and whose
fibres are `Γ`-orbits modulo `R`.  If every point has an open saturated
neighbourhood `V` with `g • V ∩ V = ∅` for `g ≠ 1`, the induced map
`RelationQuotient R → X` is a covering map.

Route.  Put the induced `MulAction Γ (RelationQuotient R)` on the quotient
(`Quotient.map (g • ·)`, well defined by `hRΓ` and `EqvGen` induction);
`ContinuousConstSMul` via `continuous_coinduced_dom`.  Prove
`IsQuotientCoveringMap (quotLift R F hFR) Γ` field by field:
`IsQuotientMap.of_comp` (since `quotLift ∘ qmk = F`); orbit condition from
`hFΓ`/`hfib`; disjointness with `U = qmk '' V` (open by
`Saturated.isOpen_image`; `g • qmk v = qmk w` with `v, w ∈ V` gives
`g • v ∈ V` by `Saturated.mem_iff`).  Conclude with
`IsQuotientCoveringMap.isCoveringMap`.  About 120 lines. -/
lemma isCoveringMap_quotLift_of_deck {X Γ : Type*} [TopologicalSpace X] [Group Γ]
    [MulAction Γ Z] [ContinuousConstSMul Γ Z]
    (hRΓ : ∀ (g : Γ) (z w : Z), R z w → Relation.EqvGen R (g • z) (g • w))
    (F : Z → X) (hF : IsQuotientMap F) (hFR : ∀ a b, R a b → F a = F b)
    (hFΓ : ∀ (g : Γ) (z : Z), F (g • z) = F z)
    (hfib : ∀ z w : Z, F z = F w → ∃ g : Γ, Relation.EqvGen R (g • w) z)
    (hloc : ∀ z : Z, ∃ V : Set Z, IsOpen V ∧ z ∈ V ∧ Saturated R V ∧
      ∀ g : Γ, (∃ v ∈ V, g • v ∈ V) → g = 1) :
    IsCoveringMap (quotLift R F hFR) := by
  let act (g : Γ) : RelationQuotient R → RelationQuotient R :=
    Quotient.map (g • ·) (by
      intro z w hzw
      induction hzw with
      | rel z w h => exact hRΓ g z w h
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ =>
          exact Relation.EqvGen.trans _ _ _ ih₁ ih₂)
  letI : MulAction Γ (RelationQuotient R) := {
    smul := act
    one_smul q := by
      induction q using Quotient.inductionOn with
      | _ z =>
        apply Quotient.sound
        simp
    mul_smul g h q := by
      induction q using Quotient.inductionOn with
      | _ z =>
        apply Quotient.sound
        simp [mul_smul]
  }
  have hact (g : Γ) (z : Z) : g • qmk R z = qmk R (g • z) := rfl
  letI : ContinuousConstSMul Γ (RelationQuotient R) := {
    continuous_const_smul g := by
      rw [continuous_coinduced_dom]
      simpa only [Function.comp_apply, hact] using
        (continuous_qmk R).comp (continuous_const_smul g)
  }
  have hquot : IsQuotientMap (quotLift R F hFR) := by
    apply IsQuotientMap.of_comp (continuous_qmk R)
      (continuous_coinduced_dom.mpr (by simpa [Function.comp_def] using hF.continuous))
    simpa [Function.comp_def] using hF
  have hqc : IsQuotientCoveringMap (quotLift R F hFR) Γ := {
    hquot with
    continuous_const_smul := continuous_const_smul
    apply_eq_iff_mem_orbit := by
      intro q₁ q₂
      induction q₁ using Quotient.inductionOn with
      | _ z =>
        induction q₂ using Quotient.inductionOn with
        | _ w =>
          constructor
          · intro heq
            obtain ⟨g, hg⟩ := hfib z w heq
            exact ⟨g, Quotient.sound hg⟩
          · rintro ⟨g, hg⟩
            have heq : Relation.EqvGen R (g • w) z := Quotient.exact hg
            change F z = F w
            rw [← eqvGen_respects F hFR heq, hFΓ]
    disjoint := by
      intro q
      induction q using Quotient.inductionOn with
      | _ z =>
        obtain ⟨V, hVo, hzV, hVs, hV⟩ := hloc z
        refine ⟨qmk R '' V, (hVs.isOpen_image hVo).mem_nhds ⟨z, hzV, rfl⟩, ?_⟩
        intro g hg
        obtain ⟨q, ⟨qv, ⟨v, hvV, rfl⟩, hqv⟩, ⟨w, hwV, rfl⟩⟩ := hg
        apply hV g
        refine ⟨v, hvV, ?_⟩
        exact (hVs.mem_iff (Quotient.exact hqv)).mpr hwV
  }
  exact hqc.isCoveringMap

/-- **Leaf (generic: images of contractible saturated opens).**  If `V` is
open and saturated and an upstairs homotopy `H`, continuous on `I × V`,
keeps `V`, starts at the identity, respects the relation downstairs and ends
in one class, then `qmk '' V` is simply connected.

Route.  Let `W = qmk '' V` (open by `Saturated.isOpen_image`).  The
restriction `V → W` is a quotient map
(`IsQuotientMap.restrictPreimage_isOpen` with `Saturated.preimage_image`),
so `I × V → I × W` is one too (`IsQuotientMap.continuous_lift_prod_left`,
`unitInterval` is locally compact).  `hresp` extends from `R` to `EqvGen R`
by induction (all points stay in `V` by `Saturated.mem_iff`), so
`(t, qmk z) ↦ qmk (H (t, z))` descends to a homotopy `W × I → W` from the
identity to the constant `qmk z₀`.  Hence `ContractibleSpace W` and
`SimplyConnectedSpace W` (`SimplyConnectedSpace.ofContractible`).
About 130 lines. -/
lemma isSimplyConnected_image_of_contraction (V : Set Z) (hVo : IsOpen V)
    (hVs : Saturated R V) (H : unitInterval × Z → Z)
    (hH : ContinuousOn H (univ ×ˢ V))
    (hmaps : ∀ t, ∀ z ∈ V, H (t, z) ∈ V)
    (h0 : ∀ z ∈ V, H (0, z) = z)
    (z₀ : Z) (hz₀ : z₀ ∈ V) (h1 : ∀ z ∈ V, qmk R (H (1, z)) = qmk R z₀)
    (hresp : ∀ t, ∀ a b, a ∈ V → R a b → qmk R (H (t, a)) = qmk R (H (t, b))) :
    IsSimplyConnected (qmk R '' V) := by
  classical
  let W : Set (RelationQuotient R) := qmk R '' V
  let K0 : unitInterval × Z → RelationQuotient R := fun p =>
    if p.2 ∈ V then qmk R (H p) else qmk R p.2
  have hK0resp (t : unitInterval) (a b : Z) (hab : R a b) :
      K0 (t, a) = K0 (t, b) := by
    by_cases ha : a ∈ V
    · have hb : b ∈ V := (hVs a b hab).mp ha
      simpa only [K0, ha, hb, if_true] using hresp t a b ha hab
    · have hb : b ∉ V := by
        intro hb
        exact ha ((hVs a b hab).mpr hb)
      simpa only [K0, ha, hb, if_false] using
        (Quotient.sound (Relation.EqvGen.rel _ _ hab) : qmk R a = qmk R b)
  let K : unitInterval × W → W := fun p =>
    ⟨Quotient.lift (fun z => K0 (p.1, z))
        (fun a b hab => eqvGen_respects (fun z => K0 (p.1, z))
          (fun a b hab => hK0resp p.1 a b hab) hab) p.2.1,
      by
        rcases p.2.2 with ⟨z, hz, hzq⟩
        refine ⟨H (p.1, z), hmaps p.1 z hz, ?_⟩
        change qmk R (H (p.1, z)) = Quotient.lift _ _ p.2.1
        rw [← hzq]
        simp [K0, hz]⟩
  have hWo : IsOpen W := hVs.isOpen_image hVo
  have hq : IsQuotientMap (W.restrictPreimage (qmk R)) :=
    (isQuotientMap_quot_mk : IsQuotientMap (qmk R)).restrictPreimage_isOpen hWo
  have hKcont : Continuous K := by
    apply hq.continuous_lift_prod_right
    apply Continuous.subtype_mk
    change Continuous (fun p : unitInterval × (qmk R ⁻¹' W) =>
      Quotient.lift (fun z => K0 (p.1, z))
        (fun a b hab => eqvGen_respects (fun z => K0 (p.1, z))
          (fun a b hab => hK0resp p.1 a b hab) hab) (qmk R p.2.1))
    simp only [Quotient.lift_mk]
    have hsub : ∀ z : qmk R ⁻¹' W, z.1 ∈ V := by
      intro z
      exact (Set.ext_iff.mp hVs.preimage_image z.1).mp z.2
    have heq : (fun p : unitInterval × (qmk R ⁻¹' W) => K0 (p.1, p.2.1)) =
        fun p => qmk R (H (p.1, p.2.1)) := by
      funext p
      simp [K0, hsub p.2]
    rw [heq]
    exact (continuous_qmk R).comp
      (hH.comp_continuous
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
        (fun p => ⟨Set.mem_univ _, hsub p.2⟩))
  have hzero : ∀ w : W, K (0, w) = w := by
    intro w
    rcases w.2 with ⟨z, hz, hzw⟩
    have hw : w = (⟨qmk R z, ⟨z, hz, rfl⟩⟩ : W) := by
      apply Subtype.ext
      exact hzw.symm
    subst w
    apply Subtype.ext
    simp [K, K0, hz, h0 z hz]
  have hone : ∀ w : W, K (1, w) = (⟨qmk R z₀, ⟨z₀, hz₀, rfl⟩⟩ : W) := by
    intro w
    rcases w.2 with ⟨z, hz, hzw⟩
    have hw : w = (⟨qmk R z, ⟨z, hz, rfl⟩⟩ : W) := by
      apply Subtype.ext
      exact hzw.symm
    subst w
    apply Subtype.ext
    simpa [K, K0, hz] using h1 z hz
  have hnull : (ContinuousMap.id W).Nullhomotopic := by
    refine ⟨⟨qmk R z₀, ⟨z₀, hz₀, rfl⟩⟩, ?_⟩
    exact ⟨⟨K, hKcont⟩, hzero, hone⟩
  letI : ContractibleSpace W := (contractible_iff_id_nullhomotopic W).2 hnull
  exact (inferInstance : SimplyConnectedSpace W)

end QuotientTools

/-! ## 3. Generic gluing of simply connected open sets -/

section SimplyConnectedGluing

variable {X : Type*} [TopologicalSpace X]

/-- **Leaf (generic, ambient two-set van Kampen).**  Two open simply connected
sets with path-connected (nonempty) overlap have simply connected union.

Route.  Work in the subtype `↥(U ∪ V)` with the open sets
`Subtype.val ⁻¹' U`, `Subtype.val ⁻¹' V`; these are homeomorphic to `U`, `V`
(`Homeomorph.Set` / `IsEmbedding.isSimplyConnected_image`), the overlap is the
homeomorphic preimage of `U ∩ V`; apply `simplyConnectedSpace_of_union_eq_univ`
from `ConstructionTargets/SimplyConnectedOpenCover.lean`.  About 70 lines. -/
lemma isSimplyConnected_union {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUs : IsSimplyConnected U) (hVs : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) : IsSimplyConnected (U ∪ V) := by
  let A : Set ↥(U ∪ V) := Subtype.val ⁻¹' U
  let B : Set ↥(U ∪ V) := Subtype.val ⁻¹' V
  have hAopen : IsOpen A := hU.preimage continuous_subtype_val
  have hBopen : IsOpen B := hV.preimage continuous_subtype_val
  have hAs : IsSimplyConnected A := by
    rw [← IsEmbedding.subtypeVal.isSimplyConnected_image,
      Subtype.image_preimage_val, inter_eq_right.2 subset_union_left]
    exact hUs
  have hBs : IsSimplyConnected B := by
    rw [← IsEmbedding.subtypeVal.isSimplyConnected_image,
      Subtype.image_preimage_val, inter_eq_right.2 subset_union_right]
    exact hVs
  have hAB : IsPathConnected (A ∩ B) := by
    have hpre : IsPathConnected (Subtype.val ⁻¹' (U ∩ V) : Set ↥(U ∪ V)) :=
      hUV.preimage_coe (by intro x hx; exact Or.inl hx.1)
    simpa [A, B, preimage_inter] using hpre
  have hcover : A ∪ B = (Set.univ : Set ↥(U ∪ V)) := by
    ext x
    simp only [A, B, mem_union, mem_preimage, mem_univ, iff_true]
    exact x.2
  exact simplyConnectedSpace_of_union_eq_univ hAopen hBopen hcover hAs hBs hAB

/-- **Leaf (generic, directed unions).**  A directed union of open simply
connected sets is simply connected.

Route.  `isSimplyConnected_iff_exists_homotopy_refl_forall_mem`.  Path
connectivity: two points lie in a common member by directedness.  Loops: the
range of a loop is compact (`isCompact_range`), covered by the open members,
so by a finite subcover and directedness it lies in one member `U k`; the
null-homotopy in `U k` stays in the union.  About 80 lines. -/
lemma isSimplyConnected_iUnion_of_directed {ι : Type*} [Nonempty ι]
    (U : ι → Set X) (hdir : Directed (· ⊆ ·) U) (hU : ∀ i, IsOpen (U i))
    (hUs : ∀ i, IsSimplyConnected (U i)) : IsSimplyConnected (⋃ i, U i) := by
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem]
  constructor
  · rw [isPathConnected_iff]
    constructor
    · let i : ι := Classical.choice ‹Nonempty ι›
      obtain ⟨x, hx⟩ := (hUs i).nonempty
      exact ⟨x, Set.mem_iUnion.2 ⟨i, hx⟩⟩
    · intro x hx y hy
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
      obtain ⟨j, hyj⟩ := Set.mem_iUnion.1 hy
      obtain ⟨k, hik, hjk⟩ := hdir i j
      obtain ⟨p, hp⟩ := (hUs k).isPathConnected.joinedIn x (hik hxi) y (hjk hyj)
      exact ⟨p, fun t => Set.mem_iUnion.2 ⟨k, hp t⟩⟩
  · intro x p hp
    have hrange : Set.range p ⊆ ⋃ i, U i := by
      rintro _ ⟨t, rfl⟩
      exact hp t
    obtain ⟨s, hs⟩ := (isCompact_range p.continuous).elim_finite_subcover U hU hrange
    obtain ⟨k, hk⟩ := hdir.finset_le s
    have hpk : ∀ t, p t ∈ U k := by
      intro t
      have hpt : p t ∈ ⋃ i ∈ s, U i := hs ⟨t, rfl⟩
      simp only [Set.mem_iUnion] at hpt
      obtain ⟨i, hi, hpti⟩ := hpt
      exact hk i hi hpti
    obtain ⟨F, hF⟩ :=
      (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp (hUs k)).2 x p hpk
    exact ⟨F, fun t => Set.mem_iUnion.2 ⟨k, hF t⟩⟩

/-- **Leaf (generic, attaching a disjoint family).**  Attaching to `U` a
pairwise disjoint family of open simply connected sets, each meeting `U` in a
path-connected set, keeps simple connectivity.

Route.  For a finset `s`, `U ∪ ⋃ j ∈ s, V j` is simply connected by
`Finset.induction` and `isSimplyConnected_union` (for `k ∉ s`, the overlap
`(U ∪ ⋃ j ∈ s, V j) ∩ V k = U ∩ V k` by disjointness).  These sets are open
and directed by inclusion, with union `U ∪ ⋃ j, V j`; apply
`isSimplyConnected_iUnion_of_directed`.  About 80 lines. -/
lemma isSimplyConnected_union_iUnion_of_pairwiseDisjoint {J : Type*} {U : Set X}
    (V : J → Set X) (hU : IsOpen U) (hV : ∀ j, IsOpen (V j))
    (hUs : IsSimplyConnected U) (hVs : ∀ j, IsSimplyConnected (V j))
    (hdisj : Pairwise fun i j => Disjoint (V i) (V j))
    (hUV : ∀ j, IsPathConnected (U ∩ V j)) :
    IsSimplyConnected (U ∪ ⋃ j, V j) := by
  classical
  let W : Finset J → Set X := fun s => U ∪ ⋃ j ∈ s, V j
  have hWopen : ∀ s, IsOpen (W s) := by
    intro s
    exact hU.union (isOpen_iUnion fun j => isOpen_iUnion fun (_ : j ∈ s) => hV j)
  have hWsimple : ∀ s, IsSimplyConnected (W s) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa [W] using hUs
    | @insert k s hks ih =>
        have hinter : W s ∩ V k = U ∩ V k := by
          apply Set.Subset.antisymm
          · rintro x ⟨hx, hxk⟩
            rcases hx with hxU | hxV
            · exact ⟨hxU, hxk⟩
            · simp only [Set.mem_iUnion] at hxV
              obtain ⟨j, hj, hxj⟩ := hxV
              have hjk : j ≠ k := by
                intro h
                subst j
                exact hks hj
              exact False.elim (Set.disjoint_left.1 (hdisj hjk) hxj hxk)
          · rintro x ⟨hxU, hxk⟩
            exact ⟨Or.inl hxU, hxk⟩
        have hunion : W (insert k s) = W s ∪ V k := by
          ext x
          simp [W, or_assoc, or_left_comm, or_comm]
        rw [hunion]
        exact isSimplyConnected_union (hWopen s) (hV k) ih (hVs k)
          (hinter ▸ hUV k)
  have hWdir : Directed (· ⊆ ·) W := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · intro x hx
      rcases hx with hxU | hxV
      · exact Or.inl hxU
      · right
        simp only [Set.mem_iUnion] at hxV ⊢
        obtain ⟨j, hj, hxj⟩ := hxV
        exact ⟨j, Finset.mem_union_left t hj, hxj⟩
    · intro x hx
      rcases hx with hxU | hxV
      · exact Or.inl hxU
      · right
        simp only [Set.mem_iUnion] at hxV ⊢
        obtain ⟨j, hj, hxj⟩ := hxV
        exact ⟨j, Finset.mem_union_right s hj, hxj⟩
  have hfinal := isSimplyConnected_iUnion_of_directed W hWdir hWopen hWsimple
  have hUnion : (⋃ s, W s) = U ∪ ⋃ j, V j := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hx⟩ := Set.mem_iUnion.1 hx
      rcases hx with hxU | hxV
      · exact Or.inl hxU
      · right
        simp only [Set.mem_iUnion] at hxV ⊢
        obtain ⟨j, _, hxj⟩ := hxV
        exact ⟨j, hxj⟩
    · rintro (hxU | hxV)
      · exact Set.mem_iUnion.2 ⟨∅, Or.inl hxU⟩
      · obtain ⟨j, hxj⟩ := Set.mem_iUnion.1 hxV
        refine Set.mem_iUnion.2 ⟨{j}, Or.inr ?_⟩
        simp only [Set.mem_iUnion]
        exact ⟨j, by simp, hxj⟩
  rwa [hUnion] at hfinal

/-- An open cover by simply connected sets whose intersection pattern is a
rooted tree: each non-root member meets its parent in a path-connected set,
and two distinct members meet only if one is the parent of the other. -/
structure TreeCover (X : Type*) [TopologicalSpace X] (ι : Type*) where
  U : ι → Set X
  depth : ι → ℕ
  parent : ι → ι
  root : ι
  isOpen : ∀ i, IsOpen (U i)
  simplyConnected : ∀ i, IsSimplyConnected (U i)
  cover : ⋃ i, U i = univ
  depth_eq_zero : ∀ i, depth i = 0 ↔ i = root
  depth_parent : ∀ i, i ≠ root → depth (parent i) + 1 = depth i
  inter_parent : ∀ i, i ≠ root → IsPathConnected (U i ∩ U (parent i))
  inter_adj : ∀ i j, i ≠ j → (U i ∩ U j).Nonempty →
    (i ≠ root ∧ j = parent i) ∨ (j ≠ root ∧ i = parent j)

/-- **Leaf (generic, trees of simply connected opens).**  A space with a
`TreeCover` is simply connected.

Route.  `O k := ⋃ i, ⋃ (_ : T.depth i ≤ k), T.U i`.  `O 0 = U root`.
`O (k+1) = O k ∪ ⋃ (i : {i // depth i = k+1}), U i`: the new members are
pairwise disjoint (by `inter_adj`, meeting members have depths differing by
one) and `O k ∩ U i = U i ∩ U (parent i)` (a member of depth `≤ k` meeting
`U i` must be `parent i`); apply
`isSimplyConnected_union_iUnion_of_pairwiseDisjoint`.  Then
`isSimplyConnected_iUnion_of_directed` over `k : ℕ` (monotone), the union is
`univ` by `cover`, and `IsSimplyConnected univ` gives `SimplyConnectedSpace X`
(`Homeomorph.Set.univ`).  About 110 lines. -/
lemma TreeCover.simplyConnectedSpace {ι : Type*} (T : TreeCover X ι) :
    SimplyConnectedSpace X := by
  classical
  let O : ℕ → Set X := fun k => ⋃ i, ⋃ (_ : T.depth i ≤ k), T.U i
  have hOopen : ∀ k, IsOpen (O k) := by
    intro k
    exact isOpen_iUnion fun i => isOpen_iUnion fun _ => T.isOpen i
  have hOzero : O 0 = T.U T.root := by
    apply Set.Subset.antisymm
    · intro x hx
      simp only [O, Set.mem_iUnion] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      have hd : T.depth i = 0 := Nat.eq_zero_of_le_zero hi
      simpa [(T.depth_eq_zero i).mp hd] using hxi
    · intro x hx
      simp only [O, Set.mem_iUnion]
      exact ⟨T.root, (T.depth_eq_zero T.root).mpr rfl ▸ le_rfl, hx⟩
  have hOsimple : ∀ k, IsSimplyConnected (O k) := by
    intro k
    induction k with
    | zero => simpa [hOzero] using T.simplyConnected T.root
    | succ k ih =>
      let J := {i : ι // T.depth i = k + 1}
      let V : J → Set X := fun i => T.U i.1
      have hroot (i : J) : i.1 ≠ T.root := by
        intro hir
        have : k + 1 = 0 := by
          rw [← i.2, hir]
          exact (T.depth_eq_zero T.root).mpr rfl
        omega
      have hdisj : Pairwise fun i j : J => Disjoint (V i) (V j) := by
        intro i j hij
        rw [Set.disjoint_left]
        intro x hxi hxj
        have hij' : i.1 ≠ j.1 := by
          intro h
          apply hij
          exact Subtype.ext h
        rcases T.inter_adj i.1 j.1 hij' ⟨x, hxi, hxj⟩ with h | h
        · have hd := T.depth_parent i.1 (hroot i)
          rw [← h.2, i.2, j.2] at hd
          omega
        · have hd := T.depth_parent j.1 (hroot j)
          rw [← h.2, i.2, j.2] at hd
          omega
      have hinter (i : J) : O k ∩ V i = T.U i.1 ∩ T.U (T.parent i.1) := by
        apply Set.Subset.antisymm
        · rintro x ⟨hxO, hxi⟩
          simp only [O, Set.mem_iUnion] at hxO
          obtain ⟨j, hj, hxj⟩ := hxO
          by_cases hji : j = i.1
          · subst j
            rw [i.2] at hj
            omega
          · rcases T.inter_adj j i.1 hji ⟨x, hxj, hxi⟩ with h | h
            · have hd := T.depth_parent j h.1
              rw [← h.2, i.2] at hd
              omega
            · exact ⟨hxi, h.2 ▸ hxj⟩
        · rintro x ⟨hxi, hp⟩
          constructor
          · simp only [O, Set.mem_iUnion]
            refine ⟨T.parent i.1, ?_, hp⟩
            have hd := T.depth_parent i.1 (hroot i)
            rw [i.2] at hd
            omega
          · exact hxi
      have hstep : O (k + 1) = O k ∪ ⋃ i : J, V i := by
        ext x
        simp only [O, V, J, Set.mem_iUnion, Set.mem_union]
        constructor
        · rintro ⟨i, hi, hxi⟩
          rcases Nat.lt_or_eq_of_le hi with hi | hi
          · exact Or.inl ⟨i, Nat.le_of_lt_succ hi, hxi⟩
          · exact Or.inr ⟨⟨i, hi⟩, hxi⟩
        · rintro (⟨i, hi, hxi⟩ | ⟨i, hxi⟩)
          · exact ⟨i, Nat.le_trans hi (Nat.le_succ k), hxi⟩
          · exact ⟨i.1, i.2.le, hxi⟩
      rw [hstep]
      refine isSimplyConnected_union_iUnion_of_pairwiseDisjoint V (hOopen k)
        (fun i => T.isOpen i.1) ih (fun i => T.simplyConnected i.1) hdisj ?_
      intro i
      rw [hinter i]
      exact T.inter_parent i.1 (hroot i)
  have hdir : Directed (· ⊆ ·) O := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩ <;> intro x hx <;>
      simp only [O, Set.mem_iUnion] at hx ⊢
    · obtain ⟨a, ha, hxa⟩ := hx
      exact ⟨a, ha.trans (Nat.le_max_left _ _), hxa⟩
    · obtain ⟨a, ha, hxa⟩ := hx
      exact ⟨a, ha.trans (Nat.le_max_right _ _), hxa⟩
  have hall : (⋃ k, O k) = (Set.univ : Set X) := by
    rw [← T.cover]
    ext x
    simp only [O, Set.mem_iUnion]
    constructor
    · rintro ⟨k, i, _, hxi⟩
      exact ⟨i, hxi⟩
    · rintro ⟨i, hxi⟩
      exact ⟨T.depth i, i, le_rfl, hxi⟩
  have huniv : IsSimplyConnected (Set.univ : Set X) := by
    rw [← hall]
    exact isSimplyConnected_iUnion_of_directed O hdir hOopen hOsimple
  exact (Homeomorph.Set.univ X).toHomotopyEquiv.simplyConnectedSpace_iff.mp huniv

end SimplyConnectedGluing

/-! ## 4. Pushing sphere points toward a pole -/

/-- Normalised straight-line push of `x` toward `p`; well defined (nonzero
vector) unless `t = 1/2` and `x = -p`, where it returns `x`. -/
def spherePush (p : S2) (q : unitInterval × S2) : S2 :=
  if h : (1 - (q.1 : ℝ)) • (q.2 : E3) + (q.1 : ℝ) • (p : E3) = 0 then q.2
  else ⟨‖(1 - (q.1 : ℝ)) • (q.2 : E3) + (q.1 : ℝ) • (p : E3)‖⁻¹ •
      ((1 - (q.1 : ℝ)) • (q.2 : E3) + (q.1 : ℝ) • (p : E3)), by
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm h⟩

/-- **Leaf (generic sphere push, continuity).**  `spherePush p` is continuous
on `I × (S² \ {-p})`.

Route.  The vector `v = (1-t)x + tp` vanishes only for `t = 1/2, x = -p`
(else `x = -(t/(1-t)) p` with norm one forces `t = 1/2`); on the given set the
`dite` is the `else` branch, and `v ↦ ‖v‖⁻¹ • v` is continuous on `{v ≠ 0}`
(`ContinuousOn.smul`, `continuousOn_inv₀`, `continuous_norm`).
About 50 lines. -/
lemma spherePush_continuousOn_aux_ne_zero (p : S2)
    (q : unitInterval × S2) (hq : q ∈ (univ ×ˢ {x | x ≠ -p})) :
    (1 - (q.1 : ℝ)) • (q.2 : E3) + (q.1 : ℝ) • (p : E3) ≠ 0 := by
  intro hzero
  have hp : ‖(p : E3)‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using p.property
  have hx : ‖(q.2 : E3)‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using q.2.property
  have ht0 : 0 ≤ (q.1 : ℝ) := q.1.property.1
  have ht1 : (q.1 : ℝ) ≤ 1 := q.1.property.2
  simp only [add_eq_zero_iff_eq_neg] at hzero
  have heq : (q.1 : ℝ) = 1 / 2 := by
    have habs : |1 - (q.1 : ℝ)| = |(q.1 : ℝ)| := by
      have := congrArg norm hzero
      simpa [norm_smul, hx, hp] using this
    rw [abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0] at habs
    linarith
  have : q.2 = -p := by
    apply Subtype.ext
    have := hzero
    rw [heq] at this
    have htwice := congrArg (fun z : E3 ↦ (2 : ℝ) • z) this
    convert htwice using 1 <;> norm_num [smul_smul]
  exact hq.2 this

lemma spherePush_continuousOn (p : S2) :
    ContinuousOn (spherePush p) (univ ×ˢ {x | x ≠ -p}) := by
  let v : unitInterval × S2 → E3 := fun q ↦
    (1 - (q.1 : ℝ)) • (q.2 : E3) + (q.1 : ℝ) • (p : E3)
  have hv : Continuous v := by
    fun_prop
  have hne (q : unitInterval × S2) (hq : q ∈ univ ×ˢ {x | x ≠ -p}) : v q ≠ 0 := by
    exact spherePush_continuousOn_aux_ne_zero p q hq
  have hscalar : ContinuousOn (fun q ↦ ‖v q‖⁻¹)
      (univ ×ˢ {x : S2 | x ≠ -p}) := by
    intro q hq
    exact (hv.continuousAt.norm.inv₀ (by simpa using hne q hq)).continuousWithinAt
  have hval : ContinuousOn (fun q ↦ (spherePush p q : E3))
      (univ ×ˢ {x : S2 | x ≠ -p}) := by
    apply (hscalar.smul hv.continuousOn).congr
    intro q hq
    simp only [spherePush, v, dif_neg (hne q hq)]
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_induced_rng.mpr
  exact continuousOn_iff_continuous_restrict.mp hval

/-- **Leaf (generic sphere push, identities).**

Route.  Unfold `spherePush`; each item is a computation with
`v = (1-t)x + tp`: at `t = 0`, `v = x` has norm one; at `t = 1`, `v = p`;
for `x = p`, `v = p`; if the normalised `v` were `-p` then
`(1-t)x = -(c+t)p` with `c > 0`, forcing `x = -p`; for `(-p, -x)` the vector
is `-v`.  About 90 lines. -/
lemma spherePush_spec (p : S2) :
    (∀ x, spherePush p (0, x) = x) ∧
    (∀ x, x ≠ -p → spherePush p (1, x) = p) ∧
    (∀ t, spherePush p (t, p) = p) ∧
    (∀ t x, x ≠ -p → spherePush p (t, x) ≠ -p) ∧
    (∀ t x, spherePush (-p) (t, -x) = -spherePush p (t, x)) := by
  have hnorm (x : S2) : ‖(x : E3)‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using x.property
  constructor
  · intro x
    simp [spherePush, hnorm]
  constructor
  · intro x hx
    have hp0 : (p : E3) ≠ 0 := by
      intro hp
      have := hnorm p
      rw [hp, norm_zero] at this
      norm_num at this
    simp [spherePush, hnorm, hp0]
  constructor
  · intro t
    simp [spherePush, ← add_smul, hnorm]
  constructor
  · intro t x hx hbad
    let v : E3 := (1 - (t : ℝ)) • (x : E3) + (t : ℝ) • (p : E3)
    by_cases hv : v = 0
    · have heq : spherePush p (t, x) = x := by simp [spherePush, v, hv]
      exact hx (by rw [← heq]; exact hbad)
    · have hout : ‖v‖⁻¹ • v = -(p : E3) := by
        have := congrArg (fun z : S2 => (z : E3)) hbad
        simpa [spherePush, v, hv] using this
      have hvform : v = -‖v‖ • (p : E3) := by
        have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
        calc
          v = ‖v‖ • (‖v‖⁻¹ • v) := by
            rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
          _ = ‖v‖ • (-(p : E3)) := by rw [hout]
          _ = -(‖v‖ • (p : E3)) := by rw [smul_neg]
          _ = -‖v‖ • (p : E3) := by rw [neg_smul]
      have hip : @inner ℝ E3 _ (x : E3) (p : E3) = -1 := by
        have he := congrArg (fun z : E3 => @inner ℝ E3 _ z ((x : E3) + p)) hvform
        simp only [v, inner_add_left, inner_add_right, inner_smul_left,
          inner_self_eq_norm_sq_to_K, hnorm, one_pow, mul_one] at he
        rw [real_inner_comm (p : E3) x] at he
        norm_num at he
        ring_nf at he
        have hn : 0 ≤ ‖v‖ := norm_nonneg _
        have hip' : @inner ℝ E3 _ (p : E3) (x : E3) = -1 := by nlinarith
        simpa [real_inner_comm] using hip'
      have hxneg : (x : E3) = -(p : E3) :=
        (inner_eq_neg_one_iff_of_norm_eq_one (hnorm x) (hnorm p)).mp hip
      apply hx
      exact Subtype.ext hxneg
  · intro t x
    have hv : (1 - (t : ℝ)) • ((-x : S2) : E3) + (t : ℝ) • ((-p : S2) : E3) =
        -((1 - (t : ℝ)) • (x : E3) + (t : ℝ) • (p : E3)) := by
      change (1 - (t : ℝ)) • (-(x : E3)) + (t : ℝ) • (-(p : E3)) = _
      module
    by_cases h : (1 - (t : ℝ)) • (x : E3) + (t : ℝ) • (p : E3) = 0
    · have hneg : (1 - (t : ℝ)) • ((-x : S2) : E3) +
          (t : ℝ) • ((-p : S2) : E3) = 0 := by rw [hv, h, neg_zero]
      simp only [spherePush, dif_pos h, dif_pos hneg]
    · have hneg : (1 - (t : ℝ)) • ((-x : S2) : E3) +
          (t : ℝ) • ((-p : S2) : E3) ≠ 0 := by
        rw [hv]
        exact neg_ne_zero.mpr h
      simp only [spherePush, dif_neg h, dif_neg hneg]
      apply Subtype.ext
      change ‖(1 - (t : ℝ)) • ((-x : S2) : E3) + (t : ℝ) • ((-p : S2) : E3)‖⁻¹ •
          ((1 - (t : ℝ)) • ((-x : S2) : E3) + (t : ℝ) • ((-p : S2) : E3)) =
        -(‖(1 - (t : ℝ)) • (x : E3) + (t : ℝ) • (p : E3)‖⁻¹ •
          ((1 - (t : ℝ)) • (x : E3) + (t : ℝ) • (p : E3)))
      rw [hv, norm_neg]
      module

/-! ## 5. Part (a): the chain of spheres -/

/-- `ZMod 0` is `ℤ`. -/
def zOf (i : ZMod 0) : ℤ := i

lemma zOf_add (i j : ZMod 0) : zOf (i + j) = zOf i + zOf j := rfl

lemma zOf_sub (i j : ZMod 0) : zOf (i - j) = zOf i - zOf j := rfl

lemma zOf_zero : zOf 0 = 0 := rfl

/-- The infinite dihedral group acting on `ℤ × S²`: rotations translate by
even integers, reflections flip the chain and apply the antipodal map. -/
def chainSMul : DihedralGroup 0 → ℤ × S2 → ℤ × S2
  | .r i, z => (z.1 + 2 * zOf i, z.2)
  | .sr i, z => (-2 * zOf i - z.1, -z.2)

instance : MulAction (DihedralGroup 0) (ℤ × S2) where
  smul := chainSMul
  one_smul z := by
    change chainSMul 1 z = z
    rw [DihedralGroup.one_def]
    simp [chainSMul, zOf_zero]
  mul_smul g h z := by
    change chainSMul (g * h) z = chainSMul g (chainSMul h z)
    cases g <;> cases h <;>
      simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr, chainSMul, zOf_add, zOf_sub, neg_neg] <;>
      refine Prod.ext ?_ rfl <;> dsimp only <;> ring

lemma chainSMul_r (i : ZMod 0) (z : ℤ × S2) :
    DihedralGroup.r i • z = (z.1 + 2 * zOf i, z.2) := rfl

lemma chainSMul_sr (i : ZMod 0) (z : ℤ × S2) :
    DihedralGroup.sr i • z = (-2 * zOf i - z.1, -z.2) := rfl

instance : ContinuousConstSMul (DihedralGroup 0) (ℤ × S2) where
  continuous_const_smul g := by
    cases g with
    | r i =>
      change Continuous fun z : ℤ × S2 => (z.1 + 2 * zOf i, z.2)
      exact (continuous_fst.add continuous_const).prodMk continuous_snd
    | sr i =>
      change Continuous fun z : ℤ × S2 => (-2 * zOf i - z.1, -z.2)
      exact (continuous_const.sub continuous_fst).prodMk
        ((continuous_neg.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _)

lemma chainRel_smul (g : DihedralGroup 0) (z w : ℤ × S2) (h : ChainRel z w) :
    Relation.EqvGen ChainRel (g • z) (g • w) := by
  cases h with
  | link n =>
    cases g with
    | r i =>
      rw [chainSMul_r, chainSMul_r]
      have : n + 1 + 2 * zOf i = (n + 2 * zOf i) + 1 := by ring
      simp only [this]
      exact Relation.EqvGen.rel _ _ (ChainRel.link _)
    | sr i =>
      rw [chainSMul_sr, chainSMul_sr, neg_north, neg_south]
      have h' := ChainRel.link (-2 * zOf i - (n + 1))
      have : -2 * zOf i - (n + 1) + 1 = -2 * zOf i - n := by ring
      rw [this] at h'
      exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h')

/-- Which wedge summand the sphere `n` covers. -/
def chainSide (n : ℤ) (y : RealProjectivePlane) : RealProjectivePlane ⊕ RealProjectivePlane :=
  if n % 2 = 0 then .inl y else .inr y

/-- **The covering map upstairs**: sphere `n` goes to the summand `n mod 2`
by the antipodal double cover. -/
def chainF (z : ℤ × S2) : ProjectivePlaneWedge :=
  quotientMap (surfacePoint false 1) (surfacePoint false 1) (chainSide z.1 (rp2Proj z.2))

/-- **Leaf.**  `chainF` respects the chain relation: both poles go to the
disk centre and `n`, `n+1` have opposite parities, so both junction points go
to the wedge point.  Route: `rp2Proj_north`, `rp2Proj_south`, `Int.emod_two_eq`,
`Quotient.sound (EqvGen.rel _ _ Rel.base)`.  About 25 lines. -/
lemma chainF_rel (z w : ℤ × S2) (h : ChainRel z w) : chainF z = chainF w := by
  cases h with
  | link n =>
    unfold chainF chainSide
    rw [rp2Proj_north, rp2Proj_south]
    split_ifs <;> try rfl
    · exact Quotient.sound
        (Relation.EqvGen.rel _ _ Rel.base)
    · exact Quotient.sound
        (Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ Rel.base))

/-- **Leaf.**  `chainF` is `D∞`-invariant: rotations preserve parity,
reflections preserve parity (`-2i - n ≡ n`) and `rp2Proj_neg`.  About 25
lines. -/
lemma chainF_smul (g : DihedralGroup 0) (z : ℤ × S2) : chainF (g • z) = chainF z := by
  cases g with
  | r i =>
      rw [chainSMul_r]
      unfold chainF chainSide
      dsimp only
      have hmod : (z.1 + 2 * zOf i) % 2 = z.1 % 2 := by omega
      rw [hmod]
  | sr i =>
      rw [chainSMul_sr]
      unfold chainF chainSide
      dsimp only
      rw [rp2Proj_neg]
      have hmod : (-2 * zOf i - z.1) % 2 = z.1 % 2 := by omega
      rw [hmod]

/-- **Leaf.**  `chainF` is a quotient map.

Route.  `chainF = quotientMap _ _ ∘ G₀` with
`G₀ (n, x) = chainSide n (rp2Proj x)`.  `G₀` is continuous, surjective
(`rp2Proj_surjective`, use `n = 0` or `1`) and open: an open set of
`ℤ × S²` is a union of slices `{n} × Wₙ` and `rp2Proj` is open
(`rp2Proj_isCoveringMap.isOpenMap`), so the image is open in the sum
(`isOpen_sum_iff`).  Hence `IsOpenMap.isQuotientMap`; compose with
`isQuotientMap_quotient_mk'` (`IsQuotientMap.comp`).  About 60 lines. -/
lemma chainF_isQuotientMap : IsQuotientMap chainF := by
  let F : ℤ × S2 → RealProjectivePlane ⊕ RealProjectivePlane :=
    fun z => chainSide z.1 (rp2Proj z.2)
  have hFc : Continuous F := by
    rw [continuous_prod_of_discrete_left]
    intro n
    unfold F chainSide
    simp only [Prod.fst, Prod.snd]
    split_ifs
    · exact continuous_inl.comp rp2Proj_isCoveringMap.continuous
    · exact continuous_inr.comp rp2Proj_isCoveringMap.continuous
  have hFo : IsOpenMap F := by
    rw [isOpenMap_prod_of_discrete_left]
    intro n
    unfold F chainSide
    simp only [Prod.fst, Prod.snd]
    split_ifs
    · exact isOpenMap_inl.comp rp2Proj_isCoveringMap.isOpenMap
    · exact isOpenMap_inr.comp rp2Proj_isCoveringMap.isOpenMap
  have hFs : Function.Surjective F := by
    intro y
    cases y with
    | inl y =>
        obtain ⟨x, rfl⟩ := rp2Proj_surjective y
        refine ⟨(0, x), ?_⟩
        simp [F, chainSide]
    | inr y =>
        obtain ⟨x, rfl⟩ := rp2Proj_surjective y
        refine ⟨(1, x), ?_⟩
        simp [F, chainSide]
  have hFq : IsQuotientMap F := hFo.isQuotientMap hFc hFs
  have hq : IsQuotientMap
      (quotientMap (surfacePoint false 1) (surfacePoint false 1)) :=
    isQuotientMap_quotient_mk'
  have hcomp := hq.comp hFq
  simpa [chainF, F, Function.comp_def] using hcomp

/-- **Leaf.**  Fibres of `chainF` are `D∞`-orbits modulo the chain relation.

Route.  Write `z = (n, x)`, `w = (m, y)`.  Use
`PointWedgeExactEquality.quotientMap_inl_injective`, `..._inr_injective`,
`quotientMap_inl_eq_inr_iff` and `rp2Proj_eq_iff`/`rp2Proj_eq_base_iff`.
Same summand, `y = x`: `g = r ((n - m)/2)`; `y = -x`: `g = sr (-(n + m)/2)`
(`n ≡ m mod 2`).  Different summands: both points are poles (junctions);
the junction `(k, north) ~ (k+1, south)` is moved to junction `k + 2i` by
`r i` and to junction `-2i - k - 1` by `sr i`; pick the parity-correct `g`
and close with one `ChainRel.link` step.  About 130 lines. -/
lemma chainF_fiber (z w : ℤ × S2) (h : chainF z = chainF w) :
    ∃ g : DihedralGroup 0, Relation.EqvGen ChainRel (g • w) z := by
  rcases z with ⟨n, x⟩
  rcases w with ⟨m, y⟩
  by_cases hn : n % 2 = 0 <;> by_cases hm : m % 2 = 0
  · have hxy : rp2Proj x = rp2Proj y := by
      exact (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_injective (surfacePoint false 1)
        (surfacePoint false 1)) (by simpa [chainF, chainSide, hn, hm] using h)
    rcases (rp2Proj_eq_iff x y).mp hxy with hy | hy
    · let i : ZMod 0 := ((n - m) / 2 : ℤ)
      refine ⟨DihedralGroup.r i, ?_⟩
      rw [chainSMul_r]
      have hi : zOf i = (n - m) / 2 := rfl
      rw [hi, hy]
      have : m + 2 * ((n - m) / 2) = n := by omega
      rw [this]
      exact Relation.EqvGen.refl _
    · let i : ZMod 0 := (-(n + m) / 2 : ℤ)
      refine ⟨DihedralGroup.sr i, ?_⟩
      rw [chainSMul_sr]
      have hi : zOf i = -(n + m) / 2 := rfl
      rw [hi, hy, neg_neg]
      have : -2 * (-(n + m) / 2) - m = n := by omega
      rw [this]
      exact Relation.EqvGen.refl _
  · have hb := (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff (surfacePoint false 1)
        (surfacePoint false 1) (rp2Proj x) (rp2Proj y)).mp
        (by simpa [chainF, chainSide, hn, hm] using h)
    have hx := (rp2Proj_eq_base_iff x).mp hb.1
    have hy := (rp2Proj_eq_base_iff y).mp hb.2
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · let i : ZMod 0 := (-(n + 1 + m) / 2 : ℤ)
      refine ⟨DihedralGroup.sr i, ?_⟩
      rw [chainSMul_sr, neg_north]
      have hi : zOf i = -(n + 1 + m) / 2 := rfl
      rw [hi]
      have heq : -2 * (-(n + 1 + m) / 2) - m = n + 1 := by omega
      rw [heq]
      exact Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ (ChainRel.link n))
    · let i : ZMod 0 := ((n + 1 - m) / 2 : ℤ)
      refine ⟨DihedralGroup.r i, ?_⟩
      rw [chainSMul_r]
      have hi : zOf i = (n + 1 - m) / 2 := rfl
      rw [hi]
      have heq : m + 2 * ((n + 1 - m) / 2) = n + 1 := by omega
      rw [heq]
      exact Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ (ChainRel.link n))
    · let i : ZMod 0 := ((n - 1 - m) / 2 : ℤ)
      refine ⟨DihedralGroup.r i, ?_⟩
      rw [chainSMul_r]
      have hi : zOf i = (n - 1 - m) / 2 := rfl
      rw [hi]
      have heq : m + 2 * ((n - 1 - m) / 2) = n - 1 := by omega
      rw [heq]
      have hlink := ChainRel.link (n - 1)
      have hidx : n - 1 + 1 = n := by omega
      rw [hidx] at hlink
      exact Relation.EqvGen.rel _ _ hlink
    · let i : ZMod 0 := (-(n - 1 + m) / 2 : ℤ)
      refine ⟨DihedralGroup.sr i, ?_⟩
      rw [chainSMul_sr, neg_south]
      have hi : zOf i = -(n - 1 + m) / 2 := rfl
      rw [hi]
      have heq : -2 * (-(n - 1 + m) / 2) - m = n - 1 := by omega
      rw [heq]
      have hlink := ChainRel.link (n - 1)
      have hidx : n - 1 + 1 = n := by omega
      rw [hidx] at hlink
      exact Relation.EqvGen.rel _ _ hlink
  · have hb := (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff (surfacePoint false 1)
        (surfacePoint false 1) (rp2Proj y) (rp2Proj x)).mp
        (by simpa [chainF, chainSide, hn, hm] using h.symm)
    have hy := (rp2Proj_eq_base_iff y).mp hb.1
    have hx := (rp2Proj_eq_base_iff x).mp hb.2
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · let i : ZMod 0 := (-(n + 1 + m) / 2 : ℤ)
      refine ⟨DihedralGroup.sr i, ?_⟩
      rw [chainSMul_sr, neg_north]
      have hi : zOf i = -(n + 1 + m) / 2 := rfl
      rw [hi]
      have heq : -2 * (-(n + 1 + m) / 2) - m = n + 1 := by omega
      rw [heq]
      exact Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ (ChainRel.link n))
    · let i : ZMod 0 := ((n + 1 - m) / 2 : ℤ)
      refine ⟨DihedralGroup.r i, ?_⟩
      rw [chainSMul_r]
      have hi : zOf i = (n + 1 - m) / 2 := rfl
      rw [hi]
      have heq : m + 2 * ((n + 1 - m) / 2) = n + 1 := by omega
      rw [heq]
      exact Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ (ChainRel.link n))
    · let i : ZMod 0 := ((n - 1 - m) / 2 : ℤ)
      refine ⟨DihedralGroup.r i, ?_⟩
      rw [chainSMul_r]
      have hi : zOf i = (n - 1 - m) / 2 := rfl
      rw [hi]
      have heq : m + 2 * ((n - 1 - m) / 2) = n - 1 := by omega
      rw [heq]
      have hlink := ChainRel.link (n - 1)
      have hidx : n - 1 + 1 = n := by omega
      rw [hidx] at hlink
      exact Relation.EqvGen.rel _ _ hlink
    · let i : ZMod 0 := (-(n - 1 + m) / 2 : ℤ)
      refine ⟨DihedralGroup.sr i, ?_⟩
      rw [chainSMul_sr, neg_south]
      have hi : zOf i = -(n - 1 + m) / 2 := rfl
      rw [hi]
      have heq : -2 * (-(n - 1 + m) / 2) - m = n - 1 := by omega
      rw [heq]
      have hlink := ChainRel.link (n - 1)
      have hidx : n - 1 + 1 = n := by omega
      rw [hidx] at hlink
      exact Relation.EqvGen.rel _ _ hlink
  · have hxy : rp2Proj x = rp2Proj y := by
      exact (ConstructionTargets.PointWedgeExactEquality.quotientMap_inr_injective (surfacePoint false 1)
        (surfacePoint false 1)) (by simpa [chainF, chainSide, hn, hm] using h)
    rcases (rp2Proj_eq_iff x y).mp hxy with hy | hy
    · let i : ZMod 0 := ((n - m) / 2 : ℤ)
      refine ⟨DihedralGroup.r i, ?_⟩
      rw [chainSMul_r]
      have hi : zOf i = (n - m) / 2 := rfl
      rw [hi, hy]
      have : m + 2 * ((n - m) / 2) = n := by omega
      rw [this]
      exact Relation.EqvGen.refl _
    · let i : ZMod 0 := (-(n + m) / 2 : ℤ)
      refine ⟨DihedralGroup.sr i, ?_⟩
      rw [chainSMul_sr]
      have hi : zOf i = -(n + m) / 2 := rfl
      rw [hi, hy, neg_neg]
      have : -2 * (-(n + m) / 2) - m = n := by omega
      rw [this]
      exact Relation.EqvGen.refl _

/-- Open hemisphere around `p`. -/
def cap (p : S2) : Set S2 := {x | 0 < inner ℝ (x : E3) (p : E3)}

/-- **Leaf.**  Disjoint-translate neighbourhood of the junction `n`:
`V = {n} × cap north ∪ {n+1} × cap south`.

Checks.  Open (slices of open hemispheres).  Saturated: `(k, north) ∈ V ↔ k = n
↔ (k+1, south) ∈ V`.  Disjoint translates: `r i` moves sphere indices by
`2i`, so `i = 0`; `sr i` sends `{n} × cap north` to sphere `-2i-n` inside
`cap south`, which would need `-2i - n = n + 1` (parity), and symmetrically.
About 90 lines. -/
lemma chain_local_junction (n : ℤ) :
    ∃ V : Set (ℤ × S2), IsOpen V ∧ (n, north) ∈ V ∧ (n + 1, south) ∈ V ∧
      Saturated ChainRel V ∧
      ∀ g : DihedralGroup 0, (∃ v ∈ V, g • v ∈ V) → g = 1 := by
  let V : Set (ℤ × S2) :=
    ({n} ×ˢ cap north) ∪ ({n + 1} ×ˢ cap south)
  have hopenN : IsOpen (cap north) := by
    exact isOpen_lt continuous_const
      ((continuous_subtype_val.inner continuous_const))
  have hopenS : IsOpen (cap south) := by
    exact isOpen_lt continuous_const
      ((continuous_subtype_val.inner continuous_const))
  have hcapNN : north ∈ cap north := by
    simp [cap, north]
  have hcapSS : south ∈ cap south := by
    simp [cap, south]
  have hnegN (x : S2) : -x ∈ cap north ↔ x ∈ cap south := by
    simp only [cap, Set.mem_setOf_eq]
    rw [← neg_north]
    simp [inner_neg_left, inner_neg_right]
  have hnegS (x : S2) : -x ∈ cap south ↔ x ∈ cap north := by
    rw [← neg_north]
    simp only [cap, Set.mem_setOf_eq]
    simp [inner_neg_left, inner_neg_right]
  have hdis (x : S2) : ¬(x ∈ cap north ∧ x ∈ cap south) := by
    rintro ⟨hpos, hneg⟩
    have heq : inner ℝ (x : E3) (south : E3) =
        -inner ℝ (x : E3) (north : E3) := by
      rw [← neg_north]
      simp
    rw [cap, Set.mem_setOf_eq, heq] at hneg
    rw [cap, Set.mem_setOf_eq] at hpos
    linarith
  refine ⟨V, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isOpen_discrete {n}).prod hopenN |>.union
      ((isOpen_discrete {n + 1}).prod hopenS)
  · exact Or.inl ⟨by simp, hcapNN⟩
  · exact Or.inr ⟨by simp, hcapSS⟩
  · intro z w h
    cases h with
    | link k =>
      change ((k, north) ∈ V ↔ (k + 1, south) ∈ V)
      simp only [V, Set.mem_union, Set.mem_prod, Set.mem_singleton_iff]
      constructor
      · rintro (⟨rfl, -⟩ | ⟨hk, hbad⟩)
        · exact Or.inr ⟨rfl, hcapSS⟩
        · exact (hdis north ⟨hcapNN, hbad⟩).elim
      · rintro (⟨hk, hbad⟩ | ⟨hk, -⟩)
        · exact (hdis south ⟨hbad, hcapSS⟩).elim
        · have : k = n := by omega
          exact Or.inl ⟨this, hcapNN⟩
  · intro g hg
    obtain ⟨⟨k, x⟩, hv, hgv⟩ := hg
    change ((k, x) ∈ V) at hv
    cases g with
    | r i =>
      rw [chainSMul_r] at hgv
      change ((k + 2 * zOf i, x) ∈ V) at hgv
      simp only [V, Set.mem_union, Set.mem_prod, Set.mem_singleton_iff] at hv hgv
      rcases hv with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;>
        rcases hgv with ⟨heq, hy⟩ | ⟨heq, hy⟩
      · have hi : zOf i = 0 := by omega
        congr 1
      · exact (hdis x ⟨hx, hy⟩).elim
      · exact (hdis x ⟨hy, hx⟩).elim
      · have hi : zOf i = 0 := by omega
        congr 1
    | sr i =>
      rw [chainSMul_sr] at hgv
      change ((-2 * zOf i - k, -x) ∈ V) at hgv
      simp only [V, Set.mem_union, Set.mem_prod, Set.mem_singleton_iff] at hv hgv
      rcases hv with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;>
        rcases hgv with ⟨heq, hy⟩ | ⟨heq, hy⟩
      · exact (hdis x ⟨hx, (hnegN x).mp hy⟩).elim
      · have : False := by omega
        contradiction
      · have : False := by omega
        contradiction
      · exact (hdis x ⟨(hnegS x).mp hy, hx⟩).elim

/-- **Leaf.**  Disjoint-translate neighbourhood of a non-pole point:
`V = {n} × ball x r` with `r ≤ 1` and `r ≤` the distances to both poles
(so `V` avoids the poles, hence is saturated, and `ball x r ∩ -ball x r = ∅`
since `‖x - (-x)‖ = 2`).  `r i` fixes the index only for `i = 0`; `sr i`
negates the sphere point.  About 80 lines. -/
lemma chain_local_regular (n : ℤ) (x : S2) (hN : x ≠ north) (hS : x ≠ south) :
    ∃ V : Set (ℤ × S2), IsOpen V ∧ (n, x) ∈ V ∧ Saturated ChainRel V ∧
      ∀ g : DihedralGroup 0, (∃ v ∈ V, g • v ∈ V) → g = 1 := by
  let d : ℝ := min (dist x north) (min (dist x south) (dist x (-x)))
  let r : ℝ := d / 3
  have hxneg : x ≠ -x := by
    intro h
    have h' := congrArg (fun y : S2 => (y : E3)) h
    have hxnorm : ‖(x : E3)‖ = 1 := by simpa using x.2
    change (x : E3) = -(x : E3) at h'
    have hxzero : (x : E3) = 0 := by
      rw [eq_neg_iff_add_eq_zero] at h'
      have htwo : (2 : ℝ) • (x : E3) = 0 := by simpa [two_smul] using h'
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    rw [hxzero, norm_zero] at hxnorm
    norm_num at hxnorm
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (dist_pos.mpr hN) (lt_min (dist_pos.mpr hS) (dist_pos.mpr hxneg))
  have hr : 0 < r := by dsimp [r]; positivity
  let V : Set (ℤ × S2) := {n} ×ˢ Metric.ball x r
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · exact (isOpen_discrete ({n} : Set ℤ)).prod Metric.isOpen_ball
  · simp [V, hr]
  · intro z w hzw
    cases hzw with
    | link k =>
      simp only [V, Set.mem_prod, Set.mem_singleton_iff, Metric.mem_ball]
      constructor
      · rintro ⟨rfl, hk⟩
        exfalso
        have hle : d ≤ dist x north := min_le_left _ _
        have : dist x north < d / 3 := by simpa [dist_comm] using hk
        linarith
      · rintro ⟨hk, hs⟩
        exfalso
        have hle : d ≤ dist x south := (min_le_right _ _).trans (min_le_left _ _)
        have : dist x south < d / 3 := by simpa [dist_comm] using hs
        linarith
  · intro g hg
    obtain ⟨⟨k, y⟩, hv, hgv⟩ := hg
    cases g with
    | r i =>
      simp only [V, Set.mem_prod, Set.mem_singleton_iff, Metric.mem_ball] at hv hgv
      rw [chainSMul_r] at hgv
      simp only [Prod.fst, Prod.snd] at hgv
      have hi : zOf i = 0 := by omega
      rw [DihedralGroup.one_def]
      congr
    | sr i =>
      simp only [V, Set.mem_prod, Set.mem_singleton_iff, Metric.mem_ball] at hv hgv
      rw [chainSMul_sr] at hgv
      simp only [Prod.fst, Prod.snd] at hgv
      have hxy : dist x y < d / 3 := by simpa [r, dist_comm] using hv.2
      have hxny : dist (-y) x < d / 3 := by simpa [r] using hgv.2
      have hynx : dist y (-x) < d / 3 := by
        have heq : dist y (-x) = dist (-y) x := by
          change ‖(y : E3) - (-(x : S2) : E3)‖ =
            ‖((-y : S2) : E3) - (x : E3)‖
          rw [show ((-y : S2) : E3) = -(y : E3) by rfl]
          rw [sub_neg_eq_add, show -(y : E3) - (x : E3) =
            -((y : E3) + (x : E3)) by module, norm_neg]
        rw [heq]
        exact hxny
      have htri : dist x (-x) ≤ dist x y + dist y (-x) := dist_triangle _ _ _
      have hle : d ≤ dist x (-x) := (min_le_right _ _).trans (min_le_right _ _)
      linarith

lemma chain_local (z : ℤ × S2) :
    ∃ V : Set (ℤ × S2), IsOpen V ∧ z ∈ V ∧ Saturated ChainRel V ∧
      ∀ g : DihedralGroup 0, (∃ v ∈ V, g • v ∈ V) → g = 1 := by
  obtain ⟨n, x⟩ := z
  by_cases hN : x = north
  · subst hN
    obtain ⟨V, h1, h2, -, h4, h5⟩ := chain_local_junction n
    exact ⟨V, h1, h2, h4, h5⟩
  by_cases hS : x = south
  · subst hS
    obtain ⟨V, h1, -, h3, h4, h5⟩ := chain_local_junction (n - 1)
    refine ⟨V, h1, ?_, h4, h5⟩
    simpa using h3
  exact chain_local_regular n x hN hS

theorem sphereChain_isCoveringMap :
    IsCoveringMap (quotLift ChainRel chainF chainF_rel) :=
  isCoveringMap_quotLift_of_deck ChainRel chainRel_smul chainF chainF_isQuotientMap
    chainF_rel chainF_smul chainF_fiber chain_local

/-- The `n`-th star of the chain: sphere `n` without its south pole and
sphere `n+1` without its north pole (they meet at the junction `n`). -/
def chainPiece (n : ℤ) : Set (ℤ × S2) :=
  {z | (z.1 = n ∧ z.2 ≠ south) ∨ (z.1 = n + 1 ∧ z.2 ≠ north)}

/-- Contraction of `chainPiece n` to the junction: push sphere `n` to its
north pole and every other sphere to its south pole. -/
def chainContraction (n : ℤ) (q : unitInterval × (ℤ × S2)) : ℤ × S2 :=
  (q.2.1, if q.2.1 = n then spherePush north (q.1, q.2.2) else spherePush south (q.1, q.2.2))

/-- **Leaf.**  `chainPiece n` is open and saturated.  Saturation:
`(k, north) ∈ P ↔ k = n ↔ (k+1, south) ∈ P` (uses `north_ne_south`).  About
35 lines. -/
lemma chainPiece_open_saturated (n : ℤ) :
    IsOpen (chainPiece n) ∧ Saturated ChainRel (chainPiece n) := by
  constructor
  · have hset : chainPiece n =
        ({n} ×ˢ ({south}ᶜ : Set S2)) ∪
          ({n + 1} ×ˢ ({north}ᶜ : Set S2)) := by
      ext z
      simp [chainPiece]
    rw [hset]
    exact (((isOpen_discrete ({n} : Set ℤ)).prod isOpen_compl_singleton).union
      ((isOpen_discrete ({n + 1} : Set ℤ)).prod isOpen_compl_singleton))
  · intro a b hab
    cases hab with
    | link k =>
      simp [chainPiece, north_ne_south, north_ne_south.symm]

/-- **Leaf.**  Each chain star is simply connected.

Route.  `isSimplyConnected_image_of_contraction` with `H = chainContraction n`,
`z₀ = (n, north)`.  Continuity on `univ ×ˢ chainPiece n`: the index is locally
constant (`ℤ` discrete), on sphere `n` use `spherePush_continuousOn north`
(points `≠ south = -north`), on sphere `n+1` use
`spherePush_continuousOn south` (points `≠ north = -south`).  Maps-to,
`H 0 = id`, endpoint and fixing of the junction from `spherePush_spec`;
`hresp`: the only nontrivial class in the piece is the junction, fixed for all
`t`.  About 100 lines. -/
lemma chainPiece_isSimplyConnected_aux_open_saturated (n : ℤ) :
    IsOpen (chainPiece n) ∧ Saturated ChainRel (chainPiece n) := by
  constructor
  · have hS : IsOpen ({x : S2 | x ≠ south}) := isClosed_singleton.isOpen_compl
    have hN : IsOpen ({x : S2 | x ≠ north}) := isClosed_singleton.isOpen_compl
    have hrepr : chainPiece n =
        ({n} ×ˢ {x : S2 | x ≠ south}) ∪
          ({n + 1} ×ˢ {x : S2 | x ≠ north}) := by
      ext z
      simp [chainPiece]
    rw [hrepr]
    exact ((isOpen_discrete ({n} : Set ℤ)).prod hS).union
      ((isOpen_discrete ({n + 1} : Set ℤ)).prod hN)
  · intro a b hab
    cases hab with
    | link k =>
      change (((k = n ∧ north ≠ south) ∨
        (k = n + 1 ∧ north ≠ north)) ↔
        ((k + 1 = n ∧ south ≠ south) ∨
          (k + 1 = n + 1 ∧ south ≠ north)))
      simp [north_ne_south, north_ne_south.symm]

lemma chainPiece_isSimplyConnected (n : ℤ) :
    IsSimplyConnected (qmk ChainRel '' chainPiece n) := by
  refine isSimplyConnected_image_of_contraction (R := ChainRel) (chainPiece n)
    (chainPiece_isSimplyConnected_aux_open_saturated n).1
    (chainPiece_isSimplyConnected_aux_open_saturated n).2 (chainContraction n)
    ?_ ?_ ?_ (n, north) ?_ ?_ ?_
  · intro q hq
    let F : ℤ × (unitInterval × S2) → ℤ × S2 := fun p =>
      (p.1, if p.1 = n then spherePush north p.2 else spherePush south p.2)
    let S : Set (ℤ × (unitInterval × S2)) :=
      {p | (p.1, p.2.2) ∈ chainPiece n}
    have hF : ContinuousOn F S := by
      rw [continuousOn_prod_of_discrete_left]
      intro k
      by_cases hk : k = n
      · subst k
        simp only [F, if_pos rfl]
        apply ContinuousOn.prodMk continuousOn_const
        apply (spherePush_continuousOn north).mono
        intro p hp
        have hp' : (n, p.2) ∈ chainPiece n := hp
        change (n = n ∧ p.2 ≠ south) ∨ (n = n + 1 ∧ p.2 ≠ north) at hp'
        exact ⟨Set.mem_univ _, by
          rcases hp' with hp' | hp'
          · simpa [neg_north] using hp'.2
          · omega⟩
      · simp only [F, if_neg hk]
        apply ContinuousOn.prodMk continuousOn_const
        apply (spherePush_continuousOn south).mono
        intro p hp
        have hp' : (k, p.2) ∈ chainPiece n := hp
        change (k = n ∧ p.2 ≠ south) ∨ (k = n + 1 ∧ p.2 ≠ north) at hp'
        exact ⟨Set.mem_univ _, by
          rcases hp' with hp' | hp'
          · exact (hk hp'.1).elim
          · simpa [neg_south] using hp'.2⟩
    have hA : Continuous (fun q : unitInterval × (ℤ × S2) =>
        (q.2.1, (q.1, q.2.2))) := by fun_prop
    have hm : MapsTo (fun q : unitInterval × (ℤ × S2) =>
        (q.2.1, (q.1, q.2.2))) (univ ×ˢ chainPiece n) S := by
      intro p hp
      exact hp.2
    simpa [F, S, chainContraction] using hF.comp hA.continuousOn hm q hq
  · intro t z hz
    change (z.1 = n ∧ z.2 ≠ south) ∨ (z.1 = n + 1 ∧ z.2 ≠ north) at hz
    change ((z.1 = n ∧ (chainContraction n (t, z)).2 ≠ south) ∨
      (z.1 = n + 1 ∧ (chainContraction n (t, z)).2 ≠ north))
    rcases hz with (h | h)
    · rcases h with ⟨hk, hx⟩
      left
      refine ⟨hk, ?_⟩
      simpa [chainContraction, hk, neg_north] using
        (spherePush_spec north).2.2.2.1 t z.2 (by simpa [neg_north] using hx)
    · rcases h with ⟨hk, hx⟩
      right
      refine ⟨hk, ?_⟩
      have hkn : z.1 ≠ n := by omega
      simpa [chainContraction, hkn, neg_south] using
        (spherePush_spec south).2.2.2.1 t z.2 (by simpa [neg_south] using hx)
  · intro z hz
    simp only [chainContraction]
    split_ifs with h
    · simp [(spherePush_spec north).1]
    · simp [(spherePush_spec south).1]
  · change (n = n ∧ north ≠ south) ∨ (n = n + 1 ∧ north ≠ north)
    left
    exact ⟨rfl, north_ne_south⟩
  · intro z hz
    change (z.1 = n ∧ z.2 ≠ south) ∨ (z.1 = n + 1 ∧ z.2 ≠ north) at hz
    rcases hz with (h | h)
    · rcases h with ⟨rfl, hx⟩
      simp [chainContraction, (spherePush_spec north).2.1 _ (by simpa [neg_north] using hx)]
    · rcases h with ⟨hk, hx⟩
      have hkn : z.1 ≠ n := by omega
      have hp := (spherePush_spec south).2.1 z.2 (by simpa [neg_south] using hx)
      simp [chainContraction, hkn, hp]
      apply Quotient.sound
      rw [hk]
      exact Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ (ChainRel.link n))
  · intro t a b ha hab
    change (a.1 = n ∧ a.2 ≠ south) ∨ (a.1 = n + 1 ∧ a.2 ≠ north) at ha
    rcases hab with ⟨k⟩
    have hk : k = n := by
      rcases ha with h | h
      · exact h.1
      · exfalso
        exact h.2 rfl
    subst k
    simp [chainContraction, (spherePush_spec north).2.2.1,
      (spherePush_spec south).2.2.1]
    simpa using (Quotient.sound (Relation.EqvGen.rel _ _ (ChainRel.link n)))

/-- **Leaf.**  Chain stars meet only when adjacent, and adjacent stars meet in
a path-connected set.

Route.  By `Saturated.image_inter`, intersections are images of upstairs
intersections; `chainPiece n ∩ chainPiece m = ∅` unless `|n - m| ≤ 1`, and
`chainPiece n ∩ chainPiece (n+1) = {n+1} × (S² \ {north, south})`, the image of
`sphere_compl_poles_isPathConnected` under the continuous
`x ↦ qmk (n+1, x)`.  About 80 lines. -/
lemma chainPiece_inter (n m : ℤ) :
    ((qmk ChainRel '' chainPiece n ∩ qmk ChainRel '' chainPiece m).Nonempty →
      n = m ∨ m = n + 1 ∨ n = m + 1) ∧
    IsPathConnected (qmk ChainRel '' chainPiece n ∩ qmk ChainRel '' chainPiece (n + 1)) := by
  have hinter (i j : ℤ) :
      qmk ChainRel '' chainPiece i ∩ qmk ChainRel '' chainPiece j =
        qmk ChainRel '' (chainPiece i ∩ chainPiece j) :=
    (chainPiece_open_saturated i).2.image_inter
  constructor
  · rw [hinter]
    rintro ⟨q, ⟨⟨k, x⟩, hkx, rfl⟩⟩
    rcases hkx with ⟨hi, hj⟩
    simp only [chainPiece] at hi hj
    rcases hi with ⟨hki, -⟩ | ⟨hki, -⟩ <;>
      rcases hj with ⟨hkj, -⟩ | ⟨hkj, -⟩
    · left; omega
    · right; right; omega
    · right; left; omega
    · left; omega
  · rw [hinter]
    have hset : chainPiece n ∩ chainPiece (n + 1) =
        (fun x : S2 => (n + 1, x)) '' {x : S2 | x ≠ north ∧ x ≠ south} := by
      ext z
      rcases z with ⟨k, x⟩
      simp only [chainPiece, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨hn, hm⟩
        rcases hn with ⟨hkn, hxS⟩ | ⟨hkn, hxN⟩ <;>
          rcases hm with ⟨hkm, hyS⟩ | ⟨hkm, hyN⟩
        · omega
        · omega
        · subst k
          exact ⟨x, ⟨hxN, hyS⟩, rfl⟩
        · omega
      · rintro ⟨y, ⟨hyN, hyS⟩, h⟩
        cases h
        exact ⟨Or.inr ⟨rfl, hyN⟩, Or.inl ⟨rfl, hyS⟩⟩
    rw [hset, Set.image_image]
    exact sphere_compl_poles_isPathConnected.image
      ((continuous_qmk ChainRel).comp (continuous_const.prodMk continuous_id))

lemma chainPiece_cover : ⋃ n, qmk ChainRel '' chainPiece n = univ := by
  apply eq_univ_of_forall
  rintro ⟨n, x⟩
  by_cases hS : x = south
  · subst hS
    refine mem_iUnion.mpr ⟨n - 1, (n, south), ?_, rfl⟩
    right
    exact ⟨by simp, north_ne_south.symm⟩
  · exact mem_iUnion.mpr ⟨n, (n, x), Or.inl ⟨rfl, hS⟩, rfl⟩

/-- The chain stars form a tree cover (a path `… - (-1) - 0 - 1 - …`). -/
def chainTreeCover : TreeCover SphereChain ℤ where
  U n := qmk ChainRel '' chainPiece n
  depth n := n.natAbs
  parent n := if 0 < n then n - 1 else n + 1
  root := 0
  isOpen n := (chainPiece_open_saturated n).2.isOpen_image (chainPiece_open_saturated n).1
  simplyConnected n := chainPiece_isSimplyConnected n
  cover := chainPiece_cover
  depth_eq_zero n := by simp
  depth_parent n hn := by split_ifs <;> omega
  inter_parent n hn := by
    split_ifs with h
    · have := (chainPiece_inter (n - 1) n).2
      rw [sub_add_cancel] at this
      rwa [inter_comm]
    · exact (chainPiece_inter n n).2
  inter_adj n m hnm hne := by
    rcases (chainPiece_inter n m).1 hne with h | h | h
    · exact absurd h hnm
    · by_cases hn : 0 ≤ n
      · right; refine ⟨by omega, ?_⟩; simp only [show 0 < m by omega, if_true]; omega
      · left; refine ⟨by omega, ?_⟩; simp only [show ¬ 0 < n by omega, if_false]; omega
    · by_cases hm : 0 ≤ m
      · left; refine ⟨by omega, ?_⟩; simp only [show 0 < n by omega, if_true]; omega
      · right; refine ⟨by omega, ?_⟩; simp only [show ¬ 0 < m by omega, if_false]; omega

/-! ## 6. Part (b): the tree of lines and spheres -/

/-- The disjoint union upstairs. -/
abbrev TreeZ := (G × unitInterval) ⊕ (G × S2)

/-- `G` acts by left multiplication on the cell labels. -/
instance : MulAction G TreeZ where
  smul g := Sum.map (fun p => (g * p.1, p.2)) (fun p => (g * p.1, p.2))
  one_smul z := by
    rcases z with ⟨h, t⟩ | ⟨h, x⟩ <;> simp [HSMul.hSMul, SMul.smul]
  mul_smul g k z := by
    rcases z with ⟨h, t⟩ | ⟨h, x⟩ <;> simp [HSMul.hSMul, SMul.smul, mul_assoc]

@[simp] lemma treeSMul_inl (g h : G) (t : unitInterval) :
    g • (Sum.inl (h, t) : TreeZ) = .inl (g * h, t) := rfl

@[simp] lemma treeSMul_inr (g h : G) (x : S2) :
    g • (Sum.inr (h, x) : TreeZ) = .inr (g * h, x) := rfl

instance : ContinuousConstSMul G TreeZ where
  continuous_const_smul g := by
    change Continuous (Sum.map (fun p : G × unitInterval => (g * p.1, p.2))
      (fun p : G × S2 => (g * p.1, p.2)))
    exact (((continuous_const_mul g).comp continuous_fst).prodMk continuous_snd).sumMap
      (((continuous_const_mul g).comp continuous_fst).prodMk continuous_snd)

lemma treeRel_smul (g : G) (z w : TreeZ) (h : TreeRel z w) :
    Relation.EqvGen TreeRel (g • z) (g • w) := by
  apply Relation.EqvGen.rel
  cases h with
  | edge k => simpa [mul_assoc] using TreeRel.edge (g * k)
  | vertex k => simpa using TreeRel.vertex (g * k)
  | pair k x => simpa [mul_assoc] using TreeRel.pair (g * k) x

/-- `t ↦ exp(2π i t)`, the unit interval wrapped once around the circle. -/
def circleOfUnit (t : unitInterval) : Circle := Circle.exp (2 * Real.pi * t)

/-- **The covering map upstairs**: every edge wraps once around the circle,
every sphere copy double covers `RP²`. -/
def treeF : TreeZ → CircleWedgeProjectivePlane
  | .inl (_, t) => quotientMap (1 : Circle) (surfacePoint false 1) (.inl (circleOfUnit t))
  | .inr (_, x) => quotientMap (1 : Circle) (surfacePoint false 1) (.inr (rp2Proj x))

/-- **Leaf.**  `treeF` respects the tree relation.  Route: `circleOfUnit 0 =
circleOfUnit 1 = 1` (`Circle.exp_zero`, `Circle.exp_two_pi`), `rp2Proj_north`
plus `Rel.base` for the vertex relation, `rp2Proj_neg` for the pair relation.
About 25 lines. -/
lemma treeF_rel (z w : TreeZ) (h : TreeRel z w) : treeF z = treeF w := by
  cases h with
  | edge g =>
      unfold treeF circleOfUnit
      simp
  | vertex g =>
      unfold treeF
      change quotientMap (1 : Circle) (surfacePoint false 1) (.inl (circleOfUnit 0)) =
        quotientMap (1 : Circle) (surfacePoint false 1) (.inr (rp2Proj north))
      rw [rp2Proj_north]
      simpa [circleOfUnit] using
        (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base) :
          quotientMap (1 : Circle) (surfacePoint false 1) (.inl 1) =
            quotientMap (1 : Circle) (surfacePoint false 1) (.inr (surfacePoint false 1)))
  | pair g x =>
      unfold treeF
      change quotientMap (1 : Circle) (surfacePoint false 1) (.inr (rp2Proj x)) =
        quotientMap (1 : Circle) (surfacePoint false 1) (.inr (rp2Proj (-x)))
      rw [rp2Proj_neg]

lemma treeF_smul (g : G) (z : TreeZ) : treeF (g • z) = treeF z := by
  rcases z with ⟨h, t⟩ | ⟨h, x⟩ <;> rfl

/-- **Leaf.**  `treeF` is a quotient map.

Route.  `treeF = quotientMap _ _ ∘ Sum.map (circleOfUnit ∘ Prod.snd)
(rp2Proj ∘ Prod.snd)`.  `Prod.snd : G × I → I` is an open surjection;
`circleOfUnit` is a continuous surjection from a compact space to a Hausdorff
space, hence closed, hence quotient (`IsClosedMap.isQuotientMap`);
`rp2Proj ∘ snd` is an open surjection.  A sum of quotient maps is a quotient
map (check `isOpen_sum_iff` on preimages), and compose with
`isQuotientMap_quotient_mk'`.  About 80 lines. -/
lemma treeF_isQuotientMap_aux_circle_surjective :
    Function.Surjective circleOfUnit := by
  intro z
  by_cases h : 0 ≤ Complex.arg (z : ℂ)
  · let t : unitInterval := ⟨Complex.arg (z : ℂ) / (2 * Real.pi), by
      constructor
      · positivity
      · apply (div_le_one (by positivity)).2
        linarith [Complex.arg_le_pi (z : ℂ)]⟩
    refine ⟨t, ?_⟩
    rw [circleOfUnit]
    convert Circle.exp_arg z using 1
    dsimp [t]
    field_simp
  · have ha : Complex.arg (z : ℂ) < 0 := lt_of_not_ge h
    let t : unitInterval :=
      ⟨(Complex.arg (z : ℂ) + 2 * Real.pi) / (2 * Real.pi), by
        constructor
        · apply div_nonneg
          · linarith [Complex.neg_pi_lt_arg (z : ℂ), Real.pi_pos]
          · positivity
        · apply (div_le_one (by positivity)).2
          linarith⟩
    refine ⟨t, ?_⟩
    rw [circleOfUnit]
    have he : 2 * Real.pi * (t : ℝ) = Complex.arg (z : ℂ) + 2 * Real.pi := by
      dsimp [t]
      field_simp
    rw [he, Circle.exp_add, Circle.exp_two_pi, mul_one, Circle.exp_arg]

lemma treeF_isQuotientMap : IsQuotientMap treeF := by
  let f : G × unitInterval → Circle := fun p => circleOfUnit p.2
  let r : G × S2 → RealProjectivePlane := fun p => rp2Proj p.2
  let F : TreeZ → Circle ⊕ RealProjectivePlane := Sum.map f r
  have hfc : Continuous f := by
    unfold f circleOfUnit
    fun_prop
  have hfs : Function.Surjective f := by
    intro z
    obtain ⟨t, ht⟩ := treeF_isQuotientMap_aux_circle_surjective z
    exact ⟨(1, t), ht⟩
  have hfq : IsQuotientMap f := by
    have hclosed : IsClosedMap circleOfUnit :=
      (Circle.exp.continuous.comp
        (continuous_subtype_val.const_mul (2 * Real.pi))).isClosedMap
    have hcq : IsQuotientMap circleOfUnit :=
      hclosed.isQuotientMap
        (Circle.exp.continuous.comp
          (continuous_subtype_val.const_mul (2 * Real.pi)))
        treeF_isQuotientMap_aux_circle_surjective
    exact hcq.comp isQuotientMap_snd
  have hrq : IsQuotientMap r := by
    apply (rp2Proj_isCoveringMap.isOpenMap.comp isOpenMap_snd).isQuotientMap
      (by
        exact rp2Proj_isCoveringMap.continuous.comp
          (continuous_snd : Continuous (fun p : G × S2 => p.2)))
      (by
        intro y
        obtain ⟨x, hx⟩ := rp2Proj_surjective y
        exact ⟨(1, x), hx⟩)
  have hFq : IsQuotientMap F := by
    rw [isQuotientMap_iff]
    refine ⟨?_, ?_⟩
    · intro y
      cases y with
      | inl y =>
          obtain ⟨x, rfl⟩ := hfs y
          exact ⟨.inl x, rfl⟩
      | inr y =>
          obtain ⟨x, rfl⟩ := hrq.surjective y
          exact ⟨.inr x, rfl⟩
    · intro U
      rw [isOpen_sum_iff, isOpen_sum_iff]
      change IsOpen (Sum.inl ⁻¹' U) ∧ IsOpen (Sum.inr ⁻¹' U) ↔
        IsOpen (f ⁻¹' (Sum.inl ⁻¹' U)) ∧ IsOpen (r ⁻¹' (Sum.inr ⁻¹' U))
      exact and_congr ((isQuotientMap_iff.mp hfq).2 _)
        ((isQuotientMap_iff.mp hrq).2 _)
  have hq : IsQuotientMap
      (quotientMap (1 : Circle) (surfacePoint false 1)) :=
    isQuotientMap_quotient_mk'
  have := hq.comp hFq
  have heq : treeF =
      (quotientMap (1 : Circle) (surfacePoint false 1)) ∘ F := by
    funext z
    cases z <;> rfl
  rw [heq]
  exact this

/-- **Leaf.**  Fibres of `treeF` are `G`-orbits modulo the tree relation.

Route.  Cases on the two summands, with the wedge equalities from
`PointWedgeExactEquality`, `circleOfUnit t = circleOfUnit s ↔ t = s ∨ {t,s} =
{0,1}` (injectivity of `Circle.exp` on `[0, 2π)`: `Circle.exp_eq_exp` /
`Circle.exp_inj` style lemmas) and `rp2Proj_eq_iff`, `rp2Proj_eq_base_iff`.
Edge points: `g = h k⁻¹` (same parameter) or one `edge` step
(`g = h a⁻¹ k⁻¹` or `g = h a k⁻¹`); sphere points: `g = h k⁻¹` or one `pair`
step (`g = h b⁻¹ k⁻¹`); wedge-point fibre: the vertex classes
`{(g,0), (g a⁻¹, 1), (g, north), (g b, south)}` are permuted transitively.
About 150 lines. -/
lemma treeF_fiber_aux_circle (t s : unitInterval)
    (h : circleOfUnit t = circleOfUnit s) :
    t = s ∨ ((t : ℝ) = 0 ∧ (s : ℝ) = 1) ∨
      ((t : ℝ) = 1 ∧ (s : ℝ) = 0) := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
  have hpi : 0 < Real.pi := Real.pi_pos
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  change 2 * Real.pi * (t : ℝ) =
    2 * Real.pi * (s : ℝ) + (m : ℝ) * (2 * Real.pi) at hm
  have hts : (t : ℝ) = (s : ℝ) + (m : ℝ) := by nlinarith
  have hmlo : (-1 : ℝ) ≤ (m : ℝ) := by linarith
  have hmhi : (m : ℝ) ≤ 1 := by linarith
  have hmlo' : (-1 : ℤ) ≤ m := by exact_mod_cast hmlo
  have hmhi' : m ≤ (1 : ℤ) := by exact_mod_cast hmhi
  have hm' : m = -1 ∨ m = 0 ∨ m = 1 := by omega
  rcases hm' with rfl | rfl | rfl
  · right; left; norm_num at hts; constructor <;> linarith
  · left; apply Subtype.ext; norm_num at hts ⊢; exact hts
  · right; right; norm_num at hts; constructor <;> linarith

lemma treeF_fiber_aux_sphere (gz gw : G) (x y : S2)
    (h : rp2Proj x = rp2Proj y) :
    ∃ g : G, Relation.EqvGen TreeRel
      (g • (Sum.inr (gw, y) : TreeZ)) (.inr (gz, x)) := by
  rcases (rp2Proj_eq_iff x y).mp h with hy | hy
  · subst y
    refine ⟨gz * gw⁻¹, ?_⟩
    change Relation.EqvGen TreeRel (.inr ((gz * gw⁻¹) * gw, x)) (.inr (gz, x))
    have he : (gz * gw⁻¹) * gw = gz := by group
    rw [he]
    exact Relation.EqvGen.refl _
  · subst y
    refine ⟨gz * b⁻¹ * gw⁻¹, ?_⟩
    change Relation.EqvGen TreeRel
      (.inr (((gz * b⁻¹ * gw⁻¹) * gw), -x)) (.inr (gz, x))
    have he : (gz * b⁻¹ * gw⁻¹) * gw = gz * b⁻¹ := by group
    rw [he]
    have heb : (gz * b⁻¹) * b = gz := by group
    simpa only [heb, neg_neg] using
      (Relation.EqvGen.rel _ _ (TreeRel.pair (gz * b⁻¹) (-x)))

lemma treeF_fiber (z w : TreeZ) (h : treeF z = treeF w) :
    ∃ g : G, Relation.EqvGen TreeRel (g • w) z := by
  rcases z with ⟨gz, t⟩ | ⟨gz, x⟩ <;> rcases w with ⟨gw, s⟩ | ⟨gw, y⟩
  · have hc : circleOfUnit t = circleOfUnit s :=
      (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_injective
        (1 : Circle) (surfacePoint false 1)) h
    rcases treeF_fiber_aux_circle t s hc with hts | ⟨ht, hs⟩ | ⟨ht, hs⟩
    · subst s
      refine ⟨gz * gw⁻¹, ?_⟩
      simpa using (Relation.EqvGen.refl (Sum.inl (gz, t) : TreeZ))
    · have ht' : t = 0 := Subtype.ext ht
      have hs' : s = 1 := Subtype.ext hs
      subst t; subst s
      refine ⟨gz * a⁻¹ * gw⁻¹, ?_⟩
      simpa [mul_assoc] using
        (Relation.EqvGen.rel _ _ (TreeRel.edge (gz * a⁻¹)))
    · have ht' : t = 1 := Subtype.ext ht
      have hs' : s = 0 := Subtype.ext hs
      subst t; subst s
      refine ⟨gz * a * gw⁻¹, ?_⟩
      simpa [mul_assoc] using
        (Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ (TreeRel.edge gz)))
  · have hb :=
      (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff
        (1 : Circle) (surfacePoint false 1) (circleOfUnit t) (rp2Proj y)).mp h
    have htbase : (t : ℝ) = 0 ∨ (t : ℝ) = 1 := by
      have hc : circleOfUnit t = circleOfUnit 0 := by simpa [circleOfUnit] using hb.1
      rcases treeF_fiber_aux_circle t 0 hc with ht | ht | ht
      · exact Or.inl (congrArg Subtype.val ht)
      · exact Or.inl ht.1
      · exact Or.inr ht.1
    rcases (rp2Proj_eq_base_iff y).mp hb.2 with hy | hy
    · subst y
      rcases htbase with ht | ht
      · have ht' : t = 0 := Subtype.ext ht
        subst t
        refine ⟨gz * gw⁻¹, ?_⟩
        simpa using (Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ (TreeRel.vertex gz)))
      · have ht' : t = 1 := Subtype.ext ht
        subst t
        refine ⟨gz * a * gw⁻¹, ?_⟩
        exact Relation.EqvGen.trans _ _ _
          (by simpa [mul_assoc] using (Relation.EqvGen.symm _ _
            (Relation.EqvGen.rel _ _ (TreeRel.vertex (gz * a)))))
          (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (TreeRel.edge gz)))
    · subst y
      rcases htbase with ht | ht
      · have ht' : t = 0 := Subtype.ext ht
        subst t
        refine ⟨gz * b⁻¹ * gw⁻¹, ?_⟩
        exact Relation.EqvGen.trans _ _ _
          (by simpa [mul_assoc] using
            (show Relation.EqvGen TreeRel (.inr (gz * b⁻¹, south)) (.inr (gz, north)) by
              rw [← neg_south]
              simpa [mul_assoc] using
                (Relation.EqvGen.rel _ _ (TreeRel.pair (gz * b⁻¹) south))))
          (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (TreeRel.vertex gz)))
      · have ht' : t = 1 := Subtype.ext ht
        subst t
        refine ⟨gz * a * b⁻¹ * gw⁻¹, ?_⟩
        exact Relation.EqvGen.trans _ _ _
          (by simpa [mul_assoc] using
            (show Relation.EqvGen TreeRel (.inr (gz * a * b⁻¹, south))
                (.inr (gz * a, north)) by
              rw [← neg_south]
              simpa [mul_assoc] using
                (Relation.EqvGen.rel _ _ (TreeRel.pair (gz * a * b⁻¹) south))))
          (Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (TreeRel.vertex (gz * a))))
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (TreeRel.edge gz))))
  · have hb :=
      (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff
        (1 : Circle) (surfacePoint false 1) (circleOfUnit s) (rp2Proj x)).mp h.symm
    have hsbase : (s : ℝ) = 0 ∨ (s : ℝ) = 1 := by
      have hc : circleOfUnit s = circleOfUnit 0 := by simpa [circleOfUnit] using hb.1
      rcases treeF_fiber_aux_circle s 0 hc with hs | hs | hs
      · exact Or.inl (congrArg Subtype.val hs)
      · exact Or.inl hs.1
      · exact Or.inr hs.1
    rcases (rp2Proj_eq_base_iff x).mp hb.2 with hx | hx
    · subst x
      rcases hsbase with hs | hs
      · have hs' : s = 0 := Subtype.ext hs
        subst s
        refine ⟨gz * gw⁻¹, ?_⟩
        simpa using (Relation.EqvGen.rel _ _ (TreeRel.vertex gz))
      · have hs' : s = 1 := Subtype.ext hs
        subst s
        refine ⟨gz * a⁻¹ * gw⁻¹, ?_⟩
        exact Relation.EqvGen.trans _ _ _
          (by simpa [mul_assoc] using
            (Relation.EqvGen.rel _ _ (TreeRel.edge (gz * a⁻¹))))
          (Relation.EqvGen.rel _ _ (TreeRel.vertex gz))
    · subst x
      rcases hsbase with hs | hs
      · have hs' : s = 0 := Subtype.ext hs
        subst s
        refine ⟨gz * b⁻¹ * gw⁻¹, ?_⟩
        exact Relation.EqvGen.trans _ _ _
          (by simpa [mul_assoc] using (Relation.EqvGen.rel _ _ (TreeRel.vertex (gz * b⁻¹))))
          (show Relation.EqvGen TreeRel (.inr (gz * b⁻¹, north)) (.inr (gz, south)) by
            rw [← neg_north]
            simpa [mul_assoc] using
              (Relation.EqvGen.rel _ _ (TreeRel.pair (gz * b⁻¹) north)))
      · have hs' : s = 1 := Subtype.ext hs
        subst s
        refine ⟨gz * b⁻¹ * a⁻¹ * gw⁻¹, ?_⟩
        exact Relation.EqvGen.trans _ _ _
          (by simpa [mul_assoc] using
            (Relation.EqvGen.rel _ _ (TreeRel.edge (gz * b⁻¹ * a⁻¹))))
          (Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.rel _ _ (TreeRel.vertex (gz * b⁻¹)))
            (show Relation.EqvGen TreeRel (.inr (gz * b⁻¹, north)) (.inr (gz, south)) by
              rw [← neg_north]
              simpa [mul_assoc] using
                (Relation.EqvGen.rel _ _ (TreeRel.pair (gz * b⁻¹) north))))
  · have hp : rp2Proj x = rp2Proj y :=
      (ConstructionTargets.PointWedgeExactEquality.quotientMap_inr_injective
        (1 : Circle) (surfacePoint false 1)) h
    exact treeF_fiber_aux_sphere gz gw x y hp

/-- **Leaf (facts about `G = ℤ * ℤ/2`).**  Route: map to `Multiplicative ℤ`
by `Monoid.Coprod.fst` (detects every item involving `a`) and to
`Multiplicative (ZMod 2)` by `Monoid.Coprod.snd` (detects `b ≠ 1`);
`b * b = inr (ofAdd 2) = 1` by `decide` in `ZMod 2`.  About 40 lines. -/
lemma G_facts :
    a ≠ 1 ∧ b ≠ 1 ∧ b * b = 1 ∧ a * a ≠ 1 ∧ a ≠ b ∧ a⁻¹ ≠ b ∧ a * b ≠ 1 := by
  constructor
  · intro h
    have := congrArg (Monoid.Coprod.fst : G → Multiplicative ℤ) h
    simp [a] at this
  constructor
  · intro h
    have := congrArg (Monoid.Coprod.snd : G → Multiplicative (ZMod 2)) h
    norm_num [b] at this
  constructor
  · have hz : (Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1 :
        Multiplicative (ZMod 2)) = 1 := by decide
    calc
      b * b = Monoid.Coprod.inr
          (Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1) := by simp [b]
      _ = Monoid.Coprod.inr 1 := congrArg Monoid.Coprod.inr hz
      _ = 1 := map_one _
  constructor
  · intro h
    have := congrArg (Monoid.Coprod.fst : G → Multiplicative ℤ) h
    change Multiplicative.ofAdd (1 + 1 : ℤ) = Multiplicative.ofAdd 0 at this
    norm_num at this
  constructor
  · intro h
    have := congrArg (Monoid.Coprod.fst : G → Multiplicative ℤ) h
    simp [a, b] at this
  constructor
  · intro h
    have := congrArg (Monoid.Coprod.fst : G → Multiplicative ℤ) h
    norm_num [a, b] at this
  · intro h
    have := congrArg (Monoid.Coprod.fst : G → Multiplicative ℤ) h
    simp [a, b] at this

/-- **Leaf.**  Disjoint-translate neighbourhood of an interior edge point:
`V = inl ({g} × (0,1))`.  No relation touches interior edge points, and
`k • V ∩ V ≠ ∅` forces `k g = g`.  About 40 lines. -/
lemma tree_local_edge (g : G) (t : unitInterval) (h0 : (t : ℝ) ≠ 0) (h1 : (t : ℝ) ≠ 1) :
    ∃ V : Set TreeZ, IsOpen V ∧ .inl (g, t) ∈ V ∧ Saturated TreeRel V ∧
      ∀ k : G, (∃ v ∈ V, k • v ∈ V) → k = 1 := by
  let U : Set unitInterval := {s | (s : ℝ) ≠ 0 ∧ (s : ℝ) ≠ 1}
  let V : Set TreeZ := {z | match z with
    | .inl (h, s) => h = g ∧ s ∈ U
    | .inr _ => False}
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · rw [isOpen_sum_iff]
    constructor
    · simpa [V, U] using
        ((isOpen_discrete ({g} : Set G)).prod
          ((isClosed_singleton.isOpen_compl.inter isClosed_singleton.isOpen_compl :
            IsOpen ({0}ᶜ ∩ {1}ᶜ : Set unitInterval))))
    · simp [V]
  · exact ⟨rfl, h0, h1⟩
  · intro z w hzw
    cases hzw with
    | edge h => simp [V, U]
    | vertex h => simp [V, U]
    | pair h x => simp [V]
  · intro k hk
    obtain ⟨v, hv, hkv⟩ := hk
    rcases v with ⟨h, s⟩ | ⟨h, x⟩
    · have hv' : h = g ∧ s ∈ U := by simpa [V] using hv
      have hh : h = g := hv'.1
      subst h
      have hkv' : k * g = g ∧ s ∈ U := by simpa [V] using hkv
      have hkg : k * g = g := hkv'.1
      exact (mul_right_cancel (hkg.trans (one_mul g).symm))
    · simp [V] at hv

/-- **Leaf.**  Disjoint-translate neighbourhood of the vertex `g`:
`V = inl ({g} × [0,1/2)) ∪ inl ({g a⁻¹} × (1/2,1]) ∪ inr ({g} × cap north)
∪ inr ({g b} × cap south)`.

Checks.  Saturated: `edge k` relates `(k,1) ∈ V ↔ k = g a⁻¹ ↔ (k a, 0) ∈ V`;
`vertex k`: `(k,0) ∈ V ↔ k = g ↔ (k, north) ∈ V`; `pair k x`:
`(k, x) ∈ V ↔ (k b, -x) ∈ V` using `b * b = 1` (`G_facts`) and
`-x ∈ cap north ↔ x ∈ cap south`.  Disjointness: a translate keeps the
`t`-coordinate (resp. the sphere point), so it stays in the same piece and
`k h = h` forces `k = 1`.  About 110 lines. -/
lemma tree_local_vertex (g : G) :
    ∃ V : Set TreeZ, IsOpen V ∧ .inl (g, 0) ∈ V ∧ .inl (g * a⁻¹, 1) ∈ V ∧
      .inr (g, north) ∈ V ∧ .inr (g * b, south) ∈ V ∧ Saturated TreeRel V ∧
      ∀ k : G, (∃ v ∈ V, k • v ∈ V) → k = 1 := by
  let V : Set TreeZ := {z | match z with
    | .inl (h, t) =>
        (h = g ∧ (t : ℝ) < (1 / 2 : ℝ)) ∨
        (h = g * a⁻¹ ∧ (1 / 2 : ℝ) < (t : ℝ))
    | .inr (h, x) =>
        (h = g ∧ (0 : ℝ) < (x : E3) 2) ∨
        (h = g * b ∧ (x : E3) 2 < 0)}
  have hbb : b * b = 1 := G_facts.2.2.1
  have hVopen : IsOpen V := by
    rw [isOpen_sum_iff]
    constructor
    · change IsOpen ({p : G × unitInterval |
          (p.1 = g ∧ (p.2 : ℝ) < (1 / 2 : ℝ)) ∨
          (p.1 = g * a⁻¹ ∧ (1 / 2 : ℝ) < (p.2 : ℝ))})
      apply IsOpen.union
      · exact (isOpen_discrete ({g} : Set G)).prod
          (isOpen_lt continuous_subtype_val continuous_const)
      · exact (isOpen_discrete ({g * a⁻¹} : Set G)).prod
          (isOpen_lt continuous_const continuous_subtype_val)
    · change IsOpen ({p : G × S2 |
          (p.1 = g ∧ (0 : ℝ) < (p.2 : E3) 2) ∨
          (p.1 = g * b ∧ (p.2 : E3) 2 < 0)})
      have hc : Continuous (fun x : S2 => ((x : E3) 2 : ℝ)) := by fun_prop
      apply IsOpen.union
      · exact (isOpen_discrete ({g} : Set G)).prod
          (isOpen_lt continuous_const hc)
      · exact (isOpen_discrete ({g * b} : Set G)).prod
          (isOpen_lt hc continuous_const)
  refine ⟨V, hVopen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inl ⟨rfl, by norm_num⟩
  · exact Or.inr ⟨rfl, by norm_num⟩
  · exact Or.inl ⟨rfl, by simp [north]⟩
  · exact Or.inr ⟨rfl, by simp [south]⟩
  · intro z w hzw
    cases hzw with
    | edge h =>
        change
          ((h = g ∧ (1 : ℝ) < 1 / 2) ∨ (h = g * a⁻¹ ∧ 1 / 2 < (1 : ℝ))) ↔
          ((h * a = g ∧ (0 : ℝ) < 1 / 2) ∨
            (h * a = g * a⁻¹ ∧ 1 / 2 < (0 : ℝ)))
        constructor
        · rintro (ha | ha)
          · norm_num at ha
          · left
            refine ⟨?_, by norm_num⟩
            calc h * a = (g * a⁻¹) * a := congrArg (fun q => q * a) ha.1
              _ = g := by simp
        · rintro (ha | ha)
          · right
            refine ⟨?_, by norm_num⟩
            calc h = (h * a) * a⁻¹ := by simp
              _ = g * a⁻¹ := congrArg (fun q => q * a⁻¹) ha.1
          · norm_num at ha
    | vertex h =>
        change
          ((h = g ∧ (0 : ℝ) < 1 / 2) ∨ (h = g * a⁻¹ ∧ 1 / 2 < (0 : ℝ))) ↔
          ((h = g ∧ (0 : ℝ) < ((north : S2) : E3) 2) ∨
            (h = g * b ∧ (((north : S2) : E3) 2) < 0))
        norm_num [north]
    | pair h x =>
        change
          ((h = g ∧ 0 < (x : E3) 2) ∨ (h = g * b ∧ (x : E3) 2 < 0)) ↔
          ((h * b = g ∧ 0 < ((-x : S2) : E3) 2) ∨
            (h * b = g * b ∧ ((-x : S2) : E3) 2 < 0))
        change
          ((h = g ∧ 0 < (x : E3) 2) ∨ (h = g * b ∧ (x : E3) 2 < 0)) ↔
          ((h * b = g ∧ 0 < -(x : E3) 2) ∨
            (h * b = g * b ∧ -(x : E3) 2 < 0))
        constructor
        · rintro (hx | hx)
          · right
            exact ⟨congrArg (fun q => q * b) hx.1, neg_lt_zero.mpr hx.2⟩
          · left
            refine ⟨?_, neg_pos.mpr hx.2⟩
            calc h * b = (g * b) * b := congrArg (fun q => q * b) hx.1
              _ = g := by rw [mul_assoc, hbb, mul_one]
        · rintro (hx | hx)
          · right
            refine ⟨?_, neg_pos.mp hx.2⟩
            calc h = (h * b) * b := by rw [mul_assoc, hbb, mul_one]
              _ = g * b := congrArg (fun q => q * b) hx.1
          · left
            exact ⟨mul_right_cancel hx.1, neg_lt_zero.mp hx.2⟩
  · intro k hk
    obtain ⟨v, hv, hkv⟩ := hk
    rcases v with ⟨h, t⟩ | ⟨h, x⟩
    · change
        ((h = g ∧ (t : ℝ) < 1 / 2) ∨ (h = g * a⁻¹ ∧ 1 / 2 < (t : ℝ))) at hv
      change
        ((k * h = g ∧ (t : ℝ) < 1 / 2) ∨
          (k * h = g * a⁻¹ ∧ 1 / 2 < (t : ℝ))) at hkv
      rcases hv with hv | hv <;> rcases hkv with hw | hw
      · apply mul_right_cancel (b := h)
        simpa using hw.1.trans hv.1.symm
      · linarith [hv.2, hw.2]
      · linarith [hv.2, hw.2]
      · apply mul_right_cancel (b := h)
        simpa using hw.1.trans hv.1.symm
    · change
        ((h = g ∧ 0 < (x : E3) 2) ∨ (h = g * b ∧ (x : E3) 2 < 0)) at hv
      change
        ((k * h = g ∧ 0 < (x : E3) 2) ∨
          (k * h = g * b ∧ (x : E3) 2 < 0)) at hkv
      rcases hv with hv | hv <;> rcases hkv with hw | hw
      · apply mul_right_cancel (b := h)
        simpa using hw.1.trans hv.1.symm
      · linarith [hv.2, hw.2]
      · linarith [hv.2, hw.2]
      · apply mul_right_cancel (b := h)
        simpa using hw.1.trans hv.1.symm

/-- **Leaf.**  Disjoint-translate neighbourhood of a non-pole sphere point:
`V = inr ({g} × B) ∪ inr ({g b} × -B)` with `B = ball x r`, `r` as in
`chain_local_regular`.  Saturated under `pair` (uses `b * b = 1`), avoids all
vertex points; `k • V ∩ V ≠ ∅` gives `k g = g`, `k g b = g b`, or a point of
`B ∩ -B = ∅`.  About 100 lines. -/
lemma tree_local_sphere (g : G) (x : S2) (hN : x ≠ north) (hS : x ≠ south) :
    ∃ V : Set TreeZ, IsOpen V ∧ .inr (g, x) ∈ V ∧ Saturated TreeRel V ∧
      ∀ k : G, (∃ v ∈ V, k • v ∈ V) → k = 1 := by
  sorry

lemma tree_local (z : TreeZ) :
    ∃ V : Set TreeZ, IsOpen V ∧ z ∈ V ∧ Saturated TreeRel V ∧
      ∀ k : G, (∃ v ∈ V, k • v ∈ V) → k = 1 := by
  have hbb := G_facts.2.2.1
  rcases z with ⟨g, t⟩ | ⟨g, x⟩
  · by_cases h0 : (t : ℝ) = 0
    · have : t = 0 := Subtype.ext h0
      subst this
      obtain ⟨V, h1, h2, -, -, -, h6, h7⟩ := tree_local_vertex g
      exact ⟨V, h1, h2, h6, h7⟩
    by_cases h1 : (t : ℝ) = 1
    · have : t = 1 := Subtype.ext h1
      subst this
      obtain ⟨V, hV1, -, h3, -, -, h6, h7⟩ := tree_local_vertex (g * a)
      refine ⟨V, hV1, ?_, h6, h7⟩
      simpa [mul_assoc] using h3
    exact tree_local_edge g t h0 h1
  · by_cases hN : x = north
    · subst hN
      obtain ⟨V, h1, -, -, h4, -, h6, h7⟩ := tree_local_vertex g
      exact ⟨V, h1, h4, h6, h7⟩
    by_cases hS : x = south
    · subst hS
      obtain ⟨V, h1, -, -, -, h5, h6, h7⟩ := tree_local_vertex (g * b)
      refine ⟨V, h1, ?_, h6, h7⟩
      simpa [mul_assoc, hbb] using h5
    exact tree_local_sphere g x hN hS

theorem lineSphereTree_isCoveringMap :
    IsCoveringMap (quotLift TreeRel treeF treeF_rel) :=
  isCoveringMap_quotLift_of_deck TreeRel treeRel_smul treeF treeF_isQuotientMap
    treeF_rel treeF_smul treeF_fiber tree_local

/-! ### Simple connectivity of the tree -/

/-- Membership in the star of the vertex `g`: the edge starting at `g`
without its far end, the edge ending at `g` without its far end, and the
sphere through `g` without its other vertex (copy `g` minus `south`, copy
`g b` minus `north`). -/
def treeStarPred (g : G) : TreeZ → Prop
  | .inl (h, t) => (h = g ∧ (t : ℝ) < 1) ∨ (h = g * a⁻¹ ∧ 0 < (t : ℝ))
  | .inr (h, x) => (h = g ∧ x ≠ south) ∨ (h = g * b ∧ x ≠ north)

def treeStar (g : G) : Set TreeZ := {z | treeStarPred g z}

/-- `(1 - s) t`. -/
def towardZero (s t : unitInterval) : unitInterval :=
  ⟨(1 - (s : ℝ)) * t, by
    constructor
    · exact mul_nonneg (by linarith [unitInterval.le_one s]) (unitInterval.nonneg t)
    · nlinarith [unitInterval.le_one s, unitInterval.nonneg s, unitInterval.le_one t,
        unitInterval.nonneg t]⟩

/-- `(1 - s) t + s`. -/
def towardOne (s t : unitInterval) : unitInterval :=
  ⟨(1 - (s : ℝ)) * t + s, by
    constructor
    · nlinarith [unitInterval.le_one s, unitInterval.nonneg s, unitInterval.nonneg t]
    · nlinarith [unitInterval.le_one s, unitInterval.nonneg s, unitInterval.le_one t,
        unitInterval.nonneg t]⟩

open Classical in
/-- Contraction of `treeStar g` to the vertex `g`: the outgoing edge shrinks
to `0`, other edges to `1`; sphere copy `g` is pushed to `north`, other copies
to `south` (so the antipodal pair relation is respected,
`spherePush_spec`). -/
noncomputable def treeContraction (g : G) : unitInterval × TreeZ → TreeZ
  | (s, .inl (h, t)) => .inl (h, if h = g then towardZero s t else towardOne s t)
  | (s, .inr (h, x)) => .inr (h, if h = g then spherePush north (s, x) else spherePush south (s, x))

/-- **Leaf.**  `treeStar g` is open and saturated (class-by-class check as in
the docstring of `treeStarPred`; uses `a ≠ 1`, `b * b = 1` from `G_facts`).
About 60 lines. -/
lemma treeStar_open_saturated (g : G) :
    IsOpen (treeStar g) ∧ Saturated TreeRel (treeStar g) := by
  sorry

/-- **Leaf.**  Each tree star is simply connected.

Route.  `isSimplyConnected_image_of_contraction` with `H = treeContraction g`,
`z₀ = inl (g, 0)`.  The branches are separated by the labels (`g a⁻¹ ≠ g`,
`g b ≠ g` from `G_facts`); continuity is per summand and per label (`G`
discrete), with `spherePush_continuousOn`.  `hresp`: vertex points are fixed;
for `pair` use `spherePush_spec` (`spherePush south (s, -x) =
-spherePush north (s, x)`) and `TreeRel.pair`.  About 130 lines. -/
-- BEGIN SEAT AREA
lemma treeStar_isSimplyConnected_aux_open_saturated (g : G) :
    IsOpen (treeStar g) ∧ Saturated TreeRel (treeStar g) := by
  have hset : treeStar g =
      Sum.inl '' (({g} ×ˢ {t : unitInterval | (t : ℝ) < 1}) ∪
        ({g * a⁻¹} ×ˢ {t : unitInterval | 0 < (t : ℝ)})) ∪
      Sum.inr '' (({g} ×ˢ ({south}ᶜ : Set S2)) ∪
        ({g * b} ×ˢ ({north}ᶜ : Set S2))) := by
    ext z
    rcases z with z | z <;> simp [treeStar, treeStarPred]
  constructor
  · rw [hset]
    apply IsOpen.union
    · apply isOpenMap_inl _
      exact ((isOpen_discrete {g}).prod (isOpen_lt continuous_subtype_val continuous_const)).union
        ((isOpen_discrete {g * a⁻¹}).prod (isOpen_lt continuous_const continuous_subtype_val))
    · apply isOpenMap_inr _
      exact ((isOpen_discrete {g}).prod isOpen_compl_singleton).union
        ((isOpen_discrete {g * b}).prod isOpen_compl_singleton)
  · intro z w hzw
    have ha : a ≠ 1 := G_facts.1
    have hb : b ≠ 1 := G_facts.2.1
    have hbb : b * b = 1 := G_facts.2.2.1
    cases hzw with
    | edge h =>
        change (((h = g ∧ (1 : ℝ) < 1) ∨ (h = g * a⁻¹ ∧ 0 < (1 : ℝ))) ↔
          ((h * a = g ∧ (0 : ℝ) < 1) ∨ (h * a = g * a⁻¹ ∧ 0 < (0 : ℝ))))
        simp only [lt_self_iff_false, and_false, false_or, zero_lt_one, and_true]
        constructor
        · rintro rfl
          simp
        · intro hh
          apply mul_right_cancel (b := a)
          simpa [mul_assoc] using hh
    | vertex h =>
        change (((h = g ∧ (0 : ℝ) < 1) ∨ (h = g * a⁻¹ ∧ 0 < (0 : ℝ))) ↔
          ((h = g ∧ north ≠ south) ∨ (h = g * b ∧ north ≠ north)))
        simp [north_ne_south]
    | pair h x =>
        change (((h = g ∧ x ≠ south) ∨ (h = g * b ∧ x ≠ north)) ↔
          ((h * b = g ∧ -x ≠ south) ∨ (h * b = g * b ∧ -x ≠ north)))
        constructor
        · rintro (⟨rfl, hx⟩ | ⟨rfl, hx⟩)
          · right
            refine ⟨rfl, ?_⟩
            intro he; apply hx
            simpa [neg_north] using congrArg Neg.neg he
          · left
            refine ⟨by simp [mul_assoc, hbb], ?_⟩
            intro he; apply hx
            simpa [neg_south] using congrArg Neg.neg he
        · rintro (⟨hh, hx⟩ | ⟨hh, hx⟩)
          · right
            refine ⟨?_, ?_⟩
            · simpa [← hh, mul_assoc, hbb]
            · intro he; apply hx
              simpa [he, neg_north]
          · left
            refine ⟨?_, ?_⟩
            exact mul_right_cancel hh
            intro he; apply hx
            simpa [he, neg_south]

lemma treeStar_isSimplyConnected (g : G) :
    IsSimplyConnected (qmk TreeRel '' treeStar g) := by
  sorry
/-
  refine isSimplyConnected_image_of_contraction (R := TreeRel) (treeStar g)
    (treeStar_isSimplyConnected_aux_open_saturated g).1
    (treeStar_isSimplyConnected_aux_open_saturated g).2 (treeContraction g)
    ?_ ?_ ?_ (.inl (g, 0)) ?_ ?_ ?_
  · intro q hq
    rcases q.2 with z | z
    · rcases z with ⟨h, t⟩
      by_cases hh : h = g
      · subst h
        let F : unitInterval × TreeZ → TreeZ := fun y =>
          .inl (g, towardZero y.1 (y.2.elim (fun z : G × unitInterval => z.2)
            (fun _ => t)))
        have hF : Continuous F := by
          apply continuous_inl.comp
          apply Continuous.prodMk continuous_const
          apply Continuous.subtype_mk
          change Continuous (fun y => (1 - (y.1 : ℝ)) *
            ((y.2.elim (fun z : G × unitInterval => z.2) (fun _ => t)) : ℝ))
          fun_prop
        apply hF.continuousAt.continuousWithinAt.congr_of_eventuallyEq
        · filter_upwards [isOpenMap_inl (isOpen_discrete ({g} : Set G)).prod
              isOpen_univ |>.mem_nhds ⟨rfl, Set.mem_univ _⟩ |> continuous_snd.isOpen_preimage.mem_nhds] with y hy
          rcases y.2 with z | z
          · rcases hy with ⟨-, k, hk, -, rfl⟩
            simpa [F, treeContraction] using hk
          · exact (hy.1.elim)
        · simp [F, treeContraction]
      · let F : unitInterval × TreeZ → TreeZ := fun y =>
          .inl (h, towardOne y.1 (y.2.elim (fun z : G × unitInterval => z.2)
            (fun _ => t)))
        have hF : Continuous F := by
          apply continuous_inl.comp
          apply Continuous.prodMk continuous_const
          apply Continuous.subtype_mk
          change Continuous (fun y => (1 - (y.1 : ℝ)) *
            ((y.2.elim (fun z : G × unitInterval => z.2) (fun _ => t)) : ℝ) + y.1)
          fun_prop
        apply hF.continuousAt.continuousWithinAt.congr_of_eventuallyEq
        · filter_upwards [isOpenMap_inl ((isOpen_discrete ({h} : Set G)).prod
              isOpen_univ) |>.mem_nhds ⟨rfl, Set.mem_univ _⟩ |> continuous_snd.isOpen_preimage.mem_nhds] with y hy
          rcases y.2 with z | z
          · rcases hy with ⟨-, k, hk, -, rfl⟩
            simpa [F, treeContraction, hh] using hk
          · exact hy.1.elim
        · simp [F, treeContraction, hh]
    · rcases z with ⟨h, x⟩
      by_cases hh : h = g
      · subst h
        sorry
      · sorry
  · intro s z hz
    rcases z with ⟨h, t⟩ | ⟨h, x⟩
    · change (h = g ∧ ((towardZero s t : unitInterval) : ℝ) < 1) ∨
          (h = g * a⁻¹ ∧ 0 < ((towardOne s t : unitInterval) : ℝ))
      change (h = g ∧ (t : ℝ) < 1) ∨ (h = g * a⁻¹ ∧ 0 < (t : ℝ)) at hz
      rcases hz with ⟨rfl, ht⟩ | ⟨hh, ht⟩
      · left; exact ⟨rfl, by simp [towardZero]; nlinarith [unitInterval.nonneg t,
          unitInterval.nonneg s, unitInterval.le_one s]⟩
      · right; refine ⟨hh, ?_⟩
        have hne : h ≠ g := by rintro rfl; exact G_facts.1 (by simpa using hh)
        simp [treeContraction, hne, towardOne]
        nlinarith [unitInterval.nonneg s, unitInterval.le_one s]
    · change (h = g ∧ (treeContraction g (s, .inr (h, x))).getRight ≠ south) ∨
          (h = g * b ∧ (treeContraction g (s, .inr (h, x))).getRight ≠ north)
      change (h = g ∧ x ≠ south) ∨ (h = g * b ∧ x ≠ north) at hz
      rcases hz with ⟨rfl, hx⟩ | ⟨hh, hx⟩
      · left; refine ⟨rfl, ?_⟩
        simpa [treeContraction, neg_north] using
          (spherePush_spec north).2.2.2.1 s x (by simpa [neg_north] using hx)
      · right; refine ⟨hh, ?_⟩
        have hne : h ≠ g := by rintro rfl; exact G_facts.2.1 (by simpa using hh)
        simpa [treeContraction, hne, neg_south] using
          (spherePush_spec south).2.2.2.1 s x (by simpa [neg_south] using hx)
  · intro z hz
    rcases z with ⟨h, t⟩ | ⟨h, x⟩ <;>
      simp [treeContraction, (spherePush_spec north).1, (spherePush_spec south).1,
        towardZero, towardOne]
  · change treeStarPred g (.inl (g, 0))
    simp [treeStarPred]
  · intro z hz
    rcases z with ⟨h, t⟩ | ⟨h, x⟩
    · change (h = g ∧ (t : ℝ) < 1) ∨ (h = g * a⁻¹ ∧ 0 < (t : ℝ)) at hz
      rcases hz with ⟨rfl, ht⟩ | ⟨hh, ht⟩
      · simp [treeContraction, towardZero]
      · have hne : h ≠ g := by rintro rfl; exact G_facts.1 (by simpa using hh)
        simp [treeContraction, hne, towardOne]
        apply Quotient.sound
        rw [hh]
        exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (TreeRel.edge (g * a⁻¹)))
    · change (h = g ∧ x ≠ south) ∨ (h = g * b ∧ x ≠ north) at hz
      rcases hz with ⟨rfl, hx⟩ | ⟨hh, hx⟩
      · simp [treeContraction, (spherePush_spec north).2.1 _ (by simpa [neg_north] using hx)]
        exact Quotient.sound (Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ (TreeRel.vertex g)))
      · have hne : h ≠ g := by rintro rfl; exact G_facts.2.1 (by simpa using hh)
        simp [treeContraction, hne, (spherePush_spec south).2.1 _
          (by simpa [neg_south] using hx)]
        rw [hh]
        exact Quotient.sound (Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (TreeRel.pair g north)))
          (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (TreeRel.vertex g))))
  · intro s z w hz hzw
    cases hzw with
    | edge h =>
        have hh : h = g := by
          change (h = g ∧ (1 : ℝ) < 1) ∨ (h = g * a⁻¹ ∧ 0 < (1 : ℝ)) at hz
          rcases hz with hz | hz
          · norm_num at hz
          · exact mul_right_cancel hz.1
        subst h
        simp [treeContraction, towardZero, towardOne]
        exact Quotient.sound (Relation.EqvGen.rel _ _ (TreeRel.edge g))
    | vertex h =>
        have hh : h = g := by
          change (h = g ∧ (0 : ℝ) < 1) ∨ (h = g * a⁻¹ ∧ 0 < (0 : ℝ)) at hz
          simpa using hz
        subst h
        simp [treeContraction, towardZero, (spherePush_spec north).2.2.1]
        exact Quotient.sound (Relation.EqvGen.rel _ _ (TreeRel.vertex g))
    | pair h x =>
        change (h = g ∧ x ≠ south) ∨ (h = g * b ∧ x ≠ north) at hz
        rcases hz with ⟨rfl, hx⟩ | ⟨hh, hx⟩
        · have hbg : g * b ≠ g := by intro e; exact G_facts.2.1 (mul_left_cancel e)
          simp [treeContraction, hbg, (spherePush_spec north).2.2.2.2]
          exact Quotient.sound (Relation.EqvGen.rel _ _
            (TreeRel.pair g (spherePush north (s, x))))
        · have hne : h ≠ g := by rintro rfl; exact G_facts.2.1 (by simpa using hh)
          have hhb : h * b = g := by rw [hh, mul_assoc, G_facts.2.2.1, mul_one]
          simp [treeContraction, hne, hhb, (spherePush_spec south).2.2.2.2]
          exact Quotient.sound (Relation.EqvGen.rel _ _
            (TreeRel.pair h (spherePush south (s, x))))
-/
-- END SEAT AREA

/-- **Leaf.**  Stars meet only along Cayley edges, and adjacent stars meet in
a path-connected set.

Route.  `Saturated.image_inter`, then label bookkeeping with `G_facts`:
`treeStar g ∩ treeStar h` contains an edge point only if `h = g a` or
`h = g a⁻¹`, a sphere point only if `h = g b`.
`treeStar g ∩ treeStar (g a) = inl ({g} × (0,1))` (path connected:
image of an interval), `treeStar g ∩ treeStar (g b)` is the copy-`g` sphere
minus both poles together with its antipodal copy, whose image is the image of
`sphere_compl_poles_isPathConnected` under `x ↦ qmk (inr (g, x))`.
About 120 lines. -/
lemma treeStar_inter (g h : G) :
    ((qmk TreeRel '' treeStar g ∩ qmk TreeRel '' treeStar h).Nonempty →
      h = g ∨ h = g * a ∨ h = g * a⁻¹ ∨ h = g * b) ∧
    IsPathConnected (qmk TreeRel '' treeStar g ∩ qmk TreeRel '' treeStar (g * a)) ∧
    IsPathConnected (qmk TreeRel '' treeStar g ∩ qmk TreeRel '' treeStar (g * b)) := by
  sorry

lemma treeStar_cover : ⋃ g, qmk TreeRel '' treeStar g = univ := by
  apply eq_univ_of_forall
  rintro ⟨z⟩
  rcases z with ⟨h, t⟩ | ⟨h, x⟩
  · by_cases ht : (t : ℝ) < 1
    · exact mem_iUnion.mpr ⟨h, .inl (h, t), Or.inl ⟨rfl, ht⟩, rfl⟩
    · refine mem_iUnion.mpr ⟨h * a, .inl (h, t), Or.inr ⟨by simp [mul_assoc], ?_⟩, rfl⟩
      linarith [unitInterval.le_one t]
  · by_cases hx : x = south
    · subst hx
      refine mem_iUnion.mpr ⟨h * b, .inr (h, south), Or.inr ⟨?_, north_ne_south.symm⟩, rfl⟩
      rw [mul_assoc, G_facts.2.2.1, mul_one]
    · exact mem_iUnion.mpr ⟨h, .inr (h, x), Or.inl ⟨rfl, hx⟩, rfl⟩

/-! ### The Cayley graph of `ℤ * ℤ/2` is a tree -/

/-- Letters `a`, `a⁻¹`, `b`. -/
inductive Letter
  | a | ai | b
  deriving DecidableEq

def Letter.inv : Letter → Letter
  | .a => .ai
  | .ai => .a
  | .b => .b

def Letter.toG : Letter → G
  | .a => APMT99A02.a
  | .ai => APMT99A02.a⁻¹
  | .b => APMT99A02.b

/-- No adjacent cancelling pair (`a a⁻¹`, `a⁻¹ a`, `b b`). -/
def Reduced (w : List Letter) : Prop := w.IsChain fun x y => y ≠ x.inv

def wordEval (w : List Letter) : G := (w.map Letter.toG).prod

/-- **Leaf (normal form for `ℤ * ℤ/2`; LIBRARY-borderline).**  Every element
of `G` is the value of exactly one reduced word.

Route (van der Waerden).  Existence: `Monoid.Coprod.induction_on` /
closure under multiplication by the letters (left-multiply a reduced word and
cancel at the head).  Uniqueness: let `G` act on the subtype of reduced
words by `cons'` (`s :: w`, cancelling a head `s.inv`); `a` acts by an
`Equiv.Perm` with inverse `cons' ai`, `b` by an involution, giving
`Multiplicative ℤ →* Perm` (`zpowersHom`) and
`Multiplicative (ZMod 2) →* Perm` (from `b² = 1`), combined by
`Monoid.Coprod.lift`.  Then `wordEval w • [] = w` for reduced `w`, so
`wordEval` is injective on reduced words.  About 200 lines. -/
lemma G_normalForm : ∀ g : G, ∃! w : List Letter, Reduced w ∧ wordEval w = g := by
  sorry

/-- **Leaf (Cayley tree of `ℤ * ℤ/2`).**  With `depth g` the length of the
reduced word of `g` and `parent g = g · (last letter)⁻¹`: depth zero only at
`1`, the parent is a neighbour of smaller depth, and of two neighbours one is
the parent of the other.

Route.  From `hNF`, with `w` the reduced word of `g` and `s` a letter: the
reduced word of `g * s.toG` is `w.dropLast` if `w.getLast? = some s.inv`,
and `w ++ [s]` otherwise (both are reduced and evaluate correctly; apply
uniqueness).  Distinctness of the three neighbours uses `G_facts`
(`a * a ≠ 1`, `a ≠ b`, `a⁻¹ ≠ b`).  About 120 lines. -/
lemma G_cayleyTree
    (hNF : ∀ g : G, ∃! w : List Letter, Reduced w ∧ wordEval w = g) :
    ∃ (depth : G → ℕ) (parent : G → G),
      (∀ g, depth g = 0 ↔ g = 1) ∧
      (∀ g, g ≠ 1 → depth (parent g) + 1 = depth g ∧
        (parent g = g * a ∨ parent g = g * a⁻¹ ∨ parent g = g * b)) ∧
      (∀ g h, (h = g * a ∨ h = g * a⁻¹ ∨ h = g * b) →
        (g ≠ 1 ∧ h = parent g) ∨ (h ≠ 1 ∧ g = parent h)) := by
  sorry

theorem lineSphereTree_simplyConnected : SimplyConnectedSpace LineSphereTree := by
  obtain ⟨depth, parent, hd0, hpar, hadj⟩ := G_cayleyTree G_normalForm
  obtain ⟨ha1, -, hbb, -, -, -, -⟩ := G_facts
  let U : G → Set LineSphereTree := fun g => qmk TreeRel '' treeStar g
  have hinter_comm : ∀ g h, U g ∩ U h = U h ∩ U g := fun g h => inter_comm _ _
  refine TreeCover.simplyConnectedSpace (ι := G)
    { U := U
      depth := depth
      parent := parent
      root := 1
      isOpen := fun g =>
        (treeStar_open_saturated g).2.isOpen_image (treeStar_open_saturated g).1
      simplyConnected := treeStar_isSimplyConnected
      cover := treeStar_cover
      depth_eq_zero := hd0
      depth_parent := fun g hg => (hpar g hg).1
      inter_parent := ?_
      inter_adj := ?_ }
  · intro g hg
    rcases (hpar g hg).2 with h | h | h <;> rw [h]
    · exact (treeStar_inter g g).2.1
    · have := (treeStar_inter (g * a⁻¹) g).2.1
      rw [mul_assoc, inv_mul_cancel, mul_one] at this
      rwa [hinter_comm]
    · exact (treeStar_inter g g).2.2
  · intro g h hgh hne
    rcases (treeStar_inter g h).1 hne with e | e | e | e
    · exact absurd e.symm hgh
    all_goals exact hadj g h (by tauto)

/-! ## 7. Part (a) simple connectivity -/

theorem sphereChain_simplyConnected : SimplyConnectedSpace SphereChain :=
  chainTreeCover.simplyConnectedSpace

end APMT99A02


theorem apm_t99a02 :
    (SimplyConnectedSpace APMT99A02.SphereChain ∧
      ∃ p : APMT99A02.SphereChain → ProjectivePlaneWedge,
        Function.Surjective p ∧ IsCoveringMap p) ∧
    (SimplyConnectedSpace APMT99A02.LineSphereTree ∧
      ∃ p : APMT99A02.LineSphereTree → APMT99A02.CircleWedgeProjectivePlane,
        Function.Surjective p ∧ IsCoveringMap p) := by
  exact ⟨⟨APMT99A02.sphereChain_simplyConnected,
      ⟨APMT99A02.quotLift APMT99A02.ChainRel APMT99A02.chainF APMT99A02.chainF_rel,
        APMT99A02.quotLift_surjective _ _ _ APMT99A02.chainF_isQuotientMap.surjective,
        APMT99A02.sphereChain_isCoveringMap⟩⟩,
    ⟨APMT99A02.lineSphereTree_simplyConnected,
      ⟨APMT99A02.quotLift APMT99A02.TreeRel APMT99A02.treeF APMT99A02.treeF_rel,
        APMT99A02.quotLift_surjective _ _ _ APMT99A02.treeF_isQuotientMap.surjective,
        APMT99A02.lineSphereTree_isCoveringMap⟩⟩⟩
