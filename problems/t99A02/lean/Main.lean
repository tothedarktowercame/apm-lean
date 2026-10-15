import Mathlib
import ConstructionTargets.StatementSurfaceModels

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

theorem apm_t99a02 :
    (SimplyConnectedSpace APMT99A02.SphereChain ∧
      ∃ p : APMT99A02.SphereChain → ProjectivePlaneWedge,
        Function.Surjective p ∧ IsCoveringMap p) ∧
    (SimplyConnectedSpace APMT99A02.LineSphereTree ∧
      ∃ p : APMT99A02.LineSphereTree → APMT99A02.CircleWedgeProjectivePlane,
        Function.Surjective p ∧ IsCoveringMap p) := by
  sorry
