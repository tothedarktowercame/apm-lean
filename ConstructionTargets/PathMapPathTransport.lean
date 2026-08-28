import ConstructionTargets.FundamentalGroupoidTwoOpenDescent

/-!
# Explicit endpoint transport for paths and two-open descent

The results here expose the endpoint casts required when propositionally equal
subdivision parameters produce paths with propositionally equal endpoint
types.  They avoid rewriting dependent endpoints underneath a functor map.
-/

open CategoryTheory
open scoped unitInterval

noncomputable section

namespace ConstructionTargets.PathMapPathTransport

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent

variable {X : Type*} [TopologicalSpace X]

/-- Subpaths at propositionally equal parameters agree after the endpoint
casts are displayed explicitly. -/
theorem subpath_cast_of_parameter_eq {x y : X} (p : Path x y)
    {a b a' b' : unitInterval} (ha : a = a') (hb : b = b') :
    (p.subpath a' b').cast (congrArg p ha) (congrArg p hb) =
      p.subpath a b := by
  subst a'
  subst b'
  rfl

variable {U V : Set X} {C : Type*} [Category C]

namespace TwoOpenDescentDatum

variable (D : @FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum X _ U V C _)

/-- `mapPath` of a cast path is the original map conjugated by the common
object-coordinate endpoint transports. -/
theorem mapPath_cast {b : Bool} {x y x' y' : X} (p : Path x y)
    (hx : x' = x) (hy : y' = y)
    (hp : ∀ t, p t ∈ twoChart U V b)
    (hp' : ∀ t, p.cast hx hy t ∈ twoChart U V b) :
    D.mapPath b (p.cast hx hy) hp' =
      eqToHom (congrArg D.obj hx) ≫ D.mapPath b p hp ≫
        eqToHom (congrArg D.obj hy).symm := by
  subst x'
  subst y'
  simp only [Path.cast_rfl_rfl]
  have : hp' = hp := Subsingleton.elim _ _
  subst this
  simp

/-- Propositionally equal subdivision parameters give conjugate `mapPath`
values, with both endpoint transports explicit. -/
theorem mapPath_subpath_parameter_eq {b : Bool} {x y : X} (p : Path x y)
    {a b' a' b'' : unitInterval} (ha : a = a') (hb : b' = b'')
    (hp : ∀ t, p.subpath a' b'' t ∈ twoChart U V b)
    (hp' : ∀ t, p.subpath a b' t ∈ twoChart U V b) :
    D.mapPath b (p.subpath a b') hp' =
      eqToHom (congrArg D.obj (congrArg p ha)) ≫
        D.mapPath b (p.subpath a' b'') hp ≫
        eqToHom (congrArg D.obj (congrArg p hb)).symm := by
  subst a'
  subst b''
  have : hp' = hp := Subsingleton.elim _ _
  subst this
  simp

#print axioms subpath_cast_of_parameter_eq
#print axioms TwoOpenDescentDatum.mapPath_cast
#print axioms TwoOpenDescentDatum.mapPath_subpath_parameter_eq

end TwoOpenDescentDatum

end ConstructionTargets.PathMapPathTransport
