import ConstructionTargets.SphereHomology

/-!
# The antipodal map in singular sphere homology

This file begins the calculation of the antipodal action with the literal
zero-sphere and records the precise naturality boundary for the production
sphere shift.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.SphereAntipodalHomology

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.SphereHomology
open ConstructionTargets.T02A06HemisphereExcision
open T02A06

abbrev SphereZero := Sphere 0
abbrev IntGroup := AddCommGrpCat.of ℤ

def sphereAntipodal (n : ℕ) : C(Sphere n, Sphere n) where
  toFun x := ⟨-x.1, by simpa [Metric.mem_sphere, dist_zero_right] using x.2⟩
  continuous_toFun :=
    (continuous_neg.comp continuous_subtype_val).subtype_mk _

@[simp] theorem sphereAntipodal_apply_val (n : ℕ) (x : Sphere n) :
    (sphereAntipodal n x).1 = -x.1 := by simp [sphereAntipodal]

@[simp] theorem sphereAntipodal_involutive (n : ℕ) (x : Sphere n) :
    sphereAntipodal n (sphereAntipodal n x) = x := by
  apply Subtype.ext
  simp [Metric.mem_sphere, dist_zero_right]

def sphereZeroPositive : SphereZero := by
  refine ⟨PiLp.single 2 (0 : Fin 1) 1, ?_⟩
  simp [Metric.mem_sphere, dist_zero_right]

def sphereZeroNegative : SphereZero := by
  refine ⟨PiLp.single 2 (0 : Fin 1) (-1), ?_⟩
  simp

@[simp] theorem sphereAntipodal_sphereZeroPositive :
    sphereAntipodal 0 sphereZeroPositive = sphereZeroNegative := by
  apply Subtype.ext
  ext i
  fin_cases i
  simp [sphereZeroPositive, sphereZeroNegative]

@[simp] theorem sphereAntipodal_sphereZeroNegative :
    sphereAntipodal 0 sphereZeroNegative = sphereZeroPositive := by
  apply Subtype.ext
  ext i
  fin_cases i
  simp [sphereZeroPositive, sphereZeroNegative]

abbrev SphereZeroH0 := SingularHomology 0 (TopCat.of SphereZero)
abbrev SphereZeroCoproduct := ∐ fun _ : SphereZero ↦ IntGroup

noncomputable def sphereZeroH0Iso : SphereZeroH0 ≅ SphereZeroCoproduct :=
  directDiscreteH0Iso AddCommGrpCat IntGroup SphereZero

noncomputable def sphereZeroAntipodalH0 : SphereZeroH0 ⟶ SphereZeroH0 :=
  HomologicalComplex.homologyMap
    (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
      IntGroup).map (TopCat.ofHom (sphereAntipodal 0))) 0

noncomputable def sphereZeroCoordinateAntipodal :
    SphereZeroCoproduct ⟶ SphereZeroCoproduct :=
  Limits.Sigma.map'
    (f := fun _ : SphereZero ↦ IntGroup)
    (g := fun _ : SphereZero ↦ IntGroup)
    (sphereAntipodal 0) (fun _ ↦ 𝟙 IntGroup)

/-- In direct point coordinates, the zero-sphere antipodal homology map is
the permutation of the two point summands. -/
theorem sphereZeroAntipodalH0_coordinates :
    sphereZeroH0Iso.inv ≫ sphereZeroAntipodalH0 =
      sphereZeroCoordinateAntipodal ≫ sphereZeroH0Iso.inv := by
  exact directDiscreteH0Iso_naturality AddCommGrpCat IntGroup
    (TopCat.ofHom (sphereAntipodal 0))

/-- The oriented reduced zero-sphere generator: negative point minus positive
point. -/
noncomputable def sphereZeroOrientedDifference :
    IntGroup ⟶ SphereZeroCoproduct :=
  Limits.Sigma.ι (fun _ : SphereZero ↦ IntGroup) sphereZeroNegative -
    Limits.Sigma.ι (fun _ : SphereZero ↦ IntGroup) sphereZeroPositive

/-- The antipodal permutation acts by `-1` on the oriented reduced
zero-sphere coordinate. -/
theorem sphereZeroCoordinateAntipodal_orientedDifference :
    sphereZeroOrientedDifference ≫ sphereZeroCoordinateAntipodal =
      -sphereZeroOrientedDifference := by
  simp [sphereZeroOrientedDifference, sphereZeroCoordinateAntipodal,
    Preadditive.sub_comp]

/-- Homology-level form: after direct H₀ coordinates, the antipodal map sends
the oriented reduced generator to its negative. -/
theorem sphereZeroAntipodalH0_orientedDifference :
    sphereZeroOrientedDifference ≫ sphereZeroH0Iso.inv ≫
        sphereZeroAntipodalH0 ≫ sphereZeroH0Iso.hom =
      -sphereZeroOrientedDifference := by
  slice_lhs 2 3 => rw [sphereZeroAntipodalH0_coordinates]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact sphereZeroCoordinateAntipodal_orientedDifference

/-! ## The first relative-pair naturality square -/

/-- The complement of the south pole, in the same final-coordinate model as
the north-pole complement used by `spherePositiveHomologyShift`. -/
def southPoleComplement (n : ℕ) : Set (Sphere n) :=
  {x | -1 < sphereHeight n x}

theorem sphereHeight_antipodal (n : ℕ) (x : Sphere n) :
    sphereHeight n (sphereAntipodal n x) = -sphereHeight n x := by
  simp [sphereHeight, sphereAntipodal]

theorem sphereAntipodal_mapsTo_north_south (n : ℕ) :
    Set.MapsTo (sphereAntipodal n) (northPoleComplement n)
      (southPoleComplement n) := by
  intro x hx
  change -1 < sphereHeight n (sphereAntipodal n x)
  rw [sphereHeight_antipodal]
  exact neg_lt_neg hx

noncomputable def antipodalNorthSouthRelativeMap (n : ℕ) :=
  relativeSingularMap (northPoleComplement n) (southPoleComplement n)
    (sphereAntipodal n) (sphereAntipodal_mapsTo_north_south n)

noncomputable def antipodalAbsoluteMap (n : ℕ) :
    SingularChains (TopCat.of (Sphere n)) ⟶ SingularChains (TopCat.of (Sphere n)) :=
  ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
    IntGroup).map (TopCat.ofHom (sphereAntipodal n))

/-- The absolute-to-relative projection square for antipodal reflection.  The
target pair is necessarily the south-pole pair, not the north-pole pair used
again by the production shift. -/
theorem antipodal_relativeProjection_naturality (n : ℕ) :
    antipodalAbsoluteMap n ≫
        relativeSingularProjection (southPoleComplement n) =
      relativeSingularProjection (northPoleComplement n) ≫
        antipodalNorthSouthRelativeMap n :=
  by
    simpa [antipodalAbsoluteMap] using
      relativeSingularMap_projection_naturality
        (northPoleComplement n) (southPoleComplement n)
        (sphereAntipodal n) (sphereAntipodal_mapsTo_north_south n)

/-- Homology-level form of the first component square. -/
theorem antipodal_relativeProjection_homology_naturality (n k : ℕ) :
    HomologicalComplex.homologyMap (antipodalAbsoluteMap n) k ≫
        HomologicalComplex.homologyMap
          (relativeSingularProjection (southPoleComplement n)) k =
      HomologicalComplex.homologyMap
          (relativeSingularProjection (northPoleComplement n)) k ≫
        HomologicalComplex.homologyMap (antipodalNorthSouthRelativeMap n) k := by
  rw [← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp,
    antipodal_relativeProjection_naturality]

#print axioms sphereZeroAntipodalH0_coordinates
#print axioms sphereZeroCoordinateAntipodal_orientedDifference
#print axioms sphereZeroAntipodalH0_orientedDifference
#print axioms antipodal_relativeProjection_naturality
#print axioms antipodal_relativeProjection_homology_naturality

end ConstructionTargets.SphereAntipodalHomology
