import ConstructionTargets.CoefficientChartPair
noncomputable section
namespace ConstructionTargets.CoefficientChartLocal
open CategoryTheory CategoryTheory.Limits
open CoefficientRadialPair CoefficientNeighborhoodLocal CoefficientChartPair
variable (R : Type) [CommRing R]
variable (m : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]
abbrev E := EuclideanSpace ℝ (Fin (m+2))
def coordinate (x : M) : E m := chartAt (E m) x x
def pointedTarget (x : M) : Set (E m) := {z | z + coordinate m x ∈ (chartAt (E m) x).target}
theorem pointed_open (x : M) : IsOpen (pointedTarget m x) :=
  (chartAt (E m) x).open_target.preimage (continuous_id.add continuous_const)
theorem pointed_zero (x : M) : 0 ∈ pointedTarget m x := by
  simp [pointedTarget, coordinate]

def translateTarget (x : M) : (chartAt (E m) x).target ≃ₜ pointedTarget m x where
  toFun y := ⟨y.val - coordinate m x, by simp [pointedTarget, y.property]⟩
  invFun z := ⟨z.val + coordinate m x, z.property⟩
  left_inv y := by ext; simp
  right_inv z := by ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def pointedChart (x : M) := (chartHomeo (m+2) x).trans (translateTarget m x)
theorem pointed_value (x : M) (y : (chartAt (E m) x).source) :
    (pointedChart m x y).val = chartAt (E m) x y.val - coordinate m x := rfl
theorem pointed_base (x : M) : (pointedChart m x (sourcePoint (m+2) x)).val = 0 := sub_self _

def H {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :=
  (CoefficientRelativeSmall.relativeChains R A).homology n

def sourceTransport (x : M) (n : ℕ) :=
  eqToIso (congrArg (fun A => H R A n) (source_deleted (m+2) x))
theorem pointed_deleted (x : M) : deleted (pointedChart m x (sourcePoint (m+2) x)) =
    localDeleted (pointedTarget m x) 0 := by
  ext y
  simp only [deleted, localDeleted, Set.mem_setOf_eq, ne_eq, Subtype.ext_iff, pointed_base]
def targetTransport (x : M) (n : ℕ) :=
  eqToIso (congrArg (fun A => H R A n) (pointed_deleted m x))

variable [T2Space M]
def localIso (x : M) : H R (deleted x) (m+2) ≅ ModuleCat.of R R :=
  (inclusionIso R (chartAt (E m) x).source x (chartAt (E m) x).open_source
    (source_member (m+2) x) (m+2)).symm ≪≫
  (sourceTransport R m x (m+2)).symm ≪≫
  homologyIso R (pointedChart m x) (sourcePoint (m+2) x) (m+2) ≪≫
  targetTransport R m x (m+2) ≪≫
  modelNormalization R m (pointedTarget m x) (pointed_open m x) (pointed_zero m x)

theorem forward_composite (x : M) : (localIso R m x).hom =
    (inclusionIso R (chartAt (E m) x).source x (chartAt (E m) x).open_source
      (source_member (m+2) x) (m+2)).inv ≫
    (sourceTransport R m x (m+2)).inv ≫
    HomologicalComplex.homologyMap
      (deletedMap R (pointedChart m x) (sourcePoint (m+2) x)) (m+2) ≫
    (targetTransport R m x (m+2)).hom ≫
    HomologicalComplex.homologyMap (inclusionMap R (pointedTarget m x) 0) (m+2) ≫
    (CoefficientModelLocal.localIso R m).hom := rfl

theorem inverse_left (x : M) : (localIso R m x).inv ≫ (localIso R m x).hom = 𝟙 _ :=
  (localIso R m x).inv_hom_id

theorem inverse_right (x : M) : (localIso R m x).hom ≫ (localIso R m x).inv = 𝟙 _ :=
  (localIso R m x).hom_inv_id

def generator (x : M) := (localIso R m x).inv.hom (1 : R)
theorem generator_normalization (x : M) : (localIso R m x).hom.hom (generator R m x) = 1 :=
  congrArg (fun f => f.hom (1 : R)) (localIso R m x).inv_hom_id

def integral_chart (m : ℕ) (x : E m) := localIso ℤ m x
def rational_chart (m : ℕ) (x : E m) := localIso ℚ m x

omit [T2Space M] in
 theorem pointed_projection (x : M) (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (deleted (sourcePoint (m+2) x)))).f n ≫
      (deletedMap R (pointedChart m x) (sourcePoint (m+2) x)).f n =
    (absoluteMap R (homeoMap (pointedChart m x))).f n ≫
      (cokernel.π (CoefficientRelativeSmall.subspaceMap R
        (deleted (pointedChart m x (sourcePoint (m+2) x))))).f n :=
  CoefficientRadialPair.projection_degree R (deleted (sourcePoint (m+2) x))
    (deleted (pointedChart m x (sourcePoint (m+2) x))) (homeoMap (pointedChart m x))
    (fun _ hy h => hy ((pointedChart m x).injective h)) n

omit [T2Space M] in
 theorem pointed_pair_inverse_right (x : M) :
    deletedMap R (pointedChart m x) (sourcePoint (m+2) x) ≫
      deletedInverse R (pointedChart m x) (sourcePoint (m+2) x) = 𝟙 _ :=
  pair_inverse_right R _ _
omit [T2Space M] in
 theorem pointed_pair_inverse_left (x : M) :
    deletedInverse R (pointedChart m x) (sourcePoint (m+2) x) ≫
      deletedMap R (pointedChart m x) (sourcePoint (m+2) x) = 𝟙 _ :=
  pair_inverse_left R _ _
omit [T2Space M] in
 theorem pointed_inverse_projection (x : M) (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R
        (deleted (pointedChart m x (sourcePoint (m+2) x))))).f n ≫
      (deletedInverse R (pointedChart m x) (sourcePoint (m+2) x)).f n =
    (absoluteMap R (homeoMap (pointedChart m x).symm)).f n ≫
      (cokernel.π (CoefficientRelativeSmall.subspaceMap R (deleted (sourcePoint (m+2) x)))).f n :=
  CoefficientRadialPair.projection_degree R
    (deleted (pointedChart m x (sourcePoint (m+2) x))) (deleted (sourcePoint (m+2) x))
    (homeoMap (pointedChart m x).symm) (fun y hy h => hy (by
      change (pointedChart m x).symm y = sourcePoint (m+2) x at h
      exact ((pointedChart m x).apply_symm_apply y).symm.trans (congrArg (pointedChart m x) h))) n

omit [T2Space M] in
 theorem pointed_pair_composite (x : M) :
    deletedMap R (pointedChart m x) (sourcePoint (m+2) x) =
      deletedMap R (chartHomeo (m+2) x) (sourcePoint (m+2) x) ≫
      deletedMap R (translateTarget m x) (chartHomeo (m+2) x (sourcePoint (m+2) x)) :=
by
  unfold deletedMap
  rw [← CoefficientPairNaturality.pair_comp]
  rfl

#print axioms pointed_inverse_projection
#print axioms pointed_pair_composite
#print axioms pointed_open
#print axioms pointed_zero
#print axioms translateTarget
#print axioms pointed_value
#print axioms pointed_base
#print axioms sourceTransport
#print axioms pointed_deleted
#print axioms targetTransport
#print axioms localIso
#print axioms forward_composite
#print axioms inverse_left
#print axioms inverse_right
#print axioms generator_normalization
#print axioms pointed_projection
#print axioms pointed_pair_inverse_left
#print axioms pointed_pair_inverse_right
#print axioms integral_chart
#print axioms rational_chart
end ConstructionTargets.CoefficientChartLocal
