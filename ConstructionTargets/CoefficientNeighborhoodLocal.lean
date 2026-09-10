import ConstructionTargets.CoefficientModelLocal
import ConstructionTargets.CoefficientExcision
noncomputable section
namespace ConstructionTargets.CoefficientNeighborhoodLocal
open CategoryTheory CategoryTheory.Limits
open CoefficientRadialPair SingularExcision
variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]
def deleted (x : X) : Set X := {y | y ≠ x}
def localDeleted (U : Set X) (x : X) : Set U := {u | u.1 ≠ x}
def inclusion (U : Set X) : C(U,X) := ⟨Subtype.val, continuous_subtype_val⟩
def inclusionMap (U : Set X) (x : X) := pairMap R (localDeleted U x) (deleted x) (inclusion U) (fun _ h => h)

theorem excision_eq (Z : Set X) (x : X) :
    CoefficientExcision.excisionMap R (deleted x) Z = inclusionMap R Zᶜ x := rfl

theorem complement_comparison (U : Set X) (x : X) :
    HEq (CoefficientExcision.excisionMap R (deleted x) Uᶜ) (inclusionMap R U x) := by
  change HEq (inclusionMap R Uᶜᶜ x) (inclusionMap R U x)
  have transport : ∀ (V W : Set X), V = W → HEq (inclusionMap R V x) (inclusionMap R W x) := by
    intro V W h
    subst W
    rfl
  exact transport _ _ (compl_compl U)

theorem projection_degree (U : Set X) (x : X) (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (localDeleted U x))).f n ≫ (inclusionMap R U x).f n =
    (absoluteMap R (inclusion U)).f n ≫ (cokernel.π (CoefficientRelativeSmall.subspaceMap R (deleted x))).f n :=
  CoefficientRadialPair.projection_degree R _ _ _ _ n

theorem inclusion_isIso [T1Space X] (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (inclusionMap R U x) n) := by
  have hZ : Uᶜ ⊆ interior (deleted x) := by
    have ho : IsOpen (deleted x) := isClosed_singleton.isOpen_compl
    rw [ho.interior_eq]
    intro y hy h
    exact hy (h.symm ▸ hx)
  have h := CoefficientExcision.excision_isIso R (deleted x) Uᶜ hU.isClosed_compl hZ n
  change IsIso (HomologicalComplex.homologyMap (inclusionMap R Uᶜᶜ x) n) at h
  exact (congrArg (fun V : Set X => IsIso (HomologicalComplex.homologyMap (inclusionMap R V x) n)) (compl_compl U)).mp h

def inclusionIso [T1Space X] (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U) (n : ℕ) := by
  letI := inclusion_isIso R U x hU hx n
  exact asIso (HomologicalComplex.homologyMap (inclusionMap R U x) n)

theorem inclusionIso_hom [T1Space X] (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U) (n : ℕ) :
    (inclusionIso R U x hU hx n).hom = HomologicalComplex.homologyMap (inclusionMap R U x) n := rfl
def nestedInclusion (U V : Set X) (h : U ⊆ V) : C(U,V) :=
  ⟨fun u => ⟨u.1, h u.2⟩, by fun_prop⟩
def nestedMap (U V : Set X) (h : U ⊆ V) (x : X) :=
  pairMap R (localDeleted U x) (localDeleted V x) (nestedInclusion U V h) (fun _ hu => hu)

theorem nested_comp (U V : Set X) (h : U ⊆ V) (x : X) :
    nestedMap R U V h x ≫ inclusionMap R V x = inclusionMap R U x := by
  exact (CoefficientPairNaturality.pair_comp R (localDeleted U x) (localDeleted V x) (deleted x)
    (nestedInclusion U V h) (inclusion V) (fun _ hu => hu) (fun _ hu => hu)).symm

theorem nested_homology (U V : Set X) (h : U ⊆ V) (x : X) (n : ℕ) :
    HomologicalComplex.homologyMap (nestedMap R U V h x) n ≫
      HomologicalComplex.homologyMap (inclusionMap R V x) n =
        HomologicalComplex.homologyMap (inclusionMap R U x) n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (fun f => HomologicalComplex.homologyMap f n) (nested_comp R U V h x))

theorem inverse_left [T1Space X] (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U) (n : ℕ) :
    (inclusionIso R U x hU hx n).inv ≫ (inclusionIso R U x hU hx n).hom = 𝟙 _ :=
  (inclusionIso R U x hU hx n).inv_hom_id

theorem inverse_right [T1Space X] (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U) (n : ℕ) :
    (inclusionIso R U x hU hx n).hom ≫ (inclusionIso R U x hU hx n).inv = 𝟙 _ :=
  (inclusionIso R U x hU hx n).hom_inv_id

def modelNormalization (m : ℕ) (U : Set (CoefficientModelLocal.E (m+2))) (hU : IsOpen U) (h0 : 0 ∈ U) :=
  inclusionIso R U 0 hU h0 (m+2) ≪≫ CoefficientModelLocal.localIso R m

theorem model_forward (m : ℕ) (U : Set (CoefficientModelLocal.E (m+2))) (hU : IsOpen U) (h0 : 0 ∈ U) :
    (modelNormalization R m U hU h0).hom =
      HomologicalComplex.homologyMap (inclusionMap R U 0) (m+2) ≫ (CoefficientModelLocal.localIso R m).hom := rfl

def modelGenerator (m : ℕ) (U : Set (CoefficientModelLocal.E (m+2))) (hU : IsOpen U) (h0 : 0 ∈ U) :=
  (modelNormalization R m U hU h0).inv.hom (1 : R)

theorem generator_normalization (m : ℕ) (U : Set (CoefficientModelLocal.E (m+2))) (hU : IsOpen U) (h0 : 0 ∈ U) :
    (modelNormalization R m U hU h0).hom.hom (modelGenerator R m U hU h0) = 1 :=
  congrArg (fun f => f.hom (1 : R)) (modelNormalization R m U hU h0).inv_hom_id

def integral_ball (m : ℕ) := modelNormalization ℤ m (Metric.ball 0 1) Metric.isOpen_ball (Metric.mem_ball_self (by norm_num))
def rational_ball (m : ℕ) := modelNormalization ℚ m (Metric.ball 0 1) Metric.isOpen_ball (Metric.mem_ball_self (by norm_num))
theorem generator_image (m : ℕ) (U : Set (CoefficientModelLocal.E (m+2))) (hU : IsOpen U) (h0 : 0 ∈ U) :
    (HomologicalComplex.homologyMap (inclusionMap R U 0) (m+2)).hom (modelGenerator R m U hU h0) =
      CoefficientModelLocal.generator R m := by
  exact congrArg (fun f => f.hom (CoefficientModelLocal.generator R m)) (inclusionIso R U 0 hU h0 (m+2)).inv_hom_id
end ConstructionTargets.CoefficientNeighborhoodLocal



#print axioms ConstructionTargets.CoefficientNeighborhoodLocal.excision_eq
#print axioms ConstructionTargets.CoefficientNeighborhoodLocal.complement_comparison
#print axioms ConstructionTargets.CoefficientNeighborhoodLocal.projection_degree
#print axioms ConstructionTargets.CoefficientNeighborhoodLocal.inclusion_isIso
#print axioms ConstructionTargets.CoefficientNeighborhoodLocal.inclusionIso_hom
#print axioms ConstructionTargets.CoefficientNeighborhoodLocal.nested_comp
#print axioms ConstructionTargets.CoefficientNeighborhoodLocal.nested_homology
#print axioms ConstructionTargets.CoefficientNeighborhoodLocal.inverse_left
#print axioms ConstructionTargets.CoefficientNeighborhoodLocal.inverse_right
#print axioms ConstructionTargets.CoefficientNeighborhoodLocal.modelNormalization
#print axioms ConstructionTargets.CoefficientNeighborhoodLocal.model_forward
#print axioms ConstructionTargets.CoefficientNeighborhoodLocal.generator_normalization
#print axioms ConstructionTargets.CoefficientNeighborhoodLocal.generator_image
#print axioms ConstructionTargets.CoefficientNeighborhoodLocal.integral_ball
#print axioms ConstructionTargets.CoefficientNeighborhoodLocal.rational_ball
