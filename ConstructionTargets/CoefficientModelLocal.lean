import ConstructionTargets.CoefficientSphereAntipodal
import ConstructionTargets.PuncturedNormedSpaceRadialEquivalence
noncomputable section
namespace ConstructionTargets.CoefficientModelLocal
open CategoryTheory CategoryTheory.Limits
open CoefficientRadialPair PuncturedNormedSpaceRadialEquivalence
variable (R : Type) [CommRing R]
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
def puncture (d : ℕ) : Set (E d) := {x | x ≠ 0}

def negation (d : ℕ) : C(E d, E d) := ⟨Neg.neg, continuous_neg⟩
theorem negation_mapsTo (d : ℕ) : Set.MapsTo (negation d) (puncture d) (puncture d) := by
  intro x hx
  exact neg_ne_zero.mpr hx

def restricted (d : ℕ) : C(puncture d, puncture d) :=
  ⟨fun x => ⟨-x.1, neg_ne_zero.mpr x.2⟩, by fun_prop⟩

theorem radial_square (d : ℕ) :
    (radialNormalize (E d)).comp (restricted d) =
      (CoefficientSphereAntipodal.antipodal).comp (radialNormalize (E d)) := by
  ext x : 1
  apply Subtype.ext
  change ‖-x.1‖⁻¹ • (-x.1) = -(‖x.1‖⁻¹ • x.1)
  simp only [norm_neg, smul_neg]

def radialIso (d q : ℕ) := CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv R
  (unitSphereHomotopyEquivPuncturedSpace (E d)).symm q

theorem radialIso_hom (d q : ℕ) : (radialIso R d q).hom =
    (F R q).map (TopCat.ofHom (radialNormalize (E d))) := rfl

def localIso (m : ℕ) :=
  CoefficientContractiblePair.contractibleConnectingIso R (puncture (m+2)) (m+1) (by omega) ≪≫
    radialIso R (m+2) (m+1) ≪≫ CoefficientSphereAntipodal.normalization R m

def pairMap (d : ℕ) := CoefficientRadialPair.pairMap R (puncture d) (puncture d)
  (negation d) (negation_mapsTo d)

theorem projection_degree (d q : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (puncture d))).f q ≫ (pairMap R d).f q =
      (absoluteMap R (negation d)).f q ≫ (cokernel.π (CoefficientRelativeSmall.subspaceMap R (puncture d))).f q :=
  CoefficientRadialPair.projection_degree R _ _ _ _ q

theorem radial_naturality (d q : ℕ) :
    (F R q).map (TopCat.ofHom (restricted d)) ≫ (radialIso R d q).hom =
      (radialIso R d q).hom ≫ (F R q).map (TopCat.ofHom CoefficientSphereAntipodal.antipodal) := by
  exact ((F R q).map_comp (TopCat.ofHom (restricted d))
    (TopCat.ofHom (radialNormalize (E d)))).symm.trans
      ((congrArg (fun f => (F R q).map (TopCat.ofHom f)) (radial_square d)).trans
        ((F R q).map_comp (TopCat.ofHom (radialNormalize (E d)))
          (TopCat.ofHom CoefficientSphereAntipodal.antipodal)))

theorem forward_composite (m : ℕ) : (localIso R m).hom =
    CoefficientPairSequence.connecting R (puncture (m+2)) (m+1) ≫
      (F R (m+1)).map (TopCat.ofHom (radialNormalize (E (m+2)))) ≫
      (CoefficientSphereAntipodal.normalization R m).hom := rfl

def relativeAction (m : ℕ) := HomologicalComplex.homologyMap (pairMap R (m+2)) (m+2)

theorem local_forward (m : ℕ) : relativeAction R m ≫ (localIso R m).hom =
    ((-1 : R)^(m+2)) • (localIso R m).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hn := congrArg (fun f => f.hom x)
    (CoefficientPairNaturality.connecting_naturality R (puncture (m+2)) (puncture (m+2))
      (negation (m+2)) (negation_mapsTo (m+2)) (m+1))
  let c := CoefficientPairSequence.connecting R (puncture (m+2)) (m+1)
  have hr := congrArg (fun f => f.hom (c.hom x)) (radial_naturality R (m+2) (m+1))
  have hs := CoefficientSphereAntipodal.scalar_equation R m ((radialIso R (m+2) (m+1)).hom.hom (c.hom x))
  exact (congrArg (fun y => (CoefficientSphereAntipodal.normalization R m).hom.hom
    ((radialIso R (m+2) (m+1)).hom.hom y)) hn.symm).trans
      ((congrArg (CoefficientSphereAntipodal.normalization R m).hom.hom hr).trans hs)

theorem inverse_left (m : ℕ) : (localIso R m).inv ≫ (localIso R m).hom = 𝟙 _ := (localIso R m).inv_hom_id
theorem inverse_right (m : ℕ) : (localIso R m).hom ≫ (localIso R m).inv = 𝟙 _ := (localIso R m).hom_inv_id

def generator (m : ℕ) := (localIso R m).inv.hom (1 : R)
theorem generator_normalization (m : ℕ) : (localIso R m).hom.hom (generator R m) = 1 :=
  congrArg (fun f => f.hom (1 : R)) (localIso R m).inv_hom_id

theorem local_conjugation (m : ℕ) : (localIso R m).inv ≫ relativeAction R m ≫ (localIso R m).hom =
    ((-1 : R)^(m+2)) • 𝟙 _ := by
  rw [local_forward]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact congrArg (fun f => ((-1 : R)^(m+2)) * f.hom r) (localIso R m).inv_hom_id

def integral_two := local_conjugation ℤ 0
def integral_three := local_conjugation ℤ 1
def rational_two := local_conjugation ℚ 0
def rational_three := local_conjugation ℚ 1
end ConstructionTargets.CoefficientModelLocal


#print axioms ConstructionTargets.CoefficientModelLocal.negation_mapsTo
#print axioms ConstructionTargets.CoefficientModelLocal.radial_square
#print axioms ConstructionTargets.CoefficientModelLocal.radialIso
#print axioms ConstructionTargets.CoefficientModelLocal.radialIso_hom
#print axioms ConstructionTargets.CoefficientModelLocal.localIso
#print axioms ConstructionTargets.CoefficientModelLocal.projection_degree
#print axioms ConstructionTargets.CoefficientModelLocal.radial_naturality
#print axioms ConstructionTargets.CoefficientModelLocal.forward_composite
#print axioms ConstructionTargets.CoefficientModelLocal.local_forward
#print axioms ConstructionTargets.CoefficientModelLocal.inverse_left
#print axioms ConstructionTargets.CoefficientModelLocal.inverse_right
#print axioms ConstructionTargets.CoefficientModelLocal.generator_normalization
#print axioms ConstructionTargets.CoefficientModelLocal.local_conjugation
#print axioms ConstructionTargets.CoefficientModelLocal.integral_two
#print axioms ConstructionTargets.CoefficientModelLocal.integral_three
#print axioms ConstructionTargets.CoefficientModelLocal.rational_two
#print axioms ConstructionTargets.CoefficientModelLocal.rational_three
