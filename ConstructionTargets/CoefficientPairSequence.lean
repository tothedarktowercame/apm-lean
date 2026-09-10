import ConstructionTargets.CoefficientExcision
import ConstructionTargets.T02A06DiskPairShift
noncomputable section
namespace ConstructionTargets.CoefficientPairSequence
open CategoryTheory CategoryTheory.Limits
variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X] (A : Set X)
abbrev absolute := CoefficientH0.SingularChains R (TopCat.of X)
abbrev relative := CoefficientRelativeSmall.relativeChains R A
abbrev inclusion := CoefficientRelativeSmall.subspaceMap R A
abbrev projection := cokernel.π (inclusion R A)
def sequence := CoefficientCokernelComparison.cokernelShortComplex R (inclusion R A)
theorem shortExact : (sequence R A).ShortExact :=
  CoefficientCokernelComparison.cokernelShortComplex_shortExact R (inclusion R A)
def connecting (n : ℕ) : (relative R A).homology (n+1) ⟶ (absolute R (X := A)).homology n :=
  (shortExact R A).δ (n+1) n rfl

theorem exact_subspace (n : ℕ) :
    (ShortComplex.mk (connecting R A n) (HomologicalComplex.homologyMap (inclusion R A) n)
      ((shortExact R A).δ_comp (n+1) n rfl)).Exact :=
  (shortExact R A).homology_exact₁ (n+1) n rfl

theorem exact_absolute (n : ℕ) :
    ((sequence R A).map (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n)).Exact :=
  (shortExact R A).homology_exact₂ n

theorem exact_relative (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (projection R A) (n+1)) (connecting R A n)
      ((shortExact R A).comp_δ (n+1) n rfl)).Exact :=
  (shortExact R A).homology_exact₃ (n+1) n rfl

/-- This algebraic lemma states its vanishing hypotheses explicitly. -/
def connectingIso (n : ℕ) (hnext : IsZero ((absolute R (X := X)).homology (n+1)))
    (hcur : IsZero ((absolute R (X := X)).homology n)) :
    (relative R A).homology (n+1) ≅ (absolute R (X := A)).homology n := by
  letI : Mono (connecting R A n) := (exact_relative R A n).mono_g (hnext.eq_of_src _ _)
  letI : Epi (connecting R A n) := (exact_subspace R A n).epi_f (hcur.eq_of_tgt _ _)
  letI := isIso_of_mono_of_epi (connecting R A n)
  exact asIso (connecting R A n)

theorem connectingIso_hom (n : ℕ) (hnext : IsZero ((absolute R (X := X)).homology (n+1)))
    (hcur : IsZero ((absolute R (X := X)).homology n)) :
    (connectingIso R A n hnext hcur).hom = connecting R A n := rfl

def relativeH1IsoKernel (h : IsZero ((absolute R (X := X)).homology 1)) :
    (relative R A).homology 1 ≅ kernel (HomologicalComplex.homologyMap (inclusion R A) 0) := by
  letI : Mono (connecting R A 0) := (exact_relative R A 0).mono_g (h.eq_of_src _ _)
  exact IsLimit.conePointUniqueUpToIso (exact_subspace R A 0).fIsKernel (limit.isLimit _)

theorem relativeH1IsoKernel_projection (h : IsZero ((absolute R (X := X)).homology 1)) :
    (relativeH1IsoKernel R A h).hom ≫ kernel.ι (HomologicalComplex.homologyMap (inclusion R A) 0) =
    connecting R A 0 := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero


theorem connecting_inverse_left (n : ℕ) (hnext : IsZero ((absolute R (X := X)).homology (n+1)))
    (hcur : IsZero ((absolute R (X := X)).homology n)) :
    (connectingIso R A n hnext hcur).inv ≫ connecting R A n = 𝟙 _ :=
  (connectingIso R A n hnext hcur).inv_hom_id

theorem connecting_inverse_right (n : ℕ) (hnext : IsZero ((absolute R (X := X)).homology (n+1)))
    (hcur : IsZero ((absolute R (X := X)).homology n)) :
    connecting R A n ≫ (connectingIso R A n hnext hcur).inv = 𝟙 _ :=
  (connectingIso R A n hnext hcur).hom_inv_id

/-- R and X are Type 0. This includes empty A and requires no contractibility. -/
def integral_disk_sequence (m : ℕ) := sequence ℤ (T02A06DiskPairShift.diskBoundarySubset m)
def rational_disk_sequence (m : ℕ) := sequence ℚ (T02A06DiskPairShift.diskBoundarySubset m)
def integral_disk_exact (m n : ℕ) := exact_relative ℤ (T02A06DiskPairShift.diskBoundarySubset m) n
def rational_disk_exact (m n : ℕ) := exact_relative ℚ (T02A06DiskPairShift.diskBoundarySubset m) n
#print axioms shortExact
#print axioms exact_subspace
#print axioms exact_absolute
#print axioms exact_relative
#print axioms connectingIso_hom
#print axioms relativeH1IsoKernel_projection
#print axioms connecting_inverse_left
#print axioms connecting_inverse_right
#print axioms integral_disk_exact
#print axioms rational_disk_exact
end ConstructionTargets.CoefficientPairSequence
