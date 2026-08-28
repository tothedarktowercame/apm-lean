import ConstructionTargets.BoundaryTorusMayerVietoris
import ConstructionTargets.SignedDiagonalCokernel

/-!
# Algebra of the signed fold in the boundary-torus Mayer--Vietoris sequence

This file works in an arbitrary abelian category.  It computes the kernel and
cokernel of `(a,b) ↦ (a+b,-a-b)` from biproduct universal properties.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.BoundaryTorusMayerVietorisAlgebra

open ConstructionTargets.SignedDiagonalCokernel

variable {C : Type*} [Category C] [Abelian C]

/-- The fold followed by the signed diagonal: in additive coordinates this is
`(a,b) ↦ (a+b,-a-b)`. -/
def signedFold (Z : C) :=
  codiagonal Z ≫ signedDiagonal Z

theorem signedFold_fst (Z : C) :
    signedFold Z ≫ biprod.fst = codiagonal Z := by
  simp [signedFold, signedDiagonal]

theorem signedFold_snd (Z : C) :
    signedFold Z ≫ biprod.snd = -codiagonal Z := by
  simp [signedFold, signedDiagonal]

@[simp] theorem signedDiagonal_comp_signedFold (Z : C) :
    signedDiagonal Z ≫ signedFold Z = 0 := by
  rw [signedFold, ← Category.assoc, signedDiagonal_comp_codiagonal, zero_comp]

def signedFoldKernelFork (Z : C) : KernelFork (signedFold Z) :=
  KernelFork.ofι (signedDiagonal Z) (signedDiagonal_comp_signedFold Z)

def signedFoldKernelIsLimit (Z : C) : IsLimit (signedFoldKernelFork Z) :=
  Fork.IsLimit.mk' _ fun s => by
    have hs : s.ι ≫ codiagonal Z = 0 := by
      apply (cancel_mono (signedDiagonal Z)).1
      simpa [signedFold, Category.assoc] using s.condition
    refine ⟨s.ι ≫ biprod.fst, ?_, ?_⟩
    · change (s.ι ≫ biprod.fst) ≫ signedDiagonal Z = s.ι
      apply biprod.hom_ext
      · simp [signedFoldKernelFork, signedDiagonal]
      · have hdecomp : s.ι =
            biprod.lift (s.ι ≫ biprod.fst) (s.ι ≫ biprod.snd) := by
          apply biprod.hom_ext <;> simp
        have hs' : s.ι ≫ biprod.fst + s.ι ≫ biprod.snd = 0 := by
          rw [hdecomp, codiagonal, biprod.lift_desc] at hs
          simpa using hs
        simp only [signedDiagonal, Category.assoc, biprod.lift_snd,
          Preadditive.comp_neg, Category.comp_id]
        simpa using congrArg Neg.neg (eq_neg_of_add_eq_zero_left hs')
    · intro m hm
      rw [← hm]
      simp [signedFoldKernelFork, signedDiagonal, Category.assoc]

def signedFoldKernelIso (Z : C) : kernel (signedFold Z) ≅ Z :=
  limit.isoLimitCone ⟨signedFoldKernelFork Z, signedFoldKernelIsLimit Z⟩

theorem signedFoldKernelIso_inv_comp_kernelι (Z : C) :
    (signedFoldKernelIso Z).inv ≫ kernel.ι (signedFold Z) = signedDiagonal Z := by
  exact limit.isoLimitCone_inv_π
    ⟨signedFoldKernelFork Z, signedFoldKernelIsLimit Z⟩ WalkingParallelPair.zero

@[simp] theorem signedFold_comp_codiagonal (Z : C) :
    signedFold Z ≫ codiagonal Z = 0 := by
  simp [signedFold]

def signedFoldCokernelCofork (Z : C) : CokernelCofork (signedFold Z) :=
  CokernelCofork.ofπ (codiagonal Z) (signedFold_comp_codiagonal Z)

def signedFoldCokernelIsColimit (Z : C) :
    IsColimit (signedFoldCokernelCofork Z) :=
  Cofork.IsColimit.mk' _ fun s => by
    letI : Epi (codiagonal Z) := by
      dsimp [codiagonal]
      infer_instance
    have hs : signedDiagonal Z ≫ s.π = 0 := by
      apply (cancel_epi (codiagonal Z)).1
      have hc : signedFold Z ≫ s.π = 0 := CokernelCofork.condition s
      dsimp only [signedFold] at hc
      rw [Category.assoc] at hc
      simpa only [comp_zero] using hc
    let t : CokernelCofork (signedDiagonal Z) := CokernelCofork.ofπ s.π hs
    let ht := signedDiagonalCokernelIsColimit Z
    refine ⟨ht.desc t, ?_, ?_⟩
    · exact ht.fac t WalkingParallelPair.one
    · intro m hm
      apply Cofork.IsColimit.hom_ext ht
      calc
        Cofork.π (signedDiagonalCokernelCofork Z) ≫ m = s.π := by
          simpa [signedDiagonalCokernelCofork,
            signedFoldCokernelCofork] using hm
        _ = Cofork.π (signedDiagonalCokernelCofork Z) ≫ ht.desc t := by
          simpa [t] using (ht.fac t WalkingParallelPair.one).symm

def signedFoldCokernelIso (Z : C) : cokernel (signedFold Z) ≅ Z :=
  colimit.isoColimitCocone
    ⟨signedFoldCokernelCofork Z, signedFoldCokernelIsColimit Z⟩

theorem cokernelπ_comp_signedFoldCokernelIso_hom (Z : C) :
    cokernel.π (signedFold Z) ≫ (signedFoldCokernelIso Z).hom =
      codiagonal Z := by
  exact colimit.isoColimitCocone_ι_hom
    ⟨signedFoldCokernelCofork Z, signedFoldCokernelIsColimit Z⟩
      WalkingParallelPair.one

def kernelSignedFoldShortComplex (Z : C) : ShortComplex C :=
  ShortComplex.mk (signedDiagonal Z) (signedFold Z)
    (signedDiagonal_comp_signedFold Z)

theorem kernelSignedFold_exact (Z : C) :
    (kernelSignedFoldShortComplex Z).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (signedFoldKernelIsLimit Z)

def signedFoldCokernelShortComplex (Z : C) : ShortComplex C :=
  ShortComplex.mk (signedFold Z) (codiagonal Z)
    (signedFold_comp_codiagonal Z)

theorem signedFoldCokernel_exact (Z : C) :
    (signedFoldCokernelShortComplex Z).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (signedFoldCokernelIsColimit Z)

abbrev IntGroup := AddCommGrpCat.of ℤ

noncomputable def intFold :=
  codiagonal IntGroup

noncomputable def intSignedLift :=
  signedDiagonal IntGroup

noncomputable def intSignedFold :=
  signedFold IntGroup

theorem intSignedFold_fst : intSignedFold ≫ biprod.fst = intFold :=
  signedFold_fst IntGroup

theorem intSignedFold_snd : intSignedFold ≫ biprod.snd = -intFold :=
  signedFold_snd IntGroup

#print axioms signedFoldKernelIsLimit
#print axioms signedFoldKernelIso
#print axioms signedFoldCokernelIsColimit
#print axioms signedFoldCokernelIso
#print axioms kernelSignedFold_exact
#print axioms signedFoldCokernel_exact
#print axioms intSignedFold_fst

end ConstructionTargets.BoundaryTorusMayerVietorisAlgebra
