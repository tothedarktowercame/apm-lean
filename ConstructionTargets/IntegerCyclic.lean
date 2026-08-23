import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Maps out of the cyclic integer module

Reusable categorical criteria for proving that a morphism out of the free
rank-one integer module is a monomorphism.  The essential hypothesis is that
the target is torsion-free; no coordinates or finite-rank assumption are
needed.
-/

open CategoryTheory

noncomputable section

namespace ConstructionTargets.IntegerCyclic

/-- A morphism from `ℤ` to a torsion-free integer module is mono as soon as it
does not kill `1`. -/
lemma mono_of_apply_one_ne_zero
    (M : Type) [AddCommGroup M] [moduleM : Module ℤ M]
    [Module.IsTorsionFree ℤ M]
    (f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ M) (hf : f (1 : ℤ) ≠ 0) :
    Mono f := by
  rw [ModuleCat.mono_iff_injective]
  change Function.Injective f.hom
  intro x y hxy
  change ℤ at x y
  have hzero : @SMul.smul ℤ M moduleM.toSMul (x - y) (f (1 : ℤ) : M) = 0 := by
    calc
      @SMul.smul ℤ M moduleM.toSMul (x - y) (f (1 : ℤ) : M) =
          f.hom ((x - y : ℤ) • (1 : ℤ)) :=
        (f.hom.map_smul (x - y) (1 : ℤ)).symm
      _ = 0 := by simp [map_sub, hxy]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hf)

/-- For maps out of `ℤ` into a torsion-free integer module, nonzero and mono
are equivalent. -/
lemma mono_iff_ne_zero
    (M : Type) [AddCommGroup M] [Module ℤ M] [Module.IsTorsionFree ℤ M]
    (f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ M) :
    Mono f ↔ f ≠ 0 := by
  constructor
  · intro _ hzero
    have hinj : Function.Injective f :=
      (ModuleCat.mono_iff_injective f).mp inferInstance
    have hone : f (1 : ℤ) = f 0 := by rw [hzero]; rfl
    exact one_ne_zero (hinj hone)
  · intro hf
    apply mono_of_apply_one_ne_zero M f
    intro hone
    apply hf
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change f.hom z = (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ M).hom z
    rw [show z = z • (1 : ℤ) by simp, f.hom.map_smul, hone]
    simp

/-- Isomorphism-invariant version of `mono_iff_ne_zero`: a nonzero morphism
from an infinite cyclic module to a torsion-free module is mono. -/
lemma mono_of_ne_zero_of_iso
    {A B : ModuleCat ℤ} (M : Type) [AddCommGroup M] [Module ℤ M]
    [Module.IsTorsionFree ℤ M]
    (eA : A ≅ ModuleCat.of ℤ ℤ) (eB : B ≅ ModuleCat.of ℤ M)
    (f : A ⟶ B) (hf : f ≠ 0) : Mono f := by
  let F : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ M := eA.inv ≫ f ≫ eB.hom
  have hF : F ≠ 0 := by
    intro h
    apply hf
    rw [← cancel_epi eA.inv, ← cancel_mono eB.hom]
    simpa [F] using h
  have hFone : F (1 : ℤ) ≠ 0 := by
    intro hone
    apply hF
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change F.hom z = (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ M).hom z
    rw [show z = z • (1 : ℤ) by simp, F.hom.map_smul, hone]
    simp
  haveI : Mono F := mono_of_apply_one_ne_zero M F hFone
  rw [ModuleCat.mono_iff_injective]
  intro x y hxy
  have hFinj : Function.Injective F :=
    (ModuleCat.mono_iff_injective F).mp inferInstance
  have heAinj : Function.Injective eA.hom :=
    (ModuleCat.mono_iff_injective eA.hom).mp inferInstance
  apply heAinj
  apply hFinj
  change eB.hom (f (eA.inv (eA.hom x))) =
    eB.hom (f (eA.inv (eA.hom y)))
  simpa using congrArg eB.hom hxy

#print axioms mono_of_apply_one_ne_zero
#print axioms mono_iff_ne_zero
#print axioms mono_of_ne_zero_of_iso

end ConstructionTargets.IntegerCyclic
