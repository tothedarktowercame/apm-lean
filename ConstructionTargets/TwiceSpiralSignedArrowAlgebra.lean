import ConstructionTargets.TwiceSpiralH1Coordinates
import Mathlib.Data.ZMod.Basic

/-!
# Kernel and cokernel of the twice-spiral signed arrow
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.TwiceSpiralSignedArrowAlgebra

open ConstructionTargets.TwiceSpiralH1Coordinates

abbrev IntPairGroup := AddCommGrpCat.of (ℤ × ℤ)
abbrev ParityGroup := AddCommGrpCat.of (ZMod 2)

/-- The actual categorical morphism underlying the signed H1 arrow. -/
def twiceSpiralSignedArrow (d : ℤ) : IntPairGroup ⟶ IntPairGroup :=
  AddCommGrpCat.ofHom (twiceSpiralSignedH1Arrow d)

@[simp] theorem twiceSpiralSignedArrow_apply (d a b : ℤ) :
    twiceSpiralSignedArrow d (a, b) = (b, -(2 * a + d * b)) := rfl

theorem twiceSpiralSignedArrow_injective (d : ℤ) :
    Function.Injective (twiceSpiralSignedArrow d) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  change (b, -(2 * a + d * b)) = (b', -(2 * a' + d * b')) at h
  have hb : b = b' := congrArg Prod.fst h
  have hs : -(2 * a + d * b) = -(2 * a' + d * b') :=
    congrArg Prod.snd h
  subst b'
  apply Prod.ext
  · omega
  · rfl

instance twiceSpiralSignedArrow_mono (d : ℤ) :
    Mono (twiceSpiralSignedArrow d) :=
  (AddCommGrpCat.mono_iff_injective _).mpr
    (twiceSpiralSignedArrow_injective d)

/-- The normalized parity quotient `(x,y) ↦ y + d*x (mod 2)`. -/
def twiceSpiralParityQuotient (d : ℤ) : IntPairGroup ⟶ ParityGroup :=
  AddCommGrpCat.ofHom
    { toFun := fun q => ((q.2 + d * q.1 : ℤ) : ZMod 2)
      map_zero' := by simp
      map_add' := by
        rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
        change (((x₂ + y₂ + d * (x₁ + y₁) : ℤ) : ZMod 2)) =
          ((x₂ + d * x₁ : ℤ) : ZMod 2) +
            ((y₂ + d * y₁ : ℤ) : ZMod 2)
        push_cast
        ring }

@[simp] theorem twiceSpiralParityQuotient_apply (d x y : ℤ) :
    twiceSpiralParityQuotient d (x, y) = ((y + d * x : ℤ) : ZMod 2) := rfl

@[simp] theorem twiceSpiralSignedArrow_comp_parity (d : ℤ) :
    twiceSpiralSignedArrow d ≫ twiceSpiralParityQuotient d = 0 := by
  apply AddCommGrpCat.hom_ext
  ext q
  rcases q with ⟨a, b⟩
  change (((-(2 * a + d * b) + d * b : ℤ) : ZMod 2)) = 0
  rw [show -(2 * a + d * b) + d * b = -2 * a by ring]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (-2 * a) 2).mpr (by omega)

def twiceSpiralCokernelCofork (d : ℤ) :
    CokernelCofork (twiceSpiralSignedArrow d) :=
  CokernelCofork.ofπ (twiceSpiralParityQuotient d)
    (twiceSpiralSignedArrow_comp_parity d)

/-- The explicit parity quotient has the cokernel universal property. -/
def twiceSpiralCokernelIsColimit (d : ℤ) :
    IsColimit (twiceSpiralCokernelCofork d) :=
  Cofork.IsColimit.mk' _ fun s => by
    let v : s.pt := s.π (0, 1)
    have hs : twiceSpiralSignedArrow d ≫ s.π = 0 := by
      simpa only [zero_comp] using s.condition
    have hv2 : (2 : ℤ) • v = 0 := by
      have h : s.π (0, -2) = 0 := by
        have h' : (twiceSpiralSignedArrow d ≫ s.π) (1, 0) = 0 := by
          rw [hs]
          rfl
        rw [CategoryTheory.comp_apply] at h'
        simpa [twiceSpiralSignedArrow, twiceSpiralSignedH1Arrow] using h'
      change (2 : ℤ) • s.π (0, 1) = 0
      have hm : s.π (0, -2) = (-2 : ℤ) • s.π (0, 1) := by
        rw [← map_zsmul]
        rfl
      rw [hm] at h
      simpa using congrArg Neg.neg h
    let t : ZMod 2 →+ s.pt := ZMod.lift 2
      ⟨zmultiplesHom s.pt v, by simpa using hv2⟩
    refine ⟨AddCommGrpCat.ofHom t, ?_, ?_⟩
    · apply AddCommGrpCat.hom_ext
      ext q
      rcases q with ⟨x, y⟩
      have hrel : s.π (x, -(d * x)) = 0 := by
        have h' : (twiceSpiralSignedArrow d ≫ s.π) (0, x) = 0 := by
          rw [hs]
          rfl
        rw [CategoryTheory.comp_apply] at h'
        simpa [twiceSpiralSignedArrow, twiceSpiralSignedH1Arrow] using h'
      have hx : s.π (x, 0) = (d * x : ℤ) • v := by
        have hsplit : s.π (x, -(d * x)) =
            s.π (x, 0) - (d * x : ℤ) • v := by
          rw [← map_zsmul]
          rw [← map_sub]
          apply congrArg s.π
          ext <;> simp
        rw [hsplit] at hrel
        exact sub_eq_zero.mp hrel
      change t (((y + d * x : ℤ) : ZMod 2)) = s.π (x, y)
      rw [ZMod.lift_coe]
      change (y + d * x : ℤ) • v = s.π (x, y)
      have hy : s.π (0, y) = (y : ℤ) • v := by
        rw [← map_zsmul]
        apply congrArg s.π
        ext <;> simp
      rw [add_zsmul, ← hx, ← hy]
      rw [← map_add]
      apply congrArg s.π
      ext <;> simp
    · intro m hm
      apply AddCommGrpCat.hom_ext
      change (show ParityGroup ⟶ s.pt from m).hom = t
      apply AddMonoidHom.ext
      intro z
      change ZMod 2 at z
      obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
      have h1 := DFunLike.congr_fun
        (congrArg AddCommGrpCat.Hom.hom hm) (0, 1)
      have h1' : m (1 : ZMod 2) = v := by
        simpa [twiceSpiralCokernelCofork, twiceSpiralParityQuotient, v]
          using h1
      change m (((n : ℤ) : ZMod 2)) = t (((n : ℤ) : ZMod 2))
      rw [show (((n : ℤ) : ZMod 2)) = (n : ℤ) • (1 : ZMod 2) by simp]
      change m.hom ((n : ℤ) • (1 : ZMod 2)) =
        t ((n : ℤ) • (1 : ZMod 2))
      have ht1 : t (1 : ZMod 2) = v := by
        change ZMod.lift 2 ⟨zmultiplesHom s.pt v, _⟩
          ((1 : ℤ) : ZMod 2) = v
        rw [ZMod.lift_coe]
        simp
      calc
        _ = (n : ℤ) • m.hom (1 : ZMod 2) := map_zsmul m.hom n _
        _ = (n : ℤ) • v := congrArg (fun w => (n : ℤ) • w) h1'
        _ = (n : ℤ) • t (1 : ZMod 2) := by rw [ht1]
        _ = _ := (map_zsmul t n _).symm

/-- The canonical cokernel is `ZMod 2`. -/
def twiceSpiralCokernelIso (d : ℤ) :
    cokernel (twiceSpiralSignedArrow d) ≅ ParityGroup :=
  colimit.isoColimitCocone
    ⟨twiceSpiralCokernelCofork d, twiceSpiralCokernelIsColimit d⟩

/-- The canonical cokernel projection is normalized to `(x,y) ↦ y+d*x`. -/
theorem cokernel_π_comp_twiceSpiralCokernelIso_hom (d : ℤ) :
    cokernel.π (twiceSpiralSignedArrow d) ≫
      (twiceSpiralCokernelIso d).hom = twiceSpiralParityQuotient d := by
  exact colimit.isoColimitCocone_ι_hom
    ⟨twiceSpiralCokernelCofork d, twiceSpiralCokernelIsColimit d⟩
      WalkingParallelPair.one

#print axioms twiceSpiralSignedArrow_injective
#print axioms twiceSpiralCokernelIsColimit
#print axioms twiceSpiralCokernelIso
#print axioms cokernel_π_comp_twiceSpiralCokernelIso_hom

end ConstructionTargets.TwiceSpiralSignedArrowAlgebra
