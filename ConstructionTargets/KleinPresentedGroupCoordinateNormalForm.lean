import ConstructionTargets.KleinPresentedGroupTwoSidedConjugation

namespace KleinPresentedGroupCoordinateNormalForm

open KleinPresentedGroupCoordinateModel
open KleinPresentedGroupConjugation
open KleinPresentedGroupTwoSidedConjugation

def fromA : ZMul →* PresentedKleinGroup :=
  zpowersHom PresentedKleinGroup generatorA

def fromB : ZMul →* PresentedKleinGroup :=
  zpowersHom PresentedKleinGroup generatorB

theorem actionCompatibilityAtGenerator (n : ℤ) :
    generatorA ^ Multiplicative.toAdd
        ((inversion ^ n) (Multiplicative.ofAdd 1)) =
      (MulAut.conj generatorB ^ n) generatorA := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [zpow_add_one inversion (n : ℤ), zpow_add_one (MulAut.conj generatorB) (n : ℤ)]
      simp only [MulAut.mul_apply]
      simpa [inversion, reverseConjugateA] using congrArg Inv.inv ih
  | pred n ih =>
      change generatorA ^ Multiplicative.toAdd
          ((inversion ^ ((-(n : ℤ)) - 1)) (Multiplicative.ofAdd 1)) =
        (MulAut.conj generatorB ^ ((-(n : ℤ)) - 1)) generatorA
      rw [zpow_sub_one inversion (-(n : ℤ)),
        zpow_sub_one (MulAut.conj generatorB) (-(n : ℤ))]
      simp only [MulAut.mul_apply]
      simpa [inversion, conjugateA] using congrArg Inv.inv ih

theorem actionCompatibility (g : ZMul) :
    fromA.comp (action g).toMonoidHom =
      (MulAut.conj (fromB g)).toMonoidHom.comp fromA := by
  apply MonoidHom.ext_mint
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, fromA, fromB,
    action, zpowersHom_apply]
  simpa [map_zpow] using actionCompatibilityAtGenerator (Multiplicative.toAdd g)

def fromCoordinates : Coordinates →* PresentedKleinGroup :=
  SemidirectProduct.lift fromA fromB actionCompatibility

theorem to_from :
    toCoordinates.comp fromCoordinates = MonoidHom.id Coordinates := by
  apply SemidirectProduct.hom_ext
  · apply MonoidHom.ext_mint
    simp [fromCoordinates, fromA, A]
  · apply MonoidHom.ext_mint
    simp [fromCoordinates, fromB, B]

theorem from_to :
    fromCoordinates.comp toCoordinates = MonoidHom.id PresentedKleinGroup := by
  apply (MonoidHom.cancel_right (PresentedGroup.mk_surjective relations)).mp
  apply FreeGroup.ext_hom
  intro i
  cases i
  · change fromCoordinates (toCoordinates generatorA) = generatorA
    rw [toCoordinates_a]
    simp [fromCoordinates, fromA, A]
  · change fromCoordinates (toCoordinates generatorB) = generatorB
    rw [toCoordinates_b]
    simp [fromCoordinates, fromB, B]

def coordinateEquiv : PresentedKleinGroup ≃* Coordinates :=
  { toCoordinates with
    invFun := fromCoordinates
    left_inv := DFunLike.congr_fun from_to
    right_inv := DFunLike.congr_fun to_from }

@[simp] theorem coordinateEquiv_a : coordinateEquiv generatorA = A :=
  toCoordinates_a

@[simp] theorem coordinateEquiv_b : coordinateEquiv generatorB = B :=
  toCoordinates_b

def coordinatePairEquiv : PresentedKleinGroup ≃ ZMul × ZMul :=
  coordinateEquiv.toEquiv.trans SemidirectProduct.equivProd

theorem uniqueNormalForm (x : PresentedKleinGroup) :
    ∃! p : ZMul × ZMul,
      x = generatorA ^ Multiplicative.toAdd p.1 *
        generatorB ^ Multiplicative.toAdd p.2 := by
  let p := coordinatePairEquiv x
  refine ⟨p, ?_, ?_⟩
  · change x = fromCoordinates ⟨p.1, p.2⟩
    exact (coordinateEquiv.toEquiv.symm_apply_apply x).symm
  · intro q hq
    have hq' : x = fromCoordinates ⟨q.1, q.2⟩ := by
      rw [hq]
      rfl
    apply coordinatePairEquiv.symm.injective
    change fromCoordinates ⟨q.1, q.2⟩ = fromCoordinates ⟨p.1, p.2⟩
    rw [← hq']
    exact (coordinateEquiv.toEquiv.symm_apply_apply x).symm

#print axioms actionCompatibility
#print axioms coordinateEquiv
#print axioms uniqueNormalForm

end KleinPresentedGroupCoordinateNormalForm
