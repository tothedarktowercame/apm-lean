import ConstructionTargets.CirclePowerKernelCard

noncomputable section

namespace ConstructionTargets.CirclePowerFiberCard

open ConstructionTargets.CirclePowerKernelCard

theorem circlePower_fiber_card (n : ℕ) [NeZero n] (y : Circle) :
    Nat.card {z : Circle // z ^ n = y} = n := by
  let f : Circle →* Circle := powMonoidHom n
  have hs : Function.Surjective f :=
    (Circle.isQuotientCoveringMap_npow n).surjective
  let a : Circle := Function.surjInv hs y
  have ha : f a = y := Function.surjInv_eq hs y
  rw [← ha]
  exact (Nat.card_congr (MonoidHom.fiberEquivKer f a)).trans
    (circlePower_kernel_card n)

theorem circlePower_fiber_finite (n : ℕ) [NeZero n] (y : Circle) :
    Finite {z : Circle // z ^ n = y} := by
  let f : Circle →* Circle := powMonoidHom n
  have hs : Function.Surjective f :=
    (Circle.isQuotientCoveringMap_npow n).surjective
  let a : Circle := Function.surjInv hs y
  have ha : f a = y := Function.surjInv_eq hs y
  rw [← ha]
  letI : Finite f.ker := by
    dsimp [f]
    exact circlePower_kernel_finite n
  exact Finite.of_injective (MonoidHom.fiberEquivKer f a)
    (MonoidHom.fiberEquivKer f a).injective

#print axioms circlePower_fiber_card
#print axioms circlePower_fiber_finite

end ConstructionTargets.CirclePowerFiberCard
