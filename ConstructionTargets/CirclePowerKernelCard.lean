import ConstructionTargets.CyclicThreeCirclesPullbackCover
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

noncomputable section

namespace ConstructionTargets.CirclePowerKernelCard

noncomputable def kernelEquivRoots (n : ℕ) [NeZero n] :
    (powMonoidHom (α := Circle) n).ker ≃ rootsOfUnity n Circle where
  toFun z := rootsOfUnity.mkOfPowEq z.1 (by
    have hz := z.2
    change z.1 ^ n = 1 at hz
    exact hz)
  invFun z := ⟨z.1.1, by
    change z.1.1 ^ n = 1
    exact congrArg Units.val ((mem_rootsOfUnity n z.1).mp z.2)⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; apply Units.ext; rfl

theorem circlePower_kernel_card (n : ℕ) [NeZero n] :
    Nat.card (powMonoidHom (α := Circle) n).ker = n := by
  rw [Nat.card_congr (kernelEquivRoots n)]
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Circle n

theorem circlePower_kernel_finite (n : ℕ) [NeZero n] :
    Finite (powMonoidHom (α := Circle) n).ker := by
  exact Finite.of_injective (kernelEquivRoots n) (kernelEquivRoots n).injective

#print axioms circlePower_kernel_card
#print axioms circlePower_kernel_finite

end ConstructionTargets.CirclePowerKernelCard
