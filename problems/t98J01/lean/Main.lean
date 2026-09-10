import Mathlib
import ConstructionTargets.RationalLefschetz

/-! # t98J01: Lefschetz number of a sphere/circle product map

S2 and S1 are the printed unit spheres in real coordinates with their subspace
topologies. The maps are the exact half-turn about the z axis and reflection
in the y axis. Lefschetz number means the alternating trace of the induced
maps on actual rational singular homology, with finiteness certificates.
Both source parts are present; the computations and homotopy obstruction are
unproved. No homology ranks or induced maps are supplied as assumptions.
-/

open ConstructionTargets.RationalLefschetz
noncomputable section
namespace T98J01

abbrev S2 := {p : ℝ × ℝ × ℝ // p.1^2 + p.2.1^2 + p.2.2^2 = 1}
abbrev S1 := {p : ℝ × ℝ // p.1^2 + p.2^2 = 1}

def rotation (p : S2) : S2 :=
  ⟨(-p.val.1, -p.val.2.1, p.val.2.2), by simpa using p.property⟩

def reflection (p : S1) : S1 :=
  ⟨(-p.val.1, p.val.2), by simpa using p.property⟩

abbrev ProductSpace := S2 × S1 × S1

def h : C(ProductSpace, ProductSpace) where
  toFun p := (rotation p.1, reflection p.2.1, reflection p.2.2)
  continuous_toFun := by
    unfold rotation reflection
    fun_prop

end T98J01

theorem apm_t98j01 :
    HasLefschetzNumber T98J01.h 8 ∧
    ¬ ContinuousMap.Homotopic T98J01.h (ContinuousMap.id T98J01.ProductSpace) := by
  sorry
