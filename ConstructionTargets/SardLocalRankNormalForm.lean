import Mathlib.Analysis.Calculus.Implicit

/-! # Local rank-coordinate normal form from complemented derivative data -/

open Filter
open scoped Topology
noncomputable section

/-- A local rank-coordinate normal form from a regular output block and a
complementary source-coordinate block. The first output coordinates are
literally `leftFun`; the remaining coordinates parametrize its local fibres. -/
theorem localRankNormalForm_of_complemented_minor
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (φ : ImplicitFunctionData ℝ E F G) :
    ∃ e : OpenPartialHomeomorph E (F × G),
      φ.pt ∈ e.source ∧
      ((e : E → F × G) = fun x => (φ.leftFun x, φ.rightFun x)) ∧
      (∀ᶠ p : F × G in 𝓝 (φ.leftFun φ.pt, φ.rightFun φ.pt),
        φ.leftFun (e.symm p) = p.1 ∧ φ.rightFun (e.symm p) = p.2) := by
  refine ⟨φ.toOpenPartialHomeomorph, φ.pt_mem_toOpenPartialHomeomorph_source, ?_, ?_⟩
  · exact φ.toOpenPartialHomeomorph_coe
  · filter_upwards [φ.prodFun_implicitFunction] with p hp
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

#print axioms localRankNormalForm_of_complemented_minor
