import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

open MulAction

namespace ConstructionTargets.FiniteSchreierCosetQuiverPositiveIndex

variable (r n : ℕ) (hr : 0 < r) (hn : 0 < n)
variable (H : Subgroup (FreeGroup (Fin r))) (hindex : H.index = n)

@[reducible] noncomputable def vertexFintype (r n : ℕ) (hn : 0 < n)
    (H : Subgroup (FreeGroup (Fin r))) (hindex : H.index = n) :
    Fintype (FreeGroup (Fin r) ⧸ H) :=
  H.fintypeOfIndexNeZero (hindex ▸ Nat.ne_of_gt hn)

theorem vertex_card : @Fintype.card (FreeGroup (Fin r) ⧸ H)
    (vertexFintype r n hn H hindex) = n := by
  letI := vertexFintype r n hn H hindex
  rw [← Nat.card_eq_fintype_card]
  simpa [Subgroup.index_eq_card] using hindex

@[reducible] noncomputable def positiveEdgeFintype (r n : ℕ) (hn : 0 < n)
    (H : Subgroup (FreeGroup (Fin r))) (hindex : H.index = n) :
    Fintype (Fin r × (FreeGroup (Fin r) ⧸ H)) :=
  letI := vertexFintype r n hn H hindex
  inferInstance

def generatorPermutation (i : Fin r) : Equiv.Perm (FreeGroup (Fin r) ⧸ H) :=
  MulAction.toPerm (FreeGroup.of i)

def inverseGeneratorPermutation (i : Fin r) :
    Equiv.Perm (FreeGroup (Fin r) ⧸ H) :=
  MulAction.toPerm (FreeGroup.of i)⁻¹

theorem generatorPermutation_inverse (i : Fin r) :
    (generatorPermutation r H i).symm = inverseGeneratorPermutation r H i := by
  ext v
  change (FreeGroup.of i)⁻¹ • v = (FreeGroup.of i)⁻¹ • v
  rfl

theorem connected_from_identity (v : FreeGroup (Fin r) ⧸ H) :
    ∃ g : FreeGroup (Fin r),
      g • ((1 : FreeGroup (Fin r)) : FreeGroup (Fin r) ⧸ H) = v := by
  exact MulAction.exists_smul_eq (FreeGroup (Fin r)) _ _

theorem positive_edge_card :
    letI := vertexFintype r n hn H hindex
    Fintype.card (Fin r × (FreeGroup (Fin r) ⧸ H)) = r * n := by
  letI := vertexFintype r n hn H hindex
  rw [Fintype.card_prod, Fintype.card_fin, vertex_card r n hn H hindex]

#print axioms vertex_card
#print axioms generatorPermutation_inverse
#print axioms connected_from_identity
#print axioms positive_edge_card

end ConstructionTargets.FiniteSchreierCosetQuiverPositiveIndex
