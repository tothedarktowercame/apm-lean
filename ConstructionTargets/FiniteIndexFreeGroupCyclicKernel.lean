import Mathlib
import ConstructionTargets.FiniteIndexFreeGroupSchreierRank

noncomputable section

namespace ConstructionTargets.FiniteIndexFreeGroupCyclicKernel

open FiniteIndexFreeGroupSchreierRank

/-- Send every free generator to the standard generator of a finite cyclic
group. For a nonempty generator type this map is onto. -/
def cyclicQuotient (n d : ℕ) :
    FreeGroup (Fin n) →* Multiplicative (ZMod d) :=
  FreeGroup.lift fun _ => Multiplicative.ofAdd 1

theorem cyclicQuotient_surjective (n d : ℕ) (hn : 0 < n) :
    Function.Surjective (cyclicQuotient n d) := by
  intro z
  let a : ZMod d := Multiplicative.toAdd z
  let k : ℤ := Classical.choose (ZMod.intCast_surjective a)
  have hk : (k : ZMod d) = a := Classical.choose_spec (ZMod.intCast_surjective a)
  refine ⟨FreeGroup.of (⟨0, hn⟩ : Fin n) ^ k, ?_⟩
  apply Multiplicative.toAdd.injective
  simpa [cyclicQuotient, a] using hk

/-- The kernel of the cyclic quotient has the prescribed positive index and
the Schreier rank predicted by the finite-index formula. -/
theorem exists_subgroup_of_index (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    ∃ G : Subgroup (FreeGroup (Fin n)),
      G.FiniteIndex ∧ G.index = d ∧
      Nonempty (G ≃* FreeGroup (Fin (1 + d * (n - 1)))) := by
  letI : NeZero d := ⟨hd.ne'⟩
  letI : Fact (0 < d) := ⟨hd⟩
  letI : Fintype (ZMod d) := inferInstance
  letI : Finite (Multiplicative (ZMod d)) :=
    Finite.of_equiv (ZMod d) Multiplicative.ofAdd
  let φ := cyclicQuotient n d
  have hsurj : Function.Surjective φ := cyclicQuotient_surjective n d hn
  have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  have hindex : φ.ker.index = d := by
    rw [Subgroup.index_ker]
    calc
      Nat.card φ.range = Nat.card (Multiplicative (ZMod d)) := by
        rw [hrange]
        exact Nat.card_congr (Equiv.Set.univ _)
      _ = Nat.card (ZMod d) := Nat.card_congr Multiplicative.toAdd
      _ = d := by rw [Nat.card_eq_fintype_card, ZMod.card]
  letI : Finite φ.range :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hfinite : φ.ker.FiniteIndex := inferInstance
  refine ⟨φ.ker, hfinite, hindex, ⟨?_⟩⟩
  have hcard : (n - 1) * d + 1 = 1 + d * (n - 1) := by
    rw [Nat.mul_comm]
    omega
  exact (finiteIndexSubgroupFreeGroupEquiv n d hn hd φ.ker hindex).trans
    (FreeGroup.freeGroupCongr (finCongr hcard))

#print axioms cyclicQuotient_surjective
#print axioms exists_subgroup_of_index

end ConstructionTargets.FiniteIndexFreeGroupCyclicKernel
