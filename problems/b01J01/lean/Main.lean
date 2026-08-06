import Mathlib

/-!
# APM b01J01: Normal subgroups, quotients, and Sylow subgroups

## Statement repairs

None.

## Encoding questions

None. `Sp(G)` is represented by Mathlib's type `Sylow p G`. To state the
source's set equality across the different ambient groups `G` and `K`, Sylow
subgroups of `K` are mapped into `G` along `K.subtype`; both sides are then
sets of `Subgroup G`.
-/

open Set

noncomputable section

/-- Sylow `p`-subgroups of `K`, regarded as subgroups of the ambient `G`. -/
def apm_b01J01_sylowSubgroupsIn {G : Type} [Group G]
    (p : ℕ) (K : Subgroup G) : Set (Subgroup G) :=
  {Q | ∃ P : Sylow p K, Q = (P : Subgroup K).map K.subtype}

/-- Intersections with `K` of Sylow `p`-subgroups of `G`. -/
def apm_b01J01_sylowTraces {G : Type} [Group G]
    (p : ℕ) (K : Subgroup G) : Set (Subgroup G) :=
  {Q | ∃ P : Sylow p G, Q = (P : Subgroup G) ⊓ K}

theorem apm_b01j01
    (G : Type) [Group G] [Finite G]
    (H K : Subgroup G) [K.Normal]
    (p : ℕ) (hp : p.Prime) :
    (p ∣ Nat.card H → ¬(p ∣ Nat.card ↥(H ⊓ K)) →
      p ∣ Nat.card (G ⧸ K)) ∧
    (p ∣ Nat.card H → ¬(p ∣ Nat.card ↥(H ⊓ commutator G)) →
      ∃ L : Subgroup G, L.index = p) ∧
    apm_b01J01_sylowSubgroupsIn p K =
      apm_b01J01_sylowTraces p K ∧
    Nat.card (Sylow p K) ∣ Nat.card (Sylow p G) := by
  -- SKIPPED: four-part finite group theory problem.
  -- (a) p|H|, p∤|H∩K| ⟹ p|G/K|: use |HK/K| = |H|/|H∩K| and p∤|H∩K|.
  -- (b) p|H|, p∤|H∩G'| ⟹ ∃ subgroup of index p: HK/K surjects onto abelian G/K,
  --     H∩G' kernel, so p | |H/(H∩G')| gives index-p subgroup.
  -- (c) Sylow subgroups of K = {P∩K : P ∈ Syl(G)}: standard Sylow restriction.
  -- (d) |Syl_p(K)| | |Syl_p(G)|: follows from (c) + orbit counting.
  -- Blocker: requires Sylow theorems (partially in Mathlib), commutator subgroup theory,
  -- second isomorphism theorem, index arguments. Each part is a separate nontrivial proof.
  -- APIs: `Sylow`, `Subgroup.Normal`, `commutator`, `Subgroup.index`, `Nat.card`
  sorry
