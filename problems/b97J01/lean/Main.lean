import Mathlib

/-!
# APM b97J01 — solvable and nilpotent groups; finite p-groups

## Statement repairs

None.

## Encoding notes

Solvability and nilpotence are defined using the derived and lower central
series, respectively.  The requested examples are the explicit groups `S₅`
and `S₃`, represented as permutation groups on `Fin 5` and `Fin 3`.
-/

def apm_b97j01_solvable (G : Type) [Group G] : Prop :=
  ∃ n : ℕ, derivedSeries G n = ⊥

def apm_b97j01_nilpotent (G : Type) [Group G] : Prop :=
  ∃ n : ℕ, lowerCentralSeries G n = ⊥

lemma apm_b97j01_S5_not_solvable :
    ¬apm_b97j01_solvable (Equiv.Perm (Fin 5)) := by
  rintro ⟨n, hn⟩
  exact Equiv.Perm.fin_5_not_solvable ⟨⟨n, hn⟩⟩

lemma apm_b97j01_pgroup_center_ne_bot
    (G : Type) [Group G] [Fintype G] (p n : ℕ)
    (hp : p.Prime) (hcard : Fintype.card G = p ^ n)
    (hne : 1 < p ^ n) : Subgroup.center G ≠ ⊥ := by
  letI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp (hcard.trans_gt hne)
  have hpg : IsPGroup p G := IsPGroup.of_card (by simpa [Nat.card_eq_fintype_card] using hcard)
  exact ne_of_gt hpg.bot_lt_center

lemma apm_b97j01_pgroup_nilpotent
    (G : Type) [Group G] [Fintype G] (p n : ℕ)
    (hp : p.Prime) (hcard : Fintype.card G = p ^ n) :
    apm_b97j01_nilpotent G := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p G := IsPGroup.of_card (by simpa [Nat.card_eq_fintype_card] using hcard)
  exact nilpotent_iff_lowerCentralSeries.mp hpg.isNilpotent

theorem apm_b97j01 :
    ¬apm_b97j01_solvable (Equiv.Perm (Fin 5)) ∧
    apm_b97j01_solvable (Equiv.Perm (Fin 3)) ∧
    ¬apm_b97j01_nilpotent (Equiv.Perm (Fin 3)) ∧
    (∀ (G : Type) [Group G] [Fintype G] (p n : ℕ),
      p.Prime → Fintype.card G = p ^ n → 1 < p ^ n →
        Subgroup.center G ≠ ⊥) ∧
    (∀ (G : Type) [Group G] [Fintype G] (p n : ℕ),
      p.Prime → Fintype.card G = p ^ n →
        apm_b97j01_nilpotent G) := by
  /-
  Boundary (pass-1 Codex, skipped): Mathlib directly supplies the large-group
  and p-group ingredients: `Equiv.Perm.fin_5_not_solvable`,
  `IsPGroup.of_card`, `IsPGroup.bot_lt_center`, `IsPGroup.isNilpotent`, and
  `nilpotent_iff_lowerCentralSeries`. These bridge the first, fourth, and fifth
  conjuncts to the statement's explicit series definitions after routine
  `Fintype.card`/`Nat.card` and `Fact p.Prime` conversions. Closer hop 1 now
  compiles all three bridges as `apm_b97j01_S5_not_solvable`,
  `apm_b97j01_pgroup_center_ne_bot`, and
  `apm_b97j01_pgroup_nilpotent`. The latter two explicitly construct the
  `Fact p.Prime`, `IsPGroup`, and (where necessary) `Nontrivial` instances,
  then apply `IsPGroup.bot_lt_center`, `IsPGroup.isNilpotent`, and
  `nilpotent_iff_lowerCentralSeries`.

  Local source and proved-sibling searches found no packaged results for the
  two concrete `Equiv.Perm (Fin 3)` conjuncts. Closing them requires either
  explicit computations proving `derivedSeries _ 2 = ⊥` and showing the lower
  central series stalls, or a formal self-normalizing proper subgroup combined
  with `normalizerCondition_of_isNilpotent`. The subgroup closures in these
  series are not exposed by the searched API as finite decidable tables, and no
  sibling contains the needed `S₃` computation. Renewed searches of
  `LEMMA-INDEX.md`, all closed artifacts, `ConstructionTargets/`, and the
  solvable/nilpotent sources found no shorter concrete route. The statement appears
  mathematically sound; the blocker is this concrete finite-group bridge.
  -/
  sorry
