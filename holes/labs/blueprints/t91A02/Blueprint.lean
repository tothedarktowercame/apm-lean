import Mathlib
import ConstructionTargets.Surfaces
import ConstructionTargets.RationalLefschetz

/-! # t91A02: Euler-characteristic obstruction to a surface cover

The sole missing foundation is multiplicativity of Euler characteristic for
the concrete finite-sheeted cover in the frozen statement.  Once supplied,
the contradiction is integer arithmetic.
-/

open ConstructionTargets.Surfaces
open ConstructionTargets.RationalLefschetz

/-- **LIBRARY.** The rational singular-homology Euler characteristic of the
standard sixteen-crosscap polygon quotient is `-14`. -/
theorem t91A02_surface16_hasEulerCharacteristic :
    HasEulerCharacteristic (Surface false 16) (-14 : ℚ) := by
  sorry

/-- **LIBRARY.** The rational singular-homology Euler characteristic of the
standard eight-crosscap polygon quotient is `-6`. -/
theorem t91A02_surface8_hasEulerCharacteristic :
    HasEulerCharacteristic (Surface false 8) (-6 : ℚ) := by
  sorry

/-- **LIBRARY.** Rational singular-homology Euler characteristic is
multiplicative for the particular positive finite-sheeted cover in this
problem.  The base computation is an explicit hypothesis so this lemma can be
proved independently of `t91A02_surface8_hasEulerCharacteristic`. -/
theorem t91A02_cover_hasEulerCharacteristic_mul
    (p : Surface false 16 → Surface false 8) (sheets : ℕ)
    (hp : IsCoveringMap p) (hsheets : 0 < sheets)
    (hfiber : ∀ x : Surface false 8,
      Nat.card {e : Surface false 16 // p e = x} = sheets)
    (hbase : HasEulerCharacteristic (Surface false 8) (-6 : ℚ)) :
    HasEulerCharacteristic (Surface false 16) ((sheets : ℚ) * (-6 : ℚ)) := by
  sorry

/-- An Euler characteristic represented by the alternating trace in
`HasEulerCharacteristic` is unique. -/
theorem t91A02_hasEulerCharacteristic_unique
    {X : Type} [TopologicalSpace X] {a b : ℚ}
    (ha : HasEulerCharacteristic X a)
    (hb : HasEulerCharacteristic X b) :
    a = b := by
  rcases ha with ⟨hfinite, m, hm, rfl⟩
  rcases hb with ⟨_, n, hn, rfl⟩
  let N := max m n
  have hmN : m + 1 ≤ N + 1 := Nat.add_le_add_right (le_max_left m n) 1
  have hnN : n + 1 ≤ N + 1 := Nat.add_le_add_right (le_max_right m n) 1
  have extend (r : ℕ) (hrN : r + 1 ≤ N + 1)
      (hr : ∀ k, r < k → Subsingleton (Homology X k)) :
      (∑ k ∈ Finset.range (r + 1),
          (-1 : ℚ)^k * LinearMap.trace ℚ (Homology X k)
            (induced (ContinuousMap.id X) k).hom) =
        ∑ k ∈ Finset.range (N + 1),
          (-1 : ℚ)^k * LinearMap.trace ℚ (Homology X k)
            (induced (ContinuousMap.id X) k).hom := by
    apply Finset.sum_subset (Finset.range_mono hrN)
    intro k hkN hkr
    have hrk : r < k := by
      simpa [Finset.mem_range] using hkr
    letI : FiniteDimensional ℚ (Homology X k) := hfinite k
    haveI : Subsingleton (Homology X k) := hr k hrk
    have hz : (induced (ContinuousMap.id X) k).hom = 0 := Subsingleton.elim _ _
    simp [hz]
  exact (extend m hmN hm).trans (extend n hnN hn).symm

/-- **LIBRARY.** Euler characteristic is multiplicative for the finite cover
between the two concrete nonorientable polygon surfaces occurring in the
problem. -/
theorem t91A02_eulerCharacteristic_finite_cover
    (p : Surface false 16 → Surface false 8) (sheets : ℕ)
    (hp : IsCoveringMap p) (hsheets : 0 < sheets)
    (hfiber : ∀ x : Surface false 8,
      Nat.card {e : Surface false 16 // p e = x} = sheets) :
    eulerCharacteristic false 16 =
      (sheets : ℤ) * eulerCharacteristic false 8 := by
  have hbase := t91A02_surface8_hasEulerCharacteristic
  have hcover :=
    t91A02_cover_hasEulerCharacteristic_mul p sheets hp hsheets hfiber hbase
  have hsource := t91A02_surface16_hasEulerCharacteristic
  have hq := t91A02_hasEulerCharacteristic_unique hsource hcover
  norm_num at hq
  norm_num [eulerCharacteristic]
  exact_mod_cast hq

theorem apm_t91a02 :
    ¬ ∃ (p : Surface false 16 → Surface false 8) (sheets : ℕ),
      IsCoveringMap p ∧ 0 < sheets ∧
      ∀ x : Surface false 8, Nat.card {e : Surface false 16 // p e = x} = sheets := by
  rintro ⟨p, sheets, hp, hsheets, hfiber⟩
  have heuler :=
    t91A02_eulerCharacteristic_finite_cover p sheets hp hsheets hfiber
  norm_num [eulerCharacteristic] at heuler
  omega

#print axioms apm_t91a02
