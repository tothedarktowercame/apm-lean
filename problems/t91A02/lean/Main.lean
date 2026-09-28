import Mathlib
import ConstructionTargets.Surfaces

/-!
# APM t91A02 — the Euler-characteristic obstruction to a surface cover

## Statement repairs

None.

## Encoding note

`apm_t91a02_Surface g` is an honestly axiomatised model of the connected sum
of `g` real projective planes: it retains the carrier, topology, compactness,
connectedness, and the defining Euler characteristic `2-g`.  A candidate cover
retains its actual topological map and `IsCoveringMap` witness, together with
the standard finite-sheet and Euler-multiplicativity data used by the problem.
This is necessary because Mathlib has covering maps but no construction of
connected sums of projective planes or Euler characteristic for them.
-/

structure apm_t91a02_Surface (genus : ℕ) where
  Carrier : Type
  topology : TopologicalSpace Carrier
  compact : @CompactSpace Carrier topology
  connected : @ConnectedSpace Carrier topology
  eulerCharacteristic : ℤ
  euler_eq : eulerCharacteristic = 2 - (genus : ℤ)

def apm_t91a02_HasFiniteCover
    {gE gB : ℕ} (E : apm_t91a02_Surface gE)
    (B : apm_t91a02_Surface gB) : Prop :=
  letI := E.topology
  letI := B.topology
  ∃ (p : E.Carrier → B.Carrier) (sheets : ℕ),
    IsCoveringMap p ∧ 0 < sheets ∧
      E.eulerCharacteristic = (sheets : ℤ) * B.eulerCharacteristic

/-- Superseded: `HasFiniteCover` included Euler-characteristic
multiplicativity as a hypothesis and its carriers were not the named surfaces. -/
theorem apm_t91a02_previous_encoding
    (E : apm_t91a02_Surface 16) (B : apm_t91a02_Surface 8) :
    ¬apm_t91a02_HasFiniteCover E B := by
  intro hcover
  dsimp [apm_t91a02_HasFiniteCover] at hcover
  obtain ⟨p, sheets, hp, hsheets, heuler⟩ := hcover
  have hE := E.euler_eq
  have hB := B.euler_eq
  norm_num at hE hB
  rw [hE, hB] at heuler
  omega

open ConstructionTargets.Surfaces

/-- Faithful statement: there is no finite-sheeted covering map from the
concrete connected sum of sixteen projective planes onto the concrete
connected sum of eight.  No Euler-characteristic equation is assumed. -/
theorem apm_t91a02 :
    ¬ ∃ (p : Surface false 16 → Surface false 8) (sheets : ℕ),
      IsCoveringMap p ∧ 0 < sheets ∧
      ∀ x : Surface false 8, Nat.card {e : Surface false 16 // p e = x} = sheets := by
  sorry
