import Mathlib
import Mathlib.GroupTheory.PresentedGroup

/-!
# APM b96J03

## Statement repairs

The supplied solution fragment gives a ring-theoretic nilpotence condition
`rⁿ = 0`, which is not a definition of a nilpotent group. The problem itself
is stated with Mathlib's standard group-theoretic lower-central-series notion.

## Encoding questions

None. Solvability and nilpotence use Mathlib's standard predicates. The group
in part (c) is the concrete presented group on generators `a,b,c`, with the
three power relations and two commutation relations listed in the source.
-/

def apm_b96j03_IsNilpotent (G : Type*) [Group G] : Prop :=
  Group.IsNilpotent G

def apm_b96j03_IsSolvable (G : Type*) [Group G] : Prop :=
  IsSolvable G

def apm_b96j03_a : FreeGroup (Fin 3) := FreeGroup.of 0
def apm_b96j03_b : FreeGroup (Fin 3) := FreeGroup.of 1
def apm_b96j03_c : FreeGroup (Fin 3) := FreeGroup.of 2

def apm_b96j03_relations : Set (FreeGroup (Fin 3)) :=
  {apm_b96j03_a ^ 2,
   apm_b96j03_b ^ 3,
   apm_b96j03_c ^ 7,
   apm_b96j03_a * apm_b96j03_b * apm_b96j03_a⁻¹ * apm_b96j03_b⁻¹,
   apm_b96j03_a * apm_b96j03_c * apm_b96j03_a⁻¹ * apm_b96j03_c⁻¹}

abbrev apm_b96j03_G := PresentedGroup apm_b96j03_relations

theorem apm_b96j03 :
    (∀ (G : Type) [Group G],
      apm_b96j03_IsNilpotent G → apm_b96j03_IsSolvable G) ∧
    (∃ (G : Type) (_ : Group G),
      @apm_b96j03_IsSolvable G ‹Group G› ∧
      ¬@apm_b96j03_IsNilpotent G ‹Group G›) ∧
    ¬apm_b96j03_IsSolvable apm_b96j03_G ∧
    ¬apm_b96j03_IsNilpotent apm_b96j03_G := by
  sorry
