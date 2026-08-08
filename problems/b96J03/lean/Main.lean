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

/-- Mathlib proves nilpotent groups solvable by comparing the derived and
lower central series. -/
lemma apm_b96j03_nilpotent_implies_solvable :
    ∀ (G : Type) [Group G],
      apm_b96j03_IsNilpotent G → apm_b96j03_IsSolvable G := by
  intro G _ h
  change Group.IsNilpotent G at h
  change IsSolvable G
  letI := h
  infer_instance

/-- The order-two transposition subgroup of `S₃`. This construction and its
normalizer argument are reused from the closed `b97J01` artifact. -/
def apm_b96j03_transpositionSubgroup : Subgroup (Equiv.Perm (Fin 3)) where
  carrier := {g | g = 1 ∨ g = Equiv.swap 0 1}
  one_mem' := Or.inl rfl
  mul_mem' := by native_decide +revert
  inv_mem' := by native_decide +revert

lemma apm_b96j03_transpositionSubgroup_normalizer :
    Subgroup.normalizer (apm_b96j03_transpositionSubgroup :
      Set (Equiv.Perm (Fin 3))) = apm_b96j03_transpositionSubgroup := by
  ext g
  rw [Subgroup.mem_normalizer_iff]
  change
    (∀ h : Equiv.Perm (Fin 3),
      (h = 1 ∨ h = Equiv.swap 0 1) ↔
        g * h * g⁻¹ = 1 ∨ g * h * g⁻¹ = Equiv.swap 0 1) ↔
      (g = 1 ∨ g = Equiv.swap 0 1)
  native_decide +revert

lemma apm_b96j03_transpositionSubgroup_ne_top :
    apm_b96j03_transpositionSubgroup ≠ ⊤ := by
  intro h
  have hm : Equiv.swap 1 2 ∈ apm_b96j03_transpositionSubgroup := by
    rw [h]
    exact Subgroup.mem_top _
  change Equiv.swap 1 2 = 1 ∨ Equiv.swap 1 2 = Equiv.swap 0 1 at hm
  have hnot : ¬(Equiv.swap (1 : Fin 3) 2 = (1 : Equiv.Perm (Fin 3)) ∨
      Equiv.swap (1 : Fin 3) 2 = Equiv.swap (0 : Fin 3) 1) := by
    native_decide
  exact hnot hm

lemma apm_b96j03_S3_not_nilpotent :
    ¬Group.IsNilpotent (Equiv.Perm (Fin 3)) := by
  intro h
  letI : Group.IsNilpotent (Equiv.Perm (Fin 3)) := h
  have hfull :=
    normalizerCondition_iff_only_full_group_self_normalizing.mp
      (normalizerCondition_of_isNilpotent (G := Equiv.Perm (Fin 3)))
      apm_b96j03_transpositionSubgroup
      apm_b96j03_transpositionSubgroup_normalizer
  exact apm_b96j03_transpositionSubgroup_ne_top hfull

/-- `S₃` is solvable via its abelian alternating subgroup and the sign map.
This is the extension proof compiled in the closed `b97J01` artifact. -/
lemma apm_b96j03_S3_solvable : IsSolvable (Equiv.Perm (Fin 3)) := by
  have hcomm : ∀ a b : alternatingGroup (Fin 3), a * b = b * a := by
    native_decide
  letI : IsSolvable (alternatingGroup (Fin 3)) := isSolvable_of_comm hcomm
  have hker : Equiv.Perm.sign.ker ≤
      (alternatingGroup (Fin 3)).subtype.range := by
    rw [← alternatingGroup_eq_sign_ker, Subgroup.range_subtype]
  exact solvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype
    Equiv.Perm.sign hker

lemma apm_b96j03_solvable_not_nilpotent_exists :
    ∃ (G : Type) (_ : Group G),
      @apm_b96j03_IsSolvable G ‹Group G› ∧
      ¬@apm_b96j03_IsNilpotent G ‹Group G› := by
  refine ⟨Equiv.Perm (Fin 3), inferInstance, ?_, ?_⟩
  · exact apm_b96j03_S3_solvable
  · exact apm_b96j03_S3_not_nilpotent

theorem apm_b96j03 :
    (∀ (G : Type) [Group G],
      apm_b96j03_IsNilpotent G → apm_b96j03_IsSolvable G) ∧
    (∃ (G : Type) (_ : Group G),
      @apm_b96j03_IsSolvable G ‹Group G› ∧
      ¬@apm_b96j03_IsNilpotent G ‹Group G›) ∧
    ¬apm_b96j03_IsSolvable apm_b96j03_G ∧
    ¬apm_b96j03_IsNilpotent apm_b96j03_G := by
  refine ⟨apm_b96j03_nilpotent_implies_solvable,
    apm_b96j03_solvable_not_nilpotent_exists, ?_⟩
  /-
  CLOSER HOP 1 BOUNDARY (statement unchanged).

  The first two conjuncts are now fully compiled. The implication uses
  `Group.IsNilpotent.to_isSolvable`. The converse counterexample is `S₃`, with
  solvability proved through the sign extension and nonnilpotence through the
  proper self-normalizing subgroup `{1, (01)}`; this code is reused from the
  closed `b97J01` artifact at git commit `f453ba3`.

  The remaining presentation is not the semidirect product described in the
  imported proof plan: there is no relation between `b` and `c`. The relations
  instead make `a` central and leave the subgroup generated by `b,c` with the
  free-product presentation `C₃ * C₇`; hence the intended route is an
  isomorphism `G ≃ C₂ × (C₃ * C₇)` (or a quotient onto a known nonsolvable
  group), followed by nonsolvability of that free product. Searches of
  `LEMMA-INDEX.md`, `ConstructionTargets`, prior presented-group artifacts,
  Mathlib's `PresentedGroup`, `Monoid.Coprod`/`CoprodI`, solvable, and
  nilpotent APIs, and git history found no packaged Tietze transformation,
  this presentation isomorphism, or a ready nonsolvability theorem for
  `C₃ * C₇`. Since
  nonnilpotence follows immediately from nonsolvability, this is the sole live
  mathematical bridge.
  -/
  sorry
