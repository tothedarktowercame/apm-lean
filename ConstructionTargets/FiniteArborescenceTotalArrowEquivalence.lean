import Mathlib.Combinatorics.Quiver.Arborescence
import Mathlib.Combinatorics.Quiver.Subquiver
import Mathlib.Combinatorics.Quiver.Cast

open Quiver

namespace FiniteArborescenceTotalArrow

universe u v

variable (V : Type u) [Quiver.{v} V] [Arborescence V]

noncomputable def targetNonroot (e : Quiver.Total V) :
    {x : V // x ≠ Quiver.root V} := by
  rcases e with ⟨a, b, e⟩
  refine ⟨b, ?_⟩
  intro h
  subst b
  have hp : (default : Path (Quiver.root V) a).cons e =
      (Path.nil : Path (Quiver.root V) (Quiver.root V)) := Subsingleton.elim _ _
  exact Path.cons_ne_nil _ _ hp

theorem targetNonroot_surjective : Function.Surjective (targetNonroot V) := by
  intro x
  let p : Path (Quiver.root V) x.1 := default
  have hn : p.length ≠ 0 := by
    intro hz
    exact x.2 (Path.eq_of_length_zero p hz).symm
  rcases (Path.length_ne_zero_iff_eq_cons p).mp hn with ⟨a, q, e, hp⟩
  refine ⟨⟨a, x.1, e⟩, ?_⟩
  apply Subtype.ext
  rfl

theorem targetNonroot_injective : Function.Injective (targetNonroot V) := by
  rintro ⟨a, c, e⟩ ⟨b, d, f⟩ h
  simp only [targetNonroot, Subtype.mk.injEq] at h
  subst d
  have hp : (default : Path (Quiver.root V) a).cons e =
      (default : Path (Quiver.root V) b).cons f := Subsingleton.elim _ _
  rcases Path.cons.inj hp with ⟨hab, _, hef⟩
  cases hab
  cases eq_of_heq hef
  rfl

noncomputable def totalEquivNonroot :
    Quiver.Total V ≃ {x : V // x ≠ Quiver.root V} :=
  Equiv.ofBijective (targetNonroot V)
    ⟨targetNonroot_injective V, targetNonroot_surjective V⟩

#check totalEquivNonroot
#print axioms totalEquivNonroot

end FiniteArborescenceTotalArrow
