import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Connected.LocPathConnected
noncomputable section
open Set Function
namespace ConstructionTargets.CoveringLiftRestriction
variable {E B A D : Type*} [TopologicalSpace E] [TopologicalSpace B]
 [TopologicalSpace A] [TopologicalSpace D]
variable (p : E → B)
def Lifts (s : C(A,B)) := {l : C(A,E) // p ∘ l = s}
variable {p}
def evaluate (s : C(A,B)) (a : A) (l : Lifts p s) : {e : E // p e = s a} :=
 ⟨l.1 a, congrFun l.2 a⟩

theorem evaluate_bijective (hp : IsCoveringMap p) [SimplyConnectedSpace A]
 [LocPathConnectedSpace A] (s : C(A,B)) (a : A) : Function.Bijective (evaluate s a (p := p)) := by
 constructor
 · intro l m h
   apply Subtype.ext
   apply ContinuousMap.coe_injective
   exact hp.eq_of_comp_eq l.1.continuous m.1.continuous (l.2.trans m.2.symm) a (congrArg Subtype.val h)
 · intro e
   obtain ⟨l,hl,_⟩ := hp.existsUnique_continuousMap_lifts s a e.1 e.2
   exact ⟨⟨l,hl.2⟩, Subtype.ext hl.1⟩

def evaluationEquiv (hp : IsCoveringMap p) [SimplyConnectedSpace A]
 [LocPathConnectedSpace A] (s : C(A,B)) (a : A) : Lifts p s ≃ {e : E // p e = s a} :=
 Equiv.ofBijective (evaluate s a) (evaluate_bijective hp s a)

def restrict (s : C(A,B)) (i : C(D,A)) (l : Lifts p s) : Lifts p (s.comp i) :=
 ⟨l.1.comp i, by funext x; exact congrFun l.2 (i x)⟩

@[simp] theorem restrict_value (s : C(A,B)) (i : C(D,A)) (l : Lifts p s) (x : D) :
 (restrict s i l).1 x = l.1 (i x) := rfl

theorem restrict_bijective (hp : IsCoveringMap p) [SimplyConnectedSpace A]
 [LocPathConnectedSpace A] [SimplyConnectedSpace D] [LocPathConnectedSpace D]
 (s : C(A,B)) (i : C(D,A)) (d : D) : Function.Bijective (restrict (p := p) s i) := by
 have hA := evaluate_bijective hp s (i d)
 have hD := evaluate_bijective hp (s.comp i) d
 constructor
 · intro l m h
   apply hA.1
   exact congrArg (evaluate (s.comp i) d) h
 · intro l
   obtain ⟨m,hm⟩ := hA.2 (evaluate (s.comp i) d l)
   exact ⟨m, hD.1 hm⟩

def restrictionEquiv (hp : IsCoveringMap p) [SimplyConnectedSpace A]
 [LocPathConnectedSpace A] [SimplyConnectedSpace D] [LocPathConnectedSpace D]
 (s : C(A,B)) (i : C(D,A)) (d : D) : Lifts p s ≃ Lifts p (s.comp i) :=
 Equiv.ofBijective (restrict s i) (restrict_bijective hp s i d)

theorem card_lifts (hp : IsCoveringMap p) [SimplyConnectedSpace A]
 [LocPathConnectedSpace A] (s : C(A,B)) (a : A) :
 Nat.card (Lifts p s) = Nat.card {e : E // p e = s a} :=
 Nat.card_congr (evaluationEquiv hp s a)

local instance simplexContractible (n : ℕ) : ContractibleSpace (stdSimplex ℝ (Fin (n+1))) :=
 (convex_stdSimplex ℝ _).contractibleSpace ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n+1))⟩
local instance simplexLocPath (n : ℕ) : LocPathConnectedSpace (stdSimplex ℝ (Fin (n+1))) :=
 (convex_stdSimplex ℝ _).locPathConnectedSpace

theorem simplex_restriction_bijective (hp : IsCoveringMap p) (n m : ℕ)
 (s : C(stdSimplex ℝ (Fin (n+1)),B))
 (i : C(stdSimplex ℝ (Fin (m+1)), stdSimplex ℝ (Fin (n+1)))) :
 Function.Bijective (restrict (p := p) s i) :=
 restrict_bijective hp s i ⟨_, single_mem_stdSimplex ℝ (0 : Fin (m+1))⟩

#print axioms simplex_restriction_bijective
#print axioms evaluate_bijective
#print axioms restrict_bijective
#print axioms card_lifts
end ConstructionTargets.CoveringLiftRestriction
