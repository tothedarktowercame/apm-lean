import Mathlib

/-!
# APM m93J02: Local and global Hölder seminorms

## Statement repairs

1. The global denominator is printed as `|x - y^α|`; it must be
   `|x-y|^α`, matching the standard Hölder seminorm and the rest of the
   problem.
2. The problem omits the range of `α` and permits a singleton `Ω`, although
   the requested counterexamples and completeness verdicts require the strict
   Hölder range `0 < α < 1` and at least two points. We add those hypotheses,
   as used by the supplied solution.

## Encoding questions

None. Potentially infinite seminorms are represented in `ℝ≥0∞`. The norm
axioms and metric completeness are stated explicitly on the common finite
Hölder space, avoiding any assumption that the desired norm instances already
exist in Mathlib.
-/

open Set Metric
open scoped ENNReal

noncomputable section

def apm_m93J02_quotient {n : ℕ} {U : Set (Fin n → ℝ)} (α : ℝ)
    (f : U → ℝ) (y z : U) : ℝ≥0∞ :=
  ENNReal.ofReal (|f z - f y| / dist (z : Fin n → ℝ) y ^ α)

/-- The infinitesimal/local Hölder seminorm from the source. -/
def apm_m93J02_localSeminorm {n : ℕ} (U : Set (Fin n → ℝ))
    (α : ℝ) (f : U → ℝ) : ℝ≥0∞ :=
  ⨆ x : U,
    Filter.limsup
      (fun ε : ℝ ↦
        ⨆ y : U, ⨆ z : U,
          if dist (y : Fin n → ℝ) x ≤ ε ∧
              dist (z : Fin n → ℝ) x ≤ ε ∧ z ≠ y then
            apm_m93J02_quotient α f y z
          else 0)
      (nhdsWithin 0 (Ioi 0))

/-- The usual global Hölder seminorm. -/
def apm_m93J02_globalSeminorm {n : ℕ} (U : Set (Fin n → ℝ))
    (α : ℝ) (f : U → ℝ) : ℝ≥0∞ :=
  ⨆ y : U, ⨆ z : U,
    if z ≠ y then apm_m93J02_quotient α f y z else 0

def apm_m93J02_supNorm {n : ℕ} {U : Set (Fin n → ℝ)}
    (f : U → ℝ) : ℝ≥0∞ :=
  ⨆ x : U, ENNReal.ofReal |f x|

def apm_m93J02_holderFunctions {n : ℕ} (U : Set (Fin n → ℝ))
    (α : ℝ) : Set (U → ℝ) :=
  {f | apm_m93J02_globalSeminorm U α f ≠ ⊤}

def apm_m93J02_localNorm {n : ℕ} (U : Set (Fin n → ℝ))
    (α : ℝ) (f : U → ℝ) : ℝ :=
  (apm_m93J02_localSeminorm U α f + apm_m93J02_supNorm f).toReal

def apm_m93J02_globalNorm {n : ℕ} (U : Set (Fin n → ℝ))
    (α : ℝ) (f : U → ℝ) : ℝ :=
  (apm_m93J02_globalSeminorm U α f + apm_m93J02_supNorm f).toReal

/-- The norm axioms restricted to a specified vector subspace carrier. -/
def apm_m93J02_isNormOn {V : Type} [AddCommGroup V] [Module ℝ V]
    (S : Set V) (q : V → ℝ) : Prop :=
  q 0 = 0 ∧
  (∀ f ∈ S, q f = 0 → f = 0) ∧
  (∀ (c : ℝ) f, f ∈ S → q (c • f) = |c| * q f) ∧
  ∀ f ∈ S, ∀ g ∈ S, q (f + g) ≤ q f + q g

/-- Sequential completeness for the metric induced by `q` on `S`. -/
def apm_m93J02_isCompleteOn {V : Type} [AddCommGroup V]
    (S : Set V) (q : V → ℝ) : Prop :=
  ∀ u : ℕ → V, (∀ n, u n ∈ S) →
    (∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, q (u m - u n) < ε) →
    ∃ f ∈ S, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, q (u n - f) < ε

theorem apm_m93j02
    (n : ℕ) (U : Set (Fin n → ℝ)) (hUcompact : IsCompact U)
    (hUconnected : IsConnected U)
    (hUnontrivial : ∃ x ∈ U, ∃ y ∈ U, x ≠ y)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ f : U → ℝ,
      apm_m93J02_localSeminorm U α f ≠ ⊤ →
        apm_m93J02_globalSeminorm U α f ≠ ⊤) ∧
    (∀ f : U → ℝ,
      apm_m93J02_globalSeminorm U α f ≠ ⊤ →
        apm_m93J02_localSeminorm U α f ≠ ⊤) ∧
    (∀ f : U → ℝ,
      apm_m93J02_localSeminorm U α f ≤
        apm_m93J02_globalSeminorm U α f) ∧
    ¬(∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ f : U → ℝ,
      apm_m93J02_globalSeminorm U α f ≤
        K * apm_m93J02_localSeminorm U α f) ∧
    apm_m93J02_isNormOn (apm_m93J02_holderFunctions U α)
      (apm_m93J02_localNorm U α) ∧
    ¬apm_m93J02_isCompleteOn (apm_m93J02_holderFunctions U α)
      (apm_m93J02_localNorm U α) ∧
    apm_m93J02_isNormOn (apm_m93J02_holderFunctions U α)
      (apm_m93J02_globalNorm U α) ∧
    apm_m93J02_isCompleteOn (apm_m93J02_holderFunctions U α)
      (apm_m93J02_globalNorm U α) := by
  have hle : ∀ f : U → ℝ,
      apm_m93J02_localSeminorm U α f ≤
        apm_m93J02_globalSeminorm U α f := by
    intro f
    unfold apm_m93J02_localSeminorm apm_m93J02_globalSeminorm
    refine iSup_le fun x ↦ Filter.limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [] with ε
    refine iSup_le fun y ↦ iSup_le fun z ↦ ?_
    split_ifs with hyz
    · exact le_iSup_of_le y (le_iSup_of_le z (by simp [hyz.2.2]))
    · exact bot_le
  have hglobal_local : ∀ f : U → ℝ,
      apm_m93J02_globalSeminorm U α f ≠ ⊤ →
        apm_m93J02_localSeminorm U α f ≠ ⊤ := by
    intro f hf htop
    exact hf (top_unique (htop ▸ hle f))
  /-
  Boundary: the remaining clauses require a compactness/cluster-point proof
  that finite local limsup forces a finite global seminorm, an explicit
  nonconstant Lipschitz function on an arbitrary compact connected nontrivial
  subtype (and proof that its local ENNReal limsup is zero), the ENNReal
  algebra needed for both norm predicates, and complete/incomplete sequence
  constructions for the two induced metrics. I searched and used
  `Filter.limsup_le_of_le` for the easy inequality above; no compiled sibling
  supplied the required local-limsup compactness or completeness machinery.
  -/
  have hremaining :
      (∀ f : U → ℝ,
        apm_m93J02_localSeminorm U α f ≠ ⊤ →
          apm_m93J02_globalSeminorm U α f ≠ ⊤) ∧
      ¬(∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ f : U → ℝ,
        apm_m93J02_globalSeminorm U α f ≤
          K * apm_m93J02_localSeminorm U α f) ∧
      apm_m93J02_isNormOn (apm_m93J02_holderFunctions U α)
        (apm_m93J02_localNorm U α) ∧
      ¬apm_m93J02_isCompleteOn (apm_m93J02_holderFunctions U α)
        (apm_m93J02_localNorm U α) ∧
      apm_m93J02_isNormOn (apm_m93J02_holderFunctions U α)
        (apm_m93J02_globalNorm U α) ∧
      apm_m93J02_isCompleteOn (apm_m93J02_holderFunctions U α)
        (apm_m93J02_globalNorm U α) := by
    sorry
  exact ⟨hremaining.1, hglobal_local, hle,
    hremaining.2.1, hremaining.2.2.1, hremaining.2.2.2.1,
    hremaining.2.2.2.2.1, hremaining.2.2.2.2.2⟩
