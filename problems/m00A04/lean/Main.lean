import Mathlib

/-!
# APM m00A04: Hilbert-space minimization and a weak elliptic solution

## Statement repairs

In part (a), the strict-minimum clause prints `V ≠ u`; since `V` is the
ambient space, this is ill-typed. We replace it by the intended `v ≠ u`.

## Encoding questions

This Mathlib snapshot has no packaged `H¹₀(Ω)` space. Rather than replacing it
by a scalar shadow, `apm_m00A04_memH10WithGradient` explicitly encodes its
standard definition: an `L²` function with `L²` distributional weak gradient
that is approximable in the energy norm by smooth compactly supported tests.
-/

open MeasureTheory Set Function
open scoped ContDiff BigOperators RealInnerProductSpace

noncomputable section

def apm_m00A04_phi {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V →L[ℝ] ℝ) (v : V) : ℝ :=
  (1 / 2 : ℝ) * ‖v‖ ^ 2 - f v

def apm_m00A04_testFunction {n : ℕ} (U : Set (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ IsCompact (support φ) ∧ support φ ⊆ U

def apm_m00A04_partial {n : ℕ} (φ : (Fin n → ℝ) → ℝ)
    (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ φ x (Pi.single i 1)

def apm_m00A04_L2On {n : ℕ} (U : Set (Fin n → ℝ))
    (u : (Fin n → ℝ) → ℝ) : Prop :=
  IntegrableOn (fun x ↦ |u x| ^ 2) U

def apm_m00A04_weakGradient {n : ℕ} (U : Set (Fin n → ℝ))
    (u : (Fin n → ℝ) → ℝ)
    (g : Fin n → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (i : Fin n) (φ : (Fin n → ℝ) → ℝ),
    apm_m00A04_testFunction U φ →
      (∫ x in U, u x * apm_m00A04_partial φ i x) =
        -∫ x in U, g i x * φ x

/-- An explicit representative-level encoding of `u ∈ H¹₀(U)` with weak
gradient `g`. -/
def apm_m00A04_memH10WithGradient {n : ℕ} (U : Set (Fin n → ℝ))
    (u : (Fin n → ℝ) → ℝ)
    (g : Fin n → (Fin n → ℝ) → ℝ) : Prop :=
  apm_m00A04_L2On U u ∧
  (∀ i, apm_m00A04_L2On U (g i)) ∧
  apm_m00A04_weakGradient U u g ∧
  ∀ ε : ℝ, 0 < ε →
    ∃ φ : (Fin n → ℝ) → ℝ,
      apm_m00A04_testFunction U φ ∧
      (∫ x in U,
        |u x - φ x| ^ 2 +
          ∑ i : Fin n, |g i x - apm_m00A04_partial φ i x| ^ 2) < ε

theorem apm_m00a04
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (f : V →L[ℝ] ℝ) :
    BddBelow (range (apm_m00A04_phi f)) ∧
    (∃ u : V,
      (∀ v : V, apm_m00A04_phi f u ≤ apm_m00A04_phi f v) ∧
      (∀ v : V, v ≠ u → apm_m00A04_phi f u < apm_m00A04_phi f v) ∧
      ∀ v : V, inner ℝ u v = f v) ∧
    ∀ (n : ℕ) (U : Set (Fin n → ℝ)),
      U.Nonempty → IsOpen U → Bornology.IsBounded U →
      ∀ F : (Fin n → ℝ) → ℝ, apm_m00A04_L2On U F →
        ∃ (u : (Fin n → ℝ) → ℝ)
          (g : Fin n → (Fin n → ℝ) → ℝ),
          apm_m00A04_memH10WithGradient U u g ∧
          ∀ (v : (Fin n → ℝ) → ℝ)
            (h : Fin n → (Fin n → ℝ) → ℝ),
            apm_m00A04_memH10WithGradient U v h →
              (∫ x in U,
                (∑ i : Fin n, g i x * h i x) + u x * v x) =
              ∫ x in U, F x * v x := by
  sorry
