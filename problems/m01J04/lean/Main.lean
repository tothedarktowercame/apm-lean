import Mathlib

/-!
# APM m01J04: Weak convergence and compensated compactness

## Statement repairs

Parts (b) and (c) use the compact embedding `H¹(Ω) ↪ L²(Ω)`, which is false
for an arbitrary domain (translations on an unbounded domain are a standard
counterexample). We therefore add the exact required hypothesis that `Ω` has
the Rellich compactness property. This covers, in particular, the bounded
Lipschitz domains intended by the supplied solution.

## Encoding questions

None. `H¹(Ω)` is represented by a function, its genuine weak gradient, and
their `L²` conditions. Weak convergence and strong `H⁻¹` convergence are
spelled out through their defining dual pairings on the actual domain.
-/

open Filter MeasureTheory Set

noncomputable section

def apm_m01J04_weaklyConverges {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (f : ℕ → X) (x : X) : Prop :=
  ∀ g : X →L[ℝ] ℝ, Tendsto (fun n ↦ g (f n)) atTop (nhds (g x))

structure apm_m01J04_H1 (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) where
  val : EuclideanSpace ℝ (Fin d) → ℝ
  grad : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)
  val_memLp : MemLp val 2 (volume.restrict Ω)
  grad_memLp : MemLp grad 2 (volume.restrict Ω)
  weakGradient : ∀ (φ : EuclideanSpace ℝ (Fin d) → ℝ),
    ContDiff ℝ ⊤ φ → HasCompactSupport φ → Function.support φ ⊆ Ω →
      ∀ i : Fin d,
        (∫ x in Ω, val x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          -(∫ x in Ω, grad x i * φ x)

def apm_m01J04_H1norm {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (u : apm_m01J04_H1 d Ω) : ℝ :=
  (eLpNorm u.val 2 (volume.restrict Ω)).toReal +
    (eLpNorm u.grad 2 (volume.restrict Ω)).toReal

def apm_m01J04_H1dist {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (u w : apm_m01J04_H1 d Ω) : ℝ :=
  (eLpNorm (fun x ↦ u.val x - w.val x) 2 (volume.restrict Ω)).toReal +
    (eLpNorm (fun x ↦ u.grad x - w.grad x) 2 (volume.restrict Ω)).toReal

def apm_m01J04_isH1Zero {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (h : apm_m01J04_H1 d Ω) : Prop :=
  ∃ approximant : ℕ → apm_m01J04_H1 d Ω,
    (∀ n, ContDiff ℝ ⊤ (approximant n).val ∧
      HasCompactSupport (approximant n).val ∧
      Function.support (approximant n).val ⊆ Ω) ∧
    Tendsto (fun n ↦ apm_m01J04_H1dist (approximant n) h) atTop (nhds 0)

def apm_m01J04_H1WeaklyConverges {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (u : ℕ → apm_m01J04_H1 d Ω) (w : apm_m01J04_H1 d Ω) : Prop :=
  (∀ q : EuclideanSpace ℝ (Fin d) → ℝ,
    MemLp q 2 (volume.restrict Ω) →
      Tendsto (fun n ↦ ∫ x in Ω, (u n).val x * q x) atTop
        (nhds (∫ x in Ω, w.val x * q x))) ∧
  (∀ q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
    MemLp q 2 (volume.restrict Ω) →
      Tendsto (fun n ↦ ∫ x in Ω, inner ℝ ((u n).grad x) (q x)) atTop
        (nhds (∫ x in Ω, inner ℝ (w.grad x) (q x))))

def apm_m01J04_L2StronglyConverges {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (u : ℕ → apm_m01J04_H1 d Ω) (w : apm_m01J04_H1 d Ω) : Prop :=
  Tendsto (fun n ↦
    (eLpNorm (fun x ↦ (u n).val x - w.val x) 2
      (volume.restrict Ω)).toReal) atTop (nhds 0)

def apm_m01J04_HasRellichProperty (d : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ u : ℕ → apm_m01J04_H1 d Ω,
    (∃ C : ℝ, ∀ n, apm_m01J04_H1norm (u n) ≤ C) →
      ∃ k : ℕ → ℕ, StrictMono k ∧
        ∃ w : apm_m01J04_H1 d Ω,
          apm_m01J04_H1WeaklyConverges (fun n ↦ u (k n)) w ∧
          apm_m01J04_L2StronglyConverges (fun n ↦ u (k n)) w

def apm_m01J04_L2WeaklyConverges {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
    MemLp q 2 (volume.restrict Ω) →
      Tendsto (fun n ↦ ∫ x in Ω, inner ℝ (v n x) (q x)) atTop
        (nhds (∫ x in Ω, inner ℝ (w x) (q x)))

def apm_m01J04_divStronglyConverges {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
    ∀ h : apm_m01J04_H1 d Ω,
      apm_m01J04_isH1Zero h → apm_m01J04_H1norm h ≤ 1 →
      |∫ x in Ω, inner ℝ (v n x - w x) (h.grad x)| ≤ ε

def apm_m01J04_isTestFunction {d : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiff ℝ ⊤ φ ∧ HasCompactSupport φ ∧ Function.support φ ⊆ Ω

theorem apm_m01j04 :
    (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
        [CompleteSpace X] (f : ℕ → X) (x : X)
        (g : ℕ → X →L[ℝ] ℝ) (h : X →L[ℝ] ℝ),
      apm_m01J04_weaklyConverges f x →
      Tendsto g atTop (nhds h) →
        Tendsto (fun n ↦ g n (f n)) atTop (nhds (h x))) ∧
    (∀ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))),
      apm_m01J04_HasRellichProperty d Ω →
      (∀ u : ℕ → apm_m01J04_H1 d Ω,
        (∃ C : ℝ, ∀ n, apm_m01J04_H1norm (u n) ≤ C) →
          ∃ k : ℕ → ℕ, StrictMono k ∧
            ∃ w : apm_m01J04_H1 d Ω,
              ∀ ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
                MemLp ψ ⊤ (volume.restrict Ω) →
                  Tendsto (fun n ↦ ∫ x in Ω,
                    (u (k n)).val x * inner ℝ ((u (k n)).grad x) (ψ x))
                    atTop (nhds (∫ x in Ω,
                      w.val x * inner ℝ (w.grad x) (ψ x)))) ∧
      (∀ (f : ℕ → apm_m01J04_H1 d Ω) (fLim : apm_m01J04_H1 d Ω)
          (v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
          (vLim : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
        apm_m01J04_H1WeaklyConverges f fLim →
        apm_m01J04_L2WeaklyConverges (Ω := Ω) v vLim →
        apm_m01J04_divStronglyConverges (Ω := Ω) v vLim →
          ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
            apm_m01J04_isTestFunction Ω φ →
              Tendsto (fun n ↦ ∫ x in Ω,
                inner ℝ (v n x) ((f n).grad x) * φ x) atTop
                (nhds (∫ x in Ω,
                  inner ℝ (vLim x) (fLim.grad x) * φ x)))) := by
  constructor
  · intro X _ _ _ f x g h hf hg
    have hpoint : ∀ q : X →L[ℝ] ℝ, ∃ C : ℝ, ∀ n : ℕ,
        ‖(NormedSpace.inclusionInDoubleDual ℝ X) (f n) q‖ ≤ C := by
      intro q
      obtain ⟨C, hC⟩ :=
        (Metric.isBounded_range_of_tendsto (fun n ↦ q (f n)) (hf q)).exists_norm_le
      refine ⟨C, fun n ↦ ?_⟩
      simpa [NormedSpace.dual_def] using hC (q (f n)) ⟨n, rfl⟩
    obtain ⟨C, hC⟩ := banach_steinhaus
      (g := fun n ↦ (NormedSpace.inclusionInDoubleDual ℝ X) (f n)) hpoint
    have hf_bounded : ∀ n, ‖f n‖ ≤ C := by
      intro n
      rw [← (NormedSpace.inclusionInDoubleDualLi (E := X) ℝ).norm_map]
      exact hC n
    have hC0 : 0 ≤ C := le_trans (norm_nonneg (f 0)) (hf_bounded 0)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨Ng, hNg⟩ := Metric.tendsto_atTop.mp hg
      (ε / (2 * (C + 1))) (by positivity)
    obtain ⟨Nf, hNf⟩ := Metric.tendsto_atTop.mp (hf h) (ε / 2) (by positivity)
    refine ⟨max Ng Nf, fun n hn => ?_⟩
    have hng := hNg n (le_trans (le_max_left _ _) hn)
    have hnf := hNf n (le_trans (le_max_right _ _) hn)
    have hfirst : dist (g n (f n)) (h (f n)) < ε / 2 := by
      rw [dist_eq_norm, ← ContinuousLinearMap.sub_apply]
      calc
        ‖(g n - h) (f n)‖ ≤ ‖g n - h‖ * ‖f n‖ := (g n - h).le_opNorm _
        _ ≤ ‖g n - h‖ * C := mul_le_mul_of_nonneg_left (hf_bounded n) (norm_nonneg _)
        _ ≤ (ε / (2 * (C + 1))) * C := by
          rw [dist_eq_norm] at hng
          exact mul_le_mul_of_nonneg_right (le_of_lt hng) hC0
        _ < (ε / (2 * (C + 1))) * (C + 1) := by
          exact mul_lt_mul_of_pos_left (lt_add_one C) (by positivity)
        _ = ε / 2 := by field_simp
    exact lt_of_le_of_lt (dist_triangle _ (h (f n)) _) (by
      simpa only [add_halves ε] using add_lt_add hfirst hnf)
  · /-
    Boundary for the Sobolev/compensated-compactness clauses: applying the
    supplied `apm_m01J04_HasRellichProperty` yields a subsequence with weak
    `H¹` and strong `L²` convergence. Part (b) then needs measurable Hölder
    estimates showing multiplication by an `L∞` vector field preserves the
    strong `L²` limit before invoking the weak×strong lemma above. Part (c)
    additionally needs a fully formal Leibniz rule for the custom weak-gradient
    structure, preservation of `apm_m01J04_isH1Zero` under multiplication by a
    test function, and the integration-by-parts identity connecting
    `apm_m01J04_divStronglyConverges` to the target integral. Repository and
    Mathlib searches found no sibling or packaged theorem matching these custom
    predicates.

    Closer hop 1 closes the abstract weak×strong pairing conjunct above,
    including weak boundedness via `banach_steinhaus` and the explicit operator
    norm estimate. Further searches of `LEMMA-INDEX.md`, all fully closed
    artifacts, `ConstructionTargets/`, and `YoungL2.lean` returned no theorem
    connecting the bespoke `apm_m01J04_H1` weak-gradient record to multiplication
    by test functions. Thus the remaining sorry is specifically the measurable
    Hölder/Leibniz/integration-by-parts assembly for these frozen predicates,
    rather than the functional-analytic pairing step.
    -/
    sorry
