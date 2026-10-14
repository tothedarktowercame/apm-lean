import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.TorusSquareDeckAction
import ConstructionTargets.T01A02PuncturedTorusH2
import ConstructionTargets.CoefficientContractiblePair
import ConstructionTargets.SphereHomology

open CategoryTheory
open CategoryTheory.Limits
open ConstructionTargets.TorusSquareDeckAction

abbrev apm_t01A02_Torus := Circle × Circle
abbrev apm_t01A02_Deck := ZMod 2 × ZMod 2

noncomputable section

def apm_t01A02_cover (x : apm_t01A02_Torus) : apm_t01A02_Torus :=
  (x.1 ^ 2, x.2 ^ 2)

def apm_t01A02_hasCoveringGroup
    {S T G : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [AddGroup G] (p : S → T) : Prop :=
  IsCoveringMap p ∧
  ∃ act : G → S → S,
    (∀ x, act 0 x = x) ∧
    (∀ g h x, act (g + h) x = act g (act h x)) ∧
    (∀ g, Continuous (act g)) ∧
    (∀ g x, p (act g x) = p x) ∧
    (∀ g x, act g x = x → g = 0) ∧
    (∀ x y, p x = p y ↔ ∃ g, act g x = y)

abbrev apm_t01A02_H2 (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t01A02_H2map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

lemma apm_t01A02_cover_eq_prod_pow_two (x : apm_t01A02_Torus) :
    apm_t01A02_cover x = (x.1 ^ 2, x.2 ^ 2) := rfl

def apm_t01A02_antipode (z : Circle) : Circle :=
  ⟨-(z : ℂ), by
    simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using z.property⟩

lemma apm_t01A02_circle_sq_eq_sq_iff (z w : Circle) :
    z ^ 2 = w ^ 2 ↔ z = w ∨ z = apm_t01A02_antipode w := by
  constructor
  · intro h
    have hc : (z : ℂ) ^ 2 = (w : ℂ) ^ 2 := by exact_mod_cast h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc with hzw | hzw
    · exact Or.inl (Subtype.ext hzw)
    · exact Or.inr (Subtype.ext hzw)
  · rintro (rfl | rfl)
    · rfl
    · ext
      simp [apm_t01A02_antipode]

lemma apm_t01A02_cover_eq_iff (x y : apm_t01A02_Torus) :
    apm_t01A02_cover x = apm_t01A02_cover y ↔
      (x.1 = y.1 ∨ x.1 = apm_t01A02_antipode y.1) ∧
      (x.2 = y.2 ∨ x.2 = apm_t01A02_antipode y.2) := by
  simp only [apm_t01A02_cover, Prod.mk.injEq]
  exact and_congr (apm_t01A02_circle_sq_eq_sq_iff x.1 y.1)
    (apm_t01A02_circle_sq_eq_sq_iff x.2 y.2)

theorem apm_t01A02_covering_group :
    apm_t01A02_hasCoveringGroup
      (G := apm_t01A02_Deck) apm_t01A02_cover := by
  refine ⟨?_, deckAction, deckAction_zero, deckAction_add,
    continuous_deckAction, ?_, deckAction_free, ?_⟩
  · simpa [apm_t01A02_cover, squareCover] using squareCover_isCoveringMap
  · intro g x
    simpa [apm_t01A02_cover, squareCover] using squareCover_deckAction g x
  · intro x y
    constructor
    · intro hxy
      rcases (apm_t01A02_cover_eq_iff x y).mp hxy with ⟨h₁, h₂⟩
      apply exists_deckAction_eq_of_coordinate_choices x y
      · simpa [antipode, apm_t01A02_antipode] using h₁
      · simpa [antipode, apm_t01A02_antipode] using h₂
    · rintro ⟨g, rfl⟩
      exact (squareCover_deckAction g x).symm

/-- Transport the banked computation for the torus punctured at `(-1,-1)`
to a puncture at an arbitrary point, by coordinatewise circle translation. -/
theorem apm_t01A02_punctured_H2_isZero (q : apm_t01A02_Torus) :
    IsZero (apm_t01A02_H2 {x : apm_t01A02_Torus // x ≠ q}) := by
  let c₁ : Circle := q.1⁻¹ * ConstructionTargets.T01A02PuncturedTorus.circleMinusOne
  let c₂ : Circle := q.2⁻¹ * ConstructionTargets.T01A02PuncturedTorus.circleMinusOne
  let h : apm_t01A02_Torus ≃ₜ apm_t01A02_Torus :=
    (Homeomorph.mulRight c₁).prodCongr (Homeomorph.mulRight c₂)
  have hq : h q = ConstructionTargets.T01A02PuncturedTorus.missingPoint := by
    ext <;> simp [h, c₁, c₂,
      ConstructionTargets.T01A02PuncturedTorus.missingPoint]
  let e : {x : apm_t01A02_Torus // x ≠ q} ≃ₜ
      ConstructionTargets.T01A02PuncturedTorus.X :=
    h.subtype fun x => by
      rw [ne_eq, ne_eq, ← hq]
      exact not_congr h.injective.eq_iff.symm
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)
  exact IsZero.of_iso
    ConstructionTargets.T01A02PuncturedTorus.puncturedTorus_H2_isZero
    (F.mapIso (TopCat.isoOfHomeo e))

theorem apm_t01A02_H2map_eq_zero
    (f : C(apm_t01A02_Torus, apm_t01A02_Torus))
    (hf : ¬Function.Surjective f) :
    apm_t01A02_H2map f = 0 := by
  simp only [Function.Surjective, not_forall, not_exists] at hf
  obtain ⟨q, hq⟩ := hf
  let W := {x : apm_t01A02_Torus // x ≠ q}
  let g : C(apm_t01A02_Torus, W) :=
    ⟨fun x ↦ ⟨f x, hq x⟩, f.continuous.subtype_mk _⟩
  let i : C(W, apm_t01A02_Torus) := ⟨fun x ↦ x.1, continuous_subtype_val⟩
  apply ConstructionTargets.T01A02PuncturedTorus.H2map_eq_zero_of_factor f g i
  · ext x <;> rfl
  · exact apm_t01A02_punctured_H2_isZero q

/-- The coordinatewise universal-cover map used to state the planar lift
pieces of the fixed-point argument. -/
def apm_t01A02_torusExp (x : ℝ × ℝ) : apm_t01A02_Torus :=
  (Circle.exp x.1, Circle.exp x.2)

/-- Explicit lift data for a torus map whose winding matrix has even entries.
The two translation identities use the period `2π` of `Circle.exp`. -/
def apm_t01A02_IsEvenLift
    (f : C(apm_t01A02_Torus, apm_t01A02_Torus))
    (F : ℝ × ℝ → ℝ × ℝ) (a b c d : ℤ) : Prop :=
  Continuous F ∧
  (∀ x, f (apm_t01A02_torusExp x) = apm_t01A02_torusExp (F x)) ∧
  (∀ x, F (x + (2 * Real.pi, 0)) =
    F x + (2 * Real.pi * (2 * a : ℤ), 2 * Real.pi * (2 * c : ℤ))) ∧
  (∀ x, F (x + (0, 2 * Real.pi)) =
    F x + (2 * Real.pi * (2 * b : ℤ), 2 * Real.pi * (2 * d : ℤ)))

/-- Seat (torus lifting): a map factoring through coordinatewise squaring has
a planar lift with an even integral winding matrix. -/
lemma apm_t01A02_evenLift_of_factorsThroughSquare_aux_lift
    (h : C(ℝ × ℝ, Circle))
    (h₁ : ∀ x, h (x + (2 * Real.pi, 0)) = h x)
    (h₂ : ∀ x, h (x + (0, 2 * Real.pi)) = h x) :
    ∃ H : C(ℝ × ℝ, ℝ), ∃ m n : ℤ,
      (∀ x, H (x + (2 * Real.pi, 0)) = H x + 2 * Real.pi * m) ∧
      (∀ x, H (x + (0, 2 * Real.pi)) = H x + 2 * Real.pi * n) ∧
      ∀ x, Circle.exp (H x) = h x := by
  let e₀ : ℝ := Complex.arg (h (0, 0) : ℂ)
  have he₀ : Circle.exp e₀ = h (0, 0) := Circle.exp_arg _
  obtain ⟨H, hH₀, hH⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts h (0, 0) e₀ he₀
  have hHexp : ∀ x, Circle.exp (H x) = h x := by
    intro x
    exact congr_fun hH₀.2 x
  have step (v : ℝ × ℝ) (hv : ∀ x, h (x + v) = h x) :
      ∃ k : ℤ, ∀ x, H (x + v) = H x + 2 * Real.pi * k := by
    have hexp0 : Circle.exp (H ((0, 0) + v)) = Circle.exp (H (0, 0)) := by
      rw [hHexp, hHexp, hv]
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hexp0
    let H₁ : C(ℝ × ℝ, ℝ) :=
      ⟨fun x ↦ H (x + v), H.continuous.comp (continuous_id.add continuous_const)⟩
    let H₂ : C(ℝ × ℝ, ℝ) :=
      ⟨fun x ↦ H x + 2 * Real.pi * k, H.continuous.add continuous_const⟩
    have h₁lift : Circle.exp ∘ H₁ = h := by
      funext x
      exact (hHexp (x + v)).trans (hv x)
    have h₂lift : Circle.exp ∘ H₂ = h := by
      funext x
      change Circle.exp (H x + 2 * Real.pi * (k : ℝ)) = h x
      rw [show H x + 2 * Real.pi * (k : ℝ) =
          H x + (k : ℝ) * (2 * Real.pi) by ring]
      exact (Circle.exp_eq_exp.mpr ⟨k, rfl⟩).trans (hHexp x)
    have hbase : H₁ (0, 0) = H₂ (0, 0) := by
      change H ((0, 0) + v) = H (0, 0) + 2 * Real.pi * (k : ℝ)
      rw [hk]
      ring
    have hu₁ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      h (0, 0) (H₁ (0, 0)) (by
        exact congr_fun h₁lift (0, 0))
    have hu₂ : H₁ = H₂ := by
      exact hu₁.unique ⟨rfl, h₁lift⟩ ⟨hbase.symm, h₂lift⟩
    refine ⟨k, fun x ↦ ?_⟩
    exact DFunLike.congr_fun hu₂ x
  obtain ⟨m, hm⟩ := step (2 * Real.pi, 0) h₁
  obtain ⟨n, hn⟩ := step (0, 2 * Real.pi) h₂
  exact ⟨H, m, n, hm, hn, hHexp⟩

lemma apm_t01A02_evenLift_of_factorsThroughSquare
    (f : C(apm_t01A02_Torus, apm_t01A02_Torus))
    (hlift : ∃ g : C(apm_t01A02_Torus, apm_t01A02_Torus),
      ∀ x, f x = apm_t01A02_cover (g x)) :
    ∃ F : ℝ × ℝ → ℝ × ℝ, ∃ a b c d : ℤ,
      apm_t01A02_IsEvenLift f F a b c d := by
  obtain ⟨g, hg⟩ := hlift
  let h₁ : C(ℝ × ℝ, Circle) :=
    ⟨fun x ↦ (g (apm_t01A02_torusExp x)).1,
      continuous_fst.comp (g.continuous.comp
        (Circle.isCoveringMap_exp.continuous.comp continuous_fst |>.prodMk
          (Circle.isCoveringMap_exp.continuous.comp continuous_snd)))⟩
  let h₂ : C(ℝ × ℝ, Circle) :=
    ⟨fun x ↦ (g (apm_t01A02_torusExp x)).2,
      continuous_snd.comp (g.continuous.comp
        (Circle.isCoveringMap_exp.continuous.comp continuous_fst |>.prodMk
          (Circle.isCoveringMap_exp.continuous.comp continuous_snd)))⟩
  have hperiod (x : ℝ × ℝ) :
      apm_t01A02_torusExp (x + (2 * Real.pi, 0)) = apm_t01A02_torusExp x := by
    ext <;> simp [apm_t01A02_torusExp, Circle.periodic_exp]
  have hperiod' (x : ℝ × ℝ) :
      apm_t01A02_torusExp (x + (0, 2 * Real.pi)) = apm_t01A02_torusExp x := by
    ext <;> simp [apm_t01A02_torusExp, Circle.periodic_exp]
  obtain ⟨H₁, a, b, ha, hb, hH₁⟩ :=
    apm_t01A02_evenLift_of_factorsThroughSquare_aux_lift h₁
      (fun x ↦ by simp [h₁, hperiod]) (fun x ↦ by simp [h₁, hperiod'])
  obtain ⟨H₂, c, d, hc, hd, hH₂⟩ :=
    apm_t01A02_evenLift_of_factorsThroughSquare_aux_lift h₂
      (fun x ↦ by simp [h₂, hperiod]) (fun x ↦ by simp [h₂, hperiod'])
  let F : ℝ × ℝ → ℝ × ℝ := fun x ↦ (2 * H₁ x, 2 * H₂ x)
  refine ⟨F, a, b, c, d, ?_, ?_, ?_, ?_⟩
  · exact (H₁.continuous.const_mul 2).prodMk (H₂.continuous.const_mul 2)
  · intro x
    rw [hg]
    apply Prod.ext
    · simp only [apm_t01A02_cover, apm_t01A02_torusExp, F]
      rw [show 2 * H₁ x = H₁ x + H₁ x by ring, Circle.exp_add, hH₁]
      simp [h₁, pow_two, apm_t01A02_torusExp]
    · simp only [apm_t01A02_cover, apm_t01A02_torusExp, F]
      rw [show 2 * H₂ x = H₂ x + H₂ x by ring, Circle.exp_add, hH₂]
      simp [h₂, pow_two, apm_t01A02_torusExp]
  · intro x
    rw [Prod.ext_iff]
    constructor
    · simp [F, ha]
      ring
    · simp [F, hc]
      ring
  · intro x
    rw [Prod.ext_iff]
    constructor
    · simp [F, hb]
      ring
    · simp [F, hd]
      ring

/-- Seat (compact fundamental square): the error of an equivariant planar
lift from its linear part is bounded. -/
lemma apm_t01A02_evenLift_error_bounded
    (f : C(apm_t01A02_Torus, apm_t01A02_Torus))
    (F : ℝ × ℝ → ℝ × ℝ) (a b c d : ℤ)
    (hF : apm_t01A02_IsEvenLift f F a b c d) :
    ∃ C : ℝ, ∀ x : ℝ × ℝ,
      ‖F x - ((2 * (a : ℝ) * x.1 + 2 * (b : ℝ) * x.2),
        (2 * (c : ℝ) * x.1 + 2 * (d : ℝ) * x.2))‖ ≤ C := by
  let L : ℝ × ℝ → ℝ × ℝ := fun x ↦
    ((2 * (a : ℝ) * x.1 + 2 * (b : ℝ) * x.2),
     (2 * (c : ℝ) * x.1 + 2 * (d : ℝ) * x.2))
  let E : ℝ × ℝ → ℝ × ℝ := fun x ↦ F x - L x
  have hcont : Continuous E := hF.1.sub (by
    apply Continuous.prodMk
    · fun_prop
    · fun_prop)
  have hp : Function.Periodic E (2 * Real.pi, 0) := by
    intro x
    dsimp [E, L]
    rw [hF.2.2.1 x]
    ext <;> simp <;> ring
  have hq : Function.Periodic E (0, 2 * Real.pi) := by
    intro x
    dsimp [E, L]
    rw [hF.2.2.2 x]
    ext <;> simp <;> ring
  have hcompact : IsCompact
      (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, ?_⟩
  intro x
  let m : ℤ := ⌊x.1 / (2 * Real.pi)⌋
  let n : ℤ := ⌊x.2 / (2 * Real.pi)⌋
  let y : ℝ × ℝ :=
    (x.1 - (m : ℝ) * (2 * Real.pi), x.2 - (n : ℝ) * (2 * Real.pi))
  have hy₁ : y.1 ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    constructor
    · dsimp [y, m]
      have hm := Int.floor_le (x.1 / (2 * Real.pi))
      have ht := Real.two_pi_pos
      apply (sub_nonneg.mpr ?_)
      exact (le_div_iff₀ ht).mp hm
    · dsimp [y, m]
      have hm := Int.lt_floor_add_one (x.1 / (2 * Real.pi))
      have ht := Real.two_pi_pos
      have hm' : x.1 < ((⌊x.1 / (2 * Real.pi)⌋ : ℤ) : ℝ) *
          (2 * Real.pi) + (2 * Real.pi) := by
        calc
          x.1 < (((⌊x.1 / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1) *
              (2 * Real.pi) := (div_lt_iff₀ ht).mp hm
          _ = _ := by ring
      linarith
  have hy₂ : y.2 ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    constructor
    · dsimp [y, n]
      have hn := Int.floor_le (x.2 / (2 * Real.pi))
      have ht := Real.two_pi_pos
      apply sub_nonneg.mpr
      exact (le_div_iff₀ ht).mp hn
    · dsimp [y, n]
      have hn := Int.lt_floor_add_one (x.2 / (2 * Real.pi))
      have ht := Real.two_pi_pos
      have hn' : x.2 < ((⌊x.2 / (2 * Real.pi)⌋ : ℤ) : ℝ) *
          (2 * Real.pi) + (2 * Real.pi) := by
        calc
          x.2 < (((⌊x.2 / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1) *
              (2 * Real.pi) := (div_lt_iff₀ ht).mp hn
          _ = _ := by ring
      linarith
  have hEy : E y = E x := by
    have hm := (hp.zsmul m) y
    have hn := (hq.zsmul n) (y + m • (2 * Real.pi, 0))
    rw [← hm, ← hn]
    congr 1
    ext <;> simp [y] <;> ring
  change ‖E x‖ ≤ C
  rw [← hEy]
  exact hC y ⟨hy₁, hy₂⟩

/-- Seat (integer parity): `I - 2A` has nonzero determinant for every
two-by-two integer matrix `A`. -/
lemma apm_t01A02_even_matrix_fixedPoint_det_ne_zero (a b c d : ℤ) :
    ((1 - 2 * a) * (1 - 2 * d) - (-2 * b) * (-2 * c)) ≠ 0 := by
  intro h
  have hodd :
      (1 - 2 * (a + d) + 4 * (a * d - b * c) : ℤ) = 0 := by
    nlinarith
  omega

/-- The Euclidean plane used by the two-dimensional Brouwer leaves. -/
abbrev apm_t01A02_Plane := EuclideanSpace ℝ (Fin 2)

/-- The closed unit disk in the Euclidean plane. -/
abbrev apm_t01A02_Disk :=
  Metric.closedBall (0 : apm_t01A02_Plane) 1

/-- The boundary circle of the closed unit disk. -/
abbrev apm_t01A02_DiskBoundary :=
  Metric.sphere (0 : apm_t01A02_Plane) 1

/-- Seat (linear reduction and rescaling): the bounded affine-error problem
reduces to the fixed-point problem for one continuous self-map of the closed
unit disk.  The implication is deliberately exposed so this leaf does not
assume Brouwer. -/
-- BEGIN SEAT AREA
lemma apm_t01A02_bounded_affine_error_reduces_to_disk_aux_norm
    (u v : ℝ) :
    ‖(WithLp.toLp 2 ![u, v] : apm_t01A02_Plane)‖ ≤ |u| + |v| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.norm_eq_abs]
  have hs : 0 ≤ u ^ 2 + v ^ 2 := by positivity
  have hr := Real.sq_sqrt hs
  have hn := Real.sqrt_nonneg (u ^ 2 + v ^ 2)
  have hr' : (Real.sqrt (|u| ^ 2 + |v| ^ 2)) ^ 2 =
      |u| ^ 2 + |v| ^ 2 := Real.sq_sqrt (by positivity)
  nlinarith [abs_nonneg u, abs_nonneg v]

lemma apm_t01A02_bounded_affine_error_reduces_to_disk
    (F : ℝ × ℝ → ℝ × ℝ) (a b c d : ℤ)
    (hcont : Continuous F)
    (hbounded : ∃ C : ℝ, ∀ x : ℝ × ℝ,
      ‖F x - ((2 * (a : ℝ) * x.1 + 2 * (b : ℝ) * x.2),
        (2 * (c : ℝ) * x.1 + 2 * (d : ℝ) * x.2))‖ ≤ C)
    (hdet : ((1 - 2 * a) * (1 - 2 * d) - (-2 * b) * (-2 * c)) ≠ 0) :
    ∃ g : C(apm_t01A02_Disk, apm_t01A02_Disk),
      (∃ y, g y = y) → ∃ x, F x = x := by
  let α : ℝ := 1 - 2 * (a : ℝ)
  let β : ℝ := -2 * (b : ℝ)
  let γ : ℝ := -2 * (c : ℝ)
  let δ : ℝ := 1 - 2 * (d : ℝ)
  let D : ℝ := α * δ - β * γ
  have hD : D ≠ 0 := by
    intro h
    apply hdet
    dsimp [D, α, β, γ, δ] at h
    exact_mod_cast h
  let E : ℝ × ℝ → ℝ × ℝ := fun x ↦
    F x - ((2 * (a : ℝ) * x.1 + 2 * (b : ℝ) * x.2),
      (2 * (c : ℝ) * x.1 + 2 * (d : ℝ) * x.2))
  obtain ⟨C, hC⟩ := hbounded
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (E (0, 0))) (hC (0, 0))
  let T : ℝ × ℝ → ℝ × ℝ := fun x ↦
    ((δ * (E x).1 - β * (E x).2) / D,
      (-γ * (E x).1 + α * (E x).2) / D)
  have hTcont : Continuous T := by
    apply Continuous.prodMk <;> dsimp [T, E]
    · fun_prop
    · fun_prop
  let K : ℝ :=
    ((|δ| + |β| + |γ| + |α|) * C) / |D|
  have hK0 : 0 ≤ K := by positivity
  have hTbound (x : ℝ × ℝ) : |(T x).1| + |(T x).2| ≤ K := by
    have he := hC x
    change ‖E x‖ ≤ C at he
    have he1 : |(E x).1| ≤ C := by
      rw [← Real.norm_eq_abs]
      exact (norm_fst_le (E x)).trans he
    have he2 : |(E x).2| ≤ C := by
      rw [← Real.norm_eq_abs]
      exact (norm_snd_le (E x)).trans he
    have hDabs : 0 < |D| := abs_pos.mpr hD
    dsimp [T, K]
    rw [abs_div, abs_div]
    have h1 := abs_sub (δ * (E x).1) (β * (E x).2)
    have h2 := abs_add_le (-γ * (E x).1) (α * (E x).2)
    rw [abs_mul, abs_mul] at h1 h2
    rw [abs_neg] at h2
    rw [← add_div]
    apply div_le_div_of_nonneg_right
    · nlinarith [mul_le_mul_of_nonneg_left he1 (abs_nonneg δ),
      mul_le_mul_of_nonneg_left he2 (abs_nonneg β),
      mul_le_mul_of_nonneg_left he1 (abs_nonneg γ),
      mul_le_mul_of_nonneg_left he2 (abs_nonneg α)]
    · exact hDabs.le
  let R : ℝ := K + 1
  have hR : 0 < R := by dsimp [R]; linarith
  let p : apm_t01A02_Plane → ℝ × ℝ := fun z ↦ (R * z 0, R * z 1)
  let q : ℝ × ℝ → apm_t01A02_Plane := fun x ↦
    WithLp.toLp 2 ![x.1 / R, x.2 / R]
  have hqT (z : apm_t01A02_Plane) : ‖q (T (p z))‖ ≤ 1 := by
    refine (apm_t01A02_bounded_affine_error_reduces_to_disk_aux_norm
      ((T (p z)).1 / R) ((T (p z)).2 / R)).trans ?_
    have hb := hTbound (p z)
    calc
      |(T (p z)).1 / R| + |(T (p z)).2 / R|
          = (|(T (p z)).1| + |(T (p z)).2|) / R := by
              simp only [abs_div, abs_of_pos hR]
              ring
      _ ≤ K / R := div_le_div_of_nonneg_right hb hR.le
      _ ≤ 1 := by apply (div_le_iff₀ hR).2; dsimp [R]; linarith
  let g : C(apm_t01A02_Disk, apm_t01A02_Disk) :=
    ⟨fun z ↦ ⟨q (T (p z.1)), by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hqT z.1⟩,
      by
        apply Continuous.subtype_mk
        dsimp [q, p]
        apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
        apply continuous_pi
        intro i
        fin_cases i <;> simp <;> fun_prop⟩
  refine ⟨g, ?_⟩
  rintro ⟨y, hy⟩
  let x : ℝ × ℝ := p y.1
  have hcoords : T x = x := by
    have heq : q (T x) = y.1 := congr_arg Subtype.val hy
    apply Prod.ext
    · have := congr_fun (congr_arg WithLp.ofLp heq) 0
      dsimp [q, x, p] at this ⊢
      field_simp [hR.ne'] at this
      linarith
    · have := congr_fun (congr_arg WithLp.ofLp heq) 1
      dsimp [q, x, p] at this ⊢
      field_simp [hR.ne'] at this
      linarith
  refine ⟨x, ?_⟩
  have hlin :
      (α * x.1 + β * x.2, γ * x.1 + δ * x.2) = E x := by
    have ht1 := congr_arg Prod.fst hcoords
    have ht2 := congr_arg Prod.snd hcoords
    apply Prod.ext <;> dsimp [T]
    · dsimp [T] at ht1 ht2
      field_simp [hD] at ht1 ht2
      calc
        α * x.1 + β * x.2 =
            (α * (D * x.1) + β * (D * x.2)) / D := by field_simp [hD]
        _ = (α * (δ * (E x).1 - β * (E x).2) +
            β * (-((E x).1 * γ) + (E x).2 * α)) / D := by rw [ht1, ht2]
        _ = (E x).1 := by field_simp [hD]; dsimp [D]; ring
    · dsimp [T] at ht1 ht2
      field_simp [hD] at ht1 ht2
      calc
        γ * x.1 + δ * x.2 =
            (γ * (D * x.1) + δ * (D * x.2)) / D := by field_simp [hD]
        _ = (γ * (δ * (E x).1 - β * (E x).2) +
            δ * (-((E x).1 * γ) + (E x).2 * α)) / D := by rw [ht1, ht2]
        _ = (E x).2 := by field_simp [hD]; dsimp [D]; ring
  apply Prod.ext
  · have := congr_arg Prod.fst hlin
    dsimp [E, α, β] at this
    linarith
  · have := congr_arg Prod.snd hlin
    dsimp [E, γ, δ] at this
    linarith
-- END SEAT AREA

/-- Seat (ray geometry): from distinct points `x,y` of the closed disk, the
ray starting at `x` and pointing away from `y` hits the boundary exactly once.
The nonnegative parameter includes `0`, which is required when `x` is already
on the boundary. -/
lemma apm_t01A02_disk_ray_hits_boundary_unique
    (x y : apm_t01A02_Disk) (hxy : x ≠ y) :
    ∃! t : Set.Ici (0 : ℝ),
      ‖(x.1 + t.1 • (x.1 - y.1) : apm_t01A02_Plane)‖ = 1 := by
  let v : apm_t01A02_Plane := x.1 - y.1
  let A : ℝ := ‖v‖ ^ 2
  let B : ℝ := inner ℝ x.1 v
  let C : ℝ := ‖x.1‖ ^ 2 - 1
  have hv : v ≠ 0 := by
    intro hv
    apply hxy
    apply Subtype.ext
    dsimp [v] at hv
    exact sub_eq_zero.mp hv
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hx : ‖x.1‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.2
  have hy : ‖y.1‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using y.2
  have hC : C ≤ 0 := by
    dsimp [C]
    nlinarith [norm_nonneg x.1]
  have hquad (t : ℝ) :
      ‖x.1 + t • v‖ ^ 2 = A * t ^ 2 + 2 * B * t + (C + 1) := by
    simp only [norm_add_sq_real, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs]
    dsimp [A, B, C]
    rw [mul_pow, sq_abs]
    ring
  have hBbound : A + C ≤ 2 * B := by
    have hnormy : ‖y.1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y.1]
    have hvnorm :
        A = ‖x.1‖ ^ 2 + ‖y.1‖ ^ 2 - 2 * inner ℝ x.1 y.1 := by
      dsimp [A, v]
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right,
        real_inner_self_eq_norm_sq, real_inner_comm]
      ring
    have hBform : 2 * B =
        2 * ‖x.1‖ ^ 2 - 2 * inner ℝ x.1 y.1 := by
      dsimp [B, v]
      simp only [inner_sub_right, real_inner_self_eq_norm_sq]
      ring
    rw [hvnorm, hBform]
    dsimp [C]
    linarith
  let D : ℝ := B ^ 2 - A * C
  have hD : 0 ≤ D := by
    dsimp [D]
    nlinarith [sq_nonneg B]
  let r : ℝ := (-B + Real.sqrt D) / A
  have hsqrt : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD
  have hr : 0 ≤ r := by
    have habs : |B| ≤ Real.sqrt D := by
      have hDb : B ^ 2 ≤ D := by
        dsimp [D]
        nlinarith
      nlinarith [sq_abs B, abs_nonneg B, Real.sqrt_nonneg D]
    have : B ≤ Real.sqrt D := le_trans (le_abs_self B) habs
    apply div_nonneg
    · linarith
    · exact hA.le
  have hrquad : A * r ^ 2 + 2 * B * r + C = 0 := by
    dsimp [r]
    field_simp [ne_of_gt hA]
    dsimp [D] at hsqrt
    nlinarith [hsqrt]
  have hrsphere : ‖x.1 + r • v‖ = 1 := by
    have hs : ‖x.1 + r • v‖ ^ 2 = 1 := by
      rw [hquad]
      linarith
    nlinarith [norm_nonneg (x.1 + r • v)]
  refine ⟨⟨r, hr⟩, ?_, ?_⟩
  · simpa [v] using hrsphere
  · intro s hs
    apply Subtype.ext
    have hsquad : A * s.1 ^ 2 + 2 * B * s.1 + C = 0 := by
      have := hquad s.1
      rw [show ‖x.1 + s.1 • v‖ = 1 by simpa [v] using hs] at this
      nlinarith
    have hfactor : (s.1 - r) * (A * (s.1 + r) + 2 * B) = 0 := by
      nlinarith [hrquad]
    rcases mul_eq_zero.mp hfactor with hsr | hsum
    · linarith
    · have hprod : C = A * s.1 * r := by
        nlinarith [hrquad, hsquad]
      have hCzero : C = 0 := by
        have hsnonneg : 0 ≤ s.1 := s.2
        have hp : 0 ≤ A * s.1 * r := mul_nonneg (mul_nonneg hA.le hsnonneg) hr
        linarith
      have hBpos : 0 < B := by
        nlinarith
      have : 0 < A * (s.1 + r) + 2 * B := by
        have hsnonneg : 0 ≤ s.1 := s.2
        positivity
      exact (this.ne' hsum).elim

/-- Seat (quadratic-formula continuity): for a continuous fixed-point-free
disk self-map, the boundary point selected by the outward ray varies
continuously.  Its value is characterized by a nonnegative ray parameter,
which lets the retraction equation be proved independently. -/
lemma apm_t01A02_continuous_boundary_hit_of_no_fixedPoint_aux_formula
    (x y : apm_t01A02_Plane) (hxy : x ≠ y) (hx : ‖x‖ ≤ 1) :
    let A := ‖x - y‖ ^ 2
    let B := inner ℝ (x - y) x
    let C := ‖x‖ ^ 2 - 1
    let t := (-B + Real.sqrt (B ^ 2 - A * C)) / A
    0 ≤ t ∧ ‖x + t • (x - y)‖ = 1 := by
  dsimp
  have hA : 0 < ‖x - y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
  have hC : ‖x‖ ^ 2 - 1 ≤ 0 := by
    have := (sq_le_sq₀ (norm_nonneg x) (by norm_num : (0:ℝ) ≤ 1)).mpr hx
    nlinarith
  have hdisc : 0 ≤ inner ℝ (x - y) x ^ 2 - ‖x - y‖ ^ 2 * (‖x‖ ^ 2 - 1) := by
    nlinarith [mul_nonneg hA.le (neg_nonneg.mpr hC)]
  have hsquare := Real.sq_sqrt hdisc
  have hsnonneg := Real.sqrt_nonneg
    (inner ℝ (x - y) x ^ 2 - ‖x - y‖ ^ 2 * (‖x‖ ^ 2 - 1))
  have ht : 0 ≤ (-inner ℝ (x - y) x +
      Real.sqrt (inner ℝ (x - y) x ^ 2 - ‖x - y‖ ^ 2 * (‖x‖ ^ 2 - 1))) /
      ‖x - y‖ ^ 2 := by
    apply div_nonneg
    · have habs : |inner ℝ (x - y) x| ≤ Real.sqrt
          (inner ℝ (x - y) x ^ 2 - ‖x - y‖ ^ 2 * (‖x‖ ^ 2 - 1)) := by
        rw [← sq_le_sq₀ (abs_nonneg _) hsnonneg]
        rw [sq_abs, hsquare]
        nlinarith
      nlinarith [le_trans (neg_le_abs _) habs]
    · exact hA.le
  refine ⟨ht, ?_⟩
  have hquad :
      ‖x - y‖ ^ 2 * ((-inner ℝ (x - y) x +
        Real.sqrt (inner ℝ (x - y) x ^ 2 - ‖x - y‖ ^ 2 * (‖x‖ ^ 2 - 1))) /
          ‖x - y‖ ^ 2) ^ 2 +
      2 * inner ℝ (x - y) x * ((-inner ℝ (x - y) x +
        Real.sqrt (inner ℝ (x - y) x ^ 2 - ‖x - y‖ ^ 2 * (‖x‖ ^ 2 - 1))) /
          ‖x - y‖ ^ 2) + (‖x‖ ^ 2 - 1) = 0 := by
    have hmul : ‖x - y‖ ^ 2 *
        ((-inner ℝ (x - y) x +
          Real.sqrt (inner ℝ (x - y) x ^ 2 - ‖x - y‖ ^ 2 * (‖x‖ ^ 2 - 1))) /
            ‖x - y‖ ^ 2) =
        -inner ℝ (x - y) x +
          Real.sqrt (inner ℝ (x - y) x ^ 2 - ‖x - y‖ ^ 2 * (‖x‖ ^ 2 - 1)) := by
      have hn : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
      field_simp [ne_of_gt hA, hn]
    nlinarith [hsquare, mul_nonneg hA.le (sq_nonneg
      ((-inner ℝ (x - y) x +
        Real.sqrt (inner ℝ (x - y) x ^ 2 - ‖x - y‖ ^ 2 * (‖x‖ ^ 2 - 1))) /
          ‖x - y‖ ^ 2))]
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp
  rw [one_pow]
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  simp only [norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg ht]
  have hi : inner ℝ x (x - y) = inner ℝ (x - y) x := real_inner_comm _ _
  nlinarith

lemma apm_t01A02_continuous_boundary_hit_of_no_fixedPoint
    (g : C(apm_t01A02_Disk, apm_t01A02_Disk))
    (hfix : ∀ x, g x ≠ x)
    (hray : ∀ x : apm_t01A02_Disk,
      ∃! t : Set.Ici (0 : ℝ),
        ‖(x.1 + t.1 • (x.1 - (g x).1) : apm_t01A02_Plane)‖ = 1) :
    ∃ r : C(apm_t01A02_Disk, apm_t01A02_DiskBoundary),
      ∀ x, ∃ t : Set.Ici (0 : ℝ),
        (r x).1 = x.1 + t.1 • (x.1 - (g x).1) := by
  let v : apm_t01A02_Disk → apm_t01A02_Plane := fun x ↦ x.1 - (g x).1
  let A : apm_t01A02_Disk → ℝ := fun x ↦ ‖v x‖ ^ 2
  let B : apm_t01A02_Disk → ℝ := fun x ↦ inner ℝ (v x) x.1
  let C : apm_t01A02_Disk → ℝ := fun x ↦ ‖x.1‖ ^ 2 - 1
  let t : apm_t01A02_Disk → ℝ := fun x ↦
    (-B x + Real.sqrt (B x ^ 2 - A x * C x)) / A x
  have hvcont : Continuous v := continuous_subtype_val.sub
    (continuous_subtype_val.comp g.continuous)
  have hAcont : Continuous A := (hvcont.norm.pow 2)
  have hBcont : Continuous B :=
    (hvcont.inner continuous_subtype_val)
  have hCcont : Continuous C := (continuous_subtype_val.norm.pow 2).sub continuous_const
  have hAne : ∀ x, A x ≠ 0 := by
    intro x
    have hvne : v x ≠ 0 := by
      intro hv
      apply hfix x
      apply Subtype.ext
      dsimp [v] at hv
      exact sub_eq_zero.mp hv |>.symm
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hvne)
  have htcont : Continuous t := by
    exact (hBcont.neg.add (((hBcont.pow 2).sub (hAcont.mul hCcont)).sqrt)).div
      hAcont hAne
  have htprop : ∀ x, 0 ≤ t x ∧ ‖x.1 + t x • v x‖ = 1 := by
    intro x
    apply apm_t01A02_continuous_boundary_hit_of_no_fixedPoint_aux_formula
    · intro heq
      exact hfix x (Subtype.ext heq.symm)
    · rw [← dist_zero_right]
      exact x.2
  let r : C(apm_t01A02_Disk, apm_t01A02_DiskBoundary) :=
    ⟨fun x ↦ ⟨x.1 + t x • v x, by
        rw [Metric.mem_sphere, dist_zero_right]
        exact (htprop x).2⟩,
      by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.add (htcont.smul hvcont)⟩
  refine ⟨r, fun x ↦ ⟨⟨t x, (htprop x).1⟩, ?_⟩⟩
  rfl

/-- Seat (boundary sign): an outward ray based at a boundary point of the
unit disk can return to the unit sphere at a nonnegative time only at time
zero.  This is the small convex-geometry fact that makes the ray map a strict
retraction. -/
lemma apm_t01A02_boundary_ray_parameter_eq_zero
    (x y : apm_t01A02_Plane) (hxy : x ≠ y)
    (hx : ‖x‖ = 1) (hy : ‖y‖ ≤ 1)
    (t : ℝ) (ht : 0 ≤ t)
    (htsphere : ‖x + t • (x - y)‖ = 1) :
    t = 0 := by
  have hxy_norm : 0 < ‖x - y‖ ^ 2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
  have hinner_xy : inner ℝ x y ≤ 1 := by
    calc
      inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
      _ ≤ 1 * 1 := mul_le_mul hx.le hy (norm_nonneg y) (by norm_num)
      _ = 1 := by norm_num
  have hinner_nonneg : 0 ≤ inner ℝ x (x - y) := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hx]
    norm_num at *
    linarith
  have hsquared :
      inner ℝ (x + t • (x - y)) (x + t • (x - y)) = inner ℝ x x := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      htsphere, hx]
  have heq :
      t * inner ℝ (x - y) x + t * inner ℝ x (x - y) +
        t ^ 2 * ‖x - y‖ ^ 2 = 0 := by
    have hnormsmul : ‖t • (x - y)‖ ^ 2 = t ^ 2 * ‖x - y‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
      ring
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq] at hsquared
    rw [hnormsmul] at hsquared
    nlinarith
  apply le_antisymm ?_ ht
  by_contra hnot
  have htpos : 0 < t := lt_of_not_ge hnot
  have hinner_nonneg' : 0 ≤ inner ℝ (x - y) x := by
    rwa [real_inner_comm]
  have hfirst :
      0 ≤ t * inner ℝ (x - y) x + t * inner ℝ x (x - y) :=
    add_nonneg (mul_nonneg ht hinner_nonneg') (mul_nonneg ht hinner_nonneg)
  have hsecond : 0 < t ^ 2 * ‖x - y‖ ^ 2 :=
    mul_pos (sq_pos_of_pos htpos) hxy_norm
  linarith

/-- Sorry-free assembly of the ray leaves: a fixed-point-free disk self-map
would produce a retraction onto the boundary circle. -/
lemma apm_t01A02_disk_retraction_of_no_fixedPoint
    (g : C(apm_t01A02_Disk, apm_t01A02_Disk))
    (hfix : ∀ x, g x ≠ x)
    (hhit : ∃ r : C(apm_t01A02_Disk, apm_t01A02_DiskBoundary),
      ∀ x, ∃ t : Set.Ici (0 : ℝ),
        (r x).1 = x.1 + t.1 • (x.1 - (g x).1))
    (hboundary : ∀ (x y : apm_t01A02_Plane), x ≠ y →
      ‖x‖ = 1 → ‖y‖ ≤ 1 →
      ∀ t : ℝ, 0 ≤ t → ‖x + t • (x - y)‖ = 1 → t = 0) :
    ∃ r : C(apm_t01A02_Disk, apm_t01A02_DiskBoundary),
      ∀ z : apm_t01A02_DiskBoundary,
        r ⟨z.1, Metric.mem_closedBall.mpr (by
          simpa [dist_zero_right] using z.2.le)⟩ = z := by
  obtain ⟨r, hr⟩ := hhit
  refine ⟨r, ?_⟩
  intro z
  let iz : apm_t01A02_Disk :=
    ⟨z.1, Metric.mem_closedBall.mpr (by
      simpa [dist_zero_right] using z.2.le)⟩
  obtain ⟨t, ht⟩ := hr iz
  have hne : iz.1 ≠ (g iz).1 := by
    intro heq
    exact hfix iz (Subtype.ext heq.symm)
  have hy : ‖(g iz).1‖ ≤ 1 := by
    rw [← dist_zero_right]
    exact (g iz).2
  have hs : ‖(r iz).1‖ = 1 := by
    rw [← dist_zero_right]
    exact (r iz).2
  have hzero : t.1 = 0 := hboundary iz.1 (g iz).1 hne
    (by simpa [iz, Metric.mem_sphere, dist_zero_right] using z.2)
    hy t.1 t.2 (by rw [← ht]; exact hs)
  apply Subtype.ext
  rw [hzero, zero_smul, add_zero] at ht
  exact ht

/-- Seat (contractibility): integral first singular homology of the closed
unit disk is zero. -/
lemma apm_t01A02_disk_H1_isZero :
    IsZero ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t01A02_Disk))) := by
  letI : ContractibleSpace apm_t01A02_Disk :=
    Metric.contractibleSpace_closedBall (by norm_num)
  exact ConstructionTargets.CoefficientContractiblePair.higher_zero
    ℤ apm_t01A02_Disk 1 (by norm_num)

/-- Seat (circle homology): integral first singular homology of the boundary
circle is nonzero. -/
lemma apm_t01A02_diskBoundary_H1_not_isZero :
    ¬ IsZero ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t01A02_DiskBoundary))) := by
  intro h
  have hz : IsZero (ModuleCat.of ℤ ℤ) :=
    h.of_iso
      (ConstructionTargets.SphereHomology.sphereModuleTopHomologyIsoInt
        1 one_pos).symm
  have hid : 𝟙 (ModuleCat.of ℤ ℤ) = 0 :=
    (IsZero.iff_id_eq_zero _).mp hz
  have hone := ConcreteCategory.congr_hom hid (1 : ℤ)
  norm_num at hone

/-- Seat (homological obstruction): a strict retraction of the disk onto its
boundary contradicts the two explicit H1 facts.  Both facts are hypotheses,
so this categorical leaf is parallel to their proofs. -/
lemma apm_t01A02_no_disk_boundary_retraction
    (hdisk : IsZero ((((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of apm_t01A02_Disk))))
    (hcircle : ¬ IsZero ((((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of apm_t01A02_DiskBoundary)))) :
    ¬ ∃ r : C(apm_t01A02_Disk, apm_t01A02_DiskBoundary),
      ∀ z : apm_t01A02_DiskBoundary,
        r ⟨z.1, Metric.mem_closedBall.mpr (by
          simpa [dist_zero_right] using z.2.le)⟩ = z := by
  rintro ⟨r, hr⟩
  let i : C(apm_t01A02_DiskBoundary, apm_t01A02_Disk) :=
    ⟨fun z ↦ ⟨z.1, Metric.mem_closedBall.mpr (by
      simpa [dist_zero_right] using z.2.le)⟩,
      continuous_subtype_val.subtype_mk _⟩
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  have hi : F.map (TopCat.ofHom i) = 0 := hdisk.eq_of_tgt _ _
  apply hcircle
  rw [IsZero.iff_id_eq_zero]
  have hsplit :
      F.map (TopCat.ofHom i) ≫ F.map (TopCat.ofHom r) = 𝟙 _ := by
    rw [← F.map_comp]
    have hir : TopCat.ofHom i ≫ TopCat.ofHom r =
        𝟙 (TopCat.of apm_t01A02_DiskBoundary) := by
      apply ConcreteCategory.hom_ext
      intro z
      exact hr z
    rw [hir, F.map_id]
  rw [← hsplit, hi, zero_comp]

/-- Two-dimensional Brouwer, assembled from the independent ray and homology
leaves above. -/
lemma apm_t01A02_disk_fixedPoint
    (g : C(apm_t01A02_Disk, apm_t01A02_Disk)) :
    ∃ x, g x = x := by
  by_contra h
  push_neg at h
  have hray := fun x =>
    apm_t01A02_disk_ray_hits_boundary_unique x (g x) (Ne.symm (h x))
  have hhit := apm_t01A02_continuous_boundary_hit_of_no_fixedPoint g h hray
  have hret := apm_t01A02_disk_retraction_of_no_fixedPoint g h hhit
    (fun x y hxy hx hy t ht hs =>
      apm_t01A02_boundary_ray_parameter_eq_zero x y hxy hx hy t ht hs)
  exact (apm_t01A02_no_disk_boundary_retraction
    apm_t01A02_disk_H1_isZero apm_t01A02_diskBoundary_H1_not_isZero) hret

/-- Planar Brouwer consequence: a bounded perturbation of a nonsingular
linear endomorphism of the plane has a zero. -/
lemma apm_t01A02_planar_fixedPoint_of_bounded_affine_error
    (F : ℝ × ℝ → ℝ × ℝ) (a b c d : ℤ)
    (hcont : Continuous F)
    (hbounded : ∃ C : ℝ, ∀ x : ℝ × ℝ,
      ‖F x - ((2 * (a : ℝ) * x.1 + 2 * (b : ℝ) * x.2),
        (2 * (c : ℝ) * x.1 + 2 * (d : ℝ) * x.2))‖ ≤ C)
    (hdet : ((1 - 2 * a) * (1 - 2 * d) - (-2 * b) * (-2 * c)) ≠ 0) :
    ∃ x, F x = x := by
  obtain ⟨g, hg⟩ := apm_t01A02_bounded_affine_error_reduces_to_disk
    F a b c d hcont hbounded hdet
  exact hg (apm_t01A02_disk_fixedPoint g)

/-- Seat (descent): a fixed point of a representing planar lift descends to
a fixed point of the torus map. -/
lemma apm_t01A02_fixedPoint_of_lift_fixedPoint
    (f : C(apm_t01A02_Torus, apm_t01A02_Torus))
    (F : ℝ × ℝ → ℝ × ℝ)
    (hrep : ∀ x, f (apm_t01A02_torusExp x) = apm_t01A02_torusExp (F x))
    (hfix : ∃ x, F x = x) :
    ∃ x, f x = x := by
  obtain ⟨x, hx⟩ := hfix
  refine ⟨apm_t01A02_torusExp x, ?_⟩
  simpa [hx] using hrep x

/-- The torus fixed-point dichotomy, assembled from the independent lift,
compactness, parity, planar Brouwer, and descent pieces above. -/
theorem apm_t01A02_fixedPoint_or_surjective_of_lift
    (f : C(apm_t01A02_Torus, apm_t01A02_Torus))
    (hlift : ∃ g : C(apm_t01A02_Torus, apm_t01A02_Torus),
      ∀ x, f x = apm_t01A02_cover (g x)) :
    (∃ x, f x = x) ∨ Function.Surjective f := by
  left
  obtain ⟨F, a, b, c, d, hF⟩ :=
    apm_t01A02_evenLift_of_factorsThroughSquare f hlift
  apply apm_t01A02_fixedPoint_of_lift_fixedPoint f F hF.2.1
  apply apm_t01A02_planar_fixedPoint_of_bounded_affine_error F a b c d hF.1
  · exact apm_t01A02_evenLift_error_bounded f F a b c d hF
  · exact apm_t01A02_even_matrix_fixedPoint_det_ne_zero a b c d

theorem apm_t01a02 :
    ∀ f : C(apm_t01A02_Torus, apm_t01A02_Torus),
      ¬Function.Surjective f →
      apm_t01A02_H2map f = 0 ∧
      apm_t01A02_hasCoveringGroup
        (G := apm_t01A02_Deck) apm_t01A02_cover ∧
      ((∃ g : C(apm_t01A02_Torus, apm_t01A02_Torus),
          ∀ x, f x = apm_t01A02_cover (g x)) →
        ∃ x, f x = x) := by
  intro f hf
  refine ⟨apm_t01A02_H2map_eq_zero f hf, apm_t01A02_covering_group, ?_⟩
  intro hlift
  exact (apm_t01A02_fixedPoint_or_surjective_of_lift f hlift).resolve_right hf

#print axioms apm_t01a02
