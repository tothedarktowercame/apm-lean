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
  sorry

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
lemma apm_t01A02_bounded_affine_error_reduces_to_disk
    (F : ℝ × ℝ → ℝ × ℝ) (a b c d : ℤ)
    (hcont : Continuous F)
    (hbounded : ∃ C : ℝ, ∀ x : ℝ × ℝ,
      ‖F x - ((2 * (a : ℝ) * x.1 + 2 * (b : ℝ) * x.2),
        (2 * (c : ℝ) * x.1 + 2 * (d : ℝ) * x.2))‖ ≤ C)
    (hdet : ((1 - 2 * a) * (1 - 2 * d) - (-2 * b) * (-2 * c)) ≠ 0) :
    ∃ g : C(apm_t01A02_Disk, apm_t01A02_Disk),
      (∃ y, g y = y) → ∃ x, F x = x := by
  sorry

/-- Seat (ray geometry): from distinct points `x,y` of the closed disk, the
ray starting at `x` and pointing away from `y` hits the boundary exactly once.
The nonnegative parameter includes `0`, which is required when `x` is already
on the boundary. -/
lemma apm_t01A02_disk_ray_hits_boundary_unique
    (x y : apm_t01A02_Disk) (hxy : x ≠ y) :
    ∃! t : Set.Ici (0 : ℝ),
      ‖(x.1 + t.1 • (x.1 - y.1) : apm_t01A02_Plane)‖ = 1 := by
  sorry

/-- Seat (quadratic-formula continuity): for a continuous fixed-point-free
disk self-map, the boundary point selected by the outward ray varies
continuously.  Its value is characterized by a nonnegative ray parameter,
which lets the retraction equation be proved independently. -/
lemma apm_t01A02_continuous_boundary_hit_of_no_fixedPoint
    (g : C(apm_t01A02_Disk, apm_t01A02_Disk))
    (hfix : ∀ x, g x ≠ x)
    (hray : ∀ x : apm_t01A02_Disk,
      ∃! t : Set.Ici (0 : ℝ),
        ‖(x.1 + t.1 • (x.1 - (g x).1) : apm_t01A02_Plane)‖ = 1) :
    ∃ r : C(apm_t01A02_Disk, apm_t01A02_DiskBoundary),
      ∀ x, ∃ t : Set.Ici (0 : ℝ),
        (r x).1 = x.1 + t.1 • (x.1 - (g x).1) := by
  sorry

/-- Seat (boundary sign): an outward ray based at a boundary point of the
unit disk can return to the unit sphere at a nonnegative time only at time
zero.  This is the small convex-geometry fact that makes the ray map a strict
retraction. -/
-- BEGIN SEAT AREA
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
-- END SEAT AREA

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
  sorry

/-- Seat (circle homology): integral first singular homology of the boundary
circle is nonzero. -/
lemma apm_t01A02_diskBoundary_H1_not_isZero :
    ¬ IsZero ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t01A02_DiskBoundary))) := by
  sorry

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
  sorry

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
  sorry

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
