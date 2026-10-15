import Mathlib

/-! # Blueprint for APM t99A01 -/

open CategoryTheory

noncomputable section

namespace APMT99A01

abbrev Disk := Metric.closedBall (0 : ℂ) 1

def circleInDisk (z : Circle) : Disk :=
  ⟨z, by simpa [Metric.mem_closedBall, dist_zero_right] using z.property.le⟩

inductive AttachRel {r : ℕ} (degree : Fin r → ℕ) :
    Sum Circle (Fin r × Disk) → Sum Circle (Fin r × Disk) → Prop
  | boundary (i : Fin r) (z : Circle) :
      AttachRel degree (Sum.inl (z ^ degree i))
        (Sum.inr (i, circleInDisk z))

def AttachSpace {r : ℕ} (degree : Fin r → ℕ) :=
  Quotient (Relation.EqvGen.setoid (AttachRel degree))

noncomputable instance {r : ℕ} (degree : Fin r → ℕ) :
    TopologicalSpace (AttachSpace degree) :=
  TopologicalSpace.coinduced (fun x ↦ Quotient.mk _ x) inferInstance

def degreeX : Fin 1 → ℕ := ![2]
def degreeY : Fin 2 → ℕ := ![2, 4]
def degreeZ : Fin 3 → ℕ := ![2, 4, 5]

abbrev X := AttachSpace degreeX
abbrev Y := AttachSpace degreeY
abbrev Z := AttachSpace degreeZ

def basepoint {r : ℕ} (degree : Fin r → ℕ) : AttachSpace degree :=
  Quotient.mk _ (Sum.inl (1 : Circle))

abbrev H (k : ℕ) (W : Type) [TopologicalSpace W] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of W))

/-- The cellular boundary contributed by the attaching maps. -/
def degreeMap {r : ℕ} (degree : Fin r → ℕ) : (Fin r → ℤ) →ₗ[ℤ] ℤ where
  toFun x := ∑ i, (degree i : ℤ) * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [smul_eq_mul, Pi.smul_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_assoc, mul_comm]

abbrev DegreeKernel {r : ℕ} (degree : Fin r → ℕ) :=
  LinearMap.ker (degreeMap degree)

abbrev DegreeCokernel {r : ℕ} (degree : Fin r → ℕ) :=
  ℤ ⧸ LinearMap.range (degreeMap degree)

end APMT99A01

def APMT99A01.circlePower (d : ℕ) : C(Circle, Circle) where
  toFun z := z ^ d
  continuous_toFun := continuous_pow d

def APMT99A01.intTimesNat (d : ℕ) : ℤ →ₗ[ℤ] ℤ where
  toFun x := (d : ℤ) * x
  map_add' x y := by simp [mul_add]
  map_smul' c x := by simp [mul_assoc, mul_comm]

/-- **LIBRARY boundary.** Van Kampen for the quotient with one degree-two cell. -/
theorem t99A01_piOne_X :
    Nonempty (FundamentalGroup APMT99A01.X
      (APMT99A01.basepoint APMT99A01.degreeX) ≃*
        Multiplicative (ZMod 2)) := by
  sorry

/-- **LIBRARY boundary.** Van Kampen for the quotient with degree-two and
degree-four cells. -/
theorem t99A01_piOne_Y :
    Nonempty (FundamentalGroup APMT99A01.Y
      (APMT99A01.basepoint APMT99A01.degreeY) ≃*
        Multiplicative (ZMod 2)) := by
  sorry

/-- **LIBRARY boundary.** Van Kampen for the quotient with cells of degrees
two, four, and five. -/
theorem t99A01_piOne_Z :
    Subsingleton (FundamentalGroup APMT99A01.Z
      (APMT99A01.basepoint APMT99A01.degreeZ)) := by
  sorry

/-! ### Generic integral homology calculation

The geometry is factored through one coordinate-level Mayer--Vietoris record.
In particular, none of the four diagram chases below has to reconstruct the
quotient cover or calculate the winding number of an attaching map. -/

namespace APMT99A01

/-- The integral Mayer--Vietoris data needed for the attaching-space
calculation.  The names `i₁`, `j₁`, `δ₁`, ... follow the consecutive arrows
in the long exact sequence.  Coordinates identify `H₁(A ∩ B)` with `ℤ^r`,
`H₁(A) ⊕ H₁(B)` with `ℤ`, and `H₀(A ∩ B)` with `ℤ^r`. -/
structure AttachMVData {r : ℕ} (degree : Fin r → ℕ) where
  i₁ : (Fin r → ℤ) →ₗ[ℤ] ℤ
  j₁ : ℤ →ₗ[ℤ] (H 1 (AttachSpace degree))
  δ₁ : (H 1 (AttachSpace degree)) →ₗ[ℤ] (Fin r → ℤ)
  i₀ : (Fin r → ℤ) →ₗ[ℤ] (ℤ × (Fin r → ℤ))
  j₀ : (ℤ × (Fin r → ℤ)) →ₗ[ℤ] (H 0 (AttachSpace degree))
  δ₂ : (H 2 (AttachSpace degree)) →ₗ[ℤ] (Fin r → ℤ)
  i₁_eq_degreeMap : i₁ = degreeMap degree
  i₀_injective : Function.Injective i₀
  exact_i₁_j₁ : LinearMap.range i₁ = LinearMap.ker j₁
  exact_j₁_δ₁ : LinearMap.range j₁ = LinearMap.ker δ₁
  exact_δ₁_i₀ : LinearMap.range δ₁ = LinearMap.ker i₀
  exact_i₀_j₀ : LinearMap.range i₀ = LinearMap.ker j₀
  j₀_surjective : Function.Surjective j₀
  δ₂_injective : Function.Injective δ₂
  exact_δ₂_i₁ : LinearMap.range δ₂ = LinearMap.ker i₁
  higher : ∀ k : ℕ, 3 ≤ k → Limits.IsZero (H k (AttachSpace degree))

end APMT99A01

/-- **LIBRARY leaf (quotient geometry, 70--130 lines).** There is an open
cover of the attaching quotient by a circle-side neighbourhood and the union
of the open disk interiors.  This is kept separate from every homology
calculation. -/
theorem t99A01_attachSpace_openCover {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i) :
    ∃ A B : Set (APMT99A01.AttachSpace degree),
      IsOpen A ∧ IsOpen B ∧ A ∪ B = Set.univ := by
  sorry

/-- **LIBRARY leaf (radial deformation, 80--150 lines).** For a standard
circle-side member of the quotient cover, radial push-out descends through
the attaching relation. -/
theorem t99A01_attachSpace_circleSide_retract {r : ℕ}
    (degree : Fin r → ℕ) (hr : 0 < r) (hdegree : ∀ i, 0 < degree i) :
    ∃ A : Set (APMT99A01.AttachSpace degree), IsOpen A ∧
      Nonempty (ContinuousMap.HomotopyEquiv A Circle) := by
  sorry

/-- **LIBRARY leaf (disk charts, 70--140 lines).** The disk-side and overlap
coordinates of the standard cover.  This statement deliberately exposes the
coordinate conclusions consumed by the MV transport. -/
theorem t99A01_attachSpace_diskSide_coordinates {r : ℕ}
    (degree : Fin r → ℕ) (hr : 0 < r) (hdegree : ∀ i, 0 < degree i) :
    ∃ A B : Set (APMT99A01.AttachSpace degree), IsOpen A ∧ IsOpen B ∧
      Nonempty (B ≃ₜ (Σ _ : Fin r, Metric.ball (0 : ℂ) 1)) ∧
      Nonempty (ContinuousMap.HomotopyEquiv (↥(A ∩ B)) (Σ _ : Fin r, Circle)) := by
  sorry

/-- **LIBRARY leaf (finite sigma homology, 35--80 lines).** Integral
coefficients are allowed by the coefficient-generic sigma/Finsupp comparison. -/
theorem t99A01_finiteSigma_integral_coordinates {r k : ℕ} :
    (k = 0 → Nonempty (APMT99A01.H k (Σ _ : Fin r, PUnit) ≅
      ModuleCat.of ℤ (Fin r → ℤ))) ∧
    (0 < k → Limits.IsZero (APMT99A01.H k (Σ _ : Fin r, PUnit))) := by
  sorry

/-- **LIBRARY leaf (circle winding, 60--120 lines).** The oriented `H₁`
coordinate of all attaching maps is the displayed positive degree row. -/
theorem t99A01_circlePower_hOne_row {r : ℕ} (degree : Fin r → ℕ) :
    ∃ e : APMT99A01.H 1 Circle ≅ ModuleCat.of ℤ ℤ,
      ∀ i : Fin r,
        e.inv ≫
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
            (ModuleCat.of ℤ ℤ)).map
              (TopCat.ofHom (APMT99A01.circlePower (degree i))) ≫ e.hom =
          ModuleCat.ofHom (APMT99A01.intTimesNat (degree i)) := by
  sorry

/-- **LIBRARY leaf (integral open-cover MV, 100--150 lines).** Construct and
transport the integral long exact sequence to the preceding coordinates.
This is the only leaf which uses the production open-cover MV machinery. -/
theorem t99A01_attachSpace_integralMVData {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i)
    (hcover : ∃ A B : Set (APMT99A01.AttachSpace degree),
      IsOpen A ∧ IsOpen B ∧ A ∪ B = Set.univ)
    (hcircle : ∃ A : Set (APMT99A01.AttachSpace degree), IsOpen A ∧
      Nonempty (ContinuousMap.HomotopyEquiv A Circle))
    (hdisk : ∃ A B : Set (APMT99A01.AttachSpace degree), IsOpen A ∧ IsOpen B ∧
      Nonempty (B ≃ₜ (Σ _ : Fin r, Metric.ball (0 : ℂ) 1)) ∧
      Nonempty (ContinuousMap.HomotopyEquiv (↥(A ∩ B)) (Σ _ : Fin r, Circle)))
    (hsigma : ∀ k : ℕ,
      (k = 0 → Nonempty (APMT99A01.H k (Σ _ : Fin r, PUnit) ≅
        ModuleCat.of ℤ (Fin r → ℤ))) ∧
      (0 < k → Limits.IsZero (APMT99A01.H k (Σ _ : Fin r, PUnit))))
    (hwinding : ∃ e : APMT99A01.H 1 Circle ≅ ModuleCat.of ℤ ℤ,
      ∀ i : Fin r, e.inv ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map
            (TopCat.ofHom (APMT99A01.circlePower (degree i))) ≫ e.hom =
        ModuleCat.ofHom (APMT99A01.intTimesNat (degree i))) :
    Nonempty (APMT99A01.AttachMVData degree) := by
  sorry

/-- Sorry-free assembly of the five independent geometric inputs and the
integral MV transport. -/
theorem t99A01_attachSpace_MVData {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i) :
    Nonempty (APMT99A01.AttachMVData degree) := by
  exact t99A01_attachSpace_integralMVData degree hr hdegree
    (t99A01_attachSpace_openCover degree hr hdegree)
    (t99A01_attachSpace_circleSide_retract degree hr hdegree)
    (t99A01_attachSpace_diskSide_coordinates degree hr hdegree)
    (fun k ↦ t99A01_finiteSigma_integral_coordinates (r := r) (k := k))
    (t99A01_circlePower_hOne_row degree)

/-! The next four leaves are independent pure algebra/diagram chases.  Their
only common input is an arbitrary `AttachMVData`; hence they can be proved in
parallel and cannot acquire the MV leaf's `sorryAx`. -/

theorem t99A01_attachMVData_hZero {r : ℕ} (degree : Fin r → ℕ)
    (D : APMT99A01.AttachMVData degree) :
    Nonempty (APMT99A01.H 0 (APMT99A01.AttachSpace degree) ≅
      ModuleCat.of ℤ ℤ) := by
  sorry

theorem t99A01_attachMVData_hOne {r : ℕ} (degree : Fin r → ℕ)
    (D : APMT99A01.AttachMVData degree) :
    Nonempty (APMT99A01.H 1 (APMT99A01.AttachSpace degree) ≅
      ModuleCat.of ℤ (APMT99A01.DegreeCokernel degree)) := by
  sorry

theorem t99A01_attachMVData_hTwo {r : ℕ} (degree : Fin r → ℕ)
    (D : APMT99A01.AttachMVData degree) :
    Nonempty (APMT99A01.H 2 (APMT99A01.AttachSpace degree) ≅
      ModuleCat.of ℤ (APMT99A01.DegreeKernel degree)) := by
  sorry

theorem t99A01_attachMVData_hHigher {r : ℕ} (degree : Fin r → ℕ)
    (D : APMT99A01.AttachMVData degree) (k : ℕ) (hk : 3 ≤ k) :
    Limits.IsZero (APMT99A01.H k (APMT99A01.AttachSpace degree)) := by
  exact D.higher k hk

/-- **LIBRARY leaf (MV, degree zero).** A nonempty positive family of cells
attached to the circle is connected. -/
theorem t99A01_attachSpace_hZero {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i) :
    Nonempty (APMT99A01.H 0 (APMT99A01.AttachSpace degree) ≅
      ModuleCat.of ℤ ℤ) := by
  exact t99A01_attachMVData_hZero degree
    (Classical.choice (t99A01_attachSpace_MVData degree hr hdegree))

/-- **LIBRARY leaf (MV, degree one).** The first homology is the cokernel of
the row of attaching degrees. -/
theorem t99A01_attachSpace_hOne {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i) :
    Nonempty (APMT99A01.H 1 (APMT99A01.AttachSpace degree) ≅
      ModuleCat.of ℤ (APMT99A01.DegreeCokernel degree)) := by
  exact t99A01_attachMVData_hOne degree
    (Classical.choice (t99A01_attachSpace_MVData degree hr hdegree))

/-- **LIBRARY leaf (MV, degree two).** The second homology is the kernel of
the row of attaching degrees. -/
theorem t99A01_attachSpace_hTwo {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i) :
    Nonempty (APMT99A01.H 2 (APMT99A01.AttachSpace degree) ≅
      ModuleCat.of ℤ (APMT99A01.DegreeKernel degree)) := by
  exact t99A01_attachMVData_hTwo degree
    (Classical.choice (t99A01_attachSpace_MVData degree hr hdegree))

/-- **LIBRARY leaf (MV, high degrees).** The homology vanishes above the
two-dimensional cover calculation. -/
theorem t99A01_attachSpace_hHigher {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i) (k : ℕ) (hk : 3 ≤ k) :
    Limits.IsZero (APMT99A01.H k (APMT99A01.AttachSpace degree)) := by
  exact t99A01_attachMVData_hHigher degree
    (Classical.choice (t99A01_attachSpace_MVData degree hr hdegree)) k hk

/-- Admission-free packaging of the generic positive-degree calculation. -/
theorem t99A01_attachSpace_homology {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i) :
    Nonempty (APMT99A01.H 0 (APMT99A01.AttachSpace degree) ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (APMT99A01.H 1 (APMT99A01.AttachSpace degree) ≅
      ModuleCat.of ℤ (APMT99A01.DegreeCokernel degree)) ∧
    Nonempty (APMT99A01.H 2 (APMT99A01.AttachSpace degree) ≅
      ModuleCat.of ℤ (APMT99A01.DegreeKernel degree)) ∧
    ∀ k : ℕ, 3 ≤ k →
      Limits.IsZero (APMT99A01.H k (APMT99A01.AttachSpace degree)) := by
  exact ⟨t99A01_attachSpace_hZero degree hr hdegree,
    t99A01_attachSpace_hOne degree hr hdegree,
    t99A01_attachSpace_hTwo degree hr hdegree,
    t99A01_attachSpace_hHigher degree hr hdegree⟩

/-! The remaining admitted leaves are finite integer linear algebra.  They
do not depend on any topology leaf and can therefore be proved in parallel. -/

def t99A01_cokernel_X_aux_mod : ℤ →ₗ[ℤ] ZMod 2 :=
  (Int.castAddHom (ZMod 2)).toIntLinearMap

lemma t99A01_cokernel_X_aux_exact : Function.Exact
    (APMT99A01.degreeMap APMT99A01.degreeX) t99A01_cokernel_X_aux_mod := by
  rw [LinearMap.exact_iff]
  ext x
  constructor
  · intro hx
    change (x : ZMod 2) = 0 at hx
    have hdvd : (2 : ℤ) ∣ x := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp hx
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨fun _ ↦ k, ?_⟩
    change (∑ i, (APMT99A01.degreeX i : ℤ) * k) = x
    calc
      _ = 2 * k := by rw [Fin.sum_univ_one]; simp [APMT99A01.degreeX]
      _ = x := hk.symm
  · rintro ⟨v, rfl⟩
    change (((∑ i, (APMT99A01.degreeX i : ℤ) * v i) : ℤ) : ZMod 2) = 0
    rw [Fin.sum_univ_one]
    rw [show APMT99A01.degreeX 0 = 2 by rfl, Int.cast_mul]
    change (2 : ZMod 2) * (v 0 : ZMod 2) = 0
    have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    rw [htwo]
    simp

theorem t99A01_cokernel_X : Nonempty
    (ModuleCat.of ℤ (APMT99A01.DegreeCokernel APMT99A01.degreeX) ≅
      ModuleCat.of ℤ (ZMod 2)) := by
  refine ⟨LinearEquiv.toModuleIso
    (t99A01_cokernel_X_aux_exact.linearEquivOfSurjective ?_)⟩
  exact ZMod.intCast_surjective

theorem t99A01_kernel_X : Limits.IsZero
    (ModuleCat.of ℤ (APMT99A01.DegreeKernel APMT99A01.degreeX)) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  constructor
  intro x y
  apply Subtype.ext
  funext i
  fin_cases i
  have hx : APMT99A01.degreeMap APMT99A01.degreeX
      (x : Fin 1 → ℤ) = 0 := x.2
  have hy : APMT99A01.degreeMap APMT99A01.degreeX
      (y : Fin 1 → ℤ) = 0 := y.2
  simp [APMT99A01.degreeMap, APMT99A01.degreeX] at hx hy
  simpa using hx.trans hy.symm

def t99A01_cokernel_Y_aux_mod : ℤ →ₗ[ℤ] ZMod 2 :=
  (Int.castAddHom (ZMod 2)).toIntLinearMap

lemma t99A01_cokernel_Y_aux_exact : Function.Exact
    (APMT99A01.degreeMap APMT99A01.degreeY) t99A01_cokernel_Y_aux_mod := by
  rw [LinearMap.exact_iff]
  ext x
  constructor
  · intro hx
    change (x : ZMod 2) = 0 at hx
    have hdvd : (2 : ℤ) ∣ x := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp hx
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨![k, 0], ?_⟩
    change (∑ i, (APMT99A01.degreeY i : ℤ) * (![k, 0] i)) = x
    simpa [APMT99A01.degreeY, Fin.sum_univ_two] using hk.symm
  · rintro ⟨v, rfl⟩
    change (((∑ i, (APMT99A01.degreeY i : ℤ) * v i) : ℤ) : ZMod 2) = 0
    rw [Fin.sum_univ_two]
    simp only [APMT99A01.degreeY, Matrix.cons_val_zero, Nat.cast_ofNat,
      Matrix.cons_val_one, Int.cast_add, Int.cast_mul]
    have h2 : ((2 : ℤ) : ZMod 2) = 0 := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) 2).2 (dvd_refl 2)
    have h4 : ((4 : ℤ) : ZMod 2) = 0 := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (4 : ℤ) 2).2 ⟨2, rfl⟩
    rw [h2, h4]
    simp

theorem t99A01_cokernel_Y : Nonempty
    (ModuleCat.of ℤ (APMT99A01.DegreeCokernel APMT99A01.degreeY) ≅
      ModuleCat.of ℤ (ZMod 2)) := by
  refine ⟨LinearEquiv.toModuleIso
    (t99A01_cokernel_Y_aux_exact.linearEquivOfSurjective ?_)⟩
  exact ZMod.intCast_surjective

theorem t99A01_kernel_Y : Nonempty
    (ModuleCat.of ℤ (APMT99A01.DegreeKernel APMT99A01.degreeY) ≅
      ModuleCat.of ℤ ℤ) := by
  sorry

-- BEGIN SEAT AREA
theorem t99A01_cokernel_Z : Limits.IsZero
    (ModuleCat.of ℤ (APMT99A01.DegreeCokernel APMT99A01.degreeZ)) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  have hsurj : Function.Surjective
      (APMT99A01.degreeMap APMT99A01.degreeZ) := by
    intro x
    refine ⟨![-2 * x, 0, x], ?_⟩
    simp [APMT99A01.degreeMap, APMT99A01.degreeZ, Fin.sum_univ_three]
    ring
  have hrange : LinearMap.range
      (APMT99A01.degreeMap APMT99A01.degreeZ) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  constructor
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  apply Quotient.sound
  apply (Submodule.quotientRel_def (p := LinearMap.range
    (APMT99A01.degreeMap APMT99A01.degreeZ))).2
  rw [hrange]
  trivial
-- END SEAT AREA

theorem t99A01_kernel_Z : Nonempty
    (ModuleCat.of ℤ (APMT99A01.DegreeKernel APMT99A01.degreeZ) ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) := by
  sorry

/-- **LIBRARY boundary.** The degree-zero integral homology of `X`. -/
theorem t99A01_hZero_X :
    Nonempty (APMT99A01.H 0 APMT99A01.X ≅ ModuleCat.of ℤ ℤ) := by
  exact (t99A01_attachSpace_homology APMT99A01.degreeX (by decide) (by decide)).1

/-- **LIBRARY boundary.** The degree-one integral homology of `X`. -/
theorem t99A01_hOne_X :
    Nonempty (APMT99A01.H 1 APMT99A01.X ≅ ModuleCat.of ℤ (ZMod 2)) := by
  exact ⟨Classical.choice
    (t99A01_attachSpace_homology APMT99A01.degreeX (by decide) (by decide)).2.1 ≪≫
      Classical.choice t99A01_cokernel_X⟩

/-- **LIBRARY boundary.** The degree-two integral homology of `X`. -/
theorem t99A01_hTwo_X :
    Limits.IsZero (APMT99A01.H 2 APMT99A01.X) := by
  exact t99A01_kernel_X.of_iso (Classical.choice
    (t99A01_attachSpace_homology APMT99A01.degreeX (by decide) (by decide)).2.2.1)

/-- **LIBRARY boundary.** The degree-zero integral homology of `Y`. -/
theorem t99A01_hZero_Y :
    Nonempty (APMT99A01.H 0 APMT99A01.Y ≅ ModuleCat.of ℤ ℤ) := by
  exact (t99A01_attachSpace_homology APMT99A01.degreeY (by decide) (by decide)).1

/-- **LIBRARY boundary.** The degree-one integral homology of `Y`. -/
theorem t99A01_hOne_Y :
    Nonempty (APMT99A01.H 1 APMT99A01.Y ≅ ModuleCat.of ℤ (ZMod 2)) := by
  exact ⟨Classical.choice
    (t99A01_attachSpace_homology APMT99A01.degreeY (by decide) (by decide)).2.1 ≪≫
      Classical.choice t99A01_cokernel_Y⟩

/-- **LIBRARY boundary.** The degree-two integral homology of `Y`. -/
theorem t99A01_hTwo_Y :
    Nonempty (APMT99A01.H 2 APMT99A01.Y ≅ ModuleCat.of ℤ ℤ) := by
  exact ⟨Classical.choice
    (t99A01_attachSpace_homology APMT99A01.degreeY (by decide) (by decide)).2.2.1 ≪≫
      Classical.choice t99A01_kernel_Y⟩

/-- **LIBRARY boundary.** The degree-zero integral homology of `Z`. -/
theorem t99A01_hZero_Z :
    Nonempty (APMT99A01.H 0 APMT99A01.Z ≅ ModuleCat.of ℤ ℤ) := by
  exact (t99A01_attachSpace_homology APMT99A01.degreeZ (by decide) (by decide)).1

/-- **LIBRARY boundary.** The degree-one integral homology of `Z`. -/
theorem t99A01_hOne_Z :
    Limits.IsZero (APMT99A01.H 1 APMT99A01.Z) := by
  exact t99A01_cokernel_Z.of_iso (Classical.choice
    (t99A01_attachSpace_homology APMT99A01.degreeZ (by decide) (by decide)).2.1)

/-- **LIBRARY boundary.** The degree-two integral homology of `Z`. -/
theorem t99A01_hTwo_Z :
    Nonempty (APMT99A01.H 2 APMT99A01.Z ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) := by
  exact ⟨Classical.choice
    (t99A01_attachSpace_homology APMT99A01.degreeZ (by decide) (by decide)).2.2.1 ≪≫
      Classical.choice t99A01_kernel_Z⟩

/-- **LIBRARY boundary.** Integral homology of `X` vanishes above its CW
dimension. -/
theorem t99A01_hHigher_X (k : ℕ) (hk : 3 ≤ k) :
    Limits.IsZero (APMT99A01.H k APMT99A01.X) := by
  exact (t99A01_attachSpace_homology APMT99A01.degreeX
    (by decide) (by decide)).2.2.2 k hk

/-- **LIBRARY boundary.** Integral homology of `Y` vanishes above its CW
dimension. -/
theorem t99A01_hHigher_Y (k : ℕ) (hk : 3 ≤ k) :
    Limits.IsZero (APMT99A01.H k APMT99A01.Y) := by
  exact (t99A01_attachSpace_homology APMT99A01.degreeY
    (by decide) (by decide)).2.2.2 k hk

/-- **LIBRARY boundary.** Integral homology of `Z` vanishes above its CW
dimension. -/
theorem t99A01_hHigher_Z (k : ℕ) (hk : 3 ≤ k) :
    Limits.IsZero (APMT99A01.H k APMT99A01.Z) := by
  exact (t99A01_attachSpace_homology APMT99A01.degreeZ
    (by decide) (by decide)).2.2.2 k hk

/-- Assembly of the independent van Kampen and homology computations. -/
theorem t99A01_attached_cells_computation :
    Nonempty (FundamentalGroup APMT99A01.X
      (APMT99A01.basepoint APMT99A01.degreeX) ≃*
        Multiplicative (ZMod 2)) ∧
    Nonempty (FundamentalGroup APMT99A01.Y
      (APMT99A01.basepoint APMT99A01.degreeY) ≃*
        Multiplicative (ZMod 2)) ∧
    Subsingleton (FundamentalGroup APMT99A01.Z
      (APMT99A01.basepoint APMT99A01.degreeZ)) ∧
    Nonempty (APMT99A01.H 0 APMT99A01.X ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (APMT99A01.H 1 APMT99A01.X ≅ ModuleCat.of ℤ (ZMod 2)) ∧
    Limits.IsZero (APMT99A01.H 2 APMT99A01.X) ∧
    Nonempty (APMT99A01.H 0 APMT99A01.Y ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (APMT99A01.H 1 APMT99A01.Y ≅ ModuleCat.of ℤ (ZMod 2)) ∧
    Nonempty (APMT99A01.H 2 APMT99A01.Y ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (APMT99A01.H 0 APMT99A01.Z ≅ ModuleCat.of ℤ ℤ) ∧
    Limits.IsZero (APMT99A01.H 1 APMT99A01.Z) ∧
    Nonempty (APMT99A01.H 2 APMT99A01.Z ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    (∀ k : ℕ, 3 ≤ k →
      Limits.IsZero (APMT99A01.H k APMT99A01.X) ∧
      Limits.IsZero (APMT99A01.H k APMT99A01.Y) ∧
      Limits.IsZero (APMT99A01.H k APMT99A01.Z)) := by
  exact ⟨t99A01_piOne_X, t99A01_piOne_Y, t99A01_piOne_Z,
    t99A01_hZero_X, t99A01_hOne_X, t99A01_hTwo_X,
    t99A01_hZero_Y, t99A01_hOne_Y, t99A01_hTwo_Y,
    t99A01_hZero_Z, t99A01_hOne_Z, t99A01_hTwo_Z,
    fun k hk ↦ ⟨t99A01_hHigher_X k hk, t99A01_hHigher_Y k hk,
      t99A01_hHigher_Z k hk⟩⟩

theorem apm_t99a01 :
    Nonempty (FundamentalGroup APMT99A01.X
      (APMT99A01.basepoint APMT99A01.degreeX) ≃*
        Multiplicative (ZMod 2)) ∧
    Nonempty (FundamentalGroup APMT99A01.Y
      (APMT99A01.basepoint APMT99A01.degreeY) ≃*
        Multiplicative (ZMod 2)) ∧
    Subsingleton (FundamentalGroup APMT99A01.Z
      (APMT99A01.basepoint APMT99A01.degreeZ)) ∧
    Nonempty (APMT99A01.H 0 APMT99A01.X ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (APMT99A01.H 1 APMT99A01.X ≅ ModuleCat.of ℤ (ZMod 2)) ∧
    Limits.IsZero (APMT99A01.H 2 APMT99A01.X) ∧
    Nonempty (APMT99A01.H 0 APMT99A01.Y ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (APMT99A01.H 1 APMT99A01.Y ≅ ModuleCat.of ℤ (ZMod 2)) ∧
    Nonempty (APMT99A01.H 2 APMT99A01.Y ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (APMT99A01.H 0 APMT99A01.Z ≅ ModuleCat.of ℤ ℤ) ∧
    Limits.IsZero (APMT99A01.H 1 APMT99A01.Z) ∧
    Nonempty (APMT99A01.H 2 APMT99A01.Z ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    (∀ k : ℕ, 3 ≤ k →
      Limits.IsZero (APMT99A01.H k APMT99A01.X) ∧
      Limits.IsZero (APMT99A01.H k APMT99A01.Y) ∧
      Limits.IsZero (APMT99A01.H k APMT99A01.Z)) := by
  exact t99A01_attached_cells_computation

#print axioms apm_t99a01
