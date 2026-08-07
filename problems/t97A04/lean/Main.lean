import Mathlib

/-!
# APM t97A04

## Statement repairs

* Part (a) asks for the degree of `L : ℝ² → ℝ²`.  Degree is intended for the
  induced torus self-map `L̄`, as confirmed by the surrounding text and the
  supplied solution; the statement records `degree(L̄)`.

## Encoding questions

The torus is encoded concretely as `(ℝ/ℤ)²` using `AddCircle 1`.  Mathlib does
not currently expose singular homology or Lefschetz numbers for this torus, so
`H₁(T²;ℤ)` is pinned to its standard concrete model `ℤ²`; the degree and
Lefschetz number are defined from the same integral lift matrix by determinant
and the alternating trace formula.  No opaque constants or axioms are used.
-/

noncomputable section

abbrev apm_t97a04_RealPlane := Fin 2 → ℝ
abbrev apm_t97a04_IntPlane := Fin 2 → ℤ
abbrev apm_t97a04_Torus := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

def apm_t97a04_L (p : apm_t97a04_RealPlane) : apm_t97a04_RealPlane :=
  ![2 * p 0 + p 1, p 1 - p 0]

/-- The map induced on `(ℝ/ℤ)²` by the integral linear lift `L`. -/
def apm_t97a04_Lbar (p : apm_t97a04_Torus) : apm_t97a04_Torus :=
  (2 • p.1 + p.2, p.2 - p.1)

def apm_t97a04_matrix : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(2 : ℤ), 1; -1, 1]

/-- The standard `H₁(T²;ℤ) ≃ ℤ²` coordinate model. -/
def apm_t97a04_inducedH1 (v : apm_t97a04_IntPlane) : apm_t97a04_IntPlane :=
  apm_t97a04_matrix.mulVec v

def apm_t97a04_degree : ℤ :=
  Matrix.det apm_t97a04_matrix

def apm_t97a04_lefschetzNumber : ℤ :=
  1 - Matrix.trace apm_t97a04_matrix + apm_t97a04_degree

theorem apm_t97a04 :
    apm_t97a04_degree = 3 ∧
    apm_t97a04_inducedH1 =
      (fun v : apm_t97a04_IntPlane => ![2 * v 0 + v 1, -v 0 + v 1]) ∧
    apm_t97a04_lefschetzNumber = 1 := by
  sorry
