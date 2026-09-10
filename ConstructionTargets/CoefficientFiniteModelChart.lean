import ConstructionTargets.CoefficientChartLocalAllDegrees
noncomputable section
namespace ConstructionTargets.CoefficientFiniteModelChart
open CategoryTheory
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
variable {d : ℕ}
def coordinates (hd : Module.finrank ℝ E = d) : E ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ContinuousLinearEquiv.ofFinrankEq (by simpa using hd)
def converted (hd : Module.finrank ℝ E = d) (e : OpenPartialHomeomorph M E) :=
  e.trans (coordinates hd).toHomeomorph.toOpenPartialHomeomorph
omit [ChartedSpace E M] in
lemma converted_source (hd : Module.finrank ℝ E = d) (e : OpenPartialHomeomorph M E) :
    (converted hd e).source = e.source := by simp [converted]
@[implicit_reducible]
def euclideanAtlas (hd : Module.finrank ℝ E = d) : ChartedSpace (EuclideanSpace ℝ (Fin d)) M where
  atlas := converted hd '' atlas E M
  chartAt x := converted hd (chartAt E x)
  mem_chart_source x := by rw [converted_source]; exact mem_chart_source E x
  chart_mem_atlas x := ⟨chartAt E x, chart_mem_atlas E x, rfl⟩
theorem chart_spec (hd : Module.finrank ℝ E = d) (x : M) :
    (letI := euclideanAtlas (M := M) hd; chartAt (EuclideanSpace ℝ (Fin d)) x) =
      converted hd (chartAt E x) := rfl
theorem atlas_spec (hd : Module.finrank ℝ E = d) :
    (letI := euclideanAtlas (M := M) hd; atlas (EuclideanSpace ℝ (Fin d)) M) =
      converted hd '' atlas E M := rfl
theorem coordinate_value (hd : Module.finrank ℝ E = d) (x y : M) :
    converted hd (chartAt E x) y = coordinates hd (chartAt E x y) := rfl
theorem inverse_value (hd : Module.finrank ℝ E = d) (x : M) (y : EuclideanSpace ℝ (Fin d)) :
    (converted hd (chartAt E x)).symm y = (chartAt E x).symm ((coordinates hd).symm y) := rfl
variable (R : Type) [CommRing R] [T2Space M]
def comparison (m : ℕ) (hd : Module.finrank ℝ E = m+2) (x : M) (n : ℕ) :=
  letI := euclideanAtlas (M := M) hd
  CoefficientChartLocalAllDegrees.comparison R m x n

theorem forward (m : ℕ) (hd : Module.finrank ℝ E = m+2) (x : M) (n : ℕ) :
    (comparison R m hd x n).hom =
      (letI := euclideanAtlas (M := M) hd
       (CoefficientChartLocalAllDegrees.comparison R m x n).hom) := rfl

theorem actual_forward (m : ℕ) (hd : Module.finrank ℝ E = m+2) (x : M) (n : ℕ) :
    letI := euclideanAtlas (M := M) hd
    (comparison R m hd x n).hom =
      (CoefficientNeighborhoodLocal.inclusionIso R (chartAt (CoefficientChartLocal.E m) x).source x
        (chartAt (CoefficientChartLocal.E m) x).open_source (CoefficientChartPair.source_member (m+2) x) n).inv ≫
      (CoefficientChartLocal.sourceTransport R m x n).inv ≫
      HomologicalComplex.homologyMap (CoefficientChartPair.deletedMap R
        (CoefficientChartLocal.pointedChart m x) (CoefficientChartPair.sourcePoint (m+2) x)) n ≫
      (CoefficientChartLocal.targetTransport R m x n).hom ≫
      HomologicalComplex.homologyMap (CoefficientNeighborhoodLocal.inclusionMap R
        (CoefficientChartLocal.pointedTarget m x) 0) n := by
  letI := euclideanAtlas (M := M) hd
  exact CoefficientChartLocalAllDegrees.forward R m x n

theorem inverse_left (m : ℕ) (hd : Module.finrank ℝ E = m+2) (x : M) (n : ℕ) :
    (comparison R m hd x n).inv ≫ (comparison R m hd x n).hom = 𝟙 _ :=
  (comparison R m hd x n).inv_hom_id

theorem inverse_right (m : ℕ) (hd : Module.finrank ℝ E = m+2) (x : M) (n : ℕ) :
    (comparison R m hd x n).hom ≫ (comparison R m hd x n).inv = 𝟙 _ :=
  (comparison R m hd x n).hom_inv_id

def normalization (m : ℕ) (hd : Module.finrank ℝ E = m+2) (x : M) :=
  comparison R m hd x (m+2) ≪≫ CoefficientModelLocal.localIso R m

def generator (m : ℕ) (hd : Module.finrank ℝ E = m+2) (x : M) :=
  (normalization R m hd x).inv.hom (1 : R)
theorem generator_normalization (m : ℕ) (hd : Module.finrank ℝ E = m+2) (x : M) :
    (normalization R m hd x).hom.hom (generator R m hd x) = 1 :=
  congrArg (fun f => f.hom (1 : R)) (normalization R m hd x).inv_hom_id
#print axioms coordinates
#print axioms euclideanAtlas
#print axioms chart_spec
#print axioms atlas_spec
#print axioms coordinate_value
#print axioms inverse_value
#print axioms comparison
#print axioms forward
#print axioms actual_forward
#print axioms inverse_left
#print axioms inverse_right
#print axioms generator_normalization
end ConstructionTargets.CoefficientFiniteModelChart
