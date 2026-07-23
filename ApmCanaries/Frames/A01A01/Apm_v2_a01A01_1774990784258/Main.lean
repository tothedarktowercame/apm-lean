import Mathlib
import ApmCanaries.Frames.A01A01.Apm_v2_a01A01_1774990784258.Scratch

noncomputable section

open scoped BigOperators MeasureTheory Topology

namespace ApmCanaries.Frames.A01A01.Apm_v2_a01A01_1774990784258.Main

/-- Short alias for the unit interval `[0,1]`. -/
def unitInterval : Set ℝ := Set.Icc (0 : ℝ) 1

/-- Lebesgue measure restricted to `[0,1]`. -/
def μ₀₁ : Measure ℝ := volume.restrict unitInterval

/-- A convenient package collecting the three properties requested in the problem. -/
structure SpikeCertificate (μ : Measure ℝ) where
  seq : ℕ → ℝ → ℝ
  nonneg : ∀ k x, 0 ≤ seq k x
  limsup_infinite : ∀ ⦃x : ℝ⦄, x ∈ unitInterval → ∀ R > 0,
    (∃ᶠ k in Filter.atTop, R ≤ seq k x)
  integral_tendsto_zero :
    Tendsto (fun k => ∫ x, seq k x ∂μ) Filter.atTop (𝓝 0)

namespace Construction

open Classical

/-- Height of the spike used at “stage” `m`. -/
def spikeHeight (m : ℕ) : ℝ := (m.succ : ℝ) ^ 2

/-- Number of dyadic tiles at “stage” `m`. -/
def stageTiles (m : ℕ) : ℕ := 2 ^ (m.succ)

/-- Left endpoint of the tile associated to `(m,j)` (with wrap-around). -/
def tileLeft (m j : ℕ) : ℝ :=
  (Nat.mod j (stageTiles m) : ℝ) / stageTiles m

/-- Right endpoint of the tile associated to `(m,j)`. -/
def tileRight (m j : ℕ) : ℝ :=
  ((Nat.mod j (stageTiles m) + 1 : ℕ) : ℝ) / stageTiles m

/-- The actual spike function number `k`, supported on a dyadic tile. -/
def unitSpike (k : ℕ) : ℝ → ℝ :=
  let p := Nat.unpair k
  let m := p.1
  let j := p.2
  spikeHeight m *
    Set.indicator (Set.Icc (tileLeft m j) (tileRight m j) ∩ unitInterval)
      (fun _ => (1 : ℝ))

lemma unitSpike_nonneg (k : ℕ) : ∀ x, 0 ≤ unitSpike k x := by
  classical
  intro x
  -- The indicator is nonnegative and the spike height is positive.
  -- TODO: unwrap the indicator and turn this into a short calculation.
  sorry

lemma unitSpike_integral (k : ℕ) :
    ∫ x, unitSpike k x ∂μ₀₁ =
      spikeHeight (Nat.unpair k).1 / stageTiles (Nat.unpair k).1 := by
  classical
  -- The integral equals `height × length` because the spike is constant on its tile.
  sorry

lemma unitSpike_limsup (x : ℝ) (hx : x ∈ unitInterval) :
    ∀ R > 0, (∃ᶠ k in Filter.atTop, R ≤ unitSpike k x) := by
  classical
  -- For each stage `m`, exactly one spike contains `x`; its height grows like `m²`.
  sorry

/-- Bundle the explicit unit-interval construction into a spike certificate. -/
def unitIntervalCertificate : SpikeCertificate μ₀₁ where
  seq := unitSpike
  nonneg := unitSpike_nonneg
  limsup_infinite := by
    classical
    intro x hx R hR
    simpa using unitSpike_limsup x hx R hR
  integral_tendsto_zero := by
    classical
    -- Each stage contributes `(m+1)^2 / 2^{m+1}`, which tends to zero.
    -- Conclude using the explicit `unitSpike_integral` formula.
    sorry

end Construction

/-- Part (1): a concrete spike sequence on `[0,1]` with integral going to zero. -/
theorem exists_unit_interval_spikes :
    ∃ cert : SpikeCertificate μ₀₁, True := by
  refine ⟨Construction.unitIntervalCertificate, trivial⟩

/-- Inflate the one-dimensional construction to `ℝⁿ` by composing with a coordinate. -/
theorem exists_spikes_Rn (n : ℕ) :
    ∃ seq : ℕ → (EuclideanSpace (Fin n) ℝ) → ℝ,
      (∀ k x, 0 ≤ seq k x) ∧
      (∀ x R, 0 < R → (∃ᶠ k in Filter.atTop, R ≤ seq k x)) ∧
      Tendsto (fun k => ∫ x, seq k x ∂volume) Filter.atTop (𝓝 0) := by
  classical
  -- Pull back `Construction.unitSpike` along the first coordinate and damp it
  -- outside the unit cube; all required estimates mirror the `[0,1]` case.
  sorry

end ApmCanaries.Frames.A01A01.Apm_v2_a01A01_1774990784258.Main
