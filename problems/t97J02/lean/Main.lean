import Mathlib

/-!
# APM t97J02

## Statement repairs

None.

## Encoding questions

Closed classified surfaces are concrete polygon quotients of the unit disk.
For nonorientable genus `g` the edge word is `a₁a₁⋯a_ga_g`; for orientable
genus `g` it is the standard product of `g` commutators. Thus the base `N₄`
and all three candidate covering surfaces are actual topological spaces.
Coverings use Mathlib's `IsCoveringMap` and exact fiber cardinality.
-/

open Set
open scoped Manifold ContDiff

noncomputable section

abbrev apm_t97J02_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t97J02_Disk := Metric.closedBall (0 : ℂ) 1

def apm_t97J02_edgePoint (edgeCount edge : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    apm_t97J02_Disk :=
  ⟨Complex.exp
      (Complex.I * (2 * Real.pi * ((edge : ℝ) + t.1) / edgeCount)), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    simp⟩

/-- The standard polygon edge relation for a classified closed surface. -/
def apm_t97J02_SurfaceRel (orientable : Bool) (genus : ℕ)
    (x y : apm_t97J02_Disk) : Prop :=
  if orientable then
    ∃ j : ℕ, j < genus ∧ ∃ t : Set.Icc (0 : ℝ) 1,
      let tr : Set.Icc (0 : ℝ) 1 :=
        ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
      (x = apm_t97J02_edgePoint (4 * genus) (4 * j) t ∧
          y = apm_t97J02_edgePoint (4 * genus) (4 * j + 2) tr) ∨
        (x = apm_t97J02_edgePoint (4 * genus) (4 * j + 1) t ∧
          y = apm_t97J02_edgePoint (4 * genus) (4 * j + 3) tr)
  else
    ∃ j : ℕ, j < genus ∧ ∃ t : Set.Icc (0 : ℝ) 1,
      x = apm_t97J02_edgePoint (2 * genus) (2 * j) t ∧
      y = apm_t97J02_edgePoint (2 * genus) (2 * j + 1) t

def apm_t97J02_Surface (orientable : Bool) (genus : ℕ) :=
  Quotient (Relation.EqvGen.setoid
    (apm_t97J02_SurfaceRel orientable genus))

noncomputable instance (orientable : Bool) (genus : ℕ) :
    TopologicalSpace (apm_t97J02_Surface orientable genus) :=
  TopologicalSpace.coinduced
    (fun x : apm_t97J02_Disk ↦ Quotient.mk _ x) inferInstance

def apm_t97J02_surfaceQuotient (orientable : Bool) (genus : ℕ) :
    apm_t97J02_Disk → apm_t97J02_Surface orientable genus :=
  fun x => Quotient.mk _ x

lemma apm_t97J02_continuous_surfaceQuotient (orientable : Bool) (genus : ℕ) :
    Continuous (apm_t97J02_surfaceQuotient orientable genus) := by
  exact continuous_coinduced_rng

lemma apm_t97J02_surjective_surfaceQuotient (orientable : Bool) (genus : ℕ) :
    Function.Surjective (apm_t97J02_surfaceQuotient orientable genus) := by
  exact Quotient.mk_surjective

/-- The Euler-characteristic formula used by the arithmetic classification. -/
def apm_t97J02_eulerCharacteristic (orientable : Bool) (genus : ℕ) : ℤ :=
  if orientable then 2 - 2 * (genus : ℤ) else 2 - (genus : ℤ)

@[simp] lemma apm_t97J02_eulerCharacteristic_orientable (genus : ℕ) :
    apm_t97J02_eulerCharacteristic true genus = 2 - 2 * (genus : ℤ) := rfl

@[simp] lemma apm_t97J02_eulerCharacteristic_nonorientable (genus : ℕ) :
    apm_t97J02_eulerCharacteristic false genus = 2 - (genus : ℤ) := rfl

lemma apm_t97J02_candidate_eulerCharacteristics :
    apm_t97J02_eulerCharacteristic false 4 = -2 ∧
    apm_t97J02_eulerCharacteristic false 12 =
      5 * apm_t97J02_eulerCharacteristic false 4 ∧
    apm_t97J02_eulerCharacteristic true 7 =
      6 * apm_t97J02_eulerCharacteristic false 4 ∧
    apm_t97J02_eulerCharacteristic false 14 =
      6 * apm_t97J02_eulerCharacteristic false 4 := by
  norm_num

/-- Euler multiplicativity over an `n`-sheeted cover of `N₄`, if supplied by
future topology infrastructure, forces the nonorientable genus to be
`2*n+2`. -/
lemma apm_t97J02_nonorientable_genus_of_euler_eq
    (n genus : ℕ)
    (h : apm_t97J02_eulerCharacteristic false genus =
      (n : ℤ) * apm_t97J02_eulerCharacteristic false 4) :
    genus = 2 * n + 2 := by
  simp only [apm_t97J02_eulerCharacteristic_nonorientable] at h
  omega

/-- The same Euler equation forces genus `n+1` in the orientable case. -/
lemma apm_t97J02_orientable_genus_of_euler_eq
    (n genus : ℕ)
    (h : apm_t97J02_eulerCharacteristic true genus =
      (n : ℤ) * apm_t97J02_eulerCharacteristic false 4) :
    genus = n + 1 := by
  simp only [apm_t97J02_eulerCharacteristic_orientable,
    apm_t97J02_eulerCharacteristic_nonorientable] at h
  omega

/-- The connected sum of four real projective planes, `N₄`. -/
abbrev apm_t97J02_X := apm_t97J02_Surface false 4

/-- An exact `n`-sheeted covering of `N₄`. -/
def apm_t97J02_IsNfoldCover
    {E : Type} [TopologicalSpace E] (n : ℕ) (p : E → apm_t97J02_X) : Prop :=
  IsCoveringMap p ∧
    ∀ x : apm_t97J02_X, Nat.card {e : E // p e = x} = n

/-- A covering carried by one of the concrete polygon surfaces. -/
structure apm_t97J02_CoverWitness (orientable : Bool) (genus n : ℕ) where
  p : apm_t97J02_Surface orientable genus → apm_t97J02_X
  covering : apm_t97J02_IsNfoldCover n p

/-- Why this unblocks `apm_t97j02`: this is the missing polygon-gluing
construction and covering-chart verification for all three concrete covers.
It supplies the three existential cover-witness conjuncts of the main
theorem. -/
theorem apm_t97J02_bridge_candidate_covers :
    Nonempty (apm_t97J02_CoverWitness false 12 5) ∧
    Nonempty (apm_t97J02_CoverWitness true 7 6) ∧
    Nonempty (apm_t97J02_CoverWitness false 14 6) := by
  sorry

/-- Why this unblocks `apm_t97j02`: this packages finite-cover Euler
multiplicativity, the odd-degree orientation obstruction, and classification
of compact connected surfaces for the concrete polygon models.  It supplies
both universal classification conjuncts of the main theorem. -/
theorem apm_t97J02_bridge_classify_five_and_six_fold_covers :
    (∀ (E : Type) [TopologicalSpace E] [T2Space E] [CompactSpace E]
        [ConnectedSpace E] [ChartedSpace apm_t97J02_E2 E]
        [IsManifold (modelWithCornersSelf ℝ apm_t97J02_E2) ⊤ E]
        (p : E → apm_t97J02_X),
      apm_t97J02_IsNfoldCover 5 p →
        Nonempty (E ≃ₜ apm_t97J02_Surface false 12)) ∧
    (∀ (E : Type) [TopologicalSpace E] [T2Space E] [CompactSpace E]
        [ConnectedSpace E] [ChartedSpace apm_t97J02_E2 E]
        [IsManifold (modelWithCornersSelf ℝ apm_t97J02_E2) ⊤ E]
        (p : E → apm_t97J02_X),
      apm_t97J02_IsNfoldCover 6 p →
        Nonempty (E ≃ₜ apm_t97J02_Surface true 7) ∨
        Nonempty (E ≃ₜ apm_t97J02_Surface false 14)) := by
  sorry

theorem apm_t97j02 :
    Nonempty (apm_t97J02_CoverWitness false 12 5) ∧
    (∀ (E : Type) [TopologicalSpace E] [T2Space E] [CompactSpace E]
        [ConnectedSpace E] [ChartedSpace apm_t97J02_E2 E]
        [IsManifold (modelWithCornersSelf ℝ apm_t97J02_E2) ⊤ E]
        (p : E → apm_t97J02_X),
      apm_t97J02_IsNfoldCover 5 p →
        Nonempty (E ≃ₜ apm_t97J02_Surface false 12)) ∧
    Nonempty (apm_t97J02_CoverWitness true 7 6) ∧
    Nonempty (apm_t97J02_CoverWitness false 14 6) ∧
    ∀ (E : Type) [TopologicalSpace E] [T2Space E] [CompactSpace E]
        [ConnectedSpace E] [ChartedSpace apm_t97J02_E2 E]
        [IsManifold (modelWithCornersSelf ℝ apm_t97J02_E2) ⊤ E]
        (p : E → apm_t97J02_X),
      apm_t97J02_IsNfoldCover 6 p →
        Nonempty (E ≃ₜ apm_t97J02_Surface true 7) ∨
        Nonempty (E ≃ₜ apm_t97J02_Surface false 14) := by
  /-
  Boundary (closer hop 1): the arithmetic classification is immediate once
  the standard surface-covering theorems are available.  Since `χ(N₄) = -2`,
  multiplicativity gives `χ(E) = -2n`; closed-surface classification then
  leaves `N₁₂` for the odd five-sheeted case, and `Σ₇` or `N₁₄` for six
  sheets.  The orientation character excludes an orientable odd-degree cover.

  The frozen statement retains actual `EqvGen` polygon quotients and actual
  `IsCoveringMap`s.  Searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`,
  Mathlib's covering/manifold sources, and closed covering artifacts
  (`t01A02`, `t01A04`, `t03J03`, `t91A02`) found no Euler characteristic for
  topological manifolds, no multiplicativity theorem for finite covering maps,
  no orientation double-cover/factorization API, and no classification theorem
  for compact connected surfaces.  Mathlib also has no polygon-gluing theorem
  from which to build the three required concrete covering witnesses.

  Thus even locally proving the integer genus equations does not connect to
  the requested `Homeomorph`s.  Closure requires constructing cyclic covers of
  these concrete polygon quotients (and the `3 ∘ 2` orientable cover), proving
  their covering charts/fiber cardinalities, then developing finite-cover
  Euler multiplicativity, the orientation parity obstruction, and surface
  classification for the universal clauses.

  CLOSER HOP 2: `apm_t97J02_surfaceQuotient` now exposes the canonical disk
  projection for every presentation, and its continuity and surjectivity are
  compiled from the coinduced topology. The complete numerical classification
  is also compiled: `apm_t97J02_eulerCharacteristic` implements the orientable
  and nonorientable formulas, and
  `apm_t97J02_candidate_eulerCharacteristics` verifies `χ(N₄)=-2`,
  `χ(N₁₂)=5χ(N₄)`, and both `χ(Σ₇)=6χ(N₄)` and `χ(N₁₄)=6χ(N₄)`.

  Going beyond the prior search, the newly exposed polygon quotient layer in
  sibling `t97A01` was compared and Mathlib's covering-quotient APIs were
  inspected. Those APIs construct covers from properly discontinuous group
  actions, but the present `SurfaceRel` is a boundary-pairing relation with no
  global action or quotient-comparison theorem. Repository-wide inspection
  also confirms that the proposed shared `Surfaces` construction target could
  not supply Euler multiplicativity: its requested theorem is exactly the
  topological result absent here. Thus quotient bookkeeping and integer genus
  equations are closed, while explicit covering maps, their charts/fibers,
  multiplicativity, parity, and surface classification remain open. The frozen
  statement is unchanged.

  CLOSER HOP 3: the candidate arithmetic is now generalized rather than merely
  checked at degrees five and six.
  `apm_t97J02_nonorientable_genus_of_euler_eq` proves that any
  nonorientable surface satisfying the required `n`-sheet Euler equation has
  genus `2*n+2`, and `apm_t97J02_orientable_genus_of_euler_eq` proves that an
  orientable one has genus `n+1`. These `omega` proofs close uniqueness of the
  genus calculation for every degree once multiplicativity and classification
  are available. Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`,
  covering and surface siblings, Mathlib topology/algebraic-topology sources,
  and git history still found no finite-cover Euler theorem, orientation
  parity theorem, polygon-cover construction, or surface classification for
  these actual quotients. The remaining bridge is wholly topological; the
  frozen statement is unchanged.
  -/
  sorry
