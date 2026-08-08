import Mathlib

/-!
# APM t95J04 — low-dimensional maps to spheres and six-manifolds

Part (a) uses genuine finite-dimensional Mathlib manifolds and `ContMDiff`
maps.  The Sard/dimension consequence—nullity of the image and hence failure
of surjectivity—is in the conclusion, not stored in the definition of a
“smooth map.”  Part (b) uses the concrete metric spheres and their products.

## Statement repairs

None.

## Encoding questions

Non-diffeomorphism in part (b) is stated via the stronger conclusion that the
underlying spaces are not homeomorphic.  This avoids introducing a surrogate
diffeomorphism predicate while still implying the source claim.
-/

open Set MeasureTheory
open scoped ContDiff Manifold ENNReal

noncomputable section

abbrev T95J04E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev T95J04I (n : ℕ) := 𝓘(ℝ, T95J04E n)
abbrev T95J04Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

abbrev T95J04SphereSix := T95J04Sphere 6
abbrev T95J04SphereTwoFour := T95J04Sphere 2 × T95J04Sphere 4
abbrev T95J04SphereThreeThree := T95J04Sphere 3 × T95J04Sphere 3

def t95J04NullHomotopic {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf : Continuous f) : Prop :=
  ∃ y : Y,
    ContinuousMap.Homotopic ⟨f, hf⟩ (ContinuousMap.const X y)

/-- An explicit coordinate point on every sphere used in the statement. -/
lemma t95J04_sphere_nonempty (n : ℕ) : Nonempty (T95J04Sphere n) := by
  exact ⟨⟨EuclideanSpace.single 0 1, by simp [T95J04Sphere]⟩⟩

lemma t95J04_sphereSix_nonempty : Nonempty T95J04SphereSix :=
  t95J04_sphere_nonempty 6

lemma t95J04_sphereTwoFour_nonempty : Nonempty T95J04SphereTwoFour :=
  Nonempty.map2 (fun x y ↦ (x, y))
    (t95J04_sphere_nonempty 2) (t95J04_sphere_nonempty 4)

lemma t95J04_sphereThreeThree_nonempty : Nonempty T95J04SphereThreeThree :=
  Nonempty.map2 (fun x y ↦ (x, y))
    (t95J04_sphere_nonempty 3) (t95J04_sphere_nonempty 3)

theorem apm_t95j04 :
    (∀ (k n : ℕ), k < n →
      ∀ (M : Type*) [TopologicalSpace M] [T2Space M]
        [SecondCountableTopology M] [CompactSpace M]
        [ChartedSpace (T95J04E k) M] [IsManifold (T95J04I k) ∞ M]
        (f : M → T95J04Sphere n),
        ∀ hf : ContMDiff (T95J04I k) (T95J04I n) ∞ f,
        μH[n] (Set.range f) = 0 ∧
        ¬ Function.Surjective f ∧
        t95J04NullHomotopic f hf.continuous) ∧
    SimplyConnectedSpace T95J04SphereSix ∧
    SimplyConnectedSpace T95J04SphereTwoFour ∧
    SimplyConnectedSpace T95J04SphereThreeThree ∧
    ¬ Nonempty (T95J04SphereSix ≃ₜ T95J04SphereTwoFour) ∧
    ¬ Nonempty (T95J04SphereSix ≃ₜ T95J04SphereThreeThree) ∧
    ¬ Nonempty (T95J04SphereTwoFour ≃ₜ T95J04SphereThreeThree) := by
  /-
  CLOSER HOP 2 boundary. The repaired statement now again has compiled,
  explicit inhabitants for `S⁶`, `S² × S⁴`, and `S³ × S³`; unlike relying on
  eventual simple-connectivity instances, these close the nonemptiness input
  needed by any direct fundamental-group or homotopy construction.

  The first conjunct still requires a manifold-domain Sard theorem proving
  `μH[n] (range f) = 0`. The repository's chartwise Sard artifacts and
  Mathlib's available results cover maps between finite-dimensional normed
  vector spaces, not arbitrary `IsManifold` domains. Non-surjectivity would
  then follow from positive Hausdorff measure of the sphere, and null-homotopy
  requires contracting the complement of an omitted point via stereographic
  projection.

  For the remaining clauses, searches of `LEMMA-INDEX.md`,
  `ConstructionTargets/`, sphere/product siblings, Mathlib's sphere,
  stereographic, fundamental-groupoid, singular-homology, and Künneth sources,
  and git history found no compiled simple-connectivity theorem for these
  metric spheres and no homology computations distinguishing the three
  six-dimensional spaces. Those foundational bridges remain open.
  -/
  sorry
