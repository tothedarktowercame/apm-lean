import Mathlib
import ConstructionTargets.ManifoldTopFormIntegral
import ConstructionTargets.ManifoldFormTargets

/-!
# APM t01A05 — finite oriented covers

The definitions below use the standard differential-topological meanings.

* A `k`-sheeted smooth cover is a topological covering map, with exactly `k`
  points in every fibre, which is smooth and a local diffeomorphism.
* Orientation preservation says that the pullback of the chosen downstairs
  positive top form is pointwise a positive multiple of the chosen upstairs
  positive top form.  This is the usual definition for a local diffeomorphism.
* A compact oriented submanifold is presented by a smooth embedding of a
  compact boundaryless oriented manifold.  This remembers the orientation,
  which a bare subset cannot do.
* Transversality says that, at each intersection pair, the derivative of a
  smooth representative of the first submanifold and that of the embedded
  second submanifold span the ambient tangent space.
* The local intersection sign compares the ambient orientation on the
  concatenated derivative frames with the two source orientations.  The
  intersection number is the finite sum of these signs.  Its definition has
  no infinite-sum fallback: finiteness is an explicit argument.  For arbitrary
  pairs, `HasIntersectionNumber` chooses a smoothly homotopic transverse
  representative.  Independence of this choice is a theorem of intersection
  theory and is not needed by the implication used in the main statement.
-/

open Set
open scoped Manifold ContDiff
noncomputable section

namespace T01A05

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Model (n : ℕ) := 𝓘(ℝ, E n)
abbrev Orientation (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (Model n) ∞ M] :=
  ConstructionTargets.ManifoldTopFormIntegral.Orientation (n := n) M
abbrev Form := ConstructionTargets.ManifoldFormTargets.Form

/-- A smooth `k`-sheeted covering, including its local-diffeomorphism property. -/
def IsKSheetedSmoothCover {n : ℕ} {Y X : Type*}
    [TopologicalSpace Y] [ChartedSpace (E n) Y]
    [TopologicalSpace X] [ChartedSpace (E n) X]
    (k : ℕ) (π : Y → X) : Prop :=
  IsCoveringMap π ∧
  (∀ x : X, Nat.card {y : Y // π y = x} = k) ∧
  ContMDiff (Model n) (Model n) ∞ π ∧
  IsLocalDiffeomorph (Model n) (Model n) ∞ π

/-- The pullback of the downstairs positive volume form is positively
proportional to the upstairs one at every point. -/
def IsOrientationPreserving {n : ℕ} {Y X : Type*}
    [TopologicalSpace Y] [ChartedSpace (E n) Y]
    [TopologicalSpace X] [ChartedSpace (E n) X]
    [IsManifold (Model n) ∞ Y] [IsManifold (Model n) ∞ X]
    (π : Y → X) (oY : Orientation n Y)
    (oX : Orientation n X) : Prop :=
  ∀ y : Y, ∃ c : ℝ, 0 < c ∧
    ConstructionTargets.ManifoldFormTargets.pullback π oX.form y = c • oY.form y

/-- A compact oriented submanifold, represented by its standard intrinsic
manifold and a smooth embedding into the ambient manifold. -/
structure OrientedSubmanifold (d n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (E n) X] where
  carrier : Type*
  topology : TopologicalSpace carrier
  t2 : T2Space carrier
  compact : CompactSpace carrier
  charts : ChartedSpace (E d) carrier
  manifold : IsManifold (Model d) ∞ carrier
  orientation : Orientation d carrier
  inclusion : carrier → X
  embedding : Topology.IsEmbedding inclusion ∧ ContMDiff (Model d) (Model n) ∞ inclusion

attribute [instance] OrientedSubmanifold.topology OrientedSubmanifold.t2
  OrientedSubmanifold.compact OrientedSubmanifold.charts OrientedSubmanifold.manifold

/-- Pairs of source points representing intersections of two embedded
submanifolds. -/
def IntersectionPoints {d e n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (E n) X]
    (A : OrientedSubmanifold d n X) (B : OrientedSubmanifold e n X)
    (a : A.carrier → X) :=
  {pq : A.carrier × B.carrier // a pq.1 = B.inclusion pq.2}

/-- The usual derivative-spanning definition of transverse embeddings. -/
def AreTransverse {d e n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (E n) X]
    (A : OrientedSubmanifold d n X) (B : OrientedSubmanifold e n X)
    (a : A.carrier → X) : Prop :=
  ∀ p : A.carrier, ∀ q : B.carrier, a p = B.inclusion q →
    LinearMap.range (mfderiv (Model d) (Model n) a p).toLinearMap ⊔
      LinearMap.range (mfderiv (Model e) (Model n) B.inclusion q).toLinearMap = ⊤

/-- The concatenated frame obtained from the derivatives of the two
embeddings, using the standard ordered Euclidean frames on their models. -/
def intersectionFrame {d e n : ℕ} (hdim : d + e = n) {X : Type*}
    [TopologicalSpace X] [ChartedSpace (E n) X]
    (A : OrientedSubmanifold d n X) (B : OrientedSubmanifold e n X)
    (a : A.carrier → X) (p : A.carrier) (q : B.carrier) (i : Fin n) : E n :=
  if h : i.val < d then
    mfderiv (Model d) (Model n) a p
      (EuclideanSpace.basisFun (Fin d) ℝ ⟨i.val, h⟩)
  else
    mfderiv (Model e) (Model n) B.inclusion q
      (EuclideanSpace.basisFun (Fin e) ℝ
        ⟨i.val - d, by omega⟩)

/-- The standard local oriented-intersection sign.  Multiplying the three
orientation evaluations gives the comparison sign, since each source factor
is nonzero and only its sign matters. -/
def localIntersectionSign {d e n : ℕ} (hdim : d + e = n) {X : Type*}
    [TopologicalSpace X] [ChartedSpace (E n) X]
    [IsManifold (Model n) ∞ X]
    (oX : Orientation n X)
    (A : OrientedSubmanifold d n X) (B : OrientedSubmanifold e n X)
    (a : A.carrier → X) (z : IntersectionPoints A B a) : ℤ :=
  if 0 <
      oX.form (a z.1.1) (intersectionFrame hdim A B a z.1.1 z.1.2) *
      A.orientation.form z.1.1 (EuclideanSpace.basisFun (Fin d) ℝ) *
      B.orientation.form z.1.2 (EuclideanSpace.basisFun (Fin e) ℝ)
    then 1 else -1

/-- The algebraic intersection number: the finite sum of the local signs. -/
def intersectionNumber {d e n : ℕ} (hdim : d + e = n) {X : Type*}
    [TopologicalSpace X] [ChartedSpace (E n) X]
    [IsManifold (Model n) ∞ X]
    (oX : Orientation n X)
    (A : OrientedSubmanifold d n X) (B : OrientedSubmanifold e n X)
    (a : A.carrier → X) (hfinite : Finite (IntersectionPoints A B a)) : ℤ := by
  letI : Fintype (IntersectionPoints A B a) := Fintype.ofFinite _
  exact ∑ z : IntersectionPoints A B a, localIntersectionSign hdim oX A B a z

/-- A smooth homotopy through maps from the source manifold. -/
def AreSmoothlyHomotopic {d n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (E n) X]
    {A : Type*} [TopologicalSpace A] [ChartedSpace (E d) A]
    (f g : A → X) : Prop :=
  ∃ H : A × ℝ → X,
    ContMDiff ((Model d).prod 𝓘(ℝ, ℝ)) (Model n) ∞ H ∧
    (∀ p, H (p, 0) = f p) ∧ (∀ p, H (p, 1) = g p)

/-- The Guillemin--Pollack definition: perturb the first embedding smoothly
within its homotopy class to a transverse map and take its finite signed count. -/
def HasIntersectionNumber {d e n : ℕ} (hdim : d + e = n) {X : Type*}
    [TopologicalSpace X] [ChartedSpace (E n) X]
    [IsManifold (Model n) ∞ X] (oX : Orientation n X)
    (A : OrientedSubmanifold d n X) (B : OrientedSubmanifold e n X)
    (m : ℤ) : Prop :=
  ∃ a : A.carrier → X,
    ContMDiff (Model d) (Model n) ∞ a ∧
    AreSmoothlyHomotopic (d := d) (n := n) A.inclusion a ∧ AreTransverse A B a ∧
    ∃ hfinite : Finite (IntersectionPoints A B a),
      intersectionNumber hdim oX A B a hfinite = m

/-- Sanity: a one-sheeted cover really has singleton fibres. -/
theorem isKSheetedSmoothCover_fibre_sanity {n : ℕ} {Y X : Type*}
    [TopologicalSpace Y] [ChartedSpace (E n) Y]
    [TopologicalSpace X] [ChartedSpace (E n) X]
    {π : Y → X} (h : IsKSheetedSmoothCover (n := n) 1 π) (x : X) :
    Nat.card {y : Y // π y = x} = 1 := h.2.1 x

/-- Sanity: orientation preservation records a genuinely positive multiplier. -/
theorem orientationPreserving_positive_sanity {n : ℕ} {Y X : Type*}
    [TopologicalSpace Y] [ChartedSpace (E n) Y]
    [TopologicalSpace X] [ChartedSpace (E n) X]
    [IsManifold (Model n) ∞ Y] [IsManifold (Model n) ∞ X]
    {π : Y → X} {oY : Orientation n Y} {oX : Orientation n X}
    (h : IsOrientationPreserving π oY oX) (y : Y) :
    ∃ c : ℝ, 0 < c ∧
      ConstructionTargets.ManifoldFormTargets.pullback π oX.form y = c • oY.form y :=
  h y

/-- Sanity: every transverse local contribution is an actual orientation
sign, never zero or another integer. -/
theorem localIntersectionSign_sanity {d e n : ℕ} (hdim : d + e = n)
    {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X]
    [IsManifold (Model n) ∞ X] (oX : Orientation n X)
    (A : OrientedSubmanifold d n X) (B : OrientedSubmanifold e n X)
    (a : A.carrier → X) (z : IntersectionPoints A B a) :
    localIntersectionSign hdim oX A B a z = 1 ∨
      localIntersectionSign hdim oX A B a z = -1 := by
  unfold localIntersectionSign
  split <;> simp

/-- Sanity: an already transverse embedded pair computes its own intersection
number, using the constant smooth homotopy. -/
theorem hasIntersectionNumber_of_transverse {d e n : ℕ} (hdim : d + e = n)
    {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X]
    [IsManifold (Model n) ∞ X] (oX : Orientation n X)
    (A : OrientedSubmanifold d n X) (B : OrientedSubmanifold e n X)
    (htrans : AreTransverse A B A.inclusion)
    (hfinite : Finite (IntersectionPoints A B A.inclusion)) :
    HasIntersectionNumber hdim oX A B
      (intersectionNumber hdim oX A B A.inclusion hfinite) := by
  refine ⟨A.inclusion, A.embedding.2, ?_, htrans, hfinite, rfl⟩
  refine ⟨fun p ↦ A.inclusion p.1, ?_, ?_, ?_⟩
  · exact A.embedding.2.comp contMDiff_fst
  · intro p
    rfl
  · intro p
    rfl

end T01A05

open T01A05

theorem apm_t01a05 :
    (∀ k : ℕ, 0 < k →
      ∃ (X Xtilde : Type)
        (_ : TopologicalSpace X) (_ : T2Space X) (_ : CompactSpace X)
        (_ : ChartedSpace (E 2) X) (_ : IsManifold (Model 2) ∞ X)
        (_ : TopologicalSpace Xtilde) (_ : T2Space Xtilde)
        (_ : CompactSpace Xtilde) (_ : ChartedSpace (E 2) Xtilde)
        (_ : IsManifold (Model 2) ∞ Xtilde)
        (π : Xtilde → X) (oX : Orientation 2 X)
        (oXtilde : Orientation 2 Xtilde),
        Nonempty X ∧ ConnectedSpace Xtilde ∧
        IsKSheetedSmoothCover (n := 2) k π ∧
        IsOrientationPreserving π oXtilde oX) ∧
    (∀ (n k : ℕ) (X Xtilde : Type*)
      [TopologicalSpace X] [T2Space X] [CompactSpace X]
      [ChartedSpace (E n) X] [IsManifold (Model n) ∞ X]
      [TopologicalSpace Xtilde] [T2Space Xtilde] [CompactSpace Xtilde]
      [ChartedSpace (E n) Xtilde] [IsManifold (Model n) ∞ Xtilde]
      (π : Xtilde → X) (oX : Orientation n X)
      (oXtilde : Orientation n Xtilde),
      IsKSheetedSmoothCover (n := n) k π → IsOrientationPreserving π oXtilde oX →
      (∀ (w : Form (E n) X n),
        ConstructionTargets.ManifoldFormTargets.IsSmooth w →
        ConstructionTargets.ManifoldTopFormIntegral.IntegrableTopForm oX w ∧
        ConstructionTargets.ManifoldTopFormIntegral.IntegrableTopForm oXtilde
          (ConstructionTargets.ManifoldFormTargets.pullback π w) ∧
        ConstructionTargets.ManifoldTopFormIntegral.integral oXtilde
            (ConstructionTargets.ManifoldFormTargets.pullback π w) =
          k * ConstructionTargets.ManifoldTopFormIntegral.integral oX w)) ∧
    (∀ (n d e k : ℕ) (hdim : d + e = n)
      (X Xtilde : Type*)
      [TopologicalSpace X] [T2Space X] [CompactSpace X]
      [ChartedSpace (E n) X] [IsManifold (Model n) ∞ X]
      [TopologicalSpace Xtilde] [T2Space Xtilde] [CompactSpace Xtilde]
      [ChartedSpace (E n) Xtilde] [IsManifold (Model n) ∞ Xtilde]
      (π : Xtilde → X) (oX : Orientation n X)
      (oXtilde : Orientation n Xtilde)
      (A : OrientedSubmanifold d n X) (B : OrientedSubmanifold e n X),
      IsKSheetedSmoothCover (n := n) k π → IsOrientationPreserving π oXtilde oX →
      ∃ (Atilde : OrientedSubmanifold d n Xtilde)
        (Btilde : OrientedSubmanifold e n Xtilde)
        (ρA : Atilde.carrier → A.carrier)
        (ρB : Btilde.carrier → B.carrier),
        Set.range Atilde.inclusion = π ⁻¹' Set.range A.inclusion ∧
        Set.range Btilde.inclusion = π ⁻¹' Set.range B.inclusion ∧
        ContMDiff (Model d) (Model d) ∞ ρA ∧
        (∀ p, A.inclusion (ρA p) = π (Atilde.inclusion p)) ∧
        IsOrientationPreserving ρA Atilde.orientation A.orientation ∧
        ContMDiff (Model e) (Model e) ∞ ρB ∧
        (∀ p, B.inclusion (ρB p) = π (Btilde.inclusion p)) ∧
        IsOrientationPreserving ρB Btilde.orientation B.orientation ∧
        ∀ m : ℤ, HasIntersectionNumber hdim oX A B m →
          HasIntersectionNumber hdim oXtilde Atilde Btilde (k * m)) := by
  sorry
