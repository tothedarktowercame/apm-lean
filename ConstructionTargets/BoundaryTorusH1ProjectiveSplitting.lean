import ConstructionTargets.BoundaryTorusH2ConnectingIso
import ConstructionTargets.ProjectiveQuotientExactSplitting
import Mathlib.Algebra.Category.ModuleCat.Projective

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.BoundaryTorusH1ProjectiveSplitting

open ConstructionTargets.BoundaryTorusMayerVietoris
open ConstructionTargets.BoundaryTorusMayerVietorisAlgebra
open ConstructionTargets.BoundaryTorusMayerVietorisExactness
open ConstructionTargets.BoundaryTorusMayerVietorisAdjacentExactness
open ConstructionTargets.SingularHomologyConcrete
open ProjectiveQuotientExactSplitting

private abbrev H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  SingularHomology k (TopCat.of X)

private abbrev BT :=
  ConstructionTargets.SolidTorusGluingOpenCover.BoundaryTorus

private abbrev Z := BoundaryTorusMayerVietorisAlgebra.IntGroup

private abbrev reassembly :=
  integerReassemblyArrow 1 circleH1GroupIsoInt

private abbrev connecting :=
  integerConnectingArrow 0 circleH0GroupIsoInt

/-- The degree-one union segment with its two arrows exposed literally. -/
noncomputable def h1UnionLiteralShortComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk reassembly connecting (by
    change integerReassemblyArrow 1 circleH1GroupIsoInt ≫
      integerConnectingArrow 0 circleH0GroupIsoInt = 0
    rw [← integerUnionShortComplex_f 0 circleH1GroupIsoInt circleH0GroupIsoInt,
      ← integerUnionShortComplex_g 0 circleH1GroupIsoInt circleH0GroupIsoInt]
    exact (integerUnionShortComplex 0 circleH1GroupIsoInt circleH0GroupIsoInt).zero)

theorem h1UnionLiteralShortComplex_exact : h1UnionLiteralShortComplex.Exact := by
  apply ShortComplex.exact_of_iso ?_
    (integerUnionShortComplex_H1_H0_exact)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using
      integerUnionShortComplex_f 0 circleH1GroupIsoInt circleH0GroupIsoInt)
    (by simpa using
      (integerUnionShortComplex_g 0 circleH1GroupIsoInt circleH0GroupIsoInt).symm)

/-- The canonical short complex obtained by descending reassembly through its
coimage and projecting the connecting map to its coimage. -/
noncomputable def h1CoreShortComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (Abelian.factorThruCoimage reassembly)
    (Abelian.coimage.π connecting) (by
      apply (cancel_epi (Abelian.coimage.π reassembly)).1
      rw [← Category.assoc, Abelian.coimage.fac]
      exact Abelian.comp_coimage_π_eq_zero h1UnionLiteralShortComplex.zero)

private noncomputable def h1LeftDescendedShortComplex :
    ShortComplex AddCommGrpCat :=
  ShortComplex.mk (Abelian.factorThruCoimage reassembly) connecting (by
    apply (cancel_epi (Abelian.coimage.π reassembly)).1
    rw [← Category.assoc, Abelian.coimage.fac]
    exact h1UnionLiteralShortComplex.zero)

private noncomputable def originalToLeftDescended :
    h1UnionLiteralShortComplex ⟶ h1LeftDescendedShortComplex where
  τ₁ := Abelian.coimage.π reassembly
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := by simp [h1UnionLiteralShortComplex,
    h1LeftDescendedShortComplex]
  comm₂₃ := by simp [h1UnionLiteralShortComplex,
    h1LeftDescendedShortComplex]

private noncomputable def coreToLeftDescended :
    h1CoreShortComplex ⟶ h1LeftDescendedShortComplex where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := Abelian.factorThruCoimage connecting
  comm₁₂ := by simp [h1CoreShortComplex, h1LeftDescendedShortComplex]
  comm₂₃ := by simp [h1CoreShortComplex, h1LeftDescendedShortComplex]

theorem h1CoreShortComplex_exact : h1CoreShortComplex.Exact := by
  letI : Epi originalToLeftDescended.τ₁ := by
    change Epi (Abelian.coimage.π reassembly)
    infer_instance
  letI : IsIso originalToLeftDescended.τ₂ := by
    change IsIso (𝟙 (H 1 BT))
    infer_instance
  letI : Mono originalToLeftDescended.τ₃ := by
    change Mono (𝟙 (Z ⊞ Z))
    infer_instance
  have hleft : h1LeftDescendedShortComplex.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      originalToLeftDescended).mp h1UnionLiteralShortComplex_exact
  letI : Epi coreToLeftDescended.τ₁ := by
    change Epi (𝟙 (Abelian.coimage reassembly))
    infer_instance
  letI : IsIso coreToLeftDescended.τ₂ := by
    change IsIso (𝟙 (H 1 BT))
    infer_instance
  letI : Mono coreToLeftDescended.τ₃ := by
    change Mono (Abelian.factorThruCoimage connecting)
    infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    coreToLeftDescended).mpr hleft

theorem h1CoreShortComplex_shortExact : h1CoreShortComplex.ShortExact where
  exact := h1CoreShortComplex_exact
  mono_f := by dsimp [h1CoreShortComplex]; infer_instance
  epi_g := by dsimp [h1CoreShortComplex]; infer_instance

/-- The literal degree-one pieces segment. -/
noncomputable def h1PiecesLiteralShortComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk intSignedFold reassembly (by
    change intSignedFold ≫ integerReassemblyArrow 1 circleH1GroupIsoInt = 0
    rw [← integerPiecesShortComplex_f 1 circleH1GroupIsoInt,
      ← integerPiecesShortComplex_g 1 circleH1GroupIsoInt]
    exact (integerPiecesShortComplex 1 circleH1GroupIsoInt).zero)

theorem h1PiecesLiteralShortComplex_exact : h1PiecesLiteralShortComplex.Exact := by
  apply ShortComplex.exact_of_iso ?_ integerPiecesShortComplex_H1_exact
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using (integerPiecesShortComplex_f 1 circleH1GroupIsoInt).symm)
    (by simpa using (integerPiecesShortComplex_g 1 circleH1GroupIsoInt).symm)

/-- Exactness at the pieces identifies the coimage of reassembly with the
categorical cokernel of the signed fold. -/
noncomputable def reassemblyCoimageIsoSignedFoldCokernel :
    Abelian.coimage reassembly ≅ cokernel intSignedFold := by
  change Abelian.coimage h1PiecesLiteralShortComplex.g ≅
    cokernel h1PiecesLiteralShortComplex.f
  exact (IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel h1PiecesLiteralShortComplex.f)
    (h1PiecesLiteralShortComplex_exact.isColimitCoimage)).symm

noncomputable def h1LeftIsoInt : Abelian.coimage reassembly ≅ Z :=
  reassemblyCoimageIsoSignedFoldCokernel ≪≫ integerSignedFoldCokernelIso

/-- Exactness at the overlap identifies the coimage of the connecting map
with the signed-fold kernel, hence with `ℤ`. -/
noncomputable def connectingImageIsoSignedFoldKernel :
    Abelian.image connecting ≅ kernel intSignedFold := by
  change Abelian.image (integerIntersectionLiteralShortComplex 0
    circleH0GroupIsoInt).f ≅
      kernel (integerIntersectionLiteralShortComplex 0 circleH0GroupIsoInt).g
  exact (IsLimit.conePointUniqueUpToIso
    (kernelIsKernel _)
    ((integerIntersectionLiteralShortComplex_exact 0
      circleH0GroupIsoInt).isLimitImage)).symm

noncomputable def h1RightIsoInt : Abelian.coimage connecting ≅ Z :=
  Abelian.coimageIsoImage connecting ≪≫
    connectingImageIsoSignedFoldKernel ≪≫ integerSignedFoldKernelIso

/-- The infinite cyclic additive group is projective, proved by lifting the
image of `1` through an epimorphism. -/
noncomputable instance intGroup_projective : Projective Z where
  factors f e _ := by
    obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective e).mp inferInstance (f 1)
    refine ⟨AddCommGrpCat.ofHom (zmultiplesHom _ x), ?_⟩
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext_int
    simpa using hx

noncomputable def boundaryTorusH1IsoIntBiprod : H 1 BT ≅ Z ⊞ Z := by
  letI : Projective (Abelian.coimage connecting) :=
    Projective.of_iso h1RightIsoInt.symm inferInstance
  letI : Projective h1CoreShortComplex.X₃ := by
    change Projective (Abelian.coimage connecting)
    infer_instance
  let split : H 1 BT ≅
      Abelian.coimage reassembly ⊞ Abelian.coimage connecting :=
    shortExactIsoBiprod h1CoreShortComplex_shortExact
  exact split ≪≫
    biprod.mapIso h1LeftIsoInt h1RightIsoInt

#print axioms h1CoreShortComplex_exact
#print axioms h1CoreShortComplex_shortExact
#print axioms reassemblyCoimageIsoSignedFoldCokernel
#print axioms h1RightIsoInt
#print axioms boundaryTorusH1IsoIntBiprod

end ConstructionTargets.BoundaryTorusH1ProjectiveSplitting
