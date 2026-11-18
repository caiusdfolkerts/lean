module

public import ToricPower.ReconstructionCompletionMappedComparison
public import ToricPower.ReconstructionCompletionQuasicoherentExtension
public import ToricPower.ReconstructionCompletionQuasicoherentComparison
public import ToricPower.ReconstructionCompletionExactAssociation
public import ToricPower.ReconstructionCompletionAffineUnitTransport
public import ToricPower.ReconstructionCompletionTopPrecompose
public import ToricPower.ReconstructionCompletionTargetColimits
public import ToricPower.AffineRankOneSections
public import ToricPower.AffineSectionsDetection

/-! # Reconstruction on every affine direct-image complex

The rank-one calculation determines the original natural augmentation
on arbitrary coordinate modules. Exact affine detectors and the actual
natural kernel then give the comparison for every unbounded complex of
quasicoherent sheaves on the affine source.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open ToricPower.FunctorTotal


namespace ToricPower

variable (R : Type) [CommRing R]
  (X : Scheme) [X.Over (Spec (.of ℂ))] [IsIntegral X]
  [(Spec (.of R)).Over (Spec (.of ℂ))] [IsIntegral (Spec (.of R))]
  (j : Spec (.of R) ⟶ X) [IsOpenImmersion j] [IsAffineHom j] [j.IsOver (Spec (.of ℂ))]
  {C : Type} [Category.{0} C] (P : Cᵒᵖ ⥤ QCoh X)
  (invertible : ∀ c, TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (P.obj (op c)).obj)
  (Φ : (C ⥤ @ModuleCat.{0} ℂ Complex.commRing.toRing) ⥤ CochainComplex (QCoh X) ℕ) [Φ.Additive]
  [PreservesFiniteLimits Φ] [PreservesColimitsOfSize.{0,0} Φ]
  (L : QCoh X) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L.obj]
  (n : ℕ) (τ : Cellular.homDiagram ℂ P ⋙ Φ ⟶ singleCoefficient (tensorLeft L) n)
  (above : ∀ M q, n < q → IsZero ((Φ.obj M).X q))
  {I : Type*} (opens : I → X.Opens) (covering : iSup opens = ⊤)
  (affine : ∀ i, IsAffineOpen (opens i))
  (rankOne : QuasiIso (τ.app (quasicoherentAffineUnitImage j)))

local instance reconstructionAffineExtensionBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionAffineExtensionTildeAdditive :
    (reconstructionAffineTildeEquivalence R).functor.Additive :=
  (reconstructionAffineTildeEquivalence R).functor.additive_of_preserves_binary_products
local instance reconstructionAffineExtensionTildeInverseAdditive :
    (reconstructionAffineTildeEquivalence R).inverse.Additive :=
  (reconstructionAffineTildeEquivalence R).inverse.additive_of_preserves_binary_products

/-- The original comparison after the actual affine tilde and direct image. -/
def reconstructionAffineModuleComparisonMap (width : ℕ) (retained : n < width) :=
  quasicoherentTopComparisonAfterMap X
    ((reconstructionAffineTildeEquivalence R).functor ⋙ quasicoherentAffinePushforward j)
    (Cellular.homDiagram ℂ P ⋙ Φ) (tensorLeft L) n width retained τ

/-- The original comparison after the actual affine direct image. -/
def reconstructionAffineComparisonMap (width : ℕ) (retained : n < width) :=
  quasicoherentTopComparisonAfterMap X (quasicoherentAffinePushforward j)
    (Cellular.homDiagram ℂ P ⋙ Φ) (tensorLeft L) n width retained τ

include invertible above covering affine rankOne in
/-- The original top comparison on every unbounded coordinate-module
complex, after the actual affine tilde and direct image. -/
def reconstructionAffineModuleComparison_quasiIso
    (width : ℕ) (retained : n < width) (K : CochainComplex (ModuleCat.{0} R) ℤ) :=
  let A := (reconstructionAffineTildeEquivalence R).functor ⋙ quasicoherentAffinePushforward j
  let H := (reconstructionAffineTildeEquivalence R).functor ⋙
    quasicoherentOpenIntrinsicLabelHom ℂ j P
  let T := A ⋙ tensorLeft L
  let Ψ := A ⋙ (Cellular.homDiagram ℂ P ⋙ Φ)
  let α := quasicoherentPrecomposedTopAugmentation X A (Cellular.homDiagram ℂ P ⋙ Φ) (tensorLeft L) n τ
  let detectors (i : I) := quasicoherentInclusion X ⋙
    FiniteCover.schemeBaseSections ℂ X (opens i)
  letI := reconstructionPaired_preservesFiniteLimits
    (reconstructionAffineTildeEquivalence R).functor (quasicoherentAffinePushforward j)
    (Cellular.homDiagram ℂ P) Φ
    (quasicoherentOpenIntrinsicLabelHom_exact ℂ j P invertible).1
  letI := reconstructionPaired_preservesFiniteColimits
    (reconstructionAffineTildeEquivalence R).functor (quasicoherentAffinePushforward j)
    (Cellular.homDiagram ℂ P) Φ
    (quasicoherentOpenIntrinsicLabelHom_exact ℂ j P invertible).2
  letI := reconstructionTensorLeft_isEquivalence X L
  letI (i : I) : PreservesFiniteLimits (detectors i) :=
    (FiniteCover.schemeBaseSections_exact ℂ X (opens i) (affine i)).1
  letI (i : I) : PreservesFiniteColimits (detectors i) :=
    (FiniteCover.schemeBaseSections_exact ℂ X (opens i) (affine i)).2
  letI (i : I) : PreservesColimitsOfSize.{0,0} (detectors i) :=
    affineBaseSections_preservesColimits ℂ X (opens i) (affine i)
  letI (i : I) : PreservesColimitsOfSize.{0,0}
      ((detectors i).mapHomologicalComplex (.up ℕ)) :=
    ⟨by intros; infer_instance⟩
  let rank :=
    letI := rankOne
    reconstructionQuasicoherentNatTrans_quasiIso_of_iso X τ
      (reconstructionAffineTildeUnitIso R X j)
  have result := reconstructionQuasicoherentModule_topComparison_quasiIso R ℂ X Ψ T n α detectors
    (quasicoherent_isZero_of_affineSections ℂ X opens covering affine)
    (fun S h => h.map_of_exact Ψ) (fun S h => h.map_of_exact T)
    (fun i J => by
      letI := reconstructionPairedDetector_preservesColimits
        (reconstructionAffineTildeEquivalence R).functor (quasicoherentAffinePushforward j)
        (Cellular.homDiagram ℂ P) Φ ((detectors i).mapHomologicalComplex (.up ℕ))
        (quasicoherentOpenIntrinsicLabelHom_preservesColimits ℂ X P j invertible)
      infer_instance)
    (fun i J => by
      letI := reconstructionTripleTarget_preservesColimits
        (reconstructionAffineTildeEquivalence R).functor (quasicoherentAffinePushforward j)
        (tensorLeft L) (detectors i)
        (reconstructionAffineTarget_preservesColimits ℂ X j L (opens i) (affine i))
      infer_instance)
    (fun M q high => above (H.obj M) q high) rank width retained K
  (quasicoherentTopComparisonAfterMap_precompose_quasiIso_iff X A (Cellular.homDiagram ℂ P ⋙ Φ)
    (tensorLeft L) n width retained τ K).mp result

include invertible above covering affine rankOne in
/-- The same proved comparison on every unbounded affine sheaf complex. -/
def reconstructionAffineComparison_quasiIso
    (width : ℕ) (retained : n < width) (K : CochainComplex (QCoh (Spec (.of R))) ℤ) :=
  quasicoherentAffineTopComparison_quasiIso_of_equivalence R (Spec (.of R)) X
    (quasicoherentAffinePushforward j)
    (Cellular.homDiagram ℂ P ⋙ Φ) (tensorLeft L) n width retained τ
    (reconstructionAffineTildeEquivalence R)
    (reconstructionAffineModuleComparison_quasiIso R X j P invertible Φ L n τ above
      opens covering affine rankOne width retained) K

/-- The proved module comparison, evaluated as the original mapped-input top map. -/
def reconstructionAffineModuleComplex_quasiIso
    (width : ℕ) (retained : n < width) (K : CochainComplex (ModuleCat.{0} R) ℤ) :=
  (quasicoherentTopComparisonAfterMap_quasiIso_iff X
    ((reconstructionAffineTildeEquivalence R).functor ⋙ quasicoherentAffinePushforward j)
    (Cellular.homDiagram ℂ P ⋙ Φ) (tensorLeft L) n width retained τ K).mp
    (reconstructionAffineModuleComparison_quasiIso R X j P invertible Φ L n τ above
      opens covering affine rankOne width retained K)

/-- The proved affine comparison, evaluated as the original mapped-input top map. -/
def reconstructionAffineComplex_quasiIso
    (width : ℕ) (retained : n < width) (K : CochainComplex (QCoh (Spec (.of R))) ℤ) :=
  (quasicoherentAffineTopComparisonAfterMap_quasiIso_iff (Spec (.of R)) X
    (quasicoherentAffinePushforward j)
    (Cellular.homDiagram ℂ P ⋙ Φ) (tensorLeft L) n width retained τ K).mp
    (reconstructionAffineComparison_quasiIso R X j P invertible Φ L n τ above
      opens covering affine rankOne width retained K)

end ToricPower

end
