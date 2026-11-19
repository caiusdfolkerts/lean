module

public import ToricPower.CartierOpenPushforward
public import ToricPower.FiniteDiagramProjectiveAffineDerived
public import ToricPower.AffineLocalizationLabelExact

/-!
# Unbounded Čech descent for the actual whole Cartier Hom diagram

The finite resolution of the constant chart diagram gives a concrete
model on arbitrary unbounded quasicoherent complexes. Every local row
is established by the actual open-direct-image contraction and the
actual Cartier projection isomorphism. The result is a natural
isomorphism with the genuine unbounded right-derived Hom diagram.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex TopologicalSpace

namespace ToricPower

variable (k : Type) [Field k] (X : Scheme) [X.Over (Spec (.of k))] [IsIntegral X]
  {L : Type} [Category.{0} L] (P : Lᵒᵖ ⥤ CartierSources X)
  {B : Type} [SemilatticeInf B] [Finite B] (opens : B ⥤ X.Opens)

local instance : HasDerivedCategory.{1} (QCoh X) := HasDerivedCategory.standard _
local instance : HasDerivedCategory.{1} (Bᵒᵖ ⥤ ModuleCat.{0} k) := HasDerivedCategory.standard _
local instance : HasDerivedCategory.{1} (L ⥤ ModuleCat.{0} k) := HasDerivedCategory.standard _

variable (affine : ∀ b, IsAffineOpen (opens.obj b))

/-- The finite projective model is defined on the full unbounded
derived category and retains every label incidence. -/
def cartierFiniteMeetDerived :
    DerivedCategory (QCoh X) ⥤ DerivedCategory (L ⥤ ModuleCat k) :=
  letI := (cartierMeetSectionsDiagram_exact k X P opens affine).1
  letI := (cartierMeetSectionsDiagram_exact k X P opens affine).2
  diagramProjectiveCoefficientDerived k (cartierMeetSectionsDiagram k X P opens)
    (FiniteCech.finiteTupleResolution k)

/-- The comparison uses exactly the original projective augmentation. -/
def cartierFiniteMeetDerivedUnit :
    (ordinaryDiagramProjectiveCoefficients k (cartierMeetSectionsDiagram k X P opens)
      (Z := (FiniteCech.tupleAugmented k).right)).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ cartierFiniteMeetDerived k X P opens affine :=
  letI := (cartierMeetSectionsDiagram_exact k X P opens affine).1
  letI := (cartierMeetSectionsDiagram_exact k X P opens affine).2
  diagramProjectiveCoefficientDerivedUnit k (cartierMeetSectionsDiagram k X P opens)
    (FiniteCech.finiteTupleResolution k)

variable [∀ b, IsAffineHom (opens.obj b).ι]
  [∀ b, IsAffine (opens.obj b).toScheme] [∀ b, IsIntegral (opens.obj b).toScheme]
  (chartsInf : ∀ b c, opens.obj (b ⊓ c) = opens.obj b ⊓ opens.obj c)
  (cover : iSup opens.obj = ⊤)

local instance cartierFiniteHomLocalLimits (a : B) :
    PreservesFiniteLimits (quasicoherentOpenLocalization (opens.obj a).ι ⋙
      Cellular.homDiagram k (P ⋙ cartierSourcesQuasicoherent X)) :=
  (quasicoherentOpenLocalizationLabelHom_exact k (opens.obj a).ι
    (P ⋙ cartierSourcesQuasicoherent X) (fun _ => by
      dsimp [cartierSourcesQuasicoherent, quasicoherentCartierObject]
      exact TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.isInvertible_sheaf _)).1

local instance cartierFiniteHomLocalColimits (a : B) :
    PreservesFiniteColimits (quasicoherentOpenLocalization (opens.obj a).ι ⋙
      Cellular.homDiagram k (P ⋙ cartierSourcesQuasicoherent X)) :=
  (quasicoherentOpenLocalizationLabelHom_exact k (opens.obj a).ι
    (P ⋙ cartierSourcesQuasicoherent X) (fun _ => by
      dsimp [cartierSourcesQuasicoherent, quasicoherentCartierObject]
      exact TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.isInvertible_sheaf _)).2

def cartierFiniteCoefficientsLocalLimits (a : B) :
    PreservesFiniteLimits (quasicoherentOpenLocalization (opens.obj a).ι ⋙
      ordinaryDiagramProjectiveCoefficients k (cartierMeetSectionsDiagram k X P opens)
        (Z := (FiniteCech.tupleAugmented k).right)) :=
  preservesFiniteLimits_of_natIso (Functor.isoWhiskerLeft
    (quasicoherentOpenLocalization (opens.obj a).ι)
    (cartierHomTupleSectionsIso k X P opens chartsInf cover))

def cartierFiniteCoefficientsLocalColimits (a : B) :
    PreservesFiniteColimits (quasicoherentOpenLocalization (opens.obj a).ι ⋙
      ordinaryDiagramProjectiveCoefficients k (cartierMeetSectionsDiagram k X P opens)
        (Z := (FiniteCech.tupleAugmented k).right)) :=
  preservesFiniteColimits_of_natIso (Functor.isoWhiskerLeft
    (quasicoherentOpenLocalization (opens.obj a).ι)
    (cartierHomTupleSectionsIso k X P opens chartsInf cover))

variable (meetEq : ∀ (q : ℕ) (t : Fin (q+1) → B),
    BondalThomsen.FiniteAffineCechHigherComparison.cechIntersection opens.obj q t =
      opens.obj (FiniteCech.tupleMeet t))
  (l : List B) (hl : ∀ b, b ∈ l)

include chartsInf cover meetEq hl

/-- All finite-source, affine-row and covering hypotheses are
discharged for the actual Cartier-label diagram. -/
theorem cartierFiniteMeetDerived_isRightDerivedFunctor :
    (cartierFiniteMeetDerived k X P opens affine).IsRightDerivedFunctor
      (cartierFiniteMeetDerivedUnit k X P opens affine)
      (HomologicalComplex.quasiIso (QCoh X) (.up ℤ)) := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  letI := (cartierMeetSectionsDiagram_exact k X P opens affine).1
  letI := (cartierMeetSectionsDiagram_exact k X P opens affine).2
  letI (a : B) : PreservesFiniteLimits (quasicoherentOpenLocalization (opens.obj a).ι ⋙
      ordinaryDiagramProjectiveCoefficients k (cartierMeetSectionsDiagram k X P opens)
        (Z := (FiniteCech.tupleAugmented k).right)) :=
    cartierFiniteCoefficientsLocalLimits k X P opens chartsInf cover a
  letI (a : B) : PreservesFiniteColimits (quasicoherentOpenLocalization (opens.obj a).ι ⋙
      ordinaryDiagramProjectiveCoefficients k (cartierMeetSectionsDiagram k X P opens)
        (Z := (FiniteCech.tupleAugmented k).right)) :=
    cartierFiniteCoefficientsLocalColimits k X P opens chartsInf cover a
  exact finiteDiagramProjectiveCoefficient_isRightDerivedFunctor opens.obj
    (IsOpenCover.mk cover) l hl k (cartierMeetSectionsDiagram k X P opens)
    (FiniteCech.finiteTupleResolution k) (Fintype.card B)
    (FiniteCech.finiteTupleResolution_isZero_of_card_lt k)
    (fun a M c n => cartierMeetFinite_openPushforward_rows k X opens meetEq P a M c n)

/-- The concrete finite model equals the actual unbounded right-derived
Hom diagram, naturally in all coefficients and all label arrows. -/
def cartierFiniteMeetRHomIso :
    cartierFiniteMeetDerived k X P opens affine ≅
      affineConeDerivedStage opens.obj
        (Cellular.homDiagram k (P ⋙ cartierSourcesQuasicoherent X)) l := by
  letI := cartierFiniteMeetDerived_isRightDerivedFunctor k X P opens affine
    chartsInf cover meetEq l hl
  letI := affineConeDerivedStage_isRightDerivedFunctor opens.obj
    (Cellular.homDiagram k (P ⋙ cartierSourcesQuasicoherent X)) l hl (IsOpenCover.mk cover)
  exact Functor.rightDerivedNatIso _ _ (cartierFiniteMeetDerivedUnit k X P opens affine)
    (affineRightDerivedUnit opens.obj
      (Cellular.homDiagram k (P ⋙ cartierSourcesQuasicoherent X)) l)
    (HomologicalComplex.quasiIso (QCoh X) (.up ℤ))
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (cartierHomTupleSectionsIso k X P opens chartsInf cover).symm
        (.up ℤ)) DerivedCategory.Q)

end ToricPower

end
