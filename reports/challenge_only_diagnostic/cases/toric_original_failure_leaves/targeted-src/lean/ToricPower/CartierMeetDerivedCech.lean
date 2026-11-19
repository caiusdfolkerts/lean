module

public import ToricPower.DiagramProjectiveCechDerived
public import ToricPower.CechMeetGlobalSections
public import ToricPower.CartierHomSectionsDiagram
public import ToricPower.RightDerivedPlusNatIso
public import ToricPower.BifunctorPostcomposeIso

/-!
# Actual derived Čech descent for complete Cartier-label diagrams

The actual inverse Cartier tensor functors, including their adjunction
mates on every source arrow, are restricted to the actual affine charts.
Their exact section functors produce a full diagram-valued projective
Čech model. Actual quasicoherent injectives have exact augmented rows.
Together with sheaf gluing and Cartier tensor adjunction this identifies
the model with the actual bounded-below derived Hom diagram.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open CochainComplex

namespace ToricPower

variable (k : Type) [Field k] (X : Scheme) [X.Over (Spec (.of k))] [IsIntegral X]
  {L : Type} [Category.{0} L] (P : Lᵒᵖ ⥤ CartierSources X)
  {B : Type} [SemilatticeInf B] [Finite B] (opens : B ⥤ X.Opens)

/-- The actual full diagram of inverse Cartier twists of a coefficient sheaf. -/
def cartierLabelTwistDiagram : QCoh X ⥤ L ⥤ QCoh X :=
  (P.rightOp ⋙ cartierSourcesQuasicoherentInverseTensor X).flip

/-- Actual chart sections for the complete diagram of actual inverse twists. -/
def cartierMeetSectionsDiagram : QCoh X ⥤ L ⥤ Bᵒᵖ ⥤ ModuleCat k :=
  cartierLabelTwistDiagram X P ⋙
    (Functor.whiskeringRight L (QCoh X) (Bᵒᵖ ⥤ ModuleCat k)).obj
      (FiniteCech.quasicoherentMeetSections k X opens)

instance cartierMeetSectionsDiagram_additive : (cartierMeetSectionsDiagram k X P opens).Additive where
  map_add {M N} {f g} := by
    apply NatTrans.ext
    funext l
    exact ((quasicoherentCartierTensorEquivalence
      (-(cartierSourceDivisor X ((P.rightOp.obj l).unop)))).functor ⋙
        FiniteCech.quasicoherentMeetSections k X opens).map_add (f := f) (g := g)

/-- Evaluation is exactly inverse Cartier tensor followed by actual
chart sections. -/
theorem cartierMeetSectionsDiagram_evaluation (l : L) :
    cartierMeetSectionsDiagram k X P opens ⋙ (evaluation L _).obj l =
      (quasicoherentCartierTensorEquivalence
        (-(cartierSourceDivisor X ((P.rightOp.obj l).unop)))).functor ⋙
          FiniteCech.quasicoherentMeetSections k X opens := rfl

/-- Exactness follows from actual inverse line tensor equivalences and
actual affine section functors, at every label and every chart. -/
theorem cartierMeetSectionsDiagram_exact (affine : ∀ b, IsAffineOpen (opens.obj b)) :
    PreservesFiniteLimits (cartierMeetSectionsDiagram k X P opens) ∧
      PreservesFiniteColimits (cartierMeetSectionsDiagram k X P opens) := by
  letI := (FiniteCech.quasicoherentMeetSections_exact k X opens affine).1
  letI := (FiniteCech.quasicoherentMeetSections_exact k X opens affine).2
  constructor
  · apply preservesFiniteLimits_of_evaluation
    intro l
    rw [cartierMeetSectionsDiagram_evaluation]
    infer_instance
  · apply preservesFiniteColimits_of_evaluation
    intro l
    rw [cartierMeetSectionsDiagram_evaluation]
    infer_instance

variable (chartsInf : ∀ b c, opens.obj (b ⊓ c) = opens.obj b ⊓ opens.obj c)
  (cover : iSup opens.obj = ⊤)

/-- Sheaf gluing identifies actual global sections with the actual
constant-chart Hom functor, naturally in every quasicoherent coefficient. -/
def quasicoherentGlobalTupleSectionsIso :
    quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤ ≅
      ordinaryProjectiveCoefficients k (FiniteCech.quasicoherentMeetSections k X opens)
        (Z := (FiniteCech.tupleAugmented k).right) :=
  NatIso.ofComponents
    (fun M => FiniteCech.globalTupleSectionsIso k X opens chartsInf cover M.obj)
    (fun f => FiniteCech.globalTupleSectionsIso_naturality k X opens chartsInf cover f.hom)

/-- The ordinary full Hom diagram is the full constant-chart Hom
diagram of inverse tensors, with all source and coefficient maps. -/
def cartierHomTupleSectionsIso :
    Cellular.homDiagram k (P ⋙ cartierSourcesQuasicoherent X) ≅
      ordinaryDiagramProjectiveCoefficients k (cartierMeetSectionsDiagram k X P opens)
        (Z := (FiniteCech.tupleAugmented k).right) :=
  cartierHomSectionsDiagramIso k X P ≪≫
    flippedCompositePostcomposeIso
      (P.rightOp ⋙ cartierSourcesQuasicoherentInverseTensor X)
      (quasicoherentGlobalTupleSectionsIso k X opens chartsInf cover)

variable [IsLocallyNoetherian X] [CompactSpace X] [X.IsSeparated]
  (meetEq : ∀ (q : ℕ) (t : Fin (q+1) → B),
    BondalThomsen.FiniteAffineCechHigherComparison.cechIntersection opens.obj q t =
      opens.obj (FiniteCech.tupleMeet t))

include meetEq in
/-- Every actual injective coefficient has exact positive Čech rows,
after every actual inverse Cartier twist. -/
theorem cartierMeetSectionsDiagram_injective_rows
    (J : QCoh X) (hJ : Injective J) (l : L) (n : ℕ) :
    (projectiveCoefficientComplex k (FiniteCech.tupleProjectiveResolution k)
      (((cartierMeetSectionsDiagram k X P opens).obj J).obj l)).ExactAt (n+1) := by
  let E := quasicoherentCartierTensorEquivalence
    (-(cartierSourceDivisor X ((P.rightOp.obj l).unop)))
  letI : Injective (E.functor.obj J) := (E.map_injective_iff J).mpr hJ
  exact FiniteCech.meetTupleCoefficient_exactAt_positive k X opens meetEq (E.functor.obj J).obj n

local instance : HasDerivedCategory.{1} (QCoh X) := HasDerivedCategory.standard _
local instance : HasDerivedCategory.{1} (Bᵒᵖ ⥤ ModuleCat.{0} k) := HasDerivedCategory.standard _
local instance : HasDerivedCategory.{1} (L ⥤ ModuleCat.{0} k) := HasDerivedCategory.standard _

variable (affine : ∀ b, IsAffineOpen (opens.obj b))

/-- The actual all-degree projective Čech model of the full Cartier-source diagram. -/
def cartierMeetDerived : DerivedCategory (QCoh X) ⥤ DerivedCategory (L ⥤ ModuleCat k) :=
  letI := (cartierMeetSectionsDiagram_exact k X P opens affine).1
  letI := (cartierMeetSectionsDiagram_exact k X P opens affine).2
  diagramProjectiveCoefficientDerived k (cartierMeetSectionsDiagram k X P opens)
    (FiniteCech.tupleProjectiveResolution k)

/-- A genuine natural isomorphism on the whole bounded-below derived
category, valued in the derived category of full incidence diagrams.
The proof retains every actual source arrow and coefficient morphism. -/
def cartierMeetDerivedPlusIso :
    DerivedCategory.Plus.ι ⋙ cartierMeetDerived k X P opens affine ≅
      (Cellular.homDiagram k (P ⋙ cartierSourcesQuasicoherent X)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι := by
  letI := (cartierMeetSectionsDiagram_exact k X P opens affine).1
  letI := (cartierMeetSectionsDiagram_exact k X P opens affine).2
  exact diagramProjectiveCoefficientPlusNatIso k (cartierMeetSectionsDiagram k X P opens)
      (FiniteCech.tupleProjectiveResolution k)
      (cartierMeetSectionsDiagram_injective_rows k X P opens meetEq) ≪≫
    Functor.isoWhiskerRight
      (rightDerivedPlusNatIso (cartierHomTupleSectionsIso k X P opens chartsInf cover).symm)
        DerivedCategory.Plus.ι

end ToricPower
