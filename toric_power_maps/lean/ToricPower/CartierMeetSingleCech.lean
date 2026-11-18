module

public import ToricPower.CartierMeetDerivedCech
public import ToricPower.DiagramProjectiveSingle
public import ToricPower.CechMeetLinearComparison

/-!
# Actual full Čech diagrams compute derived Cartier Hom on sheaves

The projective derived model is compared before localization with the
ordinary module-valued Čech complex of every inverse Cartier twist.
Consequently the actual derived Hom diagram of an actual quasicoherent
sheaf is represented by this full Čech diagram, with its exact scalar
structure and every source-label map.
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

/-- The actual presheaf diagram of inverse Cartier twists. -/
def cartierLabelPresheafDiagram (M : QCoh X) : L ⥤ X.Opensᵒᵖ ⥤ ModuleCat k :=
  (cartierLabelTwistDiagram X P).obj M ⋙ quasicoherentInclusion X ⋙
    FiniteCover.schemeBasePresheaf k X

/-- The whole ordinary scalar-linear Čech diagram, with all actual
inverse-tensor source maps and every actual tuple. -/
def cartierLabelLinearCechDiagram (M : QCoh X) : L ⥤ CochainComplex (ModuleCat k) ℕ :=
  cartierLabelPresheafDiagram k X P M ⋙ cechComplexFunctor opens.obj

variable (meetEq : ∀ (q : ℕ) (t : Fin (q+1) → B),
    BondalThomsen.FiniteAffineCechHigherComparison.cechIntersection opens.obj q t =
      opens.obj (FiniteCech.tupleMeet t))

/-- Actual section coordinates give a natural isomorphism of full
complex-valued label diagrams, before any localization. -/
def cartierLabelCechTupleIso (M : QCoh X) :
    cartierLabelLinearCechDiagram k X P opens M ≅
      diagramOrdinaryProjectiveCoefficients k (cartierMeetSectionsDiagram k X P opens)
        (FiniteCech.tupleProjectiveResolution k) M :=
  NatIso.ofComponents
    (fun l => FiniteCech.meetLinearCechComplexIso k X opens meetEq
      ((cartierLabelPresheafDiagram k X P M).obj l))
    (fun f => FiniteCech.meetLinearCechComplexIso_naturality k X opens meetEq
      ((cartierLabelPresheafDiagram k X P M).map f))

variable [IsLocallyNoetherian X] [CompactSpace X] [X.IsSeparated]
  (chartsInf : ∀ b c, opens.obj (b ⊓ c) = opens.obj b ⊓ opens.obj c)
  (cover : iSup opens.obj = ⊤) (affine : ∀ b, IsAffineOpen (opens.obj b))

local instance cartierSingleCechDerivedQCoh : HasDerivedCategory.{1} (QCoh X) := HasDerivedCategory.standard _
local instance cartierSingleCechDerivedCharts : HasDerivedCategory.{1} (Bᵒᵖ ⥤ ModuleCat.{0} k) := HasDerivedCategory.standard _
local instance cartierSingleCechDerivedLabels : HasDerivedCategory.{1} (L ⥤ ModuleCat.{0} k) := HasDerivedCategory.standard _

/-- On every actual quasicoherent sheaf, the actual derived Hom diagram
is represented by the full ordinary Čech complex, as an object in the
derived category of entire diagrams. -/
def cartierRHomPlusSingleCechIso (M : QCoh X) :
    ((Cellular.homDiagram k (P ⋙ cartierSourcesQuasicoherent X)).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor (QCoh X) 0).obj M) ≅
    DerivedCategory.Q.obj (complexDiagramTranspose
      (cartierLabelLinearCechDiagram k X P opens M ⋙
        ComplexShape.embeddingUpNat.extendFunctor (ModuleCat k))) := by
  letI := (cartierMeetSectionsDiagram_exact k X P opens affine).1
  letI := (cartierMeetSectionsDiagram_exact k X P opens affine).2
  exact diagramProjectivePlusSingleIsoOfComparisons k
    (cartierMeetSectionsDiagram k X P opens) (FiniteCech.tupleProjectiveResolution k) M
    (cartierMeetSectionsDiagram_injective_rows k X P opens meetEq)
    (cartierHomTupleSectionsIso k X P opens chartsInf cover)
    (cartierLabelCechTupleIso k X P opens meetEq M).symm

end ToricPower
