module

public import ToricPower.CartierFiniteMeetDerived
public import ToricPower.DiagramProjectiveLinear
public import ToricPower.QuasicoherentCartierLinear
public import ToricPower.CechFunctorLinear

/-!
# Actual scalar linearity of Cartier finite Čech descent

This uses the specified base-field action on actual sheaf morphisms and
sections. The resulting full diagram functor, including all Cartier
source incidences, is linear on arbitrary unbounded derived objects.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower

variable (k : Type) [Field k] (X : Scheme) [X.Over (Spec (.of k))]
  {B : Type} [SemilatticeInf B] [Finite B] (opens : B ⥤ X.Opens)

instance meetChartSectionsFunctor_linear :
    (FiniteCech.meetChartSectionsFunctor k X opens).Linear k := by
  unfold FiniteCech.meetChartSectionsFunctor
  infer_instance

instance quasicoherentMeetSections_linear :
    (FiniteCech.quasicoherentMeetSections k X opens).Linear k := by
  unfold FiniteCech.quasicoherentMeetSections
  infer_instance

variable [IsIntegral X] {L : Type} [Category.{0} L] (P : Lᵒᵖ ⥤ CartierSources X)

instance cartierMeetSectionsDiagram_linear :
    (cartierMeetSectionsDiagram k X P opens).Linear k where
  map_smul f r := by
    apply NatTrans.ext
    funext l
    exact ((quasicoherentCartierTensorEquivalence
      (-(cartierSourceDivisor X ((P.rightOp.obj l).unop)))).functor ⋙
        FiniteCech.quasicoherentMeetSections k X opens).map_smul r f

local instance : HasDerivedCategory.{1} (QCoh X) := HasDerivedCategory.standard _
local instance : HasDerivedCategory.{1} (Bᵒᵖ ⥤ ModuleCat.{0} k) := HasDerivedCategory.standard _
local instance : HasDerivedCategory.{1} (L ⥤ ModuleCat.{0} k) := HasDerivedCategory.standard _

instance cartierFiniteMeetDerived_linear (affine : ∀ b, IsAffineOpen (opens.obj b)) :
    (cartierFiniteMeetDerived k X P opens affine).Linear k := by
  unfold cartierFiniteMeetDerived
  infer_instance

end ToricPower

end
