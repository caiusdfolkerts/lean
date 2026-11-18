module

public import ToricPower.SchemePushforwardBaseSections
public import ToricPower.QuasicoherentOpenAdjunction

/-! # Scalar-linear section diagrams on invariant opens -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace ToricPower

universe u

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  (f : X ⟶ X) [f.IsOver (Spec (.of k))]
  {B : Type u} [SmallCategory B] (opens : B ⥤ X.Opensᵒᵖ)
  (fixed : ∀ b, f ⁻¹ᵁ (opens.obj b).unop = (opens.obj b).unop)

def fixedChartPreimageIso : opens ⋙ (Opens.map f.base).op ≅ opens :=
  NatIso.ofComponents (fun b => eqToIso (congrArg op (fixed b)))
    (fun _ => Subsingleton.elim _ _)

/-- The same whole chart-section diagram computes direct image when
the preimage of every displayed open is itself. -/
def fixedChartBaseSectionsIso :
    Scheme.Modules.pushforward f ⋙ FiniteCover.schemeBasePresheaf k X ⋙
        (Functor.whiskeringLeft B X.Opensᵒᵖ (ModuleCat.{u} k)).obj opens ≅
      FiniteCover.schemeBasePresheaf k X ⋙
        (Functor.whiskeringLeft B X.Opensᵒᵖ (ModuleCat.{u} k)).obj opens :=
  pushforwardChartBaseSectionsIso k f opens ≪≫
    Functor.isoWhiskerLeft (FiniteCover.schemeBasePresheaf k X)
      ((Functor.whiskeringLeft B X.Opensᵒᵖ (ModuleCat.{u} k)).mapIso
        (fixedChartPreimageIso X f opens fixed))

/-- The actual quasicoherent direct image has the same section diagram. -/
def quasicoherentFixedChartSectionsIso [IsAffineHom f] :
    quasicoherentAffinePushforward f ⋙ quasicoherentInclusion X ⋙
        FiniteCover.schemeBasePresheaf k X ⋙
        (Functor.whiskeringLeft B X.Opensᵒᵖ (ModuleCat.{u} k)).obj opens ≅
      quasicoherentInclusion X ⋙ FiniteCover.schemeBasePresheaf k X ⋙
        (Functor.whiskeringLeft B X.Opensᵒᵖ (ModuleCat.{u} k)).obj opens :=
  Functor.isoWhiskerLeft (quasicoherentInclusion X)
    (fixedChartBaseSectionsIso k X f opens fixed)

end ToricPower

end
