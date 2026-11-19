module

public import ToricPower.CartierHomSectionsDiagram

/-! # The actual Hom-section comparison in the explicit tensor-diagram interface -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ToricPower

universe u
variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsIntegral X]
  {C : Type u} [Category.{u} C] (P : Cᵒᵖ ⥤ CartierSources X)

/-- This is the same original comparison, with the flip and the
section postcomposition made explicit before geometric specialization. -/
def cartierHomTensorSectionsDiagramIso :
    Cellular.homDiagram k (P ⋙ cartierSourcesQuasicoherent X) ≅
      (P.rightOp ⋙ cartierSourcesQuasicoherentInverseTensor X).flip ⋙
        (Functor.whiskeringRight C (QCoh X) (ModuleCat.{u} k)).obj
          (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤) :=
  cartierHomSectionsDiagramIso k X P

end ToricPower

end
