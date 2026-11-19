module

public import ToricPower.CartierHomSectionsDiagram

/-! # Contravariant section coordinates of covariant Cartier labels

This is the opposite-label form of the actual Cartier Hom–section
adjunction. It retains every source map and every quasicoherent target
map over the base field.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

variable (k : Type) [Field k] (X : Scheme) [X.Over (Spec (.of k))] [IsIntegral X]
  {C : Type} [Category.{0} C] (P : C ⥤ CartierSources X)

local notation "Q" => P ⋙ cartierSourcesQuasicoherent X
local notation "Γ" => quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤

def cartierCovariantHomFunctor : QCoh X ⥤ Cᵒᵖ ⥤ ModuleCat k :=
  linearYoneda k (QCoh X) ⋙
    (Functor.whiskeringLeft Cᵒᵖ (QCoh X)ᵒᵖ (ModuleCat k)).obj (Q).op

def cartierCovariantSectionsFunctor : QCoh X ⥤ Cᵒᵖ ⥤ ModuleCat k :=
  (P.op ⋙ cartierSourcesQuasicoherentInverseTensor X ⋙
    (Functor.whiskeringRight (QCoh X) (QCoh X) (ModuleCat k)).obj Γ).flip

def cartierCovariantHomSectionsIso :
    cartierCovariantHomFunctor k X P ≅ cartierCovariantSectionsFunctor k X P :=
  NatIso.ofComponents (fun M => NatIso.ofComponents (fun c =>
    ((quasicoherentUnderlyingHomLinearEquiv k X
      ((cartierSourcesQuasicoherent X).obj (P.obj c.unop)) M).trans
        (cartierHomSectionsLinearEquiv k X
          (cartierSourceDivisor X (P.obj c.unop)) M.obj)).toModuleIso)
    (by
      intro c d f
      ext g
      exact cartierHomSectionsLinearEquiv_source k X
        (P.map f.unop).hom M.obj g.hom))
    (by
      intro M N f
      apply NatTrans.ext
      funext c
      ext g
      exact cartierHomSectionsLinearEquiv_coefficient k X
        (cartierSourceDivisor X (P.obj c.unop)) f.hom g.hom)

end ToricPower

end

