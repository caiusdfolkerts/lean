module

public import ToricPower.CartierHomSectionsDiagram

/-! # Actual Hom diagrams under source isomorphisms and linear adjunctions -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe u v w

variable (k : Type u) [CommRing k] {L : Type u} [Category.{u} L]
  {A : Type v} [Category.{u} A] [Preadditive A] [Linear k A]
  {B : Type w} [Category.{u} B] [Preadditive B] [Linear k B]

/-- A genuine source isomorphism acts contravariantly on the whole
Hom diagram, including every target morphism. -/
def homDiagramPrecomposeIso {P Q : Lᵒᵖ ⥤ A} (e : P ≅ Q) :
    homDiagram k P ≅ homDiagram k Q where
  hom := homDiagramPrecompose k e.inv
  inv := homDiagramPrecompose k e.hom
  hom_inv_id := by
    rw [← homDiagramPrecompose_comp, e.hom_inv_id, homDiagramPrecompose_id]
  inv_hom_id := by
    rw [← homDiagramPrecompose_comp, e.inv_hom_id, homDiagramPrecompose_id]

/-- The actual linear adjunction identifies complete Hom diagrams,
naturally in labels and arbitrary target objects. -/
def homDiagramAdjunctionIso (P : Lᵒᵖ ⥤ A)
    {F : A ⥤ B} {G : B ⥤ A} [G.Additive] [G.Linear k] (adj : F ⊣ G) :
    homDiagram k (P ⋙ F) ≅ G ⋙ homDiagram k P :=
  NatIso.ofComponents (fun M => NatIso.ofComponents
    (fun c => (adjunctionHomLinearEquiv k adj (P.obj (op c)) M).toModuleIso) (by
      intro c d f
      ext g
      exact adj.homEquiv_naturality_left (P.map f.op) g)) (by
        intro M N f
        ext c g
        exact adj.homEquiv_naturality_right g f)

end ToricPower.Cellular

end
