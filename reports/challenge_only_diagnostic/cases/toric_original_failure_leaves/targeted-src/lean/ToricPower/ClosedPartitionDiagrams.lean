module

public import ToricPower.ClosedPartitionScalars
public import ToricPower.ModuleDiagramDirectSum
public import ToricPower.PointClosedPullback

/-!
# Closed constant diagrams split over every actual component

A component label on the closed support is constant along all supported
incidences. This gives a literal coproduct decomposition of the entire
closed scalar diagram, including infinitely many components.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.Cellular

variable (k : Type) [Field k] {B I : Type} [Preorder B]
  (P : B → Prop) (downP : Antitone P) (label : ∀ b, P b → I)
  (compatible : ∀ {b c : B} (h : b ≤ c) (hc : P c),
    label b (downP h hc) = label c hc)

def closedComponentSupport (i : I) (b : B) : Prop :=
  MorseCoefficients.closedPartitionPredicate (P b) (label b) i

include compatible in
theorem closedComponentSupport_downward (i : I) :
    Antitone (closedComponentSupport P label i) := by
  intro b c h hc
  obtain ⟨present,equal⟩ := hc
  exact ⟨downP h present,(compatible h present).trans equal⟩

/-- Every original component carries its whole closed constant diagram. -/
def closedComponentDiagram (i : I) : B ⥤ ModuleCat.{0} k :=
  (closedConstantFunctor k (closedComponentSupport P label i)
    (closedComponentSupport_downward P downP label compatible i)).obj (ModuleCat.of k k)

/-- The pointwise unrestricted direct sum, with every face map retained. -/
def closedPartitionDiagramIso :
    ModuleDiagramSum.diagram k
      (Discrete.functor (closedComponentDiagram k P downP label compatible)) ≅
      (closedConstantFunctor k P downP).obj (ModuleCat.of k k) :=
  NatIso.ofComponents (fun b =>
    (MorseCoefficients.closedPartitionEquiv k (P b) (label b)).toModuleIso) (by
      intro b c f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (Π₀ i : I, PLift (closedComponentSupport P label i b) → k) at x
      funext hc
      change x (label c hc.down) ⟨downP f.le hc.down,compatible f.le hc.down⟩ =
        x (label b (downP f.le hc.down)) ⟨downP f.le hc.down,rfl⟩
      exact MorseCoefficients.closedPartition_component_value k (P b) (label b)
        x (downP f.le hc.down) (compatible f.le hc.down))

/-- The categorical coproduct has the same literal component coefficients. -/
def closedPartitionCoproductIso :
    colimit (Discrete.functor (closedComponentDiagram k P downP label compatible)) ≅
      (closedConstantFunctor k P downP).obj (ModuleCat.of k k) :=
  (ModuleDiagramSum.colimitIso k
    (Discrete.functor (closedComponentDiagram k P downP label compatible))).symm ≪≫
    closedPartitionDiagramIso k P downP label compatible

end ToricPower.Cellular

end
