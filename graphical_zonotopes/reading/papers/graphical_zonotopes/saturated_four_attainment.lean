module

public import Papers.GraphicalZonotopes.SaturatedFourBlocks

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule.SaturatedFour
open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem circuit_card : Fintype.card (ScopedAnchorIndex anchors rank)=14 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem neighbor_count : ∀ a : Fin 4,
    (univ.filter (fun j : ScopedAnchorIndex anchors rank => a∈scopedAnchorScope anchors rank j)).card=12 := by
  decide

open scoped Classical

/-- The exceptional saturated four-hub circuit has six all-hub modules,
eight triple modules, and exactly twelve active spokes at each hub. -/
theorem spoke_attainment :
    ∃ f : SetFunction (Fin 4⊕Fin 14),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook 4 14) f ∧ FullDimension (basePolytope f) ∧
      LatticePolytope (basePolytope f) ∧
      ∀ a : Fin 4,(univ.filter (fun j : Fin 14 =>
        ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr j))).card=12 := by
  let a₀ : anchors := ⟨2,by simp [anchors]⟩
  obtain ⟨f,hn,hi,he,hG,hd,hl,hcount⟩ := scoped_book_of_anchor_circuit
    anchors 1 (fun a => thresholdStar a.1) (fun a => by simp)
    (fun _ => 1) 1 rank block (by decide)
    (fun a => thresholdStar_boolean a.1)
    (fun a i => thresholdStar_essential (by decide) a.1 i) a₀
    (fun _ => by norm_num) scale_rigidity circuit_card
  exact ⟨f,hn,hi,he,hG,hd,hl,fun a => (hcount a).trans (neighbor_count a)⟩

end GraphicalZonotopes.BooleanModule.SaturatedFour
