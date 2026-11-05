module

public import Papers.GraphicalZonotopes.DiamondBookSmallTrees
public import Papers.GraphicalZonotopes.WeakSummandReduction

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped Pointwise

/-- The checked3-tree construction yields a full-dimensional extreme
function on every graph containing an admissible spanning3-tree. -/
theorem full_support_of_admissible_spanning_threeTree {n : ℕ} (hn : 4≤n)
    {G : SimpleGraph (Fin n)} (hG : HasAdmissibleSpanningThreeTree G) :
    ∃ z : SetFunction (Fin n),ExtremeSupermodular z ∧
      FullDimension (basePolytope z) ∧ Graphical G z := by
  obtain ⟨H,hHG,hH,hA⟩:=hG
  obtain ⟨z,hz,hi,hfour,hthree,hd,hdir,hsum⟩:=admissible_threeTree_construction hn hH hA
  have hgraph:=((isMinkowskiSummand_graphical_iff hz.1.1 hz.2.1
    (Nat.cast_nonneg (n-3))).mp hsum).1
  exact ⟨z,hz,hd,hgraph.mono_graph hHG⟩

namespace DiamondBook

theorem small_dimension_lower (k : ℕ) (hk : 1≤k) (hmax : k≤5) :
    k+3≤maximumIndecomposableDimension (graph k) := by
  obtain ⟨z,hz,hd,hgraph⟩:=full_support_of_admissible_spanning_threeTree
    (by omega : 4≤k+4) (admissible_spanning_small k hk hmax)
  have hw:=(isWeakMinkowskiSummand_graphical_iff hz.1.1 hz.2.1).mpr hgraph
  have hfinite : IsFinitePolytope (basePolytope z):=
    (show IsGeneralizedPermutahedron (basePolytope z) from ⟨z,hz.1.1,hz.2.1,rfl⟩).finitePolytope
  have hle:=dimension_le_maximum hfinite hz.minkowskiIndecomposable hw
  change Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=Fintype.card (Fin (k+4))-1 at hd
  rw [hd,Fintype.card_fin] at hle
  omega

end DiamondBook
end GraphicalZonotopes
