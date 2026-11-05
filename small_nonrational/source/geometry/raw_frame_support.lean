module
prelude
public import SharedGraphFramePairs
public import RawFrameSupportCore
public import SharedGraphCellPool
public import FullSix0FacetUniverse

@[expose] public section

/-!
The raw growth checker uses only a frame's forward cell map. A map may be
justified either as the identity or by a complete geometric relabeling check.
The later geometric assembly turns each of these alternatives into a genuine
frame with exactly the recorded forward map.
-/

namespace Papers.RationalityTen.RawFrameSupport

open ConcreteGrowth PackedGraphCertificate RawGraphSemanticCertificate
open SharedGraphFramePairs SharedGraphCellPool

def smallEmbedding (D : RawData) (c : Fin D.n) : Fin 44310 :=
  Fin.castLE (by decide) (embedding D c : Fin 6510)

theorem small_cells (c : Fin 6510) :
    FacetUniverses.FullSix0.cells (Fin.castLE (by decide) c) =
      FacetUniverses.FullSmall.cells c := by
  simp only [FacetUniverses.FullSix0.cells, Fin.coe_castLE, c.isLt, dite_true]

theorem small_cells_exact (D : RawData)
    (h : ∀ c, D.data.cells c = FacetUniverses.FullSmall.cells (embedding D c))
    (c : Fin D.n) :
    D.data.cells c = FacetUniverses.FullSix0.cells (smallEmbedding D c) := by
  rw [smallEmbedding, small_cells]
  exact h c

theorem of_group (D : RawData) (f : Fin D.g)
    (embedding : Fin D.n → Fin 44310)
    (hcells : ∀ c, D.data.cells c = FacetUniverses.FullSix0.cells (embedding c))
    (G : Group) (hG : G.Facts FacetUniverses.FullSix0.cells)
    (indices : Fin D.n → Fin G.count)
    (hgraph : ∀ q, G.graphBitCheck D.data.requiredEdges q = true)
    (hlinks : ∀ c, G.localPairCheck embedding (D.maps f) (D.inverseMaps f)
      indices c = true) : Supported D f := by
  exact Or.inr ⟨G.vertexCode, G.inverseVertexCode, D.inverseMaps f,
    Group.local_frameFacts _ _ embedding hcells G hG _ _ _ indices hgraph hlinks⟩

#print axioms small_cells_exact
#print axioms of_group

end Papers.RationalityTen.RawFrameSupport
