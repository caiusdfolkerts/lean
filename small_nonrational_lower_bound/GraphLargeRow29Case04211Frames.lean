module
prelude
public import GraphLargeRow29Case04211Data
public import RawFrameSupport

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphLargeRow29Case04211
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool RawGraphSemanticCertificate RawFrameSupport FiniteChecks

theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 0 := by
  exact of_identity record000 0 (by decide +kernel)

theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 := by
  apply Or.inr
  refine ⟨record000.vertexCode 1, record000.inverseVertexCode 1, record000.inverseMaps 1, ?_⟩
  apply frameFacts_of_interval record000.data.cells record000.data.requiredEdges
    (record000.vertexCode 1) (record000.inverseVertexCode 1) (record000.maps 1) (record000.inverseMaps 1)
  · decide +kernel
  · exact interval_of_check _ 0 114 (by decide +kernel)

theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
end Papers.RationalityTen.CompactReplay.GraphLargeRow29Case04211
