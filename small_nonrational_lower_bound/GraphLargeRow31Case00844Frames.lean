module
prelude
public import GraphLargeRow31Case00844Data
public import RawFrameSupport

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphLargeRow31Case00844
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool RawGraphSemanticCertificate RawFrameSupport FiniteChecks

theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 0 := by
  exact of_identity record000 0 (by decide +kernel)

theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record000_frames_supported
end Papers.RationalityTen.CompactReplay.GraphLargeRow31Case00844
