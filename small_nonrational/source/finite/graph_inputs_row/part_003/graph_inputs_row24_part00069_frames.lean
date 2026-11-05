module
prelude
public import GraphInputsRow24Part00069Data
public import RawFrameSupport
public import SharedFrameGroups116Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00069
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x18bab0455c29a133094c47e228513088c36c1ac4cdc62a2c19570a324d525c92408f846a2150eec75036618b0b1455426d116087041c1fd0f8879038e18a0a484e425611a08704041d00ca04982380fc07003081600aa054028812008c04401c00cc052024010007c03a01c00c0050024011007002c0100070028008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record003_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00069
