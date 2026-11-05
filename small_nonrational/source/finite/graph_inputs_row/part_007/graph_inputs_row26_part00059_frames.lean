module
prelude
public import GraphInputsRow26Part00059Data
public import RawFrameSupport
public import SharedFrameGroups008Checked
public import SharedFrameGroups011Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups021Checked
public import SharedFrameGroups026Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups070Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x71d38c5b32d00652b259906bc75d9ac95622ac8559aa9553aa114c524b92448d743da1bd07e8364181df4ece7563699af4d586753331968ca264331f96f8abc54e29a9464a0c4d126092a0918479233116c8ac4521de0eac6a033c1858bf45d62dd1578a6c4d425c12508f046422410e08543b81b70bd05b027812e08b83fc1e20da069016c0ac04d023010c08203c01c80dc05c024011807c03c0140070034012008002800c002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x71d38c5b2cd8467eb3ad94ac9064131e97b0bc959b2c9d5aaac555caad154ca104c3a5cd28c931490a35118089343f21b909883e41b20c4ece75d35e9acccd265a32a190cc7e5bf2b0145ca0e4fc26992288f446f22e11588a23bb1a70ce863e31417f8ba855a29913f09cc4bc249119888c4382160ef06dc2f016b09e04c022a0ff07983601a407e03a016c0ac04d02080dc052023011007803a0190078038014009002800c002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
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
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0551.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0551.count (({ width := 11, code := 0x3976f2d8db03556a2ce199b1d61ec0d79ada59aaf15ba854c492d2423c47086d0b2003e67a0ec1c136a698d11802e05a8ab14f2964d89911e234460860fb1ee3c8768ea1b4358670c91842f45b8b014a258490700cc1842d85009c128248480780d8178240440780e81c0320600a81402203c0680b0120200380400600800800 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0551
    Papers.RationalityTen.SharedFrameCatalogue.group0551_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0841.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0841.count (({ width := 11, code := 0x4af9091ae32c4e8930a611bfe7d6f8de83b0748e49c5b50638bf17aad95acaad5227b4c897924a2b44083d049e83b6750dc1b035262cc316f2d458ca89432744d49712521a4207b8ed1cc3806c0d11862c85607c0e21a83205a0b0150298520820dc180240440780e81c0320600a81402203c0680b0120200380400600800800 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0841
    Papers.RationalityTen.SharedFrameCatalogue.group0841_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0328.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0328.count (({ width := 8, code := 0xb3b1aeadabaaa8a7a4a2a1a09d9c9b9a969491908e8d8b8a87858483807f7e7d74706f6a686762605d5c5b5653514f4d4b474643403e3c3a383532302c29272624232221201d1b1a181716151411100d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0328.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0328.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0328.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0328.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record005_frame003_links_0000 record005_frame003_links_0064)
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0328
    Papers.RationalityTen.SharedFrameCatalogue.group0328_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
def record005_frame004_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0405.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0405.count (({ width := 8, code := 0xb3b1aeadabaaa8a7a4a2a1a09d9c9b9a969491908e8d8b8a87858483807f7e7d74706f6a686762605d5c5b5653514f4d4b474643403e3c3a383532302c29272624232221201d1b1a181716151411100d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0405.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0405.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0405.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record005_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0405.localPairCheck (smallEmbedding record005) (record005.maps 4)
      (record005.inverseMaps 4) record005_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record005_frame004_links_0000 record005_frame004_links_0064)
theorem record005_frame004_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 4 :=
  of_group record005 4 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0405
    Papers.RationalityTen.SharedFrameCatalogue.group0405_facts record005_frame004_indices record005_frame004_graph record005_frame004_links
def record005_frame005_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0167.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0167.count (({ width := 8, code := 0xb3b1aeadabaaa8a7a4a2a1a09d9c9b9a969491908e8d8b8a87858483807f7e7d74706f6a686762605d5c5b5653514f4d4b474643403e3c3a383532302c29272624232221201d1b1a181716151411100d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0167.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0167.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0167.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record005_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0167.localPairCheck (smallEmbedding record005) (record005.maps 5)
      (record005.inverseMaps 5) record005_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record005_frame005_links_0000 record005_frame005_links_0064)
theorem record005_frame005_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 5 :=
  of_group record005 5 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0167
    Papers.RationalityTen.SharedFrameCatalogue.group0167_facts record005_frame005_indices record005_frame005_graph record005_frame005_links
def record005_frame006_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0242.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0242.count (({ width := 9, code := 0xcc6431588c260afd7cbb5cae16eb459ac962aa5328d44a04fa7538994ba592a9248a411e7e3c9dce26e3619cca612f974b055299449e4d2411886401f0f074381a8c8602c1489c4c241188842200e86c34180b8582a14088401a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record005_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0242.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0242.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0242.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record005_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0242.localPairCheck (smallEmbedding record005) (record005.maps 6)
      (record005.inverseMaps 6) record005_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record005_frame006_links_0000 record005_frame006_links_0064)
theorem record005_frame006_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 6 :=
  of_group record005 6 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0242
    Papers.RationalityTen.SharedFrameCatalogue.group0242_facts record005_frame006_indices record005_frame006_graph record005_frame006_links
def record005_frame007_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0117.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0117.count (({ width := 9, code := 0x173b4d92c55faed66af52a6d2a91419fcf679329448e431e8e4622d11864260f007f3f1f6e76f36da0cc63af572ac542953a9649a411c8b3f9f0ec73381b0d2673095caa4a220f878381b0d066321609848200f070361a0b858261208038180a0401c0c04018080200 } : Fields).get c.val)
theorem record005_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0117.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record005) (record005.maps 7) (record005.inverseMaps 7) record005_frame007_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record005) (record005.maps 7) (record005.inverseMaps 7) record005_frame007_indices (Fin.ofNat record005.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record005_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record005) (record005.maps 7)
      (record005.inverseMaps 7) record005_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record005_frame007_links_0000 record005_frame007_links_0064)
theorem record005_frame007_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 7 :=
  of_group record005 7 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0117
    Papers.RationalityTen.SharedFrameCatalogue.group0117_facts record005_frame007_indices record005_frame007_graph record005_frame007_links
def record005_frame008_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xbde5822a79516a4a51ba64d30090e468a2b50cc80a3f49ed8f4e6aa2e815a8aae516281917c8983da1ce8de46642d615a8a084e623911488884102000fc07743ae1b90d986b433c18a0c105f02e816e0a8852827a13509704a024211908283bc1d208c03d81c00d205c02d01580aa05402180e0062024011007803a01c00c806002a014008803c01a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record005_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 8) (record005.inverseMaps 8) record005_frame008_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 8) (record005.inverseMaps 8) record005_frame008_indices (Fin.ofNat record005.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record005_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 8)
      (record005.inverseMaps 8) record005_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record005_frame008_links_0000 record005_frame008_links_0064)
theorem record005_frame008_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 8 :=
  of_group record005 8 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record005_frame008_indices record005_frame008_graph record005_frame008_links
def record005_frame009_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0550.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0550.count (({ width := 11, code := 0x3af71cdd1b83636bad1da132c640c5d832ea5c0b3d65a924ee9852fa4f4948c5172144067e4f51d63986e8db18f3025ecb315d2b25109f12924647c891001f23cc758e61a8340630c217a2e0588aa13e248478700cc1802c84e098120238460760d4178240440780e81c0320600a81402203c0680b0120200380400600800800 } : Fields).get c.val)
theorem record005_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record005) (record005.maps 9) (record005.inverseMaps 9) record005_frame009_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record005) (record005.maps 9) (record005.inverseMaps 9) record005_frame009_indices (Fin.ofNat record005.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record005_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record005) (record005.maps 9)
      (record005.inverseMaps 9) record005_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record005_frame009_links_0000 record005_frame009_links_0064)
theorem record005_frame009_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 9 :=
  of_group record005 9 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0550
    Papers.RationalityTen.SharedFrameCatalogue.group0550_facts record005_frame009_indices record005_frame009_graph record005_frame009_links
def record005_frame010_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0840.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0840.count (({ width := 11, code := 0x3ee794ed9d939d736de1b9b54680cdd93b11610be178ac9546a25422704d692d23a28430845011e93ba740e59ae34266cc317d2ee584ad9472884fc98121234458879071de3b06f8d81a8330628bd15c2804c86a0c21682a04b092114220430740cc168240440780e81c0320600a81402203c0680b0120200380400600800800 } : Fields).get c.val)
theorem record005_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record005) (record005.maps 10) (record005.inverseMaps 10) record005_frame010_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record005) (record005.maps 10) (record005.inverseMaps 10) record005_frame010_indices (Fin.ofNat record005.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record005_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record005) (record005.maps 10)
      (record005.inverseMaps 10) record005_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record005_frame010_links_0000 record005_frame010_links_0064)
theorem record005_frame010_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 10 :=
  of_group record005 10 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0840
    Papers.RationalityTen.SharedFrameCatalogue.group0840_facts record005_frame010_indices record005_frame010_graph record005_frame010_links
def record005_frame011_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0404.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0404.count (({ width := 8, code := 0xb3b1aeadabaaa8a7a4a2a1a09d9c9b9a969491908e8d8b8a87858483807f7e7d74706f6a686762605d5c5b5653514f4d4b474643403e3c3a383532302c29272624232221201d1b1a181716151411100d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0404.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0404.localPairCheck (smallEmbedding record005) (record005.maps 11) (record005.inverseMaps 11) record005_frame011_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0404.localPairCheck (smallEmbedding record005) (record005.maps 11) (record005.inverseMaps 11) record005_frame011_indices (Fin.ofNat record005.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record005_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0404.localPairCheck (smallEmbedding record005) (record005.maps 11)
      (record005.inverseMaps 11) record005_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record005_frame011_links_0000 record005_frame011_links_0064)
theorem record005_frame011_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 11 :=
  of_group record005 11 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0404
    Papers.RationalityTen.SharedFrameCatalogue.group0404_facts record005_frame011_indices record005_frame011_graph record005_frame011_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (Fin.cases (record005_frame004_supported hcells) (Fin.cases (record005_frame005_supported hcells) (Fin.cases (record005_frame006_supported hcells) (Fin.cases (record005_frame007_supported hcells) (Fin.cases (record005_frame008_supported hcells) (Fin.cases (record005_frame009_supported hcells) (Fin.cases (record005_frame010_supported hcells) (Fin.cases (record005_frame011_supported hcells) (fun j => Fin.elim0 j)))))))))))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x29cd26a2543e6b4bc9592464646e8d71362242783b022013f27d8f69e6bc5772ec1d5ba66b4ced95b0f614bad742c4578a754aa7e4f09b133a5849a91d1e2354628b1031fc3dc788e39c637a6c8cd19330e5f8bc95d2a2540a393e2624bc9311721c4207d0f21d0364658ca17c2f05c0b21562904d0950fc1ec3706d0d21782e85b0aa150260470720dc1982704a08c0e81c } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1bd8d776733331740b2a57f2a69514a2250926492f691a47d22bd13086542a2070ff07e83e39ed0f4c79533617d8b945662ab13b89bc45e2238f9878c37b1b20cc46402e81620ad0526280139098446622d110885c3fc1fc0fa07b43b41d30e186f436e19c0c7063030817e0b905c02d01550a68514270130095047822010e08103fc1f20f1075838c1b00d204201fc0e206f035817c0ba05b02a815009804701c80dc066027012808c03a01c } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x7d07af77d7737166f36e76c46bf68c68464f6446176025d45c25a65a057d56c56254c53e5325274cc49848045244e41340b3d73cc3aa3a538337835a34e32e31730a2fb2ee2e62dd2ab2a028c27e25725624b23f22521c20b2001f81cf1bf1be1b21a719219018416b15f15614213612a1141021010f00ee0e60de0d50cc0be0b607f07b06e06c06805c05a05805205104a04603803603202702502301d01c } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1af0aff54caa2d49e97b48da4391ac8663e29ed8f4e7952e59594aae51b2238f9c7b43a21990a44504273130883c4101f80f186e43661ad0cf06603041740b7059c2a214a09e84d425011908904141fc0ef074824410807f03701b00be05c02b01540a804c02380d8068027012007803a01c00c806002a012008804001e00b004802000e0040018008002000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
def record010_frame002_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1786a6450e28453c294b47e23b916e8483d41e44efe76d32e9858c1a5e02a9143ca084d924190187ec3e91ee8d406743131730a204ee26d128891c4462000fa079c3681a70c806102da1560a184902300fa075824410807f03701b00be05c02b01540a804c02380d8068027012007803a01c00c806002a012008804001e00b004802000e0040018008002000 } : Fields).get c.val)
theorem record010_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record010_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record010) (record010.maps 2)
      (record010.inverseMaps 2) record010_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record010_frame002_links_0000 record010_frame002_links_0064)
theorem record010_frame002_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 2 :=
  of_group record010 2 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record010_frame002_indices record010_frame002_graph record010_frame002_links
def record010_frame003_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x6b35e05c05ba59c53d5105094e74ab45845044843d3a438437d35c3012d42cb2a626f21c2142092001c11bb1ac19417016a16515414f13d1341301291191131070ff0f30ea0e50db0d50c90c408f08307e06d06b05e05b05505405304c04703603402702401e01d01c01901801501201101000f00b009008007004003002001000 } : Fields).get c.val)
theorem record010_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record010_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record010) (record010.maps 3)
      (record010.inverseMaps 3) record010_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record010_frame003_links_0000 record010_frame003_links_0064)
theorem record010_frame003_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 3 :=
  of_group record010 3 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record010_frame003_indices record010_frame003_graph record010_frame003_links
def record010_frame004_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x72f67d65364962b5d25a859e58054650e5075024fb4684384304103af37f37735731d2e62e02db2d52652592472241e11d71d01bc1b419017d17516914d1431351281170fc0f20e10d50c60c108b08007d06c06a05d05a05405305204a04503503302702401e01d01c01901801501201101000f00b009008007004003002001000 } : Fields).get c.val)
theorem record010_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record010_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record010) (record010.maps 4)
      (record010.inverseMaps 4) record010_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record010_frame004_links_0000 record010_frame004_links_0064)
theorem record010_frame004_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 4 :=
  of_group record010 4 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record010_frame004_indices record010_frame004_graph record010_frame004_links
def record010_frame005_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0864.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0864.count (({ width := 11, code := 0x24cc3884907a05bd677cee1d2b78680ce19932d5d4b49662b95029b533a5445a7d0f69e73c46b0d299a314590af15829651c9a12523e464828ff1e43b0708d519c3005d0af1501fc398700c61842b05309a130258440820d0190270480780e81c0320600a8120220400780b0120200380400600800800 } : Fields).get c.val)
theorem record010_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record010_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record010) (record010.maps 5)
      (record010.inverseMaps 5) record010_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record010_frame005_links_0000 record010_frame005_links_0064)
theorem record010_frame005_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 5 :=
  of_group record010 5 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0864
    Papers.RationalityTen.SharedFrameCatalogue.group0864_facts record010_frame005_indices record010_frame005_graph record010_frame005_links
def record010_frame006_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0820.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0820.count (({ width := 11, code := 0x249c3683b06203bd877eee9d4b876aed45a6b465dcb41652b64fc9812d2444407c4f61e83c66a8d01932f8544a694b2824f49611c22c4387b0f11cc3846e0d11922e4590a61401f43b0710ca18c2d0580a41442804a08a0d4198270480780e81c0320600a8120220400780b0120200380400600800800 } : Fields).get c.val)
theorem record010_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record010_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record010) (record010.maps 6)
      (record010.inverseMaps 6) record010_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record010_frame006_links_0000 record010_frame006_links_0064)
theorem record010_frame006_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 6 :=
  of_group record010 6 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0820
    Papers.RationalityTen.SharedFrameCatalogue.group0820_facts record010_frame006_indices record010_frame006_graph record010_frame006_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (Fin.cases (record010_frame002_supported hcells) (Fin.cases (record010_frame003_supported hcells) (Fin.cases (record010_frame004_supported hcells) (Fin.cases (record010_frame005_supported hcells) (Fin.cases (record010_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x5f45c35a657453f50e4f14bf49247647145944342f42a4164033f53ef3e63df3ac37a35e2f42cd2c72c22b129727d27526c26625123e2362281ef1c81c21a61a119217817015a15114c13913112911c1161080f70e90e30d80d20cd0c80c30b90b609e08306606305a05405104b04003603203102e02d02502301f01e01c01901501000d00a008007006005004001000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x7316fa6d86b067663260a5e35ab56c56554151e4f84f14cd4aa49348d48547f4414033e63803573503483373173022fb2ed2e22c22b82b42a92622382312112091f11dd1d61b61a519618b18718017216715112c1090fc0eb0e10d70ce0c50b30a909408106306005905305004803e03603203102e02d02502301f01e01c01901501000d00a008007006005004001000 } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record014_frame002_links_0000 record014_frame002_links_0064)
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
def record014_frame003_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0xaf353698cfc99b2aa47c5a853012003e3796ec9d73946f2da9b1b5769cc396d2bc4d294526a4a4808c10ea1741c820f79e53c074cd518a30a5b4b415c2a052c9e13525e4909091821e4247f0ec1ba35c660c81862f45b8ac1522543f8670c816c2a8520981001b0320620b81682504607c0f01c0320540800d0140200380600a01000800 } : Fields).get c.val)
theorem record014_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record014_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record014) (record014.maps 3)
      (record014.inverseMaps 3) record014_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record014_frame003_links_0000 record014_frame003_links_0064)
theorem record014_frame003_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 3 :=
  of_group record014 3 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record014_frame003_indices record014_frame003_graph record014_frame003_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (Fin.cases (record014_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x6f66b768d66e6586435ca5545284b249c4884734674604584523fa3b637c35e3423072ce2ae29328d28727926625625024a24423c2361f717417216e16915714a1401331131000fe0fa0f50e80de0d50cb0bf0bd09407607306806405805605505204a03e03b03a03102d02a02202102001f01c01901200e00d00b00a009007005004002001000 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
def record016_frame002_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xbfbba6b61b15aeaabba0b94a9008217f17b176f74272b7116fd69d6476075e35b556751d4f04c14b34a448c46743f42b41d40f3fb3ef39429e2932862772442252151f11c619518717816a1451351241010db0cd09607807506a06605a05805705404c04003d03c03202e02a02202102001f01c01901200e00d00b00a009007005004002001000 } : Fields).get c.val)
theorem record016_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record016_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record016) (record016.maps 2)
      (record016.inverseMaps 2) record016_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record016_frame002_links_0000 record016_frame002_links_0064)
theorem record016_frame002_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 2 :=
  of_group record016 2 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record016_frame002_indices record016_frame002_graph record016_frame002_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (Fin.cases (record016_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x5e2aa2949c97b42a2084f907b73d31e50d2255628d111c6402ed14a0a0c4e42600fc87903921c20d9067430617c0ba85b42cc14a0a204f426a12f094044c2180f6071036c13609804201e00ea06602f816c0b405802b815009804001e80b804e023011008003e01c00c806002a012007003401800b005001c00a0040018008002000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xa559b39838f57ec7ae74272b7136fd69d6095e356849246b41d40f3fd3ef34030b2c72b729f2732342252152021f11c31b51a81971871781451351030dc0cd09909608407807506605f05b05a05805705404c04003d02e02702302202001f01c01901801501200e00d00c00b00a007005004003002001000 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record017_frame002_links_0000 record017_frame002_links_0064)
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xebd6692f1541897a486a34d12e8533f59f20f6e7a43ca1a449b04461ec8e7c6c631f15b8a5050627013007e43c81b30d6869831017c0ba85982c01590a484bc25012008d044c21810407b83841b609804201e00ea06a03301880b405802b815009804001e80c805c02a011008003e01c00c806002a012007003401600a004801c00c0050020008002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3aed99abc658229dd476a134c024812128d144d21850607fb3f49f28f4a7933491740a8650726f91307d83d51ce8d9865a2fc1638ad452c27112f888841e1ff0f987783a01b30d6869833c1980c886282f416c0b2854429413d09a84a024211908904301de0d503f01ec0ea05b02d015c0ac055023010c07a023011007c03c01d00c806002a011008003801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x75c334d794b0450825f12168d344d217d08a8334081ff8fd87cb3dd1e88f206962e813708903d71cf8d9865631117f8b705942b814b8a184dc25c11107e43c81d00d986b434c19e0cc064431417c0ba85802b214409e84bc25012108d044c2180ee07383801b20d303a81a80d206603281880b605a01e80c806202e01680a804602200c806002a00e006802c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x6332d45594a664da25311d68b4442a1050468123f79f78fa67ae3ca9deced26cd32f96d4aa650126b12c88f846722d10fc8644272060fe87ca3d91b68c505ce2bf13b89b44c025112388e8462213100875838c19c0c805e42da1640ab85102620f907483781a80c603a81a80d206603281880b605a01e80c806202e01680a804602200c806002a00e006802c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record020_frame002_links_0000 record020_frame002_links_0064)
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
def record020_frame003_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xba2abca5aa0394e8f68978638247f67d77c379978477074572e70f6f96a264e5b956951b4f04c449a48547a45c44d4404204123f93eb39534030b2d82a02932862742652552462252151e21d51b51a818717816b1571451350f50e80da0cb0bd07506a06906606506205b05a03d03203102e02d02a02302201901801500e00d00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record020_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record020_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record020) (record020.maps 3)
      (record020.inverseMaps 3) record020_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record020_frame003_links_0000 record020_frame003_links_0064)
theorem record020_frame003_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 3 :=
  of_group record020 3 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record020_frame003_indices record020_frame003_graph record020_frame003_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (Fin.cases (record020_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x34f1994cb5626b0f15aea6552827a13ae9a24bf25e12d89624ada52528c933495a48d21c90848023e91e48ec4702364e9e6c9330191cb7e56729a9478a164d926b926090e47722190c48464161fa8f6879435017c0b1855e29c13509a045221810407503841b40d386182d615b0ab854028e14009d84d025a12608e846022610708003e41e00e807203701ac0d3050827011a08c03f01e40d406901700b405002000f0074032018009802c012008 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x76372d6f66d66c56b56065e456c5685305164f84f44b24a249c4884804434053df3d43c238436435734d33632d3183093022f82e12cf2c32bc2b02aa23822d2262091dd1d21c41a519018117a15711f1131060f90eb0e30cb0c50b50a206f06806005905605305104303e03b03602e02602502202101f01d01901201000e00d00a009008005004002001000 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record032_frame001_links_0000 record032_frame001_links_0064)
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (Fin.cases (record032_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
def record035_frame001_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x8ad89284e8428087e27bd7b979477876073170e6f56e46a86a167361a6015f05ea5e35b25a85a158c58557054451a5095004cd4ac4934844374354043a438b37c36e36c34233b32f32b3143102fc2802282211c51ba1ab1a319917612f1261010f20ea0e00db0c60c20b809607905604304103902602101e01601300f00d009008003001000 } : Fields).get c.val)
theorem record035_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record035_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record035) (record035.maps 1)
      (record035.inverseMaps 1) record035_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record035_frame001_links_0000 record035_frame001_links_0064)
theorem record035_frame001_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 1 :=
  of_group record035 1 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record035_frame001_indices record035_frame001_graph record035_frame001_links
def record035_frame002_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0965.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0965.count (({ width := 9, code := 0x1aed6eaf55a7d2e8f459ecee571f89c2606ed73b8d8abd5aacd5e994aa3d1687409d4e2672f94c92411d87c3a14fa7b3c9e0ef73389bcdd6cb61a8be582b938994923d1680389b8c25a2b954a44d2591c8a3d188a04c230f87032160983c1a090400c0200 } : Fields).get c.val)
theorem record035_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0965.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record035) (record035.maps 2) (record035.inverseMaps 2) record035_frame002_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record035) (record035.maps 2) (record035.inverseMaps 2) record035_frame002_indices (Fin.ofNat record035.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record035_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record035) (record035.maps 2)
      (record035.inverseMaps 2) record035_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record035_frame002_links_0000 record035_frame002_links_0064)
theorem record035_frame002_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 2 :=
  of_group record035 2 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0965
    Papers.RationalityTen.SharedFrameCatalogue.group0965_facts record035_frame002_indices record035_frame002_graph record035_frame002_links
def record035_frame003_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0963.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0963.count (({ width := 8, code := 0x8d8c89888685848382817e7d7b797877757472706f6e6c69686665636261605f5c5b5957565453514f4d4c4a49474442413e3d3b3a3938353431302e2c2b2927242322211e1d1b19171312100f0d0b09080706050403020100 } : Fields).get c.val)
theorem record035_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0963.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0963.localPairCheck (smallEmbedding record035) (record035.maps 3) (record035.inverseMaps 3) record035_frame003_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0963.localPairCheck (smallEmbedding record035) (record035.maps 3) (record035.inverseMaps 3) record035_frame003_indices (Fin.ofNat record035.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record035_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0963.localPairCheck (smallEmbedding record035) (record035.maps 3)
      (record035.inverseMaps 3) record035_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record035_frame003_links_0000 record035_frame003_links_0064)
theorem record035_frame003_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 3 :=
  of_group record035 3 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0963
    Papers.RationalityTen.SharedFrameCatalogue.group0963_facts record035_frame003_indices record035_frame003_graph record035_frame003_links
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (Fin.cases (record035_frame001_supported hcells) (Fin.cases (record035_frame002_supported hcells) (Fin.cases (record035_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x68967e6506466075c15b556f52951f5104ce4b547e46d46a45344c43242a4143ff3b93ad35e32130f3082bc2ad27626a25c24e23e22a21720c1f31e21d91d21bc1a818517717016715f15212811e1171040fc0dd0d90d40ca0c20bd0b80a609808c06c06405c05b05805204e03a03202a02802601f01c01501100e009007006002001000 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x70d6f96da6d468463561a6025fc5ac56556053152451f5185114fa4ea4dd4db4d34cc4a94a14433db39537732a32330e2f12e62df2d32ca2c328727f25722a1ec1e51c51af1a519a19518c18514a13d11d11010a0fb0eb0de0d70c30bf0ba0b50ae0a308a07106005f05805705604403a02a02402202101f01500e00d00c009006002001000 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x82d7e87ad6e46c36706295f85b555354f53951d4dd48647b46342d41740e3b93ae38736234c3413072de2d72c52be2ac28626624f1c31ba1af1a719418f17c15f15813d13512c1271141070fc0e60d80ce0ca0bd0b707c07106b06205b05004403d03903803302c02a02902301601500f00e00c00a008007006003002001 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
def record049_frame001_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x68965d5f85da5c15a15845555294ed4dd4b347e46d46a45d4284234103f03cd3b939137c3413212dd2d52ab27626a25c2552232152081f31de1c01b81b119518517717016b14e14613912811e11710d0e80e00d80d40ca0c20bd0b70b20a609408c07206c06805805705204003a03602602401f01501201100d009008006001000 } : Fields).get c.val)
theorem record049_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record049_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record049) (record049.maps 1)
      (record049.inverseMaps 1) record049_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record049_frame001_links_0000 record049_frame001_links_0064)
theorem record049_frame001_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 1 :=
  of_group record049 1 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record049_frame001_indices record049_frame001_graph record049_frame001_links
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (Fin.cases (record049_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
def record051_frame001_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x82b7e676e7667266df68567d67465a64f6245d95ba5b959f58957c55354e53451f4dc48b42841c40e4023e63be36734734133530e2de2c52bf2aa2852292112031e01d61c31b91b01a718f17416616115413e13512b1271070f40e80df0d40ce0cb0bd0b80af0a709d08607507106406204403903303102a02302201601500c00a008006003002 } : Fields).get c.val)
theorem record051_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record051_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record051) (record051.maps 1)
      (record051.inverseMaps 1) record051_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record051_frame001_links_0000 record051_frame001_links_0064)
theorem record051_frame001_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 1 :=
  of_group record051 1 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record051_frame001_indices record051_frame001_graph record051_frame001_links
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (Fin.cases (record051_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
def record052_frame001_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0x156ea7d0b9e13765d4b58f51ca2842a84afa5e0bb1704dadb3352688cd592b2163cc2d81af55e8bb963a9d50c9e93a25c4a48f114a1a424828ff1f93d46f4da1923185f4ba16b2a8538a013025849c8c0f31ca37c670c21622a4530a213e26c430690b41582a85109c1141c8250460800880c01201800800 } : Fields).get c.val)
theorem record052_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record052_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record052) (record052.maps 1)
      (record052.inverseMaps 1) record052_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record052_frame001_links_0000 record052_frame001_links_0064)
theorem record052_frame001_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) : Supported record052 1 :=
  of_group record052 1 (smallEmbedding record052) (small_cells_exact record052 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record052_frame001_indices record052_frame001_graph record052_frame001_links
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (Fin.cases (record052_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record052_frames_supported
theorem record053_frame000_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    Supported record053 0 :=
  of_identity record053 0 (by decide +kernel)
def record053_frame001_indices (c : Fin record053.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1848bfc5e62d69654ada565274d2cc92f459a1f10867d53d31dd0df86ca33a19b0b0c53728612a88fe45a2050f1471e37b1aa0cd06423021780acc526280130893c4502220e6063824a118074036c1960b6048020c0da06c02f81780b205402500d40660270130084038012008803000e0060018008002000 } : Fields).get c.val)
theorem record053_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record053.data.requiredEdges q = true := by decide +kernel
theorem record053_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record053) (record053.maps 1) (record053.inverseMaps 1) record053_frame001_indices (Fin.ofNat record053.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record053_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record053) (record053.maps 1) (record053.inverseMaps 1) record053_frame001_indices (Fin.ofNat record053.n i)) 64 74 :=
  interval_of_check _ 64 10 (by decide +kernel)
theorem record053_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record053) (record053.maps 1)
      (record053.inverseMaps 1) record053_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 74 record053_frame001_links_0000 record053_frame001_links_0064)
theorem record053_frame001_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) : Supported record053 1 :=
  of_group record053 1 (smallEmbedding record053) (small_cells_exact record053 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record053_frame001_indices record053_frame001_graph record053_frame001_links
def record053_frame002_indices (c : Fin record053.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x6055f85eb5c35b558d57f4ff4cf4ad4724574273fd3f03e33bb3ad37e3772ee2bd2992612422141f31e21d51ce1c01b81b11a519e18517b17416715f14a14212310f0de0d90be0b80ab0a008407906706605905805304e04703503302702602101c01201100c007006003002001000 } : Fields).get c.val)
theorem record053_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record053.data.requiredEdges q = true := by decide +kernel
theorem record053_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record053) (record053.maps 2) (record053.inverseMaps 2) record053_frame002_indices (Fin.ofNat record053.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record053_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record053) (record053.maps 2) (record053.inverseMaps 2) record053_frame002_indices (Fin.ofNat record053.n i)) 64 74 :=
  interval_of_check _ 64 10 (by decide +kernel)
theorem record053_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record053) (record053.maps 2)
      (record053.inverseMaps 2) record053_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 74 record053_frame002_links_0000 record053_frame002_links_0064)
theorem record053_frame002_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) : Supported record053 2 :=
  of_group record053 2 (smallEmbedding record053) (small_cells_exact record053 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record053_frame002_indices record053_frame002_graph record053_frame002_links
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (Fin.cases (record053_frame001_supported hcells) (Fin.cases (record053_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record053_frames_supported
theorem record054_frame000_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    Supported record054 0 :=
  of_identity record054 0 (by decide +kernel)
def record054_frame001_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x7056ca6946836446396236035e65cc5c45bf57956353f51450a4dc4bc4aa4984664534324043d83bc3b33ae36635032c3072fe2d32b82a82992252081e71c01b118917517112b11510a0ef0e00bf0b60a908a08907c06b05c05705204803502602101c01601301201100f00c009007006002001000 } : Fields).get c.val)
theorem record054_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record054) (record054.maps 1) (record054.inverseMaps 1) record054_frame001_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record054) (record054.maps 1) (record054.inverseMaps 1) record054_frame001_indices (Fin.ofNat record054.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record054_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record054) (record054.maps 1)
      (record054.inverseMaps 1) record054_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record054_frame001_links_0000 record054_frame001_links_0064)
theorem record054_frame001_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) : Supported record054 1 :=
  of_group record054 1 (smallEmbedding record054) (small_cells_exact record054 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record054_frame001_indices record054_frame001_graph record054_frame001_links
def record054_frame002_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x7076c068a68062c61c60a5df5c45a258b57d5315225004ca4bc49548147346543441b4043d63b539237736b3183062e32a929d2762632562481dc1b419917616d15713f13a1020f90f50dd0d20bf0bd0b308c08b07e06b05c05705204803402602101c01601301201100f00c009007006002001000 } : Fields).get c.val)
theorem record054_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record054) (record054.maps 2) (record054.inverseMaps 2) record054_frame002_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record054) (record054.maps 2) (record054.inverseMaps 2) record054_frame002_indices (Fin.ofNat record054.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record054_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record054) (record054.maps 2)
      (record054.inverseMaps 2) record054_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record054_frame002_links_0000 record054_frame002_links_0064)
theorem record054_frame002_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) : Supported record054 2 :=
  of_group record054 2 (smallEmbedding record054) (small_cells_exact record054 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record054_frame002_indices record054_frame002_graph record054_frame002_links
def record054_frame003_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2024ed66ecb6758ccc275f32d695f2aa553ca985332973493231915e8494091facf847323799ac8c4c5c52b89514a5a46521f8fc872437b18a8b7856e28e10407a83aa1b40d286202e816e09b049c24010b07f03841b60cd048023c10406d02f01640a804a01a809804201c00b004c02401100780300120070030008002000 } : Fields).get c.val)
theorem record054_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record054) (record054.maps 3) (record054.inverseMaps 3) record054_frame003_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record054) (record054.maps 3) (record054.inverseMaps 3) record054_frame003_indices (Fin.ofNat record054.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record054_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record054) (record054.maps 3)
      (record054.inverseMaps 3) record054_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record054_frame003_links_0000 record054_frame003_links_0064)
theorem record054_frame003_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) : Supported record054 3 :=
  of_group record054 3 (smallEmbedding record054) (small_cells_exact record054 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record054_frame003_indices record054_frame003_graph record054_frame003_links
def record054_frame004_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0994.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0994.count (({ width := 11, code := 0x275cd397f2ce3d4728b91061340e80b005e5bc1756e41c4b6a6aed219bb1060ebc96babb546a714ba614ae9011221a3fa7acef1cd30a5c0ad13f26645c851041c6364690c417429c510980fc1f4380610aa140258410640981081c02c04c0901101e0300480700c00800800 } : Fields).get c.val)
theorem record054_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record054) (record054.maps 4) (record054.inverseMaps 4) record054_frame004_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record054) (record054.maps 4) (record054.inverseMaps 4) record054_frame004_indices (Fin.ofNat record054.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record054_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record054) (record054.maps 4)
      (record054.inverseMaps 4) record054_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record054_frame004_links_0000 record054_frame004_links_0064)
theorem record054_frame004_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) : Supported record054 4 :=
  of_group record054 4 (smallEmbedding record054) (small_cells_exact record054 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0994
    Papers.RationalityTen.SharedFrameCatalogue.group0994_facts record054_frame004_indices record054_frame004_graph record054_frame004_links
def record054_frame005_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0924.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0924.count (({ width := 7, code := 0x26cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record054_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0924.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0924.localPairCheck (smallEmbedding record054) (record054.maps 5) (record054.inverseMaps 5) record054_frame005_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0924.localPairCheck (smallEmbedding record054) (record054.maps 5) (record054.inverseMaps 5) record054_frame005_indices (Fin.ofNat record054.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record054_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0924.localPairCheck (smallEmbedding record054) (record054.maps 5)
      (record054.inverseMaps 5) record054_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record054_frame005_links_0000 record054_frame005_links_0064)
theorem record054_frame005_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) : Supported record054 5 :=
  of_group record054 5 (smallEmbedding record054) (small_cells_exact record054 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0924
    Papers.RationalityTen.SharedFrameCatalogue.group0924_facts record054_frame005_indices record054_frame005_graph record054_frame005_links
theorem record054_frames_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    ∀ f : Fin record054.g, Supported record054 f :=
  (Fin.cases (record054_frame000_supported hcells) (Fin.cases (record054_frame001_supported hcells) (Fin.cases (record054_frame002_supported hcells) (Fin.cases (record054_frame003_supported hcells) (Fin.cases (record054_frame004_supported hcells) (Fin.cases (record054_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record054_frames_supported
theorem record055_frame000_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    Supported record055 0 :=
  of_identity record055 0 (by decide +kernel)
def record055_frame001_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0819.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0819.count (({ width := 11, code := 0x13d6694a48f11ba3243d86306df4bd878ae85cd35f696cfd90315614bd9722ca574ac138a6947a838f99e03886dcd61a732e638c217b2e855caa1422624948c8ec1c836c698c01642704b08b0e019c2e8580ae1382484407e0c0138250480840e0120220300480700c00800800 } : Fields).get c.val)
theorem record055_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 64 79 :=
  interval_of_check _ 64 15 (by decide +kernel)
theorem record055_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record055) (record055.maps 1)
      (record055.inverseMaps 1) record055_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 79 record055_frame001_links_0000 record055_frame001_links_0064)
theorem record055_frame001_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 1 :=
  of_group record055 1 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0819
    Papers.RationalityTen.SharedFrameCatalogue.group0819_facts record055_frame001_indices record055_frame001_graph record055_frame001_links
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (Fin.cases (record055_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record055_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059
