module
prelude
public import GraphInputsRow19Part00037Data
public import RawFrameSupport
public import SharedFrameGroups010Checked
public import SharedFrameGroups015Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups025Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups114Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xd4156e25bd26092248da384e9c6442f31754b8653d28093d49c449a23b919c8ac43f2170f7c7a63771b30d5059c29214309cc4562080fc079c3a01bf0b805902ac14f0a4050427413308504101de0d102f016c0b005702b010c070037013008c04001f00f004401c00b005002400c005002000c002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 73 :=
  interval_of_check _ 64 9 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 73 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1aaed506a4b461a0ab825b7ad715b0a16501a7c12d88ef47423851b48d3466231d1808b9453a2891368923839990b6450f25d12b494c4a024b123c91448423e91dc8de46b1eb0a644f426b1308920470218107080036c1970c405f82ca15509a84ac23a0f907803a41c40dc06a01b40d405e02d80e006e03201480a004600e00580280120070028010006001 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb7bb6fb67b19af6a23a17a109b292091390b8988138037f87ed7d77c37b97a278d75474572e70f6585e65774f649c48547a4704544454404334204123f93f33a52ad29328627b26125122e2252151cd1b51a819d1831741511451351080f50e80da0cf0bd06d06a05e05b03803703202902802300e00b00a009007005004003001 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb19a0f9098697f87d77c376174572e70f66e66165960858c57e57751c4ef4b64a749c49348547a4264204123f93a430e2ad2932862772632532312252151cd1b51a819516b1541451351151060f50e80da0bd06a06106005b03503202a02902802602301401300e00b00a009007005004003002001 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1684b2d58baa253228d6433a1150667cb3dd1e88c1c5f92f195548ba3a21998c445fe29714309b847223211587e83c61c90e106ec3681ad0d3067432c18f0be05d42a414409e84d424211908984301fc0ee07383801a606d03501840c005b01a80c80520280118054028013008803801800b005002400e005002000c004001 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xa21a15a0f9b29098667f87d77c374572e70f66e6616596085774f349c48547a4204123f93bd3ae3a434130a2c72b72ad2a12932862732632532252151cd1b51a819716b1561451351150f50e80da0bd06d06a06106005b03503202902802301501401301100e00c00b00a009007005004003002001 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record004_frame002_links_0000 record004_frame002_links_0064)
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb67a1092091390b8987f87d77c37a278d74572e70f6585e458c57e57751c4ef49c48547a4544454404204123f93f33c03b13a53412ad2932862762612512332252151e21d51cd1c41b51a81941831741451350f50e80da0cf0bd06a05e05b03803703202a02902802602301100e00b00a009007006005004003001 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xd3e56ca6bd3509a14b8257526292348e24412128fa47923ad1c07512f19748b8053d28192688ee46722090c08224021f88dd06c63511670a504562080fc07483821a20c986082ae1500a48508276134095849023a118087842c20a0fc07b83c01d00e206e03601a008d03500c8054029014009804602000f807803801500a004c02200e0058028012007 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0x92091390b86884f83b8138037f87ed7d77c375b74572e70f66e6616595e35d55c958c57e5774f04e04d24c44b64a749c49348547a42e4204123f93c03b13a530d2fb2eb2c72b72ad2a12932862342252151e21d51cd1c41b51a81941831741571451351121020f50e80da0bd06a05b03202a02902802302200e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0x315c470db72d3b2abbadeb3abeaba9e869fe789c64f932498a6238761283e0c791da741ca715c26fdbb6ddb36498b6117d5c96e5a9424e932491214791a459123d8f13b0df36cd734ccf32cc42f0b42a4a226c8c21c821f4781b04c10c2f0a8290a0230880e0300b0280901c060140400c01 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x98097796d8f38e68d789488987e7e17d07c079c7937837727637536f06de6cb6b061a61360a58e58157153f53752d4ad49f4914764704634554474393e93db3ca3b337936d3602d82cc2bd2ac2a029628627526725a2472372262091fa1e91cc1c21ba1ae1a019118317116315413712b11c0fd0f10e60d90cc0b206805903202301501401300e00d00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xa21a15a0f98396d95e91e91190a86584c8388138037f87ed7d77c375b74572e70f66e6616595e35d55c958f5815784f24e24d44b64a749c49348547a42e4204123f93bd3ae3a430b2f92e92d82c72b72ad2a12932862732632532342252151f11e21d51cd1c41b51a81961851761571451351141020f50e80da0bd06a05b03202301501401300e00d00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0x34fd3349ca724c7f14c430cb66d0b1ebbadeb3abeaba9e869fe789c64f932498a623876138420d799dc749c5709bf6edb76cd9262d845f5715b569501384c12a491214791a4591243507404f63c4ec394df36cd734ccf32cc52f4b52a4a226c8e21c821f4781b04c10c2f08c15050130380d0300b0280901c060140400c01 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
def record008_frame004_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xb42596ac5d49ca39512a6e534a99446aa30915c88b43ca19d0aa8454199f70f967ba3d11838bf25e328d14149e2485238918074238e1bd0d5c68a3331908c445fe2a814b8a184dc23911908ac3c81dd0eb07403921c20dd86d035a1a60ce865831e1830be05d42cc1600ac854829614409e84d025a12608d044c2180fd07a83b81ce0e006981a80b60320118054028013007003401800b005002400e0060028010006001 } : Fields).get c.val)
theorem record008_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record008_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 4)
      (record008.inverseMaps 4) record008_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record008_frame004_links_0000 record008_frame004_links_0064)
theorem record008_frame004_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 4 :=
  of_group record008 4 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record008_frame004_indices record008_frame004_graph record008_frame004_links
def record008_frame005_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xb7f5b62d6553ca8a53ca84d4009ed499247921a8ef47423851b48d346622a514489b4491ca8e3270a3301934c745d52e216d4a164f827293209824ba25992b494c48323e91dc8de4031f50f4c6062ef16c8b1c5722a914c8a284f426b12c892847421d10708003c61d60e306d834e1970c405d82ce15709d04ac23a10007b83c01d20e206a01a80b60320118054028013007003401800b005002400e0060028010006001 } : Fields).get c.val)
theorem record008_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record008_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record008) (record008.maps 5)
      (record008.inverseMaps 5) record008_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record008_frame005_links_0000 record008_frame005_links_0064)
theorem record008_frame005_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 5 :=
  of_group record008 5 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record008_frame005_indices record008_frame005_graph record008_frame005_links
def record008_frame006_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x7607517466d46c86bd6716606535d35c55b759858f58757f57756f54553d53552b4774664593d93cb3bd3723633582e62da2cf2b52ac2a429c29428c26225a25224822021a2131d01c91c21bd1b71b01a81a119919018617f17716916215b14b14513e13612f12711e11410d1050f70f00e90d90d40d00cc0c80c006a05b03202301501401300e00d00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record008_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record008_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record008) (record008.maps 6)
      (record008.inverseMaps 6) record008_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record008_frame006_links_0000 record008_frame006_links_0064)
theorem record008_frame006_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 6 :=
  of_group record008 6 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record008_frame006_indices record008_frame006_graph record008_frame006_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (Fin.cases (record008_frame004_supported hcells) (Fin.cases (record008_frame005_supported hcells) (Fin.cases (record008_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x7016cf59c58b5794ef4e14ce4ba4b94ad4a148f47846545744e35c34a3402af29f29528d27527426824a23522c22220f17116916316115d13d1391331261201161110f60ed0e70e50e00db0d50cd0c70c30bd0b70ac07305b05205004f04102902001f01e00f00e00d00a009004003002000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x334d6aaa8b53a29814b69db4bfa5b92b894b49ca4b524e90e45822350e28584269984cb66323109634ae25662b09500a7252b26912f89604a224a0e306d83621ac8ce45702b014a898046822210907803861b90d886502d414f0a004c024610b080835412805902b815808402900f807803a01000780380140090028010006000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 79 :=
  interval_of_check _ 64 15 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 79 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x5aaaa2d4e8a6052da57127292d48721c50cc84d3ad9a64cf866132718c8c4258d2b89598a8053929593489824b025112508083ad1cd8e306f636c1b10d386722f41698ae054829512c88d04442120f0070c3721ac0ca053c28013009184402020d502b815808604201c80a403e01e00e804402000f00700300140090028010006000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
def record013_frame002_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x6345cc5c05ae5a752a51b50f5004bb4b74b14613f53e93d73c53b53a834f33f33431a3123052e02d82d22cd2c628a24924023322721d2132041f71d51c41b11a019a17a16615d15713e12c1211161080e30d60cd0c70bc0b80a305505404104003802901f01e01d01101000f00e00c00a009005004003000 } : Fields).get c.val)
theorem record013_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record013_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record013) (record013.maps 2)
      (record013.inverseMaps 2) record013_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record013_frame002_links_0000 record013_frame002_links_0064)
theorem record013_frame002_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 2 :=
  of_group record013 2 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record013_frame002_indices record013_frame002_graph record013_frame002_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (Fin.cases (record013_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xe0d670b2f9926c845d429f14b2a2e50fa6b926e92948da448d2c6882a914b8a3650f27793909a846722d10688063ed1ee8f485c62bf1560a8050027513287e03d61ab0ca05f82dc1630a404e826612a08f045c1da0e906b81880c205902b815808403301900a403e01e00a0028012005002000c004000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 73 :=
  interval_of_check _ 64 9 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 73 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x667308180cbf05f5aa354eca614eaa6092e095e4a6a4ed25c8b344821c90b48374112054fd47d43301960c8658a2b71594aba543269933894a497246117089a4451c70db86c62b81518a4c50226f13109284642200f0070c3721a50c305d82d614d09f04b822a0f207283581940710310184066032014809404802300a00280120080028010006002 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x6605ce5c35b152c51e5124bc4aa4a349348d4623f23e63d43c83bf34c33c33132931d2e12ce2c72b62b22af28924a24223522a2202161d51c41b119819118617817416415b13e12c1211141010f60ee0e10d40cb0b20ab0a409f06e05f03803403203102902502402301501400c00a009008005004003002 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x5f82a354eca614af24ed25c87241ba088fd47d43af1a58cf2660328990cb1456e2b29568a864d3252925c8b844d222900476039e1c70df86dc36317a0b4c57029314089bc4ae24a11908803c01c30dc86a830c1760b3853427c12e07903941ac0ca038818407203501980c8052025012008c02a01400600280120080028010006002 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record017_frame002_links_0000 record017_frame002_links_0064)
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x703b379976c905d129e54aca2b4d7a6152fc9774b825a52c495d4ab24e125491c488a43d20e90047da3b51cc6992a794aca3050a279119c89e442219108c82e3ef1ef8b805782a914d8a0c3f01e00e9870c3681a80c005c029213b09a04b824811f08c044821210307e03dc1e20ea07103701ac0d204a01c4052025012008c03e01e00e805002000f0070028012008 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x6673075806bee5a92a2d4e8a604eea6152e49604a7a4f525e928487a2dd12887442ba15107882740b1facfaa6612c515b8aca55d2a1934897c4b0251125091245f2280e306d83621ab8cec5702a31498a044de26011a08883c61c60dd06cc3261890bc85b029813d096849022e10407783881a60cb04a01c4052025012008c03e01e00e805002000f0070028012008 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
def record018_frame003_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x7056a268e68162d5c85bb5a956153e53953252c52552051c5154f54e84dc4d24d04c84c04ba4ac4a43dd34332f32b3263182d42c82be2b42aa2a128727c2021f41ed1e81da19618a18017416b16314713d11c10f10b1060fc0f80f20ed0e40dd0d60d20cd0c60be0b90b40af08806f02902502402301f01e01d01401000f00e00a009008 } : Fields).get c.val)
theorem record018_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record018_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record018) (record018.maps 3)
      (record018.inverseMaps 3) record018_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record018_frame003_links_0000 record018_frame003_links_0064)
theorem record018_frame003_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 3 :=
  of_group record018 3 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record018_frame003_indices record018_frame003_graph record018_frame003_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (Fin.cases (record018_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x5f82b9951aa76530a96925c923477a36514287e4391fa8fa86f434b19e4cc064f3211594aaa54429b14a09f84de26991d08b844d2008e786fc3631a68cb063430617a0b8c5a62c215c0a9852425711908804221e00e186e43541860bb059c27c12e08e83fc1e40e5065018408603501980c8052024011808802a014006002c0140090028010006002 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x93323a4448184b07a0a40d7f8f5de63bf768ea5d038f708dedb53656b8d25a2b41594b1d612a54ec9b130a584ae8cd1421e4287c4f39e13be730ce1923045f8a814627c4ec9711a21c420830fe1f43d4778e91c836c6a0c717c2e05a0a91482784d0931041982c8580620c01282304402c0500900c01402003 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x5f82f4d774ba4530a95d44ca134eaa5c129a92e488a3bd1b28a143f21c90888374111fa8fa87be3301968c8a5f02cb95ecaca5512a493f09bc4d325d91d08b844d224901873c37e1b18d745c62c215c0ab051a25c119088042e1fd0f707803a21c30dc869032216209f04b824c0ff07903941b60ca04f01c00c406101980c804c024011802c0140090030014008003 } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record020_frame002_links_0000 record020_frame002_links_0064)
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x648314d87ea2b4f7276935e97e4b825892ae9554a6a51926292348e245921490748023b51cc8df34c97a4ac253d28c13fc9f049a23b919c8b243c1f78f7c7ac37a1790b3855229014488ac4101f80f507343001700b3855c2a01490a104ec26812f094043c21610307e03e01e00e807103701b20d204f024c0f6070013009004602000f807802200f007002c014009 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
def record021_frame002_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0xc8d8f31b5a5b3364ebdd3ea5945e7fcfe9eb39666cb9957282464898f318e2e45576ee29a6b3e654c698caec5b6b3963ab852aa4146a7045086d039f83e872cde1af34e664bb16f2d6590af1542944fc9992a23e3c0758e01ac34c638be1682a85389c1061f43586404c0901182003e0780880f01c02c05009 } : Fields).get c.val)
theorem record021_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record021_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record021) (record021.maps 2)
      (record021.inverseMaps 2) record021_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record021_frame002_links_0000 record021_frame002_links_0064)
theorem record021_frame002_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 2 :=
  of_group record021 2 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record021_frame002_indices record021_frame002_graph record021_frame002_links
def record021_frame003_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x93121e40424827031ff3d879af01d9bb2754e85c83856f8dddb4b666bad29a3342596a953b26c4c29612ba3144c8710d20c3d278cef1cc334640c01762ea540a313e2764b88810a20a4007d8f61e03a8728e11b4318628bd16e2d4570a81462744d8941041ec3686604a08c1101f03c0740880f01c02c05009 } : Fields).get c.val)
theorem record021_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record021_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record021) (record021.maps 3)
      (record021.inverseMaps 3) record021_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record021_frame003_links_0000 record021_frame003_links_0064)
theorem record021_frame003_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 3 :=
  of_group record021 3 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record021_frame003_indices record021_frame003_graph record021_frame003_links
def record021_frame004_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x5f72ed173ca6051228453ba9724a7a4bd22090c479237114a88243a21ad08283c4139facfaa7bf33097c0b2e57b2b29544a924f926d93489904aa22f914088e4061cd8dec6c434b1a08b8c5842b81560a3446822210a88003e21e30ea07183741b50d085842a813d09684a02280fd07783881ba0cb04f024c0f6070013009004602000f807802200f007002c014009 } : Fields).get c.val)
theorem record021_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record021) (record021.maps 4) (record021.inverseMaps 4) record021_frame004_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record021) (record021.maps 4) (record021.inverseMaps 4) record021_frame004_indices (Fin.ofNat record021.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record021_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record021) (record021.maps 4)
      (record021.inverseMaps 4) record021_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record021_frame004_links_0000 record021_frame004_links_0064)
theorem record021_frame004_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 4 :=
  of_group record021 4 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record021_frame004_indices record021_frame004_graph record021_frame004_links
def record021_frame005_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x6816646555a958957d56153952c52051651450c5034ee4e14dc4d74cb4c84c04ac4a449c3dd38f34b33832b31f31d2e92da2d42cf2b828727c27525120b1fc1ed1e11df1aa19d19619117a14713d13712a12311c11610f10b1071000ea0e60dd0d60d30cc0c40be0b90b70af09008707706e02602402302001f01e01100f00e00b00a009 } : Fields).get c.val)
theorem record021_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record021) (record021.maps 5) (record021.inverseMaps 5) record021_frame005_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record021) (record021.maps 5) (record021.inverseMaps 5) record021_frame005_indices (Fin.ofNat record021.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record021_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record021) (record021.maps 5)
      (record021.inverseMaps 5) record021_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record021_frame005_links_0000 record021_frame005_links_0064)
theorem record021_frame005_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 5 :=
  of_group record021 5 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record021_frame005_indices record021_frame005_graph record021_frame005_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (Fin.cases (record021_frame002_supported hcells) (Fin.cases (record021_frame003_supported hcells) (Fin.cases (record021_frame004_supported hcells) (Fin.cases (record021_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x646b19d450a024d7a5f92e09624aba55529a946498a48d23891047d23c91ce8e046f1a70bc65672a194789fc4e726b92688ee46722090587d43da1ea8dd05f02d41578a3c4f026811588203f01d20d385ec2d61660ab854029214209d84d025612408f846022610708003e41e00e807103701b00d304f023811a07b03581a8054029010007c03c01500a002c014009 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
def record022_frame002_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x5f6af254bea384eea5c929e92f48824311e48dc452a2090e88564099fecfac7c03de1988bd459c2c0159caa053b29693e49b64d225792208b644c22310047403801b20d2865c31c1718b0857029212f88c043c21410007c43c61d40e306e834c1930c485e42dc14909c84a82280fd07783881b40ce04f023811a07b03581a8054029010007c03c01500a002c014009 } : Fields).get c.val)
theorem record022_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record022_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record022) (record022.maps 2)
      (record022.inverseMaps 2) record022_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record022_frame002_links_0000 record022_frame002_links_0064)
theorem record022_frame002_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 2 :=
  of_group record022 2 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record022_frame002_indices record022_frame002_graph record022_frame002_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (Fin.cases (record022_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xabfa55a46a39a28a1497f9098dc8c98937fc7c47ad79c7937837727637537367227167036d26bf6ab61b59d5915845404bd4b04a247647046345544743942d41d3e93db3c23b33ae37b2ea2a029628627526725a2442341e51d71d01c21ba1ae1a019118316d15f1181071010f10e60d90cc0c40b506f06e06005f03303202402300c00b00a009006005004003 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
def record023_frame002_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x18f8bf05f4af4d774ba4571a98544ca134eaa4b91de8d9462a2cd14289043f21c90b484441ba088fd47d43df1bdccc065732297c0aca55c2a49470a164fc27693789a64cf25d921c8e845c226912480c3631830bd05c62d31610ae054428d119088042e1fd0f707803a21c30dc869032213e097049821e0ff07903941b60ca03881c00c406101980c8048023006002c0140090030014008003 } : Fields).get c.val)
theorem record023_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record023_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record023) (record023.maps 2)
      (record023.inverseMaps 2) record023_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record023_frame002_links_0000 record023_frame002_links_0064)
theorem record023_frame002_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 2 :=
  of_group record023 2 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record023_frame002_indices record023_frame002_graph record023_frame002_links
def record023_frame003_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1aaed0a68233f59eacee5be2ad94fca6c5082529224900477a3a11c28da469a3311868bc45ba2c113a8964479cb4ce46633281760a3a50e27d93209824ba25992b494c4a124d120c8fa47523791b081231c15c8aa453228a13d09ac4aa2460fe07b83d01d60e306d834e1970c405c82c611908584141ee0f007483881ba0d503881c00c406101980c8048023006002c0140090030014008003 } : Fields).get c.val)
theorem record023_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record023_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record023) (record023.maps 3)
      (record023.inverseMaps 3) record023_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record023_frame003_links_0000 record023_frame003_links_0064)
theorem record023_frame003_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 3 :=
  of_group record023 3 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record023_frame003_indices record023_frame003_graph record023_frame003_links
def record023_frame004_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x7ad77276e7677607596d467364f6426195b859358957c57556e56756055b55354c54754052d52651f48140f4073f63b434233a3293073002f92f22eb2e62e22db2c52be2b52af2ad2812051cb1c31bc1b51ae1a819b19116615d15b14b14313c13512e12811b1110e40df0db0ce0c90c30c00bf0b807107006206103303202402300c00b00a009006005004003 } : Fields).get c.val)
theorem record023_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record023) (record023.maps 4) (record023.inverseMaps 4) record023_frame004_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record023) (record023.maps 4) (record023.inverseMaps 4) record023_frame004_indices (Fin.ofNat record023.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record023_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record023) (record023.maps 4)
      (record023.inverseMaps 4) record023_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record023_frame004_links_0000 record023_frame004_links_0064)
theorem record023_frame004_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 4 :=
  of_group record023 4 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record023_frame004_indices record023_frame004_graph record023_frame004_links
def record023_frame005_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0258.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0258.count (({ width := 8, code := 0xa09f9e9d9c9b9a99959391908c8a8887868584838281807f7c7a78767473716d6b6a6864636261605f5e5c585756555452504a494847464544433e3d3c3b3a3938373635342f2e2d2c2b2a29282624231f1e181713120b0a090805040302 } : Fields).get c.val)
theorem record023_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0258.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0258.localPairCheck (smallEmbedding record023) (record023.maps 5) (record023.inverseMaps 5) record023_frame005_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0258.localPairCheck (smallEmbedding record023) (record023.maps 5) (record023.inverseMaps 5) record023_frame005_indices (Fin.ofNat record023.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record023_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0258.localPairCheck (smallEmbedding record023) (record023.maps 5)
      (record023.inverseMaps 5) record023_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record023_frame005_links_0000 record023_frame005_links_0064)
theorem record023_frame005_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 5 :=
  of_group record023 5 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0258
    Papers.RationalityTen.SharedFrameCatalogue.group0258_facts record023_frame005_indices record023_frame005_graph record023_frame005_links
def record023_frame006_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0152.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0152.count (({ width := 8, code := 0xa09f9e9d9c9b9a99959391908c8a8887868584838281807f7c7a78767473716d6b6a6864636261605f5e5c585756555452504a494847464544433e3d3c3b3a3938373635342f2e2d2c2b2a29282624231f1e181713120b0a090805040302 } : Fields).get c.val)
theorem record023_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0152.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0152.localPairCheck (smallEmbedding record023) (record023.maps 6) (record023.inverseMaps 6) record023_frame006_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0152.localPairCheck (smallEmbedding record023) (record023.maps 6) (record023.inverseMaps 6) record023_frame006_indices (Fin.ofNat record023.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record023_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0152.localPairCheck (smallEmbedding record023) (record023.maps 6)
      (record023.inverseMaps 6) record023_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record023_frame006_links_0000 record023_frame006_links_0064)
theorem record023_frame006_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 6 :=
  of_group record023 6 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0152
    Papers.RationalityTen.SharedFrameCatalogue.group0152_facts record023_frame006_indices record023_frame006_graph record023_frame006_links
def record023_frame007_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0252.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0252.count (({ width := 10, code := 0x85a138420e8320a7e9f07ade8785d1715c16f9bb6ddb36bdab69da36819e6659463d7b5a5665895652949519404f5394d5314b52b4991c4691744d113ecdd340cc320c4300bd2f0b929ca227c9a25c9323c8b21c811f06f1b0681845d1645514c4e1003f0e0370a0270801f0300b028090180501003 } : Fields).get c.val)
theorem record023_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record023) (record023.maps 7) (record023.inverseMaps 7) record023_frame007_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record023) (record023.maps 7) (record023.inverseMaps 7) record023_frame007_indices (Fin.ofNat record023.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record023_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record023) (record023.maps 7)
      (record023.inverseMaps 7) record023_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record023_frame007_links_0000 record023_frame007_links_0064)
theorem record023_frame007_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 7 :=
  of_group record023 7 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0252
    Papers.RationalityTen.SharedFrameCatalogue.group0252_facts record023_frame007_indices record023_frame007_graph record023_frame007_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (Fin.cases (record023_frame002_supported hcells) (Fin.cases (record023_frame003_supported hcells) (Fin.cases (record023_frame004_supported hcells) (Fin.cases (record023_frame005_supported hcells) (Fin.cases (record023_frame006_supported hcells) (Fin.cases (record023_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xabf9819068957f77e47d379c7937837727637537467326195a057356453e4bd4ab49d4904804764704634554474394204104073f837a2e72da2ce2a029628627526725a2452351e71d91cf1c21ba1ae1a019118316f16113712b0fb0f10e60d90cc0c205a05903903802a02902402302200f00e00c00b00a009006005004003001 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
def record024_frame002_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x18f8ae9530276d25891d482a3151668a144821f90e486c42a9bc4cc263231097a8aca5572a214d8a5051c28593f09da4de26992fc9584a524b90106c435319f0c185e82e31698b085702a414808d04442120fe87b83c01d10e186e434e1940b3054423c10f07f83c81ca0d902e016c07203801500a4048023011003c01c00c00580280120060028010006001 } : Fields).get c.val)
theorem record024_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record024_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record024) (record024.maps 2)
      (record024.inverseMaps 2) record024_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record024_frame002_links_0000 record024_frame002_links_0064)
theorem record024_frame002_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 2 :=
  of_group record024 2 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record024_frame002_indices record024_frame002_graph record024_frame002_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (Fin.cases (record024_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x97f9068d98c68947f77e17d079c7937837727637536195a057356453f4bd4ad49f4764704634554474393792e72d82cc2be2ac2a029628627526725a22821a1e71d91cb1c21ba1ae1a019118317116313712b0fd0f10e60d90cc06f06e05a05903903802402301501400f00e00d00c00b00a009008006005004003001 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
def record025_frame002_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x2b8d4c0a24508a76125891a48123151668a144821f90e46f133098c8c425ed2b29564a8c51c28593f09da4de26990046c435119e0ca462e30617a0b8c5a62c215c0a044de23411108383fa1ee0f007443861b90d486582cc151090043c1fe0f207281c40e005c02d80e4070024011805402800f007003401800b00500240100060028010006001 } : Fields).get c.val)
theorem record025_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record025_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record025) (record025.maps 2)
      (record025.inverseMaps 2) record025_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record025_frame002_links_0000 record025_frame002_links_0064)
theorem record025_frame002_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 2 :=
  of_group record025 2 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record025_frame002_indices record025_frame002_graph record025_frame002_links
def record025_frame003_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0253.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0253.count (({ width := 9, code := 0x516813c9d4da612f96ca64f2490c7a36fe7cbd5e6ef74ba1cce270375b4d76a2b936994c25d2c9448a3916884320d047b3c1d4e872379b0d2663117cb4592a1449c4b240f07634198a04e200f844200f07034180b050241006028100601 } : Fields).get c.val)
theorem record025_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record025) (record025.maps 3) (record025.inverseMaps 3) record025_frame003_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record025) (record025.maps 3) (record025.inverseMaps 3) record025_frame003_indices (Fin.ofNat record025.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record025_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record025) (record025.maps 3)
      (record025.inverseMaps 3) record025_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record025_frame003_links_0000 record025_frame003_links_0064)
theorem record025_frame003_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 3 :=
  of_group record025 3 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0253
    Papers.RationalityTen.SharedFrameCatalogue.group0253_facts record025_frame003_indices record025_frame003_graph record025_frame003_links
def record025_frame004_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2cfd4c4a27509a6e51ce8d5461222d0f286742aa11506660b29713cc9be4851d98e8471c3571a28ccc64231117f88e43d81e40ee875c3a01c90e106ec3681ad0d306443141730b605942c01590a9052c28813d09a04b423411307e83d41dc0e707001c40e005c02d80e4070024011805402800f007003401800b00500240100060028010006001 } : Fields).get c.val)
theorem record025_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 4) (record025.inverseMaps 4) record025_frame004_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 4) (record025.inverseMaps 4) record025_frame004_indices (Fin.ofNat record025.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record025_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 4)
      (record025.inverseMaps 4) record025_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record025_frame004_links_0000 record025_frame004_links_0064)
theorem record025_frame004_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 4 :=
  of_group record025 4 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record025_frame004_indices record025_frame004_graph record025_frame004_links
def record025_frame005_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x5d057955a54f52c4cb4c04b249649248647b46f4683973403213162f329228627b25d25624d24023822f1ac17116b16516115d15715414f14914313d12d12911611110e10c10a1051000fb0f60ee0e80da0d40c40be0b80b30af06a06905505403903802402301501400f00e00d00c00b00a009008006005004003001 } : Fields).get c.val)
theorem record025_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record025) (record025.maps 5) (record025.inverseMaps 5) record025_frame005_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record025) (record025.maps 5) (record025.inverseMaps 5) record025_frame005_indices (Fin.ofNat record025.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record025_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record025) (record025.maps 5)
      (record025.inverseMaps 5) record025_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record025_frame005_links_0000 record025_frame005_links_0064)
theorem record025_frame005_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 5 :=
  of_group record025 5 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record025_frame005_indices record025_frame005_graph record025_frame005_links
def record025_frame006_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0252.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0252.count (({ width := 10, code := 0x1fa7bdea79de2741cd725be6edb76cdaf6ad7a5a95e5695552948515404f5394d5314b4fa370d935cd534cd0330c8310c02f4b52c8a828c9d2689724c8f22c8720c7e1d0711986117459154400fc360d42a0a42007c110400f0380d0300b02809020060140400c01 } : Fields).get c.val)
theorem record025_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record025) (record025.maps 6) (record025.inverseMaps 6) record025_frame006_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record025) (record025.maps 6) (record025.inverseMaps 6) record025_frame006_indices (Fin.ofNat record025.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record025_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record025) (record025.maps 6)
      (record025.inverseMaps 6) record025_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record025_frame006_links_0000 record025_frame006_links_0064)
theorem record025_frame006_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 6 :=
  of_group record025 6 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0252
    Papers.RationalityTen.SharedFrameCatalogue.group0252_facts record025_frame006_indices record025_frame006_graph record025_frame006_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (Fin.cases (record025_frame002_supported hcells) (Fin.cases (record025_frame003_supported hcells) (Fin.cases (record025_frame004_supported hcells) (Fin.cases (record025_frame005_supported hcells) (Fin.cases (record025_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc775f72b994c09dd497a4952188f246e232516e8a544a22090e886d42b1facfaa6f433097a8aca5572a214d8a5051928413e49d44db269130895e45f22810046c435119e0ca462e30617a0b8c5a62c215c0a9852423411108003e21e30ea07183741a60c986242f21690aa04f425a11c08603f41de0e206d032c054029012008c044021010007c03c01500a003c01c00d006002c014009 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
def record026_frame002_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xd636482bf94569af4b125712aa94d4a324fd270931495248d23891748823b51cc77834c978ca3050427993849a24be2561268910477233914c8823ef1ef8dd055229514209c84c424f11e88ac4322080fc07903a41800b8055c2a01490a104ec26812b092047c230111085840c1f80f507703a01c40dc06c0348054029012008c044021010007c03c01500a003c01c00d006002c014009 } : Fields).get c.val)
theorem record026_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record026_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record026) (record026.maps 2)
      (record026.inverseMaps 2) record026_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record026_frame002_links_0000 record026_frame002_links_0064)
theorem record026_frame002_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 2 :=
  of_group record026 2 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record026_frame002_indices record026_frame002_graph record026_frame002_links
def record026_frame003_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x6d46815fc5a956152051b51450c5034fb4f54ee4e84e14dc4d84d14ac4a443f3dd38a32b32331930e3042f92f12e92e22da2d42ca2bd28727c24c1ed1e51db1cf1c51bb1b21aa1a519d19618c17f14713d12a12311c11610f10b1030fc0f80f20ec0e60dd0d60d00ca0c40be0b90b60af02a02902402302202102001f01e01501400f00e00d00c00b00a009 } : Fields).get c.val)
theorem record026_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record026_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record026) (record026.maps 3)
      (record026.inverseMaps 3) record026_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record026_frame003_links_0000 record026_frame003_links_0064)
theorem record026_frame003_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 3 :=
  of_group record026 3 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record026_frame003_indices record026_frame003_graph record026_frame003_links
def record026_frame004_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0259.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0259.count (({ width := 9, code := 0x10f8640a00fa7c3d9e8f2783b9d6e872b89bedc6c33190c05eacd64b1582bd5cab54295449f4e26d308d45211068240a00fe7d3d9e4ee75399c8e06632180bc5c2d160ac5429948a04e261289247221047c3b1c8d434190c05c2c150a04c24110803c1c0d0602c1409 } : Fields).get c.val)
theorem record026_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0259.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record026) (record026.maps 4) (record026.inverseMaps 4) record026_frame004_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record026) (record026.maps 4) (record026.inverseMaps 4) record026_frame004_indices (Fin.ofNat record026.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record026_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record026) (record026.maps 4)
      (record026.inverseMaps 4) record026_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record026_frame004_links_0000 record026_frame004_links_0064)
theorem record026_frame004_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 4 :=
  of_group record026 4 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0259
    Papers.RationalityTen.SharedFrameCatalogue.group0259_facts record026_frame004_indices record026_frame004_graph record026_frame004_links
def record026_frame005_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0153.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0153.count (({ width := 9, code := 0x10b843f9f8f67a3c9e0ee763a9cee470b79b6d86a32188bd5d2c15eae56ab156a852a893e9c4ca612a8a43a0902803f9f8fa7b3c9dcea73389c0dc643117cba5b2c95caa53291449e4d259249047221047c3b1c8d434190c05c2c150a04c24110803c1c0d0602c1409 } : Fields).get c.val)
theorem record026_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0153.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0153.localPairCheck (smallEmbedding record026) (record026.maps 5) (record026.inverseMaps 5) record026_frame005_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0153.localPairCheck (smallEmbedding record026) (record026.maps 5) (record026.inverseMaps 5) record026_frame005_indices (Fin.ofNat record026.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record026_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0153.localPairCheck (smallEmbedding record026) (record026.maps 5)
      (record026.inverseMaps 5) record026_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record026_frame005_links_0000 record026_frame005_links_0064)
theorem record026_frame005_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 5 :=
  of_group record026 5 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0153
    Papers.RationalityTen.SharedFrameCatalogue.group0153_facts record026_frame005_indices record026_frame005_graph record026_frame005_links
def record026_frame006_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0231.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0231.count (({ width := 8, code := 0x888786858482807e7c7a78767472706e6c6a686664636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a4948474645444342403e3c3a3836353432302e2c2b2a2928272625231817161514131211100f0e0d0c0b0a090807 } : Fields).get c.val)
theorem record026_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0231.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0231.localPairCheck (smallEmbedding record026) (record026.maps 6) (record026.inverseMaps 6) record026_frame006_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0231.localPairCheck (smallEmbedding record026) (record026.maps 6) (record026.inverseMaps 6) record026_frame006_indices (Fin.ofNat record026.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record026_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0231.localPairCheck (smallEmbedding record026) (record026.maps 6)
      (record026.inverseMaps 6) record026_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record026_frame006_links_0000 record026_frame006_links_0064)
theorem record026_frame006_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 6 :=
  of_group record026 6 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0231
    Papers.RationalityTen.SharedFrameCatalogue.group0231_facts record026_frame006_indices record026_frame006_graph record026_frame006_links
def record026_frame007_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0257.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0257.count (({ width := 9, code := 0xee76399c8de6e369b0d66a349a0ce6632990c661ae16ab056a8d44a15027d3c9c4d2612c94492451e8541a00fe7e3e9f0f6793b9d4e671379b8d86230174b6592b954a6512813c9a4b2491c8c45219047e3d1d8e0381b0d06430170b05428110803c1c0d0602c1409 } : Fields).get c.val)
theorem record026_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0257.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (smallEmbedding record026) (record026.maps 7) (record026.inverseMaps 7) record026_frame007_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (smallEmbedding record026) (record026.maps 7) (record026.inverseMaps 7) record026_frame007_indices (Fin.ofNat record026.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record026_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (smallEmbedding record026) (record026.maps 7)
      (record026.inverseMaps 7) record026_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record026_frame007_links_0000 record026_frame007_links_0064)
theorem record026_frame007_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 7 :=
  of_group record026 7 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0257
    Papers.RationalityTen.SharedFrameCatalogue.group0257_facts record026_frame007_indices record026_frame007_graph record026_frame007_links
def record026_frame008_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0151.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0151.count (({ width := 8, code := 0x888786858482807e7c7a78767472706e6c6a686664636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a4948474645444342403e3c3a3836353432302e2c2b2a2928272625231817161514131211100f0e0d0c0b0a090807 } : Fields).get c.val)
theorem record026_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0151.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0151.localPairCheck (smallEmbedding record026) (record026.maps 8) (record026.inverseMaps 8) record026_frame008_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0151.localPairCheck (smallEmbedding record026) (record026.maps 8) (record026.inverseMaps 8) record026_frame008_indices (Fin.ofNat record026.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record026_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0151.localPairCheck (smallEmbedding record026) (record026.maps 8)
      (record026.inverseMaps 8) record026_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record026_frame008_links_0000 record026_frame008_links_0064)
theorem record026_frame008_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 8 :=
  of_group record026 8 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0151
    Papers.RationalityTen.SharedFrameCatalogue.group0151_facts record026_frame008_indices record026_frame008_graph record026_frame008_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (Fin.cases (record026_frame002_supported hcells) (Fin.cases (record026_frame003_supported hcells) (Fin.cases (record026_frame004_supported hcells) (Fin.cases (record026_frame005_supported hcells) (Fin.cases (record026_frame006_supported hcells) (Fin.cases (record026_frame007_supported hcells) (Fin.cases (record026_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1ac0c8d57da8a135e96249fa4e126292a491a47122290a483a4011f28f2473a3811ba77d34f978ca304c4259128091c47d236913487643821410608103e91ec8f5c6e82a912a890c46221f10707f83bc1cc0e486e43521990bd05a82d01570a8052428413b09a04ac24811f08c044421610307e03dc1e40ec07303801b40d404a024c11c08d03881c00d606a01500a404802300a805001e00e } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
def record027_frame002_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x86582275d6e46755ec59959058858057857056255a55754e54653e53152a52747b3f236f2f62b62ad2a529d29528d27f27727426b26325b24e2472442201d81b81b11a91a219a19118517e17a17216a16315815014d14613f13713012811f11310c1081000f80f10e60de0db0d50d10cd0c90c50c109409308e08d07107006b06a02a02902402301501400f00e } : Fields).get c.val)
theorem record027_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record027_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record027) (record027.maps 2)
      (record027.inverseMaps 2) record027_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record027_frame002_links_0000 record027_frame002_links_0064)
theorem record027_frame002_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 2 :=
  of_group record027 2 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record027_frame002_indices record027_frame002_graph record027_frame002_links
def record027_frame003_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1106.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1106.count (({ width := 10, code := 0x79dcf6d59d61d6e5815e5715a5615654d515414e5314a51d4551131461033acdf374db364d7354d2340cf334cb324c6310c32e8a225894248902388c2248721884208801f47b1e8781d8741c8701b86b1a468198641885f1745c168591605715855104400ec3a0b02b0982505c16044100200700801 } : Fields).get c.val)
theorem record027_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record027) (record027.maps 3) (record027.inverseMaps 3) record027_frame003_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record027) (record027.maps 3) (record027.inverseMaps 3) record027_frame003_indices (Fin.ofNat record027.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record027_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record027) (record027.maps 3)
      (record027.inverseMaps 3) record027_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record027_frame003_links_0000 record027_frame003_links_0064)
theorem record027_frame003_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 3 :=
  of_group record027 3 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1106
    Papers.RationalityTen.SharedFrameCatalogue.group1106_facts record027_frame003_indices record027_frame003_graph record027_frame003_links
def record027_frame004_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1104.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1104.count (({ width := 10, code := 0x856027b5da71db36859e66d98655926358a6258660d805ed795e16a5593f4b1204751a45d144450c42508415023fcfa3e0f73bcdc340cd328c7310c12f0b92e0b52c8af2a8a829ca42849e26c98254902348c2248620c7e1f07b1e0771d8751d073190631785d1445012c4a0a829090230541403c0e } : Fields).get c.val)
theorem record027_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1104.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record027) (record027.maps 4) (record027.inverseMaps 4) record027_frame004_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record027) (record027.maps 4) (record027.inverseMaps 4) record027_frame004_indices (Fin.ofNat record027.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record027_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record027) (record027.maps 4)
      (record027.inverseMaps 4) record027_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record027_frame004_links_0000 record027_frame004_links_0064)
theorem record027_frame004_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 4 :=
  of_group record027 4 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1104
    Papers.RationalityTen.SharedFrameCatalogue.group1104_facts record027_frame004_indices record027_frame004_graph record027_frame004_links
def record027_frame005_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1103.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1103.count (({ width := 10, code := 0x856027b5da71db36859e66d98655926358a6258660d805ed795e16a5593f4b1204751a45d144450c42508415023fcfa3e0f73bcdc340cd328c7310c12f0b92e0b52c8af2a8a829ca42849e26c98254902348c2248620c7e1f07b1e0771d8751d073190631785d1445012c4a0a829090230541403c0e } : Fields).get c.val)
theorem record027_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1103.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record027) (record027.maps 5) (record027.inverseMaps 5) record027_frame005_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record027) (record027.maps 5) (record027.inverseMaps 5) record027_frame005_indices (Fin.ofNat record027.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record027_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record027) (record027.maps 5)
      (record027.inverseMaps 5) record027_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record027_frame005_links_0000 record027_frame005_links_0064)
theorem record027_frame005_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 5 :=
  of_group record027 5 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1103
    Papers.RationalityTen.SharedFrameCatalogue.group1103_facts record027_frame005_indices record027_frame005_graph record027_frame005_links
def record027_frame006_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1102.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1102.count (({ width := 10, code := 0x8ea22821f0769c16c1ae6ada8695a26759a6659664d906318a62576575454b52147d1c4651644d0e42d0a41d04404fd3ecfa3c4d9334cb320c5308bf2e8b72d8b32c0ad2a4a7298a42889f27099258912388d22887210801f87d1ec7a1e4781dc76188611705b1344c11c460a829090230541403c0e } : Fields).get c.val)
theorem record027_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record027) (record027.maps 6) (record027.inverseMaps 6) record027_frame006_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record027) (record027.maps 6) (record027.inverseMaps 6) record027_frame006_indices (Fin.ofNat record027.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record027_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record027) (record027.maps 6)
      (record027.inverseMaps 6) record027_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record027_frame006_links_0000 record027_frame006_links_0064)
theorem record027_frame006_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 6 :=
  of_group record027 6 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1102
    Papers.RationalityTen.SharedFrameCatalogue.group1102_facts record027_frame006_indices record027_frame006_graph record027_frame006_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (Fin.cases (record027_frame002_supported hcells) (Fin.cases (record027_frame003_supported hcells) (Fin.cases (record027_frame004_supported hcells) (Fin.cases (record027_frame005_supported hcells) (Fin.cases (record027_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x35a592cb04518a6b92c277534b178ca304c1257927491647a235114087c435212905480a3ec1ee0f506e82a9129090045c21c10587ec3c21cf0e306d834c1960be85b42ca1560a7852028213a099847822e11008503d80c406102e016c07203801980c8054029012008c02a014007803800c005002000c004001 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record028_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037
