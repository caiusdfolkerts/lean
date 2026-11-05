module
prelude
public import GraphInputsRow31Part00123Data
public import RawFrameSupport
public import SharedFrameGroups008Checked
public import SharedFrameGroups011Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups021Checked
public import SharedFrameGroups026Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00123
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
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1d3ee6f723b77db5ed876b4b579a96d4369bb481a32d1268533f59eacea606afa976ab545a52cc15d4adc5642a214f0a60524a7a13bc9c44bf25c12b891c48623d11de8e846fa3711aa8c545e22dd1628a9451226512a88b39f9c30dec6e234819c8c725ea2db9684b1a53b28e93909824bb25892b894c49f24c924491048323a91bc8d23d81de8ebc6842da1620aa4528286140096c48e23c11508743de1c60d8868c33a1780b2056428e13a08603dc1e40e9071836c1a80ba057829813607503801ac0d206603081700b404001e00d806603201880b404e024011808801e00d00600280100070030010004001 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record001_frame001_links_0000 (interval_append _ 64 128 146 record001_frame001_links_0064 record001_frame001_links_0128))
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
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x7ea35e1a8acde5edaddd62aa9953928e14429ca48da3f10cc83f40f9fe8fd27d93e29ed8f4e6a73219784aca53e28213b492c3e71e40cc86162eb1630ad454a29114109cc49c23e11507c43bc1c90dc867c3301900c5060c2e816e0ac854428613d09b048423411208283bc1d209c04b82300fe07903a01cc0d806903281800b805a02c81580aa054023810407803b01a00c405a028012008804201e00e807003201800b804c02000f0068030016009004001c00c0040018008002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3b05bfedb56bab4a59fcccc635b075814bc35daac495b8a9b530293d46ca124c9a5ed2b0920484a3991ac8c344c218505c80a3fd9fa0f8a7b73d31e54e6e6e936b1a3cd025de2d4159ca5851b28113788be4472120fb07aa3b21d10e3c6c832d17d0b5858e2b41488a0c4e426112388fc47222910e885441e1ff0f987ac3c61dc0e7069033c1910c486082ea16d0b3854429413509704a023211208603f81de0e204201f80ea070036018c0be05b02b81540a804c02300f4070034015809c04601f00e807003201800b0054028012008804001c00b005002000e0040018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 128 139 :=
  interval_of_check _ 128 11 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 139 record003_frame001_links_0000 (interval_append _ 64 128 139 record003_frame001_links_0064 record003_frame001_links_0128))
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x34fd98ec8f62f309982ac065df2e21708b6e5b4ab8156aa8052aa929484a354d9266d2f494d49b245521890547b22d10e484e420a0c101c8013f81f9cf1874039b9c88e3a69d33798f0c1c6042ff17ccb0656f2aa94b8a3450027c93d09d24b524011948ba45021b10b884241a1f10f3877c39c1bf0db86bc33c18f0c386082fd17809dc4ce24d11e88b44262030fd071c36c1820bb05b02a214509d84982120e904201f80ea070036018c0be05b02b81540a804c02300f4070034015809c04601f00e807003201800b0054028012008804001c00b005002000e0040018008002000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 128 139 :=
  interval_of_check _ 128 11 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 139 record003_frame002_links_0000 (interval_append _ 64 128 139 record003_frame002_links_0064 record003_frame002_links_0128))
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x7647407367066ff6d26c767a6746366306065f75e65ae56c55f55554652e5244f84eb4da4d24be4b049c48748145944c44241640e4043df3d23c43a339738b3643573483323293233093022ed2dd2d82cb2bc2af2ab26723822d22620f1fc1f41dd1d21c41b41aa19919018117a15214613a12f11d1110f90eb0d70cb0c50a90a208f08907907006906005905705305204904304104003b03903702e02d02602502302101f01e01901401301000e00d00a009008005004003001000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x7647366ff6d568567a66e63c63662a6035f45e65ae56c56055552e5244f84ec4da4be4b049b48748145944c44241640e4043df3d23c438b35734e3483293233022f92ed2d82cb2bd2af2ab28627a2642452382261fc1f41e41dd1c41aa19918f18117a15414613a11d1110fb0eb0d70cd0c50a90a207907307107006c06a06906005905705305204904304104003b03903702e02502301f01e01901801501401301101000e00d00c00a009008005004003001000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0xabf53a9e5249d93866e4bc9692b644c758d912a1442483b02603bf07d4f81ea3cc780ea9d3b746ced899db32658c1d79ae9582a794ca954fe9f5352644b8951262434608b5062023e0770e49b932c640c217b2ce564a7142254490859051fa3b4718d51902e85b0b013825c3f87a0ee1d83886e0da1902e85b0ae158268460861081e03906e0b81282303e0780c81802a050098110200380680c0140240400500800c00800 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0407.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0407.count (({ width := 8, code := 0xe2e1e0dfdad9d8d7d6d5d2d1cecac9c8c7c5c4c1c0bfbdbbb9b5b4b3b2b1b0afaeabaaa7a3a2a1a09e9d9a99989694928e8d8b898583817d797775736f6c696763615d5b595654514e4b494743413b3a3938373635312e2d2b2a272625242322211d1a191716131211100f0e0d0c0b0a0908070504030100 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0407.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0407.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0407.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0407.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record007_frame003_links_0000 record007_frame003_links_0064)
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0407
    Papers.RationalityTen.SharedFrameCatalogue.group0407_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0326.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0326.count (({ width := 9, code := 0x71b89c2e06f375b8da6cb61aad469b459ece6632d94c9643198ac461b0982bf5f2f576ba5cad96ab4592c15ead562ad54a953a994aa451a89409d4ba55248d43211047f3d1d4e26f359a4c8622f96cb25629138984a22108763a1c8e06e361a8cc6431178b84e261289046221087c3c1d0d8682a14088401e0e06830160a048200e050200c0200 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0326.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0326.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0326.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0326.localPairCheck (smallEmbedding record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record007_frame004_links_0000 record007_frame004_links_0064)
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0326
    Papers.RationalityTen.SharedFrameCatalogue.group0326_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
def record007_frame005_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0246.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0246.count (({ width := 9, code := 0xb258ec561ad566b152a853a8f44a14f26d34994ba5b2b954a651269248641198c45e230f86c1a07017dbd5e6f176bb1d4e97439dcae37037d9ac960aed6cae53a95409d4a23912853e9ecde6c34988bc5a2a9409a4b239107c3c1d8e872371b0d06431178b85428138984a23110803c1d0d8682a14088401e0e06830160a048200e050200c0200 } : Fields).get c.val)
theorem record007_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0246.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record007_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record007) (record007.maps 5)
      (record007.inverseMaps 5) record007_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record007_frame005_links_0000 record007_frame005_links_0064)
theorem record007_frame005_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 5 :=
  of_group record007 5 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0246
    Papers.RationalityTen.SharedFrameCatalogue.group0246_facts record007_frame005_indices record007_frame005_graph record007_frame005_links
def record007_frame006_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0165.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0165.count (({ width := 8, code := 0xa7a6a5a4a3a2a1a09f9e9c9b9a9897969594939291908f8e8d8c8b8a89888786858382817f7e7d7c7b7a7978777675747372706e6a6866625e5c5a5854514e4c4a484442403e3c3a373432302c2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record007_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0165.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0165.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0165.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record007_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0165.localPairCheck (smallEmbedding record007) (record007.maps 6)
      (record007.inverseMaps 6) record007_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record007_frame006_links_0000 record007_frame006_links_0064)
theorem record007_frame006_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 6 :=
  of_group record007 6 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0165
    Papers.RationalityTen.SharedFrameCatalogue.group0165_facts record007_frame006_indices record007_frame006_graph record007_frame006_links
def record007_frame007_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0117.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0117.count (({ width := 9, code := 0xc0dfefd7cbb5cae36bb55a2c35eae562a751a85329747a351285409f4ee753598cc2552993c823b1b8bc4a210f85c2a0d0581c05fefd7d3e5cee36db5196c45c2d960ad50a692c9245220f8793b1bcd66732178b6582893890452210c843f1e8ec72371a8d0602d160ac54271288c421f0e8702e1609848221007834180b048200e050200c0200 } : Fields).get c.val)
theorem record007_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0117.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record007_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record007) (record007.maps 7)
      (record007.inverseMaps 7) record007_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record007_frame007_links_0000 record007_frame007_links_0064)
theorem record007_frame007_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 7 :=
  of_group record007 7 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0117
    Papers.RationalityTen.SharedFrameCatalogue.group0117_facts record007_frame007_indices record007_frame007_graph record007_frame007_links
def record007_frame008_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x7e63b55c08d63603af6178cb2a588ac01508a48509a63123890947d22f515c863427a0c101c7f73ed9e94f2e6d33521a48bec5dd2e61540a284df22c0fa07aa3c61c48de865e31b17e0b685862a7138898c472232111083c3fe1f30eb07403841ba0d3065c3141810b6059429414409e84b424c11908603f41ec0f006d035410a07e03d81e80e807103781980ba05b02b815809a046021810807803901b80b804a02300f807803201800a8050026011008003801a00c0050024010005002000c002000 } : Fields).get c.val)
theorem record007_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record007_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 8)
      (record007.inverseMaps 8) record007_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record007_frame008_links_0000 record007_frame008_links_0064)
theorem record007_frame008_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 8 :=
  of_group record007 8 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record007_frame008_indices record007_frame008_graph record007_frame008_links
def record007_frame009_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x8b91321c4267eefc9f53d279cf19d63a0720dddafb596aed15a0b2d64ec79893075fcbb1742d0594b0954aa553aa153ca694a08d91822b42c84cff9f93e6798ef9d738a704d89ab33e640c317b2bc560a694726a49c8c91420e40c788ed1cc35c678c51762bc540a41242343906e0d81ac338650c61682905009812c2284107e0f81c83706c0b41282303e0780c81802a050098110200380680c0140240400500800c00800 } : Fields).get c.val)
theorem record007_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record007_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record007) (record007.maps 9)
      (record007.inverseMaps 9) record007_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record007_frame009_links_0000 record007_frame009_links_0064)
theorem record007_frame009_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 9 :=
  of_group record007 9 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record007_frame009_indices record007_frame009_graph record007_frame009_links
def record007_frame010_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x8498157d77ab7367277216f36ec6e86bc69c68564c61860e6025db5d35a459d58557556b5595315284ec4db4d649848a48144b42a40c3d43ab3a73a538938235834c33b3263163022e52de2b12a728f27225a2472202182071fa1dd1c81ba1ab18a18015915214712f12410d0fd0ea0e30dc0c10b908007a07707607106e06c06305a05805405304b04504204103b03803602d02502301f01e01901801501401301101000e00d00c00a009008005004003001000 } : Fields).get c.val)
theorem record007_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record007_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record007) (record007.maps 10)
      (record007.inverseMaps 10) record007_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record007_frame010_links_0000 record007_frame010_links_0064)
theorem record007_frame010_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 10 :=
  of_group record007 10 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record007_frame010_indices record007_frame010_graph record007_frame010_links
def record007_frame011_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0406.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0406.count (({ width := 8, code := 0xa7a6a5a4a3a2a1a09f9e9c9b9a9897969594939291908f8e8d8c8b8a89888786858382817f7e7d7c7b7a7978777675747372706e6a6866625e5c5a5854514e4c4a484442403e3c3a373432302c2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record007_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0406.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0406.localPairCheck (smallEmbedding record007) (record007.maps 11) (record007.inverseMaps 11) record007_frame011_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0406.localPairCheck (smallEmbedding record007) (record007.maps 11) (record007.inverseMaps 11) record007_frame011_indices (Fin.ofNat record007.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record007_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0406.localPairCheck (smallEmbedding record007) (record007.maps 11)
      (record007.inverseMaps 11) record007_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record007_frame011_links_0000 record007_frame011_links_0064)
theorem record007_frame011_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 11 :=
  of_group record007 11 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0406
    Papers.RationalityTen.SharedFrameCatalogue.group0406_facts record007_frame011_indices record007_frame011_graph record007_frame011_links
def record007_frame012_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0325.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0325.count (({ width := 8, code := 0xa7a6a5a4a3a2a1a09f9e9c9b9a9897969594939291908f8e8d8c8b8a89888786858382817f7e7d7c7b7a7978777675747372706e6a6866625e5c5a5854514e4c4a484442403e3c3a373432302c2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record007_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0325.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0325.localPairCheck (smallEmbedding record007) (record007.maps 12) (record007.inverseMaps 12) record007_frame012_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0325.localPairCheck (smallEmbedding record007) (record007.maps 12) (record007.inverseMaps 12) record007_frame012_indices (Fin.ofNat record007.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record007_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0325.localPairCheck (smallEmbedding record007) (record007.maps 12)
      (record007.inverseMaps 12) record007_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record007_frame012_links_0000 record007_frame012_links_0064)
theorem record007_frame012_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 12 :=
  of_group record007 12 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0325
    Papers.RationalityTen.SharedFrameCatalogue.group0325_facts record007_frame012_indices record007_frame012_graph record007_frame012_links
def record007_frame013_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0245.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0245.count (({ width := 10, code := 0x7fdfb7e1f67b1e97a1df76dd9735c7711b96c1ad6a9a36899c66997659926418b625825f97c5c56e5ad5f55d55531404f93b4cd324bd2e4b12a4a1244811d43d0a404fa3d0ea37cdc354d231cbe2d8b1294a124c8f230831f4761b86618c6015c531184410c421043f0f83b0e0370cc320b82c0ac2a09c25090210781d06c1a054140441003c0e0340c02c0a0240801c050100300400 } : Fields).get c.val)
theorem record007_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record007) (record007.maps 13) (record007.inverseMaps 13) record007_frame013_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record007) (record007.maps 13) (record007.inverseMaps 13) record007_frame013_indices (Fin.ofNat record007.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record007_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record007) (record007.maps 13)
      (record007.inverseMaps 13) record007_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record007_frame013_links_0000 record007_frame013_links_0064)
theorem record007_frame013_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 13 :=
  of_group record007 13 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0245
    Papers.RationalityTen.SharedFrameCatalogue.group0245_facts record007_frame013_indices record007_frame013_graph record007_frame013_links
def record007_frame014_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0164.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0164.count (({ width := 8, code := 0x9f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6c6a676563605c5a585653504d4b49474442403e3c3a373432302c2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record007_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0164.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0164.localPairCheck (smallEmbedding record007) (record007.maps 14) (record007.inverseMaps 14) record007_frame014_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0164.localPairCheck (smallEmbedding record007) (record007.maps 14) (record007.inverseMaps 14) record007_frame014_indices (Fin.ofNat record007.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record007_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0164.localPairCheck (smallEmbedding record007) (record007.maps 14)
      (record007.inverseMaps 14) record007_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record007_frame014_links_0000 record007_frame014_links_0064)
theorem record007_frame014_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 14 :=
  of_group record007 14 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0164
    Papers.RationalityTen.SharedFrameCatalogue.group0164_facts record007_frame014_indices record007_frame014_graph record007_frame014_links
def record007_frame015_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0116.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0116.count (({ width := 9, code := 0xd0e7f399ac963b1b87c260af577badc2d768b3d8ac35bacd5aa951a7d2e95459fcf66b33984a249228e45a291386c32110782c0e02ff7e3eddae870b71a8cc5faf56eb454285389747231047e3e1d0de6b33980ba5a289388c4321104803d1d8e46e35198c85c2b150a45025118843e1d0d8682c1509848221007834180b048200e050200c0200 } : Fields).get c.val)
theorem record007_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0116.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0116.localPairCheck (smallEmbedding record007) (record007.maps 15) (record007.inverseMaps 15) record007_frame015_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0116.localPairCheck (smallEmbedding record007) (record007.maps 15) (record007.inverseMaps 15) record007_frame015_indices (Fin.ofNat record007.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record007_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0116.localPairCheck (smallEmbedding record007) (record007.maps 15)
      (record007.inverseMaps 15) record007_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record007_frame015_links_0000 record007_frame015_links_0064)
theorem record007_frame015_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 15 :=
  of_group record007 15 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0116
    Papers.RationalityTen.SharedFrameCatalogue.group0116_facts record007_frame015_indices record007_frame015_graph record007_frame015_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (Fin.cases (record007_frame005_supported hcells) (Fin.cases (record007_frame006_supported hcells) (Fin.cases (record007_frame007_supported hcells) (Fin.cases (record007_frame008_supported hcells) (Fin.cases (record007_frame009_supported hcells) (Fin.cases (record007_frame010_supported hcells) (Fin.cases (record007_frame011_supported hcells) (Fin.cases (record007_frame012_supported hcells) (Fin.cases (record007_frame013_supported hcells) (Fin.cases (record007_frame014_supported hcells) (Fin.cases (record007_frame015_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))
#print axioms record007_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00123
