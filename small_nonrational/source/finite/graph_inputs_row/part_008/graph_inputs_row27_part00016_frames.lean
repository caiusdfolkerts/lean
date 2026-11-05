module
prelude
public import GraphInputsRow27Part00016Data
public import RawFrameSupport
public import SharedFrameGroups010Checked
public import SharedFrameGroups013Checked
public import SharedFrameGroups014Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups018Checked
public import SharedFrameGroups020Checked
public import SharedFrameGroups022Checked
public import SharedFrameGroups023Checked
public import SharedFrameGroups024Checked
public import SharedFrameGroups025Checked
public import SharedFrameGroups028Checked
public import SharedFrameGroups029Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups090Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups110Checked
public import SharedFrameGroups111Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups114Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1c0ec7c6342e8942ea034d7a6a13429854b825a52ba95648e245921e90348023e91e68eb4702375064683337178cba45c02ba14f4a56503279119c8a844221190448023f11e88dd06c63511828b3857829414187e03ca1d30da06883241820b1055c2a01490a104ec26812b092047423010f08484141f80f707803a81c40dc06b034012408d03781a806e03201500a4050026012808c03e01e00e807002a014009804402000e0050024010007 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6df67366c6325ae5a857956b56154953252851b5144cc4c54b84a34a149948c48246f46e43b3b13ab38137837035934533d33432f2ec2e42db2ce2c52bc2b62a927826d26424622d2242172101b91af1a519118817e17416415b14e14413912f12611b11210a1070fb0f20ef0e40e10d90cc0ba0ae0a609e08107f06906403703202a02902802602502301f01e01d01c01501401301101000e00a009008007 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1814a4f51d26e534a9944a324311f48304102038fee7d83e39edcdac51b28312148e24602090f6078c2fc1760b685862a41498a0c472232115883c3f41f30f1877034c19e0cb862830417b0ba859c2c01590a9052c28813d09a04b424c10c07b83c01b408d03781a80bc05d02d815c0ac05401b80c804c025011807c03c01c00a80500260110080038014009004001c00c005002000c002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x355daa0d4968c33fd9facf66772e096deb5c56c2a5d51aa7c50b280d3e096c495a4852208ef47423851b48d3466231d1808b9453a2891368924471c1ccb264b31c18a0b6450427b138c9a64ba2569298940496247922890847d23b91bc8d23d61858bc45b629913d09ac4c224811c086041c2000f086d832e1880bf05942aa13509584741fc0f907803a41c40dc06a02c813c06d03501780b603801b80c8062029014008c04400e00580280120070028010006001 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb7bb6fb67b19ae1adeacfabca23a17a109b297b97096192091390b89885d84f83b8138037f87ed7d77c37b97a278d75474572e70f7076585dc5d35c75b95774eb4e04d24c449c48547a4704544454404334204123f93eb3a53122fb2eb2ad29328627b26125122e2252151ef1cd1b51a819d1831741511451351121080f50e80da0cf0bd0a909c06d06a05e05b03803703203102902802302200e00b00a009007005004003001 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record002_frame002_links_0000 record002_frame002_links_0064)
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
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xdfd5a12cb562ea894c8a3590c884241820850167f93eb1f20f6e60e2fc978caaa45d1d10cc061c2fc1768b5c58a2a214a0a0c47223211587e83c61c90e106ec3681ad0d3067432c18f0be05d42a414409e84d424211908984301fc0f606d82340da06a03081800b605802b81580a803501900a4050023010007c03c01c00a8050026011007003001600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xa21a15a0f98396d95e91e91190a86584c8388108007f77ea7d47c075874272b66e6616595e35d55c958f5815784f24e24d44b34a449b49048247742b41d40f3bd3ae3a430b2f92e92d82c72b72ad2a12932862732632532342252151f11e21d51cd1c41b51a819618517615714513511408d06a05b05905805705605403202302102001f01e01c01501401300e00d00c00b00a009007006005004003001000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0xd3f4cd2729c931fc5310c32d9b42c7aeab6acaadaa6a5a127d9da4f932498a623876138420d799dc749c4705be6e5b56c590625825c56d5a5404e1304a9244851e469164490d41d013d8f13b0e537cdb35cd333ccb314bd2d4a92889b2385d13043104400fc3e0f02f08c210801f0781c0541404c0e0340c02c0a02407018050100300400 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1684b2d58ba939472a254dca6953288d546122b911087643221490848303ec9f20f6e60e2fc978ca3450527892148e24601d08e386f43541a10cc063c30e17e0a9452828311c88c84561e40ee87583a01c90e106ec3681ad0d3067432c18f0c185f02ea1660b005642a414b0a204f426812d093046822610c07e82340d405b02c81600ae05602a00c8046021010007c03c01c00a805002600e006803001600a004801c00c005002000c002000 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record005_frame003_links_0000 record005_frame003_links_0064)
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
def record005_frame004_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x16feb6c5acaa79514a79509a8013da93248f24351dc8e747023651a48cb454228513472a38c9c28cc064d31d1754b885b528593e09ca4c726012e49644ac25292088f84762018fa87a63031778b6458e2b91548a6451427a135896449423a10e88384001e30eb071836c1a70cb86202ec1670ab84e825611d08002340d405b02c81600ae05602a00c8046021010007c03c01c00a805002600e006803001600a004801c00c005002000c002000 } : Fields).get c.val)
theorem record005_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record005_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 4)
      (record005.inverseMaps 4) record005_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record005_frame004_links_0000 record005_frame004_links_0064)
theorem record005_frame004_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 4 :=
  of_group record005 4 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record005_frame004_indices record005_frame004_graph record005_frame004_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (Fin.cases (record005_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x6ae69263462661e5f05cc5c05ae5a758454c52a51b50f5004e54bb4b74b14a046144f4484133f53e93d73c53b53a036934f33f33431a3122fd2e02d82d22cd28a26c25f24924023322721d2132041f71e01d51c41b11a019a18217a16615d15713e12c1211161080f20e30d60cd0c70bc0b80a308505505404104003e03803502902701f01e01d01101000f00e00c00a009005004003000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x26c4bb93323a4447d8d911212c1e829025fe3ed7ccf5de63bf768ea5ce38f708dedb53656b0d25a2b4163cbb9652c7584acd52a9150e9d9362614b095d1fa334508790a2023e279cf09df3986e8d819c324608bf1662a05189f13b25c4708d10e2104187f0fa1ea3bc748e41b6350648c717c2e05a0a91482784d093114208400660c81642c0560620c01282304402c0500900c01402003 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0846.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0846.count (({ width := 11, code := 0x22543383f05e08c077def35d73a673ee59c13766e2d91ad34e682cf99ab2b646c6d87b0c602bd976ae5594aa142a814f89c52f2514948e117a25438869082063fa7e0f71df3a2720e09c0350664c99812ea5a4b09562905009c93425847c8e10d20e4107f8f81e43c4750e31b4354658c41742d4590a713e2604b09110a2043f0650c615c2b0540660c81302404602c0500900c01402003 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0846.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0846
    Papers.RationalityTen.SharedFrameCatalogue.group0846_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0358.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0358.count (({ width := 8, code := 0x6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0358.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0358.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0358.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0358.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record007_frame003_links_0000 record007_frame003_links_0064)
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0358
    Papers.RationalityTen.SharedFrameCatalogue.group0358_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0435.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0435.count (({ width := 8, code := 0xa5a3a19f9e9d9a98969593928f8d8b8a898785848382817f7d7c7b7a7978757271706f6d6b6a68666462605f5e5d5c5b59585755545351504f4d4c4b4948464442413f3e3d3b3a3938373635343332312f2e2d2b2a29282625242221201e1d1b1a1915141211100b0a0906050403 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0435.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0435.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0435.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0435.localPairCheck (smallEmbedding record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record007_frame004_links_0000 record007_frame004_links_0064)
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0435
    Papers.RationalityTen.SharedFrameCatalogue.group0435_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1ba6d13648314d86eb6e55728ad3dc9d24d7a66932697e4b825892ae9554a6a50926292348e245921490747e23b51cc8df3fd9ca0d3264d2f496c8b3e56129e94609fe4f826512688ee46722c90f08383ef1ef8f586f43431980bc859c2a91480a244b622b10407e03d41cd0d686002e01670ab854029214209d84d025e12808d043c21610307e03e01e00e807103701b20d204f026c12609103d81e00e006e013009004602000f807802200f007002c014009 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x344e61c8d8f31a607b97696ccd91af7582aa53ea5945e7fcfe9eb36266cb9957282464898d918e2e45583af7ddbba7714dcdb3b4d67cca98d3195f4bb16dace58eae14f295520a353825148a8a10da073f07d0ed1cb3786bcd39993045d8b796b2c8578aa14a27e4cc9511f20a3c0758e01ac34c638be1682a85389c1062043e87b0d61a43206204c0901182003e0780880f01c02c05009 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1c7edb068bb2e1962caa652327592cc916452b5558eab95582ab1548a9d4cc25d92a693c49a23951868a0444a20509684641ea0d906066f3309968ca864a32298fcabe54329a94b4a284d225b12a094048723391808b64562290c7c6122fb1770b744fc26812d0934478233115888c4382150d106482fc14309c845c20c0fc06d03480f607102f01700b605902b8158084038012809004602000f807801e00e0068028012008002000c002000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x7337006d069b69368d68367766c66565859c58b57956756555a54f4ec4de4cb4bb4b848f47846545545042441d40e4053fd35c34a3403373233213162ac29c29228c27624a23522c22420d1ee1df1d51cc1c417116916316115d13d13512f12d12912612011611110e0f60f10eb0d70d10c40bd0b70ab0a907306a05705505405205004f04103802502402302001f01e00f00e00d00a009008004003001000 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1a4acd163d30a983ac0f601afd57dcbea5eaaa2d4e8a605242909448a114b5a52125891548422c111a87142da14100e7f83ee1f18f666883359984cb663c3191884b1456e2b29580a824f926d93489984ad24491bc8be4502220d8869833a1948c5c5702a31488a044de26012588d044420e0dc86c03341600a704802160fe06b83240f607102f01700b605902b8158084038012809004602000f807801e00e0068028012008002000c002000 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record009_frame003_links_0000 record009_frame003_links_0064)
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
def record009_frame004_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x7026d76a768467e67a67767367266e6675ce5c65c05b85b55ad5a854653152951b5164ed4e34d14c34be4a149c49348f48c3bb3b23af3aa3a139d39932831b3183152ff2dc2cf2c92c62b02a229b2962932912091f91ec1e81e01b21a219519018a18417c17417016c13712f1220fc0f40df0d20ca0b50ae07706f05c05a05905705505404103802502402302001f01e00f00e00d00a009008004003001000 } : Fields).get c.val)
theorem record009_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record009_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record009) (record009.maps 4)
      (record009.inverseMaps 4) record009_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record009_frame004_links_0000 record009_frame004_links_0064)
theorem record009_frame004_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 4 :=
  of_group record009 4 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record009_frame004_indices record009_frame004_graph record009_frame004_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (Fin.cases (record009_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc1d601afb94fea6853024b123c903438a16508c83440fa038fec7dc3e31d78de26a734c9a20cf866b330965caf65652ab151ca104ea26912b894449424111cc8be4501c60db06c435419d8b8c5842b81528a044de25d12388d04441b90d4065c30c1760b1854024210e080032412807002e016c0ae05602a80e407002a013009004602100f807803a014008003c01c00b00500240100040018008002000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x695b029568a8c53124791f48e746b22fd06081c4061fecfd27db3da9e94dac5802ac14b87d43c61d98e887162fc1740b6058e2b51538a044e223910788204021fa0f987b03c61dc0e106d034c1970c886283021730b6054828813d09a84a024211907f03d81e00d503881840ba05c02d815c0ac05501c80a404a024011807c03c01d00a8050022010007803801800a004802000a0040018008002000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6cf66b5eb5db5ce53d52a52551e50e4c94bd4b14a749a49147946d4313b03a23943012f22eb2e42d428f28327726a25f25723c2322091e11d91d01c81bf1b91b41ad19017f17016515f15714d14013712211611010c1010f90f20da0d40d00b406f05f05b05a05905505405303902902502402301f01e01d01501401101000f00e00c00a009008005004003002001000 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record011_frame002_links_0000 record011_frame002_links_0064)
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x34b9814a5f527a8e936c94949aa48521e8fd47520c103c80c3fd9fa4fb47c93d99e8cdac52b28d94189044152008fb47b63c91db0bf05d42d81638ad454c29513f89bc47220f10408043f41f30f6078c3b81a60cf065c32218a0c105ec2ce1600ac854829614409e84a024211808884282060f707803500d606a03101840ae05602a80cc06402a014807c03c01d00a80500220100078038014009004001c00c005002000c004000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
def record012_frame002_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa539d49038f48e789384683a82d81f80c7f975073a7267137006ee6dc6c46b166a59d58f58253e4fb4f24e74dd4cf4c04364244144043f53e73d93c33b437932d3203133052f52e72d72cb25a24823822821a2081f91cd1c21ba1ae1a019118315614613512911a1090f30e80b306906806005f05505405303303202a02901f01e01d01501401101000f00e00a009008007006005004003002000 } : Fields).get c.val)
theorem record012_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record012_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record012) (record012.maps 2)
      (record012.inverseMaps 2) record012_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record012_frame002_links_0000 record012_frame002_links_0064)
theorem record012_frame002_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 2 :=
  of_group record012 2 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record012_frame002_indices record012_frame002_graph record012_frame002_links
def record012_frame003_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x2fbd6a4a5f527a8e53aa97f4b72571296939496a1c50bc84841a207d0147f53ed1f10ebc66032a990cbd45a92cd1634afc5712b313489864b0251125090a47222e91388023ad1cd8e306f636c1b10d406762b81538a4c50226f12d09204201fd0f707803a21c30dc86182ec1640a7850026011108083200d606a03101840ae05602a80cc06402a014807c03c01d00a80500220100078038014009004001c00c005002000c004000 } : Fields).get c.val)
theorem record012_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record012_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 3)
      (record012.inverseMaps 3) record012_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record012_frame003_links_0000 record012_frame003_links_0064)
theorem record012_frame003_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 3 :=
  of_group record012 3 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record012_frame003_indices record012_frame003_graph record012_frame003_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (Fin.cases (record012_frame002_supported hcells) (Fin.cases (record012_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc7a60eb00d7dcbea5302961448a11496248520489e43da1c50ce8454071f70f8c7b33789a64cf866132718c8c425ed2cb95ecaca5542a31464a104f9275136c9a44c025692088be4502220d8869e33c1948c5c5c62c215c0a9450226f12e88d044420e0f0070c3721ad0cb058c2a2120087035c19207002e016c0b005702b010c0720380130090046021010007c03c014007803801a00b0050024010005002000c002000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x695a98944ea134dca4c92188e746823090c884241820810127b53d29e5ca5c4f326f92147fc3d81d98e7071c3301870bf05d82d514089c44c623910407e83d81dd0eb87403761ad0d3067832218a0b985b02ca1600ac854829614409e84d025a11307e83dc1b40d503d81c00bc05c02d81600ae05602180e004c024011808003e01e00a805002200f007003401600a004802000c005002000c002000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0xc8d696ccd93af34e293511a033ea63cb394b272474608b314ddbbab74ae25a6b3e654c6d8b2ec5b6b39622b952aa414626e45086d039f13d877ce59bc35e690ca1872ec5bcb49632b8548a393c26248c8c0ea19e3185189b0d61902a0520a21382684c07c0d8130240460800f81e02a0500880f01c0340580a0120200300500800c00800 } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record014_frame002_links_0000 record014_frame002_links_0064)
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
def record014_frame003_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x878ed5d4ba5728db5b2357698d219431c62ac3d812e45c0b79362604b892d10a164127f0fc9db3a2724e09b833665cca9822ba550a593d2724d09391d232448839021ea3cc788ed1d43906f8db1b0340648b61522984a0920d61882905009e1302584a07a0d8130240460800f81e02a0500880f01c0340580a0120200300500800c00800 } : Fields).get c.val)
theorem record014_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record014_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record014) (record014.maps 3)
      (record014.inverseMaps 3) record014_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record014_frame003_links_0000 record014_frame003_links_0064)
theorem record014_frame003_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 3 :=
  of_group record014 3 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record014_frame003_indices record014_frame003_graph record014_frame003_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (Fin.cases (record014_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x697297d4729b649aa43d1d48cf45822750c8842418202cfb47b33d19e58a5650524110047b63b61cd8df06d23301870bf05ae2a613f89bc4c423910407e83d81dd0eb87403761ad0d3065830417c0b305802b21520a5851027a128090846021410307e03dc1b60d403d81ac0d406203081600ae05602180cc06402a014808003e01e00a805002200f007003401600a004801c00c005002000c004000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xd576933461a14d055582a89288936470a34d1988c645e22dd1608aa451226512488d3939ad0d2267232e9748abe53c28e94209904c125d12cc95a4a624e925892248a24091f48ea46f2358c6460c29913d09ac4b023c116886841c1e40db065c3101750ac852826e12b08083e01e00e9071036c1a807003581a80c205c02d80e407003501980c80540290130090046014007803801600a004802000e005002000c004001 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x86582281a81480f80875d6e46d26c66bc6af6755ec5dd5cd5bd5ab59959058858057857056255a55754e54653e53152a52247b3f23e33d33c33b136f2f62e42d82ce2c12b62ad2a529d29528d27f27727426b26325b24e24723f2201d81d01c91c31bd1b81b11a91a219a19118517e17a17216a16315815014914613f13713012811f11310c1081000f80f10e60de0d70d50d10cd0c90c50c109409308e08d08c07107006b06a06902a02902402302201501400f00e00d } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1106.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1106.count (({ width := 10, code := 0x79dcf731ca725c66d59d6699865d9461d6e5b16a599625815e5715a5615654d515414e5314a51d4550d314611645110431033ace8398e5388df374db364d7354d2340cf334cb324c6310c22e8a227c9d2709925894248902388c2248721884208801f47b1e4781d8741c8701b86b1a468198641885f1745b168591605715855104400ec3a0e42c0ac260942405c160441003c0801c0200400 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record017_frame002_links_0000 record017_frame002_links_0064)
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1106
    Papers.RationalityTen.SharedFrameCatalogue.group1106_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
def record017_frame003_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1102.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1102.count (({ width := 10, code := 0x8ea2287e1d87219821f07b5eb7a9e7769c16f9bc6e1b36c1ae6ada8695a26759a6659664d906318a621765755a5615453d454b52a4a1274912147d1c4651644d0e42d0a41d04404fd3ecf93c4d9358d434cd0334cb320c5308bf2e8b72d8b32c0ad2a4a7294a42889f27099258912388d22887210801f87c1ec7a1e4781dc76188611705b1684d13047118450a82909023088150500f0380d } : Fields).get c.val)
theorem record017_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record017_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record017) (record017.maps 3)
      (record017.inverseMaps 3) record017_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record017_frame003_links_0000 record017_frame003_links_0064)
theorem record017_frame003_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 3 :=
  of_group record017 3 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1102
    Papers.RationalityTen.SharedFrameCatalogue.group1102_facts record017_frame003_indices record017_frame003_graph record017_frame003_links
def record017_frame004_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x2654ad94b27a4d4958d30c61542183904e003ba768ea5cf39470ee01bd3756dedadafb566a8d35a3b41670cd197b07582ae958aa5536a09252424768d51622443885d08a0d4107ecf99f13d478cef1d53a2730dd98a3085f8bd9782e85b8b49622b6554a494027c4dc9892a23c464899102164107e8f71e23946e8da1a6330630ba16a2bc568a71402744c8951042043e07b0f419c330620c21801482804808c1101502803c0700d } : Fields).get c.val)
theorem record017_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record017) (record017.maps 4) (record017.inverseMaps 4) record017_frame004_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record017) (record017.maps 4) (record017.inverseMaps 4) record017_frame004_indices (Fin.ofNat record017.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record017_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record017) (record017.maps 4)
      (record017.inverseMaps 4) record017_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record017_frame004_links_0000 record017_frame004_links_0064)
theorem record017_frame004_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 4 :=
  of_group record017 4 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record017_frame004_indices record017_frame004_graph record017_frame004_links
def record017_frame005_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0653.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0653.count (({ width := 8, code := 0xd3d0cecdcccac7c4c2c1c0bebdb9b7b6b4b2b0aeadacabaaa7a5a4a2a09f9d9c9b989492918f8d8b8886858482817f7e7d7c7b7876757371706e6d6c6b6866656462615f5e5d5c5b5856555351504e4d4c4b494847464542403f3d3b3a38373635343332313027262322211b1a1716150f0e0b0a090605020100 } : Fields).get c.val)
theorem record017_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0653.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0653.localPairCheck (smallEmbedding record017) (record017.maps 5) (record017.inverseMaps 5) record017_frame005_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0653.localPairCheck (smallEmbedding record017) (record017.maps 5) (record017.inverseMaps 5) record017_frame005_indices (Fin.ofNat record017.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record017_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0653.localPairCheck (smallEmbedding record017) (record017.maps 5)
      (record017.inverseMaps 5) record017_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record017_frame005_links_0000 record017_frame005_links_0064)
theorem record017_frame005_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 5 :=
  of_group record017 5 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0653
    Papers.RationalityTen.SharedFrameCatalogue.group0653_facts record017_frame005_indices record017_frame005_graph record017_frame005_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (Fin.cases (record017_frame003_supported hcells) (Fin.cases (record017_frame004_supported hcells) (Fin.cases (record017_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x6abb429a08cfd67ab3b9704ab0550aa3542c94449aa4851de8e8470a3691a68cc463a3011528a244ca24911c7273391978c966393141748a3a50927b13909a64c826092e89664ad253127492c491245120c8fa47523791a480c3191828bc45722a914c8a284f426b12b892043a20e0f0875838c1b60d3865c3101740b284e82560fe07b83c01d20e206e03500d606a02e016c07203801980c806202a0148090046022007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x68066065c65865264b6035ab5a259756450c5064fb4d64d14cc4c64c14bc4b84b249d49748f48948542a3d43c93bc3b23a538733132631e30f3022fa2f52f12ec2e62e12d72d12ce2c72c22bd2b62b22ad28a2132091fc1db1d51cc1c41b91b11a019617c17315214b14613e13412c1211121080ed0e50c20bb0b70b20ab0a509e06806705a05903803703203103002a02902402302200f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
def record018_frame003_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x63e2fc17d2bd35dd2e915d2a5f528a8ed3b692c48ea41518a8b3450a2410fc87243621550187f73ec9f0cf766f13301948c8062f30f17a8aca5572a214d8a5051c28593f09da4de26992fc9584a524b921c8e845c22690f48083621a98cf860c2f41718b4c5842b81520a404b624910687f43dc1e00e8870c3721a70ca05982a211e08783fc1e40e506c831c0d606a02e016c07203801980c806202a0148090046022007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record018_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record018_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 3)
      (record018.inverseMaps 3) record018_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record018_frame003_links_0000 record018_frame003_links_0064)
theorem record018_frame003_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 3 :=
  of_group record018 3 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record018_frame003_indices record018_frame003_graph record018_frame003_links
def record018_frame004_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x7ad77276e7677607596da67166965861f5b65ae59d57c57556e56756055b55755053953252852151e47b40f4023f13e63db3ae34233532431930e3073002f92f22eb2e62de2d72d22cb2c52be2b52af2aa2802041f61eb1cb1c31bc1b51ae1a819d19317c17015514b14313c13512e12811d1130fc0f00d50ce0c90c30c00be0b706b06a05c05b03903803303203102a02902402302200f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record018_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record018_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record018) (record018.maps 4)
      (record018.inverseMaps 4) record018_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record018_frame004_links_0000 record018_frame004_links_0064)
theorem record018_frame004_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 4 :=
  of_group record018 4 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record018_frame004_indices record018_frame004_graph record018_frame004_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (Fin.cases (record018_frame003_supported hcells) (Fin.cases (record018_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xabea5197f9068d98c68947f77e17d079b79078076f7607507377236c66b36a36195a057356453f4bd4ad49f47546d4604524444364214113c53b63aa3792e72d82cc2be2ac2a029628627526725a22821a1e71d91cb1c21ba1ae1a019118317116313712b0fd0bf0b406f06e05a05905705605505403903802402302102001f01e01501400f00e00d00c00b00a009008006005004003001000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
def record019_frame002_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0253.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0253.count (({ width := 9, code := 0x2a952a2d02793a9b4c25f2d94496451f8e46a31158742e12fe7cbd5e6ef74ba1cce16f36db0d569b459cc7623095c9b4ca612e964a2451c8b4421906823d9e0ea74391bcd86933188be5a2c9508e441e0ec6833188c05e2e1409c401f0e870361a088401e0e06830160a048200c050200c0200 } : Fields).get c.val)
theorem record019_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record019_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record019) (record019.maps 2)
      (record019.inverseMaps 2) record019_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record019_frame002_links_0000 record019_frame002_links_0064)
theorem record019_frame002_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 2 :=
  of_group record019 2 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0253
    Papers.RationalityTen.SharedFrameCatalogue.group0253_facts record019_frame002_indices record019_frame002_graph record019_frame002_links
def record019_frame003_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0149.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0149.count (({ width := 9, code := 0x275389649e47218ec5e2d1487c32130681c05fefc7abc9e0e670b75b6d768b419cc96330d80bd5dae56caf562a93c8c45a29128843211027e3d9e4ec75371acd06732988be5c2c958a64e2692076381a8d05c2d158a85228128903c1d0d8683218088401e0e06830160a048200c050200c0200 } : Fields).get c.val)
theorem record019_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0149.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (smallEmbedding record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (smallEmbedding record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record019_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (smallEmbedding record019) (record019.maps 3)
      (record019.inverseMaps 3) record019_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record019_frame003_links_0000 record019_frame003_links_0064)
theorem record019_frame003_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 3 :=
  of_group record019 3 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0149
    Papers.RationalityTen.SharedFrameCatalogue.group0149_facts record019_frame003_indices record019_frame003_graph record019_frame003_links
def record019_frame004_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1c5ad2b59fa98944ea134dca39d1aa8c244421d90c885242120c10368093da9e94f2e60b29713cc9be4851d98e8471c3541a10cc063c30e17e0b9c5aa281138898c4721ec0f207743ae1d00e487083761b40d6869832218a0b985b02ca1600ac854829614409e84d025a11a08983f41b40d503881c00b805b02c81600ae05601c80e0048023010808003e01e00a805001e00e006803001600a004802000c005002000c002000 } : Fields).get c.val)
theorem record019_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 4) (record019.inverseMaps 4) record019_frame004_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 4) (record019.inverseMaps 4) record019_frame004_indices (Fin.ofNat record019.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record019_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 4)
      (record019.inverseMaps 4) record019_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record019_frame004_links_0000 record019_frame004_links_0064)
theorem record019_frame004_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 4 :=
  of_group record019 4 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record019_frame004_indices record019_frame004_graph record019_frame004_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (Fin.cases (record019_frame002_supported hcells) (Fin.cases (record019_frame003_supported hcells) (Fin.cases (record019_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x715b4ad684a624db239d1a68c0456a269110876432214908483040ea02cf6a7a530714b89043b31cf8e306f23661aa0d0866031e1870bf05d22d714089c44721ec0f207743ae1d00e487083761b40d6869833a1960b985b02c01590a9052c28813d094048423411306d83540c406102e016c0b405902c015c0ac02a0148090046022010808003e01e00a805001e00e006803001600a004801800a0040018008002000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0259.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0259.count (({ width := 9, code := 0x87c3205007cbddeaf378bbdd8e97338dc0dd6db5d96c7602f566b258ac15eae55aa14aa24fa71369846a29088341205007f3e9ecf2773a9cce47033190be5d2d964ae552893c9a4b1c0d0502713094482311084401a0c8602e160a8502612088401e0e06830160a048180a04018080200 } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0259.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record020_frame002_links_0000 record020_frame002_links_0064)
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0259
    Papers.RationalityTen.SharedFrameCatalogue.group0259_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
def record020_frame003_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0257.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0257.count (({ width := 9, code := 0x773b1cce46eb6db2d76ab4da2cf66b2d92c762b096eb4582b546a250a813e9e4e26930964a249228f42a0d007f3f1f4f87b3c9dcea73389bcdc6c31180b85a2c158a8522713094481d0dc582b150a4502713094481c0d86832180b8582a14088401e0e06830160a048180a04018080200 } : Fields).get c.val)
theorem record020_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0257.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record020_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (smallEmbedding record020) (record020.maps 3)
      (record020.inverseMaps 3) record020_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record020_frame003_links_0000 record020_frame003_links_0064)
theorem record020_frame003_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 3 :=
  of_group record020 3 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0257
    Papers.RationalityTen.SharedFrameCatalogue.group0257_facts record020_frame003_indices record020_frame003_graph record020_frame003_links
def record020_frame004_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0255.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0255.count (({ width := 7, code := 0xc78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record020_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0255.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0255.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0255.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record020_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0255.localPairCheck (smallEmbedding record020) (record020.maps 4)
      (record020.inverseMaps 4) record020_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record020_frame004_links_0000 record020_frame004_links_0064)
theorem record020_frame004_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 4 :=
  of_group record020 4 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0255
    Papers.RationalityTen.SharedFrameCatalogue.group0255_facts record020_frame004_indices record020_frame004_graph record020_frame004_links
def record020_frame005_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0256.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0256.count (({ width := 7, code := 0xc78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record020_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0256.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0256.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0256.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record020_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0256.localPairCheck (smallEmbedding record020) (record020.maps 5)
      (record020.inverseMaps 5) record020_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record020_frame005_links_0000 record020_frame005_links_0064)
theorem record020_frame005_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 5 :=
  of_group record020 5 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0256
    Papers.RationalityTen.SharedFrameCatalogue.group0256_facts record020_frame005_indices record020_frame005_graph record020_frame005_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (Fin.cases (record020_frame003_supported hcells) (Fin.cases (record020_frame004_supported hcells) (Fin.cases (record020_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0259.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0259.count (({ width := 9, code := 0x2210d80bfdf2f776ba9cee470b79b4d669b459ecd6531988bf5e2cd64ac54a9946a04ea692e94492411c8c44a1d08833e9ecf2773a9ccda6b3499cc45f2e96cb2572a9449e4d259208a421f8f06e33168b0562a1409c4c250f8783a1c0d0643017088401e0e0602c14090401c0c050200c0401 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0259.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0259
    Papers.RationalityTen.SharedFrameCatalogue.group0259_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
def record021_frame002_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1aaed0a5be2ac1420944477a3a11c28da469a3311868bc45ba2c11528a244ca24911a7273391748a3a4c826092e89664ad253127492c491245120c8fa47523791ac80631915c8aa453228a13d09ac47822d10e88383c81d60e306d834e1970c4056429413a09584041ee0f007483881b60d403881c00d606a03101840b805b01c80e006603201500a404802300a805001e00e006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record021_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record021_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record021) (record021.maps 2)
      (record021.inverseMaps 2) record021_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record021_frame002_links_0000 record021_frame002_links_0064)
theorem record021_frame002_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 2 :=
  of_group record021 2 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record021_frame002_indices record021_frame002_graph record021_frame002_links
def record021_frame003_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1c60d3159fa97d36c8e7445a1e50ce855422a0cd0348083ff1fb0fb87cb3d91e88f3060b29592087663571a28ccc64231117f8b985a82ca15c0aa052e27e13709904721ec0e487083761b40d6869832218a0c185f02ce1600ac854829614409e84a024211a08983f81ea0ee07383801b20d303881c00d606a03101840b805b01c80e006603201500a404802300a805001e00e006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record021_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record021_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 3)
      (record021.inverseMaps 3) record021_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record021_frame003_links_0000 record021_frame003_links_0064)
theorem record021_frame003_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 3 :=
  of_group record021 3 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record021_frame003_indices record021_frame003_graph record021_frame003_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (Fin.cases (record021_frame002_supported hcells) (Fin.cases (record021_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0xaf15d2b7569acb586ab553a9d52268ccd98f30a5f4ba95f2b253ca18c91762ac4f89310e1cc3585b09a0fc1882102a023fe7e8fc1f43e17b8f61ea3d0798d4da4b44678ce198b2a592af95daae552a894da834ec9c53625e4a892921a384668b9141c93786dcd91a4334640bb16b2d056cab14f29050c9c13325c4a08a9092043e87a8ee1ce38c6c8d219c320628bb1682c0550a7132224340590680cc1903104a090118220160280480800a01001802 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
def record022_frame002_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1092.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1092.count (({ width := 9, code := 0xbd5e2ed74b95c6dd6db5da6ad54a95429d4da55268f459dce66f3599cca5f2e964aa51269248a411f8e46e33178ac52271288bf1f0f77a3cde0ed6fb6db4d76b34da0c962b0d84be5dae16cb358ac15ca04e26932954923d128542205007d3d1e0ea73391c0d6673318cc45f2e168ae552a148a24e2612c9248200d858230c05c2c150803c1c0d0401c0c05018080200 } : Fields).get c.val)
theorem record022_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record022_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record022) (record022.maps 2)
      (record022.inverseMaps 2) record022_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record022_frame002_links_0000 record022_frame002_links_0064)
theorem record022_frame002_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 2 :=
  of_group record022 2 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1092
    Papers.RationalityTen.SharedFrameCatalogue.group1092_facts record022_frame002_indices record022_frame002_graph record022_frame002_links
def record022_frame003_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1083.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1083.count (({ width := 9, code := 0xbd5e2ed74b95c6dd6db5da6ad54a95429d4da55268f459dce66f3599cca5f2e964aa51269248a411f8e46e33178ac52271288bf1f0f77a3cde0ed6fb6db4d76b34da0c962b0d84be5dae16cb358ac15ca04e26932954923d128542205007d3d1e0ea73391c0d6673318cc45f2e168ae552a148a24e2612c9248200d858230c05c2c150803c1c0d0401c0c05018080200 } : Fields).get c.val)
theorem record022_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record022_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record022) (record022.maps 3)
      (record022.inverseMaps 3) record022_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record022_frame003_links_0000 record022_frame003_links_0064)
theorem record022_frame003_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 3 :=
  of_group record022 3 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1083
    Papers.RationalityTen.SharedFrameCatalogue.group1083_facts record022_frame003_indices record022_frame003_graph record022_frame003_links
def record022_frame004_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0x9b335a684c99893025bcb495f29e24c458810f61bc3084f0920e4177c8f79eb3d079af1ddf3ba76aeb5d2b9f738e5dc7b886fededbab6f6ced8db035a6a6b856a2cf590b115f2b94ec9ad3425e4b09552723d45e8a912a17422825009f63e47b0f319f326634c417a2e65a8ab9502985089e1362664bc9211d234450820f81e43b0748e31ba364688cd190310600b81662c0558a712c21c3585e0640c41802f04808c110210160280480800a01001802 } : Fields).get c.val)
theorem record022_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record022) (record022.maps 4) (record022.inverseMaps 4) record022_frame004_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record022) (record022.maps 4) (record022.inverseMaps 4) record022_frame004_indices (Fin.ofNat record022.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record022_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record022) (record022.maps 4)
      (record022.inverseMaps 4) record022_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record022_frame004_links_0000 record022_frame004_links_0064)
theorem record022_frame004_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 4 :=
  of_group record022 4 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record022_frame004_indices record022_frame004_graph record022_frame004_links
def record022_frame005_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0989.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0989.count (({ width := 8, code := 0xa3a2a1a09f9e9c9b9a9998979695949391908f8e8d8c8b8a8988868584838281807f7e7d7b7a79787776757473706e6d6b6a6968656362605f5e5d5a585756545352514f4e4d4c494746454342413e3c3b3938373635333231302d2b2a28272625242221201f1e1c1b1a1918171615141211100f0d0c0b0a0807060503020100 } : Fields).get c.val)
theorem record022_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0989.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0989.localPairCheck (smallEmbedding record022) (record022.maps 5) (record022.inverseMaps 5) record022_frame005_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0989.localPairCheck (smallEmbedding record022) (record022.maps 5) (record022.inverseMaps 5) record022_frame005_indices (Fin.ofNat record022.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record022_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0989.localPairCheck (smallEmbedding record022) (record022.maps 5)
      (record022.inverseMaps 5) record022_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record022_frame005_links_0000 record022_frame005_links_0064)
theorem record022_frame005_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 5 :=
  of_group record022 5 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0989
    Papers.RationalityTen.SharedFrameCatalogue.group0989_facts record022_frame005_indices record022_frame005_graph record022_frame005_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (Fin.cases (record022_frame002_supported hcells) (Fin.cases (record022_frame003_supported hcells) (Fin.cases (record022_frame004_supported hcells) (Fin.cases (record022_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
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
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xa7f5342981474a24508a5fd2dc95c4a5a4e525a91448223b51ae89e43da1c50bc84941a207cd1066b3309910c646212d49668b1a57e2b89598aa654829c94ac9f24db269130c9624a224a0eb473638c1bd8db06c433d1948c5c5c62c215c0a9c528281137891c46822210707f43dc1e00e8870c3721980c305d82c814f0a004c023e11103d81880b005702b015408602a010007c03c01d00a804402000f007003401600a004802000c005002000c004000 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
def record024_frame002_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x2edb9ee4b66d5b46afaaea7a8e9fa6e90a2a839f2739ba6b98a5c9524c7edf77d5eb799e1715c3705bf6f5bb6c1ad69da165d93645875fd785c5384d1304b529499174450b400fb3e4f23ace6384d4340cc324c5304bd2e8b62cca527c9923c8820c7e1e474140430e4380dc360d0270741c06c1a054110400f0380d02c0a02408018050100300800 } : Fields).get c.val)
theorem record024_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record024_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record024) (record024.maps 2)
      (record024.inverseMaps 2) record024_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record024_frame002_links_0000 record024_frame002_links_0064)
theorem record024_frame002_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 2 :=
  of_group record024 2 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record024_frame002_indices record024_frame002_graph record024_frame002_links
def record024_frame003_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xaa053ba989476a27509a52526a921487a3f51d48cf46222c113a86442120c103c80d3fd9fa4ad8543297141c9e64df20a90047da3db1e48ed87363901be0da466030e17e0ba85b22c715a883c4102010fd07cc3d81de0eb87403761ad0d306783301910c505e82e616c0b285802b21520a5851027a12f0940484230111085040c1f80f703d81880b005702b015408602a010007c03c01d00a804402000f007003401600a004802000c005002000c004000 } : Fields).get c.val)
theorem record024_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 3) (record024.inverseMaps 3) record024_frame003_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 3) (record024.inverseMaps 3) record024_frame003_indices (Fin.ofNat record024.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record024_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 3)
      (record024.inverseMaps 3) record024_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record024_frame003_links_0000 record024_frame003_links_0064)
theorem record024_frame003_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 3 :=
  of_group record024 3 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record024_frame003_indices record024_frame003_graph record024_frame003_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (Fin.cases (record024_frame002_supported hcells) (Fin.cases (record024_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x30517f4bf05f4af41774ba454129ad4c2a3d513284d2bc93b497241d1de8d9462a2cd14289043f21c90b484c41ba088ffe7ea3ea1ef8d0a6683301948c8262f30f1628adc5652ab9514a6c52828e142c9f84ed26f134c97e4b4252925c90e46c22e113487a38e1b70d8c68032c18d0c185e82e31698b0857029414089bc48a23211008303fa1ee0f007443861b90cc06182ec14d09f04b823a10f07f83c81ca0d606501c40c403901a00cc0640310150094048023011005401800b00500240100060028010006002 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
def record025_frame002_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x347da22d0a68233f19eacee578ab2956ca8f53f29b130a95e4a5248d224900477a3a11c28da469a3311868be45ba2c114889d44b223cd466813391978c986393141538a5851d28493dc9c84d326413049744b3256929893a498248922890647b23a91bc8d235a1978c705e62dd1650ae455229914509e84d624c11e08b44141fc0f707803ac1c60db069c32e1880b4856429412708c842c1fa0f707803a41c40db06a81c40c403901a00cc0640310150094048023011005401800b00500240100060028010006002 } : Fields).get c.val)
theorem record025_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record025_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record025) (record025.maps 2)
      (record025.inverseMaps 2) record025_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record025_frame002_links_0000 record025_frame002_links_0064)
theorem record025_frame002_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 2 :=
  of_group record025 2 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record025_frame002_indices record025_frame002_graph record025_frame002_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (Fin.cases (record025_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa89a82a7aa70a63a55a43a36a28a0393f93792e9239169098f88eb8dc8bc84783c82f82180e7fc7e67d57c47a079c79378377276375373e72a7166fb6f66e46d26bf6ab5da5d45cb5c25b45a359258557655a4fc4f44e94df4d14c34b24a44954784764704634554474394284184073f03ec3de3d03bf3af2a029628627526725a2492392281c21ba1ae1a01911831731651560f10e60d90cc0be09f09506c05d03602701200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
def record026_frame002_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb33b29b22b19b0baffaf1adbaccaab9da9cb9c29b89a59969889729639468c88b68aa89e88c87c86a85183d81c8138037f87ed7d77c37af79978476976374f73872170962d61f61460e6005f55e75d85cc5b25455355295225135064f74e54d74bc4b64a749c49348547a46c45c44d4384344234154073f62c72b72ad2a12932862752652551e21d51cd1c41b51a81981871781020f50e80da0cb0a809906e05f03602701200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record026_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record026_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record026) (record026.maps 2)
      (record026.inverseMaps 2) record026_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record026_frame002_links_0000 record026_frame002_links_0064)
theorem record026_frame002_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 2 :=
  of_group record026 2 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record026_frame002_indices record026_frame002_graph record026_frame002_links
def record026_frame003_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x696b499a3ed18688b429a06cfc67ab3a962ab03578ab79594ab6551aa3d4fca5e4d4a65d30a9724af252926e92348923c91de8e8470a3691a68cc462a2f916e8ae455a29113a8964479b28d746a934b9a1ccf066532918fcc405752b29550a8453229194409fa4ea26593209824ba25992b494c49f24c124491048523f91e48e646d15c8aa453228a13d09ac4b624c11e075838c1b60d3865c3101780b485641ee0f007483881b60af04d81b80be036013804801800b00500240100060028010006002 } : Fields).get c.val)
theorem record026_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record026_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record026) (record026.maps 3)
      (record026.inverseMaps 3) record026_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record026_frame003_links_0000 record026_frame003_links_0064)
theorem record026_frame003_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 3 :=
  of_group record026 3 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record026_frame003_indices record026_frame003_graph record026_frame003_links
def record026_frame004_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x73973473072a72472071b71470e70466a65d65664d64163862e6236156015bf5b75ab5a259759058357757055655354c54754153c53753152a52451c51951350c5054fe45244343b43442641d4134063fb3e639838f38237b36e36735a34d34532d32a32331e31831230d3083012fb2f32f02ea2e42de2d81f21e91e21d81d01c71bd1b41a915e15514e14413b13512911f1170cc0c50c00bc0b609c09106c05d03502701200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record026_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record026) (record026.maps 4) (record026.inverseMaps 4) record026_frame004_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record026) (record026.maps 4) (record026.inverseMaps 4) record026_frame004_indices (Fin.ofNat record026.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record026_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record026) (record026.maps 4)
      (record026.inverseMaps 4) record026_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record026_frame004_links_0000 record026_frame004_links_0064)
theorem record026_frame004_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 4 :=
  of_group record026 4 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record026_frame004_indices record026_frame004_graph record026_frame004_links
def record026_frame005_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0377.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0377.count (({ width := 9, code := 0xd6eb357aad4ea34da4d16831b8bc4e1f0b83c0dfaf776b4d9ecb63b0d7ebb5aabd4aa34fa6d2e9347a2d0a7f3b9d4e26d3499c823b1a8bc52230e8541a00f3783b5d4e772385bad969b49a0ce6632990c5612fd76ba5bad162af4522510874321508813f1a8d26833998ca643097894492411c8a43210e0662710848180b050241006028100602 } : Fields).get c.val)
theorem record026_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0377.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record026) (record026.maps 5) (record026.inverseMaps 5) record026_frame005_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record026) (record026.maps 5) (record026.inverseMaps 5) record026_frame005_indices (Fin.ofNat record026.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record026_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record026) (record026.maps 5)
      (record026.inverseMaps 5) record026_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record026_frame005_links_0000 record026_frame005_links_0064)
theorem record026_frame005_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 5 :=
  of_group record026 5 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0377
    Papers.RationalityTen.SharedFrameCatalogue.group0377_facts record026_frame005_indices record026_frame005_graph record026_frame005_links
def record026_frame006_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x68167c67566f66866065965264a6415b45ad5a059558c58057656b55f55251250b4fe4f34e84dc4d44cb4bf4b04ad4a74a149b49448d48748047947147046a46345c4563a739c39038137836e3623593503402f82ed2e12d22c92c02b32aa2a029128e28828227b27526e26826225b25425324d24724023a18f18717c17617216e16816315d12d12511a11210d1071020fe0fa0cc0c70c20be0bc0a309706c05d03502701200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record026_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record026) (record026.maps 6) (record026.inverseMaps 6) record026_frame006_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record026) (record026.maps 6) (record026.inverseMaps 6) record026_frame006_indices (Fin.ofNat record026.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record026_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record026) (record026.maps 6)
      (record026.inverseMaps 6) record026_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record026_frame006_links_0000 record026_frame006_links_0064)
theorem record026_frame006_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 6 :=
  of_group record026 6 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record026_frame006_indices record026_frame006_graph record026_frame006_links
def record026_frame007_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6d2b641af2d616a4b4c5a32d026753305596ab7551aa3d4f4a65529a8f9454a084a624e124891248023b51b48c7459a249116879433a15508a8334112040ffc7e43f09f44f827af3cf165cb0656f2ad9518a6251f28513d89a84182020fc07bc3cc1dc8e9872637f1af0d5c68a3331908c445fe2ee16e0b285602ad14e8a344f626a0e487083761b40d6869833e1980c885802b21520a5851027a13609784a01ea0ee07383801b20af04d81b80be036013804801800b00500240100060028010006002 } : Fields).get c.val)
theorem record026_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record026) (record026.maps 7) (record026.inverseMaps 7) record026_frame007_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record026) (record026.maps 7) (record026.inverseMaps 7) record026_frame007_indices (Fin.ofNat record026.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record026_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record026) (record026.maps 7)
      (record026.inverseMaps 7) record026_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record026_frame007_links_0000 record026_frame007_links_0064)
theorem record026_frame007_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 7 :=
  of_group record026 7 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record026_frame007_indices record026_frame007_graph record026_frame007_links
def record026_frame008_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x66b66566065a65364963f63762a61359258a58357c57456856055654a5384f24ea4e14db4d14c74bc4af4a549148e48748147b47346845f45844b43943742d42541a41238b38337b37436a36335834c3423302eb2e22d92d32c82bf2b42a629b28928627f27927326826225724d24323122f22521a21220a18f18918418017a17316c16615e13312c12712311d11610f1070ff0d20cb0c30bc0b609b08f06805903602701200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record026_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record026) (record026.maps 8) (record026.inverseMaps 8) record026_frame008_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record026) (record026.maps 8) (record026.inverseMaps 8) record026_frame008_indices (Fin.ofNat record026.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record026_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record026) (record026.maps 8)
      (record026.inverseMaps 8) record026_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record026_frame008_links_0000 record026_frame008_links_0064)
theorem record026_frame008_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 8 :=
  of_group record026 8 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record026_frame008_indices record026_frame008_graph record026_frame008_links
def record026_frame009_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0309.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0309.count (({ width := 8, code := 0xf4f2f0eeeceae8e6e4e1e0dedcdad8d6d4d2d0cdcccac8c6c4c2c0bebcb9b8b6b4b2b0aeacaaa8a5a4a2a09e9c9a98969492908e8c8a87868482807e7c7a78767372706e6c6a686664625f5e5c5a58564a49484746454443423b3a3938373635343331302f2e2d2b2a29281d1c110b0a0908070605040302 } : Fields).get c.val)
theorem record026_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0309.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0309.localPairCheck (smallEmbedding record026) (record026.maps 9) (record026.inverseMaps 9) record026_frame009_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0309.localPairCheck (smallEmbedding record026) (record026.maps 9) (record026.inverseMaps 9) record026_frame009_indices (Fin.ofNat record026.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record026_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0309.localPairCheck (smallEmbedding record026) (record026.maps 9)
      (record026.inverseMaps 9) record026_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record026_frame009_links_0000 record026_frame009_links_0064)
theorem record026_frame009_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 9 :=
  of_group record026 9 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0309
    Papers.RationalityTen.SharedFrameCatalogue.group0309_facts record026_frame009_indices record026_frame009_graph record026_frame009_links
def record026_frame010_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x84083a83482f82a82381c81681080571d71470a6fd6f36e86d96cd6c26a762561c6116035f75ea5d85ca5bc59d59858f58757f57756f56755f55654b54854053853052942b4224174093fd3f03de3d03c23a332f32631c30f3052fa2eb2df2d42b92b52ac2a429c29428c28427c27326826525d25524d2461b71b01a81a119919018818117914513e13612f12711e11610f1070d40d00cc0c80c40a909b06e05f03602701200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record026_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record026) (record026.maps 10) (record026.inverseMaps 10) record026_frame010_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record026) (record026.maps 10) (record026.inverseMaps 10) record026_frame010_indices (Fin.ofNat record026.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record026_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record026) (record026.maps 10)
      (record026.inverseMaps 10) record026_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record026_frame010_links_0000 record026_frame010_links_0064)
theorem record026_frame010_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 10 :=
  of_group record026 10 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record026_frame010_indices record026_frame010_graph record026_frame010_links
def record026_frame011_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0305.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0305.count (({ width := 7, code := 0xefdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record026_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0305.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0305.localPairCheck (smallEmbedding record026) (record026.maps 11) (record026.inverseMaps 11) record026_frame011_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0305.localPairCheck (smallEmbedding record026) (record026.maps 11) (record026.inverseMaps 11) record026_frame011_indices (Fin.ofNat record026.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record026_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0305.localPairCheck (smallEmbedding record026) (record026.maps 11)
      (record026.inverseMaps 11) record026_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record026_frame011_links_0000 record026_frame011_links_0064)
theorem record026_frame011_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 11 :=
  of_group record026 11 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0305
    Papers.RationalityTen.SharedFrameCatalogue.group0305_facts record026_frame011_indices record026_frame011_graph record026_frame011_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (Fin.cases (record026_frame002_supported hcells) (Fin.cases (record026_frame003_supported hcells) (Fin.cases (record026_frame004_supported hcells) (Fin.cases (record026_frame005_supported hcells) (Fin.cases (record026_frame006_supported hcells) (Fin.cases (record026_frame007_supported hcells) (Fin.cases (record026_frame008_supported hcells) (Fin.cases (record026_frame009_supported hcells) (Fin.cases (record026_frame010_supported hcells) (Fin.cases (record026_frame011_supported hcells) (fun j => Fin.elim0 j)))))))))))))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0x8c88b68aa89e88c87c86a85183d81c8138037f87ed7d77c37af79978476962b61d61360b5fe5f35e55d75cb5b454053052751c50e5014f14e14d34b64a749c49348547a46c45c44d43836e35b34e34433432230f2fd2ed2d32c72b72ad2a12932862752652551e21d51cd1c41b51a81981871781531411311211111020f50e80da0cb09906e05f04003602702602502402302201200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
def record027_frame002_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0x2fabdaf2bbae9b92ddb52cbafabbadeb3abeaba9ea2a6e94a323d8ea378d2318ba2a8921e85dfd7e9f77cdef7ade576dd1715c26fdbb6ddb36b9a768197561555494f52d4750d3b4cd27491214791a4591243908408df36cd734ccf32cc72fcb72989f2609322c872087d1e0711a05011c370cc270982509023088120300b02809020060140400c02 } : Fields).get c.val)
theorem record027_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record027_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record027) (record027.maps 2)
      (record027.inverseMaps 2) record027_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record027_frame002_links_0000 record027_frame002_links_0064)
theorem record027_frame002_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 2 :=
  of_group record027 2 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record027_frame002_indices record027_frame002_graph record027_frame002_links
def record027_frame003_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x4648bb15627c498870f21ac2d84907e0c410815011ff3f77e0fa1efb5e6b2d51a7b4a68acfd9cb32652b61682c9586af95dab3552a894928b5069ed3b2714d29792a2463b0744e49c13786dcd79a4334630c297d2ec5c0b59682c0558a7923238454879092043f07a8ee1c0364690ce1903085d8b41602a8430650ac0fc1b02704c094120230440480600b0140240400600a01001802 } : Fields).get c.val)
theorem record027_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record027) (record027.maps 3) (record027.inverseMaps 3) record027_frame003_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record027) (record027.maps 3) (record027.inverseMaps 3) record027_frame003_indices (Fin.ofNat record027.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record027_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record027) (record027.maps 3)
      (record027.inverseMaps 3) record027_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record027_frame003_links_0000 record027_frame003_links_0064)
theorem record027_frame003_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 3 :=
  of_group record027 3 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record027_frame003_indices record027_frame003_graph record027_frame003_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (Fin.cases (record027_frame002_supported hcells) (Fin.cases (record027_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x56dab5559cac75602ae5564aab5522a6d35a99b4c4a5e52ce9564a1a4c123c90547d23a11ac8c645a228d12087d435a148cf867533799a0cc265a3299930c8a63d2be15bcac45542a314e0a5251b28693dc9de4e226a931c9724ab24e123890046a1b68d7c69e33f1980c7c61c2fe1770b3057c2ae14f0a3c4fc26d12e893446222a111887042a2060f907803981b70d106382f816a0a304e825e12308b04241fa0f207303640f006e02f810006c027009004402000f007003401800b00500240100060028010006002 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
def record028_frame002_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x5892c015dcadb563aacd540a8c53da98534c9944c125bd2b694749a248121e8f5477a3a11c28da469a33118a8be45ba2b8d8e6b73531a50d08675331193cc786232b91588aa253f2979480a1a4fa27393389904c125d12cc95a4a624f92609224881bf8da86ae3411960c646082f016d0ae455229914509e84d625b12608f043620c0ff07c03c41d60e306d834e1970c405e02d215909c04a423610d07f83dc1e00e9071036c0f006e02f810006c027009004402000f007003401800b00500240100060028010006002 } : Fields).get c.val)
theorem record028_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record028) (record028.maps 2)
      (record028.inverseMaps 2) record028_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame002_links_0000 record028_frame002_links_0064)
theorem record028_frame002_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 2 :=
  of_group record028 2 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record028_frame002_indices record028_frame002_graph record028_frame002_links
def record028_frame003_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1091.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1091.count (({ width := 10, code := 0x9063d8ea378d2308b229896208420c8260680dff7edf87d1ef7b5e9799e3781dc761d5745cc699a46819d6699764990635885d9745c16d5a96758960575585555353d4c525465053f4f13749120471164490d42104400f83d0f03a8e6384dc360d4328c630cc02ecb82d0b02a8a62849c260942288620c801ec761c86f1b06715451120350b822048110400f0380d0300b02809020060140400c02 } : Fields).get c.val)
theorem record028_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record028) (record028.maps 3) (record028.inverseMaps 3) record028_frame003_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record028) (record028.maps 3) (record028.inverseMaps 3) record028_frame003_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record028) (record028.maps 3)
      (record028.inverseMaps 3) record028_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame003_links_0000 record028_frame003_links_0064)
theorem record028_frame003_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 3 :=
  of_group record028 3 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1091
    Papers.RationalityTen.SharedFrameCatalogue.group1091_facts record028_frame003_indices record028_frame003_graph record028_frame003_links
def record028_frame004_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1094.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1094.count (({ width := 9, code := 0xadd66b156aad52a34fa6d2a813e9ecee75399b4d2652f974b257299449e49229047611078341207027fbf9f8f977bb9daeb753a5cce571b81bcdd6e369b2d86ab51a4cf623017cba5bad162ae55295429f4da612a9247a2d0a83409f8f4783a1c8dc6b34194c45e2c158a851269289046218fc6c3317094421b09044200f07034180b050241006028100602 } : Fields).get c.val)
theorem record028_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1094.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record028) (record028.maps 4) (record028.inverseMaps 4) record028_frame004_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record028) (record028.maps 4) (record028.inverseMaps 4) record028_frame004_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record028) (record028.maps 4)
      (record028.inverseMaps 4) record028_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame004_links_0000 record028_frame004_links_0064)
theorem record028_frame004_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 4 :=
  of_group record028 4 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1094
    Papers.RationalityTen.SharedFrameCatalogue.group1094_facts record028_frame004_indices record028_frame004_graph record028_frame004_links
def record028_frame005_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x93e93592c9209139068f58e88d98bf84683a82d81f80c7f97e37d27c27a379c79378377276375373e72a7166fb5d95d25c95bf5b15a059058357355d4fb4f24e74dd4cf4c04af4a149347b4764704634554474394284184073f032d3203133052f52e72d92cd2be2a029628627526725a2492392282071f81e71d91cb1c21ba1ae1a019118317316515613512911a1090fc0f10e60d90cc0be07606c05d04003602701201101000f00e00d00c00b00a009008006005004003002 } : Fields).get c.val)
theorem record028_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record028) (record028.maps 5) (record028.inverseMaps 5) record028_frame005_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record028) (record028.maps 5) (record028.inverseMaps 5) record028_frame005_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record028) (record028.maps 5)
      (record028.inverseMaps 5) record028_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame005_links_0000 record028_frame005_links_0064)
theorem record028_frame005_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 5 :=
  of_group record028 5 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record028_frame005_indices record028_frame005_graph record028_frame005_links
def record028_frame006_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0xb716d2d8dadb53696d059db33646a153ba614a68ed13a0f3f2784da9ad346654be96d29e4f4949091b9e53c6786f01de3b7764ebdd5ba36aad41a334166ecb590b1861ebf17caf55deb956f2d158cafd59aa04608a11021b42481cfe9f23d8760e91cb3866f0d79a533c650bf17a2ec5bcb49632b8548a393c2624948d10c1e43a0710d819c310600b6158288348620aa0f01a0270240440800f01c0340600b0140240400600a01001802 } : Fields).get c.val)
theorem record028_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record028) (record028.maps 6) (record028.inverseMaps 6) record028_frame006_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record028) (record028.maps 6) (record028.inverseMaps 6) record028_frame006_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record028) (record028.maps 6)
      (record028.inverseMaps 6) record028_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame006_links_0000 record028_frame006_links_0064)
theorem record028_frame006_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 6 :=
  of_group record028 6 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record028_frame006_indices record028_frame006_graph record028_frame006_links
def record028_frame007_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0853.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0853.count (({ width := 8, code := 0x88878684838281807f7e7d7c7b797877767574737271706e6d6c6b6a6968676665636261605f5e5d5c5b5a5857565554535251504f4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1b19171513110f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record028_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0853.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0853.localPairCheck (smallEmbedding record028) (record028.maps 7) (record028.inverseMaps 7) record028_frame007_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0853.localPairCheck (smallEmbedding record028) (record028.maps 7) (record028.inverseMaps 7) record028_frame007_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0853.localPairCheck (smallEmbedding record028) (record028.maps 7)
      (record028.inverseMaps 7) record028_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame007_links_0000 record028_frame007_links_0064)
theorem record028_frame007_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 7 :=
  of_group record028 7 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0853
    Papers.RationalityTen.SharedFrameCatalogue.group0853_facts record028_frame007_indices record028_frame007_graph record028_frame007_links
def record028_frame008_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x526a8e9442a1250127c53c49d24e0a6cd26491b48123bd1bc8ca45c229d12688443c2181092835411a0490027ef3ef1f44c8e63230e9838bfe5ef2f09748b845b429f14a8a2a50527b93a89b44cc25f92c495049624211d08ce45a22610fc8644251a80ce86483151830bdc5d02d91650ac453a28a13c09b44c025212388e84442110ff87c83ca1d60e306d435019c0c806142f216d0aa850825e12208b041c1f20e906f03500f006e02f810006c027009004402000f007003401800b00500240100060028010006002 } : Fields).get c.val)
theorem record028_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record028) (record028.maps 8) (record028.inverseMaps 8) record028_frame008_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record028) (record028.maps 8) (record028.inverseMaps 8) record028_frame008_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record028) (record028.maps 8)
      (record028.inverseMaps 8) record028_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame008_links_0000 record028_frame008_links_0064)
theorem record028_frame008_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 8 :=
  of_group record028 8 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record028_frame008_indices record028_frame008_graph record028_frame008_links
def record028_frame009_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0351.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0351.count (({ width := 9, code := 0xc56230d84c1602fd7cbd5dee36eb5da2c960ae562a94ea652a9146a1d027b3a9bcca29118742e1105813fdf8f8793bdd8e972b85bad96ab419ccc653218ac25faf172b44ba5526914722d1085411f8fa7c3d9e4ee75399c4dc6c351a0cc6431988c25f2e96cb257299409a4a2391084401f0f06c351a0a45022088401e0e06830160a048200e06028100602 } : Fields).get c.val)
theorem record028_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record028) (record028.maps 9) (record028.inverseMaps 9) record028_frame009_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record028) (record028.maps 9) (record028.inverseMaps 9) record028_frame009_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record028) (record028.maps 9)
      (record028.inverseMaps 9) record028_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame009_links_0000 record028_frame009_links_0064)
theorem record028_frame009_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 9 :=
  of_group record028 9 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0351
    Papers.RationalityTen.SharedFrameCatalogue.group0351_facts record028_frame009_indices record028_frame009_graph record028_frame009_links
def record028_frame010_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x5642ad1540a8c53ba9894a0a3b513a82d292935490a43d1fa8ea46ba311160895445a1e50ce855422a0cd0448103ff1f90b285802b61560a8652e28e141c9e64d720a90047da3db1e48ed87463901be0d846ae3451998c846222ff1770b705942b010788204021fa0f987b03ca1de0eb87243841bb0da06b434c19f0cc064430217a0b985b02ca1600ac854829614409e84d825e12808c044421410307e03d41dc0e707003640f006e02f810006c027009004402000f007003401800b00500240100060028010006002 } : Fields).get c.val)
theorem record028_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record028) (record028.maps 10) (record028.inverseMaps 10) record028_frame010_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record028) (record028.maps 10) (record028.inverseMaps 10) record028_frame010_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record028) (record028.maps 10)
      (record028.inverseMaps 10) record028_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame010_links_0000 record028_frame010_links_0064)
theorem record028_frame010_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 10 :=
  of_group record028 10 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record028_frame010_indices record028_frame010_graph record028_frame010_links
def record028_frame011_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0xb8b702dd5b4b5f6aad1d9cb2b63693d1fa2d42e814fb9df39a6eccc98f2fe5b4aa941266464838f319dcb391716e15c037b6e8db5b335e5f0bc173adb5a2b295eab4554a614928a5029d936a664b4945242373b8754e71c63806e0d81a9344648c59842f85d8b71662be560a51462844f89d13525e4ac9291e230448861071f03c0748e11b4344648c21742cc3a86c0ba0fc1b0270240440800f01c0340600b0140240400600a01001802 } : Fields).get c.val)
theorem record028_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record028) (record028.maps 11) (record028.inverseMaps 11) record028_frame011_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record028) (record028.maps 11) (record028.inverseMaps 11) record028_frame011_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record028) (record028.maps 11)
      (record028.inverseMaps 11) record028_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame011_links_0000 record028_frame011_links_0064)
theorem record028_frame011_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 11 :=
  of_group record028 11 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record028_frame011_indices record028_frame011_graph record028_frame011_links
def record028_frame012_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x71a7117076fa6f06e66d66ca6bf6aa62261960e6005f45e85d55c75b95a059858f58757f57756f56755f55654b42841f4144063fa3ee3db3cd3bf3a632c32331930c3022f82e82dc2d12bc2b52ac2a429c29428c28427c2732681fa1f31ec1e61df1d81d11ca1c31b71b01a81a119919018818117916716015915114a14513e13612f12711e11610f1070f50ee0e70df0d80d40d00cc0c80c407806e05f04003602701201101000f00e00d00c00b00a009008006005004003002 } : Fields).get c.val)
theorem record028_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record028) (record028.maps 12) (record028.inverseMaps 12) record028_frame012_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record028) (record028.maps 12) (record028.inverseMaps 12) record028_frame012_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record028) (record028.maps 12)
      (record028.inverseMaps 12) record028_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame012_links_0000 record028_frame012_links_0064)
theorem record028_frame012_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 12 :=
  of_group record028 12 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record028_frame012_indices record028_frame012_graph record028_frame012_links
def record028_frame013_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1093.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1093.count (({ width := 8, code := 0xb5b4b3b1b0afaeadacabaaa9a8a6a5a4a3a2a1a09f9e9d9b9a9998979695949392908f8e8d8c8b8a8988878584838281807f7e7d7c7a79787776757472706f6c6a686664625f5d5c59575553514f4c4a48464442403f3c3a383634322f2d2b29272523211f1d1b19171513110f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record028_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1093.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1093.localPairCheck (smallEmbedding record028) (record028.maps 13) (record028.inverseMaps 13) record028_frame013_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1093.localPairCheck (smallEmbedding record028) (record028.maps 13) (record028.inverseMaps 13) record028_frame013_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1093.localPairCheck (smallEmbedding record028) (record028.maps 13)
      (record028.inverseMaps 13) record028_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame013_links_0000 record028_frame013_links_0064)
theorem record028_frame013_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 13 :=
  of_group record028 13 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1093
    Papers.RationalityTen.SharedFrameCatalogue.group1093_facts record028_frame013_indices record028_frame013_graph record028_frame013_links
def record028_frame014_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x59058858257b57356655f5555485394f04e84e04d94d04c54ba4ae4a349248e48748147b47346845f45844b43938938137a37336836235734a3413312e92e02d82d12c62be2b22a429a28a28627f27927326826225724d2432311cb1c51bf1bc1b71b01aa1a419d18f18918418017a17316c16615e15114b14313d13913312c12712311d11610f1070ff0f10e90e10dc0d70d20cb0c30bc0b606f06805903d03602701201101000f00e00d00c00b00a009008006005004003002 } : Fields).get c.val)
theorem record028_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record028) (record028.maps 14) (record028.inverseMaps 14) record028_frame014_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record028) (record028.maps 14) (record028.inverseMaps 14) record028_frame014_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record028) (record028.maps 14)
      (record028.inverseMaps 14) record028_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame014_links_0000 record028_frame014_links_0064)
theorem record028_frame014_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 14 :=
  of_group record028 14 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record028_frame014_indices record028_frame014_graph record028_frame014_links
def record028_frame015_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0864.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0864.count (({ width := 11, code := 0x85f0a61341f833046064057f8fc9e63c8780ee5d9bab74ce75ca387704df5bcb716d6d95b035b6a8d39702da5a8b3562ac1574ac553a9b4f09d537a684c09712aa4c48c8ed1ba3245c8990fa1b42a83d04a03358694cf99c32c644c61842f85c0b51652be560a894c28e5009992e2484748b911218418800f81e43b4738e11a8334630be1702d0570a714627c358630ac0f01a0270240440800f01c0340600b0140240400600a01001802 } : Fields).get c.val)
theorem record028_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record028) (record028.maps 15) (record028.inverseMaps 15) record028_frame015_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record028) (record028.maps 15) (record028.inverseMaps 15) record028_frame015_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record028) (record028.maps 15)
      (record028.inverseMaps 15) record028_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame015_links_0000 record028_frame015_links_0064)
theorem record028_frame015_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 15 :=
  of_group record028 15 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0864
    Papers.RationalityTen.SharedFrameCatalogue.group0864_facts record028_frame015_indices record028_frame015_graph record028_frame015_links
def record028_frame016_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x5d25ce5c45bb5b25a859d59258657b52e52351650a4ff4f54e84db4ce4c24bf4b64ac4a249b49448b48147746d39639238837e37336735d35434a33f2f22e72da2cc2bf2b22a729c29228628327a27026525b25124924223b2311c11bb1b41ae1a619e19618e18617d17917216b16515d15514f14713c13813312e12712311e11a11410d1071000f90f30e90e40de0d90d30cc0c80c20bd0b707706d05e04003602701201101000f00e00d00c00b00a009008006005004003002 } : Fields).get c.val)
theorem record028_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record028) (record028.maps 16) (record028.inverseMaps 16) record028_frame016_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record028) (record028.maps 16) (record028.inverseMaps 16) record028_frame016_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record028) (record028.maps 16)
      (record028.inverseMaps 16) record028_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame016_links_0000 record028_frame016_links_0064)
theorem record028_frame016_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 16 :=
  of_group record028 16 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record028_frame016_indices record028_frame016_graph record028_frame016_links
def record028_frame017_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0813.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0813.count (({ width := 11, code := 0x6d2d99b135d6b6d5daa35169ad159231e636c658b31061ac2582aff5fabe5792f05daba5712dd5aab3935a684c897d2e2574a894927a4744c8810da1742282d032033fc7dcfa9f23d87a8f39e23bc768eb9d02f05ccb61642c4560a914e2904fc9c93225c4a49211d22e444828fe1ee3c8770ed1d4398718dc1ae34c660c717c2dc588ae15028c4e09612423c358640aa0ec1a8260240440800f01c0340600b0140240400600a01001802 } : Fields).get c.val)
theorem record028_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record028) (record028.maps 17) (record028.inverseMaps 17) record028_frame017_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record028) (record028.maps 17) (record028.inverseMaps 17) record028_frame017_indices (Fin.ofNat record028.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record028_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record028) (record028.maps 17)
      (record028.inverseMaps 17) record028_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record028_frame017_links_0000 record028_frame017_links_0064)
theorem record028_frame017_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 17 :=
  of_group record028 17 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0813
    Papers.RationalityTen.SharedFrameCatalogue.group0813_facts record028_frame017_indices record028_frame017_graph record028_frame017_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (Fin.cases (record028_frame002_supported hcells) (Fin.cases (record028_frame003_supported hcells) (Fin.cases (record028_frame004_supported hcells) (Fin.cases (record028_frame005_supported hcells) (Fin.cases (record028_frame006_supported hcells) (Fin.cases (record028_frame007_supported hcells) (Fin.cases (record028_frame008_supported hcells) (Fin.cases (record028_frame009_supported hcells) (Fin.cases (record028_frame010_supported hcells) (Fin.cases (record028_frame011_supported hcells) (Fin.cases (record028_frame012_supported hcells) (Fin.cases (record028_frame013_supported hcells) (Fin.cases (record028_frame014_supported hcells) (Fin.cases (record028_frame015_supported hcells) (Fin.cases (record028_frame016_supported hcells) (Fin.cases (record028_frame017_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa89a82a7aa70a63a55a43a36a28a1493f93792e9239169098f88eb8dc8c984783c82f82180e7fc7e67d57c47ad79c79378377276375373e72a7167036f66e46d26bf6ab5d85cf5c65bc5ae59d58d5805705624fa4ef4e44da4cc4bd4ac49e4904804764704634554474394284184073f83e13d33c23b33a332e3233163082f82ea2dc2d02c12af2a029628627526725a24923922821a2051f61e51d71c91c21ba1ae1a01911831731651561461331271181070fa0f10e60d90cc0be0b503503403303203102602502402302200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame001_links_0000 (interval_append _ 64 128 146 record029_frame001_links_0064 record029_frame001_links_0128))
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
def record029_frame002_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb33b29b22b19b0baffaf1adbaccabc9da9cb9c29b89a59969889729639548c88b68aa89e88c87c86a85183d82a8138037f87ed7d77c37af79978477076374f73872170962861a6126085fb5f05e25d45c85b954053052751c50e5014f14e14d34c44b64a749c49348547a46c45c44d44042641840a3f93eb36e35b34e34433432230f2fd2ed2db2c72b72ad2a12932862752652552462302212111ff1ee1e21d51cd1c41b51a819818717816b1531411311211111020f50e80da0cb0c003503403303203102602502402302200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record029_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record029) (record029.maps 2)
      (record029.inverseMaps 2) record029_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame002_links_0000 (interval_append _ 64 128 146 record029_frame002_links_0064 record029_frame002_links_0128))
theorem record029_frame002_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 2 :=
  of_group record029 2 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record029_frame002_indices record029_frame002_graph record029_frame002_links
def record029_frame003_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0xe5792e3f8ce2786e0b7edeb76cfb3bce335ccb2fcaf26c871cbeaf6bcaeeba6e4b76d4b2ec2aeeb7aceafaaea7a8a9ba528ea22819ea739be3c8e6368ce308b62888a1c861fd7e9f77cdef7ade576dd1729c5709bf6edb76cdae69da06698e61d805f579561555494f52d4750d3b4cd2b491214791a4591243908408fd3d0ef3a8e738cdf36cd734ccf32cc72fcb72c0a627c9824c8b21c821f4781c46e0c8310c02f0b8260942408c220300b02809020060140400c02 } : Fields).get c.val)
theorem record029_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record029) (record029.maps 3) (record029.inverseMaps 3) record029_frame003_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record029) (record029.maps 3) (record029.inverseMaps 3) record029_frame003_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record029) (record029.maps 3) (record029.inverseMaps 3) record029_frame003_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record029) (record029.maps 3)
      (record029.inverseMaps 3) record029_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame003_links_0000 (interval_append _ 64 128 146 record029_frame003_links_0064 record029_frame003_links_0128))
theorem record029_frame003_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 3 :=
  of_group record029 3 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record029_frame003_indices record029_frame003_graph record029_frame003_links
def record029_frame004_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0452.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0452.count (({ width := 9, code := 0x2c761afd76b759abd56a751a15027d3c9d4e26d34994c24f2490c7a37188ac4a1f0c83c1607017fbf5f6f97bbd5e4f0773b1d4db6cb5daad368b3d9acb64b017cbc5d2e16cb4592c15cac552a14ca4512813c9c4d2592892482390e8541a04fe7d3d9e4ee75391c4e06f371b4d86a34198c6612f974b65a2c960ae562a950a4502712c92472290c8441200fc7c3d1208c4421100783a1c0d868160a048200e06028100602 } : Fields).get c.val)
theorem record029_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record029) (record029.maps 4) (record029.inverseMaps 4) record029_frame004_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record029) (record029.maps 4) (record029.inverseMaps 4) record029_frame004_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record029) (record029.maps 4) (record029.inverseMaps 4) record029_frame004_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record029) (record029.maps 4)
      (record029.inverseMaps 4) record029_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame004_links_0000 (interval_append _ 64 128 146 record029_frame004_links_0064 record029_frame004_links_0128))
theorem record029_frame004_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 4 :=
  of_group record029 4 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0452
    Papers.RationalityTen.SharedFrameCatalogue.group0452_facts record029_frame004_indices record029_frame004_graph record029_frame004_links
def record029_frame005_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1860c2060a30197f4bf05f3af41774ba454f2a35504a76535a9854a6a3d513284d3049704af253527692e48fa41d1de8d9462a2cd14289043f21c90c484c41ba08902a7ff3f51f50f7c6a434b1a14cf2668330194cc8262f30f1698b2e58a2bd95b8aca5582a294d8a5051c28593f09da4de269931c9684a524b91fc8d845c22690f476039e1c70df86dc3631aa8d0065831a1830bd05c62d31610ae055029414089bc4ae24511908804181fd0f707803a21c30dc86ac3301860bb058829a13e097047421e0ff07903941ac0ca01a80d0066032018809804a024011808801800b00500240100060028010006002 } : Fields).get c.val)
theorem record029_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 5) (record029.inverseMaps 5) record029_frame005_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 5) (record029.inverseMaps 5) record029_frame005_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 5) (record029.inverseMaps 5) record029_frame005_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 5)
      (record029.inverseMaps 5) record029_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame005_links_0000 (interval_append _ 64 128 146 record029_frame005_links_0064 record029_frame005_links_0128))
theorem record029_frame005_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 5 :=
  of_group record029 5 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record029_frame005_indices record029_frame005_graph record029_frame005_links
def record029_frame006_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0x2d259eb3565ec6584b055f2bad6da4546e8ad10a0f3f67d4f49db38e4fc929112063b46b8cb17a2ac4a87b0be13c2082902601bfb7e6f9df1bd9794eedd6b52694d159f33865eca592b1f62cb7d692c9586af159aae550a8d4da95514a053da734d098d2d25749890519a2743c84cf19d7398720e11b936a6bcd59a2332638c31802f85d0b71682ca574aa94927c4dc9792723644c879072023f47b0f21d838c6c8cf1903005b8ad1482784c0920660c81883005e098128240460880600b0140240400600a01001802 } : Fields).get c.val)
theorem record029_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record029) (record029.maps 6) (record029.inverseMaps 6) record029_frame006_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record029) (record029.maps 6) (record029.inverseMaps 6) record029_frame006_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record029) (record029.maps 6) (record029.inverseMaps 6) record029_frame006_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record029) (record029.maps 6)
      (record029.inverseMaps 6) record029_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame006_links_0000 (interval_append _ 64 128 146 record029_frame006_links_0064 record029_frame006_links_0128))
theorem record029_frame006_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 6 :=
  of_group record029 6 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record029_frame006_indices record029_frame006_graph record029_frame006_links
def record029_frame007_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0962.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0962.count (({ width := 10, code := 0xb0ec0af2b9ad6b2abeabaa2a59966297e5c9665694e509364a8d2308ae298922287e1a862158460d82e07816017fdfd7e5f77d5f07b5eb7a5ad6a9a7695a26819e66d9965d825f97c5e5775d1725c16d5ad6a595625795b55d555494e53147511425013e44d0d419013e8f53c8eb398e3384dc364d3340ca320c52fcbd2e4b72d0b02b0a9294a22749a254932408b224831fc7d1e8771cc6e1b46b1a4660b02b0a8290a023088210801f0300b02809020060140400c02 } : Fields).get c.val)
theorem record029_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record029) (record029.maps 7) (record029.inverseMaps 7) record029_frame007_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record029) (record029.maps 7) (record029.inverseMaps 7) record029_frame007_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record029) (record029.maps 7) (record029.inverseMaps 7) record029_frame007_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record029) (record029.maps 7)
      (record029.inverseMaps 7) record029_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame007_links_0000 (interval_append _ 64 128 146 record029_frame007_links_0064 record029_frame007_links_0128))
theorem record029_frame007_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 7 :=
  of_group record029 7 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0962
    Papers.RationalityTen.SharedFrameCatalogue.group0962_facts record029_frame007_indices record029_frame007_graph record029_frame007_links
def record029_frame008_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1a5ad2668fb461a22d0a681b3f19eacee58aac0d5e2ade5652ad9546a8f53f29b13529974c2a5c92bc94a49ba48d224900477a3a11c28da469a33118a8be45ba2c11568a444ea25911e6c435a1a8cd22681339197cc9863931415bcabe54e29e14b0a3a50a27b93909a64c826092e89664ad253127c93049124512048f647523791a470436d1ad0d1065e31c1838bcc5ba2ca15c8aa453228a13d09ac4b624c11e08b443220a0fe07b83c01d60e306d834e1970c405e02d21590a504d824e11908583f41ee0f007483881b60d501a80d0066032018809804a024011808801800b00500240100060028010006002 } : Fields).get c.val)
theorem record029_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record029) (record029.maps 8) (record029.inverseMaps 8) record029_frame008_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record029) (record029.maps 8) (record029.inverseMaps 8) record029_frame008_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record029) (record029.maps 8) (record029.inverseMaps 8) record029_frame008_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record029) (record029.maps 8)
      (record029.inverseMaps 8) record029_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame008_links_0000 (interval_append _ 64 128 146 record029_frame008_links_0064 record029_frame008_links_0128))
theorem record029_frame008_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 8 :=
  of_group record029 8 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record029_frame008_indices record029_frame008_graph record029_frame008_links
def record029_frame009_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x78d78778177c77677276d7667607596a469968d68267a67366b65a64f6425e95de5d65ce5c25b85b059f59358957c57556e56756055b55554e54754053b53452d52651f44343842e42141640f4033f23e63db37636c36135734d34233632531930e3073002f92f22eb2e62e02d92d22cb2c32bc2b52af2aa23f23422621c20e2051f81ed1e01d61cb1c31bc1b51ae1a81a119718f18617816c16615d15414b14313c13512e12812111710d1070f80ec0e40df0d40ce0c90c30c00bd0b803503403303203102602502402302200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record029_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record029) (record029.maps 9) (record029.inverseMaps 9) record029_frame009_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record029) (record029.maps 9) (record029.inverseMaps 9) record029_frame009_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record029) (record029.maps 9) (record029.inverseMaps 9) record029_frame009_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record029) (record029.maps 9)
      (record029.inverseMaps 9) record029_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame009_links_0000 (interval_append _ 64 128 146 record029_frame009_links_0064 record029_frame009_links_0128))
theorem record029_frame009_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 9 :=
  of_group record029 9 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record029_frame009_indices record029_frame009_graph record029_frame009_links
def record029_frame010_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x2bc574add5a6b2d61ab554ea75489a333663cc297d2ea59cac94f2863245d8ab13e24c438790d616c2683f0620840a808ff9fbbf07d0f85ee3d87a8f41e635d6b0d4da7349688cf99c331654b61682c9586af95dab3552a894da92516a0d3da764e29a52f2544948f91c23345c8a0ec1d1392704de1b735e690cd19030a5f4bb1702d65a0b015629e5209f1382664b894123238454879092043f07a8ee1ce3806c8d219c320610bb1682c0550a706a0d019832062098128240460880600b0140240400600a01001802 } : Fields).get c.val)
theorem record029_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record029) (record029.maps 10) (record029.inverseMaps 10) record029_frame010_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record029) (record029.maps 10) (record029.inverseMaps 10) record029_frame010_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record029) (record029.maps 10) (record029.inverseMaps 10) record029_frame010_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record029) (record029.maps 10)
      (record029.inverseMaps 10) record029_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame010_links_0000 (interval_append _ 64 128 146 record029_frame010_links_0064 record029_frame010_links_0128))
theorem record029_frame010_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 10 :=
  of_group record029 10 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record029_frame010_indices record029_frame010_graph record029_frame010_links
def record029_frame011_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x2bdd73adf5a2b155daaf546a5d4698d30e5e4b595f2ae5249d93324e2cc4f89110a1e4368610a20f41881d021ff3f87e2fb5f33dd7aef39e3bc3778ed5d8b3c66ccc596b28646c798c31261aafd5bab455aaa95129b52ca3543a7e4ea9bd332604b494123a3f46889510a1b42e840e11ba3686acd319f32a630c11792d659cb195c2ac550a514127c4d8951232404708a91021240c7f8f91e83b8740e11b434c670c81882f45b0b015629c5009c06a0d019832062098128240460880600b0140240400600a01001802 } : Fields).get c.val)
theorem record029_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record029) (record029.maps 11) (record029.inverseMaps 11) record029_frame011_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record029) (record029.maps 11) (record029.inverseMaps 11) record029_frame011_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record029) (record029.maps 11) (record029.inverseMaps 11) record029_frame011_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record029) (record029.maps 11)
      (record029.inverseMaps 11) record029_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame011_links_0000 (interval_append _ 64 128 146 record029_frame011_links_0064 record029_frame011_links_0128))
theorem record029_frame011_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 11 :=
  of_group record029 11 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record029_frame011_indices record029_frame011_graph record029_frame011_links
def record029_frame012_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0373.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0373.count (({ width := 9, code := 0x2130782c0e02ff7ebedf2f77a3c9e0ee763a9d0e672389bedd6db65aed569b459ecd65b258ec561b057ebd5dae56eb559ac55eac552a14ca4512813c9c4da6530974b255289349245208f46a2d128742a0d027f3e9e8f0763a1c8e26f369acd2673298cc25f2e970b65a2c960ae562a950a4502713094492411c8c452210c8441200fc7c3d1e0ec74391c0dc6c35108803e1e0e86c34190c05c160a048200e06028100602 } : Fields).get c.val)
theorem record029_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0373.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record029) (record029.maps 12) (record029.inverseMaps 12) record029_frame012_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record029) (record029.maps 12) (record029.inverseMaps 12) record029_frame012_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record029) (record029.maps 12) (record029.inverseMaps 12) record029_frame012_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record029) (record029.maps 12)
      (record029.inverseMaps 12) record029_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame012_links_0000 (interval_append _ 64 128 146 record029_frame012_links_0064 record029_frame012_links_0128))
theorem record029_frame012_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 12 :=
  of_group record029 12 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0373
    Papers.RationalityTen.SharedFrameCatalogue.group0373_facts record029_frame012_indices record029_frame012_graph record029_frame012_links
def record029_frame013_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0x26ccd69a1326624c09772d257ca78931162043d86f0c215c2483905df23de7acf41e6bc7784ee9dabad74ae7dce39771ee21c1b7b6eadbdb3b636c0d69a9aed5d0b856dad459eb29622be5729f13d2764de9ad342604b0955272484868f51aa2f4548850ba114127f0fb1f23d8798d59a533e664c998d3085e8b996a2c056cab9542a0530a213c26c4cc9512423a4688a1102124107e8f81e43b4748e31ba358688cd1903105e8b81662c0558a70660c81883005e094120230440840600b0140240400600a01001802 } : Fields).get c.val)
theorem record029_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record029) (record029.maps 13) (record029.inverseMaps 13) record029_frame013_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record029) (record029.maps 13) (record029.inverseMaps 13) record029_frame013_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record029) (record029.maps 13) (record029.inverseMaps 13) record029_frame013_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record029) (record029.maps 13)
      (record029.inverseMaps 13) record029_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame013_links_0000 (interval_append _ 64 128 146 record029_frame013_links_0064 record029_frame013_links_0128))
theorem record029_frame013_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 13 :=
  of_group record029 13 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record029_frame013_indices record029_frame013_graph record029_frame013_links
def record029_frame014_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1092.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1092.count (({ width := 9, code := 0x2f578bb5d2e571b7db6d769ab552a550a75369749a3d1677399bcd66732984ba592a9449a49229047e3b1b8cc5e2b1489c4a23007f3f1f4f87bbd5e6f076b8dc2df6eb6db4d86b34da0cd65b258cc561b057cbb5c2d566b1582b948a250275389a4c255248f46a2d128742a1104803e9e8ee75399c8e06f369acd26733190c45f2e164ae552a148a04e2612c92480c8602e160a844200f070341208038180a04018080200 } : Fields).get c.val)
theorem record029_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record029) (record029.maps 14) (record029.inverseMaps 14) record029_frame014_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record029) (record029.maps 14) (record029.inverseMaps 14) record029_frame014_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record029) (record029.maps 14) (record029.inverseMaps 14) record029_frame014_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record029) (record029.maps 14)
      (record029.inverseMaps 14) record029_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame014_links_0000 (interval_append _ 64 128 146 record029_frame014_links_0064 record029_frame014_links_0128))
theorem record029_frame014_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 14 :=
  of_group record029 14 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1092
    Papers.RationalityTen.SharedFrameCatalogue.group1092_facts record029_frame014_indices record029_frame014_graph record029_frame014_links
def record029_frame015_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0989.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0989.count (({ width := 8, code := 0xa3a2a1a09f9e9d9b9a9998979695949392908f8e8d8c8b8a8988878584838281807f7e7d7c7a797877767574737271706f6e6d6c6a6968676665646362615f5e5d5c5b5a59585755545352504f4e4d4c4b4a4948474644434241403f3e3d3c3b3a38373634333231302f2e2d2c2b2a29272625232221201f1d1c1b1a1918131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record029_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0989.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0989.localPairCheck (smallEmbedding record029) (record029.maps 15) (record029.inverseMaps 15) record029_frame015_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0989.localPairCheck (smallEmbedding record029) (record029.maps 15) (record029.inverseMaps 15) record029_frame015_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0989.localPairCheck (smallEmbedding record029) (record029.maps 15) (record029.inverseMaps 15) record029_frame015_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0989.localPairCheck (smallEmbedding record029) (record029.maps 15)
      (record029.inverseMaps 15) record029_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame015_links_0000 (interval_append _ 64 128 146 record029_frame015_links_0064 record029_frame015_links_0128))
theorem record029_frame015_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 15 :=
  of_group record029 15 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0989
    Papers.RationalityTen.SharedFrameCatalogue.group0989_facts record029_frame015_indices record029_frame015_graph record029_frame015_links
def record029_frame016_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1089.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1089.count (({ width := 9, code := 0x2c761af56eb357aa5469f4ca1d067d3b9ccde693197cb24d2490c7a391a8bc52250f8642a0f0481401fafa7c3d5e4f1783bddce974399cae471b85bede6e365b0d66ab51a6d167b3998cb6431986c15f2ed72b659abd5cac55aa94ea45127d3a9a4ba55248f4622d128843a190882409fcfa7c3d1e4f0773b1d0e672389bcda6c351a0ce653218cc2602f174b85b138984a241187c3c1d0e06c180b050241006028100602 } : Fields).get c.val)
theorem record029_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record029) (record029.maps 16) (record029.inverseMaps 16) record029_frame016_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record029) (record029.maps 16) (record029.inverseMaps 16) record029_frame016_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record029) (record029.maps 16) (record029.inverseMaps 16) record029_frame016_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record029) (record029.maps 16)
      (record029.inverseMaps 16) record029_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame016_links_0000 (interval_append _ 64 128 146 record029_frame016_links_0064 record029_frame016_links_0128))
theorem record029_frame016_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 16 :=
  of_group record029 16 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1089
    Papers.RationalityTen.SharedFrameCatalogue.group1089_facts record029_frame016_indices record029_frame016_graph record029_frame016_links
def record029_frame017_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1086.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1086.count (({ width := 9, code := 0x35babd469747a1cf66f3396c3613037ebe5eaef74b95becd64b0d7ab95aabd52a54fa652a8f44a15027b3a9c4d66531984be5d218fc76391b8d4622d1488c1e09017fbf5f6f97abc9deec74b9dc8e26fb71b2d568b3598ca64b2180bd5dae16cb3582b552a55027534984b251248e45a210a8441205007f3e9ecf4793c1d8e872379b0d6693419cca6431184c05f138984a241187c3c1d0e06c180b050241006028100602 } : Fields).get c.val)
theorem record029_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record029) (record029.maps 17) (record029.inverseMaps 17) record029_frame017_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record029) (record029.maps 17) (record029.inverseMaps 17) record029_frame017_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record029) (record029.maps 17) (record029.inverseMaps 17) record029_frame017_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record029) (record029.maps 17)
      (record029.inverseMaps 17) record029_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame017_links_0000 (interval_append _ 64 128 146 record029_frame017_links_0064 record029_frame017_links_0128))
theorem record029_frame017_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 17 :=
  of_group record029 17 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1086
    Papers.RationalityTen.SharedFrameCatalogue.group1086_facts record029_frame017_indices record029_frame017_graph record029_frame017_links
def record029_frame018_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1083.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1083.count (({ width := 9, code := 0x2f578bb5d2e571b7db6d769ab552a550a75369749a3d1677399bcd66732984ba592a9449a49229047e3b1b8cc5e2b1489c4a23007f3f1f4f87bbd5e6f076b8dc2df6eb6db4d86b34da0cd65b258cc561b057cbb5c2d566b1582b948a250275389a4c255248f46a2d128742a1104803e9e8ee75399c8e06f369acd26733190c45f2e164ae552a148a04e2612c92480c8602e160a844200f070341208038180a04018080200 } : Fields).get c.val)
theorem record029_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record029) (record029.maps 18) (record029.inverseMaps 18) record029_frame018_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record029) (record029.maps 18) (record029.inverseMaps 18) record029_frame018_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record029) (record029.maps 18) (record029.inverseMaps 18) record029_frame018_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record029) (record029.maps 18)
      (record029.inverseMaps 18) record029_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame018_links_0000 (interval_append _ 64 128 146 record029_frame018_links_0064 record029_frame018_links_0128))
theorem record029_frame018_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 18 :=
  of_group record029 18 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1083
    Papers.RationalityTen.SharedFrameCatalogue.group1083_facts record029_frame018_indices record029_frame018_graph record029_frame018_links
def record029_frame019_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0985.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0985.count (({ width := 8, code := 0xa3a2a1a09f9e9d9b9a9998979695949392908f8e8d8c8b8a8988878584838281807f7e7d7c7a797877767574737271706f6e6d6c6a6968676665646362615f5e5d5c5b5a59585755545352504f4e4d4c4b4a4948474644434241403f3e3d3c3b3a38373634333231302f2e2d2c2b2a29272625232221201f1d1c1b1a1918131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record029_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0985.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0985.localPairCheck (smallEmbedding record029) (record029.maps 19) (record029.inverseMaps 19) record029_frame019_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0985.localPairCheck (smallEmbedding record029) (record029.maps 19) (record029.inverseMaps 19) record029_frame019_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0985.localPairCheck (smallEmbedding record029) (record029.maps 19) (record029.inverseMaps 19) record029_frame019_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0985.localPairCheck (smallEmbedding record029) (record029.maps 19)
      (record029.inverseMaps 19) record029_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame019_links_0000 (interval_append _ 64 128 146 record029_frame019_links_0064 record029_frame019_links_0128))
theorem record029_frame019_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 19 :=
  of_group record029 19 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0985
    Papers.RationalityTen.SharedFrameCatalogue.group0985_facts record029_frame019_indices record029_frame019_graph record029_frame019_links
def record029_frame020_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0946.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0946.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record029_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0946.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0946.localPairCheck (smallEmbedding record029) (record029.maps 20) (record029.inverseMaps 20) record029_frame020_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0946.localPairCheck (smallEmbedding record029) (record029.maps 20) (record029.inverseMaps 20) record029_frame020_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0946.localPairCheck (smallEmbedding record029) (record029.maps 20) (record029.inverseMaps 20) record029_frame020_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0946.localPairCheck (smallEmbedding record029) (record029.maps 20)
      (record029.inverseMaps 20) record029_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame020_links_0000 (interval_append _ 64 128 146 record029_frame020_links_0064 record029_frame020_links_0128))
theorem record029_frame020_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 20 :=
  of_group record029 20 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0946
    Papers.RationalityTen.SharedFrameCatalogue.group0946_facts record029_frame020_indices record029_frame020_graph record029_frame020_links
def record029_frame021_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0984.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0984.count (({ width := 8, code := 0xf0eeeceae8e6e4e2e0dedcdad8d6d4d2d0cecccac8c6c4c2c0bebcbab8b6b4b2b0aeacaaa8a6a4a2a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a8988878583817f7d7b797775737271706f6e6c6a68666462605e5c5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a39383721201f1e1d1c1b1a19180c0b0a09080605040302 } : Fields).get c.val)
theorem record029_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0984.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0984.localPairCheck (smallEmbedding record029) (record029.maps 21) (record029.inverseMaps 21) record029_frame021_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0984.localPairCheck (smallEmbedding record029) (record029.maps 21) (record029.inverseMaps 21) record029_frame021_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0984.localPairCheck (smallEmbedding record029) (record029.maps 21) (record029.inverseMaps 21) record029_frame021_indices (Fin.ofNat record029.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record029_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0984.localPairCheck (smallEmbedding record029) (record029.maps 21)
      (record029.inverseMaps 21) record029_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record029_frame021_links_0000 (interval_append _ 64 128 146 record029_frame021_links_0064 record029_frame021_links_0128))
theorem record029_frame021_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 21 :=
  of_group record029 21 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0984
    Papers.RationalityTen.SharedFrameCatalogue.group0984_facts record029_frame021_indices record029_frame021_graph record029_frame021_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (Fin.cases (record029_frame002_supported hcells) (Fin.cases (record029_frame003_supported hcells) (Fin.cases (record029_frame004_supported hcells) (Fin.cases (record029_frame005_supported hcells) (Fin.cases (record029_frame006_supported hcells) (Fin.cases (record029_frame007_supported hcells) (Fin.cases (record029_frame008_supported hcells) (Fin.cases (record029_frame009_supported hcells) (Fin.cases (record029_frame010_supported hcells) (Fin.cases (record029_frame011_supported hcells) (Fin.cases (record029_frame012_supported hcells) (Fin.cases (record029_frame013_supported hcells) (Fin.cases (record029_frame014_supported hcells) (Fin.cases (record029_frame015_supported hcells) (Fin.cases (record029_frame016_supported hcells) (Fin.cases (record029_frame017_supported hcells) (Fin.cases (record029_frame018_supported hcells) (Fin.cases (record029_frame019_supported hcells) (Fin.cases (record029_frame020_supported hcells) (Fin.cases (record029_frame021_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x93e93592c9209139068f58e88d98c684683a82d81f80c7f97e37d27c27aa79b79078076f76075073b7277137005d95d25c95bf5b15a05905835735644fb4f24e74dd4cf4c04af4a149348347546d4604524444364254154043f532d3203133052f52e72d92cd2be2ac2a029628627526725a24923922821a2071f81e71d91cb1c21ba1ae1a019118317316515614613512911a1090fc05705605505405302102001f01e01d01101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
def record030_frame002_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0x9d79c89c19b59a399498596f9609518c68b48a989b88987986784e83a8278108007f77ea7d47c07ac79678176e62b61d61360b5fe5f35e55d75cb5bc54353352851f5115044f44e44d64c74b34a449b49048247746945944a43d36b35834d34133131f30c2fa2ea2d82c72b72ad2a12932862752652552462322232132011f01e21d51cd1c41b51a819818717816b15514313312311305905805705605502102001f01e01d01101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record030_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record030) (record030.maps 2)
      (record030.inverseMaps 2) record030_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame002_links_0000 record030_frame002_links_0064)
theorem record030_frame002_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 2 :=
  of_group record030 2 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record030_frame002_indices record030_frame002_graph record030_frame002_links
def record030_frame003_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0xcf73acdf34cc72ecab25c831bbe6f5bc6edba2e3b6ed2b26c1aeab6acaadaa6a5a8299a4a8d8f63a8de348c62e8aa2487a197f9fb7e1f57c5ed7a1de751cb711c16f9b96d5b16b1a56799955d545454e52946505394c52a491214791a4591243908408fd3d4f03ace8390df36cd734ccf32cc72fcb72c0a7280992508d104400fc3e0f4210801f0781d0441003c0e0340c02c0a02408018050100300800 } : Fields).get c.val)
theorem record030_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record030) (record030.maps 3)
      (record030.inverseMaps 3) record030_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame003_links_0000 record030_frame003_links_0064)
theorem record030_frame003_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 3 :=
  of_group record030 3 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record030_frame003_indices record030_frame003_graph record030_frame003_links
def record030_frame004_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0452.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0452.count (({ width := 9, code := 0x2833f9ecee73379acce632f9348e411d8d45e29118742e0d0481401fcfc7d3e1ecf46e369b0d66a349a0ce6632982bf5eaed72b75aacd62af55aa54ea551a853e9d4da650c8441200fc7c3d1e0ec74391c4e06f371b4d86a34198c86230178b85a2c960ae562a950a450271309448231105c2d160ac54190c05c2c150803c1c0d0602c14090401c0c050200c0400 } : Fields).get c.val)
theorem record030_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record030) (record030.maps 4) (record030.inverseMaps 4) record030_frame004_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record030) (record030.maps 4) (record030.inverseMaps 4) record030_frame004_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record030) (record030.maps 4)
      (record030.inverseMaps 4) record030_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame004_links_0000 record030_frame004_links_0064)
theorem record030_frame004_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 4 :=
  of_group record030 4 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0452
    Papers.RationalityTen.SharedFrameCatalogue.group0452_facts record030_frame004_indices record030_frame004_graph record030_frame004_links
def record030_frame005_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1536a8b53fa9d14d0a6052828e9448a114bfa5b92b894b49ca4b5238904476a35d1848b044f22350f687142fa12506881f3539a64d1067c3359984cac6443191884b5259a2c695f8ae25662ad9520a7252b28c94209f24ea26d93489884b1251125075a39b1c60dec6d83621a90cf46523171830bd05c62d31610ae055029414089bc4b224711a088841c1fd0f707803a21c30dc86ac3301860bb059029e140098047c0b205802b81580aa021010007c03c01d008804001e00e006803001600a004802000c005002000c004000 } : Fields).get c.val)
theorem record030_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record030) (record030.maps 5) (record030.inverseMaps 5) record030_frame005_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record030) (record030.maps 5) (record030.inverseMaps 5) record030_frame005_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record030) (record030.maps 5)
      (record030.inverseMaps 5) record030_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame005_links_0000 record030_frame005_links_0064)
theorem record030_frame005_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 5 :=
  of_group record030 5 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record030_frame005_indices record030_frame005_graph record030_frame005_links
def record030_frame006_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x23b46f8d719e2fc5b8ab13221c3c82d03202c017eefbdf43dd7a2f19df3b7760eb5d339f738e55c6385612c117fafb5eabc175ae35b6b4d56aa653ea714b28f5109f93a26b4c89852ca564a693125a4647e8e8f09d73a2730e11bb36e6c4d59a533e660c918e30c600bd1702ce578a894827c4d49892d2504848e917220428810fa1e23906c8cf1842e02584a0921202382104007c0f01d0220400780e01a0300580a0120200300500800c01000 } : Fields).get c.val)
theorem record030_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record030) (record030.maps 6) (record030.inverseMaps 6) record030_frame006_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record030) (record030.maps 6) (record030.inverseMaps 6) record030_frame006_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record030) (record030.maps 6)
      (record030.inverseMaps 6) record030_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame006_links_0000 record030_frame006_links_0064)
theorem record030_frame006_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 6 :=
  of_group record030 6 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record030_frame006_indices record030_frame006_graph record030_frame006_links
def record030_frame007_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xbcef0bb6eab9ee4b82d9b56d1abeaba9ea3a7e9ba568aa0e7c9e2769ce719ba6b98e5c9524c7fdfd7edf97ddf57c5eb799e1715c3705bf6f5bb6d9ad69da166d9965d9564d916217f5e1714e1344c12d4a52647d174450b41903400fe3ecf93cceb398e1360d4340cc324c5304bd2e8b62ccad2949f2648f220831f8790e8390e0370d81e0741c06c1a0441003c0e0340c02c0a02408018050100300800 } : Fields).get c.val)
theorem record030_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record030) (record030.maps 7) (record030.inverseMaps 7) record030_frame007_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record030) (record030.maps 7) (record030.inverseMaps 7) record030_frame007_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record030) (record030.maps 7)
      (record030.inverseMaps 7) record030_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame007_links_0000 record030_frame007_links_0064)
theorem record030_frame007_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 7 :=
  of_group record030 7 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record030_frame007_indices record030_frame007_graph record030_frame007_links
def record030_frame008_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0200.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0200.count (({ width := 10, code := 0x7a1e5789df771d9759d3741cd6e1b56c9af6b1a96919f66995649906398c62988619836017d56557555535454f53149519434bd2d4ad2949d2548d204751a45914449104390c42505404fd35cd4344ce32cc8314c02ecb62c8b02b8ac2a8a8298a22789a258932408d22c8821884208801f87c1dc721b4681946217c5c0cc320c4300bc1b06819060170441003c0e0340c02c0a02408018050100300800 } : Fields).get c.val)
theorem record030_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record030) (record030.maps 8) (record030.inverseMaps 8) record030_frame008_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record030) (record030.maps 8) (record030.inverseMaps 8) record030_frame008_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record030) (record030.maps 8)
      (record030.inverseMaps 8) record030_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame008_links_0000 record030_frame008_links_0064)
theorem record030_frame008_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 8 :=
  of_group record030 8 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0200
    Papers.RationalityTen.SharedFrameCatalogue.group0200_facts record030_frame008_indices record030_frame008_graph record030_frame008_links
def record030_frame009_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0273.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0273.count (({ width := 10, code := 0x6cdb16bdad6ada96a1a7699a56458e62d88615825f97a5d9725bd6d5ad6959d65591625815e4ed394dd354cd314b92c4a928455134450f4350b4250640d003f0fa3e0f63d0f23c0ed3a8e7308bf2f0b92d8b32c4ad2a4a52849f2749b264972549123489214821fc7c1e8781d8741c8701b86c19c62174581545213c4c0bc2e0b42c0ac1906017058150400f0380d0300b0280902007018050100300800 } : Fields).get c.val)
theorem record030_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0273.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record030) (record030.maps 9) (record030.inverseMaps 9) record030_frame009_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record030) (record030.maps 9) (record030.inverseMaps 9) record030_frame009_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record030) (record030.maps 9)
      (record030.inverseMaps 9) record030_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame009_links_0000 record030_frame009_links_0064)
theorem record030_frame009_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 9 :=
  of_group record030 9 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0273
    Papers.RationalityTen.SharedFrameCatalogue.group0273_facts record030_frame009_indices record030_frame009_graph record030_frame009_links
def record030_frame010_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0x290519a2943a82cfc9f13ce75ce293923e43c7f8e91aa31c5d8a71261d42c84d07608c07800fe5f83e66aad35a3340676cc595b27644c5d712d5594b155f2b5560aa952a9c524a1d402784e0999302584a892cf01d4396718e01b83666b8d49a1332638c31802f85d0b71682ca574ab94b2804e09812723644c879072023f47b0f21d83946d8d11923042684c0961282482104007c0f01d0220400780e01a0300580a0120200300500800c01000 } : Fields).get c.val)
theorem record030_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record030) (record030.maps 10) (record030.inverseMaps 10) record030_frame010_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record030) (record030.maps 10) (record030.inverseMaps 10) record030_frame010_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record030) (record030.maps 10)
      (record030.inverseMaps 10) record030_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame010_links_0000 record030_frame010_links_0064)
theorem record030_frame010_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 10 :=
  of_group record030 10 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record030_frame010_indices record030_frame010_graph record030_frame010_links
def record030_frame011_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0220.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0220.count (({ width := 7, code := 0x3efcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record030_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0220.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0220.localPairCheck (smallEmbedding record030) (record030.maps 11) (record030.inverseMaps 11) record030_frame011_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0220.localPairCheck (smallEmbedding record030) (record030.maps 11) (record030.inverseMaps 11) record030_frame011_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0220.localPairCheck (smallEmbedding record030) (record030.maps 11)
      (record030.inverseMaps 11) record030_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame011_links_0000 record030_frame011_links_0064)
theorem record030_frame011_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 11 :=
  of_group record030 11 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0220
    Papers.RationalityTen.SharedFrameCatalogue.group0220_facts record030_frame011_indices record030_frame011_graph record030_frame011_links
def record030_frame012_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1590ab45502a314eea6252828ed44ea134a4a4d524290f47ea3a91ae8c44582275110876432214908483040fa034ff67e92ca1600ad85582a194b8a38507279937c82a4011f68f6c7923b61d18e406f83691aa0d0866031e1870bf05d62d91638ad441e20810087e83e61ec0f287783ae1d00e487083761b40d6869833e1980c8862830217a0b985b02ca1600ac854829614409e84d825e128090846022210a08183f00b205802b81580aa021010007c03c01d008804001e00e006803001600a004802000c005002000c004000 } : Fields).get c.val)
theorem record030_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 12) (record030.inverseMaps 12) record030_frame012_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 12) (record030.inverseMaps 12) record030_frame012_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 12)
      (record030.inverseMaps 12) record030_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame012_links_0000 record030_frame012_links_0064)
theorem record030_frame012_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 12 :=
  of_group record030 12 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record030_frame012_indices record030_frame012_graph record030_frame012_links
def record030_frame013_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x59058858257b57356655f5555485404f04e84e04d94d04c54ba4ae4a349a48c48548047847046645c45544843e38938137a37336836235734a3413382e92e02d82d12c62be2b22a429a29228427d27827026625f25424a2402361cb1c51bf1bc1b71b01aa1a419d19618f18918418017a17316c16615e15715114b14313d13913312c12712311d11610f1070ff0f90f10e90e10dc0d705305205105004f02102001f01e01d01101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record030_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record030) (record030.maps 13) (record030.inverseMaps 13) record030_frame013_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record030) (record030.maps 13) (record030.inverseMaps 13) record030_frame013_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record030) (record030.maps 13)
      (record030.inverseMaps 13) record030_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame013_links_0000 record030_frame013_links_0064)
theorem record030_frame013_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 13 :=
  of_group record030 13 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record030_frame013_indices record030_frame013_graph record030_frame013_links
def record030_frame014_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0381.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0381.count (({ width := 9, code := 0x2271288c421f0e86c32170a81401fcfc7d3e1ecf4793c1daec75ba9d2e873b99cae469345a0cf6733598cb6532582bf5eaed72b75aacd62af562ad54a95429d4ca55228d208e46229108642a0d027f3e1e8f0763a1c8e06d3519cc86230178ba5b2c95caa532893c98492310c823f1e8f05228138984a190c05c2c150803c1c0d0602c14090401c0c050200c0400 } : Fields).get c.val)
theorem record030_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0381.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record030) (record030.maps 14) (record030.inverseMaps 14) record030_frame014_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record030) (record030.maps 14) (record030.inverseMaps 14) record030_frame014_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record030) (record030.maps 14)
      (record030.inverseMaps 14) record030_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame014_links_0000 record030_frame014_links_0064)
theorem record030_frame014_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 14 :=
  of_group record030 14 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0381
    Papers.RationalityTen.SharedFrameCatalogue.group0381_facts record030_frame014_indices record030_frame014_graph record030_frame014_links
def record030_frame015_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x5f45eb5e45db5d35ce5c65ba5af5a255054754053452d52651f5135084fb4ee4e84df4d94ce4c94c04b24a749a3ba3b03a83a239b39438c38037236831630b3042fc2f52ec2e52d92cb2c22b42ad2a229d29428f28627826a25f1e11d91d01c81bf1b91b61af1a81a019819018817f17717016c16615f15714d14814013713012d12812211c11611010d1081010f90f10ec0e60df0d805705605505405302102001f01e01d01101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record030_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record030) (record030.maps 15) (record030.inverseMaps 15) record030_frame015_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record030) (record030.maps 15) (record030.inverseMaps 15) record030_frame015_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record030) (record030.maps 15)
      (record030.inverseMaps 15) record030_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame015_links_0000 record030_frame015_links_0064)
theorem record030_frame015_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 15 :=
  of_group record030 15 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record030_frame015_indices record030_frame015_graph record030_frame015_links
def record030_frame016_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0272.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0272.count (({ width := 9, code := 0x22f158a44e231087c3a1b0c81c0600ff7ebf1f6fa7cbe1eef67a3cde4f077bb9daec6db65b0d76ab51a6d268b418ec56230d82c05faf97abc5dae970b75b2d166b258ac1409d4da652c9449a411a8a4320d027f3e1e8ee73379acce6430978ba5b2c158a851279309044200f07236198c842200f8783a180b8582a14078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record030_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0272.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0272.localPairCheck (smallEmbedding record030) (record030.maps 16) (record030.inverseMaps 16) record030_frame016_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0272.localPairCheck (smallEmbedding record030) (record030.maps 16) (record030.inverseMaps 16) record030_frame016_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0272.localPairCheck (smallEmbedding record030) (record030.maps 16)
      (record030.inverseMaps 16) record030_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame016_links_0000 record030_frame016_links_0064)
theorem record030_frame016_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 16 :=
  of_group record030 16 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0272
    Papers.RationalityTen.SharedFrameCatalogue.group0272_facts record030_frame016_indices record030_frame016_graph record030_frame016_links
def record030_frame017_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1624b005772b6d58eab35502a314f6a694d3265130496f4ada51d268920487a3f51dc8e747023651a48cb46222f516c8af3639adcd4c69434219d4cc464f31e18acae45622a894fca5e52028693e89ce4d626393009724b2256129493c49724812246fe36a1ab8d046583191820bc05b42c715c8aa453228a13d09ac4b624c11e08b443620c0ff07c03c41d60e306d834e1970c405e02d21590a504e025211b08683fc0b205802b81580aa021010007c03c01d008804001e00e006803001600a004802000c005002000c004000 } : Fields).get c.val)
theorem record030_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record030) (record030.maps 17) (record030.inverseMaps 17) record030_frame017_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record030) (record030.maps 17) (record030.inverseMaps 17) record030_frame017_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record030) (record030.maps 17)
      (record030.inverseMaps 17) record030_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame017_links_0000 record030_frame017_links_0064)
theorem record030_frame017_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 17 :=
  of_group record030 17 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record030_frame017_indices record030_frame017_graph record030_frame017_links
def record030_frame018_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x66765b65564a63f63762c62061360a5bd5b45aa59f59658e58157556d55f55254b54554053b53653052952351d45044143a43142441b4114043fa3f039638d38137836c36535834c34333732932231c31731130c3073002fa2f426525925124923d23222621920c1fc1f21e91e21d81d01c71bd1b41a919f18f18617c17316715e15514e14413b13512911f11710b0fb0f10ea0df0d305705605505405302102001f01e01d01101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record030_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record030) (record030.maps 18) (record030.inverseMaps 18) record030_frame018_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record030) (record030.maps 18) (record030.inverseMaps 18) record030_frame018_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record030) (record030.maps 18)
      (record030.inverseMaps 18) record030_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame018_links_0000 record030_frame018_links_0064)
theorem record030_frame018_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 18 :=
  of_group record030 18 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record030_frame018_indices record030_frame018_graph record030_frame018_links
def record030_frame019_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0377.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0377.count (({ width := 9, code := 0x3198ac461b0982c05f6f578b459ac962b057ab959ab552a14ea652a9146a25067d3c8fc72331689c421b0982c09e4ef763a5cce370371b0d568b3d9acb64b1d88c15f2f1409e4e26930964a2451c8c4522510874321508813f1ecee74389bcd86a349a0ce6632990c25e2d95ca851279306230178b85a1b0d0643017088401e0e06830160a048200c050200c0400 } : Fields).get c.val)
theorem record030_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0377.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record030) (record030.maps 19) (record030.inverseMaps 19) record030_frame019_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record030) (record030.maps 19) (record030.inverseMaps 19) record030_frame019_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record030) (record030.maps 19)
      (record030.inverseMaps 19) record030_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame019_links_0000 record030_frame019_links_0064)
theorem record030_frame019_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 19 :=
  of_group record030 19 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0377
    Papers.RationalityTen.SharedFrameCatalogue.group0377_facts record030_frame019_indices record030_frame019_graph record030_frame019_links
def record030_frame020_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x71a7117076fa6f06e66d66ca6bf6b262261960e6005f45e85d55c75b95a859758e58657e57656e56655e55554c42841f4144063fa3ee3db3cd3bf3ae32c32331930c3022f82e82dc2d12c42b42ab2a329b29328b28327b2722691fa1f31ec1e61df1d81d11ca1c31bd1b71b01a81a119919018818117917116716015915114a14513e13612f12711e11610f1070ff0f50ee0e70df0d805905805705605502102001f01e01d01101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record030_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record030) (record030.maps 20) (record030.inverseMaps 20) record030_frame020_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record030) (record030.maps 20) (record030.inverseMaps 20) record030_frame020_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record030) (record030.maps 20)
      (record030.inverseMaps 20) record030_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame020_links_0000 record030_frame020_links_0064)
theorem record030_frame020_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 20 :=
  of_group record030 20 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record030_frame020_indices record030_frame020_graph record030_frame020_links
def record030_frame021_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0864.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0864.count (({ width := 11, code := 0x217c2984d07e0cc11819015fe3f6798f21e03b9766eadd339d728e2dc0b7c6eedc1b53646bed69a9b4f5c0b696a2cd58ab055d2b154ea7d3c2754de9a13025c4aa9312323f46c8c51622543c8690a20e410810d61a533e670cb191318610be1762e05a8b295f2b0544a61472804ec9992e2484748b911218418800f81e43b4738e11b8350668c617c2e02804f09c1342602104007c0f01d0220400780e01a0300580a0120200300500800c01000 } : Fields).get c.val)
theorem record030_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record030) (record030.maps 21) (record030.inverseMaps 21) record030_frame021_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record030) (record030.maps 21) (record030.inverseMaps 21) record030_frame021_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record030) (record030.maps 21)
      (record030.inverseMaps 21) record030_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame021_links_0000 record030_frame021_links_0064)
theorem record030_frame021_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 21 :=
  of_group record030 21 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0864
    Papers.RationalityTen.SharedFrameCatalogue.group0864_facts record030_frame021_indices record030_frame021_graph record030_frame021_links
def record030_frame022_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0376.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0376.count (({ width := 9, code := 0x2210e8642a110682405fcfc7abcde2ef76badd2e671b85badb6cb5daad368b3d9acc5f2f174b85b2d164af562a946a14fa7536994ba51228f45a250e8541a04fe7d3d9e8da6c359a8d26833994c6613017cbc5d2e16cb4582b150a45027134964a249208e462291084401f0f074381b8d44c251208c441b0d0643017088401e0e06830160a048200c050200c0400 } : Fields).get c.val)
theorem record030_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0376.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record030) (record030.maps 22) (record030.inverseMaps 22) record030_frame022_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record030) (record030.maps 22) (record030.inverseMaps 22) record030_frame022_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record030) (record030.maps 22)
      (record030.inverseMaps 22) record030_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame022_links_0000 record030_frame022_links_0064)
theorem record030_frame022_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 22 :=
  of_group record030 22 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0376
    Papers.RationalityTen.SharedFrameCatalogue.group0376_facts record030_frame022_indices record030_frame022_graph record030_frame022_links
def record030_frame023_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1000.count (({ width := 11, code := 0x21542684306e0ac1281b015ffbf8778ee5d9bad74ce81cd391712df9bb36f6d2d91af3596a6d2da233c56aac5552a6540a6549a8a5009e12123e4708d51822a44a8750aa0f410804fd9f73e27acf29dd3aa738c197e2f05c8b61662c8584ae9582a6534a414327e4e89b1302544888d11622442c821001f63dc790ed1ce38c6e8d619e31c618bd1722c42704d09812c2502104007c0f01d0220400780e01a0300580a0120200300500800c01000 } : Fields).get c.val)
theorem record030_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record030) (record030.maps 23) (record030.inverseMaps 23) record030_frame023_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record030) (record030.maps 23) (record030.inverseMaps 23) record030_frame023_indices (Fin.ofNat record030.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record030_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record030) (record030.maps 23)
      (record030.inverseMaps 23) record030_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record030_frame023_links_0000 record030_frame023_links_0064)
theorem record030_frame023_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 23 :=
  of_group record030 23 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1000
    Papers.RationalityTen.SharedFrameCatalogue.group1000_facts record030_frame023_indices record030_frame023_graph record030_frame023_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (Fin.cases (record030_frame002_supported hcells) (Fin.cases (record030_frame003_supported hcells) (Fin.cases (record030_frame004_supported hcells) (Fin.cases (record030_frame005_supported hcells) (Fin.cases (record030_frame006_supported hcells) (Fin.cases (record030_frame007_supported hcells) (Fin.cases (record030_frame008_supported hcells) (Fin.cases (record030_frame009_supported hcells) (Fin.cases (record030_frame010_supported hcells) (Fin.cases (record030_frame011_supported hcells) (Fin.cases (record030_frame012_supported hcells) (Fin.cases (record030_frame013_supported hcells) (Fin.cases (record030_frame014_supported hcells) (Fin.cases (record030_frame015_supported hcells) (Fin.cases (record030_frame016_supported hcells) (Fin.cases (record030_frame017_supported hcells) (Fin.cases (record030_frame018_supported hcells) (Fin.cases (record030_frame019_supported hcells) (Fin.cases (record030_frame020_supported hcells) (Fin.cases (record030_frame021_supported hcells) (Fin.cases (record030_frame022_supported hcells) (Fin.cases (record030_frame023_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))))))
#print axioms record030_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016
