module
prelude
public import GraphInputsRow30Part00058Data
public import RawFrameSupport
public import SharedFrameGroups011Checked
public import SharedFrameGroups013Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups018Checked
public import SharedFrameGroups019Checked
public import SharedFrameGroups020Checked
public import SharedFrameGroups021Checked
public import SharedFrameGroups023Checked
public import SharedFrameGroups024Checked
public import SharedFrameGroups025Checked
public import SharedFrameGroups029Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups044Checked
public import SharedFrameGroups045Checked
public import SharedFrameGroups046Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups063Checked
public import SharedFrameGroups064Checked
public import SharedFrameGroups070Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups104Checked
public import SharedFrameGroups105Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups107Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups110Checked
public import SharedFrameGroups111Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x6ef6ad6aa6a269b6846175d55d25bb5b45ac54353d51f50b5024fa4db4d54ce4c44bc4b54ae4a94a14554094043f73f13e43db35c35434b34332a30c3062f92f12e92d32cc2bf2a729d29128727f21e2161fc1f41ec1d11c31bb1a519d19518e18117115f15314a13d12910a1040fd0f60f00de0d70d10bf0ba0ae09f08606c05c05b05705605304a04403a03703602802602502402102001f01d01201101000e00c00b009008006005002001000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xadaa8ca87a80a78a599a794293e92091390c8568457fd7c37a979b75673b72770d6fd6eb6d96cd6b76375d95d25c95bf5b15995004fa4ef4e44b948e48247546d4604324254153f23e43d63c53ba33732d3052f52e42c02aa2a02752672572492392252071f81eb1d91c218417316515314511910a0fe0d80cd0b40a308c06c05c05b05705605304a04403a03703602802602502402102001f01d01201101000e00c00b009008006005002001000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x718de5bb3746dad919d327648c658c3125bcb6d64abe570ac54c29451ca153fa7a4e89c535a3f4408750ba1241a818e69ca38e700d99a434266ccc994306600bd96f2d4598b11612744dc9492624044c851081f03d4780ed1ce3806b8d21a2328618af1582a4530a312e24c480861062003d86d0be1482884d098124230440740dc1b02804c0941202104007c0e8120220400700c0160240400600a00800800 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3a61b78d9f5cc2b5d590ab4550255928c90c47d239115e89844420c903e80d3fc1fa0fae7c63dc9990b465942c015b08444121ec0f1876037b1b20d505fc2eb16c8b105682a31490a1441e20810087e83e61d50e707243841bb0d2067c3301890c085e82e61600a58510278136097849c2160fe07403881aa08203e01bc0be05e02e816c0b205802a8128088037013809804a023010808003a0160098048022010007803801800b005002000c0050018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x6c76986935f95b65b35ac5a553a5305135094fd4e84e14d94af4a649c49048a48647f4793f83ac3a93a439f33132b31430c3032f32ec2e72c42bd2b52ac2a82a52a029c22421920c2031fc1da1d51cc1c11b419c19618f17d17917216b15913d13212611e1131070e60dc0c00ba0b007c07606d05d05c05b05905705605304804203702702602502302102001d01601301201101000f00e00c00b00a008006005003002001000 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xad9a99a8799c94493e93592c84d84581c8097f47c17a679b75273b7277106ff6eb6d96ca6375de5d95d25c95014fa4da4cc4ba49247e4754384254154013f43e43d63c932d3203133052f52bc2aa2a02962862582492392192071f81e71c21a019118217316515511b0fe0da0ce0b407e07a06d05d05c05b05905705605304a04403702702602502302102001d01601301201101000f00e00c00b00a008006005003002001000 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0591.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0591.count (({ width := 11, code := 0x10fa1742a7c0f19e2bc177cdd9b93606b2d4da0b3a66cc6589b0d608bf97c2f35e0acd4aa94520a3123a4546a8c516220432861001fa3ec7c0f61e93ca788cb99131261cc11692c8584ae9572824f89d92e254498909111f23cc758e61be3585f8b4142268480740e21a42d85a0b215c2a8540a21182083704e098128230420800e8160260480881001e0380600b0140200300500600800800 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame004_links_0000 record001_frame004_links_0064)
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0591
    Papers.RationalityTen.SharedFrameCatalogue.group0591_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0590.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0590.count (({ width := 11, code := 0x108607c0c76ce59ca38f712d09a0b36662cb18fb1962cbf97d2f55daba5722df5baa7d422824f89e51822e43c8650a2074007f8f41e43c4768eb9d039872cc39812fa5e4b91592a6538a61452604b89591b22843c858f71ce3886e8da1a83385e0b01402684706e0d61882a0530a41402704d0941041e83504e098128230420800e8160260480881001e0380600b0140200300500600800800 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame005_links_0000 record001_frame005_links_0064)
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0590
    Papers.RationalityTen.SharedFrameCatalogue.group0590_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1b44b98562a89942494949aa48521e8fd471222103e80d3fd1fa0faa7c43dc1ea0cc8591279137882a4011f68f6c7923ae1aa0bac5b22c615a0a8452028413a083c4102010fd07cc3aa1ce0e4867c3301900c485d02da1670b005642a414b0a204d825e11808884282060e9071035014a08203e01b40d8063030017c0b205802a812808803501a00ac050027010808003a0160098048022010007803801800b004001c00c005002000c004000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa8899c93d8d88c584683a82d81f80c7f279b73b7277126ff6e96d76c96b66375d85725634fb4f24e74dd4cf4b84754254154033f43e23d43c83b932d3203133052f52bc2aa2a02492392272191e81da1cd1c21ba1ae1a019117316513512911a1090db0ce0b309b07e07a06b06a06105e05d05705605304a04403503402b02802702102001d01601301201101000f00e00c00b008007006005004003002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x69c5e65a055954e4f34ef4e54e14d54c749545944a43b42f4224154114083ad3673203152ba2b42af2a529f28e25c21e2112021f61e61dd1d81cf18b18718117c17715f15b15713813212c12811711211010c10a1051000fb0f00ea0d80d20cd0c70b50b10a809107807406606505c05905805205104e04704303503402b02802702102001d01601301201101000f00e00c00b008007006005004003002000 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record002_frame003_links_0000 record002_frame003_links_0064)
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x185ab1254c288d42097f4b72571296939495a3090be849419a07900a7f03ef9f24e486a43189880b5259a2c695f8ae256428c93109624a124992008da4622298eb473638c1bd8db064e3151830aa052828013708d44462100fe87b83c01d10e186ac3301640a785002600f4073832014a08203e01b40d8063030017c0b205802a812808803501a00ac050027010808003a0160098048022010007803801800b004001c00c005002000c004000 } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record002_frame004_links_0000 record002_frame004_links_0064)
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x69834b5a4cd1f68633dd63ab0f55aa9f53629a34a4a4451de8da469a33518a8be45c22b914e8a044e225111a6c435a1a8cce06372b7957ca9c51b27113209824ba25992b494849f24c123c91048123d91d48e246b1c80dfc6362dc15c8a284f426812d89304721fd0f907903ac1a70cb86142f01690ab046821e10107b83c01d40e206d83501720a503701b40d805f02f017409403a01b80d806a03401980ac0500270130094048012008804001800b004802000e006002800c004001 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa8aa89a82a7aa5aa2d94293d9088db84c8457fb7c379c77276375873e72a71b6fb6e86d66d06b86a45d85cf5c659b56e4fa4ef4e44bb48e4764704634554474314284183ff3f03e13d33c23bb3ab33732d2e92c02a02752672572492392251e61db1cd1c21a019118017316515311910b0fe0f10e60dc0cc0be0b20a309b06c06b06a05d05c05b04a03a03703603503403302b02802702602502401201101000c00b009008007006005003002001 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x66f66e66c66a6626545d85d35b058e5395345114ef4d64c64c14bd4b64b04ab4a149a49449248b4843f93f23ec3d23b035635234c32f30d2fa2f52f12ec2e62df2da2d42cc2c52bf2ba2b62b42af24d2492151f11db1c41b91ae1a419918e16515f15514b13412c11e11510c0fe0d50cf0c50bb0b70b30ab0a409e09508d06b06a06905d05c05b04803903603503403303202b02802702602502401201101000c00b009008007006005003002001 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0xbd76a6c0d78ae95bab4d65abb56aa9d4aa9144269cd199b31e614be96d2ce564a39431a23245d8ab13e24c418790d61542683f0620840a808ff1fbbf07caf85ee3d87a8f41e63966c8d75a7349686cf99c32f654b856c2c357cae559aa953ca6d4927b4ec9c934a5e4aa9291f23846c8b9141e13b0704de1b835e690cd99030a5c0b59662c0558a594827c4e09b12e25048c879092003f07a8ec1ce3806c8d519c320610bb16e2c0550a713425c450870d21982d05706a0d01903104c0941182201802c0480800c01401802 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record004_frame001_links_0000 (interval_append _ 64 128 148 record004_frame001_links_0064 record004_frame001_links_0128))
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1092.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1092.count (({ width := 9, code := 0xc6612fb7abc5dae972b85bedb6ab4d86af56aa54aa14ea652e9346a2cf277399bcd66731984ba572a9449a49229047a3b1b8c45e2b1489c4a230b81c01f4f87b3d5e6ef76b99c6dd6db65b0d6693419ac662b1182be5e2e16ab3592c15ca852275389b4c255268f46a1d0a8341200f87a3b9d4e872381bcd26732990c45e2e164ae562a148a04e2692c9248208f86e34168a848210c8602c15088401c0d048200c050200c0200 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record004_frame002_links_0000 (interval_append _ 64 128 148 record004_frame002_links_0064 record004_frame002_links_0128))
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1092
    Papers.RationalityTen.SharedFrameCatalogue.group1092_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1083.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1083.count (({ width := 9, code := 0xc6612fb7abc5dae972b85bedb6ab4d86af56aa54aa14ea652e9346a2cf277399bcd66731984ba572a9449a49229047a3b1b8c45e2b1489c4a230b81c01f4f87b3d5e6ef76b99c6dd6db65b0d6693419ac662b1182be5e2e16ab3592c15ca852275389b4c255268f46a1d0a8341200f87a3b9d4e872381bcd26732990c45e2e164ae562a148a04e2692c9248208f86e34168a848210c8602c15088401c0d048200c050200c0200 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record004_frame003_links_0000 (interval_append _ 64 128 148 record004_frame003_links_0064 record004_frame003_links_0128))
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1083
    Papers.RationalityTen.SharedFrameCatalogue.group1083_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
def record004_frame004_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x9e333659cac9532925149d92924e4648490317e1d4388690ca1742b8410760d41081af7dee3d77a2f31e2bbc772ec5d2ba0730e4dc7b88708de1bab6f6c2d71ab350692d15a0b0e5c8b79692ce590b15602b956a9fd3da6c4cc97d2ea544949111f22e4508890ca124167f4f91ec3d6784ed9a6344648c59862f85d0b79612b0528a313c2704cc9392122c44c891082043f8778e91c63786b8cf19631c610c01702c4560a914c2784b89311822c418810ce1942d0570660c81802f04a0901102101802c0480800c01401802 } : Fields).get c.val)
theorem record004_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record004_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record004) (record004.maps 4)
      (record004.inverseMaps 4) record004_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record004_frame004_links_0000 (interval_append _ 64 128 148 record004_frame004_links_0064 record004_frame004_links_0128))
theorem record004_frame004_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 4 :=
  of_group record004 4 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record004_frame004_indices record004_frame004_graph record004_frame004_links
def record004_frame005_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0640.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0640.count (({ width := 8, code := 0xc9c8c7c6c5c4c3c2c0bfbebcbbb9b8b7b6b5b4b3b1b0afadacaaa9a8a7a6a5a3a2a19f9e9c9b9a999896959492918f8e8d8c8b8a898885848281807e7d7c7b787775747371706f6c6b6a686766646261605e5d5c5b585756545352504e4b4a48474644434241403e3d3c39383635343231302f2e2c2b2a29282625242322201f1d1c1a19151412110f0e0c0b0908060504030100 } : Fields).get c.val)
theorem record004_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0640.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0640.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0640.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0640.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record004_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0640.localPairCheck (smallEmbedding record004) (record004.maps 5)
      (record004.inverseMaps 5) record004_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record004_frame005_links_0000 (interval_append _ 64 128 148 record004_frame005_links_0064 record004_frame005_links_0128))
theorem record004_frame005_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 5 :=
  of_group record004 5 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0640
    Papers.RationalityTen.SharedFrameCatalogue.group0640_facts record004_frame005_indices record004_frame005_graph record004_frame005_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (Fin.cases (record004_frame004_supported hcells) (Fin.cases (record004_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
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
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x74e36d9736add5642a314eea5051da84d2ae94949aa48521e8fd471235d1888a844ea2210a4842417a07d01a7fa3f4999cb525942ac150ca3850726f908c82a4011f68f6c7923ae1d18e406e83691aa0c7861c2fb1758b6458c2b510a083c4102010fd07cc3ca1de0e807243681ad0d2867c3301900c506042f416c0b285802b21520a5851026c12f090846022210a08183f01d207c03c818c0c005902c01580aa04402080ac050021010007803a016009804402000f007003401800b004802000c005002000c004000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x62eafe157ca5b526a8494049e24e926d527e93248da4091de8de461a2e114e88c44321d50648204071ff8fd87da3e91b00ca864730717fcbc25d22db1524a7c52a28a94149ee4e226d133096e4b325291c48c845622490f085c4261b08d4067432418a8c185d02d915f8ac44f026d12f894848e23911888884221f20f2875838c1b50d4067030a1790b2055428412f09104581d607c03c818c0c005902c01580aa04402080ac050021010007803a016009804402000f007003401800b004802000c005002000c004000 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record006_frame002_links_0000 record006_frame002_links_0064)
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x6ec6c36165d75d25bb5b259d59257d53252e52351650a4ff4ef4e84db4c84c44bc49f49949148847f47446e3da39b39637e37335d3543412f62f22e72da2cc2bf2ac2a729c28c28828026225924e2462402382321c51c11bb1b41ae1a619618e17f17d16b16515c15514f14614013c13812e12712311e11a11410d1000f90ed0e90e40de0d90d30c407b07806205f05805705505404404102b02802102001e01d01601301101000f00e00d00c00b009008006005004003002000 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record006_frame003_links_0000 record006_frame003_links_0064)
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
def record006_frame004_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xadba9499e94a93e9209138f58e88c684e84683a82d81f80c7f27e37d27ba7aa79b76f76074f73b7277127006395e45d95bf5b15905835645024fb4f24e74dd4cf4b84af4a148b4834754524444354254154033f533832d3203133052f52d92cd2ac2a027526725924923922721a2071f81d91cb1c21ba1ae1a019117316514613512911a1090fc0db07a07706105e05705605405304404102b02802102001e01d01601301101000f00e00d00c00b009008006005004003002000 } : Fields).get c.val)
theorem record006_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record006_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record006) (record006.maps 4)
      (record006.inverseMaps 4) record006_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record006_frame004_links_0000 record006_frame004_links_0064)
theorem record006_frame004_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 4 :=
  of_group record006 4 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record006_frame004_indices record006_frame004_graph record006_frame004_links
def record006_frame005_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0606.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0606.count (({ width := 11, code := 0xa6347e694b395f2764c48f9131f62bc538930f61a42a84106e0a4047fefe1ecbd178ef01dbba9744d299332462cc4182b005e0b4567aca582ae557aa3540a6d44a8650099d2f25749c9251ea353c677cec1ce38a6f8d71a732a640bc1702d0588af15329c5149f1322584988f9142164147c8f41ca370698c917e2d84e8660c81502904b0941202383f07a0a8140210400780e8160260440800f01c0340600b0120200300500800c01000 } : Fields).get c.val)
theorem record006_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record006_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record006) (record006.maps 5)
      (record006.inverseMaps 5) record006_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record006_frame005_links_0000 record006_frame005_links_0064)
theorem record006_frame005_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 5 :=
  of_group record006 5 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0606
    Papers.RationalityTen.SharedFrameCatalogue.group0606_facts record006_frame005_indices record006_frame005_graph record006_frame005_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (Fin.cases (record006_frame004_supported hcells) (Fin.cases (record006_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1c76d7b69b34b5a30d11685b40d9f8cf66772c8162aade5652a8d51ea6c4da26a52e495e49ba48d2008ef47423851b48d3465231517c8b545822ad1488964479df0daa6c43489a04ce265f32618e0c505802b794f0a5851c28513dc9c64d326413049744b3256929093e498247922890247b23b91bc8d23911c10d1065e3071798b285722a914c8a284f425b12608b443220a0f707803ac1c60db069c32e1780b4852826c12708583f41ee0f007483881b60d503901bc0c606001d00dc06a03401900c4056028013009404602200b004c01800b00500240100060028010006002 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record007_frame001_links_0000 (interval_append _ 64 128 138 record007_frame001_links_0064 record007_frame001_links_0128))
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1998c5b5fd2fb5768ba45ca2e016e0b605a8a9694a0a1450227913a89b649fa4d51e28e045d22a510e878430212506a8234062004fde7d83e99f34f6e7883bb1b04ca664430597f0bd65de2e796f8b6a54929d94089e84e626b93249764b22541258908474233914889843f215109c8284041fd0f947b23611a98c5c6102ea16d8b0056229d14509e04da25212388c444020f0f887903ac1c60da86a03381850bc85902a6140090845420e0f907483781a80c903901bc0c606001d00dc06a03401900c4056028013009404602200b004c01800b00500240100060028010006002 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record007_frame002_links_0000 (interval_append _ 64 128 138 record007_frame002_links_0064 record007_frame002_links_0128))
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb19ad3a9da89a70a63a57a43a36a2aa1494693f9239168f88eb8c984e84782180e7e67d57ad79c79378377276374b73e72a70e7036f66e46bf6ab63c5e05d85bc5ae59c58d58056f5625024fa4da4cc4bc4ac49e48f4804764704634554474314284183ff3f83e13d33ca3b33a333832e3082f82dc2d02af2a029628627526724923921a2051f61d71c91c21ba1ae1a01911731651461331271070fa0f10e60d90cc0be0b507006d06105e03a03703503403203102b02802602502302201601300c00b00a009008006005004003002 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record007_frame003_links_0000 (interval_append _ 64 128 138 record007_frame003_links_0064 record007_frame003_links_0128))
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x6a668a67566e66766466165b65765364b5da5d55c35b75a459858253b53652451e5074fd4e34d64d14cc4c64c14ba4b64b04a84a349f49948d4864443ff3f93e63dc3d33ca3bd3b13a535c35634333c33032731f30e3022fa2f52f12ec2e62df2da2d42cc2c72bf2ba2b82b22ad24e24a22a22020b1fe1e51db1d51cc1c41b91a419918617817015b15114b14613e13412c11510c0f60ea0e10cb0c10bb0b70b20ab0a409f06f06c06105e03903603403303103002b02802602502302201601300c00b00a009008006005004003002 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record007_frame004_links_0000 (interval_append _ 64 128 138 record007_frame004_links_0064 record007_frame004_links_0128))
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
def record007_frame005_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0600.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0600.count (({ width := 11, code := 0x20fc0f7f8fe9f9bf07dcfa5f33e37bce89d038f70adedba36a68cd119ab3064ac7987308606bf97caf35d6ba571ada5b2b55682c6582a5939a6f4bc95528a4b4888f91d217426804fd9f53e07b0f19de3b6760ea1cf392708e01bb3666c8d59a6348678cd1752e6588ad1502924e89b133254498909192244247f8fa1e03a4728e01b6348668c41842e0590a913c2604a09111a224428810ca1882c8570700d4198320600bc1502804c0941182202c04c0600b0140240400600a01001802 } : Fields).get c.val)
theorem record007_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0600.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record007_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record007) (record007.maps 5)
      (record007.inverseMaps 5) record007_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record007_frame005_links_0000 (interval_append _ 64 128 138 record007_frame005_links_0064 record007_frame005_links_0128))
theorem record007_frame005_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 5 :=
  of_group record007 5 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0600
    Papers.RationalityTen.SharedFrameCatalogue.group0600_facts record007_frame005_indices record007_frame005_graph record007_frame005_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (Fin.cases (record007_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb35b2fb2cb29b24b1dafbaf4aefae7adead69d69cd9c69bd9b19a697f97496a95e95394889488987e86f86085284783c82f82180e7fc7eb7da7c97b379c79378377276375366b66465e65864d64061b61560c6015f55e85d95d25c95bf5b15a059558857b5684fa4ef4e44da4cc4bd47647046345544743937b37236535734a33f32e3233163082f82ea2de2d22c62b42a029628627526725a2442342212141c21ba1ae1a01911831331271181070f10e60d90cc06f06e06d06c02602502402300c00b00a009006005004003 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame001_links_0000 (interval_append _ 64 128 136 record008_frame001_links_0064 record008_frame001_links_0128))
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xc0cc06c01bfabf0be9bbfbb5bb0ba5b98b90a7ba6fa66a60a4ea44a1ea12a0ea019ef9e391e91190a8fb8e78d78c88b68aa89e88c87c86f8588448308138037f87ed7d77c36c46b66ac6a569868e67066365a65264563b62b61d61360b5fe5f35eb5db5cf5c354053052751c50e5014b64a749c49348547a3c23b33a639d38c37f36e35b34e3443343223163022f22e22c72b72ad2a129328626e25f24f23f1e21d51cd1c41b51a81531411311211020f50e80da07107006f06e02602502402300c00b00a009006005004003 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame002_links_0000 (interval_append _ 64 128 136 record008_frame002_links_0064 record008_frame002_links_0128))
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0xf17c3f07bfef7bbee3b5ecbafeb3a9daf67d8f5fd6f57d3b4bd2345d0b3fc5310c3308c0efebeaf6bcaeeba6e4b7ad5b32c3aeeb7aceafaaea799a639825d96a579424d92a47912418f63a8de348c62e8b2268821a7f5fa7ddf37bdeb715c26fdbb6ddb35cd6f5ad675895d561555494f52d475113c4d12c491214791a4591242d053fcfa37cdb35cd333ccb2989f2609321c821f47814c521445009825090230300b028090180501003 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame003_links_0000 (interval_append _ 64 128 136 record008_frame003_links_0064 record008_frame003_links_0128))
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
def record008_frame004_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x692b475a2ad0f683b4059a2cc665db2cd950ca15abad1d674b2e590ac595c6ad25622ae5556aa64ec271536a9a84cc263d3049704af253527692e49324351ec8e0462a2cd14289043f21c8ec07523a39cf0e6272737b9b94db46cb3601ad0d4e69934419f0cd666132e9930c6e6262d3165cb1457b2b71594a3850b27e13b49bc4d32030fd07ca3d81e48efc76039e1c70df86dc3631ae8d1c6643201830bd05c62d31610ae054428d13d89a43fa1ee0f007443861b90b1053427c12e08783fc1e40e503881c00de06e0130094048023006002c0140090030014008003 } : Fields).get c.val)
theorem record008_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 4)
      (record008.inverseMaps 4) record008_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame004_links_0000 (interval_append _ 64 128 136 record008_frame004_links_0064 record008_frame004_links_0128))
theorem record008_frame004_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 4 :=
  of_group record008 4 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record008_frame004_indices record008_frame004_graph record008_frame004_links
def record008_frame005_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0xa1542283505a0940a7f4fa9ef3d6794ef96d2c255ca894927e4a48c9112123e47986b0ba14c2684106a0bc0e80d009fcbf07d6f81ea3c977eee5d93af750e81a4341678ce59a32e648c7d8d317624c3584b045febed7aaf05dab956ead5558a8d4ea9a526a3932a634b69612aa4d414808fd1f53dc798f11d93a4734e21bc3706c8d61a633e660c918e30c600bb16c2c4564969282424748b9101c6360668c016029c4e8940c21802f85e04c0941202301802c0500900c01402003 } : Fields).get c.val)
theorem record008_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record008) (record008.maps 5)
      (record008.inverseMaps 5) record008_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame005_links_0000 (interval_append _ 64 128 136 record008_frame005_links_0064 record008_frame005_links_0128))
theorem record008_frame005_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 5 :=
  of_group record008 5 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record008_frame005_indices record008_frame005_graph record008_frame005_links
def record008_frame006_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xe2b88e1b84e0b80df77addf74dc76ec9f22c7719c5310c1b02bfefbbe2f5b2ac5b02bcadeb3ac2acaa2a4a829ca5e8ca167e9e6779d2729be6c8b228892218761a8521083209816027fdfd7edf97ddf57cdec79de2711c2701be6f1ba6719a66196651925514f529465053d4e5354c52e4a9274951944d0d41903400fe3ecf93b4e838cde314c12f4ba2d8b3234872087d1c86e1ac681304b1284908c22084200300b028090180501003 } : Fields).get c.val)
theorem record008_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record008) (record008.maps 6)
      (record008.inverseMaps 6) record008_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame006_links_0000 (interval_append _ 64 128 136 record008_frame006_links_0064 record008_frame006_links_0128))
theorem record008_frame006_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 6 :=
  of_group record008 6 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record008_frame006_indices record008_frame006_graph record008_frame006_links
def record008_frame007_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0200.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0200.count (({ width := 10, code := 0x94e5193e4d92e4991a439023d8ea3781e04805fe7edf87d1f27c1ee7b1ea729c7711c16f9bb6e5b66cdb06b5aa699a16719764d9163d8d62d895c56f5b56b5a567595635855f5755b56557555535454f5354a51d444b92c4a9284992445d1544d1143d0d3c0ec3a0e4380dc360d5348cf330c931cc22f4b82c8b02b8ac2a8a8290a02709822086210822007e19c641845e16858158541144410c420801f0781d0300b028090180501003 } : Fields).get c.val)
theorem record008_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record008) (record008.maps 7)
      (record008.inverseMaps 7) record008_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame007_links_0000 (interval_append _ 64 128 136 record008_frame007_links_0064 record008_frame007_links_0128))
theorem record008_frame007_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 7 :=
  of_group record008 7 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0200
    Papers.RationalityTen.SharedFrameCatalogue.group0200_facts record008_frame007_indices record008_frame007_graph record008_frame007_links
def record008_frame008_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0785.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0785.count (({ width := 10, code := 0xa1683a067f9f67b9e2759ca6f9b2698fe3b8de338be2b8962287e1c866167f5fa7ddf47c5ee7b1e9799e3781dd765d4741cc725c7715c3705bf66997651916398b621856097f5f1795d9745c9705b96c5a9665895e51d4550d414fd3d4bd2d4ad2949d253f4f93d4f13b4e9394e237cdc364d6350ce320c22ecb92dcb52ccb12aca62849c22c8921c8520c8119c641845e16457154531144410c4207c1e0741c0300b028090180501003 } : Fields).get c.val)
theorem record008_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record008) (record008.maps 8)
      (record008.inverseMaps 8) record008_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame008_links_0000 (interval_append _ 64 128 136 record008_frame008_links_0064 record008_frame008_links_0128))
theorem record008_frame008_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 8 :=
  of_group record008 8 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0785
    Papers.RationalityTen.SharedFrameCatalogue.group0785_facts record008_frame008_indices record008_frame008_graph record008_frame008_links
def record008_frame009_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0336.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0336.count (({ width := 10, code := 0x81e0580e017fdfd7e9f77d1f17b9eb725c670dc06f5ba6d9b46c9b06b9ac66997651916398b6258660d805f57a5d9735c16d5ad6959d6558d615394c5294851944509404f93c4e9384d9344c9304b92c4a9284992443d0d42d0941d053f0fa3e0f63d0f2368d6348ce328c6308bf2f0b92d8b32c4ad2a4a52809e2709a260962488e228861dc751cc711bc6d158531404d12c4911c450f03b0e8390781d0701b02c0a024080180501003 } : Fields).get c.val)
theorem record008_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0336.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record008) (record008.maps 9)
      (record008.inverseMaps 9) record008_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame009_links_0000 (interval_append _ 64 128 136 record008_frame009_links_0064 record008_frame009_links_0128))
theorem record008_frame009_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 9 :=
  of_group record008 9 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0336
    Papers.RationalityTen.SharedFrameCatalogue.group0336_facts record008_frame009_indices record008_frame009_graph record008_frame009_links
def record008_frame010_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0273.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0273.count (({ width := 10, code := 0x8420e8320a8220680e007f5fa7ddf4749cf731c9719c36fdbd6edb96ddb568da06759a65d946498f63189619835fd7b5dd735c16e5b16a5a16654d5153d4d52d4951d4550d414fd3d4ed394dd354cd314bd2d4ad29451124410e4310a3f4fb3e4f73d4f336cd734ccf32cc730cc02f4ba2dcb42c8ae2a8a62849f2749b2649724c8f22c871e0761d0721c06e15c541444e12c4911c450f03b0e8390781d0701b02c0a024080180501003 } : Fields).get c.val)
theorem record008_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0273.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record008) (record008.maps 10)
      (record008.inverseMaps 10) record008_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame010_links_0000 (interval_append _ 64 128 136 record008_frame010_links_0064 record008_frame010_links_0128))
theorem record008_frame010_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 10 :=
  of_group record008 10 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0273
    Papers.RationalityTen.SharedFrameCatalogue.group0273_facts record008_frame010_indices record008_frame010_graph record008_frame010_links
def record008_frame011_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1074.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1074.count (({ width := 10, code := 0xf37caf27c8f1bc4ef7baee7b8edbb4e037bddf76dcb6ed7f59d5752d3f4bc7317c4f0fc3707c0f00beef7bd2efbaee6b8adab52ceb26c4b02bb9ee769ca719b66996a5794a4e92e469063c8e2348ca2c8a624882187d5ef7ade8795e173dc9711bf6edb65dd735b569599615755954d4f5314750d404f5394d5314a9254851c4591042d06394e1368d5344cc2bca92909f254932408d158551505309825090230300b028090180501003 } : Fields).get c.val)
theorem record008_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1074.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (smallEmbedding record008) (record008.maps 11) (record008.inverseMaps 11) record008_frame011_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (smallEmbedding record008) (record008.maps 11) (record008.inverseMaps 11) record008_frame011_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (smallEmbedding record008) (record008.maps 11) (record008.inverseMaps 11) record008_frame011_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (smallEmbedding record008) (record008.maps 11)
      (record008.inverseMaps 11) record008_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame011_links_0000 (interval_append _ 64 128 136 record008_frame011_links_0064 record008_frame011_links_0128))
theorem record008_frame011_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 11 :=
  of_group record008 11 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1074
    Papers.RationalityTen.SharedFrameCatalogue.group1074_facts record008_frame011_indices record008_frame011_graph record008_frame011_links
def record008_frame012_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0840.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0840.count (({ width := 11, code := 0x8ef1ce38c6b8d31962b4548a312e244467f0fcdf83eb7cef91ebbcf79cf21e33bf704df1bcb746ded9db135f6b4d59a8b4b68acf99d334658ca59432463ec61692cf596b19612c0564ab154aa553ea6548a8d514a153fa7b4ea9b9342644648c11622644288103a054067fcfc9f435e69cd199e32e640c51872fe5e8b996e2ce590af1572a4538a414527e4dc9792c24847c7d0f51e03b4730df1782d8590ac14827c4c0940b61682c85804c0941202301802c0500900c01402003 } : Fields).get c.val)
theorem record008_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record008) (record008.maps 12) (record008.inverseMaps 12) record008_frame012_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record008) (record008.maps 12) (record008.inverseMaps 12) record008_frame012_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record008) (record008.maps 12) (record008.inverseMaps 12) record008_frame012_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record008) (record008.maps 12)
      (record008.inverseMaps 12) record008_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame012_links_0000 (interval_append _ 64 128 136 record008_frame012_links_0064 record008_frame012_links_0128))
theorem record008_frame012_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 12 :=
  of_group record008 12 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0840
    Papers.RationalityTen.SharedFrameCatalogue.group0840_facts record008_frame012_indices record008_frame012_graph record008_frame012_links
def record008_frame013_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0360.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0360.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0360.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0360.localPairCheck (smallEmbedding record008) (record008.maps 13) (record008.inverseMaps 13) record008_frame013_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0360.localPairCheck (smallEmbedding record008) (record008.maps 13) (record008.inverseMaps 13) record008_frame013_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0360.localPairCheck (smallEmbedding record008) (record008.maps 13) (record008.inverseMaps 13) record008_frame013_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0360.localPairCheck (smallEmbedding record008) (record008.maps 13)
      (record008.inverseMaps 13) record008_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame013_links_0000 (interval_append _ 64 128 136 record008_frame013_links_0064 record008_frame013_links_0128))
theorem record008_frame013_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 13 :=
  of_group record008 13 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0360
    Papers.RationalityTen.SharedFrameCatalogue.group0360_facts record008_frame013_indices record008_frame013_graph record008_frame013_links
def record008_frame014_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0976.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0976.count (({ width := 10, code := 0xde376dd773dcb70d8b5fd7b5dd735ac9b22c7718c5312c1303c02fdbeefab3ecbb26c6b16c1aeeb9ad2afab2a9a8e9da6a93a3689a16819fe7d9023c8e2368c62c87e1c8661784a0d81a03809fe7f1f87cded7a9e4711c2701bf6f1ba69da36859d66597569555414d525445013c4e1344bd2a49d254891c459104310740d003e4f43c8ea348cc320c4300bc28c9e264962348b2208314c521445009825090230300b028090180501003 } : Fields).get c.val)
theorem record008_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record008) (record008.maps 14) (record008.inverseMaps 14) record008_frame014_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record008) (record008.maps 14) (record008.inverseMaps 14) record008_frame014_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record008) (record008.maps 14) (record008.inverseMaps 14) record008_frame014_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record008) (record008.maps 14)
      (record008.inverseMaps 14) record008_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame014_links_0000 (interval_append _ 64 128 136 record008_frame014_links_0064 record008_frame014_links_0128))
theorem record008_frame014_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 14 :=
  of_group record008 14 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0976
    Papers.RationalityTen.SharedFrameCatalogue.group0976_facts record008_frame014_indices record008_frame014_graph record008_frame014_links
def record008_frame015_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0770.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0770.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0770.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0770.localPairCheck (smallEmbedding record008) (record008.maps 15) (record008.inverseMaps 15) record008_frame015_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0770.localPairCheck (smallEmbedding record008) (record008.maps 15) (record008.inverseMaps 15) record008_frame015_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0770.localPairCheck (smallEmbedding record008) (record008.maps 15) (record008.inverseMaps 15) record008_frame015_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0770.localPairCheck (smallEmbedding record008) (record008.maps 15)
      (record008.inverseMaps 15) record008_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame015_links_0000 (interval_append _ 64 128 136 record008_frame015_links_0064 record008_frame015_links_0128))
theorem record008_frame015_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 15 :=
  of_group record008 15 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0770
    Papers.RationalityTen.SharedFrameCatalogue.group0770_facts record008_frame015_indices record008_frame015_graph record008_frame015_links
def record008_frame016_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0330.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0330.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0330.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0330.localPairCheck (smallEmbedding record008) (record008.maps 16) (record008.inverseMaps 16) record008_frame016_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0330.localPairCheck (smallEmbedding record008) (record008.maps 16) (record008.inverseMaps 16) record008_frame016_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0330.localPairCheck (smallEmbedding record008) (record008.maps 16) (record008.inverseMaps 16) record008_frame016_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0330.localPairCheck (smallEmbedding record008) (record008.maps 16)
      (record008.inverseMaps 16) record008_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame016_links_0000 (interval_append _ 64 128 136 record008_frame016_links_0064 record008_frame016_links_0128))
theorem record008_frame016_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 16 :=
  of_group record008 16 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0330
    Papers.RationalityTen.SharedFrameCatalogue.group0330_facts record008_frame016_indices record008_frame016_graph record008_frame016_links
def record008_frame017_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0252.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0252.count (({ width := 10, code := 0x88a218821f87a1d8721b86a198621780a01801ff7f9fd7e9f97e1f77d9f5789e0779dc769d875dd6755d474dd173dcb71dc36f9bb6ddb36bdab61183609816017f5ed795e1775d9755d1735c56f5b56a5a1645815c53d4e5354c52d4a5013d4e5354c52d3ecf73d0f13b8ec3ace9398e3380dd368d8358d4340cc320c4300bd2f0b92d0b12689724c8f22c871cc701bc6c1845d164551003f0f83d088210801f0300b028090180501003 } : Fields).get c.val)
theorem record008_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record008) (record008.maps 17) (record008.inverseMaps 17) record008_frame017_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record008) (record008.maps 17) (record008.inverseMaps 17) record008_frame017_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record008) (record008.maps 17) (record008.inverseMaps 17) record008_frame017_indices (Fin.ofNat record008.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record008_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record008) (record008.maps 17)
      (record008.inverseMaps 17) record008_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record008_frame017_links_0000 (interval_append _ 64 128 136 record008_frame017_links_0064 record008_frame017_links_0128))
theorem record008_frame017_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 17 :=
  of_group record008 17 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0252
    Papers.RationalityTen.SharedFrameCatalogue.group0252_facts record008_frame017_indices record008_frame017_graph record008_frame017_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (Fin.cases (record008_frame004_supported hcells) (Fin.cases (record008_frame005_supported hcells) (Fin.cases (record008_frame006_supported hcells) (Fin.cases (record008_frame007_supported hcells) (Fin.cases (record008_frame008_supported hcells) (Fin.cases (record008_frame009_supported hcells) (Fin.cases (record008_frame010_supported hcells) (Fin.cases (record008_frame011_supported hcells) (Fin.cases (record008_frame012_supported hcells) (Fin.cases (record008_frame013_supported hcells) (Fin.cases (record008_frame014_supported hcells) (Fin.cases (record008_frame015_supported hcells) (Fin.cases (record008_frame016_supported hcells) (Fin.cases (record008_frame017_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x89288a88688087b87584283a83683082b82572371a70c6ff6f66e862f62661860b6025f45cd5c85c15bc5b55ae5105095024fc4f54ee4bb4af4a549a48e48247847046745d4534464374304294223f53ed3e43da3d03c33b33a739d39238637a36e36736035935635034934333e3382cf2be2b02a129328527726625824923b22d2041f91eb1df1d21c61b91b01a819f16e16315514913c1301000f70ef0e60dc0d60d00cb04304204104003903803703602602502402300c00b00a009006005004003 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record009_frame001_links_0000 (interval_append _ 64 128 130 record009_frame001_links_0064 record009_frame001_links_0128))
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x2ff5fdbf57daf85edb9b71ae0dbab676b67bcf09d73926ecd78c91762ac4f89310e0fc1882102a023fe768eb9d33a0732e4dc137c6e8db9b3b616bcd65aa34f694d159eb37660ca5842ff5f0bc1742e05b0b4164ac357caed57aa553ea654928b5069ed3b2714107fcfc1f03d0780ec1d1392704de1b730a5f4bb1702d65a0ae1522985189191c22a43c849021c0364690ce1842ec5a0b00841042003f0720e01b83604c0941202301802c0500900c01402003 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record009_frame002_links_0000 (interval_append _ 64 128 130 record009_frame002_links_0064 record009_frame002_links_0128))
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1061.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1061.count (({ width := 8, code := 0x81807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1061.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1061.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1061.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1061.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1061.localPairCheck (smallEmbedding record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record009_frame003_links_0000 (interval_append _ 64 128 130 record009_frame003_links_0064 record009_frame003_links_0128))
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1061
    Papers.RationalityTen.SharedFrameCatalogue.group1061_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
def record009_frame004_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1065.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1065.count (({ width := 8, code := 0x81807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1065.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1065.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1065.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1065.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record009_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1065.localPairCheck (smallEmbedding record009) (record009.maps 4)
      (record009.inverseMaps 4) record009_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record009_frame004_links_0000 (interval_append _ 64 128 130 record009_frame004_links_0064 record009_frame004_links_0128))
theorem record009_frame004_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 4 :=
  of_group record009 4 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1065
    Papers.RationalityTen.SharedFrameCatalogue.group1065_facts record009_frame004_indices record009_frame004_graph record009_frame004_links
def record009_frame005_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1056.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1056.count (({ width := 8, code := 0x81807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1056.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1056.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1056.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1056.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record009_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1056.localPairCheck (smallEmbedding record009) (record009.maps 5)
      (record009.inverseMaps 5) record009_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record009_frame005_links_0000 (interval_append _ 64 128 130 record009_frame005_links_0064 record009_frame005_links_0128))
theorem record009_frame005_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 5 :=
  of_group record009 5 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1056
    Papers.RationalityTen.SharedFrameCatalogue.group1056_facts record009_frame005_indices record009_frame005_graph record009_frame005_links
def record009_frame006_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1058.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1058.count (({ width := 8, code := 0x81807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1058.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1058.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1058.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1058.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record009_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1058.localPairCheck (smallEmbedding record009) (record009.maps 6)
      (record009.inverseMaps 6) record009_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record009_frame006_links_0000 (interval_append _ 64 128 130 record009_frame006_links_0064 record009_frame006_links_0128))
theorem record009_frame006_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 6 :=
  of_group record009 6 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1058
    Papers.RationalityTen.SharedFrameCatalogue.group1058_facts record009_frame006_indices record009_frame006_graph record009_frame006_links
def record009_frame007_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1053.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1053.count (({ width := 8, code := 0x81807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1053.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1053.localPairCheck (smallEmbedding record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1053.localPairCheck (smallEmbedding record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1053.localPairCheck (smallEmbedding record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record009_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1053.localPairCheck (smallEmbedding record009) (record009.maps 7)
      (record009.inverseMaps 7) record009_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record009_frame007_links_0000 (interval_append _ 64 128 130 record009_frame007_links_0064 record009_frame007_links_0128))
theorem record009_frame007_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 7 :=
  of_group record009 7 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1053
    Papers.RationalityTen.SharedFrameCatalogue.group1053_facts record009_frame007_indices record009_frame007_graph record009_frame007_links
def record009_frame008_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1054.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1054.count (({ width := 8, code := 0x81807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1054.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1054.localPairCheck (smallEmbedding record009) (record009.maps 8) (record009.inverseMaps 8) record009_frame008_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1054.localPairCheck (smallEmbedding record009) (record009.maps 8) (record009.inverseMaps 8) record009_frame008_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1054.localPairCheck (smallEmbedding record009) (record009.maps 8) (record009.inverseMaps 8) record009_frame008_indices (Fin.ofNat record009.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record009_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1054.localPairCheck (smallEmbedding record009) (record009.maps 8)
      (record009.inverseMaps 8) record009_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record009_frame008_links_0000 (interval_append _ 64 128 130 record009_frame008_links_0064 record009_frame008_links_0128))
theorem record009_frame008_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 8 :=
  of_group record009 8 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1054
    Papers.RationalityTen.SharedFrameCatalogue.group1054_facts record009_frame008_indices record009_frame008_graph record009_frame008_links
def record009_frame009_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb35b2fb2cb29b24b1dafbaf4aefae7adead698197a97096395894e84783c82f82180e7fc79c79378377276375366966165b65364863a6196106075fc5f05e25d95d25c95bf5b15a058957c56b55d53f53752d5225155074fa4ef4e44da4cc4bd4a849a48c47c47647046345544743937a37036335534833d32e3233163082f82ea2a029628627526725a2452352242161c21ba1ae1a01911831331271181070f10e60d90cc04304204104003903803703602602502402300c00b00a009006005004003 } : Fields).get c.val)
theorem record009_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 9) (record009.inverseMaps 9) record009_frame009_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 9) (record009.inverseMaps 9) record009_frame009_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 9) (record009.inverseMaps 9) record009_frame009_indices (Fin.ofNat record009.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record009_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 9)
      (record009.inverseMaps 9) record009_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record009_frame009_links_0000 (interval_append _ 64 128 130 record009_frame009_links_0064 record009_frame009_links_0128))
theorem record009_frame009_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 9 :=
  of_group record009 9 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record009_frame009_indices record009_frame009_graph record009_frame009_links
def record009_frame010_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x27ecfb9f33de7acf29cb38e704dd9a73462945189f13224c3e7b8f5de8bcc78aefdcc39371ee21c237b656c9590b1b620c2d80afc5f0bc575ae15c0b6d6bad359eb2d61abe574ad15229f530a3d4327e4f69d93826c4cc9852d2514969011f2384668b91421e396718e09b935c694d119c32e648c59822b054ca814a28c4f89a9302504747f0fa1ea3bc748e418e3085f0b81582a45209e07e0f81e83c06e0d81a83404a0901182201802c0500900c01402003 } : Fields).get c.val)
theorem record009_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record009) (record009.maps 10) (record009.inverseMaps 10) record009_frame010_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record009) (record009.maps 10) (record009.inverseMaps 10) record009_frame010_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record009) (record009.maps 10) (record009.inverseMaps 10) record009_frame010_indices (Fin.ofNat record009.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record009_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record009) (record009.maps 10)
      (record009.inverseMaps 10) record009_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record009_frame010_links_0000 (interval_append _ 64 128 130 record009_frame010_links_0064 record009_frame010_links_0128))
theorem record009_frame010_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 10 :=
  of_group record009 10 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record009_frame010_indices record009_frame010_graph record009_frame010_links
def record009_frame011_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xc0cc06c01bfabf0be9bbfbb5bb0ba5b98b90a23a17a10a079f49e88c88b68aa89e88c87c8138037f87ed7d77c36bf6b16aa6a069568b66b65e65864c64063662b61d61360b5fe5f35dd5d05c45b458f58157856e56055354053052751c50e5014ed4dd4cf4c04b64a749c49348547a3c03b13a539a38b37e36e35b34e3443343222c72b72ad2a12932862712612512421e21d51cd1c41b51a81531411311211020f50e80da04304204104003903803703602602502402300c00b00a009006005004003 } : Fields).get c.val)
theorem record009_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 11) (record009.inverseMaps 11) record009_frame011_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 11) (record009.inverseMaps 11) record009_frame011_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 11) (record009.inverseMaps 11) record009_frame011_indices (Fin.ofNat record009.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record009_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 11)
      (record009.inverseMaps 11) record009_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record009_frame011_links_0000 (interval_append _ 64 128 130 record009_frame011_links_0064 record009_frame011_links_0128))
theorem record009_frame011_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 11 :=
  of_group record009 11 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record009_frame011_indices record009_frame011_graph record009_frame011_links
def record009_frame012_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0xf17c3f07bfef7bbee3b5ecbafeb3a9d434dd2b47d1341beaf6bcaeeba6e4aeeb7aceafaaea79926197a5b9625593a4b9224590a3f8f63a8de348c62e89e2186e1784e108360a81a027f5fa7ddf37bdeb789d8739c8715c26fdbb6ddb35c96e5a9665855c561555494f52d47491214791a4591243106400fb37cdb35cd333ccb2989f2609321c821f4780e8390e0370d8350d03309825090230300b028090180501003 } : Fields).get c.val)
theorem record009_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record009) (record009.maps 12) (record009.inverseMaps 12) record009_frame012_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record009) (record009.maps 12) (record009.inverseMaps 12) record009_frame012_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record009) (record009.maps 12) (record009.inverseMaps 12) record009_frame012_indices (Fin.ofNat record009.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record009_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record009) (record009.maps 12)
      (record009.inverseMaps 12) record009_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record009_frame012_links_0000 (interval_append _ 64 128 130 record009_frame012_links_0064 record009_frame012_links_0128))
theorem record009_frame012_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 12 :=
  of_group record009 12 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record009_frame012_indices record009_frame012_graph record009_frame012_links
def record009_frame013_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0967.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0967.count (({ width := 8, code := 0x81807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0967.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0967.localPairCheck (smallEmbedding record009) (record009.maps 13) (record009.inverseMaps 13) record009_frame013_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0967.localPairCheck (smallEmbedding record009) (record009.maps 13) (record009.inverseMaps 13) record009_frame013_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0967.localPairCheck (smallEmbedding record009) (record009.maps 13) (record009.inverseMaps 13) record009_frame013_indices (Fin.ofNat record009.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record009_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0967.localPairCheck (smallEmbedding record009) (record009.maps 13)
      (record009.inverseMaps 13) record009_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record009_frame013_links_0000 (interval_append _ 64 128 130 record009_frame013_links_0064 record009_frame013_links_0128))
theorem record009_frame013_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 13 :=
  of_group record009 13 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0967
    Papers.RationalityTen.SharedFrameCatalogue.group0967_facts record009_frame013_indices record009_frame013_graph record009_frame013_links
def record009_frame014_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0174.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0174.count (({ width := 8, code := 0x81807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0174.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0174.localPairCheck (smallEmbedding record009) (record009.maps 14) (record009.inverseMaps 14) record009_frame014_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0174.localPairCheck (smallEmbedding record009) (record009.maps 14) (record009.inverseMaps 14) record009_frame014_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0174.localPairCheck (smallEmbedding record009) (record009.maps 14) (record009.inverseMaps 14) record009_frame014_indices (Fin.ofNat record009.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record009_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0174.localPairCheck (smallEmbedding record009) (record009.maps 14)
      (record009.inverseMaps 14) record009_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record009_frame014_links_0000 (interval_append _ 64 128 130 record009_frame014_links_0064 record009_frame014_links_0128))
theorem record009_frame014_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 14 :=
  of_group record009 14 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0174
    Papers.RationalityTen.SharedFrameCatalogue.group0174_facts record009_frame014_indices record009_frame014_graph record009_frame014_links
def record009_frame015_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0168.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0168.count (({ width := 8, code := 0x81807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0168.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0168.localPairCheck (smallEmbedding record009) (record009.maps 15) (record009.inverseMaps 15) record009_frame015_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0168.localPairCheck (smallEmbedding record009) (record009.maps 15) (record009.inverseMaps 15) record009_frame015_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0168.localPairCheck (smallEmbedding record009) (record009.maps 15) (record009.inverseMaps 15) record009_frame015_indices (Fin.ofNat record009.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record009_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0168.localPairCheck (smallEmbedding record009) (record009.maps 15)
      (record009.inverseMaps 15) record009_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record009_frame015_links_0000 (interval_append _ 64 128 130 record009_frame015_links_0064 record009_frame015_links_0128))
theorem record009_frame015_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 15 :=
  of_group record009 15 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0168
    Papers.RationalityTen.SharedFrameCatalogue.group0168_facts record009_frame015_indices record009_frame015_graph record009_frame015_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (Fin.cases (record009_frame004_supported hcells) (Fin.cases (record009_frame005_supported hcells) (Fin.cases (record009_frame006_supported hcells) (Fin.cases (record009_frame007_supported hcells) (Fin.cases (record009_frame008_supported hcells) (Fin.cases (record009_frame009_supported hcells) (Fin.cases (record009_frame010_supported hcells) (Fin.cases (record009_frame011_supported hcells) (Fin.cases (record009_frame012_supported hcells) (Fin.cases (record009_frame013_supported hcells) (Fin.cases (record009_frame014_supported hcells) (Fin.cases (record009_frame015_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xcd3663b2f9968cab65131dd8d0c5962730fd870b555a2ace1658b1f58aaa6d516a7f53a29a14c09db4e3a6e135499b4c825fd2dc95c4a5a4e525a92748723dd1c28c2458227911a87b4389d08e5872536c1af8d666883359984b9e5b82d89634ae25662b09500a6252327c936c9a44c925792809243e31e38ef871836c1b10d646723251898b8c5842b8130091c4682220f0070c3721b10ca060c2e616a0a7850026012308581640b005702b010808204001480a004e02000f807802000f007002c0140090028010006000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
def record010_frame002_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x37edef78dd772dbf6ad9b62d7b5ad5b26c871cc6313c3ef3bc2edbaae7b92cbb1ac1af6b8ad2afaaea7a8e9fa6e98a36869fe789da739c66e9ae2286e1882e04805fb7ddf5741c9719c16f5bb6e1a968d9d65d936458d5f9775c1495013c4c129499234550f425003ecf936cd4340cc2f4b62ccb028c9d25c93220831f87b1c03a0e4380dc330c831098250901d0701b0400f0380b028090140400c00 } : Fields).get c.val)
theorem record010_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record010_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record010) (record010.maps 2)
      (record010.inverseMaps 2) record010_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record010_frame002_links_0000 record010_frame002_links_0064)
theorem record010_frame002_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 2 :=
  of_group record010 2 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record010_frame002_indices record010_frame002_graph record010_frame002_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (Fin.cases (record010_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x9d39c99c29b79ab99f98097796d96195694b93e93592c92091390689488987e86f86085284683a82d81f80c7f979b79078076f76075066966165b65364863a61a61360a5ff5f35e55d95d25c95bf5b15a053f53752d5225155074fb4f24e74dd4cf4c047546d46045244443637c37336635934c34133032631930c2fc2ed2d42c82b62a42a329c28c27c26e2612512412312202112021f31e21c41be1b21a619718817a16c15e14d13d1311251140ed0e20d40c807907807707605705605505404304204104002102001f01e } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame001_links_0000 (interval_append _ 64 128 136 record011_frame001_links_0064 record011_frame001_links_0128))
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xa73a67a63a58a48a3ea21a15a0fa049f29e69d79c89c19b59a399491e91190a8fb8e78d78c68b48a989b8898798108007f77ea7d47c06bf6b16aa6a069568b66e66165964f64363962b61d61360b5fe5f358f58157856e56055354353352851f5115044b34a449b4904824773c43b53a739f38e38137235f3503483383263042f42e42d12ce2be2b02a829828b27f26d25d24d23d22d21d20d1e71da1cf1ca1ba1ad1a118f18017116214e13e12e0fd0f00e30d507b07a07907805905805705604304204104002102001f01e } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame002_links_0000 (interval_append _ 64 128 136 record011_frame002_links_0064 record011_frame002_links_0128))
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0xda364d835cd6354d3f4cd2746d0f40cf73acdf34cc72ec5310c3308c0efebe6f5bc6edba2e3aeab6acaadaa6a59926197a5b9625593e4c9264690e408f63a8de348c62e84e108360a81a027f9fb7e1f57c5ed711c16f9b96d5b15d1705b16858d5e5655654d50531484f5354b5264952247d1c461144410a410fe3e0f33b8e9384dd364d5344cd324c12e4b12aca427496214801ec761685916057104400fc3e0e8390e0370842007c1e } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame003_links_0000 (interval_append _ 64 128 136 record011_frame003_links_0064 record011_frame003_links_0128))
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
def record011_frame004_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x5a7ad01664b2758cac4d5ccad5563aaf155caa754daa2d4fea7453429813b09c54daa6a133098f4bfa5b92b894b49ca4b51848b044f22350f68713ad9d34e847373961c94de86e336c1b24d7c6b33539a64d1067c3359984bda5de2e9171cb765b22d49668b1a57e2b89598a3250827c93a89b64d22040fd47ce3d91e58f0076a3a11c88e046e23651a48cd06443101860be85d42d91648aec56829f14509e04cc25311f88b44061f30f287583901bb0db068831e17f0b7857429413a08503ec1dc0e103d81e80f207802c81600ae0560218108082040010808003e01e } : Fields).get c.val)
theorem record011_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 4)
      (record011.inverseMaps 4) record011_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame004_links_0000 (interval_append _ 64 128 136 record011_frame004_links_0064 record011_frame004_links_0128))
theorem record011_frame004_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 4 :=
  of_group record011 4 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record011_frame004_indices record011_frame004_graph record011_frame004_links
def record011_frame005_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x9672b654ca69432724ac8f91521a3fc7a8ed1be35c678bf16e1ac2e85309a1041a82d03202c017eefbddf3b7760eb5d339f68ccf99d337662cb191b1e632c5988b0c612c117fafb5eabc1652c557eaed5aaaf55aa994fa9c52ca3d322614b295929a4c416810fd9f63e079cf19db3a6738e31be3666b4d39a134066cc998f312604bf1742d4584ac14f28c4f49792b24647c8d11221c4187f0f51d83846b0c915828c4d0910d21a0338660961282484807e0f81e83c0420800f81e } : Fields).get c.val)
theorem record011_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record011) (record011.maps 5)
      (record011.inverseMaps 5) record011_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame005_links_0000 (interval_append _ 64 128 136 record011_frame005_links_0064 record011_frame005_links_0128))
theorem record011_frame005_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 5 :=
  of_group record011 5 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record011_frame005_indices record011_frame005_graph record011_frame005_links
def record011_frame006_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xc8f1ec6b15c470dc2304c02fdbe6f6bcef0bb6eab9ee4b2ac5b02bcadeb3abeaba9ea3a7e9b9e2769ce719ba6b8a62588a1e86e1884e0f82e08812017fdfd7edf97ddf5765d5745ce729c7715c3705bf6f5bb66d9965d9564d915555052d475093e4e9364c92f4ad28469144390841d04404ff3f0fa3e0ec39ce2374d6348ce31cc32fcbc2e0b52c8a72849b2548a214801bc6c1a4661404f1384d0e8390e0370d0330c8310781d0701b } : Fields).get c.val)
theorem record011_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record011) (record011.maps 6)
      (record011.inverseMaps 6) record011_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame006_links_0000 (interval_append _ 64 128 136 record011_frame006_links_0064 record011_frame006_links_0128))
theorem record011_frame006_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 6 :=
  of_group record011 6 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record011_frame006_indices record011_frame006_graph record011_frame006_links
def record011_frame007_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0200.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0200.count (({ width := 10, code := 0x816027fdfc7e5f67d5f37c5ef7b5eb7a1e5789df771d9729c7711c16f9bb6e1b56c9af6b1a9649906398c629885c16e5b16a5a166591625815e5715a56557555535454f5013d4e9374d1314bd2d4ad2949d2545914449104390c3c4ed3a4e5384dd364d634cd0334ca30cbe2e4b42ccb12bcad2aca929ca327c9b25c942448e22487214832047f1f4781cc6e1a46618c6016457154531244811c460cc320c4300b42c0ac2a06c1a06418 } : Fields).get c.val)
theorem record011_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record011) (record011.maps 7)
      (record011.inverseMaps 7) record011_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame007_links_0000 (interval_append _ 64 128 136 record011_frame007_links_0064 record011_frame007_links_0128))
theorem record011_frame007_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 7 :=
  of_group record011 7 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0200
    Papers.RationalityTen.SharedFrameCatalogue.group0200_facts record011_frame007_indices record011_frame007_graph record011_frame007_links
def record011_frame008_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0785.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0785.count (({ width := 10, code := 0x8f2388d2308b22889a238821d86a17852128420d82e087f5fa7ddf47c5ee7ade8795e277ddc721c6711c2701be661956498f6318961d846057e5ed785d9745c9705b96c5655654d505354a52146511425013e4b92c4a928499243f8fa3d8f23b8ea398e3380dd368d733cc930cbd2f0ba2e0b62d0b22c0aa294a026c97250912308a22086210822007a1d4701ac6618c6016056150521244811c460d4340cc320c02f0b82d0681906017 } : Fields).get c.val)
theorem record011_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record011) (record011.maps 8)
      (record011.inverseMaps 8) record011_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame008_links_0000 (interval_append _ 64 128 136 record011_frame008_links_0064 record011_frame008_links_0128))
theorem record011_frame008_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 8 :=
  of_group record011 8 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0785
    Papers.RationalityTen.SharedFrameCatalogue.group0785_facts record011_frame008_indices record011_frame008_graph record011_frame008_links
def record011_frame009_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0336.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0336.count (({ width := 10, code := 0x71dc4705be6edb86ddb56cdb16bdad6a9a8699a4689a066997651916398b621856097f5f1795a96859964589605354b52547515435053f4f53b4e5374d9344c9304b92c4851e46d18455124410e4310a421063ecf93dcf53ccf136cd734ccf32cc730cc02f4ba2dcb42b8aa298a22849f2749b264972549123489214821fc7c1e0761d0721c06e1b0671885d160551484f12848118441003f0f83d0bc2e0b42c0a8290a0270641805c16 } : Fields).get c.val)
theorem record011_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0336.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record011) (record011.maps 9)
      (record011.inverseMaps 9) record011_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame009_links_0000 (interval_append _ 64 128 136 record011_frame009_links_0064 record011_frame009_links_0128))
theorem record011_frame009_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 9 :=
  of_group record011 9 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0336
    Papers.RationalityTen.SharedFrameCatalogue.group0336_facts record011_frame009_indices record011_frame009_graph record011_frame009_links
def record011_frame010_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0273.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0273.count (({ width := 10, code := 0x741cd729c7711c1701be6f1ba6e1b66cdb16bdad6ada968da06759a65d946458e62d88615825bd6d5ad6959d65549505394c5294851944509404f93c4ed394dd354cd31499234811d46917455134450f4350b3f0fa3e0f63d0f2370d8350d0330c8310c12f8bb2e0b52bcab29ca3288a02789c26898258922388a218832007d1e4771d4731c46f1b46818c5e1645614c5012848118441003f0f83d0bc2e0b42c0a8290a0270641805c16 } : Fields).get c.val)
theorem record011_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0273.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record011) (record011.maps 10)
      (record011.inverseMaps 10) record011_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame010_links_0000 (interval_append _ 64 128 136 record011_frame010_links_0064 record011_frame010_links_0128))
theorem record011_frame010_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 10 :=
  of_group record011 10 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0273
    Papers.RationalityTen.SharedFrameCatalogue.group0273_facts record011_frame010_indices record011_frame010_graph record011_frame010_links
def record011_frame011_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x5c1adf16eab6f5b42d89608af7572ab5d590ab75522a5d50aa77534295d3a09c24d9a68531e97e4b5a57529c93c49524651ca8ce45ba28511487439b1cbce5272338e1c58d826b23511a48d046713301944c826313109840b3e5912c215d4acc5592a514f0a5e52028894109be4cb25c12949264821e28ed47483951c28dd46ca3551a20cd464a3151808be85e82ed1748b585842ac14b0a044e026312a091446c22910d082c3e61e20e806f83581990c505f42e01650ac853027e13408a040c1e40e203d81e80f207802c81600ae0560218108082040010808003e01e } : Fields).get c.val)
theorem record011_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 11) (record011.inverseMaps 11) record011_frame011_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 11) (record011.inverseMaps 11) record011_frame011_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 11) (record011.inverseMaps 11) record011_frame011_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 11)
      (record011.inverseMaps 11) record011_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame011_links_0000 (interval_append _ 64 128 136 record011_frame011_links_0064 record011_frame011_links_0128))
theorem record011_frame011_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 11 :=
  of_group record011 11 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record011_frame011_indices record011_frame011_graph record011_frame011_links
def record011_frame012_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0xbc9782eedd8ba773edf5b8b696b6d3da1b2f652c7d89b055eaa053ba694b291519a1d42e82cfb9e739e614b79572864cc8f7f4fd9f9bf07d6f95e73c8788ef9db3af74ce8dcf399722e1da8b4d690d119e33665aca992b1f634c497baf05ceb7169acc4b895d2824a4848e9172294468750a20c3f87d8f89eb3d4790ec9ce3866e0d71a533a64cc397f2ec5b0ad1552944f89992723a454869031f23c4748df18e2f4578a30e21c03786e0aa150298520821001f83e0420800f81e } : Fields).get c.val)
theorem record011_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record011) (record011.maps 12) (record011.inverseMaps 12) record011_frame012_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record011) (record011.maps 12) (record011.inverseMaps 12) record011_frame012_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record011) (record011.maps 12) (record011.inverseMaps 12) record011_frame012_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record011) (record011.maps 12)
      (record011.inverseMaps 12) record011_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame012_links_0000 (interval_append _ 64 128 136 record011_frame012_links_0064 record011_frame012_links_0128))
theorem record011_frame012_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 12 :=
  of_group record011 12 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record011_frame012_indices record011_frame012_graph record011_frame012_links
def record011_frame013_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x63262d62a62261a6156025fb5f65ed5e65df5d45cc5c65c05b55ae56355e55855254954053553152a52251b50f4d44d04cb4c54c04bb46145b45644f44844242b42541e41640c4043fa3f53ee3e93df3d738838337e37636c36135735434f34633f3342f82f42f02eb2e52e028c28527a26f26225524b24423722b2212182021f51e91de1dc1d71ce1c71bc1b41a919d19518b18017616f16214c14814013712f1241191111050fb0f00e90df0d20ba0b60af0a807707607507405705605505404104003f03e02102001f01e } : Fields).get c.val)
theorem record011_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record011) (record011.maps 13) (record011.inverseMaps 13) record011_frame013_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record011) (record011.maps 13) (record011.inverseMaps 13) record011_frame013_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record011) (record011.maps 13) (record011.inverseMaps 13) record011_frame013_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record011) (record011.maps 13)
      (record011.inverseMaps 13) record011_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame013_links_0000 (interval_append _ 64 128 136 record011_frame013_links_0064 record011_frame013_links_0128))
theorem record011_frame013_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 13 :=
  of_group record011 13 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record011_frame013_indices record011_frame013_graph record011_frame013_links
def record011_frame014_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x6d26c96c56be6b66ad69768e68868267867066765b65564a63f6375ee5e55dd5d75cd5c65bd5b45aa59f59658e55254b54554053b5364c34b94b54ad4a84a148447a47546d46245945044143a43142441b3cc3c53bc3b43a93a239638d38137836c36532932231c31731130c2ae2a129728c27f27426925d25324d2412362212142071f71f51ed1e31df1d31ca1c41b71ad1a419718b18217a16215814f14b13e13813012311a1101030f70ef0e60c90c40bf0b907907807707605705605505404104003f03e02102001f01e } : Fields).get c.val)
theorem record011_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record011) (record011.maps 14) (record011.inverseMaps 14) record011_frame014_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record011) (record011.maps 14) (record011.inverseMaps 14) record011_frame014_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record011) (record011.maps 14) (record011.inverseMaps 14) record011_frame014_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record011) (record011.maps 14)
      (record011.inverseMaps 14) record011_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame014_links_0000 (interval_append _ 64 128 136 record011_frame014_links_0064 record011_frame014_links_0128))
theorem record011_frame014_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 14 :=
  of_group record011 14 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record011_frame014_indices record011_frame014_graph record011_frame014_links
def record011_frame015_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x77076976275b75474e7217177096fc6f36e56da6d26c96c36ba6ae66465c65364d64463862d6236156085ff5f15cc5c75c05bb5b45ad5105095024fc4f54ee4be4b24a849d49148547847046745d4534463f53ed3e43da3d03c33b63aa3a039538937d35534f34834233d3372d42c32b32a529728927c26b25b24d23f23121f21821220b2091fe1f21e31d91cb1bf1b71ae1a519c19418b18217316815c14d14313512912111810f1060fe0f50ec0d90d30cd0c807b07a07907805905805705604304204104002102001f01e } : Fields).get c.val)
theorem record011_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record011) (record011.maps 15) (record011.inverseMaps 15) record011_frame015_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record011) (record011.maps 15) (record011.inverseMaps 15) record011_frame015_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record011) (record011.maps 15) (record011.inverseMaps 15) record011_frame015_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record011) (record011.maps 15)
      (record011.inverseMaps 15) record011_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame015_links_0000 (interval_append _ 64 128 136 record011_frame015_links_0064 record011_frame015_links_0128))
theorem record011_frame015_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 15 :=
  of_group record011 15 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record011_frame015_indices record011_frame015_graph record011_frame015_links
def record011_frame016_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0353.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0353.count (({ width := 8, code := 0xc1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a79777573716f6d6b6967656361605f5e5d5b59575553514f4d4b49474543413f3d3b39373533312f2d2b29272524232221201f1e1d1c1b1a1918171615141312 } : Fields).get c.val)
theorem record011_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0353.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0353.localPairCheck (smallEmbedding record011) (record011.maps 16) (record011.inverseMaps 16) record011_frame016_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0353.localPairCheck (smallEmbedding record011) (record011.maps 16) (record011.inverseMaps 16) record011_frame016_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0353.localPairCheck (smallEmbedding record011) (record011.maps 16) (record011.inverseMaps 16) record011_frame016_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0353.localPairCheck (smallEmbedding record011) (record011.maps 16)
      (record011.inverseMaps 16) record011_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame016_links_0000 (interval_append _ 64 128 136 record011_frame016_links_0064 record011_frame016_links_0128))
theorem record011_frame016_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 16 :=
  of_group record011 16 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0353
    Papers.RationalityTen.SharedFrameCatalogue.group0353_facts record011_frame016_indices record011_frame016_graph record011_frame016_links
def record011_frame017_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x603afcd7b8bc85d92e75684b2d58bac155e4ade5642ad1540a8c53ba9893729a54ca26052dc95c4a4a4d524290f47ea3a911087643221490848303699afcd5069433f19a4c1c5f92f19744b7c5aa2ca1600ad85582a194b890a471230113487442820a90047da3db1e48ed86a83421980c7861c2fc11d08cc45822510f085c42020910107ec3e81ed0f1076c3a81cd0e5070c3781b50d7069c34419b0ca063430c17f0bc05c42c215a0a9853028a13e09c84c825612408e845821e10807a03b41cc0df03d81e80f207802c81600ae0560218108082040010808003e01e } : Fields).get c.val)
theorem record011_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 17) (record011.inverseMaps 17) record011_frame017_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 17) (record011.inverseMaps 17) record011_frame017_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 17) (record011.inverseMaps 17) record011_frame017_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 17)
      (record011.inverseMaps 17) record011_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame017_links_0000 (interval_append _ 64 128 136 record011_frame017_links_0064 record011_frame017_links_0128))
theorem record011_frame017_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 17 :=
  of_group record011 17 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record011_frame017_indices record011_frame017_graph record011_frame017_links
def record011_frame018_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x5f05ec5e85e05d95d05be5b85b35ad5a559859058858257b57356652151851250d5044f84f04e84e04d94d04c548c4854804784704663e93e43e03d83d13cc3b63b13ab3a539a39538938137a37336836231931130a3052f92f32e92e02d82d12c62be28427d27827026625f1f01e91e31df1da1d31cc1c61c11bd1b91b21a71a019919319118b18618117c17516f16916115915415014814013512e12912411f11811210b1030fb0f50ef0e70df0d10c90c10bb07207107006f05305205105004003f03e03d02102001f01e } : Fields).get c.val)
theorem record011_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record011) (record011.maps 18) (record011.inverseMaps 18) record011_frame018_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record011) (record011.maps 18) (record011.inverseMaps 18) record011_frame018_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record011) (record011.maps 18) (record011.inverseMaps 18) record011_frame018_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record011) (record011.maps 18)
      (record011.inverseMaps 18) record011_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame018_links_0000 (interval_append _ 64 128 136 record011_frame018_links_0064 record011_frame018_links_0128))
theorem record011_frame018_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 18 :=
  of_group record011 18 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record011_frame018_indices record011_frame018_graph record011_frame018_links
def record011_frame019_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0381.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0381.count (({ width := 9, code := 0x8fc7a3b1c8dc6a33188bc5a2b1489c4a231087c3a110783416090381401fcfc7d3e1daec75ba9d2e86f375b8db6d365b0d76b355a8d369345a0cf673358ec662b1186c260afd7abb5cadd58ab552a550a74ea6d32974aa4d228f46a2d128742209007e3e9ecf2773a9cce26e359a0ca633097cb85a2c158a85228134944722108803e1d8e872381a0cc6431148a04e261208c44210c8602e16 } : Fields).get c.val)
theorem record011_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0381.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record011) (record011.maps 19) (record011.inverseMaps 19) record011_frame019_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record011) (record011.maps 19) (record011.inverseMaps 19) record011_frame019_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record011) (record011.maps 19) (record011.inverseMaps 19) record011_frame019_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record011) (record011.maps 19)
      (record011.inverseMaps 19) record011_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame019_links_0000 (interval_append _ 64 128 136 record011_frame019_links_0064 record011_frame019_links_0128))
theorem record011_frame019_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 19 :=
  of_group record011 19 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0381
    Papers.RationalityTen.SharedFrameCatalogue.group0381_facts record011_frame019_indices record011_frame019_graph record011_frame019_links
def record011_frame020_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0784.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0784.count (({ width := 9, code := 0x96cb2572a94ca24f2692c92472290c823f1e8ec722d158a44e25118843a190a84419f4f97c3ddecf57439dcce57238dc4e17037dbcdd6e36db4d96c35da2d067b399acc65b258ec561b056ab459ac962b051a853e9d4da652e9549a451e8d44a1d0a8341200fc7c3d1e0ec72379b0d2673298cc05e2e168b0562a1409a4a2390c823f1d0e470371a0cc6431148a04e261208c44210c8602e16 } : Fields).get c.val)
theorem record011_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0784.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record011) (record011.maps 20) (record011.inverseMaps 20) record011_frame020_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record011) (record011.maps 20) (record011.inverseMaps 20) record011_frame020_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record011) (record011.maps 20) (record011.inverseMaps 20) record011_frame020_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record011) (record011.maps 20)
      (record011.inverseMaps 20) record011_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame020_links_0000 (interval_append _ 64 128 136 record011_frame020_links_0064 record011_frame020_links_0128))
theorem record011_frame020_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 20 :=
  of_group record011 20 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0784
    Papers.RationalityTen.SharedFrameCatalogue.group0784_facts record011_frame020_indices record011_frame020_graph record011_frame020_links
def record011_frame021_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0335.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0335.count (({ width := 9, code := 0x8642e15098441e0d058240e0501803fdfcfd7e3edecf57a3cde4f1783b9d8ea74399c0df6f375b8db68b419ece66b3196ca64b218ec662b1186c260b0176ba5cae16eb65aacd62af56aad4aa451a8942a04b25124904723114884321104803e9ecf2773b1d0e470371b0d46732184bc5c2d160aa532893c9a4b2491886401e8ec72371a8d06632180bc5c2d138984a2411084401f0c8602e16 } : Fields).get c.val)
theorem record011_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0335.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0335.localPairCheck (smallEmbedding record011) (record011.maps 21) (record011.inverseMaps 21) record011_frame021_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0335.localPairCheck (smallEmbedding record011) (record011.maps 21) (record011.inverseMaps 21) record011_frame021_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0335.localPairCheck (smallEmbedding record011) (record011.maps 21) (record011.inverseMaps 21) record011_frame021_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0335.localPairCheck (smallEmbedding record011) (record011.maps 21)
      (record011.inverseMaps 21) record011_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame021_links_0000 (interval_append _ 64 128 136 record011_frame021_links_0064 record011_frame021_links_0128))
theorem record011_frame021_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 21 :=
  of_group record011 21 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0335
    Papers.RationalityTen.SharedFrameCatalogue.group0335_facts record011_frame021_indices record011_frame021_graph record011_frame021_links
def record011_frame022_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0272.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0272.count (({ width := 9, code := 0x93c9a4923914823f1d8e46e33188bc56291388c4217098441e0b0481c0600ff7ebf1eef67a3cde4f075ba9d0e773391c6e17037dbadc6db65b0d76ab519ecd6632d92c863b1588c360b0176ba5c2dd6cb457ab554a85328d429f4e269309548a39168843a1504803f1ecf275389b4d26631980b85a2b954a650271288c421f0ec7035180b8582a128904622108803e1e0e06c34190c05c2c15 } : Fields).get c.val)
theorem record011_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0272.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0272.localPairCheck (smallEmbedding record011) (record011.maps 22) (record011.inverseMaps 22) record011_frame022_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0272.localPairCheck (smallEmbedding record011) (record011.maps 22) (record011.inverseMaps 22) record011_frame022_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0272.localPairCheck (smallEmbedding record011) (record011.maps 22) (record011.inverseMaps 22) record011_frame022_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0272.localPairCheck (smallEmbedding record011) (record011.maps 22)
      (record011.inverseMaps 22) record011_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame022_links_0000 (interval_append _ 64 128 136 record011_frame022_links_0064 record011_frame022_links_0128))
theorem record011_frame022_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 22 :=
  of_group record011 22 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0272
    Papers.RationalityTen.SharedFrameCatalogue.group0272_facts record011_frame022_indices record011_frame022_graph record011_frame022_links
def record011_frame023_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x89f126234438810f214c2483b05e09c0f81501600bfb7e8fb9e33c1776ed5d93af752e8dd039c72ae39bc3736dcda9b2b61620c2983b04602bf574ae25b6b59692cd592b0d5fabb568abd42a7f4f09c53726a4cc9812ea5a4a893d1ca3445e8ad132223ae73ce31be3726ccd71a6342668c898a3065fcbc9732e05a4b01592a052ca393e26a4b09291c2264307f0f91e83bc750e61c43706a8cf1943105e8b81542944f0970e01bc3706d0a013c2704d0821001f83e0420800f81e } : Fields).get c.val)
theorem record011_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record011) (record011.maps 23) (record011.inverseMaps 23) record011_frame023_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record011) (record011.maps 23) (record011.inverseMaps 23) record011_frame023_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record011) (record011.maps 23) (record011.inverseMaps 23) record011_frame023_indices (Fin.ofNat record011.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record011_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record011) (record011.maps 23)
      (record011.inverseMaps 23) record011_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record011_frame023_links_0000 (interval_append _ 64 128 136 record011_frame023_links_0064 record011_frame023_links_0128))
theorem record011_frame023_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 23 :=
  of_group record011 23 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record011_frame023_indices record011_frame023_graph record011_frame023_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (Fin.cases (record011_frame004_supported hcells) (Fin.cases (record011_frame005_supported hcells) (Fin.cases (record011_frame006_supported hcells) (Fin.cases (record011_frame007_supported hcells) (Fin.cases (record011_frame008_supported hcells) (Fin.cases (record011_frame009_supported hcells) (Fin.cases (record011_frame010_supported hcells) (Fin.cases (record011_frame011_supported hcells) (Fin.cases (record011_frame012_supported hcells) (Fin.cases (record011_frame013_supported hcells) (Fin.cases (record011_frame014_supported hcells) (Fin.cases (record011_frame015_supported hcells) (Fin.cases (record011_frame016_supported hcells) (Fin.cases (record011_frame017_supported hcells) (Fin.cases (record011_frame018_supported hcells) (Fin.cases (record011_frame019_supported hcells) (Fin.cases (record011_frame020_supported hcells) (Fin.cases (record011_frame021_supported hcells) (Fin.cases (record011_frame022_supported hcells) (Fin.cases (record011_frame023_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1059.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1059.count (({ width := 9, code := 0x9ece66d3095caa491f8f46227128641e0d017ebe9eef579bc5deec74b99c8e26fb79b8d96bb55a4d16732d92c76230d82be5e2e96eb65aacd62af56aa9489f4ea5d249047a04f87a3c1d0e26d3599cc8602d154a651269288c44200f472381208c44200f878361a0c8602a1409848200f07030160a0481c0c05018080200 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1059.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1059
    Papers.RationalityTen.SharedFrameCatalogue.group1059_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xbb1b99b91b65b47b3ba78a6ca65a5ea4ca429d79c89c19b59a399490b8e98d98a98898798598458317f77d47c06bf6b16aa6a069568b66e66165964f64363962b61d61360b5fe5f357755d5505285115044dc4ce4bf49b48247746b45744843b3c03b13a539a38b37e36b35834d34133131f3082f62e62d42c72b72ad2a12932862322232132011cd1b51a819918317416714313312311610305805705604304204104002902802702001f01e01101000f00e00c00b00a009005004003000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
def record013_frame002_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x32f9956ca262cb0fd870b555a2ace1658b1f58aaa6d516a7f53a29a14c09b84cda6412b8939496a4391ee8e144f21ed0e275b3a69d08e6e72c3929bd0dc66d83649af8d666a734c9a20cf866b330973cb705b12c695c4acc540298948c9f24db269131895e4a024910107e43e31eb0f1c77c3ad1cd8e306f636c1b10d386723251898c185e82e31698b0857025912388d04441e00e186e43581940c185cc29e140098048c22005802b81580860420208100052028013808003e01e008804001e00e006002c0140090028010006000 } : Fields).get c.val)
theorem record013_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record013_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 2)
      (record013.inverseMaps 2) record013_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record013_frame002_links_0000 record013_frame002_links_0064)
theorem record013_frame002_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 2 :=
  of_group record013 2 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record013_frame002_indices record013_frame002_graph record013_frame002_links
def record013_frame003_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x378dcb6fd8b5ad5b26c871cc6313c3ef3bc2edbaae7b92c1ae2b4a9e9fa6e8da1a7f9ce6e9ae298962287a1b8621383e0b82204805ff7f5fb7e5f77d5d0725c6705bd6eda968d9d65d936458a5f9775c15353949515404f1384d1304b5294991b4550f4250640d003f8fb3e4d8350d0330bd2d8b32b8a327497220831f87b1cc390e0370d0330c831098250901d0701b0441003c0e0300b028090140400c00 } : Fields).get c.val)
theorem record013_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record013_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record013) (record013.maps 3)
      (record013.inverseMaps 3) record013_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record013_frame003_links_0000 record013_frame003_links_0064)
theorem record013_frame003_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 3 :=
  of_group record013 3 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record013_frame003_indices record013_frame003_graph record013_frame003_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (Fin.cases (record013_frame002_supported hcells) (Fin.cases (record013_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xc01bf0be9bc2bb8bb1ba7b99b91b64b44b38a78a6ca65a5ea4ca42a109f49e89c19a399497796895a92091390b8fe8e98d98c68b48a989b8898798708598458317f77d47c07b079077b7676c46b66ac6a569868e65a64563b6135fe5f35db5cf5c359158357957156255554353352851f5115044fb4e84da4cc49b48247746d45344443636b35834d34133131f2ad2932862232132011e21d51cd1c41b51a815514313312310409309209105805705602001f01e01101000f00e00b00a009006005004003000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record014_frame001_links_0000 (interval_append _ 64 128 132 record014_frame001_links_0064 record014_frame001_links_0128))
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x68ab41da02cd3663b2f9968cab6513159878c375aaad15670b2c58fac55592ab055429fd4d0a6052228b14329db4e3a6e135499b4c825fd2dc95c4a5a4e525a92748723dd1c289e43da1c50c6842416a060ec07523a39cf0e6272736d1b00d686883359984c9863731317c0bc05d42e496f4b665a92cd1634afc5712b31588a9e53d29793e49b64d226412a893848e1d68e6c71837b1b60d885c62c215c091c4682220fe87b83c01d10e186e42c814f0a004c022209304902440b005702b008003e01e008804001e00e00580280120060028010006000 } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record014_frame002_links_0000 (interval_append _ 64 128 132 record014_frame002_links_0064 record014_frame002_links_0128))
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
def record014_frame003_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xe1b82e037edef78dd772dbf61d6755c9b21c7318c4f0fc06fabdeedb9ee4b6ed7b4ecbb1ac1af6b8ad2afaaea7a8e9fa6e98a36869fe739ba6b99e58942488b228892218761a83205809fb7ddf57b1e7789da759d273dcb721c570dc16fdbd6edb96b9a86899764d916317b5d16d4e1344c12d4a526400fb3e4d4340cc314c12f4ba2d8b323c8820c7e1d05815c560e4380dc1d0701b0441003c0e02c0a024060140400c00 } : Fields).get c.val)
theorem record014_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record014_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record014) (record014.maps 3)
      (record014.inverseMaps 3) record014_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record014_frame003_links_0000 (interval_append _ 64 128 132 record014_frame003_links_0064 record014_frame003_links_0128))
theorem record014_frame003_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 3 :=
  of_group record014 3 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record014_frame003_indices record014_frame003_graph record014_frame003_links
def record014_frame004_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x7ecbec1f38efd7743b45d7eeaa74b37e9b96db4606afe57c4bce5dc2e8d634af5570aa814eea62522a8c14369bc4d4265d3089714afa52526a921487a3f51d48de46622e114886442120c10468063fa1f88db26c53571a68d0866f2f31704b5a56c2a194b8a224fc27392208e846322810f48564152008fb47b63c91db0ea87303841b80cc061c2fc1778b485802ae10788204021fa0f987b03761ad0d305e82e616c0b005642a414b0a204f4230111085040c1ee09304902440b005702b008003e01e008804001e00e00580280120060028010006000 } : Fields).get c.val)
theorem record014_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record014_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 4)
      (record014.inverseMaps 4) record014_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record014_frame004_links_0000 (interval_append _ 64 128 132 record014_frame004_links_0064 record014_frame004_links_0128))
theorem record014_frame004_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 4 :=
  of_group record014 4 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record014_frame004_indices record014_frame004_graph record014_frame004_links
def record014_frame005_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x6df6d46d06b76b16ae6a86a169c67f67366d5f25ee5ea5e55dd5d25b45a659a58257356655754d54152351b51350f5054fa4f04e84e04d94d04c54be4b04a749b48047046646044f4424383eb3e63e23dd3d33d03ac39c39637a36836234f34333931c31330b3072fb2f42e92e02d82d12c62be2b62a829c29327826625f25824423a2301cb1c51bf1bc1b71b018417a17314b14313d13312c12712311d1160f10e90e10dc0d408708608505205105002001f01e01101000f00e00b00a009006005004003000 } : Fields).get c.val)
theorem record014_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record014_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record014) (record014.maps 5)
      (record014.inverseMaps 5) record014_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record014_frame005_links_0000 (interval_append _ 64 128 132 record014_frame005_links_0064 record014_frame005_links_0128))
theorem record014_frame005_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 5 :=
  of_group record014 5 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record014_frame005_indices record014_frame005_graph record014_frame005_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (Fin.cases (record014_frame003_supported hcells) (Fin.cases (record014_frame004_supported hcells) (Fin.cases (record014_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6ff6f06e86cf6b66ad69a6806746085fb5ed5cc5bc5ab59958857650f4de4bd4b64ac49c47845744e43e42e41440d3ca3bd3b438d37d37235934733d2cd29c28a27827326323522220f2051f51e51d419117116d16715f15b13d13913312b12712211c0ed0e70e40d70d10ce0c50bd0b70b40ac08208107f06606406305b05805705405204f04d03403303202902702502302001e01c01301200f00e00a009007003002001000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
def record015_frame002_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x18cf12e1ec057b2f15d4b816e6b4d5daa54ce92516a0d3e276ca99131da38c6b8c713a1d43585f09e0cc13786ee1d937d6dcda1a633e66cb4d54297514a1d3da5b4a09091e232452874e69a233063cc217c2ae544a293b2664a8920ec1ce3846a0d01963045c8b61642a84007f0fa198320630c017c2f05b0b21582a0340660c81482704a08c1001e03804c0900f01c0280480700600800800 } : Fields).get c.val)
theorem record015_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record015_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record015) (record015.maps 2)
      (record015.inverseMaps 2) record015_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record015_frame002_links_0000 record015_frame002_links_0064)
theorem record015_frame002_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 2 :=
  of_group record015 2 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record015_frame002_indices record015_frame002_graph record015_frame002_links
def record015_frame003_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0379.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0379.count (({ width := 9, code := 0x6130782bfdf6f97ab9dc6c762b0d7ab95babd4a9f459ccca632f96c9a3f1e8dc5e27108341609017fbf9f0f479399b4d669b49a0c761afd7cba5bacd509c4d2612a9444a1d08803f1ecf06431180bc5d2e168b2582b9549248238f87a3c1d0e47035198c05c251208c42200f07032170a84c240f070281207018080200 } : Fields).get c.val)
theorem record015_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record015_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record015) (record015.maps 3)
      (record015.inverseMaps 3) record015_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record015_frame003_links_0000 record015_frame003_links_0064)
theorem record015_frame003_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 3 :=
  of_group record015 3 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0379
    Papers.RationalityTen.SharedFrameCatalogue.group0379_facts record015_frame003_indices record015_frame003_graph record015_frame003_links
def record015_frame004_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0449.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0449.count (({ width := 8, code := 0xb5b4b3b2b0afaeadaca6a5a4a3a1a09f9e9d9895939291908f8d8c8a878685807f7e7d7b7a797877716f6d6c6b6a6967656461605f59585655545352504e4c4a494841403f3d3c3b39383736342f2e2d28272624232221201f1d18171614131211100f0d0b0a090807060403020100 } : Fields).get c.val)
theorem record015_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0449.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0449.localPairCheck (smallEmbedding record015) (record015.maps 4) (record015.inverseMaps 4) record015_frame004_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0449.localPairCheck (smallEmbedding record015) (record015.maps 4) (record015.inverseMaps 4) record015_frame004_indices (Fin.ofNat record015.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record015_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0449.localPairCheck (smallEmbedding record015) (record015.maps 4)
      (record015.inverseMaps 4) record015_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record015_frame004_links_0000 record015_frame004_links_0064)
theorem record015_frame004_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 4 :=
  of_group record015 4 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0449
    Papers.RationalityTen.SharedFrameCatalogue.group0449_facts record015_frame004_indices record015_frame004_graph record015_frame004_links
def record015_frame005_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0307.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0307.count (({ width := 9, code := 0x3c9e0ef75ba1cee671b89b0d66ab459ccd65b2590c15e2e570b65aac95eae55aa14aa44d265309348a411c8c45a0cfe7d3e1ecf4773a9cce46f371b4cc6130178b85b2b958a650271349846229108441200f87a3c1d8e4562a148944622108803e1e0e87034160a8502612088401e0e0602c14090401c0c04018080200 } : Fields).get c.val)
theorem record015_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0307.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record015) (record015.maps 5) (record015.inverseMaps 5) record015_frame005_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record015) (record015.maps 5) (record015.inverseMaps 5) record015_frame005_indices (Fin.ofNat record015.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record015_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record015) (record015.maps 5)
      (record015.inverseMaps 5) record015_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record015_frame005_links_0000 record015_frame005_links_0064)
theorem record015_frame005_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 5 :=
  of_group record015 5 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0307
    Papers.RationalityTen.SharedFrameCatalogue.group0307_facts record015_frame005_indices record015_frame005_graph record015_frame005_links
def record015_frame006_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x36b5b04d6f68a33a59accb7651b2717aabb15c5accd61eae956a2b195709eb4bb24f926491d484230d11687f435215508483c3b69d1ce686c334e9a28cdc66032c9674a8652b28b14309f44b624f12248fe46d23191686fc31f1890c005d82db13f09c44be24b11d08bc4521880bc85a4286139098046020c0fc079836c12008f04681b40d606a031017c0bc05b02c81580a803401980c8052027012808c04001e00e004c02400f00700280120070018008002000 } : Fields).get c.val)
theorem record015_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record015) (record015.maps 6) (record015.inverseMaps 6) record015_frame006_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record015) (record015.maps 6) (record015.inverseMaps 6) record015_frame006_indices (Fin.ofNat record015.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record015_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record015) (record015.maps 6)
      (record015.inverseMaps 6) record015_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record015_frame006_links_0000 record015_frame006_links_0064)
theorem record015_frame006_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 6 :=
  of_group record015 6 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record015_frame006_indices record015_frame006_graph record015_frame006_links
def record015_frame007_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x12163dc758cd17a2bc4e8870fe084097f8f99ef3cf784ef1da3826c8d39a5344670c89863085febcd73ae3582ad15729851ea193ba714d68c907a023ec7ccf39d13866e8db1aa344668b394b28c4fc9b932232450871052003ec7b0cf19030c5c8b41602a8520a01362543c0770ea17c2f05d0ac14c2904f09a128240330640c41482704a08c1001e03804c0900f01c0280480700600800800 } : Fields).get c.val)
theorem record015_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record015) (record015.maps 7) (record015.inverseMaps 7) record015_frame007_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record015) (record015.maps 7) (record015.inverseMaps 7) record015_frame007_indices (Fin.ofNat record015.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record015_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record015) (record015.maps 7)
      (record015.inverseMaps 7) record015_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record015_frame007_links_0000 record015_frame007_links_0064)
theorem record015_frame007_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 7 :=
  of_group record015 7 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record015_frame007_indices record015_frame007_graph record015_frame007_links
def record015_frame008_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0372.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0372.count (({ width := 8, code := 0xf8f7f6f3f2f1f0ebe9e2e1e0dddcdbd9d5d3cec7c2c1c0bfbbb6b5b4b3b0aea8a7a6a3a2a19e9b99938c89878685807d7b7a7977746e67656462615b5958565553514746454342413f3e3d3c3a3231302b2a292726252422211f1a19181615141311100e0c0b0a0907060403020100 } : Fields).get c.val)
theorem record015_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0372.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0372.localPairCheck (smallEmbedding record015) (record015.maps 8) (record015.inverseMaps 8) record015_frame008_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0372.localPairCheck (smallEmbedding record015) (record015.maps 8) (record015.inverseMaps 8) record015_frame008_indices (Fin.ofNat record015.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record015_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0372.localPairCheck (smallEmbedding record015) (record015.maps 8)
      (record015.inverseMaps 8) record015_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record015_frame008_links_0000 record015_frame008_links_0064)
theorem record015_frame008_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 8 :=
  of_group record015 8 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0372
    Papers.RationalityTen.SharedFrameCatalogue.group0372_facts record015_frame008_indices record015_frame008_graph record015_frame008_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (Fin.cases (record015_frame002_supported hcells) (Fin.cases (record015_frame003_supported hcells) (Fin.cases (record015_frame004_supported hcells) (Fin.cases (record015_frame005_supported hcells) (Fin.cases (record015_frame006_supported hcells) (Fin.cases (record015_frame007_supported hcells) (Fin.cases (record015_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1a64c916142e116fab765b82da56c6b0457bab955aeac855baa9152ea8553ba9a14ae97b48b243120a8fd47b21d10c485241fa0bd0448123ff9fbce6e7303951c90e3a7173609ac8d4469234119c4cc065132098c4c426102ab14049f24f427713a4904475234916c89e44621d10b08403be1d70e7871c37e1b78d7869c33e1970c7861e30417e8bd85e02e21670ae454628d13c89984b224b11e08b043e21110106483041760a8851424c11a08483741a606002f81700b605702b00a004e024011807c03c01500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame001_links_0000 (interval_append _ 64 128 138 record016_frame001_links_0064 record016_frame001_links_0128))
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
def record016_frame002_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1abecc664b2f917aabc35d8ae7d716b42599ac8561eafd574ab6d5aaace563ab015729bd4a9a50925e919484228111e87c433215509884541ea0d8f207803b69d6ce8e7343731b58d866b134e9a28cf867533799a0cc265a2c494d4a5051a28413e895049b24691ec8da466230916c8ac3ed1ea8f007523951bf0db46be34f19f8cc063e30c17e0bb05b62cc15f0ab853c28f13f09ac4b624b11d08c445422310e068831a17b0a384ec23010a07f036c1a406002f81700b605702b00a004e024011807c03c01500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record016_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record016) (record016.maps 2)
      (record016.inverseMaps 2) record016_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame002_links_0000 (interval_append _ 64 128 138 record016_frame002_links_0064 record016_frame002_links_0128))
theorem record016_frame002_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 2 :=
  of_group record016 2 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record016_frame002_indices record016_frame002_graph record016_frame002_links
def record016_frame003_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0x1e33ae734e1dc23806fade5bab6a6ced8db035c6b0d51a8b4d694d19a131d5f6bdd79aee5d2b1d61abf574ad558aad550a8d3fa7b4f09d13826c4b095128a4d49291520a3d4748d91922e41a7b8f51e73c6780e11be3766dcda1b135c6a8d399f33464cc61842f65d0b79682c2564a81482885009d9382664b09291d228430841041fe3ec7b8f31dc340660c616a2bc4f09b12a210408520a213826849090098128220420740e01502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record016_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record016) (record016.maps 3) (record016.inverseMaps 3) record016_frame003_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record016) (record016.maps 3) (record016.inverseMaps 3) record016_frame003_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record016) (record016.maps 3) (record016.inverseMaps 3) record016_frame003_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record016) (record016.maps 3)
      (record016.inverseMaps 3) record016_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame003_links_0000 (interval_append _ 64 128 138 record016_frame003_links_0064 record016_frame003_links_0128))
theorem record016_frame003_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 3 :=
  of_group record016 3 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record016_frame003_indices record016_frame003_graph record016_frame003_links
def record016_frame004_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1069.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1069.count (({ width := 10, code := 0xec398e0f6edaf67d9360d7751d3b4ad1f43d033cce735ccb2ecaf09baae6b8addb62b9ad6b1ab2a7a8e9fa6a959c66d9aa6698a5e92a4690e3f8ee378ce2f8b228892207fde1779db75dd46d9b36c1ac6a5a668d9f67193639876097a5c56b5995f56952525424f93a4d5324b5264851944109415013f0f83d0f03acd0330c62d4af2789b254842045013c4c12c4711826094220841d0701505013048110400f0380c02c0a0240400c0200400 } : Fields).get c.val)
theorem record016_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record016) (record016.maps 4) (record016.inverseMaps 4) record016_frame004_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record016) (record016.maps 4) (record016.inverseMaps 4) record016_frame004_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record016) (record016.maps 4) (record016.inverseMaps 4) record016_frame004_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record016) (record016.maps 4)
      (record016.inverseMaps 4) record016_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame004_links_0000 (interval_append _ 64 128 138 record016_frame004_links_0064 record016_frame004_links_0128))
theorem record016_frame004_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 4 :=
  of_group record016 4 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1069
    Papers.RationalityTen.SharedFrameCatalogue.group1069_facts record016_frame004_indices record016_frame004_graph record016_frame004_links
def record016_frame005_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1d20db7695b0297ecbdf5e5aed5740b42596ac5d60aaf256f2b21568aa054629dd4c4959473a3591868ab44c20c104280f3fc9f9cfb67ca3da9e94dac6c23559a5cd0266c30717e4bc65d12df16a8b285802b61560a8652e2128ecc74438f1bb8d905f82ed16d8b145662a714b0a044e223911908ac44821d10b083c4102010fd07cc3d81e30ee075439c1c90e106ec3681ad0d3067432c18f0c406042f41730b604f426a12e08c84481fc0f6077836c1aa06002f81700b605702b00a004e024011807c03c01500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record016_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 5) (record016.inverseMaps 5) record016_frame005_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 5) (record016.inverseMaps 5) record016_frame005_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 5) (record016.inverseMaps 5) record016_frame005_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 5)
      (record016.inverseMaps 5) record016_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame005_links_0000 (interval_append _ 64 128 138 record016_frame005_links_0064 record016_frame005_links_0128))
theorem record016_frame005_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 5 :=
  of_group record016 5 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record016_frame005_indices record016_frame005_graph record016_frame005_links
def record016_frame006_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x74170d6ea68567e67767166c66764163562c62361d6136075fc5f35ea5e35d756352a52251c51550e4d34ca4c44b84b04a94a049248843542e42742141c4173ee3e33da3d13ca3be3b53a93a039739138730c2d92d22cc2c52be28327927026225825124b23f23720f2061fd1f61ee1e71de1d51cc1c51bd1b61af1ab1a71a319f19819118a18317d17316b16215915014813f13611310b1050f10eb0d90d50cf0bc0b506005f05c05b05705602802702402301f01e01501401301201101000f00e00c00b00a009004003002001000 } : Fields).get c.val)
theorem record016_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record016) (record016.maps 6) (record016.inverseMaps 6) record016_frame006_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record016) (record016.maps 6) (record016.inverseMaps 6) record016_frame006_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record016) (record016.maps 6) (record016.inverseMaps 6) record016_frame006_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record016) (record016.maps 6)
      (record016.inverseMaps 6) record016_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame006_links_0000 (interval_append _ 64 128 138 record016_frame006_links_0064 record016_frame006_links_0128))
theorem record016_frame006_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 6 :=
  of_group record016 6 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record016_frame006_indices record016_frame006_graph record016_frame006_links
def record016_frame007_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x3696b0d278ff1c631c5187f0c5f5bdd79aeedd4b9b716e05bab696bed552e9f13ba72cd899f25a45c828e91aa3145b8a914207c08800fddf73e778aef9dbbae74ae79cb391716e15c037b5feb1d5e2b354aa6d31a594a090d1d233458895109fe3f27c8f69e83c6770ea9ce38c700dc1ae34e680cc992316610be1762dc590ae95629e528a314227c4608890b1f23c46e0d21942d45705e0ba1682c8550a80a01382404607c0f01502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record016_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record016) (record016.maps 7) (record016.inverseMaps 7) record016_frame007_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record016) (record016.maps 7) (record016.inverseMaps 7) record016_frame007_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record016) (record016.maps 7) (record016.inverseMaps 7) record016_frame007_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record016) (record016.maps 7)
      (record016.inverseMaps 7) record016_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame007_links_0000 (interval_append _ 64 128 138 record016_frame007_links_0064 record016_frame007_links_0128))
theorem record016_frame007_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 7 :=
  of_group record016 7 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record016_frame007_indices record016_frame007_graph record016_frame007_links
def record016_frame008_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1068.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1068.count (({ width := 9, code := 0x251259146e33188bc5a2b1187c3a1b0c85c2a11078341608fe7c3ddecf3793b1d6ea73b99cae470b81b2d76b355a8d367b3598cb6532590c662b1186c25e2d96ab458ac154a95429548a35127d3c994b251248f462250c84411fcf8793b9d4e671371b0d46732184be5d2d964ae552993494482110074381b0c05c29140984a2311074381a0c85c2c110803c1c0d0602c14090401c0c04018080200 } : Fields).get c.val)
theorem record016_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1068.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record016) (record016.maps 8) (record016.inverseMaps 8) record016_frame008_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record016) (record016.maps 8) (record016.inverseMaps 8) record016_frame008_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record016) (record016.maps 8) (record016.inverseMaps 8) record016_frame008_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record016) (record016.maps 8)
      (record016.inverseMaps 8) record016_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame008_links_0000 (interval_append _ 64 128 138 record016_frame008_links_0064 record016_frame008_links_0128))
theorem record016_frame008_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 8 :=
  of_group record016 8 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1068
    Papers.RationalityTen.SharedFrameCatalogue.group1068_facts record016_frame008_indices record016_frame008_graph record016_frame008_links
def record016_frame009_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1940c385f72d49686b355952c71628ae656aab1d578aae553aa6d516a7f53a29a14c098e496246d2068e846921c50c284b41920750167f63ee1f18ebc7503a29ce8e5e72637a1b8cdb06c935f1accd4e69934419f0cd66612d89594ab454729a14989a44c62599280924486239917c8a04011f80f847a83c51de8eb473638c1bd8db06c435019d8c9c62a30617a0b8c5a62c215c0a9852427f136896448e23411106e43541970b28540242110080036019206002f81700b605702b00a004e024011807c03c01500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record016_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record016) (record016.maps 9) (record016.inverseMaps 9) record016_frame009_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record016) (record016.maps 9) (record016.inverseMaps 9) record016_frame009_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record016) (record016.maps 9) (record016.inverseMaps 9) record016_frame009_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record016) (record016.maps 9)
      (record016.inverseMaps 9) record016_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame009_links_0000 (interval_append _ 64 128 138 record016_frame009_links_0064 record016_frame009_links_0128))
theorem record016_frame009_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 9 :=
  of_group record016 9 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record016_frame009_indices record016_frame009_graph record016_frame009_links
def record016_frame010_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xad4a95a519d49cb9c49ba9ae9a298097796d96195694b93e93592c9209139068507f77e27d17bd7a675073d7297116fe6ef6dd6c66b366a66365d65664b63d61a61360a5ff5f35e55d95d25c95bf5b15a05044bd4ae4a048e47e4364274174023f33e83da3c53b637936d36035234533a32d3203133052f52e72d72cb2bc2aa2a029628627526725a2472372262182071f81e71d918317216413612a0fe0f20e70c00b405e05d05a05905505402802702402301f01e01501401301201101000f00e00c00b00a009004003002001000 } : Fields).get c.val)
theorem record016_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record016) (record016.maps 10) (record016.inverseMaps 10) record016_frame010_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record016) (record016.maps 10) (record016.inverseMaps 10) record016_frame010_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record016) (record016.maps 10) (record016.inverseMaps 10) record016_frame010_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record016) (record016.maps 10)
      (record016.inverseMaps 10) record016_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame010_links_0000 (interval_append _ 64 128 138 record016_frame010_links_0064 record016_frame010_links_0128))
theorem record016_frame010_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 10 :=
  of_group record016 10 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record016_frame010_indices record016_frame010_graph record016_frame010_links
def record016_frame011_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x32d636c2d79af0ddebb3752e85beb716d2d6da7b4365eca58fb1360abd5169c936e6accf99123e40c758d316a2944986f0a1fe3f77e8fc5f63e679cf21e23be76cebdd33a373ce65c8b87666c3d84b055febe9662c4576ac9542a1538a3d42a5b4aa93923a3e46a8b513a21432845039fd3ee7ccf69e83be750e41bd3686a4cf197318600bd1702ca48c8c9111ea3b4698cb1822804c85b0b41602b8530a40a01382404607c0f01502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record016_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record016) (record016.maps 11) (record016.inverseMaps 11) record016_frame011_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record016) (record016.maps 11) (record016.inverseMaps 11) record016_frame011_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record016) (record016.maps 11) (record016.inverseMaps 11) record016_frame011_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record016) (record016.maps 11)
      (record016.inverseMaps 11) record016_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame011_links_0000 (interval_append _ 64 128 138 record016_frame011_links_0064 record016_frame011_links_0128))
theorem record016_frame011_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 11 :=
  of_group record016 11 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record016_frame011_indices record016_frame011_graph record016_frame011_links
def record016_frame012_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x33f658c8d86b0ae11c137fefbde3bc3772eadcdb816e2da5b1b5b6a6d2d44a2341a7dcec9bb2964ec939011c6354668c11661542484107209c0c7e4fbdf5be67bcf51e53c6786f01de3b76b2ca990317614bfd672c557cab951a9d534a554826e4c896527a434708c114220436849039fb3e07a8ee9d83a472ce19bc35e68cce19230a5f8bd1762de4c4921191e63a4680c51822904d8560aa1482884d0980a01382404607c0f01502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record016_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record016) (record016.maps 12) (record016.inverseMaps 12) record016_frame012_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record016) (record016.maps 12) (record016.inverseMaps 12) record016_frame012_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record016) (record016.maps 12) (record016.inverseMaps 12) record016_frame012_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record016) (record016.maps 12)
      (record016.inverseMaps 12) record016_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame012_links_0000 (interval_append _ 64 128 138 record016_frame012_links_0064 record016_frame012_links_0128))
theorem record016_frame012_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 12 :=
  of_group record016 12 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record016_frame012_indices record016_frame012_graph record016_frame012_links
def record016_frame013_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6e06a266c60e6085ff5fb5f25ed5d15cc5c25bc5b25ab5a159c59158b57e5794fb4cb4c14b34a849c46545b44c43a42e42841b40e4053d53ce3ca3c23bd3b439839138d38337d37236836135c35034a3402c229228727c26f26322c2202132011f51ec1e31d51cc1ac1a81a219c19619118b18718117c17717116a16415f15b15715414f14914313d13613012b12712311d1161110f60ef0e90d90d30c50bf0b90ac0a905905805505405004f02802702402301f01e01501401301201101000f00e00c00b00a009004003002001000 } : Fields).get c.val)
theorem record016_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record016) (record016.maps 13) (record016.inverseMaps 13) record016_frame013_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record016) (record016.maps 13) (record016.inverseMaps 13) record016_frame013_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record016) (record016.maps 13) (record016.inverseMaps 13) record016_frame013_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record016) (record016.maps 13)
      (record016.inverseMaps 13) record016_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame013_links_0000 (interval_append _ 64 128 138 record016_frame013_links_0064 record016_frame013_links_0128))
theorem record016_frame013_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 13 :=
  of_group record016 13 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record016_frame013_indices record016_frame013_graph record016_frame013_links
def record016_frame014_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x288ce999b26648c8d91721641c718d91963145a8af13e25c4287d0d617be9782ef1dabb0756e1dc13796e6dadb335e6a8d2d93b1f638c618b3115fcbdd792e95ccb796bad259cb1d62abd4d693d2424447c8e50aa0d40a7f4fa1ee3d4784ec9ba3686b8d41a233a658c898b3085f8bc9712d4598b19602ba55ca894c28e5009c1322564908f1172203c4748e119a31c5b0b215a27c4d8580ae1502984f09c09c1302404607c0f01502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record016_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record016) (record016.maps 14) (record016.inverseMaps 14) record016_frame014_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record016) (record016.maps 14) (record016.inverseMaps 14) record016_frame014_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record016) (record016.maps 14) (record016.inverseMaps 14) record016_frame014_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record016) (record016.maps 14)
      (record016.inverseMaps 14) record016_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame014_links_0000 (interval_append _ 64 128 138 record016_frame014_links_0064 record016_frame014_links_0128))
theorem record016_frame014_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 14 :=
  of_group record016 14 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record016_frame014_indices record016_frame014_graph record016_frame014_links
def record016_frame015_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x23845187904a0840b813001fe3e77ccf85ef3d579ef19e1bbe77aee1dab746aed45a4b40670c55883075f6bcd77aea5c8b81632c3582ae95a2ae538a694c29351ea193ea794f09cd3926c456825009fa3de79ce49c237a6c8d51a534266ccb9822fc5dcb896b2ce588ae9592a8540a59432784dc9913025a49c9191d232444859052003f07b8f51e6360688ca1742d4550a5142254490540a61402784b0940a01382404607c0f01502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record016_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record016) (record016.maps 15) (record016.inverseMaps 15) record016_frame015_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record016) (record016.maps 15) (record016.inverseMaps 15) record016_frame015_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record016) (record016.maps 15) (record016.inverseMaps 15) record016_frame015_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record016) (record016.maps 15)
      (record016.inverseMaps 15) record016_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame015_links_0000 (interval_append _ 64 128 138 record016_frame015_links_0064 record016_frame015_links_0128))
theorem record016_frame015_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 15 :=
  of_group record016 15 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record016_frame015_indices record016_frame015_graph record016_frame015_links
def record016_frame016_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0617.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0617.count (({ width := 8, code := 0x898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record016_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0617.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0617.localPairCheck (smallEmbedding record016) (record016.maps 16) (record016.inverseMaps 16) record016_frame016_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0617.localPairCheck (smallEmbedding record016) (record016.maps 16) (record016.inverseMaps 16) record016_frame016_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0617.localPairCheck (smallEmbedding record016) (record016.maps 16) (record016.inverseMaps 16) record016_frame016_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0617.localPairCheck (smallEmbedding record016) (record016.maps 16)
      (record016.inverseMaps 16) record016_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame016_links_0000 (interval_append _ 64 128 138 record016_frame016_links_0064 record016_frame016_links_0128))
theorem record016_frame016_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 16 :=
  of_group record016 16 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0617
    Papers.RationalityTen.SharedFrameCatalogue.group0617_facts record016_frame016_indices record016_frame016_graph record016_frame016_links
def record016_frame017_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0551.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0551.count (({ width := 11, code := 0x1f4bd7796e99d0398728e49c7b85702df9bd3756dcdadb3b646c2d79ae328630c4d84b025f2ba5722de5a2b31642c2576ad94a28f50ca093fa7e4de9ad342634be9652a250498925232434167ecfb9ed3ce77ce79ca38a6e4da1b1358694d09802f25c4b59652be568ab150298520a293f26a4c49612824647c8d91822642c830ff1f43d8788ec1d2338648c21602a85009912c228430540a61402784b0940a01382404607c0f01502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record016_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record016) (record016.maps 17) (record016.inverseMaps 17) record016_frame017_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record016) (record016.maps 17) (record016.inverseMaps 17) record016_frame017_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record016) (record016.maps 17) (record016.inverseMaps 17) record016_frame017_indices (Fin.ofNat record016.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record016_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record016) (record016.maps 17)
      (record016.inverseMaps 17) record016_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record016_frame017_links_0000 (interval_append _ 64 128 138 record016_frame017_links_0064 record016_frame017_links_0128))
theorem record016_frame017_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 17 :=
  of_group record016 17 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0551
    Papers.RationalityTen.SharedFrameCatalogue.group0551_facts record016_frame017_indices record016_frame017_graph record016_frame017_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (Fin.cases (record016_frame002_supported hcells) (Fin.cases (record016_frame003_supported hcells) (Fin.cases (record016_frame004_supported hcells) (Fin.cases (record016_frame005_supported hcells) (Fin.cases (record016_frame006_supported hcells) (Fin.cases (record016_frame007_supported hcells) (Fin.cases (record016_frame008_supported hcells) (Fin.cases (record016_frame009_supported hcells) (Fin.cases (record016_frame010_supported hcells) (Fin.cases (record016_frame011_supported hcells) (Fin.cases (record016_frame012_supported hcells) (Fin.cases (record016_frame013_supported hcells) (Fin.cases (record016_frame014_supported hcells) (Fin.cases (record016_frame015_supported hcells) (Fin.cases (record016_frame016_supported hcells) (Fin.cases (record016_frame017_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x82581b8127e07ce7c57ac78c76a76375f75871a7086f96ca6946636596496405ff5c95a859e59158354b54553e52f52952251c4c34ae4a646542e4083f03e43dc38934d33b32331a30c2dd2d02c92c22b62b02ab2472041f91ec1dd1d319c19418517716d15f15811c11410c0f70ed0e60d80cc0c80c40c109209108e08d07106f06d06b06205f05e05b05905505403803703403302902702502302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x663cc197719e25c3d7feea5a9b4166ecad69abb54a985069c3376694cd9532263b4718d718e19c2d85106609c0e812f0ddc3b26f8d3198b25638c5969aa852ea2943a7b4908e119a2943a8650a9cd344660c79842f8524a09342544908d1161d839c708d41a032c608b916c2c8578831042003f8690d0198320600be1782d8590aa1501c0370680cc1482704a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record017_frame002_links_0000 record017_frame002_links_0064)
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
def record017_frame003_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x73172d72a6ff6f06e86ce69a65a64d6476366085fb5ed5c959956a56355554e50f4de4bd4b64ac49c44443942f41440d4063fb3ca3bd3b438a35933532631c3152cd29c28a2782732632182001f61e51d41cd1c219117116d16715f15b13512f12812211c1121100ed0e70e40d70d10ce0c50bd0b70b40b108608508208106a06806606405b05805705405204e04d03803703403302902702502302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record017_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record017_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record017) (record017.maps 3)
      (record017.inverseMaps 3) record017_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record017_frame003_links_0000 record017_frame003_links_0064)
theorem record017_frame003_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 3 :=
  of_group record017 3 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record017_frame003_indices record017_frame003_graph record017_frame003_links
def record017_frame004_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0449.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0449.count (({ width := 8, code := 0xb9b8b7b5b4b3b1aeabaaa9a8a6a5a4a29f9c9b9a999895939291908b898886858382807f7e7c7976757473716f6d6c6b6a666362605f5d5c5958565554534f4d4b4948464541403f3d3c3b393837363531302f2e2a29282724232221201e1d1a19181714131211100e0d0b0a090807050403020100 } : Fields).get c.val)
theorem record017_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0449.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0449.localPairCheck (smallEmbedding record017) (record017.maps 4) (record017.inverseMaps 4) record017_frame004_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0449.localPairCheck (smallEmbedding record017) (record017.maps 4) (record017.inverseMaps 4) record017_frame004_indices (Fin.ofNat record017.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record017_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0449.localPairCheck (smallEmbedding record017) (record017.maps 4)
      (record017.inverseMaps 4) record017_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record017_frame004_links_0000 record017_frame004_links_0064)
theorem record017_frame004_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 4 :=
  of_group record017 4 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0449
    Papers.RationalityTen.SharedFrameCatalogue.group0449_facts record017_frame004_indices record017_frame004_graph record017_frame004_links
def record017_frame005_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0379.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0379.count (({ width := 9, code := 0x18bc56270983c15faf56eb65aed363b1586bb57a6d329348a2ce6653197cb639198c44e210e8641a0b04803e1e2ee763adccda6b34da4d060af176b759ac55ea84e26930954a215047f3d9e0ea7332188c05e2e970b4592c15cac4c259249041200f87a3a1c8e06a33178b850271289042200f07032160a84c240f070281007018080200 } : Fields).get c.val)
theorem record017_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record017) (record017.maps 5) (record017.inverseMaps 5) record017_frame005_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record017) (record017.maps 5) (record017.inverseMaps 5) record017_frame005_indices (Fin.ofNat record017.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record017_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record017) (record017.maps 5)
      (record017.inverseMaps 5) record017_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record017_frame005_links_0000 record017_frame005_links_0064)
theorem record017_frame005_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 5 :=
  of_group record017 5 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0379
    Papers.RationalityTen.SharedFrameCatalogue.group0379_facts record017_frame005_indices record017_frame005_graph record017_frame005_links
def record017_frame006_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0307.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0307.count (({ width := 9, code := 0xfa7cbe1e4f077ba9cce17037dbcd86b355a0cb63b198ac460af172b85b2d558aa54a9548a250a6932984923914894421d067f3e9f0f67a3a1c4e06e369acd46630980bc5c2d954a44f269309047231148842209007c3d1e0ec742d160ac54271309446211007c3c1d0d86830170b0542612088401e0d0602c14090401c0a04018080200 } : Fields).get c.val)
theorem record017_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0307.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record017) (record017.maps 6) (record017.inverseMaps 6) record017_frame006_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record017) (record017.maps 6) (record017.inverseMaps 6) record017_frame006_indices (Fin.ofNat record017.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record017_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record017) (record017.maps 6)
      (record017.inverseMaps 6) record017_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record017_frame006_links_0000 record017_frame006_links_0064)
theorem record017_frame006_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 6 :=
  of_group record017 6 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0307
    Papers.RationalityTen.SharedFrameCatalogue.group0307_facts record017_frame006_indices record017_frame006_graph record017_frame006_links
def record017_frame007_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0268.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0268.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record017_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0268.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0268.localPairCheck (smallEmbedding record017) (record017.maps 7) (record017.inverseMaps 7) record017_frame007_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0268.localPairCheck (smallEmbedding record017) (record017.maps 7) (record017.inverseMaps 7) record017_frame007_indices (Fin.ofNat record017.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record017_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0268.localPairCheck (smallEmbedding record017) (record017.maps 7)
      (record017.inverseMaps 7) record017_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record017_frame007_links_0000 record017_frame007_links_0064)
theorem record017_frame007_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 7 :=
  of_group record017 7 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0268
    Papers.RationalityTen.SharedFrameCatalogue.group0268_facts record017_frame007_indices record017_frame007_graph record017_frame007_links
def record017_frame008_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0193.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0193.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record017_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0193.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0193.localPairCheck (smallEmbedding record017) (record017.maps 8) (record017.inverseMaps 8) record017_frame008_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0193.localPairCheck (smallEmbedding record017) (record017.maps 8) (record017.inverseMaps 8) record017_frame008_indices (Fin.ofNat record017.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record017_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0193.localPairCheck (smallEmbedding record017) (record017.maps 8)
      (record017.inverseMaps 8) record017_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record017_frame008_links_0000 record017_frame008_links_0064)
theorem record017_frame008_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 8 :=
  of_group record017 8 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0193
    Papers.RationalityTen.SharedFrameCatalogue.group0193_facts record017_frame008_indices record017_frame008_graph record017_frame008_links
def record017_frame009_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xdd36e6371daa2d3e69c338d8f4c1a609b03980cb7d5b82d8d5e8a94524a911476a354cf24e521690647f23d909883e4182030ffc7f03f39ca8e3a71734f98f8c0a5fe2fc17ccac650e27d13cc9de4e923791688a0440215908483436f1878c185fc2f617809904b023d11508784061fa0bf05d02d614d0a184e824c11508383e01d2094049824011e07103781b40d606202f81780b605902a815007003701a00cc052027012808c04001d00e004c02400f00700280100070018008002000 } : Fields).get c.val)
theorem record017_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record017) (record017.maps 9) (record017.inverseMaps 9) record017_frame009_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record017) (record017.maps 9) (record017.inverseMaps 9) record017_frame009_indices (Fin.ofNat record017.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record017_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record017) (record017.maps 9)
      (record017.inverseMaps 9) record017_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record017_frame009_links_0000 record017_frame009_links_0064)
theorem record017_frame009_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 9 :=
  of_group record017 9 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record017_frame009_indices record017_frame009_graph record017_frame009_links
def record017_frame010_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0769.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0769.count (({ width := 8, code := 0x9e9d9c99989796928e8d8c8b88878684807d7c7b7a777371706f6e6968676564636261605f5d5c5b5a59585655545352514d4c4b4a4948474544434241403c3b3a393837363231302f2e2d2c2b2a29282625242321201f1e1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record017_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0769.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0769.localPairCheck (smallEmbedding record017) (record017.maps 10) (record017.inverseMaps 10) record017_frame010_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0769.localPairCheck (smallEmbedding record017) (record017.maps 10) (record017.inverseMaps 10) record017_frame010_indices (Fin.ofNat record017.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record017_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0769.localPairCheck (smallEmbedding record017) (record017.maps 10)
      (record017.inverseMaps 10) record017_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record017_frame010_links_0000 record017_frame010_links_0064)
theorem record017_frame010_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 10 :=
  of_group record017 10 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0769
    Papers.RationalityTen.SharedFrameCatalogue.group0769_facts record017_frame010_indices record017_frame010_graph record017_frame010_links
def record017_frame011_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0362.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0362.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record017_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0362.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0362.localPairCheck (smallEmbedding record017) (record017.maps 11) (record017.inverseMaps 11) record017_frame011_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0362.localPairCheck (smallEmbedding record017) (record017.maps 11) (record017.inverseMaps 11) record017_frame011_indices (Fin.ofNat record017.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record017_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0362.localPairCheck (smallEmbedding record017) (record017.maps 11)
      (record017.inverseMaps 11) record017_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record017_frame011_links_0000 record017_frame011_links_0064)
theorem record017_frame011_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 11 :=
  of_group record017 11 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0362
    Papers.RationalityTen.SharedFrameCatalogue.group0362_facts record017_frame011_indices record017_frame011_graph record017_frame011_links
def record017_frame012_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0329.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0329.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record017_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0329.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0329.localPairCheck (smallEmbedding record017) (record017.maps 12) (record017.inverseMaps 12) record017_frame012_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0329.localPairCheck (smallEmbedding record017) (record017.maps 12) (record017.inverseMaps 12) record017_frame012_indices (Fin.ofNat record017.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record017_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0329.localPairCheck (smallEmbedding record017) (record017.maps 12)
      (record017.inverseMaps 12) record017_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record017_frame012_links_0000 record017_frame012_links_0064)
theorem record017_frame012_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 12 :=
  of_group record017 12 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0329
    Papers.RationalityTen.SharedFrameCatalogue.group0329_facts record017_frame012_indices record017_frame012_graph record017_frame012_links
def record017_frame013_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0249.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0249.count (({ width := 9, code := 0x12a93c8e3f1c8cc52210983c1a0b027f3edeef074ba1cae470365a6d268b398cc4613017ebe5eae96eb35729d46a04ea71309146a2912863f9f0f4793b9d8ea6d349a0ce6531970b6592b954a6522592892462210c82401f8f87a33190c4602b150a450251208c44200f87834190c05c2813090441e0e0682c1409040180a04018080200 } : Fields).get c.val)
theorem record017_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0249.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0249.localPairCheck (smallEmbedding record017) (record017.maps 13) (record017.inverseMaps 13) record017_frame013_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0249.localPairCheck (smallEmbedding record017) (record017.maps 13) (record017.inverseMaps 13) record017_frame013_indices (Fin.ofNat record017.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record017_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0249.localPairCheck (smallEmbedding record017) (record017.maps 13)
      (record017.inverseMaps 13) record017_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record017_frame013_links_0000 record017_frame013_links_0064)
theorem record017_frame013_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 13 :=
  of_group record017 13 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0249
    Papers.RationalityTen.SharedFrameCatalogue.group0249_facts record017_frame013_indices record017_frame013_graph record017_frame013_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (Fin.cases (record017_frame003_supported hcells) (Fin.cases (record017_frame004_supported hcells) (Fin.cases (record017_frame005_supported hcells) (Fin.cases (record017_frame006_supported hcells) (Fin.cases (record017_frame007_supported hcells) (Fin.cases (record017_frame008_supported hcells) (Fin.cases (record017_frame009_supported hcells) (Fin.cases (record017_frame010_supported hcells) (Fin.cases (record017_frame011_supported hcells) (Fin.cases (record017_frame012_supported hcells) (Fin.cases (record017_frame013_supported hcells) (fun j => Fin.elim0 j)))))))))))))))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x18d4c5061cb075806bee59aac71628aa653026d533098f4aca4d9258871433a12906081b4071f70f8c75e3a81d14e7472f3931b80d8c6b234c99f0cc25ed2ef1748b8e5bb2d91698b2e58a2bd95b8aca50827513489804b224f124090445f2280f8478a3bd1c60db06c435419d8c9c62a2b81528a4c4ba23411107803861b90d686583081740b184382020d706481bc0dc05d02e016c0ae05601c80dc06c026012809004602100f8078028013009004001e00e0050024010005002000c002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x30e57dcb525a1acd5654b1c58a2b49572aa6545a9d14c09b54cc263d2b293649621c509483040da02cfb87c63af1d40e8a73a3979c98dc06c63591a64cf86612e916ecb6458a2b715949a44b224f124090c45f22810047e03e11ea0f1477a3ad1cd8e306f636c1b10d4067632718a8bd05a62b814989644682220f0070c3721960c205d02ca110080835c19207103781b80ba05c02d815c0ac03901b80d804a024011807c03c01500a004c024011008003c01c00c0050024010005002000c002000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
def record019_frame002_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x12b24dc728d91a231c5f8b91221f43285707e09be57b4f4de33bc762e15bdb756dcda9afb5864cc858eb19628c3d7caf25cab75692c3526a1d3f26f4cc9751922a4468750ca0e4107b0f29db3a8730e19bc36a6b8d219c326624c197e2f05bcb014f28a4cc9291c2103e4768e01ae338640b115a2704b8640c61882a8540a613c270340660c81282404607c0f01502804c0901102003c0700c0140240400500800c00800 } : Fields).get c.val)
theorem record019_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record019_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record019) (record019.maps 2)
      (record019.inverseMaps 2) record019_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record019_frame002_links_0000 record019_frame002_links_0064)
theorem record019_frame002_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 2 :=
  of_group record019 2 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record019_frame002_indices record019_frame002_graph record019_frame002_links
def record019_frame003_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x36e9a56c0a5fb2f7d796bb55d02ca9604adb55a2a314c49944b7257123c8fa473a0c101c7f73f29f6cf6a7a536b1b08d5669734099b0bec5ce2d39600ab052e23010e88503ea1e30ecc5f82da1618ac454e28113888e446422b112087442c20f10408043f41f30f6078c3b81d50e707083681a60cb86042e616c0a9051027a12d093047c2320f607803681aa07103781b80ba05c02d815c0ac03901b80d804a024011807c03c01500a004c024011008003c01c00c0050024010005002000c002000 } : Fields).get c.val)
theorem record019_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record019_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 3)
      (record019.inverseMaps 3) record019_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record019_frame003_links_0000 record019_frame003_links_0064)
theorem record019_frame003_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 3 :=
  of_group record019 3 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record019_frame003_indices record019_frame003_graph record019_frame003_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (Fin.cases (record019_frame002_supported hcells) (Fin.cases (record019_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xbbdbb3bafba3b97b8fb64b44b38b20b06afaa76a6aa64a5ba4aa40a0e9ef9e39c19a399492191490c9018ec8dc8cb8b98ab8a188e87e87185a8468327fa7dc7c87b878f77a76575073972265a64563b6135fe5f359158357957156255554053052751c50e50149b48247746d45344443641b40d3fc3c23b33a639d38c37f36b35834d34133131f2ad29328627925f24f23f2232132011e51d81ce1c71b81ab1a018e17f1701521401301201070f20e50d70d30c109309209107006f06e02602502402302001f01e01101000f00e00b00a009 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record020_frame001_links_0000 (interval_append _ 64 128 140 record020_frame001_links_0064 record020_frame001_links_0128))
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x6673311970cb1652b2818acc3c61bb03d7eabee5a92d0d66ab2a58e2c51588aab55329fd4d0a604eea7253769ac4cf264530a9724b0253d27a92f494243d1f08e2452a2090e886b420a0b102e8003f59f54db46c035a1a20cd66612f81780ba85c92de96ccb4c5972c515ecadc56527c936c9a44c8255127091c46f22f914080c3f41f28f607923bf1d68e6c71837b1b60d885c62c215c0ab051a27b134891c46822210007c43c61d40e306e836a1a10c705f82c214c09e84b42280fd07783881ba0cb049824812207003781b804c025012008c04001f00f004402000f007002c014009 } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record020_frame002_links_0000 (interval_append _ 64 128 140 record020_frame002_links_0064 record020_frame002_links_0128))
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
def record020_frame003_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xdf379ddb73dc36dd8759d574dd1f44c9720c6f17c4b0ebfef8bd6edb9ee4b32c7b0abeae6b5ac6adaa6a5a869da668ea1e809d6709b66995e4f91e408ee3683205809fb7ddf5769d6749cf72dc8711c2701be6f1ba65d936458c5ed745b5645855e5514f529465053d4e1344c12d4a526400fb3e4f53a0e3378d4340cc318c22f8bb2dcb42c4a62809a230862047c1d86d1a8671945f160571584b1284908c22084200741c06c110400f0380b02809 } : Fields).get c.val)
theorem record020_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record020_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record020) (record020.maps 3)
      (record020.inverseMaps 3) record020_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record020_frame003_links_0000 (interval_append _ 64 128 140 record020_frame003_links_0064 record020_frame003_links_0128))
theorem record020_frame003_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 3 :=
  of_group record020 3 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record020_frame003_indices record020_frame003_graph record020_frame003_links
def record020_frame004_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x703b7e1bd2dd66e1b6c1a76d1367fb33194cc905d12e4d708b715af2d2d5acaae54d299d482a2b4d7a6a134299a4c9a63130a97e4bba5c12d29624aea55929e948498a48d238916485240d1f88f4476a398ea67283899b58d5e6992f49760b8c5b22cf9630ae85612a794f4a5651824d11dc8ce45921e10ac8384001f78f7c6f43691ab8d0c66031d1828bc85c02ce15e0aa44562080fc07a839a1bc0d686443001700ab854029214209d84d025e128090846821e10908183f01e00e807103701b20d2049824812207003781b804c025012008c04001f00f004402000f007002c014009 } : Fields).get c.val)
theorem record020_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record020_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record020) (record020.maps 4)
      (record020.inverseMaps 4) record020_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record020_frame004_links_0000 (interval_append _ 64 128 140 record020_frame004_links_0064 record020_frame004_links_0128))
theorem record020_frame004_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 4 :=
  of_group record020 4 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record020_frame004_indices record020_frame004_graph record020_frame004_links
def record020_frame005_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x7056ff6fa6f56f26ed6c26b26ae69b68868162d62a62762061b6155ed5de5d65c25b45a956155b55454f54854453e53953252c52552051c51550e5054ee4e14dc4d74cb4c34bb4b34ac4a442f41b4103f73e43dd38f38237836d36635f35434b34333832f32b2e92da2d42cf2b82b02a529128727c25124323c23522b22121620b2021fc1f41ed1aa19d19619117a16f16715314713d12a12311c11610f10b1071000fa0f40ea0e40dd0d60cc0c40be0b90b70af08708608506e06d06c02602502402302001f01e01101000f00e00b00a009 } : Fields).get c.val)
theorem record020_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record020_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record020) (record020.maps 5)
      (record020.inverseMaps 5) record020_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record020_frame005_links_0000 (interval_append _ 64 128 140 record020_frame005_links_0064 record020_frame005_links_0128))
theorem record020_frame005_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 5 :=
  of_group record020 5 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record020_frame005_indices record020_frame005_graph record020_frame005_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (Fin.cases (record020_frame003_supported hcells) (Fin.cases (record020_frame004_supported hcells) (Fin.cases (record020_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1079.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1079.count (({ width := 11, code := 0x16caabd3899328235c668c116229c4b8850f61bc2f855089f5be47b8f45e53c577aec9d5b8f716e19c037c6f0d058cb16622c31842e65c4b756a2cd58eb015d2b4552a854c25049290d18a2a43c858fa9ef3d2778eb1cd3846f8dc9b035268cae15629e50c9d9362604688a10f2124107f8f81e23b0730df1b034c668c317c2b85508610a1a0338540a60dc1b0330640a81482804e07c0f01d0220400780e0140240380600a01001800 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1079
    Papers.RationalityTen.SharedFrameCatalogue.group1079_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
def record021_frame002_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x33fd86ebef554297d3b69c74dc26a93369904bfa5b92b894b49ca4b50e2863426a0b503080a3fa9f68f8875e3a81d14e7472f3931ac8cc065532198b4c385ea2ed973cb885b82d896a4b3458d2bf15c4acc4d226192c090a47222e91388083f21f18f5878e3be1d68e6c71837b1b60d885702a914a89f44d625a12407f43dc1e00e8870c3721a70ca060c2e61640a78500260111080835419009204881ac0d405702b00dc06c03301900a8052028013807c03c01d008804001e00e005002400e0060028010006000 } : Fields).get c.val)
theorem record021_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record021_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record021) (record021.maps 2)
      (record021.inverseMaps 2) record021_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record021_frame002_links_0000 record021_frame002_links_0064)
theorem record021_frame002_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 2 :=
  of_group record021 2 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record021_frame002_indices record021_frame002_graph record021_frame002_links
def record021_frame003_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0xffde3bbc6ecd919bb30654c8d9031c62ec458730b60abf1662c8584aed5aab2558a995028b510a1541a804fc9912b25349e9292322f4588a51222043c8690aa1241c821011cb38c704d81ab34667cc197e2f05c8b796b2cc588af15c2b25548f91a22a438839031fc3a4720de1b0348660c617e2ec5b0b11542945109a12a220428710e01742e04b0940dc1b0330640a81482804e07c0f01d0220400780e0140240380600a01001800 } : Fields).get c.val)
theorem record021_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record021_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record021) (record021.maps 3)
      (record021.inverseMaps 3) record021_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record021_frame003_links_0000 record021_frame003_links_0064)
theorem record021_frame003_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 3 :=
  of_group record021 3 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record021_frame003_indices record021_frame003_graph record021_frame003_links
def record021_frame004_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb1aa92a5394e90389588b88087286385584683a82d81f80c7f975073f72b70c6f96ee6dc6c46b166a66365d65664b63d5e259d58f58256e56053e53452a51f5125044fb4f24e74dd4cf4c04364244143e73d93c33b437a37036335534833d32d3203133052f52e725a24a23a2242162081f91c21ba1ae1a019118316f16115214213512911a1090f30e80bd0b308c08b06906805505403703603303202a02902802701f01e01d01101000f00e00a009007006005004003000 } : Fields).get c.val)
theorem record021_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record021) (record021.maps 4) (record021.inverseMaps 4) record021_frame004_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record021) (record021.maps 4) (record021.inverseMaps 4) record021_frame004_indices (Fin.ofNat record021.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record021_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record021) (record021.maps 4)
      (record021.inverseMaps 4) record021_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record021_frame004_links_0000 record021_frame004_links_0064)
theorem record021_frame004_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 4 :=
  of_group record021 4 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record021_frame004_indices record021_frame004_graph record021_frame004_links
def record021_frame005_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x128234453808fa5df3ba76cec9d53a673ce6dcc39171ce19ab350692cf99ab31658c7d8b2fb5eebd578aeb5ceae54c296524a31432704da9a133a5f4b896129a4f4909051d2043fc7dcf21df3a6720d71a9348678cb190312610c197c2f65d4a113c2684a88f91922c3f47d0f61e03a4718df1b2354678ca18c3045d8b315c2744c0800fe194320530a40dc1b0330640a81482804e07c0f01d0220400780e0140240380600a01001800 } : Fields).get c.val)
theorem record021_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record021) (record021.maps 5) (record021.inverseMaps 5) record021_frame005_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record021) (record021.maps 5) (record021.inverseMaps 5) record021_frame005_indices (Fin.ofNat record021.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record021_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record021) (record021.maps 5)
      (record021.inverseMaps 5) record021_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record021_frame005_links_0000 record021_frame005_links_0064)
theorem record021_frame005_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 5 :=
  of_group record021 5 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record021_frame005_indices record021_frame005_graph record021_frame005_links
def record021_frame006_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x140272cd48f716a1b42f85509e10c1b82d03202c017eefbdcfb9d72ce29c1b7d6e8da5b0347680ced9c33365ac2d77aea5c4b61682c9584af55cab255cab55329f538a5947a4c4949151aa2e44887504a013f27d0f69e53c275ce89cc3846ecc017b2e258cad1522924b49412123a45c881071fe3dc770e41b233c610b2152238450740e616c2d0490900d41a0310600a81482804e07c0f01d0220400780e0140240380600a01001800 } : Fields).get c.val)
theorem record021_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record021) (record021.maps 6) (record021.inverseMaps 6) record021_frame006_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record021) (record021.maps 6) (record021.inverseMaps 6) record021_frame006_indices (Fin.ofNat record021.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record021_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record021) (record021.maps 6)
      (record021.inverseMaps 6) record021_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record021_frame006_links_0000 record021_frame006_links_0064)
theorem record021_frame006_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 6 :=
  of_group record021 6 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record021_frame006_indices record021_frame006_graph record021_frame006_links
def record021_frame007_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0x16d6b1d469b72ea404798d91922ec5789f11a20c3a867099efbda7a2f11ddbb675ee89cbb6f6d4d91b035c6aec6d7a2f05d6b8d6eac7588af95c2b255eaad51a9e52ea4143a404748bd0e21340c7f4f09db3a2728e11bd36c6c0d51a6346678ad1552964f89a92e250434849031fa3dc788eb1c837c6c8d319831c608b916628c4f8821021a4340550a80dc1b0330640a81482804e07c0f01d0220400780e0140240380600a01001800 } : Fields).get c.val)
theorem record021_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record021) (record021.maps 7) (record021.inverseMaps 7) record021_frame007_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record021) (record021.maps 7) (record021.inverseMaps 7) record021_frame007_indices (Fin.ofNat record021.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record021_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record021) (record021.maps 7)
      (record021.inverseMaps 7) record021_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record021_frame007_links_0000 record021_frame007_links_0064)
theorem record021_frame007_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 7 :=
  of_group record021 7 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record021_frame007_indices record021_frame007_graph record021_frame007_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (Fin.cases (record021_frame002_supported hcells) (Fin.cases (record021_frame003_supported hcells) (Fin.cases (record021_frame004_supported hcells) (Fin.cases (record021_frame005_supported hcells) (Fin.cases (record021_frame006_supported hcells) (Fin.cases (record021_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0xb956bad3d9caff486834fd9eb3463bc508930e60a40e80eff5fb3ed7c8f7dd83a4740e19c0b7c6f0dc5b4360694d0178ae45b0af951a9f516a05392624ae9492323f456890f91e53ba6ecd59a13205fcb81672c0554a59442724a47c0f11d836c6a8d018c3005d8ab0fe1f0328630b41642a8510a01381a8340640a81402704c08c1081f03c0700a0130240400700b0140240380400600800800 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x75236dd814bcb5daacb560aade544a6452d695947d235917e8984182084ff27e73eb1f1cf6e6d634b9a04bf25d12d515548ba4372128f1874438b1b20bf05da2c51598a8852628311c88c845622410e885841e1fa0f9878c3b81ce0e106d034c19d0c786202f61750a9051027a13508c84301fc0f6078036c11a06d03501840c005f02e816c0ae05602a00d4064029014009c04a02300f807803801500a004c024011008003801800a004801c00a0040018008002000 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
def record023_frame002_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x7226e668867266463f62e61b6045af59658855554252f5174da4ce4b14a349949348d45b44743c4184093f93e038c37836d34833832b3192ed2e32cd2c42bb2b82b428627a27126625924d2452302262102071f21e41d51c41b51a319718b18715f14613a12d0fb0eb0d80cd0c50aa08106706405d05c05b05905705305205003503202902802702502301f01e01c01501401301201101000e00c00a009007005004003002001000 } : Fields).get c.val)
theorem record023_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record023_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record023) (record023.maps 2)
      (record023.inverseMaps 2) record023_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record023_frame002_links_0000 record023_frame002_links_0064)
theorem record023_frame002_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 2 :=
  of_group record023 2 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record023_frame002_indices record023_frame002_graph record023_frame002_links
def record023_frame003_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x8890b9fcbee7d0f51e53bd75ade1b73696aed39a333b63cc65843025f8be178ad258caf955aa1530a1928a464868ad112174167ccf71e03b6754e79ca3626acd29a133865cc81822f65b4b295629a50c9a92e23e45c8890c1ec3b4730e018a2ec580a814824c3b8610bc1582a8540a41402604b0920d01882905009c1282303e0780e01502804c090110200380600a01201c0280400600800800 } : Fields).get c.val)
theorem record023_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record023_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record023) (record023.maps 3)
      (record023.inverseMaps 3) record023_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record023_frame003_links_0000 record023_frame003_links_0064)
theorem record023_frame003_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 3 :=
  of_group record023 3 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record023_frame003_indices record023_frame003_graph record023_frame003_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (Fin.cases (record023_frame002_supported hcells) (Fin.cases (record023_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1b74c0a5e5aed55b6a4f51d28393729a54ca26052dc95c4a324311f48304102038fee7e53ec1f1cf6e6d634b9a04b4e51b283136890a47123011348744282090f6078c2fc1760b685862b11520a4c50623911908ac44821d10b083c3f41f30f1877039c1a60cf065c30417b0ba859c2c01590a9052c28813d09a04b424c11f08603dc1e00da04681bc0dc06a02f01740b605702b015006e036019009804a02300f807803801500a004c0240110080038014009004001c00c005002000c002000 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
def record024_frame002_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa989d49ba9ae9488f48e78c289488987e86f86085284581c80975073c72870f6fc6ec6da6c866a65664b5e258f58256053f53752d5225155074fa4da4cc4364264164003f13e53d73c737936d36035234533a32d3052f52d72cb2aa25a2482382081f91e91cd1c21ba1ae1a019118317116315414411c0f30e80bf08706d06c06805c05b05905505405203703603202602502301f01e01c01501401301201101000e00a009008007006005004003001000 } : Fields).get c.val)
theorem record024_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record024_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record024) (record024.maps 2)
      (record024.inverseMaps 2) record024_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record024_frame002_links_0000 record024_frame002_links_0064)
theorem record024_frame002_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 2 :=
  of_group record024 2 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record024_frame002_indices record024_frame002_graph record024_frame002_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (Fin.cases (record024_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xede761ba91bf6dd96d93599aa8d416963465a0acde65db24190ac5e623ae596e8b4d580abbd5b8ac755a2a814f2a56515a8813f29e24bea5bd2c293e49ba4c125292248da3d91d08e13e79d38e4470d34c9a2cca263c2e19670b1251828693d49ba4cd24d11dc8ce45d21f90b883e4171f78f7c7a63541968c6855229e14309b84bc22b10407e03dc1d00df86c03501800b8059029013a09984382140ed06881780b805b02c81600ae056020810007003701b009004602000f807801e00e0058028012005002000c002000 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
def record025_frame002_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xd1d687b40598ccb3650b1e98d4c5c6283109872c1d601afb97d4bbf5d4ad15658b15574ab5d592abe5582aa1516a74530296d458a194b5a5212588c2458227911a87b438a01cfb87c63929b54d766b2330996cc546192e916ecb645652b01518a6452427c936c9a44cc256927892048922f91408883e31e38ef86c435919f0c946262e31610ae056029013e89ac4c023411108483c01c30dc85802a210b06481780b805b02c81600ae056020810007003701b009004602000f807801e00e0058028012005002000c002000 } : Fields).get c.val)
theorem record025_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record025_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record025) (record025.maps 2)
      (record025.inverseMaps 2) record025_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record025_frame002_links_0000 record025_frame002_links_0064)
theorem record025_frame002_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 2 :=
  of_group record025 2 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record025_frame002_indices record025_frame002_graph record025_frame002_links
def record025_frame003_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x73773172c7016f66ee6d66ce6c76bd6b76b06a268e68167e66865c62b6226165fe5f85f25ea5e35d85c85bb5a95a659058153752a51e4fa4f34ec4e64df4da4b54a749f45642b41740e3dd3d73b63a937636435e32b32731b30b3002e92da2d42d12bb2b12a62a128727c27323a2292201ed1e91dd1cb1c21aa19d19619317d17016816314713d13511b10e1090e90e50c90ae05c05a05905705605505404104003803703602402302001f01e00f00e00b00a009005004003001000 } : Fields).get c.val)
theorem record025_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record025) (record025.maps 3) (record025.inverseMaps 3) record025_frame003_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record025) (record025.maps 3) (record025.inverseMaps 3) record025_frame003_indices (Fin.ofNat record025.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record025_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record025) (record025.maps 3)
      (record025.inverseMaps 3) record025_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record025_frame003_links_0000 record025_frame003_links_0064)
theorem record025_frame003_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 3 :=
  of_group record025 3 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record025_frame003_indices record025_frame003_graph record025_frame003_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (Fin.cases (record025_frame002_supported hcells) (Fin.cases (record025_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x340198ecb4651316587ec385f7aef9750b455962c554be9db4e3a6e135499b4c825b929692d493a3dd1c289e43da1c50147da3e21d34e6e72536c1af8d6666032118acc345ea2ed973cb885b82d89668afc5662a994c4a464f926d934895e4a024912148ba44e22190107e43e31eb0f1c77c39b1bd8d8869c33e1928c4c5c62c215c09684921fd0f707803a21c30dc869c3281830b98590280130091844419006b03501600ae056021810408003301900a8052028013808003e01e008803c01c00b005002400e0060028010006000 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x39f9cbce3c6df3679af8d576a83525a84d3b69a3499a30d0a682b3dd9e0b825b7ad71698b3c5942bf55b0ab050b280d3e09e04e826f132296c4a223bd1d08e146d234d1988c746022e51648a7451226512477d3839b9cdae67233218dcc4c5b22c91608a3a50f27113449744ad253128092c48f24412108fa47523791ac7ac3ab1cb0c6453227a1358984490238114886041c1b60cb86202fc1650aa851826a12b07c83c01d20e206e03500da06b03501780b805b01c00dc06c03301900a4050027012008c01e00e00580280120070028010006001 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record028_frame001_links_0000 (interval_append _ 64 128 131 record028_frame001_links_0064 record028_frame001_links_0128))
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
def record028_frame002_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x346da1acff66232c5940c7c636317d8a4c4561d308180cbf05f5af01754ae956bab2557cab05542a214e2a5f4eda71d3709aa4cda6412d694849623151668a144821f90e486c42aa0fd0548043fb9f64f8672636a9aecd6466032c18b4c385cf2dc16c4aca55d29a14989f84de269933895849d24792308e845c22691147c63c71df0d885c62c215c0ac052027d13589584921e00e186e43621940c185cc2c015108a83fc1e40e506c831c0da06b03501780b805b01c00dc06c03301900a4050027012008c01e00e00580280120070028010006001 } : Fields).get c.val)
theorem record028_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record028_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record028) (record028.maps 2)
      (record028.inverseMaps 2) record028_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record028_frame002_links_0000 (interval_append _ 64 128 131 record028_frame002_links_0064 record028_frame002_links_0128))
theorem record028_frame002_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 2 :=
  of_group record028 2 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record028_frame002_indices record028_frame002_graph record028_frame002_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (Fin.cases (record028_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x66232c5940c5961fb0e17dab435952c5158eaae553a97d3ba9c94dda6b133c9914b9253d25e92847c238914a88243a215908082b4099fecfac7c03a81ce8e4c6d835f1acccc05ea2ed973cb885b82d8965caf65652ab14d0a4c4f926d934895e4a0249120c8e24011f80f847a83c51de8e6c6f63621a80c9c62a2e31610ae052427f13689684922000f8878c3a81c60dd06983261820b905842a813d09684902280fd07783881b40c404702340d606a01980c8054029014009c04c024011808003e01e00e0054028013009004401e00e0058028012007 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record029_frame001_links_0000 (interval_append _ 64 128 132 record029_frame001_links_0064 record029_frame001_links_0128))
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
def record029_frame002_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0xd25a2f3f66ccc796322e15c137deee5cdb81692bdd73ad5582aa549a7d4b28bd0c9ef39e66cb995726645c7b8d719e2ec56849072063eb7bcf51db388700de1b7b636b2d359f32a63ac297faec5b6b395daae546a714ca6e4c896527a434708a10da073f67a8ee9cb3786bcce19230a5fcbd9642bc550a513f2664848b1081f03c0758e01ac344638be1682a85289a0f41e4308600660c81502905009c130240460800f81e0380540a0130240440780e01602804807 } : Fields).get c.val)
theorem record029_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record029_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record029) (record029.maps 2)
      (record029.inverseMaps 2) record029_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record029_frame002_links_0000 (interval_append _ 64 128 132 record029_frame002_links_0064 record029_frame002_links_0128))
theorem record029_frame002_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 2 :=
  of_group record029 2 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record029_frame002_indices record029_frame002_graph record029_frame002_links
def record029_frame003_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x9c536a684c296f2c24bc708d11722744687b08dff3f97e8fbdf43e17b0f35e03bb758e8dc83856f8dc5b435f6aad3da3b4364ec7586afa5dab8d652a353aa5946a844fa9d9362614b89312123144c87107a053f27d0f79ca3886fcdb9ac348668c81802f25a4ae95028c4f89912923e4648a9001f63d8780ea1ca3706a8d0194318628bd16e2cc570a81462744c8910ee1d8310610620c01482804e0981282304407c0f01d0360540a0130240440780e01602804807 } : Fields).get c.val)
theorem record029_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record029) (record029.maps 3) (record029.inverseMaps 3) record029_frame003_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record029) (record029.maps 3) (record029.inverseMaps 3) record029_frame003_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record029) (record029.maps 3) (record029.inverseMaps 3) record029_frame003_indices (Fin.ofNat record029.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record029_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record029) (record029.maps 3)
      (record029.inverseMaps 3) record029_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record029_frame003_links_0000 (interval_append _ 64 128 132 record029_frame003_links_0064 record029_frame003_links_0128))
theorem record029_frame003_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 3 :=
  of_group record029 3 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record029_frame003_indices record029_frame003_graph record029_frame003_links
def record029_frame004_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0551.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0551.count (({ width := 11, code := 0x7e4fb5f4be17b6f5de4ba0728e3dbf3756dcd69a3340674cd59832b64ac798cb1660cbfd7a2ef5d4b856bad0592b0d5cab451ea093f2684be96520a274428690aa10416818ff9fb3e879cef9d73a673ce11b93686c0d59802f25c4b59652be558a614527e4c49611f23044c830ff1f43dc790e41c23706c0d419e3185f8ba1682b8560a81462844d894120238458850e41c42e85c0620c01502905009c130240460800f81e0380540a0130240440780e01602804807 } : Fields).get c.val)
theorem record029_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record029) (record029.maps 4) (record029.inverseMaps 4) record029_frame004_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record029) (record029.maps 4) (record029.inverseMaps 4) record029_frame004_indices (Fin.ofNat record029.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record029_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record029) (record029.maps 4) (record029.inverseMaps 4) record029_frame004_indices (Fin.ofNat record029.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record029_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record029) (record029.maps 4)
      (record029.inverseMaps 4) record029_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record029_frame004_links_0000 (interval_append _ 64 128 132 record029_frame004_links_0064 record029_frame004_links_0128))
theorem record029_frame004_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 4 :=
  of_group record029 4 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0551
    Papers.RationalityTen.SharedFrameCatalogue.group0551_facts record029_frame004_indices record029_frame004_graph record029_frame004_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (Fin.cases (record029_frame002_supported hcells) (Fin.cases (record029_frame003_supported hcells) (Fin.cases (record029_frame004_supported hcells) (fun j => Fin.elim0 j))))))
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
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x38e5af2d576a83525a84d3b69a3429a08cfd678b3a97aab825b7ad71698b3c5942ac1542a8d539297d42ca034f827813a09bc4a224d5242906479a3bd1d08e146d234d1988c746022e51648a9451226512488e3c01cb4e3870d37e9bb4dba6723319940c646212ec171cb705a82cc1620a3a50e27d93749984c826092e89664ad2531284934493246120c8fa47523791b06322b91548a6451427a135887441c1d60e306d834e1970c404e82560f707803a41c40d405802bc13809b03581a80b805b01980c8048023007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record031_frame001_links_0000 (interval_append _ 64 128 135 record031_frame001_links_0064 record031_frame001_links_0128))
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
def record031_frame002_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x33f993ec7c636317d8a4c4561d2fc17d2bd35d5ae5562aae956bab2557cab0554297d4a2a3b50e28253b69c74dc26a9336990496247520a8e5467a3151668a144821f90e486c42aa0fd05480c3fb9f64f867bb3939bdcdca6da3659b00d6866032b9914c526182f81780ba85c92de96ccaca55c2a494c0a4451c28593f09da4de269933c9764a824d121c8e845c22691246c430617a0b8c5a62c215c096c4921fd0f707803a21c30dc85982a210f07f83c81ca0c705502a413809b03581a80b805b01980c8048023007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record031_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record031_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record031) (record031.maps 2)
      (record031.inverseMaps 2) record031_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record031_frame002_links_0000 (interval_append _ 64 128 135 record031_frame002_links_0064 record031_frame002_links_0128))
theorem record031_frame002_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 2 :=
  of_group record031 2 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record031_frame002_indices record031_frame002_graph record031_frame002_links
def record031_frame003_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb18ad1abfab8ab3aaaaa1a9aa55a46a39a18a039a598197a97096395894e9038f68e98cf8bd89588b8808728638557f77e47d37b87a179c79378377276375374673271e7096f06de6c36b06aa64061b61560c6015f55e859d59158456955b54053952f52451750a4bd4b04a248947947647046345544743942d41d40d3fc3e93db3c23b33ae2e72a029628627526725a2091fa1c21ba1ae1a019118313712b0f10e60d90cc0b20a009f09609506906805a05903303202402300f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record031_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record031_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record031) (record031.maps 3)
      (record031.inverseMaps 3) record031_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record031_frame003_links_0000 (interval_append _ 64 128 135 record031_frame003_links_0064 record031_frame003_links_0128))
theorem record031_frame003_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 3 :=
  of_group record031 3 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record031_frame003_indices record031_frame003_graph record031_frame003_links
def record031_frame004_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x6a468868067d67c67a67767366065c65864e6476186035fd5f75f05e85e25ab5a259758657756455f55a55454c54350c5064fb4e74d84d64d14cc4c64c14bc4b84b24ac4a549d49748f48948544642c42741f41940e4063d43cd3c13ab39e38938438037836f36333132b3223082fb2fa2f52f12ec2e62e12dc2d62d02c92c22bd2b62b22b02131db1d51cc1c41b91b117c17314b14613e13412c1210ed0e50bb0b70b20ab09e09109008908806806705a05903203102402300f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record031_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record031) (record031.maps 4) (record031.inverseMaps 4) record031_frame004_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record031) (record031.maps 4) (record031.inverseMaps 4) record031_frame004_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record031) (record031.maps 4) (record031.inverseMaps 4) record031_frame004_indices (Fin.ofNat record031.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record031_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record031) (record031.maps 4)
      (record031.inverseMaps 4) record031_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record031_frame004_links_0000 (interval_append _ 64 128 135 record031_frame004_links_0064 record031_frame004_links_0128))
theorem record031_frame004_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 4 :=
  of_group record031 4 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record031_frame004_indices record031_frame004_graph record031_frame004_links
def record031_frame005_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3e51d1ae3070db80dbdadd46deb4c5a38d0566cb305746b455982c69610af5570a97d4a2a3c50ea8253789a84cba6112e295f473a36118a8a6449a22d0f286742aa11506682840ba014fe47dc3e59ec8f4479d3379844bf85e62ea1704b5a52b28e94209d24d524411d08c645021e90ac7663a41c88dc86be3571a28ccc64231117f8bd05c62d115f0aa052e27e13709a43d81c90e106ec3681ad0d3060c2f81600ac854829614409e84682260f5077039c1c00d305802bc13809b03581a80b805b01980c8048023007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record031_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 5) (record031.inverseMaps 5) record031_frame005_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 5) (record031.inverseMaps 5) record031_frame005_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 5) (record031.inverseMaps 5) record031_frame005_indices (Fin.ofNat record031.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record031_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 5)
      (record031.inverseMaps 5) record031_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record031_frame005_links_0000 (interval_append _ 64 128 135 record031_frame005_links_0064 record031_frame005_links_0128))
theorem record031_frame005_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 5 :=
  of_group record031 5 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record031_frame005_indices record031_frame005_graph record031_frame005_links
def record031_frame006_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x8b987e86685f85985384d84682381d81780c80579776275474873e7347286e46d76cb6b66a867366365564b63f6325e65d65c85b059e59858f58757f57756f56a56155955054553d53352b5284b447946945b4514454383ec3dc3ce3b63a437436635a35034633a2f62e92dd2c82ba2b52ac2a429c29428c28727e27626d26225a2502482451d81b71b01a81a119919016916214513e13612f12711e0f70f00d40d00cc0c80c00aa0a909c09b06b06a05c05b03303202402300f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record031_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record031) (record031.maps 6) (record031.inverseMaps 6) record031_frame006_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record031) (record031.maps 6) (record031.inverseMaps 6) record031_frame006_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record031) (record031.maps 6) (record031.inverseMaps 6) record031_frame006_indices (Fin.ofNat record031.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record031_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record031) (record031.maps 6)
      (record031.inverseMaps 6) record031_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record031_frame006_links_0000 (interval_append _ 64 128 135 record031_frame006_links_0064 record031_frame006_links_0128))
theorem record031_frame006_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 6 :=
  of_group record031 6 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record031_frame006_indices record031_frame006_graph record031_frame006_links
def record031_frame007_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x7196dd6d16c96c26ba6b16a767166365663f62f5ee5d25cd5c45bd5b35ac57657056255154652d52751c5135094ff4cb4c34b54a449849649248647b46f46845f45244343642941c40b4024003b539939338e38437e37333d33432c31830d2f42ee2e62da2d12c629228927e26b25f25d25624d24023822f22621720a1fd1ed1e41d21c91c717115715414f14914313d12511f10c10a1051000fb0f60da0d40be0b80b30af0a709809708c08b06406305505403303202402300f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record031_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record031) (record031.maps 7) (record031.inverseMaps 7) record031_frame007_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record031) (record031.maps 7) (record031.inverseMaps 7) record031_frame007_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record031) (record031.maps 7) (record031.inverseMaps 7) record031_frame007_indices (Fin.ofNat record031.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record031_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record031) (record031.maps 7)
      (record031.inverseMaps 7) record031_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record031_frame007_links_0000 (interval_append _ 64 128 135 record031_frame007_links_0064 record031_frame007_links_0128))
theorem record031_frame007_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 7 :=
  of_group record031 7 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record031_frame007_indices record031_frame007_graph record031_frame007_links
def record031_frame008_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x1392684cc98f316624c297f2ba54ca293124a3d46b8cb17e2dc568a50c617425831035ff3f87e2fb1f3be076eecdd3397714e19bfb796e8db9b53666bcd55a7346680ce59ab3362ec157f2f95e6bb973abe56eac14f2915089f93d2744e09ad2524647e8c5132234368590820c40e80cfd1f23d6788ee9d63a4740c51732d859cb01592a84bc9410f2144087e0f51e032c620a914627c4e09411822c430850c4184298520620c01202301e0380600b0140240380600a01001801 } : Fields).get c.val)
theorem record031_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record031) (record031.maps 8) (record031.inverseMaps 8) record031_frame008_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record031) (record031.maps 8) (record031.inverseMaps 8) record031_frame008_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record031) (record031.maps 8) (record031.inverseMaps 8) record031_frame008_indices (Fin.ofNat record031.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record031_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record031) (record031.maps 8)
      (record031.inverseMaps 8) record031_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record031_frame008_links_0000 (interval_append _ 64 128 135 record031_frame008_links_0064 record031_frame008_links_0128))
theorem record031_frame008_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 8 :=
  of_group record031 8 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record031_frame008_indices record031_frame008_graph record031_frame008_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (Fin.cases (record031_frame002_supported hcells) (Fin.cases (record031_frame003_supported hcells) (Fin.cases (record031_frame004_supported hcells) (Fin.cases (record031_frame005_supported hcells) (Fin.cases (record031_frame006_supported hcells) (Fin.cases (record031_frame007_supported hcells) (Fin.cases (record031_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x17d6e6d7fac7576ab5269a33065b4af8ad14224c4081500dff3f87daf91ef3d3760eb1d43856c0d29a032c642c6d78ac857cab551a9f52a9c9272474828ad11a133e4724dd9b2356684cd1702b8530a31392504607c0f11d83846d8d518c3005d8b61041fc3e0690ca18c2d0560aa1402784e0720e01a8340640a81402604808c1081e03a0700a01302003c0700b0120200380400600800800 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record032_frame001_links_0000 record032_frame001_links_0064)
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
def record032_frame002_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x7b177972971871370d6c663d62d61b61258c58257456852e52852251d51450e5074fb4c64bc4b648144d42e42240c3ff3f93c238a37536335334b33e3172ff2f92f42e62e02d529425123d23222721720a1d01ba1a819f18e17d16913512611e10b0fa0f20d50cb0c60c108c08a08706e06a06805e05a05905405305203803703403303102a02802602402302101e01d01c01401301000f00e00b009008007004003002001000 } : Fields).get c.val)
theorem record032_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record032) (record032.maps 2) (record032.inverseMaps 2) record032_frame002_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record032) (record032.maps 2) (record032.inverseMaps 2) record032_frame002_indices (Fin.ofNat record032.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record032_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record032) (record032.maps 2)
      (record032.inverseMaps 2) record032_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record032_frame002_links_0000 record032_frame002_links_0064)
theorem record032_frame002_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 2 :=
  of_group record032 2 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record032_frame002_indices record032_frame002_graph record032_frame002_links
def record032_frame003_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0375.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0375.count (({ width := 8, code := 0xb8b5b0afaeadaaa5a4a3a29d9c9b9a94939291908f8e8d8c8b8a858281807f7e7d797675747372716b696867656463615e5d5c5b5a595352504f4e4c4b4746454342413f3e3d3c3937363331302e2c2b2928272322201f1e1b1a181716141312110f0e0c0b0a080706050403020100 } : Fields).get c.val)
theorem record032_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0375.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0375.localPairCheck (smallEmbedding record032) (record032.maps 3) (record032.inverseMaps 3) record032_frame003_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0375.localPairCheck (smallEmbedding record032) (record032.maps 3) (record032.inverseMaps 3) record032_frame003_indices (Fin.ofNat record032.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record032_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0375.localPairCheck (smallEmbedding record032) (record032.maps 3)
      (record032.inverseMaps 3) record032_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record032_frame003_links_0000 record032_frame003_links_0064)
theorem record032_frame003_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 3 :=
  of_group record032 3 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0375
    Papers.RationalityTen.SharedFrameCatalogue.group0375_facts record032_frame003_indices record032_frame003_graph record032_frame003_links
def record032_frame004_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0447.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0447.count (({ width := 8, code := 0xb8b5b0afaeadaaa5a4a3a29d9c9b9a94939291908f8e8d8c8b8a858281807f7e7d797675747372716b696867656463615e5d5c5b5a595352504f4e4c4b4746454342413f3e3d3c3937363331302e2c2b2928272322201f1e1b1a181716141312110f0e0c0b0a080706050403020100 } : Fields).get c.val)
theorem record032_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0447.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0447.localPairCheck (smallEmbedding record032) (record032.maps 4) (record032.inverseMaps 4) record032_frame004_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0447.localPairCheck (smallEmbedding record032) (record032.maps 4) (record032.inverseMaps 4) record032_frame004_indices (Fin.ofNat record032.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record032_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0447.localPairCheck (smallEmbedding record032) (record032.maps 4)
      (record032.inverseMaps 4) record032_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record032_frame004_links_0000 record032_frame004_links_0064)
theorem record032_frame004_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 4 :=
  of_group record032 4 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0447
    Papers.RationalityTen.SharedFrameCatalogue.group0447_facts record032_frame004_indices record032_frame004_graph record032_frame004_links
def record032_frame005_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0304.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0304.count (({ width := 8, code := 0x8c8985848382807c7b7a797675747371706f6e6d6c6b6a69686763605f5e5d5c5b595655545352514f4e4d4c4b4a49484544434241403e3d3c3b3a393837363534333231302f2e2d2b2a29272625232221201f1e1d1b1a1918171514131211100f0e0d0b0a09080706050403020100 } : Fields).get c.val)
theorem record032_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0304.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0304.localPairCheck (smallEmbedding record032) (record032.maps 5) (record032.inverseMaps 5) record032_frame005_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0304.localPairCheck (smallEmbedding record032) (record032.maps 5) (record032.inverseMaps 5) record032_frame005_indices (Fin.ofNat record032.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record032_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0304.localPairCheck (smallEmbedding record032) (record032.maps 5)
      (record032.inverseMaps 5) record032_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record032_frame005_links_0000 record032_frame005_links_0064)
theorem record032_frame005_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 5 :=
  of_group record032 5 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0304
    Papers.RationalityTen.SharedFrameCatalogue.group0304_facts record032_frame005_indices record032_frame005_graph record032_frame005_links
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (Fin.cases (record032_frame001_supported hcells) (Fin.cases (record032_frame002_supported hcells) (Fin.cases (record032_frame003_supported hcells) (Fin.cases (record032_frame004_supported hcells) (Fin.cases (record032_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x67466c6325f05bf5ad5a855d5245195114c94bc4b149e49048547f46b43b3f93c43b03ab37033d33532f2ec2e22db2ce2c32bc2b62a927826d26424622d2242172101ed1d11b91a519117e17416414212d12511e1060fe0ee0e00d50c908107f06b06906706405b05a05705505105004f04e03903703503202902802502301f01e01d01c01501401301101000e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
def record033_frame002_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x65a6566335f85bd59d5955555185044f64bb4b44ae4a249b4954904834624223e63c83bf37b33c32931d2e02d82d22c62c02bb2b72ae28928027524922721d2061f91d51c41b119818617216815513e12c1211140f60ec0d80c50bc0b808608306e06c06a06705f05e05b05905505405305203803603403102902802502301f01e01d01c01501401301101000e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record033_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record033) (record033.maps 2) (record033.inverseMaps 2) record033_frame002_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record033) (record033.maps 2) (record033.inverseMaps 2) record033_frame002_indices (Fin.ofNat record033.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record033_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record033) (record033.maps 2)
      (record033.inverseMaps 2) record033_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record033_frame002_links_0000 record033_frame002_links_0064)
theorem record033_frame002_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 2 :=
  of_group record033 2 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record033_frame002_indices record033_frame002_graph record033_frame002_links
def record033_frame003_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x518a2b3be5e48b8ef1d22641d82702df03da7a4f19df3b9764e99bbb3b612bd578ac352aa2940a5c4b0949242404788dd1620c4047e4ee1c33726a0cf1842ea59cac94e2764d49291320a3f47b8dd1aa3205d8b616021c4286e0da1ac340600be1742d8570ac1542a03906e0d4190290500941181f03c0740e01502804c0881001c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record033_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record033) (record033.maps 3) (record033.inverseMaps 3) record033_frame003_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record033) (record033.maps 3) (record033.inverseMaps 3) record033_frame003_indices (Fin.ofNat record033.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record033_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record033) (record033.maps 3)
      (record033.inverseMaps 3) record033_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record033_frame003_links_0000 record033_frame003_links_0064)
theorem record033_frame003_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 3 :=
  of_group record033 3 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record033_frame003_indices record033_frame003_graph record033_frame003_links
def record033_frame004_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd1567db029654a89525a8e93228fa46b22fd06081c4061fa4fac7c73db9e54dac5f62aa945ca0c45d1e30e887162fc1740b6056a2a21498a0c4c223911908ac41e1fa0f9878c3b81c20da069832e18a0bd85d42ce1520a204f426a12108c84301fc0f6078024811a07103781b40d406103001740b605702b01540a803901b80d4064029014009404601f00f007403801500a004c0220100070030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record033_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 4) (record033.inverseMaps 4) record033_frame004_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 4) (record033.inverseMaps 4) record033_frame004_indices (Fin.ofNat record033.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record033_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 4)
      (record033.inverseMaps 4) record033_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record033_frame004_links_0000 record033_frame004_links_0064)
theorem record033_frame004_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 4 :=
  of_group record033 4 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record033_frame004_indices record033_frame004_graph record033_frame004_links
def record033_frame005_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x47e8f114210bf87d2f91dcb93712e0db0b5a6aad35a2b3f676cbd88adf570aa952a764a492922222436855052033fc7e8f81d5398710d619731e610c01672ae5249c92922e440808f21d03906f0cd18c2ec580ac1501fc3d8680cc190308580ae1502904e09a1302583906e0d4190290500941181f03c0740e01502804c0881001c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record033_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record033) (record033.maps 5) (record033.inverseMaps 5) record033_frame005_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record033) (record033.maps 5) (record033.inverseMaps 5) record033_frame005_indices (Fin.ofNat record033.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record033_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record033) (record033.maps 5)
      (record033.inverseMaps 5) record033_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record033_frame005_links_0000 record033_frame005_links_0064)
theorem record033_frame005_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 5 :=
  of_group record033 5 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record033_frame005_indices record033_frame005_graph record033_frame005_links
def record033_frame006_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x78e7867396f36be69e69564e6025ec5dd58557d57356355654c5405274ef49844d42c4233d63a539538b33b32e32430b3002fb2f12dd2b12a729927224f2472312282071f11dd1c81ba1a219818116415214713d11a10d0fd0eb0e30dc08c08706e06c06a06705e05d05a05805405305205103803603403102902802502301f01e01d01c01501401301101000e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record033_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record033) (record033.maps 6) (record033.inverseMaps 6) record033_frame006_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record033) (record033.maps 6) (record033.inverseMaps 6) record033_frame006_indices (Fin.ofNat record033.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record033_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record033) (record033.maps 6)
      (record033.inverseMaps 6) record033_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record033_frame006_links_0000 record033_frame006_links_0064)
theorem record033_frame006_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 6 :=
  of_group record033 6 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record033_frame006_indices record033_frame006_graph record033_frame006_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (Fin.cases (record033_frame002_supported hcells) (Fin.cases (record033_frame003_supported hcells) (Fin.cases (record033_frame004_supported hcells) (Fin.cases (record033_frame005_supported hcells) (Fin.cases (record033_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x381d8f8c685d1285d4069ae4d3a68130896f4b425612a291b489a4311fe8f747823a91b883234199b8bc65d22e015d0a7a52b28193c88ce454221108c8224011f88f446e83631a88c1459c2bc14a0a0c3f01e50e986d03441920c105882ac14f0a4050427413308b84101ec0ef074824811a06f03501880c206002f01740b605702b01540a803701900a8052028013009404601f00f007403801500a004c0220100070028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record034_frame001_links_0000 record034_frame001_links_0064)
theorem record034_frame001_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 1 :=
  of_group record034 1 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record034_frame001_indices record034_frame001_graph record034_frame001_links
def record034_frame002_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3bdda26cfb605293d4749b64d1264528c90c47d234917e83040f2030fd27d83e39edcf2a6d628d941890446e22e90487b03c61cf0e2c5f82ea16c0ad45482931418984472232115883c3f41f30f1877034c19e0cb862830417b0ba859c2c01590a9052c28813d09084301fc0f7078024811a06f03501880c206002f01740b605702b01540a803701900a8052028013009404601f00f007403801500a004c0220100070028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record034_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record034_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record034) (record034.maps 2)
      (record034.inverseMaps 2) record034_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record034_frame002_links_0000 record034_frame002_links_0064)
theorem record034_frame002_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 2 :=
  of_group record034 2 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record034_frame002_indices record034_frame002_graph record034_frame002_links
def record034_frame003_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xeeda934b63cad55728d514a1d3da724de99d3224e49491d2123e4768e519a1835e6a0c39843025d4b61692c2578a41442824f09c1352664b48f11b230430819001f03d46f8db1b034c678cc194310608c017e2f85e8bc1702d4598b21622384486d0d01802f85e0b816c2c8550a814c290370640a81482804c0941181f03c0740e01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record034_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record034) (record034.maps 3) (record034.inverseMaps 3) record034_frame003_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record034) (record034.maps 3) (record034.inverseMaps 3) record034_frame003_indices (Fin.ofNat record034.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record034_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record034) (record034.maps 3)
      (record034.inverseMaps 3) record034_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record034_frame003_links_0000 record034_frame003_links_0064)
theorem record034_frame003_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 3 :=
  of_group record034 3 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record034_frame003_indices record034_frame003_graph record034_frame003_links
def record034_frame004_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6df67366c6325ae5a857156655d54152d5245185114c94bd4b149e49148547f46b43b3b13ab38137837035934533d33432f2ec2e42db2ce2c52bc2b62a927826d26424622d2242172101b91af1a519118817e17416415814c14213712d1251060ee0e00d60c908107f06906405c05b05a05805705505105004f04e03703202a02902802602502301f01e01d01c01501401301101000e00a009008007006005004003002001000 } : Fields).get c.val)
theorem record034_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record034) (record034.maps 4) (record034.inverseMaps 4) record034_frame004_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record034) (record034.maps 4) (record034.inverseMaps 4) record034_frame004_indices (Fin.ofNat record034.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record034_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record034) (record034.maps 4)
      (record034.inverseMaps 4) record034_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record034_frame004_links_0000 record034_frame004_links_0064)
theorem record034_frame004_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 4 :=
  of_group record034 4 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record034_frame004_indices record034_frame004_graph record034_frame004_links
def record034_frame005_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0xfb5db3b072cd7dacb3665cca18b309606be17a2cc58cb015bab0554a9d4e28b4a693d17a2c452865062063f67d4e59c63826dcd71a9348670c117c2ec598ae15929e5248f918226420818fe1f23c0748e41bc360690cc1702984f09a12a1c4368600b8150298520a21402784b094124240370640a81482804c0941181f03c0740e01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record034_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record034) (record034.maps 5) (record034.inverseMaps 5) record034_frame005_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record034) (record034.maps 5) (record034.inverseMaps 5) record034_frame005_indices (Fin.ofNat record034.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record034_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record034) (record034.maps 5)
      (record034.inverseMaps 5) record034_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record034_frame005_links_0000 record034_frame005_links_0064)
theorem record034_frame005_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 5 :=
  of_group record034 5 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record034_frame005_indices record034_frame005_graph record034_frame005_links
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (Fin.cases (record034_frame001_supported hcells) (Fin.cases (record034_frame002_supported hcells) (Fin.cases (record034_frame003_supported hcells) (Fin.cases (record034_frame004_supported hcells) (Fin.cases (record034_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
def record035_frame001_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xdfd68c33e99c4b42596ac5d512a4951ca8953228d146022b113486442120c104280b3fc9f58f907b73ca1838bf25e32aa9454a0a4f122e8e747183781b30cc061c2fc1768b5c58a2a214a0a0c4c023911908ac3f41dd0eb07403921c20dd86d035a1a60ce865831e17c0ba85982a414409e84d424211908984301ec0db04681ec0da06a03081800b605a02c015c0ac05402180d4064029014008c04402000f807803801500a004c02200e006803001600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record035_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record035_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record035) (record035.maps 1)
      (record035.inverseMaps 1) record035_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record035_frame001_links_0000 record035_frame001_links_0064)
theorem record035_frame001_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 1 :=
  of_group record035 1 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record035_frame001_indices record035_frame001_graph record035_frame001_links
def record035_frame002_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb65af0ad4ac5a21a15a0f9b297e96d95e90986184a8368247f77d47c07ae79477f75574272b6fd66e6616596085de5d55c95774ee4e04d24c449b48247746b45744842841d40f3ef3bd3ae3a43412f92e92d82c72b72ad2a12932862732632532252151f11cd1b51a819716b1561451351030cd08d07b06d06a06106005b05a05805705605404303503202902802302202001f01e01c01501401301100e00d00c00b00a009007005004003002001000 } : Fields).get c.val)
theorem record035_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record035) (record035.maps 2) (record035.inverseMaps 2) record035_frame002_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record035) (record035.maps 2) (record035.inverseMaps 2) record035_frame002_indices (Fin.ofNat record035.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record035_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record035) (record035.maps 2)
      (record035.inverseMaps 2) record035_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record035_frame002_links_0000 record035_frame002_links_0064)
theorem record035_frame002_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 2 :=
  of_group record035 2 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record035_frame002_indices record035_frame002_graph record035_frame002_links
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (Fin.cases (record035_frame001_supported hcells) (Fin.cases (record035_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x38fdc5ee286d83615ae4d176763365970cb1655329193ac96648b2298f8bae5862b5558eab95582ab1548a9b4f726612ec95349e24d120c8e5461a281112881429a12d08c83d41b20c0e8869a3379984cb46543251914c7a5a02af950ca6a52d28a13e09a44b6254128090e46b23391808b64562290c7c6122fb17709f84d025a12688cc45622310e08543441920bf055428613908b84181f80da06901ec0f007103701780b805b02c815c0ac04202000e006c025012008c04001f00f004801e00e0068028012008002000c002000 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
def record036_frame002_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x7337257207006f26ea6d06b86af69b69368d68367766c66565863d5f85b959c58b57956756555a5475124ec4de4cb4bb4b849a48f47846545545042c42441d40e4053fd3ba37a35c34a34033732332130e2d02ac29c29228c27626124a23522c22420d1f31ee1df1d51cc1c417116916316113d13512f12d12612011611110e0f60f10eb0de0d70d10c40bd0b70ab0a907307006a06705705505405205004f04103f03803602502402302001f01e01200f00e00d00a009008004003001000 } : Fields).get c.val)
theorem record036_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record036) (record036.maps 2) (record036.inverseMaps 2) record036_frame002_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record036) (record036.maps 2) (record036.inverseMaps 2) record036_frame002_indices (Fin.ofNat record036.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record036_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record036) (record036.maps 2)
      (record036.inverseMaps 2) record036_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record036_frame002_links_0000 record036_frame002_links_0064)
theorem record036_frame002_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 2 :=
  of_group record036 2 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record036_frame002_indices record036_frame002_graph record036_frame002_links
def record036_frame003_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x12724bc9590d1fa3bc678c116a2844a88f1122043c8730d214c077b6f0ddebb575ceb5d4ba370adb5b2357698d2d9b32d644c5585b0a5e2bb575ae45c0b7958a8d4f09c9362694c29812d23543683d04a043ea794ed9d1392710dc1a834c67ccd99732a52ca113b2724648810a20e3f87c8f51e63c46c0d31982f45c8b4152290500941241ac348630c01482804f09a12c2503c0740d81a02504808c1001f03c0480780e01a0280480800800c00800 } : Fields).get c.val)
theorem record036_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record036) (record036.maps 3) (record036.inverseMaps 3) record036_frame003_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record036) (record036.maps 3) (record036.inverseMaps 3) record036_frame003_indices (Fin.ofNat record036.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record036_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record036) (record036.maps 3)
      (record036.inverseMaps 3) record036_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record036_frame003_links_0000 record036_frame003_links_0064)
theorem record036_frame003_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 3 :=
  of_group record036 3 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record036_frame003_indices record036_frame003_graph record036_frame003_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (Fin.cases (record036_frame002_supported hcells) (Fin.cases (record036_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0841.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0841.count (({ width := 11, code := 0x2a5d31a43452875009ed3b2734de8fd16229447881075fa3ef7cef75e7bc477aee1d7ba373ee45c5386694ca98db14602bd9722d85a6b315aaa5538a153d26c4c69812ba5349a92122a3e46e8bd1521f43083904204398664c818b30c5c0b19572a05209e12d246474870ff1ee3bc728d61a03345d8b614026c3806a0d21682c8560aa1502083e0700dc1a82604808c1082003e0780a01201e0380680b0140240400500800c00800 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0841
    Papers.RationalityTen.SharedFrameCatalogue.group0841_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xebc6e8b4ad9aebc8577a98944ea0b4dca6052dc932486239d1a08c244b21910848304102024fca7b53d29e5cd285bb29713cc9ae48522690e87fc3d81d98e7071c3621980c385f82ec16a8ac450227113188e444821d10407e83d81dd0eb86ec35a1a60cf06442e616c0b285802b21520a5851027a134096847c2260fd07b83681aa07b03c01c00dc05e02e016c0b005702b010c08003801b0098048023010007c03c01500a004802200f007003401600a004802000c005002000c002000 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
def record038_frame002_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x68dccb91b1c607b97696ccd91af3576a8d38a4d44680cfa9b731e59ca593923a37c608b314e0d3dc76eeadd1b896e4d99a6b3e654c6d8b2fd5d8b6d672c4572a854aa905189b927a4345086d039f13d872cde1af348650bb16f2d258cae15228e4f0989232303ec750cf18c28c4d86b0d2190310540a41442704d0980f81e0360680981202304007c0f0150280480880f01c0340580a0120200300500800c00800 } : Fields).get c.val)
theorem record038_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record038) (record038.maps 2) (record038.inverseMaps 2) record038_frame002_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record038) (record038.maps 2) (record038.inverseMaps 2) record038_frame002_indices (Fin.ofNat record038.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record038_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record038) (record038.maps 2)
      (record038.inverseMaps 2) record038_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record038_frame002_links_0000 record038_frame002_links_0064)
theorem record038_frame002_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 2 :=
  of_group record038 2 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record038_frame002_indices record038_frame002_graph record038_frame002_links
def record038_frame003_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x47e8b50f214c077a6ed5d4ba3728e15bdb6d6c8d5da634866cca18e31561ec0978ae45c0b795c28d4d89812d24b4748d510a164127f0fc9e53b6744e49c13706a0cd99732a608b896b2ba550a593d27249c8e91922441c7a8f31e23b4750e41be36c6c0d01922f45b0a914c2504906b0d2188300520a013c2604b0940f41d0360680981202304007c0f0150280480880f01c0340580a0120200300500800c00800 } : Fields).get c.val)
theorem record038_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record038) (record038.maps 3) (record038.inverseMaps 3) record038_frame003_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record038) (record038.maps 3) (record038.inverseMaps 3) record038_frame003_indices (Fin.ofNat record038.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record038_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record038) (record038.maps 3)
      (record038.inverseMaps 3) record038_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record038_frame003_links_0000 record038_frame003_links_0064)
theorem record038_frame003_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 3 :=
  of_group record038 3 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record038_frame003_indices record038_frame003_graph record038_frame003_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (Fin.cases (record038_frame002_supported hcells) (Fin.cases (record038_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1cbcd9e6abb509a76d2668c3429a0acf059b2ac1544a644e5251126c8f8470a34d1988c645e22dd15c8aa451226512488d3d01c9cdee6e735a1a44ce465d3131748b445922af94f0a3a50826893209824ba25992b494c49d24b124491048123e91d48de46b1d40c6460c2c514c89e84d625811e086841c1e40db065c3101750ac84dc25610107c03c01d20e206d83500e006e03581a80c205f02e016c07203801b00d406603201500a404e026012008c028012007803801600a004802000e005002000c004001 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
def record039_frame002_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0847.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0847.count (({ width := 11, code := 0x337e4dc7d8cf1561ac2380efd5eab0d55ea9541a053165fcaa92b20e3bc6f8bb16224c458710b60fc1a7d0f31ddbb173ee49c137b6d8d3d9e331638c397d2f35d0b856c2d259ab015b2a7542a7948a8850a9f13927045c7d8f69dd38a6ccd419d3225f8bc9622944cc9391a21c3e0798db1a43105c8ad14a274340670ca1902d8590ac1541c83806c0d4198320540a41382604808c0a01201e0380580a0120200380500800c01001 } : Fields).get c.val)
theorem record039_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record039_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record039) (record039.maps 2)
      (record039.inverseMaps 2) record039_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record039_frame002_links_0000 record039_frame002_links_0064)
theorem record039_frame002_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 2 :=
  of_group record039 2 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0847
    Papers.RationalityTen.SharedFrameCatalogue.group0847_facts record039_frame002_indices record039_frame002_graph record039_frame002_links
def record039_frame003_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0841.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0841.count (({ width := 11, code := 0x2a5530a4545687d019ef3b673cdf8fd15a28c41836fd1f73de7a2f15df3b975ceadd13a0730e41c4b87696ca98db145febd1712da59aacd51a9a50a9e9362654b09512724a48c8fd1c22e4528a10f21742a83503a05398664c91812e058cab9502904e49a91e21c3fc7b8ec1c0340668bc1702c4558a613e268350690cc1942f05c0b41641c03706a0d0190310540a41382604808c0a01201e0380580a0120200380500800c01001 } : Fields).get c.val)
theorem record039_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record039_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record039) (record039.maps 3)
      (record039.inverseMaps 3) record039_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record039_frame003_links_0000 record039_frame003_links_0064)
theorem record039_frame003_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 3 :=
  of_group record039 3 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0841
    Papers.RationalityTen.SharedFrameCatalogue.group0841_facts record039_frame003_indices record039_frame003_graph record039_frame003_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (Fin.cases (record039_frame002_supported hcells) (Fin.cases (record039_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xd576a134eda14d0467eb3d59d4b825a62cf1560aa1546a97d42c9e04e8251126a921479a3bd1d08e146d234d1988c746022c91528a244ca24911c72737b9b9cce465e32598e4ba45a22c91474a124f627213209824ba25992b494c49d24b124491048323e91d48de4692030efc7563191828bc45862b91548a6451427a135895c49022910e88383c21d60e306d834e1970c405d02ca14609d04ac1fc0f707803a41c40dc06a02bc13606b03501700b604001c80e006c03301900c40540290138090046022007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record040_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record040_frame001_links_0000 (interval_append _ 64 128 133 record040_frame001_links_0064 record040_frame001_links_0128))
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
def record040_frame002_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xabfaaaaa1a55a46a39a28a039819639589038f68e98bd8958728637f77e47d37a179c7937837727637537467327096f06de6c36b06aa6195fc5f059d58c57f57053e51f5124bd4ab49d4904764704634554474394204104073f03e93db3c23b33a337a3553482e72da2ce2a82a029628627526725a2452352162091fa1ca1c21ba1ae1a019118316f16114213712b0fb0f10e60d90cc0c20b209f09506906805a05904003903803603303203102a02902702402302200f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record040_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record040_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record040_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record040) (record040.maps 2)
      (record040.inverseMaps 2) record040_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record040_frame002_links_0000 (interval_append _ 64 128 133 record040_frame002_links_0064 record040_frame002_links_0128))
theorem record040_frame002_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 2 :=
  of_group record040 2 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record040_frame002_indices record040_frame002_graph record040_frame002_links
def record040_frame003_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x68067a67766065c6586526476035f05e85ab5a259757756455454c50c5064fb4d84d64d14cc4c64c14bc4b84b24a549d49748f48948542a4134093d43c93bc3b238737336933132631e30f2fa2f52f12ec2e62e12d72d12ce2c52c22bd2b62b22ad28a26c25f2132091fc1e01db1d51cc1c41b91b11a019618217c17315214b14613e13412c1211121080f20ed0e50c20bb0b70b20ab0a509e09008806806705a05903e03803703503203103002a02902702402302200f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record040_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record040) (record040.maps 3) (record040.inverseMaps 3) record040_frame003_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record040) (record040.maps 3) (record040.inverseMaps 3) record040_frame003_indices (Fin.ofNat record040.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record040_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record040) (record040.maps 3) (record040.inverseMaps 3) record040_frame003_indices (Fin.ofNat record040.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record040_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record040) (record040.maps 3)
      (record040.inverseMaps 3) record040_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record040_frame003_links_0000 (interval_append _ 64 128 133 record040_frame003_links_0064 record040_frame003_links_0128))
theorem record040_frame003_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 3 :=
  of_group record040 3 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record040_frame003_indices record040_frame003_graph record040_frame003_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (Fin.cases (record040_frame002_supported hcells) (Fin.cases (record040_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record040_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058
