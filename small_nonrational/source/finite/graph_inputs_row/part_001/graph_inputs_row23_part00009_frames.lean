module
prelude
public import GraphInputsRow23Part00009Data
public import RawFrameSupport
public import SharedFrameGroups033Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups044Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups080Checked
public import SharedFrameGroups081Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups090Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
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
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x67e2c45548a5e4bd23050846d535d997cc546192f49690ab05442999494a3049f24891007783ab1cd8dec64a3131828b8c58429013e89ac4682220ca054428213108f04441e60e606a832416e0b104981f00e406802f0160094044020810007403801b80d8060029013008804001d00d805802200f007002c0140090030014002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x60e5d85ac5a75575285074d04a749f49449048a4173c83a839c3983423373313172fb2e82d82c82a529729428f25523f2081ee1df1b119718f18117517116014f13d11e1141090fe0f70e70df0d40cd0c40b508a07c07506c06706105a05405204804003603503103002b02602402101e01c01601401301200f00d009008007005004003001000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcca544a9354209914aba3991808ac44d20bd0187fa3f49f58aaa51926e11748463b21c60de06cc2fb16c0b1856a2a211c08ac42820d0fd07ac3ca1dd0eb074038e1b40d2867c32e1900c5057c2a4144090846422610c07b03c01d208d04601b40d406903181840c005b02d01580aa05401a80c806202b01480a004602200f007403801b00b00500260110070034018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xc795632ac5538a034dda54925891a485227d0f286742ba128cce65231f170cb0e53428b94249f84a724511f08de4641f60f006f836b19f8c7861c2fd1768b7459429e13e89b44b824c11e08143c01b70ab851c27813108503fc1e808d04601b40d406903181840c005b02d01580aa05401a80c806202b01480a004602200f007403801b00b00500260110070034018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x6f76a869c6946706495ed5e15c95b558357855454553e52f52952251c4a444d43f42e40e3e438037234d34130c3042d82d02c92c22b62b02ab1dd1d31a718517716d15f15812710c0f70ed0e60d80cc0c80c40c10a909f09808e08d08207c06f06d06b05f05e05b05905505404a04403703403302702502302001d01c01601301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x5f95b65af5ab59358453a52f5134fd4e14d84a649048a47d47747146c3f83ac3a639e38e38033132830c3032ec2e42b52ac2a82a329a2972941da1d519c17d1771711661621261070f60ef0e60dc0d00c90c00ba0a109609008a08907c07606d06b06905d05c05905705305204804203703403302702502302001d01c01601301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0927.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0927.count (({ width := 9, code := 0x49a3f1d8e4622d0e8642a0f04813f9f6fa7cbe1eef674b89c0de6db65a2cf663298ec5602f97abc5d2e5708f46a08f0773b1c8e0652e968b25629948a24e261208c442110474391c0dc6a34198c4602e168984a2411084401e0e86c3419098401e0c058200e06018080200 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0927.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0927.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0927.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0927.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0927
    Papers.RationalityTen.SharedFrameCatalogue.group0927_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
def record003_frame004_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0948.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0948.count (({ width := 9, code := 0x48233178b44a21088341202fe7e3e1eaf479bc9e2f07337dbadb6c3599ccc64b1d88c25eaed74b95bad96a8f46a08f0773b1c8e0652e968b25629948a24e261208c442110474391c0dc6a34198c4602e168984a2411084401e0e86c3419098401e0c058200e06018080200 } : Fields).get c.val)
theorem record003_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0948.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0948.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0948.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record003_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0948.localPairCheck (smallEmbedding record003) (record003.maps 4)
      (record003.inverseMaps 4) record003_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record003_frame004_links_0000 record003_frame004_links_0064)
theorem record003_frame004_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 4 :=
  of_group record003 4 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0948
    Papers.RationalityTen.SharedFrameCatalogue.group0948_facts record003_frame004_indices record003_frame004_graph record003_frame004_links
def record003_frame005_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0911.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0911.count (({ width := 9, code := 0x4e25b2c9548a411489c421b0984405fafb7cbe1eef67336db4d768b3d86c25faf572b8582b958ab54aa14e8b44a00f0763a9bcda662f96cb4572a14ca44f269188842200fc70371b0d46632188bc5c2c1589046221007c3c1c0d8643017088381a0b050200c05018080200 } : Fields).get c.val)
theorem record003_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0911.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0911.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0911.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record003_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0911.localPairCheck (smallEmbedding record003) (record003.maps 5)
      (record003.inverseMaps 5) record003_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record003_frame005_links_0000 record003_frame005_links_0064)
theorem record003_frame005_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 5 :=
  of_group record003 5 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0911
    Papers.RationalityTen.SharedFrameCatalogue.group0911_facts record003_frame005_indices record003_frame005_graph record003_frame005_links
def record003_frame006_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x5e65a559e5995735554f84f14de4c849c49345943942f41440d4063fb3ad36c36535933a31c2bf2b829c28f26325a2112001f61e51d41cd1c215f15b13b12812211c1121100f50e40d70d10ce0c50bd0b70b40b109a09008a08208107807406806606405805705405204e04d04704303703403302702502302001d01c01601301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record003_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record003_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record003) (record003.maps 6)
      (record003.inverseMaps 6) record003_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record003_frame006_links_0000 record003_frame006_links_0064)
theorem record003_frame006_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 6 :=
  of_group record003 6 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record003_frame006_indices record003_frame006_graph record003_frame006_links
def record003_frame007_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0xd719f33c674ca98d2f05dcb896b2c0572a854a28e50aa093ea7a4bc8e51ba2c43e834f51e83b6758e11bb33a654c898b3065fcbe12223e4187a0ee1d2388700c516e2b0540a513e2644a89311e2103f07a0ec1d43606a0c017c2e8520a21382604808e1041f8330600bc138250460800e81c02c04c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record003_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record003_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record003) (record003.maps 7)
      (record003.inverseMaps 7) record003_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record003_frame007_links_0000 record003_frame007_links_0064)
theorem record003_frame007_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 7 :=
  of_group record003 7 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record003_frame007_indices record003_frame007_graph record003_frame007_links
def record003_frame008_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0590.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0590.count (({ width := 11, code := 0xed9cb39171cdedb6b4267ecd996319628be976ae95bcb6d6aad053ea113fa784d296d1822c432851001fc3c4768eb9cf392708df1592a64c08d91321c4107e8dd19c3145f8bc1602a4528a01342184107e0f41e43706b0c41802f0540a61402704a0921041e8350640c4138250460800e81c02c04c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record003_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record003_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record003) (record003.maps 8)
      (record003.inverseMaps 8) record003_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record003_frame008_links_0000 record003_frame008_links_0064)
theorem record003_frame008_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 8 :=
  of_group record003 8 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0590
    Papers.RationalityTen.SharedFrameCatalogue.group0590_facts record003_frame008_indices record003_frame008_graph record003_frame008_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (Fin.cases (record003_frame005_supported hcells) (Fin.cases (record003_frame006_supported hcells) (Fin.cases (record003_frame007_supported hcells) (Fin.cases (record003_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x2cb5909df3a62a440826ff9f6be47bcf65e9b6359cb2155a9550e9c930a5948e8ad11a1b42674ce49b0334630b81662ae5309c9282404606d8d5196318600bb16c25c470800fe1d4338650ba1682c8560a013c2704808e0fc1b0350680ac1402704c0901081e03a0700b0130240400780b0120200380400600800800 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x17ecbe252ca92118a88e4071f68f767a83c89dfceda65229b949c9ca4ba25091c48ac44921710187ec3e91ee8d346482f51640ab84da25f12388e44422000fa079c2a8143092046020c0fa07582d014a09104802080dc06c03181800be05c02b01540a804a02480fc06c03501a00ac050027013009004201e00e807002c013009004001e00b004802000e0040018008002000 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record004_frame002_links_0000 record004_frame002_links_0064)
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xdb156c2b0528691e472a2ad05e7fa3eb1f1cf6c7a73ca9690b1a40f1f50ec46ee2fb1630a8852628213989844102010f5075438e1b40d2867c32017b0ba05b82ce15f0a9051025e11908283f81ec0f0074829412208204081b80da063030017c0ba05c02b01540a804a02480d806a02b014009c04a02400f007403801b00b004c024011008003c018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xbf652ca9252588ff462a23901c7da3de9ea8f2277f3b69948c80538289139497445621710588103f61f48f7467432417a8b2055e27812f894847221210007d03ce1d50da86702f215609204602100fb075829412208204081b80da063030017c0ba05c02b01540a804a02480d806a02b014009c04a02400f007403801b00b004c024011008003c018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x36b94baa224ab20b4ff07d83e39ed0f4e79529493b88442f91620a9052628013989844102010f5075430417b0b7059c29614409e04d825e12708584141fc0f707803a01720a4048820810207203781b80d606802f81780ba05602a815009404901d00dc06c033018009c04c02500f007403801b00b004c024011008003c014009004001c00c0050018008002000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x2fd53d89bc49f2034fb27bf3d51e3cefe76d2f516f4a9045421610608103f41f48f7467432417a8b204462120fa079c35019c0c786142f216c098049023010907d83a816a0a4048820810207203781b80d606802f81780ba05602a815009404901d00dc06c033018009c04c02500f007403801b00b004c024011008003c014009004001c00c0050018008002000 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record006_frame002_links_0000 record006_frame002_links_0064)
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x78a6f76a86706495ed5b558357954d54553e53653152952251c4a444d44143840e3e438037435734130c2df2d82d02c92bd2b62b02ab1dd1d31c81bc1a719718517917015f15814812e12711710c0f90f00e60d80cd0c40c109808e08207c06f06b05f05b05805505404a04403f03703503303002702602302102001d01c01601301200f00e00b00a008007005003002001000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xb9856ba96d4449564a224311c8898443a034ff07e83ec1f20f687a63ca9990b4652727710888203d81d80d906a62d91620ad054829414009c84c220d10407e83aa1ce0e406ec3481980c486082f816d0b3852c28813c09b04bc24e11308583f81ee0e807102080f806f03581a00be05e02d81600aa054025011006e033018009c04c023010007403801b00b004c024011007803801600a004001c00c0050018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0591.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0591.count (({ width := 11, code := 0x3e078cec1d13766e2d81a9b3a66ac35822fe5f2bd1772e85c4acd4aa7e4e291d222354588650b9f63e07b0f51e63c0774ed19632261cb49642c055ca093b25c4ac9391b22c3e4798eb1cc37c6b0c517e2d0570a11341d0388690ca1882d85a0ae1502885008c1041b83306009c130230400740e01b02c04c0901101e0380580a01001c0300500600800800 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0591
    Papers.RationalityTen.SharedFrameCatalogue.group0591_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0590.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0590.count (({ width := 11, code := 0x3b672cdedb6b42680cd99631962abd576ae95cab816dad55a0a7d422694b68c116a1e428800fe9e23b475ce89cd392708df1863025e4ac95329a5149812b236454881041fa39c710dd1b4350670c11782c0558a01341b8358620bc16c2a0530a0134250490820f41a83105c09c130230400740e01b02c04c0901101e0380580a01001c0300500600800800 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0590
    Papers.RationalityTen.SharedFrameCatalogue.group0590_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x7276ea67f65e6125a75775074fe4b74b04a649e49940d3b73aa35c32a3012f12e92d32b229f29327b27121e1ec1cc1a519d1951691611551461331040fd0f60f00eb0e50de0d70bf0ba0b50a509c08e08c08207407306806605805705605204a04404104003f03a03303203002802402202102001f01c01b01200e00d00c00b009007006005002001000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x6e66a765c6465f55795544b84b246e46745e4584523aa3483422fb2b829328728126c25925024a23c2361ed1b319817617216c15715414a13d1331020fe0f80f50f20e80db0d50c10bf0bd0af0a609809608a07607506806605805705605204804203f03e03d03803203102f02802402202102001f01c01b01200e00d00c00b009007006005002001000 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0932.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0932.count (({ width := 7, code := 0xcf9b263c37eedab356a53a54684f9d3664b95264478b121c28301fbe7af1d3970ddb3466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0932.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0932.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0932.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0932.localPairCheck (smallEmbedding record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record009_frame003_links_0000 record009_frame003_links_0064)
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0932
    Papers.RationalityTen.SharedFrameCatalogue.group0932_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
def record009_frame004_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0955.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0955.count (({ width := 7, code := 0xcf9b263c37eedab356a53a54684f9d3664b95264478b121c28301fbe7af1d3970ddb3466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record009_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0955.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0955.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0955.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record009_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0955.localPairCheck (smallEmbedding record009) (record009.maps 4)
      (record009.inverseMaps 4) record009_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record009_frame004_links_0000 record009_frame004_links_0064)
theorem record009_frame004_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 4 :=
  of_group record009 4 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0955
    Papers.RationalityTen.SharedFrameCatalogue.group0955_facts record009_frame004_indices record009_frame004_graph record009_frame004_links
def record009_frame005_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb15acda49a1b99b8ff8c07b97a56ed6db6c26b26a15dd56c55e5004b947d46d4604324023e63d83b53a73372e42bb2752672572182091fa1e61cc17316515314513712b11910a0d80cd0c00a60a109609408807607506806605805705605204a04404104003f03a03303203002802402202102001f01c01b01200e00d00c00b009007006005002001000 } : Fields).get c.val)
theorem record009_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record009_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 5)
      (record009.inverseMaps 5) record009_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record009_frame005_links_0000 record009_frame005_links_0064)
theorem record009_frame005_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 5 :=
  of_group record009 5 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record009_frame005_indices record009_frame005_graph record009_frame005_links
def record009_frame006_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0516.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0516.count (({ width := 7, code := 0xb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record009_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0516.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0516.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0516.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record009_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0516.localPairCheck (smallEmbedding record009) (record009.maps 6)
      (record009.inverseMaps 6) record009_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record009_frame006_links_0000 record009_frame006_links_0064)
theorem record009_frame006_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 6 :=
  of_group record009 6 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0516
    Papers.RationalityTen.SharedFrameCatalogue.group0516_facts record009_frame006_indices record009_frame006_graph record009_frame006_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (Fin.cases (record009_frame004_supported hcells) (Fin.cases (record009_frame005_supported hcells) (Fin.cases (record009_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x16c2ab052828ed2f091347b21850a283e41820850227fe3f81f9ce2a66a30497e0aa64fe27491d08d045a228111487242b21090685ec2f01670ae44ee26812d88f445c22110187e836e1a40c8860c2ee16b0a9051827412607c03a413408203e01dc0de06b034017c0b605902c01540a804a02200fc06e033018009c046021010007403801b00b004c02400f007003001600a004001c00c0050018008002000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
def record010_frame002_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x99c9449018d484d7f47a673b7277106ff6ed6db6c56b46a26375de59a56e5014ba47e4254154013f43e63d83c43b73a82bc2aa2962862582492392192091fa1da1cd1a019118217316515513712b11b0fe0da0ce09407e07a07506d06906605d05905705605305204a04403f03703303002702302102001d01c01b01601301200f00e00c00b00a008007006005003002001000 } : Fields).get c.val)
theorem record010_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record010_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record010) (record010.maps 2)
      (record010.inverseMaps 2) record010_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record010_frame002_links_0000 record010_frame002_links_0064)
theorem record010_frame002_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 2 :=
  of_group record010 2 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record010_frame002_indices record010_frame002_graph record010_frame002_links
def record010_frame003_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x6f76a86706495ed5b558355454d54553e53853152952251c4a444d40e3e438034130c2df2d82d02c92c42bd2b62b02ab1dd1d31c31bc1a71a119718517c17015f15813512e12712111710c0fc0f00e60d80c40c109808207c07706f06b06805f05b05905805505404a04403f03703303002702302102001d01c01b01601301200f00e00c00b00a008007006005003002001000 } : Fields).get c.val)
theorem record010_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record010_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record010) (record010.maps 3)
      (record010.inverseMaps 3) record010_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record010_frame003_links_0000 record010_frame003_links_0064)
theorem record010_frame003_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 3 :=
  of_group record010 3 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record010_frame003_indices record010_frame003_graph record010_frame003_links
def record010_frame004_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x229c2780efe1dfba471cdb5b33616b4d51a6b46682cf1752b7522a051f22041679cf09db3aa73ce49c137a6e0a69482804ec9512824646c8b11020a408770e91c637c6c8d3196318608bb15c2a8440770e41b4338640c21682b8550a8144280470840f41b03205e09c118210400740e01b02c04c0900f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record010_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record010_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record010) (record010.maps 4)
      (record010.inverseMaps 4) record010_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record010_frame004_links_0000 record010_frame004_links_0064)
theorem record010_frame004_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 4 :=
  of_group record010 4 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record010_frame004_indices record010_frame004_graph record010_frame004_links
def record010_frame005_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1730ad752da8892ac8e444c207d01a7f83f41f64f907b43d31e54cc85a329393b88443b01b20bac5b22c415a0a9452828013909843aa1ce0e106ec34819f0cc062430617c0b6859c29614409e04d825e12708d044c2160fe074038813408203e01dc0de06b034017c0b605902c01540a804a02200fc06e033018009c046021010007403801b00b004c02400f007003001600a004001c00c0050018008002000 } : Fields).get c.val)
theorem record010_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record010_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 5)
      (record010.inverseMaps 5) record010_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record010_frame005_links_0000 record010_frame005_links_0064)
theorem record010_frame005_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 5 :=
  of_group record010 5 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record010_frame005_indices record010_frame005_graph record010_frame005_links
def record010_frame006_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x5e65a55735554f84c849c45944a43942f42641940d4063fb3ad36c33a31c2bf28f26321e2112001f61ea1e11d41cd1c215f15b15414f13b13813212812511f1121101000fb0f50f00ea0e40da0d40ce0c50b40b108a07807406f06806406105805405205104e04d04704303e03703303002702302102001d01c01b01601301200f00e00c00b00a008007006005003002001000 } : Fields).get c.val)
theorem record010_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record010_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 6)
      (record010.inverseMaps 6) record010_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record010_frame006_links_0000 record010_frame006_links_0064)
theorem record010_frame006_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 6 :=
  of_group record010 6 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record010_frame006_indices record010_frame006_graph record010_frame006_links
def record010_frame007_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x240c52855081f3bbf756e05bc3726d8d95aeb53698d1987ad9570ab934a4d472831021fc3ea7b4f49e03b4750b31632ba55ca31422744b0931202224347e8f71e03a8710db19c320600b6150290430740e21b0330620be15c298510a0134260450820f01a83205e098118210400740e01b02c04c0900f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record010_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record010_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record010) (record010.maps 7)
      (record010.inverseMaps 7) record010_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record010_frame007_links_0000 record010_frame007_links_0064)
theorem record010_frame007_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 7 :=
  of_group record010 7 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record010_frame007_indices record010_frame007_graph record010_frame007_links
def record010_frame008_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1000.count (({ width := 11, code := 0x22dc2c820ff5dfb9e6f8d4da5b43676cd998b2b64ac7976ab852e9f92222841a794ee9d439a720e19bc36c6c0ae15729a5209c9362604848e118218418790ed1cc38c6e8d51923145f0b314e2844106e0d41943005c0b21502804e09a1282484107a0e01a03005a09c118210400740e01b02c04c0900f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record010_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record010) (record010.maps 8) (record010.inverseMaps 8) record010_frame008_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record010) (record010.maps 8) (record010.inverseMaps 8) record010_frame008_indices (Fin.ofNat record010.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record010_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record010) (record010.maps 8)
      (record010.inverseMaps 8) record010_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record010_frame008_links_0000 record010_frame008_links_0064)
theorem record010_frame008_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 8 :=
  of_group record010 8 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1000
    Papers.RationalityTen.SharedFrameCatalogue.group1000_facts record010_frame008_indices record010_frame008_graph record010_frame008_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (Fin.cases (record010_frame002_supported hcells) (Fin.cases (record010_frame003_supported hcells) (Fin.cases (record010_frame004_supported hcells) (Fin.cases (record010_frame005_supported hcells) (Fin.cases (record010_frame006_supported hcells) (Fin.cases (record010_frame007_supported hcells) (Fin.cases (record010_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xda95a22529286914486a4151fc8f8478a3a51c48dc3e5137c99e45522190c48444122010fc07c03d113809803cc1d40e106cc3461930c085c42c414f0a4050427412c09284402140f6071837414a09f04d02080f8077034018c0c005f02e016c0b205802a815009404401f80c00560280138090046021010007403801b00b004c02400f0070030016008003801800a0040018008002000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xe895cc22ad13081f4069fe8fd07d93e41ed8f4c7953320ddc6c82eb16c8b185682a514a0a084e42610ea873833e1980c8062430617c0ba05b42ce1590a9052c28813609784682260fe074838814a09f04d02080f8077034018c0c005f02e016c0b205802a815009404401f80c00560280138090046021010007403801b00b004c02400f0070030016008003801800a0040018008002000 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame002_links_0000 record011_frame002_links_0064)
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x3725ce9152122f4588a112a234408710ca173e6544a713b2704d09892f2584a0929231d0394690cf196320630c317e2f05d0b616a2d0598b11602b4560a914c2944b89211a1e83a8700c41742d0590ac1542985209e1382404307c0c01582804e090118210400740e01b02c04c0900f01c0300580800e0180280400600800800 } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame003_links_0000 record011_frame003_links_0064)
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
def record011_frame004_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x3a86169852f24b49091120a3f4788e11aa3340a56cac1452844f89d93926c4c89792d1e43bc6e0d91aa348680cd192318620c017e2f85e8bb1742dc5b0b31602bc5089b12c2003d0750cc1842f05d0b41642b8560a61482504407e0c01582804e090118210400740e01b02c04c0900f01c0300580800e0180280400600800800 } : Fields).get c.val)
theorem record011_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record011) (record011.maps 4)
      (record011.inverseMaps 4) record011_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame004_links_0000 record011_frame004_links_0064)
theorem record011_frame004_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 4 :=
  of_group record011 4 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record011_frame004_indices record011_frame004_graph record011_frame004_links
def record011_frame005_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xd305b0a3f51ec861428a101060821408a000fe07e738a93b89d247423411708a044521c90b484241a17b0bc04d025b12608f445c221109080c3f41db0e406dc3481830bb854828c12607c83a414a09f04d02080f8077034018c0c005f02e016c0b205802a815009404401f80c00560280138090046021010007403801b00b004c02400f0070030016008003801800a0040018008002000 } : Fields).get c.val)
theorem record011_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 5)
      (record011.inverseMaps 5) record011_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame005_links_0000 record011_frame005_links_0064)
theorem record011_frame005_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 5 :=
  of_group record011 5 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record011_frame005_indices record011_frame005_graph record011_frame005_links
def record011_frame006_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc9e58923a11a485f424a0cd03c8093fa1f74f8e7b139214d0a4c4c4258928492648423891808a24421938c5455029414009b84b624911a888c4201ee0f007443861ab0cc05982a212107a039c14a09f04d02080f8077034018c0c005f02e016c0b205802a815009404401f80c00560280138090046021010007403801b00b004c02400f0070030016008003801800a0040018008002000 } : Fields).get c.val)
theorem record011_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 6)
      (record011.inverseMaps 6) record011_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame006_links_0000 record011_frame006_links_0064)
theorem record011_frame006_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 6 :=
  of_group record011 6 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record011_frame006_indices record011_frame006_graph record011_frame006_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (Fin.cases (record011_frame004_supported hcells) (Fin.cases (record011_frame005_supported hcells) (Fin.cases (record011_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x2cbcf08eb15620c3b7f0f5de8b646beb59672be558a954b28d50ea05392594828d50ca113b674cdd9b134666cc918c2fe5c0ab9462624788b0e11b6354680c0176298418810d41a02e85a0aa1502885009e11c1f83a06e0ac140260460881081f03c0740b0130200380680b0140240400400600800800 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x17eea5a49fa4b11b68c6452223d10a7d23be9dacca654929c13d09cc4c925d92c884c3e71ed8d8462a30617b0ba05b22c915f8abc53a27812908c44441f20f2875436a19c0bc85902ac13108403ec19009504902040e406f03181800ba05b02d015c0ac05502480e806e02b014009404602200f807803a01b00b004c022010007003401800a004802000a0040018008002000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1b64ad952f288d4209574a09fa4f467912d294a89de4dc211903456a26f12e88503f41f30f587943bc1d60e8062830417b0ba85642a414b0a204d825e12108c04442060fc07b83c01a809504902040e406f03501a40d0063030015c0ac05502480e806e03201880c005602800f807803a01b00b004c0220100070034014009004001c00c005002000c004000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x17eea5a4f6a6f536893f4959f48ef876a32997acb7c5b52a494d884c3e61ed0d8462a30617b0ba05b22c915f88c4446212100871836a1a80ce06142f21640aa850824411608483ec18e09504902040e406f03501a40d0063030015c0ac05502480e806e03201880c005602800f807803a01b00b004c0220100070034014009004001c00c005002000c004000 } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record014_frame002_links_0000 record014_frame002_links_0064)
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xb9b56ca96943e94448623911a88aa44d221d08482d4069fe0fd27a53c9999cb4a52627590407b03b01d00dd86cc3531870be45b22c415a89c44be21410688203f41e50e807203761ad0cc06282e616c0b2852c28813c09b04bc24e121089842c1ee0e806a81f00f207203781a00bc05b02d01600ac05502201040740370180098046022010007803a01b00b004c02200f007003401600a004802000c0050018008002000 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
def record016_frame002_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xabe52d27a937492d476231116a88d442a1d104080d3f61f64fa477d3b59b00ca65e72dd14e4a044e426b92e49644a4232115087842c2130f9c7b63611a70ce862a2e815f8ac051426d12388c43fe1f20f286a033818f0c285e42d81640a204c02120ea06401f00f207203781a00bc05b02d01600ac05502201040740370180098046022010007803a01b00b004c02200f007003401600a004802000c0050018008002000 } : Fields).get c.val)
theorem record016_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record016_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record016) (record016.maps 2)
      (record016.inverseMaps 2) record016_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record016_frame002_links_0000 record016_frame002_links_0064)
theorem record016_frame002_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 2 :=
  of_group record016 2 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record016_frame002_indices record016_frame002_graph record016_frame002_links
def record016_frame003_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x5f4b7b68ecbd40a4d43e824eb9bf35259ca39231fe39c598a5021e83b5752d4d9f32763cc2580af75b6b2d5e2ad54aa4145a3645e8a10d9fd3be75ce59bc33c61cbb16f2d251c9e13024a468858fd1d438c630b71361b0350650c61782a0510a01382604b07e0f41b835060098118220400780e81b02c04c0880f01c0340580a0120200300500600800800 } : Fields).get c.val)
theorem record016_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record016) (record016.maps 3) (record016.inverseMaps 3) record016_frame003_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record016) (record016.maps 3) (record016.inverseMaps 3) record016_frame003_indices (Fin.ofNat record016.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record016_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record016) (record016.maps 3)
      (record016.inverseMaps 3) record016_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record016_frame003_links_0000 record016_frame003_links_0064)
theorem record016_frame003_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 3 :=
  of_group record016 3 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record016_frame003_indices record016_frame003_graph record016_frame003_links
def record016_frame004_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x3f8796ecdd3b706c8d55a7b3f674cc98e31360abe97aae05baaa94126a4bc8990b2073fe7b8f49e23a271cdd9b135865cca1652c2574aa1452684bc9391d21a4087a8f31e237c6d8d71a432c618bf16c2c05309b1241b0350640c216c2904f09c1302504907c0ec1b83505e098118220400780e81b02c04c0880f01c0340580a0120200300500600800800 } : Fields).get c.val)
theorem record016_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record016) (record016.maps 4) (record016.inverseMaps 4) record016_frame004_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record016) (record016.maps 4) (record016.inverseMaps 4) record016_frame004_indices (Fin.ofNat record016.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record016_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record016) (record016.maps 4)
      (record016.inverseMaps 4) record016_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record016_frame004_links_0000 record016_frame004_links_0064)
theorem record016_frame004_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 4 :=
  of_group record016 4 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record016_frame004_indices record016_frame004_graph record016_frame004_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (Fin.cases (record016_frame002_supported hcells) (Fin.cases (record016_frame003_supported hcells) (Fin.cases (record016_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x55f27ad3769b449fa30d1188744102038fd87da3e91df0ed46c02f496f0b6a54927112dc94846422b10f085c4261f30f686c234e19d0c545d02bf15809b44be24711c88c4446213100071836a1a80ce06142f21640aa84bc24411608483ac18e07c03c81a80d206803181800b005602a811008203201880c0056028010007803a01b00b004c02200f0070034016009004001c00c005002000c004000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x2c8155ea7753326d128690b47d232916a8924459b54d84691338997cc706282c015b4a7851c285138c9a64c6252123c90246f2348e446302d91638ad853227a12608b443420e100074c36c1970b4852826e12b08e83c01d20e206d83500e406f03501a40c606002d816807e03a01b80d406403101800ac050026011808802c013007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x5da5b05a259e54c51c50b5074fc4c84a547146a3e03b33a63a235f33732c32a3212eb2d22ad2a824d21b20a2061ed1dd1d11c11b01a619118917f17414c14213712d11f1161060ff0f60ee0d40c70bc0b00a80a006f06c06906406306205d05a05505403f03a03703203103002b02802302201b01601300e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
def record019_frame002_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0944.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0944.count (({ width := 8, code := 0xc0bfbebdbbb9b7b5b4aaa49a989492908e8d8c8b8a897f796f6d6b6a69686563615f5c5a575553514c4a484643413e3c3a383432302e2c2a24232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record019_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0944.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0944.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0944.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record019_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0944.localPairCheck (smallEmbedding record019) (record019.maps 2)
      (record019.inverseMaps 2) record019_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record019_frame002_links_0000 record019_frame002_links_0064)
theorem record019_frame002_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 2 :=
  of_group record019 2 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0944
    Papers.RationalityTen.SharedFrameCatalogue.group0944_facts record019_frame002_indices record019_frame002_graph record019_frame002_links
def record019_frame003_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0895.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0895.count (({ width := 8, code := 0xc0bfbebdbbb9b7b5b4aaa49a989492908e8d8c8b8a897f796f6d6b6a69686563615f5c5a575553514c4a484643413e3c3a383432302e2c2a24232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record019_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0895.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0895.localPairCheck (smallEmbedding record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0895.localPairCheck (smallEmbedding record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record019_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0895.localPairCheck (smallEmbedding record019) (record019.maps 3)
      (record019.inverseMaps 3) record019_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record019_frame003_links_0000 record019_frame003_links_0064)
theorem record019_frame003_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 3 :=
  of_group record019 3 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0895
    Papers.RationalityTen.SharedFrameCatalogue.group0895_facts record019_frame003_indices record019_frame003_graph record019_frame003_links
def record019_frame004_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xb20557a9dd4cc9b44a1a42d1f48ed46522d512488b36a99c4c706282c014709c64d3263129091e46f2348e446302d91638aa453228a13d096c49822d10e88384001c60db069c32e1780b4852827412b08e83dc1e00e9071036c1a807703901bc0d4069034018c0c005b02d00fc07403701900c406002b014008c04401b00b004c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record019_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record019) (record019.maps 4) (record019.inverseMaps 4) record019_frame004_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record019) (record019.maps 4) (record019.inverseMaps 4) record019_frame004_indices (Fin.ofNat record019.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record019_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record019) (record019.maps 4)
      (record019.inverseMaps 4) record019_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record019_frame004_links_0000 record019_frame004_links_0064)
theorem record019_frame004_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 4 :=
  of_group record019 4 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record019_frame004_indices record019_frame004_graph record019_frame004_links
def record019_frame005_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xad952f288d42095747322b11348834159fd8f447902d294a89de4dc2118ec86f03661a78bdc58426e12e08503d61d60e807083761b40d6867c33018a0c185f02ea1590a9052c288136097848423411308603d41dc0e707003641a607703901bc0d4069034018c0c005b02d00fc07403701900c406002b014008c04401b00b004c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record019_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 5) (record019.inverseMaps 5) record019_frame005_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 5) (record019.inverseMaps 5) record019_frame005_indices (Fin.ofNat record019.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record019_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 5)
      (record019.inverseMaps 5) record019_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record019_frame005_links_0000 record019_frame005_links_0064)
theorem record019_frame005_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 5 :=
  of_group record019 5 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record019_frame005_indices record019_frame005_graph record019_frame005_links
def record019_frame006_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x7216e36bb6af62b5e55b55a559656d55452b5244313eb3bb3ab3332f52cd2c12b328a2712482411fe1d71c21bd1b01a81a119918818117116916215b13e13612f12711610f0ff0f70f00e90d40d00cc0c80c40c007707206f06a06906806306005b05a03f03a03703203103002b02802302201b01601300e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record019_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record019) (record019.maps 6) (record019.inverseMaps 6) record019_frame006_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record019) (record019.maps 6) (record019.inverseMaps 6) record019_frame006_indices (Fin.ofNat record019.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record019_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record019) (record019.maps 6)
      (record019.inverseMaps 6) record019_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record019_frame006_links_0000 record019_frame006_links_0064)
theorem record019_frame006_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 6 :=
  of_group record019 6 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record019_frame006_indices record019_frame006_graph record019_frame006_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (Fin.cases (record019_frame002_supported hcells) (Fin.cases (record019_frame003_supported hcells) (Fin.cases (record019_frame004_supported hcells) (Fin.cases (record019_frame005_supported hcells) (Fin.cases (record019_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0xb21596a64e99712963b4548850ea09bed7c8f79ecb2e646c3d6bace590aad52a97518a1d392614b28ad11a1b3b874ce49b0346670c898c2e0598ab939250480738db1aa32c600bb16c25c4007f0f619c328620ba1642b0540a013c2704707e0d81a8340620ac138260480881081e03a0700b01202003c0680b0120200380400600800800 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6d9b3255b4ac1526a83d2b0943460a264ff67d63e39edcf4e5a62c694649b64242078e346ca2c71510a4c50627310a87943bc1cf0e3870836819f0c885ec2ea16e0af854828812f094046421810507b03c012a09104602040e406e03681a40c605f02e81680ae05602a815009203a01b00d406202b013809404401f00f007403801b00b00480220100068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
def record021_frame002_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x6716495db5d259f57d53c5334f84de4a949b49549048a4003f83ca3a435d35531f3012cd2c02bb2b72b324f2081fb1e31da1d51c41a419117216815f14a13e12c10c1010ec0d80cf0bc0b808708508207b06f06b06a06606105d05b05805505405305204703903503403002b02702502201f01e01d01c01b01601201101000d00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record021_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record021_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record021) (record021.maps 2)
      (record021.inverseMaps 2) record021_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record021_frame002_links_0000 record021_frame002_links_0064)
theorem record021_frame002_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 2 :=
  of_group record021 2 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record021_frame002_indices record021_frame002_graph record021_frame002_links
def record021_frame003_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x97b25226c48857049edbd5746e3da934467cce99b2e25b8ad14b2664c28f1159ef3c076ceb9d334c614bf9772e45b0b014c27a49c9091c21c4087a8e01b23285e8b81542904187f0f41d4340640c61802d0560a81442704d09812c230380680cc1782a04c0941101f03c0740e01b02c0480881001a0300500901001c0280400600800800 } : Fields).get c.val)
theorem record021_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record021_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record021) (record021.maps 3)
      (record021.inverseMaps 3) record021_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record021_frame003_links_0000 record021_frame003_links_0064)
theorem record021_frame003_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 3 :=
  of_group record021 3 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record021_frame003_indices record021_frame003_graph record021_frame003_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (Fin.cases (record021_frame002_supported hcells) (Fin.cases (record021_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xcfe61daa653ac98a4ad254d28890647ba3c11d48e33861900b0a50527a13408644112008fc47c231614b0a144c21c30d106483041720a7852028213a096049423c10407e83bc1d20a404a824411808103901b80d2068031817c0bc05d02d015c0ac05502a012407403601880c0056027013009404401f00f007403801b00b00480220100068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
def record022_frame002_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xdb3664ab6941e95846a23051327fb3ec1f1cf6e7a72d3136c8483a01c68d9458e2a41498a0c4e62150f2877839e1910c105ec2ea16e0ac854829614409b04bc25010c08283dc1e00a404a824411808103901b80d2068031817c0bc05d02d015c0ac05502a012407403601880c0056027013009404401f00f007403801b00b00480220100068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record022_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record022_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 2)
      (record022.inverseMaps 2) record022_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record022_frame002_links_0000 record022_frame002_links_0064)
theorem record022_frame002_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 2 :=
  of_group record022 2 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record022_frame002_indices record022_frame002_graph record022_frame002_links
def record022_frame003_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x34661aaed4126149a92921a2944487d0ea1a38e638b69592ac53c9a92e2564a4931041e03b4730cc18a308600bd16c2d45a0b31622c0578ab1542a053896112214400790d81a0318620ba1642c0570a81442804f09c11c1d0360620c01582704c0941101f03c0740e01b02c0480881001a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record022_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record022_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record022) (record022.maps 3)
      (record022.inverseMaps 3) record022_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record022_frame003_links_0000 record022_frame003_links_0064)
theorem record022_frame003_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 3 :=
  of_group record022 3 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record022_frame003_indices record022_frame003_graph record022_frame003_links
def record022_frame004_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x37b676b794f27d4d29992fa4547c8ed1ca363b0660bb9632c05649f93826a4cc9810e1f43dc780d619e330650c71802fc5f0bd1762e85c8b51682c8588a01222344407f0e01b0338660c21742e05b0b01542a0530a41241d0360620c01582704c0941101f03c0740e01b02c0480881001a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record022_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record022) (record022.maps 4) (record022.inverseMaps 4) record022_frame004_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record022) (record022.maps 4) (record022.inverseMaps 4) record022_frame004_indices (Fin.ofNat record022.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record022_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record022) (record022.maps 4)
      (record022.inverseMaps 4) record022_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record022_frame004_links_0000 record022_frame004_links_0064)
theorem record022_frame004_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 4 :=
  of_group record022 4 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record022_frame004_indices record022_frame004_graph record022_frame004_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (Fin.cases (record022_frame002_supported hcells) (Fin.cases (record022_frame003_supported hcells) (Fin.cases (record022_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x18769d64c526092fa95f4ad253128893d491246921a8f7478a3a51c66402c295c8ac251628293849a04bd23b91988864112010fc07c23161818bc854e296139098449c2080fb87503441930c085c829e1480a084e825812508f04281fa0ef071824411806e03481a00c605f02f01700b405802b01540a803601880c0056027013009004402000f007403801b00b004802200f006802c012008003801800a0040018008002000 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
def record023_frame002_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1992a0f4ac25112648e546a22b513288742120bd01a7d83e41ed8f4e4db21210407fc3b11d00de46ca3531870bec5b22a414a0a084e621510688203d41e50eb873c3901ad0d2866030417c0ba05b82b21520a5851026c12f094044c20a0f7074824411806e03481a00c605f02f01700b405802b01540a803601880c0056027013009004402000f007403801b00b004802200f006802c012008003801800a0040018008002000 } : Fields).get c.val)
theorem record023_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record023_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 2)
      (record023.inverseMaps 2) record023_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record023_frame002_links_0000 record023_frame002_links_0064)
theorem record023_frame002_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 2 :=
  of_group record023 2 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record023_frame002_indices record023_frame002_graph record023_frame002_links
def record023_frame003_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x19da9e4fa9e53c26a4d298d2fa5c4a29352423e4788e11b1982ee5ccb91642c6574ac95629651ca113826c4c89810e2144247d8fa1e83c0768e21bc364678cd19231c600bf17c2f45d8ba1722d85a0b21602344406c0ce1983085d0b81682c0560a814c290360620c01582704c0901102003c0740e01b02c0480880f01a02c0480800e0180280400600800800 } : Fields).get c.val)
theorem record023_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record023_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record023) (record023.maps 3)
      (record023.inverseMaps 3) record023_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record023_frame003_links_0000 record023_frame003_links_0064)
theorem record023_frame003_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 3 :=
  of_group record023 3 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record023_frame003_indices record023_frame003_graph record023_frame003_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (Fin.cases (record023_frame002_supported hcells) (Fin.cases (record023_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x331d586a4d506a5611cc88543220b901a7fb3f41f58f907b73d3163ca324d92120ec86a233017d0b6458e2b41510a5050627210a88343f41eb0f287083761a40cf86603221890be05d42da15f0a9051025e12808c844c2180f6071026c11807803b81b40d206302f816c0b405802b81540a804001f80d406202b013808c04402000f807403801b00b004802200e006803001600a004001c00a0040018008002000 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x30e53a898a4b024dd26091948a243520c8fe47c23c51d48e231f1614a2e4ac24d11948aa44321910888244021f88f8062c2a811e88ac3ec1e60ea070c3661a30c986082e214f0a4050427412c092847822010a082037413609a04601e00ee069034018c0be05b02d01640b005702a815008003f01880c0056027011808804202000f807403801b00b004801c00d006002c014008003801800a0040018008002000 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
def record025_frame002_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x331d41a95847321d90c882e40fa034ff67e83ec9f20f6e7a626c90907643421980be85d62d91638ad054a29414189c842a1eb0e106ec34819f0cc06443121830be05d42da1590a9052c28813609784a0234113086038813609a04601e00ee069034018c0be05b02d01640b005702a815008003f01880c0056027011808804202000f807403801b00b004801c00d006002c014008003801800a0040018008002000 } : Fields).get c.val)
theorem record025_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record025_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 2)
      (record025.inverseMaps 2) record025_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record025_frame002_links_0000 record025_frame002_links_0064)
theorem record025_frame002_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 2 :=
  of_group record025 2 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record025_frame002_indices record025_frame002_graph record025_frame002_links
def record025_frame003_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0xc2d4026149e8f91da3045e8b114a254468810ea193185b4ad94a28e4f09d93826a4c49792c252494820f21c2378698d219e330640c61863005e0b616a2d0598b11602bc568ac1562944708d1001c4380630c41742c8550a814c2905109e1381f83e0620c0158270460881082003e0740e01b02c0480700d01802c0500800e0180280400600800800 } : Fields).get c.val)
theorem record025_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record025) (record025.maps 3) (record025.inverseMaps 3) record025_frame003_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record025) (record025.maps 3) (record025.inverseMaps 3) record025_frame003_indices (Fin.ofNat record025.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record025_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record025) (record025.maps 3)
      (record025.inverseMaps 3) record025_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record025_frame003_links_0000 record025_frame003_links_0064)
theorem record025_frame003_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 3 :=
  of_group record025 3 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record025_frame003_indices record025_frame003_graph record025_frame003_links
def record025_frame004_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xce54e27d4d69692ba4c49692122a4147e8f11ca3532c5dcb29542a2518a294227e4ec9c9362664bc870fc1d63a06e8dc1b2358690d019a328630c017e2f85e8bb1742e45b8b616a2bc4b8961101d83a8670cc1842e8590b015c2b0550a61482003f0620c0158270460881082003e0740e01b02c0480700d01802c0500800e0180280400600800800 } : Fields).get c.val)
theorem record025_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record025) (record025.maps 4) (record025.inverseMaps 4) record025_frame004_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record025) (record025.maps 4) (record025.inverseMaps 4) record025_frame004_indices (Fin.ofNat record025.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record025_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record025) (record025.maps 4)
      (record025.inverseMaps 4) record025_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record025_frame004_links_0000 record025_frame004_links_0064)
theorem record025_frame004_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 4 :=
  of_group record025 4 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record025_frame004_indices record025_frame004_graph record025_frame004_links
def record025_frame005_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x301146697a48aa33916e872430a145082830410a0450027f02f89554a004cb25c12008e846822e914088a43921710846dc30e1670ae44ee26812d893447a22e110884c4061db0e406dc3481830bb85b02a414609d83a413609a04601e00ee069034018c0be05b02d01640b005702a815008003f01880c0056027011808804202000f807403801b00b004801c00d006002c014008003801800a0040018008002000 } : Fields).get c.val)
theorem record025_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record025) (record025.maps 5) (record025.inverseMaps 5) record025_frame005_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record025) (record025.maps 5) (record025.inverseMaps 5) record025_frame005_indices (Fin.ofNat record025.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record025_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record025) (record025.maps 5)
      (record025.inverseMaps 5) record025_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record025_frame005_links_0000 record025_frame005_links_0064)
theorem record025_frame005_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 5 :=
  of_group record025 5 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record025_frame005_indices record025_frame005_graph record025_frame005_links
def record025_frame006_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x6d05b95625294f94ef4d14c94c34ba4b14a849f49448936930b2d82a929f28127826f26425925024a2412381e61b519819117b17516d16415a15214a14113712912311e11910c1060ff0f20ec0e50c309b09a08c07807706906806305f05b05a05905805705505404003f03103002b02702302202102001f01d01c01b01601200e00d00c00b00a008007006005004003002001000 } : Fields).get c.val)
theorem record025_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record025) (record025.maps 6) (record025.inverseMaps 6) record025_frame006_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record025) (record025.maps 6) (record025.inverseMaps 6) record025_frame006_indices (Fin.ofNat record025.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record025_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record025) (record025.maps 6)
      (record025.inverseMaps 6) record025_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record025_frame006_links_0000 record025_frame006_links_0064)
theorem record025_frame006_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 6 :=
  of_group record025 6 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record025_frame006_indices record025_frame006_graph record025_frame006_links
def record025_frame007_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa098c184f7f679078074e73b7277136ff6ed6db6c86b455f5034bc46d4604344254154043f43e63d83c73b73392e62962862582492392282192091fa1e91da1ba1ae1a019117316515613712b11c0ce09509408607607506706606105d05905805705605505305204003f03103002b02702302202102001f01d01c01b01601200e00d00c00b00a008007006005004003002001000 } : Fields).get c.val)
theorem record025_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record025) (record025.maps 7) (record025.inverseMaps 7) record025_frame007_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record025) (record025.maps 7) (record025.inverseMaps 7) record025_frame007_indices (Fin.ofNat record025.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record025_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record025) (record025.maps 7)
      (record025.inverseMaps 7) record025_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record025_frame007_links_0000 record025_frame007_links_0064)
theorem record025_frame007_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 7 :=
  of_group record025 7 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record025_frame007_indices record025_frame007_graph record025_frame007_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (Fin.cases (record025_frame002_supported hcells) (Fin.cases (record025_frame003_supported hcells) (Fin.cases (record025_frame004_supported hcells) (Fin.cases (record025_frame005_supported hcells) (Fin.cases (record025_frame006_supported hcells) (Fin.cases (record025_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
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
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x6e25ee5ad59759057b57450f4b94a548e4823b139d38637a34833d33732832131b30d3063002c82bb29e28227026324622a22221520e1c61bb1b118517c1301121091020f80d50c60c206f06e05c05b05705604f04903803703602502402302001f01e01501301201100f00e00a009008004003001000 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 79 :=
  interval_of_check _ 64 15 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 79 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x49622790f68713ee1f18eb074d39b9c94ddc6d535d9ac8c546192b294c8a484f926d934895a49e248117c8a03fc1d58e6c6f63621a70c946263051718b0857029013e89ac4682220fe07803861b90b2854419205c02d81600ae056027810c08204001c00dc06c024011808003e01e00d804401e00e0058028012005002000c002000 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xc8d514268132498b4b0a52928691b48223f4dc86c034b1780b805992c314609be4cf23390c084240f1b88d4465431715489c04c01f80e086c834014809d04cc2140f6074835c11c08d03581a80c206002f81700b605702b015009e03501980c8052028013809004601f00f0070028013009003c01c00a004801c00a0040018008002000 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xab04a222651247243839b9cdae67231b9898b9e5b22c91608a3a4e2268925891e48823a91bc7fc37d1b50d046322b814c89e84d624811c08a443820e0ea86d832e1880b2855428c13909583c01d20e206a01ac0d405c02d813c07003701b00cc064029014009c04802300d804401e00e00580280120070028010006001 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x24bc237c0ef9d339d6f4d89acaca544a7546a7d4ec9b130a5c4989090e2053f27d0e49bf358690c01692ba540a313e2644a48f9151c83746b0c81642a84c0770ec188308570ac14c2904e09a12c240310600a41382604a08c1101e03a06c0a01302403c0700b0140240380400600800800 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record032_frame001_links_0000 record032_frame001_links_0064)
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (Fin.cases (record032_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x694297d2b28e7455a2610607f93f394ac84a3b31bb8d905f82c515988c845622410e885841a2080fd07b03c61d50e707203761ad0d3065831e1880c105f027a13509704641fc0ef06d823811a08703581a80c005f02e016c0ae05602a013c066032014009c04802300f807803801b00a8050026012008803c01c00b005002400e0040018008002000 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
def record033_frame002_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x5f6a97d31c92c47423490e283240e9980b6256529a14989a44a02490fc07c23d41e28ef475639b1bd8d886a032718a8c145c62c215c0a484fe26d12d09243721aa0cb859424210006c023811a08703581a80c005f02e016c0ae05602a013c066032014009c04802300f807803801b00a8050026012008803c01c00b005002400e0040018008002000 } : Fields).get c.val)
theorem record033_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record033) (record033.maps 2) (record033.inverseMaps 2) record033_frame002_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record033) (record033.maps 2) (record033.inverseMaps 2) record033_frame002_indices (Fin.ofNat record033.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record033_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record033) (record033.maps 2)
      (record033.inverseMaps 2) record033_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record033_frame002_links_0000 record033_frame002_links_0064)
theorem record033_frame002_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 2 :=
  of_group record033 2 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record033_frame002_indices record033_frame002_graph record033_frame002_links
def record033_frame003_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0xc8b692a25119d937652c808e2ed9acb2a614bfd672ae5469912ca4f4868e117a2843681cfd9ea3ba75ce59bc35e670c91852fe5ec989242323cc680c11481e83c8750c21802b0550a41442684c09411c1983205009c1202303e0780e01b02a0500981202203c0700b0140240380400600800800 } : Fields).get c.val)
theorem record033_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record033) (record033.maps 3) (record033.inverseMaps 3) record033_frame003_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record033) (record033.maps 3) (record033.inverseMaps 3) record033_frame003_indices (Fin.ofNat record033.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record033_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record033) (record033.maps 3)
      (record033.inverseMaps 3) record033_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record033_frame003_links_0000 record033_frame003_links_0064)
theorem record033_frame003_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 3 :=
  of_group record033 3 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record033_frame003_indices record033_frame003_graph record033_frame003_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (Fin.cases (record033_frame002_supported hcells) (Fin.cases (record033_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1f28db466d33094bea1d504a6b90607f43f11eccf4652b27493548f42fc1600ab84fe26f10708043e61ec0d305ec2b21520a5851027a111085040c1ee0f006a02c015e0aa04902440d606a034015c0ac03301900c003e01e00d804001e00e005002400e0060028010006000 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 66 :=
  interval_of_check _ 64 2 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 66 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x3a7191ac4961aa8a13c89d04b0a46cf9e70d34b177ca304dd266919c85c41f1e70dc055226e12f07e037e1b00af853c29014109d04cc22010a07783a41600af04702340d606a03401700b605702b015009e04102000dc06c03301900c4060024011807c03c01c00d803c01c00a004801c00c005002000c002000 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x7f93bc1c24d586703329802a4751aa88d4208ce45f22b113483040c9fa4fa67b7366944ca024ef26e0e687143781b30bf05ca2b514f8a0c4561f30eb074034c1970c505ec2ea13d097048422410c06402c813c094049024011a08c03d01bc0d4069030016c0b405702b01540a804201b80c8062028011808803e01e00e8070028013008003801a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
def record039_frame002_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0651.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0651.count (({ width := 9, code := 0xacd4697429dcea671a8c45a2afd7dbe5f0f378bb1d6e96f31586c1602a14ca451a7938974b25116823d9e8ea73371b4d6623016cb4582692c8e41200f8783b1c8d46431178b0562a148a04e25108783a1b0c05c2c150a04c1e0e060281208038180a04018080200 } : Fields).get c.val)
theorem record039_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0651.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (smallEmbedding record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (smallEmbedding record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record039_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (smallEmbedding record039) (record039.maps 2)
      (record039.inverseMaps 2) record039_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record039_frame002_links_0000 record039_frame002_links_0064)
theorem record039_frame002_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 2 :=
  of_group record039 2 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0651
    Papers.RationalityTen.SharedFrameCatalogue.group0651_facts record039_frame002_indices record039_frame002_graph record039_frame002_links
def record039_frame003_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0648.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0648.count (({ width := 8, code := 0xfdf8f4ede7e6e2cecccbcab7b5b4b3afaeacabaaa5918f8e8d7a78777672716f6e6d69625c5b57565453524d4c4a49484544423d3c3a38373633302f2d2a292827262524211e1d1b1817161514130f0e0c0a09080706050403020100 } : Fields).get c.val)
theorem record039_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0648.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0648.localPairCheck (smallEmbedding record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0648.localPairCheck (smallEmbedding record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record039_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0648.localPairCheck (smallEmbedding record039) (record039.maps 3)
      (record039.inverseMaps 3) record039_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record039_frame003_links_0000 record039_frame003_links_0064)
theorem record039_frame003_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 3 :=
  of_group record039 3 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0648
    Papers.RationalityTen.SharedFrameCatalogue.group0648_facts record039_frame003_indices record039_frame003_graph record039_frame003_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (Fin.cases (record039_frame002_supported hcells) (Fin.cases (record039_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x3235874a284eaa6492c294348da43120c8dc3b89ce0dc86c034b19fcc7e5e02cc946099e467229110886440f1e88dc46542a913007e03c61d30e186802c414809d04cc23c10a07b03a412208e04681b80d606a030817c0b805b02b81580aa05402780e406c03501980c8052027012008c03e01e00e80700280120078038014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
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
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x2b7d4999128a2b442828fd9e9384670c317b2e455aa914ba875029c93125747e8dd091fb3ca6c8d119c3185fcb81672aa510999171f03c4760e71802ec558870fa1f0370640c61642b0550a81442804e0961001f8330640a8138240460881081f03c0700a01201e0380680b0140240380400600800800 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
def record043_frame001_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a50cc352fa8913628e744b20c0fca79229593c08fa3b31b10bf056225e11208743d81e40ee875c34c19e0cb86442b21520a5851027a134096847c23411307e83dc1e00da057823811a08703c01b80d606a03481a00b805b02b81580a804f02000d806603201880c004802300f807803801b00a805002400f0070034014009004001c00c005002000c002000 } : Fields).get c.val)
theorem record043_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record043_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record043) (record043.maps 1)
      (record043.inverseMaps 1) record043_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record043_frame001_links_0000 record043_frame001_links_0064)
theorem record043_frame001_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 1 :=
  of_group record043 1 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record043_frame001_indices record043_frame001_graph record043_frame001_links
def record043_frame002_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x192ac7655c2a8d45a95348322810a682e32c9910bc253527c12a08d64501d48e5463e30d17e8bb84fc26c12e09343e41e00e606dc34418c0bd055429013c08b842c1fe0da057823811a08703c01b80d606a03481a00b805b02b81580a804f02000d806603201880c004802300f807803801b00a805002400f0070034014009004001c00c005002000c002000 } : Fields).get c.val)
theorem record043_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record043_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record043) (record043.maps 2)
      (record043.inverseMaps 2) record043_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record043_frame002_links_0000 record043_frame002_links_0064)
theorem record043_frame002_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 2 :=
  of_group record043 2 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record043_frame002_indices record043_frame002_graph record043_frame002_links
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (Fin.cases (record043_frame001_supported hcells) (Fin.cases (record043_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x191ac7462830f1450a0f4f5a75d2c29524a6251523690c48323fd0567713721b00d2c6563209780a3050227993849a246722911088644232078dc455229314209c84c41f80f1874c3861b40d0052027413308f045c2140e9059023811a08c03581a80d206102e016c0b405702b01540a804f02180e406a03301900c4052024011808803e01e00e807002800f0070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
def record044_frame002_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0639.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0639.count (({ width := 9, code := 0x3218bc3e12d967b1d82a14aa3d127735994be471a89c3a1301803e9d6e77238dc4d669b459ecc64aed58a953a9544964923d1c8d451f4f074361acd05d271188a441e8f07637198c8622e168b0562a1489c4a2311084401c0d8682e160a850260f0703414090401c0a04018080200 } : Fields).get c.val)
theorem record044_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0639.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record044_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record044) (record044.maps 2)
      (record044.inverseMaps 2) record044_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record044_frame002_links_0000 record044_frame002_links_0064)
theorem record044_frame002_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 2 :=
  of_group record044 2 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0639
    Papers.RationalityTen.SharedFrameCatalogue.group0639_facts record044_frame002_indices record044_frame002_graph record044_frame002_links
def record044_frame003_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0636.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0636.count (({ width := 7, code := 0x3b75e9cf86fddb75ead3a33e6cb931e1bf7aedcb76abd6ab529d1a13e74d992e4478d162428301fbe7af1dba72e1bb66ac582f58ad5294e992a446890a03e74d9a3260b95284c911203c70c16284880e182840608080 } : Fields).get c.val)
theorem record044_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0636.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0636.localPairCheck (smallEmbedding record044) (record044.maps 3) (record044.inverseMaps 3) record044_frame003_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0636.localPairCheck (smallEmbedding record044) (record044.maps 3) (record044.inverseMaps 3) record044_frame003_indices (Fin.ofNat record044.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record044_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0636.localPairCheck (smallEmbedding record044) (record044.maps 3)
      (record044.inverseMaps 3) record044_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record044_frame003_links_0000 record044_frame003_links_0064)
theorem record044_frame003_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 3 :=
  of_group record044 3 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0636
    Papers.RationalityTen.SharedFrameCatalogue.group0636_facts record044_frame003_indices record044_frame003_graph record044_frame003_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (Fin.cases (record044_frame002_supported hcells) (Fin.cases (record044_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
def record045_frame001_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a50ce16652ced4bea4c51228413668e746022b513483040e2030ff67e930394aca304f026e11fc76638c1bc8d985f82e816c0b1c56a1ec0f207743ae1d00e387083681a60cb86443141830af854828813d09a84a024211307b03c011c08d046021c0e206b03501a40c205c02d81680ae05602a815009e03901980c8062029012008c04401f00f007403801b00a805001e00e0068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record045_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record045_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record045) (record045.maps 1)
      (record045.inverseMaps 1) record045_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record045_frame001_links_0000 record045_frame001_links_0064)
theorem record045_frame001_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 1 :=
  of_group record045 1 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record045_frame001_indices record045_frame001_graph record045_frame001_links
def record045_frame002_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x65f65164a6005ab59e58a57e56150c4f74eb4df4bb4b44ae4a94a24293d43c93b23a538633131e30f3022e02d82d22cd2c62132071fa1f01e41da1d51c41b119819118617c14a13e12c1211141010f60e50bc0b808408308207d06e06806706605f05a05905805505405305204d03803203103002902402302201f01e01d01c01b01501400f00e00d00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record045_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record045) (record045.maps 2) (record045.inverseMaps 2) record045_frame002_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record045) (record045.maps 2) (record045.inverseMaps 2) record045_frame002_indices (Fin.ofNat record045.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record045_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record045) (record045.maps 2)
      (record045.inverseMaps 2) record045_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record045_frame002_links_0000 record045_frame002_links_0064)
theorem record045_frame002_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 2 :=
  of_group record045 2 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record045_frame002_indices record045_frame002_graph record045_frame002_links
def record045_frame003_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x256c9a92b1a218c2a83904dfdbb7744e6dc83696c2d61a934b604af959aa252ea052523b46a8b1031fd3ea7bcf418a3085f8bd9782e45b0b01542864f49b12f21c4087a8f01ce364690c41542903e07b0f41e0338620c21802c0530a41442704d09812c248370620c01782804808c1101f03c0740e01b02a0500780e01a0300500901001c0280400600800800 } : Fields).get c.val)
theorem record045_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record045) (record045.maps 3) (record045.inverseMaps 3) record045_frame003_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record045) (record045.maps 3) (record045.inverseMaps 3) record045_frame003_indices (Fin.ofNat record045.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record045_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record045) (record045.maps 3)
      (record045.inverseMaps 3) record045_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record045_frame003_links_0000 record045_frame003_links_0064)
theorem record045_frame003_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 3 :=
  of_group record045 3 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record045_frame003_indices record045_frame003_graph record045_frame003_links
def record045_frame004_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x17dabb15cdab814bea4c510a8393a492c48023a91a887142e212106881f3769980ca462f30f179caca54429b14a09a44c125812889283621a88cf06523171820bd05a62b81498a044de25b0fe07803861b90d506182ec151088040411c08d046021c0e206b03501a40c205c02d81680ae05602a815009e03901980c8062029012008c04401f00f007403801b00a805001e00e0068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record045_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record045) (record045.maps 4) (record045.inverseMaps 4) record045_frame004_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record045) (record045.maps 4) (record045.inverseMaps 4) record045_frame004_indices (Fin.ofNat record045.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record045_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record045) (record045.maps 4)
      (record045.inverseMaps 4) record045_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record045_frame004_links_0000 record045_frame004_links_0064)
theorem record045_frame004_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 4 :=
  of_group record045 4 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record045_frame004_indices record045_frame004_graph record045_frame004_links
def record045_frame005_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6ce6a769b6225cd5c25ac59f57a52550f5054f84c94bd4b14a749a3e839338836f3653402eb2d52c82bf28f28327726a25f1b91b51ae1a81a019619017f17016515f15714f12c12211611010c1010f90ee0d40d008a08908808306f06906806705f05a05905805505405305204d03903303203102902402302201f01e01d01c01b01501400f00e00d00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record045_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record045) (record045.maps 5) (record045.inverseMaps 5) record045_frame005_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record045) (record045.maps 5) (record045.inverseMaps 5) record045_frame005_indices (Fin.ofNat record045.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record045_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record045) (record045.maps 5)
      (record045.inverseMaps 5) record045_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record045_frame005_links_0000 record045_frame005_links_0064)
theorem record045_frame005_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 5 :=
  of_group record045 5 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record045_frame005_indices record045_frame005_graph record045_frame005_links
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (Fin.cases (record045_frame001_supported hcells) (Fin.cases (record045_frame002_supported hcells) (Fin.cases (record045_frame003_supported hcells) (Fin.cases (record045_frame004_supported hcells) (Fin.cases (record045_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
def record046_frame001_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x32358a0c3c51427ad3ae9614aca54929894548da44d21890647f9a58cac64128c14109e64e1268919c8a8442219108c55229514209c84c41f80f2874c3861b40a7852028213a099847822e11008503bc1d20aa047023411808703581a80d206803101840b805b02d015c0ac05502a013c06603201880c0054029012008c04401f00f007403801b00a805001e00e0068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record046_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record046_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record046) (record046.maps 1)
      (record046.inverseMaps 1) record046_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record046_frame001_links_0000 record046_frame001_links_0064)
theorem record046_frame001_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 1 :=
  of_group record046 1 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record046_frame001_indices record046_frame001_graph record046_frame001_links
def record046_frame002_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x34a19c2cca52fa8914208e7469a30115a89a41820790187fb3f494ac9e04dc1d98e7c7183791b30bf05d42d81638ad43d81e40ee875c3a01a60cf065c32218a0ac854829614409e84a024211a08983dc1e00aa047023411808703581a80d206803101840b805b02d015c0ac05502a013c06603201880c0054029012008c04401f00f007403801b00a805001e00e0068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record046_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record046) (record046.maps 2) (record046.inverseMaps 2) record046_frame002_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record046) (record046.maps 2) (record046.inverseMaps 2) record046_frame002_indices (Fin.ofNat record046.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record046_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record046) (record046.maps 2)
      (record046.inverseMaps 2) record046_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record046_frame002_links_0000 record046_frame002_links_0064)
theorem record046_frame002_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 2 :=
  of_group record046 2 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record046_frame002_indices record046_frame002_graph record046_frame002_links
def record046_frame003_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0xc9d8a30e538a2541a5049892523a444648b915a2944c6a0ca98f2b8560aa9532a04f89d13726a4c8798ef1d83a8738d51a2338660c916c2d45a0b31642bc570ad1582a05389a1042044007d0ca190318620b816c2b0550a81442804f09c12c198320620c01502904808c1101f03c0740e01b02a0500780e01a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record046_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record046) (record046.maps 3) (record046.inverseMaps 3) record046_frame003_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record046) (record046.maps 3) (record046.inverseMaps 3) record046_frame003_indices (Fin.ofNat record046.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record046_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record046) (record046.maps 3)
      (record046.inverseMaps 3) record046_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record046_frame003_links_0000 record046_frame003_links_0064)
theorem record046_frame003_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 3 :=
  of_group record046 3 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record046_frame003_indices record046_frame003_graph record046_frame003_links
def record046_frame004_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xd5da1b3c574a994fa6c4d099531a6049c92923a454846d0d01992cc588af95d2b4520a214127e4f07e8f91ec3d0788df1b63606b0d31802fc5f0bd1782e45c0b716c2c8588a5114224440840d21a0338660c017c2d0590b01542a0530a4138198320620c01502904808c1101f03c0740e01b02a0500780e01a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record046_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record046) (record046.maps 4) (record046.inverseMaps 4) record046_frame004_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record046) (record046.maps 4) (record046.inverseMaps 4) record046_frame004_indices (Fin.ofNat record046.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record046_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record046) (record046.maps 4)
      (record046.inverseMaps 4) record046_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record046_frame004_links_0000 record046_frame004_links_0064)
theorem record046_frame004_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 4 :=
  of_group record046 4 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record046_frame004_indices record046_frame004_graph record046_frame004_links
def record046_frame005_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x3255900c7955c2a8d53895349fa4b123690a45022310f286842b9964c8863e29a9494a2e50a27e12a093048a23e91bc63e30d17e8bb85ba27e136097049a23c0f907803981b70d105a82ae14809e042c1fe0aa047023411808703581a80d206803101840b805b02d015c0ac05502a013c06603201880c0054029012008c04401f00f007403801b00a805001e00e0068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record046_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record046) (record046.maps 5) (record046.inverseMaps 5) record046_frame005_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record046) (record046.maps 5) (record046.inverseMaps 5) record046_frame005_indices (Fin.ofNat record046.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record046_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record046) (record046.maps 5)
      (record046.inverseMaps 5) record046_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record046_frame005_links_0000 record046_frame005_links_0064)
theorem record046_frame005_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 5 :=
  of_group record046 5 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record046_frame005_indices record046_frame005_graph record046_frame005_links
def record046_frame006_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x2fb5762b9b52fa88541c92c48c24011d48d4438a17909083440f9980c5e61e2b2955ca8853629413489864b025112506c435119e0ca462e2b81538a4c50226f0f707803a21c30dc86182ec1660a884442020a6047023411808703581a80d206803101840b805b02d015c0ac05502a013c06603201880c0054029012008c04401f00f007403801b00a805001e00e0068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record046_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record046) (record046.maps 6) (record046.inverseMaps 6) record046_frame006_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record046) (record046.maps 6) (record046.inverseMaps 6) record046_frame006_indices (Fin.ofNat record046.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record046_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record046) (record046.maps 6)
      (record046.inverseMaps 6) record046_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record046_frame006_links_0000 record046_frame006_links_0064)
theorem record046_frame006_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 6 :=
  of_group record046 6 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record046_frame006_indices record046_frame006_graph record046_frame006_links
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (Fin.cases (record046_frame001_supported hcells) (Fin.cases (record046_frame002_supported hcells) (Fin.cases (record046_frame003_supported hcells) (Fin.cases (record046_frame004_supported hcells) (Fin.cases (record046_frame005_supported hcells) (Fin.cases (record046_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
def record047_frame001_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc3744f21ed0e282d40c1d64e9a7373929ac8c546192d894c4a464f926d934896239b1c60dec6d83621a70c946263051718b0857027d135891c4682220fe07803861b90c185cc29e140098035412409104081600ae056024810c08204001b80d8050027010007c03c01d00d804402000f007002c0140090028010006000 } : Fields).get c.val)
theorem record047_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record047_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record047) (record047.maps 1)
      (record047.inverseMaps 1) record047_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record047_frame001_links_0000 record047_frame001_links_0064)
theorem record047_frame001_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 1 :=
  of_group record047 1 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record047_frame001_indices record047_frame001_graph record047_frame001_links
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (Fin.cases (record047_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
def record048_frame001_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1bc8d976ac343d990abf53a28392b28e7455a2610327fa3e99f14f6c7952c595009b44251d98ddc6c82e51630a7c52228213088584021f30f6075439c1ad0cc06402e816709e84481fc0ef07482e012809104802340dc06c03501800be05c02d81580aa05401b00d0064028013809004601e00e8070026012008003c01c00b004802000e0040018008002000 } : Fields).get c.val)
theorem record048_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record048_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record048) (record048.maps 1)
      (record048.inverseMaps 1) record048_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record048_frame001_links_0000 record048_frame001_links_0064)
theorem record048_frame001_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 1 :=
  of_group record048 1 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record048_frame001_indices record048_frame001_graph record048_frame001_links
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (Fin.cases (record048_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
def record050_frame001_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x76975b74e6e269568e5ee5d75d05c05b45ad59759057b5745094fc4ee48242942237a36035934833d33732131b3063002ca2bb29e28227226324622a2031eb1d21c61bb1b318517c17616d15513c1301121091020fa0e00c60c207b07907806f06e05c05b05805705604304104003703602402302001f01e01b01501301201100f00e00d00b00a009008005004003001000 } : Fields).get c.val)
theorem record050_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record050_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record050) (record050.maps 1)
      (record050.inverseMaps 1) record050_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record050_frame001_links_0000 record050_frame001_links_0064)
theorem record050_frame001_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 1 :=
  of_group record050 1 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record050_frame001_indices record050_frame001_graph record050_frame001_links
def record050_frame002_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0613.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0613.count (({ width := 10, code := 0x209811fe7b9db75dbb6d5b16b5a768d9e66995645835f9775854a5192146d1744d0d421033fcfb3dcef3b4e9388df374d9348c12f8b82d0b12b499250902348a210801d8711b4691704c1243b0e4380dc360c4300b82d0b0280982508c220701b0641805c16054130481103c0e0340b02809020050100300400 } : Fields).get c.val)
theorem record050_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record050) (record050.maps 2) (record050.inverseMaps 2) record050_frame002_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record050) (record050.maps 2) (record050.inverseMaps 2) record050_frame002_indices (Fin.ofNat record050.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record050_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record050) (record050.maps 2)
      (record050.inverseMaps 2) record050_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record050_frame002_links_0000 record050_frame002_links_0064)
theorem record050_frame002_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 2 :=
  of_group record050 2 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0613
    Papers.RationalityTen.SharedFrameCatalogue.group0613_facts record050_frame002_indices record050_frame002_graph record050_frame002_links
def record050_frame003_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0608.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0608.count (({ width := 9, code := 0x170b65a2c155a8d127f3b9ccd6632d94c96431689c3e04f579381b4d76ab499cc9633097eb85b2cd5cac5529d4494492391488431e8ec72381b8d46630170b257271007a33190c4602f150a450271308842200f0742e160a8502612088401e0e06830160a048200e050200c0200 } : Fields).get c.val)
theorem record050_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0608.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (smallEmbedding record050) (record050.maps 3) (record050.inverseMaps 3) record050_frame003_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (smallEmbedding record050) (record050.maps 3) (record050.inverseMaps 3) record050_frame003_indices (Fin.ofNat record050.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record050_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (smallEmbedding record050) (record050.maps 3)
      (record050.inverseMaps 3) record050_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record050_frame003_links_0000 record050_frame003_links_0064)
theorem record050_frame003_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 3 :=
  of_group record050 3 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0608
    Papers.RationalityTen.SharedFrameCatalogue.group0608_facts record050_frame003_indices record050_frame003_graph record050_frame003_links
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (Fin.cases (record050_frame001_supported hcells) (Fin.cases (record050_frame002_supported hcells) (Fin.cases (record050_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
def record051_frame001_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x2c89560a7653226d928890a47c22d515c8994491b5cce46373131608a3a4e2268923c91047523790047d43bc1c98df46d434118c8c085b02c515c0a644f426b12d093043820e0f2075436c1970c405dc2d213909584041e00e9071036c1a806f03701ac0d406002f81700b603701b00cc064028013809004601b00a804c024011007803801600a004802000e005002000c004001 } : Fields).get c.val)
theorem record051_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record051_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record051) (record051.maps 1)
      (record051.inverseMaps 1) record051_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record051_frame001_links_0000 record051_frame001_links_0064)
theorem record051_frame001_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 1 :=
  of_group record051 1 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record051_frame001_indices record051_frame001_graph record051_frame001_links
def record051_frame002_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0613.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0613.count (({ width := 10, code := 0x1ee781dc761c96edb66c99d665946416153d4b51d324851c461023f8fa3d8ef3b4e9388df374d9348d1330c7304be2e0b42c4ad2849e2448d228842007e1ec6d1a45d168561444b120370d8350d0330c8310c023088210801e0741c06c16054130481103c0e02c0a0240801c050100300801 } : Fields).get c.val)
theorem record051_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record051) (record051.maps 2) (record051.inverseMaps 2) record051_frame002_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record051) (record051.maps 2) (record051.inverseMaps 2) record051_frame002_indices (Fin.ofNat record051.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record051_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record051) (record051.maps 2)
      (record051.inverseMaps 2) record051_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record051_frame002_links_0000 record051_frame002_links_0064)
theorem record051_frame002_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 2 :=
  of_group record051 2 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0613
    Papers.RationalityTen.SharedFrameCatalogue.group0613_facts record051_frame002_indices record051_frame002_graph record051_frame002_links
def record051_frame003_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0609.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0609.count (({ width := 8, code := 0xa39f9d9b9692908e888684827672706f6a6664635d5c5a59555453504f4e4d4a494846454442403f3e3c3b393837353332312f2e2c2b2a2827262524232221201f1e1918171614131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record051_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0609.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0609.localPairCheck (smallEmbedding record051) (record051.maps 3) (record051.inverseMaps 3) record051_frame003_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0609.localPairCheck (smallEmbedding record051) (record051.maps 3) (record051.inverseMaps 3) record051_frame003_indices (Fin.ofNat record051.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record051_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0609.localPairCheck (smallEmbedding record051) (record051.maps 3)
      (record051.inverseMaps 3) record051_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record051_frame003_links_0000 record051_frame003_links_0064)
theorem record051_frame003_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 3 :=
  of_group record051 3 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0609
    Papers.RationalityTen.SharedFrameCatalogue.group0609_facts record051_frame003_indices record051_frame003_graph record051_frame003_links
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (Fin.cases (record051_frame001_supported hcells) (Fin.cases (record051_frame002_supported hcells) (Fin.cases (record051_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
def record052_frame001_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x602a8d12f691647ea3d911485142020450007e72f91558a024ee274924c8d045c21c90b48343bc1d70e386de35c1a70cb861e30417b0bc05c228d133896c49822d11088483f41ec0e406903241820bb854428c12607c824411a06e03501800be05c02d81600ac05502a00d8064028013809004602000f007403801b00a804c0240110078038016009004001c00a0040018008002000 } : Fields).get c.val)
theorem record052_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record052_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record052) (record052.maps 1)
      (record052.inverseMaps 1) record052_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record052_frame001_links_0000 record052_frame001_links_0064)
theorem record052_frame001_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) : Supported record052 1 :=
  of_group record052 1 (smallEmbedding record052) (small_cells_exact record052 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record052_frame001_indices record052_frame001_graph record052_frame001_links
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (Fin.cases (record052_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record052_frames_supported
theorem record053_frame000_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    Supported record053 0 :=
  of_identity record053 0 (by decide +kernel)
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record053_frames_supported
theorem record054_frame000_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    Supported record054 0 :=
  of_identity record054 0 (by decide +kernel)
def record054_frame001_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xcfe64faead72aaa650da8213a69c34d326391c88ce417a068d0a66833018a4c305a52c515b8aca53029111b08b844d1828b8c5842b813d89a448a23211007b83c01d10e186e43481810b8853427c12e07f83c81ca0aa054827013606f03701a00c406002f80d0066032018009404802300d802c0140090030014008003 } : Fields).get c.val)
theorem record054_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record054) (record054.maps 1) (record054.inverseMaps 1) record054_frame001_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record054) (record054.maps 1) (record054.inverseMaps 1) record054_frame001_indices (Fin.ofNat record054.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record054_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record054) (record054.maps 1)
      (record054.inverseMaps 1) record054_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record054_frame001_links_0000 record054_frame001_links_0064)
theorem record054_frame001_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) : Supported record054 1 :=
  of_group record054 1 (smallEmbedding record054) (small_cells_exact record054 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record054_frame001_indices record054_frame001_graph record054_frame001_links
theorem record054_frames_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    ∀ f : Fin record054.g, Supported record054 f :=
  (Fin.cases (record054_frame000_supported hcells) (Fin.cases (record054_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record054_frames_supported
theorem record055_frame000_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    Supported record055 0 :=
  of_identity record055 0 (by decide +kernel)
def record055_frame001_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x127e34440874fa5edbd56accf99ab1f62cb995ca984de9b533a5c454891021fe3a6720e19883065ecba9682c45089511f22c4047d0f61e03a4718df1aa33c630c11762cc5709d130248488800fe194320620a61482084006e0d8198320620c01502804e07c0f01d0360400780e0140240380600a01001800 } : Fields).get c.val)
theorem record055_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record055_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record055) (record055.maps 1)
      (record055.inverseMaps 1) record055_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record055_frame001_links_0000 record055_frame001_links_0064)
theorem record055_frame001_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 1 :=
  of_group record055 1 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record055_frame001_indices record055_frame001_graph record055_frame001_links
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (Fin.cases (record055_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record055_frames_supported
theorem record056_frame000_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    Supported record056 0 :=
  of_identity record056 0 (by decide +kernel)
def record056_frame001_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x8e30f5f8bd874ae15bb37269ad0194b21624b5562ab4540a1936a674b88e115a26444848f99e33b8758e218e3065ecba9692c8580a49392664b4881021c6380638b71642b4540810fe1ec338660c816c2d0580ae1482885007e0e41b0340640a81402704808c1081e03a0700981202003c0700b0120200380400600800800 } : Fields).get c.val)
theorem record056_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record056_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record056) (record056.maps 1)
      (record056.inverseMaps 1) record056_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record056_frame001_links_0000 record056_frame001_links_0064)
theorem record056_frame001_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) : Supported record056 1 :=
  of_group record056 1 (smallEmbedding record056) (small_cells_exact record056 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record056_frame001_indices record056_frame001_graph record056_frame001_links
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (Fin.cases (record056_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
def record058_frame001_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xcff646b139874a9a51427a53aa90347e239d1c070d34b1950c7e5e12e916b0b0c5732a794aca304df267919c8a84011e88dc86c633d18b8c105c02bc15489c04c01f80f286482c4155095847422c10908183f01c40dc06b034012409104702340de06e03581a806e03601980c806002a014009c04a024011807c03c01d00e006c02a013009004001e00e0050024010007 } : Fields).get c.val)
theorem record058_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record058_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record058) (record058.maps 1)
      (record058.inverseMaps 1) record058_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record058_frame001_links_0000 record058_frame001_links_0064)
theorem record058_frame001_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) : Supported record058 1 :=
  of_group record058 1 (smallEmbedding record058) (small_cells_exact record058 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record058_frame001_indices record058_frame001_graph record058_frame001_links
def record058_frame002_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x634c2982f0359faf15a6b24658af0ce12bad70add1b734f694d0999b2b644c6187aff5f4b316129a4fc9692aa4746a8b110a1140e7ccf69b43545ecae95722c4147d8ea1c235c588a413a258418821001fc340670ca1901b0350660c81802a05009c1282404607c0f01d03806c0a8130240400780e01402404007 } : Fields).get c.val)
theorem record058_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record058) (record058.maps 2) (record058.inverseMaps 2) record058_frame002_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record058) (record058.maps 2) (record058.inverseMaps 2) record058_frame002_indices (Fin.ofNat record058.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record058_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record058) (record058.maps 2)
      (record058.inverseMaps 2) record058_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record058_frame002_links_0000 record058_frame002_links_0064)
theorem record058_frame002_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) : Supported record058 2 :=
  of_group record058 2 (smallEmbedding record058) (small_cells_exact record058 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record058_frame002_indices record058_frame002_graph record058_frame002_links
def record058_frame003_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x46889d10a1ebff7d2f75ec33d668c798aab9530a314326f4da99d2e25649a8fd1c22b44c810ff1dd3886b0d399c31c620c197b2ea5a4b2142274458810fc1bc350670c51802e8538a213825c4007f0f81ec340670ca1901b8360660c81802a05009c1282404607c0f01d03806c0a8130240400780e01402404007 } : Fields).get c.val)
theorem record058_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record058) (record058.maps 3) (record058.inverseMaps 3) record058_frame003_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record058) (record058.maps 3) (record058.inverseMaps 3) record058_frame003_indices (Fin.ofNat record058.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record058_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record058) (record058.maps 3)
      (record058.inverseMaps 3) record058_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record058_frame003_links_0000 record058_frame003_links_0064)
theorem record058_frame003_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) : Supported record058 3 :=
  of_group record058 3 (smallEmbedding record058) (small_cells_exact record058 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record058_frame003_indices record058_frame003_graph record058_frame003_links
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (Fin.cases (record058_frame001_supported hcells) (Fin.cases (record058_frame002_supported hcells) (Fin.cases (record058_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
def record061_frame001_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x31d189ec3c507a7a93ae9684a9a52d28a91b47fa3c11d482d3b01bd4d8065532095c4a5650227a13809a2467229108c81e4011f88c0857829314289c44c41f80f186d03401920c10520274133092845c2080e9059024811a08c03781a80d206002e816c0b405702b01540a804902180e406e03501900c4050025011808803e01e00e80700260100070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record061_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record061_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record061) (record061.maps 1)
      (record061.inverseMaps 1) record061_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record061_frame001_links_0000 record061_frame001_links_0064)
theorem record061_frame001_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) : Supported record061 1 :=
  of_group record061 1 (smallEmbedding record061) (small_cells_exact record061 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record061_frame001_indices record061_frame001_graph record061_frame001_links
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (Fin.cases (record061_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record061_frames_supported
theorem record062_frame000_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) :
    Supported record062 0 :=
  of_identity record062 0 (by decide +kernel)
def record062_frame001_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x19e6ced54d29dd4cc92e485a3e91c08d2465a2f515e8a144d1970c70628283938c9a64b9256129492e48923e11d88023ea1be8d045b22c715c0a644f426b12d093045a21c10708003aa1b60cb86202ee1690a504e425611d049023411807b03781a80d206002d81680b005702b01540a804301b80c8062028011808804001f00f007403801b00a804c02200e006802c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record062_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record062_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record062) (record062.maps 1)
      (record062.inverseMaps 1) record062_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record062_frame001_links_0000 record062_frame001_links_0064)
theorem record062_frame001_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) : Supported record062 1 :=
  of_group record062 1 (smallEmbedding record062) (small_cells_exact record062 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record062_frame001_indices record062_frame001_graph record062_frame001_links
def record062_frame002_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6666625ac5a259e51750b5074e64cf4c94b249e48647f3af3a63a233332c32a30b2f32ec2dc2ce2bd2b627626d24422d20a2061fc1dd1c11b91af1a619118817f17415714212d12511e1161060fe0f60ee08107f07e07306906406305a05505405205105004f04e04303703203102802302202001f01e01d01c01b01501301100e00d00b00a009008007005004003002001000 } : Fields).get c.val)
theorem record062_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record062) (record062.maps 2) (record062.inverseMaps 2) record062_frame002_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record062) (record062.maps 2) (record062.inverseMaps 2) record062_frame002_indices (Fin.ofNat record062.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record062_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record062) (record062.maps 2)
      (record062.inverseMaps 2) record062_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record062_frame002_links_0000 record062_frame002_links_0064)
theorem record062_frame002_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) : Supported record062 2 :=
  of_group record062 2 (smallEmbedding record062) (small_cells_exact record062 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record062_frame002_indices record062_frame002_graph record062_frame002_links
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (Fin.cases (record062_frame001_supported hcells) (Fin.cases (record062_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record062_frames_supported
theorem record063_frame000_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) :
    Supported record063 0 :=
  of_identity record063 0 (by decide +kernel)
def record063_frame001_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x288d0e9791e237c6a83b032034037c0f69e33b9764ced7b2ec5cea554127c4f29712c2484788dd052023b66e4d49a032c640c49842ea59ca71442764d48f91320a3f47b8ef1ba3205b0b010e2144206e0da1a03385f0ba16c2d0570ac1542a03906e0c81882804a08c1101f03c0740e01b02a04c0800e01a0300500901001c0280400600800800 } : Fields).get c.val)
theorem record063_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record063_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record063) (record063.maps 1)
      (record063.inverseMaps 1) record063_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record063_frame001_links_0000 record063_frame001_links_0064)
theorem record063_frame001_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) : Supported record063 1 :=
  of_group record063 1 (smallEmbedding record063) (small_cells_exact record063 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record063_frame001_indices record063_frame001_graph record063_frame001_links
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (Fin.cases (record063_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record063_frames_supported
theorem record064_frame000_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    Supported record064 0 :=
  of_identity record064 0 (by decide +kernel)
def record064_frame001_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x189ec3c4f5275d3589a74c1a5a12b29534a5a51523691347fa3c11d46553209784ba457329594109e84e0268919c8a84232008fc46e43631820af052a28513889883f01e50da064830414f0a40504274133092845c22010407783a412408d04601bc0d406903401880c005d02d81680ae05602a815006e03201880c0054028012808c04401f00f007403801b00a804c02000e0068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record064_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record064_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record064) (record064.maps 1)
      (record064.inverseMaps 1) record064_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record064_frame001_links_0000 record064_frame001_links_0064)
theorem record064_frame001_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) : Supported record064 1 :=
  of_group record064 1 (smallEmbedding record064) (small_cells_exact record064 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record064_frame001_indices record064_frame001_graph record064_frame001_links
def record064_frame002_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19c0cca511a8413689a24a2a3e91a68c1456226906081e3f49f1cf6e4ef26e12008dc4111e30e7c71a3781b30bf05d42b51498a0c46e23210707cc3c81de0eb074034c19e0c505ec2ea1590a9052c28813d097848423410c07b83c012408d04601bc0d406903401880c005d02d81680ae05602a815006e03201880c0054028012808c04401f00f007403801b00a804c02000e0068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record064_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record064) (record064.maps 2) (record064.inverseMaps 2) record064_frame002_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record064) (record064.maps 2) (record064.inverseMaps 2) record064_frame002_indices (Fin.ofNat record064.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record064_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record064) (record064.maps 2)
      (record064.inverseMaps 2) record064_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record064_frame002_links_0000 record064_frame002_links_0064)
theorem record064_frame002_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) : Supported record064 2 :=
  of_group record064 2 (smallEmbedding record064) (small_cells_exact record064 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record064_frame002_indices record064_frame002_graph record064_frame002_links
def record064_frame003_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x1a133c54aa7d45a8a4f49bd342664c49812724a4848ed1c99f332614c21742d2588b015c2b4520a213c26a4cc8e11b2164007c8f71e63c46f8db1a6330650c017e2f85e8bc1742e05b8b51642c4470891101b4340670cc1802f05b0b21602a8540a61481b8320620c01502804a08c1101f03c0740e01b02a04c0800e01a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record064_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record064) (record064.maps 3) (record064.inverseMaps 3) record064_frame003_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record064) (record064.maps 3) (record064.inverseMaps 3) record064_frame003_indices (Fin.ofNat record064.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record064_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record064) (record064.maps 3)
      (record064.inverseMaps 3) record064_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record064_frame003_links_0000 record064_frame003_links_0064)
theorem record064_frame003_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) : Supported record064 3 :=
  of_group record064 3 (smallEmbedding record064) (small_cells_exact record064 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record064_frame003_indices record064_frame003_graph record064_frame003_links
def record064_frame004_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x21041d780ef5d6ba671cdedb7b696c6d7597324618bf97aa7a4ee9b53525849690d1fa3b46e849059f73d6790dc1b5334620be1772e65bca013a248454868f81e23ac728df1a8328620b91502803b8750e81883005f0bc1602b0530a21402684c0961281a8320620c01502804a08c1101f03c0740e01b02a04c0800e01a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record064_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record064) (record064.maps 4) (record064.inverseMaps 4) record064_frame004_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record064) (record064.maps 4) (record064.inverseMaps 4) record064_frame004_indices (Fin.ofNat record064.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record064_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record064) (record064.maps 4)
      (record064.inverseMaps 4) record064_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record064_frame004_links_0000 record064_frame004_links_0064)
theorem record064_frame004_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) : Supported record064 4 :=
  of_group record064 4 (smallEmbedding record064) (small_cells_exact record064 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record064_frame004_indices record064_frame004_graph record064_frame004_links
def record064_frame005_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0x299d2b94f2823f47689b0c20e41581b019efbd877ceb5d22e45bcb19622a851a9f13b2714d89011d224422824ef1d836a68ccb18f312614ad1532704a08f9092063f47b8f11cc36c6a0c81722cc4107d0f81b0340670cc1802f05b0b21602a8540a61481b8320620c01502804a08c1101f03c0740e01b02a04c0800e01a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record064_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record064) (record064.maps 5) (record064.inverseMaps 5) record064_frame005_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record064) (record064.maps 5) (record064.inverseMaps 5) record064_frame005_indices (Fin.ofNat record064.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record064_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record064) (record064.maps 5)
      (record064.inverseMaps 5) record064_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record064_frame005_links_0000 record064_frame005_links_0064)
theorem record064_frame005_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) : Supported record064 5 :=
  of_group record064 5 (smallEmbedding record064) (small_cells_exact record064 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record064_frame005_indices record064_frame005_graph record064_frame005_links
def record064_frame006_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0542.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0542.count (({ width := 9, code := 0x24b24894461308803f1f0f67a3cdd6e972381beca64b0580b85a2c15cac55a8d429c4c25d188b419fcf6793b9d8dc6c3398cc45d2e16cb4592b954a852279389449241188a44218f476391c0dc6833190c45e2e168b04c2411084401d0e06c3419098441e0e068281208038180a04018080200 } : Fields).get c.val)
theorem record064_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0542.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0542.localPairCheck (smallEmbedding record064) (record064.maps 6) (record064.inverseMaps 6) record064_frame006_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0542.localPairCheck (smallEmbedding record064) (record064.maps 6) (record064.inverseMaps 6) record064_frame006_indices (Fin.ofNat record064.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record064_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0542.localPairCheck (smallEmbedding record064) (record064.maps 6)
      (record064.inverseMaps 6) record064_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record064_frame006_links_0000 record064_frame006_links_0064)
theorem record064_frame006_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) : Supported record064 6 :=
  of_group record064 6 (smallEmbedding record064) (small_cells_exact record064 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0542
    Papers.RationalityTen.SharedFrameCatalogue.group0542_facts record064_frame006_indices record064_frame006_graph record064_frame006_links
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (Fin.cases (record064_frame001_supported hcells) (Fin.cases (record064_frame002_supported hcells) (Fin.cases (record064_frame003_supported hcells) (Fin.cases (record064_frame004_supported hcells) (Fin.cases (record064_frame005_supported hcells) (Fin.cases (record064_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record064_frames_supported
theorem record065_frame000_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) :
    Supported record065 0 :=
  of_identity record065 0 (by decide +kernel)
def record065_frame001_indices (c : Fin record065.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x19d4ab053c25112188ae44ca24911672537b99c8cbc6392e81688a3a509272131893a48823a91bc8d231916d0ad853227a135896049823c107074c36c1970c405d42d215909583c01d20e206d835015e09b03c01b80d606a034817c0b805b02d010007e03901b00cc06403101800a804e024011808802400f007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record065_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record065.data.requiredEdges q = true := by decide +kernel
theorem record065_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record065_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record065_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record065) (record065.maps 1)
      (record065.inverseMaps 1) record065_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record065_frame001_links_0000 record065_frame001_links_0064)
theorem record065_frame001_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) : Supported record065 1 :=
  of_group record065 1 (smallEmbedding record065) (small_cells_exact record065 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record065_frame001_indices record065_frame001_graph record065_frame001_links
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (Fin.cases (record065_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record065_frames_supported
theorem record066_frame000_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) :
    Supported record066 0 :=
  of_identity record066 0 (by decide +kernel)
def record066_frame001_indices (c : Fin record066.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x684b3d19daab054d29e14cc94449724311f48e0469232d17a8b6457a284ce465c31c98a0a3a507272134c9724ac252925c92048923e10046fa36a1a08c645b42c715c0a644f426b12d093047822d10e08383aa1b60cb86202ee1690ac852827212b047023411807b03581a80d205c02d81680b005702b01540a804301980c8062024011808804001f00f007403801b00a804401e00e006802c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record066_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record066.data.requiredEdges q = true := by decide +kernel
theorem record066_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record066) (record066.maps 1) (record066.inverseMaps 1) record066_frame001_indices (Fin.ofNat record066.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record066_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record066) (record066.maps 1) (record066.inverseMaps 1) record066_frame001_indices (Fin.ofNat record066.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record066_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record066) (record066.maps 1)
      (record066.inverseMaps 1) record066_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record066_frame001_links_0000 record066_frame001_links_0064)
theorem record066_frame001_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) : Supported record066 1 :=
  of_group record066 1 (smallEmbedding record066) (small_cells_exact record066 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record066_frame001_indices record066_frame001_graph record066_frame001_links
theorem record066_frames_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) :
    ∀ f : Fin record066.g, Supported record066 f :=
  (Fin.cases (record066_frame000_supported hcells) (Fin.cases (record066_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record066_frames_supported
theorem record067_frame000_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) :
    Supported record067 0 :=
  of_identity record067 0 (by decide +kernel)
def record067_frame001_indices (c : Fin record067.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x646b141878a284f5a75d3589614aca53128a93d4982489236913486a4191fe8f134b1958c825e128c14109c24d125e92688ee46722a110c8644232010dc8552295139098849c22b10407e03ca1d40e186d032614f0a40504274133092847822e11008503bc11c08d04601ac0d406903401880b805b02d01600ae05602a815006603201880c0054024011808804001f00f007403801b00a803c01c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record067_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record067.data.requiredEdges q = true := by decide +kernel
theorem record067_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record067) (record067.maps 1) (record067.inverseMaps 1) record067_frame001_indices (Fin.ofNat record067.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record067_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record067) (record067.maps 1) (record067.inverseMaps 1) record067_frame001_indices (Fin.ofNat record067.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record067_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record067) (record067.maps 1)
      (record067.inverseMaps 1) record067_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record067_frame001_links_0000 record067_frame001_links_0064)
theorem record067_frame001_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) : Supported record067 1 :=
  of_group record067 1 (smallEmbedding record067) (small_cells_exact record067 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record067_frame001_indices record067_frame001_graph record067_frame001_links
def record067_frame002_indices (c : Fin record067.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6943385994a5f51228413688e7469a2b5134887432210906081e4069fecfd27c829593c09b84801d98e7c6f23661a98cc061c2fc1750b6458e2b514a08dc3d81e40eb87403901bb0d6869833c1980c886282f81590a9052c28813d09784a024211a08983dc11c08d04601ac0d406903401880b805b02d01600ae05602a815006603201880c0054024011808804001f00f007403801b00a803c01c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record067_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record067.data.requiredEdges q = true := by decide +kernel
theorem record067_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record067) (record067.maps 2) (record067.inverseMaps 2) record067_frame002_indices (Fin.ofNat record067.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record067_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record067) (record067.maps 2) (record067.inverseMaps 2) record067_frame002_indices (Fin.ofNat record067.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record067_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record067) (record067.maps 2)
      (record067.inverseMaps 2) record067_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record067_frame002_links_0000 record067_frame002_links_0064)
theorem record067_frame002_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) : Supported record067 2 :=
  of_group record067 2 (smallEmbedding record067) (small_cells_exact record067 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record067_frame002_indices record067_frame002_graph record067_frame002_links
def record067_frame003_indices (c : Fin record067.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x64ec518729c512a0d37a5049891d222404768d51922e4588a513220350654c797b2b8560a995029851ca093e2744e09a932258448798ef1d439c718de1b0354688cf198324618b616a2d0598b21602bc570ad1582a041081100194320630c41702b0550a81482885009e138198320620c0150240460881001f03c0740e01b02a03c0700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record067_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record067.data.requiredEdges q = true := by decide +kernel
theorem record067_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record067) (record067.maps 3) (record067.inverseMaps 3) record067_frame003_indices (Fin.ofNat record067.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record067_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record067) (record067.maps 3) (record067.inverseMaps 3) record067_frame003_indices (Fin.ofNat record067.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record067_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record067) (record067.maps 3)
      (record067.inverseMaps 3) record067_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record067_frame003_links_0000 record067_frame003_links_0064)
theorem record067_frame003_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) : Supported record067 3 :=
  of_group record067 3 (smallEmbedding record067) (small_cells_exact record067 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record067_frame003_indices record067_frame003_graph record067_frame003_links
def record067_frame004_indices (c : Fin record067.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x6aed0d9e2ba54ca7d45a6c4d098d3025c4ae9452724a4909152123c368680cc9852cc588ae95a2ac544a59482885089f93c26c4707e8f91e83c4768e81c437c6d8d91ac34c668c017e2f85e8bc1742e45c0b716c2c8450891101a4340670cc1802d0590b01582a8540a6148198320620c0150240460881001f03c0740e01b02a03c0700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record067_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record067.data.requiredEdges q = true := by decide +kernel
theorem record067_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record067) (record067.maps 4) (record067.inverseMaps 4) record067_frame004_indices (Fin.ofNat record067.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record067_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record067) (record067.maps 4) (record067.inverseMaps 4) record067_frame004_indices (Fin.ofNat record067.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record067_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record067) (record067.maps 4)
      (record067.inverseMaps 4) record067_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record067_frame004_links_0000 record067_frame004_links_0064)
theorem record067_frame004_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) : Supported record067 4 :=
  of_group record067 4 (smallEmbedding record067) (small_cells_exact record067 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record067_frame004_indices record067_frame004_graph record067_frame004_links
def record067_frame005_indices (c : Fin record067.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x5f6aec5736a5f510a8393a692c48c23a91a88c144f21ed0e285e424a0d103e7f433018bcc3c5e82b2955ca6c52828c13e49b64d226192c49444942388ffc6c43511948c5c60a2e31610ae054e29414089bc4921ee0f007443861b90cc06182ec1660a8844411c08d04601ac0d406903401880b805b02d01600ae05602a815006603201880c0054024011808804001f00f007403801b00a803c01c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record067_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record067.data.requiredEdges q = true := by decide +kernel
theorem record067_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record067) (record067.maps 5) (record067.inverseMaps 5) record067_frame005_indices (Fin.ofNat record067.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record067_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record067) (record067.maps 5) (record067.inverseMaps 5) record067_frame005_indices (Fin.ofNat record067.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record067_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record067) (record067.maps 5)
      (record067.inverseMaps 5) record067_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record067_frame005_links_0000 record067_frame005_links_0064)
theorem record067_frame005_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) : Supported record067 5 :=
  of_group record067 5 (smallEmbedding record067) (small_cells_exact record067 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record067_frame005_indices record067_frame005_graph record067_frame005_links
def record067_frame006_indices (c : Fin record067.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6ce6a769b5cd5ac59f57b52551b5054f84ed4df4ce4c94bf4b24a749a48539336f3653412eb2e12c82bf2b32a229428f28527826a25f24b2071b91b51a81a019718817717016b16615f15714a12812211c1161101081010f90f30ee0d508a08908806906806706606005a05905805605505405305203303203103002a02402302202001f01e01d01c01b01500f00e00d00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record067_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record067.data.requiredEdges q = true := by decide +kernel
theorem record067_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record067) (record067.maps 6) (record067.inverseMaps 6) record067_frame006_indices (Fin.ofNat record067.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record067_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record067) (record067.maps 6) (record067.inverseMaps 6) record067_frame006_indices (Fin.ofNat record067.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record067_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record067) (record067.maps 6)
      (record067.inverseMaps 6) record067_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record067_frame006_links_0000 record067_frame006_links_0064)
theorem record067_frame006_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) : Supported record067 6 :=
  of_group record067 6 (smallEmbedding record067) (small_cells_exact record067 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record067_frame006_indices record067_frame006_graph record067_frame006_links
def record067_frame007_indices (c : Fin record067.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1004.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1004.count (({ width := 9, code := 0x97ca24b158742e12fd7dbdde8f0773b1d6e973b95c6de63b017abb57ab552a6512813c9d4da652e954821cf6793a9c8dc6c351a4ce6531984b85329144a04f26930964a2491482401f8f4783b1d0e46632188bc5c2d160ac5228138984a1f0f074361a0c8602e160a83c1c0d058281208038180a04018080200 } : Fields).get c.val)
theorem record067_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1004.graphBitCheck record067.data.requiredEdges q = true := by decide +kernel
theorem record067_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record067) (record067.maps 7) (record067.inverseMaps 7) record067_frame007_indices (Fin.ofNat record067.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record067_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record067) (record067.maps 7) (record067.inverseMaps 7) record067_frame007_indices (Fin.ofNat record067.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record067_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record067) (record067.maps 7)
      (record067.inverseMaps 7) record067_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record067_frame007_links_0000 record067_frame007_links_0064)
theorem record067_frame007_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) : Supported record067 7 :=
  of_group record067 7 (smallEmbedding record067) (small_cells_exact record067 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1004
    Papers.RationalityTen.SharedFrameCatalogue.group1004_facts record067_frame007_indices record067_frame007_graph record067_frame007_links
theorem record067_frames_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) :
    ∀ f : Fin record067.g, Supported record067 f :=
  (Fin.cases (record067_frame000_supported hcells) (Fin.cases (record067_frame001_supported hcells) (Fin.cases (record067_frame002_supported hcells) (Fin.cases (record067_frame003_supported hcells) (Fin.cases (record067_frame004_supported hcells) (Fin.cases (record067_frame005_supported hcells) (Fin.cases (record067_frame006_supported hcells) (Fin.cases (record067_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record067_frames_supported
theorem record068_frame000_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) :
    Supported record068 0 :=
  of_identity record068 0 (by decide +kernel)
def record068_frame001_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x186e871416a060eb47423961c94d6462a30c973cb705b12a014c4a464d22580e6c71837b1b60d886723251898c105e82d315c09f44d625911a08883f81e00e186e43281830b9853c28013008804041aa09204882040ae056024810808204001b80d8052028013807c03c01d00d804402000f00700300140090028010006000 } : Fields).get c.val)
theorem record068_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record068_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record068) (record068.maps 1)
      (record068.inverseMaps 1) record068_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record068_frame001_links_0000 record068_frame001_links_0064)
theorem record068_frame001_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) : Supported record068 1 :=
  of_group record068 1 (smallEmbedding record068) (small_cells_exact record068 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record068_frame001_indices record068_frame001_graph record068_frame001_links
theorem record068_frames_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) :
    ∀ f : Fin record068.g, Supported record068 f :=
  (Fin.cases (record068_frame000_supported hcells) (Fin.cases (record068_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record068_frames_supported
theorem record069_frame000_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSmall.cells (embedding record069 c)) :
    Supported record069 0 :=
  of_identity record069 0 (by decide +kernel)
theorem record069_frames_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSmall.cells (embedding record069 c)) :
    ∀ f : Fin record069.g, Supported record069 f :=
  (Fin.cases (record069_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record069_frames_supported
theorem record070_frame000_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) :
    Supported record070 0 :=
  of_identity record070 0 (by decide +kernel)
def record070_frame001_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1b5ad3b689b3fd896c375a42b5955ca9a4f32749292942485240d1f85722b094f4a304da26512f493447723390f085641c1f78f7c6062f21670aa44d625b12708ac4101f80e686f035a1800b8055421e10307e03a01c40dc04e026c12609204881e40f007003781b8060026012008c04001f00f006c02200f007002c014009 } : Fields).get c.val)
theorem record070_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record070) (record070.maps 1) (record070.inverseMaps 1) record070_frame001_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record070) (record070.maps 1) (record070.inverseMaps 1) record070_frame001_indices (Fin.ofNat record070.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record070_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record070) (record070.maps 1)
      (record070.inverseMaps 1) record070_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record070_frame001_links_0000 record070_frame001_links_0064)
theorem record070_frame001_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 1 :=
  of_group record070 1 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record070_frame001_indices record070_frame001_graph record070_frame001_links
theorem record070_frames_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) :
    ∀ f : Fin record070.g, Supported record070 f :=
  (Fin.cases (record070_frame000_supported hcells) (Fin.cases (record070_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record070_frames_supported
theorem record071_frame000_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) :
    Supported record071 0 :=
  of_identity record071 0 (by decide +kernel)
def record071_frame001_indices (c : Fin record071.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x68166b65e65a5d25b35ac5a75584ff4b149f4994944903a83a239c39834333533130f2f52e62d82c02ac29a29729423722921e1ef1df1d21b919818f1811751711370fe0f60e70d40cc0c40a009108b08a08607506c06a06705e05d05a05805405305204704003e03603503403102802702602402202101e01d01c01301201000f00d00b009008007004003002001000 } : Fields).get c.val)
theorem record071_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record071.data.requiredEdges q = true := by decide +kernel
theorem record071_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record071) (record071.maps 1) (record071.inverseMaps 1) record071_frame001_indices (Fin.ofNat record071.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record071_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record071) (record071.maps 1) (record071.inverseMaps 1) record071_frame001_indices (Fin.ofNat record071.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record071_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record071) (record071.maps 1)
      (record071.inverseMaps 1) record071_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record071_frame001_links_0000 record071_frame001_links_0064)
theorem record071_frame001_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) : Supported record071 1 :=
  of_group record071 1 (smallEmbedding record071) (small_cells_exact record071 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record071_frame001_indices record071_frame001_graph record071_frame001_links
def record071_frame002_indices (c : Fin record071.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0xb21596a954c9d32e255ca58ef0e9ff3ed7c8f79ecb2e646c5d87ad859cb2152a8c50e9c92ca4745688d0d9dd3a6724d19913185c0ab94c2724a0900f81b6354658c01762d84b8881001fc3d86f0ce1943105a0b21582a05009e1382384107e0d81a8340620a0138260480881081e03a0700981202003c0680b0120200380400600800800 } : Fields).get c.val)
theorem record071_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record071.data.requiredEdges q = true := by decide +kernel
theorem record071_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record071) (record071.maps 2) (record071.inverseMaps 2) record071_frame002_indices (Fin.ofNat record071.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record071_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record071) (record071.maps 2) (record071.inverseMaps 2) record071_frame002_indices (Fin.ofNat record071.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record071_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record071) (record071.maps 2)
      (record071.inverseMaps 2) record071_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record071_frame002_links_0000 record071_frame002_links_0064)
theorem record071_frame002_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) : Supported record071 2 :=
  of_group record071 2 (smallEmbedding record071) (small_cells_exact record071 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record071_frame002_indices record071_frame002_graph record071_frame002_links
def record071_frame003_indices (c : Fin record071.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x826fe1f6be6744e0dbdb756b2cb181af75e4bb97424b48c9011da0d41081cf81de3ae724dc9ac336660ca1612b65489b92a24a468840ff1e83ac738c71702cc568a514627c410780e41c4370660c21802e8580ae1502904e09a1302083b0720c81883005a098128240440800f81c0360680981202003c0680b0120200380400600800800 } : Fields).get c.val)
theorem record071_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record071.data.requiredEdges q = true := by decide +kernel
theorem record071_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record071) (record071.maps 3) (record071.inverseMaps 3) record071_frame003_indices (Fin.ofNat record071.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record071_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record071) (record071.maps 3) (record071.inverseMaps 3) record071_frame003_indices (Fin.ofNat record071.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record071_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record071) (record071.maps 3)
      (record071.inverseMaps 3) record071_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record071_frame003_links_0000 record071_frame003_links_0064)
theorem record071_frame003_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) : Supported record071 3 :=
  of_group record071 3 (smallEmbedding record071) (small_cells_exact record071 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record071_frame003_indices record071_frame003_graph record071_frame003_links
theorem record071_frames_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) :
    ∀ f : Fin record071.g, Supported record071 f :=
  (Fin.cases (record071_frame000_supported hcells) (Fin.cases (record071_frame001_supported hcells) (Fin.cases (record071_frame002_supported hcells) (Fin.cases (record071_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record071_frames_supported
theorem record072_frame000_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) :
    Supported record072 0 :=
  of_identity record072 0 (by decide +kernel)
def record072_frame001_indices (c : Fin record072.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19c0cca560aa2549aa23508250d1f48c145622690607e93eb1f1cf6e58d2aa94649de4dc2078f1871a3781b30bf056a2a21498a0c3f41f30f287783ac1d00e387083681a60cf86282f61750af854828813d097848423210c07b03c012408d04602040de06d03501a40c005d02d81680ae05602a815009203701a80c8062028012808c04401f00f007403801b009804402000e0068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record072_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record072.data.requiredEdges q = true := by decide +kernel
theorem record072_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record072) (record072.maps 1) (record072.inverseMaps 1) record072_frame001_indices (Fin.ofNat record072.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record072_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record072) (record072.maps 1) (record072.inverseMaps 1) record072_frame001_indices (Fin.ofNat record072.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record072_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record072) (record072.maps 1)
      (record072.inverseMaps 1) record072_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record072_frame001_links_0000 record072_frame001_links_0064)
theorem record072_frame001_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) : Supported record072 1 :=
  of_group record072 1 (smallEmbedding record072) (small_cells_exact record072 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record072_frame001_indices record072_frame001_graph record072_frame001_links
def record072_frame002_indices (c : Fin record072.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x65064a5d25bd59f58957e5335184f84ea4df4bb4a249b4954903f83e63ca3b13a535533c31f30e3022e02c62c02bb2b722721d2081fb1ef1e41da1d51c41b11a418617216814a13e12c12110c0f60ec0d80bc0b808608308207b06c06a06706605e05b05905805505405305204703603403103002802502302201f01e01d01c01b01301101000e00d00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record072_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record072.data.requiredEdges q = true := by decide +kernel
theorem record072_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record072) (record072.maps 2) (record072.inverseMaps 2) record072_frame002_indices (Fin.ofNat record072.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record072_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record072) (record072.maps 2) (record072.inverseMaps 2) record072_frame002_indices (Fin.ofNat record072.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record072_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record072) (record072.maps 2)
      (record072.inverseMaps 2) record072_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record072_frame002_links_0000 record072_frame002_links_0064)
theorem record072_frame002_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) : Supported record072 2 :=
  of_group record072 2 (smallEmbedding record072) (small_cells_exact record072 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record072_frame002_indices record072_frame002_graph record072_frame002_links
def record072_frame003_indices (c : Fin record072.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x24cc958910f215c1b826f55dfba3734e41b4b4b688cf99d2dc598ad150a974c29411e234458818f41e03b675cca98f30a5fcbd1782e45b0b01542984d89392121c4087a8f01c0348650bd1542904007b0f41d4328630c21802b8540a41442704d09812c230350660c01782704a08c1101f03c0740e01b0260440800e01a0300500901001c0280400600800800 } : Fields).get c.val)
theorem record072_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record072.data.requiredEdges q = true := by decide +kernel
theorem record072_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record072) (record072.maps 3) (record072.inverseMaps 3) record072_frame003_indices (Fin.ofNat record072.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record072_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record072) (record072.maps 3) (record072.inverseMaps 3) record072_frame003_indices (Fin.ofNat record072.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record072_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record072) (record072.maps 3)
      (record072.inverseMaps 3) record072_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record072_frame003_links_0000 record072_frame003_links_0064)
theorem record072_frame003_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) : Supported record072 3 :=
  of_group record072 3 (smallEmbedding record072) (small_cells_exact record072 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record072_frame003_indices record072_frame003_graph record072_frame003_links
theorem record072_frames_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) :
    ∀ f : Fin record072.g, Supported record072 f :=
  (Fin.cases (record072_frame000_supported hcells) (Fin.cases (record072_frame001_supported hcells) (Fin.cases (record072_frame002_supported hcells) (Fin.cases (record072_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record072_frames_supported
theorem record073_frame000_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSmall.cells (embedding record073 c)) :
    Supported record073 0 :=
  of_identity record073 0 (by decide +kernel)
def record073_frame001_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xc4f61e27a93ae9824b7a56929694549ea4c124491b486a3fd1ee8f14751954c8257229e94149c04d125e92688ee467221908c8224021f88c0c59c296138898849c22b10407e03a81b40d1064c30414f0a40504274133096049422e10a08203bc12408d04601bc0d406903401800bc05b02d01600ae05602a815006e03201880c0050026011808804001f00f007403801b009804401c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record073_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record073) (record073.maps 1) (record073.inverseMaps 1) record073_frame001_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record073) (record073.maps 1) (record073.inverseMaps 1) record073_frame001_indices (Fin.ofNat record073.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record073_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record073) (record073.maps 1)
      (record073.inverseMaps 1) record073_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record073_frame001_links_0000 record073_frame001_links_0064)
theorem record073_frame001_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSmall.cells (embedding record073 c)) : Supported record073 1 :=
  of_group record073 1 (smallEmbedding record073) (small_cells_exact record073 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record073_frame001_indices record073_frame001_graph record073_frame001_links
def record073_frame002_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xce0665288d420944486235115889a443a1910848304069fa4fb07c83db93bc9b84101ec0e806f03661a98cc061c2fc16c8ad454829414188343f41e50eb07403901bb0d6869833018a0c105f02ea1590a9052c28813d09b04bc24211308603dc12408d04601bc0d406903401800bc05b02d01600ae05602a815006e03201880c0050026011808804001f00f007403801b009804401c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record073_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record073) (record073.maps 2) (record073.inverseMaps 2) record073_frame002_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record073) (record073.maps 2) (record073.inverseMaps 2) record073_frame002_indices (Fin.ofNat record073.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record073_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record073) (record073.maps 2)
      (record073.inverseMaps 2) record073_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record073_frame002_links_0000 record073_frame002_links_0064)
theorem record073_frame002_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSmall.cells (embedding record073 c)) : Supported record073 2 :=
  of_group record073 2 (smallEmbedding record073) (small_cells_exact record073 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record073_frame002_indices record073_frame002_graph record073_frame002_links
def record073_frame003_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x342678a954fa794e49a5312604b895d28a4e4909091f23c47267ccc9732d858cae15a2ac544a59482844f09c136266428818fa1e63c4768e81c437c6c8d319e334650c017e2f85e8bc1762e85c0b616a2c8470891101b4340670cc1782e0590b01582a8540a61481b8320620c0140260460881001f03c0740e01b0260440700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record073_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record073) (record073.maps 3) (record073.inverseMaps 3) record073_frame003_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record073) (record073.maps 3) (record073.inverseMaps 3) record073_frame003_indices (Fin.ofNat record073.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record073_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record073) (record073.maps 3)
      (record073.inverseMaps 3) record073_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record073_frame003_links_0000 record073_frame003_links_0064)
theorem record073_frame003_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSmall.cells (embedding record073 c)) : Supported record073 3 :=
  of_group record073 3 (smallEmbedding record073) (small_cells_exact record073 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record073_frame003_indices record073_frame003_graph record073_frame003_links
def record073_frame004_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1111.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1111.count (({ width := 10, code := 0x2509320d825e677dd673dcd725c56fdbc6d9b06b1aa69d655853e4dd2e49d254851d45d1443908411023fcd9348c9308c02f0b82c8af2a4a327c9d2689023c8e2348c22c8a22086214821bc6b1a85d1645815c4f1344a1244711845110430d8320c4300a02608c220801f0781d0701b04c110380d02c0a0240801c060140400c0200400 } : Fields).get c.val)
theorem record073_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record073) (record073.maps 4) (record073.inverseMaps 4) record073_frame004_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record073) (record073.maps 4) (record073.inverseMaps 4) record073_frame004_indices (Fin.ofNat record073.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record073_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record073) (record073.maps 4)
      (record073.inverseMaps 4) record073_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record073_frame004_links_0000 record073_frame004_links_0064)
theorem record073_frame004_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSmall.cells (embedding record073 c)) : Supported record073 4 :=
  of_group record073 4 (smallEmbedding record073) (small_cells_exact record073 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1111
    Papers.RationalityTen.SharedFrameCatalogue.group1111_facts record073_frame004_indices record073_frame004_graph record073_frame004_links
theorem record073_frames_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSmall.cells (embedding record073 c)) :
    ∀ f : Fin record073.g, Supported record073 f :=
  (Fin.cases (record073_frame000_supported hcells) (Fin.cases (record073_frame001_supported hcells) (Fin.cases (record073_frame002_supported hcells) (Fin.cases (record073_frame003_supported hcells) (Fin.cases (record073_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record073_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009
