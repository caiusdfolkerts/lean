module
prelude
public import GraphInputsRow29Part00193Data
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
public import SharedFrameGroups075Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x7b47a977c77474b7446d66cd6c369a68a66764563f6336245e85df5b459a58e58857154652d52b5254b147346f4354244163fe3f03ba3b637c36535d33d33731d3153052ff2f92f429324423d2322292162091e11d51d01c21b01aa19418617316a14d14113512e1201131000ea0df0d60ca0c60c10b50a908d08c07d07c07206305705404b04504003f03702801e01d01901000f00e00b009004003000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x7647366ff6d568567a66e63c63662a6035f45e65ae56c56055552e5244f84ec4da4be4b049b48748145944c44241640e4043df3d23c438b35734e3483293233022f92ed2d82cb2bd2af2ab28b27f26e26d24723b22922820c2032011f81e61e01ce1c61b11af19f19d19218417d15d15c14b13f12611a1000ef0ed0de0dd0d20c70ba0b00af0a407907307107006c06a06906005905705305204904304104003b03903702e02502301f01e } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x2afd4ea79492764e19b92f25a4ad9131d63644a8510920ec0980efc1f53e07a8f31e03aa74edd1b3b62676cc9963075e6ba560a9e532a553fa7d4d49912e25449890d1822d41a818fb1f53ba738e01bd34a66ccc99230e5f8b89682ba570a894f2924c09390f21c4207f0f41d2360658c917c2f45c0b214c27c4e8980fe1e83b8760e21b8368640ba16c2b85609a118218420780e41b82e04a08c0f81e } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0407.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0407.count (({ width := 8, code := 0xe2e1e0dfdad9d8d7d6d5d2d1cecac9c8c7c5c4c1c0bfbdbbb9b5b4b3b2b1b0afaeabaaa7a3a2a1a09e9d9a99989694928e8d8c8a878684827f7e7c7b7a78767471706e6d6b6a6864625f5e5c5a575552504f4d4c4a48464544423b3a3938373635312e2d2b2a272625242322211d1a191716 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0407.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0407.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0407.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0407.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0407
    Papers.RationalityTen.SharedFrameCatalogue.group0407_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0326.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0326.count (({ width := 9, code := 0x1c6e270b81bcdd6e369b2d86ab51a6d167b3998cb6532590c662b1186c260afd7cbd5dae972b65aad164b057ab558ab552a54ea652a9146a250a7932984b24d1e8e452210e8541a00f87b3b9d8e672381b0d4663298cc05c2d15ca8532813c9a4b241188a431d8e872381b8d86a33190c45e2e138984a2411888421f0f074361a } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0326.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0326.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0326.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0326.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record001_frame004_links_0000 record001_frame004_links_0064)
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0326
    Papers.RationalityTen.SharedFrameCatalogue.group0326_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0246.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0246.count (({ width := 9, code := 0x2c963b1586b559ac54aa14ea3d12853c9b4d2652e96cae55299449a492190466311788c3e1b0681c05f6f579bc5daec753a5d0e772b8dc0df6732986c25e2dd62af552a550a650a7930954823d168a44200f871381b4d4653096cae56291449c4c2512490451f0f0763a1c8dc6c34190c45e2e150a04e261288c44200f074361a } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0246.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record001_frame005_links_0000 record001_frame005_links_0064)
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0246
    Papers.RationalityTen.SharedFrameCatalogue.group0246_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0165.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0165.count (({ width := 8, code := 0xa7a6a5a4a3a2a1a09f9e9c9b9a9897969594939291908f8e8d8c8b8a89888786858382817f7e7d7c7b7a7978777675747372716f6c6b6967646361605f5d5b5956555352504f4d4b49464543413f3d3b3938363533312f2e2d2b292827262524232221201f1e1d1c1b1a1918171615141312 } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0165.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0165.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0165.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0165.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record001_frame006_links_0000 record001_frame006_links_0064)
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0165
    Papers.RationalityTen.SharedFrameCatalogue.group0165_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
def record001_frame007_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0117.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0117.count (({ width := 9, code := 0x3037fbf5f2ed72b8daed568b0d7ab958a9d46a14ca5d1e8d44a15027d3b9d4d66330954a64f208ec6e2f128843e170a8341607017fbf5f4f974391badc6ab398cc55faf176b758ab94ea24e26d30974aa35127e3e9e8ee72371a0cc653017cb8592a14ca44f241148843210fc7a3b1c8dc6a34180b4582b1509c4a231087c3a1c } : Fields).get c.val)
theorem record001_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0117.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record001_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record001) (record001.maps 7)
      (record001.inverseMaps 7) record001_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record001_frame007_links_0000 record001_frame007_links_0064)
theorem record001_frame007_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 7 :=
  of_group record001 7 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0117
    Papers.RationalityTen.SharedFrameCatalogue.group0117_facts record001_frame007_indices record001_frame007_graph record001_frame007_links
def record001_frame008_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1f98ed5702358d80ebd85e32ca9622b00542292142698c48e24251f48bd457218d09e8304071fdcfb67a53cb9b4cd486922fb1774b9855028a137c8b03e81ea8f1871237a1978c6c5f82da1618a9c4e226311d08cc45022710808103ee1f40f1076c3b21d10e186f43621a70ce066831c18b0c305c42d414f0a6851427c132095847022010d08104001f20f1073037c1ba0d604281f80f607a03a01c40de06602e816c0ae056026811808604201e00e406e02e012808c03e01e } : Fields).get c.val)
theorem record001_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record001_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 8)
      (record001.inverseMaps 8) record001_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record001_frame008_links_0000 record001_frame008_links_0064)
theorem record001_frame008_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 8 :=
  of_group record001 8 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame008_indices record001_frame008_graph record001_frame008_links
def record001_frame009_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x22e44c871099fbbf27d4f49e73c6758e81c83776bed65abb45682cb593b1e624c1d7f2ec5d0b41652c2552a954ea854f29a5282364608ad0b2133fe7e4f99e63be75ce29c13666b4d21a3326628bf97e2d658cb095a2a052ca01382584a88e91b22c424828f51e83bc740dd1aa3245f8bd1662c8560a61382584a88f0e41b83606b0ce1943185a0a41402604b08a1041f83e0720dc1b02d04a08c0f81e } : Fields).get c.val)
theorem record001_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record001_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record001) (record001.maps 9)
      (record001.inverseMaps 9) record001_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record001_frame009_links_0000 record001_frame009_links_0064)
theorem record001_frame009_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 9 :=
  of_group record001 9 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record001_frame009_indices record001_frame009_graph record001_frame009_links
def record001_frame010_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x8498157d77ab7367277216f36ec6e86bc69c68564c61860e6025db5d35a459d58557556b5595315284ec4db4d649848a48144b42a40c3d43ab3a73a538938235834c33b3263163022e52de2b42ab29729627526124d24b22f22622321a20b2001ed1e01cf1ce1bf1bd1b419118516015f15614a13812b1131021000f00ef0e60de0cf0c60c30bb08007a07707607106e06c06305a05805405304b04504204103b03803602d02502301f01e } : Fields).get c.val)
theorem record001_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record001_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record001) (record001.maps 10)
      (record001.inverseMaps 10) record001_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record001_frame010_links_0000 record001_frame010_links_0064)
theorem record001_frame010_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 10 :=
  of_group record001 10 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record001_frame010_indices record001_frame010_graph record001_frame010_links
def record001_frame011_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0406.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0406.count (({ width := 8, code := 0xa7a6a5a4a3a2a1a09f9e9c9b9a9897969594939291908f8e8d8c8b8a89888786858382817f7e7d7c7b7a7978777675747372716f6c6b6967646361605f5d5b5956555352504f4d4b49464543413f3d3b3938363533312f2e2d2b292827262524232221201f1e1d1c1b1a1918171615141312 } : Fields).get c.val)
theorem record001_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0406.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0406.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0406.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record001_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0406.localPairCheck (smallEmbedding record001) (record001.maps 11)
      (record001.inverseMaps 11) record001_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record001_frame011_links_0000 record001_frame011_links_0064)
theorem record001_frame011_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 11 :=
  of_group record001 11 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0406
    Papers.RationalityTen.SharedFrameCatalogue.group0406_facts record001_frame011_indices record001_frame011_graph record001_frame011_links
def record001_frame012_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0325.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0325.count (({ width := 8, code := 0xa7a6a5a4a3a2a1a09f9e9c9b9a9897969594939291908f8e8d8c8b8a89888786858382817f7e7d7c7b7a7978777675747372716f6c6b6967646361605f5d5b5956555352504f4d4b49464543413f3d3b3938363533312f2e2d2b292827262524232221201f1e1d1c1b1a1918171615141312 } : Fields).get c.val)
theorem record001_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0325.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0325.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0325.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record001_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0325.localPairCheck (smallEmbedding record001) (record001.maps 12)
      (record001.inverseMaps 12) record001_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record001_frame012_links_0000 record001_frame012_links_0064)
theorem record001_frame012_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 12 :=
  of_group record001 12 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0325
    Papers.RationalityTen.SharedFrameCatalogue.group0325_facts record001_frame012_indices record001_frame012_graph record001_frame012_links
def record001_frame013_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0245.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0245.count (({ width := 10, code := 0x7fdfb7e1f67b1e97a1df76dd9735c7711b96c1ad6a9a36899c66997659926418b625825f97c5c56e5ad5f55d55531404f93b4cd324bd2e4b12a4a1244811d4410c40d023ecf53b8ec390e1380dd35cd3330c8304c02e4b82d4a928c952509123487204781c4701a4681906117059160541184410c421043f0f83b0e0370cc320b82c0ac2a09c25090210781d06c1a } : Fields).get c.val)
theorem record001_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record001) (record001.maps 13) (record001.inverseMaps 13) record001_frame013_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record001) (record001.maps 13) (record001.inverseMaps 13) record001_frame013_indices (Fin.ofNat record001.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record001_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record001) (record001.maps 13)
      (record001.inverseMaps 13) record001_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record001_frame013_links_0000 record001_frame013_links_0064)
theorem record001_frame013_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 13 :=
  of_group record001 13 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0245
    Papers.RationalityTen.SharedFrameCatalogue.group0245_facts record001_frame013_indices record001_frame013_graph record001_frame013_links
def record001_frame014_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0164.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0164.count (({ width := 8, code := 0x9f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6b6968666462615f5e5d5b5957555452514f4e4c4a48464543413f3d3b3938363533312f2e2d2b292827262524232221201f1e1d1c1b1a1918171615141312 } : Fields).get c.val)
theorem record001_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0164.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0164.localPairCheck (smallEmbedding record001) (record001.maps 14) (record001.inverseMaps 14) record001_frame014_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0164.localPairCheck (smallEmbedding record001) (record001.maps 14) (record001.inverseMaps 14) record001_frame014_indices (Fin.ofNat record001.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record001_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0164.localPairCheck (smallEmbedding record001) (record001.maps 14)
      (record001.inverseMaps 14) record001_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record001_frame014_links_0000 record001_frame014_links_0064)
theorem record001_frame014_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 14 :=
  of_group record001 14 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0164
    Papers.RationalityTen.SharedFrameCatalogue.group0164_facts record001_frame014_indices record001_frame014_graph record001_frame014_links
def record001_frame015_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0116.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0116.count (({ width := 9, code := 0x3439fce66b258ec6e1f0982bd5deeb70b5da2cf62b0d6eb356aa5469f4ba55167f3d9acce61289248a39168a44e1b0c8441e0b0380bfdf8fb773a9c6e26eb5d9ece63b0d84be5cad55ca951a893c9d4da491a8441a00fa78399b0d26831184bc5b2a94ca44f2310c8441200f476391b8d46632170ac54291409446210f874361a } : Fields).get c.val)
theorem record001_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0116.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0116.localPairCheck (smallEmbedding record001) (record001.maps 15) (record001.inverseMaps 15) record001_frame015_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0116.localPairCheck (smallEmbedding record001) (record001.maps 15) (record001.inverseMaps 15) record001_frame015_indices (Fin.ofNat record001.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record001_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0116.localPairCheck (smallEmbedding record001) (record001.maps 15)
      (record001.inverseMaps 15) record001_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record001_frame015_links_0000 record001_frame015_links_0064)
theorem record001_frame015_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 15 :=
  of_group record001 15 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0116
    Papers.RationalityTen.SharedFrameCatalogue.group0116_facts record001_frame015_indices record001_frame015_graph record001_frame015_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (Fin.cases (record001_frame006_supported hcells) (Fin.cases (record001_frame007_supported hcells) (Fin.cases (record001_frame008_supported hcells) (Fin.cases (record001_frame009_supported hcells) (Fin.cases (record001_frame010_supported hcells) (Fin.cases (record001_frame011_supported hcells) (Fin.cases (record001_frame012_supported hcells) (Fin.cases (record001_frame013_supported hcells) (Fin.cases (record001_frame014_supported hcells) (Fin.cases (record001_frame015_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))
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
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1c04ce35fb2c41608a9e543293d44c98e4c024251ce8d6455a1990147fa3f49ed8f2a6c22ee1740ad455228d93c88b444c1ea8ecc7443771990b5858c2b5141098447223211108204001ec0f187543721b30d6867832018a0c105f02e81670a8852827a13509704842320fe07783a411a08503f01c00d406002e016c0ac05502a013408c03801900a004802300f007403801900c0054028013008803c01c00b004802000e0040018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record003_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193
