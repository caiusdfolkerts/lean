module
prelude
public import GraphInputsRow29Part00284Data
public import RawFrameSupport
public import SharedFrameGroups011Checked
public import SharedFrameGroups013Checked
public import SharedFrameGroups015Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups019Checked
public import SharedFrameGroups020Checked
public import SharedFrameGroups021Checked
public import SharedFrameGroups024Checked
public import SharedFrameGroups025Checked
public import SharedFrameGroups026Checked
public import SharedFrameGroups028Checked
public import SharedFrameGroups029Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups045Checked
public import SharedFrameGroups046Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups060Checked
public import SharedFrameGroups061Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups064Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups104Checked
public import SharedFrameGroups105Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1c76d7b69b34b5a30d11685b40d9f8cf66772c8162aade5652a8d51ea6c4da26a52e495e49ba48d2008ef47423851b48d3465231517c8b545822ad1488964479df0daa6c43489a04ce265f32618e0c505802b794f0a5851c28513dc9c64d326413049744b3256929093e498247922890247b23b91bc8d23911c10d1065e3071798b285722a914c8a284f425b12608b443220a0f707803ac1c60db069c32e1780b4852826c12708583f41ee0f007483881b60d503901bc0c606001d00dc06a03401900c4056028013009404602200b004c01800b00500240100060028010006002 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record000_frame001_links_0000 (interval_append _ 64 128 138 record000_frame001_links_0064 record000_frame001_links_0128))
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1998c5b5fd2fb5768ba45ca2e016e0b605a8a9694a0a1450227913a89b649fa4d51e28e045d22a510e878430212506a8234062004fde7d83e99f34f6e7883bb1b04ca664430597f0bd65de2e796f8b6a54929d94089e84e626b93249764b22541258908474233914889843f215109c8284041fd0f947b23611a98c5c6102ea16d8b0056229d14509e04da25212388c444020f0f887903ac1c60da86a03381850bc85902a6140090845420e0f907483781a80c903901bc0c606001d00dc06a03401900c4056028013009404602200b004c01800b00500240100060028010006002 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record000_frame002_links_0000 (interval_append _ 64 128 138 record000_frame002_links_0064 record000_frame002_links_0128))
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x6e86a968768166f66866165965264b6445bb5b459558c57656b5575195124f34e84d44cb4b54ad4a74a149b49448a48748047647447046a45c4563f13ac3a237d37436935d35434b3432fd2f32cd2c42bb2af2a629b29428e28828227b27526b26826225825724f24924523b2351ee1ea1ca1c21af1a719618f18717c17617216816315815014613813112d12511a11210d1020fe0f60ee0e40d30d00cc0c70c20be0bc0bb07006d06105e03803603403303103002b02802602502302201601300c00b00a009008006005004003002 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record000_frame003_links_0000 (interval_append _ 64 128 138 record000_frame003_links_0064 record000_frame003_links_0128))
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb19ad3a9da89a70a63a57a43a36a2aa1494693f9239168f88eb8c984e84782180e7e67d57ad79c79378377276374b73e72a70e7036f66e46bf6ab63c5e05d85bc5ae59c58d58056f5625024fa4da4cc4bc4ac49e48f4804764704634554474314284183ff3f83e13d33ca3b33a333832e3082f82dc2d02af2a029628627526724923921a2051f61d71c91c21ba1ae1a01911731651461331271070fa0f10e60d90cc0be0b507006d06105e03a03703503403203102b02802602502302201601300c00b00a009008006005004003002 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record000_frame004_links_0000 (interval_append _ 64 128 138 record000_frame004_links_0064 record000_frame004_links_0128))
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x6a668a67566e66766466165b65765364b5da5d55c35b75a459858253b53652451e5074fd4e34d64d14cc4c64c14ba4b64b04a84a349f49948d4864443ff3f93e63dc3d33ca3bd3b13a535c35634333c33032731f30e3022fa2f52f12ec2e62df2da2d42cc2c72bf2ba2b82b22ad24e24a22a22020b1fe1e51db1d51cc1c41b91a419918617817015b15114b14613e13412c11510c0f60ea0e10cb0c10bb0b70b20ab0a409f06f06c06105e03903603403303103002b02802602502302201601300c00b00a009008006005004003002 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record000_frame005_links_0000 (interval_append _ 64 128 138 record000_frame005_links_0064 record000_frame005_links_0128))
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
def record000_frame006_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0606.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0606.count (({ width := 11, code := 0x29dd2fa4347689d0fa1d41a814fe9ed2ca5849e9332424547e8af1521ac2b839056003f97e0f95ee3d378af09dd3a7746e7dcb3816ecd2d92b23628c3984b035fcbd977ad159cad956aa653ca61462855029f13926a4c094d2824c4728d91522143c841041e33c0718df9af350658c81892fc5e0b81622bc538a213d2624ac9311f22842c828f91e83946d8d217c2d4560a4136248458860c217c2a05206e0d4198320600bc1502804c0941182202c04c0600b0140240400600a01001802 } : Fields).get c.val)
theorem record000_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record000_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record000) (record000.maps 6)
      (record000.inverseMaps 6) record000_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record000_frame006_links_0000 (interval_append _ 64 128 138 record000_frame006_links_0064 record000_frame006_links_0128))
theorem record000_frame006_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 6 :=
  of_group record000 6 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0606
    Papers.RationalityTen.SharedFrameCatalogue.group0606_facts record000_frame006_indices record000_frame006_graph record000_frame006_links
def record000_frame007_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0600.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0600.count (({ width := 11, code := 0x20fc0f7f8fe9f9bf07dcfa5f33e37bce89d038f70adedba36a68cd119ab3064ac7987308606bf97caf35d6ba571ada5b2b55682c6582a5939a6f4bc95528a4b4888f91d217426804fd9f53e07b0f19de3b6760ea1cf392708e01bb3666c8d59a6348678cd1752e6588ad1502924e89b133254498909192244247f8fa1e03a4728e01b6348668c41842e0590a913c2604a09111a224428810ca1882c8570700d4198320600bc1502804c0941182202c04c0600b0140240400600a01001802 } : Fields).get c.val)
theorem record000_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0600.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record000_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record000) (record000.maps 7)
      (record000.inverseMaps 7) record000_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record000_frame007_links_0000 (interval_append _ 64 128 138 record000_frame007_links_0064 record000_frame007_links_0128))
theorem record000_frame007_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 7 :=
  of_group record000 7 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0600
    Papers.RationalityTen.SharedFrameCatalogue.group0600_facts record000_frame007_indices record000_frame007_graph record000_frame007_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (Fin.cases (record000_frame006_supported hcells) (Fin.cases (record000_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xcd3663b2f9968cab65131dd8d0c5962730fd870b555a2ace1658b1f58aaa6d516a7f53a29a14c09db4e3a6e135499b4c825fd2dc95c4a5a4e525a92748723dd1c28c2458227911a87b4389d08e5872536c1af8d666883359984b9e5b82d89634ae25662b09500a6252327c936c9a44c925792809243e31e38ef871836c1b10d646723251898b8c5842b8130091c4682220f0070c3721b10ca060c2e616a0a7850026012308581640b005702b010808204001480a004e02000f807802000f007002c0140090028010006000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x37edef78dd772dbf6ad9b62d7b5ad5b26c871cc6313c3ef3bc2edbaae7b92cbb1ac1af6b8ad2afaaea7a8e9fa6e98a36869fe789da739c66e9ae2286e1882e04805fb7ddf5741c9719c16f5bb6e1a968d9d65d936458d5f9775c1495013c4c129499234550f425003ecf936cd4340cc2f4b62ccb028c9d25c93220831f87b1c03a0e4380dc330c831098250901d0701b0400f0380b028090140400c00 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x5992c65626ac75572a9d4fea6853026d533098f4ae24e525a89e43da1c4eb674d3a11cdce5872537a1b8cdb06c935f1accd4e69934419f0cd66612f69778ba45c72dd96c8b5259a2c695f8ae256628c94209f24ea26d93487c23c51de8e306d83621a78b8c5842b81550a484fe26d12e891c4682220f0070c3721ad0cb06102e81680a7850026010e03d01e40f005802b8158086042020810004202000f8078028013009004001e00e006802c0140090028010006000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xc6b11c3700be6f6bb6e7b92c0adeb3a9e9fa6e739ba6b8a62588a1e86e1884e0f82e08812017fdfd7edf97ddf5765d5745ce729c7715c3705bf6f5bb66d9965d9564d915213f4ed304a526471003ecf93d0ea394e0368d4340cc2f4b62ccaf2909e26092220831f87113c4e134390e0370d0330c8310781d0701b050130481003c0e0340b028090140400c00 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xbb1b99b91b65b47b3ba78a6ca65a5ea4ca429d79c89c19b59a399490b8e98d98a98898798598458317f77d47c06bf6b16aa6a069568b66e66165964f64363962b61d61360b5fe5f357755d5505285115044dc4ce4bf49b48247746b45744843b3c03b13a539a38b37e36b35834d34133131f3082f62e62d42c72b72ad2a12932862322232132011cd1b51a819918317416714313312311610305805705604304204104002902802702001f01e01101000f00e00c00b00a009005004003000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x32f9956ca262cb0fd870b555a2ace1658b1f58aaa6d516a7f53a29a14c09b84cda6412b8939496a4391ee8e144f21ed0e275b3a69d08e6e72c3929bd0dc66d83649af8d666a734c9a20cf866b330973cb705b12c695c4acc540298948c9f24db269131895e4a024910107e43e31eb0f1c77c3ad1cd8e306f636c1b10d386723251898c185e82e31698b0857025912388d04441e00e186e43581940c185cc29e140098048c22005802b81580860420208100052028013808003e01e008804001e00e006002c0140090028010006000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x378dcb6fd8b5ad5b26c871cc6313c3ef3bc2edbaae7b92c1ae2b4a9e9fa6e8da1a7f9ce6e9ae298962287a1b8621383e0b82204805ff7f5fb7e5f77d5d0725c6705bd6eda968d9d65d936458a5f9775c15353949515404f1384d1304b5294991b4550f4250640d003f8fb3e4d8350d0330bd2d8b32b8a327497220831f87b1cc390e0370d0330c831098250901d0701b0441003c0e0300b028090140400c00 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x68ab41da02cd3663b2f9968cab6513159878c375aaad15670b2c58fac55592ab055429fd4d0a6052228b14329db4e3a6e135499b4c825fd2dc95c4a5a4e525a92748723dd1c289e43da1c50c6842416a060ec07523a39cf0e6272736d1b00d686883359984c9863731317c0bc05d42e496f4b665a92cd1634afc5712b31588a9e53d29793e49b64d226412a893848e1d68e6c71837b1b60d885c62c215c091c4682220fe87b83c01d10e186e42c814f0a004c022209304902440b005702b008003e01e008804001e00e00580280120060028010006000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record004_frame001_links_0000 (interval_append _ 64 128 132 record004_frame001_links_0064 record004_frame001_links_0128))
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xe1b82e037edef78dd772dbf61d6755c9b21c7318c4f0fc06fabdeedb9ee4b6ed7b4ecbb1ac1af6b8ad2afaaea7a8e9fa6e98a36869fe739ba6b99e58942488b228892218761a83205809fb7ddf57b1e7789da759d273dcb721c570dc16fdbd6edb96b9a86899764d916317b5d16d4e1344c12d4a526400fb3e4d4340cc314c12f4ba2d8b323c8820c7e1d05815c560e4380dc1d0701b0441003c0e02c0a024060140400c00 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record004_frame002_links_0000 (interval_append _ 64 128 132 record004_frame002_links_0064 record004_frame002_links_0128))
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x7ecbec1f38efd7743b45d7eeaa74b37e9b96db4606afe57c4bce5dc2e8d634af5570aa814eea62522a8c14369bc4d4265d3089714afa52526a921487a3f51d48de46622e114886442120c10468063fa1f88db26c53571a68d0866f2f31704b5a56c2a194b8a224fc27392208e846322810f48564152008fb47b63c91db0ea87303841b80cc061c2fc1778b485802ae10788204021fa0f987b03761ad0d305e82e616c0b005642a414b0a204f4230111085040c1ee09304902440b005702b008003e01e008804001e00e00580280120060028010006000 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record004_frame003_links_0000 (interval_append _ 64 128 132 record004_frame003_links_0064 record004_frame003_links_0128))
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
def record004_frame004_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x75a75675573973773373072c72a7066f66f266d66465b6516486426176035fb5e45d35ce5bd5b05a658157756e56655c55655054754053452d5265225155094ff4df4ce4c94c34ac4a249443342942041a4114083dc3cb3c13a839b39438337636934733d33332d32431c31630b3042fc2f52ec2e82db2cf2c32a229428f28927226425a1e11d91d01c81bf1b918817717014814013712d12812211c1161100f10ec0e60df0d508f08e08d05605505402001f01e01101000f00e00b00a009006005004003000 } : Fields).get c.val)
theorem record004_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record004_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 4)
      (record004.inverseMaps 4) record004_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record004_frame004_links_0000 (interval_append _ 64 128 132 record004_frame004_links_0064 record004_frame004_links_0128))
theorem record004_frame004_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 4 :=
  of_group record004 4 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record004_frame004_indices record004_frame004_graph record004_frame004_links
def record004_frame005_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0758.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0758.count (({ width := 9, code := 0xa250e8541a04fe7d3d9e4ee7539954a24d2591c8a391a8cc5a29138843a190782c0e05007fbf9f8fa7c3d9e8f276ba9cee27037dbcd96bb5596c963b1988c35eaed74b75aad162af56aa14ca451a85409f4ea6d32974aa4d1c8b4420d02803f9e8f0763499cca6431184ae5429930964a2411888432090072381b8d86831180bc4a24118602e160803c1c0d050241006028100600 } : Fields).get c.val)
theorem record004_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0758.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record004_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record004) (record004.maps 5)
      (record004.inverseMaps 5) record004_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record004_frame005_links_0000 (interval_append _ 64 128 132 record004_frame005_links_0064 record004_frame005_links_0128))
theorem record004_frame005_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 5 :=
  of_group record004 5 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0758
    Papers.RationalityTen.SharedFrameCatalogue.group0758_facts record004_frame005_indices record004_frame005_graph record004_frame005_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (Fin.cases (record004_frame004_supported hcells) (Fin.cases (record004_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x8088037fc7f77f07ea7e27dd7d67d17ca7c476a75c74f7146f96e26d26c36ae65c64d6386206055ee5c75bb5ad5a55a159759058958557b5745034f64ef4a548e4824674534463e43d03c339d38637a34833d33733232832131b31730d30630028222a22421c21520e1c61b81b119a19118517c13012711e1121090ff0f80da0d50c60c207106f06e05e05c05b05905705603803703602502402302001f01e01301200f00e00a009008004003001000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc7a63531718a0c4261cb0a983ac0f601afd57dcb435952c515a4ab95532a2d4e8a604e2a6a131e96b4a424b116088d438a16d0a083040da01cff07dc3e31d14e5e72636a9aecd646883359984ba45bb2d91628adc56527c936c9a44cc2569278920489237917c8a03bd1b10d5c67e32718a8ae0546291130092c4682220dc86c03341840ba058029c10b07f035c19207103781b80bc05c02d81640ae05601c00dc06c025012008c04001f00f004c02400f0070028012008002000c002000 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x4e39b9356694cd9913065dcb69672b2534668bb15a1cc2e85307a0a40b7acf31e1bb675ee99c337c6e4db1b43606b2d4da7b47680be9782ed586ae95caa6536a55292464848bd132223f87c4f61e93c0768ea1d1390708de17d2b6560a994d2904ac92921230444851041c83846d0d219c320620b416229c520680ce1982c8580ae1542985206e0d81a82504808c1001f03c04c0900f01c0280480800800c00800 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record005_frame003_links_0000 record005_frame003_links_0064)
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
def record005_frame004_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6d06c86c16b86af6a569b69368d68367766c6085fb5ed5c95b95a859c58b5795255124fe4ec4de4cb48f47846545545043842c42441d40e4053ca3bd3b438a37a36f35c34a3402e42d02c52ac29c29224a23522c22420d1ff1f31ee1df1d51cc19117116d16715f15b13d13512f1261201161110f60f10eb0e30de0d70d10bd0b70ab0a906a06806705705505405205004f03803703602502402302001f01e01301200f00e00a009008004003001000 } : Fields).get c.val)
theorem record005_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record005_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record005) (record005.maps 4)
      (record005.inverseMaps 4) record005_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record005_frame004_links_0000 record005_frame004_links_0064)
theorem record005_frame004_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 4 :=
  of_group record005 4 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record005_frame004_indices record005_frame004_graph record005_frame004_links
def record005_frame005_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x5039fd3e67b4f29e13ae73ce49bf3726c4a69372524247d8ed1ba32c5a85b08e0c40c7f6fade13b6758ea1d1b9c72ae39c437e6ecd1da033b630c2981af55dab95572a553ea5147a884c496129a4d4848f11a22e45288d0e1dd3686b8d39a133a5d4b81662a252c9f1362084007b0ea1c43606a8b515e2884d0670cc1942a8530a41402784e0680cc190240460881001f03c04c0900f01c0280480800800c00800 } : Fields).get c.val)
theorem record005_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record005_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record005) (record005.maps 5)
      (record005.inverseMaps 5) record005_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record005_frame005_links_0000 record005_frame005_links_0064)
theorem record005_frame005_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 5 :=
  of_group record005 5 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record005_frame005_indices record005_frame005_graph record005_frame005_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (Fin.cases (record005_frame004_supported hcells) (Fin.cases (record005_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6ff6f06e86cf6b66ad69a6806746085fb5ed5cc5bc5ab59958857650f4de4bd4b64ac49c47845744e43e42e41440d3ca3bd3b438d37d37235934733d2cd29c28a27827326323522220f2051f51e51d419117116d16715f15b13d13913312b12712211c0ed0e70e40d70d10ce0c50bd0b70b40ac08208107f06606406305b05805705405204f04d03403303202902702502302001e01c01301200f00e00a009007003002001000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x18cf12e1ec057b2f15d4b816e6b4d5daa54ce92516a0d3e276ca99131da38c6b8c713a1d43585f09e0cc13786ee1d937d6dcda1a633e66cb4d54297514a1d3da5b4a09091e232452874e69a233063cc217c2ae544a293b2664a8920ec1ce3846a0d01963045c8b61642a84007f0fa198320630c017c2f05b0b21582a0340660c81482704a08c1001e03804c0900f01c0280480700600800800 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record006_frame002_links_0000 record006_frame002_links_0064)
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0379.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0379.count (({ width := 9, code := 0x6130782bfdf6f97ab9dc6c762b0d7ab95babd4a9f459ccca632f96c9a3f1e8dc5e27108341609017fbf9f0f479399b4d669b49a0c761afd7cba5bacd509c4d2612a9444a1d08803f1ecf06431180bc5d2e168b2582b9549248238f87a3c1d0e47035198c05c251208c42200f07032170a84c240f070281207018080200 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record006_frame003_links_0000 record006_frame003_links_0064)
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0379
    Papers.RationalityTen.SharedFrameCatalogue.group0379_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
def record006_frame004_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x36b5b04d6f68a33a59accb7651b2717aabb15c5accd61eae956a2b195709eb4bb24f926491d484230d11687f435215508483c3b69d1ce686c334e9a28cdc66032c9674a8652b28b14309f44b624f12248fe46d23191686fc31f1890c005d82db13f09c44be24b11d08bc4521880bc85a4286139098046020c0fc079836c12008f04681b40d606a031017c0bc05b02c81580a803401980c8052027012808c04001e00e004c02400f00700280120070018008002000 } : Fields).get c.val)
theorem record006_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record006_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record006) (record006.maps 4)
      (record006.inverseMaps 4) record006_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record006_frame004_links_0000 record006_frame004_links_0064)
theorem record006_frame004_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 4 :=
  of_group record006 4 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record006_frame004_indices record006_frame004_graph record006_frame004_links
def record006_frame005_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x12163dc758cd17a2bc4e8870fe084097f8f99ef3cf784ef1da3826c8d39a5344670c89863085febcd73ae3582ad15729851ea193ba714d68c907a023ec7ccf39d13866e8db1aa344668b394b28c4fc9b932232450871052003ec7b0cf19030c5c8b41602a8520a01362543c0770ea17c2f05d0ac14c2904f09a128240330640c41482704a08c1001e03804c0900f01c0280480700600800800 } : Fields).get c.val)
theorem record006_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record006_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record006) (record006.maps 5)
      (record006.inverseMaps 5) record006_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record006_frame005_links_0000 record006_frame005_links_0064)
theorem record006_frame005_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 5 :=
  of_group record006 5 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record006_frame005_indices record006_frame005_graph record006_frame005_links
def record006_frame006_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x174ae0dbab4363ac4578acd57e8d50c9fb39a6c4cf9812ce5446c8830b613c1d82afddf1bde7acf2ddf3b7718df5bb35a69ad1598b28646b3d5529f528a3d42a5e4a490d1f230448870e519d32e62cbf1752a8538a193c2684a4920ec1ce380688cf1922f85a0af1582843e07b0f41a0338660c01742e0590ae150290340660c81482704a08c1001e03804c0900f01c0280480700600800800 } : Fields).get c.val)
theorem record006_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record006_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record006) (record006.maps 6)
      (record006.inverseMaps 6) record006_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record006_frame006_links_0000 record006_frame006_links_0064)
theorem record006_frame006_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 6 :=
  of_group record006 6 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record006_frame006_indices record006_frame006_graph record006_frame006_links
def record006_frame007_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0372.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0372.count (({ width := 8, code := 0xf8f7f6f3f2f1f0ebe9e2e1e0dddcdbd9d5d3cec7c2c1c0bfbbb6b5b4b3b0aea8a7a6a3a2a19e9b99938c89878685807d7b7a7977746e67656462615b5958565553514746454342413f3e3d3c3a3231302b2a292726252422211f1a19181615141311100e0c0b0a0907060403020100 } : Fields).get c.val)
theorem record006_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0372.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0372.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0372.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record006_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0372.localPairCheck (smallEmbedding record006) (record006.maps 7)
      (record006.inverseMaps 7) record006_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record006_frame007_links_0000 record006_frame007_links_0064)
theorem record006_frame007_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 7 :=
  of_group record006 7 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0372
    Papers.RationalityTen.SharedFrameCatalogue.group0372_facts record006_frame007_indices record006_frame007_graph record006_frame007_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (Fin.cases (record006_frame004_supported hcells) (Fin.cases (record006_frame005_supported hcells) (Fin.cases (record006_frame006_supported hcells) (Fin.cases (record006_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x6a534f9a64cd6659b2458dac4a6142dd96d2b63572ab2156ea85534295d2f6916486a4151fa8f643a21910a483f417a0910247ff3f79cdce6072a3921c74e2e6c13591a88d246823389980ca26413189884c2058e2b91558a7251d28093e09e84ee274932c94a48223911a48b644f22190e88584201cf0df86de33e18f0c3c60a2fd17b0bc057228d13c89a44b224b11e08bc43e21110106483001760a7851424c11808483741a606002f81700b605702b00a8050027013009004602100f8078028013009004001e00e00580280120040018008002000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record007_frame001_links_0000 (interval_append _ 64 128 132 record007_frame001_links_0064 record007_frame001_links_0128))
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x6d0b609abed08674b319962ca464b2f0d73eb8b590abf55d2ace5602ae537a9534a2a4bd23290845022490f886642aa13508a83d41b1e40f0076d3ad9d1ce686e636b1b0cd6269d34519f0cea66f3341984cb45d22d89624ad855129a9490a3450827d137c9884a824b92348f646d23291848b64561e00e546fc34f1980c7c6202fc1760b6c55c28f13f09bc4b624b11d08c845422310e068831617b0a284ec23010807f036c1a406002f81700b605702b00a8050027013009004602100f8078028013009004001e00e00580280120040018008002000 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record007_frame002_links_0000 (interval_append _ 64 128 132 record007_frame002_links_0064 record007_frame002_links_0128))
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0x7a8f31e33bc768eb9d43a0734e01bcb756c6d71ac34d68cd098eafb5f0bcd772e958eb115faba56aac956aa85469fd3da784e89c1362584a894526a4948a9051ea3a46c8c917225434835031fb3dc7a4f39e33c0768e79c237a6ecdb9b43606b8d51a7326610bd9682b2540a49442804ec9611d228434841041fe3f07b8f31dc340658c61682bc4f09a12a210408520a2138268490900a0130250480881081f03a0700a0130240400780e0160280480400600800800 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record007_frame003_links_0000 (interval_append _ 64 128 132 record007_frame003_links_0064 record007_frame003_links_0128))
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1069.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1069.count (({ width := 10, code := 0xef7b5ec3a5e7798e4388e0f67d835dd2b43d0335cbb2bc26eab9ee2b76d8ae6b6ac6aca9ea4a7e9aa56719b66a99a6297a4a91a438fe3b8de338be2c8a22488216829ff7e1ec785dd76dd7751cd705b66c9b06b1a9695a367d9c61d7a5c55f5494950d3e4e935499194410a415013f0f93d0f03acd032cc62d0af2789a254842045013c4c12c471182809825090220841f0741c050130481003c0e02c0a0240400c0200400 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record007_frame004_links_0000 (interval_append _ 64 128 132 record007_frame004_links_0064 record007_frame004_links_0128))
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1069
    Papers.RationalityTen.SharedFrameCatalogue.group1069_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
def record007_frame005_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x66232c5940c6862730e183ac035f72cd5638b14563aab954ea7f534298131c92c48f240d1d08d2438a19109683240ea038fec7dc3e31d78ea074539d1cbce4c6f43719b60d926be3599a9cd3268833e19accc25db2e216c4b2e57b2b29558a8e53429314209d44d226112cc94049224111cc8be4501f08f1477a38c1b60d886a833b1938c545c62c215c0aa852427f136897448e23411106e43501970b1854024210e080036019206002f81700b605702b00a8050027013009004602100f8078028013009004001e00e00580280120040018008002000 } : Fields).get c.val)
theorem record007_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record007_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 5)
      (record007.inverseMaps 5) record007_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record007_frame005_links_0000 (interval_append _ 64 128 132 record007_frame005_links_0064 record007_frame005_links_0128))
theorem record007_frame005_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 5 :=
  of_group record007 5 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record007_frame005_indices record007_frame005_graph record007_frame005_links
def record007_frame006_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0xb9b72ae1daeb4f672c6582ae549a90d1ca0d3f67ace29a932e3bc568a11262043982903a03bfd7ecfc5f43dd7aeec1d63a8748e81cdb86702df1bc3716d0d85aeb5769ad0d9daf15c8b61642be55aa8d4fa95516a05392624ae9492323f46a8bd112193e4794ee9c93766c8d59a1334640bf9702ce580aa94b2884f49892723c3e0788ec1b6354630c01762ac5305a0b21582a8510a00a81402704c0901182103e0780a0130240400780e0160280480400600800800 } : Fields).get c.val)
theorem record007_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record007_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record007) (record007.maps 6)
      (record007.inverseMaps 6) record007_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record007_frame006_links_0000 (interval_append _ 64 128 132 record007_frame006_links_0064 record007_frame006_links_0128))
theorem record007_frame006_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 6 :=
  of_group record007 6 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record007_frame006_indices record007_frame006_graph record007_frame006_links
def record007_frame007_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x92123642c788e71ae31c5e8a30ae12c20823022013f97e6fb1d2b856fededbb3726acd45a433f66ccc996b2062ebed7baf55e2bad73ad75a4b3563ac1578ad9592ae550a894da6d4ce97128a464708c917a2b44c879092043fa7e4f91ea3c2780ea9ca344650c71832f65d4b896c2d2590ab9492844f49892c24246c8a90f20e38c700da19231c5b8b215a2784c85b0b41602b8530a40a81402704c0901182103e0780a0130240400780e0160280480400600800800 } : Fields).get c.val)
theorem record007_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record007_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record007) (record007.maps 7)
      (record007.inverseMaps 7) record007_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record007_frame007_links_0000 (interval_append _ 64 128 132 record007_frame007_links_0064 record007_frame007_links_0128))
theorem record007_frame007_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 7 :=
  of_group record007 7 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record007_frame007_indices record007_frame007_graph record007_frame007_links
def record007_frame008_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x9c536a684c597d2c253ca09311ba3145c89d11a1ec30853091f03be770ec1d339d6f4dd9b73626b2d51a7348688cb193b2363ac4d86b025fcbe97a2ed5c6b816dad75a6b3d65a9d51a9f53b26c4c29712b24c4848d91621c42a845029f93e67c0f49e337e6b0d2195312600bd9702d2574a814627c4e89912923e46c8a1102143906e8d619030c590ab154260490570ac14c2904e09a0a41382604a08c1102003c0740a0130240400780e0160280480400600800800 } : Fields).get c.val)
theorem record007_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record007_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record007) (record007.maps 8)
      (record007.inverseMaps 8) record007_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record007_frame008_links_0000 (interval_append _ 64 128 132 record007_frame008_links_0064 record007_frame008_links_0128))
theorem record007_frame008_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 8 :=
  of_group record007 8 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record007_frame008_indices record007_frame008_graph record007_frame008_links
def record007_frame009_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0616.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0616.count (({ width := 8, code := 0xabaaa9a7a6a5a3a2a19f9e9d9b9a99979695928f8e8d8b8986858482807f7e7c7a79777675747372706f6e6d6c6b69686766656362615f5e5d5c5b5a5957565554535251504f4e4d4b4a49474645444342413f3e3d3c3b3a39383736353231302d2c28272622201f1e1d1c1b1a161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record007_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0616.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0616.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0616.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0616.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record007_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0616.localPairCheck (smallEmbedding record007) (record007.maps 9)
      (record007.inverseMaps 9) record007_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record007_frame009_links_0000 (interval_append _ 64 128 132 record007_frame009_links_0064 record007_frame009_links_0128))
theorem record007_frame009_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 9 :=
  of_group record007 9 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0616
    Papers.RationalityTen.SharedFrameCatalogue.group0616_facts record007_frame009_indices record007_frame009_graph record007_frame009_links
def record007_frame010_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0619.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0619.count (({ width := 8, code := 0xd7d6d3d1d0cdcbcac7c5c3c1bfbdbbb9b7b5b3b1b0afadaba9a8a7a5a3a2a19f9d9a9897959392908e8d8b898887858482807f7d7c797776737271706e6c6b68676665636261605e5c5a5856545251504f4d4b49474645444241403f3d3b3a3935342f2e2d28261f1e1d1c1b1a161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record007_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0619.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0619.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0619.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0619.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record007_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0619.localPairCheck (smallEmbedding record007) (record007.maps 10)
      (record007.inverseMaps 10) record007_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record007_frame010_links_0000 (interval_append _ 64 128 132 record007_frame010_links_0064 record007_frame010_links_0128))
theorem record007_frame010_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 10 :=
  of_group record007 10 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0619
    Papers.RationalityTen.SharedFrameCatalogue.group0619_facts record007_frame010_indices record007_frame010_graph record007_frame010_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (Fin.cases (record007_frame005_supported hcells) (Fin.cases (record007_frame006_supported hcells) (Fin.cases (record007_frame007_supported hcells) (Fin.cases (record007_frame008_supported hcells) (Fin.cases (record007_frame009_supported hcells) (Fin.cases (record007_frame010_supported hcells) (fun j => Fin.elim0 j))))))))))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1a64c916142e116fab765b82da56c6b0457bab955aeac855baa9152ea8553ba9a14ae97b48b243120a8fd47b21d10c485241fa0bd0448123ff9fbce6e7303951c90e3a7173609ac8d4469234119c4cc065132098c4c426102ab14049f24f427713a4904475234916c89e44621d10b08403be1d70e7871c37e1b78d7869c33e1970c7861e30417e8bd85e02e21670ae454628d13c89984b224b11e08b043e21110106483041760a8851424c11a08483741a606002f81700b605702b00a004e024011807c03c01500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame001_links_0000 (interval_append _ 64 128 138 record008_frame001_links_0064 record008_frame001_links_0128))
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1abecc664b2f917aabc35d8ae7d716b42599ac8561eafd574ab6d5aaace563ab015729bd4a9a50925e919484228111e87c433215509884541ea0d8f207803b69d6ce8e7343731b58d866b134e9a28cf867533799a0cc265a2c494d4a5051a28413e895049b24691ec8da466230916c8ac3ed1ea8f007523951bf0db46be34f19f8cc063e30c17e0bb05b62cc15f0ab853c28f13f09ac4b624b11d08c445422310e068831a17b0a384ec23010a07f036c1a406002f81700b605702b00a004e024011807c03c01500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame002_links_0000 (interval_append _ 64 128 138 record008_frame002_links_0064 record008_frame002_links_0128))
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0x1e33ae734e1dc23806fade5bab6a6ced8db035c6b0d51a8b4d694d19a131d5f6bdd79aee5d2b1d61abf574ad558aad550a8d3fa7b4f09d13826c4b095128a4d49291520a3d4748d91922e41a7b8f51e73c6780e11be3766dcda1b135c6a8d399f33464cc61842f65d0b79682c2564a81482885009d9382664b09291d228430841041fe3ec7b8f31dc340660c616a2bc4f09b12a210408520a213826849090098128220420740e01502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame003_links_0000 (interval_append _ 64 128 138 record008_frame003_links_0064 record008_frame003_links_0128))
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
def record008_frame004_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1069.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1069.count (({ width := 10, code := 0xec398e0f6edaf67d9360d7751d3b4ad1f43d033cce735ccb2ecaf09baae6b8addb62b9ad6b1ab2a7a8e9fa6a959c66d9aa6698a5e92a4690e3f8ee378ce2f8b228892207fde1779db75dd46d9b36c1ac6a5a668d9f67193639876097a5c56b5995f56952525424f93a4d5324b5264851944109415013f0f83d0f03acd0330c62d4af2789b254842045013c4c12c4711826094220841d0701505013048110400f0380c02c0a0240400c0200400 } : Fields).get c.val)
theorem record008_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record008) (record008.maps 4)
      (record008.inverseMaps 4) record008_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame004_links_0000 (interval_append _ 64 128 138 record008_frame004_links_0064 record008_frame004_links_0128))
theorem record008_frame004_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 4 :=
  of_group record008 4 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1069
    Papers.RationalityTen.SharedFrameCatalogue.group1069_facts record008_frame004_indices record008_frame004_graph record008_frame004_links
def record008_frame005_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1d20db7695b0297ecbdf5e5aed5740b42596ac5d60aaf256f2b21568aa054629dd4c4959473a3591868ab44c20c104280f3fc9f9cfb67ca3da9e94dac6c23559a5cd0266c30717e4bc65d12df16a8b285802b61560a8652e2128ecc74438f1bb8d905f82ed16d8b145662a714b0a044e223911908ac44821d10b083c4102010fd07cc3d81e30ee075439c1c90e106ec3681ad0d3067432c18f0c406042f41730b604f426a12e08c84481fc0f6077836c1aa06002f81700b605702b00a004e024011807c03c01500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record008_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 5)
      (record008.inverseMaps 5) record008_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame005_links_0000 (interval_append _ 64 128 138 record008_frame005_links_0064 record008_frame005_links_0128))
theorem record008_frame005_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 5 :=
  of_group record008 5 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record008_frame005_indices record008_frame005_graph record008_frame005_links
def record008_frame006_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x74170d6ea68567e67767166c66764163562c62361d6136075fc5f35ea5e35d756352a52251c51550e4d34ca4c44b84b04a94a049248843542e42742141c4173ee3e33da3d13ca3be3b53a93a039739138730c2d92d22cc2c52be28327927026225825124b23f23720f2061fd1f61ee1e71de1d51cc1c51bd1b61af1ab1a71a319f19819118a18317d17316b16215915014813f13611310b1050f10eb0d90d50cf0bc0b506005f05c05b05705602802702402301f01e01501401301201101000f00e00c00b00a009004003002001000 } : Fields).get c.val)
theorem record008_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record008) (record008.maps 6)
      (record008.inverseMaps 6) record008_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame006_links_0000 (interval_append _ 64 128 138 record008_frame006_links_0064 record008_frame006_links_0128))
theorem record008_frame006_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 6 :=
  of_group record008 6 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record008_frame006_indices record008_frame006_graph record008_frame006_links
def record008_frame007_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x3696b0d278ff1c631c5187f0c5f5bdd79aeedd4b9b716e05bab696bed552e9f13ba72cd899f25a45c828e91aa3145b8a914207c08800fddf73e778aef9dbbae74ae79cb391716e15c037b5feb1d5e2b354aa6d31a594a090d1d233458895109fe3f27c8f69e83c6770ea9ce38c700dc1ae34e680cc992316610be1762dc590ae95629e528a314227c4608890b1f23c46e0d21942d45705e0ba1682c8550a80a01382404607c0f01502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record008_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record008) (record008.maps 7)
      (record008.inverseMaps 7) record008_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame007_links_0000 (interval_append _ 64 128 138 record008_frame007_links_0064 record008_frame007_links_0128))
theorem record008_frame007_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 7 :=
  of_group record008 7 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record008_frame007_indices record008_frame007_graph record008_frame007_links
def record008_frame008_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1063.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1063.count (({ width := 8, code := 0x9695949391908f8e8d8c8a8988878685838281807f7e7d7c7b7a797877767574737271706f6d6c6b6a69686665646362615f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524201f1e1d1c1b171615141312100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1063.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1063.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1063.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1063.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1063.localPairCheck (smallEmbedding record008) (record008.maps 8)
      (record008.inverseMaps 8) record008_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame008_links_0000 (interval_append _ 64 128 138 record008_frame008_links_0064 record008_frame008_links_0128))
theorem record008_frame008_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 8 :=
  of_group record008 8 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1063
    Papers.RationalityTen.SharedFrameCatalogue.group1063_facts record008_frame008_indices record008_frame008_graph record008_frame008_links
def record008_frame009_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1068.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1068.count (({ width := 9, code := 0x251259146e33188bc5a2b1187c3a1b0c85c2a11078341608fe7c3ddecf3793b1d6ea73b99cae470b81b2d76b355a8d367b3598cb6532590c662b1186c25e2d96ab458ac154a95429548a35127d3c994b251248f462250c84411fcf8793b9d4e671371b0d46732184be5d2d964ae552993494482110074381b0c05c29140984a2311074381a0c85c2c110803c1c0d0602c14090401c0c04018080200 } : Fields).get c.val)
theorem record008_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1068.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record008) (record008.maps 9)
      (record008.inverseMaps 9) record008_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame009_links_0000 (interval_append _ 64 128 138 record008_frame009_links_0064 record008_frame009_links_0128))
theorem record008_frame009_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 9 :=
  of_group record008 9 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1068
    Papers.RationalityTen.SharedFrameCatalogue.group1068_facts record008_frame009_indices record008_frame009_graph record008_frame009_links
def record008_frame010_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1940c385f72d49686b355952c71628ae656aab1d578aae553aa6d516a7f53a29a14c098e496246d2068e846921c50c284b41920750167f63ee1f18ebc7503a29ce8e5e72637a1b8cdb06c935f1accd4e69934419f0cd66612d89594ab454729a14989a44c62599280924486239917c8a04011f80f847a83c51de8eb473638c1bd8db06c435019d8c9c62a30617a0b8c5a62c215c0a9852427f136896448e23411106e43541970b28540242110080036019206002f81700b605702b00a004e024011807c03c01500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record008_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 10)
      (record008.inverseMaps 10) record008_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame010_links_0000 (interval_append _ 64 128 138 record008_frame010_links_0064 record008_frame010_links_0128))
theorem record008_frame010_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 10 :=
  of_group record008 10 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record008_frame010_indices record008_frame010_graph record008_frame010_links
def record008_frame011_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6d469e67763262d62a6276246215fd5f35e95e35e05dc5d35cc5c95c25b85b254d51d51951250a5064c94bf4b34a649c49348747d47243b43743443142e42b4093fc3f23ea3e73e23dc3d13ce3c73bd3b536033833533032b3292ec2e62dd2d42cc2c72be2b42af27826d26425a25324e24623d23622d22421c2172102092051fd1ed1dd1d11c11b91ae1a419a18f18717d17216c12511e1150fe0f50e00d50c80a90a105a05905605505105002802702402301f01e01501401301201101000f00e00c00b00a009004003002001000 } : Fields).get c.val)
theorem record008_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record008) (record008.maps 11) (record008.inverseMaps 11) record008_frame011_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record008) (record008.maps 11) (record008.inverseMaps 11) record008_frame011_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record008) (record008.maps 11) (record008.inverseMaps 11) record008_frame011_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record008) (record008.maps 11)
      (record008.inverseMaps 11) record008_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame011_links_0000 (interval_append _ 64 128 138 record008_frame011_links_0064 record008_frame011_links_0128))
theorem record008_frame011_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 11 :=
  of_group record008 11 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record008_frame011_indices record008_frame011_graph record008_frame011_links
def record008_frame012_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0971.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0971.count (({ width := 8, code := 0xb7b3afadacabaaa9a8a6a5a4a3a2a19f9e9d9c9b9a9896949392918f8d8c8b8a88878685848281807f7e7d7b7a7978777674737271706c68676564635f5e5c5b5a59575655545251504f4e4d4b4a49484745444342413f3e3d3c3b39383736343332312f2e2c2b2928272524232221201f1e1d181715141211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0971.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0971.localPairCheck (smallEmbedding record008) (record008.maps 12) (record008.inverseMaps 12) record008_frame012_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0971.localPairCheck (smallEmbedding record008) (record008.maps 12) (record008.inverseMaps 12) record008_frame012_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0971.localPairCheck (smallEmbedding record008) (record008.maps 12) (record008.inverseMaps 12) record008_frame012_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0971.localPairCheck (smallEmbedding record008) (record008.maps 12)
      (record008.inverseMaps 12) record008_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame012_links_0000 (interval_append _ 64 128 138 record008_frame012_links_0064 record008_frame012_links_0128))
theorem record008_frame012_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 12 :=
  of_group record008 12 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0971
    Papers.RationalityTen.SharedFrameCatalogue.group0971_facts record008_frame012_indices record008_frame012_graph record008_frame012_links
def record008_frame013_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0974.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0974.count (({ width := 8, code := 0x9695949391908f8e8d8c8a8988878685838281807f7e7d7c7b7a797877767574737271706f6d6c6b6a69686665646362615f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524201f1e1d1c1b171615141312100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0974.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0974.localPairCheck (smallEmbedding record008) (record008.maps 13) (record008.inverseMaps 13) record008_frame013_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0974.localPairCheck (smallEmbedding record008) (record008.maps 13) (record008.inverseMaps 13) record008_frame013_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0974.localPairCheck (smallEmbedding record008) (record008.maps 13) (record008.inverseMaps 13) record008_frame013_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0974.localPairCheck (smallEmbedding record008) (record008.maps 13)
      (record008.inverseMaps 13) record008_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame013_links_0000 (interval_append _ 64 128 138 record008_frame013_links_0064 record008_frame013_links_0128))
theorem record008_frame013_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 13 :=
  of_group record008 13 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0974
    Papers.RationalityTen.SharedFrameCatalogue.group0974_facts record008_frame013_indices record008_frame013_graph record008_frame013_links
def record008_frame014_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x24a489903142254478891061f4298490760bc1381f02a02c017f6fd1f73ae71ae25c237f6f6d85aeb576a0d2da4341672cd188b0b610c15812ff5d2b896dad65a4b3564ac357eaed5a2af4d29392524547e8f11121e42e83d042064007e0fa1d5398710de1b73626b0d219f32e63cc41843005e8ba16f2ce578ab94e2925049c13024e47c8b10e20e3906f0d818c300580ac14e250478570ac14c2904e09a0a01382404607c0f01502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record008_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record008) (record008.maps 14) (record008.inverseMaps 14) record008_frame014_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record008) (record008.maps 14) (record008.inverseMaps 14) record008_frame014_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record008) (record008.maps 14) (record008.inverseMaps 14) record008_frame014_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record008) (record008.maps 14)
      (record008.inverseMaps 14) record008_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame014_links_0000 (interval_append _ 64 128 138 record008_frame014_links_0064 record008_frame014_links_0128))
theorem record008_frame014_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 14 :=
  of_group record008 14 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record008_frame014_indices record008_frame014_graph record008_frame014_links
def record008_frame015_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0994.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0994.count (({ width := 11, code := 0x2664b994f1a22fc598a914626c398690be1442383905e08c0d813012013b9738e5dc7b876fed91aeb5669ad19a0b3a666cb57f2f45debad732e159ab1d622be570ac956aa7544a7d4da9849e8c515223430848fb9f23d477cee1d73a071ce11aa348678cd194322630c29802f45d4b89692c0568aa14f2925109f93a2684b09191e22e44c87909206398710de1963185d0b315c2884e0570ac14c2904e09a0a01382404607c0f01502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record008_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record008) (record008.maps 15) (record008.inverseMaps 15) record008_frame015_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record008) (record008.maps 15) (record008.inverseMaps 15) record008_frame015_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record008) (record008.maps 15) (record008.inverseMaps 15) record008_frame015_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record008) (record008.maps 15)
      (record008.inverseMaps 15) record008_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame015_links_0000 (interval_append _ 64 128 138 record008_frame015_links_0064 record008_frame015_links_0128))
theorem record008_frame015_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 15 :=
  of_group record008 15 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0994
    Papers.RationalityTen.SharedFrameCatalogue.group0994_facts record008_frame015_indices record008_frame015_graph record008_frame015_links
def record008_frame016_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0970.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0970.count (({ width := 8, code := 0x898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0970.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0970.localPairCheck (smallEmbedding record008) (record008.maps 16) (record008.inverseMaps 16) record008_frame016_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0970.localPairCheck (smallEmbedding record008) (record008.maps 16) (record008.inverseMaps 16) record008_frame016_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0970.localPairCheck (smallEmbedding record008) (record008.maps 16) (record008.inverseMaps 16) record008_frame016_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0970.localPairCheck (smallEmbedding record008) (record008.maps 16)
      (record008.inverseMaps 16) record008_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame016_links_0000 (interval_append _ 64 128 138 record008_frame016_links_0064 record008_frame016_links_0128))
theorem record008_frame016_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 16 :=
  of_group record008 16 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0970
    Papers.RationalityTen.SharedFrameCatalogue.group0970_facts record008_frame016_indices record008_frame016_graph record008_frame016_links
def record008_frame017_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0973.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0973.count (({ width := 8, code := 0x898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0973.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0973.localPairCheck (smallEmbedding record008) (record008.maps 17) (record008.inverseMaps 17) record008_frame017_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0973.localPairCheck (smallEmbedding record008) (record008.maps 17) (record008.inverseMaps 17) record008_frame017_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0973.localPairCheck (smallEmbedding record008) (record008.maps 17) (record008.inverseMaps 17) record008_frame017_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0973.localPairCheck (smallEmbedding record008) (record008.maps 17)
      (record008.inverseMaps 17) record008_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame017_links_0000 (interval_append _ 64 128 138 record008_frame017_links_0064 record008_frame017_links_0128))
theorem record008_frame017_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 17 :=
  of_group record008 17 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0973
    Papers.RationalityTen.SharedFrameCatalogue.group0973_facts record008_frame017_indices record008_frame017_graph record008_frame017_links
def record008_frame018_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xad4a95a519d49cb9c49ba9ae9a298097796d96195694b93e93592c9209139068507f77e27d17bd7a675073d7297116fe6ef6dd6c66b366a66365d65664b63d61a61360a5ff5f35e55d95d25c95bf5b15a05044bd4ae4a048e47e4364274174023f33e83da3c53b637936d36035234533a32d3203133052f52e72d72cb2bc2aa2a029628627526725a2472372262182071f81e71d918317216413612a0fe0f20e70c00b405e05d05a05905505402802702402301f01e01501401301201101000f00e00c00b00a009004003002001000 } : Fields).get c.val)
theorem record008_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 18) (record008.inverseMaps 18) record008_frame018_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 18) (record008.inverseMaps 18) record008_frame018_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 18) (record008.inverseMaps 18) record008_frame018_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 18)
      (record008.inverseMaps 18) record008_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame018_links_0000 (interval_append _ 64 128 138 record008_frame018_links_0064 record008_frame018_links_0128))
theorem record008_frame018_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 18 :=
  of_group record008 18 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record008_frame018_indices record008_frame018_graph record008_frame018_links
def record008_frame019_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x32d636c2d79af0ddebb3752e85beb716d2d6da7b4365eca58fb1360abd5169c936e6accf99123e40c758d316a2944986f0a1fe3f77e8fc5f63e679cf21e23be76cebdd33a373ce65c8b87666c3d84b055febe9662c4576ac9542a1538a3d42a5b4aa93923a3e46a8b513a21432845039fd3ee7ccf69e83be750e41bd3686a4cf197318600bd1702ca48c8c9111ea3b4698cb1822804c85b0b41602b8530a40a01382404607c0f01502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record008_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record008) (record008.maps 19) (record008.inverseMaps 19) record008_frame019_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record008) (record008.maps 19) (record008.inverseMaps 19) record008_frame019_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record008) (record008.maps 19) (record008.inverseMaps 19) record008_frame019_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record008) (record008.maps 19)
      (record008.inverseMaps 19) record008_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame019_links_0000 (interval_append _ 64 128 138 record008_frame019_links_0064 record008_frame019_links_0128))
theorem record008_frame019_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 19 :=
  of_group record008 19 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record008_frame019_indices record008_frame019_graph record008_frame019_links
def record008_frame020_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0618.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0618.count (({ width := 9, code := 0x26f369acce633097cba5b2c954a6512793496472290c823f1789446210f86c1e0d058240a00ff7f3f1eaf3793c5e0ef75ba5d0e773395c6e17037dbcdd6ab419ece66b318cc56230d84c05faf97ab95aac960ad552a54aa25027534984b2512290462250e84409fcfa7b3c1d8e872379a0ca622d960a44f2611888361a8d0663118084401f0f07036150a04c24110803c1c0c058281204018080200 } : Fields).get c.val)
theorem record008_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0618.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record008) (record008.maps 20) (record008.inverseMaps 20) record008_frame020_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record008) (record008.maps 20) (record008.inverseMaps 20) record008_frame020_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record008) (record008.maps 20) (record008.inverseMaps 20) record008_frame020_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record008) (record008.maps 20)
      (record008.inverseMaps 20) record008_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame020_links_0000 (interval_append _ 64 128 138 record008_frame020_links_0064 record008_frame020_links_0128))
theorem record008_frame020_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 20 :=
  of_group record008 20 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0618
    Papers.RationalityTen.SharedFrameCatalogue.group0618_facts record008_frame020_indices record008_frame020_graph record008_frame020_links
def record008_frame021_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0621.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0621.count (({ width := 8, code := 0x898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0621.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0621.localPairCheck (smallEmbedding record008) (record008.maps 21) (record008.inverseMaps 21) record008_frame021_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0621.localPairCheck (smallEmbedding record008) (record008.maps 21) (record008.inverseMaps 21) record008_frame021_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0621.localPairCheck (smallEmbedding record008) (record008.maps 21) (record008.inverseMaps 21) record008_frame021_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0621.localPairCheck (smallEmbedding record008) (record008.maps 21)
      (record008.inverseMaps 21) record008_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame021_links_0000 (interval_append _ 64 128 138 record008_frame021_links_0064 record008_frame021_links_0128))
theorem record008_frame021_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 21 :=
  of_group record008 21 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0621
    Papers.RationalityTen.SharedFrameCatalogue.group0621_facts record008_frame021_indices record008_frame021_graph record008_frame021_links
def record008_frame022_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6e06a266c60e6085ff5fb5f25ed5d15cc5c25bc5b25ab5a159c59158b57e5794fb4cb4c14b34a849c46545b44c43a42e42841b40e4053d53ce3ca3c23bd3b439839138d38337d37236836135c35034a3402c229228727c26f26322c2202132011f51ec1e31d51cc1ac1a81a219c19619118b18718117c17717116a16415f15b15715414f14914313d13613012b12712311d1161110f60ef0e90d90d30c50bf0b90ac0a905905805505405004f02802702402301f01e01501401301201101000f00e00c00b00a009004003002001000 } : Fields).get c.val)
theorem record008_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record008) (record008.maps 22) (record008.inverseMaps 22) record008_frame022_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record008) (record008.maps 22) (record008.inverseMaps 22) record008_frame022_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record008) (record008.maps 22) (record008.inverseMaps 22) record008_frame022_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record008) (record008.maps 22)
      (record008.inverseMaps 22) record008_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame022_links_0000 (interval_append _ 64 128 138 record008_frame022_links_0064 record008_frame022_links_0128))
theorem record008_frame022_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 22 :=
  of_group record008 22 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record008_frame022_indices record008_frame022_graph record008_frame022_links
def record008_frame023_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x23845187904a0840b813001fe3e77ccf85ef3d579ef19e1bbe77aee1dab746aed45a4b40670c55883075f6bcd77aea5c8b81632c3582ae95a2ae538a694c29351ea193ea794f09cd3926c456825009fa3de79ce49c237a6c8d51a534266ccb9822fc5dcb896b2ce588ae9592a8540a59432784dc9913025a49c9191d232444859052003f07b8f51e6360688ca1742d4550a5142254490540a61402784b0940a01382404607c0f01502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record008_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record008) (record008.maps 23) (record008.inverseMaps 23) record008_frame023_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record008) (record008.maps 23) (record008.inverseMaps 23) record008_frame023_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record008) (record008.maps 23) (record008.inverseMaps 23) record008_frame023_indices (Fin.ofNat record008.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record008_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record008) (record008.maps 23)
      (record008.inverseMaps 23) record008_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record008_frame023_links_0000 (interval_append _ 64 128 138 record008_frame023_links_0064 record008_frame023_links_0128))
theorem record008_frame023_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 23 :=
  of_group record008 23 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record008_frame023_indices record008_frame023_graph record008_frame023_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (Fin.cases (record008_frame004_supported hcells) (Fin.cases (record008_frame005_supported hcells) (Fin.cases (record008_frame006_supported hcells) (Fin.cases (record008_frame007_supported hcells) (Fin.cases (record008_frame008_supported hcells) (Fin.cases (record008_frame009_supported hcells) (Fin.cases (record008_frame010_supported hcells) (Fin.cases (record008_frame011_supported hcells) (Fin.cases (record008_frame012_supported hcells) (Fin.cases (record008_frame013_supported hcells) (Fin.cases (record008_frame014_supported hcells) (Fin.cases (record008_frame015_supported hcells) (Fin.cases (record008_frame016_supported hcells) (Fin.cases (record008_frame017_supported hcells) (Fin.cases (record008_frame018_supported hcells) (Fin.cases (record008_frame019_supported hcells) (Fin.cases (record008_frame020_supported hcells) (Fin.cases (record008_frame021_supported hcells) (Fin.cases (record008_frame022_supported hcells) (Fin.cases (record008_frame023_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x82581b8127e07ce7c57ac78c76a76375f75871a7086f96ca6946636596496405ff5c95a859e59158354b54553e52f52952251c4c34ae4a646542e4083f03e43dc38934d33b32331a30c2dd2d02c92c22b62b02ab2472041f91ec1dd1d319c19418517716d15f15811c11410c0f70ed0e60d80cc0c80c40c109209108e08d07106f06d06b06205f05e05b05905505403803703403302902702502302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x663cc197719e25c3d7feea5a9b4166ecad69abb54a985069c3376694cd9532263b4718d718e19c2d85106609c0e812f0ddc3b26f8d3198b25638c5969aa852ea2943a7b4908e119a2943a8650a9cd344660c79842f8524a09342544908d1161d839c708d41a032c608b916c2c8578831042003f8690d0198320600be1782d8590aa1501c0370680cc1482704a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0779.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0779.count (({ width := 8, code := 0xd7d6d5d2d1d0cecac6c5c4c3c0bfbebbb7b4b3b2b1ada9a7a6a5a49c9b9a989796959493928c89888685847e7b7a7877766f6d6c6b696867615e5d5b5a5952514f4e4d4b4a4342413f3e3d3b3a393837343332312e2d2c2b282726252322211a191817141312110f0e0d0b0a090806050403020100 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0779.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0779.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0779.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0779.localPairCheck (smallEmbedding record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame003_links_0000 record009_frame003_links_0064)
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0779
    Papers.RationalityTen.SharedFrameCatalogue.group0779_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
def record009_frame004_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0752.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0752.count (({ width := 9, code := 0x10a84c220b0481c09fcf67a3cde2ed763add2e56f375b4d96ab4196ca6431572b75aacd64b1582bd5cad55aa94ea4512853c9c4d25d2c9344a19088240a00fe7d3d1e4ee74391a0cc6330980be5e2a148a04d2612c94492411c8c4421908823c1d8e87034198c85e2d148a04c251208c3e1e0e86c30150a048220f070281007018080200 } : Fields).get c.val)
theorem record009_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0752.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record009) (record009.maps 4)
      (record009.inverseMaps 4) record009_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame004_links_0000 record009_frame004_links_0064)
theorem record009_frame004_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 4 :=
  of_group record009 4 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0752
    Papers.RationalityTen.SharedFrameCatalogue.group0752_facts record009_frame004_indices record009_frame004_graph record009_frame004_links
def record009_frame005_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0722.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0722.count (({ width := 8, code := 0x9e9d9c99989796928e8d8c8b88878684807d7c7b7a777371706f6e6968676564636261605f5d5c5b5a59585655545352514d4c4b4a4948474544434241403c3b3a393837363231302f2e2d2c2b2a29282625242321201f1e1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0722.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0722.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0722.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0722.localPairCheck (smallEmbedding record009) (record009.maps 5)
      (record009.inverseMaps 5) record009_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame005_links_0000 record009_frame005_links_0064)
theorem record009_frame005_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 5 :=
  of_group record009 5 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0722
    Papers.RationalityTen.SharedFrameCatalogue.group0722_facts record009_frame005_indices record009_frame005_graph record009_frame005_links
def record009_frame006_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x73172d72a6ff6f06e86ce69a65a64d6476366085fb5ed5c959956a56355554e50f4de4bd4b64ac49c44443942f41440d4063fb3ca3bd3b438a35933532631c3152cd29c28a2782732632182001f61e51d41cd1c219117116d16715f15b13512f12812211c1121100ed0e70e40d70d10ce0c50bd0b70b40b108608508208106a06806606405b05805705405204e04d03803703403302902702502302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record009_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 6)
      (record009.inverseMaps 6) record009_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame006_links_0000 record009_frame006_links_0064)
theorem record009_frame006_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 6 :=
  of_group record009 6 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record009_frame006_indices record009_frame006_graph record009_frame006_links
def record009_frame007_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0x3cd796f1ddf3ba772eb5cf388702df1bc3666c4d79a733a64ac8d8d3175f4b89682ce58eb014c29451ca154127d4f499932a6048c8b10f21241a82cf79db3aa728e39c233e654c898b3065fcbe14c2624c09512223e4007d8f41dc3a4710e017e2e85b8ac1502944f89912a24c478780ee1d83a8620c017c2e8550a41442704c09011c1a0330600bc1402704a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record009_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record009) (record009.maps 7)
      (record009.inverseMaps 7) record009_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame007_links_0000 record009_frame007_links_0064)
theorem record009_frame007_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 7 :=
  of_group record009 7 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record009_frame007_indices record009_frame007_graph record009_frame007_links
def record009_frame008_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0449.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0449.count (({ width := 8, code := 0xb9b8b7b5b4b3b1aeabaaa9a8a6a5a4a29f9c9b9a999895939291908b898886858382807f7e7c7976757473716f6d6c6b6a666362605f5d5c5958565554534f4d4b4948464541403f3d3c3b393837363531302f2e2a29282724232221201e1d1a19181714131211100e0d0b0a090807050403020100 } : Fields).get c.val)
theorem record009_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0449.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0449.localPairCheck (smallEmbedding record009) (record009.maps 8) (record009.inverseMaps 8) record009_frame008_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0449.localPairCheck (smallEmbedding record009) (record009.maps 8) (record009.inverseMaps 8) record009_frame008_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0449.localPairCheck (smallEmbedding record009) (record009.maps 8)
      (record009.inverseMaps 8) record009_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame008_links_0000 record009_frame008_links_0064)
theorem record009_frame008_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 8 :=
  of_group record009 8 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0449
    Papers.RationalityTen.SharedFrameCatalogue.group0449_facts record009_frame008_indices record009_frame008_graph record009_frame008_links
def record009_frame009_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0409.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0409.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record009_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0409.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0409.localPairCheck (smallEmbedding record009) (record009.maps 9) (record009.inverseMaps 9) record009_frame009_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0409.localPairCheck (smallEmbedding record009) (record009.maps 9) (record009.inverseMaps 9) record009_frame009_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0409.localPairCheck (smallEmbedding record009) (record009.maps 9)
      (record009.inverseMaps 9) record009_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame009_links_0000 record009_frame009_links_0064)
theorem record009_frame009_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 9 :=
  of_group record009 9 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0409
    Papers.RationalityTen.SharedFrameCatalogue.group0409_facts record009_frame009_indices record009_frame009_graph record009_frame009_links
def record009_frame010_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0395.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0395.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record009_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0395.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0395.localPairCheck (smallEmbedding record009) (record009.maps 10) (record009.inverseMaps 10) record009_frame010_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0395.localPairCheck (smallEmbedding record009) (record009.maps 10) (record009.inverseMaps 10) record009_frame010_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0395.localPairCheck (smallEmbedding record009) (record009.maps 10)
      (record009.inverseMaps 10) record009_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame010_links_0000 record009_frame010_links_0064)
theorem record009_frame010_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 10 :=
  of_group record009 10 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0395
    Papers.RationalityTen.SharedFrameCatalogue.group0395_facts record009_frame010_indices record009_frame010_graph record009_frame010_links
def record009_frame011_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0379.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0379.count (({ width := 9, code := 0x18bc56270983c15faf56eb65aed363b1586bb57a6d329348a2ce6653197cb639198c44e210e8641a0b04803e1e2ee763adccda6b34da4d060af176b759ac55ea84e26930954a215047f3d9e0ea7332188c05e2e970b4592c15cac4c259249041200f87a3a1c8e06a33178b850271289042200f07032160a84c240f070281007018080200 } : Fields).get c.val)
theorem record009_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record009) (record009.maps 11) (record009.inverseMaps 11) record009_frame011_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record009) (record009.maps 11) (record009.inverseMaps 11) record009_frame011_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record009) (record009.maps 11)
      (record009.inverseMaps 11) record009_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame011_links_0000 record009_frame011_links_0064)
theorem record009_frame011_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 11 :=
  of_group record009 11 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0379
    Papers.RationalityTen.SharedFrameCatalogue.group0379_facts record009_frame011_indices record009_frame011_graph record009_frame011_links
def record009_frame012_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0333.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0333.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record009_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0333.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0333.localPairCheck (smallEmbedding record009) (record009.maps 12) (record009.inverseMaps 12) record009_frame012_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0333.localPairCheck (smallEmbedding record009) (record009.maps 12) (record009.inverseMaps 12) record009_frame012_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0333.localPairCheck (smallEmbedding record009) (record009.maps 12)
      (record009.inverseMaps 12) record009_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame012_links_0000 record009_frame012_links_0064)
theorem record009_frame012_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 12 :=
  of_group record009 12 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0333
    Papers.RationalityTen.SharedFrameCatalogue.group0333_facts record009_frame012_indices record009_frame012_graph record009_frame012_links
def record009_frame013_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0307.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0307.count (({ width := 9, code := 0xfa7cbe1e4f077ba9cce17037dbcd86b355a0cb63b198ac460af172b85b2d558aa54a9548a250a6932984923914894421d067f3e9f0f67a3a1c4e06e369acd46630980bc5c2d954a44f269309047231148842209007c3d1e0ec742d160ac54271309446211007c3c1d0d86830170b0542612088401e0d0602c14090401c0a04018080200 } : Fields).get c.val)
theorem record009_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0307.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record009) (record009.maps 13) (record009.inverseMaps 13) record009_frame013_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record009) (record009.maps 13) (record009.inverseMaps 13) record009_frame013_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record009) (record009.maps 13)
      (record009.inverseMaps 13) record009_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame013_links_0000 record009_frame013_links_0064)
theorem record009_frame013_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 13 :=
  of_group record009 13 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0307
    Papers.RationalityTen.SharedFrameCatalogue.group0307_facts record009_frame013_indices record009_frame013_graph record009_frame013_links
def record009_frame014_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0233.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0233.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record009_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0233.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0233.localPairCheck (smallEmbedding record009) (record009.maps 14) (record009.inverseMaps 14) record009_frame014_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0233.localPairCheck (smallEmbedding record009) (record009.maps 14) (record009.inverseMaps 14) record009_frame014_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0233.localPairCheck (smallEmbedding record009) (record009.maps 14)
      (record009.inverseMaps 14) record009_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame014_links_0000 record009_frame014_links_0064)
theorem record009_frame014_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 14 :=
  of_group record009 14 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0233
    Papers.RationalityTen.SharedFrameCatalogue.group0233_facts record009_frame014_indices record009_frame014_graph record009_frame014_links
def record009_frame015_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0193.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0193.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record009_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0193.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0193.localPairCheck (smallEmbedding record009) (record009.maps 15) (record009.inverseMaps 15) record009_frame015_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0193.localPairCheck (smallEmbedding record009) (record009.maps 15) (record009.inverseMaps 15) record009_frame015_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0193.localPairCheck (smallEmbedding record009) (record009.maps 15)
      (record009.inverseMaps 15) record009_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame015_links_0000 record009_frame015_links_0064)
theorem record009_frame015_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 15 :=
  of_group record009 15 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0193
    Papers.RationalityTen.SharedFrameCatalogue.group0193_facts record009_frame015_indices record009_frame015_graph record009_frame015_links
def record009_frame016_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0170.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0170.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record009_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0170.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0170.localPairCheck (smallEmbedding record009) (record009.maps 16) (record009.inverseMaps 16) record009_frame016_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0170.localPairCheck (smallEmbedding record009) (record009.maps 16) (record009.inverseMaps 16) record009_frame016_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0170.localPairCheck (smallEmbedding record009) (record009.maps 16)
      (record009.inverseMaps 16) record009_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame016_links_0000 record009_frame016_links_0064)
theorem record009_frame016_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 16 :=
  of_group record009 16 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0170
    Papers.RationalityTen.SharedFrameCatalogue.group0170_facts record009_frame016_indices record009_frame016_graph record009_frame016_links
def record009_frame017_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xdd36e6371daa2d3e69c338d8f4c1a609b03980cb7d5b82d8d5e8a94524a911476a354cf24e521690647f23d909883e4182030ffc7f03f39ca8e3a71734f98f8c0a5fe2fc17ccac650e27d13cc9de4e923791688a0440215908483436f1878c185fc2f617809904b023d11508784061fa0bf05d02d614d0a184e824c11508383e01d2094049824011e07103781b40d606202f81780b605902a815007003701a00cc052027012808c04001d00e004c02400f00700280100070018008002000 } : Fields).get c.val)
theorem record009_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record009) (record009.maps 17) (record009.inverseMaps 17) record009_frame017_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record009) (record009.maps 17) (record009.inverseMaps 17) record009_frame017_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record009) (record009.maps 17)
      (record009.inverseMaps 17) record009_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame017_links_0000 record009_frame017_links_0064)
theorem record009_frame017_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 17 :=
  of_group record009 17 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record009_frame017_indices record009_frame017_graph record009_frame017_links
def record009_frame018_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x52fa4f492844fc9f338a604a093925e484668bb15a1cc1c806ff9fc3f4794ebdd039b72ce39b2b616b4d31a3341678be9782ed586a91472865029f92222643c8590920b3ca76cea9cd3826f4dc17d2b6560a994d2904949091b226438829021b835c698c81883045d8b41622b85508610a208408680ce1943205c0b41642b8550a21401b8360660c81482704a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record009_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record009) (record009.maps 18) (record009.inverseMaps 18) record009_frame018_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record009) (record009.maps 18) (record009.inverseMaps 18) record009_frame018_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record009) (record009.maps 18)
      (record009.inverseMaps 18) record009_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame018_links_0000 record009_frame018_links_0064)
theorem record009_frame018_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 18 :=
  of_group record009 18 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record009_frame018_indices record009_frame018_graph record009_frame018_links
def record009_frame019_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0845.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0845.count (({ width := 11, code := 0x4e09bf37a5c4af95526641c698c517a2c43585b0960abfb7cef89ed3d6768e4dbf3796e4db19eb35660c7d8d31361aba16f2da586a9147a87504a012ba3544e8850f2163da790f09d5398718e09882dc5a4b215d2b04b49491e226438839031ae358688c117a2ec578a814827c4e07e0fa1ec3d06c0d41a03385e0b816c2c8570a61481c0370680cc1482704a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record009_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record009) (record009.maps 19) (record009.inverseMaps 19) record009_frame019_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record009) (record009.maps 19) (record009.inverseMaps 19) record009_frame019_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record009) (record009.maps 19)
      (record009.inverseMaps 19) record009_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame019_links_0000 record009_frame019_links_0064)
theorem record009_frame019_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 19 :=
  of_group record009 19 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0845
    Papers.RationalityTen.SharedFrameCatalogue.group0845_facts record009_frame019_indices record009_frame019_graph record009_frame019_links
def record009_frame020_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0741.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0741.count (({ width := 8, code := 0x9e9d9c99989796928e8d8c8b88878684807d7c7b7a777371706f6e6968676564636261605f5d5c5b5a59585655545352514d4c4b4a4948474544434241403c3b3a393837363231302f2e2d2c2b2a29282625242321201f1e1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0741.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0741.localPairCheck (smallEmbedding record009) (record009.maps 20) (record009.inverseMaps 20) record009_frame020_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0741.localPairCheck (smallEmbedding record009) (record009.maps 20) (record009.inverseMaps 20) record009_frame020_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0741.localPairCheck (smallEmbedding record009) (record009.maps 20)
      (record009.inverseMaps 20) record009_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame020_links_0000 record009_frame020_links_0064)
theorem record009_frame020_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 20 :=
  of_group record009 20 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0741
    Papers.RationalityTen.SharedFrameCatalogue.group0741_facts record009_frame020_indices record009_frame020_graph record009_frame020_links
def record009_frame021_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x53aa6f4da8f517a29402724c898930a5dc9191720e34c4884f0921041b7e4f45dd3b6762eadbbb726d8d65a9b4c68cc718b3115deb2d5bab155caa53a2564949091fa394107f0fa9ec3c0768ea19d2f25ccb61662c64fc9b92c2464748890d1d03806d8cc18c3005b0b01562a0520841062003f8670cc190310590ae1582985109a1301b0350660c81402604a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record009_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record009) (record009.maps 21) (record009.inverseMaps 21) record009_frame021_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record009) (record009.maps 21) (record009.inverseMaps 21) record009_frame021_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record009) (record009.maps 21)
      (record009.inverseMaps 21) record009_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame021_links_0000 record009_frame021_links_0064)
theorem record009_frame021_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 21 :=
  of_group record009 21 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record009_frame021_indices record009_frame021_graph record009_frame021_links
def record009_frame022_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x85b85184a82081080b7e97bb78c78477d7737317237166f36ce69e69768c6846466105e95e15d45c257256c56254853e5325274dd4d44cc48c45443142141340b3c63a539738b38337832b31730a2ff2ee2e62dd27b23c23422b21f2161d21c71b91a91a018b18113a12e12510c1050fc0eb0e10d90d20ca08e08d08a08906e06c06a06805f05c05b05805605205103703603303202902702502302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record009_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record009) (record009.maps 22) (record009.inverseMaps 22) record009_frame022_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record009) (record009.maps 22) (record009.inverseMaps 22) record009_frame022_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record009) (record009.maps 22)
      (record009.inverseMaps 22) record009_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame022_links_0000 record009_frame022_links_0064)
theorem record009_frame022_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 22 :=
  of_group record009 22 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record009_frame022_indices record009_frame022_graph record009_frame022_links
def record009_frame023_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0439.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0439.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record009_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0439.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0439.localPairCheck (smallEmbedding record009) (record009.maps 23) (record009.inverseMaps 23) record009_frame023_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0439.localPairCheck (smallEmbedding record009) (record009.maps 23) (record009.inverseMaps 23) record009_frame023_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0439.localPairCheck (smallEmbedding record009) (record009.maps 23)
      (record009.inverseMaps 23) record009_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame023_links_0000 record009_frame023_links_0064)
theorem record009_frame023_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 23 :=
  of_group record009 23 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0439
    Papers.RationalityTen.SharedFrameCatalogue.group0439_facts record009_frame023_indices record009_frame023_graph record009_frame023_links
def record009_frame024_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0408.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0408.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record009_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0408.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0408.localPairCheck (smallEmbedding record009) (record009.maps 24) (record009.inverseMaps 24) record009_frame024_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0408.localPairCheck (smallEmbedding record009) (record009.maps 24) (record009.inverseMaps 24) record009_frame024_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0408.localPairCheck (smallEmbedding record009) (record009.maps 24)
      (record009.inverseMaps 24) record009_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame024_links_0000 record009_frame024_links_0064)
theorem record009_frame024_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 24 :=
  of_group record009 24 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0408
    Papers.RationalityTen.SharedFrameCatalogue.group0408_facts record009_frame024_indices record009_frame024_graph record009_frame024_links
def record009_frame025_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0300.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0300.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record009_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0300.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0300.localPairCheck (smallEmbedding record009) (record009.maps 25) (record009.inverseMaps 25) record009_frame025_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0300.localPairCheck (smallEmbedding record009) (record009.maps 25) (record009.inverseMaps 25) record009_frame025_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0300.localPairCheck (smallEmbedding record009) (record009.maps 25)
      (record009.inverseMaps 25) record009_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame025_links_0000 record009_frame025_links_0064)
theorem record009_frame025_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 25 :=
  of_group record009 25 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0300
    Papers.RationalityTen.SharedFrameCatalogue.group0300_facts record009_frame025_indices record009_frame025_graph record009_frame025_links
def record009_frame026_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0249.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0249.count (({ width := 9, code := 0x12a93c8e3f1c8cc52210983c1a0b027f3edeef074ba1cae470365a6d268b398cc4613017ebe5eae96eb35729d46a04ea71309146a2912863f9f0f4793b9d8ea6d349a0ce6531970b6592b954a6522592892462210c82401f8f87a33190c4602b150a450251208c44200f87834190c05c2813090441e0e0682c1409040180a04018080200 } : Fields).get c.val)
theorem record009_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0249.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0249.localPairCheck (smallEmbedding record009) (record009.maps 26) (record009.inverseMaps 26) record009_frame026_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0249.localPairCheck (smallEmbedding record009) (record009.maps 26) (record009.inverseMaps 26) record009_frame026_indices (Fin.ofNat record009.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record009_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0249.localPairCheck (smallEmbedding record009) (record009.maps 26)
      (record009.inverseMaps 26) record009_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record009_frame026_links_0000 record009_frame026_links_0064)
theorem record009_frame026_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 26 :=
  of_group record009 26 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0249
    Papers.RationalityTen.SharedFrameCatalogue.group0249_facts record009_frame026_indices record009_frame026_graph record009_frame026_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (Fin.cases (record009_frame004_supported hcells) (Fin.cases (record009_frame005_supported hcells) (Fin.cases (record009_frame006_supported hcells) (Fin.cases (record009_frame007_supported hcells) (Fin.cases (record009_frame008_supported hcells) (Fin.cases (record009_frame009_supported hcells) (Fin.cases (record009_frame010_supported hcells) (Fin.cases (record009_frame011_supported hcells) (Fin.cases (record009_frame012_supported hcells) (Fin.cases (record009_frame013_supported hcells) (Fin.cases (record009_frame014_supported hcells) (Fin.cases (record009_frame015_supported hcells) (Fin.cases (record009_frame016_supported hcells) (Fin.cases (record009_frame017_supported hcells) (Fin.cases (record009_frame018_supported hcells) (Fin.cases (record009_frame019_supported hcells) (Fin.cases (record009_frame020_supported hcells) (Fin.cases (record009_frame021_supported hcells) (Fin.cases (record009_frame022_supported hcells) (Fin.cases (record009_frame023_supported hcells) (Fin.cases (record009_frame024_supported hcells) (Fin.cases (record009_frame025_supported hcells) (Fin.cases (record009_frame026_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))))))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x18d4c5061cb075806bee59aac71628aa653026d533098f4aca4d9258871433a12906081b4071f70f8c75e3a81d14e7472f3931b80d8c6b234c99f0cc25ed2ef1748b8e5bb2d91698b2e58a2bd95b8aca50827513489804b224f124090445f2280f8478a3bd1c60db06c435419d8c9c62a2b81528a4c4ba23411107803861b90d686583081740b184382020d706481bc0dc05d02e016c0ae05601c80dc06c026012809004602100f8078028013009004001e00e0050024010005002000c002000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record010_frame001_links_0000 record010_frame001_links_0064)
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
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x30e57dcb525a1acd5654b1c58a2b49572aa6545a9d14c09b54cc263d2b293649621c509483040da02cfb87c63af1d40e8a73a3979c98dc06c63591a64cf86612e916ecb6458a2b715949a44b224f124090c45f22810047e03e11ea0f1477a3ad1cd8e306f636c1b10d4067632718a8bd05a62b814989644682220f0070c3721960c205d02ca110080835c19207103781b80ba05c02d815c0ac03901b80d804a024011807c03c01500a004c024011008003c01c00c0050024010005002000c002000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x12b24dc728d91a231c5f8b91221f43285707e09be57b4f4de33bc762e15bdb756dcda9afb5864cc858eb19628c3d7caf25cab75692c3526a1d3f26f4cc9751922a4468750ca0e4107b0f29db3a8730e19bc36a6b8d219c326624c197e2f05bcb014f28a4cc9291c2103e4768e01ae338640b115a2704b8640c61882a8540a613c270340660c81282404607c0f01502804c0901102003c0700c0140240400500800c00800 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record011_frame002_links_0000 record011_frame002_links_0064)
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x14c68dcef9cf3926fcd89ad2f2574a59372364044e87f0ea14c1d82cf81ea3cc788f01d8baa6eedc1b53656bed699db2d64ac6585aff58aae15929f52aa392e25449891921a36460831011f93e479cf09dc3a472ce19b93626a0cf19531c610ba9672b25089992a2264147e8ed1c636c6a8b61602704b86e0da1b02e85c0b615c2b03906e0d81282404607c0f01502804c0901102003c0700c0140240400500800c00800 } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record011_frame003_links_0000 record011_frame003_links_0064)
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
def record011_frame004_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x36e9a56c0a5fb2f7d796bb55d02ca9604adb55a2a314c49944b7257123c8fa473a0c101c7f73f29f6cf6a7a536b1b08d5669734099b0bec5ce2d39600ab052e23010e88503ea1e30ecc5f82da1618ac454e28113888e446422b112087442c20f10408043f41f30f6078c3b81d50e707083681a60cb86042e616c0a9051027a12d093047c2320f607803681aa07103781b80ba05c02d815c0ac03901b80d804a024011807c03c01500a004c024011008003c01c00c0050024010005002000c002000 } : Fields).get c.val)
theorem record011_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record011_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 4)
      (record011.inverseMaps 4) record011_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record011_frame004_links_0000 record011_frame004_links_0064)
theorem record011_frame004_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 4 :=
  of_group record011 4 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record011_frame004_indices record011_frame004_graph record011_frame004_links
def record011_frame005_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6f46cf66b66365a65064764161c6085f95eb5db5ce56c55a55553d52a5254c94b34a449749147946d43142841f4194104073e13d03bf3b03a239433132231b3012f22eb28f27926725c25723c2322092011fa1f21eb1e51e11d91d01c81bf1b91b41ad1a619e19017f17016514d1401371221161101060ff0f70f20d40d00b90b406f06d06c05b05a05905505403903703602502402301f01e01501401301201101000f00e00c00a009008005004003001000 } : Fields).get c.val)
theorem record011_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record011_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 5)
      (record011.inverseMaps 5) record011_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record011_frame005_links_0000 record011_frame005_links_0064)
theorem record011_frame005_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 5 :=
  of_group record011 5 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record011_frame005_indices record011_frame005_graph record011_frame005_links
def record011_frame006_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x13c26c4ae94d27a4dc979292123ec768dd1962d42783d06200bf47d6eb1d0b9c72ae41bf3766aad2da3b42680ced8f30f606be978ae555ca954fa9451ea2129a454788d116223438800fc1ee3ce788ee9d739e720e01ba3686b0d29a133a648c21752ce53c9f136236434820f41d43886c8b71622884d0670cc1942a0530a413c270350660c81202304407c0f01502804c0901102003c0700c0140240400500800c00800 } : Fields).get c.val)
theorem record011_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record011_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record011) (record011.maps 6)
      (record011.inverseMaps 6) record011_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record011_frame006_links_0000 record011_frame006_links_0064)
theorem record011_frame006_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 6 :=
  of_group record011 6 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record011_frame006_indices record011_frame006_graph record011_frame006_links
def record011_frame007_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x7c37957397317297237197166f36e96dd6d16c06a865063f6356196025f358557556b56055953f5314ef4e14dd4d84d44cc49848246d45e44f43a3d83c93bd3ac3a539d33b3263163093022ef2e52b12a729929128427b27226625c24f24723c23122821f2162071f11dd1c81ab19618a16415214712f12411810d0e30dc0c10b906e06c06b05a05905805405303803603502502402301f01e01501401301201101000f00e00c00a009008005004003001000 } : Fields).get c.val)
theorem record011_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record011_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record011) (record011.maps 7)
      (record011.inverseMaps 7) record011_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record011_frame007_links_0000 record011_frame007_links_0064)
theorem record011_frame007_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 7 :=
  of_group record011 7 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record011_frame007_indices record011_frame007_graph record011_frame007_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (Fin.cases (record011_frame004_supported hcells) (Fin.cases (record011_frame005_supported hcells) (Fin.cases (record011_frame006_supported hcells) (Fin.cases (record011_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record011_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284
