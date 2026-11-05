module
prelude
public import GraphInputsRow29Part00130Data
public import RawFrameSupport
public import SharedFrameGroups046Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x160ab45489a92ee50c6d8d10b6134147fefc5f43d77a2ef5ca36169ad0d98b26616b19622be54a9d9392624b29211aa2f432844e81c737668cc21702ce55ca693d2624788b10c20e3e0738db1aa340600bb14c21c428800dc1b0338590aa1502885009e1001f03d06c0bc138260460881081f03c0740c8120200380680b0140240400400600800800 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x2ec56fab4d501274936691d480a15d08680f3ed9f10f5a77d3b59ca4d6264730717fcbc25d22da1494a2850226b91f88e245722490bc82e40b1f38f6c6783221830b6453426d130091c47422610887c83ca1c30da06402da1540a184c420c0fa064026c13209103c01d40dc05f02d81680ae05602a810007c03d01b00bc04e026011808804201f00f0074032012008003801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x198ac59546294141693448e23e9182873431a0c0ff67db3d29e4ce4a55828e135c8003e81e30e3467e32f17e0b1c54e27112f895441e2060ff87e83e61e50ef06e83681a60cf864430216c0b2856028813d09784a023210c07b03c01aa09b04881e00ec06e033017c0ba05b02d015c0ac05502000f806c02e013809404602200f807803a01a00c8048022010007003401800a004802000a0040018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x169ab17509278936691a47ea36d14885a422a03cfb67c23be9dace5260e2f096d0a5251027a132492048022b90bc8363e71ed8f246a03381910c5460c2e816c8a244f026012908e84441f20f287143381900bc85b42ac13108403ec19009b04881e00ec06e033017c0ba05b02d015c0ac05502000f806c02e013809404602200f807803a01a00c8048022010007003401800a004802000a0040018008002000 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x6766575bb59d57b5225114fd4d94b04a949247546844643b41b37e35d33f2e62d52bd29a27426d24f23922c2071fe1f91c11b91b21ae1a619618e17116b15d15514713c12e12711d10d1070f90f30ea0e00cd0ca0b309908f07707506d06505e05c05a05905605505404003e03602e02702502302201f01e01d01a01901201101000e00d00c00a009008005004003002001000 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcc262caacd53e9fd4a4a43d1fa8d746222550ea8634181fecfb47c93d19e44e4a57f2b5932482a3db1e48e8c7203611a08cbc5f82c71530a544de25d12a883c40c1ff0fd07cc3ca1de0e086e834c1910c105ec2ea1600a5851027a13609784a023011108183f01ee0f006a02bc12207803701a80d2067033017c0ae05602a810006c03201880bc05c02700f807803a01a00c80480220100070034014009004001c00c005002000c004000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa049ea93492b8b784681f80c7e37d27a378f77f7507136ee6dc6b169e6805d15c85564fb4dd4cf4af4a147b46c45f4364043e73d93b43a439c32d31e3113052f52d92cd29528525a2282081f91e91c21a01911831731651561351291090fc0f30e80b309f08b07606c06806706506405d05505405304003603203102f02e02701f01e01d01a01901201101000e00d00a009008007006005004003002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xb4c58ba8e54409a449923bd1bc8b8453a2110b88454079f6cf827ac3be1da8e5263130e169ca7c50527b93689984b124912008ae42f20d10287cc3da1e48d4067032218a8c185d02d914e0a244c023a11188484021d60d406703201850bc85b42aa14209104582120fb06382ac12207803701a80d2067033017c0ae05602a810006c03201880bc05c02700f807803a01a00c80480220100070034014009004001c00c005002000c004000 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record002_frame003_links_0000 record002_frame003_links_0064)
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x6756575cd5c357552e50a4ff4e84db4c24b24a949247546745c44543a41b3913873392f22cc2bf2a729c28627626d24f23922b2202061fd1f91c11b91b21ae1a619618e17817115d14713d13913512311410d1071000f90f30e90e40d90d30ce0ca0b20a608f07706d06906806606505e05605505404003603203102f02e02701f01e01d01a01901201101000e00d00a009008007006005004003002000 } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record002_frame004_links_0000 record002_frame004_links_0064)
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
def record002_frame005_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0606.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0606.count (({ width := 11, code := 0x4f29d12a2514778a70d21541b828ff5f6be2790ea9cd3916f6dc1b2321638ba567ab955ea814da844f09b92c23e45c89508a0940677ceb1cc38a6f8d71a73105f4b495428c4fc9d1262164147f8f91e83ac6e0d317e2d8570a61081e8368630bc1682c8570ac1442484808e0f01a03005e0b41602703e0780e81a0320480881001c0340500901001c0300500800c01000 } : Fields).get c.val)
theorem record002_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record002_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record002) (record002.maps 5)
      (record002.inverseMaps 5) record002_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record002_frame005_links_0000 record002_frame005_links_0064)
theorem record002_frame005_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 5 :=
  of_group record002 5 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0606
    Papers.RationalityTen.SharedFrameCatalogue.group0606_facts record002_frame005_indices record002_frame005_graph record002_frame005_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (Fin.cases (record002_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x31497c0bb15bead354849f14e0a6cd240900432a1090407ec3e21e50efa76b35898a8c1c5ef2f09708b685aa291944ca044d7252923c8fa47123211248784171fc8f9c7b63371918bdc59429a136898048e23a11307fc3e41e50e406cc3381790aa0510260106075032013609103c01d40dc05f02d81680b005602a812008003e01e80d804e026011808804202000f0074032012007803801a00b00500240100050018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record003_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130
