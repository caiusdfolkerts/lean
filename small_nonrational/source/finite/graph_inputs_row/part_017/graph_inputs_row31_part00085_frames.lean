module
prelude
public import GraphInputsRow31Part00085Data
public import RawFrameSupport
public import SharedFrameGroups034Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups090Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups109Checked
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
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085
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
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x6fc3759b60d3e68b34099dcc8d5c9adc5696ad9558aa75512a284d5a6a134299a4c9a63130e97e4b825892ba94f4a4250126292348e244121290247d23c91ce8e040f9fe4fa47513929c40df66962e91700b585992c315c8ac253d28c140c9be4cf25e92688ee46722090c08424112010d8c6a233d1950c5c6062f21670aa452827013009384562080fc07483821b20d1064c2aa1500a48508276134095849023a116087842c2060fc07b83c01d00e206e03601a00aa047023410e06b035013c06603201800a80520280138098048023010007c03c01c00d8054028013009004401e00e0058028012007 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 128 144 :=
  interval_of_check _ 128 16 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 144 record001_frame001_links_0000 (interval_append _ 64 128 144 record001_frame001_links_0064 record001_frame001_links_0128))
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x66232c5940c5961fb0e1852bed5a1aca9628ac75572a9d534a5f4e627253769ac4cf26453149724a7a4bd2508f8471232d14a88243a215908082b4099fecfac7c03a81ce8e4c6d835f1accd4c6602ed973cb885b82d89690b2e57b2b29558a6852628c13e49b64d225792809244832388fc07c23d41e28ef475639b1bd8d886a032718a8c145c62c215c0a484fe26d12d09243f01f10f1875038c1ba0d3064c3041720b0855027a12d09204501fa0ef07103681880a6047023410e06b035013c06603201800a80520280138098048023010007c03c01c00d8054028013009004401e00e0058028012007 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 128 144 :=
  interval_of_check _ 128 16 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 144 record001_frame002_links_0000 (interval_append _ 64 128 144 record001_frame002_links_0064 record001_frame002_links_0128))
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x6ff6f56ed6c56b56af6a968062a6206155f05e15d75d15a855d55b55454f54854454053952c52051c50e5054fc4ee4e14dc4d14ca4c24b94b14a549d46e46245742d41940f4083dc37e37436936235d35234b33832b32230c3022f82e92da2d42bd2b22a829e29323f23823122721f21420b1fc1ed1e41cd1c31ba1aa19d19617f17216916015512812311c11610f10b1030fc0f50ef0ea0e60dd0d60d20cc0c40be0b90b60ad09808208107f06906804f03303203002a02902802702602402302001f01e01c01b01501401301201100f00e00b00a009007 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 128 144 :=
  interval_of_check _ 128 16 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 144 record001_frame003_links_0000 (interval_append _ 64 128 144 record001_frame003_links_0064 record001_frame003_links_0128))
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0xd25a2f3f66ccc796329e45c2b826fbddcb9b702dbda4aed5ceb5560aa9526a1d3ea5945e864f79cf35e66cb995726645c7b8d719e2ec56849072063eb7bcf51e4bb6700de1b7b636b2d4da6b3e654c75852ff5eebb16dace576ab951a9c5329912ca4f4868e117a2843681cfd9ea3ba75ce59bc35e670c91852fe5ecb115e2a85289f933242458840f81e03ac700d61a231c5f0b41542944d0890f41e43a8610c011c198320600a81482804e0981202304007c0f01c0360540a0130240440780e01602804807 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 128 144 :=
  interval_of_check _ 128 16 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 144 record001_frame004_links_0000 (interval_append _ 64 128 144 record001_frame004_links_0064 record001_frame004_links_0128))
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x9c536a684c296f2c2554978e11a22e44e88d0f61b4237f6fe5fa3ef7d0f85ef3d879af01ddbac746e69c83856f8dc5b435f6aad3da3b4364ec7586afa5dab8d6faca53aa5946a844fa9e93b26c4c2971262424768c51321c41e814fc9f43de710df9b7358690cf99a320600bc9692ba55ca814627c4c89491f2324547e8fb1ec3c0750e51b8354680ca18c3145e8b71662b8540a313a264488890ee1d83a0620c21201883005c0a41402704c0941182203e0780e81b0340540a0130240440780e01602804807 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 128 144 :=
  interval_of_check _ 128 16 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 144 record001_frame005_links_0000 (interval_append _ 64 128 144 record001_frame005_links_0064 record001_frame005_links_0128))
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x88b0f61cc238390620a3fe7a0f25dfbb475ee9dd1b8d6dcdb5b43646c0d6dabb53694d099eb3465eca59131b628c2d833005f6bd975ae4578abd522854f69d137a4f4488710aa1041a825039fc3ee7bcf21dd3b0738e21c13646acd31a233a5e8ba1702d0584ae1562a05149f1302524988f11a22841c7f0f91ec3c86f0db1ae34c668c91863005e8ba16e2d4580ab15229c5109d13225c4a07e0e01bc3685f0bc11c1782e0580a01382604a0901102103c0740e01a0320540a0130240440780e01602804807 } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 128 144 :=
  interval_of_check _ 128 16 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 144 record001_frame006_links_0000 (interval_append _ 64 128 144 record001_frame006_links_0064 record001_frame006_links_0128))
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (Fin.cases (record001_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3a41bfadce6dbb4a17ecbcb5d02c5d5e4ade563a97d3669914b5a5652908e746b22ad13086442120c10167f93f39f20d84697336178cb7c5aa2c994ac8fe45d21b90948283b31d10ddc6c83301870bf05ae2c51598a5046422b112087442c20d10407e83d81e30ea87383901bb0d6869832c18f0c406082f815f0a9051027a13508c844c1fc0db047023410e06b03501840c005f02e016c0b005702b015009e03301900a4050027012008c04001f00f007003601500a004c024011007803801600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x32818b2c3f61c2fb5686b2a58a2b1d55caa754d297d3a49b24caa6392fc92c48da3a11a489e43da1c508e83240e9fd0ea073a3931b60d7c6b33531980bce5cf2dc16c4b505652ad14d0a4c4f926d934895e4a024911c47e03e11ea0f1477a3ab1cd8dec6c43501938c5460a2e31610ae052427f13689684921fc0f0070c3721aa0b285442420d8047023410e06b03501840c005f02e016c0b005702b015009e03301900a4050027012008c04001f00f007003601500a004c024011007803801600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x7287076f76f36ce6636506416156015fa5f35cd57a56a55855454f52551e5034f64df4ce4c94b04a54984854284194073da3c93c03b939334032f32031a3152eb2e42c62bd2a229428f27626825d24b2011fa1f21eb1e51df1d91c81b91b41a619e19718817717016415d15514e14a12c12211611010c0f20ee0da0ba08a08908306906805f05e05d05a05905605505405204d03303202902802702402302001f01e01c01b01501401301201100f00e00b00a009007005004003002001000 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record002_frame003_links_0000 record002_frame003_links_0064)
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1940c806343139870c2b5f6acd5638b14576ab1d55caa753e29954be9dc4c724b12068e846923210e2864425a0c903a7f13a29cbce4c6ec3719b60d926be3599a8cd0a6683301798bb65c42d8969caca54729a1498a2a50827513489844b3250124890846e1ff0f8478a3bd1c60db06c433b1938c546062e31610ae055429213f89b43fe1b90d4065c2a012108704001b008e04681b00d606a030017c0b805b02b81580a804f01f80d006603201500a004e024011808403e01e00e0050026012008003c01c00b005002400e0040018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record003_frame001_links_0000 (interval_append _ 64 128 130 record003_frame001_links_0064 record003_frame001_links_0128))
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xe906dbb4a17bebb55d02c5d5e4ade54ea9d14be9b24d125f92b2947473a30d156898444a0c101e7f93f39f14d56681336178cb7c5aa2b49500a5647e237112884a4131d98e3c6ee3641aa8bf05b62c51598a4446422b112087442c20e10087cc3d81dc0ea87383901bb0d6869832c18f0c405782b214b09e84b823411207f03dc1de0db047023410e06c03581a80c406002f81700b605702b015009e03401980c8054028013809004601f00f007003601500a004c024010007803801600a004801c00c0040018008002000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xca061c2fb566ab1c58a2b1d55caa753e29954be9d14e1a69931c97d496240d1d08d2461a1c509683240e9fc4e8a72f3931b60d7c6b334299a0cc05e62ed9710b625a72b2951ca6852628d13489664a024911b87e03e11ea0f1477a3ac1c60db06c433b1938c5460a2e31610ae052427f13687ec3dc1d10dc865c2cc15009084442000d8047023410e06c03581a80c406002f81700b605702b015009e03401980c8054028013809004601f00f007003601500a004c024010007803801600a004801c00c0040018008002000 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame002_links_0000 record004_frame002_links_0064)
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x7286f36ce65a6476416156015fa5e15d05cd57957356155454e5255125034f64ef4c94b44a549848241f4104073da3c93c03a539839333f33832931a3142eb2d82c62bd2b528f27a26825d2482011fa1f21eb1e51e01d01bf1b91ad1a619e19718817717016415d15512b12811c1101070f30ed0da0d50cf0ba08a08908306a06906806005e05d05a05905505405204d03403303202a02802702402301f01e01c01b01501401301201000f00e00b00a009007006004003002001000 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame003_links_0000 record004_frame003_links_0064)
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
def record004_frame004_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xd5f6633255786b9f5c5ac855faae9566aafd570a2e50da7ad37a9ab4a9a4bd23290847c22810f886642aa10ceda74739a1b0cd3a68a3371980cb25e22e916c4b1257a29a9468a104fa27692a091a47b236917c7aa3c01d48e546fc36c1a78cc063e2fc1760b6c5962ae14789f84b624b11d08103e41cc0d105ec29013b08c042c1fc0db047023410e06c03581a80c406002f81700b605702b015009e03401980c8054028013809004601f00f007003601500a004c024010007803801600a004801c00c0040018008002000 } : Fields).get c.val)
theorem record004_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record004) (record004.maps 4)
      (record004.inverseMaps 4) record004_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame004_links_0000 record004_frame004_links_0064)
theorem record004_frame004_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 4 :=
  of_group record004 4 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record004_frame004_indices record004_frame004_graph record004_frame004_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (Fin.cases (record004_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xf976dd34a17bebb55d02b6d4bea3a51128393629a54ca26052dc95c4a2a4791f48e7418208101c7f73f29f1cd56681336169ca5650627713688fa47123011348744282088fa878c3b317e0bb05b42c31588a4c46422b112087442c20e10087cc3d81dc0ea873834c19e0cb85ec2ce1590a9052c28813d09a04b424c11f08d03dc1e00da047023410e06f03701ac0d406802e81700b605702b015009e03701b00cc064030012809004601f00f007003601500a004c0240100078038014009004001c00c005002000c002000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xcff61cafb566ab1c58a2a994bea3950fa8313a09c54daa6a133098f4bda56526c92c438a18109483040d9fcce8a72f3931ac8cc06433169870bca5de2e9171cb765b22d29628adc565269131496449e24811c07e03e11ea0f1477a3ac1c60db06c433b1938c545702a714989204201ee0f007443861b90d486583081740b304442020d7047023410e06f03701ac0d406802e81700b605702b015009e03701b00cc064030012809004601f00f007003601500a004c0240100078038014009004001c00c005002000c002000 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x71cb5e5aa6d506a4b509a76d3468534119facf16752f556ecb6f5ae2d31678b285582a8551aa7252fa8294069f04f0274137894449aa48520c8f3476a3a11c28da469a33118e8c045ca2c91528a244ca24911c7803909c70e1a6fd3769b74ce466332818c8c425cc2e396e0b505982c41474a1c4fb26e933098c4c125d12cc95a4a6250926892648c24191f48ea46f2360c6455229914509e84d621d107071836c1a70cb862027412b07b83c01d20e206a02f81600af055027013607703581a80d005c02d80fc066032018009004601b007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record006_frame001_links_0000 (interval_append _ 64 128 140 record006_frame001_links_0064 record006_frame001_links_0128))
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x67f327d8dec6c62fb14988ac3a5f82fa57a6bab5caac555b8ad7564aaf9560aa852fa945476a1c504a73538e9b84d5266d32092c48ea4151ca8cf45f22cd14289043f21c90d885541fa0a90187f73ec9f0cf767273751b94db46cb3601ad0cc065732298a4c305e22f01750b925bd2d99594ab85492981488a2850b27e13b49bc4d326792ec95049a24391d08b844d2248d885e82e31698b0857025b12487b83c01d10e186e42cc15108783fc1e40e506382c81540a9053027013607703581a80d005c02d80fc066032018009004601b007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record006_frame002_links_0000 (interval_append _ 64 128 140 record006_frame002_links_0064 record006_frame002_links_0128))
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb18ad1abaab8ab3aaaaa1a9aa55a46a39a18a039a597d97a97096395894e9038f68e98cf8bd89188b8808728638557f77e47d37b87a179a79378377276375374673271e7096f06de6c36b06aa64061761560c6015f55e859d59158456955b53c53952f52451750a4bd4b04a248947947447046345544743942d41d40d3fc3e93db3c23b33ae2e729628627526725a2091fa1ba1ae1a019118313712b0f10e60d90cc0b20a40a009f09c09609507506906806605a05903f03303203002402301b00f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record006_frame003_links_0000 (interval_append _ 64 128 140 record006_frame003_links_0064 record006_frame003_links_0128))
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
def record006_frame004_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x6a468867e67d67c67a67767366065c65864e6476185ff5fd5f75f05e85e25ab5a259758657756055f55a55454c54350c5064fb4e74d84d34d14cc4c64c14bc4b84b24ac4a549d49748f48948544642842741f41940e4063d43cd3c13ab39e38538438037836f36333132b3223082fb2f72f52f12ec2e62e12dc2d62d02c92c22bd2b62b22b02131d51cc1c41b91b117c17314613e13412c1210ed0e50bb0b70b20ab09e09609109008e08908807306806706505a05903d03203102f02402301b00f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record006_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record006_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record006) (record006.maps 4)
      (record006.inverseMaps 4) record006_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record006_frame004_links_0000 (interval_append _ 64 128 140 record006_frame004_links_0064 record006_frame004_links_0128))
theorem record006_frame004_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 4 :=
  of_group record006 4 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record006_frame004_indices record006_frame004_graph record006_frame004_links
def record006_frame005_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x85f0820ec1c8330620bc1481100e003f97e6f59e43c677eef1dbbb3720e2dc13776e0d95b1b5f6b6d5da832d652c858a30d612c21823015fcbe97baf05d2b916e2d659eb2964a9750aa0d3ea7a4ea9c527a4b4868e118a224408710c21441c7b0f49e23aa738e51c938a708df9bb36e6c4d59a633e664c918e31a4e89211e236458898fc1ea3686b0d31a232c5a0ae128240460881041f43d0790f01d43a0630b61682c05009e0dc1782e0580901181b01e0380600b0140240380600a01001801 } : Fields).get c.val)
theorem record006_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record006_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record006) (record006.maps 5)
      (record006.inverseMaps 5) record006_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record006_frame005_links_0000 (interval_append _ 64 128 140 record006_frame005_links_0064 record006_frame005_links_0128))
theorem record006_frame005_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 5 :=
  of_group record006 5 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record006_frame005_indices record006_frame005_graph record006_frame005_links
def record006_frame006_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x7ca3a35c44e1b701b7b5ba8dbd698b471a0acd9660ae8d670b3058d2c215eaae152fa945478a1d504a6b93509974c225c52be8e746c231514c893441a1e50ce855422a0cd0508174029fc8fb87cb3d91e88f3a66f30217f0bcc5d42e096b4a5651d28413a49aa47a23a118c8a043d2158ecc7483911b90d7c69e3451998c846222ff17a0b8c5a22be1540a5c4fc26e13487b03841bb0da06b434c1830be05642a414b0a204f423411307a83b81ce0e006982f81600af055027013607703581a80d005c02d80fc066032018009004601b007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record006_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record006_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 6)
      (record006.inverseMaps 6) record006_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record006_frame006_links_0000 (interval_append _ 64 128 140 record006_frame006_links_0064 record006_frame006_links_0128))
theorem record006_frame006_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 6 :=
  of_group record006 6 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record006_frame006_indices record006_frame006_graph record006_frame006_links
def record006_frame007_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x8b987e86285f85985384d84682381d81780c80579775975474873e7347286e46d76cb6b66a866c66365564b63f6325e65d65c85b059e59658f58757f57756f56a56155955054553d53352b5284b447246945b4514454383ec3dc3ce3b63a436b36635a35034633a2f62e92dd2c82ba2b32ac2a429c29428c28727e27626d26225a2502482451d81b01a81a119919016916213e13612f12711e0f70f00d40d00cc0c80c00b40aa0a90a609c09b07706b06a06805c05b03f03303203002402301b00f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record006_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record006_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record006) (record006.maps 7)
      (record006.inverseMaps 7) record006_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record006_frame007_links_0000 (interval_append _ 64 128 140 record006_frame007_links_0064 record006_frame007_links_0128))
theorem record006_frame007_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 7 :=
  of_group record006 7 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record006_frame007_indices record006_frame007_graph record006_frame007_links
def record006_frame008_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x9c934264cc798b312614bf95d2a6514989251ea334658bf16e2b4528630ba12c1881afe5fc3f17d8f9df03b7766e99cbb8a706dfdbcb746dcda9b335e6aad39a3340672cd599b17600bf97caf35dcb9d5f2b7560a7948a7f4fc9e93a2704d69292323f4628991021b42c841062074067e8f91eb3c4774eb1d23a0628b61672c0564aa12f250428810fc1ea3c0658c415228c4f89c1282404608b1142184286c0c41842f8530a40f41883005c0901181b01e0380600b0140240380600a01001801 } : Fields).get c.val)
theorem record006_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record006_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record006) (record006.maps 8)
      (record006.inverseMaps 8) record006_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record006_frame008_links_0000 (interval_append _ 64 128 140 record006_frame008_links_0064 record006_frame008_links_0128))
theorem record006_frame008_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 8 :=
  of_group record006 8 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record006_frame008_indices record006_frame008_graph record006_frame008_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (Fin.cases (record006_frame004_supported hcells) (Fin.cases (record006_frame005_supported hcells) (Fin.cases (record006_frame006_supported hcells) (Fin.cases (record006_frame007_supported hcells) (Fin.cases (record006_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
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
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x71736c9a32c9564632017d2b4755c2abd5469d64a9a4b12368a043ca1a0f147583701ab8ce866732c9910bc659d2bd94d4a4651728513b895049624511f48c83ea1ca8dbc63e30b17e8bb859c27e135097049a2300f006dc34416a09e03fc1640af04d824411c08d04601e00dc06b03501a40c205f02e016c0b405702b01540a804f021810007203601a80cc064031014809c048023011007c03c01d00e005002400f0070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x75db831ad0c8d63a314174eb03514283d3d69924b0a54929891b48624190567f63b89ce0dc86c034b1958bc05992bb1460a044f327093008ce45222110c881e3711950c1c55229314209c84a21f80f1874c3861a00a404e826611e08503a41640af04d824411c08d04601e00dc06b03501a40c205f02e016c0b405702b01540a804f021810007203601a80cc064031014809c048023011007c03c01d00e005002400f0070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0xbeb73acfd5faaf532974f89712c252c6e8850ce163fd7dcf9dd9ba0702db9ac34e688cc5822e65b2aed582a8544a45382644b694d1fa043cc75cdb1aa342664c31682ba554a793f22a424810ee1b42f04c89610c2003e87c0f61bc328620c21802c0560a61482884e09a130258490840fc1c83606a0cc1903105209c1202304407c0f01d0380500900f01c0340500901001c0280400600800800 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
def record008_frame004_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0639.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0639.count (({ width := 9, code := 0xd467f3590c5e1eff78b659ec759a852a8f3b9acca471f8d45a270e84c05f4f67abadcee471b81acd368b3d92bb5bad958a953a9540964923d1c8a3e9e0e86c341749c4d259248c4522108803d1e0ec6e36198c8622e168b0562a148a04e261288c44211007c381b0d05c2c150a04c240f0703414090401c0a04018080200 } : Fields).get c.val)
theorem record008_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0639.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record008_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record008) (record008.maps 4)
      (record008.inverseMaps 4) record008_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record008_frame004_links_0000 record008_frame004_links_0064)
theorem record008_frame004_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 4 :=
  of_group record008 4 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0639
    Papers.RationalityTen.SharedFrameCatalogue.group0639_facts record008_frame004_indices record008_frame004_graph record008_frame004_links
def record008_frame005_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0636.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0636.count (({ width := 7, code := 0xf3e3bf6ebd3971e1bf76cd7ab4e7cd971e2c382fdebb72d59b15eb55a94a8d09f3a64b95264478d161c28301fbd78edd396ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record008_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0636.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0636.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0636.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record008_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0636.localPairCheck (smallEmbedding record008) (record008.maps 5)
      (record008.inverseMaps 5) record008_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record008_frame005_links_0000 record008_frame005_links_0064)
theorem record008_frame005_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 5 :=
  of_group record008 5 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0636
    Papers.RationalityTen.SharedFrameCatalogue.group0636_facts record008_frame005_indices record008_frame005_graph record008_frame005_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (Fin.cases (record008_frame004_supported hcells) (Fin.cases (record008_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xe4171d38bdc44da46c2b589a16cec664b2d9962caa652327592cc91641b1f17ccb885a22b995b8ace5602ae5566aab5512a6d3809a44c325912a694748ba4191e28d3458a281128864429a13508883d41b20c0f227313739a1ccfa66f3309968ca864c32198f4b185742af950ca6a52d28313e09ce4d225b12a0940479235919c8c045b22b11486fc34f1980c7c5fc2ae14789f84ba22a111887042a1e00db86882d015508b83681a40a404d01e40f006f03701740b805b02c015c0ac04102000dc06c025012008c04001f00f004c024010007803801a00b0050024010005002000c002000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record009_frame001_links_0000 (interval_append _ 64 128 141 record009_frame001_links_0064 record009_frame001_links_0128))
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x3b65d7ce9f6d833fd9e8c8d63f3139874b4b54d2a3d450a194f4a7553169764b4258529494348da3c11b881f3fc9f48ec07383869bd4dc86c034b19fcca863f2f29618ae254f2959460a0e4df26793008ce45220790047a237618b8c085c02bc1548a604e026012887e03c61a00c9058829013a09984941ec0e9049024411c08d03781b80d606a030017c0ba05c02d815c0ac05502a012407203701b00d4066032014009c04a024011807c03c01d00e004c0240100078038014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
def record010_frame002_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x346da1acff65030dd85ebed5f1aebd732b145532a7d4bea5250fa83131c95949b24b11d08d24389fccf6275039d1c98dc06c63591a80d2c6793301944c5a61c2f616c4b4658a2b71594ab4534293146c9a44c124091c08844031de8ea871836c1b10d5064e3151840ae054a25812408403c01c30dc8660242101049024411c08d03781b80d606a030017c0ba05c02d815c0ac05502a012407203701b00d4066032014009c04a024011807c03c01d00e004c0240100078038014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record010_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record010_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 2)
      (record010.inverseMaps 2) record010_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record010_frame002_links_0000 record010_frame002_links_0064)
theorem record010_frame002_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 2 :=
  of_group record010 2 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record010_frame002_indices record010_frame002_graph record010_frame002_links
def record010_frame003_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x73673072a6ed6ae6ab68067a65f6506155d65d35a85a258457854253052351e5084ff4da4af49a46e46245743542140e4064013ee3dc3d03b83ab38b35d35134332f32b32530c3022fb2d42c929c29227224d21f2132021f41ed1e71cd1c31bd19618b15e15413411b10e1090fd0d10c508608508208106d06c06906805e05d05b05a05905505405305204903903703603503303202802702502402301f01e01d01c01301201000f00e00a009008007005004003002001000 } : Fields).get c.val)
theorem record010_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record010_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record010) (record010.maps 3)
      (record010.inverseMaps 3) record010_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record010_frame003_links_0000 record010_frame003_links_0064)
theorem record010_frame003_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 3 :=
  of_group record010 3 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record010_frame003_indices record010_frame003_graph record010_frame003_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (Fin.cases (record010_frame002_supported hcells) (Fin.cases (record010_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xf9774836d1a50cdf6642fd9796ba05a0ab6d58ea5f527a88941c9b84aca5211ce8d6455a2610c88424182034f907953611a5ccd860d2d3964ca5651b277136890842520a0ecc7443771b20cc061c2fc16c8a504c2237119089042c20d10407e83d81e30ea87383901bb0d6869833c1980c105f02ce15f0a9051027a13509784642260fe049024411c08d03781b80d606a030017c0b805b02c015c0ac05502a00dc06c03301900a004e024011808003e01e00e8070036015009804802200f007002c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record011_frame001_links_0000 (interval_append _ 64 128 129 record011_frame001_links_0064 record011_frame001_links_0128))
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xdb6699323984ac0c602adf56e0b63581aad1546a5452528ed4689cf4bda5a922c90c47ea3d916e88a43a21450227e73981c90e2e6c0337197cc1a6042fc17c8b3c5562a494049f24ee27492e092648223410e48343bc1d70e386de35c1a70cb861e30417b0bc05c22b914689e44ce25b11688843f41ec0e406903241820bb854428c126049024411c08d03781b80d606a030017c0b805b02c015c0ac05502a00dc06c03301900a004e024011808003e01e00e8070036015009804802200f007002c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record011_frame002_links_0000 (interval_append _ 64 128 129 record011_frame002_links_0064 record011_frame002_links_0128))
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xe3c6be34cda12cf2675b0957f4bd25bf2c89622ab054fa9d94c8a124db269528893348523e11c08d2465a2f514288c3e31e80efa72936b9b18ce466131b9898ba85822b89474a184e226892e49584a524b91f08d44011f50ef072637d1b50d0463230216c0b1457029913d09ac4b424c10e08383c81d50db065c3101770b484e4256101049024411c08d03781b80d606a030017c0b805b02c015c0ac05502a00dc06c03301900a004e024011808003e01e00e8070036015009804802200f007002c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record011_frame003_links_0000 (interval_append _ 64 128 129 record011_frame003_links_0064 record011_frame003_links_0128))
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
def record011_frame004_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x8748247e97c37b47b076a75c74f7206e26d96ab6a669769066363562c5ee5e85d95d25c05b45ad59f58356f50a4fd4ef4bd48247744343a42b4243f43c03b537a37136235b34833d33732930e2fb2ca2bb29e28227226324622a22221520e2031eb1d21c61bb1b319719017716d15513c13012411d1020fa0e109209108e08d06f06e06b06a06005f05c05b05805705605505403703603303202802702402302001f01e01d01c01b01501301201100f00e00b00a009008007005004003002001000 } : Fields).get c.val)
theorem record011_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record011_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record011) (record011.maps 4)
      (record011.inverseMaps 4) record011_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record011_frame004_links_0000 (interval_append _ 64 128 129 record011_frame004_links_0064 record011_frame004_links_0128))
theorem record011_frame004_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 4 :=
  of_group record011 4 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record011_frame004_indices record011_frame004_graph record011_frame004_links
def record011_frame005_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xcff65030dd7dabaf5ccad0d654b14572aa99534a5f527a87d4189d74c725f925891b474234913c87b438a124fe87b13a81ce8e4c6f33591a98cc06553169870bd85b12d41594ab453429313e49b64d225891c48843ff1f80f5077a3ab1cd8dec6c43501938c5460a2e31610ae054e29412d09244201fc0f0070c3721aa0cc05942a2121049024411c08d03781b80d606a030017c0b805b02c015c0ac05502a00dc06c03301900a004e024011808003e01e00e8070036015009804802200f007002c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record011_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record011_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 5)
      (record011.inverseMaps 5) record011_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record011_frame005_links_0000 (interval_append _ 64 128 129 record011_frame005_links_0064 record011_frame005_links_0128))
theorem record011_frame005_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 5 :=
  of_group record011 5 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record011_frame005_indices record011_frame005_graph record011_frame005_links
def record011_frame006_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x7537286f26ce6a669a6636506416275f95f35cd5c55aa59d57f55454f52551e5034f64df4ce4c94b24854644284194073ed3bf3b939338b36d36334531a3152eb2e42c62bd2a229428f27824b22a2072011f21e51df1d91c81b91b41a619e19718817717016b16614e14a13212c12211611010c1080f20ee0da08e08d08a08906d06c06906805e05d05a05905605505405305203703603303202802702402302001f01e01d01c01b01501301201100f00e00b00a009008007005004003002001000 } : Fields).get c.val)
theorem record011_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record011_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 6)
      (record011.inverseMaps 6) record011_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record011_frame006_links_0000 (interval_append _ 64 128 129 record011_frame006_links_0064 record011_frame006_links_0128))
theorem record011_frame006_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 6 :=
  of_group record011 6 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record011_frame006_indices record011_frame006_graph record011_frame006_links
def record011_frame007_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x4aa929222404728db12a2243e85103a04bed7d4f7dedbc575cea1c6b896fededb73656c2d59a032f616c157fae8598b21572ab53ea71422694ca9392523f4788bd1322242c7fcf81d33986f0d89aa34865cc41842f45d0b715e29c524a113a240460808fc1e43a0720de1b2318608b00fe1f83e07b0cc194310610ae1582985209e1382684c0960dc1b0330640a0138240460800f81e03a0700d8150260480880f01c02c0500901001c0280400600800800 } : Fields).get c.val)
theorem record011_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record011_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record011) (record011.maps 7)
      (record011.inverseMaps 7) record011_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record011_frame007_links_0000 (interval_append _ 64 128 129 record011_frame007_links_0064 record011_frame007_links_0128))
theorem record011_frame007_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 7 :=
  of_group record011 7 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record011_frame007_indices record011_frame007_graph record011_frame007_links
def record011_frame008_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x8047bf79077075d75671a7086f96d66a96a067166764963e61b5ee5e55b65ac58f58356d55f55954d53151c4cc4b74a647d44e44540f4053e43da3b038137834233831830c2f82ea2e42d82bd2ab27b27225b24723a23221a2041f31dd1d31ca1bc1ae1a81a019717b17015814a13c12e1281201170fb0f00d809008f08c08b06f06e06b06a06005f05c05b05805705605505403703603303202802702402302001f01e01d01c01b01501301201100f00e00b00a009008007005004003002001000 } : Fields).get c.val)
theorem record011_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record011_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record011) (record011.maps 8)
      (record011.inverseMaps 8) record011_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record011_frame008_links_0000 (interval_append _ 64 128 129 record011_frame008_links_0064 record011_frame008_links_0128))
theorem record011_frame008_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 8 :=
  of_group record011 8 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record011_frame008_indices record011_frame008_graph record011_frame008_links
def record011_frame009_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x51d9ed31e52c9591d19a2ec5687b0a610c09808fe1f93d9782ee9d33a1726e39c03766e4d99a6b3c5febd576ad0572ac549a8d5029f12f2404728890ea0f4167f0f89ec3c2724dc19932a620be9772e65a0ad95629a520a193b2604ac9392322a440810fc1e63a4720de1b2328630bb10820c4007f0ce198320630b61682c0570a814c290510a00d81a8320620a0138240460800f81e03a0700d8150260480880f01c02c0500901001c0280400600800800 } : Fields).get c.val)
theorem record011_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record011_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record011) (record011.maps 9)
      (record011.inverseMaps 9) record011_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record011_frame009_links_0000 (interval_append _ 64 128 129 record011_frame009_links_0064 record011_frame009_links_0128))
theorem record011_frame009_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 9 :=
  of_group record011 9 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record011_frame009_indices record011_frame009_graph record011_frame009_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (Fin.cases (record011_frame004_supported hcells) (Fin.cases (record011_frame005_supported hcells) (Fin.cases (record011_frame006_supported hcells) (Fin.cases (record011_frame007_supported hcells) (Fin.cases (record011_frame008_supported hcells) (Fin.cases (record011_frame009_supported hcells) (fun j => Fin.elim0 j)))))))))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xe9071cb741af2d596a83509a68d2e68fb445a14d0467e33c59d4bd75bd2da568cb22578ab2956ca8f538a97941c9fd4ed26d930a95e4a5248d20a8f2476a3a11c28da469a3311868be45aa2b914889d44b223cf0071c37e9b74d866a334099c8cc6632310971cb505882b71538a5851d28713749984c626092e89664ad253128492648c24191ec8ea46f2360fc07843981ad0cbc6382e51688aa453228a13d09ac4aa23611388283f81ee0f4071836c1a70cb86202e41530a2049c23210b08283dc1e00e907103741aa0b0057827013607703881bc0dc06803101800be03f01a00cc064030012809004601b006002c0140090030014008003 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record012_frame001_links_0000 (interval_append _ 64 128 153 record012_frame001_links_0064 record012_frame001_links_0128))
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
def record012_frame002_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xd2167f333593ec816363149874c3160a2fe97e0be95e82ead72ab16570ab49572aa654129ad4c2a3d50da8213a69c34d326392bc93b497241d1c88ce45f22cd14289043f21c90b484c417a068ffe7ea3ea1ef8e4e6e53659ad0d466853341980cae62930c1780b925b32d29628adc5652ae14c0a4451428593f09da4de269933c95049a24391b08b844d2248fd07b03bf1c70db86c63321900bd05c62d31610ae054427b134891446422010b87b83c01d10e186e43481810b8853427c12e093043c1fe0f2072836c1940aa054827013607703881bc0dc06803101800be03f01a00cc064030012809004601b006002c0140090030014008003 } : Fields).get c.val)
theorem record012_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record012_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 2)
      (record012.inverseMaps 2) record012_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record012_frame002_links_0000 (interval_append _ 64 128 153 record012_frame002_links_0064 record012_frame002_links_0128))
theorem record012_frame002_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 2 :=
  of_group record012 2 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record012_frame002_indices record012_frame002_graph record012_frame002_links
def record012_frame003_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x8248037df7be7af7a779c79278e78177677276e76675b7546fb6d36ca6b76a968d67a67365a64563a61860f5ff5ee5d65c25b859f58b57f57a57556e56756055b55354e54453d53452d52651f4a747345f45044242e41640f4073e13d63a739738337536134d34233a3143093053002f92f22eb2e62e22d42cd2c52bc2b52af2ad27625f24922620e2051e31d91c31bc1b51ae1a819b18b18216c16615d15b14313c13512e12811b1091030ec0e40df0db0ce0c90c30c00bf0b80a40a309a09907707106f06e06806206005f03f03403303203002502402301b00c00b00a009006005004003 } : Fields).get c.val)
theorem record012_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record012_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record012) (record012.maps 3)
      (record012.inverseMaps 3) record012_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record012_frame003_links_0000 (interval_append _ 64 128 153 record012_frame003_links_0064 record012_frame003_links_0128))
theorem record012_frame003_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 3 :=
  of_group record012 3 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record012_frame003_indices record012_frame003_graph record012_frame003_links
def record012_frame004_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x539a5f476885039f93d676ce79bd35a68cca98d2fa5bc848e11a6304558890de18c2583b062003fa7e4fa5edbcd78ceddd6ba974ae8dcd39771ae25beb7a6e2da5b13586a0d21892f95d6b816b2cb586aed5b2ab54ca293f2704cc9752b24f4928ed1ba3345e8b11121e42e845009f93de794ef9d73ac6d8d519e31a600bd1672c8574ab95129851c9f1312544708b10f21c420818fd1ee3c4738d91a63145f0b816e2c4560a71442804e0921222204386c0ce1983285f0b21602b83c0660c81882f04a0901181b01802c0500900c01402003 } : Fields).get c.val)
theorem record012_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record012_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record012) (record012.maps 4)
      (record012.inverseMaps 4) record012_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record012_frame004_links_0000 (interval_append _ 64 128 153 record012_frame004_links_0064 record012_frame004_links_0128))
theorem record012_frame004_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 4 :=
  of_group record012 4 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record012_frame004_indices record012_frame004_graph record012_frame004_links
def record012_frame005_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x542a63486885059ff3de78ced9cb3766ccd399d322624959132123ec768d51862e45189110e18c2b843056023f77def85ea3cd790f0dddbb7760eb5d3ba2736e51c5b826f4dc99e321624c1d7f2f35d6b896eacb588ad1552a1536a5147a8850a9e53a26f4d098d2e2594a89412023845a8a11121b4327e8f49de3946f0da9a233c648c51842f65d4b795f2b051c9e9352624888d91321a4107d8e81c0350658c41802d8580ac15028c4d88e11a2204386b0ce1983285f0b215c2b03b0600bc1702c04808c1101b01802c0500900c01402003 } : Fields).get c.val)
theorem record012_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record012_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record012) (record012.maps 5)
      (record012.inverseMaps 5) record012_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record012_frame005_links_0000 (interval_append _ 64 128 153 record012_frame005_links_0064 record012_frame005_links_0128))
theorem record012_frame005_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 5 :=
  of_group record012 5 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record012_frame005_indices record012_frame005_graph record012_frame005_links
def record012_frame006_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0x5c9b7d6d2d3d99b2362ac257faef5c2b5564abf552a65149fd3e676ce39a93125c4ad94526e44c848f31c230c538930f618c2984b08e0cc16819015fdbf97e0fa5f0bd679cf09c33676aed29a1b39660ca191b1361abd572ad95a2b1d5f2b8566a854da97522a2d41a804ee9cd3125649a90d1e235468800f69dd3926ecd719c328614be1742d8594ae94c2824c89411e23644c859051fe3e0788e71c0350678c818a2f85c0b21562a0518941262284486f0d41a4340620b81682c83d0680cc1903004a0901181b01802c0500900c01402003 } : Fields).get c.val)
theorem record012_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record012_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record012) (record012.maps 6)
      (record012.inverseMaps 6) record012_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record012_frame006_links_0000 (interval_append _ 64 128 153 record012_frame006_links_0064 record012_frame006_links_0128))
theorem record012_frame006_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 6 :=
  of_group record012 6 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record012_frame006_indices record012_frame006_graph record012_frame006_links
def record012_frame007_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x85a83d81f8027ed7e27d17c57bf7b07a379778f78777876e7176f76f36e96dd6c96b56aa69868a68066065864663361d6065f75e25ce5c05ba5b65a75a159258857b57656a55f55454653b52b4cd49c4864714654544444384304114063e43d13bf3b73ac3a539d39637e37637036535b34f34a33e3373213113032f82ed2e32e12aa29327c25e24a23d22421b2071fb1f11e71dd1d11c11b719f19518818317116415a1521471391211151040fb0f20ed0e20da0d10c80c20ba0a20a109409307306e06c06b06505f05d05c03e03303203102f02502402301b00c00b00a009006005004003 } : Fields).get c.val)
theorem record012_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record012_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record012) (record012.maps 7)
      (record012.inverseMaps 7) record012_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record012_frame007_links_0000 (interval_append _ 64 128 153 record012_frame007_links_0064 record012_frame007_links_0128))
theorem record012_frame007_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 7 :=
  of_group record012 7 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record012_frame007_indices record012_frame007_graph record012_frame007_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (Fin.cases (record012_frame002_supported hcells) (Fin.cases (record012_frame003_supported hcells) (Fin.cases (record012_frame004_supported hcells) (Fin.cases (record012_frame005_supported hcells) (Fin.cases (record012_frame006_supported hcells) (Fin.cases (record012_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xd01650b1a98a0c39607afd57dcbbf5d4ac4d5d0aa653fa9a14c0a3a50ea82931e95949b24b11cc8d045ea2790f6871433a0c10367f23ee1f18f6675d3929bbcdc06c63591a20cd666132218a8c325de2e396c8b4a58a2b71594ab253229214209f24ea26d934898049e24811bc8be450222100c77a38c1b60d8867a3031718b085702a514a091c46822210707e83c01c30dc86b430817409004381ae0c904d01e40f006f03701740b805b02c015c0ac04102000fc07203701b00c004a024011808404001f00f004c024010007803801a00b0050024010005002000c002000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record013_frame001_links_0000 (interval_append _ 64 128 137 record013_frame001_links_0064 record013_frame001_links_0128))
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
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3e71d26dba6b9b50da56cef66bb02573ab4156daa814eea6251da87d4169a54c0a57128a91e47d239d1aa8a944b221d0c88424182080fee7e53e31ed4f4a79736a99a4c1a5a72b6150ca5c507275935c8e244d21410447d43c61d98e846ea3621a98cc061c2fc1760b0c56229214089c44c6237119089042c20e10087cc3d81e40ef07203761ad0d3067833017a0b985b02ca1590a9052c28813d09a049823e11a07e83dc1b40d503c81e00de06e03401740b805b02c015c0ac04102000dc06c030012809004602000f8078036015009804802000f007003401600a004802000c005002000c002000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record014_frame001_links_0000 (interval_append _ 64 128 143 record014_frame001_links_0064 record014_frame001_links_0128))
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x3889ac4cc9655327592cc8363e2f8d710b415732b39580ab9555aa89536a1e4f727013529864b2254d28291748323d91a68b145022390c885342220f506c8303c79cc4dca6873379984cb464c32198f4baa5b42c615e0abe54329a949ca0c4f8275934896c4a824d11e48d646022d91588a43eb1ea8ea46fc36c1a78cc063e30d17f0b2c55c28f13f09b04ba22a111887042a1f20f0073036e1a20c605a02aa14808b842c1b40d203c81e00de06e03401740b805b02c015c0ac04102000dc06c030012809004602000f8078036015009804802000f007003401600a004802000c005002000c002000 } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record014_frame002_links_0000 (interval_append _ 64 128 143 record014_frame002_links_0064 record014_frame002_links_0128))
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
def record014_frame003_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x1be76aeb3d45a6349e83cfb8fb0adf4b956ead7daab3964ec6d55a834c691d139ff3e276cd699b30e59c9d92d22a394688b51522844b81cf91e239b716e01bdb6d6c8d7993312604bd1722ce58eaed51a9951c9f9352634b09051c22b44a8850e1fc3f27b4f19db39c700dc1af352644c21762dc594af9462844f89d12f2564948f118220414800fa1b634c5a0ae0ec1d43686c0cc16c2d0590ac1542a04007e0dc1b03004a0901182003e0780d8150260480800f01c0340580a0120200300500800c00800 } : Fields).get c.val)
theorem record014_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record014_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record014) (record014.maps 3)
      (record014.inverseMaps 3) record014_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record014_frame003_links_0000 (interval_append _ 64 128 143 record014_frame003_links_0064 record014_frame003_links_0128))
theorem record014_frame003_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 3 :=
  of_group record014 3 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record014_frame003_indices record014_frame003_graph record014_frame003_links
def record014_frame004_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x3405942c39607afd57dcbbf5d4ad45626ae555329fd4d0a6051d28754149c54d4263d2f695949b24b12348e6468230513c87b438a18106081b3f91f70f8c7b33ae9c94de66b234419accc26443151864bbc5c72d91694b1456e2b29564a6452428c13e49b64d2262927892046f22f91408883ff1f80f5077a3ac1c60db06c435119e8c145c62c215c0a9c52824711a088841c1ee0f007443861b90d486102e816609004441ae0c903c81e00de06e03401740b805b02c015c0ac04102000dc06c030012809004602000f8078036015009804802000f007003401600a004802000c005002000c002000 } : Fields).get c.val)
theorem record014_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record014_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 4)
      (record014.inverseMaps 4) record014_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record014_frame004_links_0000 (interval_append _ 64 128 143 record014_frame004_links_0064 record014_frame004_links_0128))
theorem record014_frame004_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 4 :=
  of_group record014 4 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record014_frame004_indices record014_frame004_graph record014_frame004_links
def record014_frame005_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x7557296f46e06d56cf6af6a366a6406275f95e45d35ce5ba5a859b57556355554c53d52a52551d5024f54ed4df4ce4c94c14a449748347946d4664304063ed3bf3a839b39438036b36133a32b31b3123012f22eb2e32c52bc2b32a229428f28726725c24923c23222c2072011f21e51e01d01bf1b91b51af19718817717016b16614814013713012812211c11611010b0ff0f70f30d90d50b90b407707606d06c06605b05a05905605505404104003703603002502402302001f01e01b01501301201000f00e00d00b00a009008006005004003001000 } : Fields).get c.val)
theorem record014_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record014_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record014) (record014.maps 5)
      (record014.inverseMaps 5) record014_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record014_frame005_links_0000 (interval_append _ 64 128 143 record014_frame005_links_0064 record014_frame005_links_0128))
theorem record014_frame005_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 5 :=
  of_group record014 5 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record014_frame005_indices record014_frame005_graph record014_frame005_links
def record014_frame006_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6f66b968967a67367266165d62e60f5f85d95cb5c35c05b45ab5a658056a55954e53b52c5295205074fd4f64e84d84d14c84af4a749a49348f48c4484183f93c93bb3b23af3a339b39736d35734433832831b3183102fb2f32e92dc2cf2c92c12aa2a529b29629329126826024a23722b21e20d2091fd1ef1d41c41b91b21a619817b17417016c15914f14713d1371291141091000df0d60b50ae07507406d06c06605b05a05905605505404003f03703603002502402302001f01e01b01501301201000f00e00d00b00a009008006005004003001000 } : Fields).get c.val)
theorem record014_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record014_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record014) (record014.maps 6)
      (record014.inverseMaps 6) record014_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record014_frame006_links_0000 (interval_append _ 64 128 143 record014_frame006_links_0064 record014_frame006_links_0128))
theorem record014_frame006_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 6 :=
  of_group record014 6 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record014_frame006_indices record014_frame006_graph record014_frame006_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (Fin.cases (record014_frame003_supported hcells) (Fin.cases (record014_frame004_supported hcells) (Fin.cases (record014_frame005_supported hcells) (Fin.cases (record014_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1d3edb06af3539a4ccff675b325946c8d62730e9696af9574ab05534a8653228f94509e94eaa6c535099a4c626192ee9694b1253d29093b49c24c525492348e244521c90347e23e51dc8e74702374fa47813b49d04e2c70336d1ad4d3e6653271784ba45ac2c315cca9e52b28c137c99e4b6259128091c47d236913489242a20d90607f63e91ec8f5c6e436319e8c5c6082e015e0aa44e0260123890c46221f10707f83bc1da0dd86b035218c0bd05a82d01550a8052428413b09a04ac24c11d08b044421210307e03dc1e40ec07303801b40d404d0250124091047823811a07703881bc0dc06c03581a806002a014009c04a024011806c02a013009004001e00e } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame001_links_0000 (interval_append _ 64 128 158 record015_frame001_links_0064 record015_frame001_links_0128))
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
def record015_frame002_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x8bb88086385e85284583e83382982280d80679575b74e7387227177046ed6e46ba6ad67866664e6346276145f85ec5c05ae59359058858057857056256055154954653953152a5274b247e46c45443a42d41a3fe3f23c63b436d36034a3343293162ff2f62cc2bf2b02ad2a529d29528d27f27d26e26626325624e24724421e21a20d2001f91ec1df1d81c11bb1b41b11a91a219a19118518217616e16a15f15815014d14213f13713012811f1131101040fc0f80ed0e60de0db0d50d10cd0c90c50c109a09409209108f08e08d07707106f06e06c06b06a03002a02802702502402301b01501301201000f00e } : Fields).get c.val)
theorem record015_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record015) (record015.maps 2)
      (record015.inverseMaps 2) record015_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame002_links_0000 (interval_append _ 64 128 158 record015_frame002_links_0064 record015_frame002_links_0128))
theorem record015_frame002_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 2 :=
  of_group record015 2 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record015_frame002_indices record015_frame002_graph record015_frame002_links
def record015_frame003_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1106.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1106.count (({ width := 10, code := 0x7e1f1795e4779d975dd5745cf71dc46fdb36c9ac69da568d9f675956498960d7e5e5775d1705b9685915f5795c56958559535494f5354c52547515444f9334b52848d214791a4611243901400fa3d4f33c4ed3ace3380de374db364d7354d2344ce330cb320c6310c32e0b72c4ac2a8a8290a22689725494248902388c22488214832087f1f47b1e8771d8741c8701b86b1a867194641845f1745c16859160571585511c410fc3e0f03b0e8320b02a0a427098250741705414048110400e020060140300801 } : Fields).get c.val)
theorem record015_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record015) (record015.maps 3)
      (record015.inverseMaps 3) record015_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame003_links_0000 (interval_append _ 64 128 158 record015_frame003_links_0064 record015_frame003_links_0128))
theorem record015_frame003_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 3 :=
  of_group record015 3 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1106
    Papers.RationalityTen.SharedFrameCatalogue.group1106_facts record015_frame003_indices record015_frame003_graph record015_frame003_links
def record015_frame004_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1104.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1104.count (({ width := 10, code := 0x8861d852138420c82a08812027e9f77d5ec7ade8791e2781dc769d273dc8711c16f5bc6e5b56cdac6999f6799b661956498d63187611835f97b5e5785d16b59d645815f571585594f5253e4f53a4d9344c92e4b1244851e4751a45d144450c42d0640d023f4fa3e0f73b8ed3a8e6390e2378dc350d1338cd328c7310c12f0bb2d8b32c8ad2a8a829ca22849e26c982549023c8a21c862047e1f07b1e0771d8751d0731a8641886117c5e174571444f1384c12c4a0c02a0a0270942408c1b054130481003c0e } : Fields).get c.val)
theorem record015_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1104.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record015) (record015.maps 4) (record015.inverseMaps 4) record015_frame004_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record015) (record015.maps 4) (record015.inverseMaps 4) record015_frame004_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record015) (record015.maps 4) (record015.inverseMaps 4) record015_frame004_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record015) (record015.maps 4)
      (record015.inverseMaps 4) record015_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame004_links_0000 (interval_append _ 64 128 158 record015_frame004_links_0064 record015_frame004_links_0128))
theorem record015_frame004_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 4 :=
  of_group record015 4 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1104
    Papers.RationalityTen.SharedFrameCatalogue.group1104_facts record015_frame004_indices record015_frame004_graph record015_frame004_links
def record015_frame005_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1103.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1103.count (({ width := 10, code := 0x8861d852138420c82a08812027e9f77d5ec7ade8791e2781dc769d273dc8711c16f5bc6e5b56cdac6999f6799b661956498d63187611835f97b5e5785d16b59d645815f571585594f5253e4f53a4d9344c92e4b1244851e4751a45d144450c42d0640d023f4fa3e0f73b8ed3a8e6390e2378dc350d1338cd328c7310c12f0bb2d8b32c8ad2a8a829ca22849e26c982549023c8a21c862047e1f07b1e0771d8751d0731a8641886117c5e174571444f1384c12c4a0c02a0a0270942408c1b054130481003c0e } : Fields).get c.val)
theorem record015_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1103.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record015) (record015.maps 5) (record015.inverseMaps 5) record015_frame005_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record015) (record015.maps 5) (record015.inverseMaps 5) record015_frame005_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record015) (record015.maps 5) (record015.inverseMaps 5) record015_frame005_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record015) (record015.maps 5)
      (record015.inverseMaps 5) record015_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame005_links_0000 (interval_append _ 64 128 158 record015_frame005_links_0064 record015_frame005_links_0128))
theorem record015_frame005_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 5 :=
  of_group record015 5 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1103
    Papers.RationalityTen.SharedFrameCatalogue.group1103_facts record015_frame005_indices record015_frame005_graph record015_frame005_links
def record015_frame006_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1102.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1102.count (({ width := 10, code := 0x92e448e2378c62c8aa288922286a1784a06815ff7e9f87d9f27c1e8795dc759d1731ca71dc3705ba6d5af6b9ab6a1a56899d67197651936398c6298960d785c96d5a16658d5f57556545435093c4dd354cd2f4b5254892047d1c4651644d0e43508415043fcfd3ecfa3bcee3a0e3384df36cd9344ce330cb320c5308bf2e8b92d0b12c0ab2a4a7298a32889f27099258912408b22087208801f87d1ec7a1e4781dc761a0621805f1745c16c531344b1284811c460c02a0a0270942408c1b054130481003c0e } : Fields).get c.val)
theorem record015_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record015) (record015.maps 6) (record015.inverseMaps 6) record015_frame006_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record015) (record015.maps 6) (record015.inverseMaps 6) record015_frame006_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record015) (record015.maps 6) (record015.inverseMaps 6) record015_frame006_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record015) (record015.maps 6)
      (record015.inverseMaps 6) record015_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame006_links_0000 (interval_append _ 64 128 158 record015_frame006_links_0064 record015_frame006_links_0128))
theorem record015_frame006_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 6 :=
  of_group record015 6 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1102
    Papers.RationalityTen.SharedFrameCatalogue.group1102_facts record015_frame006_indices record015_frame006_graph record015_frame006_links
def record015_frame007_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x19feca06393195896c37613b0317e4bed5d7ae65628ae15692ae554ca9753e29954bea1f506278d3929ac4c8a6212c093d497a3e11c48bb45ba29512888243a215d0a282c40ba044fd87d63e01ee8e4c6fd3739b34d6a6af34619bccc663831397a0bb65c42d89694b1456e2b294d0a4c51128693f89de4e026a12f096e49b24692288d245a22591207fe3f01ea0ef475838c1b60d8864e31517f8be45d02d81638ae854229a13d09a04c2241117887442c1f80f8878c3a81c60dd06983361820b905a429813d096849023210907c83b01be0cf04d0250124091047823811a07703881bc0dc06c03581a806002a014009c04a024011806c02a013009004001e00e } : Fields).get c.val)
theorem record015_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record015) (record015.maps 7) (record015.inverseMaps 7) record015_frame007_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record015) (record015.maps 7) (record015.inverseMaps 7) record015_frame007_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record015) (record015.maps 7) (record015.inverseMaps 7) record015_frame007_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record015) (record015.maps 7)
      (record015.inverseMaps 7) record015_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame007_links_0000 (interval_append _ 64 128 158 record015_frame007_links_0064 record015_frame007_links_0128))
theorem record015_frame007_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 7 :=
  of_group record015 7 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record015_frame007_indices record015_frame007_graph record015_frame007_links
def record015_frame008_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x72a6ed6d26ca6ba6ae6a669868568065f6506155fa5f55e65d65ce5bf5b15a858457856355b54f54453f53252552050e5054f74f54ee4e84e14dc4d24cf4c34bb4b84ad4a549d49b45744143942541140c3f93e63df3c23b538837e36935d35334332f32b30c3022f42f32ec2e42de2d62c72c42af2a42a228d28427827624a23f23121f2152021f41ed1cd1c31b61b41ae1a71a019818918616e16616414f14313a13812812311c11610f10b1030fe0f50ef0ec0e40dd0d60d20ce0c80c20bd0b80b108c08808608508308208107306f06d06c06a06906803002a02802702502402301b01501301201000f00e } : Fields).get c.val)
theorem record015_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record015) (record015.maps 8) (record015.inverseMaps 8) record015_frame008_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record015) (record015.maps 8) (record015.inverseMaps 8) record015_frame008_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record015) (record015.maps 8) (record015.inverseMaps 8) record015_frame008_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record015) (record015.maps 8)
      (record015.inverseMaps 8) record015_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame008_links_0000 (interval_append _ 64 128 158 record015_frame008_links_0064 record015_frame008_links_0128))
theorem record015_frame008_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 8 :=
  of_group record015 8 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record015_frame008_indices record015_frame008_graph record015_frame008_links
def record015_frame009_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1000.count (({ width := 11, code := 0x2734d399131a5f4b59632ae524a092322e2ec498890da16c2783f04e08bfd7eaf9defbd1786ef5db3aa744e2dc13736e4db1b3b616b8d41a6b41672ce197329644c8177ae05b0b2d5e2b655ca8d4da844f49852da5148a8fd1b22e45284906a054067f4fd1f43dc788ef9d2396728e01b93686c8cc998320618c11782d8598ae1572a253ca51452824ec9993124e4788e915220424838fe1f83e07a0ef1d03806f0d3198328610bc16e2d0578ad1542904f09b1041f83e07b0f21e03b8650c41802f85d0b816c1682a05009c1282404606c0a8130240400780e } : Fields).get c.val)
theorem record015_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record015) (record015.maps 9) (record015.inverseMaps 9) record015_frame009_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record015) (record015.maps 9) (record015.inverseMaps 9) record015_frame009_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record015) (record015.maps 9) (record015.inverseMaps 9) record015_frame009_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record015) (record015.maps 9)
      (record015.inverseMaps 9) record015_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame009_links_0000 (interval_append _ 64 128 158 record015_frame009_links_0064 record015_frame009_links_0128))
theorem record015_frame009_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 9 :=
  of_group record015 9 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1000
    Papers.RationalityTen.SharedFrameCatalogue.group1000_facts record015_frame009_indices record015_frame009_graph record015_frame009_links
def record015_frame010_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0998.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0998.count (({ width := 9, code := 0x21d0d8642e15098441e0d0580bfdfcfd7e3edf4f97c3ddecf2783bddced763add4e873389c0dc6db65aed569b45a0cd65b2990c76331588c36130580bf5f2f174b65a2c962b057ab95aac55a9d4aa250a7d3a9b4ca5d2c9348a411c8d4622d14894421d0c854220cfe7d3d1e4ee75399c4de6e359a4d06632990c6602f974b6592b954a85127938984b25124904723114884321104803f1f0f4783a1c8e06e361a8d044211007c3c1d0e0502612088401e0e } : Fields).get c.val)
theorem record015_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0998.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0998.localPairCheck (smallEmbedding record015) (record015.maps 10) (record015.inverseMaps 10) record015_frame010_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0998.localPairCheck (smallEmbedding record015) (record015.maps 10) (record015.inverseMaps 10) record015_frame010_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0998.localPairCheck (smallEmbedding record015) (record015.maps 10) (record015.inverseMaps 10) record015_frame010_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0998.localPairCheck (smallEmbedding record015) (record015.maps 10)
      (record015.inverseMaps 10) record015_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame010_links_0000 (interval_append _ 64 128 158 record015_frame010_links_0064 record015_frame010_links_0128))
theorem record015_frame010_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 10 :=
  of_group record015 10 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0998
    Papers.RationalityTen.SharedFrameCatalogue.group0998_facts record015_frame010_indices record015_frame010_graph record015_frame010_links
def record015_frame011_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0997.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0997.count (({ width := 8, code := 0xdbdad8d7d6d5d4d3d2d1cdcbcac8c7c6c5c4c3c2c1bdbbbab8b7b6b5b4b3b2afadaaa9a8a7a6a5a4a3a09e9d9b9a99989695939291908f8e8d8a888584838281807f7e7a78767574737271706f6c6a696766656461605f5e5d5c5b5a56545251504f4e4d4c4b484645434241403d3c3b3a393837363331302e2d2c2b2928272625242322201f1e1d1c1a19171615141311100e0d0c0b0a08070504030201 } : Fields).get c.val)
theorem record015_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0997.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0997.localPairCheck (smallEmbedding record015) (record015.maps 11) (record015.inverseMaps 11) record015_frame011_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0997.localPairCheck (smallEmbedding record015) (record015.maps 11) (record015.inverseMaps 11) record015_frame011_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0997.localPairCheck (smallEmbedding record015) (record015.maps 11) (record015.inverseMaps 11) record015_frame011_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0997.localPairCheck (smallEmbedding record015) (record015.maps 11)
      (record015.inverseMaps 11) record015_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame011_links_0000 (interval_append _ 64 128 158 record015_frame011_links_0064 record015_frame011_links_0128))
theorem record015_frame011_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 11 :=
  of_group record015 11 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0997
    Papers.RationalityTen.SharedFrameCatalogue.group0997_facts record015_frame011_indices record015_frame011_graph record015_frame011_links
def record015_frame012_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0996.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0996.count (({ width := 8, code := 0xdbdad8d7d6d5d4d3d2d1cdcbcac8c7c6c5c4c3c2c1bdbbbab8b7b6b5b4b3b2afadaaa9a8a7a6a5a4a3a09e9d9b9a99989695939291908f8e8d8a888584838281807f7e7a78767574737271706f6c6a696766656461605f5e5d5c5b5a56545251504f4e4d4c4b484645434241403d3c3b3a393837363331302e2d2c2b2928272625242322201f1e1d1c1a19171615141311100e0d0c0b0a08070504030201 } : Fields).get c.val)
theorem record015_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0996.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0996.localPairCheck (smallEmbedding record015) (record015.maps 12) (record015.inverseMaps 12) record015_frame012_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0996.localPairCheck (smallEmbedding record015) (record015.maps 12) (record015.inverseMaps 12) record015_frame012_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0996.localPairCheck (smallEmbedding record015) (record015.maps 12) (record015.inverseMaps 12) record015_frame012_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0996.localPairCheck (smallEmbedding record015) (record015.maps 12)
      (record015.inverseMaps 12) record015_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame012_links_0000 (interval_append _ 64 128 158 record015_frame012_links_0064 record015_frame012_links_0128))
theorem record015_frame012_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 12 :=
  of_group record015 12 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0996
    Papers.RationalityTen.SharedFrameCatalogue.group0996_facts record015_frame012_indices record015_frame012_graph record015_frame012_links
def record015_frame013_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x33b65ac9d9271fe34c5d8a30e614c1781ae85bdb6d6aecfd96b1b602bc569ac950a9ed30a3b44283cf79d734a65cc09772be52c9d92b1ea3c4658af1562143384b091f33cf794f01d8ba7740e4dc4b776e2d3da5342666cad9131861ebfd7d2f55e6ba970ad859eaf95eaae548a8d4b28b502a012d25548e8d51622142281cf99ed3cc78cec1cc3826d8d31a3328624c29772da588af9572a65209e93224a458899051f63dc750e11ae350680c61782b85109b10c210418821022003f86d0d21a0338660ca1901802a05009c1282404606c0a8130240400780e } : Fields).get c.val)
theorem record015_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record015) (record015.maps 13) (record015.inverseMaps 13) record015_frame013_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record015) (record015.maps 13) (record015.inverseMaps 13) record015_frame013_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record015) (record015.maps 13) (record015.inverseMaps 13) record015_frame013_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record015) (record015.maps 13)
      (record015.inverseMaps 13) record015_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame013_links_0000 (interval_append _ 64 128 158 record015_frame013_links_0064 record015_frame013_links_0128))
theorem record015_frame013_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 13 :=
  of_group record015 13 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record015_frame013_indices record015_frame013_graph record015_frame013_links
def record015_frame014_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x2504858f71da38c688c917e2ac4e8850f610415825029ffbfc7eefc5f4bdd7b0f01ddbb374ee81ccb8f70ede1ba36d6d6d99b0b5c6aed2da533d668ccd93b1e62ac5173ad85a6b255f2b755ea914ea8e5129bd36a674b895926a3f4708ad132214408690aa0c40c7ecfd1ef3ce798ed1d138c714d61a7338638c41832f65d4b49642be578ac9522985109b9362504748e113218410818fc1f63dc788ea1c83786e8d419c334628c01742e45a8b01562985009b1082044007f0fa1f03d86d0d41a0338660ca1901802a05009c1282404606c0a8130240400780e } : Fields).get c.val)
theorem record015_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record015) (record015.maps 14) (record015.inverseMaps 14) record015_frame014_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record015) (record015.maps 14) (record015.inverseMaps 14) record015_frame014_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record015) (record015.maps 14) (record015.inverseMaps 14) record015_frame014_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record015) (record015.maps 14)
      (record015.inverseMaps 14) record015_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame014_links_0000 (interval_append _ 64 128 158 record015_frame014_links_0064 record015_frame014_links_0128))
theorem record015_frame014_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 14 :=
  of_group record015 14 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record015_frame014_indices record015_frame014_graph record015_frame014_links
def record015_frame015_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x299511a053f27a4ef9d538a6d4d79933164a4899091f63b4718cf17a2bc4b88d0d617c2483705203bf97e2f71e9bc678aef5dc3b175ce99d2399726e49c1b7b6e6dc59db2c648c5184b025eebb9742d3594ad958aa7538a6d4a28f5109f13ba6d4d29952ea5a4aa92123a394628bd13a20434860ff9f83ce774eb1c83746d0d099d32e650c61862fa5d8b716a2bc55ca91462784d0981262464748a10f20a3f47b8e91c2370698ca1862fc5d0b415a2a45289d10c208408800fe1f83e86b0ce198328630c41841602804c0941202304406c0a8130240400780e } : Fields).get c.val)
theorem record015_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record015) (record015.maps 15) (record015.inverseMaps 15) record015_frame015_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record015) (record015.maps 15) (record015.inverseMaps 15) record015_frame015_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record015) (record015.maps 15) (record015.inverseMaps 15) record015_frame015_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record015) (record015.maps 15)
      (record015.inverseMaps 15) record015_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame015_links_0000 (interval_append _ 64 128 158 record015_frame015_links_0064 record015_frame015_links_0128))
theorem record015_frame015_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 15 :=
  of_group record015 15 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record015_frame015_indices record015_frame015_graph record015_frame015_links
def record015_frame016_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0626.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0626.count (({ width := 8, code := 0xa1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a8988878685848382817f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5a595857565554535251504f4e4d4c4b4a4948474645444342403f3e3d3c3b3a3938373635343332302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record015_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0626.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0626.localPairCheck (smallEmbedding record015) (record015.maps 16) (record015.inverseMaps 16) record015_frame016_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0626.localPairCheck (smallEmbedding record015) (record015.maps 16) (record015.inverseMaps 16) record015_frame016_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0626.localPairCheck (smallEmbedding record015) (record015.maps 16) (record015.inverseMaps 16) record015_frame016_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0626.localPairCheck (smallEmbedding record015) (record015.maps 16)
      (record015.inverseMaps 16) record015_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame016_links_0000 (interval_append _ 64 128 158 record015_frame016_links_0064 record015_frame016_links_0128))
theorem record015_frame016_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 16 :=
  of_group record015 16 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0626
    Papers.RationalityTen.SharedFrameCatalogue.group0626_facts record015_frame016_indices record015_frame016_graph record015_frame016_links
def record015_frame017_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0625.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0625.count (({ width := 9, code := 0x33992c76371586c2e0afd7cbc5dad966b2582bd5cacd56a94fa75268f43a04fa77389acbe5b2a94c9a4b239147e3d1b8cc622d1388c420b007f3edeef5793b9d8e672371b4d76a3499ecc6531588c3613017ebc5dae16eb5592c55ead552a548a35026d34994b2491c8c45a29128642a0d02803e1e8f2773a1c8e26f371b4d66a33994c8612f174b6592b154a652289409e4e2310882401f0f478381b0d46833190c4421f0f074381b0d050200e06830160a } : Fields).get c.val)
theorem record015_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0625.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0625.localPairCheck (smallEmbedding record015) (record015.maps 17) (record015.inverseMaps 17) record015_frame017_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0625.localPairCheck (smallEmbedding record015) (record015.maps 17) (record015.inverseMaps 17) record015_frame017_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0625.localPairCheck (smallEmbedding record015) (record015.maps 17) (record015.inverseMaps 17) record015_frame017_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0625.localPairCheck (smallEmbedding record015) (record015.maps 17)
      (record015.inverseMaps 17) record015_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame017_links_0000 (interval_append _ 64 128 158 record015_frame017_links_0064 record015_frame017_links_0128))
theorem record015_frame017_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 17 :=
  of_group record015 17 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0625
    Papers.RationalityTen.SharedFrameCatalogue.group0625_facts record015_frame017_indices record015_frame017_graph record015_frame017_links
def record015_frame018_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0623.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0623.count (({ width := 8, code := 0x9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record015_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0623.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0623.localPairCheck (smallEmbedding record015) (record015.maps 18) (record015.inverseMaps 18) record015_frame018_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0623.localPairCheck (smallEmbedding record015) (record015.maps 18) (record015.inverseMaps 18) record015_frame018_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0623.localPairCheck (smallEmbedding record015) (record015.maps 18) (record015.inverseMaps 18) record015_frame018_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0623.localPairCheck (smallEmbedding record015) (record015.maps 18)
      (record015.inverseMaps 18) record015_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame018_links_0000 (interval_append _ 64 128 158 record015_frame018_links_0064 record015_frame018_links_0128))
theorem record015_frame018_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 18 :=
  of_group record015 18 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0623
    Papers.RationalityTen.SharedFrameCatalogue.group0623_facts record015_frame018_indices record015_frame018_graph record015_frame018_links
def record015_frame019_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0x2dad8cafb5d6b4d63abf55aa5544a654aa814f49d93826ccd49973065d4a693f20e3d4668b314a22434851046054007fafd5f7be87c2f51e93c3774ee1d4ba072ce55abb3f670c9d8eb1861cc017b2e75c2b19622b855eaa14e28d50a9c135a654c896d2a24a4848d51a22844087d06a053f67e8ef1d83906ecda9aa346678c41842fe5f4ba16b2ca570a794e2784d0999232364548a10c2144147f8f81e63a8740de1b0358658c51802fc5d8b515e2a8528a110e20c410810fe1f83e8720dc1b03586a0d21a01802a05009c1282404606c0a8130240400780e } : Fields).get c.val)
theorem record015_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record015) (record015.maps 19) (record015.inverseMaps 19) record015_frame019_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record015) (record015.maps 19) (record015.inverseMaps 19) record015_frame019_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record015) (record015.maps 19) (record015.inverseMaps 19) record015_frame019_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record015) (record015.maps 19)
      (record015.inverseMaps 19) record015_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame019_links_0000 (interval_append _ 64 128 158 record015_frame019_links_0064 record015_frame019_links_0128))
theorem record015_frame019_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 19 :=
  of_group record015 19 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record015_frame019_indices record015_frame019_graph record015_frame019_links
def record015_frame020_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x83f8047e87dc7cd7c27ba7ac79d79477b7717166f76f36e96dd6d56c56b06a668c68166465c64a63763061f6095f95d85cd5b85b75aa5a359758957a57856955d55b54753c52c52a4cc4aa49f48847346945844843c41e4103ea3df3cd3bb3b73ac3a539d37f37836e36835d35134b33f32a3283123073052f72eb2e22e02af2a729127b27125c24723c21f21620d20a1fe1f41ea1de1d01cb1c01b61b019e19318718217717216615c15514813b1331231161101030fa0f10ec0e70df0d60cd0c40bc09208e08c08b08908808707306e06c06b06906806702f02a02802702502402301b01501301201000f00e } : Fields).get c.val)
theorem record015_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record015) (record015.maps 20) (record015.inverseMaps 20) record015_frame020_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record015) (record015.maps 20) (record015.inverseMaps 20) record015_frame020_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record015) (record015.maps 20) (record015.inverseMaps 20) record015_frame020_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record015) (record015.maps 20)
      (record015.inverseMaps 20) record015_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame020_links_0000 (interval_append _ 64 128 158 record015_frame020_links_0064 record015_frame020_links_0128))
theorem record015_frame020_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 20 :=
  of_group record015 20 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record015_frame020_indices record015_frame020_graph record015_frame020_links
def record015_frame021_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0537.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0537.count (({ width := 9, code := 0x2230f85c2a110782c1207017e3e9f2f57a3c9e2ef773b5d6e672385bede6e36db4d86b34da2ce66b2d94c963b1186c2602fd7abb5d2e56eb358ac15cad562a950a551a7d3c9c4da6530974aa411c8c45a25108742a0902803f1f4f6793c1dce672381bcda6c359a4c8623017cba5c2d964ac552a148a24f269309648239148843208f87a3c1d0e46e351a0cc6230178b85a2c1589c4c251208c44200e06c34190c05c2a110803c1c0d060280c050200c0401 } : Fields).get c.val)
theorem record015_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0537.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0537.localPairCheck (smallEmbedding record015) (record015.maps 21) (record015.inverseMaps 21) record015_frame021_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0537.localPairCheck (smallEmbedding record015) (record015.maps 21) (record015.inverseMaps 21) record015_frame021_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0537.localPairCheck (smallEmbedding record015) (record015.maps 21) (record015.inverseMaps 21) record015_frame021_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0537.localPairCheck (smallEmbedding record015) (record015.maps 21)
      (record015.inverseMaps 21) record015_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame021_links_0000 (interval_append _ 64 128 158 record015_frame021_links_0064 record015_frame021_links_0128))
theorem record015_frame021_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 21 :=
  of_group record015 21 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0537
    Papers.RationalityTen.SharedFrameCatalogue.group0537_facts record015_frame021_indices record015_frame021_graph record015_frame021_links
def record015_frame022_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0536.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0536.count (({ width := 8, code := 0xe9e8e5e4e2e1e0dfdedcdad8d7d4d3d1d0cfcecdcbc9c7c4c2c1c0bfbebcbbbab8b6b5b3b2b1afadacaba9a8a6a4a3a2a09d9b9a999897959493918d8c8a898887868482807f7e7c7b7a7876757472716f6d6c6b676664636261605e5c5a595856555452504f4e4c4b494746454342403f3e3c3a393836353331302f2d2c2b2a29282724232221201f1d1a191817161513100f0e0d0c0b09060504030201 } : Fields).get c.val)
theorem record015_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0536.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0536.localPairCheck (smallEmbedding record015) (record015.maps 22) (record015.inverseMaps 22) record015_frame022_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0536.localPairCheck (smallEmbedding record015) (record015.maps 22) (record015.inverseMaps 22) record015_frame022_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0536.localPairCheck (smallEmbedding record015) (record015.maps 22) (record015.inverseMaps 22) record015_frame022_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0536.localPairCheck (smallEmbedding record015) (record015.maps 22)
      (record015.inverseMaps 22) record015_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame022_links_0000 (interval_append _ 64 128 158 record015_frame022_links_0064 record015_frame022_links_0128))
theorem record015_frame022_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 22 :=
  of_group record015 22 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0536
    Papers.RationalityTen.SharedFrameCatalogue.group0536_facts record015_frame022_indices record015_frame022_graph record015_frame022_links
def record015_frame023_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0535.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0535.count (({ width := 10, code := 0x7c5e9795e4785df779db765d774dd1725c3701bb6ddb56c1ad6a5a267d9a65d936398c621846017a5d9715c16c5ad6959d625855d56959551505394d50d3e4ed374c9304b1284911e4691143909415033f8fb3dcf03b4eb3a8e6394e3384dc36cd7350d3338ca320c7304c02f4ba2e4b82d8b32bcad2acaa2a0a6294a12749c2609424c8e22c8821c83208801f87d1e4751d0701b06b198631805f1705b16859160571384a1244811845110400f43c0ec3a0e4380a025090230882108018050120441003c0e } : Fields).get c.val)
theorem record015_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0535.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0535.localPairCheck (smallEmbedding record015) (record015.maps 23) (record015.inverseMaps 23) record015_frame023_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0535.localPairCheck (smallEmbedding record015) (record015.maps 23) (record015.inverseMaps 23) record015_frame023_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0535.localPairCheck (smallEmbedding record015) (record015.maps 23) (record015.inverseMaps 23) record015_frame023_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0535.localPairCheck (smallEmbedding record015) (record015.maps 23)
      (record015.inverseMaps 23) record015_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame023_links_0000 (interval_append _ 64 128 158 record015_frame023_links_0064 record015_frame023_links_0128))
theorem record015_frame023_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 23 :=
  of_group record015 23 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0535
    Papers.RationalityTen.SharedFrameCatalogue.group0535_facts record015_frame023_indices record015_frame023_graph record015_frame023_links
def record015_frame024_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0533.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0533.count (({ width := 8, code := 0xe9e8e5e4e2e1e0dfdedcdad8d7d4d3d1d0cfcecdcbc9c7c4c2c1c0bfbebcbbbab8b6b5b3b2b1afadacaba9a8a6a4a3a2a09d9b9a999897959493918d8c8a898887868482807f7e7c7b7a7876757472716f6d6c6b676664636261605e5c5a595856555452504f4e4c4b494746454342403f3e3c3a393836353331302f2d2c2b2a29282724232221201f1d1a191817161513100f0e0d0c0b09060504030201 } : Fields).get c.val)
theorem record015_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0533.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0533.localPairCheck (smallEmbedding record015) (record015.maps 24) (record015.inverseMaps 24) record015_frame024_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0533.localPairCheck (smallEmbedding record015) (record015.maps 24) (record015.inverseMaps 24) record015_frame024_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame024_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0533.localPairCheck (smallEmbedding record015) (record015.maps 24) (record015.inverseMaps 24) record015_frame024_indices (Fin.ofNat record015.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record015_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0533.localPairCheck (smallEmbedding record015) (record015.maps 24)
      (record015.inverseMaps 24) record015_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record015_frame024_links_0000 (interval_append _ 64 128 158 record015_frame024_links_0064 record015_frame024_links_0128))
theorem record015_frame024_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 24 :=
  of_group record015 24 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0533
    Papers.RationalityTen.SharedFrameCatalogue.group0533_facts record015_frame024_indices record015_frame024_graph record015_frame024_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (Fin.cases (record015_frame002_supported hcells) (Fin.cases (record015_frame003_supported hcells) (Fin.cases (record015_frame004_supported hcells) (Fin.cases (record015_frame005_supported hcells) (Fin.cases (record015_frame006_supported hcells) (Fin.cases (record015_frame007_supported hcells) (Fin.cases (record015_frame008_supported hcells) (Fin.cases (record015_frame009_supported hcells) (Fin.cases (record015_frame010_supported hcells) (Fin.cases (record015_frame011_supported hcells) (Fin.cases (record015_frame012_supported hcells) (Fin.cases (record015_frame013_supported hcells) (Fin.cases (record015_frame014_supported hcells) (Fin.cases (record015_frame015_supported hcells) (Fin.cases (record015_frame016_supported hcells) (Fin.cases (record015_frame017_supported hcells) (Fin.cases (record015_frame018_supported hcells) (Fin.cases (record015_frame019_supported hcells) (Fin.cases (record015_frame020_supported hcells) (Fin.cases (record015_frame021_supported hcells) (Fin.cases (record015_frame022_supported hcells) (Fin.cases (record015_frame023_supported hcells) (Fin.cases (record015_frame024_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))))))
#print axioms record015_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085
