module
prelude
public import GraphInputsRow31Part00176Data
public import RawFrameSupport
public import SharedFrameGroups020Checked
public import SharedFrameGroups022Checked
public import SharedFrameGroups024Checked
public import SharedFrameGroups025Checked
public import SharedFrameGroups028Checked
public import SharedFrameGroups029Checked
public import SharedFrameGroups044Checked
public import SharedFrameGroups046Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups098Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups110Checked
public import SharedFrameGroups111Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00176
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xdd6689b2358f8c3a5b8aab9450a174eaa6b93329924bea5bd2c29584a1a4c124491b489a4191ee8f146e1fe4e4469634198fcbc65ac2cc9584a7a518281933c93447723391508644112010f446e833d1950bc859c2a914a09804562080fc07943861a20c985882ac14f0a4050427413308f04281ec0ef049824411c08d03801b80d606a03101840be05e02e016c0b005702b01540a803801b00cc06402a014809c04c024011808003e01e00e807002a014009004401e00e0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xeb96e5b4a1a26cc85e5abbd4bea4f50726d92fc96b49924311ce8d244c219108483040f1fecfb07c83ca9a5cb7652b28d936890444a21b8ff87b03b31cf0d9066030e17e0ba858e2a414a098447222410e88203f41ec0f187383761ad0d306783221820be059c2c01590a9052c28813d094044c1fc0f7049824411c08d03801b80d606a03101840be05e02e016c0b005702b01540a803801b00cc06402a014809c04c024011808003e01e00e807002a014009004401e00e0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x3b0702d5da933a626b915d2b553aa35422814f09c9362674bc95d28a4e4949151f23c466834ef1b435e65cc397e2f65c8b61662c2560a894b2905109f93826c4b48f115224424818fd1f03bc740e21be36c6b0cf19a310608c017e2f85e8bc1722d8598b211e234450890dc1b0348680c017c2e85c0b41642b0550a814c2903806c0cc1902a05209c130240460800f81e03a0700a8140240440780e0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0847.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0847.count (({ width := 11, code := 0x64dc497f6fc5e7b7961aabd51a83492875029d736a62cbd955252404748d315e1fc37832fa1d8b826f8db1a7b3c662c71872fa5e6ba168abd566aa54ea8a5089bd2623945c859049f63d8774e29b335067cc89802f2588ac9502945089992721c3cc6d8d11022003f07d0d019c328640b816c2c8580ac154290510a013c2703806c0cc1902a05209c130240460800f81e03a0700a8140240440780e0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame004_links_0000 record000_frame004_links_0064)
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0847
    Papers.RationalityTen.SharedFrameCatalogue.group0847_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0845.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0845.count (({ width := 11, code := 0x4af9151ba3545785b01df63e87aaef9da3ab736e4dc2b7e6d8d71a9b4c68acd99432061ab8d5b29351c9fd3425c4ae9251e22d44a859031fc3ea7bcf31d73a4704d4198320604bc16e2ce560a413d2724bc9211522040c7e8f71e43bc740e11a42fc578aa0fa1f03c8780d61a4338660bc1742e05b0b41642b0550a814c2903806c0cc1902a05209c130240460800f81e03a0700a8140240440780e0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame005_links_0000 record000_frame005_links_0064)
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0845
    Papers.RationalityTen.SharedFrameCatalogue.group0845_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xd63694b45991ac7b633b0e15fcac4558a8a142ca024e9a6b93329924b0a5652a494c49f24dd260929491246d22490b47ea3e11e28db3bc1cece4a69634119b4c7a5e32d61664a30504279938497c4ac24d12208ee46722991048424122010f406e833d1950aa452a284139093c47a22b10c88203f01e40e906c83461930b0855829e1480a084e826611e08804281ae09b04702340f006b03501880c205f02e016c0b405902c015c0ac05402000cc06402a014809c048023011008404001f00f007002a014009003c01c00d006002c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record001_frame001_links_0000 (interval_append _ 64 128 137 record001_frame001_links_0064 record001_frame001_links_0128))
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xe2b6f3b739a50d1267d3319684b05579297d49ca3950626d92fc96b473a34d1808ad44421d90c885242120c103a80b3f39f64f907943071744b7c52b28d14149b048222510dc76639f1c60de46a83421980c7861c2fc1748b5c5662a514a098047222410e87b03c81dd0eb87243841bb0da06b434c19d0cb062030617c0b305802b21520a5851027a12808d044c1b609b04702340f006b03501880c205f02e016c0b405902c015c0ac05402000cc06402a014809c048023011008404001f00f007002a014009003c01c00d006002c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record001_frame002_links_0000 (interval_append _ 64 128 137 record001_frame002_links_0064 record001_frame002_links_0128))
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x35d6a0d3193b21636c29692c5582a714b2904fe9c5342654a093124a474828f91da3846a8c916a2a44888d102163bc744e69a8344670c597d2e85c4ae1582aa54ca694a28e510a093e2724d89812f2584888a10b2103cc778ec1d4390708de1b63606a8d019a31c630c31722dc5b0b51682cc590af15a2b05208e104204388650c81702d8590ac1542a0530a41442804e07e0cc1902a05209c120230440841001f03c0700a81402403c0700d01802c0500900e0180280400600800800 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record001_frame003_links_0000 (interval_append _ 64 128 137 record001_frame003_links_0064 record001_frame003_links_0128))
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x394710e11abb51694ce17baeb5ceae95a2ad536a35422814d89a132a634ba9692ba544a293924a464808fd1e2323e2794f09b435c69cca9872fc5ecb31622be574ab9542a2538a59482865009d13926c4b08f1152243f47c8f61e83b8758e81ca3886f8da1ae344680cd186304600bf17c2f45e0b916e2d8570971142243b0690d01802f85d0b41642c0570ac1542a0520800cc1902a05209c120230440841001f03c0700a81402403c0700d01802c0500900e0180280400600800800 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record001_frame004_links_0000 (interval_append _ 64 128 137 record001_frame004_links_0064 record001_frame004_links_0128))
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1111.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1111.count (({ width := 10, code := 0x2789d67397a5a95e488d6328c21b85e14815f87c1ed765d5749d0729c8715c26fdbc6ddb46b9ad6a9a06358a621735bd6c57550521454c52d4a928489204751a45d1443d0c41905408f83ace3380cc320c530cbd2ecb82d4b22bcaa29ca12809d24c912408f2388d2308921c861f8741b06b1885a164511404e12c4a1244811c46114430ec330c82a0a42709023088210801f0781c054140480f0380d0300b0280901c060140400c0200400 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record001_frame005_links_0000 (interval_append _ 64 128 137 record001_frame005_links_0064 record001_frame005_links_0128))
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1111
    Papers.RationalityTen.SharedFrameCatalogue.group1111_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xabdaa9aa0a4ea3da30a089809619569038f38e68c089386c85d7f77df7ce7bf79b79078076f7607507397256fe6ed6db6a161a5ff5f359d58e58155e53e51f5124bd4ab49d49047546d4604524444364234133f33e63d83a73793523452e72d82cc2be2a029628627526725a2472372182091fa1cc1c21ba1ae1a019118315613712b0c009508808707606906806005f05d05a05905805705605505405204003303202a02902702402302202102001f01e01c01501401200f00e00d00c00b00a009007006005004003002001000 } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record001_frame006_links_0000 (interval_append _ 64 128 137 record001_frame006_links_0064 record001_frame006_links_0128))
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
def record001_frame007_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x5b1b4f67eb7d66ab5526855019fb3225f4b994523a40c7c8ad13a23c4286b0be1442283705205c047ecfc1f3bd270cde1b8b3865ec91862f75c8b7156aa453aa5d442814f29c9352624ae93d1fa3745c848fe1eb3ca6c8d49a2338634c397f2ee5c0b395d2aa5109e13322e444869082043f47c0e71b8358558870fa1f0370640c61702d8590ac1542a0530a41442804e0800cc1902a05209c120230440841001f03c0700a81402403c0700d01802c0500900e0180280400600800800 } : Fields).get c.val)
theorem record001_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record001_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record001) (record001.maps 7)
      (record001.inverseMaps 7) record001_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record001_frame007_links_0000 (interval_append _ 64 128 137 record001_frame007_links_0064 record001_frame007_links_0128))
theorem record001_frame007_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 7 :=
  of_group record001 7 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record001_frame007_indices record001_frame007_graph record001_frame007_links
def record001_frame008_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6cf6b66ad66a65d6506315d15bc5b257656d55f54852b50f5044cb4be4b04aa49548f48347846c46545744842e4264193fa39838337d33d33132930f2f22d52cd29228427927125c25324a23d23522c21c20f1f51ea1e11c11ac19c19617116b16516115715414f14914313d13613012712511f10f10c10a1051000fb0f60e50da0d40ac08b08007f07006406305b05a05805505405305205105004f04d03f03303202a02902702402302202102001f01e01c01501401200f00e00d00c00b00a009007006005004003002001000 } : Fields).get c.val)
theorem record001_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record001_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record001) (record001.maps 8)
      (record001.inverseMaps 8) record001_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record001_frame008_links_0000 (interval_append _ 64 128 137 record001_frame008_links_0064 record001_frame008_links_0128))
theorem record001_frame008_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 8 :=
  of_group record001 8 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record001_frame008_indices record001_frame008_graph record001_frame008_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (Fin.cases (record001_frame006_supported hcells) (Fin.cases (record001_frame007_supported hcells) (Fin.cases (record001_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xe3a717b889b48d856b1342d9d8cc965c32c5954ca464eb259922c8363e2e215ccace5602ae5566aab5512a6d3809864b2254d28e917483234d1628a044a21910a684d42220f506c8303be9d60e626d33571a1ccf867533799a0cc265a3289930c8663d2ea96d0b185792b6157caa254329a9488a0c4f8276137c9a44c425b12a092a47923591948c045b22b11486fc34f1980c7c6162fe1570a3c4fc26a12e88c845422310e08543c01b70d106402d01550a2845c2100da06901e40f006f03701740b805b02c015c0ac043020810007203701b009804a024011808404001f00f004c024010007803801a00b0050024010005002000c002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record002_frame001_links_0000 (interval_append _ 64 128 153 record002_frame001_links_0064 record002_frame001_links_0128))
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xd1d687b40598ccb3650b1a98a0c39615307581ec035faafb97d4bbf5d4ac4d54ca7f53429814b0a3a50ea82931e95949b24b12428e646822790f6871433a0c103680e3f91f70f8c7b33a69cdce4a6e03631ac8d4e69934419f0cd66613271910c546192ef171cb645a62cb9628af656e2b29550a6452428c94209f24ea26d934898049e24812088de45f228111077a38c1b60d8869e33d1718b085702a514a097448e23411108383c01c30dc86b43081740b1848021c0d706481e40f006f03701740b805b02c015c0ac043020810007203701b009804a024011808404001f00f004c024010007803801a00b0050024010005002000c002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record002_frame002_links_0000 (interval_append _ 64 128 153 record002_frame002_links_0064 record002_frame002_links_0128))
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6fe6fa6f66cf6c06b96a269968968467e67a67767367266e66165d60f5d95cb5c35c05bb5b45ab5a655953b52c5295245074fd4e84d84d14cc4af4a74a349a49348f48c4374214183ea3dd3c93c53c03bb3b73b23af3a73a339b39736d35734433933132832131b31830b2fb2f32ea2e22dc2d82cf2c92bc2aa2a52a029b29629329123721e20d2091fb1ef1c41b91b21a419818317b17417016c14f13d13712d1141090fe0df0d40b50ae07507406d06c05b05a05905605505404204003f03903703602602502402302102001f01e01301201000f00e00d00b00a009008005004003001000 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record002_frame003_links_0000 (interval_append _ 64 128 153 record002_frame003_links_0064 record002_frame003_links_0128))
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x9b93025bcb395929a5049b92323a2dc4887d0ca1441b82702200bfb7daf85e9bc6778ec5d6ba2738e61cab9171ae25c2b7f6eadb9b2b5f6b0d51872f95e4b956c2cb586add57aaa530a393f26f4cc9752ba4d4909152123e4748d91922d4468750a20e410810f29d43866b8ce193314610ba96f2ce580ab94f28c4b89291c22c44c879081fe3e4768e61ae338648b413825c348680c818c310550a814c2885009e1381c8380680cc1902504808c1082003e0780a8130240400780e01a0300580a0120200300500800c00800 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record003_frame001_links_0000 (interval_append _ 64 128 148 record003_frame001_links_0064 record003_frame001_links_0128))
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x7ce3a4dc30dea6dd35cda86d2b677b35d73ab2a5812b6d540a7753128ed43ea0b4d2a6052b891e47d239d1aa8a944b22210ec864429210906081b3fb9f94f8c7b53d29e5ccd25f62e7169cad8543297141c9d64d723891348503ea1e30ecc7423751b10d5068433018f0c385f82e71618ac4524281138898c46422410b08043e61ec0f207783921c20dd86d035a1a60cc05e82e616c0b285802b21520a5851027a134093047c2340fd06d03540f207803881bc0dc05d02e016c0b205802b815808204001c80dc06c025012008c04202000f807802a013009004001e00e006803001600a004802000c005002000c002000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record003_frame002_links_0000 (interval_append _ 64 128 148 record003_frame002_links_0064 record003_frame002_links_0128))
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x71e35f1aa0d4269a347da22d0a67bb3c17a4b695a32c895d6ac455829d94c89fd4ed26d92fe9584a224291f08ef47423851b48d3466230d17c8b545722a51408994492234efa71637b9b5cd4668133918dcc4c5c12d11608a9c52c28e93889a24c826092e89664ad253127493048f244120c8f647523791ac7d43bc1c98d5c65831916c0b145722a914c8a284f426b12608743c81d60e306d834e1970c405a427410107b83c01d20e206d83500e206f03701b00d606a03101800be05d02e016c07203701b00d006603201500a004e025012008c02a013009004001e00e006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record004_frame001_links_0000 (interval_append _ 64 128 148 record004_frame001_links_0064 record004_frame001_links_0128))
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x9b72fe5c4b495b29e50c9c92523e2e44887d0ca12c1982100dfe3ea7bef41e33bc762e91ceb9a72ce49c738a70cdf9be3746dadadb235e6aed5587af95e4b956aac9580ac555a955189ed37a664ba93d24a474868fd1da374668b115a2243886909a0d40e814f29d43866b8ce1932fc5e0ba96f2ce580ab94f28c4d08b91321e4207f8f91da384648b51602b0540a2136258320630c41802f85e0b215c2b0550a814c1a0330640c01782e05209c1302504808c0a8130240400780e01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record004_frame002_links_0000 (interval_append _ 64 128 148 record004_frame002_links_0064 record004_frame002_links_0128))
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x7cbba41c36ded6deb5e5a92d316783361740b2a5812b6d53aa7452fa88941c9a24bf256523c8fa473a2ad13088b43ca19d0aa845419a0690207f63f21f70f867b23d11e60cd85f62e7169cad254029593b89b446e22510947d43c61d98ddc6c83571a28ccc64231117f8b985b82c21580aa051e27e137099046422410b08043e61ec0ea87383921c20dd86d035a1a60cc060c2ce1600ac854829614409e84bc2340fe07a83b81ce0e006c834c0e206f03701b00d606a03101800be05d02e016c07203701b00d006603201500a004e025012008c02a013009004001e00e006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record004_frame003_links_0000 (interval_append _ 64 128 148 record004_frame003_links_0064 record004_frame003_links_0128))
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
def record004_frame004_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0xa614467e4f59db37a6b4d19872f641c698c11561fc3385b0820d3fa7e4fa5ebbca782ec1d5ba7746e69cbb8d712df5bd3716d2d9dad352692d1d88af45ceb7165ac3576ab9542864f69ad2ea5649e8f91ca3545e8b11121e42e825031fb3e47bcf29df3ae754da1a833a62cbf1792cc58cb015d2ae544a61472744988690a21040c7e8f71e2388670b61622b0538a213c268338660ca18c310610b21602b8550a814c1b8350680cc1903105209c1302504808c0a8130240400780e01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record004_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record004_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record004) (record004.maps 4)
      (record004.inverseMaps 4) record004_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record004_frame004_links_0000 (interval_append _ 64 128 148 record004_frame004_links_0064 record004_frame004_links_0128))
theorem record004_frame004_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 4 :=
  of_group record004 4 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record004_frame004_indices record004_frame004_graph record004_frame004_links
def record004_frame005_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0xa654467fcf79e33966ecd999731e4a4848fb1da33c5e8af12e2342b84305600bf47d6f5de83ca786eeddbbb075ae9dd139b728e45c2b7d6eadc19db1e61ec0d79aeb5c4b3963ab154ea714a28f5109f13ba714d098d2e2594a89292323b4668b51422243685cfc1e73ba720dd1b4342674cc992314610bd9752d05409792824446c8990d2083d46d0be16c2c0560a8142264338660ca18c310610b215c2b0540a61481a8330640c01782e050098128240460880a8130240400780e01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record004_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record004_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record004) (record004.maps 5)
      (record004.inverseMaps 5) record004_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record004_frame005_links_0000 (interval_append _ 64 128 148 record004_frame005_links_0064 record004_frame005_links_0128))
theorem record004_frame005_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 5 :=
  of_group record004 5 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record004_frame005_indices record004_frame005_graph record004_frame005_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (Fin.cases (record004_frame004_supported hcells) (Fin.cases (record004_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x38bd954c9d64b3241910c8163c2eb9618adb56aab3958eac055caac1556aa454da6192c895349ea4b52368d3458a28111487a434213108883d41b20bceb06ae33e19d4cde6683309968ca264c32298f4abe54329a948ca3050a26912d895049624591f48cc46022d91588a23a91b68d7c69e33f1980c7c5fc2ee1660af855c29e14789f84ba24d11888a844621c10a878036e1a20c685f02d4147085034813609103d81e00e206e02f81740b805b02d01600ae05602a810c08003901b009c04a024011808804001f00f007402a012008804001e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record005_frame001_links_0000 (interval_append _ 64 128 143 record005_frame001_links_0064 record005_frame001_links_0128))
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3f19ae6d43695b46d9f8ce4662af21604ac855a2a81518a775312921476a27505a4791f48e7468a30515a86442120c103880d3fd9f6cf8c7b53d29e4cd285ce2ca1600ad85582a194b8a28507279935c7d43c61d98e7471a3791980c385f82e816c8b1c54e29214089c44be22410788204021fa0f987b03bc1d70e487083761b40d686983301910c085e82e616c0b2854828813d09a84bc25011907b035413609103d81e00e206e02f81740b805b02d01600ae05602a810c08003901b009c04a024011808804001f00f007402a012008804001e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record005_frame002_links_0000 (interval_append _ 64 128 143 record005_frame002_links_0064 record005_frame002_links_0128))
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x1bf751698d27a3f44681cf3896ed5c5b816eada5afb55686ce595b1b44e7fcf89d538e6d4b393b25a43c808ed18a2d4548a1129fa3ab72ce45c5b85700dedb936d6ccd79722ce58eae158aa74fc9a931a5549c91519a2b44a8850d9ed3b8754e71c63806e0d49a232462cc217c2ec5b8af958294518a113e2744ac8f118222430838f91a42b84a08d0f01d43786c0ba16c2d0590b01582a8540a61081f83906c09c128240460881001f03c0740a8120220400780e01a0300580a0120200280400600800800 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record005_frame003_links_0000 (interval_append _ 64 128 143 record005_frame003_links_0064 record005_frame003_links_0128))
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
def record005_frame004_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xbfab20b06afaaf3ad6ac7aafa58a019d79c89c19b59a399497d96f9609498a888687686184b8377f77d47c07aa79678175a7407297126fc6a064c62b61d61360b5fe5f35dd5d75cb5b452750e5014ee4e14d349b48247746645944a42d41b40d3fc3ee39736b35834d34133131f2fa2ea2c72b72ad2a12932862652552322232132011f01cd1b51a81971871781561030bf09909107b07807106e05f05d05c05b05a05805705605504304003903602702502402302202001f01e01d01501201101000f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record005_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record005_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record005) (record005.maps 4)
      (record005.inverseMaps 4) record005_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record005_frame004_links_0000 (interval_append _ 64 128 143 record005_frame004_links_0064 record005_frame004_links_0128))
theorem record005_frame004_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 4 :=
  of_group record005 4 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record005_frame004_indices record005_frame004_graph record005_frame004_links
def record005_frame005_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x7626d96ce6ca6c66be6b96b266f62b61260e60b6055ff5fb5f45f05eb5e456d55554a53d5305234f94e34da4c94bd4b249b49248c4874804444063ee3ea3e73e13dc3d83d23cf3ca3c235834833e33332d3223032f22ed2de2d72cf2bd2b72b32af2aa26624523e23923022621b2091fd1ea1e41de1d51c91c41ab1a518f18a18618117a15f14613a12d11f1130fb0cd0a208b08507106f06a06805b05905805705605405305205104103e03903602702502402302202001f01e01d01501201101000f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record005_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record005_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record005) (record005.maps 5)
      (record005.inverseMaps 5) record005_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record005_frame005_links_0000 (interval_append _ 64 128 143 record005_frame005_links_0064 record005_frame005_links_0128))
theorem record005_frame005_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 5 :=
  of_group record005 5 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record005_frame005_indices record005_frame005_graph record005_frame005_links
def record005_frame006_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x116e14c2083d0760bc1281afade3bb976eed5d73a974ae81ce39571cd81abb51694d1da032e648c798ab11612bf97baf05d8b9d61a9e524a41472875029f93ca744de99d1ba2b44e8790c2124007d4f99ea3ca784eb9ce392714e01a1320634c39822f65c8b315f2a8534a41432764d494120228440859072063d8768e61c0364688c51502343e0790d81a8328620a81482885009e1342604b0940fc1e03706a09c128240460881001f03c0740a8120220400780e01a0300580a0120200280400600800800 } : Fields).get c.val)
theorem record005_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record005_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record005) (record005.maps 6)
      (record005.inverseMaps 6) record005_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record005_frame006_links_0000 (interval_append _ 64 128 143 record005_frame006_links_0064 record005_frame006_links_0128))
theorem record005_frame006_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 6 :=
  of_group record005 6 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record005_frame006_indices record005_frame006_graph record005_frame006_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (Fin.cases (record005_frame004_supported hcells) (Fin.cases (record005_frame005_supported hcells) (Fin.cases (record005_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1cdae4971cb6b5b12d796a4b4eda68d2d693347da30d11685340d9f0cf1675304d7d6bd75ab2cd9644b15581abc55bcaca55b2a8d508a7152f27a93949b64d4a65d30a9724af252926e918482a3c91de8e8470a3691a68cc462a2f116a8ae455a29113a8964479ed8f247803869bb4dba6c435a1a8cd226813391914c646212dc1660b1056f2af9538a7852c28e93c09ba4cc26413049744b3256929893449324612048f647523791b07b23ad1cc0e086da35a1a20cbc6382f91728b445722a914c8a284f426b12308d844e21910507f03dc1e80eb071836c1a70cb86202c61530a204d824e11908584141ee0f007483881ba0d505882c015e09d04e026c0e006f03701840c005f01a80d00660320130094048023006002c0140090030014008003 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 128 178 :=
  interval_of_check _ 128 50 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 178 record006_frame001_links_0000 (interval_append _ 64 128 178 record006_frame001_links_0064 record006_frame001_links_0128))
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x2fcdefbd96f6d7daab2761ac0578ae95bab4d65ac356aa854aa8948a8ad0f9cf3666a4d199b31e614be9752ce54ca393b1ea374698c91762ac4f89310e1e4328550920fc1882102a023fe7eefb5f2bdf7b8f61ea3d0798eadce3976f2da9b2b5d6b0d4da7349688cd5973275f4ba9712d85a0b2561abe576a8d4ea97524a2d41a7b4ec9c531a564988f91c23345c8b0fd1ea3c4760e89c93826f0db9a9338648c297d2ec5c0b59682a0528a213e2704cc9712c2464708a90f212408790eb1ca3806c8d219c328610bb1682c0560a713025c4b08810e218338660ca1602b85606a0d01983204c0941202301802c0500900c01402003 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 128 178 :=
  interval_of_check _ 128 50 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 178 record006_frame002_links_0000 (interval_append _ 64 128 178 record006_frame002_links_0064 record006_frame002_links_0128))
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1092.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1092.count (({ width := 9, code := 0x3258ec6e2b0d85c0dfaf97abc5dae972b8dbed96ab4596c560aed66b156aa54aa14ea6d2e9146a250a7d3d9dce66f3599cca612d95ca651269248a411f8ec6a31168ac52271288c3e1b0c83c1609007f3f1f4f87bbc5dcec753a1cee370b7dbadb6d351a2cf66b2d92c662b0d80bd5cad566b1582bd58aa54a9144a04ea7134974a2411a8b44a1d0a843f1ecf2773a9cce471379b4d66933998c05d2d964ae552a14ca04e2612c94481f8f87a351a0cc562a1488842200c8602e16088401e0e048200e060200c0401 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 128 178 :=
  interval_of_check _ 128 50 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 178 record006_frame003_links_0000 (interval_append _ 64 128 178 record006_frame003_links_0064 record006_frame003_links_0128))
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1092
    Papers.RationalityTen.SharedFrameCatalogue.group1092_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
def record006_frame004_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1083.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1083.count (({ width := 9, code := 0x3258ec6e2b0d85c0dfaf97abc5dae972b8dbed96ab4596c560aed66b156aa54aa14ea6d2e9146a250a7d3d9dce66f3599cca612d95ca651269248a411f8ec6a31168ac52271288c3e1b0c83c1609007f3f1f4f87bbc5dcec753a1cee370b7dbadb6d351a2cf66b2d92c662b0d80bd5cad566b1582bd58aa54a9144a04ea7134974a2411a8b44a1d0a843f1ecf2773a9cce471379b4d66933998c05d2d964ae552a14ca04e2612c94481f8f87a351a0cc562a1488842200c8602e16088401e0e048200e060200c0401 } : Fields).get c.val)
theorem record006_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 128 178 :=
  interval_of_check _ 128 50 (by decide +kernel)
theorem record006_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record006) (record006.maps 4)
      (record006.inverseMaps 4) record006_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 178 record006_frame004_links_0000 (interval_append _ 64 128 178 record006_frame004_links_0064 record006_frame004_links_0128))
theorem record006_frame004_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 4 :=
  of_group record006 4 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1083
    Papers.RationalityTen.SharedFrameCatalogue.group1083_facts record006_frame004_indices record006_frame004_graph record006_frame004_links
def record006_frame005_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1082.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1082.count (({ width := 9, code := 0x29b4aa4d1e8943a04fa793b9d4e26d359a4ca5f2d95ca64f2592486411e8ec6e33188bc56251087436150983c1a090280c01fcfb7cbddecf579bc5e0ef76ba9d0e672b91c6e270b81bcdd6db65b0d66ab4da2d067b258cc461b0580be5eaed72b85bac55cac55aa54ea652a8d409d4d259289248a411c8c45a250e854220d027e3d9e0ea74391c0de6e34194c6612f974b85b2c960ac54299489849239148641200fc783a1c0dc6c34178b85a281389842200f86832180a8502612078381a0c048200e060200c0401 } : Fields).get c.val)
theorem record006_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1082.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1082.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1082.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1082.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 128 178 :=
  interval_of_check _ 128 50 (by decide +kernel)
theorem record006_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1082.localPairCheck (smallEmbedding record006) (record006.maps 5)
      (record006.inverseMaps 5) record006_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 178 record006_frame005_links_0000 (interval_append _ 64 128 178 record006_frame005_links_0064 record006_frame005_links_0128))
theorem record006_frame005_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 5 :=
  of_group record006 5 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1082
    Papers.RationalityTen.SharedFrameCatalogue.group1082_facts record006_frame005_indices record006_frame005_graph record006_frame005_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (Fin.cases (record006_frame004_supported hcells) (Fin.cases (record006_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x71cb5e5a68d2d693347da30d11685340d9f8cf16752f5d644b15581abc55bcaca55b2a8d51ea7152f26d93529974c2a5c92bc94a49ba48d20a8f2477a3a11c28da469a33118a8be45aa2b91568a444ea25911e77a36b9b10d686a33489a04ce465f3261608ade55f2a714f0a5851d28513dc9904c125d12cc95a4a624f926091e48824091ec8ea46f2348e4c70436d1ad0d1065e31c1838bcc5aa2c215c8aa453228a13d09ac4b624c10c88283f81ee0f0075838c1b60d3865c3101780b484d824e11908583f41ee0f007483881b60d505802bc13809b03781b80c005f020810006e03601a80d006603201880a004e0260128090046022009804801800b00500240100060028010006002 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 128 164 :=
  interval_of_check _ 128 36 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 164 record007_frame001_links_0000 (interval_append _ 64 128 164 record007_frame001_links_0064 record007_frame001_links_0128))
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0xbd96aac0578ae95bab4d65ac356aa9d4aa8943e6a4d199b31e614be9752ce564a393b1a63245d8ab13e24c438790d61542483f0620840a808ff9fbbf07caf7dee3d87a8f41e63936c2d75ac35369cd25a233e670b7d6c2d0592b0d5f2bb566aa54928b5069ed3b2714d297927a4647c8e119a2e45077cec1d1392704de1b735e690ca98c30a5f4bb1702d65a0b015627c4e09992e25048c8e11521e424810fc1ea3806c8d219c320610bb1682c0550a712e258438860cc1942b8560800fc1b83606a0d0198320620a01382604a090118220260480600b0140240400600a01001802 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 128 164 :=
  interval_of_check _ 128 36 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 164 record007_frame002_links_0000 (interval_append _ 64 128 164 record007_frame002_links_0064 record007_frame002_links_0128))
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1092.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1092.count (({ width := 9, code := 0xc6e16f97abc5dae972b8dbedb6ab4582b156aa54aa14ea6d2e9346a24f677399bcd66732984ba57299449a49229047e3b1b8c45a2b1489c4a230a81401fcfc7d3e1eef579b95c6e16fb75b6da6c3599acb64b198ac360af974b75aacd62b05729d48a250275389a4c255228e46a2d128742a1104803b9d4e672381bcda6b3499ccc6431164ae552a148a04e2612c92481f0f46833150a442200f074361a0c8602e160a84c24110803c1c0d058281208038180a04018080200 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 128 164 :=
  interval_of_check _ 128 36 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 164 record007_frame003_links_0000 (interval_append _ 64 128 164 record007_frame003_links_0064 record007_frame003_links_0128))
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1092
    Papers.RationalityTen.SharedFrameCatalogue.group1092_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1089.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1089.count (({ width := 9, code := 0xb5da2c963b0d7ab759abd52a34da551e8b43a0cfa77399bcd2632d954a24d2490c7a391a8bc52210d8642a0f0481401fafa7b3cde4f1783bddcec753a5d0e672b91c6e16fb69b2d86b355a8d368b3d96c86330d82be5dae568b157ab958ab552a14ea45127d3a9a4ba55208d4622d128843a1908823e9f0f4793c1dcec74399c8e26f369a0ce653218cc2602f174b85b2b154a04f229107439160ac5228138984a2411884401f0f074381b09848180b050241006028100602 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 128 164 :=
  interval_of_check _ 128 36 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 164 record007_frame004_links_0000 (interval_append _ 64 128 164 record007_frame004_links_0064 record007_frame004_links_0128))
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1089
    Papers.RationalityTen.SharedFrameCatalogue.group1089_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
def record007_frame005_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1086.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1086.count (({ width := 9, code := 0xde6d75dadd5ea34ba3d0e7b3797ca63b1186c2606fd7cbd5dee970b6da2cd64b0d7ab95aabd52a14da652a8f44a15027b3a9b4ce6531984be5d28914863f1d8e46e35188b42a0f0480bfdfafb7cbd5d8e973b91c4df6e365a6cf66b3194c96430980bd5dae16cb3582b54ea35027534984b251248e42a110481401fcfa7b3d1e4f0763a1b0d6693419cca6431184c05f2c15ca451239187439160ac5228138984a2411884401f0f074381b09848180b050241006028100602 } : Fields).get c.val)
theorem record007_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 128 164 :=
  interval_of_check _ 128 36 (by decide +kernel)
theorem record007_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record007) (record007.maps 5)
      (record007.inverseMaps 5) record007_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 164 record007_frame005_links_0000 (interval_append _ 64 128 164 record007_frame005_links_0064 record007_frame005_links_0128))
theorem record007_frame005_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 5 :=
  of_group record007 5 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1086
    Papers.RationalityTen.SharedFrameCatalogue.group1086_facts record007_frame005_indices record007_frame005_graph record007_frame005_links
def record007_frame006_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1083.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1083.count (({ width := 9, code := 0xc6e16f97abc5dae972b8dbedb6ab4582b156aa54aa14ea6d2e9346a24f677399bcd66732984ba57299449a49229047e3b1b8c45a2b1489c4a230a81401fcfc7d3e1eef579b95c6e16fb75b6da6c3599acb64b198ac360af974b75aacd62b05729d48a250275389a4c255228e46a2d128742a1104803b9d4e672381bcda6b3499ccc6431164ae552a148a04e2612c92481f0f46833150a442200f074361a0c8602e160a84c24110803c1c0d058281208038180a04018080200 } : Fields).get c.val)
theorem record007_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 128 164 :=
  interval_of_check _ 128 36 (by decide +kernel)
theorem record007_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record007) (record007.maps 6)
      (record007.inverseMaps 6) record007_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 164 record007_frame006_links_0000 (interval_append _ 64 128 164 record007_frame006_links_0064 record007_frame006_links_0128))
theorem record007_frame006_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 6 :=
  of_group record007 6 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1083
    Papers.RationalityTen.SharedFrameCatalogue.group1083_facts record007_frame006_indices record007_frame006_graph record007_frame006_links
def record007_frame007_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x67f327d874c30610305180cbfa5f82f9d7a0bab5caac5954ca9e546aa094eca6b530a94d47aa1b50426393049704af253527692e48fa41d1c88ce462a2cd14289043f21c90c484c417a06902a7ff3f51f50f7c7253591a90d2c68533c99a0cc065332096c4b4c5972c515ecadc5652ac1514a3850b27e13b49bc4d326392d093a48f23f91b08b844d21e8ef476039e1c70df86dc3631aa8d006483121830bd05c62d31610ae055029412b891446422010607f43dc1e00e8870c3721ab0cc058829a13e097047421e0ff07903941ac0ca05502a413809b03781b80c005f020810006e03601a80d006603201880a004e0260128090046022009804801800b00500240100060028010006002 } : Fields).get c.val)
theorem record007_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 128 164 :=
  interval_of_check _ 128 36 (by decide +kernel)
theorem record007_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 7)
      (record007.inverseMaps 7) record007_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 164 record007_frame007_links_0000 (interval_append _ 64 128 164 record007_frame007_links_0064 record007_frame007_links_0128))
theorem record007_frame007_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 7 :=
  of_group record007 7 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record007_frame007_indices record007_frame007_graph record007_frame007_links
def record007_frame008_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0xa6740e6f4d99ad34264cc49812ee5a4aa9451ce26c4988b1021ec378610ae12418824fa1f23de7acf41e6bc7784ee9d83a874ae7dce39771ee21c1b7b6e4da9b3b636c0d69a9b1c5e4bb5742e15b6b5167aca588a113e27a4ec9bd35a684c09612424347a8d517a2a44285d062033f87d8f91ec3cc6c8d59a533e664c998d3085e8b69652c056cab9542a0530a213c2544908e91a228440849041fa3e0790ed1d2358688cd1903105e8b81662c0558a712824c430850d41a42e05b07e0f81a8340660c81883005e09c1302504808c110210260480600b0140240400600a01001802 } : Fields).get c.val)
theorem record007_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 128 164 :=
  interval_of_check _ 128 36 (by decide +kernel)
theorem record007_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record007) (record007.maps 8)
      (record007.inverseMaps 8) record007_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 164 record007_frame008_links_0000 (interval_append _ 64 128 164 record007_frame008_links_0064 record007_frame008_links_0128))
theorem record007_frame008_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 8 :=
  of_group record007 8 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record007_frame008_indices record007_frame008_graph record007_frame008_links
def record007_frame009_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb18ad1a9aa89a82a7aa70a63a55a43a36a18a039a694893f93792e9239169098f88eb8ce8bc85084783c82f82180e7fc7e67d57b77a079c79378377276375373e72a70e6fb6f66e46d26bf6ab63a5e25d85cf5c65bc5ae59d58d5805044fa4ef4e44da4cc4bd4ac49e4764704634554474394284183ff3f03e13d33c23b33a333a32e3233163082f82ea2dc2d02b92a72a029628627526725a2492392051f61e51d71c91c21ba1ae1a01911831731651331271181070fa0f10e60d90cc0be0b50a009f09609506d06c05e05d04104003703603503403303203102802702602502402302201301200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record007_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 128 164 :=
  interval_of_check _ 128 36 (by decide +kernel)
theorem record007_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record007) (record007.maps 9)
      (record007.inverseMaps 9) record007_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 164 record007_frame009_links_0000 (interval_append _ 64 128 164 record007_frame009_links_0064 record007_frame009_links_0128))
theorem record007_frame009_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 9 :=
  of_group record007 9 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record007_frame009_indices record007_frame009_graph record007_frame009_links
def record007_frame010_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x6a468867366e66c66a66766466065b65764e6476195dc5d55ce5c75c35b75b15a459858557653d53653252c52451e5125074fd4e64d74d64d14cc4c64c14bc4b64b04a84a149f49949348d4864424013f93f23ec3e63dc3d43ca3bd35e35635234c34333c33132731f2fa2f52f12ec2e62e12da2d42cc2c52bf2ba2b62b22ad25024a24223522a22021620b1fe1ec1df1db1d51cc1c41b91b11a419917817016415b15114b14613e13412c12111510c0ea0e10d40cb0c10bb0b70b20ab0a409f09109008908806c06b05e05d03f03e03603503403303203103002802702602502402302201301200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record007_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 128 164 :=
  interval_of_check _ 128 36 (by decide +kernel)
theorem record007_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record007) (record007.maps 10)
      (record007.inverseMaps 10) record007_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 164 record007_frame010_links_0000 (interval_append _ 64 128 164 record007_frame010_links_0064 record007_frame010_links_0128))
theorem record007_frame010_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 10 :=
  of_group record007 10 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record007_frame010_indices record007_frame010_graph record007_frame010_links
def record007_frame011_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0637.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0637.count (({ width := 8, code := 0xa3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record007_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0637.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0637.localPairCheck (smallEmbedding record007) (record007.maps 11) (record007.inverseMaps 11) record007_frame011_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0637.localPairCheck (smallEmbedding record007) (record007.maps 11) (record007.inverseMaps 11) record007_frame011_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0637.localPairCheck (smallEmbedding record007) (record007.maps 11) (record007.inverseMaps 11) record007_frame011_indices (Fin.ofNat record007.n i)) 128 164 :=
  interval_of_check _ 128 36 (by decide +kernel)
theorem record007_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0637.localPairCheck (smallEmbedding record007) (record007.maps 11)
      (record007.inverseMaps 11) record007_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 164 record007_frame011_links_0000 (interval_append _ 64 128 164 record007_frame011_links_0064 record007_frame011_links_0128))
theorem record007_frame011_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 11 :=
  of_group record007 11 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0637
    Papers.RationalityTen.SharedFrameCatalogue.group0637_facts record007_frame011_indices record007_frame011_graph record007_frame011_links
def record007_frame012_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0635.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0635.count (({ width := 9, code := 0xab5469f4ea6d32974aa4d1a89419f4f26f369acd2673298cba59299348a43208fc7a3b1c8cc6229118843e1d0d8642e110781c01fefe7ebf1f6f476bb1d6e974399cae370b5daad368b3d9acc64b1982bf5f2f578ba5c2d964af56ab154a85327d3c9c4da6932974aa4d1e8c452210c8441204fc7b3a9d0e470371b4d86b349a0cc6431978b85a2c158aa532893c9a4c2391888431e0ec66321409c4a241188842200f874381b0d064301708840180b050241006028100602 } : Fields).get c.val)
theorem record007_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0635.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0635.localPairCheck (smallEmbedding record007) (record007.maps 12) (record007.inverseMaps 12) record007_frame012_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0635.localPairCheck (smallEmbedding record007) (record007.maps 12) (record007.inverseMaps 12) record007_frame012_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0635.localPairCheck (smallEmbedding record007) (record007.maps 12) (record007.inverseMaps 12) record007_frame012_indices (Fin.ofNat record007.n i)) 128 164 :=
  interval_of_check _ 128 36 (by decide +kernel)
theorem record007_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0635.localPairCheck (smallEmbedding record007) (record007.maps 12)
      (record007.inverseMaps 12) record007_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 164 record007_frame012_links_0000 (interval_append _ 64 128 164 record007_frame012_links_0064 record007_frame012_links_0128))
theorem record007_frame012_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 12 :=
  of_group record007 12 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0635
    Papers.RationalityTen.SharedFrameCatalogue.group0635_facts record007_frame012_indices record007_frame012_graph record007_frame012_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (Fin.cases (record007_frame005_supported hcells) (Fin.cases (record007_frame006_supported hcells) (Fin.cases (record007_frame007_supported hcells) (Fin.cases (record007_frame008_supported hcells) (Fin.cases (record007_frame009_supported hcells) (Fin.cases (record007_frame010_supported hcells) (Fin.cases (record007_frame011_supported hcells) (Fin.cases (record007_frame012_supported hcells) (fun j => Fin.elim0 j))))))))))))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x33bd9bcccc65db299920c7d634b14d86ea8a53ca99d4aca41515a8614089ee4e926112fa9764b7a5a12c295a4a9a53127c93749824a524491b48a243520c8f6477a3a11c28da37e1b9cdac6c33579a64d0866f32c98f0ae85612a794f4a5651828293d09c24be2561268910477233915488643220810007de3df1e78c145e42e01670af055229614289c849e23d11588644101f80f307503861a10c886002e01600ab053c29014109d04cc25812508f034413609103c01b80be05e02e81700b605a02c81600ae05602a810006c0270130094048023011008404001f00f0074024011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame001_links_0000 (interval_append _ 64 128 155 record008_frame001_links_0064 record008_frame001_links_0128))
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x367db14d736adb50da56d1467e339198aac855a2a81518a775312941476a27505a51926491e48623e91ce8d4460a2b5110876432214908483040fa034ff67d73e31ed4f4a7932ca1600ad85582a194b8a38507279935c8243fe1f50f6078c3b31d00e346f23541a10cc063c30e17e0bac5b22c71518a4850227112f883c4102010fd07cc3d81e50ef075c3921c20dd86d035a1a60cf86603221810bd05cc2d81650b005642a414b0a204f426c12f094035413609103c01b80be05e02e81700b605a02c81600ae05602a810006c0270130094048023011008404001f00f0074024011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame002_links_0000 (interval_append _ 64 128 155 record008_frame002_links_0064 record008_frame002_links_0128))
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0xd0d9f33a66acc19532363ac5d84ab8566abd552a553ea614928c4fc97d2e2594ac94d2824d49491d20a3e4768e11aa3245e8b114a2143c86d0c2153886fcdd9b63626acd219e330628b59682ca588af95c2b2558a994d29451ca214127c4ec9c13525a4a8939242424087f8fc1f23d8798f01da3a8720e11bc36c6c0d51a433c660c41822f85d8b816e2d85a8b41662c8588b015e28c470850e21a02c8580ae1582a8540a61482885009e0fc1b02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame003_links_0000 (interval_append _ 64 128 155 record008_frame003_links_0064 record008_frame003_links_0128))
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
def record008_frame004_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xdddb936d6ced81ad353698d199bada5aab41652c357aad957aa95349ed3c2754e49bd362694cc98d2ea5a4ae95128a4e49692122a3d4748dd1a2313a873ce51c437a6dcd81a9346650ba9722de5b0b49662c6580ae9572a8544a714b290514a113f26e4d09892e256430849062064007e8fa1ee3d0770eb1d0394710df1b83646b0ce196320628c21823005f8be17a2f05d8ba1722b44b88d0ec1b02e85c0b61682c8580ae1582a8540a61001b02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 4)
      (record008.inverseMaps 4) record008_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame004_links_0000 (interval_append _ 64 128 155 record008_frame004_links_0064 record008_frame004_links_0128))
theorem record008_frame004_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 4 :=
  of_group record008 4 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record008_frame004_indices record008_frame004_graph record008_frame004_links
def record008_frame005_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa87a80a78a6ca5fa51a3fa32a22a0793e93592c9209139068f58e88d98bf84583782a81c8097f77e07cf7bf79b79078076f76075073b7277136eb6d96c66b36a05d95d25c95bf5b15a059058357355d4fa4ef4e44da4cc4bd4ac49e49047546d4604524444364254154043e43d63c53b63a632d3203133052f52e72d92cd2be2a029628627526725a2492392282071f81e71d91cb1c21ba1ae1a01911831731651560b409508b07606c05d05c05b05a05905805705605505405304003602702602502402302202102001f01e01d01201101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record008_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 5)
      (record008.inverseMaps 5) record008_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame005_links_0000 (interval_append _ 64 128 155 record008_frame005_links_0064 record008_frame005_links_0128))
theorem record008_frame005_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 5 :=
  of_group record008 5 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record008_frame005_indices record008_frame005_graph record008_frame005_links
def record008_frame006_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x69b69368d68367766c65f6526466305a159c59158b57e57956f56155a5474f24ec4e24de4d24cb4bf4b14aa49548f48347846c46545944a43c42441740e4053f936836135c35034a34033332b32130e2b92b12ac2a229c29228527a27125c25324a23d23522c21e2112031e81df1d51cc1c018b18718117c17717116c16616115715414f14914313d13813212d12311d11611110e10c10a1051000fb0f60f00ea0e50a908b08307006705805705605505405305205105004f04e03f03602702602502402302202102001f01e01d01201101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record008_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record008) (record008.maps 6)
      (record008.inverseMaps 6) record008_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame006_links_0000 (interval_append _ 64 128 155 record008_frame006_links_0064 record008_frame006_links_0128))
theorem record008_frame006_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 6 :=
  of_group record008 6 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record008_frame006_indices record008_frame006_graph record008_frame006_links
def record008_frame007_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0657.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0657.count (({ width := 8, code := 0xd3d2d1d0cfcecccac8c7c5c4c3c2c1c0bebcbab9b7b6b5b4b3b2b1afadabaaa9a8a7a6a5a3a19f9d9c9b99979695949392908e8c8b89888786858483817f7d7c7b7a7978777573716f6e6d6b69686766656463615f5d5c5b5a5958575553514f4e4d4b4a49484746454443423d3c3b38373231302f2e2d2c2b2a29282625201f1e1d1c1b1a191817161211100f0e0d0c0b0a090806050403020100 } : Fields).get c.val)
theorem record008_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0657.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0657.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0657.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0657.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0657.localPairCheck (smallEmbedding record008) (record008.maps 7)
      (record008.inverseMaps 7) record008_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame007_links_0000 (interval_append _ 64 128 155 record008_frame007_links_0064 record008_frame007_links_0128))
theorem record008_frame007_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 7 :=
  of_group record008 7 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0657
    Papers.RationalityTen.SharedFrameCatalogue.group0657_facts record008_frame007_indices record008_frame007_graph record008_frame007_links
def record008_frame008_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0658.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0658.count (({ width := 9, code := 0x6773799cbe4f1f8cc4e1b017abc5dae970b65a6cd63aed52a751a7d329347a25067d3d9dce66d33994be5927924863d1b8ac4e230f85c1e09017f3e1deee763a9cee47137db8d96c359a8d16733594c7612fd78b95b2b558aa5429544a04ea692e964a2491e8c45a210a803e9e8ee74399c8e270379b8da6c3597cba5a2a1448642209007e3e1e8f0763a1c8dc6826128904622108803e1e0e87024110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0658.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0658.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0658.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0658.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0658.localPairCheck (smallEmbedding record008) (record008.maps 8)
      (record008.inverseMaps 8) record008_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame008_links_0000 (interval_append _ 64 128 155 record008_frame008_links_0064 record008_frame008_links_0128))
theorem record008_frame008_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 8 :=
  of_group record008 8 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0658
    Papers.RationalityTen.SharedFrameCatalogue.group0658_facts record008_frame008_indices record008_frame008_graph record008_frame008_links
def record008_frame009_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0656.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0656.count (({ width := 9, code := 0x45e2d158a44e250f86426110481c0a03007fbf1f2f67abc1deee76bb1d6e97338dc2e06fb79badc6db61aad16733196c86230d84c1602fd78b95b2d560af572b558ab54a9946a15027d3c9d4e26d309548a39188b4420d0481401fcfc7c3c9d8e873391c4e06f371acd0643097cbc5b2d164b0572b154a853291249045210fc70371b0d46833190c4602f170b05222108803e1e0e870361a0c86024110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0656.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0656.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0656.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0656.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0656.localPairCheck (smallEmbedding record008) (record008.maps 9)
      (record008.inverseMaps 9) record008_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame009_links_0000 (interval_append _ 64 128 155 record008_frame009_links_0064 record008_frame009_links_0128))
theorem record008_frame009_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 9 :=
  of_group record008 9 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0656
    Papers.RationalityTen.SharedFrameCatalogue.group0656_facts record008_frame009_indices record008_frame009_graph record008_frame009_links
def record008_frame010_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb31b27b20b14b06afaaecad6ac7aaf9d79c89c19b59a399498596f9609498c38b18a889888687686484b8378108007f77ea7d47c07ac7967817567407297126fc62b61d61360b5fe5f35e55d75cb5b454053052751c50e5014f14e14d34b34a449b49048247746945944a42941b40d3fc3ee36b35834d34133131f30c2fa2ea2c72b72ad2a12932862752652552322232132011f01e21d51cd1c41b51a81981871780bf09909107806e05f05e05d05c05b05a05905805705605504003602702602502402302202102001f01e01d01201101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record008_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 10)
      (record008.inverseMaps 10) record008_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame010_links_0000 (interval_append _ 64 128 155 record008_frame010_links_0064 record008_frame010_links_0128))
theorem record008_frame010_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 10 :=
  of_group record008 10 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record008_frame010_indices record008_frame010_graph record008_frame010_links
def record008_frame011_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x175ee65c8b876f2d9daeb4b66ac7d0fa134027dcf49e139a6e4d798f2664948d91320a3ec788e11aa2ec578a713a23c418790d21742083505206c076c2d59a6b46682ce598329640c41622bc56eabd5429d528a31432734d699d30a5b4ac9352223b4568950f218426718df9b836069cd119531c618ba96e2d0588ae95729c5109e92c24a4808c91421c420818ff1f23d0770e81c4294440810dc19c2f85e0ba1702d85a0b21602b8560aa1001b02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record008) (record008.maps 11) (record008.inverseMaps 11) record008_frame011_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record008) (record008.maps 11) (record008.inverseMaps 11) record008_frame011_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record008) (record008.maps 11) (record008.inverseMaps 11) record008_frame011_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record008) (record008.maps 11)
      (record008.inverseMaps 11) record008_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame011_links_0000 (interval_append _ 64 128 155 record008_frame011_links_0064 record008_frame011_links_0128))
theorem record008_frame011_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 11 :=
  of_group record008 11 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record008_frame011_indices record008_frame011_graph record008_frame011_links
def record008_frame012_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x66a66465f65964f64563d63462761459058858257b57356655f5555485394ed4e54df4d64cd4c24b74ab4a048c48548047847046645c45544843142841e41540d38938137a37336836235734a3413312e62dd2d72ce2c32bb2af2a129728427d27827026625f25424a24022921e21520d2051cb1c51bf1bc1b71b01aa1a419d18f18918418017a17316c16615e15114b14313d13913312c12712311d11610f1070ff0b208f08506f06805905805705605505405305205105004f03d03602702602502402302202102001f01e01d01201101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record008_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record008) (record008.maps 12) (record008.inverseMaps 12) record008_frame012_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record008) (record008.maps 12) (record008.inverseMaps 12) record008_frame012_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record008) (record008.maps 12) (record008.inverseMaps 12) record008_frame012_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record008) (record008.maps 12)
      (record008.inverseMaps 12) record008_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame012_links_0000 (interval_append _ 64 128 155 record008_frame012_links_0064 record008_frame012_links_0128))
theorem record008_frame012_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 12 :=
  of_group record008 12 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record008_frame012_indices record008_frame012_graph record008_frame012_links
def record008_frame013_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0868.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0868.count (({ width := 9, code := 0x46a33188b456271187c36110682c1205017fbf5f6f97a3c5e0ef773add4e973b99c4e06f375b6da6cb5dacd26833998ca6431d8cc461b057ebd5dad966b258ac15aac55aa550a4512813e9d4e26d32984a249208e4622510874320d04813f9f8f4783b1d4e672389bcdc6a34198c86230980be5e2e970b65a2c9409a4b2290c74391c0dc6c351a0cc6431180b45622108803e1e0e870361a0c86024110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0868.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0868.localPairCheck (smallEmbedding record008) (record008.maps 13) (record008.inverseMaps 13) record008_frame013_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0868.localPairCheck (smallEmbedding record008) (record008.maps 13) (record008.inverseMaps 13) record008_frame013_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0868.localPairCheck (smallEmbedding record008) (record008.maps 13) (record008.inverseMaps 13) record008_frame013_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0868.localPairCheck (smallEmbedding record008) (record008.maps 13)
      (record008.inverseMaps 13) record008_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame013_links_0000 (interval_append _ 64 128 155 record008_frame013_links_0064 record008_frame013_links_0128))
theorem record008_frame013_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 13 :=
  of_group record008 13 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0868
    Papers.RationalityTen.SharedFrameCatalogue.group0868_facts record008_frame013_indices record008_frame013_graph record008_frame013_links
def record008_frame014_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0x394e478ee2f88e1781df779dcf3dceb37cd331cbb2ac9720c66f8bd2f0baee6b86d8b3ec6aeab6acaadaa6a5a8299a4a839f2759ca6e8f63a8de348c62e8aa2487a177f5fa7ddf37bdeb795db745c4705be6e5b56c5ac6959e63d886057e5e957551515394a519414e531491214791a4591243908408f53c0eb3a0e437cdb35cd333ccb31cbf2dc6d1a06115c5011c461144410c42104400fc3e0f4370cc270982509023088210801f0781d048110400f0380d0300b02809020060140400c0200400 } : Fields).get c.val)
theorem record008_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record008) (record008.maps 14) (record008.inverseMaps 14) record008_frame014_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record008) (record008.maps 14) (record008.inverseMaps 14) record008_frame014_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record008) (record008.maps 14) (record008.inverseMaps 14) record008_frame014_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record008) (record008.maps 14)
      (record008.inverseMaps 14) record008_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame014_links_0000 (interval_append _ 64 128 155 record008_frame014_links_0064 record008_frame014_links_0128))
theorem record008_frame014_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 14 :=
  of_group record008 14 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record008_frame014_indices record008_frame014_graph record008_frame014_links
def record008_frame015_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0380.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0380.count (({ width := 8, code := 0xa4a3a2a1a09f9e9d9c9a9998979695949392918f8e8d8c8b8a8988878684838281807f7e7d7c7a797877767574737271706f6e6d6b6a6968676665646362605f5e5d5c5b5a5958565554535251504f4e4d4c4b4a4947464544434241403f3d3c3b3a393837363534333231302e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0380.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0380.localPairCheck (smallEmbedding record008) (record008.maps 15) (record008.inverseMaps 15) record008_frame015_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0380.localPairCheck (smallEmbedding record008) (record008.maps 15) (record008.inverseMaps 15) record008_frame015_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0380.localPairCheck (smallEmbedding record008) (record008.maps 15) (record008.inverseMaps 15) record008_frame015_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0380.localPairCheck (smallEmbedding record008) (record008.maps 15)
      (record008.inverseMaps 15) record008_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame015_links_0000 (interval_append _ 64 128 155 record008_frame015_links_0064 record008_frame015_links_0128))
theorem record008_frame015_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 15 :=
  of_group record008 15 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0380
    Papers.RationalityTen.SharedFrameCatalogue.group0380_facts record008_frame015_indices record008_frame015_graph record008_frame015_links
def record008_frame016_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0381.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0381.count (({ width := 9, code := 0x4aa532893c9a4b2491c8a411389446210f87436190b84c05fefd7dbe5eef579bc5daec75ba9d2e873b99cae371385c0df69345a0cf6733598cb6532180be5e2e970b65a2c960ac55aa952a853a994aa451285409f4f2411c8c452210c8541a04f87a3c1d8e872381b4d46431180bc5d2d964ae55299449e4c248dc6c35188c05e2e168b0562a148a04e2612884401f0f074381b0d06430170b0542210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record008_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0381.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record008) (record008.maps 16) (record008.inverseMaps 16) record008_frame016_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record008) (record008.maps 16) (record008.inverseMaps 16) record008_frame016_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record008) (record008.maps 16) (record008.inverseMaps 16) record008_frame016_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record008) (record008.maps 16)
      (record008.inverseMaps 16) record008_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame016_links_0000 (interval_append _ 64 128 155 record008_frame016_links_0064 record008_frame016_links_0128))
theorem record008_frame016_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 16 :=
  of_group record008 16 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0381
    Papers.RationalityTen.SharedFrameCatalogue.group0381_facts record008_frame016_indices record008_frame016_graph record008_frame016_links
def record008_frame017_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0379.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0379.count (({ width := 9, code := 0x5eeef75ba5cae16fb6daad159ac552a751a853a974aa3cfe7b3a9ccda6933984ba592a93c9a47219047635168a4461b0b7e3e9f2f67abcde0ef76ba9c4df6f36db4d76ab51a2cf6632d90c76230980bd5c2d968b05729548a24fa7538994ba59249147a3114894320d027c3c9dce872381b8d86b3499cca63309509c4a218fc72381b8d86a34198c86230178a84c200f8783a1c0d86832180b85824110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record008) (record008.maps 17) (record008.inverseMaps 17) record008_frame017_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record008) (record008.maps 17) (record008.inverseMaps 17) record008_frame017_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record008) (record008.maps 17) (record008.inverseMaps 17) record008_frame017_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record008) (record008.maps 17)
      (record008.inverseMaps 17) record008_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame017_links_0000 (interval_append _ 64 128 155 record008_frame017_links_0064 record008_frame017_links_0128))
theorem record008_frame017_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 17 :=
  of_group record008 17 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0379
    Papers.RationalityTen.SharedFrameCatalogue.group0379_facts record008_frame017_indices record008_frame017_graph record008_frame017_links
def record008_frame018_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0452.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0452.count (({ width := 9, code := 0x58ac15eae56ab156aa54a9f419fcf677399bcd6673197496451f8e4662d13884360d0481401fcfc7d3e1ecf177bb5d6e96e369b0d66a349a0ce6632180be5e2e970b65a2c960ab54a9d4aa350a7d3a9b4ba55269147a190882401f8f87a3c1d8e471381bcdc6d361a8d06431180bc5c2d164b0572b154a852280f0763a1b0d46833190c4602f170b4582b150984a1f0f074381b0d06430170b0542210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record008_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record008) (record008.maps 18) (record008.inverseMaps 18) record008_frame018_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record008) (record008.maps 18) (record008.inverseMaps 18) record008_frame018_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record008) (record008.maps 18) (record008.inverseMaps 18) record008_frame018_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record008) (record008.maps 18)
      (record008.inverseMaps 18) record008_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame018_links_0000 (interval_append _ 64 128 155 record008_frame018_links_0064 record008_frame018_links_0128))
theorem record008_frame018_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 18 :=
  of_group record008 18 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0452
    Papers.RationalityTen.SharedFrameCatalogue.group0452_facts record008_frame018_indices record008_frame018_graph record008_frame018_links
def record008_frame019_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0451.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0451.count (({ width := 8, code := 0xa4a3a2a1a09f9e9d9c9a9998979695949392918f8e8d8c8b8a8988878684838281807f7e7d7c7a797877767574737271706f6e6d6b6a6968676665646362605f5e5d5c5b5a5958565554535251504f4e4d4c4b4a4947464544434241403f3d3c3b3a393837363534333231302e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0451.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0451.localPairCheck (smallEmbedding record008) (record008.maps 19) (record008.inverseMaps 19) record008_frame019_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0451.localPairCheck (smallEmbedding record008) (record008.maps 19) (record008.inverseMaps 19) record008_frame019_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0451.localPairCheck (smallEmbedding record008) (record008.maps 19) (record008.inverseMaps 19) record008_frame019_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0451.localPairCheck (smallEmbedding record008) (record008.maps 19)
      (record008.inverseMaps 19) record008_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame019_links_0000 (interval_append _ 64 128 155 record008_frame019_links_0064 record008_frame019_links_0128))
theorem record008_frame019_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 19 :=
  of_group record008 19 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0451
    Papers.RationalityTen.SharedFrameCatalogue.group0451_facts record008_frame019_indices record008_frame019_graph record008_frame019_links
def record008_frame020_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0310.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0310.count (({ width := 8, code := 0xbdbcbbbab9b8b7b6b5b3b2b1b0afaeadacabaaa8a6a4a2a09e9c9a9896939291908f8e8d8c8b898887868584838281807f7e7d7c7a78767472706e6c6a686564636261605f5e5d5b5a595857565554535251504f4e4c4b4a4948474645444241403f3e3d3c3b3a39383736352e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0310.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0310.localPairCheck (smallEmbedding record008) (record008.maps 20) (record008.inverseMaps 20) record008_frame020_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0310.localPairCheck (smallEmbedding record008) (record008.maps 20) (record008.inverseMaps 20) record008_frame020_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0310.localPairCheck (smallEmbedding record008) (record008.maps 20) (record008.inverseMaps 20) record008_frame020_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0310.localPairCheck (smallEmbedding record008) (record008.maps 20)
      (record008.inverseMaps 20) record008_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame020_links_0000 (interval_append _ 64 128 155 record008_frame020_links_0064 record008_frame020_links_0128))
theorem record008_frame020_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 20 :=
  of_group record008 20 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0310
    Papers.RationalityTen.SharedFrameCatalogue.group0310_facts record008_frame020_indices record008_frame020_graph record008_frame020_links
def record008_frame021_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0308.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0308.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0308.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0308.localPairCheck (smallEmbedding record008) (record008.maps 21) (record008.inverseMaps 21) record008_frame021_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0308.localPairCheck (smallEmbedding record008) (record008.maps 21) (record008.inverseMaps 21) record008_frame021_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0308.localPairCheck (smallEmbedding record008) (record008.maps 21) (record008.inverseMaps 21) record008_frame021_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0308.localPairCheck (smallEmbedding record008) (record008.maps 21)
      (record008.inverseMaps 21) record008_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame021_links_0000 (interval_append _ 64 128 155 record008_frame021_links_0064 record008_frame021_links_0128))
theorem record008_frame021_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 21 :=
  of_group record008 21 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0308
    Papers.RationalityTen.SharedFrameCatalogue.group0308_facts record008_frame021_indices record008_frame021_graph record008_frame021_links
def record008_frame022_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x2fa17aabbf5d8ae8171ab7d5b62d6569aa4d51d2885424a024f8a7893a49c14d9a4bd2308ff476236d18e8b545222410ea85d42320c904080f3ff1fb0fb67be3d49e40efa76b32398c8c3a60e2ff97bcbc25d22e116d0a7652728914089e84e726b93249784a524992048e246422b912487842f20b901c7ea3e71ed8d4067432418a8c185ee2e816c8b2856229d14509e04da260129091c47422210887fc3e41e50eb071836a1a80ce064030a1790b6832013609103c01b80be05e02e81700b605a02c81600ae05602a810006c0270130094048023011008404001f00f0074024011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record008_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 22) (record008.inverseMaps 22) record008_frame022_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 22) (record008.inverseMaps 22) record008_frame022_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 22) (record008.inverseMaps 22) record008_frame022_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 22)
      (record008.inverseMaps 22) record008_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame022_links_0000 (interval_append _ 64 128 155 record008_frame022_links_0064 record008_frame022_links_0128))
theorem record008_frame022_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 22 :=
  of_group record008 22 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record008_frame022_indices record008_frame022_graph record008_frame022_links
def record008_frame023_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x5b05ab5a75a059a59558a58457e5754fb4f64f24e94e34dd4d44ce4c94c048647f47847046846145845044943d43743042942241c41540e4083fb3f43ed3e73e036d36535f35a35334b34333c33432b2e62d92cf2c82c22bb2b02a829f29028927e27627126c26525e25724723d2342302291e11d41ca1c11b91b01a71a119a18b18417916f16816115b15615114213812f12a12311c1161101091040fe0f80f30ed0b109008707406b05c05b05a05905805705605505405305204003602702602502402302202102001f01e01d01201101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record008_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record008) (record008.maps 23) (record008.inverseMaps 23) record008_frame023_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record008) (record008.maps 23) (record008.inverseMaps 23) record008_frame023_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record008) (record008.maps 23) (record008.inverseMaps 23) record008_frame023_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record008) (record008.maps 23)
      (record008.inverseMaps 23) record008_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame023_links_0000 (interval_append _ 64 128 155 record008_frame023_links_0064 record008_frame023_links_0128))
theorem record008_frame023_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 23 :=
  of_group record008 23 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record008_frame023_indices record008_frame023_graph record008_frame023_links
def record008_frame024_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1049.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1049.count (({ width := 9, code := 0x6230b81bedeef377badcedf64b0d76b357aad4ea34fa5d067f3c9ccde6b3398cbe592a93c9245208fc7637178a446210f82405faf97bbd5e6f177badc2df6e365aed569b459ecc6531d88c2602fd7abb5bad162b057a9546a04ea6d32974aa4d208e45a210c8441a04fe7b3c1d4e873391c4e06f371b4d86b35188c05d2b9508a442190882401f8f87a3c1d8e46c2713094482311084401f0f07424110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1049.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record008) (record008.maps 24) (record008.inverseMaps 24) record008_frame024_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record008) (record008.maps 24) (record008.inverseMaps 24) record008_frame024_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame024_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record008) (record008.maps 24) (record008.inverseMaps 24) record008_frame024_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record008) (record008.maps 24)
      (record008.inverseMaps 24) record008_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame024_links_0000 (interval_append _ 64 128 155 record008_frame024_links_0064 record008_frame024_links_0128))
theorem record008_frame024_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 24 :=
  of_group record008 24 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1049
    Papers.RationalityTen.SharedFrameCatalogue.group1049_facts record008_frame024_indices record008_frame024_graph record008_frame024_links
def record008_frame025_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0604.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0604.count (({ width := 11, code := 0xfb1f4be67c0f65ebbd0796f15ddb9a730e51c738970ae01be3746d2d19a0b3b66acb594b2263ac5585b07600be9792ef5d0b956f2d1594b15602ba50ca0d4027b4e69b934a654b694d1b23145489d0fa1a426839019fb3ec7bcf59e53c0768eb1cd37c6dcd89ab346608be1772e25a0b095b2b0540a39422764d8971272464808c90b2043f47b0ee1ce38c6e8d91a6334648c617e2183b0700ca17c298520a21402784e09a1302584a0921001b02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record008) (record008.maps 25) (record008.inverseMaps 25) record008_frame025_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record008) (record008.maps 25) (record008.inverseMaps 25) record008_frame025_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame025_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record008) (record008.maps 25) (record008.inverseMaps 25) record008_frame025_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record008) (record008.maps 25)
      (record008.inverseMaps 25) record008_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame025_links_0000 (interval_append _ 64 128 155 record008_frame025_links_0064 record008_frame025_links_0128))
theorem record008_frame025_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 25 :=
  of_group record008 25 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0604
    Papers.RationalityTen.SharedFrameCatalogue.group0604_facts record008_frame025_indices record008_frame025_graph record008_frame025_links
def record008_frame026_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0x168ace598b2b62ac1d80af75ceb4d20a33452875059f93e279ceb9c1266464868fb1ca344618b71461d42c84d07608c07800fe5f83df79cefdd9ba56aad35a3340676cc595b27644c556fad2592b0d5e2b355caa151a9250ea013c2704cc9812c2544888d91522042a780ea1cb38c700dc1b335c6a4cc98e30c600be1742dc5a0b29572965009c13024e46c8990f20e4047e8f61e42443e8770d0180298520a21402784e09a1302584a0920f01a02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record008) (record008.maps 26) (record008.inverseMaps 26) record008_frame026_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record008) (record008.maps 26) (record008.inverseMaps 26) record008_frame026_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame026_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record008) (record008.maps 26) (record008.inverseMaps 26) record008_frame026_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record008) (record008.maps 26)
      (record008.inverseMaps 26) record008_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame026_links_0000 (interval_append _ 64 128 155 record008_frame026_links_0064 record008_frame026_links_0128))
theorem record008_frame026_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 26 :=
  of_group record008 26 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record008_frame026_indices record008_frame026_graph record008_frame026_links
def record008_frame027_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0822.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0822.count (({ width := 9, code := 0x452271288c421d0d8642e110682c120702803fdfcfd7d3c9e2f077bb5d6ea7439dc8e371385bedd6e369b2d669b419ccc6532590c76331186c260af96cb55a2cd62af572b156a853a994aa350a813c9d4d25d2892482210e8642a0d02803f1f4f4793c1dcea73391c0de6c34998c86230980be5e2e970b65a2c93c9a4b23110763a1c8e06e361a8d06632188b8582311084401f0f074381b0d06424110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame027_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0822.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame027_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0822.localPairCheck (smallEmbedding record008) (record008.maps 27) (record008.inverseMaps 27) record008_frame027_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame027_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0822.localPairCheck (smallEmbedding record008) (record008.maps 27) (record008.inverseMaps 27) record008_frame027_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame027_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0822.localPairCheck (smallEmbedding record008) (record008.maps 27) (record008.inverseMaps 27) record008_frame027_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame027_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0822.localPairCheck (smallEmbedding record008) (record008.maps 27)
      (record008.inverseMaps 27) record008_frame027_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame027_links_0000 (interval_append _ 64 128 155 record008_frame027_links_0064 record008_frame027_links_0128))
theorem record008_frame027_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 27 :=
  of_group record008 27 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0822
    Papers.RationalityTen.SharedFrameCatalogue.group0822_facts record008_frame027_indices record008_frame027_graph record008_frame027_links
def record008_frame028_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0351.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0351.count (({ width := 9, code := 0x6bf5babd4e9f4ba3d0e7f398ac461b0982c05faf97abbdc2db6ab358abd5aab54a9749a3d12833e9dce26b2f964a64f258a4461d0b8441604ff7e3e1e2ee75b9dc6df6db5da6cd65b258cc3602f574b758ab552a651a5d2a9348a39168842a08fc7d3e1ecf2773a9cce26e361a8d0663218cc4612f974b6592b8e870371b0d46833190c4602f170b4582b150a45022108803e1e0e870361a0c8602210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record008_frame028_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame028_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record008) (record008.maps 28) (record008.inverseMaps 28) record008_frame028_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame028_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record008) (record008.maps 28) (record008.inverseMaps 28) record008_frame028_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame028_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record008) (record008.maps 28) (record008.inverseMaps 28) record008_frame028_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame028_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record008) (record008.maps 28)
      (record008.inverseMaps 28) record008_frame028_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame028_links_0000 (interval_append _ 64 128 155 record008_frame028_links_0064 record008_frame028_links_0128))
theorem record008_frame028_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 28 :=
  of_group record008 28 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0351
    Papers.RationalityTen.SharedFrameCatalogue.group0351_facts record008_frame028_indices record008_frame028_graph record008_frame028_links
def record008_frame029_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0432.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0432.count (({ width := 8, code := 0xbdbcbbbab9b8b7b6b5b3b2b1b0afaeadacabaaa8a6a4a2a09e9c9a9896939291908f8e8d8c8b898887868584838281807f7e7d7c7a78767472706e6c6a686564636261605f5e5d5b5a595857565554535251504f4e4c4b4a4948474645444241403f3e3d3c3b3a39383736352e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame029_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0432.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame029_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0432.localPairCheck (smallEmbedding record008) (record008.maps 29) (record008.inverseMaps 29) record008_frame029_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame029_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0432.localPairCheck (smallEmbedding record008) (record008.maps 29) (record008.inverseMaps 29) record008_frame029_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame029_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0432.localPairCheck (smallEmbedding record008) (record008.maps 29) (record008.inverseMaps 29) record008_frame029_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame029_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0432.localPairCheck (smallEmbedding record008) (record008.maps 29)
      (record008.inverseMaps 29) record008_frame029_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame029_links_0000 (interval_append _ 64 128 155 record008_frame029_links_0064 record008_frame029_links_0128))
theorem record008_frame029_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 29 :=
  of_group record008 29 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0432
    Papers.RationalityTen.SharedFrameCatalogue.group0432_facts record008_frame029_indices record008_frame029_graph record008_frame029_links
def record008_frame030_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x32e1962caa652327592cc8f64432058f0adb56aab3958eac055caac9556aa454da6a93309864bb25912a6940496a46d1ee8e5469a30d1628a0446a1e90d084b42220f506c82f33e19d4cde6683309968ca664c32298f4af256c2af9544a865352931460a144ec26f93489884b6254126491647d23291808b64562288db46be34f19f8cc063e30e17f0bb85982be1570a7851e27e136897449a231115088c43821510307c83c01cc0db868831c17c0b5034813609103c01b80be05e02e81700b605a02c81600ae05602a810006c0270130094048023011008404001f00f0074024011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record008_frame030_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame030_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 30) (record008.inverseMaps 30) record008_frame030_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame030_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 30) (record008.inverseMaps 30) record008_frame030_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame030_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 30) (record008.inverseMaps 30) record008_frame030_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame030_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 30)
      (record008.inverseMaps 30) record008_frame030_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame030_links_0000 (interval_append _ 64 128 155 record008_frame030_links_0064 record008_frame030_links_0128))
theorem record008_frame030_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 30 :=
  of_group record008 30 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record008_frame030_indices record008_frame030_graph record008_frame030_links
def record008_frame031_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x15deb9d6dad1592b0559aa5536a2cd099931a60cbd9732ca55ca693d18e2e45489d1222143b8690b20f41781f02601bfd7ecfbdf3bdb7aef4de7bcb6bcd65aa34f694d159fb39664ca56c2d0592b0d5f2bb566aa551290512a093d2754e099d2e2534808e51a22f452758e79c83806ecdb1ad344664c297d2ec5c0b59682c0558a79402724d0979292464708a90f2124087e0f51dc298430800de1942b0550a814c290510a013c2704d0980fc1b02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame031_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame031_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record008) (record008.maps 31) (record008.inverseMaps 31) record008_frame031_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame031_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record008) (record008.maps 31) (record008.inverseMaps 31) record008_frame031_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame031_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record008) (record008.maps 31) (record008.inverseMaps 31) record008_frame031_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame031_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record008) (record008.maps 31)
      (record008.inverseMaps 31) record008_frame031_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame031_links_0000 (interval_append _ 64 128 155 record008_frame031_links_0064 record008_frame031_links_0128))
theorem record008_frame031_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 31 :=
  of_group record008 31 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record008_frame031_indices record008_frame031_graph record008_frame031_links
def record008_frame032_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x1aaf53ea2d3da6349e8ed11a073cdc5b816eada5afb5568ece595b1b4928e513a113fe7c4ec9c736a624bc96729e4ec969132023b4618b51522844a72ce45c5b85700dedba36d6ccd797aaed5c8b61672c7574ac553a8f50e9f939a6a4c695d272454648ad12a21436770ea9ce38c700dc1b0352688c918b3085f0bb16e2cc57cac14a28c5089f13a26a4bc9592523c4608910c20e2b84a08d0ea1b02e85c0b61682c8580ae1582a8540a60fc1b02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame032_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame032_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record008) (record008.maps 32) (record008.inverseMaps 32) record008_frame032_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame032_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record008) (record008.maps 32) (record008.inverseMaps 32) record008_frame032_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame032_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record008) (record008.maps 32) (record008.inverseMaps 32) record008_frame032_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame032_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record008) (record008.maps 32)
      (record008.inverseMaps 32) record008_frame032_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame032_links_0000 (interval_append _ 64 128 155 record008_frame032_links_0064 record008_frame032_links_0128))
theorem record008_frame032_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 32 :=
  of_group record008 32 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record008_frame032_indices record008_frame032_graph record008_frame032_links
def record008_frame033_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1096.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1096.count (({ width := 9, code := 0x412070280c01fefd7e3edeef278bc1deee76badd4e972b7dbcdc6db65aed66a349a0cf66b3194c863b1586c1602fd7cbd5c2dd6cb55a2cd62b057aad4aa4512853e9d4e26930964aa4d249047235168943a190a84419f4f87a3c9dcea74391c0dc6d359a8d0663298cc25f2f174b85b2d164b0572b154a85329130964a23114763a1c8e06e361a8d06632188bc5c241188842200f8783a1c0d86824110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame033_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1096.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame033_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1096.localPairCheck (smallEmbedding record008) (record008.maps 33) (record008.inverseMaps 33) record008_frame033_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame033_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1096.localPairCheck (smallEmbedding record008) (record008.maps 33) (record008.inverseMaps 33) record008_frame033_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame033_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1096.localPairCheck (smallEmbedding record008) (record008.maps 33) (record008.inverseMaps 33) record008_frame033_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame033_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1096.localPairCheck (smallEmbedding record008) (record008.maps 33)
      (record008.inverseMaps 33) record008_frame033_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame033_links_0000 (interval_append _ 64 128 155 record008_frame033_links_0064 record008_frame033_links_0128))
theorem record008_frame033_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 33 :=
  of_group record008 33 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1096
    Papers.RationalityTen.SharedFrameCatalogue.group1096_facts record008_frame033_indices record008_frame033_graph record008_frame033_links
def record008_frame034_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1097.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1097.count (({ width := 9, code := 0x45a2b1489c4a230f87436130481c0a03007fbf5f8fb7bbb9daeb74b9dcae471381bcdd6db65aed56a349a0ce66b3196ca62b1186c260b017cbd5e2e15eae562a950a652a8d429f4f27134984b255269147a391a8c45a09027f3e9ecf2783b1d0e471379b4d66934198c86230980be5e2e970b65a2c960ae562a93c9c4d249207a3c1d8e872381b8d86a34198c460251208c44211007c3c1d0e06c24110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame034_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1097.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame034_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record008) (record008.maps 34) (record008.inverseMaps 34) record008_frame034_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame034_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record008) (record008.maps 34) (record008.inverseMaps 34) record008_frame034_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame034_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record008) (record008.maps 34) (record008.inverseMaps 34) record008_frame034_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame034_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record008) (record008.maps 34)
      (record008.inverseMaps 34) record008_frame034_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame034_links_0000 (interval_append _ 64 128 155 record008_frame034_links_0064 record008_frame034_links_0128))
theorem record008_frame034_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 34 :=
  of_group record008 34 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1097
    Papers.RationalityTen.SharedFrameCatalogue.group1097_facts record008_frame034_indices record008_frame034_graph record008_frame034_links
def record008_frame035_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1095.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1095.count (({ width := 8, code := 0xebeae9e8e7e6e4e3e2dedbdad9d8d7d6d4d3d2cec9c8c6c5c4c2c1c0bebcbbb9b8b7b5b4b3b1afaeadacaba8a7a6a5a4a3a1a09f9b96959392918f8e8d8b89888685848281807e7c7b7a79787372706f6e6c6b6a6866656362615f5e5d5b595857565554535251504f4e4d4c464544403f37363534333231302f2e2d2b2a2221201f1e1d1c1b1a19181211100f0e0d0c0b0a090806050403020100 } : Fields).get c.val)
theorem record008_frame035_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1095.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame035_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1095.localPairCheck (smallEmbedding record008) (record008.maps 35) (record008.inverseMaps 35) record008_frame035_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame035_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1095.localPairCheck (smallEmbedding record008) (record008.maps 35) (record008.inverseMaps 35) record008_frame035_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame035_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1095.localPairCheck (smallEmbedding record008) (record008.maps 35) (record008.inverseMaps 35) record008_frame035_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame035_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1095.localPairCheck (smallEmbedding record008) (record008.maps 35)
      (record008.inverseMaps 35) record008_frame035_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame035_links_0000 (interval_append _ 64 128 155 record008_frame035_links_0064 record008_frame035_links_0128))
theorem record008_frame035_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 35 :=
  of_group record008 35 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1095
    Papers.RationalityTen.SharedFrameCatalogue.group1095_facts record008_frame035_indices record008_frame035_graph record008_frame035_links
def record008_frame036_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x195329651c9d92b23642c818f31a5b8b696c6d6da9b4b682ced99b235069c52ea4d46a88d049f33b66accf98f2ee59ca593724640c688c91822cc52794f19e1bc0778eddd93af756e8daa34d688cf99a32a63cc55862f85e6bb1712db59cb0d5e2b0536a614aa905168c114220436849039fd3e47b0ec1d239670cde1af34a678ca17e2f45d8b79692c6570a91472784c49291a21826c4087b0d21882a8540a61482885009e1382684c0960f01a02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame036_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame036_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 36) (record008.inverseMaps 36) record008_frame036_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame036_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 36) (record008.inverseMaps 36) record008_frame036_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame036_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 36) (record008.inverseMaps 36) record008_frame036_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame036_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 36)
      (record008.inverseMaps 36) record008_frame036_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame036_links_0000 (interval_append _ 64 128 155 record008_frame036_links_0064 record008_frame036_links_0128))
theorem record008_frame036_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 36 :=
  of_group record008 36 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record008_frame036_indices record008_frame036_graph record008_frame036_links
def record008_frame037_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x12ae53ca39412724c49291721e3f4378670c216c298490720cc13814f6deabcf794f0ddf3b775eea1cbb9271ae1dc137a6e8db5b2352698d21a23405c0b6d6bad359eb2d632c1578ad13da764e09b1332614ba9512723c46c8c51622643885d082073e67b8f49e33b8680cd195320624c017a2e45acac1532a0528a313e2704cc95918228440851031fc3e87a8ef1d23906f0d71a2248400790d41902b0550a814c290510a013c2704d0980f01a02604a090118220420800f81e03a0700901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame037_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame037_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record008) (record008.maps 37) (record008.inverseMaps 37) record008_frame037_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame037_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record008) (record008.maps 37) (record008.inverseMaps 37) record008_frame037_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame037_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record008) (record008.maps 37) (record008.inverseMaps 37) record008_frame037_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame037_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record008) (record008.maps 37)
      (record008.inverseMaps 37) record008_frame037_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame037_links_0000 (interval_append _ 64 128 155 record008_frame037_links_0064 record008_frame037_links_0128))
theorem record008_frame037_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 37 :=
  of_group record008 37 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record008_frame037_indices record008_frame037_graph record008_frame037_links
def record008_frame038_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x1142254478891021e4378650b612bc6786ef9debb876aec5d5ba9746dc5b6b666c8d6dabb4f68ed0999b2d650c898e31561cc157eaed5d0b91702dd4fa9e53c2734e49b133a644c096913a2143685907a093fe7e0f89e33ba76ce99d1392700dd9b434667ccd997328588ae9592a8540a594527c4e49812d24e48c8e919226434838fc1ee3d4798f11da3a8720df1b6360690cb188248400790d2180298520a21402784e09a1302584a0920e81a02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame038_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame038_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record008) (record008.maps 38) (record008.inverseMaps 38) record008_frame038_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame038_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record008) (record008.maps 38) (record008.inverseMaps 38) record008_frame038_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame038_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record008) (record008.maps 38) (record008.inverseMaps 38) record008_frame038_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame038_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record008) (record008.maps 38)
      (record008.inverseMaps 38) record008_frame038_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame038_links_0000 (interval_append _ 64 128 155 record008_frame038_links_0064 record008_frame038_links_0128))
theorem record008_frame038_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 38 :=
  of_group record008 38 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record008_frame038_indices record008_frame038_graph record008_frame038_links
def record008_frame039_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0643.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0643.count (({ width := 9, code := 0x4622f168ac52271187c36130280c01fefe7ebedf2f779bb1d4e97439dcce571b85badb6d365b0d76b351a4cd65b2992c860b017ebe5eaf174b85b2c956a95429d4ca552289409c4d26530974b255269146229128843a00fc7d3e1ecf4793b9d4e26f371b4d86b351a0cc612f978ba5c2d968b2582b958aa542993494482190472381b8d86a34198c86230178b05422108803e1e0e870361a0c86024110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame039_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0643.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame039_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0643.localPairCheck (smallEmbedding record008) (record008.maps 39) (record008.inverseMaps 39) record008_frame039_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame039_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0643.localPairCheck (smallEmbedding record008) (record008.maps 39) (record008.inverseMaps 39) record008_frame039_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame039_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0643.localPairCheck (smallEmbedding record008) (record008.maps 39) (record008.inverseMaps 39) record008_frame039_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame039_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0643.localPairCheck (smallEmbedding record008) (record008.maps 39)
      (record008.inverseMaps 39) record008_frame039_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame039_links_0000 (interval_append _ 64 128 155 record008_frame039_links_0064 record008_frame039_links_0128))
theorem record008_frame039_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 39 :=
  of_group record008 39 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0643
    Papers.RationalityTen.SharedFrameCatalogue.group0643_facts record008_frame039_indices record008_frame039_graph record008_frame039_links
def record008_frame040_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6de6db6d96d46ce6ca6c56be6b96b261260e60b6055ff5fb5f65f05eb5e457f57256d56255554a54053052350b5034f94ee4e34da4cc4bd4b249a49248c4874803ee3ea3e73e13dc3d83d43cf3ca3c236435b35835134833e33632d32230f3093032fc2f22ed2e12d72cf2bc2b72b32af2aa24523e23923022621b2122091fd1ea1e41de1d51c91c41b71ab1a518f18a18618117a17216715f15514613a12e11f1130a208b08506f06805b05a05905805705605505405305205103e03602702602502402302202102001f01e01d01201101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record008_frame040_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame040_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record008) (record008.maps 40) (record008.inverseMaps 40) record008_frame040_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame040_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record008) (record008.maps 40) (record008.inverseMaps 40) record008_frame040_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame040_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record008) (record008.maps 40) (record008.inverseMaps 40) record008_frame040_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame040_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record008) (record008.maps 40)
      (record008.inverseMaps 40) record008_frame040_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame040_links_0000 (interval_append _ 64 128 155 record008_frame040_links_0064 record008_frame040_links_0128))
theorem record008_frame040_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 40 :=
  of_group record008 40 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record008_frame040_indices record008_frame040_graph record008_frame040_links
def record008_frame041_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x15e6b8d6eacf582add56a9f526a1cc59832ee5a4ae95328e4e49792115e26c478830ea1a42f84d07206c067fafddf83eb7caf71eabc677eee1da3b067acdd99b2e652c918fb19626c315fab7568ab5552a2536a5946a7c4e69b53225e4b093522a3d44e8890ea19424700dc1b2352690ce992314600b59672c6570ab1542945049f12c24a4848f117220424818ff1f23d0770e81c226c4107d0de1a42e85c0b61682c8580ae1582a8540a61001b02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame041_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame041_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record008) (record008.maps 41) (record008.inverseMaps 41) record008_frame041_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame041_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record008) (record008.maps 41) (record008.inverseMaps 41) record008_frame041_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame041_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record008) (record008.maps 41) (record008.inverseMaps 41) record008_frame041_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame041_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record008) (record008.maps 41)
      (record008.inverseMaps 41) record008_frame041_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame041_links_0000 (interval_append _ 64 128 155 record008_frame041_links_0064 record008_frame041_links_0128))
theorem record008_frame041_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 41 :=
  of_group record008 41 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record008_frame041_indices record008_frame041_graph record008_frame041_links
def record008_frame042_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x10b21542984b0820f41c82f04a06bb976eed5d73a974ae89ce39571cd99b0b606b6d5da8b4c68ed019b33265cca59231e62ec4584afd5eebc1762e7524a41472875029f93da744de99d1f23946e8c915a2744086109206406800fd9f53e67b0f29e13ac738e49c5380640c69873045ecb916f2cc57caa14d29050c9d9352604a09011422042c839032023f07b0f21da398708d91a22343e0790d41882a0530a41442804f09c1342604b0940f01a82704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame042_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame042_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record008) (record008.maps 42) (record008.inverseMaps 42) record008_frame042_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame042_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record008) (record008.maps 42) (record008.inverseMaps 42) record008_frame042_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame042_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record008) (record008.maps 42) (record008.inverseMaps 42) record008_frame042_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame042_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record008) (record008.maps 42)
      (record008.inverseMaps 42) record008_frame042_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame042_links_0000 (interval_append _ 64 128 155 record008_frame042_links_0064 record008_frame042_links_0128))
theorem record008_frame042_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 42 :=
  of_group record008 42 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record008_frame042_indices record008_frame042_graph record008_frame042_links
def record008_frame043_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0856.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0856.count (({ width := 9, code := 0x40e02ff7e3e9f0f67a3c9dceb74b9dc8e270379b8da6b351a6d2683399acc653258ec662b0d82c05faf578ba5c2d96ab458abd5aaa5429948a25027134994c2592893492411e8d4622d1287432150682401f8f87b3d1e0ee763a1c8e270371b4d66a3499cca6431984c05e2e168b2582b958aa5429948a250279249047209006e361a8d06632188c05e2e168ac54211007c3c1d0e06c34190c05c24110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame043_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0856.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame043_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0856.localPairCheck (smallEmbedding record008) (record008.maps 43) (record008.inverseMaps 43) record008_frame043_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame043_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0856.localPairCheck (smallEmbedding record008) (record008.maps 43) (record008.inverseMaps 43) record008_frame043_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame043_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0856.localPairCheck (smallEmbedding record008) (record008.maps 43) (record008.inverseMaps 43) record008_frame043_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame043_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0856.localPairCheck (smallEmbedding record008) (record008.maps 43)
      (record008.inverseMaps 43) record008_frame043_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame043_links_0000 (interval_append _ 64 128 155 record008_frame043_links_0064 record008_frame043_links_0128))
theorem record008_frame043_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 43 :=
  of_group record008 43 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0856
    Papers.RationalityTen.SharedFrameCatalogue.group0856_facts record008_frame043_indices record008_frame043_graph record008_frame043_links
def record008_frame044_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0855.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0855.count (({ width := 8, code := 0xdedcdbd9d7d6d5d3d2d0c6c4c3c1bfbebdbbbab8b7b6b5b3b2b1b0afaeacabaaa8a7a6a5a4a3a19f9d9c9b918f8e8c8a89888685838281807e7d7c7b7a79777675737271706f6e6c6a68676665646361605f5e5d5c5a59585655545352514f4d4b4a494847464544434241403c39383534302f2e2d2c2b2a2928272624231f1e1d1c1b1a19181716151211100f0e0d0c0b0a090806050403020100 } : Fields).get c.val)
theorem record008_frame044_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0855.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame044_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0855.localPairCheck (smallEmbedding record008) (record008.maps 44) (record008.inverseMaps 44) record008_frame044_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame044_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0855.localPairCheck (smallEmbedding record008) (record008.maps 44) (record008.inverseMaps 44) record008_frame044_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame044_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0855.localPairCheck (smallEmbedding record008) (record008.maps 44) (record008.inverseMaps 44) record008_frame044_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame044_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0855.localPairCheck (smallEmbedding record008) (record008.maps 44)
      (record008.inverseMaps 44) record008_frame044_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame044_links_0000 (interval_append _ 64 128 155 record008_frame044_links_0064 record008_frame044_links_0128))
theorem record008_frame044_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 44 :=
  of_group record008 44 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0855
    Papers.RationalityTen.SharedFrameCatalogue.group0855_facts record008_frame044_indices record008_frame044_graph record008_frame044_links
def record008_frame045_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0374.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0374.count (({ width := 9, code := 0x5cee36fb6daed367b2d8ebf52a853a994aa451a89429f4d6652f964a64d23904762f1488c3a170882c09fefa7c3d9e8f373391c4e06f371b4d86b34994c86331184c05f2ed70b2582b958aa5429946a04da6932984ba411e8e46a31168a442190481401fcfc7d3e1e8f074399c8e270371b0d46833190c6612f9188a441f0f46e361a8d06632188c05e2e168ac54211007c3c1d0e06c34190c05c24110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame045_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0374.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame045_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0374.localPairCheck (smallEmbedding record008) (record008.maps 45) (record008.inverseMaps 45) record008_frame045_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame045_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0374.localPairCheck (smallEmbedding record008) (record008.maps 45) (record008.inverseMaps 45) record008_frame045_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame045_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0374.localPairCheck (smallEmbedding record008) (record008.maps 45) (record008.inverseMaps 45) record008_frame045_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame045_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0374.localPairCheck (smallEmbedding record008) (record008.maps 45)
      (record008.inverseMaps 45) record008_frame045_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame045_links_0000 (interval_append _ 64 128 155 record008_frame045_links_0064 record008_frame045_links_0128))
theorem record008_frame045_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 45 :=
  of_group record008 45 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0374
    Papers.RationalityTen.SharedFrameCatalogue.group0374_facts record008_frame045_indices record008_frame045_graph record008_frame045_links
def record008_frame046_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0373.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0373.count (({ width := 9, code := 0x4220d0481401fcfc7d3e1ecf378bbddaeb74b9dcae370b79b8da6c359a8d26833994c86331184c05f2f174b65a2c960ae56aad52a752a8d429f4ea6932984ba592a9449a49228e46229108642209007e3d9e4ee75399c0dc6c351a0cc6431180ba5c2d968b2582b958aa532893c9a4b249208e46229108642208d06431180bc5c2d160ac54291409c4c251208c441c0d86832180b8582a14098482210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record008_frame046_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0373.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame046_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record008) (record008.maps 46) (record008.inverseMaps 46) record008_frame046_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame046_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record008) (record008.maps 46) (record008.inverseMaps 46) record008_frame046_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame046_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record008) (record008.maps 46) (record008.inverseMaps 46) record008_frame046_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame046_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record008) (record008.maps 46)
      (record008.inverseMaps 46) record008_frame046_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame046_links_0000 (interval_append _ 64 128 155 record008_frame046_links_0064 record008_frame046_links_0128))
theorem record008_frame046_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 46 :=
  of_group record008 46 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0373
    Papers.RationalityTen.SharedFrameCatalogue.group0373_facts record008_frame046_indices record008_frame046_graph record008_frame046_links
def record008_frame047_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0446.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0446.count (({ width := 8, code := 0xa4a3a2a1a09f9e9d9c9a9998979695949392918f8e8d8c8b8a8988878684838281807f7e7d7c7a797877767574737271706f6e6d6b6a6968676665646362605f5e5d5c5b5a5958565554535251504f4e4d4c4b4a4947464544434241403f3d3c3b3a393837363534333231302e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame047_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0446.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame047_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0446.localPairCheck (smallEmbedding record008) (record008.maps 47) (record008.inverseMaps 47) record008_frame047_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame047_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0446.localPairCheck (smallEmbedding record008) (record008.maps 47) (record008.inverseMaps 47) record008_frame047_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame047_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0446.localPairCheck (smallEmbedding record008) (record008.maps 47) (record008.inverseMaps 47) record008_frame047_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame047_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0446.localPairCheck (smallEmbedding record008) (record008.maps 47)
      (record008.inverseMaps 47) record008_frame047_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame047_links_0000 (interval_append _ 64 128 155 record008_frame047_links_0064 record008_frame047_links_0128))
theorem record008_frame047_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 47 :=
  of_group record008 47 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0446
    Papers.RationalityTen.SharedFrameCatalogue.group0446_facts record008_frame047_indices record008_frame047_graph record008_frame047_links
def record008_frame048_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0445.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0445.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame048_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0445.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame048_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0445.localPairCheck (smallEmbedding record008) (record008.maps 48) (record008.inverseMaps 48) record008_frame048_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame048_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0445.localPairCheck (smallEmbedding record008) (record008.maps 48) (record008.inverseMaps 48) record008_frame048_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame048_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0445.localPairCheck (smallEmbedding record008) (record008.maps 48) (record008.inverseMaps 48) record008_frame048_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame048_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0445.localPairCheck (smallEmbedding record008) (record008.maps 48)
      (record008.inverseMaps 48) record008_frame048_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame048_links_0000 (interval_append _ 64 128 155 record008_frame048_links_0064 record008_frame048_links_0128))
theorem record008_frame048_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 48 :=
  of_group record008 48 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0445
    Papers.RationalityTen.SharedFrameCatalogue.group0445_facts record008_frame048_indices record008_frame048_graph record008_frame048_links
def record008_frame049_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0443.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0443.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame049_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0443.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame049_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0443.localPairCheck (smallEmbedding record008) (record008.maps 49) (record008.inverseMaps 49) record008_frame049_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame049_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0443.localPairCheck (smallEmbedding record008) (record008.maps 49) (record008.inverseMaps 49) record008_frame049_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame049_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0443.localPairCheck (smallEmbedding record008) (record008.maps 49) (record008.inverseMaps 49) record008_frame049_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame049_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0443.localPairCheck (smallEmbedding record008) (record008.maps 49)
      (record008.inverseMaps 49) record008_frame049_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame049_links_0000 (interval_append _ 64 128 155 record008_frame049_links_0064 record008_frame049_links_0128))
theorem record008_frame049_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 49 :=
  of_group record008 49 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0443
    Papers.RationalityTen.SharedFrameCatalogue.group0443_facts record008_frame049_indices record008_frame049_graph record008_frame049_links
def record008_frame050_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x69368c68567f67b67567066c6666605b35ac5a559e59a59558f58b58657f53052651b5135094ff4f44ee4e74d94cf4c44bb4b54ae4a649c49248647f47847046b3a93a439f39939439038b38638237b32b32331931430c3062fd2f72f22e72df2d52ce2c82c32bd2b52af2a52a029b29629322421920c2031fc1f31ea1e31dc1cc1c11b41ac1a519e19618f18617917216b16516115914e14513d13212711e1131080b009108b07406c05d05c05b05a05905805705605505405303f03602702602502402302202102001f01e01d01201101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record008_frame050_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame050_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record008) (record008.maps 50) (record008.inverseMaps 50) record008_frame050_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame050_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record008) (record008.maps 50) (record008.inverseMaps 50) record008_frame050_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame050_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record008) (record008.maps 50) (record008.inverseMaps 50) record008_frame050_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame050_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record008) (record008.maps 50)
      (record008.inverseMaps 50) record008_frame050_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame050_links_0000 (interval_append _ 64 128 155 record008_frame050_links_0064 record008_frame050_links_0128))
theorem record008_frame050_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 50 :=
  of_group record008 50 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record008_frame050_indices record008_frame050_graph record008_frame050_links
def record008_frame051_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1039.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1039.count (({ width := 11, code := 0x12ba54ca393b25a4948a90b1fe3bc1982903a03c027f8fd9f7beb7c4ed1d7ba7740e61c8b87702dedb73696c2d65a9b4d68ccf99bb2964ac858d313578ae55b2b1558a9950a9c52ca412ea594a6941262484808ed1a22c44c87d0c211414810fe9f63d278cee9d83a6674cb990312608bd9742da598ad9572a2528a293e2784e09a12a2484788b91321e428830ff1f23c8758e51bc2784207e0dc19c2c0570ac1542a0530a41442804f09c0f81b02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame051_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame051_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record008) (record008.maps 51) (record008.inverseMaps 51) record008_frame051_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame051_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record008) (record008.maps 51) (record008.inverseMaps 51) record008_frame051_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame051_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record008) (record008.maps 51) (record008.inverseMaps 51) record008_frame051_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame051_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record008) (record008.maps 51)
      (record008.inverseMaps 51) record008_frame051_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame051_links_0000 (interval_append _ 64 128 155 record008_frame051_links_0064 record008_frame051_links_0128))
theorem record008_frame051_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 51 :=
  of_group record008 51 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1039
    Papers.RationalityTen.SharedFrameCatalogue.group1039_facts record008_frame051_indices record008_frame051_graph record008_frame051_links
def record008_frame052_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0590.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0590.count (({ width := 11, code := 0x1032034027fefe9fabf27dcf9df039471ee25c3b826fade5ba36f6ccd059db3766ccc597328644c798b312616c1d812fd5f4bd577ae45beb716a2ce5049f13ca734e09ad33a644ba951172264468790ca1642082d031fe3f27d4f81ec3ce790f11dc3a0730e51c137861cc097d2f25c8b69672c256ca714c28a4f89c13225c4ac9111421e42c818fb1ee3cc768e71c43786d0d419e2383f87b0d01842a0530a41442804f09c1342604b0940e81a02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame052_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame052_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record008) (record008.maps 52) (record008.inverseMaps 52) record008_frame052_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame052_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record008) (record008.maps 52) (record008.inverseMaps 52) record008_frame052_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame052_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record008) (record008.maps 52) (record008.inverseMaps 52) record008_frame052_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame052_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record008) (record008.maps 52)
      (record008.inverseMaps 52) record008_frame052_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame052_links_0000 (interval_append _ 64 128 155 record008_frame052_links_0064 record008_frame052_links_0128))
theorem record008_frame052_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 52 :=
  of_group record008 52 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0590
    Papers.RationalityTen.SharedFrameCatalogue.group0590_facts record008_frame052_indices record008_frame052_graph record008_frame052_links
def record008_frame053_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0814.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0814.count (({ width := 11, code := 0x13a672ce39bd35e694ce9933125ec638bd1722b45089911e21c3e86efadf03dd7aef3de33be770ec5d139a726e31c2b7d6eedbdb435b6a4d29a1b3d5bab5d69ace594b19612be576ad13da724de9ad332604b695928a4647e8e91b2304548950fa1b426839052064066d4d59a534066cca18e31060cbb96e2ce588ae1562a2528a313b2664b0939242404608910c2043ec798e91c426c460870e61b02e85c0b61682c8580ae1582a8540a61001b02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame053_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame053_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record008) (record008.maps 53) (record008.inverseMaps 53) record008_frame053_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame053_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record008) (record008.maps 53) (record008.inverseMaps 53) record008_frame053_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame053_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record008) (record008.maps 53) (record008.inverseMaps 53) record008_frame053_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame053_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record008) (record008.maps 53)
      (record008.inverseMaps 53) record008_frame053_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame053_links_0000 (interval_append _ 64 128 155 record008_frame053_links_0064 record008_frame053_links_0128))
theorem record008_frame053_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 53 :=
  of_group record008 53 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0814
    Papers.RationalityTen.SharedFrameCatalogue.group0814_facts record008_frame053_indices record008_frame053_graph record008_frame053_links
def record008_frame054_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0810.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0810.count (({ width := 9, code := 0x4be5d2d964ae532793492411d8e46e35198bc562912874160702803f9fafb7d3e1eaf4793c1deed75ba5cee571b85bedd6d365b0d76b351a4d167b2d84c05faf576ba5c2dd6ab258abd5aac552a14ca4512813c9c4d2451e8e4622912874321102803f1f0f6793b9d4e671379b4d6693419ccc653218cc46130160ac54281388441200fc7c3d1e0ec74391c0d4662713094482311084401f0f07424110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame054_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0810.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame054_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0810.localPairCheck (smallEmbedding record008) (record008.maps 54) (record008.inverseMaps 54) record008_frame054_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame054_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0810.localPairCheck (smallEmbedding record008) (record008.maps 54) (record008.inverseMaps 54) record008_frame054_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame054_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0810.localPairCheck (smallEmbedding record008) (record008.maps 54) (record008.inverseMaps 54) record008_frame054_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame054_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0810.localPairCheck (smallEmbedding record008) (record008.maps 54)
      (record008.inverseMaps 54) record008_frame054_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame054_links_0000 (interval_append _ 64 128 155 record008_frame054_links_0064 record008_frame054_links_0128))
theorem record008_frame054_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 54 :=
  of_group record008 54 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0810
    Papers.RationalityTen.SharedFrameCatalogue.group0810_facts record008_frame054_indices record008_frame054_graph record008_frame054_links
def record008_frame055_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0346.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0346.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame055_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0346.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame055_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0346.localPairCheck (smallEmbedding record008) (record008.maps 55) (record008.inverseMaps 55) record008_frame055_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame055_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0346.localPairCheck (smallEmbedding record008) (record008.maps 55) (record008.inverseMaps 55) record008_frame055_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame055_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0346.localPairCheck (smallEmbedding record008) (record008.maps 55) (record008.inverseMaps 55) record008_frame055_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame055_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0346.localPairCheck (smallEmbedding record008) (record008.maps 55)
      (record008.inverseMaps 55) record008_frame055_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame055_links_0000 (interval_append _ 64 128 155 record008_frame055_links_0064 record008_frame055_links_0128))
theorem record008_frame055_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 55 :=
  of_group record008 55 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0346
    Papers.RationalityTen.SharedFrameCatalogue.group0346_facts record008_frame055_indices record008_frame055_graph record008_frame055_links
def record008_frame056_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0430.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0430.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame056_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0430.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame056_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0430.localPairCheck (smallEmbedding record008) (record008.maps 56) (record008.inverseMaps 56) record008_frame056_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame056_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0430.localPairCheck (smallEmbedding record008) (record008.maps 56) (record008.inverseMaps 56) record008_frame056_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame056_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0430.localPairCheck (smallEmbedding record008) (record008.maps 56) (record008.inverseMaps 56) record008_frame056_indices (Fin.ofNat record008.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record008_frame056_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0430.localPairCheck (smallEmbedding record008) (record008.maps 56)
      (record008.inverseMaps 56) record008_frame056_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record008_frame056_links_0000 (interval_append _ 64 128 155 record008_frame056_links_0064 record008_frame056_links_0128))
theorem record008_frame056_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 56 :=
  of_group record008 56 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0430
    Papers.RationalityTen.SharedFrameCatalogue.group0430_facts record008_frame056_indices record008_frame056_graph record008_frame056_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (Fin.cases (record008_frame004_supported hcells) (Fin.cases (record008_frame005_supported hcells) (Fin.cases (record008_frame006_supported hcells) (Fin.cases (record008_frame007_supported hcells) (Fin.cases (record008_frame008_supported hcells) (Fin.cases (record008_frame009_supported hcells) (Fin.cases (record008_frame010_supported hcells) (Fin.cases (record008_frame011_supported hcells) (Fin.cases (record008_frame012_supported hcells) (Fin.cases (record008_frame013_supported hcells) (Fin.cases (record008_frame014_supported hcells) (Fin.cases (record008_frame015_supported hcells) (Fin.cases (record008_frame016_supported hcells) (Fin.cases (record008_frame017_supported hcells) (Fin.cases (record008_frame018_supported hcells) (Fin.cases (record008_frame019_supported hcells) (Fin.cases (record008_frame020_supported hcells) (Fin.cases (record008_frame021_supported hcells) (Fin.cases (record008_frame022_supported hcells) (Fin.cases (record008_frame023_supported hcells) (Fin.cases (record008_frame024_supported hcells) (Fin.cases (record008_frame025_supported hcells) (Fin.cases (record008_frame026_supported hcells) (Fin.cases (record008_frame027_supported hcells) (Fin.cases (record008_frame028_supported hcells) (Fin.cases (record008_frame029_supported hcells) (Fin.cases (record008_frame030_supported hcells) (Fin.cases (record008_frame031_supported hcells) (Fin.cases (record008_frame032_supported hcells) (Fin.cases (record008_frame033_supported hcells) (Fin.cases (record008_frame034_supported hcells) (Fin.cases (record008_frame035_supported hcells) (Fin.cases (record008_frame036_supported hcells) (Fin.cases (record008_frame037_supported hcells) (Fin.cases (record008_frame038_supported hcells) (Fin.cases (record008_frame039_supported hcells) (Fin.cases (record008_frame040_supported hcells) (Fin.cases (record008_frame041_supported hcells) (Fin.cases (record008_frame042_supported hcells) (Fin.cases (record008_frame043_supported hcells) (Fin.cases (record008_frame044_supported hcells) (Fin.cases (record008_frame045_supported hcells) (Fin.cases (record008_frame046_supported hcells) (Fin.cases (record008_frame047_supported hcells) (Fin.cases (record008_frame048_supported hcells) (Fin.cases (record008_frame049_supported hcells) (Fin.cases (record008_frame050_supported hcells) (Fin.cases (record008_frame051_supported hcells) (Fin.cases (record008_frame052_supported hcells) (Fin.cases (record008_frame053_supported hcells) (Fin.cases (record008_frame054_supported hcells) (Fin.cases (record008_frame055_supported hcells) (Fin.cases (record008_frame056_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record008_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00176
