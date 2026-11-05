module
prelude
public import GraphInputsRow29Part00229Data
public import RawFrameSupport
public import SharedFrameGroups047Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups070Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups105Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0847.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0847.count (({ width := 11, code := 0x670c9d90311621c137eef55dbb9d6fad3d95b055feb6561aa7546a1d2da293fe7cce09a330a5f4ac92b21e3dc5d8b114a1c42d85106a053fb7d4f4de03ad758e5dc637e6f8db9aab4265acad8a3065ecbd1752d2584ae150a9e532a153e27a4e09310b1ec38a67cc89802f2588a511c21c3e8798db1882e45289d12a248460890d01942d8560700cc1482402a0500880f0160280400700a01001001 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0847
    Papers.RationalityTen.SharedFrameCatalogue.group0847_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xe656d2b571a6ed3568934199e0cc0633b01172ab4d5982c995beac85552a7d4d6a294f0a7113749734ae24f92668ff470a35519c8bc45ba2c514489944aa2350b68003d39d00dfc6e136d9a60d0a66b33098b4bd65a92c61618a8653028b14309b04ba25792a092c49124591f48ea472235900c6d430214c896847821c107079036c1770ac84e425610107803a41b60d405d02cc14c09f03801ac0c205c01c00cc05202400a805002200f00580280100070028010004001 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0841.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0841.count (({ width := 11, code := 0x54ca6549a855099e53a26fcd39852b64d4878f51e2344608a714221c3784d0620ac017f4fc1f6be07a2f1de03ae756e9dcc39071ce1dbdb6669acc98f31161ebe1772de5b6b3d5eaa752ca513ea734d29992d24a4828e914a2844685506a0c40a7a0dc1912e0544a413a26a478870ed1c0344668bc1622ac4f89a1262484708b0d41982f05a06e0c81482402a0500880f0160280400700a01001001 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0841
    Papers.RationalityTen.SharedFrameCatalogue.group0841_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xfc8760b911b86dc06a634819b0c9361caf516b0b095742b7d520a7852c293d42a9ce4c2a5912ba91347f23811ac89f433a12d0748083ff1fc4f967b23d71e60ebe7053501890baa5b42d59570a8852428d938493445121810a47be3ca1d60e886d633318b8c185a82ca15e8a5c4fc27a13208e44101e30dd86783221820be059c2a413509404642260fe077039c1b20d305d02cc14c09f03801ac0c205c01c00cc05202400a805002200f00580280100070028010004001 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record000_frame004_links_0000 record000_frame004_links_0064)
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0846.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0846.count (({ width := 11, code := 0x46889910218c2f845076064037f6fc5efbd5794f1ddd3b474ee95cd3886f4db9b5b5b6a6d1da2b39656c918eb0f618c1d7daef5d8b916fad7598ae9572a153ea4945a825009d531a5248690519a2a4448810a2063fe7e4f39e43bc744e41c737e698bf9602904c89391a22c40c790db1a2314608b114e27c4a08f114224418820ca1802b0510700cc1482402a0500880f0160280400700a01001001 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0846.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record000_frame005_links_0000 record000_frame005_links_0064)
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0846
    Papers.RationalityTen.SharedFrameCatalogue.group0846_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
def record000_frame006_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x8cc89186a84984782b81f80b7f27d87a976e73f72a7266fe6f16de6d56b468264c6366306045f55e05d45aa58757a57255d55654f53d53352f52650f4f54c648845243c43640a3fb3e63da3b038035133c3383103032f02e72c62a429728f27a27326c25a25024c2432201f31cf1a818717916816214c1361151070f60f00da0d00cc0c40c00b20ad0a409f07006b06105c03803302902401501401100f00b00a008007005004002001 } : Fields).get c.val)
theorem record000_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record000_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record000) (record000.maps 6)
      (record000.inverseMaps 6) record000_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record000_frame006_links_0000 record000_frame006_links_0064)
theorem record000_frame006_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 6 :=
  of_group record000 6 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record000_frame006_indices record000_frame006_graph record000_frame006_links
def record000_frame007_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0840.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0840.count (({ width := 11, code := 0x46c8990f61742c84306a07c057fcfb5edbcc786f05da3ae744e79c9b866ecda9b43576a0d19a0b33650c858db0f61ac297faf65e6bad70ad8590ad95329a530a1d402764e298d2b2494788e91522343a865072033f87d8f39e43be74ce71cd38c6b8c31662904c09391a22c3fc780d81982f45c0a713e260470870fe1f83c8770b41582784b0660bc1482402a0500880f0160280400700a01001001 } : Fields).get c.val)
theorem record000_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record000_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record000) (record000.maps 7)
      (record000.inverseMaps 7) record000_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record000_frame007_links_0000 record000_frame007_links_0064)
theorem record000_frame007_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 7 :=
  of_group record000 7 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0840
    Papers.RationalityTen.SharedFrameCatalogue.group0840_facts record000_frame007_indices record000_frame007_graph record000_frame007_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (Fin.cases (record000_frame006_supported hcells) (Fin.cases (record000_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
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
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc8e619af0d6aaaeb56e29d54b6a4f509272d2ce95a47da38d1ac89c4321fecf907953ad1bfcd1e6212db96a0a8252728d937892e4332130f1c75e3a21b40cc058e294130893c49024111d088443421810487dc3ea1e90f4074c3781b00d4868432a1920c606142fa1720b805a02a61470a004e0258129091847022810908383fc1da0e606c034812608e042020c0fc07c03801ac0c205c02c015c0aa054026012c08c04401c00cc052024010007c03a01c } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0847.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0847.count (({ width := 11, code := 0x5d8b976ead3583af957aaa551a854b2804f699d30e5f4ab92915e1bc1980efe1f33d275cea5c4b7f6f8db5aa32e650c0d7baf45d2b454ea844de98d2d25349c8c914227430809009f03de780e41b835a688ca99431a60cbe16f2dc590a613925a484889102143fc7a8e91d0374608b61442684087e0ec1d4398720d01942d8560a41442784e09011c220420700cc1482404007c0e81c } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0847
    Papers.RationalityTen.SharedFrameCatalogue.group0847_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0846.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0846.count (({ width := 11, code := 0x3ff7f0fb5ef3cb78cec9d43a5732e1db7b6a6a4d21a2b38654c2d7d2e35b8b4d642b9544a75452835009d1312444808a511a20426814f19d037c6e0d91ad352654c698c3045c4b81632c455ca51432784d49592a2464748c90c2164147a0ed1cc37c6a0d319c324618b91702cc5289d1262383e0780e41c43786d0ca1802b05109a1302504908a110208400700cc1482404007c0e81c } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0846.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record002_frame003_links_0000 record002_frame003_links_0064)
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0846
    Papers.RationalityTen.SharedFrameCatalogue.group0846_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xcbd630afd1724b32591ab15558a9f534289938c9b74aca5012668fc47022d914288c42a9fecf3273d3719b60d0466e33098a8bd058e2c194b4a3250c26a92e492047c235113486e4222060ed474239d1b90ce466c3121888b48540283139098c48a24311a089042a1fa0fc07a437a1a00c786002c41600a8850426411708a84181da0e606c034812608e042020c0fc07c03801ac0c205c02c015c0aa054026012c08c04401c00cc052024010007c03a01c } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record002_frame004_links_0000 record002_frame004_links_0064)
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
def record002_frame005_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x7ef7d47a076b72b7236ee6e06d56b167f63762d5f25e25d45a758655553c52550c4f14bd48543d4333f83e83da3ad37d33d3353002f22e72c32a327225924223622f22822120a2042021f41e31e11d51d41bf1aa19d19418b17d17b17416c16415715614e13812b12211910b1091020fa0f20e50e40dc0cf0cb0c30bf09308e08408307e07c07006b06105c05805705505404c04b04604403803302902402001f01d01c } : Fields).get c.val)
theorem record002_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record002_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record002) (record002.maps 5)
      (record002.inverseMaps 5) record002_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record002_frame005_links_0000 record002_frame005_links_0064)
theorem record002_frame005_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 5 :=
  of_group record002 5 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record002_frame005_indices record002_frame005_graph record002_frame005_links
def record002_frame006_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0840.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0840.count (({ width := 11, code := 0x4037f8fa1ed3c4780eb1d1b9e724e15b5b6669cd1da0b3264cc2d7eae95beb5961ab5536a593f2774e29892aa3d4708890f21941a804f11d13886f4dc1b4360668c91913105d8ba9692d0560a51422764cc9592a2464748c90b212404790ea1c436c680cf18e3005d8b11602a44e8961182143786c0cc194318620b41582784b08e1182204307e0f81e03b0660bc1482404007c0e81c } : Fields).get c.val)
theorem record002_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record002_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record002) (record002.maps 6)
      (record002.inverseMaps 6) record002_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record002_frame006_links_0000 record002_frame006_links_0064)
theorem record002_frame006_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 6 :=
  of_group record002 6 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0840
    Papers.RationalityTen.SharedFrameCatalogue.group0840_facts record002_frame006_indices record002_frame006_graph record002_frame006_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (Fin.cases (record002_frame005_supported hcells) (Fin.cases (record002_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
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
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x3b15cfae2b6f034b5a34d0365fb2198f8c4160c2f196f6ac855aaa794b4a2150ba77135c97d4ac244d21890647ba370ffc71f38618fcbf45b42ca961ca8a52c28a14289a647823191088644201ef0f447163451930c605ac2bd1528a6c4c82090fa074c3861b10b7858829012a08f04382140f607482cc11c06b03101840bc05c02b81540a804b02200e806c03301900a404801f00e807002800f005002000e0050020008002000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x731b8e9b46d7a6ae34dda6ad0c67eb3d59decc1632300d71eb4f597ab6955caa4546a9a94469e34e1a5b9284938490a3f91c28d146523011648a244ca25111c85b3a01bf8dc26db32e192cc725eb2d49630b0c50727b13909744af254125892248b23e91d48d244a21a107c80c3c81d98da86002f114c8a344e826512e092046421c107078436c1aa0c886082f21650a784e42560fe07803a41c80dc06a02e814c07303901ac0c806302e010c07003301880a4048022008803c01600a0038014008001 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3905bb2cfa64730d9788b9e5a92ba9516a5d51ca8453969674ad23451808ad43220f905880b3f59f20f2875a3811a40cd461e2db155ca5250526e925c8664261ce8e306f23301850be05ae2b714a098049e24812088e844221a10c08243fa1ef0f107803b01d20de06d83541a30cd863430a17d0b905bc2d21530a3850027012c094848c23811408483ec1da0e607203701a408e042020c0f607303901ac0c205c02d01600ae054026012c08603b01d00cc052024011008003e01c } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xc4f5efad39646aac545a9a13c49b74a0247d1f88c245b22310aa7ec3c39d38de66d834919b8c9c62a2fc9678b0653d28c93e49aa4c024812088d441a1dc8e486ae2ee1628a304d225812588f045820d0f887903521860ba85a02b214909504382020f604a023810607d03e01ac0b805702a815009804b0228110072033015009004201f00e807002e01600a004802000f00700280100070020008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xe20706b621aeccef66eb1d98a2bb55d1ae31626b015752ad5546a9a53ca98d49aa344fc27892f49684a6a50525c910463a2d513488e43da17506882e4029d7ce9673535a9a84d1665632218f0c4a6112ff97a4b765a82aa951ca5e52728c94089904ba251126891847522a11407da30d17e8bb84d825c12688183e41e00c605e829013c08b842c1fe0da05982bc13e09504702340d606902e015c0a8033018809003e01c00a805001e00d005002000e0060028010002000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb17b11aeaae1aabaa2a059f89bc9b09a396495994c8fe8d68be8b28a989d89487886982080d7f07e17d07ae77376474973c7287056af69f69165964e63e6025f65e659757055c55454f54753f52751a4de4d04b64ad49f48645644842f4264163fa3b23a53792d82cc2be2482382281c21ba1ae17116313712b0fd0f30e80bf0a109f09708f08808706906705a05505203303102401f01c01501400f00d00a008007006005004001000 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xf937b83b01d56dee6eab30d926bcf5dcae85612af656fa961448a0a4f9a78139c9b94c4a5d92208fe47023551848a242b21190528204071fc0f427923af9a6cd0a66d2ea9708b56524278135897e4ac24d12148aa4421ee0f287583a11c70db864431217a8bb05b42bc13689784721e40ee875c33c1970c885802b215209a04b423411307e83dc1e00da05982bc13e09504702340d606902e015c0a8033018809003e01c00a805001e00d005002000e0060028010002000 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record009_frame003_links_0000 record009_frame003_links_0064)
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
def record009_frame004_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x6f8dedb776c6bbd6d9df3362ac45866efdd7b9d69eca58cb035deb7562a894e6865039e73b6724d495728648c8a9031c22744986efe5f8be8760ea1cfb786cad75a934867eccd8ab0a5b8b49612bb564a853ba6e4bc96127a3f43e868ff1af350688b295e2b04d49792b2204287d0f21b634c658b414627c4c091114224348670b4154290330620900f81c02a0500780d0140200380600a01000800 } : Fields).get c.val)
theorem record009_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record009_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record009) (record009.maps 4)
      (record009.inverseMaps 4) record009_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record009_frame004_links_0000 record009_frame004_links_0064)
theorem record009_frame004_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 4 :=
  of_group record009 4 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record009_frame004_indices record009_frame004_graph record009_frame004_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (Fin.cases (record009_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xd6269fb455696b3856eab19530a864efa7312e295a49624691ae8c245b22bd14c89a4499bf0dd26963419964c925a72ca1504a5c50427a12c093849024492008ec47020d0e9865427912588f045a20d10007c832c1680ac852825411d08782c813c09704a825012008c03d01c80d206302d015c0ac05502a0108074031015808803e01e00e807002e01600a004001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
def record010_frame002_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x86e85082c73d7306fc6ef6d06c564a63b6025f35cf5c257c56455554c54253452c4504414083f93d53c834f34230e3012e22d729928127226925f2512492272051dd19818017917116115b15312610e1070ff0ef0e90e10ac09e09709509409008c07a07206906305a05705605505404203a03102b02201f01e01d01c01701601401000d00a009008007004003002001000 } : Fields).get c.val)
theorem record010_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record010_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record010) (record010.maps 2)
      (record010.inverseMaps 2) record010_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record010_frame002_links_0000 record010_frame002_links_0064)
theorem record010_frame002_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 2 :=
  of_group record010 2 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record010_frame002_indices record010_frame002_graph record010_frame002_links
def record010_frame003_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0651.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0651.count (({ width := 9, code := 0x14da3d064d258fc7a351885c2a07027ebede8f177bb1d6e973b4da4cb6531586b459ab558a85327d389a4ba59289246a1d0276399c4dc6d359a4c6602f16cb4582b12c8e43211047c3b1c8d86230158a8522813894441d0e05c2c150a04c2210078301208038180a04018080200 } : Fields).get c.val)
theorem record010_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0651.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record010_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (smallEmbedding record010) (record010.maps 3)
      (record010.inverseMaps 3) record010_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record010_frame003_links_0000 record010_frame003_links_0064)
theorem record010_frame003_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 3 :=
  of_group record010 3 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0651
    Papers.RationalityTen.SharedFrameCatalogue.group0651_facts record010_frame003_indices record010_frame003_graph record010_frame003_links
def record010_frame004_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0647.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0647.count (({ width := 9, code := 0x1118641decf5783bdd6e96fb79b0d76934194c76330d84c05fac962ab5529546994c24d248e4621906823f9f8f87b3b9c8da6430980ba5c2d164a85128134984a249007e3d1e0ec70351a0cc5c2d1409c4c251208c441d0e05c2c150a04c2210078301208038180a04018080200 } : Fields).get c.val)
theorem record010_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0647.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0647.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0647.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record010_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0647.localPairCheck (smallEmbedding record010) (record010.maps 4)
      (record010.inverseMaps 4) record010_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record010_frame004_links_0000 record010_frame004_links_0064)
theorem record010_frame004_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 4 :=
  of_group record010 4 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0647
    Papers.RationalityTen.SharedFrameCatalogue.group0647_facts record010_frame004_indices record010_frame004_graph record010_frame004_links
def record010_frame005_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xd0265731155b2ac753ca99d48ea414d1a63927c929484a40d13685c420a0c50388013f89a50d026333101804bfa5772b29488a204f6279127c8de45d228910085c4221e78df063828c12d093447c22010988103461760b6058028a13b09782c813c09704a825012008c03d01c80d206302d015c0ac05502a0108074031015808803e01e00e807002e01600a004001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record010_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record010_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 5)
      (record010.inverseMaps 5) record010_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record010_frame005_links_0000 record010_frame005_links_0064)
theorem record010_frame005_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 5 :=
  of_group record010 5 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record010_frame005_indices record010_frame005_graph record010_frame005_links
def record010_frame006_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0625.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0625.count (({ width := 9, code := 0x190c4dfec35fabd5aa550a15067336994c249208ec6a2f15893e5f0ef76ba5ced86ab399ac8632f572b65a2c15cac532752a843f9f8f6783b1ccd06331180b85a2c1248e44219087e3b1c8dc602f160ac5429140984a221006430170b0542411078301208038180a04018080200 } : Fields).get c.val)
theorem record010_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0625.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0625.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0625.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record010_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0625.localPairCheck (smallEmbedding record010) (record010.maps 6)
      (record010.inverseMaps 6) record010_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record010_frame006_links_0000 record010_frame006_links_0064)
theorem record010_frame006_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 6 :=
  of_group record010 6 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0625
    Papers.RationalityTen.SharedFrameCatalogue.group0625_facts record010_frame006_indices record010_frame006_graph record010_frame006_links
def record010_frame007_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0622.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0622.count (({ width := 8, code := 0x8a87867e7d7b7a797872716f6e6d6c6a6867666564635c5b59585756504f4d4c4b4a48464544434241403e3c39373635343332302e2d2c2b2a2928272524232221201f1e1d1c1b1a191817161514131211100f0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record010_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0622.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0622.localPairCheck (smallEmbedding record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0622.localPairCheck (smallEmbedding record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record010_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0622.localPairCheck (smallEmbedding record010) (record010.maps 7)
      (record010.inverseMaps 7) record010_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record010_frame007_links_0000 record010_frame007_links_0064)
theorem record010_frame007_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 7 :=
  of_group record010 7 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0622
    Papers.RationalityTen.SharedFrameCatalogue.group0622_facts record010_frame007_indices record010_frame007_graph record010_frame007_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (Fin.cases (record010_frame002_supported hcells) (Fin.cases (record010_frame003_supported hcells) (Fin.cases (record010_frame004_supported hcells) (Fin.cases (record010_frame005_supported hcells) (Fin.cases (record010_frame006_supported hcells) (Fin.cases (record010_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0xb4d606b14fc9a72d64147d8c917a264457fefe1efbd9792ee9d7b776e0d31a132b640c01712dd578ad54da714b092120a3644886d009ec3c670cdc9a72de558a69462644a4901011f83c4760e71c236c6a8d01962244187b0e01a83105d0a81442804f09c10c2103a0620b41582a04c0880f81e03a0700b8160280400680a0120200380400600800800 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x6593125832ac7533a90534698e49f24a5212903420a0c50027f13db9dace6c69134098c0c406022fe96f8ae056528d94409e44a423991748a2444217108879e3901be0cc0638303146096849a23e110084c4081b40d186002ec16c0b0053c28a13b097827812a08c03d01c80d206302d015c0ac05502a010c08403a01880b405602a013008803e01e00e807002e01600a004001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record011_frame002_links_0000 record011_frame002_links_0064)
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1922c46603ac115e2a8b53b292946a9804b6a4391f88d145f1fecfd27b73d39d74e246d32e816f4aae54228b14048984391ed0f2073a38a1638ad4506273127091c480239111086c41e1f80f886cc35819e0cb86443141820bd85d42dc14a0a184d425c128090846422410c082825411807b03d01c80d206302d015c0ac05502a010c08403a01880ac04401f00f007403801800b805802a014008804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
def record012_frame002_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x197ec7861d2d21670ada5632a6950c9dc4e625b92b492e48d22d915e89a449a16101c7d837c9ba4d2668332e1924b4859429f14b8a0e4f424812248ec47022210b88344031dd0e986fe33f1950a244f225a12588f045a21c10688003e41a60cb05dc2d01590a504e425411d087825411807b03d01c80d206302d015c0ac05502a010c08403a01880ac04401f00f007403801800b805802a014008804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record012_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record012_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 2)
      (record012.inverseMaps 2) record012_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record012_frame002_links_0000 record012_frame002_links_0064)
theorem record012_frame002_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 2 :=
  of_group record012 2 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record012_frame002_indices record012_frame002_graph record012_frame002_links
def record012_frame003_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x7f17de7c473a7306f96ef6d16c564763b5ff5f35d05c255554c53452c50e4fb4e144d4414053f93d63c834c34230b3012e32d727226925124923522e22722020b2051fa1e41dd1a019818718017917116816115b15312e12611510e1070ff0f60ef0e90e109508c07b07a07206906305a05705605505404304203a03102b02201f01e01d01c01801701601501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record012_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record012_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record012) (record012.maps 3)
      (record012.inverseMaps 3) record012_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record012_frame003_links_0000 record012_frame003_links_0064)
theorem record012_frame003_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 3 :=
  of_group record012 3 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record012_frame003_indices record012_frame003_graph record012_frame003_links
def record012_frame004_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x9f79e59d396095591f9128f08e386e85f81e80b7dd7cc7137006c86b569067c6695fe5f25be5b058a57d5215144dc4ce4a949b4043f53c73b839538a37f37935034332d3032f327426624823822821a2081f91e91db19f19017216415614613612a11c10b08f08607907807006706105805505405305204304203a03102b02201f01e01d01c01801701601501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record012_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record012_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record012) (record012.maps 4)
      (record012.inverseMaps 4) record012_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record012_frame004_links_0000 record012_frame004_links_0064)
theorem record012_frame004_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 4 :=
  of_group record012 4 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record012_frame004_indices record012_frame004_graph record012_frame004_links
def record012_frame005_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x17bcba85c1ab5958ea76533a9214829a04c724ed25290a481a1050628013f89edced67363489a04c6062030117f4ae856528f94409ee4f222e914485c4221fb0f8879e3be1c60df06bc32c18e0a8851826712d093447c22d110084c4081b60d186082ec16c0b0054428a13b097825411807b03d01c80d206302d015c0ac05502a010c08403a01880ac04401f00f007403801800b805802a014008804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record012_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record012_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 5)
      (record012.inverseMaps 5) record012_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record012_frame005_links_0000 record012_frame005_links_0064)
theorem record012_frame005_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 5 :=
  of_group record012 5 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record012_frame005_indices record012_frame005_graph record012_frame005_links
def record012_frame006_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x6bb69b68462261c5e95e25cc5c657456e53e53752051a4ba4b249448a46b44c4343d03c939639037c3763203192ea2e42d02ca26425a24123922421d21720f1f41ec1de1c31bb18918217416c16415b15114914113811d11810b1050ff0f90f10eb0e50df09508c07b07a07206906305a05705605505404304203a03102b02201f01e01d01c01801701601501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record012_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record012_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record012) (record012.maps 6)
      (record012.inverseMaps 6) record012_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record012_frame006_links_0000 record012_frame006_links_0064)
theorem record012_frame006_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 6 :=
  of_group record012 6 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record012_frame006_indices record012_frame006_graph record012_frame006_links
def record012_frame007_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1074.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1074.count (({ width := 10, code := 0xe2383dfb53d4741d0336ccf0ec32f5bcee7b8eada9e99a4a839fa799324a8ce31896217fdfe7a5e7775da6a9a364d8d6017e5ed7659d635714d52524481174450d421003ecf73c8d4340c7308be2e4b02a8a62846f1a05f178571404d1204511043108390e0330b8290881f0781d0701805c1605414044100340a0240801c0400c0200400 } : Fields).get c.val)
theorem record012_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1074.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record012_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (smallEmbedding record012) (record012.maps 7)
      (record012.inverseMaps 7) record012_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record012_frame007_links_0000 record012_frame007_links_0064)
theorem record012_frame007_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 7 :=
  of_group record012 7 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1074
    Papers.RationalityTen.SharedFrameCatalogue.group1074_facts record012_frame007_indices record012_frame007_graph record012_frame007_links
def record012_frame008_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x2fc5ecbc96b2d3588b035beb652ba433ea794d99a71ae2e43985504e02bfa77aed5cc3906f8de1a1b3b63cc6583302568aa948a874ea9b531a5b48c8f116a1742071cde1aa33e664c71812f65c8b393925c464889091fe3d4768e51b62143f0710e01a83185d0ac14c290510a0104200380620ac1101f03c0740e01802e0580a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record012_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record012) (record012.maps 8) (record012.inverseMaps 8) record012_frame008_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record012) (record012.maps 8) (record012.inverseMaps 8) record012_frame008_indices (Fin.ofNat record012.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record012_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record012) (record012.maps 8)
      (record012.inverseMaps 8) record012_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record012_frame008_links_0000 record012_frame008_links_0064)
theorem record012_frame008_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 8 :=
  of_group record012 8 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record012_frame008_indices record012_frame008_graph record012_frame008_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (Fin.cases (record012_frame002_supported hcells) (Fin.cases (record012_frame003_supported hcells) (Fin.cases (record012_frame004_supported hcells) (Fin.cases (record012_frame005_supported hcells) (Fin.cases (record012_frame006_supported hcells) (Fin.cases (record012_frame007_supported hcells) (Fin.cases (record012_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xe4a718b72da64cb1653326191ac815d9ae79622afc5642add566aa454ea92d2fa9654a7a4ed25891b46522c913888843ca1a109a83d41ba0bceba7463599a70cd265832a1914c7e5fc2ac1510a6252128b94289964b7252125091447d233916c8ae4512018e4c65e2fd1770b7451c25c12688f044621c10a878036a1a00b504f02480ff073834813c09403e01c80c205c02d015c0aa04401d00a404802200f807402e01600a003c01c00d00500240100050020008002000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1c94e3164c3241902bb35cf2c455f8ac855baacd548a9d525a59529e92c48da2c913887943420f506e82f4019eb0eac7463811ab0d386753331960ca264531f97f0a88531291945ca144b7252125891447d233116c8ae4512018eac72633c1978c2c5fa2ee16e8a6c51c26a12e0934478232111887042a1e00da86802d413c09203fc1ce0d203e01c80c205c02d015c0aa046022010c07803a01c80a404802200f807402e01600a003c01c00d00500240100050020008002000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x12263543e85b05602bdd7acecdd4ba5732db5b0b54684c8d8fb1261ac057eae45c2b755dab353ea2d352604b89390ca1040c7ecfb9f13b6738e31b4336660ca1722d8548a113926846c851072043d4798f11c03706b0cf1903105c8ad140260490820f61b43606b0c81582905009c12c2483e0700dc1b0290480881001f03a0580780e01a0280480800800800800 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record016_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229
