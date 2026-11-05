module
prelude
public import GraphInputsRow31Part00024Data
public import RawFrameSupport
public import SharedFrameGroups059Checked
public import SharedFrameGroups060Checked
public import SharedFrameGroups061Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00024
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1061811bffddf6eb872838d5c1cda06abb449a02ce2652ae3d6f8b6a5a4acd162ea7451a28953be9be4cea60d17c8ac44d223d0e084c418209101e7f93e29edcf2877132d9920c6c615300178ca8050027892ac9144692278e286f03661ad8cf06302fc1780b6c58a29114189804561f30eb07403761ad0d3065831e1750b304f425c12108904301de0db054826412e08d03d01b00d406002d81680ae05602a0108068032014008c04401f00f0070028013008003801a00b005002400e0040018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x7597487417107076bf6ba6ab5ee5e95e55e05d65cd5c45ba5b055552e5244da4be4b049348d47f4784654574464254144083cd3c83c33bd3b43ac39b38f38d3633503483373293233082fb2ed2e22d82cb2b82b42a92a529d2952832772712672261fc1f41c41aa19918b18716f16415f15214613a12f11d1110eb0d70c50a908107006906406305905705305205004b04a04003703203103002f02d02502301f01e01c01401301000e00d00a009008007005004003001000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x755b9f5cbadeb6deb675ae4d6b6b2b54daa4d44693b465a14d0467eb3d59dcbc45da2e996f0b6e5a5aac1510a785332961490a3a50628093be94448e24311f48f0474a3851b68d346623191788b745822891328924459dc0ec07503911c6cdf867232598e4c5061b30597ecb9a5c62d394749ec4e426993249844ba25a12b494c4a024b124491447d23a91bc8d23191778b6858e29913d09ac47822d10706d832e1880ac85282560f007483881b60d405f02a80e006b03501a40c205c02d816807003301900c4052024011808802800f007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record002_frame001_links_0000 (interval_append _ 64 128 140 record002_frame001_links_0064 record002_frame001_links_0128))
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x697b469a18cdf661b2c1936c94646b1bd8dcc54611b0257e0be95e9aee9748b0b5812bf15bcad655ea97d46ca2150728093ee9f04e7a71935292c48023a91a88ca45ca28512c87e43921a90888374111fdcfb27c33d61c7ce267093759b90d9466032018bcc3c61430417f8bc85df2e41594a885362941484a204fc27913789a64ce256129492e47422e113487a36219e0ca462e2e31610ae050226f12487803861b90c305d82a20ff07903941ac0c705902980e006b03501a40c205c02d816807003301900c4052024011808802800f007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record002_frame002_links_0000 (interval_append _ 64 128 140 record002_frame002_links_0064 record002_frame002_links_0128))
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x82f81a80d7ea7d87cd7bc7b97b67a97a879d78877d77276e7677607596f26ed6e96d26cd6bb67165364b63f63863362e6176136025b659859058557d57756e56956055b55654c54754053252852151b4a049649047647245e40f3f13e63db3d33cc3c33a93a639634232431930e3083022f92f42eb2e62e12d72d22cb2be2b52af2aa2041e91de1d41bc1ae1a818f18617013c12e12810d1070f00c90c30c00bd0b70ab0a107006b06a06906105c05b05a03803303203102902402302201400f00e00d00b00a009008007005004003002001 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record002_frame003_links_0000 (interval_append _ 64 128 140 record002_frame003_links_0064 record002_frame003_links_0128))
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb20b06afaad6ac7ab7a90a89a85a75a69a5aa3ba35a31a20a14a039c19a399496f96095194293692d91d9108fa8a888687684b8378247f77d47c079678176e7407297126fc6db6d46cf6c16b36a268567e67a66d66064e6135fe5f35d75cb5bc5af5a759e58e58056d52750e5014e14d34c449b48247745944a43d41b40d3fc3ee3e43d73cb3bb3ac39536a35734d34033131f30b2fa2ea2d82c62b62ad2a02932862742652552462232132011f01e11d41cd1c31b51a819718717816b0bf05d05c05b05a05805705605502502402302202001f01e01d01b01a01801501000f00e00d00b00a009008005004003002001000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame001_links_0000 (interval_append _ 64 128 161 record003_frame001_links_0064 record003_frame001_links_0128))
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc0f5faafb9796bb45cf2dc56d2b655a8ad09652b0857fabed5caad455da9fd4d0a6051d2891422a004faa7bd3ae9c44d3a56526c92c480a3a91a889e43da1c509283440f9fc8fb87c63d79e00ee876d3ae9d3ce7271d3889c20de66e23641a20cd666132218c8c4261130297f4bd85dd2e31628adc5652a294d8a504f926d93489624a224a11bc8be45022010bc8404181ff8fb87a43ac1cd0e306f436c1b10d4467a32918b8c145e62e31690b085702a714a0a044de24711a088841c1fc0f687803a01c30dc86a83301860bb03240ba05c02d81680b005702b015404a024011808804001f00f007403601a00c005402000f007003401600a004802000a0040018008002000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame002_links_0000 (interval_append _ 64 128 161 record003_frame002_links_0064 record003_frame002_links_0128))
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x34dd1f44cdb31cb32aca728c931fc5b0cc2f0ac1f03bf2edb9ee4b66d5b46cfb3acdb26c4aeea6a7a9aa26829ee739ba6b972549323d8e2338c22f8ba2d8aa2687e1785a1584a0e81dfb7ddf57ade6785dd771db761d4735c06f1ba6b1a66819764d915fd785c5645855e5695855d565454c50d374cd304b1294991e45d1142d05409003f4fb3e4f23ace6384d4340cc324c4300bd2e4b62ccac2949f2645d0f83d0f03b0e4380dc36088210801f0741c06c1a06017058150400f0380d02c0a024080140400c0200400 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame003_links_0000 (interval_append _ 64 128 161 record003_frame003_links_0064 record003_frame003_links_0128))
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
def record003_frame004_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xbbf5d02e356d8b595a7ac5960aafa572ab69594ab3550aa5d502a7753328854049f14e9270536a9a64ca26252dc9634a6a3fd1b68c7452224110a846410203cfd87db3e91ea4f2077d3b59ca0e2c70a3779b8cd9a6b33521a60cfe67332f9874bfe5ef2e91708b6c5a92cd1638aea5692aa14489e84e726492f0964481232115c87842f213101c7ea3e71ed8f1c76a3a91c68e046da34f19c8c9062830617b8b9c5b22ca15f8ac053828a13b89b44c025112388e84622110ff87c83ca1d50e286d434e19c0c806102f216d0b203200ba05c02d81680b005702b015404a024011808804001f00f007403601a00c005402000f007003401600a004802000a0040018008002000 } : Fields).get c.val)
theorem record003_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 4)
      (record003.inverseMaps 4) record003_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame004_links_0000 (interval_append _ 64 128 161 record003_frame004_links_0064 record003_frame004_links_0128))
theorem record003_frame004_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 4 :=
  of_group record003 4 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record003_frame004_indices record003_frame004_graph record003_frame004_links
def record003_frame005_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x4338570a20fc1c831026034037f8fe5f93ea7ccf8deebda7aaf1ddf3ba762eb5d4ba6746e81ccb9671ede1b4b646acd45a6b3c65ec9d8f316624bfd7d2f15d0b61692cd58ab015cab3560ab1542a453ea3d41a7d4e69b534a674c89812da574a28f51822a4408690ba063f47d0f59e53c4748e79c93866e4d91ad346678cb18f30e5fcba96d2ca57cab94f296524a013d2684c4949242424648a9082063f07a8ee1cc3846c8d419a324620bd1741c82384608a110210410800fc1102104007c0e81c0360680c01702a04c0800f01c0340580a0120200280400600800800 } : Fields).get c.val)
theorem record003_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record003) (record003.maps 5)
      (record003.inverseMaps 5) record003_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame005_links_0000 (interval_append _ 64 128 161 record003_frame005_links_0064 record003_frame005_links_0128))
theorem record003_frame005_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 5 :=
  of_group record003 5 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record003_frame005_indices record003_frame005_graph record003_frame005_links
def record003_frame006_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0699.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0699.count (({ width := 8, code := 0xe9e7e6e4e3e2e1e0dfdedddcdbdad9d8d7d6d3d1d0cecdcccbcac9c8c7c6c0bcbab6b4b2afadacaaa9a8a6a5a4a3a2a1a09f9e9d9c9b9a9998979492918f8e8d8c8b8a898887817d7b777573706e6d6b6a6967666564636261605f5e5c5a59575655535251504e4c4b49484745444342403f3e3d3b39383635343231302f29272625242221201f1d1c1b1a18171615141312110f0e0d0c0a090807050403020100 } : Fields).get c.val)
theorem record003_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0699.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0699.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0699.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0699.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0699.localPairCheck (smallEmbedding record003) (record003.maps 6)
      (record003.inverseMaps 6) record003_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame006_links_0000 (interval_append _ 64 128 161 record003_frame006_links_0064 record003_frame006_links_0128))
theorem record003_frame006_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 6 :=
  of_group record003 6 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0699
    Papers.RationalityTen.SharedFrameCatalogue.group0699_facts record003_frame006_indices record003_frame006_graph record003_frame006_links
def record003_frame007_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0962.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0962.count (({ width := 10, code := 0x2bbad2b1aaaa7a9296a5693a3a8ca1a7f9ee789ca6f9aa5e9625593e4c92647916438fe3d8e62a88e208661684e0a812007f1f87d9ee7b1ea7a1dd769d7749cf729c670dbf6edb76c9a868da16719a66196651926398c6217c5dd745c16d5ad61569565454d52d4550d414fd394cd2e495204611142d053fcf93d0f03a8e5388e036cd9348d0328c7314bf2f4b82d4b12b4a8290a22709a254922408b2246511043108410fc3e0f43c088210801f0741c06c1a06017054130400f0380d02c0a024080140400c0200400 } : Fields).get c.val)
theorem record003_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record003) (record003.maps 7)
      (record003.inverseMaps 7) record003_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame007_links_0000 (interval_append _ 64 128 161 record003_frame007_links_0064 record003_frame007_links_0128))
theorem record003_frame007_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 7 :=
  of_group record003 7 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0962
    Papers.RationalityTen.SharedFrameCatalogue.group0962_facts record003_frame007_indices record003_frame007_graph record003_frame007_links
def record003_frame008_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0731.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0731.count (({ width := 8, code := 0xd0cecdcbcac9c8c7c6c5c4c3c2c1c0bfbebdbab8b7b5b4b3b2b1b0afaeadaaa8a7a5a4a3a09e9d9b9a9997969594939291908f8e8d8c8b8a8988858382807f7e7d7c7b7a7978757372706f6e6b69686665646261605f5e5d5c5b5a595755545251504e4d4c4b494746444342403f3e3d3b3a393836343331302f2d2c2b2a29272625242221201f1d1c1b1a18171615141312110f0e0d0c0a090807050403020100 } : Fields).get c.val)
theorem record003_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0731.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0731.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0731.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0731.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0731.localPairCheck (smallEmbedding record003) (record003.maps 8)
      (record003.inverseMaps 8) record003_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame008_links_0000 (interval_append _ 64 128 161 record003_frame008_links_0064 record003_frame008_links_0128))
theorem record003_frame008_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 8 :=
  of_group record003 8 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0731
    Papers.RationalityTen.SharedFrameCatalogue.group0731_facts record003_frame008_indices record003_frame008_graph record003_frame008_links
def record003_frame009_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0714.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0714.count (({ width := 9, code := 0x1a3cfe773598cbe572993c9647218fc7637198bc560ef577b8dbadb69b459ecd65b257eb155a85369945a04fa75389bcce632f96cb255299449e4d2491486411f8f45a1f0c8340e02fe7e3edf4f97c3c1d0e56fb71b6d467b3592c7633057cbb5c2d966b157ab558a751a8938994b2491e8c45a1906823f1f0f4773a9cce46c34998c6602f174b65a2c95cac552a10c6c351a0cc6230178b83e1e0e87034190c05c2c15098481e0e0683014090401c0a04018080200 } : Fields).get c.val)
theorem record003_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0714.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0714.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0714.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0714.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0714.localPairCheck (smallEmbedding record003) (record003.maps 9)
      (record003.inverseMaps 9) record003_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame009_links_0000 (interval_append _ 64 128 161 record003_frame009_links_0064 record003_frame009_links_0128))
theorem record003_frame009_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 9 :=
  of_group record003 9 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0714
    Papers.RationalityTen.SharedFrameCatalogue.group0714_facts record003_frame009_indices record003_frame009_graph record003_frame009_links
def record003_frame010_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd736a1b4ad9f8ce4666b16188ac35604afd5794b8c5bcad9d682b2c5822a814eea6251da89d4269ff4f7a7713709a44c024791f48e7460a2b513486442120c101a7fb3f49f18f6a7a53c99c90e2270136a9b04d2c65832298ccc1a5f82e815b0a8652e28393cc9be4cb25d92a09084702260fa878c3b31c68de46cc3301870bf05b22c715a8a4850227112f894c49824511b88c044420e10388043f21f30f607903bc1d70e807203821bb0d986b434c19e0cc064431417a0b985b02ca15f0ac054829414409e84d425e12809083540ba05c02d81680b005702b015404a024011808804001f00f007403601a00c005402000f007003401600a004802000a0040018008002000 } : Fields).get c.val)
theorem record003_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 10)
      (record003.inverseMaps 10) record003_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame010_links_0000 (interval_append _ 64 128 161 record003_frame010_links_0064 record003_frame010_links_0128))
theorem record003_frame010_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 10 :=
  of_group record003 10 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame010_indices record003_frame010_graph record003_frame010_links
def record003_frame011_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6e06d56cf6b76aa69e68067a67666a66264f63c63963562761e60a5e45d35ce5ba5af5a259859358d57f57456253d52a5255105054f84df4ce4c94b24a749a48347946d46244544143c4304274184023ff3fb3ed3e33d23a839b39438037236835e35935334533932a3012f22eb2d62c82bf2a229428f27826a25f24923c23222821f2172122071ff1f01e01d81d01c71bf1b91b51af1a81a019718f18817e17717016b16615f15714814013713012c12712211b11611010c1081010f90b405b05a05905805605505405302502402302202001f01e01d01b01a01801501000f00e00d00b00a009008005004003002001000 } : Fields).get c.val)
theorem record003_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record003) (record003.maps 11) (record003.inverseMaps 11) record003_frame011_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record003) (record003.maps 11) (record003.inverseMaps 11) record003_frame011_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record003) (record003.maps 11) (record003.inverseMaps 11) record003_frame011_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record003) (record003.maps 11)
      (record003.inverseMaps 11) record003_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame011_links_0000 (interval_append _ 64 128 161 record003_frame011_links_0064 record003_frame011_links_0128))
theorem record003_frame011_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 11 :=
  of_group record003 11 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record003_frame011_indices record003_frame011_graph record003_frame011_links
def record003_frame012_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0758.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0758.count (({ width := 9, code := 0x1369a4ce612f974b6592b94c9e49219047e3d1d8dc5a291387c36170a84c220d0480be5eaf375ba1cae27037db4d86b349a2d067b399acc653218ac260b017ebe5e2dd6ab4582b958ab552a54ea5512692c94462250c8340a00f6793b9cce471381bcdc6d361acd46833194c6623097cbc5d2e168b0572a950a6512813c9c4c259289247229108441200f87a3c1d8c854291409c4a24118883a1c0d86830170b0542813090441e0e0683014090401c0a04018080200 } : Fields).get c.val)
theorem record003_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0758.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record003) (record003.maps 12) (record003.inverseMaps 12) record003_frame012_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record003) (record003.maps 12) (record003.inverseMaps 12) record003_frame012_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record003) (record003.maps 12) (record003.inverseMaps 12) record003_frame012_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record003) (record003.maps 12)
      (record003.inverseMaps 12) record003_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame012_links_0000 (interval_append _ 64 128 161 record003_frame012_links_0064 record003_frame012_links_0128))
theorem record003_frame012_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 12 :=
  of_group record003 12 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0758
    Papers.RationalityTen.SharedFrameCatalogue.group0758_facts record003_frame012_indices record003_frame012_graph record003_frame012_links
def record003_frame013_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x6b26a169868767e67865664e6466376316236126096035f65f05e25c45b25a859258657d57756e56655654f53f5134fd4f34d94cc4c34aa49949247f47546e45944f44643b41a41140b3fd3f53e73d63cd3c73ba3b43a638837336735434a34133b33132a31a3123032d72bd2b029a29028726e25924f24023923221d2132071fe1f71ef1ea1db1d61cb1c01ba1b41ad1a619e19518e18617f17c17817216a16515d15414f14714013813312e12712211d11a11310d1070ff0f90f30ed0b305c05b05a05905705605505402502402302202001f01e01d01b01a01801501000f00e00d00b00a009008005004003002001000 } : Fields).get c.val)
theorem record003_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record003) (record003.maps 13) (record003.inverseMaps 13) record003_frame013_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record003) (record003.maps 13) (record003.inverseMaps 13) record003_frame013_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record003) (record003.maps 13) (record003.inverseMaps 13) record003_frame013_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record003) (record003.maps 13)
      (record003.inverseMaps 13) record003_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame013_links_0000 (interval_append _ 64 128 161 record003_frame013_links_0064 record003_frame013_links_0128))
theorem record003_frame013_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 13 :=
  of_group record003 13 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record003_frame013_indices record003_frame013_graph record003_frame013_links
def record003_frame014_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0961.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0961.count (({ width := 9, code := 0x1a2d067f399bcce47218fc5e2b0d82c0e02fb7cbcdd6e772b7dbad96ab4da2cd65b1d76b357a9d469f4ca4d1e8b43a14fe7d3d9e4d6693397cba552692c9243208ec662f1689c4a210e86c32150983c05fafb7bbd5e6f076badd2e77338dc4e170375b2d668b3994c6612fd76b85aac95eac552a14aa34f271309549a3d1a8b44a1906813f1f0f076399c0dc6b349587c3d1e0ec72381b8d844211007c3a1c0d86830170a84c200f07034160a048200a04018080200 } : Fields).get c.val)
theorem record003_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0961.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0961.localPairCheck (smallEmbedding record003) (record003.maps 14) (record003.inverseMaps 14) record003_frame014_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0961.localPairCheck (smallEmbedding record003) (record003.maps 14) (record003.inverseMaps 14) record003_frame014_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0961.localPairCheck (smallEmbedding record003) (record003.maps 14) (record003.inverseMaps 14) record003_frame014_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0961.localPairCheck (smallEmbedding record003) (record003.maps 14)
      (record003.inverseMaps 14) record003_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame014_links_0000 (interval_append _ 64 128 161 record003_frame014_links_0064 record003_frame014_links_0128))
theorem record003_frame014_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 14 :=
  of_group record003 14 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0961
    Papers.RationalityTen.SharedFrameCatalogue.group0961_facts record003_frame014_indices record003_frame014_graph record003_frame014_links
def record003_frame015_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0730.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0730.count (({ width := 8, code := 0xa09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0730.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0730.localPairCheck (smallEmbedding record003) (record003.maps 15) (record003.inverseMaps 15) record003_frame015_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0730.localPairCheck (smallEmbedding record003) (record003.maps 15) (record003.inverseMaps 15) record003_frame015_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0730.localPairCheck (smallEmbedding record003) (record003.maps 15) (record003.inverseMaps 15) record003_frame015_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0730.localPairCheck (smallEmbedding record003) (record003.maps 15)
      (record003.inverseMaps 15) record003_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame015_links_0000 (interval_append _ 64 128 161 record003_frame015_links_0064 record003_frame015_links_0128))
theorem record003_frame015_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 15 :=
  of_group record003 15 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0730
    Papers.RationalityTen.SharedFrameCatalogue.group0730_facts record003_frame015_indices record003_frame015_graph record003_frame015_links
def record003_frame016_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0713.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0713.count (({ width := 8, code := 0xefeeedecebeae9e8e7e6e5e4e3e2e1e0dfdedbd8d7d5d4d3d1d0cfcecdccc9c5c3c0bebdb9b7b6b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a29f9c9b9998979594939291908d89878482817d7b7a7877767574737271706f6e6d6c6a686765646361605f5e5c5a59575655535251504e4d4c4b494746444342403f3e3d372e2d2c2b292827261f1e1d1c1a191817161513120f0e0d0c0a090807050403020100 } : Fields).get c.val)
theorem record003_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0713.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0713.localPairCheck (smallEmbedding record003) (record003.maps 16) (record003.inverseMaps 16) record003_frame016_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0713.localPairCheck (smallEmbedding record003) (record003.maps 16) (record003.inverseMaps 16) record003_frame016_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0713.localPairCheck (smallEmbedding record003) (record003.maps 16) (record003.inverseMaps 16) record003_frame016_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0713.localPairCheck (smallEmbedding record003) (record003.maps 16)
      (record003.inverseMaps 16) record003_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame016_links_0000 (interval_append _ 64 128 161 record003_frame016_links_0064 record003_frame016_links_0128))
theorem record003_frame016_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 16 :=
  of_group record003 16 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0713
    Papers.RationalityTen.SharedFrameCatalogue.group0713_facts record003_frame016_indices record003_frame016_graph record003_frame016_links
def record003_frame017_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xcaa64eb259910c8163d3065816bfe5f1af51760b775b4ad71682b325872b39580ab9555aa9153aa8d53aa97d466a1d4f6a6192c8953496a46d2148d3458a2810f486842ba11107a8364179f2cf787ae3c79dfceb47213891c10dca6d535819bccc265a3261914c7e6343109834bd05d42d9957ca8653528c14289f84d225b12a091647d23791808b645622891008564151f58f4c74e36c1af0d3c67c33018f8c345fc2ee16e8b2c57a2ae14e8a3c4fc26c12e893447822a111887042a2050f887803961b70d106342f816a0ab83480ba05c02d81680b005702b015404a024011808804001f00f007403601a00c005402000f007003401600a004802000a0040018008002000 } : Fields).get c.val)
theorem record003_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 17) (record003.inverseMaps 17) record003_frame017_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 17) (record003.inverseMaps 17) record003_frame017_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 17) (record003.inverseMaps 17) record003_frame017_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 17)
      (record003.inverseMaps 17) record003_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame017_links_0000 (interval_append _ 64 128 161 record003_frame017_links_0064 record003_frame017_links_0128))
theorem record003_frame017_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 17 :=
  of_group record003 17 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record003_frame017_indices record003_frame017_graph record003_frame017_links
def record003_frame018_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6d96ce6ca6be6b96b469a69469168767f67165665464e64563e62d60b5ff5fb5f05eb5e65df5d45cb5c05b65a756d55554a5305235194f94e34da4bd4b24a549248c48748046a46546245a45244642c42942541d4174083e73dc3d83cf3ca3c43be3b73af3a239638535834833e32d32231b3032f22ed2d72cf2c62b72b32af2aa2a429b29328427826424423d23922f22621b2112091fd1f41e91e31de1d41c91c41b61ab1a519918a18618117a17116615f15414613a12d11f1131070a205905805705605405305205102502402302202001f01e01d01b01a01801501000f00e00d00b00a009008005004003002001000 } : Fields).get c.val)
theorem record003_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record003) (record003.maps 18) (record003.inverseMaps 18) record003_frame018_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record003) (record003.maps 18) (record003.inverseMaps 18) record003_frame018_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record003) (record003.maps 18) (record003.inverseMaps 18) record003_frame018_indices (Fin.ofNat record003.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record003_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record003) (record003.maps 18)
      (record003.inverseMaps 18) record003_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record003_frame018_links_0000 (interval_append _ 64 128 161 record003_frame018_links_0064 record003_frame018_links_0128))
theorem record003_frame018_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 18 :=
  of_group record003 18 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record003_frame018_indices record003_frame018_graph record003_frame018_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (Fin.cases (record003_frame005_supported hcells) (Fin.cases (record003_frame006_supported hcells) (Fin.cases (record003_frame007_supported hcells) (Fin.cases (record003_frame008_supported hcells) (Fin.cases (record003_frame009_supported hcells) (Fin.cases (record003_frame010_supported hcells) (Fin.cases (record003_frame011_supported hcells) (Fin.cases (record003_frame012_supported hcells) (Fin.cases (record003_frame013_supported hcells) (Fin.cases (record003_frame014_supported hcells) (Fin.cases (record003_frame015_supported hcells) (Fin.cases (record003_frame016_supported hcells) (Fin.cases (record003_frame017_supported hcells) (Fin.cases (record003_frame018_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc8b61cb071804bce5daae7d54ca3451028354049f74f826d533098f4bba5bd2988fd475a3550e284a418206cfe67de3e41eb8f3a7953c81d68e9c7383841ac8d3067b31f18b8c3a60d30097f0ba45bb2d91654af254129b94a4a0e4e926912c893c49024191c08c245221f90cc8484191f08f1477a3aa1ce8df465031615c0a4c49023611207e83d61e00e7070c3721960c205d02c614209904802020d705201e80de06e03481740ae05602a012408403701b00c406002f016809804a01f00f0070028013009004001a00a004802000e005002000c002000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record004_frame001_links_0000 (interval_append _ 64 128 133 record004_frame001_links_0064 record004_frame001_links_0128))
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record004_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00024
