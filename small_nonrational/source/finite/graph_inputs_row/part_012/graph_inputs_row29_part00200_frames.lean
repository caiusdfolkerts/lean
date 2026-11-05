module
prelude
public import GraphInputsRow29Part00200Data
public import RawFrameSupport
public import SharedFrameGroups060Checked
public import SharedFrameGroups061Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups063Checked
public import SharedFrameGroups064Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00200
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x638c13726d2d70a834066bcba91d20e3f45488d1021dc2983705603bd2696ca5902fc588ad95329e51899929a4c4888d112a214267f4df9b7350680c31672b45349e9352504808a1041fe3e0798dd1a032c638bb16c2c85289a1142103806a0c01782d0560aa1402384307a0ec1d02c054098128220400780e81602a0440780d0140240400600600800800 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x305d530a3b513a3f11d283f416a078fd27ca3dc9e4cdc656428393cc7903b51858be45d42b514b0a144be20f10407c43d41de0eb86783301910c505e82e61650a5850c278121089042c20a0f707783a01aa0bf04f02200fe07b03a81cc0e406202f01680ac055028011c08603d01d80e8054026011007803a01900b805802a011008003c01a00b00500240100060018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xa7f9bf96f9608888787d17bd7ab76e74472d6fc6c96115d75cb51050347f47446843d41f4113ee36b35832f31d2fa2ea2742652552462232131f01c41b41a716b1441341251040f60e90bf0b209c08807f07b07507307206205e05a05605505004704303d03b03a02a02602201e01d01901701601501101000f00d00b00a009008006003002001000 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x6e26bb68965d65464a6346275f55c158456b56a5555405294dd4c94c84b64ab48c47e46d46a45542842341840d3ed3b937c36c35a3413383212d52c92b72ae29727d27626a25c2402232152102051f31c01b41ad1a919618518017717015714e14613d13912811e1170f30e80e00dd0ca0c20bd0b20a90a609408c08807406c06b05c05705405305204f04103a03902a02402202101f01d01500e00d00c009008006002001000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x73a70b6da69468c68466f6646336025c65ad5ac59757d56552e52151f5185124fa4ea4dd4db4ce4ae4a94a14984754433fa3e73db3bd3b039533f33532a32330e2f12e62df2d32b429728727f2702572081f01ec1e51c51af1a519a19516b15914a13d13211d11010a0eb0e30de0d70c30bf0ba0ae0a60a309308a08807907106f06005b05805705605304403a03902a02402202101f01d01500e00d00c009008006002001000 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record004_frame002_links_0000 record004_frame002_links_0064)
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0756.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0756.count (({ width := 9, code := 0x5027b38974b25324914722f1084c2206ff7ebe5ecf5793c5d6e872b91c2d96c359a8d16631580bb5b2d164ae562a54ea44fa7536984a239188b44a210a813f9f4f074391c0dc6832188c05f2e164ae4e2693096492411c8a442190882401d8e87234188b85a2c1489c4c251007034190b854260e068301208030080200 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0756.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record004_frame003_links_0000 record004_frame003_links_0064)
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0756
    Papers.RationalityTen.SharedFrameCatalogue.group0756_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
def record004_frame004_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0782.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0782.count (({ width := 9, code := 0x4662d118441a0901803f1eef075ba9cee572381badc6cb61a4cf6632d90c1602f978b95a2b552a651a89429d4da612c93472311487419f8f87b3c9e0ea71379b4d06431180bc582a94ca25026928903f1f0f4783a1c8e06c351a0cc6431180bc5c2d1509c4c2511084401f0f06830170a84c240d0602c1007030080200 } : Fields).get c.val)
theorem record004_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0782.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0782.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0782.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record004_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0782.localPairCheck (smallEmbedding record004) (record004.maps 4)
      (record004.inverseMaps 4) record004_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record004_frame004_links_0000 record004_frame004_links_0064)
theorem record004_frame004_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 4 :=
  of_group record004 4 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0782
    Papers.RationalityTen.SharedFrameCatalogue.group0782_facts record004_frame004_indices record004_frame004_graph record004_frame004_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (Fin.cases (record004_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xcd960b2ff179ab5d541a9b14989e54b124fd2568ed46ba28d1007fa3ef9f24f5a6823329948c825852b49590a9053929594649ee4d925891b48c445321f10407123691a88ca462e2e5162096c48c23511187b83ba1d10e006182ec1530a004c023e0fe07a039c1900bb05382500f8071034818c0c405902a814008e04502200e406803101700b005602a010808003a01600a803c01c00d006002000e006002000c004000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x73b7336ed6c06aa69067665963b62d61b6195f85ed5df5d45bb57f53b5355074fa4df4c149f49047946c46444644041d4073ea3df3dd3c43a93a339835d3432ff2f92c32a429728525324623723022820c1fe1e21ce1c91c61c11b21a319f18b18718017917116615a15014414113c13112a10e1080fa0f40ee0e50d80d20c30bc0b60b30ae0ac0a709908f08607c07105d05a05805504d04203702602202101d01901101000c00a006001000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x76f76a71e6e26d46c56b269c68e67d65d65c64a6396266146055e859d58f5625545345134ee4d94b649f49a48748246c46144c43343242340e4003f03d43c537e37334b33632a3152f02e12cc2c02bc2b12aa28d27026025424523822121d2051fe1f71e41dd1cb1bf1ac1a119c18f18317b14a13e12011410b0f30df0d50be0b10a70a209d09a09708b08507c07206b05a05705505204904003702602202101d01901101000c00a006001000 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record006_frame002_links_0000 record006_frame002_links_0064)
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0813.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0813.count (({ width := 11, code := 0xf99f23d6798f19e03b774ce6dcb38f71ae0dbe3716d6d75a4b2c650c6189b0a5fcbbd72ad659ab2d5eabb550a7d4828b512a053aa714da95125a2e454849029ff3ec78cee9d439e734e01bb34a640c51822f05acaf959298524a21392624a89111821c428828f41e03746c8cd1903105c0ad14e25c4888e11221c428830fe1f43b06e0ce1502905009a1101e83604a0841001d0320440800c01401800800 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record006_frame003_links_0000 record006_frame003_links_0064)
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0813
    Papers.RationalityTen.SharedFrameCatalogue.group0813_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xded6cdb5e1a04cdf65bb21184abc85d22c99604ab1554291141c9e04dc262d2d293448e242d1b08b6440a1a50b08424171f54ee474c3641a88ca46492f99724b4c5842b21520a3e50b27e935c97649223f11c08bc4501870bb45b826d12608ec3e41cc0b4055426212508b83d01d00da06582c415609004782080da06903181780b205402500d406202b0130084038016009804802200d006002000e006002000c002000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xcee66032b58c2c476142f0d6f0b395902b2d564a4d518a79537a9a04c6a575274908475a35514688042820d50407ee3d71e20e9073236d9b04ca663b2fa975cb805b02c715c8a9853729493f49be4b925192548d643f1a90ca062c2a814009b83dc1d10c205d028413209003d01ce0d705f82ac14e09004782080da06903181780b205402500d406202b0130084038016009804802200d006002000e006002000c002000 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xf4d76abab5c0edd86ceb3c98ccbe35dd2c715eea4d51927093369754aa248d1fe8c9457226d0d284740a1ff0fd47c23c91cc8d5e6862f4170ca324fe247119c8824201f78f2c72a37a1b38cd46262e01640ad851c25e0f2875839e19f0c806242b214b093047c21810507e83a41c40da06682c415609004782080da06903181780b205402500d406202b0130084038016009804802200d006002000e006002000c002000 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record007_frame003_links_0000 record007_frame003_links_0064)
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x6f2dc1b675f6b7d55a132e635c477aaec5a2b3359ea6538a5745e824e89b734a5bca290b1de36c588930b6023f2776ea5b9b6a670c7584afc5d0b4d5b2a853ca0937a5348c8f514a1a360684cd1662ae5409792520a400758e31b63105e0b41542844f08c1161f8358670c21702b8520900d41882b04c0840e0160260480880d0180200380600800c00800 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record007_frame004_links_0000 record007_frame004_links_0064)
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x117a2b44c88d0e21842883104e023e47a2f01d0b9a70ade9b6b6c6ccd59a2b3d65ec818930e608be1732dd59ab054a27a4da97929a494848e116a1d426835019f23be774e51bf36a698cd1952f85bcb215726c4c08f1181ee3c8750e31b4348658c116c2bc4f099124228400780e21ac3085d0b014c2904e0921101b0340600ac1302103e0700901101a0300400700c00c00800 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x7657256e96c469c67d66963962060a5f15ec59d58f55653451b4db4b64a747e44c43540e3f23e63d33cd3c837636b34933632a31a2ee2e12cc2c52702552492452382242051fe1f51e41dd1c21ac1a119a18b1871791551451391201141030f30e40d50be0b60a709d08408007c06705a05505004c04904704604003703503102702602202101d01c01901701601101000c00a007006003001000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x8147c779176c73c7157036c56ac68a65b64e5fa5f15bf5a058855a54854151a4be4a946244d42f4033ef3e538638034e33632230d2e52df2d02c926224b24623c22220a1e61df1d51c31bb1a719818c18716f16915513512d12711810e1040ef0e20d50c40c10bc0b108e08a08606d05e05905405004d04b04a04203703503102702602202101d01c01901701601101000c00a007006003001000 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0744.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0744.count (({ width := 8, code := 0x89888786858382807f7e7d7c7a7978777675747372706f6d6c6b6a6968666564636261605f5e5d5a5857565453504f4e4d4b4a484645444342413f3e3c3b3938373635343331302f2b2a282624201f1e1d1c1b1a19181716151413100e0d0b0a08070504030100 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0744.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0744.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0744.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0744.localPairCheck (smallEmbedding record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame003_links_0000 record009_frame003_links_0064)
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0744
    Papers.RationalityTen.SharedFrameCatalogue.group0744_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
def record009_frame004_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0777.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0777.count (({ width := 8, code := 0x89888786858382807f7e7d7c7a7978777675747372706f6d6c6b6a6968666564636261605f5e5d5a5857565453504f4e4d4b4a484645444342413f3e3c3b3938373635343331302f2b2a282624201f1e1d1c1b1a19181716151413100e0d0b0a08070504030100 } : Fields).get c.val)
theorem record009_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0777.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0777.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0777.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0777.localPairCheck (smallEmbedding record009) (record009.maps 4)
      (record009.inverseMaps 4) record009_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame004_links_0000 record009_frame004_links_0064)
theorem record009_frame004_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 4 :=
  of_group record009 4 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0777
    Papers.RationalityTen.SharedFrameCatalogue.group0777_facts record009_frame004_indices record009_frame004_graph record009_frame004_links
def record009_frame005_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0721.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0721.count (({ width := 8, code := 0xdddbdad9d2cdcbc7c4c3c2bfb9b8b6b5b3b2b0aea9a09f9b98979695928c8a8988868382817e7d72706f6e6a6966656462605d5b5958575653514f4d4b4a484746454241403e3a393534312e2b272625242322211f1e1d1b1a18171412110f0e0b090605030100 } : Fields).get c.val)
theorem record009_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0721.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0721.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0721.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0721.localPairCheck (smallEmbedding record009) (record009.maps 5)
      (record009.inverseMaps 5) record009_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame005_links_0000 record009_frame005_links_0064)
theorem record009_frame005_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 5 :=
  of_group record009 5 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0721
    Papers.RationalityTen.SharedFrameCatalogue.group0721_facts record009_frame005_indices record009_frame005_graph record009_frame005_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (Fin.cases (record009_frame004_supported hcells) (Fin.cases (record009_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record009_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00200
