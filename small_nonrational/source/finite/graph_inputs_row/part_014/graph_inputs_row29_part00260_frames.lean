module
prelude
public import GraphInputsRow29Part00260Data
public import RawFrameSupport
public import SharedFrameGroups018Checked
public import SharedFrameGroups043Checked
public import SharedFrameGroups044Checked
public import SharedFrameGroups045Checked
public import SharedFrameGroups046Checked
public import SharedFrameGroups070Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups114Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00260
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x61f27653309924bea58528693048323f91ee8f14712370c865ab2cc9584a304cf24d10c88444112010f807a233c1950bc8552260115870c3661a20c985c42c41560a7852027413309604782140f6077837414209304701f80e006b03281840be05e02e016c0b005702a815008c03801980b4052027013009004602000f807403801800a004802200f007002c014008003801800a0040018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x66628492fa96b499239d1308643fd9fa0fb07c83d31e549bc44921b8ff87663641980b1c5682a414a09c84c222310e88203d81ce0dd86443121820be05b42ce1600ac854828813d09b04a02260fe07b838814209304701f80e006b03281840be05e02e016c0b005702a815008c03801980b4052027013009004602000f807403801800a004802200f007002c014008003801800a0040018008002000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x620a1533a654b89412123b4528951122043285cc89732e25a0ae14e28e4d49892e2584949190a2103fc798e51bc330640c51862f05d0b716c2d4598b21622bc560a91502944a0871041dc350650be16c2c8580ac1542905109e138228380660b41482704c0901182003e0740e0180280480880f01c02c0500800e0180280400600800800 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x67ca8541a814f09b12f25748a9051f23c46a8cccd97d2f65c8b31582a24fc9d93826c4bc969142244247e8ef1d0358690cf19a318620c11802fc5e8bc1762e45b0b31642bc4e88f1141f0370690c617c2e85c0b41642b0550a6148230380660b41482704c0901182003e0740e0180280480880f01c02c0500800e0180280400600800800 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record000_frame004_links_0000 record000_frame004_links_0064)
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0591.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0591.count (({ width := 11, code := 0x80ce7dc137d6d6d559d32b60cbf97caf45d0b893725049a8fd1721941c7c8f61ea3cc774ed1a8344644be9642ae4d49712b24e46c8b111214404798ec1cc35c628b415c268438830fc1c8350650c21742d85a0b015c2a0530a2140218380660b41482704c0901182003e0740e0180280480880f01c02c0500800e0180280400600800800 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record000_frame005_links_0000 record000_frame005_links_0064)
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0591
    Papers.RationalityTen.SharedFrameCatalogue.group0591_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
def record000_frame006_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0589.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0589.count (({ width := 11, code := 0x7a8dc5ac353684c8d822f1586ae5592ab540a611f228446851039f43c8704dd9b83646a0d198b3105d8ae94727648c8f11a22c428831011f83d8760e61c0354630b71622804207c0f01c0340640bc1682c0570aa1502885009c134208360620b01402604a08c1101f03c0700d8180280480880f01c02c0500800e0180280400600800800 } : Fields).get c.val)
theorem record000_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0589.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record000_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record000) (record000.maps 6)
      (record000.inverseMaps 6) record000_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record000_frame006_links_0000 record000_frame006_links_0064)
theorem record000_frame006_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 6 :=
  of_group record000 6 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0589
    Papers.RationalityTen.SharedFrameCatalogue.group0589_facts record000_frame006_indices record000_frame006_graph record000_frame006_links
def record000_frame007_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0590.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0590.count (({ width := 11, code := 0x7c6da5a7348676cb98cb0b5deba572ae05aab412ba3b46e8990b2003ea770eb9d139a708df19331c604b695328a4888d9152204107e8f71e63b4710de1b433c608b01562684087d0f01b03185e0b41582a0530a21402684c0941241f0360620b41482704c0901182003e0740e0180280480880f01c02c0500800e0180280400600800800 } : Fields).get c.val)
theorem record000_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record000_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record000) (record000.maps 7)
      (record000.inverseMaps 7) record000_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record000_frame007_links_0000 record000_frame007_links_0064)
theorem record000_frame007_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 7 :=
  of_group record000 7 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0590
    Papers.RationalityTen.SharedFrameCatalogue.group0590_facts record000_frame007_indices record000_frame007_graph record000_frame007_links
def record000_frame008_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0587.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0587.count (({ width := 8, code := 0xb6aeacaba9a6a09f989695949290878584827f7978716f6e6d6b69666563605a5952504f4e4c4a484746444342403e3d3c3b39383736353433302f2e2d2c2a292726252423221f1e1d1c1b191816151411100f0e0d0b0a080706050403020100 } : Fields).get c.val)
theorem record000_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0587.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0587.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0587.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record000_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0587.localPairCheck (smallEmbedding record000) (record000.maps 8)
      (record000.inverseMaps 8) record000_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record000_frame008_links_0000 record000_frame008_links_0064)
theorem record000_frame008_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 8 :=
  of_group record000 8 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0587
    Papers.RationalityTen.SharedFrameCatalogue.group0587_facts record000_frame008_indices record000_frame008_graph record000_frame008_links
def record000_frame009_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0588.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0588.count (({ width := 9, code := 0x6d3318ec66230174b958abd5cad55aa536964aa4d1e8944200fc7d3e1e8f073391c0d86632974b65a2c95caa53291449e4e2692c9047231108441200f4783b1b8d06632188c05c2d158a852281388c401f0f074381a0c85c2c14088401e0e0682c1408038180a04018080200 } : Fields).get c.val)
theorem record000_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0588.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0588.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0588.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record000_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0588.localPairCheck (smallEmbedding record000) (record000.maps 9)
      (record000.inverseMaps 9) record000_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record000_frame009_links_0000 record000_frame009_links_0064)
theorem record000_frame009_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 9 :=
  of_group record000 9 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0588
    Papers.RationalityTen.SharedFrameCatalogue.group0588_facts record000_frame009_indices record000_frame009_graph record000_frame009_links
def record000_frame010_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0586.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0586.count (({ width := 8, code := 0xb6aeacaba9a6a09f989695949290878584827f7978716f6e6d6b69666563605a5952504f4e4c4a484746444342403e3d3c3b39383736353433302f2e2d2c2a292726252423221f1e1d1c1b191816151411100f0e0d0b0a080706050403020100 } : Fields).get c.val)
theorem record000_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0586.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0586.localPairCheck (smallEmbedding record000) (record000.maps 10) (record000.inverseMaps 10) record000_frame010_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0586.localPairCheck (smallEmbedding record000) (record000.maps 10) (record000.inverseMaps 10) record000_frame010_indices (Fin.ofNat record000.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record000_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0586.localPairCheck (smallEmbedding record000) (record000.maps 10)
      (record000.inverseMaps 10) record000_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record000_frame010_links_0000 record000_frame010_links_0064)
theorem record000_frame010_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 10 :=
  of_group record000 10 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0586
    Papers.RationalityTen.SharedFrameCatalogue.group0586_facts record000_frame010_indices record000_frame010_graph record000_frame010_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (Fin.cases (record000_frame006_supported hcells) (Fin.cases (record000_frame007_supported hcells) (Fin.cases (record000_frame008_supported hcells) (Fin.cases (record000_frame009_supported hcells) (Fin.cases (record000_frame010_supported hcells) (fun j => Fin.elim0 j))))))))))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x692b44d96ec8d632b141580aae52928a14009eb4cda64d2e29624aaa53528493f49c24c524c92348e245521490747e23e51e48e74702364e8872b3659a7ccf065f31c16acb3253c28c13cc9c24c4259128090247d236916c87643820d90608103e91ec8f2467832a1668aa450827212a890c46221210707f83d81cc0e486b03521990bd05a82b41570a8052428013b09a04b424811f08b044421610307e03d41e40ec07303801b40d4057826c12e093048823811a08c03c01d00e006e03581a80d204001680a404e0240118088030014009003c01c00d } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame001_links_0000 (interval_append _ 64 128 132 record001_frame001_links_0064 record001_frame001_links_0128))
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x85184c82d82281480f73772e6f66e46c66bc64f6406085ec5cd5bd59c59959058857b57857056855a55754954653e53152a52245544640e3f23d33c33a23493403082f62d82ce2b62ad2a529829528d28527727426626325b24e24723f20c2071e51d81c91c31b81b11a919e19a19118917e17a16e16a16315815014914613f13712c12811f11710c1080fc0f80f10e60de0d70d50d10cd0c90c50c10a909b09709309108e08d08c07807407006e06b06a06904002d02902702402302201801401200f00e00d } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame002_links_0000 (interval_append _ 64 128 132 record001_frame002_links_0064 record001_frame002_links_0128))
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1106.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1106.count (({ width := 10, code := 0x775dc749cf729c96adaa6819d661975fd7b5cd6e5a966585605795c5655855954545505354c52947515434a525475184511042cf93e0ee3ace6394df374db360d7354d3340cf330cb324c6310c22c0af294a22749c258942488f2388c2288721883208801f47b1e4781d8741c4701b86c1a468194641885f1745b16859160571585513848110400f83b0e8390cc2f0ac29098250901e06816050110400f02c070140200400 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame003_links_0000 (interval_append _ 64 128 132 record001_frame003_links_0064 record001_frame003_links_0128))
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1106
    Papers.RationalityTen.SharedFrameCatalogue.group1106_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1104.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1104.count (({ width := 10, code := 0x83e0e816027f5fc79de6775da755d4709bf6e1b36b9aa689a16799b659956498f62989611836017b5e5765956256d565454d515394e12f4b127499204751a455144450e4250840d023fcfa3e0f53a4e837cdc35cd6340cd328c5310c12f8b92e0b32c8af2a8a8294a42849e26498254922348c21c8620c7e1f0791e0771d8751d0731bc6b19c631845e1745c160541404e12c4a124380b42909c2408c22060140480f0380d } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1104.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame004_links_0000 (interval_append _ 64 128 132 record001_frame004_links_0064 record001_frame004_links_0128))
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1104
    Papers.RationalityTen.SharedFrameCatalogue.group1104_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1103.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1103.count (({ width := 10, code := 0x83e0e816027f5fc79de6775da755d4709bf6e1b36b9aa689a16799b659956498f62989611836017b5e5765956256d565454d515394e12f4b127499204751a455144450e4250840d023fcfa3e0f53a4e837cdc35cd6340cd328c5310c12f8b92e0b32c8af2a8a8294a42849e26498254922348c21c8620c7e1f0791e0771d8751d0731bc6b19c631845e1745c160541404e12c4a124380b42909c2408c22060140480f0380d } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1103.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame005_links_0000 (interval_append _ 64 128 132 record001_frame005_links_0064 record001_frame005_links_0128))
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1103
    Papers.RationalityTen.SharedFrameCatalogue.group1103_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1102.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1102.count (({ width := 10, code := 0x8c22f896228761c7f9fd7cdf07adea749ce719c16f1b86c5b06b9ab699a56899f66999651936418c629885b96a5895d561545353b4e9304b52849d2147d1c45d1644d1042d0a41504404fd3ecf939ce6370d9350d3334cb320c3308bf2f0b72d8b12c0ad2a4a7294a42889f26899258932388d22087210801f87c1ec7a1e4781dc761bc691946117c5c16c5a150501304a11c46114350b42909c2408c22060140480f0380d } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame006_links_0000 (interval_append _ 64 128 132 record001_frame006_links_0064 record001_frame006_links_0128))
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1102
    Papers.RationalityTen.SharedFrameCatalogue.group1102_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
def record001_frame007_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1101.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1101.count (({ width := 9, code := 0x8ec72331688c42110782405f8fb7a3cde2ec74b99c8e371385bcdd6db65acd5693459ecc65b2988c360af172b65a2bd5cab5428d449f4f27534994ba55249147235168843a1902803e9e8ea74389c0de6c359a4ce6431980be5d2d164b0572b154a4512793494492311486401f8f87a3c1d8e872381b8d86830170ac54291409844200e870361a0c050240f070341607028080200 } : Fields).get c.val)
theorem record001_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1101.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1101.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1101.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1101.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1101.localPairCheck (smallEmbedding record001) (record001.maps 7)
      (record001.inverseMaps 7) record001_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame007_links_0000 (interval_append _ 64 128 132 record001_frame007_links_0064 record001_frame007_links_0128))
theorem record001_frame007_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 7 :=
  of_group record001 7 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1101
    Papers.RationalityTen.SharedFrameCatalogue.group1101_facts record001_frame007_indices record001_frame007_graph record001_frame007_links
def record001_frame008_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0606.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0606.count (({ width := 11, code := 0xa4948a88d09a013e65c4b593725243c838c11761c426831029fe3fb7e8fa5eabd479ef0dd9bb1740e75ca3826eedb196b2a630c35812fa5d8b596a2b554ea5d46a824fc9d1312614b8945222424668c914a1641c818f51e73886d4d319c324638c19732e45b0b21592ae530a514326a4bc9492724445c839062023e8780ed1c83806b8c617a2d0588a9142258478880f41cc3886f0da1b03586a0c61883005e0b61682c83c0560a4138240460880c01402403c0700d } : Fields).get c.val)
theorem record001_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record001) (record001.maps 8)
      (record001.inverseMaps 8) record001_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame008_links_0000 (interval_append _ 64 128 132 record001_frame008_links_0064 record001_frame008_links_0128))
theorem record001_frame008_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 8 :=
  of_group record001 8 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0606
    Papers.RationalityTen.SharedFrameCatalogue.group0606_facts record001_frame008_indices record001_frame008_graph record001_frame008_links
def record001_frame009_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0604.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0604.count (({ width := 11, code := 0x7e8fc9ef3d5792f0dd1ba0718e0dbd3726a2d399c32b640c5d8730d612c097b2f55e2bad70ae05aeb55672c457cae14a2904fa9c133a5d4a49011e226434835019fc3f27c8f39e63c4774e91d038c710de9ae34e678c59892e0584ab9502905149f1322624a89211c236448889081f43c4750e91c83786b0d519c32c618c01742dc588aa1462744d897126238458880fa1d83a0720e01b83686c0ca18c3085f0ba1702d84005a0a4138240460880c01402403c0700d } : Fields).get c.val)
theorem record001_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record001) (record001.maps 9)
      (record001.inverseMaps 9) record001_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame009_links_0000 (interval_append _ 64 128 132 record001_frame009_links_0064 record001_frame009_links_0128))
theorem record001_frame009_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 9 :=
  of_group record001 9 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0604
    Papers.RationalityTen.SharedFrameCatalogue.group0604_facts record001_frame009_indices record001_frame009_graph record001_frame009_links
def record001_frame010_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0599.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0599.count (({ width := 11, code := 0x6c8d81a934f692d1d92b1e628c3d82b035daba16d2d1594b055b2b455ea9d5029f536a5d442874f89ed3aa6b4cc98120a3c45a8850d2144147dcfb1e73c2778ec9d1394718db9b635e6b0d29a433265cc91883045f4b31622a2528a093d26c4cc9592224046c8b90d216410810fd1e63b8738e31bc364668c918a30c5e0b91622bc550a01362504908d10e2103f0780e21b43586a0d2198328640b61642b8560a814c2903705209c130240460880c01402403c0700d } : Fields).get c.val)
theorem record001_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0599.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0599.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0599.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0599.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0599.localPairCheck (smallEmbedding record001) (record001.maps 10)
      (record001.inverseMaps 10) record001_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame010_links_0000 (interval_append _ 64 128 132 record001_frame010_links_0064 record001_frame010_links_0128))
theorem record001_frame010_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 10 :=
  of_group record001 10 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0599
    Papers.RationalityTen.SharedFrameCatalogue.group0599_facts record001_frame010_indices record001_frame010_graph record001_frame010_links
def record001_frame011_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0597.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0597.count (({ width := 8, code := 0x838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0597.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0597.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0597.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0597.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0597.localPairCheck (smallEmbedding record001) (record001.maps 11)
      (record001.inverseMaps 11) record001_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame011_links_0000 (interval_append _ 64 128 132 record001_frame011_links_0064 record001_frame011_links_0128))
theorem record001_frame011_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 11 :=
  of_group record001 11 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0597
    Papers.RationalityTen.SharedFrameCatalogue.group0597_facts record001_frame011_indices record001_frame011_graph record001_frame011_links
def record001_frame012_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0596.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0596.count (({ width := 9, code := 0x8dc662d1488c42110680bf9f6f97a3c9dae973b91c4e170379b8db6d361acd5693459ecd65b2586c15e2e16cb358ab154a55127d3a9b4d2612c954a249208f4622d128742a0d02803e1e4f0763a1cce470379b4d66934194c86330178b85b2d164ae562a148a04f2612c94472290c8441200fc7c3d1d8e46e351a0c86230170b4582b150a4501f0d86832180b858200e0682c1409 } : Fields).get c.val)
theorem record001_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0596.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0596.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0596.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0596.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0596.localPairCheck (smallEmbedding record001) (record001.maps 12)
      (record001.inverseMaps 12) record001_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame012_links_0000 (interval_append _ 64 128 132 record001_frame012_links_0064 record001_frame012_links_0128))
theorem record001_frame012_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 12 :=
  of_group record001 12 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0596
    Papers.RationalityTen.SharedFrameCatalogue.group0596_facts record001_frame012_indices record001_frame012_graph record001_frame012_links
def record001_frame013_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0594.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0594.count (({ width := 8, code := 0x8d8c8b8a89888685848382817f7e7d7c7b7a7877767574737271706f6d6c6b6a6968676665646362605f5e5d5c5b5a5857565554535251504e4d4c4b4a4948474645444341403f3e3d3c3b3a3937363534333231302f2e2d2c2b2a2927262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0594.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0594.localPairCheck (smallEmbedding record001) (record001.maps 13) (record001.inverseMaps 13) record001_frame013_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0594.localPairCheck (smallEmbedding record001) (record001.maps 13) (record001.inverseMaps 13) record001_frame013_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0594.localPairCheck (smallEmbedding record001) (record001.maps 13) (record001.inverseMaps 13) record001_frame013_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0594.localPairCheck (smallEmbedding record001) (record001.maps 13)
      (record001.inverseMaps 13) record001_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame013_links_0000 (interval_append _ 64 128 132 record001_frame013_links_0064 record001_frame013_links_0128))
theorem record001_frame013_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 13 :=
  of_group record001 13 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0594
    Papers.RationalityTen.SharedFrameCatalogue.group0594_facts record001_frame013_indices record001_frame013_graph record001_frame013_links
def record001_frame014_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0592.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0592.count (({ width := 8, code := 0xe5e4e2e1dfdedad9d6d4d3d1cdccc9c7c6c4c1c0bfbdbbbab9b7b6b5b1b0aeacabaaa7a6a3a1a09e9b98979492918f8d8c8a8887868483827e7d7b797877757472706f6e6c6b6a6867666462615d5c5b58575655545351504f4d4b4a46454441403f3e3d3c3b3a3937353332312f2e2d2b2a29282726251d1a19181716150f0e0d0b0a09 } : Fields).get c.val)
theorem record001_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0592.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0592.localPairCheck (smallEmbedding record001) (record001.maps 14) (record001.inverseMaps 14) record001_frame014_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0592.localPairCheck (smallEmbedding record001) (record001.maps 14) (record001.inverseMaps 14) record001_frame014_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0592.localPairCheck (smallEmbedding record001) (record001.maps 14) (record001.inverseMaps 14) record001_frame014_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0592.localPairCheck (smallEmbedding record001) (record001.maps 14)
      (record001.inverseMaps 14) record001_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame014_links_0000 (interval_append _ 64 128 132 record001_frame014_links_0064 record001_frame014_links_0128))
theorem record001_frame014_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 14 :=
  of_group record001 14 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0592
    Papers.RationalityTen.SharedFrameCatalogue.group0592_facts record001_frame014_indices record001_frame014_graph record001_frame014_links
def record001_frame015_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0847.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0847.count (({ width := 11, code := 0xc5d893065fdbe37b2c7586acb55ea5545a2d422714cb9712ca53ca393725a44c848f11ba2dc5988f1121cc2b83b059e0bb5730e19bc3736d4ced98b0d5f4bbd762e35b4b4d61ac156eab55029f520a394327b4e29b51c22e4107d8f31e23b073ce39b936c6acd0996326614c117b2e0598b015a2a252c9e9362544788910f2043f07a0ea1c03686c0ca17e2d0540a0120214418811001f83e87c0dc1b0340670ca1903183e05a0a4138240460880c01402403c0700d } : Fields).get c.val)
theorem record001_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record001) (record001.maps 15) (record001.inverseMaps 15) record001_frame015_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record001) (record001.maps 15) (record001.inverseMaps 15) record001_frame015_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record001) (record001.maps 15) (record001.inverseMaps 15) record001_frame015_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record001) (record001.maps 15)
      (record001.inverseMaps 15) record001_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame015_links_0000 (interval_append _ 64 128 132 record001_frame015_links_0064 record001_frame015_links_0128))
theorem record001_frame015_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 15 :=
  of_group record001 15 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0847
    Papers.RationalityTen.SharedFrameCatalogue.group0847_facts record001_frame015_indices record001_frame015_graph record001_frame015_links
def record001_frame016_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0845.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0845.count (({ width := 11, code := 0x92122a3c46e8c717206c077e8fb1efbdb76ceb9cab886f4dcdb5b696c6d79ac35569cd219db3965acad91b18620c3160ab9544a59452854fa96d2ba3b45a8890ea1441881cff9fe3f07ccf49e83bc770ea1ca3846fccb9902ee5b8b115e2aa540a49412804ec9a12724c4688c912214410808fe1f03d0770e91c436c6a0d3192314600b91662b8568a71442744d0961122043f87d0f81e43c0770de1b4358690ce1983284005a0a4138240460880c01402403c0700d } : Fields).get c.val)
theorem record001_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record001) (record001.maps 16) (record001.inverseMaps 16) record001_frame016_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record001) (record001.maps 16) (record001.inverseMaps 16) record001_frame016_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record001) (record001.maps 16) (record001.inverseMaps 16) record001_frame016_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record001) (record001.maps 16)
      (record001.inverseMaps 16) record001_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame016_links_0000 (interval_append _ 64 128 132 record001_frame016_links_0064 record001_frame016_links_0128))
theorem record001_frame016_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 16 :=
  of_group record001 16 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0845
    Papers.RationalityTen.SharedFrameCatalogue.group0845_facts record001_frame016_indices record001_frame016_graph record001_frame016_links
def record001_frame017_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0839.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0839.count (({ width := 8, code := 0x838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0839.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0839.localPairCheck (smallEmbedding record001) (record001.maps 17) (record001.inverseMaps 17) record001_frame017_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0839.localPairCheck (smallEmbedding record001) (record001.maps 17) (record001.inverseMaps 17) record001_frame017_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0839.localPairCheck (smallEmbedding record001) (record001.maps 17) (record001.inverseMaps 17) record001_frame017_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0839.localPairCheck (smallEmbedding record001) (record001.maps 17)
      (record001.inverseMaps 17) record001_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame017_links_0000 (interval_append _ 64 128 132 record001_frame017_links_0064 record001_frame017_links_0128))
theorem record001_frame017_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 17 :=
  of_group record001 17 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0839
    Papers.RationalityTen.SharedFrameCatalogue.group0839_facts record001_frame017_indices record001_frame017_graph record001_frame017_links
def record001_frame018_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0837.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0837.count (({ width := 8, code := 0x838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0837.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0837.localPairCheck (smallEmbedding record001) (record001.maps 18) (record001.inverseMaps 18) record001_frame018_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0837.localPairCheck (smallEmbedding record001) (record001.maps 18) (record001.inverseMaps 18) record001_frame018_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0837.localPairCheck (smallEmbedding record001) (record001.maps 18) (record001.inverseMaps 18) record001_frame018_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0837.localPairCheck (smallEmbedding record001) (record001.maps 18)
      (record001.inverseMaps 18) record001_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame018_links_0000 (interval_append _ 64 128 132 record001_frame018_links_0064 record001_frame018_links_0128))
theorem record001_frame018_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 18 :=
  of_group record001 18 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0837
    Papers.RationalityTen.SharedFrameCatalogue.group0837_facts record001_frame018_indices record001_frame018_graph record001_frame018_links
def record001_frame019_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0283.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0283.count (({ width := 8, code := 0x838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0283.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0283.localPairCheck (smallEmbedding record001) (record001.maps 19) (record001.inverseMaps 19) record001_frame019_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0283.localPairCheck (smallEmbedding record001) (record001.maps 19) (record001.inverseMaps 19) record001_frame019_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0283.localPairCheck (smallEmbedding record001) (record001.maps 19) (record001.inverseMaps 19) record001_frame019_indices (Fin.ofNat record001.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record001_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0283.localPairCheck (smallEmbedding record001) (record001.maps 19)
      (record001.inverseMaps 19) record001_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record001_frame019_links_0000 (interval_append _ 64 128 132 record001_frame019_links_0064 record001_frame019_links_0128))
theorem record001_frame019_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 19 :=
  of_group record001 19 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0283
    Papers.RationalityTen.SharedFrameCatalogue.group0283_facts record001_frame019_indices record001_frame019_graph record001_frame019_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (Fin.cases (record001_frame006_supported hcells) (Fin.cases (record001_frame007_supported hcells) (Fin.cases (record001_frame008_supported hcells) (Fin.cases (record001_frame009_supported hcells) (Fin.cases (record001_frame010_supported hcells) (Fin.cases (record001_frame011_supported hcells) (Fin.cases (record001_frame012_supported hcells) (Fin.cases (record001_frame013_supported hcells) (Fin.cases (record001_frame014_supported hcells) (Fin.cases (record001_frame015_supported hcells) (Fin.cases (record001_frame016_supported hcells) (Fin.cases (record001_frame017_supported hcells) (Fin.cases (record001_frame018_supported hcells) (Fin.cases (record001_frame019_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1a86d3b68cb4299facf56752d295b8a8853c29813bc97048e24311e88ef47423851b88c545e22dd1628a9451226512a88b37b1b9cd2067232598e4b4259229d94749ec4e426413049744b1256929893e496248922090647d23a91bc8d23bd1a10bbc5b42c415c8aa453228612d88f045421d10707bc3ac1c60db068c2f01590a384e825610c07b83c01d20e306d835015e09b03801ac0d206102e016808003c01c00d806603201880b4052027012008c044014007803401800b005002000e0060028010004001 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0847.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0847.count (({ width := 11, code := 0x31a62ac2580efa5efbcb64eb554aa8b4fe894de96d2c2544a29352564946c8bb162294428710b614418774ec5c8b826ecdc59db3161abe977aec5c2b61692c6580ad9562a153ca4546a854f89c93723a414798f11dc3a872ce29bb340644c31812f259cac9502944f88e90e2063ec798e119e3105c8b014a274480850d01943185b0ac1501f03c0700d8198320620b41482704808c1101401e0340600b0140200380600a01001001 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0847
    Papers.RationalityTen.SharedFrameCatalogue.group0847_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0841.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0841.count (({ width := 11, code := 0x28b50f9f13b671ce19b92163344988b0fe123ff7ccf8dee3d97a8f45e6bb775ceadd3b9e730e41c7384634c5179ae25acb455129a4f29b12fa5e4a89392524447e8e118a294508790d21541a81d011d735862cc31802f45d0b81682a4520a093b26a4888c11321c418770e01aa348668c116e2c4558a713e268480890d41983205e0b41601f03b06e0d4190310600b41482704808c1101401e0340600b0140200380600a01001001 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame003_links_0000 record002_frame003_links_0064)
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0841
    Papers.RationalityTen.SharedFrameCatalogue.group0841_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record002_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00260
