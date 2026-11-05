module
prelude
public import GraphInputsRow31Part00000Data
public import RawFrameSupport
public import SharedFrameGroups000Checked
public import SharedFrameGroups001Checked
public import SharedFrameGroups002Checked
public import SharedFrameGroups003Checked
public import SharedFrameGroups004Checked
public import SharedFrameGroups005Checked
public import SharedFrameGroups006Checked
public import SharedFrameGroups007Checked
public import SharedFrameGroups008Checked
public import SharedFrameGroups009Checked
public import SharedFrameGroups011Checked
public import SharedFrameGroups013Checked
public import SharedFrameGroups014Checked
public import SharedFrameGroups015Checked
public import SharedFrameGroups020Checked
public import SharedFrameGroups024Checked
public import SharedFrameGroups025Checked
public import SharedFrameGroups026Checked
public import SharedFrameGroups029Checked
public import SharedFrameGroups030Checked
public import SharedFrameGroups031Checked
public import SharedFrameGroups032Checked
public import SharedFrameGroups033Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups042Checked
public import SharedFrameGroups043Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups057Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups079Checked
public import SharedFrameGroups080Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups095Checked
public import SharedFrameGroups096Checked
public import SharedFrameGroups097Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups116Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1a52d2368c3445972cb464e3251904c7a624b0fd84ec1d5f12f31662b235852bd55d4ad5553aa4d50ea7352428693309724a5251126c8f046ea2e514c87c41b20890047ee3dd9ea0e787363881c04dd26da34f1a44cf266c3149850b2656e2a89520a5e506274936c97c49a23a916489a4312098fd074637b1b28d8065430917c0b70596291138098449423b10687f824811807003581820c005f82f817a0bc05c02d01660b2053824010606c02f815009403301380700240070018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1015.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1015.count (({ width := 10, code := 0x86e18856128360b81e047fdfc7ddf47bdec795e3775d5751cf731c7711bf6f1b76c9aa6a5a66859e65d93639876097c5e1735b16757d5c5394b519424f93a4d5314b5294891f4711844d0e42d08404ff3e0f53c8eb3a4e2378d9350ce318c42fcb92d4b02b0a72849d260942348b18860148501344c12c4a1244811c461144410c400f0390c42a094200641202c0400c0200400 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1015
    Papers.RationalityTen.SharedFrameCatalogue.group1015_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x305608c057fef3de2bb9762e95cfb716dad95afb21622a0539a6b4c295d28a2343e85d079d337a4d48f9011ee394648bd14224c36847072074077daf91e1bbe770ed1d6ba971ce29c1b7e6b0d4981af55c2b55662c055ca9d4c2854ea98d2e24a466885021f63c4768e69bd366694ce9832e65a0ad14f25e498658c61622ac520a31442845009f13625c4b09511e1fc3b0650b21382403304e0700900700600800800 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0573.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0573.count (({ width := 9, code := 0x357a8d26873597cb6572792c5e2b1187c05feeb73b95c6df6eb4da2cd65b0576a14da4d1e8b419fcf679379a4ce612e94c9e37198b44e1f0d82409fefc7a3c9c8e16eb6db0d56933d98c7623057ebc5bacd56a751a853e9b4ca59268f462250c843f1f0c25e2b958a4512813c9c4d2612c9449239047635188b04e1d0b8401805018080200 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0573.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0573.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0573.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0573.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record000_frame004_links_0000 record000_frame004_links_0064)
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0573
    Papers.RationalityTen.SharedFrameCatalogue.group0573_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x6ff6fd6f56f26cb6ca6c26c06ba6b46946906876846676616096055ff5f85f45eb5ca5c35c05b558c57f5315245064ff4f34da4cf4bb4ad48f47c47246145742e4274003fd3f63f03e83e33c03bb3b33ad37d3773263142fe2ee2e32d22bd2b32992802742612592422262141f31e21d51ce1c01b81b11a519e18517b17416715f14a1420de0d90be0b80af0ae0ad0ac0ab0aa0a70a20a10a009708407906605904e04703302701c012007003002001000 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record000_frame005_links_0000 record000_frame005_links_0064)
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
def record000_frame006_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0378.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0378.count (({ width := 7, code := 0x3af4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record000_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0378.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0378.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0378.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record000_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0378.localPairCheck (smallEmbedding record000) (record000.maps 6)
      (record000.inverseMaps 6) record000_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record000_frame006_links_0000 record000_frame006_links_0064)
theorem record000_frame006_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 6 :=
  of_group record000 6 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0378
    Papers.RationalityTen.SharedFrameCatalogue.group0378_facts record000_frame006_indices record000_frame006_graph record000_frame006_links
def record000_frame007_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0450.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0450.count (({ width := 7, code := 0x3af4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record000_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0450.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0450.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0450.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record000_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0450.localPairCheck (smallEmbedding record000) (record000.maps 7)
      (record000.inverseMaps 7) record000_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record000_frame007_links_0000 record000_frame007_links_0064)
theorem record000_frame007_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 7 :=
  of_group record000 7 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0450
    Papers.RationalityTen.SharedFrameCatalogue.group0450_facts record000_frame007_indices record000_frame007_graph record000_frame007_links
def record000_frame008_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0307.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0307.count (({ width := 9, code := 0x1fcfd7e3edeef67abd1e6f1773b5d8e972b91badc6db69b2d76a34da4cf6632986c2602fd7cbd5dae96eb459ac560ad53a99409f4f275389b4ba592a9447a350c854220902803f1f4f6793c1d8ea72371b4d26833994c8633117cba5a2c960a851259287e3e1d0e470371b0d46833190c4602f170ac5024100683215090301404018080200 } : Fields).get c.val)
theorem record000_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0307.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record000_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record000) (record000.maps 8)
      (record000.inverseMaps 8) record000_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record000_frame008_links_0000 record000_frame008_links_0064)
theorem record000_frame008_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 8 :=
  of_group record000 8 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0307
    Papers.RationalityTen.SharedFrameCatalogue.group0307_facts record000_frame008_indices record000_frame008_graph record000_frame008_links
def record000_frame009_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0017.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0017.count (({ width := 7, code := 0x3af4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record000_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0017.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0017.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0017.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record000_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0017.localPairCheck (smallEmbedding record000) (record000.maps 9)
      (record000.inverseMaps 9) record000_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record000_frame009_links_0000 record000_frame009_links_0064)
theorem record000_frame009_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 9 :=
  of_group record000 9 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0017
    Papers.RationalityTen.SharedFrameCatalogue.group0017_facts record000_frame009_indices record000_frame009_graph record000_frame009_links
def record000_frame010_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0006.count (({ width := 7, code := 0x3af4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record000_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0006.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0006.localPairCheck (smallEmbedding record000) (record000.maps 10) (record000.inverseMaps 10) record000_frame010_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0006.localPairCheck (smallEmbedding record000) (record000.maps 10) (record000.inverseMaps 10) record000_frame010_indices (Fin.ofNat record000.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record000_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0006.localPairCheck (smallEmbedding record000) (record000.maps 10)
      (record000.inverseMaps 10) record000_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record000_frame010_links_0000 record000_frame010_links_0064)
theorem record000_frame010_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 10 :=
  of_group record000 10 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0006
    Papers.RationalityTen.SharedFrameCatalogue.group0006_facts record000_frame010_indices record000_frame010_graph record000_frame010_links
def record000_frame011_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0012.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0012.count (({ width := 7, code := 0x3af4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record000_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0012.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0012.localPairCheck (smallEmbedding record000) (record000.maps 11) (record000.inverseMaps 11) record000_frame011_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0012.localPairCheck (smallEmbedding record000) (record000.maps 11) (record000.inverseMaps 11) record000_frame011_indices (Fin.ofNat record000.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record000_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0012.localPairCheck (smallEmbedding record000) (record000.maps 11)
      (record000.inverseMaps 11) record000_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record000_frame011_links_0000 record000_frame011_links_0064)
theorem record000_frame011_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 11 :=
  of_group record000 11 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0012
    Papers.RationalityTen.SharedFrameCatalogue.group0012_facts record000_frame011_indices record000_frame011_graph record000_frame011_links
def record000_frame012_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0011.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0011.count (({ width := 7, code := 0x3af4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record000_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0011.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0011.localPairCheck (smallEmbedding record000) (record000.maps 12) (record000.inverseMaps 12) record000_frame012_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0011.localPairCheck (smallEmbedding record000) (record000.maps 12) (record000.inverseMaps 12) record000_frame012_indices (Fin.ofNat record000.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record000_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0011.localPairCheck (smallEmbedding record000) (record000.maps 12)
      (record000.inverseMaps 12) record000_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record000_frame012_links_0000 record000_frame012_links_0064)
theorem record000_frame012_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 12 :=
  of_group record000 12 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0011
    Papers.RationalityTen.SharedFrameCatalogue.group0011_facts record000_frame012_indices record000_frame012_graph record000_frame012_links
def record000_frame013_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0002.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0002.count (({ width := 7, code := 0x3af4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record000_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0002.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0002.localPairCheck (smallEmbedding record000) (record000.maps 13) (record000.inverseMaps 13) record000_frame013_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0002.localPairCheck (smallEmbedding record000) (record000.maps 13) (record000.inverseMaps 13) record000_frame013_indices (Fin.ofNat record000.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record000_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0002.localPairCheck (smallEmbedding record000) (record000.maps 13)
      (record000.inverseMaps 13) record000_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record000_frame013_links_0000 record000_frame013_links_0064)
theorem record000_frame013_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 13 :=
  of_group record000 13 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0002
    Papers.RationalityTen.SharedFrameCatalogue.group0002_facts record000_frame013_indices record000_frame013_graph record000_frame013_links
def record000_frame014_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0004.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0004.count (({ width := 7, code := 0x3af4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record000_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0004.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0004.localPairCheck (smallEmbedding record000) (record000.maps 14) (record000.inverseMaps 14) record000_frame014_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0004.localPairCheck (smallEmbedding record000) (record000.maps 14) (record000.inverseMaps 14) record000_frame014_indices (Fin.ofNat record000.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record000_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0004.localPairCheck (smallEmbedding record000) (record000.maps 14)
      (record000.inverseMaps 14) record000_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record000_frame014_links_0000 record000_frame014_links_0064)
theorem record000_frame014_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 14 :=
  of_group record000 14 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0004
    Papers.RationalityTen.SharedFrameCatalogue.group0004_facts record000_frame014_indices record000_frame014_graph record000_frame014_links
def record000_frame015_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0000.count (({ width := 7, code := 0x3af4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record000_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0000.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0000.localPairCheck (smallEmbedding record000) (record000.maps 15) (record000.inverseMaps 15) record000_frame015_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0000.localPairCheck (smallEmbedding record000) (record000.maps 15) (record000.inverseMaps 15) record000_frame015_indices (Fin.ofNat record000.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record000_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0000.localPairCheck (smallEmbedding record000) (record000.maps 15)
      (record000.inverseMaps 15) record000_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record000_frame015_links_0000 record000_frame015_links_0064)
theorem record000_frame015_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 15 :=
  of_group record000 15 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0000
    Papers.RationalityTen.SharedFrameCatalogue.group0000_facts record000_frame015_indices record000_frame015_graph record000_frame015_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (Fin.cases (record000_frame006_supported hcells) (Fin.cases (record000_frame007_supported hcells) (Fin.cases (record000_frame008_supported hcells) (Fin.cases (record000_frame009_supported hcells) (Fin.cases (record000_frame010_supported hcells) (Fin.cases (record000_frame011_supported hcells) (Fin.cases (record000_frame012_supported hcells) (Fin.cases (record000_frame013_supported hcells) (Fin.cases (record000_frame014_supported hcells) (Fin.cases (record000_frame015_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x4838fb1d235c678c91862fc528a113a254428810de1942f84504e06c0a7c2f7deebd87aaf3dde3b8766eb1d139a726dc1b3b636b4d59a6b3c670ccd9431e61ec297faf75e4b5168acc58caf95aa9c530a053ea6b4c89792c25146887d0ca0c4067c8f21d6396708de1a833e660c31782c6580aa14d28c4e8991162143e4778e71902f85d8b11502684b0931242444808f11c21c4107d0f61c4360640c0130210260440680900900e00800800 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0819.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0819.count (({ width := 11, code := 0x50ea1b412814fc9f33e27ace59c73766c4d49a531e634c09732a2534a48fb1e23a46e8d519228c4d8890f617c22836fb5f4be37b0f49e2ba8742e69c4b796ccd7da5b4567ec959031962ac41852f85ecba5722d1594b095d2b0518a0d3fa714ce9251ea2d444839039f33da780e21b735869ccb98e3085ecba1542844c4929191d836c698c01642704b08f11c2344608b1142184107e0f41c03385d0ae1101f8270480700900900e00800800 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0819
    Papers.RationalityTen.SharedFrameCatalogue.group0819_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0320.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0320.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0320.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0320.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0320.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0320.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0320
    Papers.RationalityTen.SharedFrameCatalogue.group0320_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0403.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0403.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0403.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0403.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0403.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0403.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame004_links_0000 record001_frame004_links_0064)
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0403
    Papers.RationalityTen.SharedFrameCatalogue.group0403_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0161.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0161.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0161.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0161.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0161.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0161.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame005_links_0000 record001_frame005_links_0064)
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0161
    Papers.RationalityTen.SharedFrameCatalogue.group0161_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0213.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0213.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0213.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0213.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0213.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0213.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame006_links_0000 record001_frame006_links_0064)
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0213
    Papers.RationalityTen.SharedFrameCatalogue.group0213_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
def record001_frame007_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0077.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0077.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0077.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0077.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0077.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0077.localPairCheck (smallEmbedding record001) (record001.maps 7)
      (record001.inverseMaps 7) record001_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame007_links_0000 record001_frame007_links_0064)
theorem record001_frame007_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 7 :=
  of_group record001 7 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0077
    Papers.RationalityTen.SharedFrameCatalogue.group0077_facts record001_frame007_indices record001_frame007_graph record001_frame007_links
def record001_frame008_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0109.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0109.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0109.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0109.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0109.localPairCheck (smallEmbedding record001) (record001.maps 8)
      (record001.inverseMaps 8) record001_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame008_links_0000 record001_frame008_links_0064)
theorem record001_frame008_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 8 :=
  of_group record001 8 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0109
    Papers.RationalityTen.SharedFrameCatalogue.group0109_facts record001_frame008_indices record001_frame008_graph record001_frame008_links
def record001_frame009_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0070.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0070.count (({ width := 8, code := 0xeeedecebe9e8e7e6e5e4e3e1e0dfdedddcdad8d7d5d1d0cfcdcccbc9c8c6c5c4c2c0bcbab9b8b7b4b1b0afaca9a7a5a3a1a09b9a989796959291908f8c8a8887858281807e7b7a78747371706d6b6a666564625f5e5c5a595352504d4c4644433f3e393837363534333231302e2c292724211a1913100c0a0604020100 } : Fields).get c.val)
theorem record001_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0070.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0070.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0070.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0070.localPairCheck (smallEmbedding record001) (record001.maps 9)
      (record001.inverseMaps 9) record001_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame009_links_0000 record001_frame009_links_0064)
theorem record001_frame009_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 9 :=
  of_group record001 9 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0070
    Papers.RationalityTen.SharedFrameCatalogue.group0070_facts record001_frame009_indices record001_frame009_graph record001_frame009_links
def record001_frame010_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0045.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0045.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0045.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0045.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0045.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0045.localPairCheck (smallEmbedding record001) (record001.maps 10)
      (record001.inverseMaps 10) record001_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame010_links_0000 record001_frame010_links_0064)
theorem record001_frame010_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 10 :=
  of_group record001 10 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0045
    Papers.RationalityTen.SharedFrameCatalogue.group0045_facts record001_frame010_indices record001_frame010_graph record001_frame010_links
def record001_frame011_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0032.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0032.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0032.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0032.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0032.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0032.localPairCheck (smallEmbedding record001) (record001.maps 11)
      (record001.inverseMaps 11) record001_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame011_links_0000 record001_frame011_links_0064)
theorem record001_frame011_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 11 :=
  of_group record001 11 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0032
    Papers.RationalityTen.SharedFrameCatalogue.group0032_facts record001_frame011_indices record001_frame011_graph record001_frame011_links
def record001_frame012_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0043.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0043.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0043.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0043.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0043.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0043.localPairCheck (smallEmbedding record001) (record001.maps 12)
      (record001.inverseMaps 12) record001_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame012_links_0000 record001_frame012_links_0064)
theorem record001_frame012_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 12 :=
  of_group record001 12 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0043
    Papers.RationalityTen.SharedFrameCatalogue.group0043_facts record001_frame012_indices record001_frame012_graph record001_frame012_links
def record001_frame013_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0021.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0021.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0021.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0021.localPairCheck (smallEmbedding record001) (record001.maps 13) (record001.inverseMaps 13) record001_frame013_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0021.localPairCheck (smallEmbedding record001) (record001.maps 13) (record001.inverseMaps 13) record001_frame013_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0021.localPairCheck (smallEmbedding record001) (record001.maps 13)
      (record001.inverseMaps 13) record001_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame013_links_0000 record001_frame013_links_0064)
theorem record001_frame013_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 13 :=
  of_group record001 13 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0021
    Papers.RationalityTen.SharedFrameCatalogue.group0021_facts record001_frame013_indices record001_frame013_graph record001_frame013_links
def record001_frame014_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0030.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0030.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0030.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0030.localPairCheck (smallEmbedding record001) (record001.maps 14) (record001.inverseMaps 14) record001_frame014_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0030.localPairCheck (smallEmbedding record001) (record001.maps 14) (record001.inverseMaps 14) record001_frame014_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0030.localPairCheck (smallEmbedding record001) (record001.maps 14)
      (record001.inverseMaps 14) record001_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame014_links_0000 record001_frame014_links_0064)
theorem record001_frame014_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 14 :=
  of_group record001 14 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0030
    Papers.RationalityTen.SharedFrameCatalogue.group0030_facts record001_frame014_indices record001_frame014_graph record001_frame014_links
def record001_frame015_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0007.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0007.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0007.localPairCheck (smallEmbedding record001) (record001.maps 15) (record001.inverseMaps 15) record001_frame015_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0007.localPairCheck (smallEmbedding record001) (record001.maps 15) (record001.inverseMaps 15) record001_frame015_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0007.localPairCheck (smallEmbedding record001) (record001.maps 15)
      (record001.inverseMaps 15) record001_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame015_links_0000 record001_frame015_links_0064)
theorem record001_frame015_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 15 :=
  of_group record001 15 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0007
    Papers.RationalityTen.SharedFrameCatalogue.group0007_facts record001_frame015_indices record001_frame015_graph record001_frame015_links
def record001_frame016_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0013.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0013.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0013.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0013.localPairCheck (smallEmbedding record001) (record001.maps 16) (record001.inverseMaps 16) record001_frame016_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0013.localPairCheck (smallEmbedding record001) (record001.maps 16) (record001.inverseMaps 16) record001_frame016_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0013.localPairCheck (smallEmbedding record001) (record001.maps 16)
      (record001.inverseMaps 16) record001_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame016_links_0000 record001_frame016_links_0064)
theorem record001_frame016_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 16 :=
  of_group record001 16 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0013
    Papers.RationalityTen.SharedFrameCatalogue.group0013_facts record001_frame016_indices record001_frame016_graph record001_frame016_links
def record001_frame017_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0001.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0001.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0001.localPairCheck (smallEmbedding record001) (record001.maps 17) (record001.inverseMaps 17) record001_frame017_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0001.localPairCheck (smallEmbedding record001) (record001.maps 17) (record001.inverseMaps 17) record001_frame017_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0001.localPairCheck (smallEmbedding record001) (record001.maps 17)
      (record001.inverseMaps 17) record001_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame017_links_0000 record001_frame017_links_0064)
theorem record001_frame017_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 17 :=
  of_group record001 17 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0001
    Papers.RationalityTen.SharedFrameCatalogue.group0001_facts record001_frame017_indices record001_frame017_graph record001_frame017_links
def record001_frame018_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0005.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0005.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0005.localPairCheck (smallEmbedding record001) (record001.maps 18) (record001.inverseMaps 18) record001_frame018_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0005.localPairCheck (smallEmbedding record001) (record001.maps 18) (record001.inverseMaps 18) record001_frame018_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0005.localPairCheck (smallEmbedding record001) (record001.maps 18)
      (record001.inverseMaps 18) record001_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame018_links_0000 record001_frame018_links_0064)
theorem record001_frame018_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 18 :=
  of_group record001 18 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0005
    Papers.RationalityTen.SharedFrameCatalogue.group0005_facts record001_frame018_indices record001_frame018_graph record001_frame018_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (Fin.cases (record001_frame006_supported hcells) (Fin.cases (record001_frame007_supported hcells) (Fin.cases (record001_frame008_supported hcells) (Fin.cases (record001_frame009_supported hcells) (Fin.cases (record001_frame010_supported hcells) (Fin.cases (record001_frame011_supported hcells) (Fin.cases (record001_frame012_supported hcells) (Fin.cases (record001_frame013_supported hcells) (Fin.cases (record001_frame014_supported hcells) (Fin.cases (record001_frame015_supported hcells) (Fin.cases (record001_frame016_supported hcells) (Fin.cases (record001_frame017_supported hcells) (Fin.cases (record001_frame018_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x34bda52d2368834359f4cf5674b39197ccb364db229902c70623309180abff5f62ec973eb7e5b5acbd650b00579ab815a6a9c53e299d4b6a3f509a7c13c69c04bfa56528e940483a37d1928a84491f48efe76d3ac1d24e8c74039b9c80e3671037b9bd0dd26d03549a74d086783301964ca864c31b983cbfc5ee2f11744b8257c2ab9538a9450e27913a498e4be23190ec84c4081f48f747383741b40d8464230717a8b6859025f11c88c44001f40f386dc33218f0bb05b02c814109804902300c106002f00ac05502a014009a04701600a404a01e00e807002c01300780240100070018008002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record002_frame001_links_0000 (interval_append _ 64 128 143 record002_frame001_links_0064 record002_frame001_links_0128))
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x395dc94e46713b871bf0ded6eab739b3ed8b6b9b57daa4d4668cb3a996aca1640b131870c1c60a2f5978cba05c82df96eeb2e57dab6556ca9b53ca959496a3c4f4a6dd32297d4a924b123090647f20c4fe27e73e99f08f7c7aa3c31dd8ee475e39d1ce0e6272837e1ba8d8a6b634a1a04ce066432a98ccc4060f30297fcbf25a72be9584ab0528286140c9e64ef249119c8a2438211106879839b1c00db46763201868bf85ec27812608f84242040fd07283421910ba05ac2c014309d04bc24c0cd06603240ac05502a014009a04701600a404a01e00e807002c01300780240100070018008002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record002_frame002_links_0000 (interval_append _ 64 128 143 record002_frame002_links_0064 record002_frame002_links_0128))
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1026.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1026.count (({ width := 11, code := 0x11c636c698cd18e2ec5a8ab14a254468830f61cc358630a61041b82902e033fe7f2f9df23db7b0f49e7bc4768e9dcfb9a71ae15c1b7b6d4d69a8b4c67ccd598329648b95642c3578ad5592af552a8d5029d52ea554928c50a9fd3826a4b695d2a2514968f11c2354648b915a103f67d4f99dc3ac750e61ca360664c617f2e45bcae14b28a5089912c252490909081f03cc730e11be350648c51782e05a0ad1522945188310420425049090114218410580a41281e03a0700b01301e0240400700600800800 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record002_frame003_links_0000 (interval_append _ 64 128 143 record002_frame003_links_0064 record002_frame003_links_0128))
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1026
    Papers.RationalityTen.SharedFrameCatalogue.group1026_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1031.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1031.count (({ width := 10, code := 0x391e3789e1b83df77add772dab66d875dd6755d3b4ad1740cef36cc72bc9b17c530cc2704c06fbbd2edb9ae5b7ad7b5acfb0ab6abaa9a7e97a4a8ca1e5890e3f8e6338c22d89e2287e1c85a148460b81e047edf87bdeb7a1e678dda759d3745cd729b6699a06798d61d855f97c5a15853d454f1394a51b45512414ff3f0f73d0e0358d4328c8318bd2c8ae294a1274962488e230771d8751244811c44108400ac280901e0741c0581303c090200700c0200400 } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1031.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record002_frame004_links_0000 (interval_append _ 64 128 143 record002_frame004_links_0064 record002_frame004_links_0128))
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1031
    Papers.RationalityTen.SharedFrameCatalogue.group1031_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1a5ed29691b43da14cf9678b3a19c0cbe659b26d914c816382ff9736b67597aca1600af35702b4d522a71530a96d44ca034f8274d38097f4aca51d28090746fa32515089240d1f98fa47a53bf9db4eae7483a39cf4e7471f38e1c10e026f536e9b68d5069034199accbe65a32a192cc4460d30017b8bc05d32e09678b0c5792b09550aa054a2a11468a084f8274936499a4be22f10d884c4031f48f747503801b70d8466e31617a8ba459025f11c88c44001f40f3863c2d816409804902300c106002f012c09304781580aa054028813809001e00e807002c01300780240100070018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame001_links_0000 (interval_append _ 64 128 142 record003_frame001_links_0064 record003_frame001_links_0128))
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1caee4a7233895c1adf66ef3751b92d9f6c5b5cdabed526a33275868c135eb2f19740b905bf2ddd634ae95652ad9512a6a52b29114789e94dba6452fa952496246120c8fe442213106280c3f89f9cfa47c13e01e6cf2a7753ba1d3ce927393971cacdf66d73621a98d22684338198cc8a630311983cc086002fc9760b665a22c415d0ad05582a694cca3e51328193e49ea4ef246918c8a243421110687be3ab1c80db46963301868c145ec27812608f84242040fd06442d616009d04bc24c0cd066032412c09304781580aa054028813809001e00e807002c01300780240100070018008002000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame002_links_0000 (interval_append _ 64 128 142 record003_frame002_links_0064 record003_frame002_links_0128))
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1026.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1026.count (({ width := 11, code := 0x238c6d8d319630c5c8b11522844a88d1061ec3986b06a02bf87cef91edbd87a4f3ddebad748e7dc9b8a70ae01bdb6a6b4d45a633e66acc194b24612bc572ad4590b0d5dab4566ab555aa2542a6d4ca96520a39422764de9852d2584a89412123b4728d518a2f45688d0ba0e4047e4fb9f33de78ced1d83a8740e71ca35a658c617c2e45bcb014f2905089b12f25249c909081f03cc730e11be3145c0b4152294518831042043a0710da1282484808c1102101e03a0700b01301e0240400700600800800 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame003_links_0000 (interval_append _ 64 128 142 record003_frame003_links_0064 record003_frame003_links_0128))
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1026
    Papers.RationalityTen.SharedFrameCatalogue.group1026_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
def record003_frame004_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1031.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1031.count (({ width := 10, code := 0xe478de2785e077cde374dc36ad9b61d7759d573fcc325c5f14c3309c1301be2f1baae6b8adbb5ed3b3ec2adaaeaa69fa5e92a32879ca619624c90e3f8e2328c62b8a6218821a8621583e0d819ff7e9f37b9ec7a1e5779d975dd3741ce729c46f1b46b1a46899e66d9362d89615826017c5995653d434f1394b51f46112425023f0fa3d0e0358d4328c8318ae2849d2488e230771d8751bc6c1a04912047114431041e0741c0581303c090200700c0200400 } : Fields).get c.val)
theorem record003_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1031.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record003) (record003.maps 4)
      (record003.inverseMaps 4) record003_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame004_links_0000 (interval_append _ 64 128 142 record003_frame004_links_0064 record003_frame004_links_0128))
theorem record003_frame004_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 4 :=
  of_group record003 4 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1031
    Papers.RationalityTen.SharedFrameCatalogue.group1031_facts record003_frame004_indices record003_frame004_graph record003_frame004_links
def record003_frame005_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1019.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1019.count (({ width := 9, code := 0x2632f96cb2552993c9a492391486411f8f462270f87436190b854260f0480bfdfafa7c3d9e8f277bb1d4e872b8dc2df6f371b4d96bb59a6d067b3598c863b1588c2602fd7aba5c2d566b157ab956a953a9548a25027d3a9a4c255269047a35148842a11047f3d1d4e66f369b0d46631980bc5b2c15ca84e251248a44218ec6c35180bc5c2d160ac5429140984a24118843e12088401a0b0481c0c05018080200 } : Fields).get c.val)
theorem record003_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1019.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1019.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1019.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1019.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1019.localPairCheck (smallEmbedding record003) (record003.maps 5)
      (record003.inverseMaps 5) record003_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame005_links_0000 (interval_append _ 64 128 142 record003_frame005_links_0064 record003_frame005_links_0128))
theorem record003_frame005_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 5 :=
  of_group record003 5 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1019
    Papers.RationalityTen.SharedFrameCatalogue.group1019_facts record003_frame005_indices record003_frame005_graph record003_frame005_links
def record003_frame006_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1e2af0d7833b99da8ebd7543a65cf0e2670a37f5bd0dd96dc34e1a1ccf9659b2918d6c58616b05572eb5e59dac915e6ac95592a394f4a2b4f9273d3709874aea51924490e46822ed15e89f449a2310ee862430a10507681940b9fd8fe67e43df1edcec47423971c3cdf26ec36c9b2cd5669334319d0cc265131d9834bda5d92dd1690b2e5842bb1558a7c53128f94309f84e6255125491247a23811a88563e71df0e446ce34318b8c185b026a11d88b43fe1f20f2061c2b014a08e043c2020d1068033012c09304781580aa054028813809001e00e807002c01300780240100070018008002000 } : Fields).get c.val)
theorem record003_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 6)
      (record003.inverseMaps 6) record003_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame006_links_0000 (interval_append _ 64 128 142 record003_frame006_links_0064 record003_frame006_links_0128))
theorem record003_frame006_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 6 :=
  of_group record003 6 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record003_frame006_indices record003_frame006_graph record003_frame006_links
def record003_frame007_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x73072d72a72271c7127076ff6fb6e36dd6d46d06cb6c068966564f63562f62161c60f60a5df5ce5c35bc5a258b57d56a55c54153152151a5004e74d94ca4bc49047c47246545945344c44744643c43842c42b41d41b4144064043e33d63c93c03b83b43ad3a839237e37736b35f35834e33532c3253183093052fe2f92e32cf2c82be2b02a929d27125e25524823d23721e2051f91ee1d91c91b41ae19916d15c15813f13a1341060f90f60dd0d60d20b70b60b209208f08b05405305204f04c04601e01d01c01601300f009008007003002001000 } : Fields).get c.val)
theorem record003_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record003) (record003.maps 7)
      (record003.inverseMaps 7) record003_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame007_links_0000 (interval_append _ 64 128 142 record003_frame007_links_0064 record003_frame007_links_0128))
theorem record003_frame007_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 7 :=
  of_group record003 7 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record003_frame007_indices record003_frame007_graph record003_frame007_links
def record003_frame008_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x8da8d58cf8b88ad8a089a89388886b86585984e8438387ef7c97b879e79478277876b76473170e6f56e46cd6bc6ad6a069867365764663761a6015f05e25da5b259c59158057556f56855c55b54854453253151e51a5135085044e14cd4bf4ac49c49348447946b45c45444543a43442c4184043f63e83d93d13c23b73a439438b37c37136b36333b32631c30b3012fb2e02b82a02802602482282232151c51ab1a318617e17712f11310b0f20ea0e10bf0be0bc09609308f05605505405104e04801e01d01c01601300f009008007003002001000 } : Fields).get c.val)
theorem record003_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record003) (record003.maps 8)
      (record003.inverseMaps 8) record003_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame008_links_0000 (interval_append _ 64 128 142 record003_frame008_links_0064 record003_frame008_links_0128))
theorem record003_frame008_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 8 :=
  of_group record003 8 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record003_frame008_indices record003_frame008_graph record003_frame008_links
def record003_frame009_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1024.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1024.count (({ width := 10, code := 0x8420d82a0981e0580e017fdfd7edf97ddf57cded7a1e476dd874dd0731c9711be6e9b76c9ae6ada8695a06699664d8e62987611815e5725b968591615755a565535454d53146511424f13a4dd344c52e4ad2a499244851e4751945d164490f4310941903408fe3f0f93d8f53c4ef3b8ea380d9354cf32cc8304ba2dcb22aca828ca026c90224872047f1f8741b46b194631885815c561304a120390e0370d8350cc1b06819050110340801c0600c0200400 } : Fields).get c.val)
theorem record003_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1024.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1024.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1024.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1024.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1024.localPairCheck (smallEmbedding record003) (record003.maps 9)
      (record003.inverseMaps 9) record003_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame009_links_0000 (interval_append _ 64 128 142 record003_frame009_links_0064 record003_frame009_links_0128))
theorem record003_frame009_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 9 :=
  of_group record003 9 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1024
    Papers.RationalityTen.SharedFrameCatalogue.group1024_facts record003_frame009_indices record003_frame009_graph record003_frame009_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (Fin.cases (record003_frame005_supported hcells) (Fin.cases (record003_frame006_supported hcells) (Fin.cases (record003_frame007_supported hcells) (Fin.cases (record003_frame008_supported hcells) (Fin.cases (record003_frame009_supported hcells) (fun j => Fin.elim0 j)))))))))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x71070e70a7067026f86f36f26ef6ee6ec6e76e46e36e16d16cd6bc6b16ad69568167d67266d65c65164f64c64864663a63963563361c6145f95f65e55cf5c55b45af5a75505204ae47a46e45545244243f3fe3f33c93be3b23ac38c37436c35f35334133733631a3022e12d52c22b02a928026025524d23822021b2121e01c41a119b17a16d16412410a1070ef0e40e10c10b50a609e09c09b09a09609409008d08a08208007a07707406a06602b02802301d01c01601300e008007 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x7377307227187107047037026f76f36f26e76e06df6d86c36be6af6a86a768f67d67c66e66d65764e64c64663c63a6296266166145f75ee5d75d45c45b059f59859058953e50449747346e44d44742a41e3d03c439a39538c38736134633e3323263103053002e22d12b92ae2a329729426524123823020f1f81f21e51b71a718b1851701661621241051020e80e00dd0c20bb0b40af0ad0ac0a80a40a109c09a09408e08a08207f07706e06a02b02802301d01c01601300e008007 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame002_links_0000 record004_frame002_links_0064)
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0940.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0940.count (({ width := 8, code := 0xe4e2e0dedcdbdad9d7d6d5d4d2d1d0cfcecdcbcac9c7c6c4c3c2c1c0bfbdbcbbbab8b7b6b5b4b3b1b0afadacaaa9a7a5a3a19c9a96948e8c89878583807d7b78777371706d6a666462605f5c595755534f4e4c494642413e3d3c3b3a3937353432302e2d2c2b2a292827262524232221201f1e0e0d0c0b0a0908070605 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0940.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0940.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0940.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0940.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame003_links_0000 record004_frame003_links_0064)
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0940
    Papers.RationalityTen.SharedFrameCatalogue.group0940_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
def record004_frame004_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0892.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0892.count (({ width := 8, code := 0xe4e2e0dedcdbdad9d7d6d5d4d2d1d0cfcecdcbcac9c7c6c4c3c2c1c0bfbdbcbbbab8b7b6b5b4b3b1b0afadacaaa9a7a5a3a19c9a96948e8c89878583807d7b78777371706d6a666462605f5c595755534f4e4c494642413e3d3c3b3a3937353432302e2d2c2b2a292827262524232221201f1e0e0d0c0b0a0908070605 } : Fields).get c.val)
theorem record004_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0892.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0892.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0892.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0892.localPairCheck (smallEmbedding record004) (record004.maps 4)
      (record004.inverseMaps 4) record004_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame004_links_0000 record004_frame004_links_0064)
theorem record004_frame004_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 4 :=
  of_group record004 4 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0892
    Papers.RationalityTen.SharedFrameCatalogue.group0892_facts record004_frame004_indices record004_frame004_graph record004_frame004_links
def record004_frame005_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0900.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0900.count (({ width := 8, code := 0xe4e2e0dedcdbdad9d7d6d5d4d2d1d0cfcecdcbcac9c7c6c4c3c2c1c0bfbdbcbbbab8b7b6b5b4b3b1b0afadacaaa9a7a5a3a19c9a96948e8c89878583807d7b78777371706d6a666462605f5c595755534f4e4c494642413e3d3c3b3a3937353432302e2d2c2b2a292827262524232221201f1e0e0d0c0b0a0908070605 } : Fields).get c.val)
theorem record004_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0900.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0900.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0900.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0900.localPairCheck (smallEmbedding record004) (record004.maps 5)
      (record004.inverseMaps 5) record004_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame005_links_0000 record004_frame005_links_0064)
theorem record004_frame005_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 5 :=
  of_group record004 5 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0900
    Papers.RationalityTen.SharedFrameCatalogue.group0900_facts record004_frame005_indices record004_frame005_graph record004_frame005_links
def record004_frame006_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0880.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0880.count (({ width := 8, code := 0xe4e2e0dedcdbdad9d7d6d5d4d2d1d0cfcecdcbcac9c7c6c4c3c2c1c0bfbdbcbbbab8b7b6b5b4b3b1b0afadacaaa9a7a5a3a19c9a96948e8c89878583807d7b78777371706d6a666462605f5c595755534f4e4c494642413e3d3c3b3a3937353432302e2d2c2b2a292827262524232221201f1e0e0d0c0b0a0908070605 } : Fields).get c.val)
theorem record004_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0880.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0880.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0880.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0880.localPairCheck (smallEmbedding record004) (record004.maps 6)
      (record004.inverseMaps 6) record004_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame006_links_0000 record004_frame006_links_0064)
theorem record004_frame006_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 6 :=
  of_group record004 6 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0880
    Papers.RationalityTen.SharedFrameCatalogue.group0880_facts record004_frame006_indices record004_frame006_graph record004_frame006_links
def record004_frame007_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0884.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0884.count (({ width := 8, code := 0xe4e2e0dedcdbdad9d7d6d5d4d2d1d0cfcecdcbcac9c7c6c4c3c2c1c0bfbdbcbbbab8b7b6b5b4b3b1b0afadacaaa9a7a5a3a19c9a96948e8c89878583807d7b78777371706d6a666462605f5c595755534f4e4c494642413e3d3c3b3a3937353432302e2d2c2b2a292827262524232221201f1e0e0d0c0b0a0908070605 } : Fields).get c.val)
theorem record004_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0884.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0884.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0884.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0884.localPairCheck (smallEmbedding record004) (record004.maps 7)
      (record004.inverseMaps 7) record004_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame007_links_0000 record004_frame007_links_0064)
theorem record004_frame007_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 7 :=
  of_group record004 7 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0884
    Papers.RationalityTen.SharedFrameCatalogue.group0884_facts record004_frame007_indices record004_frame007_graph record004_frame007_links
def record004_frame008_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0879.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0879.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0879.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0879.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0879.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0879.localPairCheck (smallEmbedding record004) (record004.maps 8)
      (record004.inverseMaps 8) record004_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame008_links_0000 record004_frame008_links_0064)
theorem record004_frame008_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 8 :=
  of_group record004 8 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0879
    Papers.RationalityTen.SharedFrameCatalogue.group0879_facts record004_frame008_indices record004_frame008_graph record004_frame008_links
def record004_frame009_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x60dc17802fc5f4bd97aaf4de3bc377eecdd4ba774adddb8b616aed5590af95e6b1d5da8b50ea153fa754e299531a594ae8a511a1342281ce99b933a60cb68f516200bdb7a8f1de13b7766e09beb5068ccc993afd5dcb9d6b2ca574ab153a834ea95523a3343484cff1ef3d076ce59b7362694c09732a65309791f2303dc730e21a2328638b71642a8528a41462784d097124240460820fe1e43b8720d2194158280460740e01602603804007 } : Fields).get c.val)
theorem record004_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record004) (record004.maps 9)
      (record004.inverseMaps 9) record004_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame009_links_0000 record004_frame009_links_0064)
theorem record004_frame009_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 9 :=
  of_group record004 9 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record004_frame009_indices record004_frame009_graph record004_frame009_links
def record004_frame010_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0x5d0b9b716de5b8b5f6b6d65a9b5169ed1da1b4167ac4586af95cab7d5eaa353a9e538a4b48a90d1fa3946e8cd18a2b4527f4fb9e73c272cd39932fa5b4ae8b50a5e639f72ae21c13796eacdd96b075febc5762cd580ae956aa4522a113fa634a68d915a174007e4f11cb3866e4d619f33a644b996428c504921182263c06f0dd1943005f8ae1522884f09d13826c4b094120238458831001ec3c8760da1a8158280460740e01602603804007 } : Fields).get c.val)
theorem record004_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record004) (record004.maps 10)
      (record004.inverseMaps 10) record004_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame010_links_0000 record004_frame010_links_0064)
theorem record004_frame010_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 10 :=
  of_group record004 10 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record004_frame010_indices record004_frame010_graph record004_frame010_links
def record004_frame011_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0589.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0589.count (({ width := 11, code := 0x4458871021ec398650c61842d8590ae1542584708a0b41581f03205bfb7e4fc1f23e179ef39e6bcb792f21e33c577eef9d7bae752ea1d1b9871ee25c0b7c6a0c9d63aa2534a394628950e9d13925b4ac93524a3345a8a90ea16416819019ee3c4734e01b535068ccc18f312604ba1622b85509e9322484888990a20c390698d11802e45c0a61422684b09512824c4788b1122204207d0f21d43a06f0d0194150270440700d81602603804007 } : Fields).get c.val)
theorem record004_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0589.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record004) (record004.maps 11)
      (record004.inverseMaps 11) record004_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame011_links_0000 record004_frame011_links_0064)
theorem record004_frame011_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 11 :=
  of_group record004 11 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0589
    Papers.RationalityTen.SharedFrameCatalogue.group0589_facts record004_frame011_indices record004_frame011_graph record004_frame011_links
def record004_frame012_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0501.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0501.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0501.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0501.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0501.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0501.localPairCheck (smallEmbedding record004) (record004.maps 12)
      (record004.inverseMaps 12) record004_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame012_links_0000 record004_frame012_links_0064)
theorem record004_frame012_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 12 :=
  of_group record004 12 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0501
    Papers.RationalityTen.SharedFrameCatalogue.group0501_facts record004_frame012_indices record004_frame012_graph record004_frame012_links
def record004_frame013_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0510.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0510.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0510.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0510.localPairCheck (smallEmbedding record004) (record004.maps 13) (record004.inverseMaps 13) record004_frame013_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0510.localPairCheck (smallEmbedding record004) (record004.maps 13) (record004.inverseMaps 13) record004_frame013_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0510.localPairCheck (smallEmbedding record004) (record004.maps 13)
      (record004.inverseMaps 13) record004_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame013_links_0000 record004_frame013_links_0064)
theorem record004_frame013_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 13 :=
  of_group record004 13 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0510
    Papers.RationalityTen.SharedFrameCatalogue.group0510_facts record004_frame013_indices record004_frame013_graph record004_frame013_links
def record004_frame014_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0482.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0482.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0482.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0482.localPairCheck (smallEmbedding record004) (record004.maps 14) (record004.inverseMaps 14) record004_frame014_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0482.localPairCheck (smallEmbedding record004) (record004.maps 14) (record004.inverseMaps 14) record004_frame014_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0482.localPairCheck (smallEmbedding record004) (record004.maps 14)
      (record004.inverseMaps 14) record004_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame014_links_0000 record004_frame014_links_0064)
theorem record004_frame014_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 14 :=
  of_group record004 14 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0482
    Papers.RationalityTen.SharedFrameCatalogue.group0482_facts record004_frame014_indices record004_frame014_graph record004_frame014_links
def record004_frame015_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0463.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0463.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0463.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0463.localPairCheck (smallEmbedding record004) (record004.maps 15) (record004.inverseMaps 15) record004_frame015_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0463.localPairCheck (smallEmbedding record004) (record004.maps 15) (record004.inverseMaps 15) record004_frame015_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0463.localPairCheck (smallEmbedding record004) (record004.maps 15)
      (record004.inverseMaps 15) record004_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame015_links_0000 record004_frame015_links_0064)
theorem record004_frame015_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 15 :=
  of_group record004 15 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0463
    Papers.RationalityTen.SharedFrameCatalogue.group0463_facts record004_frame015_indices record004_frame015_graph record004_frame015_links
def record004_frame016_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0462.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0462.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0462.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0462.localPairCheck (smallEmbedding record004) (record004.maps 16) (record004.inverseMaps 16) record004_frame016_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0462.localPairCheck (smallEmbedding record004) (record004.maps 16) (record004.inverseMaps 16) record004_frame016_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0462.localPairCheck (smallEmbedding record004) (record004.maps 16)
      (record004.inverseMaps 16) record004_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame016_links_0000 record004_frame016_links_0064)
theorem record004_frame016_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 16 :=
  of_group record004 16 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0462
    Papers.RationalityTen.SharedFrameCatalogue.group0462_facts record004_frame016_indices record004_frame016_graph record004_frame016_links
def record004_frame017_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0669.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0669.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0669.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0669.localPairCheck (smallEmbedding record004) (record004.maps 17) (record004.inverseMaps 17) record004_frame017_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0669.localPairCheck (smallEmbedding record004) (record004.maps 17) (record004.inverseMaps 17) record004_frame017_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0669.localPairCheck (smallEmbedding record004) (record004.maps 17)
      (record004.inverseMaps 17) record004_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame017_links_0000 record004_frame017_links_0064)
theorem record004_frame017_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 17 :=
  of_group record004 17 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0669
    Papers.RationalityTen.SharedFrameCatalogue.group0669_facts record004_frame017_indices record004_frame017_graph record004_frame017_links
def record004_frame018_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0667.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0667.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0667.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0667.localPairCheck (smallEmbedding record004) (record004.maps 18) (record004.inverseMaps 18) record004_frame018_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0667.localPairCheck (smallEmbedding record004) (record004.maps 18) (record004.inverseMaps 18) record004_frame018_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0667.localPairCheck (smallEmbedding record004) (record004.maps 18)
      (record004.inverseMaps 18) record004_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame018_links_0000 record004_frame018_links_0064)
theorem record004_frame018_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 18 :=
  of_group record004 18 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0667
    Papers.RationalityTen.SharedFrameCatalogue.group0667_facts record004_frame018_indices record004_frame018_graph record004_frame018_links
def record004_frame019_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0668.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0668.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0668.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0668.localPairCheck (smallEmbedding record004) (record004.maps 19) (record004.inverseMaps 19) record004_frame019_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0668.localPairCheck (smallEmbedding record004) (record004.maps 19) (record004.inverseMaps 19) record004_frame019_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0668.localPairCheck (smallEmbedding record004) (record004.maps 19)
      (record004.inverseMaps 19) record004_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame019_links_0000 record004_frame019_links_0064)
theorem record004_frame019_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 19 :=
  of_group record004 19 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0668
    Papers.RationalityTen.SharedFrameCatalogue.group0668_facts record004_frame019_indices record004_frame019_graph record004_frame019_links
def record004_frame020_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0666.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0666.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0666.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0666.localPairCheck (smallEmbedding record004) (record004.maps 20) (record004.inverseMaps 20) record004_frame020_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0666.localPairCheck (smallEmbedding record004) (record004.maps 20) (record004.inverseMaps 20) record004_frame020_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0666.localPairCheck (smallEmbedding record004) (record004.maps 20)
      (record004.inverseMaps 20) record004_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame020_links_0000 record004_frame020_links_0064)
theorem record004_frame020_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 20 :=
  of_group record004 20 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0666
    Papers.RationalityTen.SharedFrameCatalogue.group0666_facts record004_frame020_indices record004_frame020_graph record004_frame020_links
def record004_frame021_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0663.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0663.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0663.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0663.localPairCheck (smallEmbedding record004) (record004.maps 21) (record004.inverseMaps 21) record004_frame021_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0663.localPairCheck (smallEmbedding record004) (record004.maps 21) (record004.inverseMaps 21) record004_frame021_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0663.localPairCheck (smallEmbedding record004) (record004.maps 21)
      (record004.inverseMaps 21) record004_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame021_links_0000 record004_frame021_links_0064)
theorem record004_frame021_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 21 :=
  of_group record004 21 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0663
    Papers.RationalityTen.SharedFrameCatalogue.group0663_facts record004_frame021_indices record004_frame021_graph record004_frame021_links
def record004_frame022_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0662.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0662.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0662.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0662.localPairCheck (smallEmbedding record004) (record004.maps 22) (record004.inverseMaps 22) record004_frame022_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0662.localPairCheck (smallEmbedding record004) (record004.maps 22) (record004.inverseMaps 22) record004_frame022_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0662.localPairCheck (smallEmbedding record004) (record004.maps 22)
      (record004.inverseMaps 22) record004_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame022_links_0000 record004_frame022_links_0064)
theorem record004_frame022_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 22 :=
  of_group record004 22 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0662
    Papers.RationalityTen.SharedFrameCatalogue.group0662_facts record004_frame022_indices record004_frame022_graph record004_frame022_links
def record004_frame023_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0029.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0029.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0029.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0029.localPairCheck (smallEmbedding record004) (record004.maps 23) (record004.inverseMaps 23) record004_frame023_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0029.localPairCheck (smallEmbedding record004) (record004.maps 23) (record004.inverseMaps 23) record004_frame023_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0029.localPairCheck (smallEmbedding record004) (record004.maps 23)
      (record004.inverseMaps 23) record004_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame023_links_0000 record004_frame023_links_0064)
theorem record004_frame023_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 23 :=
  of_group record004 23 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0029
    Papers.RationalityTen.SharedFrameCatalogue.group0029_facts record004_frame023_indices record004_frame023_graph record004_frame023_links
def record004_frame024_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0027.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0027.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0027.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0027.localPairCheck (smallEmbedding record004) (record004.maps 24) (record004.inverseMaps 24) record004_frame024_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0027.localPairCheck (smallEmbedding record004) (record004.maps 24) (record004.inverseMaps 24) record004_frame024_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0027.localPairCheck (smallEmbedding record004) (record004.maps 24)
      (record004.inverseMaps 24) record004_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame024_links_0000 record004_frame024_links_0064)
theorem record004_frame024_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 24 :=
  of_group record004 24 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0027
    Papers.RationalityTen.SharedFrameCatalogue.group0027_facts record004_frame024_indices record004_frame024_graph record004_frame024_links
def record004_frame025_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0026.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0026.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0026.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0026.localPairCheck (smallEmbedding record004) (record004.maps 25) (record004.inverseMaps 25) record004_frame025_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0026.localPairCheck (smallEmbedding record004) (record004.maps 25) (record004.inverseMaps 25) record004_frame025_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0026.localPairCheck (smallEmbedding record004) (record004.maps 25)
      (record004.inverseMaps 25) record004_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame025_links_0000 record004_frame025_links_0064)
theorem record004_frame025_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 25 :=
  of_group record004 25 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0026
    Papers.RationalityTen.SharedFrameCatalogue.group0026_facts record004_frame025_indices record004_frame025_graph record004_frame025_links
def record004_frame026_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0386.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0386.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0386.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0386.localPairCheck (smallEmbedding record004) (record004.maps 26) (record004.inverseMaps 26) record004_frame026_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0386.localPairCheck (smallEmbedding record004) (record004.maps 26) (record004.inverseMaps 26) record004_frame026_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0386.localPairCheck (smallEmbedding record004) (record004.maps 26)
      (record004.inverseMaps 26) record004_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame026_links_0000 record004_frame026_links_0064)
theorem record004_frame026_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 26 :=
  of_group record004 26 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0386
    Papers.RationalityTen.SharedFrameCatalogue.group0386_facts record004_frame026_indices record004_frame026_graph record004_frame026_links
def record004_frame027_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0384.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0384.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame027_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0384.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame027_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0384.localPairCheck (smallEmbedding record004) (record004.maps 27) (record004.inverseMaps 27) record004_frame027_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame027_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0384.localPairCheck (smallEmbedding record004) (record004.maps 27) (record004.inverseMaps 27) record004_frame027_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame027_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0384.localPairCheck (smallEmbedding record004) (record004.maps 27)
      (record004.inverseMaps 27) record004_frame027_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame027_links_0000 record004_frame027_links_0064)
theorem record004_frame027_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 27 :=
  of_group record004 27 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0384
    Papers.RationalityTen.SharedFrameCatalogue.group0384_facts record004_frame027_indices record004_frame027_graph record004_frame027_links
def record004_frame028_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0010.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0010.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame028_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0010.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame028_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0010.localPairCheck (smallEmbedding record004) (record004.maps 28) (record004.inverseMaps 28) record004_frame028_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame028_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0010.localPairCheck (smallEmbedding record004) (record004.maps 28) (record004.inverseMaps 28) record004_frame028_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame028_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0010.localPairCheck (smallEmbedding record004) (record004.maps 28)
      (record004.inverseMaps 28) record004_frame028_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame028_links_0000 record004_frame028_links_0064)
theorem record004_frame028_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 28 :=
  of_group record004 28 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0010
    Papers.RationalityTen.SharedFrameCatalogue.group0010_facts record004_frame028_indices record004_frame028_graph record004_frame028_links
def record004_frame029_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0009.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0009.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame029_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0009.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame029_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0009.localPairCheck (smallEmbedding record004) (record004.maps 29) (record004.inverseMaps 29) record004_frame029_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame029_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0009.localPairCheck (smallEmbedding record004) (record004.maps 29) (record004.inverseMaps 29) record004_frame029_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame029_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0009.localPairCheck (smallEmbedding record004) (record004.maps 29)
      (record004.inverseMaps 29) record004_frame029_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame029_links_0000 record004_frame029_links_0064)
theorem record004_frame029_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 29 :=
  of_group record004 29 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0009
    Papers.RationalityTen.SharedFrameCatalogue.group0009_facts record004_frame029_indices record004_frame029_graph record004_frame029_links
def record004_frame030_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0008.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0008.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame030_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0008.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame030_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0008.localPairCheck (smallEmbedding record004) (record004.maps 30) (record004.inverseMaps 30) record004_frame030_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame030_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0008.localPairCheck (smallEmbedding record004) (record004.maps 30) (record004.inverseMaps 30) record004_frame030_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame030_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0008.localPairCheck (smallEmbedding record004) (record004.maps 30)
      (record004.inverseMaps 30) record004_frame030_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame030_links_0000 record004_frame030_links_0064)
theorem record004_frame030_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 30 :=
  of_group record004 30 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0008
    Papers.RationalityTen.SharedFrameCatalogue.group0008_facts record004_frame030_indices record004_frame030_graph record004_frame030_links
def record004_frame031_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0236.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0236.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame031_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0236.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame031_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0236.localPairCheck (smallEmbedding record004) (record004.maps 31) (record004.inverseMaps 31) record004_frame031_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame031_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0236.localPairCheck (smallEmbedding record004) (record004.maps 31) (record004.inverseMaps 31) record004_frame031_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame031_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0236.localPairCheck (smallEmbedding record004) (record004.maps 31)
      (record004.inverseMaps 31) record004_frame031_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame031_links_0000 record004_frame031_links_0064)
theorem record004_frame031_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 31 :=
  of_group record004 31 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0236
    Papers.RationalityTen.SharedFrameCatalogue.group0236_facts record004_frame031_indices record004_frame031_graph record004_frame031_links
def record004_frame032_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0235.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0235.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame032_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0235.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame032_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0235.localPairCheck (smallEmbedding record004) (record004.maps 32) (record004.inverseMaps 32) record004_frame032_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame032_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0235.localPairCheck (smallEmbedding record004) (record004.maps 32) (record004.inverseMaps 32) record004_frame032_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame032_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0235.localPairCheck (smallEmbedding record004) (record004.maps 32)
      (record004.inverseMaps 32) record004_frame032_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame032_links_0000 record004_frame032_links_0064)
theorem record004_frame032_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 32 :=
  of_group record004 32 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0235
    Papers.RationalityTen.SharedFrameCatalogue.group0235_facts record004_frame032_indices record004_frame032_graph record004_frame032_links
def record004_frame033_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0218.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0218.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame033_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0218.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame033_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0218.localPairCheck (smallEmbedding record004) (record004.maps 33) (record004.inverseMaps 33) record004_frame033_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame033_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0218.localPairCheck (smallEmbedding record004) (record004.maps 33) (record004.inverseMaps 33) record004_frame033_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame033_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0218.localPairCheck (smallEmbedding record004) (record004.maps 33)
      (record004.inverseMaps 33) record004_frame033_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame033_links_0000 record004_frame033_links_0064)
theorem record004_frame033_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 33 :=
  of_group record004 33 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0218
    Papers.RationalityTen.SharedFrameCatalogue.group0218_facts record004_frame033_indices record004_frame033_graph record004_frame033_links
def record004_frame034_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0217.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0217.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame034_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0217.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame034_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0217.localPairCheck (smallEmbedding record004) (record004.maps 34) (record004.inverseMaps 34) record004_frame034_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame034_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0217.localPairCheck (smallEmbedding record004) (record004.maps 34) (record004.inverseMaps 34) record004_frame034_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame034_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0217.localPairCheck (smallEmbedding record004) (record004.maps 34)
      (record004.inverseMaps 34) record004_frame034_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame034_links_0000 record004_frame034_links_0064)
theorem record004_frame034_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 34 :=
  of_group record004 34 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0217
    Papers.RationalityTen.SharedFrameCatalogue.group0217_facts record004_frame034_indices record004_frame034_graph record004_frame034_links
def record004_frame035_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0215.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0215.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame035_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0215.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame035_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0215.localPairCheck (smallEmbedding record004) (record004.maps 35) (record004.inverseMaps 35) record004_frame035_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame035_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0215.localPairCheck (smallEmbedding record004) (record004.maps 35) (record004.inverseMaps 35) record004_frame035_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame035_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0215.localPairCheck (smallEmbedding record004) (record004.maps 35)
      (record004.inverseMaps 35) record004_frame035_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame035_links_0000 record004_frame035_links_0064)
theorem record004_frame035_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 35 :=
  of_group record004 35 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0215
    Papers.RationalityTen.SharedFrameCatalogue.group0215_facts record004_frame035_indices record004_frame035_graph record004_frame035_links
def record004_frame036_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0216.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0216.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame036_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0216.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame036_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0216.localPairCheck (smallEmbedding record004) (record004.maps 36) (record004.inverseMaps 36) record004_frame036_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame036_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0216.localPairCheck (smallEmbedding record004) (record004.maps 36) (record004.inverseMaps 36) record004_frame036_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame036_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0216.localPairCheck (smallEmbedding record004) (record004.maps 36)
      (record004.inverseMaps 36) record004_frame036_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame036_links_0000 record004_frame036_links_0064)
theorem record004_frame036_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 36 :=
  of_group record004 36 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0216
    Papers.RationalityTen.SharedFrameCatalogue.group0216_facts record004_frame036_indices record004_frame036_graph record004_frame036_links
def record004_frame037_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0138.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0138.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame037_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0138.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame037_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0138.localPairCheck (smallEmbedding record004) (record004.maps 37) (record004.inverseMaps 37) record004_frame037_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame037_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0138.localPairCheck (smallEmbedding record004) (record004.maps 37) (record004.inverseMaps 37) record004_frame037_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame037_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0138.localPairCheck (smallEmbedding record004) (record004.maps 37)
      (record004.inverseMaps 37) record004_frame037_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame037_links_0000 record004_frame037_links_0064)
theorem record004_frame037_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 37 :=
  of_group record004 37 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0138
    Papers.RationalityTen.SharedFrameCatalogue.group0138_facts record004_frame037_indices record004_frame037_graph record004_frame037_links
def record004_frame038_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0115.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame038_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame038_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0115.localPairCheck (smallEmbedding record004) (record004.maps 38) (record004.inverseMaps 38) record004_frame038_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame038_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0115.localPairCheck (smallEmbedding record004) (record004.maps 38) (record004.inverseMaps 38) record004_frame038_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame038_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0115.localPairCheck (smallEmbedding record004) (record004.maps 38)
      (record004.inverseMaps 38) record004_frame038_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame038_links_0000 record004_frame038_links_0064)
theorem record004_frame038_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 38 :=
  of_group record004 38 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0115
    Papers.RationalityTen.SharedFrameCatalogue.group0115_facts record004_frame038_indices record004_frame038_graph record004_frame038_links
def record004_frame039_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0137.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0137.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame039_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0137.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame039_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0137.localPairCheck (smallEmbedding record004) (record004.maps 39) (record004.inverseMaps 39) record004_frame039_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame039_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0137.localPairCheck (smallEmbedding record004) (record004.maps 39) (record004.inverseMaps 39) record004_frame039_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame039_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0137.localPairCheck (smallEmbedding record004) (record004.maps 39)
      (record004.inverseMaps 39) record004_frame039_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame039_links_0000 record004_frame039_links_0064)
theorem record004_frame039_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 39 :=
  of_group record004 39 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0137
    Papers.RationalityTen.SharedFrameCatalogue.group0137_facts record004_frame039_indices record004_frame039_graph record004_frame039_links
def record004_frame040_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0112.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame040_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0112.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame040_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0112.localPairCheck (smallEmbedding record004) (record004.maps 40) (record004.inverseMaps 40) record004_frame040_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame040_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0112.localPairCheck (smallEmbedding record004) (record004.maps 40) (record004.inverseMaps 40) record004_frame040_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame040_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0112.localPairCheck (smallEmbedding record004) (record004.maps 40)
      (record004.inverseMaps 40) record004_frame040_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame040_links_0000 record004_frame040_links_0064)
theorem record004_frame040_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 40 :=
  of_group record004 40 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0112
    Papers.RationalityTen.SharedFrameCatalogue.group0112_facts record004_frame040_indices record004_frame040_graph record004_frame040_links
def record004_frame041_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0114.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame041_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0114.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame041_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0114.localPairCheck (smallEmbedding record004) (record004.maps 41) (record004.inverseMaps 41) record004_frame041_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame041_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0114.localPairCheck (smallEmbedding record004) (record004.maps 41) (record004.inverseMaps 41) record004_frame041_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame041_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0114.localPairCheck (smallEmbedding record004) (record004.maps 41)
      (record004.inverseMaps 41) record004_frame041_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame041_links_0000 record004_frame041_links_0064)
theorem record004_frame041_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 41 :=
  of_group record004 41 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0114
    Papers.RationalityTen.SharedFrameCatalogue.group0114_facts record004_frame041_indices record004_frame041_graph record004_frame041_links
def record004_frame042_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0111.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0111.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame042_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0111.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame042_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0111.localPairCheck (smallEmbedding record004) (record004.maps 42) (record004.inverseMaps 42) record004_frame042_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame042_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0111.localPairCheck (smallEmbedding record004) (record004.maps 42) (record004.inverseMaps 42) record004_frame042_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame042_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0111.localPairCheck (smallEmbedding record004) (record004.maps 42)
      (record004.inverseMaps 42) record004_frame042_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame042_links_0000 record004_frame042_links_0064)
theorem record004_frame042_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 42 :=
  of_group record004 42 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0111
    Papers.RationalityTen.SharedFrameCatalogue.group0111_facts record004_frame042_indices record004_frame042_graph record004_frame042_links
def record004_frame043_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0110.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame043_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0110.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame043_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0110.localPairCheck (smallEmbedding record004) (record004.maps 43) (record004.inverseMaps 43) record004_frame043_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame043_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0110.localPairCheck (smallEmbedding record004) (record004.maps 43) (record004.inverseMaps 43) record004_frame043_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame043_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0110.localPairCheck (smallEmbedding record004) (record004.maps 43)
      (record004.inverseMaps 43) record004_frame043_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame043_links_0000 record004_frame043_links_0064)
theorem record004_frame043_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 43 :=
  of_group record004 43 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0110
    Papers.RationalityTen.SharedFrameCatalogue.group0110_facts record004_frame043_indices record004_frame043_graph record004_frame043_links
def record004_frame044_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0214.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0214.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame044_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0214.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame044_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0214.localPairCheck (smallEmbedding record004) (record004.maps 44) (record004.inverseMaps 44) record004_frame044_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame044_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0214.localPairCheck (smallEmbedding record004) (record004.maps 44) (record004.inverseMaps 44) record004_frame044_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame044_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0214.localPairCheck (smallEmbedding record004) (record004.maps 44)
      (record004.inverseMaps 44) record004_frame044_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame044_links_0000 record004_frame044_links_0064)
theorem record004_frame044_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 44 :=
  of_group record004 44 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0214
    Papers.RationalityTen.SharedFrameCatalogue.group0214_facts record004_frame044_indices record004_frame044_graph record004_frame044_links
def record004_frame045_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0205.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0205.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame045_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0205.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame045_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0205.localPairCheck (smallEmbedding record004) (record004.maps 45) (record004.inverseMaps 45) record004_frame045_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame045_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0205.localPairCheck (smallEmbedding record004) (record004.maps 45) (record004.inverseMaps 45) record004_frame045_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame045_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0205.localPairCheck (smallEmbedding record004) (record004.maps 45)
      (record004.inverseMaps 45) record004_frame045_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame045_links_0000 record004_frame045_links_0064)
theorem record004_frame045_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 45 :=
  of_group record004 45 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0205
    Papers.RationalityTen.SharedFrameCatalogue.group0205_facts record004_frame045_indices record004_frame045_graph record004_frame045_links
def record004_frame046_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0206.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0206.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame046_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0206.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame046_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0206.localPairCheck (smallEmbedding record004) (record004.maps 46) (record004.inverseMaps 46) record004_frame046_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame046_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0206.localPairCheck (smallEmbedding record004) (record004.maps 46) (record004.inverseMaps 46) record004_frame046_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame046_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0206.localPairCheck (smallEmbedding record004) (record004.maps 46)
      (record004.inverseMaps 46) record004_frame046_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame046_links_0000 record004_frame046_links_0064)
theorem record004_frame046_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 46 :=
  of_group record004 46 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0206
    Papers.RationalityTen.SharedFrameCatalogue.group0206_facts record004_frame046_indices record004_frame046_graph record004_frame046_links
def record004_frame047_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0080.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame047_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0080.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame047_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0080.localPairCheck (smallEmbedding record004) (record004.maps 47) (record004.inverseMaps 47) record004_frame047_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame047_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0080.localPairCheck (smallEmbedding record004) (record004.maps 47) (record004.inverseMaps 47) record004_frame047_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame047_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0080.localPairCheck (smallEmbedding record004) (record004.maps 47)
      (record004.inverseMaps 47) record004_frame047_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame047_links_0000 record004_frame047_links_0064)
theorem record004_frame047_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 47 :=
  of_group record004 47 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0080
    Papers.RationalityTen.SharedFrameCatalogue.group0080_facts record004_frame047_indices record004_frame047_graph record004_frame047_links
def record004_frame048_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0071.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0071.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame048_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0071.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame048_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0071.localPairCheck (smallEmbedding record004) (record004.maps 48) (record004.inverseMaps 48) record004_frame048_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame048_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0071.localPairCheck (smallEmbedding record004) (record004.maps 48) (record004.inverseMaps 48) record004_frame048_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame048_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0071.localPairCheck (smallEmbedding record004) (record004.maps 48)
      (record004.inverseMaps 48) record004_frame048_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame048_links_0000 record004_frame048_links_0064)
theorem record004_frame048_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 48 :=
  of_group record004 48 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0071
    Papers.RationalityTen.SharedFrameCatalogue.group0071_facts record004_frame048_indices record004_frame048_graph record004_frame048_links
def record004_frame049_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0101.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0101.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame049_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0101.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame049_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0101.localPairCheck (smallEmbedding record004) (record004.maps 49) (record004.inverseMaps 49) record004_frame049_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame049_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0101.localPairCheck (smallEmbedding record004) (record004.maps 49) (record004.inverseMaps 49) record004_frame049_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame049_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0101.localPairCheck (smallEmbedding record004) (record004.maps 49)
      (record004.inverseMaps 49) record004_frame049_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame049_links_0000 record004_frame049_links_0064)
theorem record004_frame049_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 49 :=
  of_group record004 49 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0101
    Papers.RationalityTen.SharedFrameCatalogue.group0101_facts record004_frame049_indices record004_frame049_graph record004_frame049_links
def record004_frame050_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0096.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0096.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame050_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0096.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame050_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0096.localPairCheck (smallEmbedding record004) (record004.maps 50) (record004.inverseMaps 50) record004_frame050_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame050_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0096.localPairCheck (smallEmbedding record004) (record004.maps 50) (record004.inverseMaps 50) record004_frame050_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame050_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0096.localPairCheck (smallEmbedding record004) (record004.maps 50)
      (record004.inverseMaps 50) record004_frame050_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame050_links_0000 record004_frame050_links_0064)
theorem record004_frame050_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 50 :=
  of_group record004 50 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0096
    Papers.RationalityTen.SharedFrameCatalogue.group0096_facts record004_frame050_indices record004_frame050_graph record004_frame050_links
def record004_frame051_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0095.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0095.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame051_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0095.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame051_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0095.localPairCheck (smallEmbedding record004) (record004.maps 51) (record004.inverseMaps 51) record004_frame051_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame051_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0095.localPairCheck (smallEmbedding record004) (record004.maps 51) (record004.inverseMaps 51) record004_frame051_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame051_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0095.localPairCheck (smallEmbedding record004) (record004.maps 51)
      (record004.inverseMaps 51) record004_frame051_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame051_links_0000 record004_frame051_links_0064)
theorem record004_frame051_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 51 :=
  of_group record004 51 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0095
    Papers.RationalityTen.SharedFrameCatalogue.group0095_facts record004_frame051_indices record004_frame051_graph record004_frame051_links
def record004_frame052_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0057.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0057.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame052_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0057.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame052_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0057.localPairCheck (smallEmbedding record004) (record004.maps 52) (record004.inverseMaps 52) record004_frame052_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame052_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0057.localPairCheck (smallEmbedding record004) (record004.maps 52) (record004.inverseMaps 52) record004_frame052_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame052_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0057.localPairCheck (smallEmbedding record004) (record004.maps 52)
      (record004.inverseMaps 52) record004_frame052_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame052_links_0000 record004_frame052_links_0064)
theorem record004_frame052_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 52 :=
  of_group record004 52 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0057
    Papers.RationalityTen.SharedFrameCatalogue.group0057_facts record004_frame052_indices record004_frame052_graph record004_frame052_links
def record004_frame053_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0062.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0062.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame053_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0062.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame053_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0062.localPairCheck (smallEmbedding record004) (record004.maps 53) (record004.inverseMaps 53) record004_frame053_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame053_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0062.localPairCheck (smallEmbedding record004) (record004.maps 53) (record004.inverseMaps 53) record004_frame053_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame053_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0062.localPairCheck (smallEmbedding record004) (record004.maps 53)
      (record004.inverseMaps 53) record004_frame053_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame053_links_0000 record004_frame053_links_0064)
theorem record004_frame053_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 53 :=
  of_group record004 53 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0062
    Papers.RationalityTen.SharedFrameCatalogue.group0062_facts record004_frame053_indices record004_frame053_graph record004_frame053_links
def record004_frame054_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0042.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0042.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame054_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0042.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame054_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0042.localPairCheck (smallEmbedding record004) (record004.maps 54) (record004.inverseMaps 54) record004_frame054_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame054_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0042.localPairCheck (smallEmbedding record004) (record004.maps 54) (record004.inverseMaps 54) record004_frame054_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame054_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0042.localPairCheck (smallEmbedding record004) (record004.maps 54)
      (record004.inverseMaps 54) record004_frame054_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame054_links_0000 record004_frame054_links_0064)
theorem record004_frame054_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 54 :=
  of_group record004 54 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0042
    Papers.RationalityTen.SharedFrameCatalogue.group0042_facts record004_frame054_indices record004_frame054_graph record004_frame054_links
def record004_frame055_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0041.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame055_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0041.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame055_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0041.localPairCheck (smallEmbedding record004) (record004.maps 55) (record004.inverseMaps 55) record004_frame055_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame055_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0041.localPairCheck (smallEmbedding record004) (record004.maps 55) (record004.inverseMaps 55) record004_frame055_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame055_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0041.localPairCheck (smallEmbedding record004) (record004.maps 55)
      (record004.inverseMaps 55) record004_frame055_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame055_links_0000 record004_frame055_links_0064)
theorem record004_frame055_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 55 :=
  of_group record004 55 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0041
    Papers.RationalityTen.SharedFrameCatalogue.group0041_facts record004_frame055_indices record004_frame055_graph record004_frame055_links
def record004_frame056_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0035.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0035.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame056_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0035.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame056_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0035.localPairCheck (smallEmbedding record004) (record004.maps 56) (record004.inverseMaps 56) record004_frame056_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame056_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0035.localPairCheck (smallEmbedding record004) (record004.maps 56) (record004.inverseMaps 56) record004_frame056_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame056_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0035.localPairCheck (smallEmbedding record004) (record004.maps 56)
      (record004.inverseMaps 56) record004_frame056_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame056_links_0000 record004_frame056_links_0064)
theorem record004_frame056_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 56 :=
  of_group record004 56 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0035
    Papers.RationalityTen.SharedFrameCatalogue.group0035_facts record004_frame056_indices record004_frame056_graph record004_frame056_links
def record004_frame057_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0046.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame057_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0046.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame057_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0046.localPairCheck (smallEmbedding record004) (record004.maps 57) (record004.inverseMaps 57) record004_frame057_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame057_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0046.localPairCheck (smallEmbedding record004) (record004.maps 57) (record004.inverseMaps 57) record004_frame057_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame057_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0046.localPairCheck (smallEmbedding record004) (record004.maps 57)
      (record004.inverseMaps 57) record004_frame057_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame057_links_0000 record004_frame057_links_0064)
theorem record004_frame057_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 57 :=
  of_group record004 57 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0046
    Papers.RationalityTen.SharedFrameCatalogue.group0046_facts record004_frame057_indices record004_frame057_graph record004_frame057_links
def record004_frame058_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0044.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0044.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame058_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0044.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame058_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0044.localPairCheck (smallEmbedding record004) (record004.maps 58) (record004.inverseMaps 58) record004_frame058_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame058_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0044.localPairCheck (smallEmbedding record004) (record004.maps 58) (record004.inverseMaps 58) record004_frame058_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame058_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0044.localPairCheck (smallEmbedding record004) (record004.maps 58)
      (record004.inverseMaps 58) record004_frame058_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame058_links_0000 record004_frame058_links_0064)
theorem record004_frame058_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 58 :=
  of_group record004 58 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0044
    Papers.RationalityTen.SharedFrameCatalogue.group0044_facts record004_frame058_indices record004_frame058_graph record004_frame058_links
def record004_frame059_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0034.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0034.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame059_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0034.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame059_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0034.localPairCheck (smallEmbedding record004) (record004.maps 59) (record004.inverseMaps 59) record004_frame059_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame059_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0034.localPairCheck (smallEmbedding record004) (record004.maps 59) (record004.inverseMaps 59) record004_frame059_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame059_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0034.localPairCheck (smallEmbedding record004) (record004.maps 59)
      (record004.inverseMaps 59) record004_frame059_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame059_links_0000 record004_frame059_links_0064)
theorem record004_frame059_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 59 :=
  of_group record004 59 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0034
    Papers.RationalityTen.SharedFrameCatalogue.group0034_facts record004_frame059_indices record004_frame059_graph record004_frame059_links
def record004_frame060_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0033.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0033.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame060_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0033.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame060_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0033.localPairCheck (smallEmbedding record004) (record004.maps 60) (record004.inverseMaps 60) record004_frame060_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame060_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0033.localPairCheck (smallEmbedding record004) (record004.maps 60) (record004.inverseMaps 60) record004_frame060_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame060_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0033.localPairCheck (smallEmbedding record004) (record004.maps 60)
      (record004.inverseMaps 60) record004_frame060_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame060_links_0000 record004_frame060_links_0064)
theorem record004_frame060_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 60 :=
  of_group record004 60 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0033
    Papers.RationalityTen.SharedFrameCatalogue.group0033_facts record004_frame060_indices record004_frame060_graph record004_frame060_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (Fin.cases (record004_frame004_supported hcells) (Fin.cases (record004_frame005_supported hcells) (Fin.cases (record004_frame006_supported hcells) (Fin.cases (record004_frame007_supported hcells) (Fin.cases (record004_frame008_supported hcells) (Fin.cases (record004_frame009_supported hcells) (Fin.cases (record004_frame010_supported hcells) (Fin.cases (record004_frame011_supported hcells) (Fin.cases (record004_frame012_supported hcells) (Fin.cases (record004_frame013_supported hcells) (Fin.cases (record004_frame014_supported hcells) (Fin.cases (record004_frame015_supported hcells) (Fin.cases (record004_frame016_supported hcells) (Fin.cases (record004_frame017_supported hcells) (Fin.cases (record004_frame018_supported hcells) (Fin.cases (record004_frame019_supported hcells) (Fin.cases (record004_frame020_supported hcells) (Fin.cases (record004_frame021_supported hcells) (Fin.cases (record004_frame022_supported hcells) (Fin.cases (record004_frame023_supported hcells) (Fin.cases (record004_frame024_supported hcells) (Fin.cases (record004_frame025_supported hcells) (Fin.cases (record004_frame026_supported hcells) (Fin.cases (record004_frame027_supported hcells) (Fin.cases (record004_frame028_supported hcells) (Fin.cases (record004_frame029_supported hcells) (Fin.cases (record004_frame030_supported hcells) (Fin.cases (record004_frame031_supported hcells) (Fin.cases (record004_frame032_supported hcells) (Fin.cases (record004_frame033_supported hcells) (Fin.cases (record004_frame034_supported hcells) (Fin.cases (record004_frame035_supported hcells) (Fin.cases (record004_frame036_supported hcells) (Fin.cases (record004_frame037_supported hcells) (Fin.cases (record004_frame038_supported hcells) (Fin.cases (record004_frame039_supported hcells) (Fin.cases (record004_frame040_supported hcells) (Fin.cases (record004_frame041_supported hcells) (Fin.cases (record004_frame042_supported hcells) (Fin.cases (record004_frame043_supported hcells) (Fin.cases (record004_frame044_supported hcells) (Fin.cases (record004_frame045_supported hcells) (Fin.cases (record004_frame046_supported hcells) (Fin.cases (record004_frame047_supported hcells) (Fin.cases (record004_frame048_supported hcells) (Fin.cases (record004_frame049_supported hcells) (Fin.cases (record004_frame050_supported hcells) (Fin.cases (record004_frame051_supported hcells) (Fin.cases (record004_frame052_supported hcells) (Fin.cases (record004_frame053_supported hcells) (Fin.cases (record004_frame054_supported hcells) (Fin.cases (record004_frame055_supported hcells) (Fin.cases (record004_frame056_supported hcells) (Fin.cases (record004_frame057_supported hcells) (Fin.cases (record004_frame058_supported hcells) (Fin.cases (record004_frame059_supported hcells) (Fin.cases (record004_frame060_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x5c8b8d6f2da5afb5966ec9586b0557ea853ea5945a86cf69e13866dcbc95925e454778e510e17422834fcded39b6fed65a8b48686d099eb34666ca59431f63cbfd7aaed5cab7d652c3578ae155aa553e9fd37a644c28ed0fa0f4007dcf29db3ac6f0d81a833c630bd9752d25009091a22c4147c8f31ca3846e0d11882c8570a21422804e88e0da1642985209e134228370580a41282303a0700b01301c0280400700600800800 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x2a3d45a774e699d31a2d44e8650a9d134e5549c90b2023c47388d0c60c40f814ff9f1bd178cf09d3b9b704de1b9b656c2d31a0b3c66acb195b23644c798930d618c2174ad85a4b1d602b4554a9d4ea9451aa213a2684c2951252474828ed1522343a860ff1f33da778ed9c637a6e0d21923125f0ba1652b455c9510b20a408718d319e2ec570aa1422804f89811a214408670ae1442804d0941101b02303a0700b01301c0280400700600800800 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000
