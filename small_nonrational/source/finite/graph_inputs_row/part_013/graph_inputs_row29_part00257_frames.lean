module
prelude
public import GraphInputsRow29Part00257Data
public import RawFrameSupport
public import SharedFrameGroups072Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups097Checked
public import SharedFrameGroups098Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups111Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00257
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xdec6b833315fca9d54528492f691e47d239d13086442a207101a7fb3f41e98f2a5ca2b495589bc4471f50f187663641980c805d02d91638ad04e426110087e43e61ec0e707243841bb0d906603221890c185b42ce1520a5051027a13509784a01fc0f6071023c11c08403881b00d605f02e81700b605802b81540a804c01c80d0066027012809004602000f807403801800a804802000f007003001600a004001c00a0040018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb5db1fab69fd9c09b39508f58a88868768227f77ec7aa79678176d7136fe6486126095bb56852750e5014c249b49246645944a43c3fd3f034d34033131f2d62c72b72ad29f2652552452342021f21cd1c31b51a81971871781151030dc08f08e08407106c06b05f05d05c05b05805705505404c03903403302702502402302001f01d01c01801501201000f00e00c00b00a008007005004003002001000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x332587ca644eca5d92dc9684b0a50d260913486a4191fc8e246e1b4cc8654f29e14aca304cf24d11508864322110f807a22e01668af055226011587943a81c30d985c42c41560a7852027413309284782200f6077837414e08f04702100d806b03281880be05d02e016c0b005702a815009803401980b4054027012809004602000f807403801800a804802000f007002c014008003801800a0040018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x35c1998a9d50924792168fa473a2610c881e4069fecfd07a63ca95a49bc3ea1eb8f187663641980ba85b22c715a09c84c22010fc87cc3d81ce0dd86783301910c485b42ce1600ac854828813d09784a02340fe07b838814e08f04702100d806b03281880be05d02e016c0b005702a815009803401980b4054027012809004602000f807403801800a804802000f007002c014008003801800a0040018008002000 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0xcdd882ac50a9652aa534a09091da2e4588a512a1942e6e0c89652c257cae14e28e4e89c135262494918fc1f03d8798e51bc344678cc1902f05d0b716c2d4598b21602bc568a91502944c8831041f0330650be1702c8570ac1542905109e138250340660b41502704a0901182003e0740e01802a0480800f01c02c0500800e0180280400600800800 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xda99f2cd5429d538a6f4d89792ba4a49091520a3546671ccd96f2d65a4b31582a2510a113f2764bc969062044007e8ef1d036c6c8d61a4318620c11802fc5e8bc1742e45b8b31642bc5188b114208350690c61802e85b0b41642b0550a6148260340660b41502704a0901182003e0740e01802a0480800f01c02c0500800e0180280400600800800 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record001_frame004_links_0000 record001_frame004_links_0064)
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1111.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1111.count (({ width := 10, code := 0x26993626829e2779dc765cb715b86d9b36bda36857e5893a4d9344c523475104390b41cfb3e4d5344cf330be2e0ab2a4a628896250912408f2348c2288921c832087f1e86d1b06816c5a150511384c12c4a11c4611043104340cc2d0a8270942408c2007c1d07018054120400f0380b0280801c060140400c0200400 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record001_frame005_links_0000 record001_frame005_links_0064)
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1111
    Papers.RationalityTen.SharedFrameCatalogue.group1111_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb1fab69c09508a88978868768227f77ab79678176d7136fe6125bb52751b50e5014c249b46845944a43c3fd3f034d34033131f2d62ad2742652552452021f21e21d51cd1b51a81871781571151040dc0a508f08e08406c06b06506205f05d05c05b05805705505404c03403302d02a02702502402302001f01d01c01801501201000f00e00b00a008007006005004003002001000 } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record001_frame006_links_0000 record001_frame006_links_0064)
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
def record001_frame007_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0868.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0868.count (({ width := 9, code := 0x45e15037b3bddaeb7538dbcd86bb59a8cd65b1570b157ab558a55026932984b23d1a8742a0d047b3b1c0de6e36194c6613017cba5c2d164ae53291449c4a2491884411e0ec74381b8d86632180bc5c2a1489046221007c3c1b0d0602e1409848200f0702c1408038180a04018080200 } : Fields).get c.val)
theorem record001_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0868.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0868.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0868.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record001_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0868.localPairCheck (smallEmbedding record001) (record001.maps 7)
      (record001.inverseMaps 7) record001_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record001_frame007_links_0000 record001_frame007_links_0064)
theorem record001_frame007_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 7 :=
  of_group record001 7 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0868
    Papers.RationalityTen.SharedFrameCatalogue.group0868_facts record001_frame007_indices record001_frame007_graph record001_frame007_links
def record001_frame008_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0866.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0866.count (({ width := 8, code := 0xcdcac4c1bbbab8b7b0afabaaa9a7a2a19b9892918f8e87868281807e797872716f6e67666261605e59585655545352504f4d4948474542413e3b3a3635343231302e2d2b2a29262521201f1d1c1b191816151312110f0e0d0b0a080706050403020100 } : Fields).get c.val)
theorem record001_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0866.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0866.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0866.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record001_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0866.localPairCheck (smallEmbedding record001) (record001.maps 8)
      (record001.inverseMaps 8) record001_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record001_frame008_links_0000 record001_frame008_links_0064)
theorem record001_frame008_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 8 :=
  of_group record001 8 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0866
    Papers.RationalityTen.SharedFrameCatalogue.group0866_facts record001_frame008_indices record001_frame008_graph record001_frame008_links
def record001_frame009_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x6846625a458151b5125094ff4e14c44a549c49248a47146c39e37d31931330c3062ec2d52bc2b52af2a829729420c2021fc1f31d51b419518f18617d16616215914e1451321271131080fa0dc0d40ba09908908807e06a06906306005d05b05a05905605505305204a03403302d02a02702502402302001f01d01c01801501201000f00e00b00a008007006005004003002001000 } : Fields).get c.val)
theorem record001_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record001_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record001) (record001.maps 9)
      (record001.inverseMaps 9) record001_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record001_frame009_links_0000 record001_frame009_links_0064)
theorem record001_frame009_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 9 :=
  of_group record001 9 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record001_frame009_indices record001_frame009_graph record001_frame009_links
def record001_frame010_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1039.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1039.count (({ width := 11, code := 0x128a3cc0d7c8e9dcfb98722dcdb0b4567ccdd96b1b628ad54925349e9312423143e80cfe9f63de764ea190310608bd9602a24ec9c13425e4608a10f2144187c8f21ca378698bf17029c4687c0f61d8328640bc16c2c0560aa1502885009c134240340660b41502704a0901182003e0740e01802a0480800f01c02c0500800e0180280400600800800 } : Fields).get c.val)
theorem record001_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record001_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record001) (record001.maps 10)
      (record001.inverseMaps 10) record001_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record001_frame010_links_0000 record001_frame010_links_0064)
theorem record001_frame010_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 10 :=
  of_group record001 10 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1039
    Papers.RationalityTen.SharedFrameCatalogue.group1039_facts record001_frame010_indices record001_frame010_graph record001_frame010_links
def record001_frame011_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1037.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1037.count (({ width := 8, code := 0x8a8988878281807e7d7b7a797776757473726d6c6b69686665646261605f5a595856555352514f4e4d4c4b4a494746444342403f3d3c3a3938363532302e2d2c2b2a292827262423201e1c1b1a191817161512100e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1037.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1037.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1037.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record001_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1037.localPairCheck (smallEmbedding record001) (record001.maps 11)
      (record001.inverseMaps 11) record001_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record001_frame011_links_0000 record001_frame011_links_0064)
theorem record001_frame011_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 11 :=
  of_group record001 11 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1037
    Papers.RationalityTen.SharedFrameCatalogue.group1037_facts record001_frame011_indices record001_frame011_graph record001_frame011_links
def record001_frame012_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1038.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1038.count (({ width := 9, code := 0x4fe63228a4220b04813edeeef773b1d4e6723558ebb5c2dd6aae55289429f4ea652e8b4421d0a7e3d1c8e26f369a4ce653218cc2602f174b6592c158a851281349449219047e3d1e0ec70371a8d06630178a44e2511888421e0e86c34160a048200f0702c1408038180a04018080200 } : Fields).get c.val)
theorem record001_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1038.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1038.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1038.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record001_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1038.localPairCheck (smallEmbedding record001) (record001.maps 12)
      (record001.inverseMaps 12) record001_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record001_frame012_links_0000 record001_frame012_links_0064)
theorem record001_frame012_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 12 :=
  of_group record001 12 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1038
    Papers.RationalityTen.SharedFrameCatalogue.group1038_facts record001_frame012_indices record001_frame012_graph record001_frame012_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (Fin.cases (record001_frame006_supported hcells) (Fin.cases (record001_frame007_supported hcells) (Fin.cases (record001_frame008_supported hcells) (Fin.cases (record001_frame009_supported hcells) (Fin.cases (record001_frame010_supported hcells) (Fin.cases (record001_frame011_supported hcells) (Fin.cases (record001_frame012_supported hcells) (fun j => Fin.elim0 j))))))))))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xde96b9b50da56cfc6723335794b0055029dd4c4a3b513a84d30091e47d239d1828ad44d219109e842418207101a7fb3f49f18f6a7a53c99a58b9856c2a194b8a0e4f326f91307d43c61d98e346f23661980c6c61c2fc1740b6458e2b51490a044e225f11108043f21f30f607903bc1d70e807243841bb0d686983301910c505e82e616c0b2854829414409e84d425e12809083d81aa07403881740b805b02d01600ae05602a80f0072025012008c04402000f807803a01800a804001e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame001_links_0000 (interval_append _ 64 128 129 record002_frame001_links_0064 record002_frame001_links_0128))
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xc055dfae8171ab6c5acad3d594a65510a8093e29d24e0a6d529a8ff46da31d148890442a11905e8204079fecfd87db3e91ea4f2077d3b59b34cbc61d2ff97bcba45c22db1550a244f427393249784b224091b88c845722310f085e4262038fd47ce3db1b68c9062830617b8b9c5b22ca15f8ac453a28a136898048e23a11888443fe1f20f286d434e19c0c806102f216d0b2042019007403881740b805b02d01600ae05602a80f0072025012008c04402000f807803a01800a804001e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame002_links_0000 (interval_append _ 64 128 129 record002_frame002_links_0064 record002_frame002_links_0128))
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x6cf6b26a169868767e6786235e15c45b25a859258657d53f5134fd4f34d94cc4c34aa49d49949248647f47546e45944f44643b3e73a538837336735434a3413032d72bd2b029a29028726e26025924f24424023923221d2132071fe1cb1b41ad1a619e19518e18617f17d17917216515d14f14714013813312e12711a11310d1070ff0f90f30ed0cd0b307307005c05b05a05905705605505403c03902502402302202001f01e01d01801501000f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame003_links_0000 (interval_append _ 64 128 129 record002_frame003_links_0064 record002_frame003_links_0128))
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb5ab20b06afaad6ac7ab7a5a9ff9c19a399496f9609518fa8a888687684b8378247f77e87d47c07aa79678176e7407297126fc6a264a6135fe5f35d75cb5bc56d52750e5014e14d34c449b48d48247746645944a43d41b40d3fc3ee39534d34033131f30b2fa2ea2d82c72b72ad2932862652552462232132011f01cd1c31b51a819718717816b1030bf07407105d05c05b05a05805705605503c03902502402302202001f01e01d01801501000f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame004_links_0000 (interval_append _ 64 128 129 record002_frame004_links_0064 record002_frame004_links_0128))
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x3755a50ccc65332418d2c5361fadc1586a67520a8ad4089ee4ed265d2ec96e4b425852b29534a62515260928491246d22690d48323fd1de8e8470a368ff073a36b1abcd3266f32c9910b5454f29e14aca3050427a13849a249a24391dc8ce45422190c88464001f78f7c79e33b1700b345782a914a8a144e426211588604101f80f287503861b40c886002e01600ab053c29013a099849423c11708803bc1a206503101740b805b02d01600ae05602a80b4054025012008c04402000f807803a01800a804001e00e006802c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame001_links_0000 (interval_append _ 64 128 135 record003_frame001_links_0064 record003_frame001_links_0128))
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3ae1bccd736a1b4ad9f8ce4666af29608aa053ba989476a27509a5f123c90b47d239d1a68c1456a2690c885142120c103c80d3fd9fa4f8c7b53d29e4cd2c5d02b6150ca5c507279937c8903ea1eb8f1876639f1c68de46cc33018e8c385f82ea16c8b1c56a29214089c44be22210087e43e61ec0f207783ae1d00dd86cc35a1a60cf066032218a0bd05cc2d81650b005642a414409e84bc25012108d03dc1aa06503101740b805b02d01600ae05602a80b4054025012008c04402000f807803a01800a804001e00e006802c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame002_links_0000 (interval_append _ 64 128 135 record003_frame002_links_0064 record003_frame002_links_0128))
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0xde1a7b3a660ca98eb17622bb5622af54aa7d4928c50c9992ca554a69412624a48e9111da3746a8c91722c4528990f21b430854fc9d03766c4d599e330648b91652c257cae1582ac54ca81472865049f13a2704d49912a24e490909091f83e07b0f31de3b4750e71bc3686c0d51a233c660c91822f85d8b816e2d85a8b31642c0578ae15a2a05185f0b815c2b0550a81482885009e0b41502504808c1102003e0780e81802a0400780e01a02c050090100180280400600800800 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame003_links_0000 (interval_append _ 64 128 135 record003_frame003_links_0064 record003_frame003_links_0128))
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
def record003_frame004_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xebdc3b6d6c0d69a634667ec49752d0586af557aa9544a093aa714de9b1342664c69812ba534a29392524848a9091d2374688c5061e43946f4db9a9346670be16f2d65a4b31622c0574ad15129a52ca41442844fc9e1342624b89591320c408800fd1f23dc7a0f11d0390710df1b63646b0d3196320628c21823005f8bd1782e85c8b816e2c8568630c016c2d0590b01582a8540a60b41502504808c1102003e0780e81802a0400780e01a02c050090100180280400600800800 } : Fields).get c.val)
theorem record003_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record003) (record003.maps 4)
      (record003.inverseMaps 4) record003_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame004_links_0000 (interval_append _ 64 128 135 record003_frame004_links_0064 record003_frame004_links_0128))
theorem record003_frame004_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 4 :=
  of_group record003 4 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record003_frame004_indices record003_frame004_graph record003_frame004_links
def record003_frame005_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x3199808bbf5d02e356d8b595a7ab294cca2150127c53a49c14daa5311fe8eb46da31d1688a4448221508c831410203cffa7ec3ed9f48f527903be9dacd9a65f30e97fcbde5d22e116d8aa651228093d09ce4d626492f096448123811908ae44821e10bc84c4071fa8f9c7b636d1920c5060c2f71738b645942bf14509dc4da260128891c47423110887fc3e41e50eb071836a19c0c805e42da1640ab842419006503101740b805b02d01600ae05602a80b4054025012008c04402000f807803a01800a804001e00e006802c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record003_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 5)
      (record003.inverseMaps 5) record003_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame005_links_0000 (interval_append _ 64 128 135 record003_frame005_links_0064 record003_frame005_links_0128))
theorem record003_frame005_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 5 :=
  of_group record003 5 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record003_frame005_indices record003_frame005_graph record003_frame005_links
def record003_frame006_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x5f25c15a759a59558457e57753d50c4f24e34dd4ce4c94c249147846f46846145745044944243042842241c41440e4084023f43ed3e73e03ae37c35f35334b33c33432d2f52cf2c72c22bb2af2a829f29827e27527126c26425e25725223d2342302291f01ca1c01b91b01a61a119a19317916e16816115a15615114d13812f12a12311c1161101040fe0f30ed0e80e30c80b106205f05a05905805705505405305202d02a02502402302202001f01e01d01801501000f00e00d00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record003_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record003) (record003.maps 6)
      (record003.inverseMaps 6) record003_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame006_links_0000 (interval_append _ 64 128 135 record003_frame006_links_0064 record003_frame006_links_0128))
theorem record003_frame006_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 6 :=
  of_group record003 6 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record003_frame006_indices record003_frame006_graph record003_frame006_links
def record003_frame007_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1048.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1048.count (({ width := 9, code := 0x4421d0a83c1a0702803f5f6f77a3cde0ef76ba5c8e17037dbadc6db69aad268b419ccd6632d8cc461b0982bf5dae16eb459ac55aa852a9146a15027d3c994b255289248a411e8a4421d0c843f9f0f67a3c1dcec75381b4d86b349a0ce663097cbc5d2e16cb4582b954a8532913c9a3c1d8e06e361a8cc64311809448211007c3c1c0d8683214098401e0e0682c1409040180a04018080200 } : Fields).get c.val)
theorem record003_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1048.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1048.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1048.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1048.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1048.localPairCheck (smallEmbedding record003) (record003.maps 7)
      (record003.inverseMaps 7) record003_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame007_links_0000 (interval_append _ 64 128 135 record003_frame007_links_0064 record003_frame007_links_0128))
theorem record003_frame007_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 7 :=
  of_group record003 7 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1048
    Papers.RationalityTen.SharedFrameCatalogue.group1048_facts record003_frame007_indices record003_frame007_graph record003_frame007_links
def record003_frame008_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1049.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1049.count (({ width := 9, code := 0x64b1781bdde6eb73b8dbacf5dabd56a34fa6d1279389bcd6653197cb64f23914823d1d8dc6a29118843e1d077ebddeaf177bb5c8dc6c35daad268b3d9ac761b0980be5eaed74b458ac15ea85027136994b255269145a1d0c8441204fe7e3c1d4e873391c4e06e369acd46934194c44b2410c8441200f87a3c1d8b454251208c44200f8783a180a8401e0e0682c1409040180a04018080200 } : Fields).get c.val)
theorem record003_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1049.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record003) (record003.maps 8)
      (record003.inverseMaps 8) record003_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame008_links_0000 (interval_append _ 64 128 135 record003_frame008_links_0064 record003_frame008_links_0128))
theorem record003_frame008_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 8 :=
  of_group record003 8 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1049
    Papers.RationalityTen.SharedFrameCatalogue.group1049_facts record003_frame008_indices record003_frame008_graph record003_frame008_links
def record003_frame009_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xba2b57b20b06afaad6ac7ab7a5aa039c19a399496f9609518f68a889788687686384b8378247f77e97d47c07ab79678176e7407297126fc6a264e6135fe5f35d75cb5bc56952751b50e5014f04e14d34c449b48f48247746845944a43d41b40d3fc3ee39534d34033131f30b2fa2ea2d82ad2a02932862742652552462232132011f01e21d51cd1b51a818717816b1571040bf06506205d05c05b05a05805705605502d02a02502402302202001f01e01d01801501000f00e00d00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record003_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 9)
      (record003.inverseMaps 9) record003_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame009_links_0000 (interval_append _ 64 128 135 record003_frame009_links_0064 record003_frame009_links_0128))
theorem record003_frame009_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 9 :=
  of_group record003 9 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record003_frame009_indices record003_frame009_graph record003_frame009_links
def record003_frame010_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x36059d0caa64eb259910c8163d2ec161cace5602ae5556aa454ea7a530c9754b2254d27e92d48da4291a68c2458a28111887a434215d08883d41b20bceb46b03379984cb464c32298fcb5e55f2a8150ca6a52528c14289f84d226192d895049824591f48de46022d91588a23a71a78cf866031f1868bf85dc2dd1570a7451e27e136097449a23c115088c43821510307c83c01b70d105f02d41570a4042c1a406503101740b805b02d01600ae05602a80b4054025012008c04402000f807803a01800a804001e00e006802c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record003_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 10)
      (record003.inverseMaps 10) record003_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame010_links_0000 (interval_append _ 64 128 135 record003_frame010_links_0064 record003_frame010_links_0128))
theorem record003_frame010_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 10 :=
  of_group record003 10 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record003_frame010_indices record003_frame010_graph record003_frame010_links
def record003_frame011_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x16dec456dac9582a954da8f45e70cc697b2e655ca69411c62a44d89110a1d43485909607c08806ff5fabef7cef81ebbd379ef2dd0b6f6a8d29a2b39664cad762c9584af95dab2552a894da824f29d5382664b894d24a394688bd149ec3906fcdd9b6358688cc98f2ec5bcb59682be558a79482724d0979292464708a9092043d4770e71c230c5305c0b2150298520a213c2704d0980b41502504808c1102003e0780e81802a0400780e01a02c050090100180280400600800800 } : Fields).get c.val)
theorem record003_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record003) (record003.maps 11) (record003.inverseMaps 11) record003_frame011_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record003) (record003.maps 11) (record003.inverseMaps 11) record003_frame011_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record003) (record003.maps 11) (record003.inverseMaps 11) record003_frame011_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record003) (record003.maps 11)
      (record003.inverseMaps 11) record003_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame011_links_0000 (interval_append _ 64 128 135 record003_frame011_links_0064 record003_frame011_links_0128))
theorem record003_frame011_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 11 :=
  of_group record003 11 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record003_frame011_indices record003_frame011_graph record003_frame011_links
def record003_frame012_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x1b735d6a2d31a4f44681cf789eee5bab5f6aace595b1f4f289d079ff3e275ce39b534659ca693b25a444808ed1b22d4548a1129fb3ad716e01bdb6d6ccd8186ae45aeb3963ab9562a9d4ea7e4e49a931a5649c9151e22b44a8850d9eb39c714e01b835e6a4d119b3085ecbb16e2ca57cac15128c5089f13a26a4bc9591e230430839021f434c570630c016c2d0590b01582a8540a60b41502504808c1102003e0780e81802a0400780e01a02c050090100180280400600800800 } : Fields).get c.val)
theorem record003_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record003) (record003.maps 12) (record003.inverseMaps 12) record003_frame012_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record003) (record003.maps 12) (record003.inverseMaps 12) record003_frame012_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record003) (record003.maps 12) (record003.inverseMaps 12) record003_frame012_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record003) (record003.maps 12)
      (record003.inverseMaps 12) record003_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame012_links_0000 (interval_append _ 64 128 135 record003_frame012_links_0064 record003_frame012_links_0128))
theorem record003_frame012_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 12 :=
  of_group record003 12 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record003_frame012_indices record003_frame012_graph record003_frame012_links
def record003_frame013_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1096.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1096.count (({ width := 9, code := 0x4220d02803fdf8fb7cbd9e8f0773b5d4e973b85b8da6cb5daad4693459acb653218cc561b0980bf5f2f578ba5b2d166b057ab54ea25027d3a9b4d2612e9348a411c8c45a25108642a11067f3d1e0ee75399c8e06f359a4d0663218cc2602f174b85b2d164b0562a94ca45128138983f1e8e470371b0d06632188a04c22108803e1d0e06c34160a0401e0e0682c1409040180a04018080200 } : Fields).get c.val)
theorem record003_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1096.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1096.localPairCheck (smallEmbedding record003) (record003.maps 13) (record003.inverseMaps 13) record003_frame013_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1096.localPairCheck (smallEmbedding record003) (record003.maps 13) (record003.inverseMaps 13) record003_frame013_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1096.localPairCheck (smallEmbedding record003) (record003.maps 13) (record003.inverseMaps 13) record003_frame013_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1096.localPairCheck (smallEmbedding record003) (record003.maps 13)
      (record003.inverseMaps 13) record003_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame013_links_0000 (interval_append _ 64 128 135 record003_frame013_links_0064 record003_frame013_links_0128))
theorem record003_frame013_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 13 :=
  of_group record003 13 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1096
    Papers.RationalityTen.SharedFrameCatalogue.group1096_facts record003_frame013_indices record003_frame013_graph record003_frame013_links
def record003_frame014_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1097.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1097.count (({ width := 9, code := 0x46a3114894461d0d85c220d02803fdf8fb7cbc1d6e873b95c6e27037db6d86bb55a6d26833d9acc65b2992c761b0580bd5e2e962ac54aa14ca451a85409c4ca612c9449a45208e46a3116843f9f0f6793b9d8e873379b0d66933998c86330980be5e2e970b6592c158aa54299449e411f8ec74391c0d86a34198a44e2311084401e0e87036160a0401e0e0682c1409040180a04018080200 } : Fields).get c.val)
theorem record003_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1097.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record003) (record003.maps 14) (record003.inverseMaps 14) record003_frame014_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record003) (record003.maps 14) (record003.inverseMaps 14) record003_frame014_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record003) (record003.maps 14) (record003.inverseMaps 14) record003_frame014_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record003) (record003.maps 14)
      (record003.inverseMaps 14) record003_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame014_links_0000 (interval_append _ 64 128 135 record003_frame014_links_0064 record003_frame014_links_0128))
theorem record003_frame014_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 14 :=
  of_group record003 14 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1097
    Papers.RationalityTen.SharedFrameCatalogue.group1097_facts record003_frame014_indices record003_frame014_graph record003_frame014_links
def record003_frame015_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1038.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1038.count (({ width := 9, code := 0x52a8d409e4ea6d34994b653238fc7633178ac3611058240a00ff7ebf1eef479bc5deee763add0e772b8dc0dc6b349a0cc6532180bb5c2dd6ab3592c15eaa53a9948a250a7d3c9b4d2612c9045a210e8541a09007f3d1dcec74391c4de6e359a8d06632990c66130178ba5c2d960aa43208f4783b1d0e06e361a8a44e2311084401e0e87036160a0401e0e0682c1409040180a04018080200 } : Fields).get c.val)
theorem record003_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1038.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1038.localPairCheck (smallEmbedding record003) (record003.maps 15) (record003.inverseMaps 15) record003_frame015_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1038.localPairCheck (smallEmbedding record003) (record003.maps 15) (record003.inverseMaps 15) record003_frame015_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1038.localPairCheck (smallEmbedding record003) (record003.maps 15) (record003.inverseMaps 15) record003_frame015_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1038.localPairCheck (smallEmbedding record003) (record003.maps 15)
      (record003.inverseMaps 15) record003_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame015_links_0000 (interval_append _ 64 128 135 record003_frame015_links_0064 record003_frame015_links_0128))
theorem record003_frame015_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 15 :=
  of_group record003 15 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1038
    Papers.RationalityTen.SharedFrameCatalogue.group1038_facts record003_frame015_indices record003_frame015_graph record003_frame015_links
def record003_frame016_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x72b6f46d96ce6ca6be6b96b467162d60b5ff5fb5f05eb5e65a556d56155554a53f5305235194f94ed4e34da4cb4bd4b24a549248c4874804464083e73dc3d83cf3ca3c438235835034833e33532d32231b3032fb2f22ed2e02d72cf2c62b72b32af2aa26423922f22621b2112091fd1f41de1d41c91c41b61ab1a519918a18618117a17216715f14613a11f1131070fc0ce0a205f05e05905805705605405305205102d02a02502402302202001f01e01d01801501000f00e00d00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record003_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record003) (record003.maps 16) (record003.inverseMaps 16) record003_frame016_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record003) (record003.maps 16) (record003.inverseMaps 16) record003_frame016_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record003) (record003.maps 16) (record003.inverseMaps 16) record003_frame016_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record003) (record003.maps 16)
      (record003.inverseMaps 16) record003_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame016_links_0000 (interval_append _ 64 128 135 record003_frame016_links_0064 record003_frame016_links_0128))
theorem record003_frame016_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 16 :=
  of_group record003 16 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record003_frame016_indices record003_frame016_graph record003_frame016_links
def record003_frame017_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0856.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0856.count (({ width := 9, code := 0x41608ff7d3e1e8f2783b5d8e771381b8da6c355a4cf6733596ca64b218ac260b017cbd5e2ed70b65aad166b256aa14ca25027936984aa5126914823d1c8b4421d0c8441a09027e3e1ecf4793b1cce471379b8da6c34998ca6431184c05f2e168b2582b958aa53291409e4e2692c92391c0d46833190c05e2e1688c441f0f074381a0c8602e14098401e0e0682c1409040180a04018080200 } : Fields).get c.val)
theorem record003_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0856.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0856.localPairCheck (smallEmbedding record003) (record003.maps 17) (record003.inverseMaps 17) record003_frame017_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0856.localPairCheck (smallEmbedding record003) (record003.maps 17) (record003.inverseMaps 17) record003_frame017_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0856.localPairCheck (smallEmbedding record003) (record003.maps 17) (record003.inverseMaps 17) record003_frame017_indices (Fin.ofNat record003.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record003_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0856.localPairCheck (smallEmbedding record003) (record003.maps 17)
      (record003.inverseMaps 17) record003_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record003_frame017_links_0000 (interval_append _ 64 128 135 record003_frame017_links_0064 record003_frame017_links_0128))
theorem record003_frame017_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 17 :=
  of_group record003 17 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0856
    Papers.RationalityTen.SharedFrameCatalogue.group0856_facts record003_frame017_indices record003_frame017_graph record003_frame017_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (Fin.cases (record003_frame005_supported hcells) (Fin.cases (record003_frame006_supported hcells) (Fin.cases (record003_frame007_supported hcells) (Fin.cases (record003_frame008_supported hcells) (Fin.cases (record003_frame009_supported hcells) (Fin.cases (record003_frame010_supported hcells) (Fin.cases (record003_frame011_supported hcells) (Fin.cases (record003_frame012_supported hcells) (Fin.cases (record003_frame013_supported hcells) (Fin.cases (record003_frame014_supported hcells) (Fin.cases (record003_frame015_supported hcells) (Fin.cases (record003_frame016_supported hcells) (Fin.cases (record003_frame017_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x19770f5eaba96fed059bb2b54a915069ef376694cd9511c635c638990f219c2d85106609c0e812f0ddc3b26f8d31a4325638c5969aab550a2943a7b4c68e119a2943a8650a9cd358688c79842f8590a09342544908d1161fa39c708d41a032c608b916c2c85788c1042003f8720d0198320610be1782d8590aa1501c0370680cc1482704a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record005_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00257
