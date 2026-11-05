module
prelude
public import GraphInputsRow23Part00035Data
public import RawFrameSupport
public import SharedFrameGroups012Checked
public import SharedFrameGroups013Checked
public import SharedFrameGroups019Checked
public import SharedFrameGroups020Checked
public import SharedFrameGroups021Checked
public import SharedFrameGroups023Checked
public import SharedFrameGroups024Checked
public import SharedFrameGroups027Checked
public import SharedFrameGroups028Checked
public import SharedFrameGroups029Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups044Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups061Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups063Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups098Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x6ad5d553d4fa4d54ce4c44bc4b54ae4553db35c35434b34332a30c2f92f12e92d32cc2bf2a729d29128721e2161fc1f41ec1c31bb1a519d19518e18117115f15313d1291040fd0f60f00de0d70d10bf0ba0ae09f08606c05c05b05705605304a04403a03703602802602502402102001f01d01201101000e00c00b009008006005002001000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa8c94284579b73b72770d6fd6eb6d96375995004fa4ef4e44b948e47546d4604324254153f23e43d63c533732d3052f52e42aa2a02752672572492392252071f81d91c217316515314511910a0fe0d80cd0b40a308c06c05c05b05705605304a04403a03703602802602502402102001f01d01201101000e00c00b009008006005002001000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x5cc2b5d2ac94648623e91c8898444207d01a7f83f41f5cf8c6642d190888243d81e30ec06c83541758b645882b41518a4841e20810087e83e61d50e707243841bb0d2067c3301890c085e82e61600a58510278136097849c2160fe07403881aa08203e01bc0be05e02e816c0b205802a8128088037013809804a023010808003a0160098048022010007803801800b005002000c0050018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x5f95b653a5305135094fd4e14d94a649c49048a48647f3f83ac33132b31430c3032ec2e72bd2b52ac2a82a52a022421920c2031fc1da1d51cc1c11b419c19618f17d17917216b15913d13212611e1131070e60dc0c00ba0b007c07606d05d05c05b05905705605304804203702702602502302102001d01601301201101000f00e00c00b00a008006005003002001000 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1040.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1040.count (({ width := 11, code := 0x762e359db37658ca591b14622be179aeb5ceb916ea944e88890f211418810fa1f13b475ce89ce396710bd9752de5a0b214c29050c9e93725048c8f91021a424828fa1da3946f0da1a432c5a8ae136260478700d81942b0550a81482804f0981041e83604e098128230420800e8160260480881001e0380600b0140200300500600800800 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1040.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1040
    Papers.RationalityTen.SharedFrameCatalogue.group1040_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x99c94484d84581c8097f47a679b73b7277106ff6eb6d96375de5014fa4da4cc4ba47e4754254154013f43e43d632d3203133052f52bc2aa2a02962862582492392192071f81e71c21a019118217316515511b0fe0da0ce0b407e07a06d05d05c05b05905705605304a04403702702602502302102001d01601301201101000f00e00c00b00a008006005003002001000 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record001_frame004_links_0000 record001_frame004_links_0064)
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x5e65a54f84f24de4d24c849c49545944a43942f4244173ad36c2bf2b92a229c28f26325c21e2112001f61e81df18b18718117c17715f15b15715414f13b13813212812311d11610c1000fb0f50f00ea0e40ce0c50b40b10a907807406805805705605405205104e04704303702702602502302102001d01601301201101000f00e00c00b00a008006005003002001000 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record001_frame005_links_0000 record001_frame005_links_0064)
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0591.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0591.count (({ width := 11, code := 0x7c0f19bb3726c0d65a9b3a66cc4d86b045fcbe179ab352a91d22a354628b10ca183f47d8f81ec3d2794cb99131261cc11692c8584ae9572824f89d92e254498909111f23cc758e61be3585f8b4142268480740e21a42d85a0b215c2a8540a21182083704e098128230420800e8160260480881001e0380600b0140200300500600800800 } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record001_frame006_links_0000 record001_frame006_links_0064)
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0591
    Papers.RationalityTen.SharedFrameCatalogue.group0591_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
def record001_frame007_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0590.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0590.count (({ width := 11, code := 0x76ce59a134166ccc59631962cbe97aaed5d2b916fa9f5088c11721e432851001fe3c8788ed1d73a0730c39812fa5e4b91592a6538a61452604b89591b22843c858f71ce3886e8da1a83385e0b01402684706e0d61882a0530a41402704d0941041e83504e098128230420800e8160260480881001e0380600b0140200300500600800800 } : Fields).get c.val)
theorem record001_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record001_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record001) (record001.maps 7)
      (record001.inverseMaps 7) record001_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record001_frame007_links_0000 record001_frame007_links_0064)
theorem record001_frame007_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 7 :=
  of_group record001 7 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0590
    Papers.RationalityTen.SharedFrameCatalogue.group0590_facts record001_frame007_indices record001_frame007_graph record001_frame007_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (Fin.cases (record001_frame006_supported hcells) (Fin.cases (record001_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2e6158a8e2444207d01a7fa3f41f54f886642c88eb86a82eb16c8b185682a1148083c4102010fd07cc3aa1ce0e4867c3301900c485d02da1670b005642a414b0a204d825e11808884282060e9071035014a08203e01b40d8063030017c0b205802a812808803501a00ac050027010808003a0160098048022010007803801800b004001c00c005002000c004000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x99c93d7f279b73b7277126ff6e96d76375d84b84754254154033f43e23d432d3203133052f52bc2aa2a02492392272191e81da1cd1c21ba1ae1a019117316513512911a1090db0ce0b309b07e07a06b06a06105e05d05705605304a04403503402b02802702102001d01601301201101000f00e00c00b008007006005004003002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x5e65a04c749545944a43b42f4224153ad36728e25c21e2112021f61e61dd18b18718117c17715f15b15713813212c12811711211010c10a1051000fb0f00ea0d80d20cd0c70b50b10a809107807406606505c05905805205104e04704303503402b02802702102001d01601301201101000f00e00c00b008007006005004003002000 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record002_frame003_links_0000 record002_frame003_links_0064)
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x2c4953092b461217d09283340f2014fe07243521590a324c425892849264802368eb473638c1bd8db064e3151830aa052828013708d44462100fe87b83c01d10e186ac3301640a785002600f4073832014a08203e01b40d8063030017c0b205802a812808803501a00ac050027010808003a0160098048022010007803801800b004001c00c005002000c004000 } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record002_frame004_links_0000 record002_frame004_links_0064)
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
def record002_frame005_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x63f5f15244ee4c04b24a649948b4814053b72ea2b428627826925e2512471e11d91d01c81bf1a619e19816c16615e15614113813212d12812211c11610d1080f10ec0e60df0c90c10b309e08007a06b06a06105e05d05705605304a04403503402b02802702102001d01601301201101000f00e00c00b008007006005004003002000 } : Fields).get c.val)
theorem record002_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record002_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 5)
      (record002.inverseMaps 5) record002_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record002_frame005_links_0000 record002_frame005_links_0064)
theorem record002_frame005_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 5 :=
  of_group record002 5 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record002_frame005_indices record002_frame005_graph record002_frame005_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (Fin.cases (record002_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xd3058eac3d3629a3457229d1406c435a1a8cce06372b7957ca9c51b271129091e48824091ec8ea3901bf8ae451427a134096c4982390fe87c83c81d60d3865c30a1780b4855823410f08083dc1e00e206d83501720a503701b40d805f02f017409403a01b80d806a03401980ac0500270130094048012008804001800b004802000e006002800c004001 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa8a94293d84c8456fb6e86d65d85cf5c659b56e4fa4ef4e44bb48e4313ff3f03e13d33c233732d2a02752672572492392251e61db1cd1c21a019118017316515311910b0fe0f10e60cc0be0b20a309b06c06b06a05d05c05b04a03a03703603503403302b02802702602502401201101000c00b009008007006005003002001 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x66f5d85d35395344a149a4943f93f23ec3d23b035635234c32f30d2df2cc2c52bf2ba2b624d2491db1c41b91ae1a419918e16515f15514b13412c11e11510c0fe0d50cf0c50bb0b70ab0a409e09508d06b06a06905d05c05b04803903603503403303202b02802702602502401201101000c00b009008007006005003002001 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
def record003_frame004_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xbf452c292927a92f3e89ef0f4c6443179868bd45bd29d949ca244e525d114885442520a10107e43601a80ac44f026d12e894848e2370ff07d03ce1d60d4067031a1850bc85a825c12408c041c1f20de06a031816a0a503701b40d805f02f017409403a01b80d806a03401980ac0500270130094048012008804001800b004802000e006002800c004001 } : Fields).get c.val)
theorem record003_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record003_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 4)
      (record003.inverseMaps 4) record003_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record003_frame004_links_0000 record003_frame004_links_0064)
theorem record003_frame004_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 4 :=
  of_group record003 4 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record003_frame004_indices record003_frame004_graph record003_frame004_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x2fdd0ea832410202cffc7ec3eb9f48d806532f396e8a924e225b9294926481238919089243c2130d4062a30617a0ba05b22c715f8ac44f026d12e894848e23711888884221f20f2875835019c0c686142f216a0b2055428412208b03a012a09202c81600ac055022010407403701580a004202000f807803a011008003801a00c0058024010006002800c004000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x34c51dc8d946923251888bd45a22bcef06d533698d0b0051826f931c9804b925912b093c4972448dfc68232c18b0c105e02d71638ae451427a134096c498239116886c4181f00f1075834e1970c285e02d21560a504e025210d07f83a012a09202c81600ac055022010407403701580a004202000f807803a011008003801a00c0058024010006002800c004000 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record004_frame002_links_0000 record004_frame002_links_0064)
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x55f24fd18688c43aa0c904080e3ff1fb0fb47d236015249c44b725291c48c845622490f085c4261b08d4067432418a8c185d02d915f8ac44f026d12f894848e23911888884221f20f2875838c1b50d4067030a1790b2055428412f09104581d607c03c818c0c005902c01580aa04402080ac050021010007803a016009804402000f007003401800b004802000c005002000c004000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x16409b446522d4daa6c43489a04ce265f32618e0c505802b794f0a5851c28513dc9c64d3252123c90247b23791a47222b91548a6451427a12d893045a21910507b83c01d60e306d834e1970bc05a4294136093842c1fa0f707803a41c40db03901bc0c606001d00dc06a03401900c4056028013009404602200b004c01800b00500240100060028010006002 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x14b493f4061f60ca664430597f0bd65de2e796f8b6a54929d94089e84e626b93249764b222910a88284041f28f646c22b114e8a284f026d129091c46222010787c43c81d60e306d435019c0c285e42c81530a0048422a10707c83a41bc0d403901bc0c606001d00dc06a03401900c4056028013009404602200b004c01800b00500240100060028010006002 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record006_frame002_links_0000 record006_frame002_links_0064)
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x5bb51948a4763ac3a237d37436935d35434b3432fd2f32cd2c42bb2af2a629b29426b25824f24923b2351ee18f18717c17617216816315815014613813112d12511a11210d1020fe0f60ee0e40d30d00cc0c70c20be0bc07006d06105e03803603403303103002b02802602502302201601300c00b00a009008006005004003002 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record006_frame003_links_0000 record006_frame003_links_0064)
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xad255caa992d694849622c111a87142da0c10368073ee1f18daa6bb3591628adc56527c936c9a44ad24f12408de45f2280ef46c432718a8ae054629111a08883721840ba058029c10b07f035c19207103781b80bc05c02d81640ae05601c00dc06c025012008c04001f00f004c02400f0070028012008002000c002000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x5c95b95a84ec4de4cb48f47846545543842c42440e40538a37a36f2ac29c29224a23522c20d1ff1f31df1d51cc19117115f15b13d13512f1161110f60e30de0d70d10bd0b70ab0a906a06806705705505405205004f03803703602502402302001f01e01301200f00e00a009008004003001000 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x4848fb1da063fb7d6f09db3ac750e71cab8e6fcdd98c30a606a5147a884c496129a424788d114a23438774da1a133a5d4b816627c4d8820ea1c43606a8b515e2884d0670cc1942a8530a41402784e0680cc190240460881001f03c04c0900f01c0280480800800c00800 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record007_frame003_links_0000 record007_frame003_links_0064)
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xcb7651b2715a8ac655c27ad2ec93e484230d11685542120f0cdc66032c9674a8651627d12d891246d23191686fc31f1760b6c4fc24b11d08bc4521880bc85a4286139098046020c0fc079836c12008f04681b40d606a031017c0bc05b02c81580a803401980c8052027012808c04001e00e004c02400f00700280120070018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x8ef15a20439828ff5fb3dd7aebc5722d8590af956aa352aa2d40a724c495d2323f46a8890c9f23ca774e49bb364684cd1902fe5c0b39552965109892723c3e0788ec1b6354630c01762ac5305a0b21582a8510a00a81402704c0901182103e0780a0130240400780e0160280480400600800800 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x7c0ef9d339d6f4d89acb48688a7546a7d4ec9b130a5c4989091b22c438855029f93e67a4f19bf358690ca9893005c0b495d2a05189f13225247c8a1102143906e8d619030c590ab154260490570ac14c2904e09a0a41382604a08c1102003c0740a0130240400780e0160280480400600800800 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0616.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0616.count (({ width := 8, code := 0x928f8b898682807c7a6362615f5e5d5c5a59575655545251504e4d4b4a494746454342413f3e3d3b3a393736353231302d2c28272622201f1e1d1c1b1a161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0616.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0616.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0616.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0616.localPairCheck (smallEmbedding record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record009_frame003_links_0000 record009_frame003_links_0064)
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0616
    Papers.RationalityTen.SharedFrameCatalogue.group0616_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x25ed22c8fd47b21d107e82f3ff9fbcaac50127713a490445b22790b08403be1d70e7871c37e1b78d7869c33e1970c7861e30417e8bd85e02e21670ae454628d13c89984b224b11e08b043e21110106483041760a8851424c11a08483741a606002f81700b605702b00a004e024011807c03c01500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
def record010_frame002_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x26392588e846921c506481d3ee1f18b6256529a14989a44a0249117c8a04011f80f847a83c51de8eb473638c1bd8db06c435019d8c9c62a30617a0b8c5a62c215c0a9852427f136896448e23411106e43541970b28540242110080036019206002f81700b605702b00a004e024011807c03c01500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record010_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record010_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 2)
      (record010.inverseMaps 2) record010_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record010_frame002_links_0000 record010_frame002_links_0064)
theorem record010_frame002_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 2 :=
  of_group record010 2 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record010_frame002_indices record010_frame002_graph record010_frame002_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (Fin.cases (record010_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x7ac78c76a7636ca6946636495ff5c95a858354b54553e52f52952251c46542e3f03e438934d32330c2dd2d02c92c22b62b02ab2472041dd1d319c19418517716d15f15811c11410c0f70ed0e60d80cc0c80c40c109209108e08d07106f06d06b06205f05e05b05905505403803703403302902702502302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x5ffba96a6d0530a0d386694a99131da31c3385b0a20cc1381d025be34c64ac7169aa85149ed242384668a50ea1942a734d11842f8524a09342544908d1161d839c708d41a032c608b916c2c8578831042003f8690d0198320600be1782d8590aa1501c0370680cc1482704a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame002_links_0000 record011_frame002_links_0064)
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0752.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0752.count (({ width := 9, code := 0x1027f3d9e8e972b79b4d56832d8ab95bad566b258ac156aa522893c9c4ba4d12864220902803f9f4f474391a0cc6330980be5e2a148a04d2612c94492411c8c4421908823c1d8e87034198c85e2d148a04c251208c3e1e0e86c30150a048220f070281007018080200 } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0752.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame003_links_0000 record011_frame003_links_0064)
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0752
    Papers.RationalityTen.SharedFrameCatalogue.group0752_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
def record011_frame004_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6ce69a65a64d5c959956a55550f4de4bd49c44443942f41440d4063fb38a35932631c2cd29c2782632182001f61e51d41cd1c219117115f15b13512f12812211c1121100ed0e70e40d70d10ce0c50bd0b70b40b108608508208106a06806606405b05805705405204e04d03803703403302902702502302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record011_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record011) (record011.maps 4)
      (record011.inverseMaps 4) record011_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame004_links_0000 record011_frame004_links_0064)
theorem record011_frame004_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 4 :=
  of_group record011 4 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record011_frame004_indices record011_frame004_graph record011_frame004_links
def record011_frame005_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0449.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0449.count (({ width := 8, code := 0xb1aeabaaa29f9c9a989593908b8988868583827c797574716f6c6a666362605f5d5c595854534f4d4b4948464541403f3d3c3b393837363531302f2e2a29282724232221201e1d1a19181714131211100e0d0b0a090807050403020100 } : Fields).get c.val)
theorem record011_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0449.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0449.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0449.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0449.localPairCheck (smallEmbedding record011) (record011.maps 5)
      (record011.inverseMaps 5) record011_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame005_links_0000 record011_frame005_links_0064)
theorem record011_frame005_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 5 :=
  of_group record011 5 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0449
    Papers.RationalityTen.SharedFrameCatalogue.group0449_facts record011_frame005_indices record011_frame005_graph record011_frame005_links
def record011_frame006_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0379.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0379.count (({ width := 9, code := 0x17ebd5bad95dabd3693459ccca5b1c8cc6227108743200f8773b1ccda69b4182bc5dadd66b157aa138954a215047f3d9e0ea7332188c05e2e970b4592c15cac4c259249041200f87a3a1c8e06a33178b850271289042200f07032160a84c240f070281007018080200 } : Fields).get c.val)
theorem record011_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record011) (record011.maps 6)
      (record011.inverseMaps 6) record011_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame006_links_0000 record011_frame006_links_0064)
theorem record011_frame006_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 6 :=
  of_group record011 6 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0379
    Papers.RationalityTen.SharedFrameCatalogue.group0379_facts record011_frame006_indices record011_frame006_graph record011_frame006_links
def record011_frame007_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0333.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0333.count (({ width := 7, code := 0x6edbb35e5c98f0dfbd76d59b15eb55a94e7ce992e4c88d121c28301fbe7af1db86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record011_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0333.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0333.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0333.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0333.localPairCheck (smallEmbedding record011) (record011.maps 7)
      (record011.inverseMaps 7) record011_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame007_links_0000 record011_frame007_links_0064)
theorem record011_frame007_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 7 :=
  of_group record011 7 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0333
    Papers.RationalityTen.SharedFrameCatalogue.group0333_facts record011_frame007_indices record011_frame007_graph record011_frame007_links
def record011_frame008_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0307.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0307.count (({ width := 9, code := 0xea73385c0d065b1d8ac15e2e56aac552a54aa451285248e44a21067f3e1e8e871381b8da6b35198c25c2d954a44f269309047231148842209007c3d1e0ec742d160ac54271309446211007c3c1d0d86830170b0542612088401e0d0602c14090401c0a04018080200 } : Fields).get c.val)
theorem record011_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0307.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record011) (record011.maps 8)
      (record011.inverseMaps 8) record011_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame008_links_0000 record011_frame008_links_0064)
theorem record011_frame008_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 8 :=
  of_group record011 8 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0307
    Papers.RationalityTen.SharedFrameCatalogue.group0307_facts record011_frame008_indices record011_frame008_graph record011_frame008_links
def record011_frame009_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0193.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0193.count (({ width := 7, code := 0x6edbb35e5c98f0dfbd76d59b15eb55a94e7ce992e4c88d121c28301fbe7af1db86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record011_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0193.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0193.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0193.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0193.localPairCheck (smallEmbedding record011) (record011.maps 9)
      (record011.inverseMaps 9) record011_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame009_links_0000 record011_frame009_links_0064)
theorem record011_frame009_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 9 :=
  of_group record011 9 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0193
    Papers.RationalityTen.SharedFrameCatalogue.group0193_facts record011_frame009_indices record011_frame009_graph record011_frame009_links
def record011_frame010_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xce363d3069826af454a292547699e49ca42d1ec84c41f20c10187fe3f81f9cd3e63e2ff17e0ac650e27993a48de45a228110085642120d0dbc61e2f617809904b023d11508784061fa0bf05d02d614d0a184e824c11508383e01d2094049824011e07103781b40d606202f81780b605902a815007003701a00cc052027012808c04001d00e004c02400f00700280100070018008002000 } : Fields).get c.val)
theorem record011_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 10)
      (record011.inverseMaps 10) record011_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame010_links_0000 record011_frame010_links_0064)
theorem record011_frame010_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 10 :=
  of_group record011 10 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record011_frame010_indices record011_frame010_graph record011_frame010_links
def record011_frame011_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x4e29812824e43983900dfc3ca75ee81c73656c2d69a6346682cf161aa450ca052222642c82cf29db3aa734e09bd3705f4ad94d2904949091b226438829021b835c698c81883045d8b41622b85508610a208408680ce1943205c0b41642b8550a21401b8360660c81482704a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record011_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record011) (record011.maps 11) (record011.inverseMaps 11) record011_frame011_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record011) (record011.maps 11) (record011.inverseMaps 11) record011_frame011_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record011) (record011.maps 11)
      (record011.inverseMaps 11) record011_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame011_links_0000 record011_frame011_links_0064)
theorem record011_frame011_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 11 :=
  of_group record011 11 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record011_frame011_indices record011_frame011_graph record011_frame011_links
def record011_frame012_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0845.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0845.count (({ width := 11, code := 0x4999071a6314157f6f9ded3b4726df9b633d66acc18fb1a626c3561aa450ea092ba35442858f69e43c2754e61c6382620b715d2b04b49491e226438839031ae358688c117a2ec578a814827c4e07e0fa1ec3d06c0d41a03385e0b816c2c8570a61481c0370680cc1482704a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record011_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record011) (record011.maps 12) (record011.inverseMaps 12) record011_frame012_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record011) (record011.maps 12) (record011.inverseMaps 12) record011_frame012_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record011) (record011.maps 12)
      (record011.inverseMaps 12) record011_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame012_links_0000 record011_frame012_links_0064)
theorem record011_frame012_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 12 :=
  of_group record011 12 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0845
    Papers.RationalityTen.SharedFrameCatalogue.group0845_facts record011_frame012_indices record011_frame012_graph record011_frame012_links
def record011_frame013_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0769.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0769.count (({ width := 8, code := 0x96928e8d84807d7b7773716e696867656463625d5c5a59565553514d4c4b4a494847454441403c3b3a393837363231302f2e2d2c2b2a29282625242321201f1e1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0769.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0769.localPairCheck (smallEmbedding record011) (record011.maps 13) (record011.inverseMaps 13) record011_frame013_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0769.localPairCheck (smallEmbedding record011) (record011.maps 13) (record011.inverseMaps 13) record011_frame013_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0769.localPairCheck (smallEmbedding record011) (record011.maps 13)
      (record011.inverseMaps 13) record011_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame013_links_0000 record011_frame013_links_0064)
theorem record011_frame013_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 13 :=
  of_group record011 13 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0769
    Papers.RationalityTen.SharedFrameCatalogue.group0769_facts record011_frame013_indices record011_frame013_graph record011_frame013_links
def record011_frame014_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0741.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0741.count (({ width := 8, code := 0x96928e8d84807d7b7773716e696867656463625d5c5a59565553514d4c4b4a494847454441403c3b3a393837363231302f2e2d2c2b2a29282625242321201f1e1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0741.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0741.localPairCheck (smallEmbedding record011) (record011.maps 14) (record011.inverseMaps 14) record011_frame014_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0741.localPairCheck (smallEmbedding record011) (record011.maps 14) (record011.inverseMaps 14) record011_frame014_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0741.localPairCheck (smallEmbedding record011) (record011.maps 14)
      (record011.inverseMaps 14) record011_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame014_links_0000 record011_frame014_links_0064)
theorem record011_frame014_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 14 :=
  of_group record011 14 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0741
    Papers.RationalityTen.SharedFrameCatalogue.group0741_facts record011_frame014_indices record011_frame014_graph record011_frame014_links
def record011_frame015_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x5009c93226246989109e103f27a2ee9d5b776e4db1acb53698d1977acb562ab93a2564848e5041fc3ea7b0f01da3a8674bc9662c64fc9b92c2464748890d1d03806d8cc18c3005b0b01562a0520841062003f8670cc190310590ae1582985109a1301b0350660c81402604a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record011_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record011) (record011.maps 15) (record011.inverseMaps 15) record011_frame015_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record011) (record011.maps 15) (record011.inverseMaps 15) record011_frame015_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record011) (record011.maps 15)
      (record011.inverseMaps 15) record011_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame015_links_0000 record011_frame015_links_0064)
theorem record011_frame015_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 15 :=
  of_group record011 15 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record011_frame015_indices record011_frame015_graph record011_frame015_links
def record011_frame016_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0439.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0439.count (({ width := 7, code := 0x6edbb35e5c98f0dfbd76d59b15eb55a94e7ce992e4c88d121c28301fbe7af1db86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record011_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0439.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0439.localPairCheck (smallEmbedding record011) (record011.maps 16) (record011.inverseMaps 16) record011_frame016_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0439.localPairCheck (smallEmbedding record011) (record011.maps 16) (record011.inverseMaps 16) record011_frame016_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0439.localPairCheck (smallEmbedding record011) (record011.maps 16)
      (record011.inverseMaps 16) record011_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame016_links_0000 record011_frame016_links_0064)
theorem record011_frame016_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 16 :=
  of_group record011 16 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0439
    Papers.RationalityTen.SharedFrameCatalogue.group0439_facts record011_frame016_indices record011_frame016_graph record011_frame016_links
def record011_frame017_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0417.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0417.count (({ width := 7, code := 0x5cb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record011_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0417.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0417.localPairCheck (smallEmbedding record011) (record011.maps 17) (record011.inverseMaps 17) record011_frame017_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0417.localPairCheck (smallEmbedding record011) (record011.maps 17) (record011.inverseMaps 17) record011_frame017_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0417.localPairCheck (smallEmbedding record011) (record011.maps 17)
      (record011.inverseMaps 17) record011_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame017_links_0000 record011_frame017_links_0064)
theorem record011_frame017_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 17 :=
  of_group record011 17 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0417
    Papers.RationalityTen.SharedFrameCatalogue.group0417_facts record011_frame017_indices record011_frame017_graph record011_frame017_links
def record011_frame018_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0362.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0362.count (({ width := 7, code := 0x6edbb35e5c98f0dfbd76d59b15eb55a94e7ce992e4c88d121c28301fbe7af1db86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record011_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0362.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0362.localPairCheck (smallEmbedding record011) (record011.maps 18) (record011.inverseMaps 18) record011_frame018_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0362.localPairCheck (smallEmbedding record011) (record011.maps 18) (record011.inverseMaps 18) record011_frame018_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0362.localPairCheck (smallEmbedding record011) (record011.maps 18)
      (record011.inverseMaps 18) record011_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame018_links_0000 record011_frame018_links_0064)
theorem record011_frame018_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 18 :=
  of_group record011 18 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0362
    Papers.RationalityTen.SharedFrameCatalogue.group0362_facts record011_frame018_indices record011_frame018_graph record011_frame018_links
def record011_frame019_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0188.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0188.count (({ width := 7, code := 0x5cb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record011_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0188.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0188.localPairCheck (smallEmbedding record011) (record011.maps 19) (record011.inverseMaps 19) record011_frame019_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0188.localPairCheck (smallEmbedding record011) (record011.maps 19) (record011.inverseMaps 19) record011_frame019_indices (Fin.ofNat record011.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record011_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0188.localPairCheck (smallEmbedding record011) (record011.maps 19)
      (record011.inverseMaps 19) record011_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record011_frame019_links_0000 record011_frame019_links_0064)
theorem record011_frame019_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 19 :=
  of_group record011 19 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0188
    Papers.RationalityTen.SharedFrameCatalogue.group0188_facts record011_frame019_indices record011_frame019_graph record011_frame019_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (Fin.cases (record011_frame004_supported hcells) (Fin.cases (record011_frame005_supported hcells) (Fin.cases (record011_frame006_supported hcells) (Fin.cases (record011_frame007_supported hcells) (Fin.cases (record011_frame008_supported hcells) (Fin.cases (record011_frame009_supported hcells) (Fin.cases (record011_frame010_supported hcells) (Fin.cases (record011_frame011_supported hcells) (Fin.cases (record011_frame012_supported hcells) (Fin.cases (record011_frame013_supported hcells) (Fin.cases (record011_frame014_supported hcells) (Fin.cases (record011_frame015_supported hcells) (Fin.cases (record011_frame016_supported hcells) (Fin.cases (record011_frame017_supported hcells) (Fin.cases (record011_frame018_supported hcells) (Fin.cases (record011_frame019_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x2a992b293649621c506081b3ee1f18dc06c63591698b2e58a2bd95b8aca508275134898049e24812088be4501f08f1477a38c1b60d8867632718a8ae054a29311a08883c01c30dc86583081740b184382020d706481bc0dc05d02e016c0ae05601c80dc06c026012809004602100f8078028013009004001e00e0050024010005002000c002000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xad255caa992b293649621c506081b3ee1f18dc06c63591628adc565269127892045f22810047e03e11ea0f1477a3ad1cd8e306f636c1b10d4067632718a8bd05a62b814989644682220f0070c3721960c205d02ca110080835c19207103781b80ba05c02d815c0ac03901b80d804a024011807c03c01500a004c024011008003c01c00c0050024010005002000c002000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
def record013_frame002_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x44887d0c9e33bc762e15bab6e6bed617caf25ca9bd3325d46488d0ea0e4107b0f29db3a8730e19bc36a6b8d219c326624c197e2f05bcb014f28a4cc9291c2103e4768e01ae338640b115a2704b8640c61882a8540a613c270340660c81282404607c0f01502804c0901102003c0700c0140240400500800c00800 } : Fields).get c.val)
theorem record013_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record013_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record013) (record013.maps 2)
      (record013.inverseMaps 2) record013_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record013_frame002_links_0000 record013_frame002_links_0064)
theorem record013_frame002_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 2 :=
  of_group record013 2 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record013_frame002_indices record013_frame002_graph record013_frame002_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (Fin.cases (record013_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x61ba97d0e282d40c1f68f886b233018b4c385ea2ed973cb885b82d893489864b022e913875a39b1c60dec6d836215c09f44d625a12407f43dc1e00e8870c3721a70ca060c2e61640a78500260111080835419009204881ac0d405702b00dc06c03301900a8052028013807c03c01d008804001e00e005002400e0060028010006000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6045af59658855552f5174da4b14a349949348d3e038c37836d34832b3192ed2cd2c42bb2b82b428627a27126625924d2452302262102071f21e41d51c41b51a319718b18715f14613a12d0fb0eb0d80cd0c50aa08106706405d05c05b05905705305205003503202902802702502301f01e01c01501401301201101000e00c00a009007005004003002001000 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x25ad29092c44f21ed0e27dc3e31d34e6e72536a9aecd6462a30c965caf65652aa14c8a484f926d934895a49e248117c8a039b1bd8d8869c3251898b8c5842b814809f44d623411107f43dc1e00e8870c37215108883240bc05c02d81600ae056021810408003801b80d804c024011808003e01e008803c01c00b005002400c005002000c002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x25f52de96149824892368e8470a070fec7cf3a71c88e1a65131e1584a7a518280937499a49a23b919c87e42e20f8fbc7be2f21670aa452426e12f08ac4101f80e806fc3601800b8055829e1480a084e826610a07783440bc05c02d81600ae056021810408003801b80d804c024011808003e01e008803c01c00b005002400c005002000c002000 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x52fa2790f68713ed1f10e9a7373929980c5661a2f5176cb9e5c42dc16c4aa653129193e49b64d2257928092445d2270e6c6f63621a70c946262e31610ae04b42490fe87b83c01d10e186e434e1940c185cc2c8140098044419006b03501600ae056021810408003301900a8052028013808003e01e008803c01c00b005002400e0060028010006000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x5f6a97cfac7c033017a8bb65cf2e216e0b625972bd9594aac53429313e49b64d2257928092448323890047e03e11ea0f1477a39b1bd8d886a032718a8b8c5842b814909fc4da25a12486983261820b9058427a12d07e83bc1c40c404702340d606a01980c8054029014009c04c024011808003e01e00e0054028013009004401e00e0058028012007 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xd1753123d91c08d2465a29914289a3ce9a44cb662429e141899e4c726012e49644ac25291f08ec3d31d40e4c6022ef16c8a644f426b12508e845621a10708003c61b60cb86202ce1570a404dc25611d08003d812008d03c01a80b605802b81580a804302000d4064026011808404001f00f0070028013009003801a00b005002400e005002000c002000 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0xaff58e68cb68ad102054037fcfe1f6be47bcf4dc2b60694d01963215e2b215f2ad546a553924e48e90515a234267c8e49bb364684cd1702b8530a31392504607c0f11d83846d8d518c3005d8b61041fc3e0690ca18c2d0560aa1402784e0720e01a8340640a81402604808c1081e03a0700a01302003c0700b0120200380400600800800 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
def record022_frame002_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x72971863d61b58c56852e52852251d51450e5074fb48144d42e42240c3ff3c238a37536335333e3172ff2f92f42e62e02d529425123d23221720a1d01ba1a819f18e17d16913512611e10b0fa0f20d50cb0c60c108c08a08706e06a06805e05a05905405305203803703403303102a02802602402302101e01d01c01401301000f00e00b009008007004003002001000 } : Fields).get c.val)
theorem record022_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record022_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record022) (record022.maps 2)
      (record022.inverseMaps 2) record022_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record022_frame002_links_0000 record022_frame002_links_0064)
theorem record022_frame002_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 2 :=
  of_group record022 2 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record022_frame002_indices record022_frame002_graph record022_frame002_links
def record022_frame003_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0375.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0375.count (({ width := 8, code := 0xb0afa5a39d9a94939291908f8e8d858281807f7e7976757473716b696867656463615e5d5c5a595352504f4e4c4b4746454342413f3e3d3c3937363331302e2c2b2928272322201f1e1b1a181716141312110f0e0c0b0a080706050403020100 } : Fields).get c.val)
theorem record022_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0375.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0375.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0375.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record022_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0375.localPairCheck (smallEmbedding record022) (record022.maps 3)
      (record022.inverseMaps 3) record022_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record022_frame003_links_0000 record022_frame003_links_0064)
theorem record022_frame003_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 3 :=
  of_group record022 3 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0375
    Papers.RationalityTen.SharedFrameCatalogue.group0375_facts record022_frame003_indices record022_frame003_graph record022_frame003_links
def record022_frame004_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0447.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0447.count (({ width := 8, code := 0xb0afa5a39d9a94939291908f8e8d858281807f7e7976757473716b696867656463615e5d5c5a595352504f4e4c4b4746454342413f3e3d3c3937363331302e2c2b2928272322201f1e1b1a181716141312110f0e0c0b0a080706050403020100 } : Fields).get c.val)
theorem record022_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0447.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0447.localPairCheck (smallEmbedding record022) (record022.maps 4) (record022.inverseMaps 4) record022_frame004_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0447.localPairCheck (smallEmbedding record022) (record022.maps 4) (record022.inverseMaps 4) record022_frame004_indices (Fin.ofNat record022.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record022_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0447.localPairCheck (smallEmbedding record022) (record022.maps 4)
      (record022.inverseMaps 4) record022_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record022_frame004_links_0000 record022_frame004_links_0064)
theorem record022_frame004_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 4 :=
  of_group record022 4 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0447
    Papers.RationalityTen.SharedFrameCatalogue.group0447_facts record022_frame004_indices record022_frame004_graph record022_frame004_links
def record022_frame005_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0304.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0304.count (({ width := 8, code := 0x85847c7a767371706f6e6d6c6b6a63605f5e5d5c5956555453514f4e4d4c4b4a494845444341403e3d3c3b3a393837363534333231302f2e2d2b2a29272625232221201f1e1d1b1a1918171514131211100f0e0d0b0a09080706050403020100 } : Fields).get c.val)
theorem record022_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0304.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0304.localPairCheck (smallEmbedding record022) (record022.maps 5) (record022.inverseMaps 5) record022_frame005_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0304.localPairCheck (smallEmbedding record022) (record022.maps 5) (record022.inverseMaps 5) record022_frame005_indices (Fin.ofNat record022.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record022_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0304.localPairCheck (smallEmbedding record022) (record022.maps 5)
      (record022.inverseMaps 5) record022_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record022_frame005_links_0000 record022_frame005_links_0064)
theorem record022_frame005_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 5 :=
  of_group record022 5 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0304
    Papers.RationalityTen.SharedFrameCatalogue.group0304_facts record022_frame005_indices record022_frame005_graph record022_frame005_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (Fin.cases (record022_frame002_supported hcells) (Fin.cases (record022_frame003_supported hcells) (Fin.cases (record022_frame004_supported hcells) (Fin.cases (record022_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x5f05bf5ad55d5245114c94bc4b149e49048547f46b3f93c43b037033d32f2ec2e22db2ce2c32bc2b62a927826d26424622d2242172101ed1d11b91a519117e17416414212d12511e1060fe0ee0e00d50c908107f06b06906706405b05a05705505105004f04e03903703503202902802502301f01e01d01c01501401301101000e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
def record023_frame002_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x5f85bd59d5555184f64bb4b44ae4a249b4954904834223e63c837b33c31d2e02d82d22c62c02bb2b72ae28928027524922721d2061f91d51c41b119818617216815513e12c1211140f60ec0d80c50bc0b808608306e06c06a06705f05e05b05905505405305203803603403102902802502301f01e01d01c01501401301101000e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record023_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record023_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record023) (record023.maps 2)
      (record023.inverseMaps 2) record023_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record023_frame002_links_0000 record023_frame002_links_0064)
theorem record023_frame002_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 2 :=
  of_group record023 2 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record023_frame002_indices record023_frame002_graph record023_frame002_links
def record023_frame003_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x4bc9171de2641d816f81ed3d278cef9dcbb274cced84af5586a5540a5c4b0949242404788dd1620c4047e4ee1c33726a0cf1842ea59cac94e2764d49291320a3f47b8dd1aa3205d8b616021c4286e0da1ac340600be1742d8570ac1542a03906e0d4190290500941181f03c0740e01502804c0881001c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record023_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record023_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record023) (record023.maps 3)
      (record023.inverseMaps 3) record023_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record023_frame003_links_0000 record023_frame003_links_0064)
theorem record023_frame003_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 3 :=
  of_group record023 3 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record023_frame003_indices record023_frame003_graph record023_frame003_links
def record023_frame004_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xb2a544a92d3228fa45fa0c103880c3f49f58f8e7b73ca97d8aaa51722e8f187162fc1740b6056a2a21498a0c4c223911908ac41e1fa0f9878c3b81c20da069832e18a0bd85d42ce1520a204f426a12108c84301fc0f6078024811a07103781b40d406103001740b605702b01540a803901b80d4064029014009404601f00f007403801500a004c0220100070030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record023_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 4) (record023.inverseMaps 4) record023_frame004_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 4) (record023.inverseMaps 4) record023_frame004_indices (Fin.ofNat record023.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record023_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 4)
      (record023.inverseMaps 4) record023_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record023_frame004_links_0000 record023_frame004_links_0064)
theorem record023_frame004_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 4 :=
  of_group record023 4 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record023_frame004_indices record023_frame004_graph record023_frame004_links
def record023_frame005_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x4217f0fa5dcb93706d85ad35569ad159fb3b65eb7d5c2aa4ec94922222436855052033fc7e8f81d5398710d619731e610c01672ae5249c92922e440808f21d03906f0cd18c2ec580ac1501fc3d8680cc190308580ae1502904e09a1302583906e0d4190290500941181f03c0740e01502804c0881001c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record023_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record023) (record023.maps 5) (record023.inverseMaps 5) record023_frame005_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record023) (record023.maps 5) (record023.inverseMaps 5) record023_frame005_indices (Fin.ofNat record023.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record023_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record023) (record023.maps 5)
      (record023.inverseMaps 5) record023_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record023_frame005_links_0000 record023_frame005_links_0064)
theorem record023_frame005_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 5 :=
  of_group record023 5 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record023_frame005_indices record023_frame005_graph record023_frame005_links
def record023_frame006_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x4628790a5f6bbf742da5b0b58696d119f33a662be9662b24ee9411d2063fa7d4f41e03b675ce71bb36e6c4d119531e60cbe96c2c0550a193624e4848b1021ea3c0738d21942f4590aa1482003d8670ca18c308580ae1502904e09a1302583706a0cc1802804e0941181f03c0740e01502804c0881001c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record023_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record023) (record023.maps 6) (record023.inverseMaps 6) record023_frame006_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record023) (record023.maps 6) (record023.inverseMaps 6) record023_frame006_indices (Fin.ofNat record023.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record023_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record023) (record023.maps 6)
      (record023.inverseMaps 6) record023_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record023_frame006_links_0000 record023_frame006_links_0064)
theorem record023_frame006_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 6 :=
  of_group record023 6 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record023_frame006_indices record023_frame006_graph record023_frame006_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (Fin.cases (record023_frame002_supported hcells) (Fin.cases (record023_frame003_supported hcells) (Fin.cases (record023_frame004_supported hcells) (Fin.cases (record023_frame005_supported hcells) (Fin.cases (record023_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x135c9a74d026112de9684ac254523691348623fd1ee8f04752370bc65d22e015d0a7a52b28193c88ce454221108c8224011f88f446e83631a88c1459c2bc14a0a0c3f01e50e986d03441920c105882ac14f0a4050427413308b84101ec0ef074824811a06f03501880c206002f01740b605702b01540a803701900a8052028013009404601f00f007403801500a004c0220100070028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
def record024_frame002_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x136c9a24c8a5192188fa46922fd06081e4061fa4fb07c73db9e5490446e22e90487b03c61cf0e2c5f82ea16c0ad45482931418984472232115883c3f41f30f1877034c19e0cb862830417b0ba859c2c01590a9052c28813d09084301fc0f7078024811a06f03501880c206002f01740b605702b01540a803701900a8052028013009404601f00f007403801500a004c0220100070028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record024_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record024_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 2)
      (record024.inverseMaps 2) record024_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record024_frame002_links_0000 record024_frame002_links_0064)
theorem record024_frame002_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 2 :=
  of_group record024 2 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record024_frame002_indices record024_frame002_graph record024_frame002_links
def record024_frame003_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x138a6e4d697d2b2534969211922e4568991121f43a85cbe97a2ee5acb115f2ae5509f13a26e4c89712b25248c8a11121c4087c8f61dc3ac6a8d119c324628c21802e85b8b616a2d0598b215c2ac548a814e218408690c81702d85a0b015c2a8510a013c270370640a81482804c0941181f03c0740e01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record024_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record024) (record024.maps 3) (record024.inverseMaps 3) record024_frame003_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record024) (record024.maps 3) (record024.inverseMaps 3) record024_frame003_indices (Fin.ofNat record024.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record024_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record024) (record024.maps 3)
      (record024.inverseMaps 3) record024_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record024_frame003_links_0000 record024_frame003_links_0064)
theorem record024_frame003_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 3 :=
  of_group record024 3 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record024_frame003_indices record024_frame003_graph record024_frame003_links
def record024_frame004_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x146a8a50e9ed3926f4ce9912724a48e9091f23b4728ccc39843025d4b61692c2578a41442824f09c1352664b48f11b230430819001f03d46f8db1b034c678cc194310608c017e2f85e8bc1702d4598b21622384486d0d01802f85e0b816c2c8550a814c290370640a81482804c0941181f03c0740e01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record024_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record024) (record024.maps 4) (record024.inverseMaps 4) record024_frame004_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record024) (record024.maps 4) (record024.inverseMaps 4) record024_frame004_indices (Fin.ofNat record024.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record024_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record024) (record024.maps 4)
      (record024.inverseMaps 4) record024_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record024_frame004_links_0000 record024_frame004_links_0064)
theorem record024_frame004_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 4 :=
  of_group record024 4 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record024_frame004_indices record024_frame004_graph record024_frame004_links
def record024_frame005_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x57156655d54152d5245185114c94bd4b149e49148547f46b38137837035934533d33432f2ec2e42db2ce2c52bc2b62a927826d26424622d2242172101b91af1a519118817e17416415814c14213712d1251060ee0e00d60c908107f06906405c05b05a05805705505105004f04e03703202a02902802602502301f01e01d01c01501401301101000e00a009008007006005004003002001000 } : Fields).get c.val)
theorem record024_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record024) (record024.maps 5) (record024.inverseMaps 5) record024_frame005_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record024) (record024.maps 5) (record024.inverseMaps 5) record024_frame005_indices (Fin.ofNat record024.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record024_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record024) (record024.maps 5)
      (record024.inverseMaps 5) record024_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record024_frame005_links_0000 record024_frame005_links_0064)
theorem record024_frame005_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 5 :=
  of_group record024 5 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record024_frame005_indices record024_frame005_graph record024_frame005_links
def record024_frame006_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0x19b32e650c5984b035f0bd1662c6580add582aa54ea7117a2c452865062063f67d4e59c63826dcd71a9348670c117c2ec598ae15929e5248f918226420818fe1f23c0748e41bc360690cc1702984f09a12a1c4368600b8150298520a21402784b094124240370640a81482804c0941181f03c0740e01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record024_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record024) (record024.maps 6) (record024.inverseMaps 6) record024_frame006_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record024) (record024.maps 6) (record024.inverseMaps 6) record024_frame006_indices (Fin.ofNat record024.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record024_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record024) (record024.maps 6)
      (record024.inverseMaps 6) record024_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record024_frame006_links_0000 record024_frame006_links_0064)
theorem record024_frame006_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 6 :=
  of_group record024 6 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record024_frame006_indices record024_frame006_graph record024_frame006_links
def record024_frame007_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x1e23bf772e9dcd393710e0db0b5b6aad35a333f676cbd41a7d4ec9912c2524929111121c42a829021fe3f47c0ea9cc3886b0cb98f308600a49422724a4901172204047e8f71e43b4740e419a2ec580ad1501fc3d8660c21642c0570aa1502904e09a130258370640a81482804c0941181f03c0740e01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record024_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record024) (record024.maps 7) (record024.inverseMaps 7) record024_frame007_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record024) (record024.maps 7) (record024.inverseMaps 7) record024_frame007_indices (Fin.ofNat record024.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record024_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record024) (record024.maps 7)
      (record024.inverseMaps 7) record024_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record024_frame007_links_0000 record024_frame007_links_0064)
theorem record024_frame007_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 7 :=
  of_group record024 7 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record024_frame007_indices record024_frame007_graph record024_frame007_links
def record024_frame008_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0980.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0980.count (({ width := 8, code := 0xdddbd9d6d4d2cfcec4c2c1c0bebdbcbba6a4a29f9d9b98978d8b8a89878685847d7b797674726f6e646261605e5d5c5b5a5958575655524f4e4d4c494844433b3a39383736333231302d2c24232221201f1c1b1a191211100f0e0d0a09080706050403020100 } : Fields).get c.val)
theorem record024_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0980.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0980.localPairCheck (smallEmbedding record024) (record024.maps 8) (record024.inverseMaps 8) record024_frame008_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0980.localPairCheck (smallEmbedding record024) (record024.maps 8) (record024.inverseMaps 8) record024_frame008_indices (Fin.ofNat record024.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record024_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0980.localPairCheck (smallEmbedding record024) (record024.maps 8)
      (record024.inverseMaps 8) record024_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record024_frame008_links_0000 record024_frame008_links_0064)
theorem record024_frame008_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 8 :=
  of_group record024 8 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0980
    Papers.RationalityTen.SharedFrameCatalogue.group0980_facts record024_frame008_indices record024_frame008_graph record024_frame008_links
def record024_frame009_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x89388687b84581c8097de7cd75073a7267006ec6da6c86a253e53452a4fa4da4cc4aa49c4364244143f53e53d73c73a837936d36032d3052f52d72cb25a24823821a2081f91e91cd1c21ba1ae1a019118314611c0fe0f30e808c08706d06806005f05e05c05b05905505405305203703202a02902802602502301f01e01d01c01501401301101000e00a009008007006005004003002001000 } : Fields).get c.val)
theorem record024_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record024) (record024.maps 9) (record024.inverseMaps 9) record024_frame009_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record024) (record024.maps 9) (record024.inverseMaps 9) record024_frame009_indices (Fin.ofNat record024.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record024_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record024) (record024.maps 9)
      (record024.inverseMaps 9) record024_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record024_frame009_links_0000 record024_frame009_links_0064)
theorem record024_frame009_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 9 :=
  of_group record024 9 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record024_frame009_indices record024_frame009_graph record024_frame009_links
def record024_frame010_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x24748a90d1c631c5d89b11a0a40c80afe1f7be67bef4d7baf15d6b3d5f2b4546a71312584a09051b22d44884cfe1f83e4750e11bb350684b395e2ac5189d9322524608890d2104087e8f81c2340630c11782043e0680c61702d85a0b015c2a8510a013c270370640a81482804c0941181f03c0740e01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record024_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record024) (record024.maps 10) (record024.inverseMaps 10) record024_frame010_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record024) (record024.maps 10) (record024.inverseMaps 10) record024_frame010_indices (Fin.ofNat record024.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record024_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record024) (record024.maps 10)
      (record024.inverseMaps 10) record024_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record024_frame010_links_0000 record024_frame010_links_0064)
theorem record024_frame010_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 10 :=
  of_group record024 10 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record024_frame010_indices record024_frame010_graph record024_frame010_links
def record024_frame011_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0x23fc768d313a1c43083704defbd879cef9da3ad748e4d63ac457caa54aa8d4f69d12023a45e8910d2114127e4ef9d839e6d8d31a332a634ad1532924e09712823e44c869092063f47b8f11b63205e8b91662083e86c0d01802f85e0b816c2c8550a814c290370640a81482804c0941181f03c0740e01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record024_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record024) (record024.maps 11) (record024.inverseMaps 11) record024_frame011_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record024) (record024.maps 11) (record024.inverseMaps 11) record024_frame011_indices (Fin.ofNat record024.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record024_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record024) (record024.maps 11)
      (record024.inverseMaps 11) record024_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record024_frame011_links_0000 record024_frame011_links_0064)
theorem record024_frame011_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 11 :=
  of_group record024 11 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record024_frame011_indices record024_frame011_graph record024_frame011_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (Fin.cases (record024_frame002_supported hcells) (Fin.cases (record024_frame003_supported hcells) (Fin.cases (record024_frame004_supported hcells) (Fin.cases (record024_frame005_supported hcells) (Fin.cases (record024_frame006_supported hcells) (Fin.cases (record024_frame007_supported hcells) (Fin.cases (record024_frame008_supported hcells) (Fin.cases (record024_frame009_supported hcells) (Fin.cases (record024_frame010_supported hcells) (Fin.cases (record024_frame011_supported hcells) (fun j => Fin.elim0 j)))))))))))))
#print axioms record024_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035
