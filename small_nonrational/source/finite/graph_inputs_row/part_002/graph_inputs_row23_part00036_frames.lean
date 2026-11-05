module
prelude
public import GraphInputsRow23Part00036Data
public import RawFrameSupport
public import SharedFrameGroups016Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups064Checked
public import SharedFrameGroups070Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups090Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
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
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xa89524a6451a28c045622690c8842418202cff27d63e41edcf2855528a917473a38c1bc0d9866030e17e0b5c58a2a214a0a0c4c023911908ac3f41dd0eb07403921c20dd86d035a1a60ce865831e17c0ba85982a414409e84d424211908984301ec0db04681ec0da06a03081800b605a02c015c0ac05402180d4064029014008c04402000f807803801500a004c02200e006803001600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0x9b297e90986184a8368247f77d47c079477f75574272b6fd6085de5774ee4e04d24c449b48247745744842841d40f3ef3bd3ae3a43412f92e92d82c72b72ad2a12932862732632532252151f11cd1b51a819716b1561451351030cd08d07b06d06a06106005b05a05805705605404303503202902802302202001f01e01c01501401301100e00d00c00b00a009007005004003002001000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x57855a5114b44aa49f49748047046645344643042a42040e3703523092ac2a029628f27826625f24823e2282202172061ee1e71e11bc1a319c19618f18918418017a17316a16415c14d14513a12711d11610e0f90f20eb0e30d30b808107206706405b05a05505405205105004e04003503202902802302202001f01e01c01501401301100e00d00c00b00a009007005004003002001000 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xbae5862ac15369984bb254d278906472a30d140889429a12d07a8363a21a68c9463d2af950ca6a51427c134896c4a824391ac8c045b22b0c7c6122fb17709f84d025a126888c4382150d1055428613908b84181f80da06901ec0f007103701780b805b02c815c0ac04202000e006c025012008c04001f00f004801e00e0068028012008002000c002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x5f85b95675474ec4de4cb4bb49a48f47846545542c42440e4053ba37a32330e2ac29c29227626124a23522c20d1f31df1d51cc17116916316113d13512f12d11611110e0f60de0d70d10c40bd0b70ab0a907307006a06705705505405205004f04103f03803602502402302001f01e01200f00e00d00a009008004003001000 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x4077b6eb9d1b6d6c8d5da633665ac898ab0b5e2bb5722e0562a3530a5a43683d049f53ca76ce89c93706a0cf99b32e52ca113b2724648810a20e3d4798f11b02f45c8b4152290500941241ac348630c01482804f09a12c2503c0740d81a02504808c1001f03c0480780e01a0280480800800c00800 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0841.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0841.count (({ width := 11, code := 0x8fd101fa3dd79ef11debaf746e45c534a654c6d8a2d8598a153d26c4c695d29a4d4909151f23745e8a90fa1841c820e619932062cc31702c655ca814825a48c8e90e1fe3dc728d61a03345d8b614026c3806a0d21682c8560aa1502083e0700dc1a82604808c1082003e0780a01201e0380680b0140240400500800c00800 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0841
    Papers.RationalityTen.SharedFrameCatalogue.group0841_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xbc8577a82d26490c473a34112c86442120c10127e53da9e94d285bb26b8ff87b03b31ce0d8866030e17e0b5456228113888e444821d10407e83d81dd0eb86ec35a1a60cf06442e616c0b285802b21520a5851027a134096847c2260fd07b83681aa07b03c01c00dc05e02e016c0b005702b010c08003801b0098048023010007c03c01500a004802200f007003401600a004802000c005002000c002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x607b976469c526a234066dcc79672964746f8c11660d3dc746d359f32a636bf5762db59cae550a955209b927a4345086d039f13d872cde1af348650bb16f2d258cae15228e4f0989232303ec750cf18c28c4d86b0d2190310540a41442704d0980f81e0360680981202304007c0f0150280480880f01c0340580a0120200300500800c00800 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x4077a6e8db6b646aed319b328638c55812f15c8b815c28d4b48850b2093f8794ed9d13926e0d419b32e608b896b2ba550a593d27249c8e91922441c7a8f31e23b4750e41be36c6c0d01922f45b0a914c2504906b0d2188300520a013c2604b0940f41d0360680981202304007c0f0150280480880f01c0340580a0120200300500800c00800 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0847.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0847.count (({ width := 11, code := 0x2c3557a8340a62caa8bb12616c1f798eedd8b9f724e09bdb6c69ecf198b1c61cbe979ae854ea8548a884f89c9171f63ba714d99a833a644bf1792c4528999272344387c0f31b63105c8ad14a274340670ca1902d8590ac1541c83806c0d4198320540a41382604808c0a01201e0380580a0120200380500800c01001 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0847
    Papers.RationalityTen.SharedFrameCatalogue.group0847_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xcea558297d2888f344ca248e4e6f737399c8cbc64b31c9748b4459228e94249ec4e424e925891047523791a46322c315c8aa453228a13d09ac4ae248114887441c1e10eb071836c1a70cb86202e81650a304e82560fe07b83c01d20e206a02bc13606b03501700b604001c80e006c03301900c40540290138090046022007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record005_frame001_links_0000 record005_frame001_links_0064)
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
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x191aaa94a9a4ed25491b4852281110877434215d07a8364179e34dc665132515b0aa253528a94289f84df26212a091047d23791948b64562288d3c66031f1858bb85ba2ae14789f84d424d11e08a844621c10a868831617b0b5055c28a13b08403f81a409e04a01e80e005c02d81680ae05602a810c08403901c00a804c024011808804201f00f0074028010007803801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x2b04b38ad13222c42877052054037fefe1eebd77a2ebdc2b2963cb215f2ad536a5d46a814e4989272484828d511219422724dd9b234e670c917f2e059cae14d28c4c49391e22c3e0788ec1ce3846d8d51802ec530891041c0348560aa1502885009e10c210390700a8130240460881081f03c0740a01001e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record006_frame002_links_0000 record006_frame002_links_0064)
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x247c1677ced5d6ba873ede9b936b6c8d6da4344680cad80ac357c9d9362614a493922236458871072073f67ccf49e33b8654c49802f05acaf95028c4f89b12b2424508810a2063906e8d61a232c640c31562a8490820f81b0330530a41442704d0980fc1f03706c0a4128230440841001e03a0700a01001e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record006_frame003_links_0000 record006_frame003_links_0064)
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
def record006_frame004_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x17b4a32496244d1fc8ea46a21c50b284641a207cfb87c63d79d6cde264e31e165caf65652a114d8a50508275134895c4a224a12088be4502200e306d83621a78ca462e2e31610ae054a281137891c46822210706e43501970c305d82c6150087040019209e04a01e80e005c02d81680ae05602a810c08403901c00a804c024011808804201f00f0074028010007803801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record006_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record006_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 4)
      (record006.inverseMaps 4) record006_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record006_frame004_links_0000 record006_frame004_links_0064)
theorem record006_frame004_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 4 :=
  of_group record006 4 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record006_frame004_indices record006_frame004_graph record006_frame004_links
def record006_frame005_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x66a5b252951a50f5095004d14c24b74b24a949348f48b4463f73a73a13313213183002fd2f62e22d82c92b12ad2a72a029629329021e20d2091fb1e81e01c41b91b21a419018a17b17417016c13712811f11610b0fe0f60d40cc0ae09208c07606e05a05905805505405304204103903802a02602402302202101f01e01d01401000f00e00d00b00a009008004003002001000 } : Fields).get c.val)
theorem record006_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record006_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record006) (record006.maps 5)
      (record006.inverseMaps 5) record006_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record006_frame005_links_0000 record006_frame005_links_0064)
theorem record006_frame005_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 5 :=
  of_group record006 5 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record006_frame005_indices record006_frame005_graph record006_frame005_links
def record006_frame006_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x1acb03590b11602bd56ea5d48a8b510a09372684c693d19a003f471cdd9b4352698cf99931e610bc1772e45a8b115e2b44b893121238444860fd1ea3c4750e31bc348670ca18e2b8558a814e2904f09a11a228400730dc1943005009e1382584a09210c210390700a8130240460881081f03c0740a01001e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record006_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record006_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record006) (record006.maps 6)
      (record006.inverseMaps 6) record006_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record006_frame006_links_0000 record006_frame006_links_0064)
theorem record006_frame006_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 6 :=
  of_group record006 6 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record006_frame006_indices record006_frame006_graph record006_frame006_links
def record006_frame007_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x1fb381680ce59ab3265ac4986307608bf976ae65c6b0548a4948881cfe1f73ce794ef9d3392704d89ad34e684cb99231e548a514527a4c49591e234450861001f43c4750e51c631c620c117e2f05c0b314a28c4a8790ea19c310540a61482784e09a0f41e0350680a0120220420800f81d03806c0a01001e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record006_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record006_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record006) (record006.maps 7)
      (record006.inverseMaps 7) record006_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record006_frame007_links_0000 record006_frame007_links_0064)
theorem record006_frame007_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 7 :=
  of_group record006 7 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record006_frame007_indices record006_frame007_graph record006_frame007_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (Fin.cases (record006_frame004_supported hcells) (Fin.cases (record006_frame005_supported hcells) (Fin.cases (record006_frame006_supported hcells) (Fin.cases (record006_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x34a1562a8952fa92d23c8fa473a2fd06081c4061fecfd27d63e39e54afa555295945c7d43c61d98e2c5f82e816c0b1c56a2a2149898447220f10408043f41f30f6078c3b81c20da069832e1910c505ec2ce1520a204f426a12809084641fc0f6078023811a07103681ac0d406102e81700b605702b01540a803901a80cc064029012809004601f00f007403801500a004402000f0070030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x65f5c95bd5ab59d52751850c4f64bb4b44ae4a94a249b4954833f23e63d43c834c33c33131d2e02d82d22cd2c62c02bb2ae28924924023322721d2132061f91d51c41b119819118617215513e12c1211141010f60ec0c50bc0b808408306e06a06806705f05b05a05905505405305203803403203102902502402301f01e01d01c01501401101000f00e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x12b62243c8630a5e53bf76ee85b4b616b0d49a5b4467ccc56b2cc57cac92d2504948e9031fd3ea7bcf41e03b6738dd9a233e668ca98f31460cbe96c2c0550a193d26c49c8b1021ea3c0738d91a4328590aa1481f03d8670c6188308580a814c2904e09a130258370660c41802804a0901181f03c0740e0150280440800f01c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record007_frame003_links_0000 record007_frame003_links_0064)
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x2fb5510a7152fa92d2b293649623fd0e285c42420d103e8063f99ec4d2c6793301944b1456e2b2950c9a44c1258128892848123811088023ad1cd8e306f636c1b10d406762f41698ae052628113789204201e00e186e43541860bb0594242110080823811a07103681ac0d406102e81700b605702b01540a803901a80cc064029012809004601f00f007403801500a004402000f0070030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record007_frame004_links_0000 record007_frame004_links_0064)
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
def record007_frame005_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6ce5e85d85cd5c153d52a52550e4c94bd4b14a749a48c4844643ad39f3933873012f22eb2d428f28327726a25f25224a22a2091e11d91d01c81bf1b91b41ad19017f17016515f15714913212211611010c1010f90f20da0d40d008a08906f06b06906805f05b05a05905505405305203903503303202902502402301f01e01d01c01501401101000f00e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record007_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record007_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record007) (record007.maps 5)
      (record007.inverseMaps 5) record007_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record007_frame005_links_0000 record007_frame005_links_0064)
theorem record007_frame005_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 5 :=
  of_group record007 5 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record007_frame005_indices record007_frame005_graph record007_frame005_links
def record007_frame006_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x1019d3397720e19a033465ac717c2f25d6b9d712da5a8b1d32a5749e918ff1f23d8774dc9b335a6a4d219d32e62cba95f2b0544a51412744cc9712423644c851062023d0710d61a232c640bd1742cc4d0951221b8368600ba16c2d0540a21402784b094124240340620bc1702804a0901181f03c0740e0150280440800f01c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record007_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record007_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record007) (record007.maps 6)
      (record007.inverseMaps 6) record007_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record007_frame006_links_0000 record007_frame006_links_0064)
theorem record007_frame006_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 6 :=
  of_group record007 6 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record007_frame006_indices record007_frame006_graph record007_frame006_links
def record007_frame007_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0xe359d332656c9572adc5aeb29522a0534a5547a8b50c9e919228440868ef9db3ae728d31a1338658c918c3105f0b214928a4fc9d9362624b49391a22041c7e8f91ea3a8700d1194318608b81662b44f89b12e1d0398620be1742e0540a013c2704a092120238350620bc1702804a0901181f03c0740e0150280440800f01c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record007_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record007_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record007) (record007.maps 7)
      (record007.inverseMaps 7) record007_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record007_frame007_links_0000 record007_frame007_links_0064)
theorem record007_frame007_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 7 :=
  of_group record007 7 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record007_frame007_indices record007_frame007_graph record007_frame007_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (Fin.cases (record007_frame005_supported hcells) (Fin.cases (record007_frame006_supported hcells) (Fin.cases (record007_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x191aa284d725f52de9614ac24c124491b489a4191fe8f7478a370d2c5e32b094f4a3050324d11dc8ce454219108c8224021e88dd05e42ce1548a504562080fc07943861b40d1064c2c41560a7852028213a099847822e10a07b03bc12608e04681c00d606a03101840bc05c02d81600ae05602a815007003301900a8052026012008c04001f00f007403801500a004401e00e0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a50a5f4db24c92188e7469219108483040f1fecfd27d83e41e54a564821ff0f6076639e1980c385f82ea1638ad454829413088e44101fa0f6078c3761ad0d3067832218a0c105f02ce1600ac854829614409e84a024211307f03dc12608e04681c00d606a03101840bc05c02d81600ae05602a815007003301900a8052026012008c04001f00f007403801500a004401e00e0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x193a9c4e29712b2504968ed1aa3245c8a51322244085cd417d2d0588ae15728e5049f13a26a4c89712c2464507f8f91e63b86f0d81aa344660c918a30c5d0b716c2d45a0b31642bc570ac1522a0438821021a8328640b816c2c0560aa1482885009e1381c0330640a81482604808c1001f03c0740e0150280440780e0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
def record008_frame004_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x1ababa51a9e13926c4ce95d28a4e4949152123e4788ccda1872e45b0b31612a252ca414427e4f09c13625a478849031fa3e0740e21be36c6b0d319e334620c11802fc5f0bd1782e45c0b61662c84788a1121b8348680c017c2e05a0b21582a8540a61481c0330640a81482604808c1001f03c0740e0150280440780e0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record008_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record008_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 4)
      (record008.inverseMaps 4) record008_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record008_frame004_links_0000 record008_frame004_links_0064)
theorem record008_frame004_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 4 :=
  of_group record008 4 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record008_frame004_indices record008_frame004_graph record008_frame004_links
def record008_frame005_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x17daa5f4eaa5ad29092c48ba2790f687142f20d103e8083fa1ec4cc05ea2cb95ecaca55627c936c9a44c32511250906471221100473637b1b10d405c62c215c0a9c50226f12d09244201fd0f707803a21c30dc86182ec151090844412608e04681c00d606a03101840bc05c02d81600ae05602a815007003301900a8052026012008c04001f00f007403801500a004401e00e0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record008_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record008_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 5)
      (record008.inverseMaps 5) record008_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record008_frame005_links_0000 record008_frame005_links_0064)
theorem record008_frame005_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 5 :=
  of_group record008 5 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record008_frame005_indices record008_frame005_graph record008_frame005_links
def record008_frame006_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6ce5cd57d54553252551a4df4ce4c94bf4a749a48e4854643933433092fa2eb2e02a229428f28526a25f25424b22a2091d91c81b91b418817717016b15f15714e14a13212d12812211c1161101010f90ee0da0d508f08a08906e06906806005f05c05a05905605505405305203803303202a02902602402302001f01e01d01c01501401100f00e00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record008_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record008_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record008) (record008.maps 6)
      (record008.inverseMaps 6) record008_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record008_frame006_links_0000 record008_frame006_links_0064)
theorem record008_frame006_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 6 :=
  of_group record008 6 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record008_frame006_indices record008_frame006_graph record008_frame006_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (Fin.cases (record008_frame004_supported hcells) (Fin.cases (record008_frame005_supported hcells) (Fin.cases (record008_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x97f9038f18e48d68c48937f77df7ce7bf7a87367226c36b069d61959d58c57f57056253e4bd4ab49d4904804204103c23b33a33792e72d82cc2be2ac2a029628627526725a22821a2091fa1c21ba1ae1a019118315614613712b0f10e60d90cc0be0b206f06e06906806706005f05a05905803903803303203102a02902402302201501400f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x2b8d4bea4c51b288541c9d549624612008ea46a21690887d93e19eb0de26603291900c5e61e2f51594aae54429b14a097e4ac22e113487a4011b10d4467832918b8c185e82e31698b08570281137896c4921fd0f707803a21c30dc86182ec1660a8843c1fe0f2072835818e07103801ac0d406903101840b805b02d00e407003301900c4054029012008c04401500a003c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x12522d4518911061d4347dcf91ecbcf788e65c93686bed6d912ef5ceb7d6cad1592a394227a4e49a5242434468710ca083766d8d81ab34a67ccc19231c618c01672bc54ca512d2504848e9172203e8788e61b62c05389d12823c448610c016c2d0590a814c2704d0980dc1b0310600bc1502904808c1101502803c0700d01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame003_links_0000 record009_frame003_links_0064)
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
def record009_frame004_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0259.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0259.count (({ width := 9, code := 0x405fefe7ebf1f6f97bbd5e6f177b69acca6330d7ebc5d2e16cb459ac962b057ab93497462250c8441a0902803f9f4f6793b9d4e66d359a4ce5f2e96cb2572a9449e4d25914843f1e0dc662d160ac54291409c4c251207c3c1d0e06c34190c05c2c110803c1c0d0602c14090401c0c050200c0401 } : Fields).get c.val)
theorem record009_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0259.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record009) (record009.maps 4)
      (record009.inverseMaps 4) record009_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame004_links_0000 record009_frame004_links_0064)
theorem record009_frame004_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 4 :=
  of_group record009 4 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0259
    Papers.RationalityTen.SharedFrameCatalogue.group0259_facts record009_frame004_indices record009_frame004_graph record009_frame004_links
def record009_frame005_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x2df1560a9c54429e14cca104a224c123890c47d230d178899449222ce4e67232f192cc726282e91474a124f6272134c93a49623a91bc8d240318c8c0c5de2da1638ae455229914509e84d623c116887441c1d60e306d834e1970c4056429413a09583dc1e00e9071036c1a807103801ac0d406903101840b805b02d00e407003301900c4054029012008c04401500a003c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record009_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 5)
      (record009.inverseMaps 5) record009_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame005_links_0000 record009_frame005_links_0064)
theorem record009_frame005_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 5 :=
  of_group record009 5 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record009_frame005_indices record009_frame005_graph record009_frame005_links
def record009_frame006_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x6015ab59e59358a57e56250c5024f74eb4df4b34ad48f48948242a3d43c93bc3b23a538733132631e30f3022d72d12b62b22ad2892132071fa1f01e41db1d51cc1c41b91b119118617c17314b14613e13412c1211010f60ed0e50bb0b70b20ab0a409e06e06d06806706606005f05a05905803803703203103002a02902402302201501400f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record009_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record009) (record009.maps 6)
      (record009.inverseMaps 6) record009_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame006_links_0000 record009_frame006_links_0064)
theorem record009_frame006_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 6 :=
  of_group record009 6 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record009_frame006_indices record009_frame006_graph record009_frame006_links
def record009_frame007_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x6d467166465364b63f6195b65a959859058555354c52852151b47b40f4023f13e63db3ae34233532431930e2de2d72b52af2aa27d2041f41e91de1d41cb1c31bc1b51ae1a818f18617c17014b14313c13512e12810d1070fc0f00ce0c90c30c00bd0b707107006b06a06906206105c05b05a03903803303203102a02902402302201501400f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record009_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record009) (record009.maps 7)
      (record009.inverseMaps 7) record009_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame007_links_0000 record009_frame007_links_0064)
theorem record009_frame007_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 7 :=
  of_group record009 7 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record009_frame007_indices record009_frame007_graph record009_frame007_links
def record009_frame008_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0253.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0253.count (({ width := 9, code := 0x5167f3e9ecee7335984ba592b9545e290d8541dfcf87bbd9e8f2773a5cee57238da0cd6330d80ae4da6530974b251228e45a210c8341200fc74391bcd86933174b65a2c9449c4b24118863c1d8e872381b0d46833190a04e261289044211007c3c110803c1c0d0602c14090401c0c050200c0401 } : Fields).get c.val)
theorem record009_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record009) (record009.maps 8) (record009.inverseMaps 8) record009_frame008_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record009) (record009.maps 8) (record009.inverseMaps 8) record009_frame008_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record009) (record009.maps 8)
      (record009.inverseMaps 8) record009_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame008_links_0000 record009_frame008_links_0064)
theorem record009_frame008_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 8 :=
  of_group record009 8 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0253
    Papers.RationalityTen.SharedFrameCatalogue.group0253_facts record009_frame008_indices record009_frame008_graph record009_frame008_links
def record009_frame009_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2cfd4bea4c51ba8914209b6473a34d1808ad44d20690107b23d11e40c1652b28c140c9e04dc2410ecc73e38c1bc8d985cc2d413f09b84b82390f607903ba1d70e807243841bb0da06b434c1910c5060c2f81600ac854829614409e84a024211a08983d41dc0e707003641a607103801ac0d406903101840b805b02d00e407003301900c4054029012008c04401500a003c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record009_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 9) (record009.inverseMaps 9) record009_frame009_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 9) (record009.inverseMaps 9) record009_frame009_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 9)
      (record009.inverseMaps 9) record009_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame009_links_0000 record009_frame009_links_0064)
theorem record009_frame009_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 9 :=
  of_group record009 9 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record009_frame009_indices record009_frame009_graph record009_frame009_links
def record009_frame010_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6255cd5c25b65ac59f57d52551b50f5054f84bb4ad47646a45f3eb39338837c36f3653432eb2e12d52c82bf28127323922f2252091b91b51ae1a81a019819018817f17717015f15714f14a12d12812211c1161101010f90f30ee0d30ce0c70bf0b80b206f06e06906806706005f05a05905803903803303203102a02902402302201501400f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record009_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record009) (record009.maps 10) (record009.inverseMaps 10) record009_frame010_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record009) (record009.maps 10) (record009.inverseMaps 10) record009_frame010_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record009) (record009.maps 10)
      (record009.inverseMaps 10) record009_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame010_links_0000 record009_frame010_links_0064)
theorem record009_frame010_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 10 :=
  of_group record009 10 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record009_frame010_indices record009_frame010_graph record009_frame010_links
def record009_frame011_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0258.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0258.count (({ width := 8, code := 0x9a9897969492918f8e8d8b8982817b7977757472706f6e6c6b696766655d5b565553514f4e4d4c4b4a49484746454241403f3b3a39383736333231302c2b2a29272524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0258.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0258.localPairCheck (smallEmbedding record009) (record009.maps 11) (record009.inverseMaps 11) record009_frame011_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0258.localPairCheck (smallEmbedding record009) (record009.maps 11) (record009.inverseMaps 11) record009_frame011_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0258.localPairCheck (smallEmbedding record009) (record009.maps 11)
      (record009.inverseMaps 11) record009_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame011_links_0000 record009_frame011_links_0064)
theorem record009_frame011_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 11 :=
  of_group record009 11 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0258
    Papers.RationalityTen.SharedFrameCatalogue.group0258_facts record009_frame011_indices record009_frame011_graph record009_frame011_links
def record009_frame012_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x75d6e46d26c66bc6af66e5e65d15c35b65a556555d53352b5244743ec3d73c93bc3ab36f2f62e42d82ce2c128227a2502482412201d81d01c91c31bd1b71b01a81a119919017917116916214513e13612f12711e1070ff0f70f00d40d00cc0c80c40c007107006b06a06906206105c05b05a03903803303203102a02902402302201501400f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record009_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record009) (record009.maps 12) (record009.inverseMaps 12) record009_frame012_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record009) (record009.maps 12) (record009.inverseMaps 12) record009_frame012_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record009) (record009.maps 12)
      (record009.inverseMaps 12) record009_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame012_links_0000 record009_frame012_links_0064)
theorem record009_frame012_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 12 :=
  of_group record009 12 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record009_frame012_indices record009_frame012_graph record009_frame012_links
def record009_frame013_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x11a618c2a84307209bfc76eeb9d139b720d81abb3966acc181abe566aad512975049292123b46a8b0fe1f43ac748e69bb314610bf17b2f05ccb61672c0564aa13d26c4bc9410f2144087e0f51e0364690cb1882a45189f1382604a0670cc188308600b2160298520a20dc1b0310600bc1482804808c1101502803c0700d01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record009_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record009) (record009.maps 13) (record009.inverseMaps 13) record009_frame013_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record009) (record009.maps 13) (record009.inverseMaps 13) record009_frame013_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record009) (record009.maps 13)
      (record009.inverseMaps 13) record009_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame013_links_0000 record009_frame013_links_0064)
theorem record009_frame013_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 13 :=
  of_group record009 13 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record009_frame013_indices record009_frame013_graph record009_frame013_links
def record009_frame014_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1000.count (({ width := 11, code := 0x112a08c09804ff9fb3e073ee59c73876fad49a532a648c756ca9851ea1d3fa764c48a510a1a426838f21dc3766d4d799a2cc58cb015d2b054ca69482864fc9d12a2444708c1001f63dc790ed1ce358678c918a2b8560a61402744d0620c21702d85a0ae1582885009e0d81a83005e0b81502904808c1101502803c0700d01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record009_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record009) (record009.maps 14) (record009.inverseMaps 14) record009_frame014_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record009) (record009.maps 14) (record009.inverseMaps 14) record009_frame014_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record009) (record009.maps 14)
      (record009.inverseMaps 14) record009_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame014_links_0000 record009_frame014_links_0064)
theorem record009_frame014_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 14 :=
  of_group record009 14 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1000
    Papers.RationalityTen.SharedFrameCatalogue.group1000_facts record009_frame014_indices record009_frame014_graph record009_frame014_links
def record009_frame015_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0xd4995b2663ec6d8b3085aeb4565ac6582a7d4ca814f89e528a2043684d0720a3fc75ce89cb38c70cd019b3045f8bd9642624b8941232404748d115220430838f91ea3bc758dc1b0344670ca18c2e0598ae1522684b09211c230450620c21742e05b0aa1502784e09a0d41a02f05c0b41482804808c1101502803c0700d01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record009_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record009) (record009.maps 15) (record009.inverseMaps 15) record009_frame015_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record009) (record009.maps 15) (record009.inverseMaps 15) record009_frame015_indices (Fin.ofNat record009.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record009_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record009) (record009.maps 15)
      (record009.inverseMaps 15) record009_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record009_frame015_links_0000 record009_frame015_links_0064)
theorem record009_frame015_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 15 :=
  of_group record009 15 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record009_frame015_indices record009_frame015_graph record009_frame015_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (Fin.cases (record009_frame004_supported hcells) (Fin.cases (record009_frame005_supported hcells) (Fin.cases (record009_frame006_supported hcells) (Fin.cases (record009_frame007_supported hcells) (Fin.cases (record009_frame008_supported hcells) (Fin.cases (record009_frame009_supported hcells) (Fin.cases (record009_frame010_supported hcells) (Fin.cases (record009_frame011_supported hcells) (Fin.cases (record009_frame012_supported hcells) (Fin.cases (record009_frame013_supported hcells) (Fin.cases (record009_frame014_supported hcells) (Fin.cases (record009_frame015_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x646a8a135c9614aca54929894549f24dd260929491246d22490b47c23c51b66962f19460a084f3270934497c4ac24d12208ee46722991048244021e80dd055229514209c84c424f11e88ac4322080fc07903a41a30c985842ac14f0a4050427413308f045c22010a06b823811a06b03501880c205c02d81680b205802b81580a803301900a8052024011808804202000f807803801500a003c01c00d006002c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
def record010_frame002_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x694297d36c8e7469a30115a89a44421d90c885242120c103a80b3ec9f20f2852b2410ecc73e38c1bc8d986a83421980c7861c2fc1748b5c54a29413008e43d81e40ee875c3a01c90e106ec3681ad0d3067432c1830be05982c01590a9052c28813d094048423411306d823811a06b03501880c205c02d81680b205802b81580a803301900a8052024011808804202000f807803801500a003c01c00d006002c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record010_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record010_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 2)
      (record010.inverseMaps 2) record010_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record010_frame002_links_0000 record010_frame002_links_0064)
theorem record010_frame002_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 2 :=
  of_group record010 2 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record010_frame002_indices record010_frame002_graph record010_frame002_links
def record010_frame003_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x6aeae946a6c4d099531a604ba9692ba544a293924a4647e8f1191b430e598b115f2ba568ab9542a2538a59482865009c9362584787e8f91ec3d0788ee1d63a0728e21be3686b8d019a30c608c017e2f85e8bc1722e05b8b615c228448690d01802f85a0b21602b8560aa150290330640a8148240460881082003e0780e01502803c0700d01802c0500900e0180280400600800800 } : Fields).get c.val)
theorem record010_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record010_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record010) (record010.maps 3)
      (record010.inverseMaps 3) record010_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record010_frame003_links_0000 record010_frame003_links_0064)
theorem record010_frame003_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 3 :=
  of_group record010 3 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record010_frame003_indices record010_frame003_graph record010_frame003_links
def record010_frame004_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1111.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1111.count (({ width := 10, code := 0x97a1b7e1d9755d2741cd729c8715c26fdbc6ddb46b5aa68173541314b52a4a125489204751a45d1443d0c415023e0eb330c8314c3300bd2ecb82d4b22bcaa29ca0274932449023c8e2348c2248821c861f86c1ac5a164511404b12849120471184510c330c82a0a42408c220842007c1e070150500f0380d0300b0280901c060140400c0200400 } : Fields).get c.val)
theorem record010_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record010_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record010) (record010.maps 4)
      (record010.inverseMaps 4) record010_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record010_frame004_links_0000 record010_frame004_links_0064)
theorem record010_frame004_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 4 :=
  of_group record010 4 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1111
    Papers.RationalityTen.SharedFrameCatalogue.group1111_facts record010_frame004_indices record010_frame004_graph record010_frame004_links
def record010_frame005_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa4e9038937f77df7ce7bf7a879b79078076f7607507397256ed6db6a159d53e4bd4ab49d49048047546d4604524444364234133e63d83a73792e72d82cc2be2ac2a029628627526725a2472372091fa1cc1c21ba1ae1a019118315614613712b0c008808706906806005f05a05905805705605505405203303202a02902402302202102001f01e01c01501400f00e00d00c00b00a009007006005004003002001000 } : Fields).get c.val)
theorem record010_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record010_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record010) (record010.maps 5)
      (record010.inverseMaps 5) record010_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record010_frame005_links_0000 record010_frame005_links_0064)
theorem record010_frame005_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 5 :=
  of_group record010 5 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record010_frame005_indices record010_frame005_graph record010_frame005_links
def record010_frame006_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x66a57652b4cb4be4b04aa49e49548f48347846c4654574484264193fa33d2f229228427927126525c25324a23d23522c21c20f1ea1e11c11ac17116b16516115d15715414f14914313d13613012511f10f10c10a1051000fb0f60e50e00da0d40ac08007f06406305b05a05505405305205105004f04d03303202a02902402302202102001f01e01c01501400f00e00d00c00b00a009007006005004003002001000 } : Fields).get c.val)
theorem record010_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record010_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 6)
      (record010.inverseMaps 6) record010_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record010_frame006_links_0000 record010_frame006_links_0064)
theorem record010_frame006_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 6 :=
  of_group record010 6 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record010_frame006_indices record010_frame006_graph record010_frame006_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (Fin.cases (record010_frame002_supported hcells) (Fin.cases (record010_frame003_supported hcells) (Fin.cases (record010_frame004_supported hcells) (Fin.cases (record010_frame005_supported hcells) (Fin.cases (record010_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xd56684adf1560a104a223b91ce8e046ca3491968b6457a2a114288c39399c8ba451d26393009724b2256129492048924111f08d440318c8ae455229914509e84d623c116887441c1e40eb071836c1a70cb86202b214a09d04ac202094049823811a07103801ac0d406203081700b605902c015c0ac05502a00e407003301900a8052024011808404001f00f007403801500a003c01c00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xd60646abed4509ae4b0a4f926e930494a48923690647fa3e11e28dc3ba9a58bc651825f12b093448823b919c86442320910087a2374154893c47a22b10c88203f01c30da068c3261620ab053c29014109d04cc23c11708804281ec094049823811a07103801ac0d406203081700b605902c015c0ac05502a00e407003301900a8052024011808404001f00f007403801500a003c01c00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record011_frame002_links_0000 record011_frame002_links_0064)
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1105.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1105.count (({ width := 8, code := 0xd9d8d3d2cecdc9c8c7c6c5c4c1c0bfbebbb1ab9f99939291908f8e8b8a8988857e787271706f6e6d6a69686764636261605f5e5b5a59585551504e4d484745443f3e3c3b3938373635342a29272621201e1d1b1a1918171612110f0e0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1105.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1105.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1105.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1105.localPairCheck (smallEmbedding record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record011_frame003_links_0000 record011_frame003_links_0064)
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1105
    Papers.RationalityTen.SharedFrameCatalogue.group1105_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
def record011_frame004_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xe286942cfd4be9b6473a2210ec86442921090607fb3f49f64f9079530594ac9043b31aa0d0866031e1870bf058e2b51528a504c22390f607243841bb0da06b434c1910c5060c2f81670b005642a414b0a204f425012108d044c1fc094049823811a07103801ac0d406203081700b605902c015c0ac05502a00e407003301900a8052024011808404001f00f007403801500a003c01c00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record011_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record011_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 4)
      (record011.inverseMaps 4) record011_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record011_frame004_links_0000 record011_frame004_links_0064)
theorem record011_frame004_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 4 :=
  of_group record011 4 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record011_frame004_indices record011_frame004_graph record011_frame004_links
def record011_frame005_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x86582275d6e466e5e659758e58657e57656e55554c54453c5254743ec36f2f62b42ab2a329b29328b2722692612592422201d81b71b01a81a119919017917116916214c14513e13612f12711e1070ff0f70f00da09409308e08d07107006b06a06206105c05b05905805705605505403903803303202a02902402302102001f01e01d01c01501400f00e00c00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record011_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record011_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record011) (record011.maps 5)
      (record011.inverseMaps 5) record011_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record011_frame005_links_0000 record011_frame005_links_0064)
theorem record011_frame005_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 5 :=
  of_group record011 5 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record011_frame005_indices record011_frame005_graph record011_frame005_links
def record011_frame006_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x35b64eb414e2714a09051f23b4708d51922944c88d102173b86a0be95c29a528a39442824f89a93225e4b0919141e6390708de1b63606a8cc192318618ba16e2d85a8b41662c8578ae15a2b05488810e2084086b0d41943205c0b61582a8530a41442804f09c0e41c0330640a8148240460841001f03c0740e01502803c0700c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record011_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record011_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record011) (record011.maps 6)
      (record011.inverseMaps 6) record011_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record011_frame006_links_0000 record011_frame006_links_0064)
theorem record011_frame006_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 6 :=
  of_group record011 6 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record011_frame006_indices record011_frame006_graph record011_frame006_links
def record011_frame007_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x3926aebd55d28d4d89752d2574a8945272454848fd1e2333de6d0c39662ae550a894e2965209f93c2724d89691e1fa3b8758e81ca3886f8d61a6340668c41823005f8be17a2f05c8b816e2d85989011e2284486f0dc1a4340600be1682c8570ac1542a0530a40e41c0330640a8148240460841001f03c0740e01502803c0700c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record011_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record011_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record011) (record011.maps 7)
      (record011.inverseMaps 7) record011_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record011_frame007_links_0000 record011_frame007_links_0064)
theorem record011_frame007_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 7 :=
  of_group record011 7 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record011_frame007_indices record011_frame007_graph record011_frame007_links
def record011_frame008_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1104.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1104.count (({ width := 10, code := 0x215809ed769c66c9a06759a65d9464588615825fd775a5554fd2c47d1c4651644d1041d04404fe3d8ef370cf330c9318c3300b72d0b12b8a628ca02749a25c9422c88214821e86418c5e174511404b128471184410c411003f0f83d0f0360d4330c82a0a42408c210801f0781d070150500f0380c02c0a0240801c060140400c0200400 } : Fields).get c.val)
theorem record011_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1104.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record011_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record011) (record011.maps 8)
      (record011.inverseMaps 8) record011_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record011_frame008_links_0000 record011_frame008_links_0064)
theorem record011_frame008_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 8 :=
  of_group record011 8 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1104
    Papers.RationalityTen.SharedFrameCatalogue.group1104_facts record011_frame008_indices record011_frame008_graph record011_frame008_links
def record011_frame009_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1103.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1103.count (({ width := 10, code := 0x215809ed769c66c9a06759a65d9464588615825fd775a5554fd2c47d1c4651644d1041d04404fe3d8ef370cf330c9318c3300b72d0b12b8a628ca02749a25c9422c88214821e86418c5e174511404b128471184410c411003f0f83d0f0360d4330c82a0a42408c210801f0781d070150500f0380c02c0a0240801c060140400c0200400 } : Fields).get c.val)
theorem record011_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1103.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record011_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record011) (record011.maps 9)
      (record011.inverseMaps 9) record011_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record011_frame009_links_0000 record011_frame009_links_0064)
theorem record011_frame009_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 9 :=
  of_group record011 9 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1103
    Papers.RationalityTen.SharedFrameCatalogue.group1103_facts record011_frame009_indices record011_frame009_graph record011_frame009_links
def record011_frame010_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xabca4e97f9038937f779b79078076f7607507137006ed6db6a261959d53e4bd47546d4604524444364043f53e63d83a83792e72a029628627526725a22821a2091fa1cd1c21ba1ae1a019118315614613712b0fe08e08d08808706f06e06906806005f05a05905705605505405305203903803303202a02902402302102001f01e01d01c01501400f00e00c00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record011_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record011_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 10)
      (record011.inverseMaps 10) record011_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record011_frame010_links_0000 record011_frame010_links_0064)
theorem record011_frame010_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 10 :=
  of_group record011 10 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record011_frame010_indices record011_frame010_graph record011_frame010_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (Fin.cases (record011_frame004_supported hcells) (Fin.cases (record011_frame005_supported hcells) (Fin.cases (record011_frame006_supported hcells) (Fin.cases (record011_frame007_supported hcells) (Fin.cases (record011_frame008_supported hcells) (Fin.cases (record011_frame009_supported hcells) (Fin.cases (record011_frame010_supported hcells) (fun j => Fin.elim0 j))))))))))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0x97d8a888687686184b8378247f77d47c07aa79678176e7407297126fc5dd52750e5014ee4e14d34c449b48247746645944a43d41b40d3fc3ee36b35834d34133131f2fa2ea2d82c72b72ad2a12932862652552462322232132011f01cd1b51a819718717816b1561030bf07b07105d05c05b05a05805705605504303902502402302202001f01e01d01501101000f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
def record012_frame002_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x524256526c92c48b24051d48d444f21ed0e285c424a0d103e7f23ee1f18f5e64e2c515b8aca5552a294d8a504f926d93489824b125112508de45f228110075a39b1c60dec6d836219e8ca462e30617a0b8c5a62c215c0a5050226f12c891c46822210707803861b90d5066030c1760b2844019207b03881740b805b02d01600ae05602a810c072025012008c04402000f807803a015008804001e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record012_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record012_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 2)
      (record012.inverseMaps 2) record012_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record012_frame002_links_0000 record012_frame002_links_0064)
theorem record012_frame002_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 2 :=
  of_group record012 2 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record012_frame002_indices record012_frame002_graph record012_frame002_links
def record012_frame003_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xb76a6a7a9aa4689a0a7b9ce6e9ae61972549323d8e2338c1ee701bc6e9b16b1a66819764d916157f5e171591615795a4e1344c12d4a52645d1142d0640d003f8fb3e4eb398e1360d4340cc324bd2d8b32b0a527c9924073174501303e0f43c0ec390e0370d8340c0220842007c1d0701b068150441003c0e0340c02c0a024080140400c0200400 } : Fields).get c.val)
theorem record012_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record012_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record012) (record012.maps 3)
      (record012.inverseMaps 3) record012_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record012_frame003_links_0000 record012_frame003_links_0064)
theorem record012_frame003_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 3 :=
  of_group record012 3 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record012_frame003_indices record012_frame003_graph record012_frame003_links
def record012_frame004_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0785.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0785.count (({ width := 10, code := 0x815e4779db759d2739ca711c06f9ba6d9b16b1a46859e66d6750d3f4f53a4e1354c92a4992447d1b4550f41d0540d00390e1378db360d5330c6300bb2e4b72d4b32c4a92909f2649624c902388720c811f8791d06f1a45a13049114390e0370d8340cc320c4300b01e0741c06c1906017058150441003c0e0340c02c0a024080140400c0200400 } : Fields).get c.val)
theorem record012_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record012_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record012) (record012.maps 4)
      (record012.inverseMaps 4) record012_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record012_frame004_links_0000 record012_frame004_links_0064)
theorem record012_frame004_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 4 :=
  of_group record012 4 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0785
    Papers.RationalityTen.SharedFrameCatalogue.group0785_facts record012_frame004_indices record012_frame004_graph record012_frame004_links
def record012_frame005_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x55826192c895349ea4b523690a469a2c514088a43d21a10ae84441ea0d905e6512af950ca6a52328c14289f84d225b12a092c48b23e91bc8c045b22b11446da35f1a78cfc66031f17f0bb85ba2cc15f0ab853c28f13f097449a23c11888a844621c10a878036e1a20c685f02d41570a384281a407b03881740b805b02d01600ae05602a810c072025012008c04402000f807803a015008804001e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record012_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record012_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record012) (record012.maps 5)
      (record012.inverseMaps 5) record012_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record012_frame005_links_0000 record012_frame005_links_0064)
theorem record012_frame005_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 5 :=
  of_group record012 5 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record012_frame005_indices record012_frame005_graph record012_frame005_links
def record012_frame006_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x5f456d55554a53d5305235194f94e34da4c94bd4b24a549248c4874803d235834833e33332d32231b3032f22ed2de2d72cf2c62b72b32af2aa24523e23923022621b2091fd1f41ea1e41de1d51c91c41ab1a519918f18a18618117a15f14613a12d11f1131070fb0cd0a207106a05905805705605405305205104103902502402302202001f01e01d01501101000f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record012_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record012_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record012) (record012.maps 6)
      (record012.inverseMaps 6) record012_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record012_frame006_links_0000 record012_frame006_links_0064)
theorem record012_frame006_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 6 :=
  of_group record012 6 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record012_frame006_indices record012_frame006_graph record012_frame006_links
def record012_frame007_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x5b853b52c52951c5115095004e84d84d14c44b94b24a949a49348f48b3a732831b31830c3022fd2f62dc2cf2c92bd2b32ad2a729b29629329022c22521e21520d2091ef1e81e01d51cc1c41c01b91b219819018a18217b17417016c14f13d13712a12011610b0ff0d50ae07706f05b05a05905805605505405304203902502402302202001f01e01d01501101000f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record012_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record012_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record012) (record012.maps 7)
      (record012.inverseMaps 7) record012_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record012_frame007_links_0000 record012_frame007_links_0064)
theorem record012_frame007_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 7 :=
  of_group record012 7 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record012_frame007_indices record012_frame007_graph record012_frame007_links
def record012_frame008_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0751.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0751.count (({ width := 8, code := 0x797574737271706f6e6d6c6b6a6968666564635c5857565554535251504f4e4d4c4b494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0751.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0751.localPairCheck (smallEmbedding record012) (record012.maps 8) (record012.inverseMaps 8) record012_frame008_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0751.localPairCheck (smallEmbedding record012) (record012.maps 8) (record012.inverseMaps 8) record012_frame008_indices (Fin.ofNat record012.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record012_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0751.localPairCheck (smallEmbedding record012) (record012.maps 8)
      (record012.inverseMaps 8) record012_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record012_frame008_links_0000 record012_frame008_links_0064)
theorem record012_frame008_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 8 :=
  of_group record012 8 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0751
    Papers.RationalityTen.SharedFrameCatalogue.group0751_facts record012_frame008_indices record012_frame008_graph record012_frame008_links
def record012_frame009_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0778.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0778.count (({ width := 7, code := 0xd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record012_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0778.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0778.localPairCheck (smallEmbedding record012) (record012.maps 9) (record012.inverseMaps 9) record012_frame009_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0778.localPairCheck (smallEmbedding record012) (record012.maps 9) (record012.inverseMaps 9) record012_frame009_indices (Fin.ofNat record012.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record012_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0778.localPairCheck (smallEmbedding record012) (record012.maps 9)
      (record012.inverseMaps 9) record012_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record012_frame009_links_0000 record012_frame009_links_0064)
theorem record012_frame009_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 9 :=
  of_group record012 9 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0778
    Papers.RationalityTen.SharedFrameCatalogue.group0778_facts record012_frame009_indices record012_frame009_graph record012_frame009_links
def record012_frame010_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x52424791f48e7468a30515a89a432210906081c4069fecfd27c63da9e94f265141f50f1876639d1c68de46cc3301870bf05d02d91638ad4524281138897c41e20810087e83e61ec0ef075c3a01c90e106ec3681ad0d3066032218a0c085e82e616c0b2854828813d09a84bc25012108c83d81aa07b03881740b805b02d01600ae05602a810c072025012008c04402000f807803a015008804001e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record012_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 10) (record012.inverseMaps 10) record012_frame010_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 10) (record012.inverseMaps 10) record012_frame010_indices (Fin.ofNat record012.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record012_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 10)
      (record012.inverseMaps 10) record012_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record012_frame010_links_0000 record012_frame010_links_0064)
theorem record012_frame010_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 10 :=
  of_group record012 10 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record012_frame010_indices record012_frame010_graph record012_frame010_links
def record012_frame011_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x5be53d52a5255195105054f84df4ce4c94bd4b24a749a48347946d4623843012f22eb2df2d62c82bf2a229428f28327826a25f24923c2322281e11d91d01c81bf1b91af1a81a019819018817f17717016615f15714d14814013713012211611010c1081010f90f20d40b407906f05b05a05905805605505405304303902502402302202001f01e01d01501101000f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record012_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record012) (record012.maps 11) (record012.inverseMaps 11) record012_frame011_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record012) (record012.maps 11) (record012.inverseMaps 11) record012_frame011_indices (Fin.ofNat record012.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record012_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record012) (record012.maps 11)
      (record012.inverseMaps 11) record012_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record012_frame011_links_0000 record012_frame011_links_0064)
theorem record012_frame011_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 11 :=
  of_group record012 11 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record012_frame011_indices record012_frame011_graph record012_frame011_links
def record012_frame012_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0xb4344e7fcf89d538e6d4d19672764b4879011da3645a8a9142253725c8b3963ab8562a9d4ea7e4d498d2aa4e48a8f115a2544286cee1d539c718e01b8352688cd992316610be1762dc57cac151294518a113e2744ac8f118222430839021f2348570780de16c2d0590b01582a8540a61081c82504808c1102003e0780e8150220400780e01a0300580a0120200280400600800800 } : Fields).get c.val)
theorem record012_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record012) (record012.maps 12) (record012.inverseMaps 12) record012_frame012_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record012) (record012.maps 12) (record012.inverseMaps 12) record012_frame012_indices (Fin.ofNat record012.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record012_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record012) (record012.maps 12)
      (record012.inverseMaps 12) record012_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record012_frame012_links_0000 record012_frame012_links_0064)
theorem record012_frame012_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 12 :=
  of_group record012 12 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record012_frame012_indices record012_frame012_graph record012_frame012_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (Fin.cases (record012_frame002_supported hcells) (Fin.cases (record012_frame003_supported hcells) (Fin.cases (record012_frame004_supported hcells) (Fin.cases (record012_frame005_supported hcells) (Fin.cases (record012_frame006_supported hcells) (Fin.cases (record012_frame007_supported hcells) (Fin.cases (record012_frame008_supported hcells) (Fin.cases (record012_frame009_supported hcells) (Fin.cases (record012_frame010_supported hcells) (Fin.cases (record012_frame011_supported hcells) (Fin.cases (record012_frame012_supported hcells) (fun j => Fin.elim0 j))))))))))))))
#print axioms record012_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036
