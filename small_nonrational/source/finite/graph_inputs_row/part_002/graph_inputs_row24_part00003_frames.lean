module
prelude
public import GraphInputsRow24Part00003Data
public import RawFrameSupport
public import SharedFrameGroups004Checked
public import SharedFrameGroups005Checked
public import SharedFrameGroups007Checked
public import SharedFrameGroups046Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003
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
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x741b8b1ab2cbd5ca28dd40a9d54c9a39913488f43da1990ae80a3d31e24cc050326892848be3b21b30d6c68e3321918b584e423f11487ac3ba1d00dc85f02da15109704a024210c07783a41c40ac04601c00d206302d81680aa05401c00c4056023011007403801900b005001c00d005802000e0040018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x171acacfe99b23a31c5485106609c0e812f95eebd7754e45c2b1660cbd96cab65509ed332444668750ca154067c0ed1b73445f0b393d2684908d116208340658c116c2c8578960fe1902f85b0aa1502984c08e0f41a03304e0941182003a0700900f01c0280400700600800800 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 79 :=
  interval_of_check _ 64 15 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 79 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
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
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x3281804b1153226713369904baa5a929293949223dd0788083e79ed8f3c7853b99684b3a5912bc15b0aa24081fb0fa47ba3c31dd8ebc7263871b588484001f40f387743981b00d586783241880bd85bc2c613f09604982340fe077036c1a20c3055029c14409104582100fe06e02380d805c027012809003c01d00e00640240100078024010007 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x3921a46be355f271d38c9bf4d8a6a932c9864bfa5cd25691647e23cd1d88e446e98a4c4060d2f4175cb4e4011f80f847a23ba1d88e786f236819c06483021720b105602a21470a184ec26812e093047c22c10908183f81ee0ea07203701ac0d0057029c14409104582100fe06e02380d805c027012809003c01d00e00640240100078024010007 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x6165bf56150a4b64b54af4a449e49048848147542c4184013f83f13ea3e332131f31930a3052f323e23523122a21c21a2152072011ee13913012b12411e11810f10c1050ff0fb0f40ee0e70dd0d70d40cf0c40be0b80b50b009d09909608708107d07a06b04703602e02702502401e01d01c01901201000f009008007 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xa8e9fe8a576574d73671c7056d96495ad5a759e58e58056841c40e3fe3f03d73cb3bb3ac36a3572a02742242142031f21cc1b81ab18a17b1661401301281170fa0ed0d70c80ba0a009108b08407f06e05304c04703602e02702502401e01d01c01b01a01901801501201000f009008007 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x2c454c88f73e79ed8f3c7853b99c8ccba5a42cd1638aea5692a910207ec3e91ee8ed475238d1c08d3c67227712888484001f40f386c033c1920bd85bc2c613f09604982340fe077036c1a20c3051024411608403f81b80a604c02380d805c027012809003c01d00e006c03401900c00540240100078024010007 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x193cc4551d277131c9204619fe8fd27953b51c44a0c4a822d0fb071e2c615a898449824511c08c441c1ff0fc87cc3b81b30cb864031417b0b385602a214a09e84b824211208603f81d208d04582140d406002d81580aa0540298134064028011807803a01c00d806803201800a004c02000e004802000e0040018008002000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
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
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1998c90622aed562ca9f51d28493b8993490230d1307fb3f41edcf4c7953ae1c44d025e22b594189bc4a822f8fb071e3641638ad0506272130893048a238114888c43a20e0ff87e43e61dc0e707043741970c886242f61750b6859c2b01510a504f425c12808904301fc0e2045817c0b605702a81500a6027011807c03a01c00d806803201800a004802000e005002000e0040018008002000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x180cbdd5d3ada55c8a84521a8d53f29b24a6a4151ec8414182004fe07e73db1da8e3a6a132017fcbe65c02c194b89e84e922e914085c42120d0fd07c03bd1ce0e346fc35d19e0cb463c2fd1780b3457025a12688f444021310187e83b41c70db06482ec16c0a284ec24c0e9045817c0b605702a81500a6027011807c03a01c00d806803201800a004802000e005002000e0040018008002000 } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record020_frame002_links_0000 record020_frame002_links_0064)
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
def record020_frame003_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x6d26ba69a66c62b5f25c85bb5a457c54751c50e4ba4b149448948146a44b41c3d939f37836b3543292f22cc2be26425924123823122221b20e1fb1f51ee1dd1ca1c41bd1ab1a319719016c16415a14914113713112812211d1131050ff0eb0e50d90c308b05f05b05705505405302702301f01d01c01b01a01901801401201000e00a008007004003002001000 } : Fields).get c.val)
theorem record020_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record020_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record020) (record020.maps 3)
      (record020.inverseMaps 3) record020_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record020_frame003_links_0000 record020_frame003_links_0064)
theorem record020_frame003_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 3 :=
  of_group record020 3 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record020_frame003_indices record020_frame003_graph record020_frame003_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (Fin.cases (record020_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0049.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0049.count (({ width := 8, code := 0x86827f7c7b7a79767472716f6e6c68666361605f5c5a595854535251504d4b4948474542403d3c3b393735333231302f2c2a2827262524232221201f1e1c1b1817161514110f0d0c0b080706050403020100 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0049.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0049.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0049.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0049.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0049
    Papers.RationalityTen.SharedFrameCatalogue.group0049_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0605.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0605.count (({ width := 10, code := 0xe176bcc325c831dbbeeab36c4a6e96a46879de4d90e338b62b88df77c9d06dda368197649765494b515404e11b4390941d033ecec354d133cca318c52dc9c25c9022c8a214801f4761c85f1745914c49118380d0320ac220781203c0e034090200400400 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0605.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0605.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0605.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0605.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0605
    Papers.RationalityTen.SharedFrameCatalogue.group0605_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0606.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0606.count (({ width := 11, code := 0xa854b23dbf27cef75ddb7f6e8da1adb5068ed0d9bb2b650bb9632bd56ea653ba6d4c89190aa0d3fa7bcda99c316600ba95b2644b08e1112183d4600b715628c4e8931182143c8720c6178270450780ec1c0360680b81682c0480841001201e0380680901001000800 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0606
    Papers.RationalityTen.SharedFrameCatalogue.group0606_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
def record023_frame002_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0107.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0107.count (({ width := 7, code := 0x972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record023_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0107.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0107.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0107.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record023_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0107.localPairCheck (smallEmbedding record023) (record023.maps 2)
      (record023.inverseMaps 2) record023_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record023_frame002_links_0000 record023_frame002_links_0064)
theorem record023_frame002_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 2 :=
  of_group record023 2 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0107
    Papers.RationalityTen.SharedFrameCatalogue.group0107_facts record023_frame002_indices record023_frame002_graph record023_frame002_links
def record023_frame003_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0069.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0069.count (({ width := 7, code := 0x972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record023_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0069.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0069.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0069.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record023_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0069.localPairCheck (smallEmbedding record023) (record023.maps 3)
      (record023.inverseMaps 3) record023_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record023_frame003_links_0000 record023_frame003_links_0064)
theorem record023_frame003_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 3 :=
  of_group record023 3 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0069
    Papers.RationalityTen.SharedFrameCatalogue.group0069_facts record023_frame003_indices record023_frame003_graph record023_frame003_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (Fin.cases (record023_frame002_supported hcells) (Fin.cases (record023_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0845.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0845.count (({ width := 11, code := 0x13365347e8b10fa124137acf45dfbb3738e49b63686c4d759eb30634c4d86ac2546a013e2754ae9150b2053c2748e61c63826f8d99a12dc560a3929248478839031fe3e4798ed1ac2ec578a413e2703e8670c21702c8530a40f41c03305209c1182003a0700900f01c0280400700600800800 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0845
    Papers.RationalityTen.SharedFrameCatalogue.group0845_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3331920c3554f28493b8993473a2610cc80a3f41ed8f4c7953ae1c04ad44de254117c7663641990b58568282139098449824511c08a444621d10388003f21ec0e707203721890be05d02da1670ac054429413d09704a01fc0ef074838811607002f81700b605502a014c070027012008c03a01c00d806803201800a004801e00e005802000e0040018008002000 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1994c455b3ac5953ea35508277132692045f22690607fb3f49edce226332f115aca024dc254117c7d838a1b30bf058e2b514189484a224a11d88b84222040fe07d03b61d10e206f436c1a70cd064831617e0bb05ac2c815b0aa053427c131094848822a10d08103ec1cc0df06c034811a08c04581e80d406902d81680ae05602a81500a604201900c404602200f807803a01c } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
def record035_frame001_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0604.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0604.count (({ width := 11, code := 0x3fd7c6efdd3b7f6dad99aeb5361ea714d29852a9e531a5449e92923a4344c7f8f99e83c2770e79c93846d0d49a0336664cb18e2ae5289c1302524748d11520c400798ec1d03886e0d819a3145f8bb1562082784e08e0fc1f03d0780e01903105e0b4118220320500700d00800c01001 } : Fields).get c.val)
theorem record035_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record035_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record035) (record035.maps 1)
      (record035.inverseMaps 1) record035_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record035_frame001_links_0000 record035_frame001_links_0064)
theorem record035_frame001_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 1 :=
  of_group record035 1 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0604
    Papers.RationalityTen.SharedFrameCatalogue.group0604_facts record035_frame001_indices record035_frame001_graph record035_frame001_links
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (Fin.cases (record035_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x730b5919a6b925b52c594209f74f9277d31e8c044d21fd0b68333ff1fb0f747a23c81978c6c5e226e130c97c4ab22d8e306cc34b1938bfc5942b814309b84b82290ee87403741a60cb86443141750a204f425012108984301ce0e006c834c15c06a03481980c205b02d00c806202e014808c04401900a003801a00a004802000e005002000c004001 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x352d9facee5e32e8d6b6a6652d28dd3de8fa471233117e8b7458226d12488b3b41d74e9a70532598a0c266082fc16c09ec4d325c12b494c49624892288fa47723791a48ae42c2020f546802c715d0aa052c289135892447822d100075c38a1b30d306202cc1590a504741e20e9071036c1a806a034816c0b405301e80e006403101700a404602200d006001c00d0050024010007002000c004001 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x6bf34f5878b1956c275d38e9c64dfa6c13469714aaa519272932495a47121e90748023ad1c08d93a81904c5262030696f89e64d124c919c8844322118fc47743b11cf0d3c50826211507e03a61c30da06082b01510a3850c276134092047c23010b08283f01ea0ea07103701ac0d0057023411808b03501a406403101700a404602200f807803a01c00c805001c00d0050024010007 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0604.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0604.count (({ width := 11, code := 0x1fe3bc74cda9b335d6a6c3d77ade5b0b1d4da964a893d25247486898ff1f53d4780e69c836666ccc99631c55ca513a24e47c8c9141fe3a0710dc1b0334628bf1762ac3686c0b816c2784e0961282484808e0c81882f05a08c1101f03c0740e0190280380680a0120200380400600800800 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0604
    Papers.RationalityTen.SharedFrameCatalogue.group0604_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6652d9d62ca104ee264d1348303fd9fa4f6e6332f1137095045f1b30bf058e2b5141893048a23811487e43ba1d00e086e83661a60cb86443141750ac054429413d09704a024210c046823011606a034816c0b405702b01540a805301900c404602200f807803a01c00d806803201800a003801a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
def record042_frame002_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0606.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0606.count (({ width := 11, code := 0x9e73265e47c8df18dff3c8754e89c3b40662bbd72adb50a9611f2354387fcfd1f43d8710d31953105f4bb9692ba550a713a23c44c850ff1e63ac728cb0d61a83485a0b21342604909011c230450600bc1182203e0780e81c0360680c8180280380680a0120200380400600800800 } : Fields).get c.val)
theorem record042_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record042) (record042.maps 2) (record042.inverseMaps 2) record042_frame002_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record042) (record042.maps 2) (record042.inverseMaps 2) record042_frame002_indices (Fin.ofNat record042.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record042_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record042) (record042.maps 2)
      (record042.inverseMaps 2) record042_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record042_frame002_links_0000 record042_frame002_links_0064)
theorem record042_frame002_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 2 :=
  of_group record042 2 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0606
    Papers.RationalityTen.SharedFrameCatalogue.group0606_facts record042_frame002_indices record042_frame002_graph record042_frame002_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (Fin.cases (record042_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
def record049_frame001_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3a0dc26d576652e516f8b1550828153be8ac44d223d0f68664261fe8fd266032417849b84d12558de06cc35b1a38cc86302c615a88a83ac1d00dc86b43301900c505f02a213d09084301de0e904b823411806a03481800b605a02b01540a803201880a004602200f0074038019009803801a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record049_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 64 79 :=
  interval_of_check _ 64 15 (by decide +kernel)
theorem record049_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record049) (record049.maps 1)
      (record049.inverseMaps 1) record049_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 79 record049_frame001_links_0000 record049_frame001_links_0064)
theorem record049_frame001_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 1 :=
  of_group record049 1 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record049_frame001_indices record049_frame001_graph record049_frame001_links
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (Fin.cases (record049_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
def record051_frame001_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1994b7958aa8413b88ac44d2198ff47e932297849b84a81bc0d986642c615a893048a23111507e43ac1d00e406e43661ad0cc064031417c0ac054429413d09084301de0e9046823011606a03481800b605a02b01540a805301900c4050023011007803a01c00d8068032018009803801a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record051_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record051_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 1)
      (record051.inverseMaps 1) record051_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record051_frame001_links_0000 record051_frame001_links_0064)
theorem record051_frame001_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 1 :=
  of_group record051 1 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record051_frame001_indices record051_frame001_graph record051_frame001_links
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (Fin.cases (record051_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record052_frames_supported
theorem record053_frame000_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    Supported record053 0 :=
  of_identity record053 0 (by decide +kernel)
def record053_frame001_indices (c : Fin record053.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1994a104fd27bd3b89904562268ff47e926e13189764a822e0de06cc2c615a893048a23111507e43ac1d00d9864031415f0ac052828813d097848422610c07803a411a08c04581a80d2066030016c0b405602a81500a603201880b8050023011007803a01c00d8068032018009803801a009004001c00a0040018008002000 } : Fields).get c.val)
theorem record053_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record053.data.requiredEdges q = true := by decide +kernel
theorem record053_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record053) (record053.maps 1) (record053.inverseMaps 1) record053_frame001_indices (Fin.ofNat record053.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record053_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record053) (record053.maps 1) (record053.inverseMaps 1) record053_frame001_indices (Fin.ofNat record053.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record053_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record053) (record053.maps 1)
      (record053.inverseMaps 1) record053_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record053_frame001_links_0000 record053_frame001_links_0064)
theorem record053_frame001_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) : Supported record053 1 :=
  of_group record053 1 (smallEmbedding record053) (small_cells_exact record053 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record053_frame001_indices record053_frame001_graph record053_frame001_links
def record053_frame002_indices (c : Fin record053.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x18f2a9c54429d54bea0248d24290ce85731f18bcc4260d2e114249f847c23790ac82a3d41df8cf85da2dd14e89304782050f8872c36e1a20be055c27813107f83d011a08c04581a80d2066030016c0b405602a81500a603201880b8050023011007803a01c00d8068032018009803801a009004001c00a0040018008002000 } : Fields).get c.val)
theorem record053_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record053.data.requiredEdges q = true := by decide +kernel
theorem record053_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record053) (record053.maps 2) (record053.inverseMaps 2) record053_frame002_indices (Fin.ofNat record053.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record053_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record053) (record053.maps 2) (record053.inverseMaps 2) record053_frame002_indices (Fin.ofNat record053.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record053_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record053) (record053.maps 2)
      (record053.inverseMaps 2) record053_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record053_frame002_links_0000 record053_frame002_links_0064)
theorem record053_frame002_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) : Supported record053 2 :=
  of_group record053 2 (smallEmbedding record053) (small_cells_exact record053 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record053_frame002_indices record053_frame002_graph record053_frame002_links
def record053_frame003_indices (c : Fin record053.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x33d58eb095feba5469b33463ac6c6bed55a834562ea994ea44478835039f83e2714d099b2f655ca893425c4908f118218408790eb1963104488810e1a0338640bc1642c0540a6148288320620b8140230440780e81c0360680c8180260380680901001c0280400600800800 } : Fields).get c.val)
theorem record053_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record053.data.requiredEdges q = true := by decide +kernel
theorem record053_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record053) (record053.maps 3) (record053.inverseMaps 3) record053_frame003_indices (Fin.ofNat record053.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record053_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record053) (record053.maps 3) (record053.inverseMaps 3) record053_frame003_indices (Fin.ofNat record053.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record053_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record053) (record053.maps 3)
      (record053.inverseMaps 3) record053_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record053_frame003_links_0000 record053_frame003_links_0064)
theorem record053_frame003_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) : Supported record053 3 :=
  of_group record053 3 (smallEmbedding record053) (small_cells_exact record053 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record053_frame003_indices record053_frame003_graph record053_frame003_links
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (Fin.cases (record053_frame001_supported hcells) (Fin.cases (record053_frame002_supported hcells) (Fin.cases (record053_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record053_frames_supported
theorem record054_frame000_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    Supported record054 0 :=
  of_identity record054 0 (by decide +kernel)
theorem record054_frames_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    ∀ f : Fin record054.g, Supported record054 f :=
  (Fin.cases (record054_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record054_frames_supported
theorem record055_frame000_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    Supported record055 0 :=
  of_identity record055 0 (by decide +kernel)
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record055_frames_supported
theorem record056_frame000_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    Supported record056 0 :=
  of_identity record056 0 (by decide +kernel)
def record056_frame001_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x35e1992c535bcaa65470a0f4ee246d15a8994331f14f6c7a738f9914aca50426d92a07ce3791b28cc852228213989484a224a11308444141fe0ef87603a41cb0df06d835c1990c385e42ee16f0b2056c2a814d09f04a423c11508484181f60f2075037c1b00d2048823011607f03701b00d205f02e01680ac05502a014c08e03601a00c404e024011007803a01c } : Fields).get c.val)
theorem record056_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record056_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record056) (record056.maps 1)
      (record056.inverseMaps 1) record056_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record056_frame001_links_0000 record056_frame001_links_0064)
theorem record056_frame001_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) : Supported record056 1 :=
  of_group record056 1 (smallEmbedding record056) (small_cells_exact record056 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record056_frame001_indices record056_frame001_graph record056_frame001_links
def record056_frame002_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x72f7066eb6a165361d6075f45a856a55c54650e5075024da4934384013ed3d737f34033431d2e62e02db2cb2ca2c028e26a25e24f21d2102051f61e41e01d31b619818318117916315915014c1381191040f60e70e50cf0c80c30b90b30ae08b08608507d06c06a06705d05a05805405305205104503503303002702402201e01d01c } : Fields).get c.val)
theorem record056_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record056) (record056.maps 2) (record056.inverseMaps 2) record056_frame002_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record056) (record056.maps 2) (record056.inverseMaps 2) record056_frame002_indices (Fin.ofNat record056.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record056_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record056) (record056.maps 2)
      (record056.inverseMaps 2) record056_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record056_frame002_links_0000 record056_frame002_links_0064)
theorem record056_frame002_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) : Supported record056 2 :=
  of_group record056 2 (smallEmbedding record056) (small_cells_exact record056 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record056_frame002_indices record056_frame002_graph record056_frame002_links
def record056_frame003_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0864.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0864.count (({ width := 11, code := 0x12663b46489709201bf37d0ef9c93886f0d019c332632bfd692af538a4d36a444788b4fa1ed3ce76ced1d43706b8d399e30c5f8bc1732d0584ad9492704ac9512122a43c849021ea38c6c8d31863085b0b11542884f09a0fe1e83c8700c61842f0560a61442684c096128208340640bc138240440780e81c } : Fields).get c.val)
theorem record056_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record056) (record056.maps 3) (record056.inverseMaps 3) record056_frame003_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record056) (record056.maps 3) (record056.inverseMaps 3) record056_frame003_indices (Fin.ofNat record056.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record056_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record056) (record056.maps 3)
      (record056.inverseMaps 3) record056_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record056_frame003_links_0000 record056_frame003_links_0064)
theorem record056_frame003_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) : Supported record056 3 :=
  of_group record056 3 (smallEmbedding record056) (small_cells_exact record056 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0864
    Papers.RationalityTen.SharedFrameCatalogue.group0864_facts record056_frame003_indices record056_frame003_graph record056_frame003_links
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (Fin.cases (record056_frame001_supported hcells) (Fin.cases (record056_frame002_supported hcells) (Fin.cases (record056_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
def record058_frame001_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x67a33b1928af2532a6191f2898449a074e9a6a031c989cbf054b272134894a49023811588843bb1bf0dac6a62f01630aa853428910687f43e41c70db869825411a08783a012208e04601b80d205f02d01580aa054029811c06c033018809c04802200f807803a01c00d806002401000680240100070018008002000 } : Fields).get c.val)
theorem record058_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record058_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record058) (record058.maps 1)
      (record058.inverseMaps 1) record058_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record058_frame001_links_0000 record058_frame001_links_0064)
theorem record058_frame001_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) : Supported record058 1 :=
  of_group record058 1 (smallEmbedding record058) (small_cells_exact record058 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record058_frame001_indices record058_frame001_graph record058_frame001_links
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (Fin.cases (record058_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
def record059_frame001_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0845.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0845.count (({ width := 11, code := 0x27a4b993922e33c367fcfb5f2bc4758e1998b1460cbe5762ea5ceb355baab528a2d3525648a8b9111fb3d6788e39ac342644b695e27047c861081e639c700d61962ec5a88a0ee1942c0540a6148280310580a41101e03a0700b00f01a0240400700600800800 } : Fields).get c.val)
theorem record059_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 64 74 :=
  interval_of_check _ 64 10 (by decide +kernel)
theorem record059_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record059) (record059.maps 1)
      (record059.inverseMaps 1) record059_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 74 record059_frame001_links_0000 record059_frame001_links_0064)
theorem record059_frame001_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) : Supported record059 1 :=
  of_group record059 1 (smallEmbedding record059) (small_cells_exact record059 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0845
    Papers.RationalityTen.SharedFrameCatalogue.group0845_facts record059_frame001_indices record059_frame001_graph record059_frame001_links
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (Fin.cases (record059_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
def record060_frame001_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd0d5c22d35594ab652aa33913288f43ea1110648243e99e50ca06192cb1608a4239a1b28d6c69231017f0bc053e26010e085439e1ab0d205f02ea1660a184f020a0ef07403881b60c204f024011007502f81680a805001e809c04401c00c805c02c012006802c0140070018008002000 } : Fields).get c.val)
theorem record060_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 64 69 :=
  interval_of_check _ 64 5 (by decide +kernel)
theorem record060_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record060) (record060.maps 1)
      (record060.inverseMaps 1) record060_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 69 record060_frame001_links_0000 record060_frame001_links_0064)
theorem record060_frame001_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) : Supported record060 1 :=
  of_group record060 1 (smallEmbedding record060) (small_cells_exact record060 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record060_frame001_indices record060_frame001_graph record060_frame001_links
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (Fin.cases (record060_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record061_frames_supported
theorem record062_frame000_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) :
    Supported record062 0 :=
  of_identity record062 0 (by decide +kernel)
def record062_frame001_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0xc17762d8543a153a25d4648a912221408802fe1f8b976bad4995afc5ecb49632914f89c1332594ae93d152274287f4f81cc382648be96b2ce578aa9502564888a9041f03cc638b61642bc5509b0be1682a0530a010c1f83e07a0d4160270440800e0160240340500700600800800 } : Fields).get c.val)
theorem record062_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record062_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record062) (record062.maps 1)
      (record062.inverseMaps 1) record062_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record062_frame001_links_0000 record062_frame001_links_0064)
theorem record062_frame001_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) : Supported record062 1 :=
  of_group record062 1 (smallEmbedding record062) (small_cells_exact record062 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record062_frame001_indices record062_frame001_graph record062_frame001_links
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (Fin.cases (record062_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record062_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003
