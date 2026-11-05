module
prelude
public import GraphInputsRow23Part00020Data
public import RawFrameSupport
public import SharedFrameGroups008Checked
public import SharedFrameGroups011Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups021Checked
public import SharedFrameGroups026Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x4a5245120a8ff47c23a51c68dc4021ea4e947203679aa8cd45bd2a6137c8e845522010c48464121ff8fc07c23d11a70b744e02050f307443841b40d186403021720b1053c26612c08b84401fa0f6071825c0e806503001700b205602a815009a04701e00ec07003401680a004802100f0074038018009803c018009004001c00c0040018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x47ea185080831410a000fe27e73941bd0d3667d31d1870bfc57e29493b892047423291708a244521b10b484441a1cd8cec5ec28a134096049823e11708784242040fd076c3241830b0054825e12607c825c0e806503001700b205602a815009a04701e00ec07003401680a004802100f0074038018009803c018009004001c00c0040018008002000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x5ba26b92928fd430a1010628214001fc4fce7282bf14a49dc47422e114488a42d21110687ec3cd1be0c705fa2f614609a04b424c11f08b844021210207e83b61c70d186483061760b0054828a12f09303e412e08503f81d00ca06002e01640ac05502a013408e03c01680a004802100f007403801900c005c028013008003c018009004001c00c0040018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
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
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0551.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0551.count (({ width := 11, code := 0xd55a8b1761ec0d742da59aaf15ba3c4707e8f99e839c704da9a6344634c29802e05a8ab14f2965109b13223c4688c1122183ec7b8f21da3a86d0d61923085e8b71602944b0920e01983085b0ae1402704a0921201e03605e0ac1202203c0740e0190300580a81402203c0680b0120200380400600800800 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0551
    Papers.RationalityTen.SharedFrameCatalogue.group0551_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x60ca8e92128fc44521450628113f89cbcc045f72b8146c9da4a424991cc8d045122210e48443ce1ce8db467a30d1818adc51a27812d893047c221109081038c1b40d206443001770b5858029e14609d04bc13c08c03c81a40b405802b01540a804302080c405a02a013008804001e00e8070032016009803c01a00b004802000e0050018008002000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1534a5d51225f12348d3460a14505a81e3f49f1cf687a72b314a49e04481f30e7c71a31d17c8ba856a29314009cc48e23f11107a83c81de0eb86e836619e0c886282f616e0b0054028813c097848423410b08283dc1e00e804601fc0e406b03481940c405d02d01580aa05402380e806603101680a804a02200f007403801900c005802a0100078034014009004001c00c0050018008002000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2c014989c748ea39515a862427a10905e81c4069fa4f907b63d39730a304931f48ec46f232e18d8c385f62e816c8ad4528282139891c47e22210007a83c81d70e486e435a1a50cc062830617c0ba05b829414409a84bc25012108984141ec0e904601d00e2069033018c0b805a02c01580aa05401e00e406202e015809004402000f007403801900c005802a00f0068030016009004001c00a0040018008002000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x13789b44cba5d52be9594a624b925092248d244d21a8ff478a3a51c66082fb16a8a9c516282138493048723b91988a844321190087e03e11cc8e1c6762df1538a544e422910c08203ee1e50ea06d03261810b9055829e13a092847822e11008503f41de0e304601a40cc06503181880b805a02c01580aa05401880b805a02b015009004402000f007403801900c005802a00f006802c012008003801800a0040018008002000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
def record015_frame002_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x13b49c74be24751ca8d3456a1890a2842417a07901a7e93e41ed8f4e4a624991207d23b11cf8de465c31d1870bec5d42d915a8a5050427312388fc4442000f507903ae1b90d986b434a19e0cc06282f81740b705802b214409784a024211a08984141ee0e904601a40cc06503181880b805a02c01580aa05401880b805a02b015009004402000f007403801900c005802a00f006802c012008003801800a0040018008002000 } : Fields).get c.val)
theorem record015_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record015_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 2)
      (record015.inverseMaps 2) record015_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record015_frame002_links_0000 record015_frame002_links_0064)
theorem record015_frame002_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 2 :=
  of_group record015 2 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record015_frame002_indices record015_frame002_graph record015_frame002_links
def record015_frame003_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x13ba734cc9612724c48e8e51ba354628b9162264408710d1832fe5c8b215a2b054ca29432824f49d1382644b094126234458848fb1e23bc750dc1b43606a0d119e324618bf17a2dc5b0b31602bc570ad1582a8540a610018c3005f0ba1702b0540a41402784e0620b81682b0540901102003c0740e0190300580a80f01a02c0480800e0180280400600800800 } : Fields).get c.val)
theorem record015_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record015_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record015) (record015.maps 3)
      (record015.inverseMaps 3) record015_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record015_frame003_links_0000 record015_frame003_links_0064)
theorem record015_frame003_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 3 :=
  of_group record015 3 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record015_frame003_indices record015_frame003_graph record015_frame003_links
def record015_frame004_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x149a8f5049d1352684c695529a5149a929242424788e11b18d3125f0b71642c4574a794d29651ca21422784d899130248480899051f63e47a0e61c83886f0db1b234c668c918e304600bd1742e45c0b716c2d0590b011019c320630c21802d0580ac150298520620b81682b0540901102003c0740e0190300580a80f01a02c0480800e0180280400600800800 } : Fields).get c.val)
theorem record015_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record015) (record015.maps 4) (record015.inverseMaps 4) record015_frame004_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record015) (record015.maps 4) (record015.inverseMaps 4) record015_frame004_indices (Fin.ofNat record015.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record015_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record015) (record015.maps 4)
      (record015.inverseMaps 4) record015_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record015_frame004_links_0000 record015_frame004_links_0064)
theorem record015_frame004_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 4 :=
  of_group record015 4 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record015_frame004_indices record015_frame004_graph record015_frame004_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (Fin.cases (record015_frame002_supported hcells) (Fin.cases (record015_frame003_supported hcells) (Fin.cases (record015_frame004_supported hcells) (fun j => Fin.elim0 j))))))
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
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x543a93538e9904aba4711828ac427a0bcff47e93eb1f1cf4e55328c924c8b84231f40e346f031b17d8b1856a2a214989cc48e23f115085041e1ff0fc07943bc1d60d2867c32018a0bd85b8294144097848423210c08283d81e00e904601d00da069033018c0c005d02d01580aa05401e00d406202e01580a004a02200f007403801900c00580260110080034018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x68ab4094ea90946ba34917a8af453228512668f32f98d8a7450a270931c95849e24b92248f847020c8f4872235618b8a5c50e27a135093047622d10d08383fe1f20da069032e1870b48560294137095847021e0f604b824011807903481680b005602a815008203c01a80c405a026011008404001e00e8070032016009803c01a00b004802000e0050018008002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x68567a66e63c63662a6035f45ae56c56055552e4f84ec4da4b048745944c44241640e4043df3d238b35734e3483293022f92ed2cb2af26e22920c2031ce1b119f15d0ef0de0ba0b007907307107006c06a06906005905705305204904304104003b03903702e02502301f01e } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x9d93866e4bc9692b644c758950a21241d812fc1f53e0798ea9ba3676c4ced9932c60ebcd60a9e532a553fa6a4c8971262303ec700d299b2e2574a890f1962f85309f0fe1e83b8760e21b8368640ba16c2b85609a118218420780e41b82e04a08c0f81e } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record020_frame002_links_0000 record020_frame002_links_0064)
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
def record020_frame003_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0407.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0407.count (({ width := 8, code := 0xdad9d8d7d6d5d2d1cac9c8c7c5c1c0bfbbb5b3b2b1b0afaeabaaa3a2a1a09e9a9998948e877f7c7b716e6b5f504d46453b3a3938373635312e2d2b2a272625242322211d1a191716 } : Fields).get c.val)
theorem record020_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0407.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0407.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0407.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record020_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0407.localPairCheck (smallEmbedding record020) (record020.maps 3)
      (record020.inverseMaps 3) record020_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record020_frame003_links_0000 record020_frame003_links_0064)
theorem record020_frame003_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 3 :=
  of_group record020 3 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0407
    Papers.RationalityTen.SharedFrameCatalogue.group0407_facts record020_frame003_indices record020_frame003_graph record020_frame003_links
def record020_frame004_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0326.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0326.count (({ width := 9, code := 0x6f375b8da6cb61aad468b3d9ccc65b2590c6623097ebe5eaed74b95b2d564b057ab558aa54a9d4aa34ca3d14883e1dce6662a14090461d8e872381b8d86a33190c45e2e138984a2411888421f0f074361a } : Fields).get c.val)
theorem record020_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0326.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0326.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0326.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record020_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0326.localPairCheck (smallEmbedding record020) (record020.maps 4)
      (record020.inverseMaps 4) record020_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record020_frame004_links_0000 record020_frame004_links_0064)
theorem record020_frame004_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 4 :=
  of_group record020 4 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0326
    Papers.RationalityTen.SharedFrameCatalogue.group0326_facts record020_frame004_indices record020_frame004_graph record020_frame004_links
def record020_frame005_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0246.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0246.count (({ width := 9, code := 0xad566b152a853a8f449e4da6932974ae55299348633188bc461f0d8340df6f579bc5daea74ba1cae061ac554a94c24116712b94894491f0f0763a1c8dc6c34190c45e2e150a04e261288c44200f074361a } : Fields).get c.val)
theorem record020_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0246.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record020_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record020) (record020.maps 5)
      (record020.inverseMaps 5) record020_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record020_frame005_links_0000 record020_frame005_links_0064)
theorem record020_frame005_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 5 :=
  of_group record020 5 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0246
    Papers.RationalityTen.SharedFrameCatalogue.group0246_facts record020_frame005_indices record020_frame005_graph record020_frame005_links
def record020_frame006_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0165.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0165.count (({ width := 8, code := 0xa3a2a1a09f9e9c9b98979695949291908e8c8a898887868583827f7e7d7c7b79787775736c6461605653504639362f2e292827262524232221201f1e1d1c1b1a1918171615141312 } : Fields).get c.val)
theorem record020_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0165.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0165.localPairCheck (smallEmbedding record020) (record020.maps 6) (record020.inverseMaps 6) record020_frame006_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0165.localPairCheck (smallEmbedding record020) (record020.maps 6) (record020.inverseMaps 6) record020_frame006_indices (Fin.ofNat record020.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record020_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0165.localPairCheck (smallEmbedding record020) (record020.maps 6)
      (record020.inverseMaps 6) record020_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record020_frame006_links_0000 record020_frame006_links_0064)
theorem record020_frame006_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 6 :=
  of_group record020 6 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0165
    Papers.RationalityTen.SharedFrameCatalogue.group0165_facts record020_frame006_indices record020_frame006_graph record020_frame006_links
def record020_frame007_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0117.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0117.count (({ width := 9, code := 0xbb5cae36bb55a2c35eac54ea350a651e8d44a04ee6b31984aa5327904762f128843e170682c0dfefa6eb197ebc53a71307e33180a853241148843210fc7a3b1c8dc6a34180b4582b1509c4a231087c3a1c } : Fields).get c.val)
theorem record020_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0117.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record020) (record020.maps 7) (record020.inverseMaps 7) record020_frame007_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record020) (record020.maps 7) (record020.inverseMaps 7) record020_frame007_indices (Fin.ofNat record020.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record020_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record020) (record020.maps 7)
      (record020.inverseMaps 7) record020_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record020_frame007_links_0000 record020_frame007_links_0064)
theorem record020_frame007_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 7 :=
  of_group record020 7 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0117
    Papers.RationalityTen.SharedFrameCatalogue.group0117_facts record020_frame007_indices record020_frame007_graph record020_frame007_links
def record020_frame008_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x603af6178cb2a588ac01508a484c624712128fa45ea18d09e8303fb9e94da66a434917d8bba5cc2a814508b03e81ea8f1871232f18d8bf058627111407dc3c41db0d8867031c14f08804081cc0df04281f80f607a03a01c40de06602e816c0ae056026811808604201e00e406e02e012808c03e01e } : Fields).get c.val)
theorem record020_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 8) (record020.inverseMaps 8) record020_frame008_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 8) (record020.inverseMaps 8) record020_frame008_indices (Fin.ofNat record020.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record020_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 8)
      (record020.inverseMaps 8) record020_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record020_frame008_links_0000 record020_frame008_links_0064)
theorem record020_frame008_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 8 :=
  of_group record020 8 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record020_frame008_indices record020_frame008_graph record020_frame008_links
def record020_frame009_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x7eefc9f53d279cf19d63a06eed7dacb5768acb593b1e60ebb1682ca584aa552a9d50a9e5282364608ad0b1ff3f27ccef9c53485fcb59632804b08e8f517e2cc4e0960e41b83606b0ce1943185a0a41402604b08a1041f83e0720dc1b02d04a08c0f81e } : Fields).get c.val)
theorem record020_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record020) (record020.maps 9) (record020.inverseMaps 9) record020_frame009_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record020) (record020.maps 9) (record020.inverseMaps 9) record020_frame009_indices (Fin.ofNat record020.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record020_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record020) (record020.maps 9)
      (record020.inverseMaps 9) record020_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record020_frame009_links_0000 record020_frame009_links_0064)
theorem record020_frame009_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 9 :=
  of_group record020 9 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record020_frame009_indices record020_frame009_graph record020_frame009_links
def record020_frame010_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x7367277216f36ec6e86bc69c64c61860e6025db5a459d58556b5314ec4db4d649848a48144b42a3d43ab3a73a538935834c33b3162e529724d22f2261ed1cf1bf1601020f00cf0c608007a07707607106e06c06305a05805405304b04504204103b03803602d02502301f01e } : Fields).get c.val)
theorem record020_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record020) (record020.maps 10) (record020.inverseMaps 10) record020_frame010_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record020) (record020.maps 10) (record020.inverseMaps 10) record020_frame010_indices (Fin.ofNat record020.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record020_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record020) (record020.maps 10)
      (record020.inverseMaps 10) record020_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record020_frame010_links_0000 record020_frame010_links_0064)
theorem record020_frame010_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 10 :=
  of_group record020 10 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record020_frame010_indices record020_frame010_graph record020_frame010_links
def record020_frame011_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0406.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0406.count (({ width := 8, code := 0xa3a2a1a09f9e9c9b98979695949291908e8c8a898887868583827f7e7d7c7b79787775736c6461605653504639362f2e292827262524232221201f1e1d1c1b1a1918171615141312 } : Fields).get c.val)
theorem record020_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0406.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0406.localPairCheck (smallEmbedding record020) (record020.maps 11) (record020.inverseMaps 11) record020_frame011_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0406.localPairCheck (smallEmbedding record020) (record020.maps 11) (record020.inverseMaps 11) record020_frame011_indices (Fin.ofNat record020.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record020_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0406.localPairCheck (smallEmbedding record020) (record020.maps 11)
      (record020.inverseMaps 11) record020_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record020_frame011_links_0000 record020_frame011_links_0064)
theorem record020_frame011_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 11 :=
  of_group record020 11 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0406
    Papers.RationalityTen.SharedFrameCatalogue.group0406_facts record020_frame011_indices record020_frame011_graph record020_frame011_links
def record020_frame012_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0325.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0325.count (({ width := 8, code := 0xa3a2a1a09f9e9c9b98979695949291908e8c8a898887868583827f7e7d7c7b79787775736c6461605653504639362f2e292827262524232221201f1e1d1c1b1a1918171615141312 } : Fields).get c.val)
theorem record020_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0325.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0325.localPairCheck (smallEmbedding record020) (record020.maps 12) (record020.inverseMaps 12) record020_frame012_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0325.localPairCheck (smallEmbedding record020) (record020.maps 12) (record020.inverseMaps 12) record020_frame012_indices (Fin.ofNat record020.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record020_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0325.localPairCheck (smallEmbedding record020) (record020.maps 12)
      (record020.inverseMaps 12) record020_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record020_frame012_links_0000 record020_frame012_links_0064)
theorem record020_frame012_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 12 :=
  of_group record020 12 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0325
    Papers.RationalityTen.SharedFrameCatalogue.group0325_facts record020_frame012_indices record020_frame012_graph record020_frame012_links
def record020_frame013_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0245.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0245.count (({ width := 10, code := 0x7b1e97a1df76dd9735c76e5b06b5aa68d9c669976498b6097e5f1715b96b57d57531404f93b4cd2f4b92c4a12040cee390e1330c12e4951c469170591184410c421043f0f83b0e0370cc320b82c0ac2a09c25090210781d06c1a } : Fields).get c.val)
theorem record020_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record020) (record020.maps 13) (record020.inverseMaps 13) record020_frame013_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record020) (record020.maps 13) (record020.inverseMaps 13) record020_frame013_indices (Fin.ofNat record020.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record020_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record020) (record020.maps 13)
      (record020.inverseMaps 13) record020_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record020_frame013_links_0000 record020_frame013_links_0064)
theorem record020_frame013_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 13 :=
  of_group record020 13 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0245
    Papers.RationalityTen.SharedFrameCatalogue.group0245_facts record020_frame013_indices record020_frame013_graph record020_frame013_links
def record020_frame014_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0164.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0164.count (({ width := 8, code := 0x9b9a9998979695949291908f8e8c8b8a888684838281807f7e7d7b7a797877757473716f69625f5e55524f4639362f2e292827262524232221201f1e1d1c1b1a1918171615141312 } : Fields).get c.val)
theorem record020_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0164.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0164.localPairCheck (smallEmbedding record020) (record020.maps 14) (record020.inverseMaps 14) record020_frame014_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0164.localPairCheck (smallEmbedding record020) (record020.maps 14) (record020.inverseMaps 14) record020_frame014_indices (Fin.ofNat record020.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record020_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0164.localPairCheck (smallEmbedding record020) (record020.maps 14)
      (record020.inverseMaps 14) record020_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record020_frame014_links_0000 record020_frame014_links_0064)
theorem record020_frame014_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 14 :=
  of_group record020 14 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0164
    Papers.RationalityTen.SharedFrameCatalogue.group0164_facts record020_frame014_indices record020_frame014_graph record020_frame014_links
def record020_frame015_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0116.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0116.count (({ width := 9, code := 0xc963b1b87c260af577b85aed167b156eb356a8d2e8b3f9ecd667309449239168a44e1b0883c1602fc71b3d8ec35728d3c8434988aa532310c8441200f476391b8d46632170ac54291409446210f874361a } : Fields).get c.val)
theorem record020_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0116.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0116.localPairCheck (smallEmbedding record020) (record020.maps 15) (record020.inverseMaps 15) record020_frame015_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0116.localPairCheck (smallEmbedding record020) (record020.maps 15) (record020.inverseMaps 15) record020_frame015_indices (Fin.ofNat record020.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record020_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0116.localPairCheck (smallEmbedding record020) (record020.maps 15)
      (record020.inverseMaps 15) record020_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record020_frame015_links_0000 record020_frame015_links_0064)
theorem record020_frame015_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 15 :=
  of_group record020 15 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0116
    Papers.RationalityTen.SharedFrameCatalogue.group0116_facts record020_frame015_indices record020_frame015_graph record020_frame015_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (Fin.cases (record020_frame003_supported hcells) (Fin.cases (record020_frame004_supported hcells) (Fin.cases (record020_frame005_supported hcells) (Fin.cases (record020_frame006_supported hcells) (Fin.cases (record020_frame007_supported hcells) (Fin.cases (record020_frame008_supported hcells) (Fin.cases (record020_frame009_supported hcells) (Fin.cases (record020_frame010_supported hcells) (Fin.cases (record020_frame011_supported hcells) (Fin.cases (record020_frame012_supported hcells) (Fin.cases (record020_frame013_supported hcells) (Fin.cases (record020_frame014_supported hcells) (Fin.cases (record020_frame015_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))
#print axioms record020_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020
