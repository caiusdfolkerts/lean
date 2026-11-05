module
prelude
public import GraphInputsRow24Part00014Data
public import RawFrameSupport
public import SharedFrameGroups068Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups096Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014
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
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6cbb60da22cc962daafd572a38507a5392588ad44ca23d0f67d33e29ed8f4e7272c59614a084db20d0fe06f23651ad8d1c53e29114109cc4021de0eb873c35a1980ba05b827a12808904141de0e905c028c12209004601b80d806902f81700b405602a815006c034018809c04802200f0074038012008003c01a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x73673171a7066ee66065e61d6075c05ad56a55c55454d51450e5075024dd4484444013ed39938534033432b3242eb2e62e02db25121920c1fb1d01b417d1751351170f20e10c60c10a109608b08a08606c06a06705d05a05805405305203503303002702402201e01d01c01201000f00d00b009008007004003002001000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0864.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0864.count (({ width := 11, code := 0x93b26e454768cd0b215c037e6f39e2b92710e0dbf345680ce19931b5bab7157a9c4f49c92223c4728ccfd1f43da79ccf9842f85d4ac14724a47c790e119c300578a812a2343f87e0f418c3085e0ac14c2884d09812c1a03205e09c1202203c0740e01202003c0680b0120200380400600800800 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0864
    Papers.RationalityTen.SharedFrameCatalogue.group0864_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcc55c629dd476a0b49a20c0ff67ca3d29e4ccb0543283935c8002fc1638a584e225f12988183f41f30f287783901c10dd86b434c1980c885e82d81650ac04f425011908904301de0d504d8244102078037017c0b605a02b81580aa04902000d804e023011007c03c01d00d8068024011008003801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xb4d559a8093a49b348d203cfb67ad3be9dacd665ff2e916d0a52457217902c7ce3db1e38ce062a3061740b6456029c14509b44c024711d08443e41e50e286402da1560a184c41f40c804d8244102078037017c0b605a02b81580aa04902000d804e023011007c03c01d00d8068024011008003801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record006_frame002_links_0000 record006_frame002_links_0064)
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x33d19c0c3b547a9ed3ac9534a2246d20c8f0475238cdea6e23409900c625712b193d09a04c0254919c86440f2008fc47c23c21810bd050a26112888e83f01c30d006483041720a404e826612508f04101fa0e904882300dc06902f81740b405702b01540a804901f00d806a031013809404401f00f00740380120080034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1992ab3507a7fd286934460a2650607fb3e39edcf4e57f26d932c81e4001c68d945f82c71498a0c4e625310307943bc1cf0e086983221820bd85d42dc15f0ac054828813d09784a023210c08283c012208c04081b80d205f02e81680ae05602a8150092036018809c04a02200f807803a01c00d80680240110080034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1b3cc90629b0dd672a2b4f7274939a9874bd25c12c495b4a6a509280939498a48d23890e483a3f11da8e646f9a64cb263c31a15e4ab851827092688ee46722190c87de3df1e78f146142ed15489c84562080fc07503861800b805802b01510a484ec26812608f845822410b08183f01ea0e807103701ac0d2051826c12208003c01b80800360138090046022010007c03c01d009003c01c00d0058028012008 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
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
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33158b0b8c55029dd4c4a3b513a82d28e933444a1dcf947b93d29e4ce486582b6150ca5c507279935c8263ff1aa8d0c52c285138897c4a620e10388043e61ec0ef075c3901c10dd86b434c1980c885e82e616c0b285782ae14b09b046822410b07b83bc1d00d504d82440f006e02f816c0b405602a810006c027011808803c01d00d8068024010007803801a00b00500240100060018008002000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xaafa90a3b9c19a399496f9609498c48b281180174472d7126fc6db6856135fe5f35d75cb5b45415314b44a541f4113fc3ee3e436a35734d33131f2fa2ea2c62b62ad2932862652552232132011f01e01d31c41981571441341040f60e90bf09909107806e05f05b05a05605504003602702302201e01d01b01a01201000f00e00d00b00a009008006003002001000 } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record014_frame002_links_0000 record014_frame002_links_0064)
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
def record014_frame003_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x2d3562cab3510a8093e29d24e0a6cd26091943b2178f5a7943be9dace506b330e97fcbde5d22e116d0a7852825312508163f91f38f6c78e34f19c8c9060c2f716c8b2856029c14509b44c024711d08443fe1f20f287503881a80c2855c28613008483e81d40c804d82440f006e02f816c0b405602a810006c027011808803c01d00d8068024010007803801a00b00500240100060018008002000 } : Fields).get c.val)
theorem record014_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record014_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record014) (record014.maps 3)
      (record014.inverseMaps 3) record014_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record014_frame003_links_0000 record014_frame003_links_0064)
theorem record014_frame003_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 3 :=
  of_group record014 3 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record014_frame003_indices record014_frame003_graph record014_frame003_links
def record014_frame004_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x6766566125c45b25a859258657b52c5214bd4b445d45344643b41a3d638837336735434a33f2f02e52812782212172071fe1f71c01ba1b41a619e18e18617c17817216515d14f14713813312e12712111c1141000eb0e50df0ce0c90c30b309908f07706d05e05a05905505404003602702302201e01d01b01a01201000f00e00d00b00a009008006003002001000 } : Fields).get c.val)
theorem record014_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record014_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record014) (record014.maps 4)
      (record014.inverseMaps 4) record014_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record014_frame004_links_0000 record014_frame004_links_0064)
theorem record014_frame004_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 4 :=
  of_group record014 4 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record014_frame004_indices record014_frame004_graph record014_frame004_links
def record014_frame005_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x31e1832b775672b01572aab5522a6d35699947c239908a83e41b20bcf967213379984cb464c32298f4af456d27693808c245c22b114488036c1af0d3c66031f17f0bb85962bd1570a3c4fc25d12688a844621c10a88103e01cc0c7052027613008583f81e60d204d82440f006e02f816c0b405602a810006c027011808803c01d00d8068024010007803801a00b00500240100060018008002000 } : Fields).get c.val)
theorem record014_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record014_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record014) (record014.maps 5)
      (record014.inverseMaps 5) record014_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record014_frame005_links_0000 record014_frame005_links_0064)
theorem record014_frame005_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 5 :=
  of_group record014 5 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record014_frame005_indices record014_frame005_graph record014_frame005_links
def record014_frame006_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x19e72d611b756bed559cb2b63692d1d98b2f62dc558a112a15be0716e01bdb6d6ccd797b2ee520a211622644286d099db3a8738e01b8352688c898a3085d8b715f2b0518a113e2744cc969252243e8788ea1a6328618ae1282343a86c0ba1642c0540a60fc1b0270460880f01d0360680901001e0380680b0140240400600600800800 } : Fields).get c.val)
theorem record014_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record014_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record014) (record014.maps 6)
      (record014.inverseMaps 6) record014_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record014_frame006_links_0000 record014_frame006_links_0064)
theorem record014_frame006_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 6 :=
  of_group record014 6 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record014_frame006_indices record014_frame006_graph record014_frame006_links
def record014_frame007_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x6606355f25a559a59558b58657f5315274da4d048047947046b43e3f239f39439038638237b32c3242e82e02a129c29629328c22321820c1fc1f31e31dc1cb1c01b41a519e18f18617216b16516115714c13d11e0fa0f00e60d40ca0c00b009108b07406c05d05905805405303f03602702302201e01d01b01a01201000f00e00d00b00a009008006003002001000 } : Fields).get c.val)
theorem record014_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record014) (record014.maps 7) (record014.inverseMaps 7) record014_frame007_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record014) (record014.maps 7) (record014.inverseMaps 7) record014_frame007_indices (Fin.ofNat record014.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record014_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record014) (record014.maps 7)
      (record014.inverseMaps 7) record014_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record014_frame007_links_0000 record014_frame007_links_0064)
theorem record014_frame007_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 7 :=
  of_group record014 7 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record014_frame007_indices record014_frame007_graph record014_frame007_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (Fin.cases (record014_frame003_supported hcells) (Fin.cases (record014_frame004_supported hcells) (Fin.cases (record014_frame005_supported hcells) (Fin.cases (record014_frame006_supported hcells) (Fin.cases (record014_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1c96c8d6282f994509eb4e6a6192fe9774b4a5892a894d4a124e523890747e23cd1ce8e046c9a70cb86393169554a6251e27d139c9924ab23390c880c3ea1ed0f2877c2e61610abc51627812d08f03f01c30cb85ec2d615b0aa853829214209d84d025a12608f845821a10708003e41e00ea07103701ac0d3057826c12208e04682300f006e03581a80d203601800bc04e01f00f007403601a0090028012008 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x73873370661d60756a55c55454d50e5075024dc44c43f4013ed3943893403343283213173072ed2e62e02db2cf25121920c1fb1ef1eb1d01b417d1751601521351170f20e10cb0c60c108b08606c06a06705d05a05805405305203d03503303002e02702402202101e01d01c01201000f00d00b009008007004003002001000 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33258b0ac6559283d3fe91e460a2b513288a43c1f1cf6c7a73921648afc4db2658fa871a3791b28d5868829314109cc4a620e10388043bc1d70e7871c3801b40cf860c2f61740b7057c2b01520a204f425e12808283d81e00e904882300dc06902f81740b805a02b01540a8036018809c04a024011007803a01c00d80680240100078034018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xab3a909d59c694d9428a884b83782381280274172a7146db62961b5b85af5274e14d34c34b54a641c40e3fe3e436a35734d2fa2ea2d72c52b52a12752342242142031e11d41cd1b51a81871781251030f70ea09108c06e06905f05d05c05a05605505403603102702502402201e01d01c01b01a01201000f00d00c009008007005004003002001000 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record017_frame002_links_0000 record017_frame002_links_0064)
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1ae4d2e688b3f19d4b134d3a3c51cc8da466231516e8ae454a28d1368924459dc0d0264c30d94b09ee4c926112e895a4a624c124491047b23b91bc8d22be15209ac47820b100076c3821880ac84a023a0f907883a41c40db06a02bc13607803b01b80d4069033817c0b605a02000d8068032018809c04a023011004801c00d0050024010007002000c004001 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x18b2bf05d22dc1696a4e499a2010b08354092004fbc7d13e19ed4f2a77b3b49ad8bf85cf2d613d09924ae24d92108ce45a21f90c884a4041fd0f947b22b814b898047421010087703801900b6850426210d07e83a41bc0d406302ac13607803b01b80d4069033817c0b605a02000d8068032018809c04a023011004801c00d0050024010007002000c004001 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x5e158455b5365125084e04b849e49548f48447d3bd36334832d3082ed2cf2b82b42a42442262091e31c41a518b18716e16316015814913d1301221161020fd0f00ec0e00d40cf0c60bb0b20a60a109408b08508108006f06806406303e03603203103002f02702502302201f01e01d01c01b01a01201000e00d00a009008007 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
def record019_frame002_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x48c8b70f614c13814fb9ec3c9784eedd9baf60caf9552964e49611ea2343c82cdf9a4314598aa13e24c4888710720a4007d0f51de3a4710d91aa334660c31782e0598aa14c27c4d08d1041f43d0790de1a4330650800d8190310600bc138250460880f81e03a0700d81a0240400700d01402404007 } : Fields).get c.val)
theorem record019_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record019_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record019) (record019.maps 2)
      (record019.inverseMaps 2) record019_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record019_frame002_links_0000 record019_frame002_links_0064)
theorem record019_frame002_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 2 :=
  of_group record019 2 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record019_frame002_indices record019_frame002_graph record019_frame002_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (Fin.cases (record019_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1804b5351022e911a877429a10d05a8134019fb4fcc70a2f112ec92c485235117c89a43b21810788324091708b3457228d13c896c49a221109872036e1a40c9060c2ee16c0a9051827610807b839c1b80d2057826c0f006e03501a40d006702f816c0b404001b00c8062030017809c04602200d806802400e006802c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1026.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1026.count (({ width := 11, code := 0x1f93cb6eec6d873055ecbb5722d95a0b1d6128944c6f8d99ab338650c59822f45c4b716c23e4648b90e2123f87c8ec1ce348670cb18c3045f0b91642bc55097122238450860f81dc3285e0b61682c8580a413c2704006c0c81883005e09c118220360680900e01a02c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record020_frame002_links_0000 record020_frame002_links_0064)
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1026
    Papers.RationalityTen.SharedFrameCatalogue.group1026_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
def record020_frame003_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xaaba3b9417f87d77c379978476974572e70f6f96855ae49c48547a45c44d4384204123f93eb3e42c62b62ad2932862652552252151cd1c41b51a81981871781571451350f50e80da0cb0bd0a809907806e06a06906806705f05b05a04003603203103002f02702302201b01a01200e00d00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record020_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record020_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record020) (record020.maps 3)
      (record020.inverseMaps 3) record020_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record020_frame003_links_0000 record020_frame003_links_0064)
theorem record020_frame003_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 3 :=
  of_group record020 3 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record020_frame003_indices record020_frame003_graph record020_frame003_links
def record020_frame004_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1982b8c4fda19d08a8334081ff8fc87cb3dd1e88f206582638ccc6222ff16e0b2856029714309b84b82530e407043761ad0d3066032217c0ba854829614409e84d825e12808d044c2180ee07383801b20d3057826c0f006e03501a40d006702f816c0b404001b00c8062030017809c04602200d806802400e006802c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record020_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record020_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 4)
      (record020.inverseMaps 4) record020_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record020_frame004_links_0000 record020_frame004_links_0064)
theorem record020_frame004_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 4 :=
  of_group record020 4 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record020_frame004_indices record020_frame004_graph record020_frame004_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (Fin.cases (record020_frame003_supported hcells) (Fin.cases (record020_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6df6dc6b361360f5e55555305194da4b24a549348d3ec3e83e03d33c33be36235d34832d31b3113072ed2cf2c62bb2b82b42a524323f2262091f41eb1e21c41a519918e18b18715f14613a11f1131070eb0c508108006406305905705605305205105004503d03503203102502302201f01e01d01c01000e00d00a009008007005004003002001000 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
def record021_frame002_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x33d19c0c3c547a9ed3ae9684a9a51523690647fa3c11d46f53711b00d0264131895c4ac652b27a13449804a923390c884640f2008fc478430217a0af050a26212888e83f01c30da06803241820a404e826612508f045c2080e904682300d406902e816c0b405702b01540a804901f00d4064031012808c04401f00f00740380100070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record021_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record021_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record021) (record021.maps 2)
      (record021.inverseMaps 2) record021_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record021_frame002_links_0000 record021_frame002_links_0064)
theorem record021_frame002_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 2 :=
  of_group record021 2 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record021_frame002_indices record021_frame002_graph record021_frame002_links
def record021_frame003_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x15eab954498f30a48c3a84d05df5bd579af01dcb3b66acb58f30d60eaf55caaa52ca1d3ea714b08f519226446879061be372690c51772da594aa13e26c4ac931222063e47a0e81c2368650b10f41e4330650b61642c0550a814c2904907c0d41903104a08c1101f03c0740e01001c0340500901001c0280400600800800 } : Fields).get c.val)
theorem record021_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record021_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record021) (record021.maps 3)
      (record021.inverseMaps 3) record021_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record021_frame003_links_0000 record021_frame003_links_0064)
theorem record021_frame003_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 3 :=
  of_group record021 3 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record021_frame003_indices record021_frame003_graph record021_frame003_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (Fin.cases (record021_frame002_supported hcells) (Fin.cases (record021_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcca5c62b1d566a104ffa52126889a432210906080d3fd9fa4f907b732c164cafe4dc26590508003661980c385f82d91638ad4528283129883440c1fa0f287403901c10dd86b434c1980c8862830417c0ba857c2b01520a204f425e128090846422610c04682300d406902d81680b005702b01540a8032018808c04402000f807803a01c00d806802200e006802c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
def record022_frame002_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xab4a3b9d69c794e9428c58b38247f77d47c079678176e74272b68562a61c5b95af5425324c449b48247745944a43d41d40f3e436935634130c2d82c62b62ad2932862652552462332252151e11d41cd1b51a818717816b15614513508d08c06a06905b05a05805705605505403203102302202001f01e01d01c01b01a01100e00d00b00a009008007005004003002001000 } : Fields).get c.val)
theorem record022_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record022_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record022) (record022.maps 2)
      (record022.inverseMaps 2) record022_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record022_frame002_links_0000 record022_frame002_links_0064)
theorem record022_frame002_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 2 :=
  of_group record022 2 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record022_frame002_indices record022_frame002_graph record022_frame002_links
def record022_frame003_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xb4e559a9314729b44d324c5234885423208101e7ec3ed9f48f567923599918c625b52d494f4a524b224091908ae43c21790988123f71e38d386703151740afc56029c14509b44c024711d08c4446213100875438a1b50ce06402f216d0b2055828813104682300d406902d81680b005702b01540a8032018808c04402000f807803a01c00d806802200e006802c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record022_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record022_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record022) (record022.maps 3)
      (record022.inverseMaps 3) record022_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record022_frame003_links_0000 record022_frame003_links_0064)
theorem record022_frame003_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 3 :=
  of_group record022 3 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record022_frame003_indices record022_frame003_graph record022_frame003_links
def record022_frame004_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x6776125d15cd57c57752d5224c34aa49949247f47546e45b4513d639539134033b2f12e628726e25924f24023923221f2151f71bf1b91ae19617f17c17817216515d14f14714013d13a13512211d11a10d1070f90f30ed0ea0e60e008b08a06906805a05905705605505405303203102302202001f01e01d01c01b01a01100e00d00b00a009008007005004003002001000 } : Fields).get c.val)
theorem record022_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record022) (record022.maps 4) (record022.inverseMaps 4) record022_frame004_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record022) (record022.maps 4) (record022.inverseMaps 4) record022_frame004_indices (Fin.ofNat record022.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record022_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record022) (record022.maps 4)
      (record022.inverseMaps 4) record022_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record022_frame004_links_0000 record022_frame004_links_0064)
theorem record022_frame004_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 4 :=
  of_group record022 4 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record022_frame004_indices record022_frame004_graph record022_frame004_links
def record022_frame005_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0825.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0825.count (({ width := 11, code := 0x35a680ca9932ff5f6b696aaaa536a4d462824fa9d13626547e8a5131fe3f4764ea1a9334640c397d2f45ccb51652aa4dc9912e2404448710a20e4087e8f51e23ac748e61c2344660c81883005d0b71642c0568a80ea1d02f05d09e1382604b0941242403206208c1102003e0780e81c0360680880e01a02c0500901001c0280400600800800 } : Fields).get c.val)
theorem record022_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0825.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record022) (record022.maps 5) (record022.inverseMaps 5) record022_frame005_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record022) (record022.maps 5) (record022.inverseMaps 5) record022_frame005_indices (Fin.ofNat record022.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record022_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record022) (record022.maps 5)
      (record022.inverseMaps 5) record022_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record022_frame005_links_0000 record022_frame005_links_0064)
theorem record022_frame005_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 5 :=
  of_group record022 5 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0825
    Papers.RationalityTen.SharedFrameCatalogue.group0825_facts record022_frame005_indices record022_frame005_graph record022_frame005_links
def record022_frame006_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xced5e0ac455fea6652aa6953268fa47023491968bd45b22bd14289a3b69b18d6c62830c15c4ac24d325c92b094a49724812248f847622c8df46d03411820b1c5702a814c89e84d624c11e08b443820e100075438a1b60cb86202d21590a504e425611d04682300d406902d81680b005702b01540a8032018808c04402000f807803a01c00d806802200e006802c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record022_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record022) (record022.maps 6) (record022.inverseMaps 6) record022_frame006_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record022) (record022.maps 6) (record022.inverseMaps 6) record022_frame006_indices (Fin.ofNat record022.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record022_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record022) (record022.maps 6)
      (record022.inverseMaps 6) record022_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record022_frame006_links_0000 record022_frame006_links_0064)
theorem record022_frame006_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 6 :=
  of_group record022 6 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record022_frame006_indices record022_frame006_graph record022_frame006_links
def record022_frame007_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x80878a7197106af69e6216185a558657656e55e55554c53c5344a442741e3ab39c32b3222c12a329328b27b27226925925123a1f81f11e61d11bd1b61af1a819919018117917116816215b14413d13612711e10f1070ff0f60f00e908d08c06a06905b05a05805705605505403203102302202001f01e01d01c01b01a01100e00d00b00a009008007005004003002001000 } : Fields).get c.val)
theorem record022_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record022) (record022.maps 7) (record022.inverseMaps 7) record022_frame007_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record022) (record022.maps 7) (record022.inverseMaps 7) record022_frame007_indices (Fin.ofNat record022.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record022_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record022) (record022.maps 7)
      (record022.inverseMaps 7) record022_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record022_frame007_links_0000 record022_frame007_links_0064)
theorem record022_frame007_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 7 :=
  of_group record022 7 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record022_frame007_indices record022_frame007_graph record022_frame007_links
def record022_frame008_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x7076a966665a6085fe5bc5b355d54553b53652952351d50f50849c44f4403ee3e339538c33531c31130c3002fa2f42e72e12ce2632572492261fc1f11e81e21d01c71b41a919f19018817e15d15414e13b13511f11710b0fc0f30ec08708606806705905805605505405305203103002302202001f01e01d01c01b01a01100e00d00b00a009008007005004003002001000 } : Fields).get c.val)
theorem record022_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record022) (record022.maps 8) (record022.inverseMaps 8) record022_frame008_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record022) (record022.maps 8) (record022.inverseMaps 8) record022_frame008_indices (Fin.ofNat record022.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record022_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record022) (record022.maps 8)
      (record022.inverseMaps 8) record022_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record022_frame008_links_0000 record022_frame008_links_0064)
theorem record022_frame008_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 8 :=
  of_group record022 8 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record022_frame008_indices record022_frame008_graph record022_frame008_links
def record022_frame009_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x6425f05b15aa55554e50f5084b34a049348c47f4784724674603e93a339934333a2f42ea29428127426d26125a25524a24422f1e61da1c81ad19518e18617c17216e16315d15815314a14012c12411a10d1070fe0fa0f60f10e80de08908806806705905805605505405305203103002302202001f01e01d01c01b01a01100e00d00b00a009008007005004003002001000 } : Fields).get c.val)
theorem record022_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record022) (record022.maps 9) (record022.inverseMaps 9) record022_frame009_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record022) (record022.maps 9) (record022.inverseMaps 9) record022_frame009_indices (Fin.ofNat record022.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record022_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record022) (record022.maps 9)
      (record022.inverseMaps 9) record022_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record022_frame009_links_0000 record022_frame009_links_0064)
theorem record022_frame009_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 9 :=
  of_group record022 9 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record022_frame009_indices record022_frame009_graph record022_frame009_links
def record022_frame010_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1045.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1045.count (({ width := 11, code := 0x3a670eda5b2b34658c3984ad3586add582a653ca65462874b48f11ba013f276ceb9a632e628c117a2e65b4b015b2964e49b1332504708c91722642c830fe1f23d0778ec1d035c6a8d11923105e0b71642b4550a60d61a82b0550941242384608a1102182f05c08c1102003e0780e81c0360680880e01a02c0500901001c0280400600800800 } : Fields).get c.val)
theorem record022_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1045.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record022) (record022.maps 10) (record022.inverseMaps 10) record022_frame010_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record022) (record022.maps 10) (record022.inverseMaps 10) record022_frame010_indices (Fin.ofNat record022.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record022_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record022) (record022.maps 10)
      (record022.inverseMaps 10) record022_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record022_frame010_links_0000 record022_frame010_links_0064)
theorem record022_frame010_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 10 :=
  of_group record022 10 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1045
    Papers.RationalityTen.SharedFrameCatalogue.group1045_facts record022_frame010_indices record022_frame010_graph record022_frame010_links
def record022_frame011_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0820.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0820.count (({ width := 11, code := 0x47589d0a610bf67e0f31e339870cdf1bb36d6d0d89ac352616b896baa15369c93523143e85507a044027ecf91ed3ba6a0cf1952fc59caf9562a452ca393d2704c89612623a40c7e0f71d83986f0dc1ae344650c20f61e8310610ae1582a0530a41442803106008c1102003e0780e81c0360680880e01a02c0500901001c0280400600800800 } : Fields).get c.val)
theorem record022_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record022) (record022.maps 11) (record022.inverseMaps 11) record022_frame011_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record022) (record022.maps 11) (record022.inverseMaps 11) record022_frame011_indices (Fin.ofNat record022.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record022_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record022) (record022.maps 11)
      (record022.inverseMaps 11) record022_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record022_frame011_links_0000 record022_frame011_links_0064)
theorem record022_frame011_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 11 :=
  of_group record022 11 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0820
    Papers.RationalityTen.SharedFrameCatalogue.group0820_facts record022_frame011_indices record022_frame011_graph record022_frame011_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (Fin.cases (record022_frame002_supported hcells) (Fin.cases (record022_frame003_supported hcells) (Fin.cases (record022_frame004_supported hcells) (Fin.cases (record022_frame005_supported hcells) (Fin.cases (record022_frame006_supported hcells) (Fin.cases (record022_frame007_supported hcells) (Fin.cases (record022_frame008_supported hcells) (Fin.cases (record022_frame009_supported hcells) (Fin.cases (record022_frame010_supported hcells) (Fin.cases (record022_frame011_supported hcells) (fun j => Fin.elim0 j)))))))))))))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1994ac650827fd1f48c144d22290e68303fd9fa4f8e7b72c913709963c61c68d986ac33f17e0b1c56a293141894c41c1f30ef074038e1b40d3067c32218a0c185ec2ea15f0ac054828813d09784a024210c07b03c011a08c03b01a80d205d02d81680ae05602a815007c032018809404602200f807803a01c00d806802000e0068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
def record023_frame002_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x169ca4b4da26991b68a4442a1dd0b480f3ed9f48f5479232296d4b524f426492c894e49022b90bc84c4081fb8f1c69e30616c8afc55e278130094847423111208484021d50e286d43381900bc85b42c813108403ec11a08c03b01a80d205d02d81680ae05602a815007c032018809404602200f807803a01c00d806802000e0068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record023_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record023_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record023) (record023.maps 2)
      (record023.inverseMaps 2) record023_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record023_frame002_links_0000 record023_frame002_links_0064)
theorem record023_frame002_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 2 :=
  of_group record023 2 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record023_frame002_indices record023_frame002_graph record023_frame002_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (Fin.cases (record023_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1b3cc3c59ca75d39094549ea4d926092248da43520c8ff478a3a8f7c641316934497a4ab24d11dc8ce443219108c8043f11df098849c23c11588203f01d40e186d03261820a40504274133096049423c11708804282080ef04682300d4069034019c0b605a02c015c0ac05502a00c8062030017808c04402000f807803a01c00d806801c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
def record024_frame002_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1cf0cca5c628413f689a443a1d50c88424182034ff67e93e41edccb04dc2638d986a63411980c385f82d91638ad452828312987403901c10dd86b434c1980c886282f81750a9052c28813d09b04bc25012108d044c2180f704682300d4069034019c0b605a02c015c0ac05502a00c8062030017808c04402000f807803a01c00d806801c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record024_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record024_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 2)
      (record024.inverseMaps 2) record024_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record024_frame002_links_0000 record024_frame002_links_0064)
theorem record024_frame002_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 2 :=
  of_group record024 2 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record024_frame002_indices record024_frame002_graph record024_frame002_links
def record024_frame003_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x1b730e5c6a0d3da444808f51da354648b114a26440874f798f30e540a614928e5049f13826a4c89612923c39c718e01bc3606a8cf198324618c016a2d0598b21622c0578ae15a2b0558a8102200320630c41842a8540a41442804f09c0c81883005e08c1102003e0780e81c0360680700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record024_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record024) (record024.maps 3) (record024.inverseMaps 3) record024_frame003_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record024) (record024.maps 3) (record024.inverseMaps 3) record024_frame003_indices (Fin.ofNat record024.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record024_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record024) (record024.maps 3)
      (record024.inverseMaps 3) record024_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record024_frame003_links_0000 record024_frame003_links_0064)
theorem record024_frame003_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 3 :=
  of_group record024 3 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record024_frame003_indices record024_frame003_graph record024_frame003_links
def record024_frame004_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x1d2b3c610a7d4ba604b89652ba5149c92122a424788e501199322568ab1532a252ca414227e4f09b1332503c4768ea1d03886f8d91ac34c668ca17e2f85e8bc1762e85c8b816e2d85a8b2112220340670cc1942c8580ac1542a0530a40c81883005e08c1102003e0780e81c0360680700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record024_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record024) (record024.maps 4) (record024.inverseMaps 4) record024_frame004_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record024) (record024.maps 4) (record024.inverseMaps 4) record024_frame004_indices (Fin.ofNat record024.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record024_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record024) (record024.maps 4)
      (record024.inverseMaps 4) record024_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record024_frame004_links_0000 record024_frame004_links_0064)
theorem record024_frame004_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 4 :=
  of_group record024 4 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record024_frame004_indices record024_frame004_graph record024_frame004_links
def record024_frame005_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb8aab4a3b94e94182480f7ff7f77d47c079678176e74272b6855b95ae4c44b24a349b48247745944a43d41d40f3e42d82c62b62ad2932862652552462252151cd1c41b51a819818717816b15714513510408d08c06a06906806705b05a05805705605505403203103002f02302202001f01e01d01c01b01a00e00d00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record024_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record024) (record024.maps 5) (record024.inverseMaps 5) record024_frame005_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record024) (record024.maps 5) (record024.inverseMaps 5) record024_frame005_indices (Fin.ofNat record024.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record024_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record024) (record024.maps 5)
      (record024.inverseMaps 5) record024_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record024_frame005_links_0000 record024_frame005_links_0064)
theorem record024_frame005_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 5 :=
  of_group record024 5 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record024_frame005_indices record024_frame005_graph record024_frame005_links
def record024_frame006_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x189eb4e559a6d134488543a217108c8204079fb0fb67d23d59e48d665b52d292c894849224091908ae43c21790988123f71e38afc56029c14509b44c024711d08c44262010da86a03381900c285e42da1640ab851026210904682300d4069034019c0b605a02c015c0ac05502a00c8062030017808c04402000f807803a01c00d806801c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record024_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record024) (record024.maps 6) (record024.inverseMaps 6) record024_frame006_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record024) (record024.maps 6) (record024.inverseMaps 6) record024_frame006_indices (Fin.ofNat record024.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record024_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record024) (record024.maps 6)
      (record024.inverseMaps 6) record024_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record024_frame006_links_0000 record024_frame006_links_0064)
theorem record024_frame006_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 6 :=
  of_group record024 6 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record024_frame006_indices record024_frame006_graph record024_frame006_links
def record024_frame007_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x5e357652e4c14b744243c43643042241c40e4084023f63ef39c32c32329828f28827e27126c25e25725223f23621e19318a18317916816115615114d13a1311101091040fe0f80f30ed0e80e30de0d80c808308206706606506405805705505405305205103203103002f02302202001f01e01d01c01b01a00e00d00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record024_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record024) (record024.maps 7) (record024.inverseMaps 7) record024_frame007_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record024) (record024.maps 7) (record024.inverseMaps 7) record024_frame007_indices (Fin.ofNat record024.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record024_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record024) (record024.maps 7)
      (record024.inverseMaps 7) record024_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record024_frame007_links_0000 record024_frame007_links_0064)
theorem record024_frame007_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 7 :=
  of_group record024 7 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record024_frame007_indices record024_frame007_graph record024_frame007_links
def record024_frame008_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1049.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1049.count (({ width := 9, code := 0x31d70b5532932d95ca64f2290476371a8b44e14ec74b3596c963b0980bd5dae96cb356a451e8d45a1908813f9f8f477381bcdc6d361acd4693419ccc652c960a04f2713482401f0f4783b1d0c862301788c44200f8783a1c0d8681c0d058281208038180a04018080200 } : Fields).get c.val)
theorem record024_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1049.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record024) (record024.maps 8) (record024.inverseMaps 8) record024_frame008_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record024) (record024.maps 8) (record024.inverseMaps 8) record024_frame008_indices (Fin.ofNat record024.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record024_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record024) (record024.maps 8)
      (record024.inverseMaps 8) record024_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record024_frame008_links_0000 record024_frame008_links_0064)
theorem record024_frame008_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 8 :=
  of_group record024 8 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1049
    Papers.RationalityTen.SharedFrameCatalogue.group1049_facts record024_frame008_indices record024_frame008_graph record024_frame008_links
def record024_frame009_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1047.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1047.count (({ width := 9, code := 0x2833296c7a370481401fcf97bbd1e4f176ba9c4d3682e56eb559ab958a953a99449f4ca09007e3e1dcea72381bcd66830980be5e2e970b65a2c960ae56269308e462291074391b8d86a34198b85a2c15884401e0e870361a0c8601c0d058281208038180a04018080200 } : Fields).get c.val)
theorem record024_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1047.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1047.localPairCheck (smallEmbedding record024) (record024.maps 9) (record024.inverseMaps 9) record024_frame009_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1047.localPairCheck (smallEmbedding record024) (record024.maps 9) (record024.inverseMaps 9) record024_frame009_indices (Fin.ofNat record024.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record024_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1047.localPairCheck (smallEmbedding record024) (record024.maps 9)
      (record024.inverseMaps 9) record024_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record024_frame009_links_0000 record024_frame009_links_0064)
theorem record024_frame009_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 9 :=
  of_group record024 9 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1047
    Papers.RationalityTen.SharedFrameCatalogue.group1047_facts record024_frame009_indices record024_frame009_graph record024_frame009_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (Fin.cases (record024_frame002_supported hcells) (Fin.cases (record024_frame003_supported hcells) (Fin.cases (record024_frame004_supported hcells) (Fin.cases (record024_frame005_supported hcells) (Fin.cases (record024_frame006_supported hcells) (Fin.cases (record024_frame007_supported hcells) (Fin.cases (record024_frame008_supported hcells) (Fin.cases (record024_frame009_supported hcells) (fun j => Fin.elim0 j)))))))))))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (fun j => Fin.elim0 j))
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
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3f49c90d7467c32e56b8b1951227993a09ba4b823a511886b423a0c900e7b43c298a0bca4f0259127090c43c1da8d6066e31317f0b4c5002470f5075c34819109e04d824211a08584141ee0e807102b412608c03581a40ca05a02a8150066031016808803a01c00c005801e00d005002000e0060018008002000 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record033_frame001_links_0000 record033_frame001_links_0064)
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
def record035_frame001_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1968bde58b28913d29b74b6a3a50647b43c01aa8bc44f025a920c8723b517f0a004a824711c08a44362000f507743ae1ba0d2065c32215e0a184f026c12e090846821610507b83a01c408c04502200d606903281680aa0540290140066031016808803a01c00d806403001700b005001e00d005002000e0060018008002000 } : Fields).get c.val)
theorem record035_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record035_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record035) (record035.maps 1)
      (record035.inverseMaps 1) record035_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record035_frame001_links_0000 record035_frame001_links_0064)
theorem record035_frame001_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 1 :=
  of_group record035 1 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record035_frame001_indices record035_frame001_graph record035_frame001_links
def record035_frame002_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x18d2bc25902a8d4e0a324ec255514483c4101db0d8464430d979cb3e53725511688824171f60ef872634e18e8bf45dc2ad13e097049a2040db068431c17b0ab852026012508583cc1d008c04502200d606903281680aa0540290140066031016808803a01c00d806403001700b005001e00d005002000e0060018008002000 } : Fields).get c.val)
theorem record035_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record035) (record035.maps 2) (record035.inverseMaps 2) record035_frame002_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record035) (record035.maps 2) (record035.inverseMaps 2) record035_frame002_indices (Fin.ofNat record035.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record035_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record035) (record035.maps 2)
      (record035.inverseMaps 2) record035_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record035_frame002_links_0000 record035_frame002_links_0064)
theorem record035_frame002_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 2 :=
  of_group record035 2 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record035_frame002_indices record035_frame002_graph record035_frame002_links
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (Fin.cases (record035_frame001_supported hcells) (Fin.cases (record035_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record046_frame001_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x395db2ecc46412fcd69aadf54d29813c297349723d116c8ad44d22450b88133cc1cf0bce4a524811d889c4081e20ea47083481968bf858829813d88f04542000f786d43301590a384742180e106282bc13609104682300f606902d015c0aa05402000d8064031013808c04401f00f007403801900680280100070020008002000 } : Fields).get c.val)
theorem record046_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 64 79 :=
  interval_of_check _ 64 15 (by decide +kernel)
theorem record046_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record046) (record046.maps 1)
      (record046.inverseMaps 1) record046_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 79 record046_frame001_links_0000 record046_frame001_links_0064)
theorem record046_frame001_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 1 :=
  of_group record046 1 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record046_frame001_indices record046_frame001_graph record046_frame001_links
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (Fin.cases (record046_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
def record047_frame001_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x73ab6d59e4c7160c2d75670af256d2b19516a7d4f8a73130c96e4ad247d2228b4457a26112688c412205cf6e69331b94f89c44a524491c08d443d2038f687583781ae0cfc6622f416e0a2447222d10e07f43e41e40d3055829413908d043c2020e8049023811408102b01540a803701980a004801f00f007403801800880240100070018008002000 } : Fields).get c.val)
theorem record047_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record047_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record047) (record047.maps 1)
      (record047.inverseMaps 1) record047_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record047_frame001_links_0000 record047_frame001_links_0064)
theorem record047_frame001_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 1 :=
  of_group record047 1 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record047_frame001_indices record047_frame001_graph record047_frame001_links
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (Fin.cases (record047_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (fun j => Fin.elim0 j))
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
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1fb4ed6700b735aeed4267db3997cca224f326e93329704a524991fe8c6457a144ff07e93da1e9cf2a6b227712c890c46521e10587e43cb1c90dec63a2c415a8a004e62610ea86cc34c18a0b7059c26c127090846821610507f03dc1d00ad03781ac0ca05602a815006e033016807803a01c00c004c01e00a004802000e0060018008002000 } : Fields).get c.val)
theorem record051_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record051_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 1)
      (record051.inverseMaps 1) record051_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record051_frame001_links_0000 record051_frame001_links_0064)
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
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014
