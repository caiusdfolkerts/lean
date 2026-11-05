module
prelude
public import GraphInputsRow23Part00023Data
public import RawFrameSupport
public import SharedFrameGroups057Checked
public import SharedFrameGroups059Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups111Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x60cad3d4b48d4460207d0187d73c99b94c365261d00e305d62d8151897c45221b10408003f41f20f287743ae1d00e106e83681ac0cf865c32218a0c085cc2d81650b00540284136089842c2080f007403841aa08803e01c80c205e02d01640aa05002200e8052026011008403a01900b8058028011007803801a00c00500240100060028008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x5f7ad3556e94049622350f284b4179e68de0658293145c93248a232914477c3931af8d3867e32f1870bf45dc2dd15f0ab453c28e136897049a23c118888c438215103077836a18e09e04c02480ff079839c1a408803e01c80c205e02d01640aa05002200e8052026011008403a01900b8058028011007803801a00c00500240100060028008002000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0xc8b7eed44ec9c52263fc61895055e5b79574ac12ba4d46486cf81e63aa734e31bf3606a0d119b31660cbe1752cc578ac1512945089f13a26a4a48e1121e43a8710cb1862ec570840f21c02f85c0b015c2984e0860e8148260440840e81902e0580a01101e0380680c0140240400600a00800800 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x5af2bc94bc919480217d0908073d79d98dfe65f2ac15109884b024111007be3c31cd8e2c6f636b1a90cf065231717a0b885a62c11540a4c50226f12c88d044420e0fe87783821ab0a88504262101079839819208803e01c80c205e02d01640aa05002200e8052026011008403a01900b8058028011007803801a00c00500240100060028008002000 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record000_frame004_links_0000 record000_frame004_links_0064)
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x6ad2e29668a9d544287939093148e23451788a74459cd0d6867032f98e4bbe55f28d94289c84a424091d48d230414509d44d025b12388b43fa1f20d3864830a1780b2052823410f07b83881b60d405f82ac0e607003681a40c806102f016807403501980c4056026012008802200d0060024010007003000c004001 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x63d28553648f546c9a04b7c5972b09538a2c505279938491047623311548844231f80f8469e3281790b7c54e29614209c84322070fb87983a61b40c085c828e139099049021e10307a83b81b80d606802ac12008c04401b40d205001a80c405c02c01580a404c024011008403c01d00e006402e01600a004401e00d0060024010007 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x250121288d42b212d05e79837719b4bea59c2bc956ca8252628c13ec9d84ce25a126491646e23291808a24001be8d7c69831d1870bb85b82be15589f04da24d11d88c44462150e606d034218e09c84c024a0fc07983a01a405f02f01680b2055028011c07a02c013809804a022010808003a016009004401e00d00600280100060018008002000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x11e23243c85108203bd272ed2d7e2d2588ad9532945189f139a664b293522233456895099fd3986fcdb9a032a618be96e2ce554a713d2684b0901141fe3e0798ee1a032c638b61642bc5285f0bc1682c8550a011c1e82c04e098128220420800e8160240440780d0180280400600600800800 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record004_frame002_links_0000 record004_frame002_links_0064)
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x57e56855854651d5084e34c54a84944904684283ce3b93b035f3493433262fc2cd2a629e29a29729425223c23721b1e71b618918017a1751711371270fc0e70e00d20c40b608a06b06005e05d05c05a05705405204b04904503b03402802702401e01c01301200f009007004003002001000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x5585084a84a04944904684283ce3c43b93b035f3493433262fc2cd2a629f29a29729426025224a23c23722521b1fc1e71c01b61a518917a17517113712a0ff0e70e00d50c40b606b05e05d05a05405204b04904503b03503402802702401e01c01501301201100f00c009007004003002001000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
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
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x371dad2d3e54ba5f92ca8d241e1f9cfb07c23da1e9cac644a2188e786102b31520a38500273119089042c2080f1875434c18f0c406082dc14b093842c20a0fe07b83a01b60b6053025811e06b031017c0bc05602a00cc0540270130078038015009804802200f005002400e0060018008002000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 71 :=
  interval_of_check _ 64 7 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 71 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xc2755c27fd3a484941e20d4fb26743339964bcc5bf2cc949092e45a22a90046fc34e1978c7c5d82db1568a384fc24b11d08c03bc1b50c585a42ac14509e04c024811808403fc1e60e706d824010a08303581a80c2054026812c06a03301900a8052026010807003201700a004c02400f00700280120070028008002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
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
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x52fa45d0107db3e29e28e006d035b1a10cce6602f5172cb6855627a935c95e483238917889e3f01ef0f507843bd1cd8dec6c43501938c545c02bf15c09fc4da25a0ca86142ea14109884842220fe07983981b006b03501880bc054026812c07a03b01980c80540290130080038015009804802200f00700280120070030008002000 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x18e6a0e4d9a5f52ea929490a3a51c688a4031c7ccf665332017d4b765942a713748ec41f2068fc07c23ce1c30d3064a2df137081c36019e0c085c82be13308704281fa0ed074838c16409003681980c805e02e01640ac054026812c08203601880b805802400f0070032017007802400e005002000c002000 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 74 :=
  interval_of_check _ 64 10 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 74 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x7296875bc5515385295224fc4de4bd4a846f46242b3e439338634a30c2d02c92c42b62b02ab28726224b2041c31bb19d18c17c16f15f13512d11d1040fc0ef0e60c40c10bc09207f07d06b05b05905404d04b04704503903703302a02702302101d01c01901701000f00e00c00a007006003001000 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x8c115e193a86e4d81a03055f0bb964ac15148b11221a4027d8f61e63b4738de19f3005acaa94e2924e89792b24c4888e1042023c8740e41a4324628c21742d4538a40f21cc380670ae14c290490861042003806c0981182103e0780c81702804c0800e01a0280480800800c00800 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
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
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0xf35b333c64ac016dad0598aed5025149691d162263f472ce31b733e66cae15629c47c871031f23bc720db1b033c660c61762c45109a1102143d0710ce1702c0560961281f8370640c41502803e0780e81101c0280480700c01001800 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 67 :=
  interval_of_check _ 64 3 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 67 record032_frame001_links_0000 record032_frame001_links_0064)
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (Fin.cases (record032_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x16a6ac14f3a55516a89238b1c10d2267e32e9704b5e53c294942093a48f24091bc8303a61aa8bb8530279135896049622d10d08344001e40da86583101750b4052826e12a08e84041d20e206d835010a07d03781a80c005b026811407203701a80c8054028013008c03201700a004c02000e0050024010007002000c004001 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x69c32815a6a3b4cea5952068e02e916e8a7a525281919c8a84232088fc47a23631a58b3856c2940fc07943681a20c1058825611d08783f01c40dc06b03401500a0049023410a07d03781a806e03201500a004c02300f807803a01c00a804c02200e0050024010007 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ record034_frame001_links_0000
theorem record034_frame001_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 1 :=
  of_group record034 1 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record034_frame001_indices record034_frame001_graph record034_frame001_links
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (Fin.cases (record034_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
def record035_frame001_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x258d1608363be9d9cda66bd328990cb7e59b2a1148ca2e50727e12d492c48a23d11bc8ac4512008eec6be34e19f8cbc63e30a1750af855a29e14709f84d2249118888c4381de0bc051c27813008a84281fe0f306c03480c805b02b013408604101c80dc058029011808803c01d00c805c02200f0070030014009002800c002000 } : Fields).get c.val)
theorem record035_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 64 79 :=
  interval_of_check _ 64 15 (by decide +kernel)
theorem record035_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record035) (record035.maps 1)
      (record035.inverseMaps 1) record035_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 79 record035_frame001_links_0000 record035_frame001_links_0064)
theorem record035_frame001_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 1 :=
  of_group record035 1 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record035_frame001_indices record035_frame001_graph record035_frame001_links
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (Fin.cases (record035_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xd37688b2895a4aac51ea67523e90a4701748b7456129e9460a064df238915087a43121190447e03d11b18d2c5e42ce1548a504e02020f287383841b40d106042c412b08e843c2060fc06e03581a00a804b024c11a08503981c00d403201500a004c024011807803a01c00a804c02200f0070024010007 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 73 :=
  interval_of_check _ 64 9 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 73 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x3859bc4ca05d8adf547699d4b9a5952228e02e916e8a9252528c137c91043121190487e03d11b18d2c5b42b615489c04321c20da068c30216209584742060fc07703701ac0d0054028814009404682140fe07d03881a807203201500a0048023010807803a01c00a804c01e00e0060024010007 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 71 :=
  interval_of_check _ 64 7 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 71 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6245e75b854653851b5074e34d54c34a74a142b3d137d31a2fb2db2a529b23721b1f91df1b61a218f16c14c13a1371141090fc0f40e70df0d20ca0c40b50ae09408e07707506f06c05c05a05705404504003b03602e02c02502402001e01301200f00d009008004003001000 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
def record043_frame001_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6245e75b85385074d54a743742b3dd3d13a737d31a2fb2db2a529b26024a23722521b1df1c01b618f18216c14c13a1371141090ff0f40e70df0d50ca0c40b50ae09408e07707506f06c05a05404504204003b03903602e02c02502402001e01501301201100f00d00c009008004003001000 } : Fields).get c.val)
theorem record043_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record043_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record043) (record043.maps 1)
      (record043.inverseMaps 1) record043_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record043_frame001_links_0000 record043_frame001_links_0064)
theorem record043_frame001_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 1 :=
  of_group record043 1 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record043_frame001_indices record043_frame001_graph record043_frame001_links
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (Fin.cases (record043_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x5395064d64a643742b3dd3d13a734332630c2f52cd2bd2ac29027422c22520b1fa1e51d51c21c01a318718217b14e13c1371131080ff0f60e70de0d50cc0c40b40ae09108b07907105a05404504204003b03903602802702402201e01d01901701101000f00c00b009004003001000 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 74 :=
  interval_of_check _ 64 10 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 74 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record048_frame001_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x15e691244d21dce9a7373929c00da86ba35918a8c3253329293d49ae4c3258927c9224402088e6c71637b1b58d8869c3251898ae04fa26b11a08883fa1de0e0869c2a214109884782220f3073035419209e03a81cc0bc058021810408003d01d80dc06c02a013008804001d00c805c02200f007002c0140090030014002000 } : Fields).get c.val)
theorem record048_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record048_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record048) (record048.maps 1)
      (record048.inverseMaps 1) record048_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record048_frame001_links_0000 record048_frame001_links_0064)
theorem record048_frame001_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 1 :=
  of_group record048 1 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record048_frame001_indices record048_frame001_graph record048_frame001_links
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (Fin.cases (record048_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
def record049_frame001_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xc1a51da62d24c8f642e20f906081c3ff1fc0fce6af327180cbf05722b11474a1a4f827491688a042b210906879a39d1be8dbc67a31d1878bd85e02b813288f44562030fd07183001770b5853c28c13a09304602140f8074825012006f03581900be05b02a815007203701a80cc05802a013809804602100e8070032017009804801e00e005002000e0050018008002000 } : Fields).get c.val)
theorem record049_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record049_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record049) (record049.maps 1)
      (record049.inverseMaps 1) record049_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record049_frame001_links_0000 record049_frame001_links_0064)
theorem record049_frame001_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 1 :=
  of_group record049 1 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record049_frame001_indices record049_frame001_graph record049_frame001_links
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (Fin.cases (record049_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
def record050_frame001_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6685b75ac5a758f53a5074d74a749f49449048a4373dd39c39837d33132730b2fb2d82ce2bc2a529729428f27425423e23721d1fb1df1b81a418f1811751711371141090fe0f70e70df0d40cd0c40b509f08a07506c06706406205a05405204204003903603503102e02c02602402101e01c01901701301200f00d009008007005004003001000 } : Fields).get c.val)
theorem record050_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record050_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record050) (record050.maps 1)
      (record050.inverseMaps 1) record050_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record050_frame001_links_0000 record050_frame001_links_0064)
theorem record050_frame001_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 1 :=
  of_group record050 1 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record050_frame001_indices record050_frame001_graph record050_frame001_links
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (Fin.cases (record050_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
def record052_frame001_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x342d994a8950827193208f9468a2b113484140e1fe8fd27d62aa937092445c1e28e746f03661868ba058c2b515108f846422a0fd07c83ac1d00da06b032018a09e84d425e12108c844c2180f607803a416408d04601ec0e206d03501a40cc064030016c0b405602a815008603901a80c806202e01600a004602200f007403801900b80540260110070034018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record052_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record052_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record052) (record052.maps 1)
      (record052.inverseMaps 1) record052_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record052_frame001_links_0000 record052_frame001_links_0064)
theorem record052_frame001_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) : Supported record052 1 :=
  of_group record052 1 (smallEmbedding record052) (small_cells_exact record052 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record052_frame001_indices record052_frame001_graph record052_frame001_links
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (Fin.cases (record052_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record052_frames_supported
theorem record053_frame000_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    Supported record053 0 :=
  of_identity record053 0 (by decide +kernel)
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record056_frame001_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x4259f64ece7413989af4d2e68732198f4b7e599293145ca0e4f924c92288f446c23291448023bb1c80d7c69c33f1978c7c5d42d915f0ab453c28e13f0924470231111887040c1de0da85e027813009204541fe0f307383601a405e02c813409604102000dc06c029013008804201d00c805c02200f00700300140090030014002000 } : Fields).get c.val)
theorem record056_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record056_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record056) (record056.maps 1)
      (record056.inverseMaps 1) record056_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record056_frame001_links_0000 record056_frame001_links_0064)
theorem record056_frame001_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) : Supported record056 1 :=
  of_group record056 1 (smallEmbedding record056) (small_cells_exact record056 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record056_frame001_indices record056_frame001_graph record056_frame001_links
def record056_frame002_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x4039e28e8072a3929b48d706b23151864b965b42ac1510a6652526212c093e49124111008223dd1e08e6c71637b1b58d8864a31317a0b885a62c115c09f44d625911a08883fa1de0e086502a214109884782020f3073035419205e02c813409604102000dc06c029013008804201d00c805c02200f00700300140090030014002000 } : Fields).get c.val)
theorem record056_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record056) (record056.maps 2) (record056.inverseMaps 2) record056_frame002_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record056) (record056.maps 2) (record056.inverseMaps 2) record056_frame002_indices (Fin.ofNat record056.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record056_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record056) (record056.maps 2)
      (record056.inverseMaps 2) record056_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record056_frame002_links_0000 record056_frame002_links_0064)
theorem record056_frame002_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) : Supported record056 2 :=
  of_group record056 2 (smallEmbedding record056) (small_cells_exact record056 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record056_frame002_indices record056_frame002_graph record056_frame002_links
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (Fin.cases (record056_frame001_supported hcells) (Fin.cases (record056_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
def record057_frame001_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x72c3791a20c7a626b0ed7e6b7f555a8553d09d64cea63d2928fc47aa364bea5b82c89584a9c4da24411d88383f01f08f2c70c3491910bc85be26b10c881c35a1810b9057028e139087840c1dc0dc06802a014c09c048824011808504181e40dc06d03480d405c02c013009004201e00e006402e0110078030012007 } : Fields).get c.val)
theorem record057_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record057_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record057) (record057.maps 1)
      (record057.inverseMaps 1) record057_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record057_frame001_links_0000 record057_frame001_links_0064)
theorem record057_frame001_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) : Supported record057 1 :=
  of_group record057 1 (smallEmbedding record057) (small_cells_exact record057 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record057_frame001_indices record057_frame001_graph record057_frame001_links
def record057_frame002_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6e76c468e66b65e65a64661c5df5b95ac5a757255c5054a549e48837d35c3463313272f92d82ce2a329729428e27425023a22521d1e41c01b818617517116a14b1390fd0ec0d30bc0ad09909809108b08a08607f07d07506c06b06703502e02c02602402101e01c01901701100f00c009007 } : Fields).get c.val)
theorem record057_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record057) (record057.maps 2) (record057.inverseMaps 2) record057_frame002_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record057) (record057.maps 2) (record057.inverseMaps 2) record057_frame002_indices (Fin.ofNat record057.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record057_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record057) (record057.maps 2)
      (record057.inverseMaps 2) record057_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record057_frame002_links_0000 record057_frame002_links_0064)
theorem record057_frame002_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) : Supported record057 2 :=
  of_group record057 2 (smallEmbedding record057) (small_cells_exact record057 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record057_frame002_indices record057_frame002_graph record057_frame002_links
def record057_frame003_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0xa4f436714b99592924bc7f8a50a60d4147eafadd7b696cad4555a9550e9e93aa524668b1011f43de794ec9c536a68cce16c2a853c9812023844c810f61aa3305e0af14a230458861001fc3e0760e81bc348680ca0cc1602b04a08c1001d0360640b81101e03004807 } : Fields).get c.val)
theorem record057_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record057) (record057.maps 3) (record057.inverseMaps 3) record057_frame003_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record057) (record057.maps 3) (record057.inverseMaps 3) record057_frame003_indices (Fin.ofNat record057.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record057_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record057) (record057.maps 3)
      (record057.inverseMaps 3) record057_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record057_frame003_links_0000 record057_frame003_links_0064)
theorem record057_frame003_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) : Supported record057 3 :=
  of_group record057 3 (smallEmbedding record057) (small_cells_exact record057 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record057_frame003_indices record057_frame003_graph record057_frame003_links
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (Fin.cases (record057_frame001_supported hcells) (Fin.cases (record057_frame002_supported hcells) (Fin.cases (record057_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
def record058_frame001_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x217506480f3ff1f6cfa46f93691b18afc5592a714349de4c424992008e246322b912487642f2130ce86423151818bdc5d02d61650afc53a278130094847423111107fc3e41e50e306c83501990c806142ec16d0b2055425e12208b01640ae05602a811c08a04201700b005202100f807803a011007803801a00c0050024010006002000c004000 } : Fields).get c.val)
theorem record058_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record058_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record058) (record058.maps 1)
      (record058.inverseMaps 1) record058_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record058_frame001_links_0000 record058_frame001_links_0064)
theorem record058_frame001_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) : Supported record058 1 :=
  of_group record058 1 (smallEmbedding record058) (small_cells_exact record058 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record058_frame001_indices record058_frame001_graph record058_frame001_links
def record058_frame002_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0xd059a327646c59892c8576ad12e25349a8e916a1d418815001f93e87c4f51e53c4620be1762d4594b015429e52ca09352524948c91521a40c7e0f51ce37c6d0d219a328610bd1742c8538a113610c2084007e0e01b0340500981201e03806c0d01101e0380680c0140240400600800c01000 } : Fields).get c.val)
theorem record058_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record058) (record058.maps 2) (record058.inverseMaps 2) record058_frame002_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record058) (record058.maps 2) (record058.inverseMaps 2) record058_frame002_indices (Fin.ofNat record058.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record058_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record058) (record058.maps 2)
      (record058.inverseMaps 2) record058_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record058_frame002_links_0000 record058_frame002_links_0064)
theorem record058_frame002_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) : Supported record058 2 :=
  of_group record058 2 (smallEmbedding record058) (small_cells_exact record058 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record058_frame002_indices record058_frame002_graph record058_frame002_links
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (Fin.cases (record058_frame001_supported hcells) (Fin.cases (record058_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
def record059_frame001_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xaed566ab0d0ba8324079ff8fb67d237c9b48d8c493238915c89242f2130e746ea3671a80ce862a2f71740b2857e29d14489e04d8260129091847423111107fc3e41e50e306d035019b0c806142f016d0b2055425e12208b01fc0fa07a02c815c0ac055023811408402100f807803a01900b8050022010007803801a00c0050024010006002000c004000 } : Fields).get c.val)
theorem record059_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record059_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record059) (record059.maps 1)
      (record059.inverseMaps 1) record059_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record059_frame001_links_0000 record059_frame001_links_0064)
theorem record059_frame001_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) : Supported record059 1 :=
  of_group record059 1 (smallEmbedding record059) (small_cells_exact record059 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record059_frame001_indices record059_frame001_graph record059_frame001_links
def record059_frame002_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x3fe7e8fb5a0b3464ec8d8b312590aed5a20c4007d0f89e53c46a4cd192320620bb1652c053ca59412784d49812924a4808c91521a40c7e0f51ce3806d0d319a328618bd1742c8538a113616c2c8570861042003f0700d81a01e03806c0d0160280480881001e0380680c0140240400600800c01000 } : Fields).get c.val)
theorem record059_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record059) (record059.maps 2) (record059.inverseMaps 2) record059_frame002_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record059) (record059.maps 2) (record059.inverseMaps 2) record059_frame002_indices (Fin.ofNat record059.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record059_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record059) (record059.maps 2)
      (record059.inverseMaps 2) record059_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record059_frame002_links_0000 record059_frame002_links_0064)
theorem record059_frame002_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) : Supported record059 2 :=
  of_group record059 2 (smallEmbedding record059) (small_cells_exact record059 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record059_frame002_indices record059_frame002_graph record059_frame002_links
def record059_frame003_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xc4d604af851ce8d9465a31116c8af3f51eb8f144c0259129493c49024490607a23a61bf8da86823191820b6858e2a914c0a284f226b12d892c47822d10d87f83e01e20e306d434e1960c405e02d01590a504e023610d07f81fc0fa07a02c815c0ac055023811408402100f807803a01900b8050022010007803801a00c0050024010006002000c004000 } : Fields).get c.val)
theorem record059_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record059) (record059.maps 3) (record059.inverseMaps 3) record059_frame003_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record059) (record059.maps 3) (record059.inverseMaps 3) record059_frame003_indices (Fin.ofNat record059.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record059_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record059) (record059.maps 3)
      (record059.inverseMaps 3) record059_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record059_frame003_links_0000 record059_frame003_links_0064)
theorem record059_frame003_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) : Supported record059 3 :=
  of_group record059 3 (smallEmbedding record059) (small_cells_exact record059 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record059_frame003_indices record059_frame003_graph record059_frame003_links
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (Fin.cases (record059_frame001_supported hcells) (Fin.cases (record059_frame002_supported hcells) (Fin.cases (record059_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
def record060_frame001_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x12ee9514a298bcc165ec2ef16fcb6a57e2ac9538a4e51128113cc9ce4d726412f09644141f90f947b239d1ba8d9c53a28913c09b04c025212308e84622200fe87c43c81d60e306a03201850b685902a612d090845420e0e906f03500cc06403080d406603201880b8058029013009004602200c805c02800c00500240100060028010006002 } : Fields).get c.val)
theorem record060_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record060_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record060) (record060.maps 1)
      (record060.inverseMaps 1) record060_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record060_frame001_links_0000 record060_frame001_links_0064)
theorem record060_frame001_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) : Supported record060 1 :=
  of_group record060 1 (smallEmbedding record060) (small_cells_exact record060 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record060_frame001_indices record060_frame001_graph record060_frame001_links
def record060_frame002_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x1cdb91714a4d43a7c4ee9b13425c4a693521a3c46c8bd1522643e8690b9d839a71ce09a9334648a093c26a4c0949252404648a90c2043ec7a0ef1ce368668ca17a2e8580a6140268488851001ec2684b0920bc1682c0560a0130240460841001f02c0500900c0140240400600a01001802 } : Fields).get c.val)
theorem record060_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record060) (record060.maps 2) (record060.inverseMaps 2) record060_frame002_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record060) (record060.maps 2) (record060.inverseMaps 2) record060_frame002_indices (Fin.ofNat record060.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record060_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record060) (record060.maps 2)
      (record060.inverseMaps 2) record060_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record060_frame002_links_0000 record060_frame002_links_0064)
theorem record060_frame002_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) : Supported record060 2 :=
  of_group record060 2 (smallEmbedding record060) (small_cells_exact record060 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record060_frame002_indices record060_frame002_graph record060_frame002_links
def record060_frame003_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x244c788dad61a734467ccc59530c5e8b95682c8586af55dab3550a894da3e4668b91420c3e8794be9752e05a8b41602aa53ca413e2664b89412323843c810fc1dc39c700d219c320610b41602a82e85b0b00d4198320620b81602904c0901182203205c0a00c0140240400600a01001802 } : Fields).get c.val)
theorem record060_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record060) (record060.maps 3) (record060.inverseMaps 3) record060_frame003_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record060) (record060.maps 3) (record060.inverseMaps 3) record060_frame003_indices (Fin.ofNat record060.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record060_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record060) (record060.maps 3)
      (record060.inverseMaps 3) record060_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record060_frame003_links_0000 record060_frame003_links_0064)
theorem record060_frame003_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) : Supported record060 3 :=
  of_group record060 3 (smallEmbedding record060) (small_cells_exact record060 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record060_frame003_indices record060_frame003_graph record060_frame003_links
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (Fin.cases (record060_frame001_supported hcells) (Fin.cases (record060_frame002_supported hcells) (Fin.cases (record060_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record062_frame001_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x3ff7e6f1dc9b7f6ecdc1902e15749952d25049c8c515a1c42481d009f73e27a8f21a0320624c217b2ec58cae95529e4f49892b23e3fc7c8ed1c2344658c416c2c8570a411c1b42e85c0b215c2984708a0f41b82c04e098128230420800e8130240440780e0180280400600600800800 } : Fields).get c.val)
theorem record062_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record062_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record062) (record062.maps 1)
      (record062.inverseMaps 1) record062_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record062_frame001_links_0000 record062_frame001_links_0064)
theorem record062_frame001_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) : Supported record062 1 :=
  of_group record062 1 (smallEmbedding record062) (small_cells_exact record062 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record062_frame001_indices record062_frame001_graph record062_frame001_links
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (Fin.cases (record062_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record062_frames_supported
theorem record063_frame000_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) :
    Supported record063 0 :=
  of_identity record063 0 (by decide +kernel)
def record063_frame001_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc1a589aa612188f744c207cff07e83eb9b98bbe5641ec0f0c6c82eb1620ad054623e115087042c20f10407e83d81d50e707243841ab0cf86603121810bd05cc29614309b049c22410b07f03bc1d00e206a81fc0fa075037817c0bc05b02c815408e04501e80dc04e026011808403a01900b804c024011008003c01c00c00580280100060018008002000 } : Fields).get c.val)
theorem record063_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record063_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record063) (record063.maps 1)
      (record063.inverseMaps 1) record063_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record063_frame001_links_0000 record063_frame001_links_0064)
theorem record063_frame001_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) : Supported record063 1 :=
  of_group record063 1 (smallEmbedding record063) (small_cells_exact record063 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record063_frame001_indices record063_frame001_graph record063_frame001_links
def record063_frame002_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0814.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0814.count (({ width := 11, code := 0x4998e1165ebbcd754dddb33606b6c61752d04d699125a25432859099e639e708de9b5356680ca1812fa5dcb715a2a25289f93b2664b0861011e6384668c717c2bc548a41361e03b0710da1742e0590ae14c2384507a0dc138260460840e81902e04c0901102003c0700c0160280400600600800800 } : Fields).get c.val)
theorem record063_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record063) (record063.maps 2) (record063.inverseMaps 2) record063_frame002_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record063) (record063.maps 2) (record063.inverseMaps 2) record063_frame002_indices (Fin.ofNat record063.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record063_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record063) (record063.maps 2)
      (record063.inverseMaps 2) record063_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record063_frame002_links_0000 record063_frame002_links_0064)
theorem record063_frame002_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) : Supported record063 2 :=
  of_group record063 2 (smallEmbedding record063) (small_cells_exact record063 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0814
    Papers.RationalityTen.SharedFrameCatalogue.group0814_facts record063_frame002_indices record063_frame002_graph record063_frame002_links
def record063_frame003_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0813.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0813.count (({ width := 11, code := 0x39c6ecd7d8c313600b85692cf596a653b26142c838fc1dd3a8744e69a6324618bf9782e6590ac1462844fc9c92723a45c841051fc3dc718db1a63185c0b21522744b8931121bc370690ca1542a0520a01302003f0720d8130250440800e81902e04c0901102003c0700c0160280400600600800800 } : Fields).get c.val)
theorem record063_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record063) (record063.maps 3) (record063.inverseMaps 3) record063_frame003_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record063) (record063.maps 3) (record063.inverseMaps 3) record063_frame003_indices (Fin.ofNat record063.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record063_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record063) (record063.maps 3)
      (record063.inverseMaps 3) record063_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record063_frame003_links_0000 record063_frame003_links_0064)
theorem record063_frame003_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) : Supported record063 3 :=
  of_group record063 3 (smallEmbedding record063) (small_cells_exact record063 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0813
    Papers.RationalityTen.SharedFrameCatalogue.group0813_facts record063_frame003_indices record063_frame003_graph record063_frame003_links
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (Fin.cases (record063_frame001_supported hcells) (Fin.cases (record063_frame002_supported hcells) (Fin.cases (record063_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record063_frames_supported
theorem record064_frame000_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    Supported record064 0 :=
  of_identity record064 0 (by decide +kernel)
def record064_frame001_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x98e42fa0cd03c8053b39a90d046652fb9738b6e5b12c295a4a324f726c93109624a124992008da3bd1cd8e246f63691b10c9c62a2a814009b848c23511188403dc1dd0e887003721ab0b205002600fe07a039c19006d030017c0b2055023811406a03401700b0050027010808003a013009004401e00e006002000e006002000c004000 } : Fields).get c.val)
theorem record064_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record064_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record064) (record064.maps 1)
      (record064.inverseMaps 1) record064_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record064_frame001_links_0000 record064_frame001_links_0064)
theorem record064_frame001_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) : Supported record064 1 :=
  of_group record064 1 (smallEmbedding record064) (small_cells_exact record064 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record064_frame001_indices record064_frame001_graph record064_frame001_links
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (Fin.cases (record064_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record064_frames_supported
theorem record065_frame000_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) :
    Supported record065 0 :=
  of_identity record065 0 (by decide +kernel)
def record065_frame001_indices (c : Fin record065.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xd1b59aac3d5ccac24e4a68d2f4956468a2b914e8a036b9ad0d3a6372c1157ca904e2247922090247514509d44b623910487f43e41e40d386482f0156093046821e10107b83881b60d405b02880e606e03681b00c805f02f017406e03601a80cc05002701300900240110060024010007003000c004001 } : Fields).get c.val)
theorem record065_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record065.data.requiredEdges q = true := by decide +kernel
theorem record065_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record065_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 64 73 :=
  interval_of_check _ 64 9 (by decide +kernel)
theorem record065_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record065) (record065.maps 1)
      (record065.inverseMaps 1) record065_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 73 record065_frame001_links_0000 record065_frame001_links_0064)
theorem record065_frame001_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) : Supported record065 1 :=
  of_group record065 1 (smallEmbedding record065) (small_cells_exact record065 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record065_frame001_indices record065_frame001_graph record065_frame001_links
def record065_frame002_indices (c : Fin record065.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0825.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0825.count (({ width := 11, code := 0x377664ca590b185c6b6166ac551e9cd37a6945a895102023ba748e61ae2ec5c8b716220a3fc7c0ee1c63786e0d718c3085e0b51542945189f134234448861021f0330610c017c2c0530a41441b0350680cc1402704c090090110180240400700c00c01001 } : Fields).get c.val)
theorem record065_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0825.graphBitCheck record065.data.requiredEdges q = true := by decide +kernel
theorem record065_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record065) (record065.maps 2) (record065.inverseMaps 2) record065_frame002_indices (Fin.ofNat record065.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record065_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record065) (record065.maps 2) (record065.inverseMaps 2) record065_frame002_indices (Fin.ofNat record065.n i)) 64 73 :=
  interval_of_check _ 64 9 (by decide +kernel)
theorem record065_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record065) (record065.maps 2)
      (record065.inverseMaps 2) record065_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 73 record065_frame002_links_0000 record065_frame002_links_0064)
theorem record065_frame002_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) : Supported record065 2 :=
  of_group record065 2 (smallEmbedding record065) (small_cells_exact record065 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0825
    Papers.RationalityTen.SharedFrameCatalogue.group0825_facts record065_frame002_indices record065_frame002_graph record065_frame002_links
def record065_frame003_indices (c : Fin record065.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0819.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0819.count (({ width := 11, code := 0x4a287f0c61341b7b8f39e0bb26e2d25a333e5b6b356329a4e69a530a3d3f07c4f71df2ae550a313824a4748c9111f23c0720db18e3005d8b215826c4a8911021e42e8590b015c2984f09c134190310600b81382604a090090110180240400700c00c01001 } : Fields).get c.val)
theorem record065_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.graphBitCheck record065.data.requiredEdges q = true := by decide +kernel
theorem record065_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record065) (record065.maps 3) (record065.inverseMaps 3) record065_frame003_indices (Fin.ofNat record065.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record065_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record065) (record065.maps 3) (record065.inverseMaps 3) record065_frame003_indices (Fin.ofNat record065.n i)) 64 73 :=
  interval_of_check _ 64 9 (by decide +kernel)
theorem record065_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record065) (record065.maps 3)
      (record065.inverseMaps 3) record065_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 73 record065_frame003_links_0000 record065_frame003_links_0064)
theorem record065_frame003_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) : Supported record065 3 :=
  of_group record065 3 (smallEmbedding record065) (small_cells_exact record065 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0819
    Papers.RationalityTen.SharedFrameCatalogue.group0819_facts record065_frame003_indices record065_frame003_graph record065_frame003_links
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (Fin.cases (record065_frame001_supported hcells) (Fin.cases (record065_frame002_supported hcells) (Fin.cases (record065_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record065_frames_supported
theorem record066_frame000_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) :
    Supported record066 0 :=
  of_identity record066 0 (by decide +kernel)
def record066_frame001_indices (c : Fin record066.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0x4847c8f6d802f15d4b9d6fad2574a853c26f4c094d1ba2b44485cfe9ee3d279cf01d437c69cc017b2dc590a61412744c8891031dc3ac710d819c2d44e09611a2003b8760d61802f83f0680cc1602a05009c130250480840f01d0380640b8130240440800f01802404007 } : Fields).get c.val)
theorem record066_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record066.data.requiredEdges q = true := by decide +kernel
theorem record066_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record066) (record066.maps 1) (record066.inverseMaps 1) record066_frame001_indices (Fin.ofNat record066.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record066_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record066) (record066.maps 1) (record066.inverseMaps 1) record066_frame001_indices (Fin.ofNat record066.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record066_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record066) (record066.maps 1)
      (record066.inverseMaps 1) record066_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record066_frame001_links_0000 record066_frame001_links_0064)
theorem record066_frame001_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) : Supported record066 1 :=
  of_group record066 1 (smallEmbedding record066) (small_cells_exact record066 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record066_frame001_indices record066_frame001_graph record066_frame001_links
def record066_frame002_indices (c : Fin record066.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0709.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0709.count (({ width := 9, code := 0x156964adfef7793c1daeb7337db2d769b3d98cb653257eb85a2c960ae54a893e9c4ca51228f46a2cfe78359a0cc6431168a450279289248219007e2d150a450271208c44211007c3c1d0e0642e1309044200f060241007 } : Fields).get c.val)
theorem record066_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0709.graphBitCheck record066.data.requiredEdges q = true := by decide +kernel
theorem record066_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0709.localPairCheck (smallEmbedding record066) (record066.maps 2) (record066.inverseMaps 2) record066_frame002_indices (Fin.ofNat record066.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record066_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0709.localPairCheck (smallEmbedding record066) (record066.maps 2) (record066.inverseMaps 2) record066_frame002_indices (Fin.ofNat record066.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record066_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0709.localPairCheck (smallEmbedding record066) (record066.maps 2)
      (record066.inverseMaps 2) record066_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record066_frame002_links_0000 record066_frame002_links_0064)
theorem record066_frame002_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) : Supported record066 2 :=
  of_group record066 2 (smallEmbedding record066) (small_cells_exact record066 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0709
    Papers.RationalityTen.SharedFrameCatalogue.group0709_facts record066_frame002_indices record066_frame002_graph record066_frame002_links
def record066_frame003_indices (c : Fin record066.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0679.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0679.count (({ width := 8, code := 0xb8a9a8948f8c8b8a89878685848382807f7e7d7773706f6e6c696867656462605f5e5d545048454443423d3837363332312e2d2c2221201f1e1d1c1b1a191817161512100e0d0c0b0a09080706 } : Fields).get c.val)
theorem record066_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0679.graphBitCheck record066.data.requiredEdges q = true := by decide +kernel
theorem record066_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0679.localPairCheck (smallEmbedding record066) (record066.maps 3) (record066.inverseMaps 3) record066_frame003_indices (Fin.ofNat record066.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record066_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0679.localPairCheck (smallEmbedding record066) (record066.maps 3) (record066.inverseMaps 3) record066_frame003_indices (Fin.ofNat record066.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record066_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0679.localPairCheck (smallEmbedding record066) (record066.maps 3)
      (record066.inverseMaps 3) record066_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record066_frame003_links_0000 record066_frame003_links_0064)
theorem record066_frame003_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) : Supported record066 3 :=
  of_group record066 3 (smallEmbedding record066) (small_cells_exact record066 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0679
    Papers.RationalityTen.SharedFrameCatalogue.group0679_facts record066_frame003_indices record066_frame003_graph record066_frame003_links
def record066_frame004_indices (c : Fin record066.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x97347e23d4bea5bf2cc1618ae8561294937c91047622a90c48023f01f08f4470c3501948c5c60a2f215d09c04322070f307083241810b9058828e13908e845821e10908183b81b80d6068028812209003f81b80da04701b00d405c02c014009c04c025012008403c01d00e006402e013009004402000f0060024010007 } : Fields).get c.val)
theorem record066_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record066.data.requiredEdges q = true := by decide +kernel
theorem record066_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record066) (record066.maps 4) (record066.inverseMaps 4) record066_frame004_indices (Fin.ofNat record066.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record066_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record066) (record066.maps 4) (record066.inverseMaps 4) record066_frame004_indices (Fin.ofNat record066.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record066_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record066) (record066.maps 4)
      (record066.inverseMaps 4) record066_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record066_frame004_links_0000 record066_frame004_links_0064)
theorem record066_frame004_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) : Supported record066 4 :=
  of_group record066 4 (smallEmbedding record066) (small_cells_exact record066 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record066_frame004_indices record066_frame004_graph record066_frame004_links
def record066_frame005_indices (c : Fin record066.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0824.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0824.count (({ width := 11, code := 0x408720e3565abc564ab552a9a5129b524a4446a8a109a0a40c7f4f11d739871cdf1b734061cb115c29a5089612523e45c800f41b8360698cc18c2d45109c1302143e07b0e019c3304506c0d41702c05009c130250480840f01d0380640b8130240440800f01802404007 } : Fields).get c.val)
theorem record066_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.graphBitCheck record066.data.requiredEdges q = true := by decide +kernel
theorem record066_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record066) (record066.maps 5) (record066.inverseMaps 5) record066_frame005_indices (Fin.ofNat record066.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record066_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record066) (record066.maps 5) (record066.inverseMaps 5) record066_frame005_indices (Fin.ofNat record066.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record066_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record066) (record066.maps 5)
      (record066.inverseMaps 5) record066_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record066_frame005_links_0000 record066_frame005_links_0064)
theorem record066_frame005_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) : Supported record066 5 :=
  of_group record066 5 (smallEmbedding record066) (small_cells_exact record066 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0824
    Papers.RationalityTen.SharedFrameCatalogue.group0824_facts record066_frame005_indices record066_frame005_graph record066_frame005_links
theorem record066_frames_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) :
    ∀ f : Fin record066.g, Supported record066 f :=
  (Fin.cases (record066_frame000_supported hcells) (Fin.cases (record066_frame001_supported hcells) (Fin.cases (record066_frame002_supported hcells) (Fin.cases (record066_frame003_supported hcells) (Fin.cases (record066_frame004_supported hcells) (Fin.cases (record066_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record066_frames_supported
theorem record067_frame000_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) :
    Supported record067 0 :=
  of_identity record067 0 (by decide +kernel)
def record067_frame001_indices (c : Fin record067.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1ab6d4755fa54d1dc8dd46ca31117a8b445798d09be4c025b92c89544a524f12246823261820b5c58e28a13a896c47222d10d87c03c41a70c905e02ac14a09c04341fe0ee074026012c09203e81cc0c805902c01580aa04101b80a004201f00f007402200e0068030012008003000c004000 } : Fields).get c.val)
theorem record067_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record067.data.requiredEdges q = true := by decide +kernel
theorem record067_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record067) (record067.maps 1) (record067.inverseMaps 1) record067_frame001_indices (Fin.ofNat record067.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record067_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record067) (record067.maps 1) (record067.inverseMaps 1) record067_frame001_indices (Fin.ofNat record067.n i)) 64 70 :=
  interval_of_check _ 64 6 (by decide +kernel)
theorem record067_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record067) (record067.maps 1)
      (record067.inverseMaps 1) record067_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 70 record067_frame001_links_0000 record067_frame001_links_0064)
theorem record067_frame001_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) : Supported record067 1 :=
  of_group record067 1 (smallEmbedding record067) (small_cells_exact record067 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record067_frame001_indices record067_frame001_graph record067_frame001_links
theorem record067_frames_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) :
    ∀ f : Fin record067.g, Supported record067 f :=
  (Fin.cases (record067_frame000_supported hcells) (Fin.cases (record067_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record067_frames_supported
theorem record068_frame000_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) :
    Supported record068 0 :=
  of_identity record068 0 (by decide +kernel)
theorem record068_frames_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) :
    ∀ f : Fin record068.g, Supported record068 f :=
  (Fin.cases (record068_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record068_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023
