module
prelude
public import GraphInputsRow24Part00010Data
public import RawFrameSupport
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010
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
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x18d2d2d6a9af20e3f4468810a60dc1580f00df33d479af19d6398722e15a6b29640bd9612a653ca45462534888d112a214267c0de9a8340648c315a27a4d4941202283e0798dd1a032c638b61642944206a0b41582a84909010c1d83a0580941102003c0740b00f01a0280480800600800800 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x69532dd7eab41530a6911ca8ad41fa0bcfd27b63d39e0cd8260d29691c07623791858bec56a282139894c49a24612008dc4602070f507903ae1c80d2867833018a0be05d02dc1580a184d425012108283bc1d208c03981a40c605c02d01580aa05401d80c4056024011007803a01c00d806802e01600a803c01a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd2a65bafd54c29ff4e426e13488e5456a10505e7e93db1e9cf066c1296932c9284842380ec46f230d17d8ad4504273129893448c24011b88c040e1ea0f2075c3581a50cf06282e816e0af85602a413509784a024211308283c01d208c03481900c605c02d01580aa05401880b0056024011007803a01c00d806802e01600a803c01a009004001c00a0040018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x29f50d92f1de1141a7e6f69cdb7f6b2d45a5345670cad92aea5ceb1d602ab53e99130a584768b107a003ee7a4f29db3ac6a0cf1912f65d4b49532804a89091a22c3e4798e51c2370688c41642b84706d0b214c2904908a0f81b8350580a41282303a0700b01301c0280400700600800800 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
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
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0xa1b1de284478790d61141a824fcded3bc736dfdacb51694d159c2ab53ea214227a4ea99130a5947688d07a003ee794ed9d638e704dd1b6350678cc17b2ea5a4aa1402424688b10e2103fc7c8f31da394708dc1ae344620bd1642b84706d0b214c2904506e0c01602904a08c0e81c0340580980e0140200380600600800800 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x196eca2636a9814749ee4eda6dd34696d4ada51d1ee8c343ba0c8ff07a63ca9e0cedc73929614189744a724191bc8724272098f0c71e34317f0b104e4261129893448c24011c08c445621b10a08383d61dc0e0869032e17b0ba85b42ce15e0ab852c28613c09b04b824e12108d04481fc0f707403880fa06f02d81540a804501b808c03a01c00d806802e01600a004c02000e005002000e0060018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0814.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0814.count (({ width := 11, code := 0x25d4b595d12e2142a84305606bfd7ecfb1e6bb9736df9b334467cce99b32d58aaf5552a3534a4d43a834f89912ba4045686503a044007d8f69e83be758e81c13766d0c99872da554a493425a4a09291e22c430808fa1e63a0708dc1ac3345f0b81522903b06d0b214c2904506e08c0e81c0360680b81602804c0800e0140200380600600800800 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0814
    Papers.RationalityTen.SharedFrameCatalogue.group0814_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0813.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0813.count (({ width := 11, code := 0x1db3b3754d59a8340678cdd9a32b64ec8989b085eeba1692be574ae15aaac4ac9452123e4728d916a29448839011f03c2750df1bc3746d4d71a833e668c99852fa5dcab94d27048c8b0ff1f03cc778eb1d038c6d8d61a632c630c31802e0548a512e24c370650a41302583f06c0880e81c0360680b81602804c0800e0140200380600600800800 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0813
    Papers.RationalityTen.SharedFrameCatalogue.group0813_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x18c2b9e5b52afd3de9bf4a3a50110a87b4122044fe07dd3bf1db0ebc74f39c9b1cd826af346199cbfa5ed2e81700a9c54a27993209644a223111648744312048fa07b83b81d50e407043681b08bd85922bf15689b84bc24811c08904021f30f3075c33218f0bb05b02c810807c03a81c00d603b016c0b405401f80f8058029011808804001c00d005802600e00680300140070018008002000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0820.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0820.count (({ width := 11, code := 0x238c548a304a013ae73ee4dc6b776dcd31a2b4167cce989b1060ac05612b0516a2125a37454891082053ee79cf11de39e704db9b231860cbb16e2ce578ac946278498869061f63946e8c21702ac530a013625c340620b61582803d0720c4170280440840e01702c0500980e01a02c0480700800800800 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0820
    Papers.RationalityTen.SharedFrameCatalogue.group0820_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x778b4618e0ab3505a57d29891a47fa3691a6879422a0b8f507993ba1c80de8684333966cabc52d28b13c49c24ae23a119888042320a101079e32c1778af854e28213908fc40a1f70e886d034a1950b0047822e0fd07183440c605c02d01580aa049024010807e03b01c00ac04802200f007402c00f00680240100040018008002000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x32dd80caf1559a9d946a96d49a23f117c7fb3f49edcf4e78336916f4afe54228090e48003c81c50b1c56a28313989604a024912088ec44020c10587d83cc1db0e206bc34619a0c9062c30a17e0bb05bc2c815b0a304e8262129091047022a10d08303ec1cc0df06c034812a08c04081e80e406903181680ae05602a815009204201d00c405602200f807803a01c } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6e834a996ec08576ab1d4c2a374b6a4bd1ca8ad41fa0bd0147e93db1e9cf066d42dc964ca5a50321c8fec7623791858bec5ac2b514109cc4b0250124890447622010908143de1e60f007603961aa0d406543161850be85dc2de1640ad8518274131094848823810908303ec1e40ea06f83601a408c04001cc0e006903181700b405602a815009003b01c00c4056024011007803a01c } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xbf9599263925290346ba1b108a8354029fd4fca7db37a9b84d7e68132f1880bfa56528813c899045d22890b88444091fa8f8479e3bd1be0d746382c915309d04d424f12008c042a2060fc87683461760b6058028a13b09784701ea0e506d834412a08c03d018c0b404201f00e806202b011007c03c01d00e006c03401700b005002000d002000c004001 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record032_frame001_links_0000 record032_frame001_links_0064)
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (Fin.cases (record032_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x748b45594ac636162ac14809fe4e6a71537c9b64d8265530c96b4a824e5248918487a41d2008f3475a3911b261f303979cb3c57829813b89564322118fc47c23b01cc0de065e30916089fc4781c30da06082e41590a70508278132096849c23e118088843020a0fe07a83c01c40dc06b034013a09504601e80e406901d00c405e02b011007c03c01d00e006802c00d0050024010007 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
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
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0846.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0846.count (({ width := 11, code := 0x2304408690820bc11798eb5d0b8e71ae05b836369ad018f31c61ec197daf55d6b8953a844ee9b932a5d4928dd122163fc7ccf69e43ba720e31bd36e6c4d39923005a0a994e27a4d89692221c4287e0f51e239c700dc1ac334630bb16e2a85109812823c338650bc1742c85609e0e81983105e0ac1202201a0240400700c00c01001 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0846.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0846
    Papers.RationalityTen.SharedFrameCatalogue.group0846_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0847.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0847.count (({ width := 11, code := 0xc4f802f1da8b19576a6d48a6f4c692d049d931e42c798c51421942682f04dee3d1760e05bb3716c0d61a833363abf16fad6574ac1512954fa9d934a5f4ac94125a2c42a7d0f31e238c6bcd2197324628bd1712d6584ab94e2844c89311d22a4187d8ed1c831c5e0ab1482703e0540760e81c0330620880f01d03806c0d01702c0500780d00c00c01001 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0847
    Papers.RationalityTen.SharedFrameCatalogue.group0847_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record039_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010
