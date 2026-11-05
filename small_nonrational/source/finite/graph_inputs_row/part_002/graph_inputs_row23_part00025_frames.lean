module
prelude
public import GraphInputsRow23Part00025Data
public import RawFrameSupport
public import SharedFrameGroups043Checked
public import SharedFrameGroups044Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups065Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups099Checked
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
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025
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
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1832c0a484a3f111085141f2044ffc72f3011744ae051b27692448e646822d111087242b1e78db461a30315c8a2c4ee25b11086d03221800bb85ac2c014f0a304e825e0f807482c013c08c03c81bc0d606903201680b005502a010c08203701980c405a02c015009804402000e807002e016009803c01a00b005002000e0050018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record001_frame001_links_0000 record001_frame001_links_0064)
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
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x99331644c5d851065f83bb754e81bab656b2d598a2c0564a9d2a2434708a5042043fe78cd319c2f85e0a313f2684b08e9192223bc740dc1aa318608ba1602ac4207f0f81d4368670c01642905109e1342604207a0cc180250440800f81d0380580900e01a0280400700800800800 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x680b3ed7eab4254e298d3ac93047ba39d16c8a844fa268f1667d3261894a504f726812e493849724811d876c3921948c604d225611e08b04162000f886182e61590a484a023a10e07a83bc12808f04602100f007103481880b405902b81540a804502000d0062025011008003e01d00e005802400e00680280100070020008002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x9a33324cc7b8ad1160fbe779ef09ceb8f708dfd9f2e95acb1946a834ec98924a4447a890f29dc3706ccb99702c2564a414026e4087e0ec1c6354668c516a2bc4107f0f81d8360670c01642885009e134260410780c0168240420800f81d0380580900e01a0280400700800800800 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record002_frame003_links_0000 record002_frame003_links_0064)
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x604ac536a6a47f8d711e1cbef7d4ee9d638d708cfd8ab08608be564ac2568a9d4d291508911071fe3f07b0d89aa33262cbd9722c8560a81452244247b0e51983084787e0c61702c8560a6144280490860f81c0350640c41502504407c0e81c02a0400680a01001c0300500800800800 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xc364e8a5652a691348323c11d47f33f11cd4e186a934a96a0a4e50427a13388c645421910808023f11ef0ce4570295142897c3e81e50e186c43241820b7855829e148092847822010407783a415e08c03481880ba05a02b81540a804c022810007403601900c4054025011007c03a01c00a804001a00a004001c00c0050020008002000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x71d6e169265d64c61460355352d4d84af4333f038c3212d62aa24522a2212051e41cf1bf1a118f15f11c1100fb0eb0d50cd0c50a70a209a09708c08607307206c06b05905304003702902802502201f01d01101000c00a005004001000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 62 :=
  interval_of_check _ 0 62 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ record004_frame001_links_0000
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
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
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0xc7361a92d049d72ca48c7f8d31962fb9b678c7984ad9578ab54e299528a053d27346c8a10ca053fa72cdd1ad33c5fcbd9632604948d10b1fa3a8718da18c2dc5708c0f01a8318610be16c2d0540a01382584a07a0d41983105a0b0130220400740e01802e0580981101e0340580a01001c0300500600800800 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
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
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x806eedda38c700db5b0b4e680bed772df5129c135a3f4607bced9ce3746c8d01962dc5a0b39522964dc9911b232414800cf1902f85c8ad1542804c0950ec1c03685e0ba1582a0520a012c240440700c8188290500901001f03804c0900f01c0280480700800800800 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
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
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x5084ff4e149b49248a47146c4514003b43a339738933b31130b3062ec2ba2b42af2a82a429729423c2011fb1f31d519418e18617d1781661621451271080f10dc0cb0ba09808807d06906205f05d05a05905505305204a04904403903503302c02902702402301f01d01c01701401200f00e00a008007005004003002001000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
def record013_frame002_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0801.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0801.count (({ width := 10, code := 0x16e5ad5e52546509364c9304811243d0a418fa3c0ed3ace1350d133ccd32cc530cba2ccb12bca626c9925c9424c90238871f8751ac6417458138481143f0ec3a0e4380dc350cc320c02f0b42c0ac29090220841f0781b06418050120400e0340a020070140400c0200400 } : Fields).get c.val)
theorem record013_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0801.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0801.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0801.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record013_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0801.localPairCheck (smallEmbedding record013) (record013.maps 2)
      (record013.inverseMaps 2) record013_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record013_frame002_links_0000 record013_frame002_links_0064)
theorem record013_frame002_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 2 :=
  of_group record013 2 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0801
    Papers.RationalityTen.SharedFrameCatalogue.group0801_facts record013_frame002_indices record013_frame002_graph record013_frame002_links
def record013_frame003_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x9674b0a50d21890647f23891b88ac3f89cd0dc86bc33f96a4a7452a28c133c8a4442219108881e3e01e88ce85962bb15489803c61d30e186cc3401710b1052026611e08503d81d20dd053023810606b03201840be05c02d815c0aa054026012c08c03901a80cc058029013809004601f00e807002e014009003c01c00a004001c00a0040018008002000 } : Fields).get c.val)
theorem record013_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record013_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record013) (record013.maps 3)
      (record013.inverseMaps 3) record013_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record013_frame003_links_0000 record013_frame003_links_0064)
theorem record013_frame003_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 3 :=
  of_group record013 3 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record013_frame003_indices record013_frame003_graph record013_frame003_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (Fin.cases (record013_frame002_supported hcells) (Fin.cases (record013_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0589.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0589.count (({ width := 11, code := 0x41b73ed5da8b31646c1165ac3572a814c2905009a910a1440e804fa1cf390704dd9b835068cc516a2c8574a393b26048c8f116214418788eb1cc37c6d8d51962dc558a010e2103c0730d01902c0550a81402704d08c114208360620b01482604a08c1101e03806c0b81402403c0700b0140200380400600800800 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0589.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0589
    Papers.RationalityTen.SharedFrameCatalogue.group0589_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6472f0d5d697b4b424251ce8984051fecfd07a63ca9d68d1e5b722390d07aa3b31b20b5858e2b4139098449c23910407c83d81e30e706ec35619e0c8862430417c0b6859c29414309e84d425c12808c83f81de0e2047021010607e03801ac0be05c02d815c0aa054026012c08c038019809c04802300f807403801800b8054028012008803c01c00b005002000e0040018008002000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
def record015_frame002_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0591.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0591.count (({ width := 11, code := 0x7f8f9de5b816f6d79aab3a616c197f2e85c4b595ca9949e92d19a2e4327d0f91ec3ba768e81bd322604be9752c855ca413d26a4b8959272364587c0f21d83946f0d71962d05409a0fc1d83a8720d41942d8580ae14c2885009011c2183806609c1202303e0740e01802e0540a01202203c0700b0140200380400600800800 } : Fields).get c.val)
theorem record015_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record015_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record015) (record015.maps 2)
      (record015.inverseMaps 2) record015_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record015_frame002_links_0000 record015_frame002_links_0064)
theorem record015_frame002_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 2 :=
  of_group record015 2 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0591
    Papers.RationalityTen.SharedFrameCatalogue.group0591_facts record015_frame002_indices record015_frame002_graph record015_frame002_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (Fin.cases (record015_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x192ac76551aa6906882e4009d54e826ab34b9964c8861f2d61660aa054229a93e09864b525411ac8a03ed1d28e4461a2fd1770b684d825c12688e44362060f907803901b30c605e829013c091045c2160ff072836815e08e04681ac0d205c02b815009804b02000d806603201880b4058024011807c03c01c00a805001e00d005002000e0060028010002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa4ea058d68be6af69f68f6526475fa5ee59d57055251b50e4d94cb4bd47c4514434363f13a537934f3422d82cc2be2a92482382282171d81c21ba1ae19c18d17116313712b1080fd0f30e80cb0bf09f08808706906705a05505204c04b04003603303203102d02c02402301f01e01c01501400f00d00a008007006005004001000 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
def record018_frame003_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x322e32b316422bc51887062083e37b4ed9d539b6d8d819eb33654bf570ada59ca854526e498900fe1f13d8770d219d328610b71632b8548a21392464607a0ea1ae33c630c215628c4587a0f21842f85209a128230450780d0198320620b41602404607c0f01c02a0500780d0140200380600a01000800 } : Fields).get c.val)
theorem record018_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record018_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record018) (record018.maps 3)
      (record018.inverseMaps 3) record018_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record018_frame003_links_0000 record018_frame003_links_0064)
theorem record018_frame003_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 3 :=
  of_group record018 3 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record018_frame003_indices record018_frame003_graph record018_frame003_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (Fin.cases (record018_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x26bc43790ef9daba873ee01bd36b6c8d6da4344680c6574a8b4ec985272444568910e21641c81cfd9e93c6770d518e310600bc1712d657ca813e2564848810a2063b8740e41ba358688cb1902a8490841041a0330530a41442704d0981041f83906c0b0148250460881081e03a0700b81401e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0589.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0589.count (({ width := 11, code := 0x20e3a0662c8d8bb0b60ab796cacb586ae95329f52ea0535a2742881cfb1f53c0764ea9cf390704de1ac34e688c316a2c8574aa9522985209d92a24647c8810920a3c4758e61be36c6a8cf1962ac4b8841041a4340550a814c2804f09c1041f03806c0b0148250460881081e03a0700b81401e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0589.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record020_frame002_links_0000 record020_frame002_links_0064)
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0589
    Papers.RationalityTen.SharedFrameCatalogue.group0589_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x5e32bb52128e7468a2b513483f4182028ff67e93da9e94f266922dc8f5476639d1bc8d986162fc16b0b1c56a281138897c49c239111086c4101f20f607743ae1d00dd86cc34c19e0c886282e616c0b2852828613d09a84b825012108c83bc1aa07e03d81cc0e005c02d81680ae05602a811808603b01c009004602200f807803a01800b8054028011007803801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
def record021_frame002_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x564a97d1d28c7459224110a81d4079fa4fb67d23c81df4ed66cc32c13fc9ce4d425e12c88c245721c90bc84c3f51f38f6c76e38f1b68d9c67430517b8b605942bf14509dc4c025111d08c43fe1f20f2869c3361900c205e02da1640ab03e819007e03d81cc0e005c02d81680ae05602a811808603b01c009004602200f807803a01800b8054028011007803801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record021_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record021_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record021) (record021.maps 2)
      (record021.inverseMaps 2) record021_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record021_frame002_links_0000 record021_frame002_links_0064)
theorem record021_frame002_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 2 :=
  of_group record021 2 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record021_frame002_indices record021_frame002_graph record021_frame002_links
def record021_frame003_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0xc0d72a92511a053b66fcb194b23e40c738c1166294197b6ced9531c618c056c2ce574ac152a95520a2d40a6e49a9051421140e7c4f61df396708d79a432861cbb16f2d25189d931248464860fd1e63044d86d0d6198320520a21402684c0961041f03806c0901182203e0780e81802e0540a01101e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record021_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record021_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record021) (record021.maps 3)
      (record021.inverseMaps 3) record021_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record021_frame003_links_0000 record021_frame003_links_0064)
theorem record021_frame003_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 3 :=
  of_group record021 3 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record021_frame003_indices record021_frame003_graph record021_frame003_links
def record021_frame004_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x80af49b135769ad099d31a62ac0d7eaf55c8b816eab7516851049fd3e27a4e79c93726d0d619b32e650c69822de5a4ae94f2964f49c93424e4888c91220e4087a8f31e23786d0d81a2328620bf1742844906d0d61943105009e1382584a0921001e83806c0901182203e0780e81802e0540a01101e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record021_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record021) (record021.maps 4) (record021.inverseMaps 4) record021_frame004_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record021) (record021.maps 4) (record021.inverseMaps 4) record021_frame004_indices (Fin.ofNat record021.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record021_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record021) (record021.maps 4)
      (record021.inverseMaps 4) record021_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record021_frame004_links_0000 record021_frame004_links_0064)
theorem record021_frame004_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 4 :=
  of_group record021 4 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record021_frame004_indices record021_frame004_graph record021_frame004_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (Fin.cases (record021_frame002_supported hcells) (Fin.cases (record021_frame003_supported hcells) (Fin.cases (record021_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x31d18a0a0f4f5a6412a494c490a46d21890647fa38ce6c6e435f1958b2e502279938490a4762339148884432211903c7c23281498a104e421610387e03c61d30e186d03401720a404cc23c11708503f41d20b204702300d606903201840b805a02b81580aa05402180f007203501980c4058029012008803e01e00e807002e0140078034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x6402ae1546a9c518a4fd25891b44621e50d083532c9910c7c5e6292945ca1449824511f48aa42d1f68e9c72633e1978c7c61a2fd1770b7453a28e13f09b04b824d11e08183e41e00e506d42d414809e04902160ff073823811806b03501a40c406102e01680ae05502a00cc06403101500a404802200f807403801800b805402800f0070034014009004001c00c0050020008002000 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0613.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0613.count (({ width := 10, code := 0x8260276db56b5a56799560d7759d635854a5192748d2146d1744d0840cff3ecf73b4e8374d8318be2dcb12b4a526490228831d86d1a46117050130491183d0ec390dc310b82d0a8290a0260942408c2207c1c06c1906017054130440f0340b028080140400400 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0613
    Papers.RationalityTen.SharedFrameCatalogue.group0613_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x14ec90a45aa264f326f43731b5cd1c68033918dcc4c59f2c89608a7252b28e93889a24ab24792208ea46f1f50ee06d433d1810b6053227612d093045421c10707bc3c81b60c985dc2d214709c84ac21810107803a41b60d403781ac0c005c026011807603701b00cc06402c014009c04802300a804c02200f00580280100070028010004001 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x4f19a51a62ec207a0f21d5b936e4db1b2b596a6d31a32cb580ab93ca73472869042043f87d4f01da3a8698ce97c2f2598b193f2584748890d1f43d0740db18c3005b0b01562a05208d1142103f8750ce1983105c0b215c2985109a130210350660c81582604a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
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
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x5229f91922d3f26fcda9b1b5769cc39842da59eabd4c2894d293518217426838fb1ef3ca780e99b73545e8b69682c85709e12f2484848c10f2124107f0f81d83806b8cc19030c5e8b71582a44a88e0fe1b43385b0aa148260450800dc1b0320620b41602504607c0f01c02a04c0800d0140200380600a01000800 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x76fb789aaccde539291d470a21467213107e8193fd1fa4fa67c53db1e9ca7c51328213b47343181858b9458c2b514f8a4450427310087c43bc1980c806282e816e0a184f424211208283bc1d20b204f027012e09404802300f207303601a40c005c02d01580aa05402080ec068031014009004401e00e807002e013008003c01a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record032_frame001_links_0000 record032_frame001_links_0064)
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (Fin.cases (record032_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xc0b5be292147490a428a1010628114001fc4e5e6022fb93dc8d045c22890e485a4221fb0eb871834e1960a884ce25b12608f845a22110908103901b60c906082ee1600a8851825e0f904e025811807b03c81cc0d206403001700b405802b01540a804302080ec06202c014009004402000f007403801800b80540260110078034016009004001c00a0040018008002000 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x31d189ea0f4f5259d296945498248121a8f14752388fe876035e1954a7452a28113809a249a23a914888640f2010fc47c02cb15d8a4c4e226211588183c61d40d0064c3041710a404cc24a11708504101ba0b204902300de06903201800b605a02c015c0aa054023010c07203701a80c4058028011808804001f00e807002e013007003401600a004001c00a0040018008002000 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record034_frame001_links_0000 record034_frame001_links_0064)
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
def record035_frame001_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x470895105f83e37b8d79acb4d680ce194b21632b7d6229f52aa4545a6d4cc8cd039f33d878cee1d639860cbd16d29a4e49992d246440848ef1d038c700d018e2f0590ad150218418810f41bc360660c616c2c0560a4144280410780ec1c8340620b4150280480881081e03a0700b81302003c0680b0120200380400600800800 } : Fields).get c.val)
theorem record035_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record035_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record035) (record035.maps 1)
      (record035.inverseMaps 1) record035_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record035_frame001_links_0000 record035_frame001_links_0064)
theorem record035_frame001_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 1 :=
  of_group record035 1 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record035_frame001_indices record035_frame001_graph record035_frame001_links
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (Fin.cases (record035_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x66f2c01498a2148f23e118284f420a070ff47e93e39ed8f4e5cc28c13b47d43c41c68c6c61a2e81630ad4526282139893846422210087c43c81de0d606403141830bd85d02dc1520a504f426a12f09084141ec0f0074827011807903a01c40d206403001740b805a02b01540a804101e00e406202c014009404802200f007403801800b80540260100078034018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record036_frame001_links_0000 record036_frame001_links_0064)
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
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0814.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0814.count (({ width := 11, code := 0x9ad30e5f44f87b0e1e5b64684cf164aba56aaa54928a4d49692b2504988d517a2a44885d07a0b3ee75ce499f31a620c117e2c256cab1502804d0969081fe3bc6f8cb1842f0538a213e268470881062083b06d0d019c228370640c41682c0540a01282304407c0f01d0380600b8150260400700d01402404007 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0814
    Papers.RationalityTen.SharedFrameCatalogue.group0814_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
def record038_frame002_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0xa4541a7f47e8c9171f837c6acd3557a98524a253a26b49a8f91e23746685d09a0e40c7c8f29e038c6dcd61832da5a0b215f292514a093c264490908fd1ee3ac6f8cf18c304580ab14e28c470840fe1f83b06d0d019c228370640c41682c0540a01282304407c0f01d0380600b8150260400700d01402404007 } : Fields).get c.val)
theorem record038_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record038) (record038.maps 2) (record038.inverseMaps 2) record038_frame002_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record038) (record038.maps 2) (record038.inverseMaps 2) record038_frame002_indices (Fin.ofNat record038.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record038_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record038) (record038.maps 2)
      (record038.inverseMaps 2) record038_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record038_frame002_links_0000 record038_frame002_links_0064)
theorem record038_frame002_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 2 :=
  of_group record038 2 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record038_frame002_indices record038_frame002_graph record038_frame002_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (Fin.cases (record038_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x680b3d14f0a6348623dd1c08c245ea2d914279b3799978c726252cf14249c84d0263930097249724812088f83b91d38cac6322da14c89e04b024c11e08b041c1f10db06542ea1690ac852425610e07b025011c08c03c01ac0d205c02d01600ae05502a013008003901980c4054024011008404001f00e807002e012007803801a00b005002000e0050020008002000 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x18e8c50507a7ad2ec9664a9a53124291b48323fd1e08e339b1b90d7c6562a794a4a044f427092148ec46722910c884640f2008f845c02ba1498a144e421610387e03c61c30da06803241720a404cc24a11e08b83f41d20b204702300d606903201740b805a02b81580aa05402180f007203501980c4058025012008803e01e00e807002e0100078034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
def record043_frame001_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x67a2a694f092e48623811968bd45b22bd14289332e18e4a0e4e425c929492e49024491f08e04441dd0da867e2da14c8a244d625a12608f045a21c10707c836c1a60c405dc2d21590a504e425610f04b023811807b03981ac0d206402e01680b005702b01540a804301d80cc06202c012008804001f00f007403801800b805402200f006802c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record043_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record043_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record043) (record043.maps 1)
      (record043.inverseMaps 1) record043_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record043_frame001_links_0000 record043_frame001_links_0064)
theorem record043_frame001_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 1 :=
  of_group record043 1 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record043_frame001_indices record043_frame001_graph record043_frame001_links
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (Fin.cases (record043_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3385600a4c51224791f08c1456a13d08283040e1fecfd27c73d39730a304f01f50f1071a37918d8c345f82e81638ad452627312708884021f10f207783ae1c20d6069832218a0c185ec2dc1520a504f426a12f094048420a0f6078023811807403881ac0d206402e81700b405702b01540a803c01c80cc06202c012809004401f00f007403801800b805402000f0068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
def record045_frame001_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x18a09eb4e1a65d2ec9664aca54d298928490a46d22690647fa3c11c665630d96a8a9e52928213d09c248723b119c8a843221190047c23ac19d8b8057429514289c84302070fc07943861b40c905c82ac14f0a404cc24a11e08b84401fa0ef074823811806b03481940c806202e81700b405702b01540a803301880b405802a012809004401f00f007403801800b805402000f0068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record045_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record045_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record045) (record045.maps 1)
      (record045.inverseMaps 1) record045_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record045_frame001_links_0000 record045_frame001_links_0064)
theorem record045_frame001_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 1 :=
  of_group record045 1 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record045_frame001_indices record045_frame001_graph record045_frame001_links
def record045_frame002_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19c2a244f6a5f123c8f8469a30515a851420a0c103c7fb3f49f1cf4e4f025c91207d43c41cf8e346f231d1868bf05d42c715a8a4c4e624e11108043e21e40ef075c3661ac0d3067832218a0bd85b82c01590a904f425e128090846820a0f7078023811806b03481940c806202e81700b405702b01540a803301880b405802a012809004401f00f007403801800b805402000f0068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record045_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record045) (record045.maps 2) (record045.inverseMaps 2) record045_frame002_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record045) (record045.maps 2) (record045.inverseMaps 2) record045_frame002_indices (Fin.ofNat record045.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record045_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record045) (record045.maps 2)
      (record045.inverseMaps 2) record045_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record045_frame002_links_0000 record045_frame002_links_0064)
theorem record045_frame002_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 2 :=
  of_group record045 2 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record045_frame002_indices record045_frame002_graph record045_frame002_links
def record045_frame003_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x18a2894f49992ca5149892923a374688c91722944c87d0d19530c5c8b295d2b0558a99432804f89d1352644ac9311d2123f07a0ef1da3a86d0d71aa344660c91842f45b8b616a2c8580af15c2b4550a814e208400650c617c2f05c0ae1582a0510a013c270330620b41602a04a0901101f03c0740e01802e0540800f01a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record045_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record045) (record045.maps 3) (record045.inverseMaps 3) record045_frame003_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record045) (record045.maps 3) (record045.inverseMaps 3) record045_frame003_indices (Fin.ofNat record045.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record045_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record045) (record045.maps 3)
      (record045.inverseMaps 3) record045_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record045_frame003_links_0000 record045_frame003_links_0064)
theorem record045_frame003_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 3 :=
  of_group record045 3 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record045_frame003_indices record045_frame003_graph record045_frame003_links
def record045_frame004_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x1a1aa652ca093aa6d4d099931a534a0939252454848ed1b1a03205f0b79672c4580ae94d294520a213f2784d4981272264187f0f91ee3d0720e11be36c6b0d319831c608c017e2f05d0b91702dc5a0b2162228440690ce18c310600b61682c0550a814c290330620b41602a04a0901101f03c0740e01802e0540800f01a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record045_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record045) (record045.maps 4) (record045.inverseMaps 4) record045_frame004_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record045) (record045.maps 4) (record045.inverseMaps 4) record045_frame004_indices (Fin.ofNat record045.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record045_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record045) (record045.maps 4)
      (record045.inverseMaps 4) record045_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record045_frame004_links_0000 record045_frame004_links_0064)
theorem record045_frame004_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 4 :=
  of_group record045 4 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record045_frame004_indices record045_frame004_graph record045_frame004_links
def record045_frame005_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1111.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1111.count (({ width := 10, code := 0x9460e805ee789da755d3741c16f9bc6e1b36c1a969166565464e9324b52b4a119459144410b421013f0f4384d5334c8318c32d0b12bcab298a3270972449023c8c2288922087210822046c1a85a1605414c511304b124461144410c330c42d0b02a094240881f0781d0701805c150400f0340a0240801c060140400c0200400 } : Fields).get c.val)
theorem record045_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record045) (record045.maps 5) (record045.inverseMaps 5) record045_frame005_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record045) (record045.maps 5) (record045.inverseMaps 5) record045_frame005_indices (Fin.ofNat record045.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record045_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record045) (record045.maps 5)
      (record045.inverseMaps 5) record045_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record045_frame005_links_0000 record045_frame005_links_0064)
theorem record045_frame005_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 5 :=
  of_group record045 5 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1111
    Papers.RationalityTen.SharedFrameCatalogue.group1111_facts record045_frame005_indices record045_frame005_graph record045_frame005_links
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (Fin.cases (record045_frame001_supported hcells) (Fin.cases (record045_frame002_supported hcells) (Fin.cases (record045_frame003_supported hcells) (Fin.cases (record045_frame004_supported hcells) (Fin.cases (record045_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
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
def record047_frame001_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x31413d69c34cba565298930494246d22690d48323fd1e28e332b186cb54504270926890e46722a110c8644232010f8475833b14a89c84562180fc07943a81c30da064c2e41560a7852026612508f045c22010a07e83bc12c08e04601cc0d606903281900c405c02d01600ae05602a815007603301880b405802a012008804001f00f007403801800b805401e00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record047_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record047_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record047) (record047.maps 1)
      (record047.inverseMaps 1) record047_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record047_frame001_links_0000 record047_frame001_links_0064)
theorem record047_frame001_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 1 :=
  of_group record047 1 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record047_frame001_indices record047_frame001_graph record047_frame001_links
def record047_frame002_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33854489ed4be234d15a864428a0c103c80d3fd9fa4f907a727812e489039f1bc8cc063a2fc1750b6458e2b514a09cc49c2220f2075c3761b30d306783301910c505f02dc1600ac854827a12f094048423411308283dc12c08e04601cc0d606903281900c405c02d01600ae05602a815007603301880b405802a012008804001f00f007403801800b805401e00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record047_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record047_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record047) (record047.maps 2)
      (record047.inverseMaps 2) record047_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record047_frame002_links_0000 record047_frame002_links_0064)
theorem record047_frame002_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 2 :=
  of_group record047 2 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record047_frame002_indices record047_frame002_graph record047_frame002_links
def record047_frame003_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0xc5144a7a4cc93123a3b46e8c91722c4528991021a32a618b91582a651ca193e2744e09a9322584988e9091de3a86f0da1aa344678cc19230c5e8b716c2d4590b015e2b8568ac1542a0450821001b4328630be1782e0560a81482885009e1381d8330620b41602a0480881001f03c0740e01802e0540780d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record047_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record047) (record047.maps 3) (record047.inverseMaps 3) record047_frame003_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record047) (record047.maps 3) (record047.inverseMaps 3) record047_frame003_indices (Fin.ofNat record047.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record047_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record047) (record047.maps 3)
      (record047.inverseMaps 3) record047_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record047_frame003_links_0000 record047_frame003_links_0064)
theorem record047_frame003_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 3 :=
  of_group record047 3 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record047_frame003_indices record047_frame003_graph record047_frame003_links
def record047_frame004_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xd0d532965049a131a574a69392524848a9091e236340640be1622ba544a69482885089f93c26c4c0939131f23d0740e41be36c6c8d61a6334638c11802fc5e0ba1722e05b8b61682c84908a1101c4348670c61883005a0b01582a8540a61481d8330620b41602a0480881001f03c0740e01802e0540780d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record047_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record047) (record047.maps 4) (record047.inverseMaps 4) record047_frame004_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record047) (record047.maps 4) (record047.inverseMaps 4) record047_frame004_indices (Fin.ofNat record047.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record047_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record047) (record047.maps 4)
      (record047.inverseMaps 4) record047_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record047_frame004_links_0000 record047_frame004_links_0064)
theorem record047_frame004_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 4 :=
  of_group record047 4 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record047_frame004_indices record047_frame004_graph record047_frame004_links
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (Fin.cases (record047_frame001_supported hcells) (Fin.cases (record047_frame002_supported hcells) (Fin.cases (record047_frame003_supported hcells) (Fin.cases (record047_frame004_supported hcells) (fun j => Fin.elim0 j))))))
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
def record049_frame001_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xcb7647321d8fcad4558a7a92e894048c242518288d432a15908483c337192cb3854128c141c9f64b424591e88dc46322d0df85b823b11788a438c1b40b4850c27213009284181f80f307402c012008f04601e40de06d03581a40ca05f02f01680b205502a010406e03401980c4058027012808804001d00e004c02400f00680280100070018008002000 } : Fields).get c.val)
theorem record049_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record049_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record049) (record049.maps 1)
      (record049.inverseMaps 1) record049_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record049_frame001_links_0000 record049_frame001_links_0064)
theorem record049_frame001_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 1 :=
  of_group record049 1 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record049_frame001_indices record049_frame001_graph record049_frame001_links
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (Fin.cases (record049_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
def record050_frame001_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x2bf565aa53425c4ab83f061ff3f87daf91ef3d9720d81a4b3f65cc8d8bac8578a9533a5948e90515a23436724dc9a32e855ca61462724a0901011f83e0708db1aa32c600bb16c2204207f0f61bc358650c41682b0540a013c270410780ec1a8340620b4140260480881081e03a0700b81302003c0680b0120200380400600800800 } : Fields).get c.val)
theorem record050_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record050_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record050) (record050.maps 1)
      (record050.inverseMaps 1) record050_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record050_frame001_links_0000 record050_frame001_links_0064)
theorem record050_frame001_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 1 :=
  of_group record050 1 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record050_frame001_indices record050_frame001_graph record050_frame001_links
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (Fin.cases (record050_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record050_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025
