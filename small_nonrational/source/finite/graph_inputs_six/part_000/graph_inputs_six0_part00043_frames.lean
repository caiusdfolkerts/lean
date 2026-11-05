module
prelude
public import GraphInputsSix0Part00043Data
public import RawFrameSupport
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups105Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups107Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups111Checked
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
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x6fedf7bc772eccd97b2b64662cb395724e42c7f8bb0c615c2984f005fdbed7b6e65aab0143e7b4d48d315624c4386b0aa12410808ff9f83e57beec9d2397700dc9b2b5c6b2d51a7b4a68ad059a32d5c4b5964abe576ad94ea975069d938a56498788e49bc36e670c91832ec5acb41632945108a9092043ac728d91a4338650bb1682c05608710c198328570ac11c1f02504808c0580a01201402003 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (embedding (N := 44310) record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (embedding (N := 44310) record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (embedding (N := 44310) record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (embedding record000) hcells Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x119c8b9c5262410a484d422e0f8ec77503a45c90e217093651b16d756ba3579a52d1d687b4059a0c9f61d2c595d0aa64c7257927692e483a39119c8a143f21c909882f40d1d48e787273729b2cd6869f34c9a20cf866b3309974c6e6262d9968cb1456e2b2957ca6052227e13789a64a824d0efc71c36e1b18cc86403031718b085702af13d89a43c01c30dc86042e214d09f04b824c0ff07903941b609c04d81bc0dc06002f812407e025012008c01600a0048014008003 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (embedding record000) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x63cee4370eb4e5a1ec5160dacdd6028033c09cd4e066d9306964ca7a4ff26a928c8e2438e156f3b6ddb2ed0d671332d818ade55fa95544aa114aca53919c8ac44ca23d0608243fc9f9cfa67c53db9e9cf286d82d5162ca424f126e909483439a1bc0d946b62fc1780b1456629f1488a0c4e626010b07783ac1cf0dd86b434c18f0c405d42dc16609e8448218105077836c17009e04801b00c005f02d015c0ac05401a00a004e02200f8078038013009004001a00b005002400e0040018008002000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (embedding record005) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x153aa94530695310d87ac36a18d062825c0b6036e396bcb4d1a14cf167530ad7febd75bf2c8956caa6538a9794249b64a524e920a8f2470a34d1988be45aa2b913a8964479f20f4678036e9b18ce46663191884b1057128e94449ba4cc25d12b494c49324611f48ea46f2360fc07843981b68d106383101728b4457029913d09ac4bc23611388783f81ee0f4075436c1970c405ec2a614409d846421610507803a41c40dd06a82c015e09c04d81bc0dc06002f80cc064024011806c01600a0048014008003 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x11728b1447e21eea0748b9c9cd0e2170937cdbd2cfe64fb0e97e0bab5caad1d65cb16572aa994c2a5750da8213ae98e497248d1c88ce450a1f90e484c417a068fd47d43df1d48e7872735a1a98cc065a3149860b665a82b2957ca6052227e13789a64a824d11d08b844d2248fd07b03bf1cf0df86c635d1990c8060a2e31610ae055827b134897046422010b87f03c01c30dc86bc3021710b384f825c12607f83c81ca0db06502a815209c04d81bc0dc06002f80cc064024011806c01600a0048014008003 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xa96a8fa6fa619088ff8ed8ec8be8b58a589b8037be79277275b75471d70b6fb6d66a967366d64563a61b5ee5b85b258b57f56e56055b54e54453d52d52651f4cd4b84a745044540f40a3e13d638337834233d3143092f92eb2e62d42cd2be2b52af2ad27625f24923421c2051ff1e31d91ca1bc1ae1a81a318b18217d16615d15b14a13c12e1281231091030fd0e40df0db0c90c30c00bf0b80a40a309a09906f06e06005f03303202402301b00b00a009005004003 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record007_frame003_links_0000 record007_frame003_links_0064)
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xa65a61a5fa5ba19a17a15a1398898596e96b94594092e9298758257ea7c47b57b176975b74e7206e26ae69568e63862c5ee5d75d05c05b45ad59759057b5745705094fc4ee4bd4824464294223c33b537a36035934833d33732131b3063002fc2d52c32a528927d26b24d23121f21220b20a1f21d91cb1be1b51a619d18b18217917415c14313511810f1050fc0ed0e40e30d30cd0c80c70c307b07907806f06e05c05b05805705604304104003703602402302001f01e } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0613.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0613.count (({ width := 10, code := 0x96e5a9665895253946509164490a418fa3d8ea398ae22866148420e826047f9fa7b9e176dd7729c76edb56c5ad69da36799a65591639835f9775bd615414a519334bd2146d1744d0d421033fcfb3dcf43c4ee3ace4384de36cd433cc9310c32fcba2d8b32bca828c9c25c9223c8b218821e4741bc6b1905f1785814c4e1344a0ec390e0370d8310c02e0b42c0a026094230881c06c1906017 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (embedding (N := 44310) record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (embedding (N := 44310) record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (embedding (N := 44310) record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group0613
    Papers.RationalityTen.SharedFrameCatalogue.group0613_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0608.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0608.count (({ width := 9, code := 0x377badcee369b3d8ec343a0cf6773599cae531383bede6ed74b85b2d165b056aab51a5d26893f9dce66b3196ca64b218f45a270f84c09f4f5793a5cee06d35daad2673258cc25faf172b75aac15aab54a913e9b4b2552690462250e83401f4f274389bcd8683197cb4582a144a04b23908823e198c86230178a85228138984421100783a170b0542813 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0608.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (embedding (N := 44310) record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (embedding (N := 44310) record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (embedding (N := 44310) record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group0608
    Papers.RationalityTen.SharedFrameCatalogue.group0608_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
def record008_frame004_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2e9973cb965c66ca7644b1ad86a7f93df9d5ce4a6012e59574a3df38e936dd34ad9decd75f9af2173ab4156da98943ea0b4ae25211ce8a944b21910848303fb9f94f6a7a53cb9afcd28669306969ca5c4eb26b90a08283b31ba8d8866030e17e0b0c562281138898c478233112885c4242090fd87b43c41d40e6872c3781ae0d3868433218e0c385e02e216a0b1054c28a13e095849023811408484082000ed073037c1ba0d603d81e40f006f03701700b605802b815808604102000dc06c024011808003e01e } : Fields).get c.val)
theorem record008_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record008_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record008) (record008.maps 4)
      (record008.inverseMaps 4) record008_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record008_frame004_links_0000 record008_frame004_links_0064)
theorem record008_frame004_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 4 :=
  of_group record008 4 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record008_frame004_indices record008_frame004_graph record008_frame004_links
def record008_frame005_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1074.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1074.count (({ width := 10, code := 0xfd3f3fcbf1fafeaf9fe5f7bddf73dbf6bd9f63d7f13b4e979ae5390de774db360d2f3ccbb2ac1f02bb2ddb5ec8afebaab2a6a6291a32749be67966438b21b855fa7d9e1755d170dba6d5a968992631875e1745a9625795a541485053b4dd364b1234791a45509410fa3ccec398dc34cce304ba2ccae2889d2709223c8c2288417c5d1705414c4a12446114440e4370d8320c42408c2007c1e } : Fields).get c.val)
theorem record008_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1074.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (embedding (N := 44310) record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (embedding (N := 44310) record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record008_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (embedding (N := 44310) record008) (record008.maps 5)
      (record008.inverseMaps 5) record008_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record008_frame005_links_0000 record008_frame005_links_0064)
theorem record008_frame005_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 5 :=
  of_group record008 5 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group1074
    Papers.RationalityTen.SharedFrameCatalogue.group1074_facts record008_frame005_indices record008_frame005_graph record008_frame005_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (Fin.cases (record008_frame004_supported hcells) (Fin.cases (record008_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1079.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1079.count (({ width := 11, code := 0xd6bacb57624c3f8630b612c1581301e00beb7cef959fb29636bc534a4d476854ff9f13064fc9191119a2c44b87b0be1141b82703e043f17c8f51e53c576aeadd4377616ba963a98524a053e2574888f111a16426734e31a333c634c41632904ec9892923e460879041fe3ec760e61c434c668c91722b85509c10a19c328550a6104200360640c4140270400780e80f01c02c0480700a01001800 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group1079
    Papers.RationalityTen.SharedFrameCatalogue.group1079_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x47e23c71a98ca451e267102877408a010ff27ea3ee9f48f747b03d3de62f1d78634c99d0c7f60e303580cb635832a99496a3c51aa5ed22c8fd47b2145080830408a000fe07e73981c90e2e6bc32d980cbf25f32cf1558a9250127c93b89d24dc23891a08b845022110e485a42120d0f006de3601878c145ec2f016f89944b624c11e88ac44221210187e83901a40c905dc28c12607c83a40c005f02e016c0b005502a00fc072035014009c0480230100074038013009003c01c00b004001c00a0040018008002000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x51128534049f4cdb66b333698fc7623811a78cec6222e510d87e439e1af0c185436c1acacf163f314987cb4b5802a314329ed4eca62d2c294a4a1a43520a8fe478a3a51c48dc40f9fe4fa477337b99fccb06432f29618aec518283937c99e4bb229110c86242220790087e03e01e88dd862e3071548a604e0260126078c3a81c20d986803261810b8858829013a09984942140f607183740c005f02e016c0b005502a00fc072035014009c0480230100074038013009003c01c00b004001c00a0040018008002000 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record011_frame002_links_0000 record011_frame002_links_0064)
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1079.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1079.count (({ width := 11, code := 0x19d337664cbd93b25644c8189f12621c3d86f0c611c1981b015fcbef632bdd56a67492904f79cf3124f48f91712a10c1281cf6de93cb778ecdd63a7716e01bc360670c5586b095d0b1d5fa97520a093ea7348e9111e23745a8a510a194287d0e61c4346670c71892fe548a714627c4d098929248480879041fe3c86c8c81722cc2e85c0b21602a8520a20fc1c83505009c120230400740e01302403c0700b01001c0280400600800800 } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record011_frame003_links_0000 record011_frame003_links_0064)
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group1079
    Papers.RationalityTen.SharedFrameCatalogue.group1079_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x34259e5ce066432678f79f64f3e7673a19c44dba5dd2d3962ca825032738cd460a2ab13e88f3399998bf65e5ae81682ac7527a8894249b84a4235915e8984069fe0fd07c83da1e98f2a6c234b99b0c1a59328d93b89bc48420a0e886f636416c8b1056829414009c84c2237119089042c20d10407e83d81e30ea87383901bb0cf06603121820be05b42ce15f0a204d425e12708c844c2160fe07403880de06b02f816c0b005502a00dc066027011808003a01c00d8054026012008803c01c00b005002000e0050018008002000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
def record013_frame002_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x285f4189fa4f1a741356812403dfc0fd67e0be49ee8f607a7bcc5e3af0c76abb15d42e91736b03980cb7d5b82d8d606aa352528ed46a9cf4b524311fc8f6428a0f90608113ff1fc0fce7303921c5cd8065f30217e0be659e2a493e49de4e923411688a043921590848343bc1d70e386de35c1a70cb861e30417b0bc05c22b9133896c47a22d110880c3f41ec0d206082ee16b0a8851827412607c03a40de06b02f816c0b005502a00dc066027011808003a01c00d8054026012008803c01c00b005002000e0050018008002000 } : Fields).get c.val)
theorem record013_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record013_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record013) (record013.maps 2)
      (record013.inverseMaps 2) record013_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record013_frame002_links_0000 record013_frame002_links_0064)
theorem record013_frame002_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 2 :=
  of_group record013 2 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record013_frame002_indices record013_frame002_graph record013_frame002_links
def record013_frame003_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xab3aa7a96a85a79a6190d90a8fb8f68f18e68c28bf8ba8ab8a689f87487286e86c86675f75871a7086f96d66a066764964061b5e55ac59158354d54553e53152952251c4cc4b74a647d4454053e43dc3b037833831a30c2d82d02c92bd2b62b02ab27b27225b24723a23221a2041f31dd1d31ca1bc1a019718517b17015f15814a12e12011710c0fb0f00e60d80c40c106f06b05f05b05805505403703302702302001d01c01b01501301201100f00e00b00a008007005003002001000 } : Fields).get c.val)
theorem record013_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record013_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record013) (record013.maps 3)
      (record013.inverseMaps 3) record013_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record013_frame003_links_0000 record013_frame003_links_0064)
theorem record013_frame003_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 3 :=
  of_group record013 3 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record013_frame003_indices record013_frame003_graph record013_frame003_links
def record013_frame004_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x35c6b3d53a834a687b8d702dedbcb716c2d159eb35646c5d89adf5b2b2d62ab925e484668bb15a1ec21808fe1fa3d9774e85cb38e6ccd85ad34d68cd059e2ff5eabb5682b151aa053f25e4728750920b3c276cea9c93826f4dc19932a620be9772e65a0ad95629a520a193b24e48c8d915220414810fc1d23786c8d3194318608bb15c2a8338640b415c2a0510a00d8190270460800e81c0360540981202203c0700b0140200380500600800800 } : Fields).get c.val)
theorem record013_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record013) (record013.maps 4) (record013.inverseMaps 4) record013_frame004_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record013) (record013.maps 4) (record013.inverseMaps 4) record013_frame004_indices (Fin.ofNat record013.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record013_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record013) (record013.maps 4)
      (record013.inverseMaps 4) record013_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record013_frame004_links_0000 record013_frame004_links_0064)
theorem record013_frame004_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 4 :=
  of_group record013 4 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record013_frame004_indices record013_frame004_graph record013_frame004_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (Fin.cases (record013_frame002_supported hcells) (Fin.cases (record013_frame003_supported hcells) (Fin.cases (record013_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x302e02bf17daf6decbd777eed5cfb97722e1db8b6967acc595b15616bfd7bae74c6884f19b3322624959091f63b45c89110e19415808fddf7be17a8f35d6b9b728e09bd372678c85893075feb896eacb588a854a28f5109e53a2544808e11121b4327e8f49de3946f0da9a233c660c91842ea5bcaf9582944f49a93124e46c869041fe3a0700d4196310600ac15028c4d88e11a220438670cc1942b85605e0b81202304406c0600a01201402003 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (embedding (N := 44310) record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (embedding (N := 44310) record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (embedding (N := 44310) record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (embedding record016) hcells Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
def record016_frame002_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xb04afcadaad5ac0aadaa7a76a58a3da2da26a149ef9e399198097195694392891690683d8027c579777876e7176f36e96dd6aa68a68066163361d6065f75e25ce5c058856a55f54653b52b4cd49c4864714664384304114063bf3ac3a539d37e37633e3213112ed2e32e12aa29327c25e24a23d22421b20e2071f11dd1d11c11b71a41951881831781641521471401211151040fb0f20ed0d10c80c20ba0a20a109409306e06c06b05d05c03203102502402301b00c00a009005004003 } : Fields).get c.val)
theorem record016_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record016_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record016) (record016.maps 2)
      (record016.inverseMaps 2) record016_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record016_frame002_links_0000 record016_frame002_links_0064)
theorem record016_frame002_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) : Supported record016 2 :=
  of_group record016 2 (embedding record016) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record016_frame002_indices record016_frame002_graph record016_frame002_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (Fin.cases (record016_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xa5f9f79da9cf9c89b09a398a98697896095995494e92190a8f78e88e48d28bf8ac8a189989488c88587487286e86c8667aa78b75f7586f96ca6a26496405ff5e759158357854553e53852f52952251c4a648042e3e43dc3b334d31a30c3042dd2d82d02c92b62b02ab2472041dd1d31cf19c18516d15f15814f11c10c0ed0e60d80cc0c80c40c109809208d07106f06b06205f05b05905505403703403302702502302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x316607bf97d2f95e9bcb772ecdd7b9b726e35c4b5d69ed0593b21632c357eaf15d2b956dad7596b0d59aa95327fce39852ee41c698a10820dbf27c8ec5d5ba46e4db1b2b596a6d31a33115feb2d572a951c9591fa39464821021fc3ea780ed1d433a5e4b31632c24fc9611d222434858e81b6318600b61602ac540a410c2103f8670cc1882c8570a61442684c06a0cc1902604a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (embedding (N := 44310) record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (embedding (N := 44310) record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (embedding (N := 44310) record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
def record018_frame003_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xad1a70a4ca43a3ea28a1ea0aa009f39e19d99d49ce99598497695b95493d93191c90b9018ff8f38ef8cd8ca8bc8b88a97e87ba77d7737166f36d768c68464662d5d45c25b956c56255854853e5325274cc4a745441340b3ec3a538337836f32b32531730a2ee2e62dd27b23c21f2162111d21b91a018b18117b13a1251050fc0eb0e10d90d20ca09208e08906e06c06805f05c05805605205103603303202702502302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record018_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record018_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record018) (record018.maps 3)
      (record018.inverseMaps 3) record018_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record018_frame003_links_0000 record018_frame003_links_0064)
theorem record018_frame003_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 3 :=
  of_group record018 3 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record018_frame003_indices record018_frame003_graph record018_frame003_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (Fin.cases (record018_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x14fe93523a3f4628a512a1f43684d04a074027fced9d539e724dc9b335268cd099932e64cc790b19621c3e841059ef3d974ae15bb3726ded35a0337652c858c3125ceb555a28d50e9b533a5c4ae8e115a264447ccf59e33b8758e59c435a638c197b2ea5a4b21602724cc96922220420810fe1c6380638b71642b4540a31021982d85a0b015c2885007e0e41a02a05009c120230420740e0130240400780e0160200380400600800800 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (embedding (N := 44310) record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
def record019_frame002_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x44160c3043814c00df9efbc7cf3e11ebcf2a78abbe5de6ebc74b3a05ceee5771eb85dc04df86ec3725b70da765030ad766b9d58a2ba1446a104c724b11d08d2464216506681e3f89f74f8e7b13931bbcd46631310176cb885b12d39594a6852628a928492648423711808a24422018ef471836c1b10c9c62a3031528a5050026e11a888c4201ff0dc86a02a012108704001e80e704a01b00c005f02e016c0aa05401f80e406802a014009c0480230108074038013009004001e00e005802000e0040018008002000 } : Fields).get c.val)
theorem record019_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record019_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record019) (record019.maps 2)
      (record019.inverseMaps 2) record019_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record019_frame002_links_0000 record019_frame002_links_0064)
theorem record019_frame002_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 2 :=
  of_group record019 2 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record019_frame002_indices record019_frame002_graph record019_frame002_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (Fin.cases (record019_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a12cf166432618edc6fe29312b87ec2f613b06f81cb81db9ad9367ab3257fabcf5cfab9d57ea93530a8f501677939d9c24d8e6152c59514a0e4c724c919c889d20ce36662e8167aac451328492b28e7455a2610387fa3f41f14f6c7a63ca99b0c12590279137884a3b31bb8d905d02c615a0a4450427213088dc46422410b08384021f30f6075439c1980c806243061740b6859c27a13508903f81ec0ef07483880ee07103601800be05c02d81540a803f01c80d0050027012008c03a01c00d8054026012008003c01c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record020_frame001_links_0000 (interval_append _ 64 128 133 record020_frame001_links_0064 record020_frame001_links_0128))
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (embedding record020) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x7cef93f13dffbef7bedfda7b1f57ea7d37a0ef7de3b9f5eea5d3ba5744e73cc39772ce4fc0b7cef0dd7b676aecfd8fb075beb5d67abb2d60cc0f742ded96ad55968b4e499f3223ec6a8b71161c429842f99e6ba56eadbd99b0f5febe9602b3552a61482864fc9692aa4746a8b110a1140e7ccf69a0330634c11712cc574919191da34c658c116c2a4368690cc16c2d0580ae1442803d06e0d01402704808c0e81c0360540981202003c0700c0160200380400600800800 } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record020_frame002_links_0000 (interval_append _ 64 128 133 record020_frame002_links_0064 record020_frame002_links_0128))
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (embedding record020) hcells Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
def record020_frame003_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x11a68c8c54e27d10d882c3a61bd0d2858c29e13b081829c10a06cff47e6beb9f3af917a7bca1e28f03778baf1d2ce8173bb95dc7ae1770137e1bb0dc96dc369d940bb35ceac515c2a97511a84131c92c47423490b883340f1fc4fba7c73d89c98dde6a33189880b6256529a14989824a124991b88c04512210ffc7e03d41de8eb071836c1b10c9c62a29414009b84b623511188403721aa0a8048422010007a039c0ee07103601800be05c02d81540a803f01c80d0050027012008c03a01c00d8054026012008003c01c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record020_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record020_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record020) (record020.maps 3)
      (record020.inverseMaps 3) record020_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record020_frame003_links_0000 (interval_append _ 64 128 133 record020_frame003_links_0064 record020_frame003_links_0128))
theorem record020_frame003_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) : Supported record020 3 :=
  of_group record020 3 (embedding record020) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record020_frame003_indices record020_frame003_graph record020_frame003_links
def record020_frame004_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x56dad1566a6d40a7f4f69dd3aa6f4da9ad32a1f42e855039fd3ea7bcf59c93766dcd99ad2da574a894d26648c8890920e4047e8f91e62742183d011fa3e0782ef9c9b746c4d7191b15616bf57a2ed5d0b2157a9a4f69e12da464748d9049fe3ec7a4f19de3b46e0da9a833e668c81883025c8b713225a48c8e90c2104086f8d917c2b85389f130240338630c21582a8520a212c2503d06e0cc1402704808c0e81c0360540981202003c0700c0160200380400600800800 } : Fields).get c.val)
theorem record020_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record020_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record020) (record020.maps 4)
      (record020.inverseMaps 4) record020_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record020_frame004_links_0000 (interval_append _ 64 128 133 record020_frame004_links_0064 record020_frame004_links_0128))
theorem record020_frame004_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) : Supported record020 4 :=
  of_group record020 4 (embedding record020) hcells Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record020_frame004_indices record020_frame004_graph record020_frame004_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (Fin.cases (record020_frame003_supported hcells) (Fin.cases (record020_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x3e9fc6f7deb3cb787ef3c778b711da9b3b64eb2d4da8f50694ca18ff1d635c4586f0a60fbb1756e75aeb57682ced93a2543e6b4bc9431ba35c5b83b022013ff7b4f35e2bb9760eadd335a676c8175ae85a6a553f2784ea96126a474788d518a2c414808f91e13b672cdc9b132a638c498429a5109d92b24a47c828f71de390638bb16c2c0548a20dc1b43485e0ba16c2a8540720dc1982704a08c0e81c0360540981202003c0700c0140200380500600800800 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record021_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record021_frame001_links_0000 (interval_append _ 64 128 130 record021_frame001_links_0064 record021_frame001_links_0128))
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (embedding record021) hcells Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
def record021_frame002_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x34259e2ce1e6432618f7c525d1ae6d703aff579eb9f573aafd526a6151ea02cece7453899b2ccda63b30a92548c644f19a8c1455627d11e6733331740b2a56328894249b847d22bd13088a40e1fe0fd07c73da1e98f2a66c2fb16489dc4de2420f186f63641ab0ba05882b41498a004e426111b88c844821610708043e61ec0ea873838e1c20c4860c2f616d0b3857c288135097849c2160fe07b03c01d00e203881bc0d605f02e816c0aa05401c80dc066027012808c03a01c00d8054026012008003c01c00c005002000e0050018008002000 } : Fields).get c.val)
theorem record021_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record021_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record021_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record021) (record021.maps 2)
      (record021.inverseMaps 2) record021_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record021_frame002_links_0000 (interval_append _ 64 128 130 record021_frame002_links_0064 record021_frame002_links_0128))
theorem record021_frame002_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) : Supported record021 2 :=
  of_group record021 2 (embedding record021) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record021_frame002_indices record021_frame002_graph record021_frame002_links
def record021_frame003_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xb13b0cb04af4ae6ad5ac6a70a69a60a1aa10a099ea9df9db9d89cd98d97b97596d95294693d9398fd8f88f28cd8ca8bc8b88a977d7737166f36d668c6846616025d45c25bc57d56c56254c53e5325274cc49846641340b3eb3a538337837232e31730a2fb2ee2e62dd2af2a729127b27125c24723c21f21620e2071b91ad1a218b18117815213d1311250fc0eb0e30dc0d20ca06e06c06805c05a05805205103803603202702502301d01c01b01501301201000f00e00c00a008007005003002001000 } : Fields).get c.val)
theorem record021_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record021_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record021_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record021) (record021.maps 3)
      (record021.inverseMaps 3) record021_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record021_frame003_links_0000 (interval_append _ 64 128 130 record021_frame003_links_0064 record021_frame003_links_0128))
theorem record021_frame003_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) : Supported record021 3 :=
  of_group record021 3 (embedding record021) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record021_frame003_indices record021_frame003_graph record021_frame003_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (Fin.cases (record021_frame002_supported hcells) (Fin.cases (record021_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1446a15cf627952f9971480a3d313088ec21a0eadb069333b58a4c3a5a5ab055109ed4eaa6c535099a4c626192ee9694b1253d29094149524452108fc47ca3cd1d88e046e9f48cb063f2f41618a9e52b28c137c99e4c322790c48023f01e88de462e2e015e0aa44e026012a07803841920c085882b014909d84d025c12608e845821210307e03dc1e20ea07203701ac0d004a024411a07103701a806c032014009c04a024011807803a01c009804802000f0070024010007 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (embedding record022) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x58eac4557bab3c6162df139893423a0fae0667fb13d742a9a4f526c535099a4c626192d295c4aa253928491c48b240d1f88f3475a3811b271332d18e8bb05b22c615cca5650927293288ce45921590708023f11e58da468631d1820af053427612d87e03d41bc0d6864830415c0aa854029214209d84d025e12108d044421210507e03e01e00ea07103701b20d0057826c12409104682300f006f03701a80d2032018009404601f00f00700360100070028012007 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (embedding record024) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1985cbd65bf1e36e8b65da7ed15659af1d72e80b3bc9cece126c724c919c88a3c51c98da46522f9171771365dab0d0f671ad1157ea74529289929c8e746ca2ad11e8193fd1fa4fa67c53db1e54c2058b2a014789e441a1d98e946ee35b1728b1856a29f1488a084c22010f987b03aa1ad0cc06403141740b384f424211207f03bc1d20b804a024011a06c03501800b805b02b01540a803401900a004802300f0074038013008003c01c00b004802000e0040018008002000 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (embedding record025) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x2cb763cb1257b294b3ff9f24ede6cf3538cdc6162df09784341d59e8c7e547a8652d091b47fa3c11d48dc3b01bd4d8067f2f295c4a56507260119c8a442320790047e23d11bb0c0857829812887e03c61b40d006483041620a404e826612508b84101ec0e904902340de06a03001740b605702b01540a804901c80dc06a032014009404601f00f00740380130080038014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x34259b6cabe4f71ef867c25e0d3023706b3c59babff5bbad94e626ff37492548c644ea4f4dc250d1f48d64181fa4f8e7b73ca946c90840f1e30e885f82b51498a0c4c223711907e83e61e30d306783141820bd85d42ce15f0a9051027a135097848423210c07f03c012408d04081bc0d406002e816c0ae05602a815009203701900a004a02300f807803a01c00d80540260110080038014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (embedding record027) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x34259e5cdb64cf2058f7affd6eeb653e79e54ef27373829bb478a3931b48ca45f22e2ce35fb2d0558ea4f51326e12908e746b22ad08480d3fd1fa4f907b63ca9b08c1a59328d93c89084141d98e886ee30e16c8b1856a294141098446e23210688203f41ec0f187543901ad0cf066032018a0c105f02e81670af854828813d09a84bc24211908983f81d208d03501800b805b02c01580aa05401900a0048023010007803a01c00d80540260110078038016009004001c00a0040018008002000 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x26e33649accd325792ab94dca29facfc37dcbe99f2ed596a834bda30cff67b33b9702b1454c29dd4cca154d424b12168fa47823851a68cc46322f916a8b045522891368924459cb0d9265931c18a0bae574282138c9a64c925d12b494c4a024c123c91448423e91dc8de46916c8b1c53227a135893045a20e10006d832e1880b4852825611d07803a41c40db06a02c813c06f03501a40c005b02d00dc064031014008c044013007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (embedding record029) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
def record029_frame002_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2e7f72fb90dc3ac9763cb11581e3fd1ea8e8c6e2358e3670db6a9ac2d08676b34d688aca523a88d4209bb4a5a33915889a448219d08a833413a040fec7ec3f01f2cf747a23c81840b2c513277937090e4171cd0de06cc35c1998c445fe2f316e0b085702ac14b8a184dc25c0eb07403761ad0d3066031417c0ba854828813d097848422610c077039c1c00d906982c813c06f03501a40c005b02d00dc064031014008c044013007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record029_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record029_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record029) (record029.maps 2)
      (record029.inverseMaps 2) record029_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record029_frame002_links_0000 record029_frame002_links_0064)
theorem record029_frame002_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) : Supported record029 2 :=
  of_group record029 2 (embedding record029) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record029_frame002_indices record029_frame002_graph record029_frame002_links
def record029_frame003_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x7f77f57f37f17c27c07be7bc72a7287267247226c36b969c68966f6686645ff5d55ab5a259e57654651650b5075034e84d14ca4c44b44a549f49848848047146a40a3dd3ae3a63a238535d33232c32a32730e2f62ed2e92de2d22cf2ca2bf2b72ad2a820a2061dd1c11b91a619117f17414212d1251161060f60ee0c70bc0b00a80a009208806906406305a05505403703203102802302201300e00d00b00a009008007005004003002001 } : Fields).get c.val)
theorem record029_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record029) (record029.maps 3) (record029.inverseMaps 3) record029_frame003_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record029) (record029.maps 3) (record029.inverseMaps 3) record029_frame003_indices (Fin.ofNat record029.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record029_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record029) (record029.maps 3)
      (record029.inverseMaps 3) record029_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record029_frame003_links_0000 record029_frame003_links_0064)
theorem record029_frame003_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) : Supported record029 3 :=
  of_group record029 3 (embedding record029) hcells Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record029_frame003_indices record029_frame003_graph record029_frame003_links
def record029_frame004_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x324e45c879070be15c2583abed7aaef5d2b94e69bb3125a49f9312461fc23800fe5f9bdb778e75ca38f716e05bbb746e0d9dafb5d6aed39a533f676b4559a895049f53023a432841062093fa7c8f71ea3c4764ec1d2394714dd9b729c5249d93025648c8e1102163cc748e41b233c630c21642b4548a6146254458670c61882d8570ac0d81883005008c1101301c0340580a0120200380500800c01001 } : Fields).get c.val)
theorem record029_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record029) (record029.maps 4) (record029.inverseMaps 4) record029_frame004_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record029) (record029.maps 4) (record029.inverseMaps 4) record029_frame004_indices (Fin.ofNat record029.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record029_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record029) (record029.maps 4)
      (record029.inverseMaps 4) record029_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record029_frame004_links_0000 record029_frame004_links_0064)
theorem record029_frame004_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) : Supported record029 4 :=
  of_group record029 4 (embedding record029) hcells Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record029_frame004_indices record029_frame004_graph record029_frame004_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (Fin.cases (record029_frame002_supported hcells) (Fin.cases (record029_frame003_supported hcells) (Fin.cases (record029_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xb505a4acb560bafc57be9034669ffcf9277b3979c1c76a3a11b784cc2320f7036811c04201f0067f9b3c5902c5154628713d894b4a2a4c124491b48223c51d48db3b19bdcd8067d32b9794aec502270134497649a23b919c8ae43020790087e23d01bb0c1c52627113109304562080fc07a03821a00c986082c214809d04cc24a11708504101ae08d03501800b605a02c015c0ac05402180fc06a032014008c04402000f8078038013007003401600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x684b3819b6c99e40b1ef706b3c59babff5bbad92d0558ea4f4dc25211ac86442120c101a7e93e41edcf2a60d2c9946c9084141d10cc061c2fc16c8ad452828313088dc46420d0fd078c3901bb0d6869833c1980c506082f81750b3857c2a414409e84d425e12108c844c2180fe04902340de06a030016c0b005702b01540a803701900a004602000f807803a01c00d8054026011007002c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (embedding record031) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
def record031_frame002_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x55d6a75528a6e5306953341973cb4250125f9262df9622a9f50926952668e0469232d17a8af450a2691187293631984ba857128612e49584a524b92248f847623510047d437d1a08c0857029913d09ac4b424c116887041c2000f2075436c1970c405dc2d214a09c84ac23a10104902340de06a030016c0b005702b01540a803701900a004602000f807803a01c00d8054026011007002c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record031_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record031_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record031) (record031.maps 2)
      (record031.inverseMaps 2) record031_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record031_frame002_links_0000 record031_frame002_links_0064)
theorem record031_frame002_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) : Supported record031 2 :=
  of_group record031 2 (embedding record031) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record031_frame002_indices record031_frame002_graph record031_frame002_links
def record031_frame003_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x99098a98898398197f95d95194f94493b93875f7196d56706215d458657656e55e54c53c5345254764273da37132b2e72a329328b27b26925925124221e21a1f81e61cf1b61a819919018718117116816215b14c14413612711e11510f0ff0f60f00e90da09208d06f06a06005b05805705605505403703202802302001f01e01d01c01b01501301100e00b00a009008007005004003002001000 } : Fields).get c.val)
theorem record031_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record031_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record031) (record031.maps 3)
      (record031.inverseMaps 3) record031_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record031_frame003_links_0000 record031_frame003_links_0064)
theorem record031_frame003_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) : Supported record031 3 :=
  of_group record031 3 (embedding record031) hcells Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record031_frame003_indices record031_frame003_graph record031_frame003_links
def record031_frame004_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x87a86e86985784d8487ef7cf7c97ba7b07aa5fc5d25ae5735435194e64cf4c94b249e48647f46b4083db3b138335b33530b2f32ec2dc2ce2bd2b62a927626d24422d2171fc1dd1c11b91af1a619118817f17416415714212d12511e1161060fe0f60ee0e008107f06906405a05505205105004f04e03703202802302001f01e01d01c01b01501301100e00b00a009008007005004003002001000 } : Fields).get c.val)
theorem record031_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record031) (record031.maps 4) (record031.inverseMaps 4) record031_frame004_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record031) (record031.maps 4) (record031.inverseMaps 4) record031_frame004_indices (Fin.ofNat record031.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record031_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record031) (record031.maps 4)
      (record031.inverseMaps 4) record031_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record031_frame004_links_0000 record031_frame004_links_0064)
theorem record031_frame004_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) : Supported record031 4 :=
  of_group record031 4 (embedding record031) hcells Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record031_frame004_indices record031_frame004_graph record031_frame004_links
def record031_frame005_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x14c69752da574a293d14a1341e81cff9fb0a204bea78aea1c4b6e6cad85ab34d680ced97ae8590aad422654948bd1322242c828ff9fa3e074ce61aa32e610b715e29c524a113a2524808c1102023f0790e81c83786c8cd18c3045d8b00fe1ec330610ae1482784e09a130258370640a01182003e0780e81c0360540981101c02c0500901001c0280400600800800 } : Fields).get c.val)
theorem record031_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (embedding (N := 44310) record031) (record031.maps 5) (record031.inverseMaps 5) record031_frame005_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (embedding (N := 44310) record031) (record031.maps 5) (record031.inverseMaps 5) record031_frame005_indices (Fin.ofNat record031.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record031_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (embedding (N := 44310) record031) (record031.maps 5)
      (record031.inverseMaps 5) record031_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record031_frame005_links_0000 record031_frame005_links_0064)
theorem record031_frame005_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) : Supported record031 5 :=
  of_group record031 5 (embedding record031) hcells Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record031_frame005_indices record031_frame005_graph record031_frame005_links
def record031_frame006_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x1ae354ea6d29a3743e40c4d87b06dfebef0f610c047b2ee9d0b806ecdc9b335b69ad219e2d0562a352f23943a7f0f89ec3c2758e49c3370664ca9772d0558a193b2604ac939232384548810b2043f0798e91c83786c8cf194318610bb1081fc338630b615c2a0530a4144280360620a01182003e0780e81c0360540981101c02c0500901001c0280400600800800 } : Fields).get c.val)
theorem record031_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record031) (record031.maps 6) (record031.inverseMaps 6) record031_frame006_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record031) (record031.maps 6) (record031.inverseMaps 6) record031_frame006_indices (Fin.ofNat record031.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record031_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record031) (record031.maps 6)
      (record031.inverseMaps 6) record031_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record031_frame006_links_0000 record031_frame006_links_0064)
theorem record031_frame006_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) : Supported record031 6 :=
  of_group record031 6 (embedding record031) hcells Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record031_frame006_indices record031_frame006_graph record031_frame006_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (Fin.cases (record031_frame002_supported hcells) (Fin.cases (record031_frame003_supported hcells) (Fin.cases (record031_frame004_supported hcells) (Fin.cases (record031_frame005_supported hcells) (Fin.cases (record031_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd09678b36d930c82e3df149703b735b26cf5664af0d726b65549a98547a851416a02c92a4632278f147263691948be45c59c6ac651326e123c8fa473a2ad11481c3fd1fa4f8e7b63ca96489e44841f50f187663771ab0ba058c2b51498a084c223711908384021f30f6075438e1b40c8062830617b0ba059c2be1520a204f426a12f09083f81ec0f007482340e206a03001740b805b02b01540a803901900a004a024011807803a01c00d80540260100078038018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (embedding record033) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x2575299931c94228913086542d9facfc37dcbe99f2ee906e83565aa0d2e688b4119f8cf66772da5626a9c53ba9993fa9a7498242d1f48f147423691988c345aa2c11528a344da24911672c3409930c706282eb94b09ee4e326993249744ad253128093048f24511ec8ee46f2348b6458e2be135895845a20b100076c3101730a504a023a0f907883a41c40db06a01c40de06a03481880c005b02d00dc06803201880a004a023011004c01c00d0050024010007002000c004001 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record034_frame001_links_0000 record034_frame001_links_0064)
theorem record034_frame001_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 1 :=
  of_group record034 1 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record034_frame001_indices record034_frame001_graph record034_frame001_links
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (Fin.cases (record034_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x2de96e4b1d588ab53596abdd59e72b3819b2cd463f31e08c2c5be0c104e81fc08e020e06627b0f17429ea4eba6c53509864b4a5712a894e4a3247122c90348023cd1d68e046ca0c4caa6412f09748ae652b28213d09c04d123391508464011f88dc86c630415e0a5450a27113107e03ca1b40c906082aa1500a48508276134095849823a118088842420a0fc07a83c01d40e206e03581a009204682300de06a03480dc06403101800a8050025011808803e01e00e8070036015009804001c00d0050024010007 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (embedding record036) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x684b2ad93cc98619f093832c12d7deb775b9a00cede73137f9ba495a47b21e8ff47aa3591a98c8c5b99cac09511a84134a94547d235515c8304101fdcf8e7b73c91b549de4dc238904478c3a11bd0bf05d82c31498a0c4bc23711908383e61e40ef07583a01a60cf06282f61750ac854829614409e84d024c11a08603f41ee0f006d02340de06a03481a00ba05b02b81580a803701900c4060025011807c03c01c00d80540260100070034014009004001c00c005002000c002000 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (embedding record037) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x1f4fdf7b8f2de33c3f79d9bb235dea3d41a531ce34c5d762eadce9792862dc1d7fef81ed3c6772ec9d333b640b4d4aa754b89612423c46e8b1052023b66e4c49842ea59ca71442764d49291f2264147e8f71de374640bb16c2c0438850dc1b43405f0ba16c2b8560aa1501c8370640a01282303e0780e81c0360540981001c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (embedding record038) hcells Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
def record038_frame002_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x684b3879b6c9864171ef8a4af0d726b65549a98547a73137f9ba492a4632275952b193708fa44520c10387e93e39edcf2a5f62c9121078c35617e0ba056a293141898446e23210707cc38e1c20da06983141830bd85d42ce15f0a9051027a13509784842180fe07b03c012408d03881bc0d406002e816c0ae05602a815007203701900a004a02300f807803a01c00d80540260100070030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record038_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record038) (record038.maps 2) (record038.inverseMaps 2) record038_frame002_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record038) (record038.maps 2) (record038.inverseMaps 2) record038_frame002_indices (Fin.ofNat record038.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record038_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record038) (record038.maps 2)
      (record038.inverseMaps 2) record038_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record038_frame002_links_0000 record038_frame002_links_0064)
theorem record038_frame002_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) : Supported record038 2 :=
  of_group record038 2 (embedding record038) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record038_frame002_indices record038_frame002_graph record038_frame002_links
def record038_frame003_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xb13b04afcae6adaad5ac6a0ea089f69db9d89cd97496b9638fd8f88f26f36d66616025bc58557d56354c5405274984663eb3a537233b32e30b2fb2f12dd2af2a727124720e2071f11dd1ba1ad1a219818117816415214713d13111a0fd0eb0e30dc08c08706e06c06705d05a05805405305205103803603102802502301f01e01d01c01b01501301000e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record038_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record038) (record038.maps 3) (record038.inverseMaps 3) record038_frame003_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record038) (record038.maps 3) (record038.inverseMaps 3) record038_frame003_indices (Fin.ofNat record038.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record038_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record038) (record038.maps 3)
      (record038.inverseMaps 3) record038_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record038_frame003_links_0000 record038_frame003_links_0064)
theorem record038_frame003_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) : Supported record038 3 :=
  of_group record038 3 (embedding record038) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record038_frame003_indices record038_frame003_graph record038_frame003_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (Fin.cases (record038_frame002_supported hcells) (Fin.cases (record038_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x684b3af9cccdb647f21d8f7c50611705d81aafbd70eb653f89edcf024a1237914c7463711ac8d2c6362f2ce2596a93944a9b8456226910a86442120c10427f93e41edcf285f928d13c49083781b30d4466030e17e0bb458a294141898046e2320f207583a01c20dd86d035a1a60ce863c30617c0ba85982be1520a204f426a12f090844c2180f606d82340ee06a030016c0b405802b81580a803f01900a0046022010007c03c01c00d805402600e006803001600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (embedding record040) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x4d2a66930e97c4a064d72409153905974cb1652325991ac8163d2f99688adc5672b01572ab3555aa9153a9b14a9a4ed23690a47f228111086842ba13508a83d41b20bcf226e733e99bccc265a32a1930c8a63f2c014d4a4250a27e13cc95049423e91bc8ce46122d91588a234f1980c7c5fc2ee16e8ab851e27e12e893447822a111887042a1a20b5055c2760fe069027812805c02d81680ae05602a809004602200f807803a010007803801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (embedding record042) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
def record042_frame002_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x5c7ae176e3b63588ac0f5e3ae5c011b52d8a6adb4ada18ce4666b031688acf55029dd4c4a5651da89d42694e473a33915a89a447a0c10327fb3f49f74f947b53d29e4cdb06102cd95b0a8652e291141c9e64df20d0ecc7343791b30d6c5f82e51638ad455229614089c44be2010f987b03bc1d70e806ec35a1a60cc064431417a0b985b02ca13d09404842240ef06a827812805c02d81680ae05602a809004602200f807803a010007803801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record042_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record042) (record042.maps 2) (record042.inverseMaps 2) record042_frame002_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record042) (record042.maps 2) (record042.inverseMaps 2) record042_frame002_indices (Fin.ofNat record042.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record042_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record042) (record042.maps 2)
      (record042.inverseMaps 2) record042_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record042_frame002_links_0000 record042_frame002_links_0064)
theorem record042_frame002_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) : Supported record042 2 :=
  of_group record042 2 (embedding record042) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record042_frame002_indices record042_frame002_graph record042_frame002_links
def record042_frame003_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x1e63cbf94f25e27c3781efdc1756ea7d3da4f46681cf7902fb5c7b756bed55a5b39656c7d2a9f13a66d4d199525a434768d918e2dc548a112a083c6730e2dc037b6ecdb5b33605f6b1d5baa753aa5531a5448a8f11a22c44a8850d9ce3806e0d49a2336610bb16e2be560a89462844f89d11820e408788ca15c25c4805a0b21602a8540a60901182203e0780e81001e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record042_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (embedding (N := 44310) record042) (record042.maps 3) (record042.inverseMaps 3) record042_frame003_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (embedding (N := 44310) record042) (record042.maps 3) (record042.inverseMaps 3) record042_frame003_indices (Fin.ofNat record042.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record042_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (embedding (N := 44310) record042) (record042.maps 3)
      (record042.inverseMaps 3) record042_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record042_frame003_links_0000 record042_frame003_links_0064)
theorem record042_frame003_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) : Supported record042 3 :=
  of_group record042 3 (embedding record042) hcells Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record042_frame003_indices record042_frame003_graph record042_frame003_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (Fin.cases (record042_frame002_supported hcells) (Fin.cases (record042_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
def record043_frame001_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x16a0b49582ebf15f2a3dd18287d4239cbce0e6cf3538d046562ff0db865c2ca13908f83f3595920c82629b0fd600a2b50ea7b93b49614a6251526092248da43520c8ff47423851b47733739b0cd3267c32c9910bca57628c14089c24d125d92688ee467229110c86442320a0fbc7be3cf1bb0c1c552293139098849822b10407e03c61d40e186d034a1800b8058029013a099849423c11708503440b805b02d01600ae05602a810c07e039012008c04402000f807803a00f007003401600a004802000a0040018008002000 } : Fields).get c.val)
theorem record043_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record043_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record043) (record043.maps 1)
      (record043.inverseMaps 1) record043_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record043_frame001_links_0000 record043_frame001_links_0064)
theorem record043_frame001_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) : Supported record043 1 :=
  of_group record043 1 (embedding record043) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record043_frame001_indices record043_frame001_graph record043_frame001_links
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (Fin.cases (record043_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x67973819b6c99e40b1ef829b8e5c26d6f6adb3fd882c0b5bbad955e2aab53ca88ceae72537a9574a3e4ef25791f48b1a56ce4666ad054c4a27509a6e12908e7468a2b513486442120c101a7fb3f49ed4f4a79330694b89e64df242105076639d1bc8d9866030e17e0b6458e2b514089c44be23710688203f41ec0eb87403901bb0d6869833c1980c886282e616c0b2857c2a414409e84d425e12809084642260d503d81700b605a02c015c0ac0550218090046022010007c03c01d00d805402200f007003401600a004802000a0040018008002000 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record044_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record044_frame001_links_0000 (interval_append _ 64 128 131 record044_frame001_links_0064 record044_frame001_links_0128))
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (embedding record044) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
def record044_frame002_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x46522e51628a0c47e21f096833416e0450177fbbf05f6cf7d7b93d49e3af0b76b3a11cf2e6e702b7e9bdedd06df36c17dcbb45cf2b954c0a24508a75d2fc92c48b23a91a889e43da1c509283440f9f70f8c7af3799984c646212f616a0aca55529b14a09f24db26912c494449422f91408803ff1d58e6c6f63621948c5c60a2e31610ae054e29414089bc46822210707f03c01c30dc86a83301860bb05942a20c903d81700b605a02c015c0ac0550218090046022010007c03c01d00d805402200f007003401600a004802000a0040018008002000 } : Fields).get c.val)
theorem record044_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record044_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record044_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record044) (record044.maps 2)
      (record044.inverseMaps 2) record044_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record044_frame002_links_0000 (interval_append _ 64 128 131 record044_frame002_links_0064 record044_frame002_links_0128))
theorem record044_frame002_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) : Supported record044 2 :=
  of_group record044 2 (embedding record044) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record044_frame002_indices record044_frame002_graph record044_frame002_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (Fin.cases (record044_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
def record045_frame001_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x11898b9c4da24109582d4106049019803bed5f38f7f7ba3d89e3cefd76bafb9768b9e57429fd4d0a6051d289142292c475235119087142ca0d103e7f63ee1f18f5e75d3779a20cd666132218c8c425a72b2955ca6c52828a94209d44d225112508e645f228110080638c1b60d8867a32918b8c0c5c62c215c0a94528281137891c46822210707fc3721a80c305d82a010e080032412805c02d81680ae05602a80fc07202a012008c04402100f807803a010007803801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record045_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record045_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record045) (record045.maps 1)
      (record045.inverseMaps 1) record045_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record045_frame001_links_0000 record045_frame001_links_0064)
theorem record045_frame001_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) : Supported record045 1 :=
  of_group record045 1 (embedding record045) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record045_frame001_indices record045_frame001_graph record045_frame001_links
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (Fin.cases (record045_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
def record046_frame001_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19e2c98623f0f1867c12dbf2dbf6c2b5bd9d2bef5dfae3d6eeadd559aa05449a5cce766830254bea2450826d12428fd475231116089d4182078ff67e93e49eccf4679136a94ac9e04dc2400fb47923b61c80df06d22fc1750b1c56a29513f89bc4ba23710708043e61ec0f207783ae1d00d3067832218a0bd85642a414b0a204f425e128090844421410307e03dc1e00d403581a80d2068031015c0ac05501980c8062030015007c03c01d00d805402000f0070034014009004001c00c005002000c004000 } : Fields).get c.val)
theorem record046_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record046_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record046) (record046.maps 1)
      (record046.inverseMaps 1) record046_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record046_frame001_links_0000 record046_frame001_links_0064)
theorem record046_frame001_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 1 :=
  of_group record046 1 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record046_frame001_indices record046_frame001_graph record046_frame001_links
def record046_frame002_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x119189f43721a10be848c12a07d0308113f99f4af997c5bdf5e82f217873b697debb75d0ad454bea21507274d2b8939496a4111da8d7438a17906881f3fa9f68f887ad3ae9980c5e61e2f41634ae25662a414e4a564d2261928892847222e913887c3ff1d60e306d83621a88cf465231715c0a9c50226f12407b83c01d10e186e43301860bb053c28013008f84442020c803581a80d2068031015c0ac05501980c8062030015007c03c01d00d805402000f0070034014009004001c00c005002000c004000 } : Fields).get c.val)
theorem record046_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record046) (record046.maps 2) (record046.inverseMaps 2) record046_frame002_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record046) (record046.maps 2) (record046.inverseMaps 2) record046_frame002_indices (Fin.ofNat record046.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record046_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record046) (record046.maps 2)
      (record046.inverseMaps 2) record046_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record046_frame002_links_0000 record046_frame002_links_0064)
theorem record046_frame002_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 2 :=
  of_group record046 2 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record046_frame002_indices record046_frame002_graph record046_frame002_links
def record046_frame003_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x8cd8bc8a98a389d89287686e86b86885684484183983682481d8178066d06ac6a066a5cd5ac59f57b54052d5265135084fb4c94bf4a749a48647746b46043039336f3653413042f52ec2d92cb2c228f28526a25f24c23a2302262071e01d01bf1b91b51af1a81a017016b15f15714912812211c1161101081010f90ec0e60df0d80d50d00b306906806706606005505405303303203103002a01f01e01d01b01501000f00e00d00a009008007006005004003002000 } : Fields).get c.val)
theorem record046_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record046) (record046.maps 3) (record046.inverseMaps 3) record046_frame003_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record046) (record046.maps 3) (record046.inverseMaps 3) record046_frame003_indices (Fin.ofNat record046.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record046_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record046) (record046.maps 3)
      (record046.inverseMaps 3) record046_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record046_frame003_links_0000 record046_frame003_links_0064)
theorem record046_frame003_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 3 :=
  of_group record046 3 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record046_frame003_indices record046_frame003_graph record046_frame003_links
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (Fin.cases (record046_frame001_supported hcells) (Fin.cases (record046_frame002_supported hcells) (Fin.cases (record046_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
def record047_frame001_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x54f2a554c3a55d2568ff421a06cd7a68d319981caa250f2619273565a14d0467ab3b9702ab053c299942a94448623e91e08e1469a33118c8be45ba2c1144899449222ce4a67232f18e4c505d028e94249c84d326313049744b3256929893a498248922890647d23a91bc8d240518c8b6858e2b614c89e84d625812608f045a20e0e986d832e1880ba85a42b214a09583e01e00e9071036c1a806b03501a40b805b02d00fc07203301900c406002a012008c04400f007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record047_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record047_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record047) (record047.maps 1)
      (record047.inverseMaps 1) record047_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record047_frame001_links_0000 record047_frame001_links_0064)
theorem record047_frame001_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) : Supported record047 1 :=
  of_group record047 1 (embedding record047) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record047_frame001_indices record047_frame001_graph record047_frame001_links
def record047_frame002_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x45ce2c9120888c4121e909084041aa0b502480cbf15f6af7f7ba32057e0be95dd2e915d0a5f510a8393b492c47523511948a143f21c90d484c41ba088fee7d93e19eb0dde66032918bcc3c5e82b2955ca6c52828a142c9f84ed26f134c97e4b4252925c90e47422e113487a4031b10ca462e3031718b085702a514a0a044de2490fd07803861b90d4066030c1760a8844c1fe0f2072835818e06b03501a40b805b02d00fc07203301900c406002a012008c04400f007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record047_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record047_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record047) (record047.maps 2)
      (record047.inverseMaps 2) record047_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record047_frame002_links_0000 record047_frame002_links_0064)
theorem record047_frame002_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) : Supported record047 2 :=
  of_group record047 2 (embedding record047) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record047_frame002_indices record047_frame002_graph record047_frame002_links
def record047_frame003_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xa97a90a70a62a59a51a24a1b9ec9e89d39ca9a899898197a7af77276e7607596d967164b63f61e5b659058557d56e56055b55654e54754053252852151b47940f4023e63db3ac34233531930e3053002f92f22eb2e62de2d92d22cb2c52be2b52af2aa27f2041de1d41c81bc1ae1a819e19718f18617014813c12e12811e11710d1070f00cf0c90c30c00bd0b706b06a06905c05b05a03f03903303203103002a02402302200f00e00d00b00a009008007005004003002001 } : Fields).get c.val)
theorem record047_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record047) (record047.maps 3) (record047.inverseMaps 3) record047_frame003_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record047) (record047.maps 3) (record047.inverseMaps 3) record047_frame003_indices (Fin.ofNat record047.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record047_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record047) (record047.maps 3)
      (record047.inverseMaps 3) record047_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record047_frame003_links_0000 record047_frame003_links_0064)
theorem record047_frame003_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) : Supported record047 3 :=
  of_group record047 3 (embedding record047) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record047_frame003_indices record047_frame003_graph record047_frame003_links
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (Fin.cases (record047_frame001_supported hcells) (Fin.cases (record047_frame002_supported hcells) (Fin.cases (record047_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
def record049_frame001_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x233d1738a5c48218f0a584d4195fd6fc07a33addcb6e386ee362daead746af3499a2ad07680b33d93ec3a59d2c8562cac4555aa9931c92e485239119c872417a068e8e7313939b68d806b434f9a64d1067c3359984c9863731316ccb445972bd9594a96530291142c9da4d325412687ca3c91df8e386dc3631a38cc86403031718b0857028d13d89a43fe1b90ce06042e215209f04b824c11307903941b609c04d81c00de06e030017c09203f013009004600b0050024008003 } : Fields).get c.val)
theorem record049_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record049_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record049) (record049.maps 1)
      (record049.inverseMaps 1) record049_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record049_frame001_links_0000 record049_frame001_links_0064)
theorem record049_frame001_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) : Supported record049 1 :=
  of_group record049 1 (embedding record049) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record049_frame001_indices record049_frame001_graph record049_frame001_links
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (Fin.cases (record049_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
def record051_frame001_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xaac54e69cd4c1a55d12a65b2f1932488e3971bd87d43160fb06d71132098f0b8e5762b5558eab95532a7d3b69ac498a4852068f943f21b90a084c41f20d906278e3989b90d0e6753341968ca664331e9674af651728393b891447a23311708ac4511e18e6070236b1af8cfc63e2ff1750b645942be14f09f84bc24911c08c444621c10b081436e1780b5854c28e13c09804542140ff07983601a409b048816c0ac04102000dc06c029013808c04401e00e806c02200f0070030014009002800c002000 } : Fields).get c.val)
theorem record051_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record051_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record051) (record051.maps 1)
      (record051.inverseMaps 1) record051_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record051_frame001_links_0000 record051_frame001_links_0064)
theorem record051_frame001_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) : Supported record051 1 :=
  of_group record051 1 (embedding record051) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record051_frame001_indices record051_frame001_graph record051_frame001_links
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (Fin.cases (record051_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
def record052_frame001_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x8cf8b88a188e86b84683f82381d8168118027ee7e87e47de7da7d674c74a73a73873666065c5ac5a75785625595515125075014f94ba4b34a749f49449048a4473f83a839c39836434e3443373313032fb2f72e82d82b42ae2a529729428f25523f23722d1ee1df1d619718f18117517116014f13d13711e1141090fe0f70e70df0d40cd0c40b508a07506c06705a05405204003603503103002602402101e01c01401301200f00d009008007005004003001000 } : Fields).get c.val)
theorem record052_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record052_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record052) (record052.maps 1)
      (record052.inverseMaps 1) record052_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record052_frame001_links_0000 record052_frame001_links_0064)
theorem record052_frame001_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) : Supported record052 1 :=
  of_group record052 1 (embedding record052) hcells Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record052_frame001_indices record052_frame001_graph record052_frame001_links
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (Fin.cases (record052_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record052_frames_supported
theorem record053_frame000_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) :
    Supported record053 0 :=
  of_identity record053 0 (by decide +kernel)
def record053_frame001_indices (c : Fin record053.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd07e79736d933c82e3df14d702b5cda76d11664aa454bea3b429a0bd01a5d32ce961c92e4652288f147263691948be45c59c6b40544a899322948473a2ad11480c3fd1fa4fac7b63ca9830aaa4f222e90507663771ab0b6058c2b51510a084c223811588344101fa0f6075438e1b40cf865c32018a0ba059c2be1520a204f424211908983f81ec0f007482340da06a03081800b805b02b01540a803501900a4050024011807803a01c00d80500260110078038018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record053_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record053.data.requiredEdges q = true := by decide +kernel
theorem record053_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record053) (record053.maps 1) (record053.inverseMaps 1) record053_frame001_indices (Fin.ofNat record053.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record053_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record053) (record053.maps 1) (record053.inverseMaps 1) record053_frame001_indices (Fin.ofNat record053.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record053_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record053) (record053.maps 1)
      (record053.inverseMaps 1) record053_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record053_frame001_links_0000 record053_frame001_links_0064)
theorem record053_frame001_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) : Supported record053 1 :=
  of_group record053 1 (embedding record053) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record053_frame001_indices record053_frame001_graph record053_frame001_links
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (Fin.cases (record053_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record053_frames_supported
theorem record054_frame000_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) :
    Supported record054 0 :=
  of_identity record054 0 (by decide +kernel)
def record054_frame001_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x67973879b6c99e4171ef41da05cffe7c53c59dd4ca6621304974cb3a586d2b6723335810b4055a2a314c4a50513a84d2908e746022b513488a4182030ff67e93ed9ed4f4a79336a1830b0055829714709e64df20a0ecc7183791b30d585f82d81638ad454e281138897c47020d10407e83d81e50ee875c3a01c70e106d034c19f0cb86443141810b985b02ca15f0a9051027a12809084642260f607803540c205c02d81680ae05602a80a4048023011007c03c01d00d805002200f007003401800a004802000a0040018008002000 } : Fields).get c.val)
theorem record054_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record054) (record054.maps 1) (record054.inverseMaps 1) record054_frame001_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record054) (record054.maps 1) (record054.inverseMaps 1) record054_frame001_indices (Fin.ofNat record054.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record054_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record054) (record054.maps 1)
      (record054.inverseMaps 1) record054_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record054_frame001_links_0000 record054_frame001_links_0064)
theorem record054_frame001_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) : Supported record054 1 :=
  of_group record054 1 (embedding record054) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record054_frame001_indices record054_frame001_graph record054_frame001_links
def record054_frame002_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x5562a73520a73530695710b878c3761ad0bc854417608d02d811402dfe4c96640b1e97c4b4056aab1d572ab25522a75358953496246d2148f945021e50d085742620f506c82f3c71b90cea66832d194cc8a63f2bd94d4a2e50a27e13b895048a23e91bc8cc45b22b11447d836b1af8cfc63e30e17e8bb85ba2ca15f0a784fc26d12e0934478231111887042a2050f006dc34416a0ab851c27810a07f83480c205c02d81680ae05602a80a4048023011007c03c01d00d805002200f007003401800a004802000a0040018008002000 } : Fields).get c.val)
theorem record054_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record054) (record054.maps 2) (record054.inverseMaps 2) record054_frame002_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record054) (record054.maps 2) (record054.inverseMaps 2) record054_frame002_indices (Fin.ofNat record054.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record054_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record054) (record054.maps 2)
      (record054.inverseMaps 2) record054_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record054_frame002_links_0000 record054_frame002_links_0064)
theorem record054_frame002_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) : Supported record054 2 :=
  of_group record054 2 (embedding record054) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record054_frame002_indices record054_frame002_graph record054_frame002_links
def record054_frame003_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x1f5be97cbf85ef7dc75eebbd6fad758eadd2ba4744e85cfb9d693d039ef1edf3b816d2d55a3b2b63e934f89c536a68cc692d1fe3b46c8c51522844a81af0dc8b856f6dd1b33605eeb1d582a753aa4531a4d48a8f119a2544286cfe9da3aa718dc1b0350688cd9903165f0b71662bc560a894a2844f89d1342564788c1072043e4790d21962b82f85a0b21602a8540a60a41202304407c0f01d0360500880f01c0340600a0120200280400600800800 } : Fields).get c.val)
theorem record054_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (embedding (N := 44310) record054) (record054.maps 3) (record054.inverseMaps 3) record054_frame003_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (embedding (N := 44310) record054) (record054.maps 3) (record054.inverseMaps 3) record054_frame003_indices (Fin.ofNat record054.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record054_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (embedding (N := 44310) record054) (record054.maps 3)
      (record054.inverseMaps 3) record054_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record054_frame003_links_0000 record054_frame003_links_0064)
theorem record054_frame003_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) : Supported record054 3 :=
  of_group record054 3 (embedding record054) hcells Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record054_frame003_indices record054_frame003_graph record054_frame003_links
def record054_frame004_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x46522eb1628a0c48a21eec9760bae1d5aea17493929c84e397173889c26bee5da2e796a0ae4545a9d14c0a5051228452fc92c48023a91a88c4438a12106881f4059f70f8c7af3ae1bc8d3267c3309958c646212d41594a88536294146c9a44b0251125090c45f22811008003ab1cd8dec6c435219e0ca462e30417a0b4c5702a81498a044de25911a088841c1fc0f0070c3721860bb05942a211008083240c205c02d81680ae05602a80a4048023011007c03c01d00d805002200f007003401800a004802000a0040018008002000 } : Fields).get c.val)
theorem record054_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record054) (record054.maps 4) (record054.inverseMaps 4) record054_frame004_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record054) (record054.maps 4) (record054.inverseMaps 4) record054_frame004_indices (Fin.ofNat record054.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record054_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record054) (record054.maps 4)
      (record054.inverseMaps 4) record054_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record054_frame004_links_0000 record054_frame004_links_0064)
theorem record054_frame004_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) : Supported record054 4 :=
  of_group record054 4 (embedding record054) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record054_frame004_indices record054_frame004_graph record054_frame004_links
def record054_frame005_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x8ce8c78c48bd8b68b37fa7f87f47ef7eb7e57ce7cb7c77c37be7b86cf6aa69e6696265eb5db5ce5c65af5a254f52550f5054f84f04c94b14a749a49147946d46242f3ec3b03a239438c3723683152eb2d52c82bf2b628f27726a25f25723c2322282081df1d91c81b91b61ae1a81a019619017f17016c16515f15714d14013713012c1221161101010f90f20ee0d40d00b405f05a05905805505405302902402302201f01e01d01b01401100f00e00d00c00a009008005004003002001000 } : Fields).get c.val)
theorem record054_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record054) (record054.maps 5) (record054.inverseMaps 5) record054_frame005_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record054) (record054.maps 5) (record054.inverseMaps 5) record054_frame005_indices (Fin.ofNat record054.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record054_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record054) (record054.maps 5)
      (record054.inverseMaps 5) record054_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record054_frame005_links_0000 record054_frame005_links_0064)
theorem record054_frame005_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) : Supported record054 5 :=
  of_group record054 5 (embedding record054) hcells Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record054_frame005_indices record054_frame005_graph record054_frame005_links
def record054_frame006_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x8c68bb8b78a989888d7b27a77a17a079d79778478177b77376876267265f65b62d5f75ce5c65c05ba5ad5a85505295105095004f84d14b84b24a94a249348f48b4473f83c03b73af3a939d39933b3183012fd2f62ec2c92b22ad2a72a129629329026922a2252152091fe1ee1e81e01d31cc1c01b21a719719018a18217417016c16114f13d13711610b0ff0f70d50cd0ae05f05a05905805505405302902402302201f01e01d01b01401100f00e00d00c00a009008005004003002001000 } : Fields).get c.val)
theorem record054_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record054) (record054.maps 6) (record054.inverseMaps 6) record054_frame006_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record054) (record054.maps 6) (record054.inverseMaps 6) record054_frame006_indices (Fin.ofNat record054.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record054_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record054) (record054.maps 6)
      (record054.inverseMaps 6) record054_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record054_frame006_links_0000 record054_frame006_links_0064)
theorem record054_frame006_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) : Supported record054 6 :=
  of_group record054 6 (embedding record054) hcells Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record054_frame006_indices record054_frame006_graph record054_frame006_links
theorem record054_frames_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) :
    ∀ f : Fin record054.g, Supported record054 f :=
  (Fin.cases (record054_frame000_supported hcells) (Fin.cases (record054_frame001_supported hcells) (Fin.cases (record054_frame002_supported hcells) (Fin.cases (record054_frame003_supported hcells) (Fin.cases (record054_frame004_supported hcells) (Fin.cases (record054_frame005_supported hcells) (Fin.cases (record054_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record054_frames_supported
theorem record055_frame000_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) :
    Supported record055 0 :=
  of_identity record055 0 (by decide +kernel)
def record055_frame001_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xab2aaba83a7ca4ba469f69de9c59b69b09a298e97596f96095895394d92190a8f78e88e48d28bf8ac8a189989488c88587487286e86c86675f7586f969c6946496405e15c959158357855454553e52f52952251c4a643f42e3e43dc37234d31a30c3042d82d02c92c22b62b02ab2472412041dd1d31cf18517716d15f15814f10c0f70ed0e60d80cc0c80c40c10a909f09808e08d06f06d06b05f05e05b05905505403703403302702502302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record055_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record055_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record055) (record055.maps 1)
      (record055.inverseMaps 1) record055_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record055_frame001_links_0000 record055_frame001_links_0064)
theorem record055_frame001_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) : Supported record055 1 :=
  of_group record055 1 (embedding record055) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record055_frame001_indices record055_frame001_graph record055_frame001_links
def record055_frame002_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x95094f94994793e93c9199078ee8e28db8d18bd89c89588888087a87785a84483582381c8117fa7e47d67c97c57bb7b879b7957867807736476365ed59e59955554e4f14de4ac49c49345943942f41440d4063fb3b436535931c3152b829c27326325a2112001f61e51d41cd1c219118c17115f15b15812812211c11211010d0e40d70d10ce0c50bd0b70b40b109a09008a08208106806606405805705405204e04d03703403302702502302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record055_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record055) (record055.maps 2) (record055.inverseMaps 2) record055_frame002_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record055) (record055.maps 2) (record055.inverseMaps 2) record055_frame002_indices (Fin.ofNat record055.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record055_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record055) (record055.maps 2)
      (record055.inverseMaps 2) record055_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record055_frame002_links_0000 record055_frame002_links_0064)
theorem record055_frame002_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) : Supported record055 2 :=
  of_group record055 2 (embedding record055) hcells Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record055_frame002_indices record055_frame002_graph record055_frame002_links
def record055_frame003_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0x91d236414818f11da2e45589b132244468870f21cc348630be16c1f83905e0840d813009febfa7ecfd1f8bef7d8fa9f23e27b8df1bc35e678ce98d3175dcb8963ac0572a854a28e50aa093ea7a4c08dd1620d4167a0ed9c73846ecce99532262cc197f2f8530a513124447c8f0f41dc3a4710e01ba2dc560a814a27c4c89512623c4207e0f41d83a8600be1742905109c130240470660c01782704a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record055_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record055) (record055.maps 3) (record055.inverseMaps 3) record055_frame003_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record055) (record055.maps 3) (record055.inverseMaps 3) record055_frame003_indices (Fin.ofNat record055.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record055_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record055) (record055.maps 3)
      (record055.inverseMaps 3) record055_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record055_frame003_links_0000 record055_frame003_links_0064)
theorem record055_frame003_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) : Supported record055 3 :=
  of_group record055 3 (embedding record055) hcells Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record055_frame003_indices record055_frame003_graph record055_frame003_links
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (Fin.cases (record055_frame001_supported hcells) (Fin.cases (record055_frame002_supported hcells) (Fin.cases (record055_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record055_frames_supported
theorem record056_frame000_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    Supported record056 0 :=
  of_identity record056 0 (by decide +kernel)
def record056_frame001_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x1efbdefb5f69e9bd1f7bedbd83abf50e5bc8f90f1be25c3f756d8da5b3b6169fd35a4f46e87d039df3966dca792f21d90aad3a657c778e51021b3fe7daf91ef3d97a6c6d6c2ce590a5543a724b291d15a2343684cee9d3392668c61702ae5309c928240460890f81b6354658c61802ec5b0971001fc338650b41642b05009e1382383f06c0d41a02804e0981202103c0740e0130240400780b0120200380400600800800 } : Fields).get c.val)
theorem record056_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record056_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record056) (record056.maps 1)
      (record056.inverseMaps 1) record056_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record056_frame001_links_0000 record056_frame001_links_0064)
theorem record056_frame001_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) : Supported record056 1 :=
  of_group record056 1 (embedding record056) hcells Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record056_frame001_indices record056_frame001_graph record056_frame001_links
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (Fin.cases (record056_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
def record057_frame001_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19f8cf6e6db20b8f7c33616ae056b9b4eda22cc9599abf55a2a9152fa8ed0a282d40594e49f64e324a918c89e3c91cb8db454227312e6d2338d582a264aca50d23c8ab4451fe8fac7c73db1e9cf2a58d279109481e3ea1bb8d5858c2a21498a084e626110b08204021d50e386d033e1900bd85d02dc1670af854828813d097846420a0fe07b03c01d209104081b80da06002f81740b805602a815009203601a80a004e025012007803a01c00d804c024011008003c018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record057_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record057_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record057) (record057.maps 1)
      (record057.inverseMaps 1) record057_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record057_frame001_links_0000 record057_frame001_links_0064)
theorem record057_frame001_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) : Supported record057 1 :=
  of_group record057 1 (embedding record057) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record057_frame001_indices record057_frame001_graph record057_frame001_links
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (Fin.cases (record057_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
def record058_frame001_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x7bcf77ed7da7adf55debb875feadd4ba3f3ce5bc8f90f1de29c3774edbda3b37626b5d51a7f4d693d1fa273fd9cb21556a74f59d32ba53c778e51061d436828ff5fb3ed7c8f7decbd26d0c6988ad859ca954b28c50ea053926248c8fd15a24436848ee9d334666cc898c2fe5c0b394b2884e49492022e4487c0db1aa340658c01762ac4b87f0ca1682c8540a21402704707e0d41a02804e0981102103e0780e0130240400680b0140240380400600800800 } : Fields).get c.val)
theorem record058_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record058_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record058_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record058) (record058.maps 1)
      (record058.inverseMaps 1) record058_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record058_frame001_links_0000 (interval_append _ 64 128 129 record058_frame001_links_0064 record058_frame001_links_0128))
theorem record058_frame001_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) : Supported record058 1 :=
  of_group record058 1 (embedding record058) hcells Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record058_frame001_indices record058_frame001_graph record058_frame001_links
def record058_frame002_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x11898b9c4da2410f5871417a0730117f8bf7df72f947b63d31e74f1777d3b85d74e9a73fb9d1cc2e3b70db801beade26e636edb2ec38612aec9738aa7549288941e98e4c223a51a68c8438a0c903a8033f89f78f907b035998c0c3e5b12d11560a6a52728a94209d44d225012488dc461229110477a3aa19e8ca062c3031718b0857027f136896046c22410787fc3721630a8050826410e080036016009003601800be05a02b81580a804901f80d4068028013809804402100f8078038013009004001a00b005002400e0040018008002000 } : Fields).get c.val)
theorem record058_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record058) (record058.maps 2) (record058.inverseMaps 2) record058_frame002_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record058) (record058.maps 2) (record058.inverseMaps 2) record058_frame002_indices (Fin.ofNat record058.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record058_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record058) (record058.maps 2) (record058.inverseMaps 2) record058_frame002_indices (Fin.ofNat record058.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record058_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record058) (record058.maps 2)
      (record058.inverseMaps 2) record058_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record058_frame002_links_0000 (interval_append _ 64 128 129 record058_frame002_links_0064 record058_frame002_links_0128))
theorem record058_frame002_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) : Supported record058 2 :=
  of_group record058 2 (embedding record058) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record058_frame002_indices record058_frame002_graph record058_frame002_links
def record058_frame003_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x4b295b2864ec9a9331e2384678c918a2fc5989b11a21c3e8710d20fc1481d02a023f77dcfa1f33e37c2f75ebb7a6ead45a3b28646bf17badd5b8af15b2b252ea19402794e69c1352644467dcf81ce3926c0d299e334664c79842ea5c0b29642c056c9d936230440859071fa3d4788e11b8358680cc1903105709e1342604a08d1142083d06c0bc1502984e0961282404507e0d41a02804e0981102103e0780e0130240400680b0140240380400600800800 } : Fields).get c.val)
theorem record058_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record058) (record058.maps 3) (record058.inverseMaps 3) record058_frame003_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record058) (record058.maps 3) (record058.inverseMaps 3) record058_frame003_indices (Fin.ofNat record058.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record058_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record058) (record058.maps 3) (record058.inverseMaps 3) record058_frame003_indices (Fin.ofNat record058.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record058_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record058) (record058.maps 3)
      (record058.inverseMaps 3) record058_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record058_frame003_links_0000 (interval_append _ 64 128 129 record058_frame003_links_0064 record058_frame003_links_0128))
theorem record058_frame003_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) : Supported record058 3 :=
  of_group record058 3 (embedding record058) hcells Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record058_frame003_indices record058_frame003_graph record058_frame003_links
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (Fin.cases (record058_frame001_supported hcells) (Fin.cases (record058_frame002_supported hcells) (Fin.cases (record058_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
def record059_frame001_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x16feb59da62d07678afcd6e2b2f57cab8d54aa73519a00cede73137f9ba4c1a57f29c93ec9c64ad23d90f36e99cacce56da88d41e95c457226d0607f73f29f60f8e7b73d39e48b4e4ef26d90a06f436717e0b0c5622a41498a0c4e625e10b07943bc1d60e7869830417b0ba85b82b21520a5851027a12608f843020a0fd07b83c01b40a404081bc0dc06903401780ba05702b015009203701b00c4060026012807c03c01c00d804c0240110080034014009004001c00c005002000c002000 } : Fields).get c.val)
theorem record059_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record059_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record059) (record059.maps 1)
      (record059.inverseMaps 1) record059_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record059_frame001_links_0000 record059_frame001_links_0064)
theorem record059_frame001_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) : Supported record059 1 :=
  of_group record059 1 (embedding record059) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record059_frame001_indices record059_frame001_graph record059_frame001_links
def record059_frame002_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x104f80ec03dffefef7d53de1ed4f5a7a53c69e0eee375d3a35cfce73735b8edc1cdff6fa37b1b9cdbd6cdb0e576ab9f553288141a98f475a3550e283040da020fe67de3e41eb8d6462e30e96c8a6e529269127892048323811848a443f1de8d4867a32818b0ae04b424811b08903dc1e00e8870c3721840ba050826412008884041ae0a404081bc0dc06903401780ba05702b015009203701b00c4060026012807c03c01c00d804c0240110080034014009004001c00c005002000c002000 } : Fields).get c.val)
theorem record059_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record059) (record059.maps 2) (record059.inverseMaps 2) record059_frame002_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record059) (record059.maps 2) (record059.inverseMaps 2) record059_frame002_indices (Fin.ofNat record059.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record059_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record059) (record059.maps 2)
      (record059.inverseMaps 2) record059_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record059_frame002_links_0000 record059_frame002_links_0064)
theorem record059_frame002_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) : Supported record059 2 :=
  of_group record059 2 (embedding record059) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record059_frame002_indices record059_frame002_graph record059_frame002_links
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (Fin.cases (record059_frame001_supported hcells) (Fin.cases (record059_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
def record060_frame001_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcf2e6db2678f7c43e1c30b5702b5cda76d11664afed6f6b3f584aafd522a5f51d9f3cf2a77939b9c14dda5dd2d3962ca8250327374836859c6ccc5d02b0d44ca124aca5211ce8ab44c221501a7fa3f41f58f907b63d31e54cd858f279137884a4141d98ddc6c835116c8b185682a214a0a084e426110b08344101fa0f6075439c19f0cc064031217c0ba05b42ce15f0a9051027a12f08c844c1fc0f607483880ee06d030017c0b805b02c01540a803f01a80a004e024011808003a01c00d804c024011007803801800b004001c00a0040018008002000 } : Fields).get c.val)
theorem record060_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record060_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record060_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record060) (record060.maps 1)
      (record060.inverseMaps 1) record060_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record060_frame001_links_0000 (interval_append _ 64 128 132 record060_frame001_links_0064 record060_frame001_links_0128))
theorem record060_frame001_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) : Supported record060 1 :=
  of_group record060 1 (embedding record060) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record060_frame001_indices record060_frame001_graph record060_frame001_links
def record060_frame002_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x8ca458a28310f86c4332159052814404a008fcd7d6be0dedaf5f7943c4de04ef07583a91d2ce8073b39b1c62e2570bb805beeded65030b1766b9d58a2a59446a104c725f92588e8469230109283340f2018fe87dd3e39ec4e4c6a23189880b625a82b294d0a4c516258928492648123891808a24421de8eac73637b1b10c9c62a2a814a0a004dc24911a888c4201fc0f0070c3721980b2854424211007a039c0ee06d030017c0b805b02c01540a803f01a80a004e024011808003a01c00d804c024011007803801800b004001c00a0040018008002000 } : Fields).get c.val)
theorem record060_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record060) (record060.maps 2) (record060.inverseMaps 2) record060_frame002_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record060) (record060.maps 2) (record060.inverseMaps 2) record060_frame002_indices (Fin.ofNat record060.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record060_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record060) (record060.maps 2) (record060.inverseMaps 2) record060_frame002_indices (Fin.ofNat record060.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record060_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record060) (record060.maps 2)
      (record060.inverseMaps 2) record060_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record060_frame002_links_0000 (interval_append _ 64 128 132 record060_frame002_links_0064 record060_frame002_links_0128))
theorem record060_frame002_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) : Supported record060 2 :=
  of_group record060 2 (embedding record060) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record060_frame002_indices record060_frame002_graph record060_frame002_links
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (Fin.cases (record060_frame001_supported hcells) (Fin.cases (record060_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
def record061_frame001_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcfd67bf3cb91ec86e40b13f863b95dc62d675f9adc565eaf9571aa954e6a333bc9dbce6e7053769804b9657f25591e48924031ed8a844e625cd9e674333958ea21507a571288932454a26d10e8423fe1f94fb07c83db1e9cf24593276936c8504101ff0dd46ce3531870b205622a414a0a084e625e10b08344101e50e7872035a1980c806082f81740b705642a414b0a204f424c11f08984141fa0f707483680f206e03481a00bc05c02c01580a804101b00c4060026012008003c01c00d804c0240110078034016009004001c00c005002000c002000 } : Fields).get c.val)
theorem record061_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record061_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record061_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record061) (record061.maps 1)
      (record061.inverseMaps 1) record061_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record061_frame001_links_0000 (interval_append _ 64 128 132 record061_frame001_links_0064 record061_frame001_links_0128))
theorem record061_frame001_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) : Supported record061 1 :=
  of_group record061 1 (embedding record061) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record061_frame001_indices record061_frame001_graph record061_frame001_links
def record061_frame002_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0551.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0551.count (({ width := 11, code := 0x98930e614bc9772ea594ad93325a484818fd1e63ac728dd1b635c5b8b31522844d8830fa1dc2f85d0b214c2883706a0cbd5780eedb534d692ca593323602bed7baed5a6b2d63ac1578add582534688bd0620840c798f09dc3a66ecd99b0356698d119c2be564ab14125a49c8c1082003dc790ed1d437c6d8d71a43385d8b51562944f89a124224328600b6168290500981282403b0680bc170260480800f01c03604c0901101e0340580901001c0300500800c00800 } : Fields).get c.val)
theorem record061_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (embedding (N := 44310) record061) (record061.maps 2) (record061.inverseMaps 2) record061_frame002_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (embedding (N := 44310) record061) (record061.maps 2) (record061.inverseMaps 2) record061_frame002_indices (Fin.ofNat record061.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record061_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (embedding (N := 44310) record061) (record061.maps 2) (record061.inverseMaps 2) record061_frame002_indices (Fin.ofNat record061.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record061_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (embedding (N := 44310) record061) (record061.maps 2)
      (record061.inverseMaps 2) record061_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record061_frame002_links_0000 (interval_append _ 64 128 132 record061_frame002_links_0064 record061_frame002_links_0128))
theorem record061_frame002_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) : Supported record061 2 :=
  of_group record061 2 (embedding record061) hcells Papers.RationalityTen.SharedFrameCatalogue.group0551
    Papers.RationalityTen.SharedFrameCatalogue.group0551_facts record061_frame002_indices record061_frame002_graph record061_frame002_links
def record061_frame003_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0550.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0550.count (({ width := 11, code := 0x9d93aa74ce29c137e6ccd697d2f65aca69412764d49892924a46c7e8f91e23b4748cd18e304548a513e2644b87b0f21d3f17b4f5dbeb5a6aace19a33362ac3d85afe5ceb796d2d559eb2d61a6948a9091221f4347dcf99ef3ce740e51c53806e8db1af2de5a8b314d2704c48f90d20c3e4798eb1cc36c6a8d11983185b0af14e27c4d09711e2183285e0b21602804e094120230390680bc170260480800f01c03604c0901101e0340580901001c0300500800c00800 } : Fields).get c.val)
theorem record061_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (embedding (N := 44310) record061) (record061.maps 3) (record061.inverseMaps 3) record061_frame003_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (embedding (N := 44310) record061) (record061.maps 3) (record061.inverseMaps 3) record061_frame003_indices (Fin.ofNat record061.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record061_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (embedding (N := 44310) record061) (record061.maps 3) (record061.inverseMaps 3) record061_frame003_indices (Fin.ofNat record061.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record061_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (embedding (N := 44310) record061) (record061.maps 3)
      (record061.inverseMaps 3) record061_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record061_frame003_links_0000 (interval_append _ 64 128 132 record061_frame003_links_0064 record061_frame003_links_0128))
theorem record061_frame003_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) : Supported record061 3 :=
  of_group record061 3 (embedding record061) hcells Papers.RationalityTen.SharedFrameCatalogue.group0550
    Papers.RationalityTen.SharedFrameCatalogue.group0550_facts record061_frame003_indices record061_frame003_graph record061_frame003_links
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (Fin.cases (record061_frame001_supported hcells) (Fin.cases (record061_frame002_supported hcells) (Fin.cases (record061_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record061_frames_supported
theorem record062_frame000_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    Supported record062 0 :=
  of_identity record062 0 (by decide +kernel)
def record062_frame001_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19d7ce666db23f90ec7be27f0b56feb5eda6ad0b66eafcd706b3357eab4553aa6b5179fc4f6e7812fb9704b264a1237914b6ddb42ce2665ab79586a25508a5652908ac44ca2150c88424181fe4fce7d63e41edcf4e7942d5163c9e24dd21290506f03651a88cc061c2fc1628acc54429414189cc4c021610687943ac1cf0e106ec3681ad0d3063c31017c0ba85b82cc15f0a9051027a12f08c844c21810507b036c0ee06d030017c0b405802b81580a803f01a80a004e022010007c03c01c00d804c024011006803001600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record062_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record062_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record062_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record062) (record062.maps 1)
      (record062.inverseMaps 1) record062_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record062_frame001_links_0000 (interval_append _ 64 128 133 record062_frame001_links_0064 record062_frame001_links_0128))
theorem record062_frame001_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) : Supported record062 1 :=
  of_group record062 1 (embedding record062) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record062_frame001_indices record062_frame001_graph record062_frame001_links
def record062_frame002_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x118e8c3c58a277134887c39a15904f816c042002fdd7d53e21ed6f5c79c3c59e08ee0759ba99d34e34713b86db96dba6d7b0e1858bb25ce2a9d52ca22507a6392fc8e9469a30113c87b438a0c903a8063fa1f78f907b03599a88c6061f2d896a0a6a52728b13e49b64d2250124890247123091488823bd1d58d4865031617a0b8c5a62c215c09fc4da24911b089041e1fc0f0070c3721980b2854428413208803600ee06d030017c0b405802b81580a803f01a80a004e022010007c03c01c00d804c024011006803001600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record062_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record062) (record062.maps 2) (record062.inverseMaps 2) record062_frame002_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record062) (record062.maps 2) (record062.inverseMaps 2) record062_frame002_indices (Fin.ofNat record062.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record062_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record062) (record062.maps 2) (record062.inverseMaps 2) record062_frame002_indices (Fin.ofNat record062.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record062_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record062) (record062.maps 2)
      (record062.inverseMaps 2) record062_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record062_frame002_links_0000 (interval_append _ 64 128 133 record062_frame002_links_0064 record062_frame002_links_0128))
theorem record062_frame002_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) : Supported record062 2 :=
  of_group record062 2 (embedding record062) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record062_frame002_indices record062_frame002_graph record062_frame002_links
def record062_frame003_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x8cc8c98c48bb8b98b38ac89887786a86185d85384583883082b82181a8148087f07ec7e97c47bf7bc7a279e79a6f36eb6a869c5fa5ef5ad5a055454f5044f74ec4df4ce4c94a549848c48547b46f4633c03b537036631a3152c72be2b22a229428f26825d25224b23e2342291e51df1b61a719f19018817f17717015d15514a14213913112c1221161101080f20ee0e80e10d40ba07506b05e05d05805605505405203f03502802702202001f01e01c01b01301201100d00c00b00a009007005004003002001000 } : Fields).get c.val)
theorem record062_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record062) (record062.maps 3) (record062.inverseMaps 3) record062_frame003_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record062) (record062.maps 3) (record062.inverseMaps 3) record062_frame003_indices (Fin.ofNat record062.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record062_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record062) (record062.maps 3) (record062.inverseMaps 3) record062_frame003_indices (Fin.ofNat record062.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record062_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record062) (record062.maps 3)
      (record062.inverseMaps 3) record062_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record062_frame003_links_0000 (interval_append _ 64 128 133 record062_frame003_links_0064 record062_frame003_links_0128))
theorem record062_frame003_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) : Supported record062 3 :=
  of_group record062 3 (embedding record062) hcells Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record062_frame003_indices record062_frame003_graph record062_frame003_links
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (Fin.cases (record062_frame001_supported hcells) (Fin.cases (record062_frame002_supported hcells) (Fin.cases (record062_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record062_frames_supported
theorem record063_frame000_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    Supported record063 0 :=
  of_identity record063 0 (by decide +kernel)
def record063_frame001_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xb565a7ed2361cb0557debc95d6ae1525a8ff464a0c4ff67c53ab9cdce1e68b32e98bc76a3a11b7888c4161e109984641eda04cee628b0f553aa894f627613169824ad252d28893d498248923690447ea3dd1e28ea471a36ce206fb32b9908b0c57228293809a04bd24d11dc8ce43021090448043f11f08f4062e30314b09c44c224e11588203f01c10d906883261820b9058429e1480a084e826612c09284282080fd077835c0d006002f81780b405802b81580a8030014009c04c022010007c03c01c00d804c024011006802c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record063_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record063_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record063_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record063) (record063.maps 1)
      (record063.inverseMaps 1) record063_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record063_frame001_links_0000 (interval_append _ 64 128 136 record063_frame001_links_0064 record063_frame001_links_0128))
theorem record063_frame001_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 1 :=
  of_group record063 1 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record063_frame001_indices record063_frame001_graph record063_frame001_links
def record063_frame002_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xceb672f38191ec86e40b1898aec4fdc82e1b6feb4c5a0ecf1624b04d7e6b2f57cab8cfe27b73c097dcb8259325091bc8a5b6ed9e671332d5bcac7512a8452b294446a22b113288743221090607f93f39f60f907b73d39e50b54593278937484a4101d00de06ca3531980c385f82c51598a90528283139898042c20d0f2875839e1c80dd86b434c18f0c406082f81750b705982b21520a5851027a136097844c21810507b836c0d006002f81780b405802b81580a8030014009c04c022010007c03c01c00d804c024011006802c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record063_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record063) (record063.maps 2) (record063.inverseMaps 2) record063_frame002_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record063) (record063.maps 2) (record063.inverseMaps 2) record063_frame002_indices (Fin.ofNat record063.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record063_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record063) (record063.maps 2) (record063.inverseMaps 2) record063_frame002_indices (Fin.ofNat record063.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record063_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record063) (record063.maps 2)
      (record063.inverseMaps 2) record063_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record063_frame002_links_0000 (interval_append _ 64 128 136 record063_frame002_links_0064 record063_frame002_links_0128))
theorem record063_frame002_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 2 :=
  of_group record063 2 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record063_frame002_indices record063_frame002_graph record063_frame002_links
def record063_frame003_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x86d0d61a42d8590ae1542884d0720c41481501e02403802ffdfabf27def61eabd2786efdddbb0758ea1a4b4262ac3d5f2b7514a113125d49a91921a404768d5192274488891021d434858e51c332c640b71692b2548a794c28e5049f1332604b89612924c488829001e03a4730e31bc3606a8ca18e314618c017a2e45b0b51682cc590b11602b0558aa1502903105a0b21602a0520a21402703005009c1302204007c0f01c03604c0901101a02c0500900e0180280400600800800 } : Fields).get c.val)
theorem record063_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (embedding (N := 44310) record063) (record063.maps 3) (record063.inverseMaps 3) record063_frame003_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (embedding (N := 44310) record063) (record063.maps 3) (record063.inverseMaps 3) record063_frame003_indices (Fin.ofNat record063.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record063_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (embedding (N := 44310) record063) (record063.maps 3) (record063.inverseMaps 3) record063_frame003_indices (Fin.ofNat record063.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record063_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (embedding (N := 44310) record063) (record063.maps 3)
      (record063.inverseMaps 3) record063_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record063_frame003_links_0000 (interval_append _ 64 128 136 record063_frame003_links_0064 record063_frame003_links_0128))
theorem record063_frame003_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 3 :=
  of_group record063 3 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record063_frame003_indices record063_frame003_graph record063_frame003_links
def record063_frame004_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x9c137e6f4c49853025f4ba96d2564848b8fb1e63ac738df1ae2ac508970ba15c2882703e05c007f6fd9bfb76688cf5712d954ea813f2794d29892fa5c4ae945272434808f91e23946c8c8ee1d3342668bc1732c6570ac9562a252ca413d2744e09b1332604b08790a1f43cc780ed1d03886f8d41a233c668ca18e30c600bf17c2f45e0bb1742d85a8b41642b83305e0ba1702c0560aa1502903005009c1302204007c0f01c03604c0901101a02c0500900e0180280400600800800 } : Fields).get c.val)
theorem record063_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record063) (record063.maps 4) (record063.inverseMaps 4) record063_frame004_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record063) (record063.maps 4) (record063.inverseMaps 4) record063_frame004_indices (Fin.ofNat record063.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record063_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record063) (record063.maps 4) (record063.inverseMaps 4) record063_frame004_indices (Fin.ofNat record063.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record063_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record063) (record063.maps 4)
      (record063.inverseMaps 4) record063_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record063_frame004_links_0000 (interval_append _ 64 128 136 record063_frame004_links_0064 record063_frame004_links_0128))
theorem record063_frame004_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 4 :=
  of_group record063 4 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record063_frame004_indices record063_frame004_graph record063_frame004_links
def record063_frame005_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x8c6c61a2e513a899c47e1fd0f3873419e0bd04f807bffdfdefc27dcbea9ed4f5a7a53acdd4ce9a71a389dc36dcb6dd36bd870c295d92e7154ea9a511283d31c97a48ca3a51a68c144f21ed0e283240ea020fe87de3e41ec0d666a6318187cb625a42ac14d4a4e51827c936c9a44a0249120c8e2461229110477a3ab1a90ca062c3051718b0857027f1368968492236112083c3dc1e00e8870c3721ab0cc054428413208883600d006002f81780b405802b81580a8030014009c04c022010007c03c01c00d804c024011006802c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record063_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record063) (record063.maps 5) (record063.inverseMaps 5) record063_frame005_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record063) (record063.maps 5) (record063.inverseMaps 5) record063_frame005_indices (Fin.ofNat record063.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record063_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record063) (record063.maps 5) (record063.inverseMaps 5) record063_frame005_indices (Fin.ofNat record063.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record063_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record063) (record063.maps 5)
      (record063.inverseMaps 5) record063_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record063_frame005_links_0000 (interval_append _ 64 128 136 record063_frame005_links_0064 record063_frame005_links_0128))
theorem record063_frame005_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 5 :=
  of_group record063 5 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record063_frame005_indices record063_frame005_graph record063_frame005_links
def record063_frame006_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x91190c90a8f48f38ee8e88e68e58aa8a389e88487d87586986786084383b8347f97f07ec7c87c37b97a179a7936af6a96626535d75d158757b54253b5195095004f94ec4df4da4c54bd4b64b04a84a049940f4083bb3ae35d35232430d3032f82e92da2d42b22a829e29328927e27121f2141e61ce1c41ba1aa19d19617216916015514913f13312211b11510e1091040fd0e50df0d80cb0b506605e05d05c05805605505405203002802702602202001f01e01c01b01301201100d00b00a009007006005004003002001000 } : Fields).get c.val)
theorem record063_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record063) (record063.maps 6) (record063.inverseMaps 6) record063_frame006_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record063) (record063.maps 6) (record063.inverseMaps 6) record063_frame006_indices (Fin.ofNat record063.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record063_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record063) (record063.maps 6) (record063.inverseMaps 6) record063_frame006_indices (Fin.ofNat record063.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record063_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record063) (record063.maps 6)
      (record063.inverseMaps 6) record063_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record063_frame006_links_0000 (interval_append _ 64 128 136 record063_frame006_links_0064 record063_frame006_links_0128))
theorem record063_frame006_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 6 :=
  of_group record063 6 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record063_frame006_indices record063_frame006_graph record063_frame006_links
def record063_frame007_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x8cb8c88c68ba8b88b58b18af8ac87c87b87786085c85784f84984582f82a8257f07ec7e97c47bf7bc7a279e79a6f36e96a869c5fa5f35ad5a055454b51c5044f74ed4df4ce4c94a549848e48547b46f4633c03b937036631a3112e22c72be2b32a229428f26825d25424b23e2342291e51df1b61a719f19718817717015d15514e14a14213913112812211c11611010d1080ee0e80e10d50ba06605e05d05c05805605505405203002802702602202001f01e01c01b01301201100d00b00a009007006005004003002001000 } : Fields).get c.val)
theorem record063_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record063) (record063.maps 7) (record063.inverseMaps 7) record063_frame007_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record063) (record063.maps 7) (record063.inverseMaps 7) record063_frame007_indices (Fin.ofNat record063.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record063_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record063) (record063.maps 7) (record063.inverseMaps 7) record063_frame007_indices (Fin.ofNat record063.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record063_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record063) (record063.maps 7)
      (record063.inverseMaps 7) record063_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record063_frame007_links_0000 (interval_append _ 64 128 136 record063_frame007_links_0064 record063_frame007_links_0128))
theorem record063_frame007_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 7 :=
  of_group record063 7 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record063_frame007_indices record063_frame007_graph record063_frame007_links
def record063_frame008_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1003.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1003.count (({ width := 9, code := 0xd268f45a1d067f3d9dce66f3397c8e3f1b8cc56230580bf5dae972b55a2cd61afd76a14ea04fa6f3593c963b1b89c3a190a83c0e02fa7c3d9e8f177bb5cae36ab4d96c960af174b85aac55ea853291449f4ea6d24904420d027f3e1e0ec6f369acd26632188be5e2e970b65a2c954a853291408c3f1f0f472371b0d4662e138984a210f8783a1b0d04c24110682c1409038180a04018080200 } : Fields).get c.val)
theorem record063_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1003.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (embedding (N := 44310) record063) (record063.maps 8) (record063.inverseMaps 8) record063_frame008_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (embedding (N := 44310) record063) (record063.maps 8) (record063.inverseMaps 8) record063_frame008_indices (Fin.ofNat record063.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record063_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (embedding (N := 44310) record063) (record063.maps 8) (record063.inverseMaps 8) record063_frame008_indices (Fin.ofNat record063.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record063_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (embedding (N := 44310) record063) (record063.maps 8)
      (record063.inverseMaps 8) record063_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record063_frame008_links_0000 (interval_append _ 64 128 136 record063_frame008_links_0064 record063_frame008_links_0128))
theorem record063_frame008_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 8 :=
  of_group record063 8 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group1003
    Papers.RationalityTen.SharedFrameCatalogue.group1003_facts record063_frame008_indices record063_frame008_graph record063_frame008_links
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (Fin.cases (record063_frame001_supported hcells) (Fin.cases (record063_frame002_supported hcells) (Fin.cases (record063_frame003_supported hcells) (Fin.cases (record063_frame004_supported hcells) (Fin.cases (record063_frame005_supported hcells) (Fin.cases (record063_frame006_supported hcells) (Fin.cases (record063_frame007_supported hcells) (Fin.cases (record063_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record063_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043
