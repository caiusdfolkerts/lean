module
prelude
public import GraphInputsRow29Part00194Data
public import RawFrameSupport
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00194
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
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3f09d76dfc6652f1962cb04543292942098f4c024251a28c044d218d06080c3fd9fa4f6e6922f11740aa451626e116c8983d51ce8e306cc32f17e0b6058e2b514188e44522220ee87403741b30d3067832e1910c506082ea14a0a204f426a128090846422610c078023411807e03d81a80d2066030816c0b405702b01540a804602180c806202e014808c04401f00f007403801900c00540280110070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record001_frame001_links_0000 record001_frame001_links_0064)
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
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x539a4d44a87cd69792b248c8c8dd1ae26c4484f076044027e4fb1ed3cd78aee5d83ab74cd699db2b61ec2975ae8588af14ea954fc9e1362674b093523a3c46a8c5162023f0784e11b9362654c71842f65cca69442764ac929112164147b8ef1c831c5d8b61602a45107e0f61b8368690bc1742d8550a81302383906e0cc138250460740e0190300540981202003c0700c0140200380500600800800 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xdec6bbb399998ba05952bf9534a8a511284932497b48d23e915e898432a1510387f83f41f1cf687a63ca99b0bec5ca2b315589dc4de22f111c7cc3c61bd8d906623201740b1056829314009c84c223211508583f21f30f6075439c1c20dd06c83121830bd85b42ce1500a5051026a12f093842c1fc0f607803a01c408403f81c40de06b02f81740b605502a013008e03901b80cc04e025011807403801900c0054026012008003c01c00c005002000e0050018008002000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x7d07af77d7737166f36e76c46bf68c68464f6446176025d45c25a65a057d56c56254c53e5325274cc49848045244e41340b3d73cc3aa3a538337835a34e32e31730a2fb2ee2e62dd2a729827b24e24723c21f2162071fa1f01b91ad1a218b18116315915213d1311250fc0eb0e30dc0d20ca07f07b06e06c06805c05a05805205104a04603803603202702502301d01c01901801501301201000f00e00c00a008007005003002001000 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
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
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x6f3b755a50ccb627b0f1704b70561a9993d49d74d426893389794b8a5a52b89544a7251926492b48e2459206900479a3ad1c08d94051fe0e746d532a9904ba45bf2d51534a7852b28213d09c04d124c921c8ce45421190047e23631a80cec5bc2cd15e0a5450a27113108a84301f80f286d03241820ab854028e14009d84d025612608e846022210908283f01ea0f007503881b80d6068024811a08c03781a80d203701900c405c02d01500a004a023011007c03c01d00e0064030015009804001c00d0050024010007 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x8a113e1e434841076034057caf71e03bd754e85ce38970cdfdb8b6b6cad7da5343662cad8931060abe5752e5594b25502954f49dd352624c09492724b4868fd1da374488790920b3ee7acf21b535a69cc798b3105f0bb9732de560a79402744908a90d1fc3e8778e91ce3806b8d519c32c628bc1742c8568a9142254468881061dc3a8740c41802f8350640c41702d0540a01282304407c0f01d0380640c0150260400700d01402404007 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0xb27642b5557a674ae865099c333253ca08f51be33c4587d0d20fc1781f021fb3f07c2f75e1bc1764e9dcb3926c6d7d9230b5c8b79622bd56ea694a28d4f89d938a6c4ae93d2023a448845049d839c718d49a5346658c798930a5bcb395a2a64e09411f21e428800fa1f03cc750e81bc3746b0cb1943005e0ba1682ac530a213c2083e87c0d81a0338370640c41702d0540a01282304407c0f01d0380640c0150260400700d01402404007 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record005_frame003_links_0000 record005_frame003_links_0064)
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1f7ede96b93329794b0054faa21498a104c024711f48c144d218d09e83040e1fecfd27c73db9a58b9856b2aa14609b844c1f40f1871a3661978c6c5f82e81638ad452628311107fc3f21f30f207783a01c20dd069832218a0c185ec2ea14a0a204f426a12f09404842180f6078023411807403881a80d206602e816c0b405702b01540a803c01c80c806202e012808c04401f00f007403801900c005402000e0068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x19acc055df2d39594a6551028393bc9b44a6a3f51b68a4442a11505e80f3fd9f6cfa47aa3c91b34cbc61c3051774b6a55428813d09924b224011b88ae44621790988103f71b68c886283061738b6457e29d144898047423111208484021a70ce06403081790b6859026210807d823411807403881a80d206602e816c0b405702b01540a803c01c80c806202e012808c04401f00f007403801900c005402000e0068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record006_frame002_links_0000 record006_frame002_links_0064)
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
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x3755a50ccb61e2dc1586a664eba65d2e896e4b425652a6945497a4a123691348323fd1e08ea3fc1ce8daa6412d51534a7852b28213d09a2499243919c8a843221190047e233b16f0b3457829514289884542180fc07943861b40c906082ac14f09d04cc24a11e08b84402080ef074823411806a03481980ca06202e816c0b405702b01540a803201880b805a02a012808c04401f00f007403801900c005402000e0068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3ae1bccd726652f29608a9f50825f123890b47d234d18289a431a14506081e3fd9fa4f8e7b734b1740ad64dc2240fa07ae3c61cf8e346cc32f18e8bf05d42c715a8a4c5062220ff87e43e61e40ef07403741b30d3067832218a0bd85d42c01590a204f425e12809084682180f7078023411806a03481980ca06202e816c0b405702b01540a803201880b805a02a012808c04401f00f007403801900c005402000e0068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0xde1a7b3961cbb5622ae5069992ba554a6931252444748dd1922e4528990fa1d3f2740dd18f2e458cb095f2b0558a81462864f89d1352644ac949091f43e07b0ef1da39c6e8da1aa344660c91843005b8b61662c8580af15c2b4558a814e204400640c61802f85c0ae1542a0510a013c270320620b81682a04a08c1101f03c0740e0190300540800e01a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record007_frame003_links_0000 record007_frame003_links_0064)
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xebdc3b6c678c49752cf53ea0939a714de9a1332604ac94d2724a48a9091da39418790e49992f85b4b59692c4580ad15029a520a213f2784d499913208408800f91ee3c4738e41be36c6b0d3198328608c017a2f05d0b91702dc5a8b2162224440680ce190318600b61642c0550a814c290320620b81682a04a08c1101f03c0740e0190300540800e01a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record007_frame004_links_0000 record007_frame004_links_0064)
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
def record007_frame005_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1111.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1111.count (({ width := 10, code := 0x2829d26b9323f8c628825ee781de771d574dcd711c16f1b86cdb06a5a765d8960161519384d9344b52b4951c465144410b421013fce134cd133cc8318c02dcb42bcab298a32709a244902348c2288922087214822046b1a85916055150511304a124461144410c320c42e0b42a094230881f0781d07019060150400e0340a0240801c060140400c0200400 } : Fields).get c.val)
theorem record007_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record007_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record007) (record007.maps 5)
      (record007.inverseMaps 5) record007_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record007_frame005_links_0000 record007_frame005_links_0064)
theorem record007_frame005_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 5 :=
  of_group record007 5 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1111
    Papers.RationalityTen.SharedFrameCatalogue.group1111_facts record007_frame005_indices record007_frame005_graph record007_frame005_links
def record007_frame006_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x3199808bbe5a72b294cca204da25311fa8eb46da2d1148885422a0c501e7fd3ed9f48f54792366997cc385b52a99440a024f426b1324964480238115c89042f21310207ee36d1910c5060c2e716c8afc512277130094447423110908043ac1c60ce06402f216d0b2055c26210907d823411806a03481980ca06202e816c0b405702b01540a803201880b805a02a012808c04401f00f007403801900c005402000e0068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record007_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record007_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 6)
      (record007.inverseMaps 6) record007_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record007_frame006_links_0000 record007_frame006_links_0064)
theorem record007_frame006_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 6 :=
  of_group record007 6 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record007_frame006_indices record007_frame006_graph record007_frame006_links
def record007_frame007_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x5f25c15a657653d50c4f14c149147646f46845745044242f42841c4144084023f53ef3ae37c35e32c2f52cd2c72c22af2a829827d27526c26425725223e2361f01c81c01b91a61a119317816e16115a15114d13913111c1161040fe0f30ed0e80e30d80c80c308308206706606306205f05a05805705405305205103203102e02d02a02502302201f01e01d01c01901801501000e00d00a009008007006005004003002001000 } : Fields).get c.val)
theorem record007_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record007_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record007) (record007.maps 7)
      (record007.inverseMaps 7) record007_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record007_frame007_links_0000 record007_frame007_links_0064)
theorem record007_frame007_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 7 :=
  of_group record007 7 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record007_frame007_indices record007_frame007_graph record007_frame007_links
def record007_frame008_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x6f56ce6b16776235e25c357c53e5115064fd4e44d94c34a949e49248747546e45a4513e73a63873403022d52c82bd2a329a28726d26124f24523923221e2151cb1b21ad1a619518e17f17116a15d15414714013913512311e10d1070f90f30ed0eb0e00ce0ca08b08a06906806506406105c05a05905605505405303203102e02d02a02502302201f01e01d01c01901801501000e00d00a009008007006005004003002001000 } : Fields).get c.val)
theorem record007_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record007_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record007) (record007.maps 8)
      (record007.inverseMaps 8) record007_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record007_frame008_links_0000 record007_frame008_links_0064)
theorem record007_frame008_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 8 :=
  of_group record007 8 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record007_frame008_indices record007_frame008_graph record007_frame008_links
def record007_frame009_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1048.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1048.count (({ width := 9, code := 0x4421d097fbf5f6f6763a5c6e170375b8da6a349a0ce6632d8ec560afd74b056a9d4aa450a813c984b251249047a2d12843f1f0f6783b9d4de6d359a4ce6631180b85b2c15caa5429948a04f2711c8c41200f4783b1c0d86a32188c05e2a148984a241087c3c1b0d06430150a04c200e068281208038180a04018080200 } : Fields).get c.val)
theorem record007_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1048.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1048.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1048.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record007_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1048.localPairCheck (smallEmbedding record007) (record007.maps 9)
      (record007.inverseMaps 9) record007_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record007_frame009_links_0000 record007_frame009_links_0064)
theorem record007_frame009_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 9 :=
  of_group record007 9 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1048
    Papers.RationalityTen.SharedFrameCatalogue.group1048_facts record007_frame009_indices record007_frame009_graph record007_frame009_links
def record007_frame010_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1049.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1049.count (({ width := 9, code := 0x64b1780b85bacf5ca651275389bcca632d9348e411e8dc6a2b138741df8ec72369b0d7693459ac661b017cbb5d2d566a84f27136964aa45148742208fe7e3c9dce471371b4d66a349a0cc6532164b05027930964821904803d1e0ec7432188b85a2a1288c441f0f07438190c054200e068281208038180a04018080200 } : Fields).get c.val)
theorem record007_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1049.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record007_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record007) (record007.maps 10)
      (record007.inverseMaps 10) record007_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record007_frame010_links_0000 record007_frame010_links_0064)
theorem record007_frame010_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 10 :=
  of_group record007 10 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1049
    Papers.RationalityTen.SharedFrameCatalogue.group1049_facts record007_frame010_indices record007_frame010_graph record007_frame010_links
def record007_frame011_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1047.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1047.count (({ width := 9, code := 0x5127d39994c255258f4621f0d864220f047ebe9eef5793c5d8ea72b7db4d366b1184c15eaf172b257ab154a7532853e9646a2d148642a08f6783a9cce06f351a0c6622f978b85b2d164ae562a93498472310c84401e0e872361a8d0662e168a8522711884401d0e06c34170b050200e068281208038180a04018080200 } : Fields).get c.val)
theorem record007_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1047.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1047.localPairCheck (smallEmbedding record007) (record007.maps 11) (record007.inverseMaps 11) record007_frame011_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1047.localPairCheck (smallEmbedding record007) (record007.maps 11) (record007.inverseMaps 11) record007_frame011_indices (Fin.ofNat record007.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record007_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1047.localPairCheck (smallEmbedding record007) (record007.maps 11)
      (record007.inverseMaps 11) record007_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record007_frame011_links_0000 record007_frame011_links_0064)
theorem record007_frame011_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 11 :=
  of_group record007 11 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1047
    Papers.RationalityTen.SharedFrameCatalogue.group1047_facts record007_frame011_indices record007_frame011_graph record007_frame011_links
def record007_frame012_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x72b6f46d86b367162d60a5e55a556c56155553f5305194f84ed4da4cb4b24a549348d4464083e63c338235735034833532d31b3022fb2ed2e02cf2c62b82b426423822f2262112091f41dd1d41c41b61a519918b18717216714613a11f1131070fc0eb0ce0c508108006406306005f05e05905705605305205105003203102e02d02a02502302201f01e01d01c01901801501000e00d00a009008007006005004003002001000 } : Fields).get c.val)
theorem record007_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record007) (record007.maps 12) (record007.inverseMaps 12) record007_frame012_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record007) (record007.maps 12) (record007.inverseMaps 12) record007_frame012_indices (Fin.ofNat record007.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record007_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record007) (record007.maps 12)
      (record007.inverseMaps 12) record007_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record007_frame012_links_0000 record007_frame012_links_0064)
theorem record007_frame012_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 12 :=
  of_group record007 12 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record007_frame012_indices record007_frame012_graph record007_frame012_links
def record007_frame013_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x1702c6d6da8942e6bcba9231aa234408750ba134177f8fd9f5be47aaf35e03b9708d499930d5acacd562aa534a5943a6c4c69612623d46488d0f1db3626a0d21913145dcb115b2a85249f13624c488881091f23d0740e11b4350650b71621e83c8660ca188308600b61642c0550a814c290320620b81682a04a08c1101f03c0740e0190300540800e01a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record007_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record007) (record007.maps 13) (record007.inverseMaps 13) record007_frame013_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record007) (record007.maps 13) (record007.inverseMaps 13) record007_frame013_indices (Fin.ofNat record007.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record007_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record007) (record007.maps 13)
      (record007.inverseMaps 13) record007_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record007_frame013_links_0000 record007_frame013_links_0064)
theorem record007_frame013_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 13 :=
  of_group record007 13 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record007_frame013_indices record007_frame013_graph record007_frame013_links
def record007_frame014_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0856.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0856.count (({ width := 9, code := 0x41608fe77bb5d8e66bb55a2cf6732d94c86230980be5e2ed72b759ac9589d4da5d2a9448a411c8a442190882409fcfa793a9cce46f371b0d06632188c05f2e96cae5629948a04f27134984b2510c843c1d8e872381a8cc642f170b458261289046220f87438190c05c2c150a04c200e068281208038180a04018080200 } : Fields).get c.val)
theorem record007_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0856.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0856.localPairCheck (smallEmbedding record007) (record007.maps 14) (record007.inverseMaps 14) record007_frame014_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0856.localPairCheck (smallEmbedding record007) (record007.maps 14) (record007.inverseMaps 14) record007_frame014_indices (Fin.ofNat record007.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record007_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0856.localPairCheck (smallEmbedding record007) (record007.maps 14)
      (record007.inverseMaps 14) record007_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record007_frame014_links_0000 record007_frame014_links_0064)
theorem record007_frame014_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 14 :=
  of_group record007 14 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0856
    Papers.RationalityTen.SharedFrameCatalogue.group0856_facts record007_frame014_indices record007_frame014_graph record007_frame014_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (Fin.cases (record007_frame005_supported hcells) (Fin.cases (record007_frame006_supported hcells) (Fin.cases (record007_frame007_supported hcells) (Fin.cases (record007_frame008_supported hcells) (Fin.cases (record007_frame009_supported hcells) (Fin.cases (record007_frame010_supported hcells) (Fin.cases (record007_frame011_supported hcells) (Fin.cases (record007_frame012_supported hcells) (Fin.cases (record007_frame013_supported hcells) (Fin.cases (record007_frame014_supported hcells) (fun j => Fin.elim0 j))))))))))))))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xdd569430f16e0ac34eba65d2dc9594a2a4a124491b489a43520c8ff478a3a8ff073a32096a8a78504268921c8ee46722a110c8644232010fc46762cd14a89884302080fc07943a81c30da064c3041560a784e826612508f045c22010a08203bc13008d04601d40d406903301940c405b02d01600ae05602a815007a03201880b805a02a011808804001f00f007403801900c005401c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xeb86f33329794b0450825f12168d344d214508483040f2034ff67e93e41edcd2c5d026e11207ae39f1b30c7461c2fc1750b6458e2b514a0a0c4441f90f207403661ad0d306783301910c505f02ea1600ac851027a12f094048423411308603dc13008d04601d40d406903301940c405b02d01600ae05602a815007a03201880b805a02a011808804001f00f007403801900c005401c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x37869ec3976ac45069992aa4c4888dd1aa3245c8b114a26440874fc9d031e5c8b09582a050ca093e2744e09a9322584a4848f81de39c6d0d81aa344678cc19230c600b716c2cc590b015e2b8568ac1562a0458811001b8320630c017c2e0550a81482885009e1381e0320620b81682a0460881001f03c0740e0190300540700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
def record008_frame004_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x3af70ecf1892ea53ea0938a684c094d28a4e49492122a424788e5061e43325f0b59622b4534a59482885089f93c26c4cc899021f23c4720e21be36c6c8d61a6334650c11802f45e0ba1722e05b8b616a2c84a0891101cc340670c818c300590b01582a8540a61481e8320620b81682a0460881001f03c0740e0190300540700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record008_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record008_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 4)
      (record008.inverseMaps 4) record008_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record008_frame004_links_0000 record008_frame004_links_0064)
theorem record008_frame004_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 4 :=
  of_group record008 4 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record008_frame004_indices record008_frame004_graph record008_frame004_links
def record008_frame005_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xc666022d39594a664da25311d68b4442a0c504080f3fe9fb0fb67d23d59e48d9a65f2da954ca024d625911c08c845722410f085e4262048fdc6da3141738afc4ee26d130094448e23a118884c4021d60e306703201790b685902ae144098842413008d04601d40d406903301940c405b02d01600ae05602a815007a03201880b805a02a011808804001f00f007403801900c005401c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record008_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record008_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 5)
      (record008.inverseMaps 5) record008_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record008_frame005_links_0000 record008_frame005_links_0064)
theorem record008_frame005_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 5 :=
  of_group record008 5 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record008_frame005_indices record008_frame005_graph record008_frame005_links
def record008_frame006_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x6f56ce6776235e257c53e5064e44c349e49949248747f47546e45b4513e73a63403022c82a328726125924f24524023923221f2151cb1ad19517f16a16515d15414f14714013a13512311e10d1070f90f30ed0eb0e60e00ce09608b08a07406906806506406105a05905705605505405303d03203102e02d02a02302202001f01e01d01c01901801500e00d00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record008_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record008_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record008) (record008.maps 6)
      (record008.inverseMaps 6) record008_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record008_frame006_links_0000 record008_frame006_links_0064)
theorem record008_frame006_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 6 :=
  of_group record008 6 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record008_frame006_indices record008_frame006_graph record008_frame006_links
def record008_frame007_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xba2b57ab4a5aa0394e8f68978638247e97d47c07ab79678176e74272b6a264e5b956951b4f04c448f48247746845944a43d41d40f39534030b2d82a02932862742652552462252151e21d51b51a818717816b15714513510409608d08c07506a06906606506205b05a05805705605505403d03203102e02d02a02302202001f01e01d01c01901801500e00d00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record008_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record008_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 7)
      (record008.inverseMaps 7) record008_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record008_frame007_links_0000 record008_frame007_links_0064)
theorem record008_frame007_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 7 :=
  of_group record008 7 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record008_frame007_indices record008_frame007_graph record008_frame007_links
def record008_frame008_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0866.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0866.count (({ width := 8, code := 0xd1cfc9c8c6c0bebab5b2aeadacabaaa9a8a6a49f9d9795918c898584838281807f7d7b75716c696564636261605f5d5b56555352504f4e4d4c4b4844403f3d3938373635302f2e2d2c2b2a2824232221201b1a19181716151413120d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0866.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0866.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0866.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record008_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0866.localPairCheck (smallEmbedding record008) (record008.maps 8)
      (record008.inverseMaps 8) record008_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record008_frame008_links_0000 record008_frame008_links_0064)
theorem record008_frame008_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 8 :=
  of_group record008 8 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0866
    Papers.RationalityTen.SharedFrameCatalogue.group0866_facts record008_frame008_indices record008_frame008_graph record008_frame008_links
def record008_frame009_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0825.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0825.count (({ width := 11, code := 0x397714d69a3b355feb91652bb554a5549a8c50ca093ea744d8995232343fc78ce49b8352650c81873025f4bd1732d4594a192d23e444821021fa3dc7a8f11d6398708d219a310600ba16e2c8588ad1502703d0750e81a02f05d0b41642b04f09c1302584a0921201e0320620b81682a0460881001f03c0740e0190300540700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record008_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0825.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record008_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record008) (record008.maps 9)
      (record008.inverseMaps 9) record008_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record008_frame009_links_0000 record008_frame009_links_0064)
theorem record008_frame009_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 9 :=
  of_group record008 9 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0825
    Papers.RationalityTen.SharedFrameCatalogue.group0825_facts record008_frame009_indices record008_frame009_graph record008_frame009_links
def record008_frame010_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0821.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0821.count (({ width := 7, code := 0x68cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record008_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0821.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0821.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0821.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record008_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0821.localPairCheck (smallEmbedding record008) (record008.maps 10)
      (record008.inverseMaps 10) record008_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record008_frame010_links_0000 record008_frame010_links_0064)
theorem record008_frame010_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 10 :=
  of_group record008 10 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0821
    Papers.RationalityTen.SharedFrameCatalogue.group0821_facts record008_frame010_indices record008_frame010_graph record008_frame010_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (Fin.cases (record008_frame004_supported hcells) (Fin.cases (record008_frame005_supported hcells) (Fin.cases (record008_frame006_supported hcells) (Fin.cases (record008_frame007_supported hcells) (Fin.cases (record008_frame008_supported hcells) (Fin.cases (record008_frame009_supported hcells) (Fin.cases (record008_frame010_supported hcells) (fun j => Fin.elim0 j))))))))))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x6db6a967d67566f65d63862b5e75e15b15a258454e54c5145044ed4dd4d44a84a649847e47747045144d43a4284234103df3d93a939237c34e33a30c2f32dd2d52cc2a729429027626f25f24f23c2322232152081e21dd1c01ba1aa1a119a19518517f16315b14e1461391281081000f70e80e00de0d80d40ca0c20b70b20a80a309408c07106a06805f05805705205003e03703602d02602401f01e01801201100d009008006003001000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record009_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00194
