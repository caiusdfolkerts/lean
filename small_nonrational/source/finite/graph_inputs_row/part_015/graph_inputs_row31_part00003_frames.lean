module
prelude
public import GraphInputsRow31Part00003Data
public import RawFrameSupport
public import SharedFrameGroups001Checked
public import SharedFrameGroups002Checked
public import SharedFrameGroups006Checked
public import SharedFrameGroups010Checked
public import SharedFrameGroups013Checked
public import SharedFrameGroups020Checked
public import SharedFrameGroups025Checked
public import SharedFrameGroups026Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups064Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups079Checked
public import SharedFrameGroups080Checked
public import SharedFrameGroups081Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups095Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups104Checked
public import SharedFrameGroups105Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x3c21dbaea770eb79da62d0766db35d96cc9462db0f1852c0f5d42e596e0b48593abc958cab5539a8f1454a044ee26ed30c95a4a4a41d1928b4457a261126876439a1350527f43ed1f24f687523a09c74df26dc3551a0ccee6332fe97b0b905a42c39554a5c52226f128c91c48923a11c08023ba1bf0ca86062f014489e44b422d10687c834c1960bb852825410f06882c0138095049023811808a03481680ac05502a014806202200f007403801b00c005c02a01000680240100070018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x1a2b40e7ace19af19e13bff7fafb5f2bd5796f15dfb8b706dd5acb47646c0d7cacf552a4d3ca5746e834f29d333645c668b90d215419831042054017f6fe1fabda7a8f25debb073ee41c43726cad6da734366ec998cb135fab2157aaa518a1d2d246458840ff1f838e6f0d518e2f659c9c92e2323fc768db128240440851062003f07c0c6158290510a01381882203c0740e01b03005c0a81001a0240400700600800800 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x13e2784e69ab33a554999132224247d8ef1c636c698ab1422643f86d0a60d415800fe1fa3ee7c0f55e53bd76ae85c1b736ded75acb4d698d059cb2c64ac898f3055febf179ae85b2b29622ae548a854ca8d4fe9c933a604988c110a1e418824f59d337666cc51842be558a513c25e4787f0f81ce340630bb1282204087f0fa1e83c0760ba1482704d0981281682203c0740e01b03005c0a81001a0240400700600800800 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x420a09900f7b33c45b64d2665732b190ec6061530257f4be05b62d65662b045702a914eca6450f278539e9a94c0257924a8fc476229d0547f53f49ec4f4e77a3bc1d4ce586f636a9b18d5863831297f4ba05ac2b81508a604ea256926c8ea44c2150fc47903b81b98bd85822b513e89cc46e22210707c43c81de0d986b033c18a0bd85b829414309a848422410506882c0138095049023811808a03481680ac05502a014806202200f007403801b00c005c02a01000680240100070018008002000 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record000_frame004_links_0000 record000_frame004_links_0064)
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x8f58ee8e38b38a88448207fe7fc7ee7e47d07c67b97af77976f75573a72770b6ef6e76b768e6836646476316125f35e95b156c55354c53252c51b51950b5014ed4e34d64cc49448946a44d4374183f93ef3b738b38136734c33931d3012f92c928927026924f24921e20b1f91dd1d01ca1a019818717116115312e1261150ff0ef0e10be0aa09c09509208e08c08a06905a05605505405203102201e01d01c01b01801701501000d009008007003002001000 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record000_frame005_links_0000 record000_frame005_links_0064)
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
def record000_frame006_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x151e9fd3ba4d482744cc9652c255ca593b2624948e8f71d636c618b11161a43083d03e03bfe7e6fb5ee3cb78aeb9c23706dad45a6b4067ecdd98b2c64cc858eb0860abe9742df59eb115f2ac538a5945a7c4de9852ba53478848fd1f63bc76cdc9a732a5f4b916b2a052ca092d23e4487e0f61d2358638bb130248440851041f83e07a0c01482704d0981281802203c0740e01b03005c0a81001a0240400700600800800 } : Fields).get c.val)
theorem record000_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record000_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record000) (record000.maps 6)
      (record000.inverseMaps 6) record000_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record000_frame006_links_0000 record000_frame006_links_0064)
theorem record000_frame006_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 6 :=
  of_group record000 6 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record000_frame006_indices record000_frame006_graph record000_frame006_links
def record000_frame007_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x154aa5d46a5949a774d697f2f65e4b69672b653c9f9212324347e8f31ae2fc5b8930fe1cc2e84506602bf57dcf55d539a72cdf1bbb666cad89aeb5b6a8d35a4334660c89883065ecbb1732cc584af95aaa8540a594828b4f49451d235442874ff9e63ac6e4d69a63065e8b895a2924e08910c1fc3906b0c612c238440831021f83e07b0c01442704d09812c1682103c0740e01b03005c0a81001a0240400700600800800 } : Fields).get c.val)
theorem record000_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record000_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record000) (record000.maps 7)
      (record000.inverseMaps 7) record000_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record000_frame007_links_0000 record000_frame007_links_0064)
theorem record000_frame007_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 7 :=
  of_group record000 7 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record000_frame007_indices record000_frame007_graph record000_frame007_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (Fin.cases (record000_frame006_supported hcells) (Fin.cases (record000_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x76eba95c76e1d6f2b5eda62d08679b3b59b4cc963fb169878c0c5d52e616ccaed565aad14eea3e51627e930295f4a4242d19089a448a1d90e684d4041f68f3e7523a09c74df26dc33f18a0bfa5ec2e41690b0e529269928c91c48922990fc8724252008f8c7ae37e1a10ca06062f01560a7051627b137896846e20d0f787243721a80cc06302ee15409504301ce0e1068825412408d046022c10c06f03481800b405702a81500a404501900c404602200f007403801b00a804001a0080038008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0xba7732dfdbab6f6a2c1568aaf53ea2d41a694b29251ba114127b4d198b2de524959232062fc548910d2013d2788edddabac73ee59c5b7a6ecda1aa34965ac4183b015ecb8d6c2bb53e9d12c25244e8750d2114087e4f99d53806d0d39a030c5f8ba96d2cc580a693523e450869062003e4798e81ac324588aa13c21c428811001fc3d8690c61682a05109e138260430640c41182203c0740e01b02a0400680800e00800800 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x86e85f83e8338268037c179377c77276676174e7427387287066fd6f06c66b66a968d67366b65561b6075f65d158354052e51c51a5104fe4ee4d74b64b049d48447044140a3fc3f63e53ce3be3a237a33931430b2d12c72c42bc2af2a329b27125024323222a2081fd1f21e81df1d31c21a218917316715b15314913d1221060f30d00c70b508f08c08708608508106c06605d05705405205104f04403103002302201e01d01c01b01501000d008007002001000 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0864.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0864.count (({ width := 11, code := 0x1336654c497b2ea5a4a994f2864fc9992323640c7a8e31be34c678bf15624c3682cfa5f3bde7aaf41e13b2758e61c7b696b2d3da033264cc918f31c628c29802fb5e4b9d72ad658cb01562a25229f12ca1940e810f69e73ba754e79ce392708de1b53646b4d31a032e648c09792e2578ab9452764b48f90d1fe3c46f8dc18a3004c8971222203d0780d8198320610bc1442684c0961241e82f0540a01202203c0740e01801a0240400700600800800 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0864
    Papers.RationalityTen.SharedFrameCatalogue.group0864_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1cb2e4c7233905c80e3c71ab8a5c3ce1d70737e9bdedee6efb689b2cd766b5353da98d466a034e9a44d0f670337999acbb65531dd8eac6462931057a2bc25cdae316fcb775b8ada96c6b2b58babf15d6adc566aadd538a8b53e29b54ae9c64dba6953269614a9250125c90d48323f91ee8d545fa2a112286442a210906482440a2008fe47a53c81d64e887313959c94e3c7173739b50d6e6a734b9a1cce265632318d8c4c6102ca9620af256a2a014cca4851527d13d49de4ea26992fc95a49b23b91ac8bc45222410f085e4231b78c3c5ec2f013c892c47821110105ac2be13a09704981f00e806e834c1980cb06483201800bf0550290134013009003c01c00a0048008002000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame001_links_0000 (interval_append _ 64 128 162 record004_frame001_links_0064 record004_frame001_links_0128))
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1069.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1069.count (({ width := 10, code := 0xfb7ebfa3e6f97e2f7fdcf6bd9f5bd2f43cff33c9f1fc6f13c0effbbedfb3ebbacea3a7e8f9fe6f93e4b8ee2b86df77add772db368d9761d7758d574fd2f48d1340ceb36ccf2fcaf22c7717c4703bfaf8bcae7b8edeb66d2b36c7b06b6acaadaa2a4a829ba5a8ca1a7c9da6e9ae6798e5e9564f91e449023c8de308b6298962086212836077e9f47bde977ddc761d573dc9711be6d1b16b5aa69da46819d5c5494e935441013f0f03acc22ecab2909e2448a210812007f1f87d1f07b1e0731b4130480f0380a0240200400 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame002_links_0000 (interval_append _ 64 128 162 record004_frame002_links_0064 record004_frame002_links_0128))
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1069
    Papers.RationalityTen.SharedFrameCatalogue.group1069_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1ab2d576aab54daa4d506a4b515a84d4169fb4dda64d31696b3d99e8ce8671332d990cc165ab2b992ac8e638b1b58c4c536243099848c176052ff5700b7b5b32d85690b3c597ac8d628afc57aab6559aac055a2a9d520a8553ca9b94c09c84dd26ad33a9714afa53927891e48323b11ac8b6452224d10286442720d904280e3fc1f80f947913c61db8ed27533a49cf4e667263849c08dd06dd3671b0cd6669d3471a00ce26612f09754b945be2ce9640b025742ae9528a7052a28713fc9e04e126492d894849624491d88c64541de8d8864e31515c09fc4da23411106142ea14109884841e60e606c03241820c005f02f416c0b50530290134013009003c01c00a0048008002000 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame003_links_0000 (interval_append _ 64 128 162 record004_frame003_links_0064 record004_frame003_links_0128))
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
def record004_frame004_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0907.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0907.count (({ width := 9, code := 0x2f579bc5deed75b9dc2dd6db65aad167b358ac15eae56ab157ab556a953a8d429d4da5d2a9347a35128541a04fe7d3d9e4ee75389bcd6693298cbe5b2c954a64f23914823f1d8e46a33178b452251087436170983c160702803f9f8f57a3c1deec75ba9d2e87137db6d86b34da2ce663258ec45d2dd6ab3572ad52a7522853c9c4ca592a934823516894421906813d9d8e47034998c8612f960ac51279389649239148441200fc783b1b8d868110803c1c0a048080200 } : Fields).get c.val)
theorem record004_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0907.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0907.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0907.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0907.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0907.localPairCheck (smallEmbedding record004) (record004.maps 4)
      (record004.inverseMaps 4) record004_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame004_links_0000 (interval_append _ 64 128 162 record004_frame004_links_0064 record004_frame004_links_0128))
theorem record004_frame004_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 4 :=
  of_group record004 4 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0907
    Papers.RationalityTen.SharedFrameCatalogue.group0907_facts record004_frame004_indices record004_frame004_graph record004_frame004_links
def record004_frame005_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0904.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0904.count (({ width := 8, code := 0xa1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0904.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0904.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0904.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0904.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0904.localPairCheck (smallEmbedding record004) (record004.maps 5)
      (record004.inverseMaps 5) record004_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame005_links_0000 (interval_append _ 64 128 162 record004_frame005_links_0064 record004_frame005_links_0128))
theorem record004_frame005_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 5 :=
  of_group record004 5 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0904
    Papers.RationalityTen.SharedFrameCatalogue.group0904_facts record004_frame005_indices record004_frame005_graph record004_frame005_links
def record004_frame006_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0901.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0901.count (({ width := 8, code := 0xa1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0901.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0901.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0901.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0901.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0901.localPairCheck (smallEmbedding record004) (record004.maps 6)
      (record004.inverseMaps 6) record004_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame006_links_0000 (interval_append _ 64 128 162 record004_frame006_links_0064 record004_frame006_links_0128))
theorem record004_frame006_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 6 :=
  of_group record004 6 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0901
    Papers.RationalityTen.SharedFrameCatalogue.group0901_facts record004_frame006_indices record004_frame006_graph record004_frame006_links
def record004_frame007_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0890.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0890.count (({ width := 8, code := 0xa1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0890.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0890.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0890.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0890.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0890.localPairCheck (smallEmbedding record004) (record004.maps 7)
      (record004.inverseMaps 7) record004_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame007_links_0000 (interval_append _ 64 128 162 record004_frame007_links_0064 record004_frame007_links_0128))
theorem record004_frame007_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 7 :=
  of_group record004 7 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0890
    Papers.RationalityTen.SharedFrameCatalogue.group0890_facts record004_frame007_indices record004_frame007_graph record004_frame007_links
def record004_frame008_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0889.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0889.count (({ width := 8, code := 0xa1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0889.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0889.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0889.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0889.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0889.localPairCheck (smallEmbedding record004) (record004.maps 8)
      (record004.inverseMaps 8) record004_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame008_links_0000 (interval_append _ 64 128 162 record004_frame008_links_0064 record004_frame008_links_0128))
theorem record004_frame008_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 8 :=
  of_group record004 8 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0889
    Papers.RationalityTen.SharedFrameCatalogue.group0889_facts record004_frame008_indices record004_frame008_graph record004_frame008_links
def record004_frame009_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0887.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0887.count (({ width := 8, code := 0xa1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0887.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0887.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0887.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0887.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0887.localPairCheck (smallEmbedding record004) (record004.maps 9)
      (record004.inverseMaps 9) record004_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame009_links_0000 (interval_append _ 64 128 162 record004_frame009_links_0064 record004_frame009_links_0128))
theorem record004_frame009_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 9 :=
  of_group record004 9 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0887
    Papers.RationalityTen.SharedFrameCatalogue.group0887_facts record004_frame009_indices record004_frame009_graph record004_frame009_links
def record004_frame010_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0886.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0886.count (({ width := 8, code := 0xa1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0886.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0886.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0886.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0886.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0886.localPairCheck (smallEmbedding record004) (record004.maps 10)
      (record004.inverseMaps 10) record004_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame010_links_0000 (interval_append _ 64 128 162 record004_frame010_links_0064 record004_frame010_links_0128))
theorem record004_frame010_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 10 :=
  of_group record004 10 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0886
    Papers.RationalityTen.SharedFrameCatalogue.group0886_facts record004_frame010_indices record004_frame010_graph record004_frame010_links
def record004_frame011_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0885.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0885.count (({ width := 8, code := 0xa1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0885.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0885.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0885.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0885.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0885.localPairCheck (smallEmbedding record004) (record004.maps 11)
      (record004.inverseMaps 11) record004_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame011_links_0000 (interval_append _ 64 128 162 record004_frame011_links_0064 record004_frame011_links_0128))
theorem record004_frame011_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 11 :=
  of_group record004 11 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0885
    Papers.RationalityTen.SharedFrameCatalogue.group0885_facts record004_frame011_indices record004_frame011_graph record004_frame011_links
def record004_frame012_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0883.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0883.count (({ width := 8, code := 0xd8d6d4d3d2d1cfcecccbcac8c6c5c3c0bebcbbb9b8b7b6b5b4b2b0afaeadacaaa9a8a7a6a5a3a09e9d9c9b9a99979594939291908f8d8b89878584838281807f7e7d7c7b7a7978777675747372716f6d6c6b696664636261605f5d5b5a595857565553514f4d4b4a494847464544434241403f3e3d3c3b3a39383735333231302e2d2c2a29272524232221201f1e1d1c1b1a17161514131211090807060504020100 } : Fields).get c.val)
theorem record004_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0883.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0883.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0883.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0883.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0883.localPairCheck (smallEmbedding record004) (record004.maps 12)
      (record004.inverseMaps 12) record004_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame012_links_0000 (interval_append _ 64 128 162 record004_frame012_links_0064 record004_frame012_links_0128))
theorem record004_frame012_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 12 :=
  of_group record004 12 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0883
    Papers.RationalityTen.SharedFrameCatalogue.group0883_facts record004_frame012_indices record004_frame012_graph record004_frame012_links
def record004_frame013_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1010.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1010.count (({ width := 8, code := 0xa1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1010.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1010.localPairCheck (smallEmbedding record004) (record004.maps 13) (record004.inverseMaps 13) record004_frame013_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1010.localPairCheck (smallEmbedding record004) (record004.maps 13) (record004.inverseMaps 13) record004_frame013_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1010.localPairCheck (smallEmbedding record004) (record004.maps 13) (record004.inverseMaps 13) record004_frame013_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1010.localPairCheck (smallEmbedding record004) (record004.maps 13)
      (record004.inverseMaps 13) record004_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame013_links_0000 (interval_append _ 64 128 162 record004_frame013_links_0064 record004_frame013_links_0128))
theorem record004_frame013_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 13 :=
  of_group record004 13 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1010
    Papers.RationalityTen.SharedFrameCatalogue.group1010_facts record004_frame013_indices record004_frame013_graph record004_frame013_links
def record004_frame014_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1009.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1009.count (({ width := 8, code := 0xa1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1009.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1009.localPairCheck (smallEmbedding record004) (record004.maps 14) (record004.inverseMaps 14) record004_frame014_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1009.localPairCheck (smallEmbedding record004) (record004.maps 14) (record004.inverseMaps 14) record004_frame014_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1009.localPairCheck (smallEmbedding record004) (record004.maps 14) (record004.inverseMaps 14) record004_frame014_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1009.localPairCheck (smallEmbedding record004) (record004.maps 14)
      (record004.inverseMaps 14) record004_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame014_links_0000 (interval_append _ 64 128 162 record004_frame014_links_0064 record004_frame014_links_0128))
theorem record004_frame014_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 14 :=
  of_group record004 14 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1009
    Papers.RationalityTen.SharedFrameCatalogue.group1009_facts record004_frame014_indices record004_frame014_graph record004_frame014_links
def record004_frame015_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1008.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1008.count (({ width := 8, code := 0xa1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1008.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1008.localPairCheck (smallEmbedding record004) (record004.maps 15) (record004.inverseMaps 15) record004_frame015_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1008.localPairCheck (smallEmbedding record004) (record004.maps 15) (record004.inverseMaps 15) record004_frame015_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1008.localPairCheck (smallEmbedding record004) (record004.maps 15) (record004.inverseMaps 15) record004_frame015_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1008.localPairCheck (smallEmbedding record004) (record004.maps 15)
      (record004.inverseMaps 15) record004_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame015_links_0000 (interval_append _ 64 128 162 record004_frame015_links_0064 record004_frame015_links_0128))
theorem record004_frame015_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 15 :=
  of_group record004 15 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1008
    Papers.RationalityTen.SharedFrameCatalogue.group1008_facts record004_frame015_indices record004_frame015_graph record004_frame015_links
def record004_frame016_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0876.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0876.count (({ width := 8, code := 0xa1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0876.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0876.localPairCheck (smallEmbedding record004) (record004.maps 16) (record004.inverseMaps 16) record004_frame016_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0876.localPairCheck (smallEmbedding record004) (record004.maps 16) (record004.inverseMaps 16) record004_frame016_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0876.localPairCheck (smallEmbedding record004) (record004.maps 16) (record004.inverseMaps 16) record004_frame016_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0876.localPairCheck (smallEmbedding record004) (record004.maps 16)
      (record004.inverseMaps 16) record004_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame016_links_0000 (interval_append _ 64 128 162 record004_frame016_links_0064 record004_frame016_links_0128))
theorem record004_frame016_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 16 :=
  of_group record004 16 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0876
    Papers.RationalityTen.SharedFrameCatalogue.group0876_facts record004_frame016_indices record004_frame016_graph record004_frame016_links
def record004_frame017_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0875.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0875.count (({ width := 8, code := 0xa1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0875.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0875.localPairCheck (smallEmbedding record004) (record004.maps 17) (record004.inverseMaps 17) record004_frame017_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0875.localPairCheck (smallEmbedding record004) (record004.maps 17) (record004.inverseMaps 17) record004_frame017_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0875.localPairCheck (smallEmbedding record004) (record004.maps 17) (record004.inverseMaps 17) record004_frame017_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0875.localPairCheck (smallEmbedding record004) (record004.maps 17)
      (record004.inverseMaps 17) record004_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame017_links_0000 (interval_append _ 64 128 162 record004_frame017_links_0064 record004_frame017_links_0128))
theorem record004_frame017_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 17 :=
  of_group record004 17 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0875
    Papers.RationalityTen.SharedFrameCatalogue.group0875_facts record004_frame017_indices record004_frame017_graph record004_frame017_links
def record004_frame018_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0874.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0874.count (({ width := 8, code := 0xa1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0874.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0874.localPairCheck (smallEmbedding record004) (record004.maps 18) (record004.inverseMaps 18) record004_frame018_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0874.localPairCheck (smallEmbedding record004) (record004.maps 18) (record004.inverseMaps 18) record004_frame018_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0874.localPairCheck (smallEmbedding record004) (record004.maps 18) (record004.inverseMaps 18) record004_frame018_indices (Fin.ofNat record004.n i)) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem record004_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0874.localPairCheck (smallEmbedding record004) (record004.maps 18)
      (record004.inverseMaps 18) record004_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 162 record004_frame018_links_0000 (interval_append _ 64 128 162 record004_frame018_links_0064 record004_frame018_links_0128))
theorem record004_frame018_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 18 :=
  of_group record004 18 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0874
    Papers.RationalityTen.SharedFrameCatalogue.group0874_facts record004_frame018_indices record004_frame018_graph record004_frame018_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (Fin.cases (record004_frame004_supported hcells) (Fin.cases (record004_frame005_supported hcells) (Fin.cases (record004_frame006_supported hcells) (Fin.cases (record004_frame007_supported hcells) (Fin.cases (record004_frame008_supported hcells) (Fin.cases (record004_frame009_supported hcells) (Fin.cases (record004_frame010_supported hcells) (Fin.cases (record004_frame011_supported hcells) (Fin.cases (record004_frame012_supported hcells) (Fin.cases (record004_frame013_supported hcells) (Fin.cases (record004_frame014_supported hcells) (Fin.cases (record004_frame015_supported hcells) (Fin.cases (record004_frame016_supported hcells) (Fin.cases (record004_frame017_supported hcells) (Fin.cases (record004_frame018_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x3965c98e46720b901c78e35714b879c3ae0e6fd37bdbdcddf6d1b5ddaa6d486a2b501a46cee668332d976c85633b1898a4bd85d12e156f0b715b3ace1612aed56e2b05552a8d53e29853a89b64d2a5bd2a2940486a4151fe8f747622f915086442921110648244092010fe47a53c81d64e887313959c94e3c7173739b50d6e6a734b9a1cce265632318d8c4c6102c495e4a6852427d13b89d44c525691dc8b645222410b08463a31bc8d0c6322ff17b8bc058228712f093847822410a08082d215f09c04b824c0f607403741a60cc06583241900c005f82a414609904181f40e6028012007c02400e0048008002000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame001_links_0000 (interval_append _ 64 128 147 record005_frame001_links_0064 record005_frame001_links_0128))
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x3b35d84eb6755baa9d3ee8773db9c1cdee647293935c98e47708b77db6cd9d6cd362da8cd1d68234059e4cba657b2ad94cc496042fad798bb85cbad99692b2a58b2bd55b8ad05642af9472a0a4f926c531897d4a2a4bd24090c47f236519489243e21b50b284d422a0fd06e7f33f01ec4f447873ba1d84e9c7343839be0dba6ca35b9a90d1467633819a4cc465a2e616e4ace55829594209fc4da26592788f6471233916c8ae3c51c78d506563021780b6c56628a130893c47422c11208702ce15609704902300f1073836c1a40ce06683281920c106002a414609904181f40e6028012007c02400e0048008002000 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame002_links_0000 (interval_append _ 64 128 147 record005_frame002_links_0064 record005_frame002_links_0128))
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0x101e02c027feff9fdbf87eafc9f8bee7d4f9df33e37bef6dec3d37a2f39e1bc0776ee5db3ac74ee95d139571ce21c137e6f0dc5b5b656c2d6daab4f696d159e33465ec698930d5f0bcd782ea5ccb796cac457eaf15b2b255aaa95229a528a294227c4f29d538a6c4c69752aa5249c92922a3e4768dd19a2e444875019fe3d678cf09d73a46fcdb9b53646a8d41952fe5a8aa1462824ec971182144147f8f91e83b8608bb1542904f090114210408800fe1f83e87c0f61e03a06f0ca1802d0260440740900e01200800800 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame003_links_0000 (interval_append _ 64 128 147 record005_frame003_links_0064 record005_frame003_links_0128))
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
def record005_frame004_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x121e42c7d8f51e63c4768e31ae354698cd18e314608a513a254428810fe1a42f84f09a1141681902e043e17b4f55e7bcc786ef1dc3b6766eb1d2b9f736e49b83676c6d59a6b49678ce199b2e650c858f30f614c157fafa5eabc174ad65a6b2d62abe56aac555aa4536a5d472875029f53a26c4ca97d2ca5243e865019ff3e4790f09d03966f0d59a834665cca9782c6550a393a2644a4909162144087c8f31da3945f0bb1622b05409e1342584a8921222384688810e1f43d8770d81a8320260440740900e01200800800 } : Fields).get c.val)
theorem record005_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record005) (record005.maps 4)
      (record005.inverseMaps 4) record005_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame004_links_0000 (interval_append _ 64 128 147 record005_frame004_links_0064 record005_frame004_links_0128))
theorem record005_frame004_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 4 :=
  of_group record005 4 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record005_frame004_indices record005_frame004_graph record005_frame004_links
def record005_frame005_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0790.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0790.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0790.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0790.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0790.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0790.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0790.localPairCheck (smallEmbedding record005) (record005.maps 5)
      (record005.inverseMaps 5) record005_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame005_links_0000 (interval_append _ 64 128 147 record005_frame005_links_0064 record005_frame005_links_0128))
theorem record005_frame005_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 5 :=
  of_group record005 5 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0790
    Papers.RationalityTen.SharedFrameCatalogue.group0790_facts record005_frame005_indices record005_frame005_graph record005_frame005_links
def record005_frame006_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0788.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0788.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0788.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0788.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0788.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0788.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0788.localPairCheck (smallEmbedding record005) (record005.maps 6)
      (record005.inverseMaps 6) record005_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame006_links_0000 (interval_append _ 64 128 147 record005_frame006_links_0064 record005_frame006_links_0128))
theorem record005_frame006_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 6 :=
  of_group record005 6 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0788
    Papers.RationalityTen.SharedFrameCatalogue.group0788_facts record005_frame006_indices record005_frame006_graph record005_frame006_links
def record005_frame007_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0789.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0789.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0789.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0789.localPairCheck (smallEmbedding record005) (record005.maps 7) (record005.inverseMaps 7) record005_frame007_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0789.localPairCheck (smallEmbedding record005) (record005.maps 7) (record005.inverseMaps 7) record005_frame007_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0789.localPairCheck (smallEmbedding record005) (record005.maps 7) (record005.inverseMaps 7) record005_frame007_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0789.localPairCheck (smallEmbedding record005) (record005.maps 7)
      (record005.inverseMaps 7) record005_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame007_links_0000 (interval_append _ 64 128 147 record005_frame007_links_0064 record005_frame007_links_0128))
theorem record005_frame007_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 7 :=
  of_group record005 7 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0789
    Papers.RationalityTen.SharedFrameCatalogue.group0789_facts record005_frame007_indices record005_frame007_graph record005_frame007_links
def record005_frame008_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0786.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0786.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0786.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0786.localPairCheck (smallEmbedding record005) (record005.maps 8) (record005.inverseMaps 8) record005_frame008_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0786.localPairCheck (smallEmbedding record005) (record005.maps 8) (record005.inverseMaps 8) record005_frame008_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0786.localPairCheck (smallEmbedding record005) (record005.maps 8) (record005.inverseMaps 8) record005_frame008_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0786.localPairCheck (smallEmbedding record005) (record005.maps 8)
      (record005.inverseMaps 8) record005_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame008_links_0000 (interval_append _ 64 128 147 record005_frame008_links_0064 record005_frame008_links_0128))
theorem record005_frame008_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 8 :=
  of_group record005 8 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0786
    Papers.RationalityTen.SharedFrameCatalogue.group0786_facts record005_frame008_indices record005_frame008_graph record005_frame008_links
def record005_frame009_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0787.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0787.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0787.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0787.localPairCheck (smallEmbedding record005) (record005.maps 9) (record005.inverseMaps 9) record005_frame009_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0787.localPairCheck (smallEmbedding record005) (record005.maps 9) (record005.inverseMaps 9) record005_frame009_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0787.localPairCheck (smallEmbedding record005) (record005.maps 9) (record005.inverseMaps 9) record005_frame009_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0787.localPairCheck (smallEmbedding record005) (record005.maps 9)
      (record005.inverseMaps 9) record005_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame009_links_0000 (interval_append _ 64 128 147 record005_frame009_links_0064 record005_frame009_links_0128))
theorem record005_frame009_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 9 :=
  of_group record005 9 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0787
    Papers.RationalityTen.SharedFrameCatalogue.group0787_facts record005_frame009_indices record005_frame009_graph record005_frame009_links
def record005_frame010_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0312.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0312.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0312.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0312.localPairCheck (smallEmbedding record005) (record005.maps 10) (record005.inverseMaps 10) record005_frame010_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0312.localPairCheck (smallEmbedding record005) (record005.maps 10) (record005.inverseMaps 10) record005_frame010_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0312.localPairCheck (smallEmbedding record005) (record005.maps 10) (record005.inverseMaps 10) record005_frame010_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0312.localPairCheck (smallEmbedding record005) (record005.maps 10)
      (record005.inverseMaps 10) record005_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame010_links_0000 (interval_append _ 64 128 147 record005_frame010_links_0064 record005_frame010_links_0128))
theorem record005_frame010_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 10 :=
  of_group record005 10 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0312
    Papers.RationalityTen.SharedFrameCatalogue.group0312_facts record005_frame010_indices record005_frame010_graph record005_frame010_links
def record005_frame011_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0311.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0311.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0311.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0311.localPairCheck (smallEmbedding record005) (record005.maps 11) (record005.inverseMaps 11) record005_frame011_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0311.localPairCheck (smallEmbedding record005) (record005.maps 11) (record005.inverseMaps 11) record005_frame011_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0311.localPairCheck (smallEmbedding record005) (record005.maps 11) (record005.inverseMaps 11) record005_frame011_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0311.localPairCheck (smallEmbedding record005) (record005.maps 11)
      (record005.inverseMaps 11) record005_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame011_links_0000 (interval_append _ 64 128 147 record005_frame011_links_0064 record005_frame011_links_0128))
theorem record005_frame011_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 11 :=
  of_group record005 11 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0311
    Papers.RationalityTen.SharedFrameCatalogue.group0311_facts record005_frame011_indices record005_frame011_graph record005_frame011_links
def record005_frame012_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0398.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0398.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0398.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0398.localPairCheck (smallEmbedding record005) (record005.maps 12) (record005.inverseMaps 12) record005_frame012_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0398.localPairCheck (smallEmbedding record005) (record005.maps 12) (record005.inverseMaps 12) record005_frame012_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0398.localPairCheck (smallEmbedding record005) (record005.maps 12) (record005.inverseMaps 12) record005_frame012_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0398.localPairCheck (smallEmbedding record005) (record005.maps 12)
      (record005.inverseMaps 12) record005_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame012_links_0000 (interval_append _ 64 128 147 record005_frame012_links_0064 record005_frame012_links_0128))
theorem record005_frame012_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 12 :=
  of_group record005 12 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0398
    Papers.RationalityTen.SharedFrameCatalogue.group0398_facts record005_frame012_indices record005_frame012_graph record005_frame012_links
def record005_frame013_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0397.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0397.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0397.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0397.localPairCheck (smallEmbedding record005) (record005.maps 13) (record005.inverseMaps 13) record005_frame013_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0397.localPairCheck (smallEmbedding record005) (record005.maps 13) (record005.inverseMaps 13) record005_frame013_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0397.localPairCheck (smallEmbedding record005) (record005.maps 13) (record005.inverseMaps 13) record005_frame013_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0397.localPairCheck (smallEmbedding record005) (record005.maps 13)
      (record005.inverseMaps 13) record005_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame013_links_0000 (interval_append _ 64 128 147 record005_frame013_links_0064 record005_frame013_links_0128))
theorem record005_frame013_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 13 :=
  of_group record005 13 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0397
    Papers.RationalityTen.SharedFrameCatalogue.group0397_facts record005_frame013_indices record005_frame013_graph record005_frame013_links
def record005_frame014_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0396.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0396.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0396.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0396.localPairCheck (smallEmbedding record005) (record005.maps 14) (record005.inverseMaps 14) record005_frame014_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0396.localPairCheck (smallEmbedding record005) (record005.maps 14) (record005.inverseMaps 14) record005_frame014_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0396.localPairCheck (smallEmbedding record005) (record005.maps 14) (record005.inverseMaps 14) record005_frame014_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0396.localPairCheck (smallEmbedding record005) (record005.maps 14)
      (record005.inverseMaps 14) record005_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame014_links_0000 (interval_append _ 64 128 147 record005_frame014_links_0064 record005_frame014_links_0128))
theorem record005_frame014_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 14 :=
  of_group record005 14 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0396
    Papers.RationalityTen.SharedFrameCatalogue.group0396_facts record005_frame014_indices record005_frame014_graph record005_frame014_links
def record005_frame015_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0157.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0157.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0157.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0157.localPairCheck (smallEmbedding record005) (record005.maps 15) (record005.inverseMaps 15) record005_frame015_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0157.localPairCheck (smallEmbedding record005) (record005.maps 15) (record005.inverseMaps 15) record005_frame015_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0157.localPairCheck (smallEmbedding record005) (record005.maps 15) (record005.inverseMaps 15) record005_frame015_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0157.localPairCheck (smallEmbedding record005) (record005.maps 15)
      (record005.inverseMaps 15) record005_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame015_links_0000 (interval_append _ 64 128 147 record005_frame015_links_0064 record005_frame015_links_0128))
theorem record005_frame015_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 15 :=
  of_group record005 15 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0157
    Papers.RationalityTen.SharedFrameCatalogue.group0157_facts record005_frame015_indices record005_frame015_graph record005_frame015_links
def record005_frame016_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0204.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0204.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0204.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0204.localPairCheck (smallEmbedding record005) (record005.maps 16) (record005.inverseMaps 16) record005_frame016_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0204.localPairCheck (smallEmbedding record005) (record005.maps 16) (record005.inverseMaps 16) record005_frame016_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0204.localPairCheck (smallEmbedding record005) (record005.maps 16) (record005.inverseMaps 16) record005_frame016_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0204.localPairCheck (smallEmbedding record005) (record005.maps 16)
      (record005.inverseMaps 16) record005_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame016_links_0000 (interval_append _ 64 128 147 record005_frame016_links_0064 record005_frame016_links_0128))
theorem record005_frame016_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 16 :=
  of_group record005 16 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0204
    Papers.RationalityTen.SharedFrameCatalogue.group0204_facts record005_frame016_indices record005_frame016_graph record005_frame016_links
def record005_frame017_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0202.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0202.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0202.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0202.localPairCheck (smallEmbedding record005) (record005.maps 17) (record005.inverseMaps 17) record005_frame017_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0202.localPairCheck (smallEmbedding record005) (record005.maps 17) (record005.inverseMaps 17) record005_frame017_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0202.localPairCheck (smallEmbedding record005) (record005.maps 17) (record005.inverseMaps 17) record005_frame017_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0202.localPairCheck (smallEmbedding record005) (record005.maps 17)
      (record005.inverseMaps 17) record005_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame017_links_0000 (interval_append _ 64 128 147 record005_frame017_links_0064 record005_frame017_links_0128))
theorem record005_frame017_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 17 :=
  of_group record005 17 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0202
    Papers.RationalityTen.SharedFrameCatalogue.group0202_facts record005_frame017_indices record005_frame017_graph record005_frame017_links
def record005_frame018_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0203.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0203.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0203.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0203.localPairCheck (smallEmbedding record005) (record005.maps 18) (record005.inverseMaps 18) record005_frame018_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0203.localPairCheck (smallEmbedding record005) (record005.maps 18) (record005.inverseMaps 18) record005_frame018_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0203.localPairCheck (smallEmbedding record005) (record005.maps 18) (record005.inverseMaps 18) record005_frame018_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0203.localPairCheck (smallEmbedding record005) (record005.maps 18)
      (record005.inverseMaps 18) record005_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame018_links_0000 (interval_append _ 64 128 147 record005_frame018_links_0064 record005_frame018_links_0128))
theorem record005_frame018_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 18 :=
  of_group record005 18 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0203
    Papers.RationalityTen.SharedFrameCatalogue.group0203_facts record005_frame018_indices record005_frame018_graph record005_frame018_links
def record005_frame019_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0201.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0201.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0201.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0201.localPairCheck (smallEmbedding record005) (record005.maps 19) (record005.inverseMaps 19) record005_frame019_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0201.localPairCheck (smallEmbedding record005) (record005.maps 19) (record005.inverseMaps 19) record005_frame019_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0201.localPairCheck (smallEmbedding record005) (record005.maps 19) (record005.inverseMaps 19) record005_frame019_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0201.localPairCheck (smallEmbedding record005) (record005.maps 19)
      (record005.inverseMaps 19) record005_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame019_links_0000 (interval_append _ 64 128 147 record005_frame019_links_0064 record005_frame019_links_0128))
theorem record005_frame019_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 19 :=
  of_group record005 19 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0201
    Papers.RationalityTen.SharedFrameCatalogue.group0201_facts record005_frame019_indices record005_frame019_graph record005_frame019_links
def record005_frame020_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0025.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0025.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0025.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0025.localPairCheck (smallEmbedding record005) (record005.maps 20) (record005.inverseMaps 20) record005_frame020_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0025.localPairCheck (smallEmbedding record005) (record005.maps 20) (record005.inverseMaps 20) record005_frame020_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0025.localPairCheck (smallEmbedding record005) (record005.maps 20) (record005.inverseMaps 20) record005_frame020_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0025.localPairCheck (smallEmbedding record005) (record005.maps 20)
      (record005.inverseMaps 20) record005_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame020_links_0000 (interval_append _ 64 128 147 record005_frame020_links_0064 record005_frame020_links_0128))
theorem record005_frame020_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 20 :=
  of_group record005 20 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0025
    Papers.RationalityTen.SharedFrameCatalogue.group0025_facts record005_frame020_indices record005_frame020_graph record005_frame020_links
def record005_frame021_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0024.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0024.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0024.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0024.localPairCheck (smallEmbedding record005) (record005.maps 21) (record005.inverseMaps 21) record005_frame021_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0024.localPairCheck (smallEmbedding record005) (record005.maps 21) (record005.inverseMaps 21) record005_frame021_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0024.localPairCheck (smallEmbedding record005) (record005.maps 21) (record005.inverseMaps 21) record005_frame021_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0024.localPairCheck (smallEmbedding record005) (record005.maps 21)
      (record005.inverseMaps 21) record005_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame021_links_0000 (interval_append _ 64 128 147 record005_frame021_links_0064 record005_frame021_links_0128))
theorem record005_frame021_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 21 :=
  of_group record005 21 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0024
    Papers.RationalityTen.SharedFrameCatalogue.group0024_facts record005_frame021_indices record005_frame021_graph record005_frame021_links
def record005_frame022_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0023.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0023.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0023.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0023.localPairCheck (smallEmbedding record005) (record005.maps 22) (record005.inverseMaps 22) record005_frame022_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0023.localPairCheck (smallEmbedding record005) (record005.maps 22) (record005.inverseMaps 22) record005_frame022_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0023.localPairCheck (smallEmbedding record005) (record005.maps 22) (record005.inverseMaps 22) record005_frame022_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0023.localPairCheck (smallEmbedding record005) (record005.maps 22)
      (record005.inverseMaps 22) record005_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame022_links_0000 (interval_append _ 64 128 147 record005_frame022_links_0064 record005_frame022_links_0128))
theorem record005_frame022_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 22 :=
  of_group record005 22 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0023
    Papers.RationalityTen.SharedFrameCatalogue.group0023_facts record005_frame022_indices record005_frame022_graph record005_frame022_links
def record005_frame023_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0093.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0093.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0093.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0093.localPairCheck (smallEmbedding record005) (record005.maps 23) (record005.inverseMaps 23) record005_frame023_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0093.localPairCheck (smallEmbedding record005) (record005.maps 23) (record005.inverseMaps 23) record005_frame023_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0093.localPairCheck (smallEmbedding record005) (record005.maps 23) (record005.inverseMaps 23) record005_frame023_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0093.localPairCheck (smallEmbedding record005) (record005.maps 23)
      (record005.inverseMaps 23) record005_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame023_links_0000 (interval_append _ 64 128 147 record005_frame023_links_0064 record005_frame023_links_0128))
theorem record005_frame023_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 23 :=
  of_group record005 23 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0093
    Papers.RationalityTen.SharedFrameCatalogue.group0093_facts record005_frame023_indices record005_frame023_graph record005_frame023_links
def record005_frame024_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0091.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0091.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0091.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0091.localPairCheck (smallEmbedding record005) (record005.maps 24) (record005.inverseMaps 24) record005_frame024_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0091.localPairCheck (smallEmbedding record005) (record005.maps 24) (record005.inverseMaps 24) record005_frame024_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame024_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0091.localPairCheck (smallEmbedding record005) (record005.maps 24) (record005.inverseMaps 24) record005_frame024_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0091.localPairCheck (smallEmbedding record005) (record005.maps 24)
      (record005.inverseMaps 24) record005_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame024_links_0000 (interval_append _ 64 128 147 record005_frame024_links_0064 record005_frame024_links_0128))
theorem record005_frame024_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 24 :=
  of_group record005 24 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0091
    Papers.RationalityTen.SharedFrameCatalogue.group0091_facts record005_frame024_indices record005_frame024_graph record005_frame024_links
def record005_frame025_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0092.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0092.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0092.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0092.localPairCheck (smallEmbedding record005) (record005.maps 25) (record005.inverseMaps 25) record005_frame025_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0092.localPairCheck (smallEmbedding record005) (record005.maps 25) (record005.inverseMaps 25) record005_frame025_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame025_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0092.localPairCheck (smallEmbedding record005) (record005.maps 25) (record005.inverseMaps 25) record005_frame025_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0092.localPairCheck (smallEmbedding record005) (record005.maps 25)
      (record005.inverseMaps 25) record005_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame025_links_0000 (interval_append _ 64 128 147 record005_frame025_links_0064 record005_frame025_links_0128))
theorem record005_frame025_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 25 :=
  of_group record005 25 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0092
    Papers.RationalityTen.SharedFrameCatalogue.group0092_facts record005_frame025_indices record005_frame025_graph record005_frame025_links
def record005_frame026_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0089.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0089.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0089.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0089.localPairCheck (smallEmbedding record005) (record005.maps 26) (record005.inverseMaps 26) record005_frame026_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0089.localPairCheck (smallEmbedding record005) (record005.maps 26) (record005.inverseMaps 26) record005_frame026_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame026_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0089.localPairCheck (smallEmbedding record005) (record005.maps 26) (record005.inverseMaps 26) record005_frame026_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0089.localPairCheck (smallEmbedding record005) (record005.maps 26)
      (record005.inverseMaps 26) record005_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame026_links_0000 (interval_append _ 64 128 147 record005_frame026_links_0064 record005_frame026_links_0128))
theorem record005_frame026_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 26 :=
  of_group record005 26 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0089
    Papers.RationalityTen.SharedFrameCatalogue.group0089_facts record005_frame026_indices record005_frame026_graph record005_frame026_links
def record005_frame027_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0090.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0090.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame027_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0090.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame027_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0090.localPairCheck (smallEmbedding record005) (record005.maps 27) (record005.inverseMaps 27) record005_frame027_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame027_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0090.localPairCheck (smallEmbedding record005) (record005.maps 27) (record005.inverseMaps 27) record005_frame027_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame027_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0090.localPairCheck (smallEmbedding record005) (record005.maps 27) (record005.inverseMaps 27) record005_frame027_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame027_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0090.localPairCheck (smallEmbedding record005) (record005.maps 27)
      (record005.inverseMaps 27) record005_frame027_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame027_links_0000 (interval_append _ 64 128 147 record005_frame027_links_0064 record005_frame027_links_0128))
theorem record005_frame027_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 27 :=
  of_group record005 27 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0090
    Papers.RationalityTen.SharedFrameCatalogue.group0090_facts record005_frame027_indices record005_frame027_graph record005_frame027_links
def record005_frame028_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0016.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0016.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame028_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0016.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame028_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0016.localPairCheck (smallEmbedding record005) (record005.maps 28) (record005.inverseMaps 28) record005_frame028_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame028_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0016.localPairCheck (smallEmbedding record005) (record005.maps 28) (record005.inverseMaps 28) record005_frame028_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame028_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0016.localPairCheck (smallEmbedding record005) (record005.maps 28) (record005.inverseMaps 28) record005_frame028_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame028_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0016.localPairCheck (smallEmbedding record005) (record005.maps 28)
      (record005.inverseMaps 28) record005_frame028_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame028_links_0000 (interval_append _ 64 128 147 record005_frame028_links_0064 record005_frame028_links_0128))
theorem record005_frame028_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 28 :=
  of_group record005 28 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0016
    Papers.RationalityTen.SharedFrameCatalogue.group0016_facts record005_frame028_indices record005_frame028_graph record005_frame028_links
def record005_frame029_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0015.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0015.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame029_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0015.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame029_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0015.localPairCheck (smallEmbedding record005) (record005.maps 29) (record005.inverseMaps 29) record005_frame029_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame029_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0015.localPairCheck (smallEmbedding record005) (record005.maps 29) (record005.inverseMaps 29) record005_frame029_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame029_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0015.localPairCheck (smallEmbedding record005) (record005.maps 29) (record005.inverseMaps 29) record005_frame029_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame029_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0015.localPairCheck (smallEmbedding record005) (record005.maps 29)
      (record005.inverseMaps 29) record005_frame029_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame029_links_0000 (interval_append _ 64 128 147 record005_frame029_links_0064 record005_frame029_links_0128))
theorem record005_frame029_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 29 :=
  of_group record005 29 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0015
    Papers.RationalityTen.SharedFrameCatalogue.group0015_facts record005_frame029_indices record005_frame029_graph record005_frame029_links
def record005_frame030_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0014.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0014.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame030_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0014.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame030_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0014.localPairCheck (smallEmbedding record005) (record005.maps 30) (record005.inverseMaps 30) record005_frame030_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame030_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0014.localPairCheck (smallEmbedding record005) (record005.maps 30) (record005.inverseMaps 30) record005_frame030_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame030_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0014.localPairCheck (smallEmbedding record005) (record005.maps 30) (record005.inverseMaps 30) record005_frame030_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame030_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0014.localPairCheck (smallEmbedding record005) (record005.maps 30)
      (record005.inverseMaps 30) record005_frame030_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame030_links_0000 (interval_append _ 64 128 147 record005_frame030_links_0064 record005_frame030_links_0128))
theorem record005_frame030_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 30 :=
  of_group record005 30 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0014
    Papers.RationalityTen.SharedFrameCatalogue.group0014_facts record005_frame030_indices record005_frame030_graph record005_frame030_links
def record005_frame031_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0003.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0003.count (({ width := 8, code := 0x9291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame031_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0003.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame031_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0003.localPairCheck (smallEmbedding record005) (record005.maps 31) (record005.inverseMaps 31) record005_frame031_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame031_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0003.localPairCheck (smallEmbedding record005) (record005.maps 31) (record005.inverseMaps 31) record005_frame031_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame031_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0003.localPairCheck (smallEmbedding record005) (record005.maps 31) (record005.inverseMaps 31) record005_frame031_indices (Fin.ofNat record005.n i)) 128 147 :=
  interval_of_check _ 128 19 (by decide +kernel)
theorem record005_frame031_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0003.localPairCheck (smallEmbedding record005) (record005.maps 31)
      (record005.inverseMaps 31) record005_frame031_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 147 record005_frame031_links_0000 (interval_append _ 64 128 147 record005_frame031_links_0064 record005_frame031_links_0128))
theorem record005_frame031_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 31 :=
  of_group record005 31 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0003
    Papers.RationalityTen.SharedFrameCatalogue.group0003_facts record005_frame031_indices record005_frame031_graph record005_frame031_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (Fin.cases (record005_frame004_supported hcells) (Fin.cases (record005_frame005_supported hcells) (Fin.cases (record005_frame006_supported hcells) (Fin.cases (record005_frame007_supported hcells) (Fin.cases (record005_frame008_supported hcells) (Fin.cases (record005_frame009_supported hcells) (Fin.cases (record005_frame010_supported hcells) (Fin.cases (record005_frame011_supported hcells) (Fin.cases (record005_frame012_supported hcells) (Fin.cases (record005_frame013_supported hcells) (Fin.cases (record005_frame014_supported hcells) (Fin.cases (record005_frame015_supported hcells) (Fin.cases (record005_frame016_supported hcells) (Fin.cases (record005_frame017_supported hcells) (Fin.cases (record005_frame018_supported hcells) (Fin.cases (record005_frame019_supported hcells) (Fin.cases (record005_frame020_supported hcells) (Fin.cases (record005_frame021_supported hcells) (Fin.cases (record005_frame022_supported hcells) (Fin.cases (record005_frame023_supported hcells) (Fin.cases (record005_frame024_supported hcells) (Fin.cases (record005_frame025_supported hcells) (Fin.cases (record005_frame026_supported hcells) (Fin.cases (record005_frame027_supported hcells) (Fin.cases (record005_frame028_supported hcells) (Fin.cases (record005_frame029_supported hcells) (Fin.cases (record005_frame030_supported hcells) (Fin.cases (record005_frame031_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1ab0d566aa352da8cd436703315964c8562db1057dcbb45cf2e51718b865b22cfd64cb0c581abed5eaaea56a2b21576aaf53028914229ef4e2269d2d494749624591d48d4438a0d103e7dc3e31ebcf4e7a03cc1e10ef076e3b41d88ea274439d9cb8e006d335c9984c646212fc1744b7456529b14a09ec4d826912b894449422f914088043621390688244071f98f887ae3c61cb0dd86c434c1948c5c5c02bf15c0a4450226f11a088841c1b90c305d819208003f01ec0b805b02d015c0ac05501e80ec070024011808803e01e00e803c01c00d00500240100040018008002000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record006_frame001_links_0000 (interval_append _ 64 128 138 record006_frame001_links_0064 record006_frame001_links_0128))
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1a5ad276913471a2ad0f64831d98cec2c605300171ab595a7ad29680b3657c2b61592ab8552aa5d51ea8553ba9bd4cca614f8a70536a9894b1a53522a8e9463a2c91208854079f6cfa47903be9dacec87553a31cb8e3470d37e1bccdcc6d53671b1cd1066332c17bcb845b62c11574a9e4e725e12c88fc46122b90e485e4261fa8f9c7b63d01de8ebc7423951c38de46de36819a0c405ee2e31650afc50e26a13009104742310ff87c83ca1900b6859019008003f01ec0b805b02d015c0ac05501e80ec070024011808803e01e00e803c01c00d00500240100040018008002000 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record006_frame002_links_0000 (interval_append _ 64 128 138 record006_frame002_links_0064 record006_frame002_links_0128))
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x23d4798f11da3a4728c116a2ac4d88f1061441c83105a0940e804fe1f8beb7cef8df13de7b4f65eabd4774eb5d4ba072ce3dbfb706c8d75a8b4d64ec59892fa5e2ba171ae05bab696a2ce592b1d60abc574ad554aa15389f536a694ba9512722a43485d021f83e87a4f29e239e724e19bd36c6bcd51a734066ccc1933085c8b295c29e52c9d92f25247c8c9152063f07a8cd17a2e83905c0b4160230450881042003f0640c41802104007c0e01b03403c0700d0140240400400600800800 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record006_frame003_links_0000 (interval_append _ 64 128 138 record006_frame003_links_0064 record006_frame003_links_0128))
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
def record006_frame004_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0962.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0962.count (({ width := 10, code := 0xbaeeaba6e7b96e3b5ed3b42ccb26c6ac6a7a92a2a7a9aa4a8ba16809f2789de739be6e9aa699564c926438f6398b6268821c85a13801f87d9ec7a9e879de4785de76dd8755d3741cd72dc86f1b46bda1669986418a619745b56b57d585594f5354b50d414fd3c4d9304ad284891d46915424fd3d0ee394e235cce328c32fcbd2d4b12b49522c89194581585410c421043e0f43c0bc2e0b4210801f0701b0680f0380d028090200400c0200400 } : Fields).get c.val)
theorem record006_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record006_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record006) (record006.maps 4)
      (record006.inverseMaps 4) record006_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record006_frame004_links_0000 (interval_append _ 64 128 138 record006_frame004_links_0064 record006_frame004_links_0128))
theorem record006_frame004_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 4 :=
  of_group record006 4 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0962
    Papers.RationalityTen.SharedFrameCatalogue.group0962_facts record006_frame004_indices record006_frame004_graph record006_frame004_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (Fin.cases (record006_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x3561aacd546a5b519a86ce0662b2c990ac5b620afb9768b9e5b32d11656af55642abd4c0a24508a4b11d48d4438a0d103e7dc3e31ebcf4879a3c91df0ee076c3b41d60e9874439b1cb8e3070c3841c00ddc6e23699b20d726613191884bfa5f82ee9744b8c5ba2ca15e0aca55529b14a09ec4d826912b894449422f91408804192090fc47c43d51e30e606f03621a78ca462e2e015f8ae052228113788d044420e0dc86182ec0c902e016c0b405702b01540a6052027812008c04301e80ec070024011808803e01e00e803c01c00d00500240100040018008002000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record007_frame001_links_0000 (interval_append _ 64 128 135 record007_frame001_links_0064 record007_frame001_links_0128))
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x34b5a4ed2268e3455a1ec9063b319d858c0a6002e356b2b4f57eab75596a8f537a9853e29c14daa31d1208854079f6cfa47903be9daceb274a3a19c88e2670737e1bb0dc06d53661b1cd5c69f34c1a20cf4673331997ccb05ef2e116d8b1c5822b49574aa854f29213fc9ce4d425e12c88fc46122b90e485e4261fa8f9c7b63ad1d08e146f236e1b40cdc6242f71728b2857e287135098048823a11887fc3e41e50c805b42c80c802e016c0b405702b01540a6052027812008c04301e80ec070024011808803e01e00e803c01c00d00500240100040018008002000 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record007_frame002_links_0000 (interval_append _ 64 128 135 record007_frame002_links_0064 record007_frame002_links_0128))
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x11ea3cc788ed1d2394608b515626c478830a20e418808fe9f9be27b2f51dd3ad752d91a8b4d64ec59892fa5e2ba170ade5b6b5567acc592b095fabc570ad558aae558aa5532a4542a7d4e27d4da9a53025d4ae95128a4e4828d11522443485d021f83e87a4f29e239e724e19ae35467ccd997326614b99652ba53ca593b25e4a48f91922a40c7e0f519a2f45d07208c114220410800fc1e83c0760e41b8350640c41802104007c0e01b03403c0700d0140240400400600800800 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record007_frame003_links_0000 (interval_append _ 64 128 135 record007_frame003_links_0064 record007_frame003_links_0128))
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0962.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0962.count (({ width := 10, code := 0x2ebbaae9b9ee5b8ed7b4ed0b32c9b1ab1a9ea4a528da1e779ba699564c9262085a13801f87d9ec7a9e8795e277ddc765d6755d1739cd725c8711c16fdbc6e5b76d1b26bda166998649906318a621865f5785d1715b56b57d585594f5354b50d414fd2f4ad21475194550a3f8f43bce5388d7338ca30cbf2f4b52c4ad2548b2246510c421043e0f43c0e8390e0360d0320bc2e0b4210801f0701b0680f0380d028090200400c0200400 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record007_frame004_links_0000 (interval_append _ 64 128 135 record007_frame004_links_0064 record007_frame004_links_0128))
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0962
    Papers.RationalityTen.SharedFrameCatalogue.group0962_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x34899aecc966232fd8cac3660a30117a8bac5bc2d39690b3e59aac255d2acb5622a314d8a604da26ad33098b4bda5c92ca9554a7251923a8e8458a21501e7db3e91e48ec87553a31c68de66ce3639a2cccc6592da96bcb3e5912c115e8ad855d2aa953ca584fd26912c88ae42f2130fdc73a3751b38c145b02bf14489b04c024611d08c44021b40cd86402f016d0b204c414209e04682300d406902d81680ae05602a8150064031011808803e01e00e807003201700a003801a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x7427257187177166f46dd6d56ce6b66a868e67767366d66765063a62461d5fc5e75dd57c57957056855e5595515465405395245034e24c349247546e45143743142b4143ff3e83e13be3ad3a134033d33432c32131c31430a3042fd2e82c62a028724f2392322151e31cf1c81a518d17f17116415d14e14714013511910c1070f80f30ed0e009f09c08b08a06906805a05905605505405303203102302201f01e01d01c01901701400e00d00a009008007004003002001000 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xd2266bb19d69cb4859f2cd5612ae9565ab11518a6c53026d12f69554a3221501e7db3e91e48eb274a3a19c4cdd86cc3639a60d16673333197ccb2631304176cb6a58e2c115a4aba5542a794a49fe4d4259115c85e4261fb8f187683ad1ce8e3070a3751b70d9c6a433c1890c145ca2d815f8a244d826012308e84622010da066c3201780b6859026208d04601a80d205b02d015c0ac05502a014c0a404f023010c064031011808803e01e00e807003201700a003801a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xf0573036819dace666ab3098fac415fe2f95722b5859c299944a9ec4e623e91968b6457a2690f2864428a01cfa879c3c71d34e787183849be4dd26b63471970c505f82f3970cb685a42ca1584a72507269929492048923b116088243020c10007d83d11df0e9870236c19f0cac6022ef1638a604f226b12588f045a2000da86583101680ac852823a08d04601a80d205b02d015c0ac05502a014c0a404f023010c064031011808803e01e00e807003201700a003801a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x7296f56b664264063e63c6276156055fe5db5cc5c255553f52d5204b348c47847246044d44844242540e3fb3f63db3d23c43bd3b83b339937b35c34333032931d3143093042ea2cc2ad29426d25a25524422e22722321720e20a1fe1f91f31e91de1c51bf1aa1a419517b17116e16215d15814011910c1070fd0fa0f60de08908806806705905805505405305205105004d04404103103002302201f01e01d01c01901701400e00d00a009008007004003002001000 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record009_frame003_links_0000 record009_frame003_links_0064)
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1c0ed816b733a19aac7963ab1998aebfe5ea2ec16b8b325872ae1546a9c54ba9bd4569e94ed26652ea93f485239918488c42ba0f105481a4041e7ced874637a9b08d3865932218f8c746192f016d8b365602a1145c9f84d325a92288de45a22490d08384051fa0f687843ae1cb8c7c5dc2dd13f093447820c0fb878838c1b40c405e42ae13007982b415408d04601ac0d406903281880b605a02b01540a803301900c4058029011808803c01d00e003c01c00d00500240100070018008002000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
def record010_frame002_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x7116ef6e76b56ac63562e62b6286146075fa5da5cb5bb57655754c54553c52950d5084ed4dd4be49e49047745843040d3f53f23ef3d93c93bc39d38c37c33d31e31330c3032f02d92cb2ad29b27926524b2342101f71d41bc1ba1b81b31ad1a91a319d19717116115d13d12d12910d10b1060fd0f80ed0e70e00ce0b409509407f07e06406306205e05b05405304f04e04d03303203102c02902302201e01d01c00f00e00d00a009008007003002001000 } : Fields).get c.val)
theorem record010_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record010_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 2)
      (record010.inverseMaps 2) record010_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record010_frame002_links_0000 record010_frame002_links_0064)
theorem record010_frame002_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 2 :=
  of_group record010 2 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record010_frame002_indices record010_frame002_graph record010_frame002_links
def record010_frame003_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1976c66630b0117feb4e5a52d0166cafa56d2b2952ea7753327b937c9b44d7a6452d694c4a3a4651d68b4442a1790627fd3e91e3cec87553a31bf0daa6c73459998cb25ec2df96d4b625942b79554a9c513279932096448223190ec84c3f41e80ef475e3a11ca8e1c6f236f1b40bdc5942bf13008e84621dc0e506dc3461990c005d82c813007502a415008d04601ac0d406903281880b605a02b01540a803301900c4058029011808803c01d00e003c01c00d00500240100070018008002000 } : Fields).get c.val)
theorem record010_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record010_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record010) (record010.maps 3)
      (record010.inverseMaps 3) record010_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record010_frame003_links_0000 record010_frame003_links_0064)
theorem record010_frame003_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 3 :=
  of_group record010 3 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record010_frame003_indices record010_frame003_graph record010_frame003_links
def record010_frame004_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x6fe6cd6ca69e69b66165f65664d62260c6035e65d05c059458558057d57155a5495445275124f34e24d04ba4a548b47746945e45341a4073fe3e03c03b238f38137c37a36b35033e33731a30b2f62ed2d62c72b42a929a29028527826c26125424823f2371f31dc1d619e18617e15d15214713812f1191101010e60c009d09b08708606906806706306005905805405305203303203102c02902302201e01d01c00f00e00d00a009008007003002001000 } : Fields).get c.val)
theorem record010_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record010_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record010) (record010.maps 4)
      (record010.inverseMaps 4) record010_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record010_frame004_links_0000 record010_frame004_links_0064)
theorem record010_frame004_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 4 :=
  of_group record010 4 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record010_frame004_indices record010_frame004_graph record010_frame004_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (Fin.cases (record010_frame002_supported hcells) (Fin.cases (record010_frame003_supported hcells) (Fin.cases (record010_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x17dabb15cdae41710b825b2ad81684b34594ac6d5f6af456a2b19576aad52fa88541c9ef4f427113689a74cba4b11d48d4438a0d103e7a43cd1e48eda7683a79d10e7272e3841c04dc46d73641af4cc062f30f17f4bf05dd2e89718b7456529b14a09a44a224a10ac83841b20a0fe47f03ea1ee0f387483931c20dcc6ca35c1a30cc063c2fc1758b6c5942bb1598a78510276117087040e1f50f387603941bb0da068031817c09d84ac2340ee070834418608e046823011608a04381ac0d406902e016c0b405702b01540a8053029013c066032018809004602200f807803a01c } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record011_frame001_links_0000 (interval_append _ 64 128 138 record011_frame001_links_0064 record011_frame001_links_0128))
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1716b575a72d0566eb3257d2bbd5b4acf5652b1152ea8c53ba9b14cca604f726f93689894bda58d2aa94d4a3231d1208854079f6cfa47593a51d0ce146fc3719b54d9a6c734c1a2cce666632f9964bd85bf2da9638b045692ae9550a9e4e725e12c88ae42f2130f047643b11d28e2871237d1b80da868832e18e0c345f82ef1700b3c5842a81498a004e626412d093447c2340fd07b43c01cd0de86b03441930c485fc2e016609504782240e406d034018408e046823011608a04381ac0d406902e016c0b405702b01540a8053029013c066032018809004602200f807803a01c } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record011_frame002_links_0000 (interval_append _ 64 128 138 record011_frame002_links_0064 record011_frame002_links_0128))
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x213c1b82f04e07c0b806ffdfcbf57e4fb9f1be17b4f61eabd3772eb1d43a0738e59c938f716d91a8b4d64ec59892e15bcb6d66ac9580af15cab5558aa9522a253ea753e26c4d09812ea574a89452722a43485cfa1e53c46e0d89b0358688d099d332654c61822f45c0b41642b4548a714427e4e09992c25048c8e1182003e4790e91c63706b0cf1983185f8bc1462744b8820fa1e0378630c41843005f0bc1482885008c114220410800fc1f03d0780ec1682c0560841001f03806c0d019 } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record011_frame003_links_0000 (interval_append _ 64 128 138 record011_frame003_links_0064 record011_frame003_links_0128))
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
def record011_frame004_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0962.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0962.count (({ width := 10, code := 0xac2a6a8e9fa6e97a4e90a3289a1a839e2769be6d9aa689524b922439063d8ee398de2085a13801f87d9e5789df75dd573dcd729c86fdbd6ddb56c9b06819965d926418c62988619745b56b5594d52d384c9314b52448d1f46d1743907408fb3d8f33b0e7390dd368d4344cb324c6300be2ccaf2aca628c9e26c96250912308a1f0791d86c1a8681905e1745c16c5a1644c12c4a10c421043e0f43c0ec3a0e4380a8290a0210801f0701b06819 } : Fields).get c.val)
theorem record011_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record011_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record011) (record011.maps 4)
      (record011.inverseMaps 4) record011_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record011_frame004_links_0000 (interval_append _ 64 128 138 record011_frame004_links_0064 record011_frame004_links_0128))
theorem record011_frame004_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 4 :=
  of_group record011 4 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0962
    Papers.RationalityTen.SharedFrameCatalogue.group0962_facts record011_frame004_indices record011_frame004_graph record011_frame004_links
def record011_frame005_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a50ce166532c1938c8b61ab0797eabde5e52ed16ceb545962c59608af152fa8914209dc4e526913269804b6a39d15a89a4181fecfd277c3b41d5ce026ea3609aa8d2c6803199880bf05e22e816f4a564f026e12a092c47022f91308723b31bc8d985f82c715a894849624a12188d846a22e11388804142030fe07d43da1e70f007603a21c40de86d835e1a70d0866832418b0b905ac2c815b0aa053428c13e09c04c425212208484081f60e606f83601a408e046823011608a04381ac0d406902e016c0b405702b01540a8053029013c066032018809004602200f807803a01c } : Fields).get c.val)
theorem record011_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record011_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 5)
      (record011.inverseMaps 5) record011_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record011_frame005_links_0000 (interval_append _ 64 128 138 record011_frame005_links_0064 record011_frame005_links_0128))
theorem record011_frame005_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 5 :=
  of_group record011 5 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record011_frame005_indices record011_frame005_graph record011_frame005_links
def record011_frame006_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6ce6a769b69568e68967667166265964f64663563061e61460a6005cd5ac59f58d58757456b5625595255054f84c94a749a45b45544f43c43742741e41840f3fb3f63e33d93d23c839336f36535334d33933032a3212eb2c82bf28f26a25f21d2152142102062051fd1f61ee1dc1d31cb1c21bb1b71b11aa1a219318b18217a17216e16816115913e13512f12a12511e11911210e1091030fb0e40dd0d70c50bd0b70b108a08908808708608306906806705a05905805505405305205105004d03303203102402302201f01e01d01c } : Fields).get c.val)
theorem record011_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record011_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 6)
      (record011.inverseMaps 6) record011_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record011_frame006_links_0000 (interval_append _ 64 128 138 record011_frame006_links_0064 record011_frame006_links_0128))
theorem record011_frame006_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 6 :=
  of_group record011 6 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record011_frame006_indices record011_frame006_graph record011_frame006_links
def record011_frame007_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0961.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0961.count (({ width := 9, code := 0x33d9acc65b2992c7e371588c3613017fbe5eef378b8db6d768b3d96c963b155ea34fa3d0e853a9c4da6731974b255289248e411f8ec722b1187c3217098441e0cfb7abcdd6e773371b0d76ab419ecd65b2588c05eae56cb4582b556a7522813a994ba51208e4421504803e9e8ee74391bcd86a31180bc5a2c960aa5329144a04f2710c84411e8f076381b8d86a34198c84e2612884401f0e06c3419 } : Fields).get c.val)
theorem record011_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0961.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0961.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0961.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0961.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record011_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0961.localPairCheck (smallEmbedding record011) (record011.maps 7)
      (record011.inverseMaps 7) record011_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record011_frame007_links_0000 (interval_append _ 64 128 138 record011_frame007_links_0064 record011_frame007_links_0128))
theorem record011_frame007_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 7 :=
  of_group record011 7 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0961
    Papers.RationalityTen.SharedFrameCatalogue.group0961_facts record011_frame007_indices record011_frame007_graph record011_frame007_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (Fin.cases (record011_frame004_supported hcells) (Fin.cases (record011_frame005_supported hcells) (Fin.cases (record011_frame006_supported hcells) (Fin.cases (record011_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xe6272ab901b96dc36ce35c1a7ecb7627307181cc065ff2fb97c4bd15dfaee1758b9b5c4adf96e2b635acabb95b6a8e53da92d476a354d8a62d29892647f23d917083e4181ff8fe07e73f01f38f787a53c69e08ee07593a09cc4e4a7173881aa4d2c64831a9814bf05f32c11588a5a50d27793a497245a22810ac84241a1e68e746fa36f19e8c7461e2f61780ae047a2030fd07182ee16b0a304e824c10a07c03a41760b603781ac0c805f02d81540a803701980b004e02300e8070032017009804801e00e005002000e0050018008002000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record012_frame001_links_0000 (interval_append _ 64 128 129 record012_frame001_links_0064 record012_frame001_links_0128))
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xe6272ab901c5adfe6e6b671ae0d3f66332818bac376073019802bcc5cb2ded6dcb635ac2bc5522a4a51da8d542699b49b24311fc8f645fa23d07c8303ff1fc0fce7e03e71ef0f4a78d3c11dc0eb27413989c94e2e69e34018f4c3e5f82f99608ac452d28693bc9d24b424891a08b445021c90ac84241a2090ff47cc3d11d48e246de3491948c3c60c2f61780ad851e23d10187e83941a10b584e824c10707c03a410c08404001f80de06b02f816c0aa05401e80dc06602c013808c04001d00e004c02400f00700280100070018008002000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record013_frame001_links_0000 (interval_append _ 64 128 129 record013_frame001_links_0064 record013_frame001_links_0128))
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
def record013_frame002_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x84d84c84a84083881f7fa7f17d27a179678077575f7587537427307177056f96f36c76926676496406345fc5c75ac59158356f56154553e52952251c51850f5085034fd4f64ed4e64df4d04bb4a646445442d4173e43dc39c38836234c31a30c2f72e92d82d02c92bd2b62b02ab2a529a29028826e25724722d2152041f91dd1d31ba1af18515f15813d12c10c0e60d80c80c40c108408308007e06f06b05f05b05505403d03703302c02702302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record013_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record013_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record013) (record013.maps 2)
      (record013.inverseMaps 2) record013_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record013_frame002_links_0000 (interval_append _ 64 128 129 record013_frame002_links_0064 record013_frame002_links_0128))
theorem record013_frame002_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 2 :=
  of_group record013 2 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record013_frame002_indices record013_frame002_graph record013_frame002_links
def record013_frame003_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x548a8d5129fd38a55456884ff9a93325bcab92f242464828eb18e2d4568a50de0d4047f0fd1f63c875ae85cb38e704de1b0b5a68cd059e33a666ca99332063ac658830a602bdd76ac2576a8d4ca814fc94121a3044a849059fb3e0784ed9d5392704de9b83686b4d39a0322610be96f2c856cac14d2904e49891b20a4087a0e71a63045d8b115c2a83d0780ea1d0338640b415c288500760d81902c04e08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record013_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record013_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record013) (record013.maps 3)
      (record013.inverseMaps 3) record013_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record013_frame003_links_0000 (interval_append _ 64 128 129 record013_frame003_links_0064 record013_frame003_links_0128))
theorem record013_frame003_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 3 :=
  of_group record013 3 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record013_frame003_indices record013_frame003_graph record013_frame003_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (Fin.cases (record013_frame002_supported hcells) (Fin.cases (record013_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x7313955c80e2d6ff3735b38d7069fb319940c5d61bb03980cbd15cdadf96e2b6351da8d51fc8f645fa23d07c8303ff1fc0fce7d43e21ec0f3c78d3bc1d90ea47413971c88e2e7053601ab0d3c68032f992cc7a61f30217e0be65ce2cf1608ade5622a494b4a3450d27c93bc9d24b424891a08b445021c90ac84241a1f20f4475638b1b78d2c65630f1828bd85e02b614788f44061fa0e506842d613a093041c1f00e903781ac0be05b02a81500a6052027013009004601e80dc06602c013808c04001d00e004c02400f00700280100070018008002000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record014_frame001_links_0000 (interval_append _ 64 128 132 record014_frame001_links_0064 record014_frame001_links_0128))
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x84d84c84a84083881f7fa7f17d27a179678077575f75874473271e70c6f964964059158356f56154553e52952251c51550d5065014fd4f14e84e44df4c94b44a649947d46c46445444543642d4174053e43dc3c53b039c39038837836235534c33831a30c2f72e92d82d02c92bd2b62b02ab28f28826f25824722f2172041f71dd1d31ba1af18515f15813d12c10c0e60d80c80c40c106f06b05f05b05505405305204e04c04804603d03703302c02702302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record014_frame002_links_0000 (interval_append _ 64 128 132 record014_frame002_links_0064 record014_frame002_links_0128))
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
def record014_frame003_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0xa9151aa253fa714aa8ad109ff352664b795725e484848ef1a22fc567f0fd1cb38e704de1b0b5a68cd059e33765aca192320636c4d8730a5f8bc976ae45a0b1d612bb562aa551a9951aa053f26f4bc94124a434728c11522543a849059fb3e0784ed9d5392704de9b834c680c91852fa5c0b295b2ae534a413926246c829021e839c698c11762c4570aa0ce1902d0570a21402784e094120228440760d81902c04e08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record014_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record014_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record014) (record014.maps 3)
      (record014.inverseMaps 3) record014_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record014_frame003_links_0000 (interval_append _ 64 128 132 record014_frame003_links_0064 record014_frame003_links_0128))
theorem record014_frame003_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 3 :=
  of_group record014 3 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record014_frame003_indices record014_frame003_graph record014_frame003_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (Fin.cases (record014_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1cc4e5572038b5bfcdcd6c7b58da96d3f699303180cbf15ed2eed748b7f5b72d69606afa5732b19546a9a5432999494a3d51aa71533696049b24311fe8f645f22310788303fe1fc0fce7e03e71ef0f4a78d3c11dc0eb27413989c94e2e69e34018f4c3e5f82f996b4aac50127713a496a49522810848344141f80f0876839f1c48df46c435419f8ca463a30617b8bc056a28b12d892847a221108080c3f41c90d185a427012608483d81d2092047022810807e02f816c0aa05401e80dc066028013809004601f00e807002e012007002c0100070018008002000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record015_frame001_links_0000 (interval_append _ 64 128 134 record015_frame001_links_0064 record015_frame001_links_0128))
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record015_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003
