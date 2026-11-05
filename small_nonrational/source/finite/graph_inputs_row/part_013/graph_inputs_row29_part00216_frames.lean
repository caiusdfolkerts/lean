module
prelude
public import GraphInputsRow29Part00216Data
public import RawFrameSupport
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00216
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x3889be0cbe65631fd8b4c425deae2d4b2a4750d27d53ba9b34cfa4a5242914482a3fd0808083601aa4d0265332097d4b7e5772b21528a8052628d94209ee4dc26a12208ec455218908c81c4031f90f7479a3861a80c205ea2db1688adc55829914409b44ca21910387983841b40cf865030616e0af055829e14109984b024a117074838c0cc06403001640ac055023811408203501900c405c02c014008403c01d00c805c02600c004802000c005002000c004000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0x16eedbd96b1b606bb56caa752e885089f53ba71cc5965076084007def99c3b7f67ccd594b1c62cc0178ae25aab2162ab756aac15529e5389e137a604a692d2123945a87d0a1fd3dc78ceb9ca3906f0dc9b535e694d11802f65b8b215d2aa538a193725e49c8d90f2023f47b0ec15e2982c0560a81342504907e0f81e8330600bc1602a0500840f01d03205c0980c0120200300500800c01000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0824.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0824.count (({ width := 11, code := 0x14c693cf29d938a6c4d096529e3946b8c516628439854ef5da3a672ee45a6b465fcbd976ae25bcb2d5e2a753aa4d4828850a9f93c26a4d0925222354508810d21541880cfc9e23ae704dc9ae356674cd99431e618c19622b8534a113b26a4b89391b228438838fc1e23a8720d91602a83005e0b81542905108a110208350640c41702c0500840f01d03205c0980c0120200300500800c01000 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0824
    Papers.RationalityTen.SharedFrameCatalogue.group0824_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x39b9b5cd5e6a534b5a42d18686b40d9f8cf66772e396aab1556f2af1546a8f53628893d29a94b9254126e92348023bd1d08df46d23451988c545f22d51608ab452225911e73f3541a44cf665f31c18a0bd455329e1498a144e326993049764b3257129893e48f24512048fc47723791a483c34419a8c1c5942a914a0a284ea26b12d88b44322140f7078038c1b10d386483101780a504d826210b07e83dc1e40e9071036c1aa0b405001d40e606f03301900c003701a80c8062028013008c04401300600280120080030010006002 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record001_frame001_links_0000 record001_frame001_links_0064)
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
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x2bd52da3142a814b691320639c608810ae09c017e2f91edbca77aeb5ce3956fade1b8b5d6a8c55782bc56aabd51a98524a013825a4a29391fa3c46e8cd1221a420824fa9f43d0788ec9d237a6c4cc9862f25c0b51612aa540a51452824f49912924c45c8990f2123fc7a0ed1ce3706b0d018e3085e0b115a2a05288e0da1903105e08a0dc1a8320620b81602804c0941182203205c0980c0140240400600a01001802 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x379dae0cbb63eb0fd704b0b52b28613b49b84d126152f29704b2a56d2a894e4a324e126492a492247122a90348023ed1cc8df4051e28d8668432217d4b7e5742a694f4a0a4f4270134495849924411d88ce45521190407be3cf1c30d4060a2de1670a5850a27113108f445421910387e03cc1b40d085c02c01570a8051c28413909a04b424c11d08c043c21210507e03d41dc0ea07103701ac0d205002480fa06f02280dc05c02c014009804a023011008403e01e00e806402e013008804001c00d0060028012008 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0814.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0814.count (({ width := 11, code := 0x14267d4de99d3024947f8ad11e1d41f814fc1efbda796f05ddbb5758e7dcab8f712e01bd3646c4d79a3b41620be5672c256ea7d4727b4dc9ad2da564a09311fa3946c8bd1522542e84d032033cc73cda9a4340638c41822fc5b8b31622b6558a894027649c92122234444868ff1fa3d0758df1ba34c658c91842f05a8b114e2884f89c11c2203b06d08a0dc1702c050098128230440840f81e03a0640b8130220400700d01802804808 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0814
    Papers.RationalityTen.SharedFrameCatalogue.group0814_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x15eab0d2aa2b40667cb690f1c62fc45861052044027e0f95eebd5798ef9db3af74ee79cb37c6f4dc9af35562abc15b2a452aa013825a4a29391fa3c46e8cd1121d43084d072073e47a8ed1d437a6c4cb98a3085b8b41642be554a814a28a5049e9322564648a11021440c800f71ec3b8748df1bc354678ce18c3045d8b91602ac538a611c2103b06d08a0dc1702c050098128230440840f81e03a0640b8130220400700d01802804808 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record003_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00216
